{-# LANGUAGE BangPatterns #-}

module MVP (badCore, goodCore) where

import qualified Control.Monad.State.Strict as S
import           Data.Foldable
import           Data.Functor.Identity
import           Data.Monoid
import           Data.Tuple

goodCore :: Int -> Int
goodCore n = getSum $ snd $ flip S.runState mempty $ for_ [0..n] $ \i -> S.modify (<> Sum i)

badCore :: Int -> Int
badCore n  = getSum $ fst $ run  $ runState mempty $ for_ [0..n] $ \i ->   modify (<> Sum i)

data Union (r :: [* -> *]) a where
  Union :: e a -> Union '[e] a

decomp :: Union (e ': r) a -> e a
decomp (Union a) = a
{-# INLINE decomp #-}

absurdU :: Union '[] a -> b
absurdU = absurdU

newtype Semantic r a = Semantic
  { runSemantic
        :: ∀ m
         . Monad m
        => (∀ x. Union r x -> m x)
        -> m a
  }

instance Functor (Semantic f) where
  fmap f (Semantic m) = Semantic $ \k -> fmap f $ m k
  {-# INLINE fmap #-}

instance Applicative (Semantic f) where
  pure a = Semantic $ const $ pure a
  {-# INLINE pure #-}
  Semantic f <*> Semantic a = Semantic $ \k -> f k <*> a k
  {-# INLINE (<*>) #-}

instance Monad (Semantic f) where
  return = pure
  {-# INLINE return #-}
  Semantic ma >>= f = Semantic $ \k -> do
    z <- ma k
    runSemantic (f z) k
  {-# INLINE (>>=) #-}

data State s a
  = Get (s -> a)
  | Put s a
  deriving Functor

get :: Semantic '[State s] s
get = Semantic $ \k -> k $ Union $ Get id
{-# INLINE get #-}

put :: s -> Semantic '[State s] ()
put !s = Semantic $ \k -> k $ Union $! Put s ()
{-# INLINE put #-}

modify :: (s -> s) -> Semantic '[State s] ()
modify f = do
  !s <- get
  put $! f s
{-# INLINE modify #-}

runState :: s -> Semantic (State s ': r) a -> Semantic r (s, a)
runState = interpretInStateT $ \case
  Get k   -> fmap k S.get
  Put s k -> S.put s >> pure k
{-# INLINE[3] runState #-}

run :: Semantic '[] a -> a
run (Semantic m) = runIdentity $ m absurdU
{-# INLINE run #-}

interpretInStateT
    :: (∀ x. e x -> S.StateT s (Semantic r) x)
    -> s
    -> Semantic (e ': r) a
    -> Semantic r (s, a)
interpretInStateT f s (Semantic m) = Semantic $ \k ->
  fmap swap $ flip S.runStateT s $ m $ \u ->
    S.mapStateT (\z -> runSemantic z k) $ f $ decomp u
{-# INLINE interpretInStateT #-}

___interpretInStateT___loop_breaker
    :: (∀ x. e x -> S.StateT s (Semantic r) x)
    -> s
    -> Semantic (e ': r) a
    -> Semantic r (s, a)
___interpretInStateT___loop_breaker = interpretInStateT
{-# NOINLINE ___interpretInStateT___loop_breaker #-}

