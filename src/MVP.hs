{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -O2 -ddump-rules -ddump-rule-firings -ddump-spec #-}

module MVP (badCore, goodCore, easy) where

import qualified Control.Monad.State.Strict as S
import           Data.Foldable
import           Data.Functor.Identity
import           Data.Monoid
import           Data.Tuple
import Control.Applicative

-- slowBeforeSpecialization :: (Num a, Ord a) => Semantic '[State a] a
-- slowBeforeSpecialization = do
--   n <- get
--   if n <= 0
--      then pure n
--      else do
--        put $ n - 1
--        slowBeforeSpecialization

-- easy :: Int -> Int
-- easy n = n -- fst $ run $ runState n $ slowBeforeSpecialization

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
        :: forall m
         . Monad m
        => (forall x. Union r x -> m x)
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
  liftA2 f x = (<*>) (fmap f x)
  {-# INLINE liftA2 #-}
  a1 *> a2 = (id <$ a1) <*> a2
  {-# INLINE (*>) #-}

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
    :: (forall x. e x -> S.StateT s (Semantic r) x)
    -> s
    -> Semantic (e ': r) a
    -> Semantic r (s, a)
interpretInStateT f s (Semantic m) = Semantic $ \k ->
  fmap swap $ flip S.runStateT s $ m $ \u ->
    S.mapStateT (\z -> runSemantic z k) $ f $ decomp u
{-# INLINE interpretInStateT #-}

