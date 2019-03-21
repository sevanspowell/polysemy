{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module MVP (oneBigNumber, baselineFoldMap) where

import qualified Control.Monad.State.Strict as S
import Data.Monoid
import Data.Foldable
import Data.Functor.Identity
import Data.Tuple


data Union (r :: [(* -> *) -> * -> *]) (m :: * -> *) a where
  Union
      :: Functor (IndexOf r n m)
      => SNat n
      -> IndexOf r n m a
      -> Union r m a

instance (Functor m) => Functor (Union r m) where
  fmap f (Union w t) = Union w $ fmap f t
  {-# INLINE fmap #-}

class    (e ~ IndexOf r (Found r e), forall m. (Functor m => Functor (e m))) => Member e r
instance (e ~ IndexOf r (Found r e), forall m. (Functor m => Functor (e m))) => Member e r

data Nat = Z | S Nat

data SNat :: Nat -> * where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

type family IndexOf (ts :: [k]) (n :: Nat) :: k where
  IndexOf (k ': ks) 'Z = k
  IndexOf (k ': ks) ('S n) = IndexOf ks n

type family Found (ts :: [k]) (t :: k) :: Nat where
  Found (t ': ts) t = 'Z
  Found (u ': ts) t = 'S (Found ts t)

decomp :: Union (e ': r) m a -> Either (Union r m a) (e m a)
decomp (Union p a) =
  case p of
    SZ   -> Right a
    SS n -> Left $ Union n a
{-# INLINE decomp #-}

absurdU :: Union '[] m a -> b
absurdU = absurdU

newtype Semantic r a = Semantic
  { runSemantic
        :: ∀ m
         . Monad m
        => (∀ x. Union r (Semantic r) x -> m x)
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

data State s m a
  = Get (s -> a)
  | Put s a
  deriving Functor

get :: Semantic '[State s] s
get = Semantic $ \k -> k $ Union SZ $ Get id
{-# INLINE get #-}

put :: s -> Semantic '[State s] ()
put !s = Semantic $ \k -> k $ Union SZ $! Put s ()
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

baselineFoldMap :: Int -> Int
baselineFoldMap n = getSum $ snd $ flip S.runState mempty $ for_ [0..n] $ \i -> S.modify (<> Sum i)

oneBigNumber :: Int -> Int
oneBigNumber    n = getSum $ fst $ run  $ runState mempty $ for_ [0..n] $ \i ->   modify (<> Sum i)

run :: Semantic '[] a -> a
run (Semantic m) = runIdentity $ m absurdU
{-# INLINE run #-}

interpretInStateT
    :: (∀ x. e (Semantic (e ': r)) x -> S.StateT s (Semantic r) x)
    -> s
    -> Semantic (e ': r) a
    -> Semantic r (s, a)
interpretInStateT f s (Semantic m) = Semantic $ \k ->
  fmap swap $ flip S.runStateT s $ m $ \u ->
    case decomp u of
        Left _ -> undefined
        Right y -> S.mapStateT (\z -> runSemantic z k) $ f y
{-# INLINE interpretInStateT #-}

___interpretInStateT___loop_breaker
    :: (∀ x. e (Semantic (e ': r)) x -> S.StateT s (Semantic r) x)
    -> s
    -> Semantic (e ': r) a
    -> Semantic r (s, a)
___interpretInStateT___loop_breaker = interpretInStateT
{-# NOINLINE ___interpretInStateT___loop_breaker #-}

