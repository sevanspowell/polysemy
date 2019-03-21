{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies          #-}

module MVP (oneBigNumber, baselineFoldMap) where

import qualified Control.Monad.State.Strict as S
import Data.Monoid
import Data.Foldable
import Data.Typeable
import Data.Functor.Identity
import Data.Coerce
import Data.Tuple


data Union (r :: [(* -> *) -> * -> *]) (m :: * -> *) a where
  Union
      :: Effect (IndexOf r n)
      => SNat n
      -> IndexOf r n m a
      -> Union r m a


instance (Functor m) => Functor (Union r m) where
  fmap f (Union w t) = Union w $ fmap' f t
    where
      fmap' :: (Functor m, Effect f) => (a -> b) -> f m a -> f m b
      fmap' = fmap
      {-# INLINE fmap' #-}
  {-# INLINE fmap #-}



type Member e r =
  ( Find r e
  , e ~ IndexOf r (Found r e)
  , Effect e
  )




------------------------------------------------------------------------------
data Nat = Z | S Nat
  deriving Typeable


------------------------------------------------------------------------------
data SNat :: Nat -> * where
  SZ :: SNat 'Z
  SS :: Typeable n => SNat n -> SNat ('S n)
  deriving Typeable


type family IndexOf (ts :: [k]) (n :: Nat) :: k where
  IndexOf (k ': ks) 'Z = k
  IndexOf (k ': ks) ('S n) = IndexOf ks n


type family Found (ts :: [k]) (t :: k) :: Nat where
  Found (t ': ts) t = 'Z
  Found (u ': ts) t = 'S (Found ts t)


class Typeable (Found r t) => Find (r :: [k]) (t :: k) where
  finder :: SNat (Found r t)

instance {-# OVERLAPPING #-} Find (t ': z) t where
  finder = SZ
  {-# INLINE finder #-}

instance ( Find z t
         , Found (_1 ': z) t ~ 'S (Found z t)
         ) => Find (_1 ': z) t where
  finder = SS $ finder @_ @z @t
  {-# INLINE finder #-}


------------------------------------------------------------------------------
decomp :: Union (e ': r) m a -> Either (Union r m a) (e m a)
decomp (Union p a) =
  case p of
    SZ   -> Right a
    SS n -> Left $ Union n a
{-# INLINE decomp #-}



------------------------------------------------------------------------------
absurdU :: Union '[] m a -> b
absurdU = absurdU



------------------------------------------------------------------------------
inj :: forall r e a m. (Functor m , Member e r) => e m a -> Union r m a
inj e = Union (finder @_ @r @e) e
{-# INLINE inj #-}





newtype Semantic r a = Semantic
  { runSemantic
        :: ∀ m
         . Monad m
        => (∀ x. Union r (Semantic r) x -> m x)
        -> m a
  }

data State s m a
  = Get (s -> a)
  | Put s a
  deriving (Functor, Effect)

get :: Member (State s) r => Semantic r s
get = send $ Get id
{-# INLINE get #-}


put :: Member (State s) r => s -> Semantic r ()
put !s = send $! Put s ()
{-# INLINE put #-}



modify :: Member (State s) r => (s -> s) -> Semantic r ()
modify f = do
  !s <- get
  put $! f s
{-# INLINE modify #-}


runState :: s -> Semantic (State s ': r) a -> Semantic r (s, a)
runState = stateful $ \case
  Get k   -> \s -> pure (s, k s)
  Put s k -> const $ pure (s, k)
{-# INLINE[3] runState #-}


baselineFoldMap :: Int -> Int
baselineFoldMap n = getSum $ snd $ flip S.runState mempty $ for_ [0..n] $ \i -> S.modify (<> Sum i)

oneBigNumber :: Int -> Int
oneBigNumber    n = getSum $ fst $ run  $ runState mempty $ for_ [0..n] $ \i ->   modify (<> Sum i)


------------------------------------------------------------------------------
run :: Semantic '[] a -> a
run (Semantic m) = runIdentity $ m absurdU
{-# INLINE run #-}


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


------------------------------------------------------------------------------
stateful
    :: Effect e
    => (∀ x. e (Semantic (e ': r)) x -> s -> Semantic r (s, x))
    -> s
    -> Semantic (e ': r) a
    -> Semantic r (s, a)
stateful f = interpretInStateT $ \e -> S.StateT $ fmap swap . f e
{-# INLINE[3] stateful #-}

------------------------------------------------------------------------------
interpretInStateT
    :: Effect e
    => (∀ x. e (Semantic (e ': r)) x -> S.StateT s (Semantic r) x)
    -> s
    -> Semantic (e ': r) a
    -> Semantic r (s, a)
interpretInStateT f s (Semantic m) = Semantic $ \k ->
  fmap swap $ flip S.runStateT s $ m $ \u ->
    case decomp u of
        Left x -> S.StateT $ \s' ->
          k . fmap swap
            . weave (s', ()) (uncurry $ ___interpretInStateT___loop_breaker f)
            $ x
        Right y -> S.mapStateT (usingSemantic k) $ f y
{-# INLINE interpretInStateT #-}

___interpretInStateT___loop_breaker
    :: Effect e
    => (∀ x. e (Semantic (e ': r)) x -> S.StateT s (Semantic r) x)
    -> s
    -> Semantic (e ': r) a
    -> Semantic r (s, a)
___interpretInStateT___loop_breaker = interpretInStateT
{-# NOINLINE ___interpretInStateT___loop_breaker #-}

------------------------------------------------------------------------------
usingSemantic
    :: Monad m
    => (∀ x. Union r (Semantic r) x -> m x)
    -> Semantic r a
    -> m a
usingSemantic k m = runSemantic m k
{-# INLINE usingSemantic #-}


class (∀ m. Functor m => Functor (e m)) => Effect e where
  weave
      :: (Functor s, Functor m, Functor n)
      => s ()
      -> (∀ x. s (m x) -> n (s x))
      -> e m a
      -> e n (s a)

  default weave
      :: ( Coercible (e m (s a)) (e n (s a))
         , Functor s
         , Functor m
         , Functor n
         )
      => s ()
      -> (∀ x. s (m x) -> n (s x))
      -> e m a
      -> e n (s a)
  weave s _ = coerce . fmap (<$ s)
  {-# INLINE weave #-}

  hoist
        :: ( Functor m
           , Functor n
           )
        => (∀ x. m x -> n x)
        -> e m a
        -> e n a

  default hoist
      :: ( Coercible (e m a) (e n a)
         , Functor m
         )
      => (∀ x. m x -> n x)
      -> e m a
      -> e n a
  hoist _ = coerce
  {-# INLINE hoist #-}



send :: Member e r => e (Semantic r) a -> Semantic r a
send = liftSemantic . inj
{-# INLINE[3] send #-}

liftSemantic :: Union r (Semantic r) a -> Semantic r a
liftSemantic u = Semantic $ \k -> k u
{-# INLINE liftSemantic #-}

instance Effect (Union r) where
  weave s f (Union w e) = Union w $ weave s f e
  {-# INLINE weave #-}

  hoist f (Union w e) = Union w $ hoist f e
  {-# INLINE hoist #-}

