{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

module Lib where

import Data.Functor.Identity
import Debug.Trace
import Data.OpenUnion
import Data.Functor.Compose
import Data.IORef
import Control.Arrow (second)
import System.IO.Unsafe
import Unsafe.Coerce


newtype Freer f a = Freer
  { runFreer :: forall m. Monad m => (forall t s. s -> f t -> (s, m t)) -> m a
  }

-- freeMap :: (f ~> g) -> Freer f ~> Freer g
-- freeMap nat (Freer m) = Freer $ \k -> m $ k . nat
-- {-# INLINE freeMap #-}

instance Functor (Freer f) where
  fmap f (Freer z) = Freer $ \z' -> fmap f $ z z'
  {-# INLINE fmap #-}

instance Applicative (Freer f) where
  pure a = Freer $ const $ pure a
  {-# INLINE pure #-}
  Freer f <*> Freer a = Freer $ \k -> f k <*> a k
  {-# INLINE (<*>) #-}

instance Monad (Freer f) where
  return = pure
  {-# INLINE return #-}
  Freer ma >>= f = Freer $ \k -> do
    z <- ma k
    runFreer (f z) k
  {-# INLINE (>>=) #-}


type Eff r = Freer (Union r)


send :: Member eff r => eff a -> Eff r a
send t = Freer $ \k -> snd $ k "hello" $ inj t
{-# INLINE send #-}


run :: Freer (Union '[Identity]) a -> a
run = runIdentity . runM



runM :: Monad m => Freer (Union '[m]) a -> m a
runM z = runFreer z $ \s -> (s,) . extract
{-# INLINE runM #-}


data State s a where
  Get :: State s s
  Put :: s -> State s ()

get :: Member (State s) r => Eff r s
get = send Get
{-# INLINE get #-}

put :: Member (State s) r => s -> Eff r ()
put = send . Put
{-# INLINE put #-}


foom :: Eff '[State String, IO] String
foom = do
  z <- get @String
  put $ "nice!" ++ z
  get @String

main = runM (runState "hello" foom) >>= print

type f ~> g = forall x. f x -> g x
infixr 1 ~>

interpret :: (eff ~> Eff r) -> Eff (eff ': r) ~> Eff r
interpret f (Freer m) = Freer $ \k -> m $ \s u -> do
  case decomp u of
    Left x -> k s x
    Right y -> (s, runFreer (f y) k)
{-# INLINE interpret #-}

interpretS :: s -> (forall x. s -> eff x -> (s, Eff r x)) -> Eff (eff ': r) ~> Eff r
interpretS s f (Freer m) = Freer $ \k -> m $ \s u -> do
  case decomp u of
    Left x -> k s x
    Right y ->
      let (s', e) = f (unsafeCoerce s) y
       in (unsafeCoerce s', runFreer e k)
{-# INLINE interpretS #-}


-- runTeletype :: forall r a. Member IO r => Eff (State String ': r) a -> Eff r a
-- runTeletype = interpret bind
--   where
--     bind :: forall x. State String x -> Eff r x
--     bind Get     = send getLine
--     bind (Put s) = send $ putStrLn s



-- raise :: Eff r a -> Eff (u ': r) a
-- raise = freeMap weaken
-- {-# INLINE raise #-}


-- introduce :: Eff (eff ': r) a -> Eff (eff ': u ': r) a
-- introduce = freeMap (shuffle . weaken)
-- {-# INLINE introduce #-}

-- interpretS2
--     :: Show s => ((,) s `Compose` eff ~> (,) s `Compose` Eff r)
--     -> s
--     -> Eff (eff ': r) ~> Eff r
-- interpretS2 f s mm =
--     freeMap (snd . getCompose) $ Freer $ \k -> m $ \(Compose (s', u)) ->
--       case decomp u of
--         Left x -> k $ Compose (showTrace s', x)
--         Right y ->
--             let (s'', e) = getCompose $ f $ Compose (s', y)
--              in runFreer _ $ k . Compose . (\l -> (s'', l))

--   where
--     Freer m = freeMap (\e -> Compose (s, e)) mm


runState :: forall s r a. Show s => s -> Eff (State s ': r) a -> Eff r a
runState s = interpretS s nat
  where
    nat :: s -> State s x -> (s, Eff r x)
    nat s Get      = (s, pure s)
    nat _ (Put s') = (s', pure ())
{-# INLINE runState #-}

-- showTrace :: Show a => a -> a
-- showTrace = trace =<< show

