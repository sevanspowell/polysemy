{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}
{-# OPTIONS_GHC -Wall                   #-}

module Lib where

import Data.Proxy
import GHC.TypeLits
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Resource
import qualified Control.Exception as X
import qualified Control.Monad.Trans.Except as E
import qualified Control.Monad.Trans.State.Strict as S
import           Data.OpenUnion
import           Data.OpenUnion.Internal
import           Eff.Interpretation
import           Eff.Type
import Data.Coerce


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
  put "nice!"
  put "nice!"
  put "nice!"
  get @String


runTeletype :: Member IO r => Eff (State String ': r) a -> Eff r a
runTeletype = interpret $ \case
    Get   -> send getLine
    Put s -> send $ putStrLn s



runState :: s -> Eff (State s ': r) a -> Eff r (a, s)
runState = stateful $ \case
  Get    -> S.get
  Put s' -> S.put s'
{-# INLINE runState #-}


newtype Error e r where
  Error :: e -> Error e r


throwError :: Member (Error e) r => e -> Eff r a
throwError = send . Error
{-# INLINE throwError #-}


runError :: Eff (Error e ': r) a -> Eff r (Either e a)
runError = shortCircuit $ \(Error e) -> E.throwE e


runErrorRelay :: Eff (Error e ': r) a -> Eff r (Either e a)
runErrorRelay = relay (pure . Right) $ \(Error e) _ -> pure $ Left e


subsume :: Member eff r => Eff (eff ': r) ~> Eff r
subsume = interpret send


effPrint :: Member IO r => String -> Eff r ()
effPrint = send @IO . putStrLn


data Bracket r a where
  Bracket :: KnownNat (Length r')
          => (Eff r' ~> Eff r)
          -> Eff r' a
          -> (a -> Eff r' ())
          -> (a -> Eff r' b)
          -> Bracket r b

type Bracketed r = Eff (Bracket r ': r)


liftBracket :: forall r r'. (Eff r ~> Eff r') -> Bracketed r ~> Bracketed r'
liftBracket f (Freer m) = Freer $ \k -> m $ \u ->
  case decomp u of
    Left x -> usingFreer k $ raise $ f $ liftEff x
    Right (Bracket z alloc dealloc doit) ->
      usingFreer k $ send $Bracket (f . z) alloc dealloc doit


raiseLast :: forall m r. Eff r ~> Eff (r :++: '[m])
raiseLast = coerce

liftZoom :: (Eff r ~> Eff '[IO]) -> Eff (r :++: '[m]) ~> Eff '[IO, m]
liftZoom f z = introduce $ f $ coerce z


type family Length (r :: [k]) where
  Length '[] = 0
  Length (a ': r) = 1 + Length r

getLength :: forall (r :: [k]). KnownNat (Length r) => Word
getLength = fromInteger $ natVal $ Proxy @(Length r)




runBracket :: Bracketed '[IO] ~> IO
runBracket (Freer m) = runResourceT $ m $ \u ->
  case decomp u of
    Left x -> liftIO $ extract x
    Right (Bracket z (alloc :: Eff r' a) dealloc doit) -> do
      let z' :: Eff (r' :++: '[ResourceT IO]) ~> Eff '[ResourceT IO]
          z' = fmap (interpret $ send . liftIO @(ResourceT IO)) $ liftZoom z

          raising :: Eff r' ~> Eff (r' :++: '[ResourceT IO])
          raising = raiseLast @(ResourceT IO)

          liftResource :: ResourceT IO ~> Eff (r' :++: '[ResourceT IO])
          liftResource = liftEff . unsafeInj (getLength @_ @r' + 1)


      runM $ (z') $ do
        a <- raising alloc
        key <- liftResource $ register $ runM $ z $ dealloc a
        r <- raiseLast @(ResourceT IO) $ doit a
        liftResource $ release key
        pure r


bracket
    :: KnownNat (Length r)
    => Eff r a
    -> (a -> Eff r ())
    -> (a -> Eff r b)
    -> Bracketed r b
bracket alloc dealloc doit = send $ Bracket id alloc dealloc doit

fromRight :: Either a b -> b
fromRight = either undefined id

main :: IO ()
main = runBracket $ liftBracket (fmap fromRight . runError @String) $ do
  bracket (effPrint "alloc") (const $ effPrint "dealloc") $ const $ do
    effPrint "hi"
    throwError "fuck"
    effPrint "bye"

