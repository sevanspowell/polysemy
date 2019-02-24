{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ViewPatterns               #-}
{-# OPTIONS_GHC -Wall                   #-}

module Lib where

import qualified Control.Exception as X
import qualified Control.Monad.Trans.Except as E
import qualified Control.Monad.Trans.State.Strict as S
import           Data.OpenUnion
import           Eff.Interpretation
import           Eff.Type


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
  Bracket :: Eff r a -> (a -> Eff r ()) -> (a -> Eff r b) -> Bracket r b

type Bracketed r = Eff (Bracket r ': r)


liftBracket :: forall r r'. (Eff r ~> Eff r') -> Bracketed r ~> Bracketed r'
liftBracket f (Freer m) = Freer $ \k -> m $ \u ->
  case decomp u of
    Left x -> usingFreer k $ raise $ f $ liftEff x
    Right (Bracket alloc dealloc doit) ->
      let liftJob :: Eff r ~> Eff r'
          liftJob n = runFreer n $ f . liftEff
       in usingFreer k
            . send
            $ Bracket (liftJob alloc)
                      (fmap liftJob dealloc)
                      (fmap liftJob doit)


runBracket :: Bracketed '[IO] ~> IO
runBracket (Freer m) = m $ \u ->
  case decomp u of
    Left x -> extract x
    Right (Bracket alloc dealloc doit) ->
      X.bracket (runM alloc) (fmap runM dealloc) (fmap runM doit)


bracket :: Eff r a -> (a -> Eff r ()) -> (a -> Eff r b) -> Bracketed r b
bracket alloc dealloc doit = send $ Bracket alloc dealloc doit

fromRight :: Either a b -> b
fromRight = either undefined id

-- main :: IO ()
-- main = runBracket $ liftBracket (fmap fromRight . runError @String) $ do
--   bracket (effPrint "alloc") (const $ effPrint "dealloc") $ const $ do
--     effPrint "hi"
--     throwError "fuck"
--     effPrint "bye"

-- main :: IO ()
-- main = runM . fmap fromRight . runError @String $ do
--     effPrint "hi"
--     throwError "fuck"
--     effPrint "bye"

