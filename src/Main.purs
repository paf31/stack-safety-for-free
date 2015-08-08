module Main where

import Prelude

import Data.Either
import Data.Bifunctor

import Control.Monad.Free.Naive
import Control.Monad.Free.Trans.Naive

import Control.Monad.Eff
import Control.Monad.Eff.Console
import Control.Monad.ST
import Control.Monad.Trans

data CounterF a 
  = Increment a
  | Read (Int -> a)
  | Reset a
  
instance functorCounterF :: Functor CounterF where
  map f (Increment a) = Increment (f a)
  map f (Read k) = Read (f <<< k)
  map f (Reset a) = Reset (f a)
    
-- | The free monad for `CounterF`.
 
type Counter = Free CounterF

increment :: Counter Unit
increment = liftFree (Increment unit)

read :: Counter Int
read = liftFree (Read id)

reset :: Counter Unit
reset = liftFree (Reset unit)

readAndReset :: Counter Int
readAndReset = do
  current <- read
  reset
  return current
  
runCounter :: forall eff h a. 
  STRef h Int -> 
  Counter a -> 
  Eff (st :: ST h | eff) a
runCounter ref = runFree go
  where
  go (Increment a) = do
    modifySTRef ref (1 +)
    return a
  go (Read k) = map k (readSTRef ref)
  go (Reset a) = do
    writeSTRef ref 0
    return a
    
-- | The free monad transformer for `CounterF`.
    
type CounterT = FreeT CounterF

incrementT :: forall m. (Monad m) => CounterT m Unit
incrementT = liftFreeT (Increment unit)

readT :: forall m. (Monad m) => CounterT m Int
readT = liftFreeT (Read id)

resetT :: forall m. (Monad m) => CounterT m Unit
resetT = liftFreeT (Reset unit)
    
readAndResetT :: forall eff. CounterT (Eff (console :: CONSOLE | eff)) Int
readAndResetT = do
  current <- readT
  lift $ log $ "The current value is " ++ show current
  resetT
  return current
  
runCounterT :: forall eff h a. 
  STRef h Int -> 
  CounterT (Eff (st :: ST h | eff)) a -> 
  Eff (st :: ST h | eff) a
runCounterT ref = runFreeT go
  where
  go (Increment a) = do
    modifySTRef ref (1 +)
    return a
  go (Read k) = map k (readSTRef ref)
  go (Reset a) = do
    writeSTRef ref 0
    return a

main = runST do
  ref <- newSTRef 0
  runCounterT ref do
    incrementT
    incrementT
    incrementT
    readAndResetT
    after <- readT
    lift $ log $ "The final value is " ++ show after