module Control.Monad.Free.Naive where

import Prelude

import Data.Either
import Data.Bifunctor

newtype Free f a = Free (Either a (f (Free f a)))

resume :: forall f a. Free f a -> Either a (f (Free f a))
resume (Free a) = a

runFree :: forall f m a. (Monad m) => (f (Free f a) -> m (Free f a)) -> Free f a -> m a
runFree phi = either return ((>>= (runFree phi)) <<< phi) <<< resume

liftFree :: forall f a. (Functor f) => f a -> Free f a
liftFree = Free <<< Right <<< map return

instance functorFree :: (Functor f) => Functor (Free f) where
  map f = Free <<< bimap f (map (map f)) <<< resume
  
instance applyFree :: (Functor f) => Apply (Free f) where
  apply = ap
  
instance bindFree :: (Functor f) => Bind (Free f) where
  bind (Free (Left a)) f = f a
  bind (Free (Right fs)) f = Free (Right (map (>>= f) fs))
  
instance applicativeFree :: (Functor f) => Applicative (Free f) where
  pure = Free <<< Left
  
instance monadFree :: (Functor f) => Monad (Free f)