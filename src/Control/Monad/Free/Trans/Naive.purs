module Control.Monad.Free.Trans.Naive where

import Prelude

import Data.Either
import Data.Bifunctor

import Control.Bind ((<=<))
import Control.Monad.Trans

newtype FreeT f m a = FreeT (m (Either a (f (FreeT f m a))))

resumeT :: forall f m a. FreeT f m a -> m (Either a (f (FreeT f m a)))
resumeT (FreeT a) = a

liftFreeT :: forall f m a. (Functor f, Monad m) => f a -> FreeT f m a
liftFreeT = FreeT <<< return <<< Right <<< map return

runFreeT :: forall f m a. (Monad m) => (f (FreeT f m a) -> m (FreeT f m a)) -> FreeT f m a -> m a
runFreeT phi = either return ((>>= (runFreeT phi)) <<< phi) <=< resumeT

instance functorFreeT :: (Functor f, Functor m) => Functor (FreeT f m) where
  map f = FreeT <<< map (bimap f (map (map f))) <<< resumeT
  
instance applyFreeT :: (Functor f, Monad m) => Apply (FreeT f m) where
  apply = ap
  
instance bindFreeT :: (Functor f, Monad m) => Bind (FreeT f m) where
  bind (FreeT a) f = FreeT (a >>= go)
    where
    go (Left a) = resumeT (f a)
    go (Right fs) = return (Right (map (>>= f) fs))
  
instance applicativeFreeT :: (Functor f, Monad m) => Applicative (FreeT f m) where
  pure = FreeT <<< pure <<< Left
  
instance monadFreeT :: (Functor f, Monad m) => Monad (FreeT f m)

instance monadTransFreeT :: (Functor f) => MonadTrans (FreeT f) where
  lift = FreeT <<< map Left