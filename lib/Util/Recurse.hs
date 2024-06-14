{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}

module Util.Recurse (module Util.Recurse, (&&&)) where

import           Control.Arrow
import           Data.Function
import           Util.Common

class View f a | f → a where
  project ∷ a → f a
  inject ∷ f a → a

newtype Fix f where
  Fix ∷ {unFix ∷ f (Fix f)} → Fix f

deriving newtype instance (Eq (f (Fix f))) ⇒ Eq (Fix f)

deriving newtype instance (Ord (f (Fix f))) ⇒ Ord (Fix f)

deriving newtype instance (Show (f (Fix f))) ⇒ Show (Fix f)

cata ∷ (Functor f) ⇒ (f a → a) → Fix f → a
cata alg = fix \rec → unFix .> fmap rec .> alg

cataM ∷ (Monad m, Traversable f) ⇒ FnM (f a) m a → Fix f → m a
cataM algM = fix \rec → (unFix .> traverseOf traversed rec) >.> algM

para ∷ (Functor f) ⇒ Fn (f (Fix f, a)) a → Fix f → a
para phi = fix \rec → unFix .> fmap (id &&& rec) .> phi

ana ∷ (Functor f) ⇒ Fn a (f a) → a → Fix f
ana coalg = fix \rec → coalg .> fmap rec .> Fix
