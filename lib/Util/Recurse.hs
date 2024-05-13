{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}

module Util.Recurse (module Util.Recurse, (&&&)) where

import           Control.Arrow
import           Data.Function
import           Util.Common

class View f a where
  project ∷ a → f a
  inject ∷ f a → a

newtype Fix f where
  Fix ∷ {unFix ∷ f (Fix f)} → Fix f

instance (Eq (f (Fix f))) ⇒ Eq (Fix f) where
  (unFix → fa) == (unFix → fb) = fa == fb

instance (Ord (f (Fix f))) ⇒ Ord (Fix f) where
  (unFix → fa) `compare` (unFix → fb) = fa `compare` fb

cata ∷ (Functor f) ⇒ (f a → a) → Fix f → a
cata alg = fix \rec → unFix .> fmap rec .> alg

cataM ∷ (Monad m, Traversable f) ⇒ FnM (f a) m a → Fix f → m a
cataM algM = fix \rec → (unFix .> traverseOf traversed rec) >.> algM

para ∷ (Functor f) ⇒ Fn (f (a, Fix f)) a → Fix f → a
para phi = fix \rec → unFix .> fmap (rec &&& id) .> phi

ana ∷ (Functor f) ⇒ Fn a (f a) → a → Fix f
ana coalg = fix \rec → coalg .> fmap rec .> Fix
