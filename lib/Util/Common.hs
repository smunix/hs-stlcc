{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ViewPatterns           #-}

module Util.Common (module Util.Common, module X) where

import           Control.Applicative as X
import           Control.Arrow       as X
import           Control.Monad       as X
import           Data.Function       as X
import qualified Data.IntMap.Optics  as IntMap
import           Data.IntMap.Strict  (IntMap)
import           Data.Kind           as X
import           Data.List           as X hiding (group, groupBy, uncons,
                                           unsnoc)
import           Data.Map            as X (Map)
import           Data.Map.Optics     as X (toMapOf)
import           Data.Maybe          as X
import           Data.Semigroup
import           Data.Set            as X (Set)
import           Data.Set.Optics     as X (setOf)
import           Data.Word           as X
import           GHC.Generics        hiding (to)
import           GHC.TypeLits
import           Optics              as X

type Pos = (Int, Int)

class Inv a where
  inv ∷ a → a

type family MapOfT i where
  MapOfT Int = IntMap
  MapOfT i = Map i

class MapOf_ m i a where
  mapOf_
    ∷ (k `Is` A_Fold, is `HasSingleIndex` i, Ord i) ⇒ Optic' k is s a → s → m a
  default mapOf_
    ∷ (k `Is` A_Fold, is `HasSingleIndex` i, Ord i, m ~ Map i)
    ⇒ Optic' k is s a
    → s
    → m a
  mapOf_ = toMapOf

instance MapOf_ IntMap Int a where
  mapOf_
    ∷ (k `Is` A_Fold, is `HasSingleIndex` i, i ~ Int, m ~ IntMap)
    ⇒ Optic' k is s a
    → s
    → m a
  mapOf_ = IntMap.toMapOf

mapOf
  ∷ ∀ k is i s a
   . (k `Is` A_Fold, is `HasSingleIndex` i, Ord i, MapOf_ (MapOfT i) i a)
  ⇒ Optic' k is s a
  → s
  → MapOfT i a
mapOf = mapOf_ @(MapOfT i)

class NameOf a where
  nameOf ∷ a → String

-- | Annotations
class Ann f a | f → a where
  ann ∷ Lens' f a
  anns ∷ Getter f [a]
  anns = to (view ann .> pure)

instance Ann (Note a x) a where
  ann = _1

data Flag (s ∷ Symbol)
  = Off
  | On
  deriving (Show)

newtype Note a b = Note (a, b)
  deriving
    ( Applicative
    , Foldable
    , Functor
    , Generic
    , Monad
    , Show
    )

instance (Eq a) ⇒ Eq (Note n a) where
  (view _2 → a) == (view _2 → b) = a == b

instance (Ord a) ⇒ Ord (Note n a) where
  (view _2 → a) `compare` (view _2 → b) = a `compare` b

type Fn a b = a → b

type FnM a m b = a → m b

instance Field1 (Note a b) (Note a' b) a a' where
  _1 =
    lens
      (view $ coerced @(Note a b) @(a, b) % _1)
      (\pair a → pair & (coerced @(Note a b) @(a, b) % _1 .~ a) & Note)

instance Field2 (Note a b) (Note a b') b b' where
  _2 =
    lens
      (view $ coerced @(Note a b) @(a, b) % _2)
      (\pair b → pair & (coerced @(Note a b) @(a, b) % _2 .~ b) & Note)

instance Field1 (Arg a b) (Arg a' b) a a'

instance Field2 (Arg a b) (Arg a b') b b'

instance (Cons (f a) (f a) a a, AsEmpty (f a)) ⇒ Inv (f a) where
  inv = rev
    where
      rev ∷ (Cons (f a) (f a) a a, AsEmpty (f a)) ⇒ f a → f a
      rev = ($ id) $ fix \rec kont → \case
        Empty → kont Empty
        a :< as → rec (kont <. (a :<)) as

pattern MkNote ∷ a → b → Note a b
pattern MkNote a b ← Note (a, b)
  where
    MkNote a b = Note (a, b)

(.>) ∷ Fn a b → Fn b c → Fn a c
(.>) = flip (.)

(<.) ∷ Fn b c → Fn a b → Fn a c
(<.) = (.)

(>.>) ∷ (Monad m) ⇒ FnM a m b → FnM b m c → FnM a m c
(>.>) = (>=>)

(<.<) ∷ (Monad m) ⇒ FnM b m c → FnM a m b → FnM a m c
(<.<) = (<=<)
