{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE UndecidableInstances   #-}

module Util.Common (module Util.Common, module X) where

import           Control.Applicative as X
import           Control.Arrow       as X
import           Control.Monad       as X
import           Data.Function       as X
import           Data.Kind           as X
import           Data.List           as X hiding (group, groupBy, uncons,
                                           unsnoc)
import           Data.Maybe          as X
import           Data.Semigroup
import           Data.Word           as X
import           GHC.Generics
import           GHC.TypeLits
import           Optics              as X

type Pos = (Int, Int)

class Inv a where
  inv ∷ a → a

class NameOf a where
  nameOf ∷ a → String

-- | Annotations
class Ann f a | f → a where
  ann ∷ Lens' f a
  anns ∷ Getter f [a]

data Flag (s ∷ Symbol)
  = Off
  | On
  deriving (Show)

newtype Pair a b = Pair (a, b)
  deriving
    ( Applicative
    , Eq
    , Foldable
    , Functor
    , Generic
    , Monad
    , Ord
    , Show
    )

type Fn a b = a → b

type FnM a m b = a → m b

instance Field1 (Pair a b) (Pair a' b) a a' where
  _1 =
    lens
      (view $ coerced @(Pair a b) @(a, b) % _1)
      (\pair a → pair & (coerced @(Pair a b) @(a, b) % _1 .~ a) & Pair)

instance Field2 (Pair a b) (Pair a b') b b' where
  _2 =
    lens
      (view $ coerced @(Pair a b) @(a, b) % _2)
      (\pair b → pair & (coerced @(Pair a b) @(a, b) % _2 .~ b) & Pair)

instance Field1 (Arg a b) (Arg a' b) a a'

instance Field2 (Arg a b) (Arg a b') b b'

instance (Cons (f a) (f a) a a, AsEmpty (f a)) ⇒ Inv (f a) where
  inv = rev
    where
      rev ∷ (Cons (f a) (f a) a a, AsEmpty (f a)) ⇒ f a → f a
      rev = ($ id) $ fix \rec kont → \case
        Empty → kont Empty
        a :< as → rec (kont <. (a :<)) as

pattern MkPair ∷ a → b → Pair a b
pattern MkPair a b ← Pair (a, b)
  where
    MkPair a b = Pair (a, b)

(.>) ∷ Fn a b → Fn b c → Fn a c
(.>) = flip (.)

(<.) ∷ Fn b c → Fn a b → Fn a c
(<.) = (.)

(>.>) ∷ (Monad m) ⇒ FnM a m b → FnM b m c → FnM a m c
(>.>) = (>=>)

(<.<) ∷ (Monad m) ⇒ FnM b m c → FnM a m b → FnM a m c
(<.<) = (<=<)
