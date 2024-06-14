{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RoleAnnotations    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE ViewPatterns       #-}

module SQLC.Core where

import           Data.String
import           Util        hiding (Index)

type List a = [a]

data Dom where
  Col ∷ Dom

data DomId where
  Rec ∷ DomId
  Val ∷ DomId
  Hash ∷ DomId

newtype Name (n ∷ Dom) where
  Name ∷ String → Name n
  deriving newtype (Show, Eq, Ord, IsString, Semigroup, Monoid)

type role Name phantom

newtype Index (i ∷ Dom) where
  Index ∷ Int → Index i
  deriving newtype (Show, Eq, Ord)

type role Index phantom

newtype Id (i ∷ DomId) where
  Id ∷ Int → Id i
  deriving newtype (Show, Eq, Ord)

type role Id phantom

data Ty where
  Hole ∷ Ty
  I32 ∷ Ty
  String ∷ Ty
  Schema ∷ Schema → Ty
  deriving (Show, Eq, Ord)

instance AsEmpty Ty where
  _Empty = nearly Hole (== Hole)

instance IsString (Name Col, Ty) where
  fromString = fromString .> (,Hole)

newtype Schema where
  MkSchema ∷ {_schema ∷ Map (Name Col) Ty} → Schema
  deriving newtype (Show, Eq, Ord, Monoid, Semigroup)

instance MapOf_ (Map (Name Col)) (Name Col) a

class SchemaOf a where
  schemaOf ∷ a → Schema

data Value where
  Int ∷ Int → Value
  Str ∷ String → Value
  Tbl ∷ Table → Value
  deriving (Eq, Ord, Show)

instance IsString Value where
  fromString = Str

instance Num Value where
  fromInteger = fromInteger .> Int
  (+) ∷ Value → Value → Value
  (+) = error "Num Value does not implement '(+)'"
  (*) ∷ Value → Value → Value
  (*) = error "Num Value does not implement '(*)'"
  abs ∷ Value → Value
  abs = error "Num Value does not implement 'abs'"
  signum ∷ Value → Value
  signum = error "Num Value does not implement 'signum'"
  negate ∷ Value → Value
  negate = error "Num Value does not implement 'negate'"

newtype Record where
  Record ∷ {_fields ∷ Map (Name Col) Value} → Record
  deriving newtype (Eq, Ord, Show, Monoid, Semigroup)

data Table where
  Table
    ∷ { _description ∷ Schema
      , _recordList ∷ List Record
      }
    → Table
  deriving (Eq, Ord, Show)

data Combine a b where
  Combine ∷ a → b → Combine a b
  deriving (Eq, Show)

data Sub b where
  Sub ∷ Name Col → b → Sub b
  deriving (Eq, Show)

data Unfold b where
  Unfold ∷ Name Col → b → Unfold b
  deriving (Eq, Show)

makeLenses ''Record
makeLenses ''Schema
makePrisms ''Value
makePrisms ''Ty
makeLenses ''Table

instance AsEmpty Record where
  _Empty = nearly (Record Empty) (== Record Empty)

instance AsEmpty Schema where
  _Empty = nearly (MkSchema Empty) (view schema .> is _Empty)

instance SchemaOf Schema where
  schemaOf = id

instance SchemaOf (List (Name Col, Ty)) where
  schemaOf = MkSchema <. toMapOf (folded % ifolded)

instance (SchemaOf a, SchemaOf b) ⇒ SchemaOf (Combine a b) where
  schemaOf (Combine (schemaOf → a) (schemaOf → b)) = a <> b

instance () ⇒ SchemaOf (Sub Schema) where
  schemaOf (Sub c sch) = MkSchema $ toMapOf (folded % ifolded) [(c, Schema sch)]

instance () ⇒ SchemaOf (Unfold Schema) where
  schemaOf
    ( Unfold
        c0
        (MkSchema (preview (ix c0) .> fmap (c0,) → def))
      )
      | Just
          ( _
            , Schema
                ( MkSchema
                    ( itoListOf ifolded
                        .> fmap (first \c → c0 <> Name "." <> c)
                        .> mapOf (folded % ifolded)
                        .> MkSchema →
                        sch'
                      )
                  )
            ) ←
          def =
          sch'
      | Just r ← def =
          error $ "unfold schema expected a schema, but found: " <> show r
      | Nothing ← def = error $ "unfold schema failed to find: " <> show c0
