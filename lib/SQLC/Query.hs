{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns    #-}

module SQLC.Query where

import           Data.String
import           SQLC.Core   hiding (Val)
import qualified SQLC.Core   as Core
import qualified SQLC.Term   as Term
import           Util

data Pred' r where
  And' ∷ r → r → Pred' r
  Eq' ∷ Ref → Ref → Pred' r
  Ne' ∷ Ref → Ref → Pred' r
  Ge' ∷ Ref → Ref → Pred' r
  Le' ∷ Ref → Ref → Pred' r
  deriving (Functor, Foldable, Show)

type Pred = Fix Pred'

instance View Pred' Pred where
  project = unFix
  inject = Fix

instance SchemaOf Pred where
  schemaOf = cata \case
    And' a b → a <> b
    Eq' a b → schemaOf a <> schemaOf b
    Ne' a b → schemaOf a <> schemaOf b
    Ge' a b → schemaOf a <> schemaOf b
    Le' a b → schemaOf a <> schemaOf b

pattern And a b ← (project → And' a b)
  where
    And a b = inject $ And' a b

pattern Eq a b ← (project → Eq' a b)
  where
    Eq a b = inject $ Eq' a b

pattern Ne a b ← (project → Ne' a b)
  where
    Ne a b = inject $ Ne' a b

pattern Ge a b ← (project → Ge' a b)
  where
    Ge a b = inject $ Ge' a b

pattern Le a b ← (project → Le' a b)
  where
    Le a b = inject $ Le' a b

data Ref where
  Val ∷ Value → Ref
  Fld ∷ (Name Col, Ty) → Ref
  deriving (Show)

instance IsString Ref where
  fromString = fromString .> (,Hole) .> Fld

instance SchemaOf Ref where
  schemaOf = \case
    Val {} → Empty -- FIXME: use error "Empty" instead?
    Fld c → MkSchema $ toMapOf (folded % ifolded) [c]

data Query' r where
  ScanFile' ∷ {columns ∷ List (Name Col, Ty), fp ∷ FilePath} → Query' r
  ProjectAs'
    ∷ { sources ∷ List (Name Col, Ty)
      , targets ∷ List (Name Col, Ty)
      , query ∷ r
      }
    → Query' r
  Filter' ∷ Pred → r → Query' r
  Join' ∷ r → r → Query' r
  HashJoin' ∷ Map (Name Col) Ty → List (Name Col) → r → Query' r
  GroupBy' ∷ Map (Name Col) Ty → Name Col → r → Query' r
  Expand' ∷ Name Col → r → Query' r
  Count' ∷ Name Col → Name Col → r → Query' r
  deriving (Functor, Foldable, Show)

type Query = Fix Query'

instance View Query' Query where
  project = unFix
  inject = Fix

instance SchemaOf Query where
  schemaOf ∷ Query → Schema
  schemaOf = cata \case
    ScanFile' {columns} → schemaOf columns
    ProjectAs' {sources, targets, query} → schemaOf do
      ((s, _), (t, _)) ← zip sources targets
      let
        Just ty = tys ^? ix s
      return (t, ty)
      where
        tys ∷ Map (Name Col) Ty
        tys =
          query ^. (coerced @_ @(Map (Name Col) Ty))
    Filter' p r → r
    Join' a b → schemaOf (Combine a b)
    HashJoin' {} → undefined
    GroupBy' cols0 col query → schemaOf $ Combine cols (Sub col query)
      where
        cols = schemaOf do
          (col, _) ← itoListOf ifolded cols0
          let
            Just ty = tys ^? ix col
          return (col, ty)
        tys ∷ Map (Name Col) Ty
        tys =
          query ^. schema
    Expand' col sch → schemaOf $ Combine sch (Unfold col sch)
    Count' _agg col0 query → schemaOf $ Combine query col
      where
        col = schemaOf do
          c ← [col0]
          let
            Just ty = tys ^? ix c
          return (c, ty)

        tys ∷ Map (Name Col) Ty
        tys =
          query ^. (coerced @_ @(Map (Name Col) Ty))

pattern ScanFile cols fp ← (project → ScanFile' cols fp)
  where
    ScanFile cols fp = inject do ScanFile' cols fp

pattern ProjectAs sources aliases query ← (project → ProjectAs' sources aliases query)
  where
    ProjectAs sources aliases query = inject do ProjectAs' sources aliases query

pattern Filter pred q ← (project → Filter' pred q)
  where
    Filter pred q = inject do Filter' pred q

pattern Join l r ← (project → Join' l r)
  where
    Join l r = inject do Join' l r

pattern HashJoin as bs q ← (project → HashJoin' as bs q)
  where
    HashJoin as bs q = inject do HashJoin' as bs q

pattern GroupBy cols col q ← (project → GroupBy' cols col q)
  where
    GroupBy cols col q = inject do GroupBy' cols col q

pattern Expand col q ← (project → Expand' col q)
  where
    Expand col q = inject do Expand' col q

pattern Count a b q ← (project → Count' a b q)
  where
    Count a b q = inject do Count' a b q
