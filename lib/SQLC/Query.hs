{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE ViewPatterns      #-}

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

data Query' q where
  ScanFile' ∷ {columns ∷ List (Name Col, Ty), fp ∷ FilePath} → Query' q
  ProjectAs'
    ∷ { sources ∷ List (Name Col, Ty)
      , targets ∷ List (Name Col, Ty)
      , query ∷ q
      }
    → Query' q
  Filter' ∷ Pred → q → Query' q
  Join' ∷ q → q → Query' q
  HashJoin' ∷ Map (Name Col) Ty → List (Name Col) → q → Query' q
  GroupBy' ∷ Map (Name Col) Ty → Name Col → q → Query' q
  Expand' ∷ Name Col → q → Query' q
  Count' ∷ Name Col → Name Col → q → Query' q
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
    Count' tag countCol query → schemaOf $ Combine query col
      where
        col = schemaOf do
          c ← [countCol]
          let
            Just ty = tys ^? ix tag
          return (c, ty)

        tys ∷ Map (Name Col) Ty
        tys =
          query ^. (coerced @_ @(Map (Name Col) Ty))

pattern ScanFile cols fp ← (project → ScanFile' cols fp)
  where
    ScanFile cols fp = inject do ScanFile' cols fp

pattern ProjectAs sources targets query ← (project → ProjectAs' sources targets query)
  where
    ProjectAs sources targets query = inject do ProjectAs' sources targets query

pattern Filter pred query ← (project → Filter' pred query)
  where
    Filter pred query = inject do Filter' pred query

pattern Join l r ← (project → Join' l r)
  where
    Join l r = inject do Join' l r

pattern HashJoin as bs query ← (project → HashJoin' as bs query)
  where
    HashJoin as bs query = inject do HashJoin' as bs query

pattern GroupBy cols col query ← (project → GroupBy' cols col query)
  where
    GroupBy cols col query = inject do GroupBy' cols col query

pattern Expand col query ← (project → Expand' col query)
  where
    Expand col query = inject do Expand' col query

pattern Count tag countCol query ← (project → Count' tag countCol query)
  where
    Count tag countCol query = inject do Count' tag countCol query

as ∷ Name Col → Query → Query
as tag = para \case
  ProjectAs'
    { sources = sources
    , targets = targets
    , query = query
    } → ProjectAs sources (prependCol tag <$> targets) (query ^. _2)
  Filter' (prependPred tag → pred) query → Filter pred (query ^. _2)
  query → inject $ fst <$> query
  where
    prependCol ∷ () ⇒ Name Col → (Name Col, d) → (Name Col, d)
    prependCol tag = first ((tag <> ".") <>)

    prependPred ∷ Name Col → Pred → Pred
    prependPred tag = cata \case
      Eq' (prepend → a) (prepend → b) → Eq a b
      Ne' (prepend → a) (prepend → b) → Ne a b
      Ge' (prepend → a) (prepend → b) → Ge a b
      Le' (prepend → a) (prepend → b) → Le a b
      p → inject p
      where
        prepend = \case
          Fld (prependCol tag → fld) → Fld fld
          ref → ref

    prependQuery ∷ () ⇒ Name Col → Query → Query
    prependQuery tag = cata \case
      Filter' (prependPred tag → pred) q → inject $ Filter' pred q
      q → inject q
