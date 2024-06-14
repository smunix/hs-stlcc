{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns    #-}

module SQLC.Term where

import           SQLC.Core hiding (Record)
import qualified SQLC.Core as Core
import           Util

-- | Boolean propositions
data Cond' r where
  And' ∷ r → r → Cond' r
  Eq' ∷ Val → Val → Cond' r
  Ne' ∷ Val → Val → Cond' r
  Ge' ∷ Val → Val → Cond' r
  Le' ∷ Val → Val → Cond' r
  deriving (Foldable, Functor, Show)

type Cond = Fix Cond'

instance View Cond' Cond where
  inject = Fix
  project = unFix

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

-- | Values
data Val where
  Val ∷ Value → Val
  VId ∷ Id Core.Val → Val
  Select ∷ Name Col → Record → Val
  deriving (Show)

-- | Record terms
data Record' r where
  RecordList' ∷ List r → Record' r
  RecordId' ∷ Id Core.Rec → Record' r
  Record' ∷ Map (Name Col) Val → Record' r
  deriving (Foldable, Functor, Show)

type Record = Fix Record'

instance View Record' Record where
  inject = Fix
  project = unFix

pattern RecordList a ← (project → RecordList' a)
  where
    RecordList a = inject $ RecordList' a

pattern RecordId i ← (project → RecordId' i)
  where
    RecordId i = inject $ RecordId' i

pattern Record m ← (project → Record' m)
  where
    Record m = inject $ Record' m
