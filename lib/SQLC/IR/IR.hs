{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}

module SQLC.IR.IR where

import           Bluefin
import           Bluefin.Eff
import           Bluefin.State
import           SQLC.Core
import qualified SQLC.Core     as Core
import           SQLC.Query    (Query (..))
import qualified SQLC.Query    as Query
import qualified SQLC.Term     as Term
import           Util
import Data.Map qualified as Map

data IR' r where
  ScanFile' ∷ FilePath → Id Core.Rec → r → IR' r
  Emit' ∷ Schema → Term.Record → IR' r
  If' ∷ Term.Cond → r → IR' r
  NewHTable' ∷ Id Core.Hash → r → r → IR' r
  InsHTable' ∷ Id Core.Hash → Map (Name Col) Ty → Term.Record → IR' r
  ScanHTable'
    ∷ Id Core.Hash → Map (Name Col) Ty → Name Col → Id Core.Rec → r → IR' r
  Expand' ∷ Term.Record → Name Col → Id Core.Rec → r → IR' r
  Count' ∷ Term.Record → Name Col → Name Col → Id Core.Rec → r → IR' r
  Let' ∷ Id Core.Val → Term.Value → r → IR' r
  deriving (Functor, Foldable, Show)

type IR = Fix IR'

instance View IR' IR where
  project = unFix
  inject = Fix

pattern ScanFile fp i query ← (project → ScanFile' fp i query)
  where
    ScanFile fp i query = inject do ScanFile' fp i query

pattern Emit sch record ← (project → Emit' sch record)
  where
    Emit sch record = inject do Emit' sch record

pattern If cond query ← (project → If' cond query)
  where
    If cond query = inject do If' cond query

pattern NewHTable i build scan ← (project → NewHTable' i build scan)
  where
    NewHTable i build scan = inject do NewHTable' i build scan

pattern InsHTable i cols record ← (project → InsHTable' i cols record)
  where
    InsHTable i cols record = inject do InsHTable' i cols record

pattern ScanHTable i cols tag rid query ←
  (project → ScanHTable' i cols tag rid query)
  where
    ScanHTable i cols tag rid query = inject do ScanHTable' i cols tag rid query

pattern Expand r tag rid query ← (project → Expand' r tag rid query)
  where
    Expand r tag rid query = inject do Expand' r tag rid query

pattern Count record tag countCol rid query ←
  (project → Count' record tag countCol rid query)
  where
    Count record tag countCol rid query = inject do Count' record tag countCol rid query

pattern Let i val query ← (project → Let' i val query)
  where
    Let i val query = inject do Let' i val query

data Store where
  Store ∷ {_u ∷ Int} → Store
  deriving (Eq, Show)

instance AsEmpty Store where
  _Empty = nearly (Store 0) (== Store 0)

makeLenses ''Store

ir ∷ Query → IR
ir
  q0@( schemaOf →
        sch0@(view schema → cols)
      ) = runPureEff do evalState Empty \store → lower store cols (return <. Emit sch0) q0
    where
      newId
        ∷ ∀ i st m es r
         . (m ~ Eff es, st :> es)
        ⇒ State Store st
        → FnM (Id i) m r
        → m r
      newId store kont = do
        nid ← get store
        modify store (u %~ (+ 1))
        kont (Id $ nid ^. u)

      lower
        ∷ ∀ st m es
         . (m ~ Eff es, st :> es)
        ⇒ State Store st
        → Map (Name Col) Ty
        → FnM Term.Record m IR
        → Query
        → m IR
      lower store neededCols kont = \case
        Query.ScanFile
          (toListOf (folded % filtered \(c, _) → isJust (neededCols ^? ix c)) → cols')
          fp →
            newId store \i →
              ScanFile fp i <$> withFields (Term.RecordId i) cols'
        Query.ProjectAs
          sources
          targets
          query →
            lower
              store
              (mapOf (folded % ifolded) sources)
              (rename sources targets .> kont)
              query
        Query.Filter
          pred@(schemaOf .> view schema → predSch)
          query@(schemaOf .> view schema → querySch) →
            lower
              store
              (predSch <> querySch)
              (lowerPred kont pred)
              query
        Query.Join l r → flip (lower store neededCols) l \l →
          flip (lower store neededCols) r \r → kont do
            case (l, r) of
              (Term.Record l, Term.Record r) → Term.Record (Map.intersection l r) -- FIXME: this is buggy
              (l, r)                         → Term.RecordList [l, r]
        Query.GroupBy cols@((neededCols <>) → cols') tag query →
          newId store \hid → do
            build ← lower store cols' (pure <. InsHTable hid cols) query
            scan ← newId store \rid → ScanHTable hid cols tag rid <$> kont (Term.RecordId rid)
            return do NewHTable hid build scan
        Query.Expand col query → flip (lower store neededCols) query \r →
          newId store \i →
            Expand r col i <$> kont (Term.RecordId i)
        Query.Count aggCol countCol query → flip (lower store neededCols) query \record →
          newId store \i →
            Count record aggCol countCol i <$> kont (Term.RecordId i)
        where
          lowerPred ∷ FnM Term.Record m IR → Query.Pred → FnM Term.Record m IR
          lowerPred k = cata \case
            Query.And' a b → \r →
              (,) <$> a r <*> b r >>= \case
                (If aCond _, If bCond _) → If (Term.And aCond bCond) <$> k r
                _other → error "lowerPred attempt on unconditioned IRs"
            Query.Eq' a b → \r →
              If
                ( Term.Eq
                    (unJust "failed lowerPred Eq'" (select r a))
                    (unJust "failed lowerPred Eq'" (select r b))
                )
                <$> k r
            Query.Ne' a b → \r →
              If
                ( Term.Ne
                    (unJust "failed lowerPred Ne'" (select r a))
                    (unJust "failed lowerPred Ne'" (select r b))
                )
                <$> k r
            Query.Ge' a b → \r →
              If
                ( Term.Ge
                    (unJust "failed lowerPred Ge'" (select r a))
                    (unJust "failed lowerPred Ge'" (select r b))
                )
                <$> k r
            Query.Le' a b → \r →
              If
                ( Term.Le
                    (unJust "failed lowerPred Le'" (select r a))
                    (unJust "failed lowerPred Le'" (select r b))
                )
                <$> k r

          select ∷ Term.Record → Query.Ref → Maybe Term.Value
          select record = \case
            Query.Val v → return $ Term.Value v
            Query.Fld (c, _) → case record of
              Term.Record row → row ^? ix c
              other           → Just do Term.Select c other

          rename ∷ List (Name Col, Ty) → List (Name Col, Ty) → Fn Term.Record Term.Record
          rename sources targets record = Term.Record $ toMapOf (folded % ifolded) do
            (Query.Fld → src, (tgt, _)) ← zip sources targets
            return
              ( tgt
              , unJust
                  ( "failed to rename '"
                      <> show src
                      <> "' -> '"
                      <> show tgt
                      <> "', in '"
                      <> show record
                      <> "'"
                  )
                  (select record src)
              )

          withFields
            ∷ Term.Record → [(Name Col, Ty)] → m IR
          withFields record =
            ( fix \walk mk → \case
                Empty → kont (Term.Record $ mk Empty)
                ((c, _) :< cs) → newId store \i →
                  Let i (Term.Select c record) <$> walk (mk <. (at c ?~ Term.VId i)) cs
            )
              id
