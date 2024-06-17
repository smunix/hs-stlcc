{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ViewPatterns           #-}

module SQLC.IR.Asm where

import           Bluefin
import           Bluefin.Eff
import           Bluefin.IO
import qualified Bluefin.IO    as Io
import           Bluefin.State hiding (get, modify)
import qualified Bluefin.State as State
import           Control.Monad
import           SQLC.Core
import           SQLC.IR.IR    (IR)
import qualified SQLC.IR.IR    as IR
import qualified SQLC.Term     as Term
import           Util          hiding (bind, insert)

type HTable = Map [Value] [Record]

data Asm a where
  Pure ∷ a → Asm a
  Then ∷ Asm a → FnM a Asm b → Asm b
  Stop ∷ Asm ()
  Fail ∷ String → Asm a
  Load ∷ FilePath → Asm Table
  Trace ∷ (Show t) ⇒ t → Asm a → Asm a
  Sandbox ∷ Asm a → Asm a
  BindValue ∷ Id Val → Value → Asm ()
  BindRecord ∷ Id Rec → Record → Asm ()
  BindHTable ∷ Id Hash → HTable → Asm ()
  EvalCondition ∷ Term.Cond → Asm Bool
  EvalValue ∷ Term.Value → Asm Value
  EvalRecord ∷ Term.Record → Asm Record
  GetHTable ∷ Id Hash → Asm HTable
  ModHTable ∷ Id Hash → Fn HTable HTable → Asm ()

instance Functor Asm where fmap = liftM

instance Applicative Asm where pure = Pure; (<*>) = ap

instance Monad Asm where (>>=) = Then

instance MonadFail Asm where
  fail ∷ String → Asm a
  fail = Fail

instance (AsEmpty c) ⇒ AsEmpty (Asm c) where
  _Empty = nearly (pure Empty) undefined

stop ∷ Asm ()
stop = Stop

trace ∷ ∀ t a. (Show t) ⇒ t → Asm a → Asm a
trace = Trace

load ∷ FilePath → Asm Table
load = Load

-- | run and restore initial state
sandbox ∷ Asm a → Asm a
sandbox = Sandbox

new ∷ (Bind ref obj, AsEmpty obj) ⇒ Id ref → Asm ()
new hid = bind hid Empty

class Get ref obj | ref → obj where
  get ∷ Id ref → Asm obj

class Modify ref obj | ref → obj where
  modify ∷ Id ref → Fn obj obj → Asm ()

class Insert ref obj | ref → obj where
  insert ∷ Id ref → obj → Asm ()

class Bind ref obj | ref → obj where
  bind ∷ Id ref → obj → Asm ()

class Eval term obj | term → obj where
  eval ∷ term → Asm obj

instance Get Hash HTable where
  get = GetHTable

instance Modify Hash HTable where
  modify = ModHTable

instance Bind Rec Record where
  bind = BindRecord

instance Bind Hash HTable where
  bind = BindHTable

instance Bind Val Value where
  bind = BindValue

instance Eval Term.Record Record where
  eval = EvalRecord

instance Eval Term.Cond Bool where
  eval = EvalCondition

instance Eval Term.Value Value where
  eval = EvalValue

instance Insert Rec Record where
  insert = bind

instance Insert Val Value where
  insert = bind

instance Insert Hash (Map (Name Col) Ty, Term.Record) where
  insert hid (cols, record) = do
    record ← eval record
    Just (hkey ∷ List Value) ←
      sequence
        <$> ifoldrOf ifolded (\col _ty → fmap (record ^? fields % ix col :<)) Empty cols
    modify
      hid
      ( at hkey
          %~ \case
            Just records → Just (record :< records)
            Empty → Just [record]
      )

asm ∷ IR → Asm ()
asm = cata \case
  IR.ScanFile' fp rid query → load fp >>= traverseOf_ (recordList % traversed) (bind rid >=> const query)
  IR.Emit' sch record → sandbox (eval record) >>= flip trace stop
  IR.If' cond query →
    sandbox (eval cond) >>= \case
      True → query
      False → return ()
  IR.NewHTable' hid build scan → do
    new hid
    build
    scan
  IR.InsHTable' hid cols record → insert hid (cols, record)
  IR.ScanHTable' hid cols tag rid query →
    get hid >>= itraverseOf_ itraversed \vals records → do
      insert rid do
        Record do
          mapOf
            (folded % ifolded)
            ( zipWith
                (flip (set _2))
                ((tag, Empty) :< itoListOf ifolded cols)
                (Tbl (Table Empty records) :< vals)
            )
      query
  IR.Expand' record tag rid query → do
    record ← sandbox do eval record
    let
      Just (Tbl (Table _sch records)) = record ^. fields % at tag
    records
      & traverseOf_
        traversed
        \( ifoldrOf
            (fields % ifolded)
            (\(((tag <> ".") <>) → col) val → at col ?~ val)
            Empty
            .> Record →
            record'
          ) → do
            insert rid (record <> record')
            query
  IR.Count' record tag countCol rid query → do
    record ← sandbox do eval record
    let
      Just (Tbl (Table _sch (lengthOf folded → len))) = record ^. fields % at tag
      record' = Record do mapOf (folded % ifolded) [(countCol, Int len)]
    insert rid (record <> record')
    query
  IR.Let' vid val query → do
    val ← eval val
    insert vid val
    query

data Machine where
  Machine
    ∷ { _values ∷ Map (Id Val) Value
      , _records ∷ Map (Id Rec) Record
      , _hTables ∷ Map (Id Hash) HTable
      , _fileSystem ∷ Map FilePath String
      }
    → Machine
  deriving (Show, Eq)

instance AsEmpty Machine where
  _Empty = nearly (Machine Empty Empty Empty Empty) (== Machine Empty Empty Empty Empty)

makeLenses ''Machine

class With io st term m obj | term → obj where
  with ∷ IOE io → State Machine st → term → m obj

instance (m ~ Eff es, io :> es, st :> es) ⇒ With io st Term.Cond m Bool where
  with ∷ IOE io → State Machine st → Term.Cond → m Bool
  with io st = cata \case
    Term.And' a b → (&&) <$> a <*> b
    Term.Eq' a b → (==) <$> with io st a <*> with io st b
    Term.Ne' a b → (/=) <$> with io st a <*> with io st b
    Term.Ge' a b → (>=) <$> with io st a <*> with io st b
    Term.Le' a b → (<=) <$> with io st a <*> with io st b

instance (m ~ Eff es, io :> es, st :> es) ⇒ With io st Term.Value m Value where
  with ∷ IOE io → State Machine st → Term.Value → m Value
  with io st = \case
    Term.Value v → return v
    Term.VId reg →
      State.get st
        >>= view (values % at reg) .> \case
          Just v → return v
          Empty → effIO io do fail $ "With Term.Value: vid '" <> show reg <> "' not found"
    Term.Select col record → do
      record ← with io st record
      record ^. fields % at col & \case
        Just v → return v
        Empty → effIO io do
          fail $
            "With Term.Value: select '"
              <> show col
              <> "' not found in '"
              <> show record
              <> "'"

instance (m ~ Eff es, io :> es, st :> es) ⇒ With io st Term.Record m Record where
  with ∷ IOE io → State Machine st → Term.Record → m Record
  with io st = cata \case
    Term.RecordList' (sequence → records) → foldOf folded <$> records
    Term.RecordId' reg →
      State.get st
        >>= view (records % at reg) .> \case
          Just r → return r
          Empty → effIO io do fail $ "With Term.Record: rid '" <> show reg <> "' not found"
    Term.Record' values → Record <$> traverseOf traversed (with io st) values

exec ∷ ∀ a. Asm a → IO a
exec pgm = runEff \io → evalState (Empty @Machine) \st → walk io st pgm
  where
    walk
      ∷ ∀ a io st es m
       . (m ~ Eff es, io :> es, st :> es)
      ⇒ IOE io
      → State Machine st
      → Asm a
      → m a
    walk io st = \case
      Pure a → return a
      Then m k → walk io st m >>= (k .> walk io st)
      Stop → return ()
      Fail str → effIO io do fail str
      Load fp → return tbl
        where
          tbl = Table sch recs
          sch =
            MkSchema $
              toMapOf (folded % ifolded) [("Name", String), ("Age", I32), ("City", String)]
          recs =
            (toMapOf (folded % ifolded) .> Record)
              <$> [ [("Name", "Kinja"), ("Age", 6), ("City", "Montreal")]
                  , [("Name", "Paluku"), ("Age", 29), ("City", "Toronto")]
                  , [("Name", "Kaze"), ("Age", 11), ("City", "Vancouver")]
                  , [("Name", "Ahmed"), ("Age", 29), ("City", "Moncton")]
                  , [("Name", "Koze"), ("Age", 3), ("City", "Montreal")]
                  , [("Name", "Megan"), ("Age", 11), ("City", "Vancouver")]
                  ]
      Trace msg m → do
        effIO io do print' msg
        walk io st m
      Sandbox m → do
        mach0 ← State.get st
        r ← walk io st m
        State.put st mach0
        return r
      BindValue reg val → State.modify st (values % at reg ?~ val)
      BindRecord reg record → State.modify st (records % at reg ?~ record)
      BindHTable reg hTable → State.modify st (hTables % at reg ?~ hTable)
      EvalCondition cond → with io st cond
      EvalValue value → with io st value
      EvalRecord record → with io st record
      GetHTable reg →
        State.get st
          >>= view (hTables % at reg)
            .> maybe (effIO io do fail $ "GetHTable: id '" <> show reg <> "' not found") return
      ModHTable reg mod →
        State.modify
          st
          ( hTables
              % at reg
              %~ maybe (error $ "ModHTable: id '" <> show reg <> "' not found") (mod .> Just)
          )
