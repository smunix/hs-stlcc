{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}

module Util.CFG where

import           Bluefin.Eff
import           Bluefin.State
import           Control.Arrow
import           Data.Function
import           Data.List
import           Data.Map           (Map)
import qualified Data.Map           as Map
import           Data.Maybe
import           Data.Set           (Set)
import qualified Data.Set           as Set
import           GHC.TypeLits
import           Optics
import           Optics.Core.Extras
import           Util.Common
import           Util.Sequence
import           Util.State
import           Util.String
import           Util.Turing        hiding (next)

-- | Instruction class with flow type and label manipulation.
class (Inv i) ⇒ Instr i where
  -- | Get the flow type of an instruction.
  flowTy ∷ i → FlowTy

  -- | Create a label instruction.
  label ∷ String → i

  -- | Create a jump instruction.
  jump ∷ String → i

-- | ListMap class for applying a function to elements inside a functor.
class ListMap f where
  -- | Apply a function to elements inside a functor and return a new functor.
  listMap ∷ (i → [j]) → f i → f j

-- | Flow type representing different kinds of control flow in a program.
data FlowTy where
  -- | No flow control.
  NoFlow ∷ FlowTy
  -- | A label definition.
  LabelDef ∷ String → FlowTy
  -- | A jump source to multiple labels.
  JumpSrc ∷ [String] → FlowTy
  deriving (Show)

-- | Basic Block data type with instructions and metadata.
data BBlock i where
  BBlock
    ∷ { _instrs ∷ [i]
      -- ^ Instructions in the block.
      , _ident ∷ Int
      -- ^ Identifier for the block.
      , _rank ∷ Int
      -- ^ Rank of the block.
      , _offset ∷ Int
      -- ^ Offset of the block.
      }
    → BBlock i
  deriving (Functor, Foldable)

-- | Control Flow Graph data type consisting of basic blocks.
newtype CFG i where
  CFG
    ∷ { _bblocks ∷ [BBlock i]
      -- ^ List of basic blocks in the CFG.
      }
    → CFG i
  deriving (Functor)

-- | Order data type used for arranging basic blocks.
data Order i where
  Order
    ∷ { _rankO ∷ !Int
      -- ^ Current rank.
      , _tracesO ∷ ![BBlock i]
      -- ^ Traced basic blocks.
      , _nextupO ∷ ![BBlock i]
      -- ^ Next basic blocks to process.
      , _availsO ∷ ![BBlock i]
      -- ^ Available basic blocks.
      }
    → Order i

-- Generate prisms and lenses for the data types.
makePrisms ''FlowTy
makeLenses ''BBlock
makeLenses ''CFG
makeLenses ''Order

-- | Instance to make BBlock obey the Inv type class, which presumably performs some form of inversion.
instance {-# OVERLAPPING #-} (Inv i) ⇒ Inv (BBlock i) where
  inv =
    instrs %~ do
      ($ id) $ fix \rec kont → \case
        Empty → kont Empty
        i :< Empty → kont $ inv i :< Empty
        i :< instrs → rec ((i :<) .> kont) instrs

-- | Instance to derive the name of a BBlock, assuming the name is the first label instruction found.
instance (Instr i) ⇒ NameOf (BBlock i) where
  nameOf =
    headOf (instrs % folded)
      .> maybe
        "<label>"
        ( flowTy .> \case
            LabelDef n → n
            _other → "<label>"
        )

-- | Instance to handle snoc (append) operations on BBlock.
instance Snoc (BBlock i) (BBlock i) i i where
  _Snoc = prism' (\(bb, i) → bb & instrs %~ (:> i)) \bb@(view instrs → is) → case is of
    (is :> i)  → Just (bb & instrs .~ is, i)
    _otherwise → Empty

-- | Instance to handle cons (prepend) operations on BBlock.
instance Cons (BBlock i) (BBlock i) i i where
  _Cons = prism' (\(i, bb) → bb & instrs %~ (i :<)) \bb@(view instrs → is) → case is of
    (i :< is)  → Just (i, bb & instrs .~ is)
    _otherwise → Empty

-- | Instance to handle snoc (append) operations on CFG.
instance Snoc (CFG i) (CFG i) (BBlock i) (BBlock i) where
  _Snoc = prism' (\(CFG bbs, bb) → CFG (bbs :> bb)) \(CFG bbs) → case bbs of
    (bbs :> bb) → Just (CFG bbs, bb)
    _other      → Empty

-- | Instance to handle cons (prepend) operations on CFG.
instance Cons (CFG i) (CFG i) (BBlock i) (BBlock i) where
  _Cons = prism' (\(bb, CFG bbs) → CFG (bb :< bbs)) \(CFG bbs) → case bbs of
    (bb :< bbs) → Just (bb, CFG bbs)
    _other      → Empty

-- | ListMap instance for BBlock to apply a function to its instructions.
instance ListMap BBlock where
  listMap fn = instrs %~ foldMapOf folded fn

-- | ListMap instance for CFG to apply a function to its basic blocks.
instance ListMap CFG where
  listMap fn (CFG as) = CFG (as <&> listMap fn)

-- | Equality instance for BBlock based on its identifier.
instance Eq (BBlock i) where
  a == b = a ^. ident == b ^. ident

-- | Ordering instance for BBlock based on its rank.
instance Ord (BBlock i) where
  a `compare` b = (a ^. rank) `compare` (b ^. rank)

-- | Create a new CFG from a list of instructions.
new ∷ ∀ i st es. (st :> es, Instr i) ⇒ State Int st → [i] → Eff es (CFG i)
new counter is = CFG <$> walk 0 On Empty is >>= return . order
  where
    -- \| Walk through the instructions to create basic blocks.
    walk ∷ Int → Flag "label" → [BBlock i] → [i] → Eff es [BBlock i]
    walk !n On !bs = \case
      Empty → return bs
      (i :< is)
        -- If a label is found, create a new basic block.
        | LabelDef {} ← flowTy i → walk (n + 1) Off (BBlock [i] n 0 0 :< bs) is
        -- Otherwise, create a new basic block with a generated label.
        | otherwise → do
            lbl ← fresh counter (label . prfx "bb")
            walk (n + 1) Off (BBlock [lbl] n 0 0 : bs) is
    -- \| Continue processing instructions when not on a label.
    walk !n Off (b :< bs) = \case
      (i :< is)
        -- If a label is found, create a jump and continue with the label.
        | LabelDef lbl ← flowTy i → walk n Off (b :< bs) (jump lbl :< i :< is)
        -- If a jump source is found, process the block and continue.
        | JumpSrc {} ← flowTy i → walk n On ((b :> i) :< bs) is
        -- Otherwise, continue processing the current block.
        | otherwise → walk n Off ((b :> i) :< bs) is

-- | Order the basic blocks in the CFG based on their ranks and instructions.
order ∷ ∀ i. (Instr i) ⇒ CFG i → CFG i
order (view bblocks → bs) =
  CFG $
    foldOf folded $
      unfold
        (view tracesO)
        next
        (is _Empty . view nextupO)
        (Order 0 Empty [bb0] bs')
  where
    (bb0 : bs') =
      closePointed $
        fromMaybe (error "failed to find bblock id 0") $
          findBy ((== 0) . view rank) bs

-- | Process the next order of basic blocks.
next ∷ ∀ i. (Instr i, Inv i) ⇒ Order i → Order i
next = ($ id) $ fix \rec setTrace → \case
  o@Order {_nextupO = Empty, ..} → o & tracesO .~ Empty & availsO .~ Empty
  o@Order {_nextupO = b :< Empty, _availsO = Empty, ..} → o & tracesO .~ [b & rank .~ o ^. rankO]
  o@Order {_nextupO = b :< bs, ..} → do
    let
      -- \| Calculate the number of instructions and update the rank.
      instrsCount, rank' ∷ Int
      instrsCount = lengthOf (instrs % folded) b
      rank' = o ^. rankO + instrsCount

      -- \| Extract the labels of jump targets from the last instruction in a block.
      jumpLabels ∷ BBlock i → [String]
      jumpLabels (lastOf (instrs % folded) .> fmap flowTy → flow) =
        flow & maybe Empty \case
          JumpSrc lbls → lbls
          _other → Empty

      -- \| Check if a label is available in the available blocks.
      isAvail ∷ Fn String Bool
      isAvail = flip isBlockLabel _availsO

      -- \| Check if a label is live in the next blocks to process.
      isLive ∷ Fn String Bool
      isLive = flip isBlockLabel bs

      -- \| Check if a block with a given label exists in either the live or available blocks.
      blockExists ∷ Fn String Bool
      blockExists = (isLive &&& isAvail) .> anyOf each (const True)

      -- \| Check if a label is present in a list of blocks.
      isBlockLabel ∷ String → [BBlock i] → Bool
      isBlockLabel lbl = fmap nameOf .> elemOf folded lbl

      -- \| Reorder the blocks to bring a specific label to the front.
      reorder ∷ Fn String ([BBlock i], [BBlock i])
      reorder lbl
        -- If the label is live, find it in the live blocks and move it to the front.
        | isLive lbl =
            bs
              & findBy (nameOf .> (== lbl))
              & maybe
                (error $ "reorder (nextup) failed to find label: " <> lbl)
                (closePointed &&& const _availsO)
        -- If the label is not live, find it in the available blocks and move it to the front.
        | otherwise =
            _availsO
              & findBy (nameOf .> (== lbl))
              & maybe
                (error $ "reorder (avails) failed to find label: " <> lbl)
                (view point .> (:< bs) &&& close (const Empty))

      -- \| Update the order with a modified block, updating next up and available blocks.
      step ∷ Fn (BBlock i) (BBlock i) → String → [String] → Order i
      step modBBlock lbl lbls = do
        let
          (nextups', avails') = reorder lbl
          (nextups'', avails'') = partition (nameOf .> flip (elemOf folded) lbls) avails'
        o
          & rankO .~ rank'
          & tracesO .~ Empty
          & nextupO .~ (nextups' <> nextups'')
          & availsO .~ avails''
          & rec ((tracesO %~ ((b & modBBlock & rank .~ _rankO) :<)) .> setTrace)

      -- \| Attempt to order the blocks by labels, updating the order state accordingly.
      tryOrder ∷ [String] → Order i
      tryOrder = \case
        -- Single label case: simply step with that label.
        [lbl] → step id lbl Empty
        -- Two labels: prioritize target label if it exists, otherwise fallback to from label.
        [flbl, tlbl] | blockExists tlbl → step id tlbl [flbl]
        [flbl, tlbl] | blockExists flbl → step inv flbl [tlbl]
        -- Multiple labels: partition and update nextup and available blocks.
        lbls → do
          let
            (nextups', blocks') = partition (nameOf .> flip (elemOf folded) lbls) _availsO
          Order
            { _rankO = rank'
            , _tracesO = [b & rank .~ _rankO]
            , _nextupO = o ^. nextupO <> nextups'
            , _availsO = blocks'
            }

    -- Attempt to order the blocks using the jump labels from the current block.
    tryOrder (jumpLabels b)
