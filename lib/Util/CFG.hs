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

class (Inv i) ⇒ Instr i where
  flowTy ∷ i → FlowTy
  label ∷ String → i
  jump ∷ String → i

class ListMap f where
  listMap ∷ (i → [j]) → f i → f j

data FlowTy where
  NoFlow ∷ FlowTy
  LabelDef ∷ String → FlowTy
  JumpSrc ∷ [String] → FlowTy
  deriving (Show)

data BBlock i where
  BBlock
    ∷ { _instrs ∷ [i]
      , _ident ∷ Int
      , _rank ∷ Int
      , _offset ∷ Int
      }
    → BBlock i
  deriving (Functor, Foldable)

newtype CFG i where
  CFG
    ∷ { _bblocks ∷ [BBlock i]
      }
    → CFG i
  deriving (Functor)

data Order i where
  Order
    ∷ { _rankO ∷ !Int
      , _tracesO ∷ ![BBlock i]
      , _nextupO ∷ ![BBlock i]
      , _availsO ∷ ![BBlock i]
      }
    → Order i

makePrisms ''FlowTy
makeLenses ''BBlock
makeLenses ''CFG
makeLenses ''Order

instance {-# OVERLAPPING #-} (Inv i) ⇒ Inv (BBlock i) where
  inv =
    instrs %~ do
      ($ id) $ fix \rec kont → \case
        Empty → kont Empty
        i :< Empty → kont $ inv i :< Empty
        i :< instrs → rec ((i :<) .> kont) instrs

instance (Instr i) ⇒ NameOf (BBlock i) where
  nameOf =
    headOf (instrs % folded)
      .> maybe
        "<label>"
        ( flowTy .> \case
            LabelDef n → n
            _other → "<label>"
        )

instance Snoc (BBlock i) (BBlock i) i i where
  _Snoc = prism' (\(bb, i) → bb & instrs %~ (:> i)) \bb@(view instrs → is) → case is of
    (is :> i)  → Just (bb & instrs .~ is, i)
    _otherwise → Empty

instance Cons (BBlock i) (BBlock i) i i where
  _Cons = prism' (\(i, bb) → bb & instrs %~ (i :<)) \bb@(view instrs → is) → case is of
    (i :< is)  → Just (i, bb & instrs .~ is)
    _otherwise → Empty

instance Snoc (CFG i) (CFG i) (BBlock i) (BBlock i) where
  _Snoc = prism' (\(CFG bbs, bb) → CFG (bbs :> bb)) \(CFG bbs) → case bbs of
    (bbs :> bb) → Just (CFG bbs, bb)
    _other      → Empty

instance Cons (CFG i) (CFG i) (BBlock i) (BBlock i) where
  _Cons = prism' (\(bb, CFG bbs) → CFG (bb :< bbs)) \(CFG bbs) → case bbs of
    (bb :< bbs) → Just (bb, CFG bbs)
    _other      → Empty

instance ListMap BBlock where
  listMap fn = instrs %~ foldMapOf folded fn

instance ListMap CFG where
  listMap fn (CFG as) = CFG (as <&> listMap fn)

instance Eq (BBlock i) where
  a == b = a ^. ident == b ^. ident

instance Ord (BBlock i) where
  a `compare` b = (a ^. rank) `compare` (b ^. rank)

new ∷ ∀ i st es. (st :> es, Instr i) ⇒ State Int st → [i] → Eff es (CFG i)
new counter is = CFG <$> walk 0 On Empty is >>= return . order
  where
    walk ∷ Int → Flag "label" → [BBlock i] → [i] → Eff es [BBlock i]
    walk !n On !bs = \case
      Empty → return bs
      (i :< is)
        | LabelDef {} ← flowTy i → walk (n + 1) Off (BBlock [i] n 0 0 :< bs) is
        | otherwise → do
            lbl ← fresh counter (label . prfx "bb")
            walk (n + 1) Off (BBlock [lbl] n 0 0 : bs) is
    walk !n Off (b :< bs) = \case
      (i :< is)
        | LabelDef lbl ← flowTy i → walk n Off (b :< bs) (jump lbl :< i :< is)
        | JumpSrc {} ← flowTy i → walk n On ((b :> i) :< bs) is
        | otherwise → walk n Off ((b :> i) :< bs) is

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

next ∷ ∀ i. (Instr i, Inv i) ⇒ Order i → Order i
next = ($ id) $ fix \rec setTrace → \case
  o@Order {_nextupO = Empty, ..} → o & tracesO .~ Empty & availsO .~ Empty
  o@Order {_nextupO = b :< Empty, _availsO = Empty, ..} → o & tracesO .~ [b & rank .~ o ^. rankO]
  o@Order {_nextupO = b :< bs, ..} → do
    let
      instrsCount, rank' ∷ Int
      instrsCount = lengthOf (instrs % folded) b
      rank' = o ^. rankO + instrsCount

      jumpLabels ∷ BBlock i → [String]
      jumpLabels (lastOf (instrs % folded) .> fmap flowTy → flow) =
        flow & maybe Empty \case
          JumpSrc lbls → lbls
          _other → Empty

      isAvail ∷ Fn String Bool
      isAvail = flip isBlockLabel _availsO

      isLive ∷ Fn String Bool
      isLive = flip isBlockLabel bs

      blockExists ∷ Fn String Bool
      blockExists = (isLive &&& isAvail) .> anyOf each (const True)

      isBlockLabel ∷ String → [BBlock i] → Bool
      isBlockLabel lbl = fmap nameOf .> elemOf folded lbl

      reorder ∷ Fn String ([BBlock i], [BBlock i])
      reorder lbl
        | isLive lbl =
            bs
              & findBy (nameOf .> (== lbl))
              & maybe
                (error $ "reorder (nextup) failed to find label: " <> lbl)
                (closePointed &&& const _availsO)
        | otherwise =
            _availsO
              & findBy (nameOf .> (== lbl))
              & maybe
                (error $ "reorder (avails) failed to find label: " <> lbl)
                (view point .> (:< bs) &&& close (const Empty))

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

      tryOrder ∷ [String] → Order i
      tryOrder = \case
        [lbl] → step id lbl Empty
        [flbl, tlbl] | blockExists tlbl → step id tlbl [flbl]
        [flbl, tlbl] | blockExists flbl → step inv flbl [tlbl]
        lbls → do
          let
            (nextups', blocks') = partition (nameOf .> flip (elemOf folded) lbls) _availsO
          Order
            { _rankO = rank'
            , _tracesO = [b & rank .~ _rankO]
            , _nextupO = o ^. nextupO <> nextups'
            , _availsO = blocks'
            }

    tryOrder (jumpLabels b)
