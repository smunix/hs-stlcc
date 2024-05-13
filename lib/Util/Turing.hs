{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}

module Util.Turing where

import           Control.Monad
import           Data.Function
import           Data.Maybe
import           Optics
import           Optics.Core.Extras (is)
import           Util.Common

data Tape a where
  Tape
    ∷ { _l ∷ [a]
      , _point ∷ a
      , _r ∷ [a]
      }
    → Tape a

makeLenses ''Tape

takeNextM ∷ Tape a → Maybe (Tape a)
takeNextM tape@(view point → curr)
  | ar :< asr ← tape ^. r = Just $ tape & l %~ (curr :<) & point .~ ar & r .~ asr
  | otherwise = Empty

takeNext ∷ Tape a → Tape a
takeNext = fromMaybe (error "tape takeNext failed") . takeNextM

nextM ∷ Tape a → Maybe (Tape a)
nextM = takeNextM

next ∷ Tape a → Tape a
next = takeNext

takePrevM ∷ Tape a → Maybe (Tape a)
takePrevM tape@(view point → curr)
  | al :< asl ← tape ^. l = Just $ tape & r %~ (curr :<) & point .~ al & l .~ asl
  | otherwise = Empty

takePrev ∷ Tape a → Tape a
takePrev = fromMaybe (error "tape takePrev failed") . takePrevM

prevM ∷ Tape a → Maybe (Tape a)
prevM = takePrevM

prev ∷ Tape a → Tape a
prev = takePrev

eos ∷ Tape a → Bool
eos = is _Empty . view r

bos ∷ Tape a → Bool
bos = is _Empty . view l

openM ∷ ∀ f a. (Foldable f) ⇒ f a → Maybe (Tape a)
openM =
  toListOf folded .> \case
    a :< as → Just $ Tape as a Empty
    _other → Empty

open ∷ ∀ f a. (Foldable f) ⇒ f a → Tape a
open = openM .> fromMaybe (error "open failed")

close ∷ ∀ a. Fn a [a] → Tape a → [a]
close currFn tape =
  tape ^. r % to inv
    <> currFn (tape ^. point)
    <> tape ^. l

update ∷ Tape a → a → Tape a
update tape = ($ tape) . (point .~)

cut ∷ Tape a → Tape a
cut tape
  | a :< _ ← tape ^. r = tape & point .~ a & r %~ drop 1
  | a :< _ ← tape ^. l = tape & point .~ a & l %~ drop 1
  | otherwise = tape

pointed = view point

closePointed ∷ Tape a → [a]
closePointed tape = tape ^. point :< (tape ^. r % to inv <> tape ^. l)

findNextBy ∷ Fn a Bool → Tape a → Maybe (Tape a)
findNextBy pred = fix \rec tape@(view point → curr) →
  if pred curr
    then Just tape
    else case nextM tape of
      Empty      → Empty
      Just tape' → rec tape'

findPrevBy ∷ Fn a Bool → Tape a → Maybe (Tape a)
findPrevBy pred = fix \rec tape@(view point → curr) →
  if pred curr
    then Just tape
    else case prevM tape of
      Empty      → Empty
      Just tape' → rec tape'

findBy ∷ Fn a Bool → [a] → Maybe (Tape a)
findBy pred = openM >=> findNextBy pred
