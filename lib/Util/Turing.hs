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

-- | The 'Tape' data structure represents a bidirectional tape with a current focus point.
data Tape a where
  Tape
    ∷ { _l ∷ [a]
      -- ^ The list of elements to the left of the focus point.
      , _point ∷ a
      -- ^ The current focus point.
      , _r ∷ [a]
      -- ^ The list of elements to the right of the focus point.
      }
    → Tape a

-- | Automatically generate lenses for the 'Tape' data structure.
makeLenses ''Tape

-- | Move the focus point to the next element, if possible, returning 'Nothing' if the tape is at the end.
-- If there is no element to the right, return 'Nothing'.
takeNextM ∷ Tape a → Maybe (Tape a)
takeNextM tape@(view point → curr)
  | ar :< asr ← tape ^. r = Just $ tape & l %~ (curr :<) & point .~ ar & r .~ asr
  -- If there is an element to the right, update the tape with the new focus point and adjusted lists.
  | otherwise = Empty

-- | Move the focus point to the next element, raising an error if the tape is at the end.
-- Attempt to move to the next element, raising an error if it fails.
takeNext ∷ Tape a → Tape a
takeNext = fromMaybe (error "tape takeNext failed") . takeNextM

-- | Alias for 'takeNextM' to provide a more concise name.
nextM ∷ Tape a → Maybe (Tape a)
nextM = takeNextM

-- | Alias for 'takeNext' to provide a more concise name.
next ∷ Tape a → Tape a
next = takeNext

-- | Move the focus point to the previous element, if possible, returning 'Nothing' if the tape is at the beginning.
takePrevM ∷ Tape a → Maybe (Tape a)
takePrevM tape@(view point → curr)
  -- If there is an element to the left, update the tape with the new focus point and adjusted lists.
  | al :< asl ← tape ^. l = Just $ tape & r %~ (curr :<) & point .~ al & l .~ asl
  -- If there is no element to the left, return 'Nothing'.
  | otherwise = Empty

-- | Move the focus point to the previous element, raising an error if the tape is at the beginning.
-- Attempt to move to the previous element, raising an error if it fails.
takePrev ∷ Tape a → Tape a
takePrev = fromMaybe (error "tape takePrev failed") . takePrevM

-- | Alias for 'takePrevM' to provide a more concise name.
prevM ∷ Tape a → Maybe (Tape a)
prevM = takePrevM

-- | Alias for 'takePrev' to provide a more concise name.
prev ∷ Tape a → Tape a
prev = takePrev

-- | Check if the tape is at the end (right side is empty).
eos ∷ Tape a → Bool
eos = is _Empty . view r

-- | Check if the tape is at the beginning (left side is empty).
bos ∷ Tape a → Bool
bos = is _Empty . view l

-- | Create a 'Tape' from a foldable collection, returning 'Nothing' if the collection is empty.
-- If the collection is empty, return 'Nothing'.
openM ∷ ∀ f a. (Foldable f) ⇒ f a → Maybe (Tape a)
openM =
  toListOf folded .> \case
    a :< as → Just $ Tape as a Empty
    -- If the collection is non-empty, create a tape with the first element as the focus point.
    _other → Empty

-- | Create a 'Tape' from a foldable collection, raising an error if the collection is empty.
-- Attempt to create a tape, raising an error if the collection is empty.
open ∷ ∀ f a. (Foldable f) ⇒ f a → Tape a
open = openM .> fromMaybe (error "open failed")

-- | Convert a 'Tape' back into a list using a function to transform the focus point.
-- Combine the reversed right side, transformed focus point, and left side into a single list.
close ∷ ∀ a. Fn a [a] → Tape a → [a]
close currFn tape =
  tape ^. r % to inv
    <> currFn (tape ^. point)
    <> tape ^. l

-- | Update the focus point of the tape with a new value.
-- Set the focus point of the tape to a new value.
update ∷ Tape a → a → Tape a
update tape = ($ tape) . (point .~)

-- | Move the focus point to the next or previous element, if possible.
cut ∷ Tape a → Tape a
cut tape
  -- If there is an element to the right, move the focus point to that element and drop it from the right list.
  | a :< _ ← tape ^. r = tape & point .~ a & r %~ drop 1
  -- If there is an element to the left, move the focus point to that element and drop it from the left list.
  | a :< _ ← tape ^. l = tape & point .~ a & l %~ drop 1
  -- If there are no elements to the left or right, keep the tape unchanged.
  | otherwise = tape

-- | Get the current focus point of the tape.
pointed ∷ Tape a → a
pointed = view point

-- | Convert a 'Tape' back into a list, with the focus point as the first element.
-- Combine the focus point and the reversed right side with the left side into a single list.
closePointed ∷ Tape a → [a]
closePointed tape = tape ^. point :< (tape ^. r % to inv <> tape ^. l)

-- | Find the next element in the tape that satisfies a predicate.
-- Recursively move to the next element until an element satisfying the predicate is found or the end is reached.
findNextBy ∷ Fn a Bool → Tape a → Maybe (Tape a)
findNextBy pred = fix \rec tape@(view point → curr) →
  if pred curr
    then Just tape
    else case nextM tape of
      Empty      → Empty
      Just tape' → rec tape'

-- | Find the previous element in the tape that satisfies a predicate.
-- Recursively move to the previous element until an element satisfying the predicate is found or the beginning is reached.
findPrevBy ∷ Fn a Bool → Tape a → Maybe (Tape a)
findPrevBy pred = fix \rec tape@(view point → curr) →
  if pred curr
    then Just tape
    else case prevM tape of
      Empty      → Empty
      Just tape' → rec tape'

-- | Find the first element in a list that satisfies a predicate and return it as a 'Tape'.
-- Convert the list to a tape and then find the next element satisfying the predicate.
findBy ∷ Fn a Bool → [a] → Maybe (Tape a)
findBy pred = openM >=> findNextBy pred
