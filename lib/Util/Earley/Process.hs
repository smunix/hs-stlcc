{-# LANGUAGE MultiWayIf      #-}
{-# LANGUAGE TemplateHaskell #-}

-- |
-- This Haskell module provides functionality for managing and manipulating
-- processes that contain elements and consumers. A process in this context is a
-- construct that holds a list of elements and a list of consumers, where
-- consumers are functions that take an element and produce a result. The module
-- offers operations to create, modify, and interact with these processes,
-- ensuring that elements can be produced and consumed efficiently.
module Util.Earley.Process where

import           Prelude hiding (consume, elem)
import           Util

-- | Data type representing a process containing elements of type 'a' and consumers of type @a -> r@.
data Process a r where
  Process ∷ {_elems ∷ [a], _consumers ∷ [a → r]} → Process a r

-- | Generate lenses for 'Process' data type.
makeLenses ''Process

-- | Instance to check if a 'Process' is empty.
instance AsEmpty (Process a r) where
  _Empty = nearly (Process Empty Empty) checkEmpty
    where
      -- \| Helper function to check if both elements and consumers lists are empty.
      checkEmpty p =
        if
          | Empty ← p ^. consumers, Empty ← p ^. elems → True
          | otherwise                                  → False

-- | Create a process from a single element.
-- Create a 'Process' with the given element and no consumers.
produce0 ∷ a → Process a r
produce0 elem = Process {_elems = [elem], _consumers = Empty}

-- | Create a process from a single consumer.
-- Create a 'Process' with the given consumer and no elements.
consume0 ∷ (a → r) → Process a r
consume0 k = Process {_elems = Empty, _consumers = [k]}

-- | Produce an element to a process, returning the new process and presentation results.
produce ∷ a → Process a r → (Process a r, [r])
produce elem p = (newProcess, results)
  where
    -- \| Create a new process with the new element added to the list of elements.
    newProcess = Process (elem : _elems p) (_consumers p)
    -- \| Apply all consumers to the new element and collect the results.
    results = map (\k → k elem) (_consumers p)

-- | Attach a consumer to a process, returning the new process and presentation results.
consume ∷ (a → r) → Process a r → (Process a r, [r])
consume k p = (newProcess, results)
  where
    -- \| Create a new process with the new consumer added to the list of consumers.
    newProcess = Process (_elems p) (k : _consumers p)
    -- \| Apply the new consumer to all existing elements and collect the results.
    results = map k (_elems p)
