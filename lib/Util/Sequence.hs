{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE MultiWayIf   #-}
{-# LANGUAGE ViewPatterns #-}

module Util.Sequence where

import           Control.Arrow
import           Data.Function
import           Data.List     (intercalate, intersperse)
import           Data.Map      (Map)
import qualified Data.Map      as Map
import           Data.Maybe
import           Data.Set      (Set)
import qualified Data.Set      as Set
import           Optics
import           Util.Common

names ∷ [String]
names = shorts <> ["t" <> show i | i ← [0 ..]]
  where
    shorts = map pure ['a' .. 'z']

insertBatch ∷ (Ord k) ⇒ Map k v → [(k, v)] → Map k v
insertBatch = foldrOf folded \(k, v) m → m & at k .~ Just v

deleteAll ∷ (Ord a) ⇒ [a] → Set a → Set a
deleteAll = flip (foldrOf folded sans)

unique ∷ ∀ a. (Ord a) ⇒ [a] → [a]
unique = Set.toList . Set.fromList

count ∷ Fn a Bool → [a] → Int
count pred = ($ id) $ fix \rec fn → \case
  [] → fn 0
  ((fromEnum . pred → v) : as) → rec (\n → fn (n + v)) as

uj ∷ Maybe a → a
uj (Just a) = a

suj ∷ String → Maybe a → a
suj s = maybe (error s) id

duj ∷ a → Maybe a → a
duj = flip maybe id

shead ∷ String → [a] → a
shead s = \case
  [] → error s
  (a : _) → a

mhead ∷ [a] → Maybe a
mhead = headOf folded

rtail ∷ [a] → [a]
rtail = inv . (\case Empty → Empty; (_ : as) → as) . inv

choice ∷ Maybe a → Either a ()
choice = maybe (Right ()) Left

meither ∷ Fn a b → b → Maybe a → b
meither = flip maybe

meitherM ∷ (Monad m) ⇒ FnM a m b → m b → m (Maybe a) → m b
meitherM fn d = (>>= meither fn d)

choose ∷ a → Maybe a → a
choose = fromMaybe

spani ∷ (Num n) ⇒ Fn a (Fn n Bool) → [a] → ([a], [a])
spani pred = ($ (0, id)) $ uncurry $ fix \rec !n ctor → \case
  as@[] → (ctor as, as)
  (a : as) →
    if pred a n
      then rec (n + 1) (ctor . (a :)) as
      else (ctor [], as)

splitn ∷ Int → [a] → ([a], [a])
splitn n = spani (const (< n))

taken ∷ Int → [a] → Maybe [a]
taken n = walk 0 id
  where
    walk !i ctor = \case
      as@[] → ctor Empty
      (a : as) →
        if i == n
          then ctor (Just [])
          else walk (i + 1) (maybe Empty (Just . (a :))) as

windown ∷ Fn [a] [[a]] → Int → [a] → [[a]]
windown end n = fix \rec → \case
  [] → []
  as@(a : as') → case taken n as of
    Just xs → xs : rec as'
    Empty   → end as

subSeqs ∷ Fn [a] [[a]] → Int → [a] → [[a]]
subSeqs = windown

chunksn ∷ Fn [a] [[a]] → Int → [a] → [[a]]
chunksn end n = fix \rec as →
  case taken n as of
    Just xs → xs : rec (drop n as)
    Empty   → end as

isPrefix ∷ (Eq a) ⇒ [a] → [a] → Bool
isPrefix = startsWith

startsWith ∷ (Eq a) ⇒ [a] → [a] → Bool
startsWith = curry $ fix \rec → \case
  ((p : ps), (t : ts))
    | p == t → rec (ps, ts)
    | otherwise → False
  (Empty, (_ : _)) → True
  ((_ : _), Empty) → False

class IndexOf a where
  indexOf1By ∷ Fn a Bool → [a] → Maybe Int
  indexOf1By pred = ($ id) $ fix \rec kont → \case
    Empty → kont Empty
    (a : as)
      | pred a → kont $ Just 0
      | otherwise → rec (maybe (kont Empty) \((+ 1) → i) → kont (Just i)) as
  indexOf1 ∷ (Eq a) ⇒ a → [a] → Maybe Int
  indexOf1 = indexOf1By . (==)

  -- \| indexOf searches a pattern from a given text.
  -- TODO: Implement me using Knutt-Patt-Morison (KPM) algorithm
  indexOf ∷ (Eq a) ⇒ [a] → [a] → Maybe Int
  indexOf pat@(lengthOf folded → n) = ($ id) $ fix \rec kont → \case
    text@(drop 1 → next) → case taken n text of
      Empty → Nothing
      Just text'
        | pat == text' → kont $ Just 0
        | otherwise → rec (maybe (kont Empty) \((+ 1) → i) → kont (Just i)) next

groupBy ∷ ∀ k a b. (Ord k) ⇒ Fn a k → [(a, b)] → [(k, [b])]
groupBy fn = asList . asMap
  where
    asMap ∷ [(a, b)] → Map k [b]
    asMap = ifoldrOf (folded % ifolded) add Empty
    add ∷ a → b → Map k [b] → Map k [b]
    add a@(fn → k) v = at k %~ \case Just ((v :) → bs) → Just bs; Empty → Just [v]
    asList = itoListOf ifolded

group ∷ (Ord a) ⇒ [(a, b)] → [(a, [b])]
group = groupBy id

mapi ∷ (Int → a → b) → [a] → [b]
mapi fn = ifoldrOf ifolded (\i a → ((fn i a) :)) Empty

foldri ∷ (Int → a → b → b) → b → [a] → b
foldri = ifoldrOf ifolded

foldli ∷ (Int → b → a → b) → b → [a] → b
foldli = ifoldlOf' ifolded

mapiM ∷ (Monad m) ⇒ (Int → a → m b) → [a] → m [b]
mapiM = itraverseOf itraversed

unfold ∷ Fn a b → Fn a a → Fn a Bool → a → [b]
unfold get next stop = uf Empty
  where
    uf bs a@((get &&& next) → (b, a'))
      | stop a = b : bs
      | otherwise = uf (b : bs) a'

-- Unification
bound ∷ (Ord a) ⇒ a → Map a a → Maybe a
bound = view . at

isBound ∷ (Ord a) ⇒ a → Map a a → Bool
isBound a m = isJust (bound a m)

binding ∷ (Ord a) ⇒ a → Map a a → a
binding a m
  | Just a' ← bound a m = binding a' m
  | otherwise = a

bind ∷ (Ord a) ⇒ a → a → Map a a → Map a a
bind k v = at k .~ Just v

subst ∷ (Ord a) ⇒ Map a a → Map a a
subst m0 = ifoldrOf ifolded sb Empty m0
  where
    sb k v = at k .~ Just (binding k m0)

unify
  ∷ (Ord a, Show a) ⇒ Fn a Bool → Map a a → [(a, a)] → Either String (Map a a)
unify ground m = fix \rec → \case
  Empty → return m
  ((a@(flip binding m → a'), b@(flip binding m → b')) : rs)
    | a == b → rec rs
    | allOf folded (== True) [ground a, ground b] →
        Left $
          unwords $
            intersperse
              " "
              [ "unification error:"
              , show a
              , "/="
              , show b
              ]
    | ground a → rec ((b, a) : rs)
    | Just {} ← bound a m → rec ((a', b) : rs)
    | Just {} ← bound b m → rec ((b', a) : rs)
    | otherwise → unify ground (bind a b m) rs
