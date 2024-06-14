-- | This Haskell module defines a framework for working with context-sensitive
--   grammars using Earley parsing. The key components of this module include data
--   types and functions that enable the construction, manipulation, and parsing of
--   grammars in a monadic context
module Util.Earley.Language where

import           Data.HMap           (HKey, HMap)
import qualified Data.HMap           as HMap
import           Prelude             hiding (exp, fail, lex)
import           Util
import           Util.Earley.Process (Process)
import qualified Util.Earley.Process as Process

-- | Type of grammars. RHS of a production rules. Synthesizing values of type 'a'. Monadic construction allows context-sensitive grammars.
data Grammar a where
  Ret
    ∷ a
    → Grammar a
    -- ^ Return a value in the grammar.
  Alts
    ∷ [Grammar a]
    → Grammar a
    -- ^ Alternative grammars.
  GetNonTerminal
    ∷ NonTerminal b
    → (b → Grammar a)
    → Grammar a
    -- ^ Retrieve a non-terminal and bind its result to a new grammar.

-- | Type of non-terminals. LHS of a production rules. Carrying values of type 'a'.
data NonTerminal a where
  -- | Non-terminal with a name and a key.
  NonTerminal ∷ ∀ x a. String → (HKey x (Value a)) → NonTerminal a

-- | Data type representing a grammar rule.
data Rule where
  Rule ∷ (NonTerminal a) → (Grammar a) → Rule

-- | Type for language definition over terminals (tokens) of type 't'. A collection of production rules together with an entry point. Constructed monadically.
data Language t a where
  Language
    ∷ {runLanguage ∷ NonTerminal t → (a, [Rule])}
    → Language t a

-- | Type to represent the effort taken during parsing. Used by some unit-tests.
newtype Effort = Effort Int deriving (Show)

-- | Type of cursors. Used in parse error reports. Indicates the index of the input token list reached before the error was encountered.
type Cursor = Int

-- | From type representing the start of a grammar.
type From a = (a, Cursor)

-- | To type representing the end of a grammar.
type To a = (a, Cursor)

-- | An Earley item: A located/dotted Rule. i.e. Rule + 2 positions.
data Item where
  Item ∷ ∀ a. Cursor → (NonTerminal a) → Cursor → (Grammar a) → Item

-- | State for Earley parsing.
data State where
  State ∷ {processes ∷ HMap, effort ∷ Effort} → State

-- | Type for state values.
type Value a = Map Cursor (Process (To a) Item)

instance Functor (Language t) where fmap = liftM

instance Applicative (Language t) where
  pure a = Language $ const (a, [])
  (<*>) = ap

instance Monad (Language t) where
  (>>=) m f = Language $ \tok →
    let
      (a, rules1) = runLanguage m tok
      (b, rules2) = runLanguage (f a) tok
     in
      (b, rules1 <> rules2)

instance Functor Grammar where fmap = liftM

instance Applicative Grammar where
  pure = Ret
  (<*>) = ap

instance Monad Grammar where
  (>>=) = bind
    where
      -- \| Bind operation for 'Grammar', enabling monadic sequencing.
      bind ∷ Grammar a → (a → Grammar b) → Grammar b
      bind grammar f = case grammar of
        Ret a               → f a
        Alts gs             → Alts [g >>= f | g ← gs]
        GetNonTerminal nt k → GetNonTerminal nt (k >=> f)

instance Alternative Grammar where
  empty = Alts Empty
  (<|>) a b = Alts [a, b]

instance MonadPlus Grammar

instance AsEmpty (Grammar a) where
  _Empty = nearly empty undefined

-- | Show instance for 'NonTerminal'.
instance Show (NonTerminal a) where
  show (NonTerminal name _) = name

-- | Grammar constructed from a list of alternatives. Alternations may be nested; we are not restricted to just having alternate productions for a given non-terminal.
alts ∷ [Grammar a] → Grammar a
alts = Alts

-- | Grammar constructed from no alternatives. @fail == alts []@
fail ∷ Grammar a
fail = Alts Empty

-- | Kleene '*' which ignores the synthesized value.
-- @skipWhile p == do _ <- many p; return ()@
skipWhile ∷ Grammar () → Grammar ()
skipWhile p = void $ many p

-- | Create a non-terminal within a language definition and pass it to a continuation.
withNonTerminal ∷ String → (NonTerminal a → b) → b
withNonTerminal name k = HMap.withKey $ \key → k (NonTerminal name key)

-- | Extract the key of a non-terminal and pass it to a continuation.
withKeyOfNonTerminal ∷ NonTerminal a → (∀ x. HKey x (Value a) → b) → b
withKeyOfNonTerminal (NonTerminal _ key) k = k key

-- | Check if a rule is keyed by a specific non-terminal.
isRuleKeyedBy ∷ NonTerminal a → Rule → Bool
isRuleKeyedBy nt1 (Rule nt2 _) = withKeyOfNonTerminal nt1 $ \key1 →
  withKeyOfNonTerminal nt2 $ \key2 →
    HMap.unique key1 == HMap.unique key2

-- | Access to the grammar for tokens within a language definition.
getToken ∷ Language t (Grammar t)
getToken = Language $ \tok → (referenceNonTerminal tok, [])

-- | Create a fresh non-terminal within a language definition. The name is only used for debugging and reporting ambiguity. This is a low level primitive. Simpler to use 'declare'.
createNamedNonTerminal ∷ (Show a) ⇒ String → Language t (NonTerminal a)
createNamedNonTerminal name = withNonTerminal name $ \nt → Language $ const (nt, [])

-- | Reference a non-terminal on the RHS of a production. This is a low level primitive. Simpler to use 'declare'.
referenceNonTerminal ∷ NonTerminal a → Grammar a
referenceNonTerminal nt = GetNonTerminal nt Ret

-- | Convenience combination of 'createNamedNonTerminal' and 'referenceNonTerminal', returning a pair of values for a fresh non-terminal, for use on the LHS/RHS.
declare ∷ (Show a) ⇒ String → Language t (NonTerminal a, Grammar a)
declare name = do
  nt ← createNamedNonTerminal name
  return (nt, referenceNonTerminal nt)

-- | Define a language production, linking the LHS and RHS of the rule.
produce ∷ NonTerminal a → Grammar a → Language t ()
produce nt grammar = Language $ const ((), [Rule nt grammar])

-- | Combination of declare/produce to allow reference to a grammar within its own definition. Use this for languages with left-recursion.
fix
  ∷ (Show a)
  ⇒ String
  → (Grammar a → Language t (Grammar a))
  → Language t (Grammar a)
fix name f = do
  (nt, grammar) ← declare name
  fixed ← f grammar
  produce nt fixed
  return grammar

-- | Increment the parsing effort.
incEffort ∷ Effort → Effort
incEffort (Effort x) = Effort (x + 1)

-- | Increment the effort in the state.
incEffortState ∷ State → State
incEffortState s = s {effort = incEffort (effort s)}

-- | Check if a process exists for a given non-terminal and position in the state.
existsProcess ∷ State → From (NonTerminal a) → Bool
existsProcess s from = isJust $ lookProcess s from

-- | Look up a process for a given non-terminal and position in the state.
lookProcess ∷ State → From (NonTerminal a) → Maybe (Process (To a) Item)
lookProcess s (nt, cursor) = withKeyOfNonTerminal nt $ \key →
  HMap.lookup key (processes s) >>= (^. at cursor)

-- | Insert a process for a given non-terminal and position in the state.
insertProcess ∷ State → From (NonTerminal a) → Process (To a) Item → State
insertProcess s (nt, cursor) process = withKeyOfNonTerminal nt $ \key →
  let
    m = HMap.findWithDefault mempty key (processes s)
    m' = m & at cursor ?~ process
   in
    s {processes = HMap.insert key m' (processes s)}

-- | Check if a full parse is available at a given non-terminal and position in the state.
fullParseAt ∷ NonTerminal a → Cursor → State → Bool
fullParseAt start cursor s = not . null $ do
  (a, p) ← _elems
  guard (p == cursor)
  return a
  where
    _elems = maybe [] (^. Process.elems) (lookProcess s (start, 0))

-- | Result of running a parsing function: 'parse' or 'parseAmb'. Combines the outcome with the effort taken.
data Parsing a where
  Parsing ∷ {effortP ∷ Effort, outcomeP ∷ a} → Parsing a
  deriving (Functor)

-- | Type describing a syntax-error encountered during parsing. In all cases the final position reached before the error is reported. This position is automatically determined by the Earley parsing algorithm.
data SyntaxError where
  UnexpectedTokenAt ∷ Cursor → SyntaxError
  UnexpectedEOF ∷ Cursor → SyntaxError
  ExpectedEOF ∷ Cursor → SyntaxError
  deriving (Show, Eq)

-- | Type describing a parse ambiguity for a specific non-terminal (name), across a position range. This may be reported as an error by the 'parse' entry point.
data Ambiguity where
  Ambiguity ∷ String → Cursor → Cursor → Ambiguity
  deriving (Show, Eq)

-- | Union of 'SyntaxError' and 'Ambiguity', for reporting errors from 'parse'.
data ParseError where
  SyntaxError ∷ SyntaxError → ParseError
  AmbiguityError ∷ Ambiguity → ParseError
  deriving (Show, Eq)

-- | Entry-point to run a parse. Rejects ambiguity. Parse a list of tokens using a Language/Grammar definition. Returns the single parse or a parse-error.
parse
  ∷ (Show a, Show t)
  ⇒ Language t (Grammar a)
  → [t]
  → Parsing (Either ParseError a)
parse language input = ggparse rejectAmb language input <&> handleResult
  where
    handleResult (Left e) = Left e
    handleResult (Right []) = error "ggparse, [] results not possible"
    handleResult (Right [x]) = Right x
    handleResult (Right (_ : _)) = Left (AmbiguityError (Ambiguity "start" 0 (length input)))

-- | Entry-point to run a parse. Allows ambiguity. Parses a list of tokens using a Language/Grammar definition. Returns all parses or a syntax-error.
parseAmb
  ∷ (Eq a, Show a, Show t)
  ⇒ Language t (Grammar a)
  → [t]
  → Parsing (Either SyntaxError [a])
parseAmb language input = ggparse allowAmb language input <&> handleResult
  where
    handleResult (Left (SyntaxError e)) = Left e
    handleResult (Left (AmbiguityError _)) = error "ggparseAmb, AmbiguityError not possible"
    handleResult (Right xs) = Right xs

-- | Configuration for parsing, determining whether ambiguity is allowed.
newtype Config = Config {allowAmbiguity ∷ Bool}

-- | Configuration that allows ambiguity.
allowAmb ∷ Config
allowAmb = Config {allowAmbiguity = True}

-- | Configuration that rejects ambiguity.
rejectAmb ∷ Config
rejectAmb = Config {allowAmbiguity = False}

-- | Type alias for the outcome of parsing.
type Outcome a = Either ParseError [a]

-- | Generalized parse function.
ggparse
  ∷ (Show a, Show t)
  ⇒ Config
  → Language t (Grammar a)
  → [t]
  → Parsing (Outcome a)
ggparse config language input = withNonTerminal "<token>" $ \tokenNonTerminal → do
  let
    (grammar, rules) = runLanguage language tokenNonTerminal
  walk tokenNonTerminal config grammar rules input

-- | Walk through the grammar and input to perform parsing.
walk
  ∷ NonTerminal t → Config → Grammar a → [Rule] → [t] → Parsing (Outcome a)
walk tokenNonTerminal config grammar rules input = withNonTerminal "<start>" $ \startNonTerminal → do
  let
    initState = State {processes = HMap.empty, effort = Effort 0}
    state0 = insertProcess initState (startNonTerminal, 0) Empty
    startItem = Item 0 startNonTerminal 0 grammar
    (state1, optAmb) = execItemsWithRules config rules [startItem] state0
  case optAmb of
    Just ambiguity → Parsing (effort state1) (Left (AmbiguityError ambiguity))
    Empty → loop startNonTerminal tokenNonTerminal config rules 0 state1 input
  where
    -- \| Main parsing loop that processes the input tokens.
    loop
      ∷ NonTerminal a
      → NonTerminal t
      → Config
      → [Rule]
      → Cursor
      → State
      → [t]
      → Parsing (Outcome a)
    loop startNonTerminal tokenNonTerminal config rules cursor s xs = case xs of
      [] → finalCheck startNonTerminal cursor s
      x : xs → case lookProcess s (tokenNonTerminal, cursor) of
        Empty → finalFallback startNonTerminal cursor s
        Just process → do
          let
            upto = (x, cursor + 1)
            (process', items) = Process.produce upto process
            s2 = insertProcess s (tokenNonTerminal, cursor) process'
            (s3, optAmb) = execItemsWithRules config rules items s2
          case optAmb of
            Just ambiguity → Parsing (effort s) (Left (AmbiguityError ambiguity))
            Empty → loop startNonTerminal tokenNonTerminal config rules (cursor + 1) s3 xs
      where
        -- \| Check for final parse results at the end of input.
        finalCheck ∷ NonTerminal a → Cursor → State → Parsing (Outcome a)
        finalCheck startNonTerminal cursor s = case lookProcess s (startNonTerminal, 0) of
          Empty → error "startProcess missing"
          Just process → do
            let
              results = [a | (a, p) ← Process._elems process, p == cursor]
            case results of
              [] →
                Parsing (effort s) $
                  Left $
                    if existsProcess s (tokenNonTerminal, cursor)
                      then SyntaxError (UnexpectedEOF (cursor + 1))
                      else SyntaxError (UnexpectedTokenAt cursor)
              xs → Parsing (effort s) (Right xs)

        -- \| Handle fallback case when no process is found.
        finalFallback ∷ NonTerminal a → Cursor → State → Parsing (Outcome a)
        finalFallback startNonTerminal cursor s
          | fullParseAt startNonTerminal cursor s =
              Parsing (effort s) (Left (SyntaxError (ExpectedEOF (cursor + 1))))
          | otherwise = Parsing (effort s) (Left (SyntaxError (UnexpectedTokenAt cursor)))

    -- \| Execute items with rules and update the state.
    execItemsWithRules ∷ Config → [Rule] → [Item] → State → (State, Maybe Ambiguity)
    execItemsWithRules config rules items state = execItems items state
      where
        -- \| Find rules associated with a non-terminal.
        findRules ∷ NonTerminal a → [Rule]
        findRules nt = filter (isRuleKeyedBy nt) rules

        -- \| Execute a list of items and update the state.
        execItems ∷ [Item] → State → (State, Maybe Ambiguity)
        execItems [] s = (s, Empty)
        execItems (Item p1 nt p2 grammar : items) s = case grammar of
          Alts gs → execItems (map (Item p1 nt p2) gs ++ items) s
          Ret a → case produceState s (nt, p1) (a, p2) of
            Left ambiguity → (s, Just ambiguity)
            Right (s1, items1) → execItems (items1 ++ items) (incEffortState s1)
          GetNonTerminal ntB kB → execItems (items ++ items1) (incEffortState s1)
            where
              (s1, items1) = awaitState s (ntB, p2) (\(b, p3) → Item p1 nt p3 (kB b))

        -- \| Produce state and update the process.
        produceState
          ∷ State → From (NonTerminal a) → To a → Either Ambiguity (State, [Item])
        produceState s from upto = case lookProcess s from of
          Empty → error ("produceState, missing process for: " ++ show from)
          Just process
            | allowAmbiguity config →
                let
                  (process', items) = Process.produce upto process
                 in
                  Right (insertProcess s from process', items)
            | otherwise → case writeProcessNoAmb upto process of
                Empty → Left (Ambiguity (show $ fst from) (snd from) (snd upto))
                Just (process', items) → Right (insertProcess s from process', items)

        -- \| Write to the process without ambiguity.
        writeProcessNoAmb
          ∷ To a → Process (To a) Item → Maybe (Process (To a) Item, [Item])
        writeProcessNoAmb upto process =
          if any ((== snd upto) . snd) (process ^. Process.elems)
            then Empty
            else Just (Process.produce upto process)

        -- \| Await state and update the process with a consumer.
        awaitState ∷ State → From (NonTerminal a) → (To a → Item) → (State, [Item])
        awaitState s from consumer = case lookProcess s from of
          Empty → (insertProcess s from (Process.consume0 consumer), predict from)
          Just process →
            let
              (process', items) = Process.consume consumer process
             in
              (insertProcess s from process', items)

        -- \| Predict items for a given non-terminal and position.
        predict ∷ From (NonTerminal a) → [Item]
        predict (nt, cursor) = map (itemOfRule cursor) (findRules nt)

        -- \| Create an item from a rule.
        itemOfRule ∷ Cursor → Rule → Item
        itemOfRule cursor (Rule nt grammar) = Item cursor nt cursor grammar
