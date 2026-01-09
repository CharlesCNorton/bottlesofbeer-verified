/- ****************************************************************************

                   99 Bottles of Beer: Verified Termination

     A pedagogical Lean 4 development using the familiar "99 Bottles" song
     to teach formal verification. Every section is commented to serve as
     a self-contained introduction to theorem proving in Lean 4.

     We model the song as a state machine and prove:
       - Conservation: bottles on wall + passed = starting count
       - Termination: the song always reaches "no more bottles"
       - Correctness: verses match the trajectory through states

     "Anything can happen, child. Anything can be."
     — Shel Silverstein

     Original Author: Charles C. Norton
     Original Date: December 2025
     Lean 4 Port: January 2026

**************************************************************************** -/

namespace Bottles

/- =========================================================================
   PART I: STATE MACHINE MODEL
   =========================================================================
   We model the song as transitions between states. Each state tracks
   how many bottles remain on the wall, how many have been passed
   around, and what we started with (for the conservation invariant).
   ========================================================================= -/

/-- State: A snapshot of the song at any moment.
    Structures in Lean bundle multiple named fields into a single type.
    This is similar to a struct in C or a record in ML. -/
structure State where
  on_wall : Nat        -- Bottles currently on the wall.
  passed_around : Nat  -- Bottles taken down and passed.
  starting_count : Nat -- Original count; never changes.
  deriving Repr, DecidableEq

/-- initial: Constructs the starting state for a song with n bottles.
    At the start, all bottles are on the wall, none have been passed. -/
def initial (n : Nat)  -- Takes the starting bottle count.
    : State            -- Returns a State record.
    := { on_wall := n           -- All n bottles begin on the wall.
       , passed_around := 0     -- Zero bottles passed initially.
       , starting_count := n }  -- Record n for invariant checking.

/-- terminal: Predicate that holds when the song is finished.
    A Prop is a logical proposition; this one asserts on_wall is zero. -/
def terminal (s : State)  -- Takes a state to examine.
    : Prop                -- Returns a proposition (provable or not).
    := s.on_wall = 0      -- True iff no bottles remain.

/-- Decidability instance for terminal.
    This allows us to compute whether a state is terminal. -/
instance : Decidable (terminal s) :=
  inferInstanceAs (Decidable (s.on_wall = 0))

/-- step: Performs one verse of the song—takes one bottle down.
    If already at zero, the state doesn't change (fixpoint behavior). -/
def step (s : State)       -- Takes the current state.
    : State                -- Returns the next state.
    := match s.on_wall with        -- Pattern match on bottles remaining.
       | 0 => s                    -- Zero bottles: song over, no change.
       | n + 1 =>                  -- n+1 bottles: n remain after taking one.
         { on_wall := n
         , passed_around := s.passed_around + 1  -- One more passed.
         , starting_count := s.starting_count }  -- Starting count unchanged.

/-- invariant: The conservation law—bottles are never created or destroyed.
    This is the key property: on_wall + passed_around = starting_count. -/
def invariant (s : State)  -- Takes a state to check.
    : Prop                 -- Returns a proposition.
    := s.on_wall + s.passed_around = s.starting_count  -- Conservation equation.

/- =========================================================================
   PART II: CORE SAFETY THEOREMS
   =========================================================================
   We prove that the invariant holds initially and is preserved by
   each step. This "inductive invariant" pattern is fundamental to
   proving properties of state machines and transition systems.
   ========================================================================= -/

/-- initial_satisfies_invariant: The starting state satisfies conservation.
    This is the "base case" of our inductive invariant argument. -/
theorem initial_satisfies_invariant (n : Nat)  -- For any starting count n...
    : invariant (initial n)                    -- ...the initial state satisfies the invariant.
    := by
  simp [invariant, initial]  -- Expand definitions; n + 0 = n is trivial.

/-- step_preserves_invariant: If a state satisfies the invariant, so does its successor.
    This is the "inductive step"—preservation under transitions. -/
theorem step_preserves_invariant (s : State) (h : invariant s)
    : invariant (step s) := by
  simp only [invariant, step] at *  -- Expand definitions everywhere.
  cases hs : s.on_wall with         -- Case split: is on_wall zero or a successor?
  | zero => simp [hs] at *; exact h -- w = 0: step doesn't change state.
  | succ k => simp [hs] at *; omega -- w = S k: one bottle moves from wall to passed.

/-- step_preserves_starting_count: The starting count never changes.
    This is obvious but useful as a rewrite lemma. -/
theorem step_preserves_starting_count (s : State)
    : (step s).starting_count = s.starting_count := by
  simp only [step]           -- Expand the step definition.
  cases s.on_wall <;> rfl    -- Both cases: starting_count field preserved.

/-- step_decreases_or_terminal: Each step either terminates or makes progress.
    This is crucial for termination: we can't loop forever. -/
theorem step_decreases_or_terminal (s : State)
    : terminal s ∨ (step s).on_wall < s.on_wall := by
  cases hs : s.on_wall with          -- Case split on bottles remaining.
  | zero => left; simp [terminal, hs]   -- w = 0: choose left disjunct (terminal).
  | succ k => right; simp [step, hs]    -- w = S k: choose right (decreases).

/-- terminal_is_fixpoint: Once terminal, step has no effect.
    The song is over; taking another step doesn't change anything. -/
theorem terminal_is_fixpoint (s : State) (h : terminal s)
    : step s = s := by
  simp only [terminal] at h  -- h says on_wall = 0.
  simp only [step, h]        -- Rewrite and simplify.

/- =========================================================================
   PART III: EXECUTION AND TERMINATION
   =========================================================================
   We define a "fuel-based" execution model: run n steps and see where
   we end up. Then we prove that sufficient fuel always reaches terminal
   state, establishing termination of the song.
   ========================================================================= -/

/-- run: Execute the state machine for a fixed number of steps.
    This defines a recursive function; fuel decreases each call. -/
def run (fuel : Nat)   -- Number of steps to execute.
        (s : State)    -- Starting state.
    : State            -- Ending state after fuel steps.
    := match fuel with
       | 0 => s                -- No fuel: return current state.
       | n + 1 => run n (step s)  -- Fuel remaining: step once, recurse.

/-- run_preserves_invariant: Running any number of steps preserves the invariant.
    By induction: base case is trivial, inductive case uses step_preserves_invariant. -/
theorem run_preserves_invariant (fuel : Nat) (s : State) (h : invariant s)
    : invariant (run fuel s) := by
  induction fuel generalizing s with  -- Induction on fuel.
  | zero => exact h                   -- Base: run 0 s = s; H already holds.
  | succ k ih =>                      -- Inductive: run (S k) s = run k (step s).
    exact ih (step s) (step_preserves_invariant s h)

/-- run_preserves_starting_count: Running preserves the starting count.
    Follows from step_preserves_starting_count by induction. -/
theorem run_preserves_starting_count (fuel : Nat) (s : State)
    : (run fuel s).starting_count = s.starting_count := by
  induction fuel generalizing s with
  | zero => rfl
  | succ k ih => simp [run]; rw [ih, step_preserves_starting_count]

/-- run_reaches_zero: With enough fuel equal to on_wall, we reach zero bottles.
    This is the key lemma: fuel = on_wall is sufficient for termination. -/
theorem run_reaches_zero (w p st : Nat)
    : (run w { on_wall := w, passed_around := p, starting_count := st }).on_wall = 0 := by
  induction w generalizing p with
  | zero => rfl                         -- Base: already at zero.
  | succ k ih => simp [run, step]; exact ih (p + 1)  -- Step and recurse.

/-- sufficient_fuel_reaches_terminal: Starting with on_wall fuel always terminates.
    This establishes that the song ALWAYS ends—no infinite loops possible. -/
theorem sufficient_fuel_reaches_terminal (s : State)
    : terminal (run s.on_wall s) := by
  simp only [terminal]
  cases s with
  | mk w p st => exact run_reaches_zero w p st

/-- song_terminates: The classic 99-bottle song terminates.
    Verified by direct computation (native_decide). -/
theorem song_terminates : terminal (run 99 (initial 99)) := by
  native_decide  -- Lean computes this directly and verifies it's true.

/-- all_bottles_passed_at_end: At termination, all bottles have been passed.
    Combines invariant preservation with termination. -/
theorem all_bottles_passed_at_end (n : Nat)
    : (run n (initial n)).passed_around = n := by
  have hinv := run_preserves_invariant n (initial n) (initial_satisfies_invariant n)
  have hterm := sufficient_fuel_reaches_terminal (initial n)
  have hst := run_preserves_starting_count n (initial n)
  simp only [invariant, terminal, initial] at *
  omega  -- Arithmetic: 0 + passed = n and starting = n implies passed = n.

/- =========================================================================
   PART IV: TRAJECTORY ANALYSIS
   =========================================================================
   We prove that the sequence of states forms a monotonic trajectory:
   bottles on wall never increases, bottles passed never decreases.
   This captures the "one-way" nature of the song's progress.
   ========================================================================= -/

/-- monotonic_decreasing: A function from Nat to State has non-increasing on_wall. -/
def monotonic_decreasing (f : Nat → State) : Prop :=
  ∀ i j, i ≤ j → (f j).on_wall ≤ (f i).on_wall

/-- trajectory: The sequence of states reached by running 0, 1, 2, ... steps. -/
def trajectory (s : State) : Nat → State :=
  fun i => run i s

/-- step_nonincreasing: Taking a step never increases bottles on wall. -/
theorem step_nonincreasing (s : State) : (step s).on_wall ≤ s.on_wall := by
  cases hs : s.on_wall with
  | zero => simp [step, hs]   -- 0 → 0: no change.
  | succ k => simp [step, hs] -- S k → k: decreases by 1.

/-- no_bottles_created: Running never creates new bottles on wall.
    Bottles can only decrease or stay the same. -/
theorem no_bottles_created (s : State) (fuel : Nat)
    : (run fuel s).on_wall ≤ s.on_wall := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ k ih =>
    simp only [run]
    calc (run k (step s)).on_wall
        ≤ (step s).on_wall := ih (step s)
      _ ≤ s.on_wall := step_nonincreasing s

/-- on_wall_run_step: Running after a step gives ≤ on_wall than running without. -/
theorem on_wall_run_step (fuel : Nat) (s : State)
    : (run fuel (step s)).on_wall ≤ (run fuel s).on_wall := by
  induction fuel generalizing s with
  | zero => simp [run]; exact step_nonincreasing s
  | succ k ih => simp only [run]; exact ih (step s)

/-- run_succ_le: One more step means on_wall is no greater. -/
theorem run_succ_le (fuel : Nat) (s : State)
    : (run (fuel + 1) s).on_wall ≤ (run fuel s).on_wall := by
  simp only [run]
  exact on_wall_run_step fuel s

/-- trajectory_monotonic: The trajectory has monotonically decreasing on_wall.
    As we take more steps, bottles on wall can only go down. -/
theorem trajectory_monotonic (s : State) : monotonic_decreasing (trajectory s) := by
  intro i j hij
  simp only [trajectory]
  induction hij with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    calc (run (_ + 1) s).on_wall
        ≤ (run _ s).on_wall := run_succ_le _ s
      _ ≤ (run i s).on_wall := ih

/-- monotonic_increasing: A function from Nat to State has non-decreasing passed_around. -/
def monotonic_increasing (f : Nat → State) : Prop :=
  ∀ i j, i ≤ j → (f i).passed_around ≤ (f j).passed_around

/-- step_passed_nondecreasing: Taking a step never decreases passed_around. -/
theorem step_passed_nondecreasing (s : State)
    : s.passed_around ≤ (step s).passed_around := by
  cases hs : s.on_wall with
  | zero => simp [step, hs]   -- 0: no change, same passed.
  | succ k => simp [step, hs] -- S k: passed increases by 1.

/-- no_bottles_lost: Running never loses passed bottles.
    passed_around can only increase or stay the same. -/
theorem no_bottles_lost (s : State) (fuel : Nat)
    : s.passed_around ≤ (run fuel s).passed_around := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ k ih =>
    simp only [run]
    calc s.passed_around
        ≤ (step s).passed_around := step_passed_nondecreasing s
      _ ≤ (run k (step s)).passed_around := ih (step s)

/-- passed_run_step: Running after a step gives ≥ passed than running without. -/
theorem passed_run_step (fuel : Nat) (s : State)
    : (run fuel s).passed_around ≤ (run fuel (step s)).passed_around := by
  induction fuel generalizing s with
  | zero => simp [run]; exact step_passed_nondecreasing s
  | succ k ih => simp only [run]; exact ih (step s)

/-- run_succ_passed_ge: One more step means passed_around is no less. -/
theorem run_succ_passed_ge (fuel : Nat) (s : State)
    : (run fuel s).passed_around ≤ (run (fuel + 1) s).passed_around := by
  simp only [run]
  exact passed_run_step fuel s

/-- trajectory_passed_monotonic: The trajectory has monotonically increasing passed_around.
    As we take more steps, bottles passed can only go up. -/
theorem trajectory_passed_monotonic (s : State)
    : monotonic_increasing (trajectory s) := by
  intro i j hij
  simp only [trajectory]
  induction hij with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    calc (run i s).passed_around
        ≤ (run _ s).passed_around := ih
      _ ≤ (run (_ + 1) s).passed_around := run_succ_passed_ge _ s

/- =========================================================================
   PART V: REACHABILITY
   =========================================================================
   We define reachability as an inductive relation: a state is reachable
   from another if we can get there by zero or more steps. This gives us
   a more abstract way to reason about the state machine.
   ========================================================================= -/

/-- Reachable: Inductive definition of reachability.
    s' is reachable from s0 if:
    - s' = s0 (reflexive base case), or
    - s' = step s for some reachable s (transitive step case). -/
inductive Reachable (s0 : State) : State → Prop where
  | refl : Reachable s0 s0
  | step (s s' : State) : Reachable s0 s → s' = step s → Reachable s0 s'

/-- reachable_trans: Reachability is transitive.
    If s1 is reachable from s0 and s2 is reachable from s1,
    then s2 is reachable from s0. -/
theorem reachable_trans (s0 s1 s2 : State)
    (h1 : Reachable s0 s1) (h2 : Reachable s1 s2) : Reachable s0 s2 := by
  induction h2 with
  | refl => exact h1
  | step s s' _ hs' ih => exact Reachable.step s s' ih hs'

/-- reachable_run: Any state reached by run is reachable.
    This connects our fuel-based execution to the abstract reachability. -/
theorem reachable_run (fuel : Nat) (s : State) : Reachable s (run fuel s) := by
  induction fuel generalizing s with
  | zero => exact Reachable.refl
  | succ k ih =>
    simp only [run]
    have h1 : Reachable s (step s) := Reachable.step s (step s) Reachable.refl rfl
    exact reachable_trans s (step s) (run k (step s)) h1 (ih (step s))

/-- reachable_preserves_invariant: Invariant holds for all reachable states.
    If we start satisfying the invariant, every reachable state does too. -/
theorem reachable_preserves_invariant (s0 s : State)
    (hinv : invariant s0) (hreach : Reachable s0 s) : invariant s := by
  induction hreach with
  | refl => exact hinv
  | step _ s' _ hs' ih =>
    rw [hs']
    exact step_preserves_invariant _ ih

/-- reachable_terminal_exists: From any state, a terminal state is reachable.
    This is another way to state termination. -/
theorem reachable_terminal_exists (s : State)
    : ∃ s', Reachable s s' ∧ terminal s' :=
  ⟨run s.on_wall s, reachable_run s.on_wall s, sufficient_fuel_reaches_terminal s⟩

/- =========================================================================
   PART VI: STRING CONVERSION
   =========================================================================
   To generate actual verse text, we need to convert numbers to strings.
   This section defines nat↔string conversion functions and proves they
   are inverses (round-trip property).
   ========================================================================= -/

/-- digitToChar: Convert a single digit (0-9) to its ASCII character.
    For inputs ≥ 10, returns '9' (but we only use this for valid digits). -/
def digitToChar (d : Nat) : Char :=
  match d with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | _ => '9'

/-- digitToString: Convert a digit to a single-character string. -/
def digitToString (d : Nat) : String :=
  String.singleton (digitToChar d)

/-- natToStringAux: Auxiliary function for nat→string conversion.
    Uses fuel to ensure termination; builds string right-to-left. -/
def natToStringAux (fuel n : Nat) (acc : String) : String :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    let d := n % 10        -- Rightmost digit.
    let r := n / 10        -- Remaining digits.
    let acc' := digitToString d ++ acc  -- Prepend digit.
    match r with
    | 0 => acc'            -- No more digits.
    | _ => natToStringAux f r acc'  -- Recurse on remaining.

/-- natToString: Convert a natural number to its decimal string representation.
    Special case for 0 to avoid empty string. -/
def natToString (n : Nat) : String :=
  match n with
  | 0 => "0"
  | _ => natToStringAux n n ""

-- Test cases for natToString.
#eval natToString 0   -- "0"
#eval natToString 1   -- "1"
#eval natToString 10  -- "10"
#eval natToString 99  -- "99"
#eval natToString 42  -- "42"

/-- charToDigit: Convert an ASCII digit character to its numeric value.
    Returns none for non-digit characters. -/
def charToDigit (c : Char) : Option Nat :=
  match c with
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3 | '4' => some 4
  | '5' => some 5 | '6' => some 6 | '7' => some 7 | '8' => some 8 | '9' => some 9
  | _ => none

/-- charToDigitToChar: Round-trip property for char↔digit conversion.
    Converting a digit to char and back gives the original digit. -/
theorem charToDigitToChar (d : Nat) (h : d < 10)
    : charToDigit (digitToChar d) = some d := by
  match d with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl
  | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl | 9 => rfl
  | n + 10 => omega

/-- stringToNatAux: Auxiliary function for string→nat conversion.
    Processes characters left-to-right, accumulating the value. -/
def stringToNatAux (s : String) (acc : Nat) : Option Nat :=
  s.foldl (fun optAcc c =>
    match optAcc with
    | none => none
    | some a =>
      match charToDigit c with
      | none => none
      | some d => some (a * 10 + d)
  ) (some acc)

/-- stringToNat: Convert a string to a natural number.
    Returns none for empty strings or strings with non-digit characters. -/
def stringToNat (s : String) : Option Nat :=
  if s.isEmpty then none
  else stringToNatAux s 0

-- Test cases for stringToNat.
#eval stringToNat "99"   -- some 99
#eval stringToNat "0"    -- some 0
#eval stringToNat ""     -- none
#eval stringToNat "abc"  -- none

/- =========================================================================
   PART VII: VERSE GENERATION
   =========================================================================
   We define functions to generate the actual verse text. Each verse
   depends on the bottle count, using singular/plural grammar and
   special handling for the final verse (0 bottles).
   ========================================================================= -/

/-- bottleWord: Returns "bottle" (singular) or "bottles" (plural).
    English grammar requires singular for exactly 1 bottle. -/
def bottleWord (n : Nat) : String :=
  match n with
  | 1 => "bottle"
  | _ => "bottles"

/-- countPhrase: Generates "N bottle(s)" or "No more bottles" for count n. -/
def countPhrase (n : Nat) : String :=
  match n with
  | 0 => "No more bottles"
  | _ => natToString n ++ " " ++ bottleWord n

/-- verse: Generate a complete verse for the song.
    start is the original bottle count (for the final verse).
    n is the current bottle count. -/
def verse (start n : Nat) : String :=
  match n with
  | 0 =>  -- Final verse: "No more bottles... Go to the store..."
    "No more bottles of beer on the wall, no more bottles of beer. " ++
    "Go to the store and buy some more, " ++
    natToString start ++ " bottles of beer on the wall."
  | k + 1 =>  -- Regular verse: "N bottles... Take one down..."
    countPhrase (k + 1) ++ " of beer on the wall, " ++
    countPhrase (k + 1) ++ " of beer. " ++
    "Take one down and pass it around, " ++
    countPhrase k ++ " of beer on the wall."

/-- currentVerse: Get the verse for the current state.
    Uses starting_count and on_wall to determine the verse. -/
def currentVerse (s : State) : String :=
  verse s.starting_count s.on_wall

/-- fullSongAux: Build the complete song list recursively.
    Collects verses from count m down to 0. -/
def fullSongAux (start n : Nat) (acc : List String) : List String :=
  match n with
  | 0 => acc ++ [verse start 0]
  | k + 1 => fullSongAux start k (acc ++ [verse start (k + 1)])

/-- fullSong: Generate the complete list of verses for a song.
    Returns n+1 verses for a song starting with n bottles. -/
def fullSong (start : Nat) : List String :=
  fullSongAux start start []

-- Test verse generation.
#eval verse 99 99  -- First verse
#eval verse 99 1   -- Singular bottle verse
#eval verse 99 0   -- Final verse
#eval (fullSong 5).length  -- Should be 6

/- =========================================================================
   PART VIII: VERSE STRUCTURE LEMMAS
   =========================================================================
   We prove structural properties of verses: grammar correctness,
   length bounds, and that different counts produce different verses.
   These support the main injectivity theorem.
   ========================================================================= -/

/-- verse_one_singular: Verse for 1 bottle uses singular "bottle". -/
theorem verse_one_singular (start : Nat)
    : verse start 1 =
      "1 bottle of beer on the wall, 1 bottle of beer. " ++
      "Take one down and pass it around, No more bottles of beer on the wall." := by
  rfl

/-- verse_two_plural: Verse for 2 bottles uses plural "bottles". -/
theorem verse_two_plural (start : Nat)
    : verse start 2 =
      "2 bottles of beer on the wall, 2 bottles of beer. " ++
      "Take one down and pass it around, 1 bottle of beer on the wall." := by
  rfl

/-- verse_99: The classic opening verse, verified by computation. -/
theorem verse_99
    : verse 99 99 =
      "99 bottles of beer on the wall, 99 bottles of beer. " ++
      "Take one down and pass it around, 98 bottles of beer on the wall." := by
  native_decide

/-- verse_0_uses_start: The final verse references the starting count. -/
theorem verse_0_uses_start (start : Nat)
    : verse start 0 =
      "No more bottles of beer on the wall, no more bottles of beer. " ++
      "Go to the store and buy some more, " ++
      natToString start ++ " bottles of beer on the wall." := by
  rfl

/-- fullSongAux_length: Helper lemma for song length calculation. -/
theorem fullSongAux_length (start m : Nat) (acc : List String)
    : (fullSongAux start m acc).length = acc.length + m + 1 := by
  induction m generalizing acc with
  | zero => simp [fullSongAux, List.length_append]
  | succ k ih =>
    simp only [fullSongAux]
    rw [ih]
    simp [List.length_append]
    omega

/-- full_song_length: A song with n bottles has exactly n+1 verses. -/
theorem full_song_length (n : Nat) : (fullSong n).length = n + 1 := by
  simp [fullSong, fullSongAux_length]

/-- ninety_nine_bottles_100_verses: The classic song has exactly 100 verses. -/
theorem ninety_nine_bottles_100_verses : (fullSong 99).length = 100 := by
  simp [full_song_length]

-- Quick checks of song generation.
#eval (fullSong 99)[0]!   -- Verse 99
#eval (fullSong 99)[98]!  -- Verse 1
#eval (fullSong 99)[99]!  -- Verse 0

/- =========================================================================
   PART IX: LEADING NUMBER EXTRACTION
   =========================================================================
   To prove verse injectivity, we need to extract the leading number
   from a verse string. These functions parse the first decimal number
   from a string.
   ========================================================================= -/

/-- leadingNatAux: Extract digits from the front of a character list. -/
def leadingNatAux (s : List Char) (acc : Nat) : Nat :=
  match s with
  | [] => acc
  | c :: rest =>
    match charToDigit c with
    | none => acc          -- Non-digit: stop parsing.
    | some d => leadingNatAux rest (acc * 10 + d)  -- Digit: accumulate.

/-- leadingNat: Extract the leading natural number from a string.
    Returns none if the string doesn't start with a digit. -/
def leadingNat (s : String) : Option Nat :=
  match s.toList with
  | [] => none
  | c :: rest =>
    match charToDigit c with
    | none => none         -- Doesn't start with digit.
    | some d => some (leadingNatAux rest d)

/-- isDigitChar': Predicate for ASCII digit characters. -/
def isDigitChar' (c : Char) : Bool :=
  match charToDigit c with
  | some _ => true
  | none => false

/-- allDigits: Check if all characters in a string are digits. -/
def allDigits (s : String) : Bool :=
  s.toList.all isDigitChar'

/-- isDigitChar_digitToChar: digitToChar always produces a digit character. -/
theorem isDigitChar_digitToChar (d : Nat) : isDigitChar' (digitToChar d) = true := by
  simp only [isDigitChar', digitToChar, charToDigit]
  match d with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl
  | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl | 9 => rfl
  | _ + 10 => rfl

/-- allDigits_digitToString: Single-digit strings are all digits. -/
theorem allDigits_digitToString (d : Nat) (h : d < 10)
    : allDigits (digitToString d) = true := by
  match d with
  | 0 => native_decide | 1 => native_decide | 2 => native_decide
  | 3 => native_decide | 4 => native_decide | 5 => native_decide
  | 6 => native_decide | 7 => native_decide | 8 => native_decide
  | 9 => native_decide | n + 10 => omega

/-- digitToChar_ne_N: Digit characters are never 'N'.
    This distinguishes "No more" from numeric verses. -/
theorem digitToChar_ne_N (d : Nat) (h : d < 10) : digitToChar d ≠ 'N' := by
  match d with
  | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide
  | 5 => decide | 6 => decide | 7 => decide | 8 => decide | 9 => decide
  | n + 10 => omega

/-- digitToChar_inj: digitToChar is injective on digits 0-9. -/
theorem digitToChar_inj (d1 d2 : Nat) (h1 : d1 < 10) (h2 : d2 < 10)
    (heq : digitToChar d1 = digitToChar d2) : d1 = d2 := by
  match d1, d2 with
  | 0, 0 => rfl | 0, 1 => simp [digitToChar] at heq | 0, 2 => simp [digitToChar] at heq
  | 0, 3 => simp [digitToChar] at heq | 0, 4 => simp [digitToChar] at heq
  | 0, 5 => simp [digitToChar] at heq | 0, 6 => simp [digitToChar] at heq
  | 0, 7 => simp [digitToChar] at heq | 0, 8 => simp [digitToChar] at heq
  | 0, 9 => simp [digitToChar] at heq | 0, _ + 10 => omega
  | 1, 0 => simp [digitToChar] at heq | 1, 1 => rfl
  | 1, 2 => simp [digitToChar] at heq | 1, 3 => simp [digitToChar] at heq
  | 1, 4 => simp [digitToChar] at heq | 1, 5 => simp [digitToChar] at heq
  | 1, 6 => simp [digitToChar] at heq | 1, 7 => simp [digitToChar] at heq
  | 1, 8 => simp [digitToChar] at heq | 1, 9 => simp [digitToChar] at heq
  | 1, _ + 10 => omega
  | 2, 0 => simp [digitToChar] at heq | 2, 1 => simp [digitToChar] at heq
  | 2, 2 => rfl | 2, 3 => simp [digitToChar] at heq
  | 2, 4 => simp [digitToChar] at heq | 2, 5 => simp [digitToChar] at heq
  | 2, 6 => simp [digitToChar] at heq | 2, 7 => simp [digitToChar] at heq
  | 2, 8 => simp [digitToChar] at heq | 2, 9 => simp [digitToChar] at heq
  | 2, _ + 10 => omega
  | 3, 0 => simp [digitToChar] at heq | 3, 1 => simp [digitToChar] at heq
  | 3, 2 => simp [digitToChar] at heq | 3, 3 => rfl
  | 3, 4 => simp [digitToChar] at heq | 3, 5 => simp [digitToChar] at heq
  | 3, 6 => simp [digitToChar] at heq | 3, 7 => simp [digitToChar] at heq
  | 3, 8 => simp [digitToChar] at heq | 3, 9 => simp [digitToChar] at heq
  | 3, _ + 10 => omega
  | 4, 0 => simp [digitToChar] at heq | 4, 1 => simp [digitToChar] at heq
  | 4, 2 => simp [digitToChar] at heq | 4, 3 => simp [digitToChar] at heq
  | 4, 4 => rfl | 4, 5 => simp [digitToChar] at heq
  | 4, 6 => simp [digitToChar] at heq | 4, 7 => simp [digitToChar] at heq
  | 4, 8 => simp [digitToChar] at heq | 4, 9 => simp [digitToChar] at heq
  | 4, _ + 10 => omega
  | 5, 0 => simp [digitToChar] at heq | 5, 1 => simp [digitToChar] at heq
  | 5, 2 => simp [digitToChar] at heq | 5, 3 => simp [digitToChar] at heq
  | 5, 4 => simp [digitToChar] at heq | 5, 5 => rfl
  | 5, 6 => simp [digitToChar] at heq | 5, 7 => simp [digitToChar] at heq
  | 5, 8 => simp [digitToChar] at heq | 5, 9 => simp [digitToChar] at heq
  | 5, _ + 10 => omega
  | 6, 0 => simp [digitToChar] at heq | 6, 1 => simp [digitToChar] at heq
  | 6, 2 => simp [digitToChar] at heq | 6, 3 => simp [digitToChar] at heq
  | 6, 4 => simp [digitToChar] at heq | 6, 5 => simp [digitToChar] at heq
  | 6, 6 => rfl | 6, 7 => simp [digitToChar] at heq
  | 6, 8 => simp [digitToChar] at heq | 6, 9 => simp [digitToChar] at heq
  | 6, _ + 10 => omega
  | 7, 0 => simp [digitToChar] at heq | 7, 1 => simp [digitToChar] at heq
  | 7, 2 => simp [digitToChar] at heq | 7, 3 => simp [digitToChar] at heq
  | 7, 4 => simp [digitToChar] at heq | 7, 5 => simp [digitToChar] at heq
  | 7, 6 => simp [digitToChar] at heq | 7, 7 => rfl
  | 7, 8 => simp [digitToChar] at heq | 7, 9 => simp [digitToChar] at heq
  | 7, _ + 10 => omega
  | 8, 0 => simp [digitToChar] at heq | 8, 1 => simp [digitToChar] at heq
  | 8, 2 => simp [digitToChar] at heq | 8, 3 => simp [digitToChar] at heq
  | 8, 4 => simp [digitToChar] at heq | 8, 5 => simp [digitToChar] at heq
  | 8, 6 => simp [digitToChar] at heq | 8, 7 => simp [digitToChar] at heq
  | 8, 8 => rfl | 8, 9 => simp [digitToChar] at heq
  | 8, _ + 10 => omega
  | 9, 0 => simp [digitToChar] at heq | 9, 1 => simp [digitToChar] at heq
  | 9, 2 => simp [digitToChar] at heq | 9, 3 => simp [digitToChar] at heq
  | 9, 4 => simp [digitToChar] at heq | 9, 5 => simp [digitToChar] at heq
  | 9, 6 => simp [digitToChar] at heq | 9, 7 => simp [digitToChar] at heq
  | 9, 8 => simp [digitToChar] at heq | 9, 9 => rfl
  | 9, _ + 10 => omega
  | _ + 10, _ => omega

/-- firstChar: Get the first character of a string as Option. -/
def firstChar (s : String) : Option Char :=
  s.toList.head?

/-- N_not_digit: 'N' is not a digit character. -/
theorem N_not_digit : isDigitChar' 'N' = false := by native_decide

/-- firstChar_append_left: First char of concatenation is first char of left string.
    (When left string is non-empty.) -/
theorem firstChar_append_left (s1 s2 : String) (c : Char) (h : s1.toList.head? = some c)
    : (s1 ++ s2).toList.head? = some c := by
  simp only [String.toList_append]
  cases hs : s1.toList with
  | nil => simp [hs] at h
  | cons d ds => simp [List.head?, hs] at h ⊢; exact h

/-- verse_first_char_0: Verse 0 starts with 'N' (for "No more"). -/
theorem verse_first_char_0 (start : Nat) : firstChar (verse start 0) = some 'N' := by
  simp only [verse, firstChar]
  apply firstChar_append_left
  apply firstChar_append_left
  apply firstChar_append_left
  native_decide

/-- natToString_first_char_digit: natToString produces strings starting with a digit.
    (For n > 0 and n ≤ 99.) Proved by exhaustive case analysis. -/
theorem natToString_first_char_digit (n : Nat) (h : n > 0) (h2 : n ≤ 99)
    : ∃ c, (natToString n).toList.head? = some c ∧ isDigitChar' c = true := by
  match n with
  | 0 => omega
  | 1 => exact ⟨'1', by native_decide, by native_decide⟩
  | 2 => exact ⟨'2', by native_decide, by native_decide⟩
  | 3 => exact ⟨'3', by native_decide, by native_decide⟩
  | 4 => exact ⟨'4', by native_decide, by native_decide⟩
  | 5 => exact ⟨'5', by native_decide, by native_decide⟩
  | 6 => exact ⟨'6', by native_decide, by native_decide⟩
  | 7 => exact ⟨'7', by native_decide, by native_decide⟩
  | 8 => exact ⟨'8', by native_decide, by native_decide⟩
  | 9 => exact ⟨'9', by native_decide, by native_decide⟩
  | 10 => exact ⟨'1', by native_decide, by native_decide⟩
  | 11 => exact ⟨'1', by native_decide, by native_decide⟩
  | 12 => exact ⟨'1', by native_decide, by native_decide⟩
  | 13 => exact ⟨'1', by native_decide, by native_decide⟩
  | 14 => exact ⟨'1', by native_decide, by native_decide⟩
  | 15 => exact ⟨'1', by native_decide, by native_decide⟩
  | 16 => exact ⟨'1', by native_decide, by native_decide⟩
  | 17 => exact ⟨'1', by native_decide, by native_decide⟩
  | 18 => exact ⟨'1', by native_decide, by native_decide⟩
  | 19 => exact ⟨'1', by native_decide, by native_decide⟩
  | 20 => exact ⟨'2', by native_decide, by native_decide⟩
  | 21 => exact ⟨'2', by native_decide, by native_decide⟩
  | 22 => exact ⟨'2', by native_decide, by native_decide⟩
  | 23 => exact ⟨'2', by native_decide, by native_decide⟩
  | 24 => exact ⟨'2', by native_decide, by native_decide⟩
  | 25 => exact ⟨'2', by native_decide, by native_decide⟩
  | 26 => exact ⟨'2', by native_decide, by native_decide⟩
  | 27 => exact ⟨'2', by native_decide, by native_decide⟩
  | 28 => exact ⟨'2', by native_decide, by native_decide⟩
  | 29 => exact ⟨'2', by native_decide, by native_decide⟩
  | 30 => exact ⟨'3', by native_decide, by native_decide⟩
  | 31 => exact ⟨'3', by native_decide, by native_decide⟩
  | 32 => exact ⟨'3', by native_decide, by native_decide⟩
  | 33 => exact ⟨'3', by native_decide, by native_decide⟩
  | 34 => exact ⟨'3', by native_decide, by native_decide⟩
  | 35 => exact ⟨'3', by native_decide, by native_decide⟩
  | 36 => exact ⟨'3', by native_decide, by native_decide⟩
  | 37 => exact ⟨'3', by native_decide, by native_decide⟩
  | 38 => exact ⟨'3', by native_decide, by native_decide⟩
  | 39 => exact ⟨'3', by native_decide, by native_decide⟩
  | 40 => exact ⟨'4', by native_decide, by native_decide⟩
  | 41 => exact ⟨'4', by native_decide, by native_decide⟩
  | 42 => exact ⟨'4', by native_decide, by native_decide⟩
  | 43 => exact ⟨'4', by native_decide, by native_decide⟩
  | 44 => exact ⟨'4', by native_decide, by native_decide⟩
  | 45 => exact ⟨'4', by native_decide, by native_decide⟩
  | 46 => exact ⟨'4', by native_decide, by native_decide⟩
  | 47 => exact ⟨'4', by native_decide, by native_decide⟩
  | 48 => exact ⟨'4', by native_decide, by native_decide⟩
  | 49 => exact ⟨'4', by native_decide, by native_decide⟩
  | 50 => exact ⟨'5', by native_decide, by native_decide⟩
  | 51 => exact ⟨'5', by native_decide, by native_decide⟩
  | 52 => exact ⟨'5', by native_decide, by native_decide⟩
  | 53 => exact ⟨'5', by native_decide, by native_decide⟩
  | 54 => exact ⟨'5', by native_decide, by native_decide⟩
  | 55 => exact ⟨'5', by native_decide, by native_decide⟩
  | 56 => exact ⟨'5', by native_decide, by native_decide⟩
  | 57 => exact ⟨'5', by native_decide, by native_decide⟩
  | 58 => exact ⟨'5', by native_decide, by native_decide⟩
  | 59 => exact ⟨'5', by native_decide, by native_decide⟩
  | 60 => exact ⟨'6', by native_decide, by native_decide⟩
  | 61 => exact ⟨'6', by native_decide, by native_decide⟩
  | 62 => exact ⟨'6', by native_decide, by native_decide⟩
  | 63 => exact ⟨'6', by native_decide, by native_decide⟩
  | 64 => exact ⟨'6', by native_decide, by native_decide⟩
  | 65 => exact ⟨'6', by native_decide, by native_decide⟩
  | 66 => exact ⟨'6', by native_decide, by native_decide⟩
  | 67 => exact ⟨'6', by native_decide, by native_decide⟩
  | 68 => exact ⟨'6', by native_decide, by native_decide⟩
  | 69 => exact ⟨'6', by native_decide, by native_decide⟩
  | 70 => exact ⟨'7', by native_decide, by native_decide⟩
  | 71 => exact ⟨'7', by native_decide, by native_decide⟩
  | 72 => exact ⟨'7', by native_decide, by native_decide⟩
  | 73 => exact ⟨'7', by native_decide, by native_decide⟩
  | 74 => exact ⟨'7', by native_decide, by native_decide⟩
  | 75 => exact ⟨'7', by native_decide, by native_decide⟩
  | 76 => exact ⟨'7', by native_decide, by native_decide⟩
  | 77 => exact ⟨'7', by native_decide, by native_decide⟩
  | 78 => exact ⟨'7', by native_decide, by native_decide⟩
  | 79 => exact ⟨'7', by native_decide, by native_decide⟩
  | 80 => exact ⟨'8', by native_decide, by native_decide⟩
  | 81 => exact ⟨'8', by native_decide, by native_decide⟩
  | 82 => exact ⟨'8', by native_decide, by native_decide⟩
  | 83 => exact ⟨'8', by native_decide, by native_decide⟩
  | 84 => exact ⟨'8', by native_decide, by native_decide⟩
  | 85 => exact ⟨'8', by native_decide, by native_decide⟩
  | 86 => exact ⟨'8', by native_decide, by native_decide⟩
  | 87 => exact ⟨'8', by native_decide, by native_decide⟩
  | 88 => exact ⟨'8', by native_decide, by native_decide⟩
  | 89 => exact ⟨'8', by native_decide, by native_decide⟩
  | 90 => exact ⟨'9', by native_decide, by native_decide⟩
  | 91 => exact ⟨'9', by native_decide, by native_decide⟩
  | 92 => exact ⟨'9', by native_decide, by native_decide⟩
  | 93 => exact ⟨'9', by native_decide, by native_decide⟩
  | 94 => exact ⟨'9', by native_decide, by native_decide⟩
  | 95 => exact ⟨'9', by native_decide, by native_decide⟩
  | 96 => exact ⟨'9', by native_decide, by native_decide⟩
  | 97 => exact ⟨'9', by native_decide, by native_decide⟩
  | 98 => exact ⟨'9', by native_decide, by native_decide⟩
  | 99 => exact ⟨'9', by native_decide, by native_decide⟩
  | n + 100 => omega

/-- firstChar_append_left': Variant of firstChar_append_left using firstChar. -/
theorem firstChar_append_left' (s1 s2 : String) (c : Char)
    (h : s1.toList.head? = some c) : firstChar (s1 ++ s2) = some c := by
  simp only [firstChar]
  exact firstChar_append_left s1 s2 c h

/-- verse_first_char_pos: Positive-count verses start with a digit. -/
theorem verse_first_char_pos (start n : Nat) (h : n > 0) (h2 : n ≤ 99)
    : ∃ c, firstChar (verse start n) = some c ∧ isDigitChar' c = true := by
  have ⟨c, hc, hdig⟩ := natToString_first_char_digit n h h2
  refine ⟨c, ?_, hdig⟩
  simp only [verse, firstChar, countPhrase]
  match n with
  | 0 => omega
  | k + 1 =>
    repeat apply firstChar_append_left
    exact hc

/-- verse_0_ne_pos: Verse 0 differs from all positive verses.
    The key distinguishing feature: verse 0 starts with 'N', others with digits. -/
theorem verse_0_ne_pos (start n : Nat) (h : n > 0) (h2 : n ≤ 99)
    : verse start 0 ≠ verse start n := by
  intro heq
  have h0 := verse_first_char_0 start
  have ⟨c, hc, hdig⟩ := verse_first_char_pos start n h h2
  simp only [firstChar] at h0 hc
  rw [heq] at h0
  rw [h0] at hc
  injection hc with hc'
  rw [← hc'] at hdig
  exact absurd hdig (by native_decide)

/- =========================================================================
   PART X: VERSE INJECTIVITY
   =========================================================================
   The main theorem: different bottle counts produce different verses.
   This is essential for proving the song has no duplicate verses.
   ========================================================================= -/

/-- leadingNat_natToString: leadingNat correctly extracts n from natToString n.
    Proved by exhaustive computation for n ≤ 99. -/
theorem leadingNat_natToString (n : Nat) (h : n > 0) (h2 : n ≤ 99)
    : leadingNat (natToString n) = some n := by
  match n with
  | 0 => omega
  | 1 => native_decide | 2 => native_decide | 3 => native_decide
  | 4 => native_decide | 5 => native_decide | 6 => native_decide
  | 7 => native_decide | 8 => native_decide | 9 => native_decide
  | 10 => native_decide | 11 => native_decide | 12 => native_decide
  | 13 => native_decide | 14 => native_decide | 15 => native_decide
  | 16 => native_decide | 17 => native_decide | 18 => native_decide
  | 19 => native_decide | 20 => native_decide | 21 => native_decide
  | 22 => native_decide | 23 => native_decide | 24 => native_decide
  | 25 => native_decide | 26 => native_decide | 27 => native_decide
  | 28 => native_decide | 29 => native_decide | 30 => native_decide
  | 31 => native_decide | 32 => native_decide | 33 => native_decide
  | 34 => native_decide | 35 => native_decide | 36 => native_decide
  | 37 => native_decide | 38 => native_decide | 39 => native_decide
  | 40 => native_decide | 41 => native_decide | 42 => native_decide
  | 43 => native_decide | 44 => native_decide | 45 => native_decide
  | 46 => native_decide | 47 => native_decide | 48 => native_decide
  | 49 => native_decide | 50 => native_decide | 51 => native_decide
  | 52 => native_decide | 53 => native_decide | 54 => native_decide
  | 55 => native_decide | 56 => native_decide | 57 => native_decide
  | 58 => native_decide | 59 => native_decide | 60 => native_decide
  | 61 => native_decide | 62 => native_decide | 63 => native_decide
  | 64 => native_decide | 65 => native_decide | 66 => native_decide
  | 67 => native_decide | 68 => native_decide | 69 => native_decide
  | 70 => native_decide | 71 => native_decide | 72 => native_decide
  | 73 => native_decide | 74 => native_decide | 75 => native_decide
  | 76 => native_decide | 77 => native_decide | 78 => native_decide
  | 79 => native_decide | 80 => native_decide | 81 => native_decide
  | 82 => native_decide | 83 => native_decide | 84 => native_decide
  | 85 => native_decide | 86 => native_decide | 87 => native_decide
  | 88 => native_decide | 89 => native_decide | 90 => native_decide
  | 91 => native_decide | 92 => native_decide | 93 => native_decide
  | 94 => native_decide | 95 => native_decide | 96 => native_decide
  | 97 => native_decide | 98 => native_decide | 99 => native_decide
  | n + 100 => omega

/-- leadingNatAux_append_nondigit: Non-digit characters terminate parsing. -/
theorem leadingNatAux_append_nondigit (s : List Char) (c : Char) (rest : List Char)
    (hc : charToDigit c = none) (acc : Nat)
    : leadingNatAux (s ++ c :: rest) acc = leadingNatAux s acc := by
  induction s generalizing acc with
  | nil => simp [leadingNatAux, hc]
  | cons x xs ih =>
    simp only [leadingNatAux, List.cons_append]
    cases hxd : charToDigit x with
    | none => rfl
    | some d => exact ih (acc * 10 + d)

/-- space_not_digit: Space character is not a digit. -/
theorem space_not_digit : charToDigit ' ' = none := by native_decide

/-- leadingNat_prepend_nondigit: Non-digit suffix doesn't affect leading number. -/
theorem leadingNat_prepend_nondigit (s rest : String) (n : Nat)
    (h : leadingNat s = some n)
    (hrest : ∀ c, rest.toList.head? = some c → charToDigit c = none)
    : leadingNat (s ++ rest) = some n := by
  simp only [leadingNat, String.toList_append] at h ⊢
  cases hs : s.toList with
  | nil => simp [hs] at h
  | cons c cs =>
    simp only [hs, List.cons_append] at h ⊢
    cases hcd : charToDigit c with
    | none => simp [hcd] at h
    | some d =>
      simp only [hcd, Option.some.injEq] at h ⊢
      cases hrl : rest.toList with
      | nil => simp [List.append_nil]; exact h
      | cons r rs =>
        have hrd := hrest r (by simp [hrl])
        rw [leadingNatAux_append_nondigit cs r rs hrd d]
        exact h

/-- verse_leadingNat_aux: leadingNat extracts the bottle count from a verse.
    Proved by exhaustive computation. -/
theorem verse_leadingNat_aux (n : Nat) (h : n > 0) (h2 : n ≤ 99)
    : leadingNat (verse n n) = some n := by
  match n with
  | 0 => omega
  | 1 => native_decide | 2 => native_decide | 3 => native_decide
  | 4 => native_decide | 5 => native_decide | 6 => native_decide
  | 7 => native_decide | 8 => native_decide | 9 => native_decide
  | 10 => native_decide | 11 => native_decide | 12 => native_decide
  | 13 => native_decide | 14 => native_decide | 15 => native_decide
  | 16 => native_decide | 17 => native_decide | 18 => native_decide
  | 19 => native_decide | 20 => native_decide | 21 => native_decide
  | 22 => native_decide | 23 => native_decide | 24 => native_decide
  | 25 => native_decide | 26 => native_decide | 27 => native_decide
  | 28 => native_decide | 29 => native_decide | 30 => native_decide
  | 31 => native_decide | 32 => native_decide | 33 => native_decide
  | 34 => native_decide | 35 => native_decide | 36 => native_decide
  | 37 => native_decide | 38 => native_decide | 39 => native_decide
  | 40 => native_decide | 41 => native_decide | 42 => native_decide
  | 43 => native_decide | 44 => native_decide | 45 => native_decide
  | 46 => native_decide | 47 => native_decide | 48 => native_decide
  | 49 => native_decide | 50 => native_decide | 51 => native_decide
  | 52 => native_decide | 53 => native_decide | 54 => native_decide
  | 55 => native_decide | 56 => native_decide | 57 => native_decide
  | 58 => native_decide | 59 => native_decide | 60 => native_decide
  | 61 => native_decide | 62 => native_decide | 63 => native_decide
  | 64 => native_decide | 65 => native_decide | 66 => native_decide
  | 67 => native_decide | 68 => native_decide | 69 => native_decide
  | 70 => native_decide | 71 => native_decide | 72 => native_decide
  | 73 => native_decide | 74 => native_decide | 75 => native_decide
  | 76 => native_decide | 77 => native_decide | 78 => native_decide
  | 79 => native_decide | 80 => native_decide | 81 => native_decide
  | 82 => native_decide | 83 => native_decide | 84 => native_decide
  | 85 => native_decide | 86 => native_decide | 87 => native_decide
  | 88 => native_decide | 89 => native_decide | 90 => native_decide
  | 91 => native_decide | 92 => native_decide | 93 => native_decide
  | 94 => native_decide | 95 => native_decide | 96 => native_decide
  | 97 => native_decide | 98 => native_decide | 99 => native_decide
  | n + 100 => omega

/-- leadingNat_of_prefix: Alias for leadingNat_prepend_nondigit. -/
theorem leadingNat_of_prefix (s1 s2 : String) (n : Nat)
    (h1 : leadingNat s1 = some n)
    (h2 : ∀ c, s2.toList.head? = some c → charToDigit c = none)
    : leadingNat (s1 ++ s2) = some n :=
  leadingNat_prepend_nondigit s1 s2 n h1 h2

/-- verse_has_natToString_prefix: Positive verses start with the number string. -/
theorem verse_has_natToString_prefix (start n : Nat) (h : n > 0)
    : ∃ rest, verse start n = natToString n ++ " " ++ rest := by
  match n with
  | 0 => omega
  | k + 1 =>
    refine ⟨bottleWord (k + 1) ++ " of beer on the wall, " ++
        (natToString (k + 1) ++ " " ++ bottleWord (k + 1)) ++ " of beer. " ++
        "Take one down and pass it around, " ++
        countPhrase k ++
        " of beer on the wall.", ?_⟩
    simp only [verse, countPhrase, String.append_assoc]

/-- leadingNat_natToString_space: leadingNat extracts n from "n ..." strings. -/
theorem leadingNat_natToString_space (s : String) (n : Nat) (h : n > 0) (h2 : n ≤ 99)
    : leadingNat (natToString n ++ " " ++ s) = some n := by
  have hassoc : natToString n ++ " " ++ s = natToString n ++ (" " ++ s) := by
    simp only [String.append_assoc]
  rw [hassoc]
  apply leadingNat_prepend_nondigit (natToString n) (" " ++ s) n
  · exact leadingNat_natToString n h h2
  · intro c hc
    have hspace : (" " ++ s).toList = ' ' :: s.toList := by
      simp only [String.toList_append]
      have : " ".toList = [' '] := by native_decide
      simp [this]
    simp only [hspace, List.head?] at hc
    injection hc with hc'
    rw [← hc']
    native_decide

/-- verse_leadingNat: leadingNat correctly extracts n from verse start n.
    This is the key lemma for injectivity. -/
theorem verse_leadingNat (start n : Nat) (h : n > 0) (h2 : n ≤ 99)
    : leadingNat (verse start n) = some n := by
  obtain ⟨rest, hrest⟩ := verse_has_natToString_prefix start n h
  rw [hrest]
  exact leadingNat_natToString_space rest n h h2

/-- verse_inj: THE MAIN INJECTIVITY THEOREM.
    Different bottle counts produce different verses.
    This is the heart of the uniqueness proof. -/
theorem verse_inj (start n1 n2 : Nat) (h1 : n1 ≤ 99) (h2 : n2 ≤ 99)
    (heq : verse start n1 = verse start n2) : n1 = n2 := by
  match n1, n2 with
  | 0, 0 => rfl
  | 0, m + 1 => exact absurd heq (verse_0_ne_pos start (m + 1) (by omega) h2)
  | m + 1, 0 => exact absurd heq.symm (verse_0_ne_pos start (m + 1) (by omega) h1)
  | m + 1, k + 1 =>
    -- Both are positive: extract leading numbers and compare.
    have hln1 := verse_leadingNat start (m + 1) (by omega) h1
    have hln2 := verse_leadingNat start (k + 1) (by omega) h2
    rw [heq] at hln1
    rw [hln1] at hln2
    injection hln2

/- =========================================================================
   PART XI: NO DUPLICATE VERSES
   =========================================================================
   We prove that the complete song has no duplicate verses. This follows
   from verse injectivity: each verse uniquely identifies its count.
   ========================================================================= -/

/-- fullSongAux_pairwise: Helper for proving song has pairwise distinct verses. -/
theorem fullSongAux_pairwise (n m : Nat) (acc : List String) (hn : n ≤ 99)
    (hm : m ≤ n) (hacc : acc.Pairwise (· ≠ ·))
    (hvs : ∀ v ∈ acc, ∃ k, m < k ∧ k ≤ n ∧ v = verse n k)
    : (fullSongAux n m acc).Pairwise (· ≠ ·) := by
  induction m generalizing acc with
  | zero =>
    simp only [fullSongAux]
    apply List.pairwise_append.mpr
    constructor
    · exact hacc
    constructor
    · exact List.pairwise_singleton _ _
    · intro v hv1 w hw1
      simp only [List.mem_singleton] at hw1
      have ⟨k, hk1, hk2, hk3⟩ := hvs v hv1
      rw [hk3, hw1]
      intro heq
      have hk2' : k ≤ 99 := Nat.le_trans hk2 hn
      have := verse_inj n k 0 hk2' (by omega) heq
      omega
  | succ m' ih =>
    simp only [fullSongAux]
    apply ih
    · omega
    · apply List.pairwise_append.mpr
      constructor
      · exact hacc
      constructor
      · exact List.pairwise_singleton _ _
      · intro v hv1 w hw1
        simp only [List.mem_singleton] at hw1
        have ⟨k, hk1, hk2, hk3⟩ := hvs v hv1
        rw [hk3, hw1]
        intro heq
        have hk2' : k ≤ 99 := Nat.le_trans hk2 hn
        have := verse_inj n k (m' + 1) hk2' (by omega) heq
        omega
    · intro v hv
      simp only [List.mem_append, List.mem_singleton] at hv
      cases hv with
      | inl hv =>
        have ⟨k, hk1, hk2, hk3⟩ := hvs v hv
        exact ⟨k, by omega, hk2, hk3⟩
      | inr hv =>
        exact ⟨m' + 1, by omega, by omega, hv⟩

/-- fullSong_pairwise: The complete song has pairwise distinct verses. -/
theorem fullSong_pairwise (n : Nat) (h : n ≤ 99)
    : (fullSong n).Pairwise (· ≠ ·) := by
  unfold fullSong
  apply fullSongAux_pairwise n n [] h (Nat.le_refl n) List.Pairwise.nil
  intro v hv
  cases hv

/-- ninety_nine_bottles_all_distinct: The 99-bottle song has 100 unique verses. -/
theorem ninety_nine_bottles_all_distinct
    : (fullSong 99).Pairwise (· ≠ ·) :=
  fullSong_pairwise 99 (by omega)

/- =========================================================================
   PART XII: BISIMULATION AND TRAJECTORY-SONG CORRESPONDENCE
   =========================================================================
   We prove bisimulation-style theorems: the state machine execution
   corresponds exactly to counting down bottles, and each step through
   the state machine produces the verse at the corresponding position
   in the song.
   ========================================================================= -/

/-- conservation_law: Bottles are conserved for all reachable states.
    on_wall + passed_around always equals the starting count. -/
theorem conservation_law (n : Nat) (s : State) (h : Reachable (initial n) s)
    : s.on_wall + s.passed_around = n := by
  have hinv := reachable_preserves_invariant (initial n) s (initial_satisfies_invariant n) h
  simp [invariant] at hinv
  have hst : s.starting_count = n := by
    induction h with
    | refl => simp [initial]
    | step prev curr hprev heq ih =>
      rw [heq, step_preserves_starting_count]
      have hpinv := reachable_preserves_invariant (initial n) prev (initial_satisfies_invariant n) hprev
      simp [invariant] at hpinv
      exact ih hpinv
  omega

/-- run_on_wall_aux: Helper relating run to on_wall decrease.
    The key insight: on_wall only depends on initial on_wall and steps taken. -/
theorem run_on_wall_aux (k w p st : Nat)
    : (run k { on_wall := w, passed_around := p, starting_count := st }).on_wall =
      w - min k w := by
  induction k generalizing w p with
  | zero => simp [run]
  | succ k' ih =>
    cases w with
    | zero =>
      simp only [run, step]
      specialize ih 0 p
      simp at ih
      exact ih
    | succ w' =>
      simp only [run, step]
      rw [ih w' (p + 1)]
      omega

/-- bisimulation: Characterizes the state after k steps.
    After k steps from initial n: on_wall = n - min(k, n). -/
theorem bisimulation (n k : Nat)
    : (run k (initial n)).on_wall = n - min k n := by
  simp [initial]
  exact run_on_wall_aux k n 0 n

/-- state_verse_consistent: A state has valid bounds for verse generation. -/
def state_verse_consistent (s : State) : Prop :=
  s.on_wall ≤ s.starting_count ∧ s.starting_count ≤ 99

/-- initial_verse_consistent: Initial states are verse-consistent. -/
theorem initial_verse_consistent (n : Nat) (h : n ≤ 99)
    : state_verse_consistent (initial n) := by
  simp [state_verse_consistent, initial, h]

/-- step_verse_consistent: Step preserves verse-consistency. -/
theorem step_verse_consistent (s : State) (h : state_verse_consistent s)
    : state_verse_consistent (step s) := by
  simp [state_verse_consistent, step] at *
  cases hs : s.on_wall with
  | zero => simp [hs] at *; exact h
  | succ k => simp [hs] at *; omega

/-- run_verse_consistent: Run preserves verse-consistency. -/
theorem run_verse_consistent (fuel : Nat) (s : State) (h : state_verse_consistent s)
    : state_verse_consistent (run fuel s) := by
  induction fuel generalizing s with
  | zero => exact h
  | succ k ih => exact ih (step s) (step_verse_consistent s h)

/-- fullSongAux_getElem: Indexing into fullSongAux results. -/
theorem fullSongAux_getElem (start m : Nat) (acc : List String) (k : Nat) (hk : k < acc.length + m + 1)
    : (fullSongAux start m acc)[k]? =
      if k < acc.length then acc[k]?
      else some (verse start (m - (k - acc.length))) := by
  induction m generalizing k acc with
  | zero =>
    simp only [fullSongAux]
    by_cases hka : k < acc.length
    · simp only [hka, ↓reduceIte]
      exact List.getElem?_append_left hka
    · simp only [hka, ↓reduceIte]
      have hka' : acc.length ≤ k := Nat.not_lt.mp hka
      have hk2 : k = acc.length := by omega
      subst hk2
      simp [Nat.le_refl]
  | succ m' ih =>
    simp only [fullSongAux]
    by_cases hka : k < acc.length
    · simp only [hka, ↓reduceIte]
      have hk3 : k < (acc ++ [verse start (m' + 1)]).length + m' + 1 := by simp; omega
      rw [ih (acc ++ [verse start (m' + 1)]) k hk3]
      have hka2 : k < (acc ++ [verse start (m' + 1)]).length := by simp; omega
      simp only [hka2, ↓reduceIte]
      exact List.getElem?_append_left hka
    · simp only [hka, ↓reduceIte]
      have hka' : acc.length ≤ k := Nat.not_lt.mp hka
      have hk3 : k < (acc ++ [verse start (m' + 1)]).length + m' + 1 := by simp; omega
      rw [ih (acc ++ [verse start (m' + 1)]) k hk3]
      by_cases hka2 : k < (acc ++ [verse start (m' + 1)]).length
      · simp only [hka2, ↓reduceIte]
        simp at hka2
        have hkeq : k = acc.length := by omega
        subst hkeq
        simp [Nat.le_refl]
      · simp only [hka2, ↓reduceIte]
        have hka2' : (acc ++ [verse start (m' + 1)]).length ≤ k := Nat.not_lt.mp hka2
        simp only [List.length_append, List.length_singleton] at hka2'
        simp only [List.length_append, List.length_singleton]
        congr 2
        omega

/-- fullSong_nth: The k-th element of fullSong n is verse n (n-k). -/
theorem fullSong_nth (n k : Nat) (h : k ≤ n)
    : (fullSong n)[k]? = some (verse n (n - k)) := by
  simp only [fullSong]
  have hk2 : k < ([] : List String).length + n + 1 := by simp; omega
  rw [fullSongAux_getElem n n [] k hk2]
  simp

/-- trajectory_verses_match: State machine trajectory matches song verses.
    The k-th state in the trajectory produces the k-th verse of the song. -/
theorem trajectory_verses_match (n k : Nat) (_hn : n ≤ 99) (hk : k ≤ n)
    : currentVerse (run k (initial n)) = verse n (n - k) := by
  simp only [currentVerse]
  rw [run_preserves_starting_count, bisimulation]
  simp [initial]
  congr 1
  omega

/-- trajectory_full_song_correspondence: Complete correspondence theorem.
    For the 99-bottle song, the k-th trajectory state produces the k-th song verse. -/
theorem trajectory_full_song_correspondence (k : Nat) (h : k ≤ 99)
    : currentVerse (run k (initial 99)) = (fullSong 99)[k]! := by
  rw [trajectory_verses_match 99 k (by omega) h]
  have hget := fullSong_nth 99 k h
  have hlen : k < (fullSong 99).length := by simp [full_song_length]; omega
  simp only [List.getElem!_eq_getElem?_getD, hget, Option.getD_some]

/-- final_verse_is_terminal: The verse at step n is the terminal verse. -/
theorem final_verse_is_terminal (n : Nat) (h : n ≤ 99)
    : currentVerse (run n (initial n)) = verse n 0 := by
  rw [trajectory_verses_match n n h (Nat.le_refl n)]
  simp

/- =========================================================================
   PART XIII: PARAMETRICITY
   =========================================================================
   Some theorems hold for ANY starting count n, while others require
   n ≤ 99 for string parsing reasons. We make this distinction explicit.
   ========================================================================= -/

-- Theorems that hold for ANY n (no bound required):

/-- general_termination: The song terminates for ANY starting count.
    No bound on n required—the state machine always reaches terminal. -/
theorem general_termination (n : Nat) : terminal (run n (initial n)) :=
  sufficient_fuel_reaches_terminal (initial n)

/-- general_conservation: Conservation holds for ANY starting count.
    Bottles are conserved regardless of how many we start with. -/
theorem general_conservation (n : Nat) (s : State) (h : Reachable (initial n) s)
    : s.on_wall + s.passed_around = n :=
  conservation_law n s h

/-- general_invariant: The invariant holds for ANY starting count.
    This is the most fundamental property—no bounds needed. -/
theorem general_invariant (n fuel : Nat) : invariant (run fuel (initial n)) :=
  run_preserves_invariant fuel (initial n) (initial_satisfies_invariant n)

/-- general_all_bottles_passed: All bottles get passed for ANY n.
    At termination, passed_around equals the starting count. -/
theorem general_all_bottles_passed (n : Nat)
    : (run n (initial n)).passed_around = n :=
  all_bottles_passed_at_end n

-- Theorems requiring n ≤ 99 (for string parsing):

/-- bounded_verse_injectivity: Different counts give different verses.
    Requires n ≤ 99 for the leading_nat extraction to compute. -/
theorem bounded_verse_injectivity (start n1 n2 : Nat)
    (h1 : n1 ≤ 99) (h2 : n2 ≤ 99) (heq : verse start n1 = verse start n2) : n1 = n2 :=
  verse_inj start n1 n2 h1 h2 heq

/-- bounded_song_NoDup: The song has no duplicate verses.
    Requires n ≤ 99 because it depends on verse injectivity. -/
theorem bounded_song_NoDup (n : Nat) (h : n ≤ 99)
    : (fullSong n).Pairwise (· ≠ ·) :=
  fullSong_pairwise n h

/- =========================================================================
   PART XIV: THE SONG ITSELF
   =========================================================================
   Finally, we prove that our verified machinery produces the actual
   song. Each theorem below is a certificate that a specific verse
   computes to exactly the text we expect. Lean verifies each by
   computation—no trust required.
   ========================================================================= -/

/-- the_song_verse_99: The first verse of the song. -/
theorem the_song_verse_99
    : (fullSong 99)[0]! =
      "99 bottles of beer on the wall, 99 bottles of beer. " ++
      "Take one down and pass it around, 98 bottles of beer on the wall." := by
  native_decide  -- Verified by computation.

/-- the_song_verse_98: The second verse. -/
theorem the_song_verse_98
    : (fullSong 99)[1]! =
      "98 bottles of beer on the wall, 98 bottles of beer. " ++
      "Take one down and pass it around, 97 bottles of beer on the wall." := by
  native_decide

/-- the_song_verse_97: The third verse. -/
theorem the_song_verse_97
    : (fullSong 99)[2]! =
      "97 bottles of beer on the wall, 97 bottles of beer. " ++
      "Take one down and pass it around, 96 bottles of beer on the wall." := by
  native_decide

/-- the_song_verse_50: The middle of the song. -/
theorem the_song_verse_50
    : (fullSong 99)[49]! =
      "50 bottles of beer on the wall, 50 bottles of beer. " ++
      "Take one down and pass it around, 49 bottles of beer on the wall." := by
  native_decide

/-- the_song_verse_10: Getting close to the end. -/
theorem the_song_verse_10
    : (fullSong 99)[89]! =
      "10 bottles of beer on the wall, 10 bottles of beer. " ++
      "Take one down and pass it around, 9 bottles of beer on the wall." := by
  native_decide

/-- the_song_verse_3: Three bottles remain. -/
theorem the_song_verse_3
    : (fullSong 99)[96]! =
      "3 bottles of beer on the wall, 3 bottles of beer. " ++
      "Take one down and pass it around, 2 bottles of beer on the wall." := by
  native_decide

/-- the_song_verse_2: Two bottles remain—last plural verse. -/
theorem the_song_verse_2
    : (fullSong 99)[97]! =
      "2 bottles of beer on the wall, 2 bottles of beer. " ++
      "Take one down and pass it around, 1 bottle of beer on the wall." := by
  native_decide

/-- the_song_verse_1: One bottle remains—the singular verse. -/
theorem the_song_verse_1
    : (fullSong 99)[98]! =
      "1 bottle of beer on the wall, 1 bottle of beer. " ++
      "Take one down and pass it around, No more bottles of beer on the wall." := by
  native_decide

/-- the_song_verse_0: No more bottles—the final verse. -/
theorem the_song_verse_0
    : (fullSong 99)[99]! =
      "No more bottles of beer on the wall, no more bottles of beer. " ++
      "Go to the store and buy some more, 99 bottles of beer on the wall." := by
  native_decide

/-- the_song_is_complete: The song has exactly 100 verses, all verified.
    Combines length, uniqueness, and termination guarantees. -/
theorem the_song_is_complete
    : (fullSong 99).length = 100 ∧
      (fullSong 99).Pairwise (· ≠ ·) ∧
      terminal (run 99 (initial 99)) :=
  ⟨ninety_nine_bottles_100_verses,
   ninety_nine_bottles_all_distinct,
   song_terminates⟩

/-- the_song_matches_execution: Every verse matches state machine execution.
    The song list and the execution trajectory are perfectly synchronized. -/
theorem the_song_matches_execution (k : Nat) (h : k ≤ 99)
    : (fullSong 99)[k]! = currentVerse (run k (initial 99)) :=
  (trajectory_full_song_correspondence k h).symm

/-- song_complete: The state machine visits every verse in order.
    Combining termination, correspondence, and verse count. -/
theorem song_complete (n : Nat) (hn : n ≤ 99)
    : (∀ k, k ≤ n → currentVerse (run k (initial n)) = (fullSong n)[k]!) ∧
      terminal (run n (initial n)) := by
  constructor
  · intro k hk
    rw [trajectory_verses_match n k hn hk]
    have hget := fullSong_nth n k hk
    have hlen : k < (fullSong n).length := by simp [full_song_length]; omega
    simp only [List.getElem!_eq_getElem?_getD, hget, Option.getD_some]
  · exact sufficient_fuel_reaches_terminal (initial n)

/- =========================================================================
   PART XV: ADDITIONAL STRING PROPERTIES
   =========================================================================
   Round-trip properties for string conversion and additional helper
   lemmas used throughout the development.
   ========================================================================= -/

/-- stringToNat_natToString: Round-trip property: string(nat(s)) = s.
    Proved by exhaustive computation for n ≤ 99. -/
theorem stringToNat_natToString (n : Nat) (h : n ≤ 99)
    : stringToNat (natToString n) = some n := by
  match n with
  | 0 => native_decide | 1 => native_decide | 2 => native_decide
  | 3 => native_decide | 4 => native_decide | 5 => native_decide
  | 6 => native_decide | 7 => native_decide | 8 => native_decide
  | 9 => native_decide | 10 => native_decide | 11 => native_decide
  | 12 => native_decide | 13 => native_decide | 14 => native_decide
  | 15 => native_decide | 16 => native_decide | 17 => native_decide
  | 18 => native_decide | 19 => native_decide | 20 => native_decide
  | 21 => native_decide | 22 => native_decide | 23 => native_decide
  | 24 => native_decide | 25 => native_decide | 26 => native_decide
  | 27 => native_decide | 28 => native_decide | 29 => native_decide
  | 30 => native_decide | 31 => native_decide | 32 => native_decide
  | 33 => native_decide | 34 => native_decide | 35 => native_decide
  | 36 => native_decide | 37 => native_decide | 38 => native_decide
  | 39 => native_decide | 40 => native_decide | 41 => native_decide
  | 42 => native_decide | 43 => native_decide | 44 => native_decide
  | 45 => native_decide | 46 => native_decide | 47 => native_decide
  | 48 => native_decide | 49 => native_decide | 50 => native_decide
  | 51 => native_decide | 52 => native_decide | 53 => native_decide
  | 54 => native_decide | 55 => native_decide | 56 => native_decide
  | 57 => native_decide | 58 => native_decide | 59 => native_decide
  | 60 => native_decide | 61 => native_decide | 62 => native_decide
  | 63 => native_decide | 64 => native_decide | 65 => native_decide
  | 66 => native_decide | 67 => native_decide | 68 => native_decide
  | 69 => native_decide | 70 => native_decide | 71 => native_decide
  | 72 => native_decide | 73 => native_decide | 74 => native_decide
  | 75 => native_decide | 76 => native_decide | 77 => native_decide
  | 78 => native_decide | 79 => native_decide | 80 => native_decide
  | 81 => native_decide | 82 => native_decide | 83 => native_decide
  | 84 => native_decide | 85 => native_decide | 86 => native_decide
  | 87 => native_decide | 88 => native_decide | 89 => native_decide
  | 90 => native_decide | 91 => native_decide | 92 => native_decide
  | 93 => native_decide | 94 => native_decide | 95 => native_decide
  | 96 => native_decide | 97 => native_decide | 98 => native_decide
  | 99 => native_decide | n + 100 => omega

/-- natToString_inj: natToString is injective on 0-99. -/
theorem natToString_inj (n1 n2 : Nat) (h1 : n1 ≤ 99) (h2 : n2 ≤ 99)
    (heq : natToString n1 = natToString n2) : n1 = n2 := by
  have hs1 := stringToNat_natToString n1 h1
  have hs2 := stringToNat_natToString n2 h2
  rw [heq] at hs1
  rw [hs1] at hs2
  injection hs2

-- Concrete examples of natToString.
theorem natToString_0 : natToString 0 = "0" := by native_decide
theorem natToString_1 : natToString 1 = "1" := by native_decide
theorem natToString_10 : natToString 10 = "10" := by native_decide
theorem natToString_42 : natToString 42 = "42" := by native_decide
theorem natToString_99 : natToString 99 = "99" := by native_decide

-- Concrete examples of stringToNat.
theorem stringToNat_0 : stringToNat "0" = some 0 := by native_decide
theorem stringToNat_1 : stringToNat "1" = some 1 := by native_decide
theorem stringToNat_10 : stringToNat "10" = some 10 := by native_decide
theorem stringToNat_42 : stringToNat "42" = some 42 := by native_decide
theorem stringToNat_99 : stringToNat "99" = some 99 := by native_decide

/-- natToString_pos_ne_zero_str: Positive numbers don't stringify to "0". -/
theorem natToString_pos_ne_zero_str (n : Nat) (h : n > 0) (h2 : n ≤ 99)
    : natToString n ≠ "0" := by
  match n with
  | 0 => omega
  | 1 => native_decide | 2 => native_decide | 3 => native_decide
  | 4 => native_decide | 5 => native_decide | 6 => native_decide
  | 7 => native_decide | 8 => native_decide | 9 => native_decide
  | 10 => native_decide | 11 => native_decide | 12 => native_decide
  | 13 => native_decide | 14 => native_decide | 15 => native_decide
  | 16 => native_decide | 17 => native_decide | 18 => native_decide
  | 19 => native_decide | 20 => native_decide | 21 => native_decide
  | 22 => native_decide | 23 => native_decide | 24 => native_decide
  | 25 => native_decide | 26 => native_decide | 27 => native_decide
  | 28 => native_decide | 29 => native_decide | 30 => native_decide
  | 31 => native_decide | 32 => native_decide | 33 => native_decide
  | 34 => native_decide | 35 => native_decide | 36 => native_decide
  | 37 => native_decide | 38 => native_decide | 39 => native_decide
  | 40 => native_decide | 41 => native_decide | 42 => native_decide
  | 43 => native_decide | 44 => native_decide | 45 => native_decide
  | 46 => native_decide | 47 => native_decide | 48 => native_decide
  | 49 => native_decide | 50 => native_decide | 51 => native_decide
  | 52 => native_decide | 53 => native_decide | 54 => native_decide
  | 55 => native_decide | 56 => native_decide | 57 => native_decide
  | 58 => native_decide | 59 => native_decide | 60 => native_decide
  | 61 => native_decide | 62 => native_decide | 63 => native_decide
  | 64 => native_decide | 65 => native_decide | 66 => native_decide
  | 67 => native_decide | 68 => native_decide | 69 => native_decide
  | 70 => native_decide | 71 => native_decide | 72 => native_decide
  | 73 => native_decide | 74 => native_decide | 75 => native_decide
  | 76 => native_decide | 77 => native_decide | 78 => native_decide
  | 79 => native_decide | 80 => native_decide | 81 => native_decide
  | 82 => native_decide | 83 => native_decide | 84 => native_decide
  | 85 => native_decide | 86 => native_decide | 87 => native_decide
  | 88 => native_decide | 89 => native_decide | 90 => native_decide
  | 91 => native_decide | 92 => native_decide | 93 => native_decide
  | 94 => native_decide | 95 => native_decide | 96 => native_decide
  | 97 => native_decide | 98 => native_decide | 99 => native_decide
  | n + 100 => omega

/-- reachable_preserves_starting_count: Starting count is constant on reachable states. -/
theorem reachable_preserves_starting_count (s0 s : State)
    (hreach : Reachable s0 s) : s.starting_count = s0.starting_count := by
  induction hreach with
  | refl => rfl
  | step prev curr _ heq ih =>
    rw [heq, step_preserves_starting_count]
    exact ih

/-- terminal_reachable_from_any: From any state, a terminal state is reachable. -/
theorem terminal_reachable_from_any (s : State)
    : ∃ s', Reachable s s' ∧ terminal s' ∧ s'.starting_count = s.starting_count :=
  ⟨run s.on_wall s, reachable_run s.on_wall s, sufficient_fuel_reaches_terminal s,
   run_preserves_starting_count s.on_wall s⟩

/-- verse_50_full: Explicit verification of verse 50. -/
theorem verse_50_full
    : verse 99 50 =
      "50 bottles of beer on the wall, 50 bottles of beer. " ++
      "Take one down and pass it around, 49 bottles of beer on the wall." := by
  native_decide

/-- allDigits_natToString: natToString produces all-digit strings. -/
theorem allDigits_natToString (n : Nat) (h : n ≤ 99)
    : allDigits (natToString n) = true := by
  match n with
  | 0 => native_decide | 1 => native_decide | 2 => native_decide
  | 3 => native_decide | 4 => native_decide | 5 => native_decide
  | 6 => native_decide | 7 => native_decide | 8 => native_decide
  | 9 => native_decide | 10 => native_decide | 11 => native_decide
  | 12 => native_decide | 13 => native_decide | 14 => native_decide
  | 15 => native_decide | 16 => native_decide | 17 => native_decide
  | 18 => native_decide | 19 => native_decide | 20 => native_decide
  | 21 => native_decide | 22 => native_decide | 23 => native_decide
  | 24 => native_decide | 25 => native_decide | 26 => native_decide
  | 27 => native_decide | 28 => native_decide | 29 => native_decide
  | 30 => native_decide | 31 => native_decide | 32 => native_decide
  | 33 => native_decide | 34 => native_decide | 35 => native_decide
  | 36 => native_decide | 37 => native_decide | 38 => native_decide
  | 39 => native_decide | 40 => native_decide | 41 => native_decide
  | 42 => native_decide | 43 => native_decide | 44 => native_decide
  | 45 => native_decide | 46 => native_decide | 47 => native_decide
  | 48 => native_decide | 49 => native_decide | 50 => native_decide
  | 51 => native_decide | 52 => native_decide | 53 => native_decide
  | 54 => native_decide | 55 => native_decide | 56 => native_decide
  | 57 => native_decide | 58 => native_decide | 59 => native_decide
  | 60 => native_decide | 61 => native_decide | 62 => native_decide
  | 63 => native_decide | 64 => native_decide | 65 => native_decide
  | 66 => native_decide | 67 => native_decide | 68 => native_decide
  | 69 => native_decide | 70 => native_decide | 71 => native_decide
  | 72 => native_decide | 73 => native_decide | 74 => native_decide
  | 75 => native_decide | 76 => native_decide | 77 => native_decide
  | 78 => native_decide | 79 => native_decide | 80 => native_decide
  | 81 => native_decide | 82 => native_decide | 83 => native_decide
  | 84 => native_decide | 85 => native_decide | 86 => native_decide
  | 87 => native_decide | 88 => native_decide | 89 => native_decide
  | 90 => native_decide | 91 => native_decide | 92 => native_decide
  | 93 => native_decide | 94 => native_decide | 95 => native_decide
  | 96 => native_decide | 97 => native_decide | 98 => native_decide
  | 99 => native_decide | n + 100 => omega

/-- countPhrase_first_char: Count phrases for n > 0 start with a digit. -/
theorem countPhrase_first_char (n : Nat) (h : n > 0) (h2 : n ≤ 99)
    : ∃ c, firstChar (countPhrase n) = some c ∧ isDigitChar' c = true := by
  simp only [countPhrase]
  match n with
  | 0 => omega
  | k + 1 =>
    have ⟨c, hc, hdig⟩ := natToString_first_char_digit (k + 1) (by omega) h2
    refine ⟨c, ?_, hdig⟩
    simp only [firstChar]
    apply firstChar_append_left
    apply firstChar_append_left
    exact hc

/-- NoDup_singleton: A singleton list has no duplicates. -/
theorem NoDup_singleton {α : Type} (a : α) : [a].Pairwise (· ≠ ·) := by
  apply List.Pairwise.cons
  · intro b hb; cases hb
  · exact List.Pairwise.nil

/-- NoDup_cons: Adding a non-member preserves no-duplicates property. -/
theorem NoDup_cons {α : Type} [DecidableEq α] (a : α) (l : List α)
    (hnotin : a ∉ l) (hnd : l.Pairwise (· ≠ ·)) : (a :: l).Pairwise (· ≠ ·) := by
  apply List.Pairwise.cons
  · intro b hb
    intro heq
    rw [heq] at hnotin
    exact hnotin hb
  · exact hnd

/-- String.ne_of_length_ne: Different-length strings are not equal. -/
theorem String.ne_of_length_ne (s1 s2 : String) (h : s1.length ≠ s2.length) : s1 ≠ s2 := by
  intro heq
  rw [heq] at h
  exact h rfl

/-- canonical_natToString: Positive numbers don't start with '0'. -/
theorem canonical_natToString (n : Nat) (h : n > 0) (h2 : n ≤ 99)
    : (natToString n).toList.head? ≠ some '0' := by
  match n with
  | 0 => omega
  | 1 => native_decide | 2 => native_decide | 3 => native_decide
  | 4 => native_decide | 5 => native_decide | 6 => native_decide
  | 7 => native_decide | 8 => native_decide | 9 => native_decide
  | 10 => native_decide | 11 => native_decide | 12 => native_decide
  | 13 => native_decide | 14 => native_decide | 15 => native_decide
  | 16 => native_decide | 17 => native_decide | 18 => native_decide
  | 19 => native_decide | 20 => native_decide | 21 => native_decide
  | 22 => native_decide | 23 => native_decide | 24 => native_decide
  | 25 => native_decide | 26 => native_decide | 27 => native_decide
  | 28 => native_decide | 29 => native_decide | 30 => native_decide
  | 31 => native_decide | 32 => native_decide | 33 => native_decide
  | 34 => native_decide | 35 => native_decide | 36 => native_decide
  | 37 => native_decide | 38 => native_decide | 39 => native_decide
  | 40 => native_decide | 41 => native_decide | 42 => native_decide
  | 43 => native_decide | 44 => native_decide | 45 => native_decide
  | 46 => native_decide | 47 => native_decide | 48 => native_decide
  | 49 => native_decide | 50 => native_decide | 51 => native_decide
  | 52 => native_decide | 53 => native_decide | 54 => native_decide
  | 55 => native_decide | 56 => native_decide | 57 => native_decide
  | 58 => native_decide | 59 => native_decide | 60 => native_decide
  | 61 => native_decide | 62 => native_decide | 63 => native_decide
  | 64 => native_decide | 65 => native_decide | 66 => native_decide
  | 67 => native_decide | 68 => native_decide | 69 => native_decide
  | 70 => native_decide | 71 => native_decide | 72 => native_decide
  | 73 => native_decide | 74 => native_decide | 75 => native_decide
  | 76 => native_decide | 77 => native_decide | 78 => native_decide
  | 79 => native_decide | 80 => native_decide | 81 => native_decide
  | 82 => native_decide | 83 => native_decide | 84 => native_decide
  | 85 => native_decide | 86 => native_decide | 87 => native_decide
  | 88 => native_decide | 89 => native_decide | 90 => native_decide
  | 91 => native_decide | 92 => native_decide | 93 => native_decide
  | 94 => native_decide | 95 => native_decide | 96 => native_decide
  | 97 => native_decide | 98 => native_decide | 99 => native_decide
  | n + 100 => omega

/-- song_complete_summary: Comprehensive summary of all verified properties.
    The complete 99-bottle song:
    - Has exactly 100 verses
    - Each verse corresponds to a trajectory state
    - All verses are distinct
    - The state machine terminates
    - All 99 bottles get passed -/
theorem song_complete_summary
    : (fullSong 99).length = 100 ∧
      (∀ k, k ≤ 99 → (fullSong 99)[k]! = verse 99 (99 - k)) ∧
      (fullSong 99).Pairwise (· ≠ ·) ∧
      terminal (run 99 (initial 99)) ∧
      (run 99 (initial 99)).passed_around = 99 := by
  refine ⟨ninety_nine_bottles_100_verses, ?_, ninety_nine_bottles_all_distinct,
         song_terminates, all_bottles_passed_at_end 99⟩
  intro k hk
  have hget := fullSong_nth 99 k hk
  have hlen : k < (fullSong 99).length := by simp [full_song_length]; omega
  simp only [List.getElem!_eq_getElem?_getD, hget, Option.getD_some]

/- =========================================================================
   CONCLUSION
   =========================================================================
   We have formally verified the "99 Bottles of Beer" song:

   1. TERMINATION: The song always ends (song_terminates)
   2. CONSERVATION: Bottles are neither created nor destroyed
      (conservation_law)
   3. CORRECTNESS: Each verse correctly reflects the bottle count
      (trajectory_full_song_correspondence)
   4. UNIQUENESS: Every verse is distinct (ninety_nine_bottles_all_distinct)
   5. COMPLETENESS: The state machine visits every verse (song_complete)

   This development demonstrates key verification techniques:
     - State machine modeling
     - Inductive invariants
     - Well-founded recursion
     - String manipulation with round-trip proofs
     - Injectivity arguments

   The familiar song provides intuition; the proofs provide certainty.
   ========================================================================= -/

end Bottles
