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

/-! ## Part I: State Machine Model

We model the song as transitions between states. Each state tracks how many
bottles remain on the wall, how many have been passed around, and what we
started with (for the conservation invariant).

**Key insight**: A state machine is just a set of states plus a transition
function. Here our states are triples (on_wall, passed_around, starting_count)
and our transition is "take one down and pass it around." -/

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
instance (s : State) : Decidable (terminal s) :=
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

/-! ## Part II: Core Safety Theorems

We prove that the invariant holds initially and is preserved by each step.
This "inductive invariant" pattern is fundamental to proving properties of
state machines and transition systems.

**The pattern**: To prove a property P holds for all reachable states:
1. Show P holds for the initial state (base case)
2. Show that if P holds for state s, it holds for step(s) (inductive case)
Then P holds everywhere the machine can go. -/

/-- initial_satisfies_invariant: The starting state satisfies conservation.
    This is the "base case" of our inductive invariant argument.

    **Proof idea**: Unfolding definitions, we need to show n + 0 = n, which is
    trivially true by the definition of addition on natural numbers.

    **Why this matters**: This is the anchor for our inductive argument. Without
    a valid starting point, we couldn't prove anything about reachable states. -/
theorem initial_satisfies_invariant
    (n : Nat)                    -- For any starting bottle count n...
    : invariant (initial n)      -- ...the initial state satisfies the invariant.
    := by
  -- Goal: invariant (initial n)
  -- Unfolding: (initial n).on_wall + (initial n).passed_around = (initial n).starting_count
  -- Simplifies to: n + 0 = n, which is definitionally true.
  simp [invariant, initial]

/-- step_preserves_invariant: If a state satisfies the invariant, so does its successor.
    This is the "inductive step"—preservation under transitions.

    **Proof idea**: Case split on whether on_wall is zero or positive.
    - If zero: step is identity, so invariant trivially preserved.
    - If positive: one bottle moves from wall to passed, sum unchanged.

    **The key arithmetic**: If w + p = s and we transition to (w-1) + (p+1),
    the sum is still s because (w-1) + (p+1) = w + p = s. -/
theorem step_preserves_invariant
    (s : State)          -- Given any state s...
    (h : invariant s)    -- ...that satisfies the invariant...
    : invariant (step s) -- ...its successor also satisfies the invariant.
    := by
  -- First, unfold the definitions so we can see what we're proving.
  -- h becomes: s.on_wall + s.passed_around = s.starting_count
  -- Goal becomes: (step s).on_wall + (step s).passed_around = (step s).starting_count
  simp only [invariant, step] at *
  -- Now case split on whether s.on_wall is zero or a successor.
  -- This determines which branch of the match in `step` we take.
  cases hs : s.on_wall with
  | zero =>
    -- Case: s.on_wall = 0, so step s = s (the song is over, no change).
    -- The invariant h already says 0 + s.passed_around = s.starting_count.
    -- After step, nothing changes, so the same equation holds.
    simp [hs] at *
    exact h
  | succ k =>
    -- Case: s.on_wall = k + 1 for some k ≥ 0.
    -- After step: on_wall becomes k, passed_around becomes s.passed_around + 1.
    -- We need: k + (s.passed_around + 1) = s.starting_count.
    -- From h: (k + 1) + s.passed_around = s.starting_count.
    -- Rearranging: k + s.passed_around + 1 = s.starting_count. QED.
    simp [hs] at *
    omega

/-- step_preserves_starting_count: The starting count never changes.
    This is obvious but useful as a rewrite lemma.

    **Why we need this**: Many proofs need to know that starting_count is
    constant throughout execution. Having an explicit lemma lets us rewrite
    (step s).starting_count to s.starting_count automatically. -/
theorem step_preserves_starting_count
    (s : State)                                    -- For any state s...
    : (step s).starting_count = s.starting_count   -- ...step preserves starting_count.
    := by
  -- Unfold step to see its definition.
  simp only [step]
  -- Case split on s.on_wall. In both cases, starting_count is unchanged.
  -- Case 0: step returns s unchanged, so starting_count = starting_count.
  -- Case n+1: step returns a new record with same starting_count field.
  cases s.on_wall <;> rfl

/-- step_decreases_or_terminal: Each step either terminates or makes progress.
    This is crucial for termination: we can't loop forever.

    **Termination argument**: This is a disjunction (OR). Either:
    - LEFT: We're already terminal (on_wall = 0), or
    - RIGHT: Taking a step strictly decreases on_wall.

    Since on_wall is a natural number that decreases each non-terminal step,
    we must eventually reach terminal. This is well-founded recursion. -/
theorem step_decreases_or_terminal
    (s : State)                                  -- For any state s...
    : terminal s ∨ (step s).on_wall < s.on_wall  -- ...either terminal or progressing.
    := by
  -- Case split: is s.on_wall zero or positive?
  cases hs : s.on_wall with
  | zero =>
    -- s.on_wall = 0 means we're terminal.
    -- Choose the LEFT disjunct: terminal s.
    left
    -- terminal s means s.on_wall = 0, which we just established.
    simp [terminal, hs]
  | succ k =>
    -- s.on_wall = k + 1 means we can take a step.
    -- Choose the RIGHT disjunct: (step s).on_wall < s.on_wall.
    right
    -- After step, on_wall becomes k, and k < k + 1.
    simp [step, hs]

/-- terminal_is_fixpoint: Once terminal, step has no effect.
    The song is over; taking another step doesn't change anything.

    **Fixpoint**: A state s is a fixpoint of step if step(s) = s. Terminal
    states are fixpoints because the match on on_wall = 0 returns s unchanged.

    **Why this matters**: This ensures we don't "overshoot" terminal. Running
    extra steps after finishing the song is harmless—we stay at the end. -/
theorem terminal_is_fixpoint
    (s : State)        -- For any state s...
    (h : terminal s)   -- ...that is terminal (on_wall = 0)...
    : step s = s       -- ...step s equals s unchanged.
    := by
  -- h says terminal s, which unfolds to s.on_wall = 0.
  simp only [terminal] at h
  -- Now simplify step using h. The match sees on_wall = 0 and returns s.
  simp only [step, h]

/-! ## Part III: Execution and Termination

We define a "fuel-based" execution model: run n steps and see where we end up.
Then we prove that sufficient fuel always reaches terminal state, establishing
termination of the song.

**Why fuel?** Lean requires all functions to terminate. By passing explicit
"fuel" (a natural number that decreases each step), we guarantee termination
structurally. The key theorem shows that fuel = on_wall is always sufficient. -/

/-- run: Execute the state machine for a fixed number of steps.
    This defines a recursive function; fuel decreases each call.

    **How it works**: run is structurally recursive on fuel. Each recursive
    call decreases fuel by 1, guaranteeing termination. The function applies
    `step` once, then recurses with the stepped state and decremented fuel.

    **Example**: run 3 s = run 2 (step s) = run 1 (step (step s)) = step (step (step s))

    **Note**: We step FIRST, then recurse. So run n s applies n steps total. -/
def run
    (fuel : Nat)   -- Number of steps to execute (decreases each recursive call).
    (s : State)    -- Starting state for this batch of steps.
    : State        -- Ending state after applying `fuel` steps to s.
    := match fuel with
       | 0 =>
         -- Base case: no fuel left, return the current state unchanged.
         s
       | n + 1 =>
         -- Recursive case: apply one step, then recurse with n remaining.
         -- Lean sees that n < n + 1, so this terminates.
         run n (step s)

/-- run_preserves_invariant: Running any number of steps preserves the invariant.
    By induction: base case is trivial, inductive case uses step_preserves_invariant.

    **Proof technique**: This is a classic induction on the fuel parameter.
    - Base case (fuel = 0): run 0 s = s, and we already know invariant s.
    - Inductive case (fuel = k + 1): run (k+1) s = run k (step s).
      By step_preserves_invariant, invariant (step s) holds.
      By IH applied to (step s), invariant (run k (step s)) holds.

    **Key insight**: The invariant is "closed under step," so it's closed under
    any finite number of steps. This is the power of inductive invariants. -/
theorem run_preserves_invariant
    (fuel : Nat)         -- Number of steps to run.
    (s : State)          -- Starting state.
    (h : invariant s)    -- Assumption: starting state satisfies invariant.
    : invariant (run fuel s)  -- Conclusion: ending state satisfies invariant.
    := by
  -- Induction on fuel. The `generalizing s` lets the IH apply to any state.
  induction fuel generalizing s with
  | zero =>
    -- Base case: run 0 s = s by definition.
    -- We need invariant s, which is exactly our hypothesis h.
    exact h
  | succ k ih =>
    -- Inductive case: run (k+1) s = run k (step s) by definition.
    -- We need invariant (run k (step s)).
    -- By step_preserves_invariant: invariant (step s).
    -- By IH applied to (step s): invariant (run k (step s)).
    exact ih (step s) (step_preserves_invariant s h)

/-- run_preserves_starting_count: Running preserves the starting count.
    Follows from step_preserves_starting_count by induction.

    **Why this matters**: We often need to know that starting_count stays
    constant throughout execution to connect final states back to initial. -/
theorem run_preserves_starting_count
    (fuel : Nat)                                   -- Number of steps.
    (s : State)                                    -- Starting state.
    : (run fuel s).starting_count = s.starting_count  -- starting_count unchanged.
    := by
  induction fuel generalizing s with
  | zero =>
    -- run 0 s = s, so starting_count is trivially preserved.
    rfl
  | succ k ih =>
    -- run (k+1) s = run k (step s)
    -- By IH: (run k (step s)).starting_count = (step s).starting_count
    -- By step_preserves_starting_count: (step s).starting_count = s.starting_count
    simp [run]
    rw [ih, step_preserves_starting_count]

/-- run_reaches_zero: With enough fuel equal to on_wall, we reach zero bottles.
    This is the key lemma: fuel = on_wall is sufficient for termination.

    **The key insight**: If we start with w bottles and run w steps, we end
    with 0 bottles. Each step decreases on_wall by 1 (when positive), so
    after exactly w steps, we've counted down to zero.

    **Proof**: By induction on w. If w = 0, we're already at zero. If w = k+1,
    one step gives us k bottles, and by IH, k more steps reach zero. -/
theorem run_reaches_zero
    (w p st : Nat)  -- on_wall, passed_around, starting_count
    : (run w { on_wall := w, passed_around := p, starting_count := st }).on_wall = 0
    := by
  -- Induction on w (the bottle count / fuel amount).
  -- We generalize p because it changes each step but doesn't affect the result.
  induction w generalizing p with
  | zero =>
    -- Base case: w = 0, so on_wall is already 0.
    -- run 0 s = s, and s.on_wall = 0.
    rfl
  | succ k ih =>
    -- Inductive case: w = k + 1.
    -- run (k+1) s = run k (step s)
    -- After step: on_wall becomes k, passed_around becomes p + 1.
    -- By IH with on_wall = k: the result has on_wall = 0.
    simp [run, step]
    exact ih (p + 1)

/-- sufficient_fuel_reaches_terminal: Starting with on_wall fuel always terminates.
    This establishes that the song ALWAYS ends—no infinite loops possible.

    **The termination guarantee**: For ANY state s, if we run s.on_wall steps,
    we reach a terminal state. This is unconditional—every execution terminates.

    **Proof**: Destructure s into its fields, then apply run_reaches_zero. -/
theorem sufficient_fuel_reaches_terminal
    (s : State)                    -- For any state s...
    : terminal (run s.on_wall s)   -- ...running on_wall steps reaches terminal.
    := by
  -- Unfold terminal to: (run s.on_wall s).on_wall = 0
  simp only [terminal]
  -- Destructure s into { on_wall := w, passed_around := p, starting_count := st }
  -- Then apply run_reaches_zero which proves exactly this.
  cases s with
  | mk w p st => exact run_reaches_zero w p st

/-- song_terminates: The classic 99-bottle song terminates.
    Verified by direct computation (native_decide).

    **What native_decide does**: Lean evaluates (run 99 (initial 99)).on_wall
    at compile time and checks that it equals 0. This is a PROOF by computation—
    if the check succeeds, the theorem is proven; if it fails, compilation fails.

    **Trust**: We're not "trusting" the computation; we're using Lean's kernel
    to verify that the computation produces the expected result. -/
theorem song_terminates
    : terminal (run 99 (initial 99))  -- The 99-bottle song reaches terminal.
    := by
  -- Let Lean compute (run 99 (initial 99)).on_wall and verify it's 0.
  native_decide

/-- all_bottles_passed_at_end: At termination, all bottles have been passed.
    Combines invariant preservation with termination.

    **The connection**: We know three things at the end:
    1. on_wall = 0 (from termination)
    2. on_wall + passed_around = starting_count (from invariant)
    3. starting_count = n (from run_preserves_starting_count)
    Combining: 0 + passed_around = n, so passed_around = n.

    **Why this matters**: This proves the song is "complete"—every bottle that
    started on the wall gets passed around exactly once. -/
theorem all_bottles_passed_at_end
    (n : Nat)                               -- For any starting count n...
    : (run n (initial n)).passed_around = n -- ...all n bottles are passed at the end.
    := by
  -- Gather our three key facts:
  -- hinv: The invariant holds after running n steps from initial n.
  have hinv := run_preserves_invariant n (initial n) (initial_satisfies_invariant n)
  -- hterm: After n steps, we're terminal (on_wall = 0).
  have hterm := sufficient_fuel_reaches_terminal (initial n)
  -- hst: starting_count is still n after running.
  have hst := run_preserves_starting_count n (initial n)
  -- Unfold all the definitions to expose the arithmetic.
  simp only [invariant, terminal, initial] at *
  -- Now we have: 0 + passed = starting, starting = n.
  -- omega solves: passed = n.
  omega

/-! ## Part IV: Trajectory Analysis

We prove that the sequence of states forms a monotonic trajectory: bottles on
wall never increases, bottles passed never decreases. This captures the
"one-way" nature of the song's progress.

**Monotonicity matters**: These lemmas establish that the song makes steady
progress toward termination. You can't "un-pass" a bottle. Each step either
decreases on_wall or leaves the state unchanged (at terminal). -/

/-- monotonic_decreasing: A function from Nat to State has non-increasing on_wall.

    **What this means**: If we look at states at times i and j with i ≤ j,
    the later state (j) has fewer or equal bottles on wall than the earlier (i).
    In other words, bottles never magically reappear on the wall. -/
def monotonic_decreasing
    (f : Nat → State)  -- A function mapping time steps to states.
    : Prop             -- Returns a proposition (provable or not).
    := ∀ i j,          -- For all time steps i and j...
       i ≤ j →         -- ...if i comes before or at j...
       (f j).on_wall ≤ (f i).on_wall  -- ...then j has ≤ bottles than i.

/-- trajectory: The sequence of states reached by running 0, 1, 2, ... steps.

    **Intuition**: trajectory s is an infinite sequence of states:
    trajectory s 0 = s
    trajectory s 1 = run 1 s = step s
    trajectory s 2 = run 2 s = step (step s)
    ...and so on.

    This captures the complete history of the state machine's execution. -/
def trajectory
    (s : State)        -- Starting state.
    : Nat → State      -- Returns a function from time to state.
    := fun i => run i s  -- The state at time i is run i s.

/-- step_nonincreasing: Taking a step never increases bottles on wall.

    **The one-step guarantee**: Either on_wall stays the same (at terminal) or
    decreases by exactly 1. It NEVER increases. This is the building block
    for all our monotonicity results. -/
theorem step_nonincreasing
    (s : State)                        -- For any state s...
    : (step s).on_wall ≤ s.on_wall     -- ...step doesn't increase on_wall.
    := by
  -- Case split on whether we're at zero or positive bottles.
  cases hs : s.on_wall with
  | zero =>
    -- At 0 bottles: step s = s, so on_wall unchanged. 0 ≤ 0. ✓
    simp [step, hs]
  | succ k =>
    -- At k+1 bottles: step gives k bottles. k ≤ k+1. ✓
    simp [step, hs]

/-- no_bottles_created: Running never creates new bottles on wall.
    Bottles can only decrease or stay the same.

    **The multi-step guarantee**: Extending step_nonincreasing to any number
    of steps. No matter how many steps we take, we never end up with MORE
    bottles than we started with.

    **Proof**: By induction on fuel, using step_nonincreasing at each step. -/
theorem no_bottles_created
    (s : State)                        -- Starting state.
    (fuel : Nat)                       -- Number of steps to run.
    : (run fuel s).on_wall ≤ s.on_wall -- After running, on_wall is ≤ original.
    := by
  -- Induct on fuel; generalize s so IH applies to any starting state.
  induction fuel generalizing s with
  | zero =>
    -- run 0 s = s, so on_wall is unchanged. Trivially ≤.
    simp [run]
  | succ k ih =>
    -- run (k+1) s = run k (step s)
    -- We need: (run k (step s)).on_wall ≤ s.on_wall
    simp only [run]
    -- Use calc mode to chain inequalities:
    calc (run k (step s)).on_wall
        ≤ (step s).on_wall := ih (step s)  -- By IH: running k steps from step s
      _ ≤ s.on_wall := step_nonincreasing s -- By step_nonincreasing

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

/-! ## Part V: Reachability

We define reachability as an inductive relation: a state is reachable from
another if we can get there by zero or more steps. This gives us a more
abstract way to reason about the state machine.

**Inductive relations**: Instead of counting steps, we say "s' is reachable
from s if s' = s, or if s' = step(s'') for some reachable s''." This captures
the transitive closure of the step relation. -/

/-- Reachable: Inductive definition of reachability.
    s' is reachable from s0 if:
    - s' = s0 (reflexive base case), or
    - s' = step s for some reachable s (transitive step case).

    **Why inductive?** An inductive relation is defined by its constructors.
    To prove Reachable s0 s', you must build a proof using these constructors.
    To use a proof of Reachable s0 s', you case-split on which constructor made it.

    **Alternative view**: Reachable s0 s' means there exists a finite sequence
    s0 → s1 → s2 → ... → s' where each arrow is one step. The inductive
    definition captures this without explicitly mentioning sequences.

    **Notation**: Reachable s0 s' is sometimes written s0 →* s' in the literature
    (the reflexive-transitive closure of the step relation). -/
inductive Reachable
    (s0 : State)     -- The starting state (fixed for all constructors).
    : State → Prop   -- Takes an ending state, returns a proposition.
    where
  | refl :
    -- Base case: every state is reachable from itself (0 steps).
    Reachable s0 s0
  | step (s : State) :
    -- Inductive case: if s is reachable from s0, so is step(s).
    -- This adds one more step to the path.
    Reachable s0 s → Reachable s0 (step s)

/-- reachable_trans: Reachability is transitive.
    If s1 is reachable from s0 and s2 is reachable from s1,
    then s2 is reachable from s0.

    **Why this matters**: Transitivity lets us chain reachability proofs.
    If we know s0 →* s1 and s1 →* s2, we get s0 →* s2.

    **Proof**: Induction on the proof of Reachable s1 s2.
    - If s2 = s1 (refl): s0 →* s1 = s0 →* s2. ✓
    - If s2 = step(s) where s1 →* s (step case): By IH, s0 →* s.
      Then Reachable.step gives s0 →* step(s) = s0 →* s2. ✓ -/
theorem reachable_trans
    (s0 s1 s2 : State)             -- Three states in a chain.
    (h1 : Reachable s0 s1)         -- s0 can reach s1.
    (h2 : Reachable s1 s2)         -- s1 can reach s2.
    : Reachable s0 s2              -- Therefore s0 can reach s2.
    := by
  -- Induct on how s2 is reachable from s1.
  induction h2 with
  | refl =>
    -- Case: s2 = s1 (zero steps from s1 to s2).
    -- We need Reachable s0 s1, which is exactly h1.
    exact h1
  | step s _ ih =>
    -- Case: s2 = step(s) where Reachable s1 s.
    -- ih : Reachable s0 s (by induction hypothesis).
    -- We need Reachable s0 (step s).
    -- Apply the step constructor to ih.
    exact Reachable.step s ih

/-- reachable_run: Any state reached by run is reachable.
    This connects our fuel-based execution to the abstract reachability.

    **The bridge**: We have two ways to describe execution:
    1. run fuel s: concrete, computable, needs fuel parameter
    2. Reachable s s': abstract, logical, no fuel needed

    This theorem proves they agree: run always produces reachable states.

    **Proof**: Induction on fuel.
    - fuel = 0: run 0 s = s, and Reachable.refl gives s →* s.
    - fuel = k+1: run (k+1) s = run k (step s).
      By IH, step(s) →* run k (step s).
      By Reachable.step, s →* step(s).
      By transitivity, s →* run k (step s). -/
theorem reachable_run
    (fuel : Nat)                       -- Number of steps to run.
    (s : State)                        -- Starting state.
    : Reachable s (run fuel s)         -- The ending state is reachable from s.
    := by
  induction fuel generalizing s with
  | zero => exact Reachable.refl
  | succ k ih =>
    simp only [run]
    exact reachable_trans s (step s) (run k (step s)) (Reachable.step s Reachable.refl) (ih (step s))

/-- reachable_preserves_invariant: Invariant holds for all reachable states.
    If we start satisfying the invariant, every reachable state does too.

    **The power of inductive invariants**: This theorem says that if you start
    in a "good" state (satisfying the invariant), you can NEVER reach a "bad"
    state. The invariant is an impenetrable barrier.

    **Proof**: Induction on the reachability proof.
    - refl case: s = s0, and hinv says s0 satisfies the invariant.
    - step case: s = step(s') where s' is reachable. By IH, s' satisfies
      the invariant. By step_preserves_invariant, step(s') does too. -/
theorem reachable_preserves_invariant
    (s0 s : State)                  -- Starting and ending states.
    (hinv : invariant s0)           -- Starting state satisfies invariant.
    (hreach : Reachable s0 s)       -- Ending state is reachable.
    : invariant s                   -- Therefore ending state satisfies invariant.
    := by
  -- Induct on how s is reachable from s0.
  induction hreach with
  | refl =>
    -- Case: s = s0. We need invariant s0, which is hinv.
    exact hinv
  | step _ _ ih =>
    -- Case: s = step(prev) where prev is reachable.
    -- ih : invariant prev (by induction)
    -- We need invariant (step prev).
    exact step_preserves_invariant _ ih

/-- reachable_terminal_exists: From any state, a terminal state is reachable.
    This is another way to state termination.

    **Existential termination**: Instead of saying "run n s is terminal," we say
    "there EXISTS a terminal state reachable from s." This is a more abstract
    formulation that doesn't mention fuel.

    **Proof**: Witness the state (run s.on_wall s). We've already proven:
    1. It's reachable (by reachable_run)
    2. It's terminal (by sufficient_fuel_reaches_terminal) -/
theorem reachable_terminal_exists
    (s : State)                              -- For any state s...
    : ∃ s', Reachable s s' ∧ terminal s'     -- ...there's a reachable terminal state.
    :=
  -- Construct the witness explicitly using angle-bracket notation.
  -- ⟨witness, proof1, proof2⟩ proves ∃ x, P x ∧ Q x.
  ⟨run s.on_wall s,                          -- The witness: run enough steps.
   reachable_run s.on_wall s,                -- Proof it's reachable.
   sufficient_fuel_reaches_terminal s⟩       -- Proof it's terminal.

/-! ## Part VI: String Conversion

To generate actual verse text, we need to convert numbers to strings. This
section defines nat↔string conversion functions and proves they are inverses
(round-trip property).

**Why verify string conversion?** Bugs in number formatting are common and
subtle (off-by-one, wrong base, missing leading zeros). By proving round-trip
properties, we ensure our natToString and stringToNat are correct inverses. -/

/-- digitToChar: Convert a single digit (0-9) to its ASCII character.
    For inputs ≥ 10, returns '9' (but we only use this for valid digits).

    **ASCII encoding**: The characters '0' through '9' have consecutive ASCII
    codes (48-57). We could compute '0'.toNat + d, but explicit matching is
    clearer and easier to prove properties about.

    **Totality**: Every Nat maps to some Char. Inputs ≥ 10 all map to '9'.
    This makes the function total without requiring a proof that d < 10. -/
def digitToChar
    (d : Nat)   -- A digit value (0-9 for correct behavior).
    : Char      -- The corresponding ASCII character.
    := match d with
       | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
       | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | _ => '9'

/-- digitToString: Convert a digit to a single-character string.

    **Composition**: This is just digitToChar wrapped in String.singleton.
    Separating these makes proofs cleaner—we can reason about the Char
    separately from the String wrapper. -/
def digitToString
    (d : Nat)   -- A digit value.
    : String    -- A single-character string like "7".
    := String.singleton (digitToChar d)

/-- natToStringAux: Auxiliary function for nat→string conversion.
    Uses fuel to ensure termination; builds string right-to-left.

    **Algorithm**: Extract digits from right to left using mod 10 / div 10,
    prepending each digit to an accumulator string.
    - n % 10 gives the rightmost digit (ones place).
    - n / 10 gives the remaining digits (tens place and up).

    **Example**: For n = 42:
    - First iteration: d = 2, r = 4, acc' = "2"
    - Second iteration: d = 4, r = 0, acc' = "42"
    - r = 0, so return "42".

    **Fuel**: We use n itself as fuel (upper bound on iterations needed). -/
def natToStringAux
    (fuel : Nat)   -- Countdown to guarantee termination.
    (n : Nat)      -- The number being converted.
    (acc : String) -- Accumulated string (builds right-to-left).
    : String       -- Final string representation.
    := match fuel with
       | 0 => acc    -- Out of fuel: return what we have.
       | f + 1 =>
         let d := n % 10                    -- Rightmost digit (ones place).
         let r := n / 10                    -- Remaining number (tens and up).
         let acc' := digitToString d ++ acc -- Prepend this digit to accumulator.
         match r with
         | 0 => acc'                        -- No more digits: we're done.
         | _ => natToStringAux f r acc'     -- More digits: recurse.

/-- natToString: Convert a natural number to its decimal string representation.
    Special case for 0 to avoid empty string.

    **Why special-case zero?** Our algorithm extracts digits by repeated
    division. For n = 0, the first d = 0 % 10 = 0, r = 0 / 10 = 0, so we'd
    return "" if acc started empty. Special-casing avoids this.

    **Fuel choice**: We pass n as fuel. Since n / 10 < n for n > 0, we have
    enough fuel to extract all digits. (For n = 0, we special-case anyway.) -/
def natToString
    (n : Nat)   -- The number to convert.
    : String    -- Its decimal string representation like "42".
    := match n with
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

/-- charToDigit_some_lt: If charToDigit returns some d, then d < 10. -/
theorem charToDigit_some_lt (c : Char) (d : Nat) (h : charToDigit c = some d) : d < 10 := by
  simp only [charToDigit] at h
  split at h
  all_goals (first | (injection h with h; omega) | (simp at h))

/-- digitToCharToDigit: Inverse round-trip: char→digit→char preserves digit chars.
    If charToDigit c = some d, then digitToChar d = c.
    Proved by first extracting that d < 10, then case analysis on d. -/
theorem digitToCharToDigit (c : Char) (d : Nat) (h : charToDigit c = some d)
    : digitToChar d = c := by
  have hd := charToDigit_some_lt c d h
  match d with
  | 0 => simp only [charToDigit] at h; split at h <;> simp_all [digitToChar]
  | 1 => simp only [charToDigit] at h; split at h <;> simp_all [digitToChar]
  | 2 => simp only [charToDigit] at h; split at h <;> simp_all [digitToChar]
  | 3 => simp only [charToDigit] at h; split at h <;> simp_all [digitToChar]
  | 4 => simp only [charToDigit] at h; split at h <;> simp_all [digitToChar]
  | 5 => simp only [charToDigit] at h; split at h <;> simp_all [digitToChar]
  | 6 => simp only [charToDigit] at h; split at h <;> simp_all [digitToChar]
  | 7 => simp only [charToDigit] at h; split at h <;> simp_all [digitToChar]
  | 8 => simp only [charToDigit] at h; split at h <;> simp_all [digitToChar]
  | 9 => simp only [charToDigit] at h; split at h <;> simp_all [digitToChar]
  | _ + 10 => omega

/-- div10_lt: Dividing a positive number by 10 yields a smaller number.
    Key lemma for termination arguments. -/
theorem div10_lt (n : Nat) (h : n > 0) : n / 10 < n :=
  Nat.div_lt_self h (by omega)

/-- String.singleton_length: String.singleton always produces a length-1 string. -/
theorem String.singleton_length (c : Char) : (String.singleton c).length = 1 := by
  simp only [String.singleton, String.length, String.toList_push]
  rfl

/-- digitToString_length: A digit string has length 1.
    This holds for ALL d, not just d < 10, because digitToChar maps everything ≥10 to '9'. -/
theorem digitToString_length (d : Nat) : (digitToString d).length = 1 := by
  simp only [digitToString]
  exact String.singleton_length (digitToChar d)

/-- single_digit_length: Single digits (0-9) produce length-1 strings. -/
theorem single_digit_length (n : Nat) (h : n < 10) : (natToString n).length = 1 := by
  match n with
  | 0 => native_decide | 1 => native_decide | 2 => native_decide
  | 3 => native_decide | 4 => native_decide | 5 => native_decide
  | 6 => native_decide | 7 => native_decide | 8 => native_decide
  | 9 => native_decide | n + 10 => omega

/-- double_digit_length: Two-digit numbers (10-99) produce length-2 strings. -/
theorem double_digit_length (n : Nat) (h1 : 10 ≤ n) (h2 : n < 100) : (natToString n).length = 2 := by
  match n with
  | 0 => omega | 1 => omega | 2 => omega | 3 => omega | 4 => omega
  | 5 => omega | 6 => omega | 7 => omega | 8 => omega | 9 => omega
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

/-- digitToString_inj: digitToString is injective on digits 0-9.
    Proved by exhaustive computation. -/
theorem digitToString_inj (d1 d2 : Nat) (h1 : d1 < 10) (h2 : d2 < 10)
    (heq : digitToString d1 = digitToString d2) : d1 = d2 := by
  match d1, d2 with
  | 0, 0 => rfl | 1, 1 => rfl | 2, 2 => rfl | 3, 3 => rfl | 4, 4 => rfl
  | 5, 5 => rfl | 6, 6 => rfl | 7, 7 => rfl | 8, 8 => rfl | 9, 9 => rfl
  | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 | 0, 6 | 0, 7 | 0, 8 | 0, 9 =>
    simp [digitToString, digitToChar, String.singleton] at heq
  | 1, 0 | 1, 2 | 1, 3 | 1, 4 | 1, 5 | 1, 6 | 1, 7 | 1, 8 | 1, 9 =>
    simp [digitToString, digitToChar, String.singleton] at heq
  | 2, 0 | 2, 1 | 2, 3 | 2, 4 | 2, 5 | 2, 6 | 2, 7 | 2, 8 | 2, 9 =>
    simp [digitToString, digitToChar, String.singleton] at heq
  | 3, 0 | 3, 1 | 3, 2 | 3, 4 | 3, 5 | 3, 6 | 3, 7 | 3, 8 | 3, 9 =>
    simp [digitToString, digitToChar, String.singleton] at heq
  | 4, 0 | 4, 1 | 4, 2 | 4, 3 | 4, 5 | 4, 6 | 4, 7 | 4, 8 | 4, 9 =>
    simp [digitToString, digitToChar, String.singleton] at heq
  | 5, 0 | 5, 1 | 5, 2 | 5, 3 | 5, 4 | 5, 6 | 5, 7 | 5, 8 | 5, 9 =>
    simp [digitToString, digitToChar, String.singleton] at heq
  | 6, 0 | 6, 1 | 6, 2 | 6, 3 | 6, 4 | 6, 5 | 6, 7 | 6, 8 | 6, 9 =>
    simp [digitToString, digitToChar, String.singleton] at heq
  | 7, 0 | 7, 1 | 7, 2 | 7, 3 | 7, 4 | 7, 5 | 7, 6 | 7, 8 | 7, 9 =>
    simp [digitToString, digitToChar, String.singleton] at heq
  | 8, 0 | 8, 1 | 8, 2 | 8, 3 | 8, 4 | 8, 5 | 8, 6 | 8, 7 | 8, 9 =>
    simp [digitToString, digitToChar, String.singleton] at heq
  | 9, 0 | 9, 1 | 9, 2 | 9, 3 | 9, 4 | 9, 5 | 9, 6 | 9, 7 | 9, 8 =>
    simp [digitToString, digitToChar, String.singleton] at heq
  | 0, _ + 10 | 1, _ + 10 | 2, _ + 10 | 3, _ + 10 | 4, _ + 10 => omega
  | 5, _ + 10 | 6, _ + 10 | 7, _ + 10 | 8, _ + 10 | 9, _ + 10 => omega
  | _ + 10, _ => omega

/-- natToStringAux_acc_append: Accumulator can be split via append.
    Building with acc1++acc2 equals building with acc1 then appending acc2.
    This is the key structural lemma for natToString. -/
theorem natToStringAux_acc_append (f n : Nat) (acc1 acc2 : String)
    : natToStringAux f n (acc1 ++ acc2) = natToStringAux f n acc1 ++ acc2 := by
  induction f generalizing n acc1 with
  | zero => rfl
  | succ f' ih =>
    simp only [natToStringAux]
    match n / 10 with
    | 0 => simp only [String.append_assoc]
    | _ + 1 =>
      have : digitToString (n % 10) ++ (acc1 ++ acc2) =
             (digitToString (n % 10) ++ acc1) ++ acc2 := by
        simp only [String.append_assoc]
      rw [this]
      exact ih _ (digitToString (n % 10) ++ acc1)

/-- natToStringAux_acc_empty: Appending to empty acc equals appending after. -/
theorem natToStringAux_acc_empty (f n : Nat) (acc : String)
    : natToStringAux f n acc = natToStringAux f n "" ++ acc := by
  calc natToStringAux f n acc
      = natToStringAux f n ("" ++ acc) := by simp
    _ = natToStringAux f n "" ++ acc := natToStringAux_acc_append f n "" acc

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

/-- stringToNat_zero: "0" parses to 0. -/
theorem stringToNat_zero : stringToNat "0" = some 0 := by native_decide

/-- stringToNat_single: Single digit strings parse correctly. -/
theorem stringToNat_single (d : Nat) (h : d < 10) : stringToNat (digitToString d) = some d := by
  match d with
  | 0 => native_decide | 1 => native_decide | 2 => native_decide
  | 3 => native_decide | 4 => native_decide | 5 => native_decide
  | 6 => native_decide | 7 => native_decide | 8 => native_decide
  | 9 => native_decide | n + 10 => omega

/-- stringToNatAux_empty: Empty string returns accumulator. -/
theorem stringToNatAux_empty : stringToNatAux "" 0 = some 0 := by native_decide

/-- string_neq_first_char: Strings with different first chars are not equal. -/
theorem string_neq_first_char (s1 s2 : String) (c1 c2 : Char)
    (h1 : s1.toList.head? = some c1) (h2 : s2.toList.head? = some c2) (hne : c1 ≠ c2)
    : s1 ≠ s2 := by
  intro heq
  rw [heq] at h1
  rw [h1] at h2
  injection h2 with h2'
  exact hne h2'

/-! ## Part VII: Verse Generation

We define functions to generate the actual verse text. Each verse depends on
the bottle count, using singular/plural grammar and special handling for the
final verse (0 bottles).

**Grammar matters**: "1 bottle" vs "2 bottles" and "No more bottles" require
careful case analysis. The verse function handles all three cases: zero (final
verse with "Go to the store"), one (singular), and n+2 (plural). -/

/-- bottleWord: Returns "bottle" (singular) or "bottles" (plural).
    English grammar requires singular for exactly 1 bottle.

    **English morphology**: Most English nouns form plurals by adding 's'.
    We only need the singular form for exactly one bottle; everything else
    (including zero) uses plural: "0 bottles", "1 bottle", "2 bottles".

    **Note**: "No more bottles" always uses plural, handled separately. -/
def bottleWord
    (n : Nat)   -- The bottle count.
    : String    -- "bottle" or "bottles".
    := match n with
       | 1 => "bottle"   -- Singular: exactly one.
       | _ => "bottles"  -- Plural: zero, two, three, ...

/-- countPhrase: Generates "N bottle(s)" or "No more bottles" for count n.

    **Three cases**:
    - n = 0: "No more bottles" (special phrasing for zero)
    - n = 1: "1 bottle" (singular)
    - n ≥ 2: "N bottles" (plural)

    **Composition**: Uses natToString for the number and bottleWord for grammar. -/
def countPhrase
    (n : Nat)   -- The bottle count.
    : String    -- Human-readable phrase like "42 bottles" or "No more bottles".
    := match n with
       | 0 => "No more bottles"                  -- Special case for zero.
       | _ => natToString n ++ " " ++ bottleWord n  -- "N bottle(s)".

/-- verse: Generate a complete verse for the song.
    start is the original bottle count (for the final verse).
    n is the current bottle count.

    **Structure of a verse**:
    - For n > 0: "[N bottles] of beer on the wall, [N bottles] of beer.
                  Take one down and pass it around, [N-1 bottles] of beer on the wall."
    - For n = 0: "No more bottles of beer on the wall, no more bottles of beer.
                  Go to the store and buy some more, [start bottles] of beer on the wall."

    **The start parameter**: Only matters for verse 0, where we reference how
    many bottles to buy to restart. For positive verses, start is ignored.

    **Verb agreement**: "Take one down" is singular because we always take exactly
    one bottle, regardless of how many remain. -/
def verse
    (start : Nat)  -- Original bottle count (for final verse's "buy some more").
    (n : Nat)      -- Current bottle count (which verse to generate).
    : String       -- The complete verse text.
    := match n with
       | 0 =>
         -- Final verse: "No more bottles... Go to the store..."
         -- References 'start' to say how many to buy.
         "No more bottles of beer on the wall, no more bottles of beer. " ++
         "Go to the store and buy some more, " ++
         natToString start ++ " " ++ bottleWord start ++ " of beer on the wall."
       | k + 1 =>
         -- Regular verse: "N bottles... Take one down..."
         -- Note: after taking one down, we have k bottles (one less than k+1).
         countPhrase (k + 1) ++ " of beer on the wall, " ++
         countPhrase (k + 1) ++ " of beer. " ++
         "Take one down and pass it around, " ++
         countPhrase k ++ " of beer on the wall."

/-- currentVerse: Get the verse for the current state.
    Uses starting_count and on_wall to determine the verse.

    **State-to-verse mapping**: This connects our abstract state machine to
    concrete verse text. The state's on_wall field determines which verse
    we're at; starting_count is passed for the final verse. -/
def currentVerse
    (s : State)   -- The current state of the song.
    : String      -- The verse corresponding to this state.
    := verse s.starting_count s.on_wall

/-- fullSongAux: Build the complete song list recursively.
    Collects verses from count n down to 0.

    **Algorithm**: We count DOWN from n to 0, appending each verse to acc.
    The recursion goes: n, n-1, n-2, ..., 1, 0.
    Final list order: [verse n, verse (n-1), ..., verse 1, verse 0].

    **Accumulator pattern**: We build the list left-to-right using an
    accumulator. Each recursive call appends one verse to acc. -/
def fullSongAux
    (start : Nat)      -- Original bottle count (passed to verse).
    (n : Nat)          -- Current countdown value.
    (acc : List String) -- Accumulated verses so far.
    : List String       -- Final list of all verses.
    := match n with
       | 0 =>
         -- Base case: append the final verse (verse 0) and we're done.
         acc ++ [verse start 0]
       | k + 1 =>
         -- Recursive case: append verse (k+1), then recurse for verses k..0.
         fullSongAux start k (acc ++ [verse start (k + 1)])

/-- fullSong: Generate the complete list of verses for a song.
    Returns n+1 verses for a song starting with n bottles.

    **The complete song**: For a song starting with n bottles, we get:
    - Verse n (first verse: "n bottles...")
    - Verse n-1
    - ...
    - Verse 1 ("1 bottle...")
    - Verse 0 (final verse: "No more bottles... Go to the store...")

    That's n+1 verses total (from n down to 0 inclusive). -/
def fullSong
    (start : Nat)    -- Starting bottle count.
    : List String    -- List of all verses in order.
    := fullSongAux start start []  -- Start countdown from 'start', empty accumulator.

-- Test verse generation.
#eval verse 99 99  -- First verse
#eval verse 99 1   -- Singular bottle verse
#eval verse 99 0   -- Final verse
#eval (fullSong 5).length  -- Should be 6

/-! ## Part VIII: Verse Structure Lemmas

We prove structural properties of verses: grammar correctness, length bounds,
and that different counts produce different verses. These support the main
injectivity theorem.

**Building toward injectivity**: To prove verse n1 ≠ verse n2 when n1 ≠ n2, we
need structural lemmas: verse 0 starts with 'N', positive verses start with
digits, and we can extract the leading number from a verse. -/

/-- verse_one_singular: Verse for 1 bottle uses singular "bottle".

    **Grammar test**: This theorem verifies that when n = 1, we correctly
    use "bottle" (singular) not "bottles" (plural). This is the only verse
    where singular form appears (except in "Take one down"). -/
theorem verse_one_singular
    (start : Nat)  -- The starting count (ignored for verse 1).
    : verse start 1 =
      "1 bottle of beer on the wall, 1 bottle of beer. " ++
      "Take one down and pass it around, No more bottles of beer on the wall."
    := by rfl  -- Definitional equality: Lean computes both sides and checks.

/-- verse_two_plural: Verse for 2 bottles uses plural "bottles".

    **Grammar test**: This verifies plural form for n > 1. Also note that
    after taking one down from 2, we have "1 bottle" (singular) remaining. -/
theorem verse_two_plural
    (start : Nat)  -- The starting count (ignored for verse 2).
    : verse start 2 =
      "2 bottles of beer on the wall, 2 bottles of beer. " ++
      "Take one down and pass it around, 1 bottle of beer on the wall."
    := by rfl

/-- verse_99: The classic opening verse, verified by computation.

    **The iconic first line**: "99 bottles of beer on the wall..."
    native_decide asks Lean to compute verse 99 99 and compare strings.
    If they match, the theorem is proven by computation. -/
theorem verse_99
    : verse 99 99 =
      "99 bottles of beer on the wall, 99 bottles of beer. " ++
      "Take one down and pass it around, 98 bottles of beer on the wall."
    := by native_decide  -- Verified by direct string computation.

/-- verse_0_uses_start: The final verse references the starting count.

    **The restart**: The final verse says "Go to the store and buy some more,
    [start] bottles..." This is the ONLY verse that uses the 'start' parameter.
    All other verses ignore it. -/
theorem verse_0_uses_start
    (start : Nat)  -- This actually matters for verse 0!
    : verse start 0 =
      "No more bottles of beer on the wall, no more bottles of beer. " ++
      "Go to the store and buy some more, " ++
      natToString start ++ " " ++ bottleWord start ++ " of beer on the wall."
    := by rfl

/-- verse_50_from_99: Verse 50 of the 99-bottle song.

    **Mid-song check**: Verifies that the middle verse is generated correctly.
    After taking one from 50, we have 49 remaining. -/
theorem verse_50_from_99
    : verse 99 50 =
      "50 bottles of beer on the wall, 50 bottles of beer. " ++
      "Take one down and pass it around, 49 bottles of beer on the wall."
    := by native_decide

/-- verse_50_from_0: Verse 50 when start is 0 (edge case).

    **Edge case**: Even when start = 0 (weird!), verse 50 is still correct
    because positive verses don't use the start parameter. -/
theorem verse_50_from_0
    : verse 0 50 =
      "50 bottles of beer on the wall, 50 bottles of beer. " ++
      "Take one down and pass it around, 49 bottles of beer on the wall."
    := by native_decide

/-- verse_start_irrelevant_pos: For positive n, verse doesn't depend on start.

    **Key observation**: The 'start' parameter only matters for verse 0 (the
    "go to the store" verse). For all other verses, changing start doesn't
    change the output. This is important for injectivity proofs. -/
theorem verse_start_irrelevant_pos
    (s1 s2 n : Nat)     -- Two different start values, same bottle count.
    (h : n > 0)         -- n must be positive.
    : verse s1 n = verse s2 n  -- The verses are identical.
    := by
  match n with
  | 0 => omega           -- n = 0 contradicts h : n > 0.
  | k + 1 => rfl         -- For n = k + 1 > 0, verse doesn't use start.

/-- fullSongAux_length: Helper lemma for song length calculation.

    **Accumulator analysis**: fullSongAux adds m + 1 verses to the accumulator.
    Starting from acc with length L, we end with length L + m + 1.

    **Proof**: Induction on m.
    - m = 0: Add one verse (verse 0). Length = L + 0 + 1 = L + 1. ✓
    - m = k + 1: Add verse (k+1) to acc, then recurse for k.
      By IH: length = (L + 1) + k + 1 = L + (k + 1) + 1. ✓ -/
theorem fullSongAux_length
    (start m : Nat)          -- Starting count and countdown.
    (acc : List String)      -- Accumulator.
    : (fullSongAux start m acc).length = acc.length + m + 1
    := by
  induction m generalizing acc with
  | zero =>
    -- m = 0: fullSongAux returns acc ++ [verse start 0].
    -- Length = acc.length + 1 = acc.length + 0 + 1. ✓
    simp [fullSongAux, List.length_append]
  | succ k ih =>
    -- m = k + 1: fullSongAux recurses with acc ++ [verse start (k+1)].
    simp only [fullSongAux]
    rw [ih]  -- Apply IH to the recursive call.
    simp [List.length_append]
    omega    -- Arithmetic: (L + 1) + k + 1 = L + (k + 1) + 1.

/-- full_song_length: A song with n bottles has exactly n+1 verses.

    **Counting verses**: Verses are numbered n, n-1, ..., 1, 0.
    That's n + 1 distinct numbers, hence n + 1 verses.

    **Proof**: Apply fullSongAux_length with acc = [] (length 0). -/
theorem full_song_length
    (n : Nat)                      -- Starting bottle count.
    : (fullSong n).length = n + 1  -- Song has n + 1 verses.
    := by simp [fullSong, fullSongAux_length]

/-- ninety_nine_bottles_100_verses: The classic song has exactly 100 verses.

    **The magic number**: 99 + 1 = 100. The song goes from verse 99 down
    to verse 0, inclusive. That's 100 verses total. -/
theorem ninety_nine_bottles_100_verses
    : (fullSong 99).length = 100
    := by simp [full_song_length]

-- Quick checks of song generation.
#eval (fullSong 99)[0]!   -- Verse 99
#eval (fullSong 99)[98]!  -- Verse 1
#eval (fullSong 99)[99]!  -- Verse 0

/-! ## Part IX: Leading Number Extraction

To prove verse injectivity, we need to extract the leading number from a verse
string. These functions parse the first decimal number from a string.

**The strategy**: A verse for count n starts with the digits of n (e.g., "99
bottles..."). If two verses are equal, they must have the same leading number,
so they must have the same count. This gives us injectivity. -/

/-- leadingNatAux: Extract digits from the front of a character list.

    **Parsing algorithm**: Walk through characters left-to-right. For each digit,
    multiply accumulator by 10 and add the digit value. Stop at first non-digit.

    **Example**: For "42 bottles", starting with acc = 0:
    - '4' → acc = 0 * 10 + 4 = 4
    - '2' → acc = 4 * 10 + 2 = 42
    - ' ' → stop, return 42

    **Note**: If called with acc = d (first digit already parsed), this parses
    the remaining digits and returns the complete number. -/
def leadingNatAux
    (s : List Char)   -- Remaining characters to parse.
    (acc : Nat)       -- Accumulated value so far.
    : Nat             -- Final parsed number.
    := match s with
       | [] => acc               -- No more characters: return accumulator.
       | c :: rest =>
         match charToDigit c with
         | none => acc           -- Non-digit: stop parsing, return accumulator.
         | some d =>             -- Digit: extend the number.
           leadingNatAux rest (acc * 10 + d)  -- Shift left and add new digit.

/-- leadingNat: Extract the leading natural number from a string.
    Returns none if the string doesn't start with a digit.

    **Purpose**: Given a verse string like "99 bottles...", extract 99.
    Given "No more bottles...", return none (starts with 'N', not a digit).

    **Why Option?** We need to distinguish "starts with 0" (some 0) from
    "doesn't start with digit" (none). This matters for verse 0 detection. -/
def leadingNat
    (s : String)       -- The string to parse.
    : Option Nat       -- some n if starts with digits spelling n, none otherwise.
    := match s.toList with
       | [] => none              -- Empty string: no leading number.
       | c :: rest =>
         match charToDigit c with
         | none => none          -- Doesn't start with digit: return none.
         | some d =>             -- Starts with digit d.
           some (leadingNatAux rest d)  -- Parse remaining digits, starting from d.

/-- isDigitChar': Predicate for ASCII digit characters.

    **Boolean predicate**: Returns true iff c is '0'..'9'.
    Used for string analysis (checking if strings are all-digit). -/
def isDigitChar'
    (c : Char)   -- Character to test.
    : Bool       -- true if c is a digit, false otherwise.
    := match charToDigit c with
       | some _ => true   -- charToDigit succeeded: it's a digit.
       | none => false    -- charToDigit failed: not a digit.

/-- allDigits: Check if all characters in a string are digits.

    **String validation**: Returns true iff every character in s is '0'..'9'.
    Used to verify that natToString produces digit-only strings. -/
def allDigits
    (s : String)   -- String to check.
    : Bool         -- true if all characters are digits.
    := s.toList.all isDigitChar'  -- Check each character using List.all.

/-- isDigitChar_digitToChar: digitToChar always produces a digit character. -/
theorem isDigitChar_digitToChar (d : Nat) : isDigitChar' (digitToChar d) = true := by
  simp only [isDigitChar', digitToChar, charToDigit]
  match d with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl
  | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl | 9 => rfl
  | _ + 10 => rfl

/-- isDigitChar_digitToChar_any: digitToChar produces digits even for d ≥ 10. -/
theorem isDigitChar_digitToChar_any (d : Nat) : isDigitChar' (digitToChar d) = true :=
  isDigitChar_digitToChar d

/-- isDigit_neq_N: Digit characters are not 'N'. -/
theorem isDigit_neq_N (c : Char) (h : isDigitChar' c = true) : c ≠ 'N' := by
  simp only [isDigitChar'] at h
  cases hc : charToDigit c with
  | none => simp [hc] at h
  | some d =>
    intro heq
    rw [heq] at hc
    simp [charToDigit] at hc

/-- leadingNatAux_nil: Empty list returns accumulator. -/
theorem leadingNatAux_nil (acc : Nat) : leadingNatAux [] acc = acc := rfl

/-- leadingNatAux_cons_digit: Digit extends the accumulator. -/
theorem leadingNatAux_cons_digit (c : Char) (rest : List Char) (acc d : Nat)
    (h : charToDigit c = some d) : leadingNatAux (c :: rest) acc = leadingNatAux rest (acc * 10 + d) := by
  simp [leadingNatAux, h]

/-- leadingNatAux_cons_nondigit: Non-digit stops parsing. -/
theorem leadingNatAux_cons_nondigit (c : Char) (rest : List Char) (acc : Nat)
    (h : charToDigit c = none) : leadingNatAux (c :: rest) acc = acc := by
  simp [leadingNatAux, h]

/-- allDigits_digitToString: Single-digit strings are all digits. -/
theorem allDigits_digitToString (d : Nat) (h : d < 10)
    : allDigits (digitToString d) = true := by
  match d with
  | 0 => native_decide | 1 => native_decide | 2 => native_decide
  | 3 => native_decide | 4 => native_decide | 5 => native_decide
  | 6 => native_decide | 7 => native_decide | 8 => native_decide
  | 9 => native_decide | n + 10 => omega

/-- allDigits_app: Concatenation of all-digit strings is all digits. -/
theorem allDigits_app (s1 s2 : String) (h1 : allDigits s1 = true) (h2 : allDigits s2 = true)
    : allDigits (s1 ++ s2) = true := by
  simp only [allDigits, String.toList_append, List.all_append, Bool.and_eq_true]
  exact ⟨h1, h2⟩

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
  repeat apply firstChar_append_left
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
    The key distinguishing feature: verse 0 starts with 'N', others with digits.

    **The crucial distinction**: This theorem is half of our injectivity proof.
    - Verse 0: "No more bottles..." → starts with 'N'
    - Verse n (n > 0): "42 bottles..." → starts with a digit

    Since 'N' is not a digit, verse 0 can never equal any positive verse.

    **Proof**: Assume verse 0 = verse n for n > 0 (toward contradiction).
    - verse_first_char_0: verse 0 starts with 'N'
    - verse_first_char_pos: verse n starts with a digit character c
    - If the verses are equal, their first characters are equal: 'N' = c
    - But c is a digit and 'N' is not a digit: contradiction. -/
theorem verse_0_ne_pos
    (start n : Nat)          -- Fixed start, positive bottle count.
    (h : n > 0)              -- n is positive.
    (h2 : n ≤ 99)            -- n is in our range.
    : verse start 0 ≠ verse start n  -- Verse 0 ≠ Verse n.
    := by
  -- Assume for contradiction that verse start 0 = verse start n.
  intro heq
  -- h0: firstChar (verse start 0) = some 'N'
  have h0 := verse_first_char_0 start
  -- Get a digit c that is the first char of verse n.
  have ⟨c, hc, hdig⟩ := verse_first_char_pos start n h h2
  simp only [firstChar] at h0 hc
  -- Since the verses are equal, their first chars are equal.
  rw [heq] at h0
  -- Now h0: some 'N' = firstChar (verse start n) and hc: firstChar (verse start n) = some c
  rw [h0] at hc
  -- hc: some 'N' = some c, so 'N' = c
  injection hc with hc'
  -- hdig says c is a digit, but c = 'N' is not a digit.
  rw [← hc'] at hdig
  exact absurd hdig (by native_decide)  -- 'N' is not a digit: contradiction.

/-! ## Part X: Verse Injectivity

The main theorem: different bottle counts produce different verses. This is
essential for proving the song has no duplicate verses.

**The crown jewel**: `verse_inj` proves that if verse(start, n1) = verse(start, n2)
then n1 = n2. Combined with the fact that fullSong generates verses for counts
n, n-1, ..., 1, 0, this proves all 100 verses are distinct. -/

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
    This is the heart of the uniqueness proof.

    **Why this matters**: This theorem is the foundation for proving the song
    has no duplicate verses. If two verses are equal, their bottle counts must
    be equal—contrapositive: different counts give different verses.

    **Proof strategy**: Three cases by case split on whether n1, n2 are zero:
    1. Both zero: trivially n1 = n2 = 0.
    2. One zero, one positive: verse 0 starts with 'N', verse n>0 starts with
       a digit, so they can't be equal (verse_0_ne_pos).
    3. Both positive: extract the leading number from each verse. Since the
       verses are equal, their leading numbers are equal, so n1 = n2.

    **The key insight**: Verses are "self-describing"—the bottle count appears
    at the start of the verse string, so we can recover it by parsing. -/
theorem verse_inj
    (start n1 n2 : Nat)                          -- Fixed start, two bottle counts.
    (h1 : n1 ≤ 99) (h2 : n2 ≤ 99)                -- Both counts are in our range.
    (heq : verse start n1 = verse start n2)      -- Assume the verses are equal.
    : n1 = n2                                    -- Conclude the counts are equal.
    := by
  -- Case split on whether n1 and n2 are zero or positive.
  match n1, n2 with
  | 0, 0 =>
    -- Both zero: trivially equal.
    rfl
  | 0, m + 1 =>
    -- n1 = 0, n2 = m + 1 > 0.
    -- verse 0 starts with 'N', verse (m+1) starts with a digit.
    -- These can't be equal, contradicting heq.
    exact absurd heq (verse_0_ne_pos start (m + 1) (by omega) h2)
  | m + 1, 0 =>
    -- n1 = m + 1 > 0, n2 = 0.
    -- Symmetric to above, using heq.symm.
    exact absurd heq.symm (verse_0_ne_pos start (m + 1) (by omega) h1)
  | m + 1, k + 1 =>
    -- Both positive: n1 = m + 1, n2 = k + 1.
    -- Extract the leading number from each verse.
    have hln1 := verse_leadingNat start (m + 1) (by omega) h1
    -- hln1 : leadingNat (verse start (m + 1)) = some (m + 1)
    have hln2 := verse_leadingNat start (k + 1) (by omega) h2
    -- hln2 : leadingNat (verse start (k + 1)) = some (k + 1)
    -- Since the verses are equal, their leading numbers are equal.
    rw [heq] at hln1
    -- hln1 : leadingNat (verse start (k + 1)) = some (m + 1)
    rw [hln1] at hln2
    -- hln2 : some (m + 1) = some (k + 1)
    -- Injecting through Option.some: m + 1 = k + 1.
    injection hln2

/-! ## Part XI: No Duplicate Verses

We prove that the complete song has no duplicate verses. This follows from
verse injectivity: each verse uniquely identifies its count.

**Pairwise distinctness**: We prove `(fullSong n).Pairwise (· ≠ ·)`, meaning
every pair of verses in the song is distinct. This uses verse_inj plus
induction on the song construction. -/

/-- fullSongAux_pairwise: Helper for proving song has pairwise distinct verses.

    **The induction strategy**: We maintain an invariant about the accumulator:
    1. acc already has pairwise distinct elements
    2. Every element of acc is verse n k for some k with m < k ≤ n

    As we count down from m to 0, we add verse n m to acc. By verse_inj,
    verse n m differs from all verses with different indices, so it's distinct
    from everything already in acc.

    **Parameters**:
    - n: the starting count (fixed throughout)
    - m: current countdown (decreases to 0)
    - acc: accumulated verses so far (verses n, n-1, ..., m+1)
    - hn: n ≤ 99 (needed for verse_inj)
    - hm: m ≤ n (countdown doesn't exceed start)
    - hacc: acc is already pairwise distinct
    - hvs: every verse in acc corresponds to some k with m < k ≤ n -/
theorem fullSongAux_pairwise
    (n m : Nat)              -- Start count and current countdown.
    (acc : List String)      -- Accumulated verses.
    (hn : n ≤ 99)            -- Start is in range.
    (hm : m ≤ n)             -- Countdown hasn't exceeded start.
    (hacc : acc.Pairwise (· ≠ ·))  -- Acc is pairwise distinct.
    (hvs : ∀ v ∈ acc, ∃ k, m < k ∧ k ≤ n ∧ v = verse n k)  -- Acc elements are high-index verses.
    : (fullSongAux n m acc).Pairwise (· ≠ ·)  -- Result is pairwise distinct.
    := by
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

/-- fullSong_pairwise: The complete song has pairwise distinct verses.

    **The main NoDup theorem**: This proves that all n+1 verses in fullSong n
    are distinct. No verse appears twice. Combined with full_song_length, this
    means the song has exactly n+1 unique verses.

    **Proof**: Apply fullSongAux_pairwise with:
    - acc = [] (empty accumulator, trivially pairwise distinct)
    - m = n (start countdown at n)
    - The invariant is vacuously true for empty acc -/
theorem fullSong_pairwise
    (n : Nat)                             -- Starting bottle count.
    (h : n ≤ 99)                          -- Must be in our range for verse_inj.
    : (fullSong n).Pairwise (· ≠ ·)       -- All verses are pairwise distinct.
    := by
  unfold fullSong
  -- Apply the helper with empty accumulator.
  apply fullSongAux_pairwise n n [] h (Nat.le_refl n) List.Pairwise.nil
  -- Prove the invariant for empty acc: ∀ v ∈ [], ∃ k, ...
  -- This is vacuously true since [] has no elements.
  intro v hv
  cases hv  -- hv : v ∈ [] is impossible.

/-- ninety_nine_bottles_all_distinct: The 99-bottle song has 100 unique verses.

    **THE UNIQUENESS GUARANTEE**: This is the theorem that says the classic
    99-bottle song has no repeated verses. All 100 verses (from "99 bottles"
    down to "No more bottles") are distinct strings.

    **Corollary of verse_inj**: Since different counts produce different verses,
    and fullSong generates verses for counts 99, 98, ..., 1, 0 (all distinct
    counts), all the verses must be distinct. -/
theorem ninety_nine_bottles_all_distinct
    : (fullSong 99).Pairwise (· ≠ ·)  -- All 100 verses are distinct.
    := fullSong_pairwise 99 (by omega)  -- 99 ≤ 99.

/-! ## Part XII: Bisimulation and Trajectory-Song Correspondence

We prove bisimulation-style theorems: the state machine execution corresponds
exactly to counting down bottles, and each step through the state machine
produces the verse at the corresponding position in the song.

**Bisimulation**: Two systems are bisimilar if they "step in lockstep." Here
we show that (1) running k steps from initial(n) gives on_wall = n - min(k,n),
and (2) the verse at position k in fullSong matches currentVerse of the k-th
state in the trajectory. -/

/-- conservation_law: Bottles are conserved for all reachable states.
    on_wall + passed_around always equals the starting count.

    **THE FUNDAMENTAL LAW OF BOTTLES**: No bottles are ever created or destroyed.
    Every bottle that leaves the wall (on_wall decreases) becomes a passed
    bottle (passed_around increases). The sum is constant.

    **Physical interpretation**: Think of two bins: "wall" and "passed". Bottles
    move from wall to passed, never disappearing or appearing from nowhere.
    This is analogous to conservation of mass in physics.

    **Formal statement**: For any state s reachable from initial(n), we have
    s.on_wall + s.passed_around = n. This holds regardless of how many steps
    we've taken—0, 50, or 99.

    **Proof outline**:
    1. By reachable_preserves_invariant, s satisfies the invariant:
       s.on_wall + s.passed_around = s.starting_count
    2. By induction on reachability, s.starting_count = n
    3. Combining: s.on_wall + s.passed_around = n -/
theorem conservation_law
    (n : Nat)                           -- Starting bottle count.
    (s : State)                         -- Any state in the execution.
    (h : Reachable (initial n) s)       -- Proof that s is reachable from start.
    : s.on_wall + s.passed_around = n   -- Bottles on wall + passed = n.
    := by
  -- Step 1: Get the invariant for state s.
  -- hinv : s.on_wall + s.passed_around = s.starting_count
  have hinv := reachable_preserves_invariant (initial n) s (initial_satisfies_invariant n) h
  -- Step 2: Prove s.starting_count = n by induction on reachability.
  have hst : s.starting_count = n := by
    induction h with
    | refl =>
      -- Base case: s = initial n, so starting_count = n by definition.
      simp [initial]
    | step prev hprev ih =>
      -- Inductive case: s = step(prev) where prev is reachable.
      -- By IH: prev.starting_count = n.
      -- By step_preserves_starting_count: s.starting_count = prev.starting_count.
      have hpinv := reachable_preserves_invariant (initial n) prev
                      (initial_satisfies_invariant n) hprev
      simp [step_preserves_starting_count, ih hpinv]
  -- Step 3: Combine hinv and hst.
  -- hinv: on_wall + passed = starting_count
  -- hst: starting_count = n
  -- Therefore: on_wall + passed = n
  simp only [invariant] at hinv
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
    The k-th state in the trajectory produces the k-th verse of the song.

    **The correspondence**: After running k steps from initial(n):
    - State has on_wall = n - k (by bisimulation)
    - currentVerse reads verse n (n - k)
    - fullSong n has verse n (n - k) at position k

    This three-way correspondence shows the state machine and song list
    are perfectly synchronized. -/
theorem trajectory_verses_match
    (n k : Nat)             -- Starting count and step count.
    (_hn : n ≤ 99)          -- In range (for consistency, not strictly needed here).
    (hk : k ≤ n)            -- Don't overshoot.
    : currentVerse (run k (initial n)) = verse n (n - k)  -- k-th state → k-th verse.
    := by
  simp only [currentVerse]
  -- run k (initial n) has starting_count = n and on_wall = n - k.
  rw [run_preserves_starting_count, bisimulation]
  simp [initial]
  -- After simplification, need to show verse n (n - min k n) = verse n (n - k).
  -- Since k ≤ n, min k n = k.
  congr 1
  omega

/-- trajectory_full_song_correspondence: Complete correspondence theorem.
    For the 99-bottle song, the k-th trajectory state produces the k-th song verse.

    **THE GRAND CORRESPONDENCE**: This theorem ties everything together:
    - The state machine (run k (initial 99))
    - The verse generator (currentVerse)
    - The song list ((fullSong 99)[k]!)

    They all agree: running k steps gives the state that produces the k-th
    verse in the song list. This is the "bisimulation" property. -/
theorem trajectory_full_song_correspondence
    (k : Nat)                -- Step count (0 to 99).
    (h : k ≤ 99)             -- Valid step count.
    : currentVerse (run k (initial 99)) = (fullSong 99)[k]!  -- Trajectory = Song.
    := by
  -- First show currentVerse matches verse 99 (99 - k).
  rw [trajectory_verses_match 99 k (by omega) h]
  -- Then show fullSong 99 at position k is verse 99 (99 - k).
  have hget := fullSong_nth 99 k h
  have hlen : k < (fullSong 99).length := by simp [full_song_length]; omega
  simp only [List.getElem!_eq_getElem?_getD, hget, Option.getD_some]

/-- final_verse_is_terminal: The verse at step n is the terminal verse.

    **The last verse**: After exactly n steps, the state machine reaches
    on_wall = 0, and currentVerse produces verse n 0 (the "No more bottles"
    verse). This is the endpoint of both the state machine and the song. -/
theorem final_verse_is_terminal
    (n : Nat)                -- Starting count.
    (h : n ≤ 99)             -- In range.
    : currentVerse (run n (initial n)) = verse n 0  -- n steps → final verse.
    := by
  rw [trajectory_verses_match n n h (Nat.le_refl n)]
  simp  -- n - n = 0.

/-! ## Part XIII: Parametricity

Some theorems hold for ANY starting count n, while others require n ≤ 99 for
string parsing reasons. We make this distinction explicit.

**Why the bound?** Our string parsing lemmas use `native_decide` which requires
concrete computation. For n > 99, we'd need 3+ digit handling. The core state
machine theorems (termination, conservation) work for any n; only the string
injectivity proofs need the bound. -/

/-! ### Unbounded Theorems (work for any n) -/

/-- general_termination: The song terminates for ANY starting count.
    No bound on n required—the state machine always reaches terminal.

    **Universality**: Whether you have 99 bottles, 1000 bottles, or a googol
    bottles, the song WILL end. This follows from well-founded recursion on
    natural numbers—you can't count down forever. -/
theorem general_termination
    (n : Nat)                              -- ANY starting count.
    : terminal (run n (initial n))         -- The song terminates.
    := sufficient_fuel_reaches_terminal (initial n)

/-- general_conservation: Conservation holds for ANY starting count.
    Bottles are conserved regardless of how many we start with.

    **Physical law**: Like conservation of mass or energy, bottles neither
    appear from nor disappear into nothing. This is a mathematical certainty,
    not an empirical observation. -/
theorem general_conservation
    (n : Nat)                              -- ANY starting count.
    (s : State)                            -- ANY reachable state.
    (h : Reachable (initial n) s)          -- Proof s is reachable.
    : s.on_wall + s.passed_around = n      -- Conservation holds.
    := conservation_law n s h

/-- general_invariant: The invariant holds for ANY starting count.
    This is the most fundamental property—no bounds needed.

    **The core guarantee**: Run the state machine for any number of steps,
    from any starting count—the invariant ALWAYS holds. -/
theorem general_invariant
    (n fuel : Nat)                         -- Starting count and step count.
    : invariant (run fuel (initial n))     -- Invariant holds after fuel steps.
    := run_preserves_invariant fuel (initial n) (initial_satisfies_invariant n)

/-- general_all_bottles_passed: All bottles get passed for ANY n.
    At termination, passed_around equals the starting count.

    **Complete accounting**: When the song ends, every bottle that was on the
    wall has been passed around exactly once. No bottle is lost or duplicated. -/
theorem general_all_bottles_passed
    (n : Nat)                              -- ANY starting count.
    : (run n (initial n)).passed_around = n -- All n bottles get passed.
    := all_bottles_passed_at_end n

/-! ### Bounded Theorems (require n ≤ 99) -/

/-- bounded_verse_injectivity: Different counts give different verses.
    Requires n ≤ 99 for the leading_nat extraction to compute.

    **The bound**: We use `native_decide` to verify that leadingNat correctly
    extracts n from natToString n. This requires concrete computation, which
    we've only verified for 1..99. Extending to larger n would require more
    proof infrastructure. -/
theorem bounded_verse_injectivity
    (start n1 n2 : Nat)                    -- Fixed start, two counts.
    (h1 : n1 ≤ 99) (h2 : n2 ≤ 99)          -- Both in the verified range.
    (heq : verse start n1 = verse start n2) -- If verses are equal...
    : n1 = n2                               -- ...counts are equal.
    := verse_inj start n1 n2 h1 h2 heq

/-- bounded_song_NoDup: The song has no duplicate verses.
    Requires n ≤ 99 because it depends on verse injectivity.

    **Practical implication**: For any song with ≤ 100 verses (n ≤ 99),
    every verse is unique. You'll never hear the same verse twice. -/
theorem bounded_song_NoDup
    (n : Nat)                              -- Starting count.
    (h : n ≤ 99)                           -- In the verified range.
    : (fullSong n).Pairwise (· ≠ ·)        -- No duplicate verses.
    := fullSong_pairwise n h

/-! ## Part XIV: The Song Itself

Finally, we prove that our verified machinery produces the actual song. Each
theorem below is a certificate that a specific verse computes to exactly the
text we expect. Lean verifies each by computation—no trust required.

**Executable specifications**: Each `native_decide` proof asks Lean to compute
the verse string and check equality. This is both a test AND a proof—if the
computation succeeds, the theorem is true by construction. -/

/-- the_song_verse_99: The first verse of the song.

    **Opening act**: "99 bottles of beer on the wall, 99 bottles of beer..."
    This is THE iconic opening line. Lean verifies it's exactly right. -/
theorem the_song_verse_99
    : (fullSong 99)[0]! =                    -- Index 0 is the first verse.
      "99 bottles of beer on the wall, 99 bottles of beer. " ++
      "Take one down and pass it around, 98 bottles of beer on the wall."
    := by native_decide  -- Verified by direct string computation.

/-- the_song_verse_98: The second verse.

    **Following the pattern**: 98 bottles, take one down, 97 remain. -/
theorem the_song_verse_98
    : (fullSong 99)[1]! =                    -- Index 1 is the second verse.
      "98 bottles of beer on the wall, 98 bottles of beer. " ++
      "Take one down and pass it around, 97 bottles of beer on the wall."
    := by native_decide

/-- the_song_verse_97: The third verse.

    **Continuing down**: The pattern continues predictably. -/
theorem the_song_verse_97
    : (fullSong 99)[2]! =                    -- Index 2 is the third verse.
      "97 bottles of beer on the wall, 97 bottles of beer. " ++
      "Take one down and pass it around, 96 bottles of beer on the wall."
    := by native_decide

/-- the_song_verse_50: The middle of the song.

    **Halftime**: 50 bottles remain at index 49 (since 99 - 49 = 50). -/
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

/-! ## Part XV: Additional String Properties

Round-trip properties for string conversion and additional helper lemmas used
throughout the development.

**Round-trip proofs**: We prove `stringToNat(natToString(n)) = some n`, which
guarantees our conversion functions are correct inverses. This style of
verification—proving that encoding and decoding are inverses—is common in
verified serialization and parsing. -/

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
  | step prev _ ih => simp [step_preserves_starting_count, ih]

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
    - All 99 bottles get passed

    **THE GRAND FINALE**: This theorem bundles ALL the key properties we've
    proven into a single statement. It serves as both a summary and a
    certificate that our verification is complete.

    **Five-part conjunction**: We prove:
    1. `(fullSong 99).length = 100` — Exactly 100 verses (0..99 inclusive)
    2. `∀ k, k ≤ 99 → (fullSong 99)[k]! = verse 99 (99 - k)` — Verse order correct
    3. `(fullSong 99).Pairwise (· ≠ ·)` — All verses distinct (no duplicates)
    4. `terminal (run 99 (initial 99))` — Song terminates (state machine halts)
    5. `(run 99 (initial 99)).passed_around = 99` — All bottles passed

    **Why bundle these?** A single theorem with all properties makes it easy
    to see at a glance that the verification is complete. Each conjunct can
    also be extracted separately using `.1`, `.2.1`, etc.

    **Trust chain**: This theorem depends on everything we've built:
    - State machine definitions (State, step, run)
    - Invariant proofs (preservation, termination)
    - String conversion (natToString, round-trip)
    - Verse generation (verse, fullSong)
    - Injectivity (verse_inj, NoDup) -/
theorem song_complete_summary
    : (fullSong 99).length = 100 ∧                           -- 100 verses
      (∀ k, k ≤ 99 → (fullSong 99)[k]! = verse 99 (99 - k)) ∧ -- Correct order
      (fullSong 99).Pairwise (· ≠ ·) ∧                        -- All distinct
      terminal (run 99 (initial 99)) ∧                        -- Terminates
      (run 99 (initial 99)).passed_around = 99                -- All passed
    := by
  -- Build the 5-tuple using ⟨_, _, _, _, _⟩ notation.
  -- The second component needs a proof, so we use ?_ placeholder.
  refine ⟨ninety_nine_bottles_100_verses,      -- (1) Length = 100
          ?_,                                   -- (2) Verse order (prove below)
          ninety_nine_bottles_all_distinct,     -- (3) All distinct
          song_terminates,                      -- (4) Terminates
          all_bottles_passed_at_end 99⟩         -- (5) All bottles passed
  -- Prove component (2): ∀ k, k ≤ 99 → (fullSong 99)[k]! = verse 99 (99 - k)
  intro k hk
  -- Get the k-th element of fullSong 99.
  have hget := fullSong_nth 99 k hk
  -- Show k is a valid index.
  have hlen : k < (fullSong 99).length := by simp [full_song_length]; omega
  -- Simplify the list access using our lemma.
  simp only [List.getElem!_eq_getElem?_getD, hget, Option.getD_some]

/-! ## Conclusion

We have formally verified the "99 Bottles of Beer" song:

1. **Termination**: The song always ends (`song_terminates`)
2. **Conservation**: Bottles are neither created nor destroyed (`conservation_law`)
3. **Correctness**: Each verse correctly reflects the bottle count (`trajectory_full_song_correspondence`)
4. **Uniqueness**: Every verse is distinct (`ninety_nine_bottles_all_distinct`)
5. **Completeness**: The state machine visits every verse (`song_complete`)

This development demonstrates key verification techniques:
- State machine modeling
- Inductive invariants
- Well-founded recursion
- String manipulation with round-trip proofs
- Injectivity arguments

The familiar song provides intuition; the proofs provide certainty. -/

end Bottles
