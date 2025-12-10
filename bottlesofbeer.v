(******************************************************************************)
(*                                                                            *)
(*                   99 Bottles of Beer: Verified Termination                 *)
(*                                                                            *)
(*     A pedagogical Coq development using the familiar "99 Bottles" song     *)
(*     to teach formal verification. Every line is commented to serve as      *)
(*     a self-contained introduction to theorem proving in Coq.               *)
(*                                                                            *)
(*     We model the song as a state machine and prove:                        *)
(*       - Conservation: bottles on wall + passed = starting count            *)
(*       - Termination: the song always reaches "no more bottles"             *)
(*       - Correctness: verses match the trajectory through states            *)
(*                                                                            *)
(*     "Anything can happen, child. Anything can be."                         *)
(*     — Shel Silverstein                                                     *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 2025                                                    *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Arith.PeanoNat.      (* Peano natural numbers and arithmetic. *)
Require Import Coq.Lists.List.          (* List type and operations. *)
Require Import Lia.                     (* Linear integer arithmetic tactic. *)
Require Import Coq.Strings.String.      (* String type for verse generation. *)
Require Import Coq.Strings.Ascii.       (* ASCII character type. *)
Require Import Coq.Arith.Wf_nat.        (* Well-founded recursion on naturals. *)
Require Import Coq.Program.Wf.          (* Program library for well-founded fixpoints. *)
Require Import Coq.Bool.Bool.           (* Boolean operations and lemmas. *)
Import ListNotations.                   (* Enable [x; y; z] list syntax. *)

Open Scope string_scope.               (* Use "..." for string literals. *)

(* Bottles: The main module encapsulating all definitions and proofs. *)
(* Using a module keeps our namespace clean and groups related items. *)
Module Bottles.

  (** ===================================================================== *)
  (** PART I: STATE MACHINE MODEL                                           *)
  (** ===================================================================== *)
  (** We model the song as transitions between states. Each state tracks    *)
  (** how many bottles remain on the wall, how many have been passed        *)
  (** around, and what we started with (for the conservation invariant).    *)
  (** ===================================================================== *)

  (* State: A snapshot of the song at any moment. *)
  (* Records in Coq bundle multiple named fields into a single type. *)
  (* This is similar to a struct in C or a record in ML. *)
  Record State
    := mkState                          (* mkState is the constructor name. *)
         { on_wall : nat                (* Bottles currently on the wall. *)
         ; passed_around : nat          (* Bottles taken down and passed. *)
         ; starting_count : nat         (* Original count; never changes. *)
         }.

  (* initial: Constructs the starting state for a song with n bottles. *)
  (* At the start, all bottles are on the wall, none have been passed. *)
  Definition initial (n : nat)          (* Takes the starting bottle count. *)
    : State                             (* Returns a State record. *)
    := {| on_wall := n                  (* All n bottles begin on the wall. *)
        ; passed_around := 0            (* Zero bottles passed initially. *)
        ; starting_count := n           (* Record n for invariant checking. *)
        |}.

  (* terminal: Predicate that holds when the song is finished. *)
  (* A Prop is a logical proposition; this one asserts on_wall is zero. *)
  Definition terminal (s : State)       (* Takes a state to examine. *)
    : Prop                              (* Returns a proposition (provable or not). *)
    := on_wall s = 0.                   (* True iff no bottles remain. *)

  (* step: Performs one verse of the song—takes one bottle down. *)
  (* If already at zero, the state doesn't change (fixpoint behavior). *)
  Definition step (s : State)           (* Takes the current state. *)
    : State                             (* Returns the next state. *)
    := match on_wall s with             (* Pattern match on bottles remaining. *)
       | O => s                         (* Zero bottles: song over, no change. *)
       | S k => {| on_wall := k         (* S k bottles: k remain after taking one. *)
                 ; passed_around := S (passed_around s)  (* One more passed. *)
                 ; starting_count := starting_count s    (* Starting count unchanged. *)
                 |}
       end.

  (* invariant: The conservation law—bottles are never created or destroyed. *)
  (* This is the key property: on_wall + passed_around = starting_count. *)
  Definition invariant (s : State)      (* Takes a state to check. *)
    : Prop                              (* Returns a proposition. *)
    := on_wall s + passed_around s = starting_count s.  (* Conservation equation. *)

  (** ===================================================================== *)
  (** PART II: CORE SAFETY THEOREMS                                         *)
  (** ===================================================================== *)
  (** We prove that the invariant holds initially and is preserved by       *)
  (** each step. This "inductive invariant" pattern is fundamental to       *)
  (** proving properties of state machines and transition systems.          *)
  (** ===================================================================== *)

  (* initial_satisfies_invariant: The starting state satisfies conservation. *)
  (* This is the "base case" of our inductive invariant argument. *)
  Theorem initial_satisfies_invariant
    : forall n,                         (* For any starting count n... *)
      invariant (initial n).            (* ...the initial state satisfies the invariant. *)
  Proof.
    intro n.                            (* Introduce n into the context. *)
    unfold invariant, initial.          (* Expand definitions to see the equation. *)
    simpl.                              (* Simplify: n + 0 = n. *)
    lia.                                (* Linear arithmetic solves n + 0 = n. *)
  Qed.

  (* step_preserves_invariant: If a state satisfies the invariant, so does its successor. *)
  (* This is the "inductive step"—preservation under transitions. *)
  Theorem step_preserves_invariant
    : forall s,                         (* For any state s... *)
      invariant s ->                    (* ...if s satisfies the invariant... *)
      invariant (step s).               (* ...then step s also satisfies it. *)
  Proof.
    intros [w p st] H.                  (* Destruct s into components w, p, st; H is hypothesis. *)
    unfold invariant, step in *.        (* Expand definitions everywhere. *)
    simpl in *.                         (* Simplify record projections. *)
    destruct w.                         (* Case split: is w zero or a successor? *)
    - simpl.                            (* w = 0: step doesn't change state. *)
      lia.                              (* Arithmetic: same equation still holds. *)
    - simpl.                            (* w = S k: one bottle moves from wall to passed. *)
      lia.                              (* Arithmetic: k + S p = st follows from S k + p = st. *)
  Qed.

  (* step_preserves_starting_count: The starting count never changes. *)
  (* This is obvious but useful as a rewrite lemma. *)
  Theorem step_preserves_starting_count
    : forall s,                         (* For any state s... *)
      starting_count (step s) = starting_count s.  (* ...step preserves starting_count. *)
  Proof.
    intros [w p st].                    (* Destruct s into its components. *)
    unfold step.                        (* Expand the step definition. *)
    simpl.                              (* Simplify the projection. *)
    destruct w.                         (* Case split on w. *)
    - reflexivity.                      (* w = 0: state unchanged, so equal. *)
    - reflexivity.                      (* w = S k: starting_count field copied. *)
  Qed.

  (* step_decreases_or_terminal: Each step either terminates or makes progress. *)
  (* This is crucial for termination: we can't loop forever. *)
  Theorem step_decreases_or_terminal
    : forall s,                         (* For any state s... *)
      terminal s \/                     (* ...either s is terminal (no bottles)... *)
      on_wall (step s) < on_wall s.     (* ...or step decreases bottles on wall. *)
  Proof.
    intros [w p st].                    (* Destruct s into components. *)
    unfold terminal, step.              (* Expand definitions. *)
    simpl.                              (* Simplify projections. *)
    destruct w.                         (* Case split on w. *)
    - left.                             (* w = 0: choose left disjunct (terminal). *)
      reflexivity.                      (* 0 = 0 is trivially true. *)
    - right.                            (* w = S k: choose right disjunct (decreases). *)
      apply Nat.lt_succ_diag_r.         (* Lemma: k < S k. *)
  Qed.

  (* terminal_is_fixpoint: Once terminal, step has no effect. *)
  (* The song is over; taking another step doesn't change anything. *)
  Theorem terminal_is_fixpoint
    : forall s,                         (* For any state s... *)
      terminal s ->                     (* ...if s is terminal... *)
      step s = s.                       (* ...then step s equals s. *)
  Proof.
    intros [w p st] H.                  (* Destruct s; H says on_wall = 0. *)
    unfold terminal, step in *.         (* Expand definitions. *)
    simpl in *.                         (* Simplify. *)
    rewrite H.                          (* Rewrite on_wall to 0 using H. *)
    reflexivity.                        (* {| 0; p; st |} = {| 0; p; st |}. *)
  Qed.

  (** ===================================================================== *)
  (** PART III: EXECUTION AND TERMINATION                                   *)
  (** ===================================================================== *)
  (** We define a "fuel-based" execution model: run n steps and see where   *)
  (** we end up. Then we prove that sufficient fuel always reaches terminal *)
  (** state, establishing termination of the song.                          *)
  (** ===================================================================== *)

  (* run: Execute the state machine for a fixed number of steps. *)
  (* Fixpoint defines a recursive function; fuel decreases each call. *)
  Fixpoint run (fuel : nat)             (* Number of steps to execute. *)
               (s : State)              (* Starting state. *)
    : State                             (* Ending state after fuel steps. *)
    := match fuel with                  (* Pattern match on fuel. *)
       | O => s                         (* No fuel: return current state. *)
       | S k => run k (step s)          (* Fuel remaining: step once, recurse with k. *)
       end.

  (* run_preserves_invariant: Running any number of steps preserves the invariant. *)
  (* By induction: base case is trivial, inductive case uses step_preserves_invariant. *)
  Theorem run_preserves_invariant
    : forall fuel s,                    (* For any fuel and state s... *)
      invariant s ->                    (* ...if s satisfies the invariant... *)
      invariant (run fuel s).           (* ...then so does run fuel s. *)
  Proof.
    induction fuel.                     (* Induction on fuel. *)
    - intros s H.                       (* Base: fuel = 0. *)
      simpl.                            (* run 0 s = s. *)
      exact H.                          (* H already says invariant s. *)
    - intros s H.                       (* Inductive: fuel = S k. *)
      simpl.                            (* run (S k) s = run k (step s). *)
      apply IHfuel.                     (* Apply induction hypothesis. *)
      apply step_preserves_invariant.   (* Need: invariant (step s). *)
      apply H.                          (* Need: invariant s, which is H. *)
  Qed.

  (* run_preserves_starting_count: Running doesn't change starting_count. *)
  (* Another simple induction using step_preserves_starting_count. *)
  Theorem run_preserves_starting_count
    : forall fuel s,                    (* For any fuel and state s... *)
      starting_count (run fuel s) = starting_count s.  (* ...starting_count unchanged. *)
  Proof.
    induction fuel.                     (* Induction on fuel. *)
    - intro s.                          (* Base: fuel = 0. *)
      simpl.                            (* run 0 s = s. *)
      reflexivity.                      (* starting_count s = starting_count s. *)
    - intro s.                          (* Inductive: fuel = S k. *)
      simpl.                            (* run (S k) s = run k (step s). *)
      rewrite IHfuel.                   (* Apply IH: starting_count (run k _) = starting_count _. *)
      apply step_preserves_starting_count.  (* step preserves starting_count. *)
  Qed.

  (* run_reaches_zero: Running exactly w steps from w bottles reaches zero. *)
  (* The key lemma: fuel = bottles on wall is always sufficient. *)
  Lemma run_reaches_zero
    : forall w p st,                    (* For any w, p, st... *)
      on_wall (run w {| on_wall := w;   (* Running w steps from state with w bottles... *)
                        passed_around := p;
                        starting_count := st |}) = 0.  (* ...reaches 0 bottles. *)
  Proof.
    induction w.                        (* Induction on w (bottles on wall). *)
    - intros p st.                      (* Base: w = 0. *)
      simpl.                            (* run 0 s = s; on_wall = 0. *)
      reflexivity.                      (* 0 = 0. *)
    - intros p st.                      (* Inductive: w = S w'. *)
      simpl.                            (* run (S w') steps from S w' bottles. *)
      apply IHw.                        (* After one step: w' bottles, w' fuel—use IH. *)
  Qed.

  (* sufficient_fuel_reaches_terminal: on_wall steps always suffice to terminate. *)
  (* Packages run_reaches_zero into the terminal predicate. *)
  Theorem sufficient_fuel_reaches_terminal
    : forall s,                         (* For any state s... *)
      terminal (run (on_wall s) s).     (* ...running on_wall s steps reaches terminal. *)
  Proof.
    intros [w p st].                    (* Destruct s into components. *)
    unfold terminal.                    (* Expand: need on_wall (run w s) = 0. *)
    simpl.                              (* Simplify on_wall projection. *)
    apply run_reaches_zero.             (* Apply the key lemma. *)
  Qed.

  (* song_terminates: The classic 99-bottles song terminates. *)
  (* A concrete instance: 99 steps from 99 bottles reaches zero. *)
  Theorem song_terminates
    : terminal (run 99 (initial 99)).   (* 99 steps from initial 99 is terminal. *)
  Proof.
    reflexivity.                        (* Coq computes this; both sides equal 0. *)
  Qed.

  (* all_bottles_passed_at_end: At termination, all bottles have been passed. *)
  (* Combines invariant preservation with terminal condition. *)
  Theorem all_bottles_passed_at_end
    : forall n,                         (* For any starting count n... *)
      passed_around (run n (initial n)) = n.  (* ...all n bottles get passed. *)
  Proof.
    intro n.                            (* Introduce n. *)
    pose proof (run_preserves_invariant n (initial n)    (* Get invariant preservation. *)
                  (initial_satisfies_invariant n)) as Hinv.
    pose proof (sufficient_fuel_reaches_terminal         (* Get terminal condition. *)
                  (initial n)) as Hterm.
    pose proof (run_preserves_starting_count n           (* Get starting_count preservation. *)
                  (initial n)) as Hst.
    unfold initial, invariant, terminal in *.  (* Expand all definitions. *)
    simpl in *.                         (* Simplify record projections. *)
    rewrite Hst in Hinv.                (* starting_count (run n _) = n. *)
    simpl in Hinv.                      (* Further simplification. *)
    lia.                                (* on_wall = 0 and on_wall + passed = n gives passed = n. *)
  Qed.

  (** ===================================================================== *)
  (** PART IV: TRAJECTORY ANALYSIS                                          *)
  (** ===================================================================== *)
  (** A trajectory is the sequence of states visited during execution.      *)
  (** We prove trajectories are monotonically decreasing in bottle count—   *)
  (** bottles are only ever taken down, never added.                        *)
  (** ===================================================================== *)

  (* monotonic_decreasing: A function f is monotonic decreasing in on_wall. *)
  (* As the index increases, on_wall can only stay same or decrease. *)
  Definition monotonic_decreasing (f : nat -> State)  (* A function from indices to states. *)
    : Prop                              (* Returns a proposition. *)
    := forall i j,                      (* For all indices i and j... *)
       i <= j ->                        (* ...if i ≤ j... *)
       on_wall (f j) <= on_wall (f i).  (* ...then on_wall at j ≤ on_wall at i. *)

  (* trajectory: The sequence of states starting from s. *)
  (* trajectory s maps index i to the state after i steps from s. *)
  Definition trajectory (s : State)     (* Starting state. *)
    : nat -> State                      (* Returns function from step count to state. *)
    := fun i => run i s.                (* The i-th state is run i s. *)

  (* step_nonincreasing: A single step never increases on_wall. *)
  (* Bottles on wall either decrease by 1 or stay at 0. *)
  Lemma step_nonincreasing
    : forall s,                         (* For any state s... *)
      on_wall (step s) <= on_wall s.    (* ...step doesn't increase on_wall. *)
  Proof.
    intros [w p st].                    (* Destruct s. *)
    unfold step.                        (* Expand step. *)
    simpl.                              (* Simplify projection. *)
    destruct w.                         (* Case split on w. *)
    - apply Nat.le_refl.                (* w = 0: 0 ≤ 0. *)
    - apply Nat.le_succ_diag_r.         (* w = S k: k ≤ S k. *)
  Qed.

  (* no_bottles_created: Running never increases on_wall. *)
  (* Generalization of step_nonincreasing to multiple steps. *)
  Theorem no_bottles_created
    : forall s fuel,                    (* For any state s and fuel... *)
      on_wall (run fuel s) <= on_wall s.  (* ...running doesn't increase on_wall. *)
  Proof.
    intros s fuel.                      (* Introduce s and fuel. *)
    revert s.                           (* Generalize s for induction. *)
    induction fuel.                     (* Induction on fuel. *)
    - intro s.                          (* Base: fuel = 0. *)
      simpl.                            (* run 0 s = s. *)
      lia.                              (* on_wall s ≤ on_wall s. *)
    - intro s.                          (* Inductive: fuel = S k. *)
      simpl.                            (* run (S k) s = run k (step s). *)
      specialize (IHfuel (step s)).     (* Apply IH to step s. *)
      pose proof (step_nonincreasing s).  (* step s has ≤ bottles. *)
      lia.                              (* Transitivity: run k (step s) ≤ step s ≤ s. *)
  Qed.

  (* on_wall_run_step: Running from step s has ≤ bottles than running from s. *)
  (* Key lemma for proving trajectory monotonicity. *)
  Lemma on_wall_run_step
    : forall fuel s,                    (* For any fuel and state s... *)
      on_wall (run fuel (step s)) <= on_wall (run fuel s).  (* ...starting lower stays lower. *)
  Proof.
    induction fuel.                     (* Induction on fuel. *)
    - intro s.                          (* Base: fuel = 0. *)
      simpl.                            (* run 0 _ = identity. *)
      apply step_nonincreasing.         (* step s ≤ s. *)
    - intro s.                          (* Inductive: fuel = S k. *)
      simpl.                            (* run (S k) s = run k (step s). *)
      apply IHfuel.                     (* Apply IH. *)
  Qed.

  (* run_succ_le: One more step means ≤ bottles. *)
  (* run (S fuel) s has at most as many bottles as run fuel s. *)
  Lemma run_succ_le
    : forall fuel s,                    (* For any fuel and state s... *)
      on_wall (run (S fuel) s) <= on_wall (run fuel s).  (* ...more steps = fewer bottles. *)
  Proof.
    intros fuel s.                      (* Introduce fuel and s. *)
    simpl.                              (* run (S fuel) s = run fuel (step s). *)
    apply on_wall_run_step.             (* Apply the previous lemma. *)
  Qed.

  (* trajectory_monotonic: The trajectory from any state is monotonic decreasing. *)
  (* Main theorem: as we progress through the song, bottles only decrease. *)
  Theorem trajectory_monotonic
    : forall s,                         (* For any starting state s... *)
      monotonic_decreasing (trajectory s).  (* ...its trajectory is monotonic. *)
  Proof.
    intros s i j Hij.                   (* Introduce s, i, j, and proof that i ≤ j. *)
    unfold trajectory.                  (* Expand: need on_wall (run j s) ≤ on_wall (run i s). *)
    induction Hij.                      (* Induction on the proof that i ≤ j. *)
    - lia.                              (* Base: i = j, so equal. *)
    - pose proof (run_succ_le m s).     (* run (S m) s ≤ run m s. *)
      lia.                              (* Transitivity with IH. *)
  Qed.

  (** ----- Dual results: passed_around is monotonically increasing ----- *)

  (* monotonic_increasing: A function f is monotonic increasing in passed_around. *)
  (* As the index increases, passed_around can only stay same or increase. *)
  Definition monotonic_increasing (f : nat -> State)  (* A function from indices to states. *)
    : Prop                              (* Returns a proposition. *)
    := forall i j,                      (* For all indices i and j... *)
       i <= j ->                        (* ...if i ≤ j... *)
       passed_around (f i) <= passed_around (f j).  (* ...then passed at i ≤ passed at j. *)

  (* step_passed_nondecreasing: A single step never decreases passed_around. *)
  (* Bottles passed either increase by 1 or stay same (at 0 on_wall). *)
  Lemma step_passed_nondecreasing
    : forall s,                         (* For any state s... *)
      passed_around s <= passed_around (step s).  (* ...step doesn't decrease passed. *)
  Proof.
    intros [w p st].                    (* Destruct s into components. *)
    unfold step.                        (* Expand step definition. *)
    simpl.                              (* Simplify projection. *)
    destruct w.                         (* Case split on w. *)
    - apply Nat.le_refl.                (* w = 0: p ≤ p. *)
    - apply Nat.le_succ_diag_r.         (* w = S k: p ≤ S p. *)
  Qed.

  (* no_bottles_lost: Running never decreases passed_around. *)
  (* Generalization of step_passed_nondecreasing to multiple steps. *)
  Theorem no_bottles_lost
    : forall s fuel,                    (* For any state s and fuel... *)
      passed_around s <= passed_around (run fuel s).  (* ...running doesn't decrease passed. *)
  Proof.
    intros s fuel.                      (* Introduce s and fuel. *)
    revert s.                           (* Generalize s for induction. *)
    induction fuel.                     (* Induction on fuel. *)
    - intro s.                          (* Base: fuel = 0. *)
      simpl.                            (* run 0 s = s. *)
      apply Nat.le_refl.                (* passed_around s ≤ passed_around s. *)
    - intro s.                          (* Inductive: fuel = S k. *)
      simpl.                            (* run (S k) s = run k (step s). *)
      pose proof (IHfuel (step s)) as IH.  (* Apply IH to step s. *)
      pose proof (step_passed_nondecreasing s) as Hstep.  (* step s has ≥ passed. *)
      lia.                              (* Transitivity: s ≤ step s ≤ run k (step s). *)
  Qed.

  (* passed_run_step: Running from step s has ≥ passed than running from s. *)
  (* Key lemma for proving trajectory monotonicity. *)
  Lemma passed_run_step
    : forall fuel s,                    (* For any fuel and state s... *)
      passed_around (run fuel s) <= passed_around (run fuel (step s)).  (* ...starting higher stays higher. *)
  Proof.
    induction fuel.                     (* Induction on fuel. *)
    - intro s.                          (* Base: fuel = 0. *)
      simpl.                            (* run 0 _ = identity. *)
      apply step_passed_nondecreasing.  (* step s ≥ s in passed_around. *)
    - intro s.                          (* Inductive: fuel = S k. *)
      simpl.                            (* run (S k) s = run k (step s). *)
      apply IHfuel.                     (* Apply IH. *)
  Qed.

  (* run_succ_passed_ge: One more step means ≥ passed_around. *)
  (* run (S fuel) s has at least as many passed as run fuel s. *)
  Lemma run_succ_passed_ge
    : forall fuel s,                    (* For any fuel and state s... *)
      passed_around (run fuel s) <= passed_around (run (S fuel) s).  (* ...more steps = more passed. *)
  Proof.
    intros fuel s.                      (* Introduce fuel and s. *)
    simpl.                              (* run (S fuel) s = run fuel (step s). *)
    apply passed_run_step.              (* Apply the previous lemma. *)
  Qed.

  (* trajectory_passed_monotonic: The trajectory from any state is monotonic increasing in passed. *)
  (* Main theorem: as we progress through the song, passed_around only increases. *)
  Theorem trajectory_passed_monotonic
    : forall s,                         (* For any starting state s... *)
      monotonic_increasing (trajectory s).  (* ...its trajectory is monotonic in passed. *)
  Proof.
    intros s i j Hij.                   (* Introduce s, i, j, and proof that i ≤ j. *)
    unfold trajectory.                  (* Expand: need passed (run i s) ≤ passed (run j s). *)
    induction Hij.                      (* Induction on the proof that i ≤ j. *)
    - apply Nat.le_refl.                (* Base: i = j, so equal. *)
    - pose proof (run_succ_passed_ge m s) as Hsucc.  (* run (S m) s ≥ run m s. *)
      lia.                              (* Transitivity with IH. *)
  Qed.

  (** ===================================================================== *)
  (** PART V: REACHABILITY                                                  *)
  (** ===================================================================== *)
  (** We define an inductive reachability relation: s' is reachable from s  *)
  (** if we can get from s to s' by zero or more steps. This provides an    *)
  (** alternative characterization of the states we can visit.              *)
  (** ===================================================================== *)

  (* Reachable: Inductive definition of reachability between states. *)
  (* s' is reachable from s0 if there's a path of steps from s0 to s'. *)
  Inductive Reachable (s0 : State)      (* s0 is the starting state (parameter). *)
    : State -> Prop                     (* Returns a predicate on states. *)
    := | reach_refl                     (* Constructor 1: reflexivity. *)
         : Reachable s0 s0              (* Any state reaches itself. *)
       | reach_step s s'                (* Constructor 2: extend by one step. *)
         : Reachable s0 s ->            (* If s is reachable from s0... *)
           s' = step s ->               (* ...and s' is the step from s... *)
           Reachable s0 s'.             (* ...then s' is reachable from s0. *)

  (* reachable_trans: Reachability is transitive. *)
  (* If s1 is reachable from s0, and s2 from s1, then s2 from s0. *)
  Lemma reachable_trans
    : forall s0 s1 s2,                  (* For any three states... *)
      Reachable s0 s1 ->                (* ...if s1 is reachable from s0... *)
      Reachable s1 s2 ->                (* ...and s2 is reachable from s1... *)
      Reachable s0 s2.                  (* ...then s2 is reachable from s0. *)
  Proof.
    intros s0 s1 s2 H1 H2.              (* Introduce states and hypotheses. *)
    induction H2.                       (* Induction on the proof that s2 is reachable from s1. *)
    - exact H1.                         (* Base: s2 = s1, so use H1. *)
    - apply reach_step with s.          (* Inductive: s2 = step s for some reachable s. *)
      + exact IHReachable.              (* s is reachable from s0 by IH. *)
      + exact H.                        (* s' = step s by assumption. *)
  Qed.

  (* reachable_run: run fuel s is always reachable from s. *)
  (* Connects the computational run with the relational Reachable. *)
  Theorem reachable_run
    : forall fuel s,                    (* For any fuel and state s... *)
      Reachable s (run fuel s).         (* ...run fuel s is reachable from s. *)
  Proof.
    induction fuel.                     (* Induction on fuel. *)
    - intro s.                          (* Base: fuel = 0. *)
      simpl.                            (* run 0 s = s. *)
      apply reach_refl.                 (* s reaches itself. *)
    - intro s.                          (* Inductive: fuel = S k. *)
      simpl.                            (* run (S k) s = run k (step s). *)
      apply reachable_trans with (step s).  (* Go via step s. *)
      + apply reach_step with s.        (* s reaches step s. *)
        * apply reach_refl.             (* s reaches s. *)
        * reflexivity.                  (* step s = step s. *)
      + apply IHfuel.                   (* step s reaches run k (step s) by IH. *)
  Qed.

  (* terminal_reachable_from_any_start: From any initial state, terminal is reachable. *)
  (* Existence theorem: there is always a path to completion. *)
  Theorem terminal_reachable_from_any_start
    : forall n,                         (* For any starting count n... *)
      exists s,                         (* ...there exists a state s... *)
        Reachable (initial n) s /\      (* ...reachable from initial n... *)
        terminal s.                     (* ...that is terminal. *)
  Proof.
    intro n.                            (* Introduce n. *)
    exists (run n (initial n)).         (* Witness: run n steps. *)
    split.                              (* Prove both conjuncts. *)
    - apply reachable_run.              (* run n (initial n) is reachable. *)
    - pose proof (sufficient_fuel_reaches_terminal (initial n)) as H.  (* It's terminal. *)
      unfold initial in *.              (* Expand initial. *)
      simpl in *.                       (* Simplify. *)
      exact H.                          (* Use the termination theorem. *)
  Qed.

  (* reachable_preserves_invariant: All reachable states satisfy the invariant. *)
  (* Inductive invariant: base case + preservation = all reachable states. *)
  Theorem reachable_preserves_invariant
    : forall s0 s,                      (* For any s0 and s... *)
      invariant s0 ->                   (* ...if s0 satisfies the invariant... *)
      Reachable s0 s ->                 (* ...and s is reachable from s0... *)
      invariant s.                      (* ...then s satisfies the invariant. *)
  Proof.
    intros s0 s Hinv Hreach.            (* Introduce states and hypotheses. *)
    induction Hreach.                   (* Induction on reachability proof. *)
    - exact Hinv.                       (* Base: s = s0, use Hinv. *)
    - rewrite H.                        (* Inductive: s' = step s. *)
      apply step_preserves_invariant.   (* step preserves invariant. *)
      exact IHHreach.                   (* s satisfies invariant by IH. *)
  Qed.

  (* reachable_preserves_starting_count: starting_count is constant along paths. *)
  (* Another invariant: the original count is remembered at every reachable state. *)
  Theorem reachable_preserves_starting_count
    : forall s0 s,                      (* For any s0 and s... *)
      Reachable s0 s ->                 (* ...if s is reachable from s0... *)
      starting_count s = starting_count s0.  (* ...they have the same starting_count. *)
  Proof.
    intros s0 s Hreach.                 (* Introduce states and reachability. *)
    induction Hreach.                   (* Induction on reachability. *)
    - reflexivity.                      (* Base: s = s0. *)
    - rewrite H.                        (* Inductive: s' = step s. *)
      rewrite step_preserves_starting_count.  (* step preserves starting_count. *)
      exact IHHreach.                   (* Use IH for s. *)
  Qed.

  (* conservation_law: The fundamental theorem—bottles are conserved. *)
  (* For any reachable state: on_wall + passed_around = starting count = n. *)
  Theorem conservation_law
    : forall n s,                       (* For any n and state s... *)
      Reachable (initial n) s ->        (* ...if s is reachable from initial n... *)
      on_wall s + passed_around s = n.  (* ...then on_wall + passed = n. *)
  Proof.
    intros n s Hreach.                  (* Introduce n, s, and reachability. *)
    pose proof (reachable_preserves_invariant (initial n) s) as Hinv.  (* Get invariant. *)
    pose proof (reachable_preserves_starting_count (initial n) s Hreach) as Hst.  (* Get starting_count. *)
    unfold invariant, initial in *.     (* Expand definitions. *)
    simpl in *.                         (* Simplify. *)
    rewrite Hst in Hinv.                (* starting_count s = n. *)
    apply Hinv.                         (* Apply the invariant. *)
    - unfold invariant, initial.        (* Need: invariant (initial n). *)
      simpl.                            (* n + 0 = n. *)
      lia.                              (* Arithmetic. *)
    - exact Hreach.                     (* Need: Reachable (initial n) s. *)
  Qed.

  (** ===================================================================== *)
  (** PART VI: STRING CONVERSION                                            *)
  (** ===================================================================== *)
  (** To generate actual song lyrics, we need to convert natural numbers    *)
  (** to strings (e.g., 99 → "99"). This is surprisingly subtle in a proof  *)
  (** assistant—we must prove our conversion is correct and invertible.     *)
  (** ===================================================================== *)

  (* digit_to_char: Converts a single digit 0-9 to its ASCII character. *)
  (* For d >= 10, defaults to '9' (though we'll only use valid digits). *)
  Definition digit_to_char (d : nat)    (* Takes a digit 0-9. *)
    : ascii                             (* Returns an ASCII character. *)
    := match d with                     (* Pattern match on the digit. *)
       | 0 => "0"                       (* 0 maps to character '0'. *)
       | 1 => "1"                       (* 1 maps to character '1'. *)
       | 2 => "2"                       (* 2 maps to character '2'. *)
       | 3 => "3"                       (* 3 maps to character '3'. *)
       | 4 => "4"                       (* 4 maps to character '4'. *)
       | 5 => "5"                       (* 5 maps to character '5'. *)
       | 6 => "6"                       (* 6 maps to character '6'. *)
       | 7 => "7"                       (* 7 maps to character '7'. *)
       | 8 => "8"                       (* 8 maps to character '8'. *)
       | _ => "9"                       (* 9 (or anything else) maps to '9'. *)
       end.

  (* digit_to_string: Wraps a digit character into a single-character string. *)
  (* Coq strings are lists of characters; String c EmptyString is [c]. *)
  Definition digit_to_string (d : nat)  (* Takes a digit 0-9. *)
    : string                            (* Returns a one-character string. *)
    := String (digit_to_char d) EmptyString.  (* Wrap the char in a string. *)

  (* nat_to_string_aux: Recursive helper for number-to-string conversion. *)
  (* Builds the string right-to-left using modulo and division by 10. *)
  (* The fuel parameter ensures termination (Coq requires structural decrease). *)
  Fixpoint nat_to_string_aux (fuel n : nat)  (* fuel for termination, n is the number. *)
                             (acc : string)  (* Accumulator for digits built so far. *)
    : string                            (* Returns the final string. *)
    := match fuel with                  (* Pattern match on fuel. *)
       | O => acc                       (* No fuel: return accumulator. *)
       | S f =>                         (* Fuel remaining: extract one digit. *)
           let d := n mod 10 in         (* d is the last digit of n. *)
           let r := n / 10 in           (* r is n with last digit removed. *)
           let acc' := digit_to_string d ++ acc in  (* Prepend digit to accumulator. *)
           match r with                 (* Check if more digits remain. *)
           | O => acc'                  (* r = 0: we're done. *)
           | _ => nat_to_string_aux f r acc'  (* r > 0: recurse with remaining digits. *)
           end
       end.

  (* nat_to_string: Converts a natural number to its decimal string representation. *)
  (* Special-cases 0 (which would otherwise produce empty string). *)
  Definition nat_to_string (n : nat)    (* Takes any natural number. *)
    : string                            (* Returns its string representation. *)
    := match n with                     (* Pattern match on n. *)
       | O => "0"                       (* Zero is just "0". *)
       | _ => nat_to_string_aux n n ""  (* Otherwise, use helper with n as fuel. *)
       end.

  (* nat_to_string_0: Sanity check—0 converts to "0". *)
  Lemma nat_to_string_0                 (* A simple computational test. *)
    : nat_to_string 0 = "0".            (* 0 should produce "0". *)
  Proof.
    reflexivity.                        (* Coq computes this directly. *)
  Qed.

  (* nat_to_string_1: Sanity check—1 converts to "1". *)
  Lemma nat_to_string_1                 (* Another computational test. *)
    : nat_to_string 1 = "1".            (* 1 should produce "1". *)
  Proof.
    reflexivity.                        (* Coq computes this directly. *)
  Qed.

  (* nat_to_string_10: Sanity check—10 converts to "10". *)
  Lemma nat_to_string_10                (* Test a two-digit number. *)
    : nat_to_string 10 = "10".          (* 10 should produce "10". *)
  Proof.
    reflexivity.                        (* Coq computes this directly. *)
  Qed.

  (* nat_to_string_99: Sanity check—99 converts to "99". *)
  Lemma nat_to_string_99                (* The song's starting count. *)
    : nat_to_string 99 = "99".          (* 99 should produce "99". *)
  Proof.
    reflexivity.                        (* Coq computes this directly. *)
  Qed.

  (* nat_to_string_42: Sanity check—42 converts to "42". *)
  Lemma nat_to_string_42                (* The answer to everything. *)
    : nat_to_string 42 = "42".          (* 42 should produce "42". *)
  Proof.
    reflexivity.                        (* Coq computes this directly. *)
  Qed.

  (* char_to_digit: Inverse of digit_to_char—converts '0'-'9' to 0-9. *)
  (* Returns None for non-digit characters. *)
  Definition char_to_digit (c : ascii)  (* Takes an ASCII character. *)
    : option nat                        (* Returns Some digit or None. *)
    := match c with                     (* Pattern match on the character. *)
       | "0" => Some 0                  (* '0' maps to 0. *)
       | "1" => Some 1                  (* '1' maps to 1. *)
       | "2" => Some 2                  (* '2' maps to 2. *)
       | "3" => Some 3                  (* '3' maps to 3. *)
       | "4" => Some 4                  (* '4' maps to 4. *)
       | "5" => Some 5                  (* '5' maps to 5. *)
       | "6" => Some 6                  (* '6' maps to 6. *)
       | "7" => Some 7                  (* '7' maps to 7. *)
       | "8" => Some 8                  (* '8' maps to 8. *)
       | "9" => Some 9                  (* '9' maps to 9. *)
       | _ => None                      (* Non-digit returns None. *)
       end%char.                        (* %char tells Coq these are character literals. *)

  (* char_to_digit_to_char: Round-trip property—digit to char to digit recovers the digit. *)
  (* This proves char_to_digit is a left inverse of digit_to_char on valid digits. *)
  Lemma char_to_digit_to_char
    : forall d,                         (* For any digit d... *)
      d < 10 ->                         (* ...if d is a valid digit (0-9)... *)
      char_to_digit (digit_to_char d) = Some d.  (* ...round-trip recovers d. *)
  Proof.
    intros d Hd.                        (* Introduce d and bound hypothesis. *)
    do 10 (destruct d; [reflexivity|]). (* Try d = 0, 1, ..., 9; each works. *)
    lia.                                (* d >= 10 contradicts Hd. *)
  Qed.

  (* digit_to_char_to_digit: The other round-trip—char to digit to char. *)
  (* If char_to_digit succeeds, digit_to_char inverts it. *)
  Lemma digit_to_char_to_digit
    : forall c d,                       (* For any character c and digit d... *)
      char_to_digit c = Some d ->       (* ...if c parses to d... *)
      digit_to_char d = c.              (* ...then d converts back to c. *)
  Proof.
    intros c d H.                       (* Introduce c, d, and hypothesis. *)
    destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].  (* Destruct ASCII into 8 bits. *)
    destruct b0, b1, b2, b3, b4, b5, b6, b7;  (* Case split on all 256 possibilities. *)
      simpl in H;                       (* Simplify char_to_digit. *)
      try discriminate H;               (* Most cases give None; discard them. *)
      injection H as <-;                (* Extract d from Some d. *)
      reflexivity.                      (* digit_to_char d = c follows. *)
  Qed.

  (* string_to_nat_aux: Recursive helper for string-to-number conversion. *)
  (* Processes characters left-to-right, accumulating the value. *)
  Fixpoint string_to_nat_aux (s : string)  (* The remaining string to parse. *)
                             (acc : nat)   (* Accumulated value so far. *)
    : option nat                        (* Returns Some n or None on invalid input. *)
    := match s with                     (* Pattern match on the string. *)
       | EmptyString => Some acc        (* Empty string: return accumulated value. *)
       | String c rest =>               (* Non-empty: process first character. *)
           match char_to_digit c with   (* Try to parse c as a digit. *)
           | None => None               (* Not a digit: parsing fails. *)
           | Some d => string_to_nat_aux rest (acc * 10 + d)  (* Shift acc and add d. *)
           end
       end.

  (* string_to_nat: Converts a decimal string to its natural number value. *)
  (* Returns None for empty strings or strings with non-digit characters. *)
  Definition string_to_nat (s : string) (* Takes a string. *)
    : option nat                        (* Returns Some n or None. *)
    := match s with                     (* Pattern match on the string. *)
       | EmptyString => None            (* Empty string is invalid. *)
       | String c rest =>               (* Non-empty: start parsing. *)
           match char_to_digit c with   (* Parse first character. *)
           | None => None               (* Not a digit: fail. *)
           | Some d => string_to_nat_aux rest d  (* Start accumulator with first digit. *)
           end
       end.

  (* string_to_nat_aux_app: Parsing a concatenation equals parsing sequentially. *)
  (* Key lemma for proving string operations compose correctly. *)
  Lemma string_to_nat_aux_app
    : forall s1 s2 acc,                 (* For any strings s1, s2 and accumulator... *)
        string_to_nat_aux (s1 ++ s2) acc =  (* Parsing s1++s2... *)
        match string_to_nat_aux s1 acc with  (* ...equals parsing s1 first... *)
        | None => None                  (* ...if s1 fails, whole thing fails... *)
        | Some n => string_to_nat_aux s2 n  (* ...otherwise continue with s2. *)
        end.
  Proof.
    induction s1.                       (* Induction on s1. *)
    - intros s2 acc.                    (* Base: s1 is empty. *)
      simpl.                            (* "" ++ s2 = s2; aux "" acc = Some acc. *)
      reflexivity.                      (* Both sides equal string_to_nat_aux s2 acc. *)
    - intros s2 acc.                    (* Inductive: s1 = String a s1'. *)
      simpl.                            (* Simplify the append and aux calls. *)
      destruct (char_to_digit a).       (* Case split on whether a is a digit. *)
      + apply IHs1.                     (* a is digit: apply induction hypothesis. *)
      + reflexivity.                    (* a not digit: both sides are None. *)
  Qed.

  (* string_to_nat_single: A single-digit string parses to that digit. *)
  Lemma string_to_nat_single
    : forall d,                         (* For any digit d... *)
      d < 10 ->                         (* ...if d is valid... *)
      string_to_nat (digit_to_string d) = Some d.  (* ...its string parses to d. *)
  Proof.
    intros d Hd.                        (* Introduce d and bound. *)
    unfold string_to_nat, digit_to_string.  (* Expand definitions. *)
    rewrite char_to_digit_to_char by assumption.  (* char_to_digit inverts digit_to_char. *)
    reflexivity.                        (* Some d = Some d. *)
  Qed.

  (* string_to_nat_aux_single: Auxiliary version of single-digit parsing. *)
  Lemma string_to_nat_aux_single
    : forall d acc,                     (* For any digit d and accumulator acc... *)
      d < 10 ->                         (* ...if d is valid... *)
      string_to_nat_aux (digit_to_string d) acc = Some (acc * 10 + d).  (* ...result is acc*10+d. *)
  Proof.
    intros d acc Hd.                    (* Introduce d, acc, and bound. *)
    unfold digit_to_string.             (* Expand digit_to_string. *)
    simpl.                              (* Simplify string_to_nat_aux. *)
    rewrite char_to_digit_to_char by assumption.  (* Use round-trip lemma. *)
    reflexivity.                        (* Some (acc * 10 + d) = Some (acc * 10 + d). *)
  Qed.

  (* string_app_assoc: String concatenation is associative. *)
  (* Standard property needed for reasoning about string operations. *)
  Lemma string_app_assoc
    : forall s1 s2 s3 : string,         (* For any three strings... *)
      (s1 ++ (s2 ++ s3) = (s1 ++ s2) ++ s3)%string.  (* ...++ is associative. *)
  Proof.
    induction s1.                       (* Induction on s1. *)
    - intros s2 s3.                     (* Base: s1 is empty. *)
      simpl.                            (* "" ++ x = x on both sides. *)
      reflexivity.                      (* s2 ++ s3 = s2 ++ s3. *)
    - intros s2 s3.                     (* Inductive: s1 = String a s1'. *)
      simpl.                            (* Simplify both sides. *)
      rewrite IHs1.                     (* Apply induction hypothesis. *)
      reflexivity.                      (* String a (...) = String a (...). *)
  Qed.

  (* string_cons_app: String cons distributes over append. *)
  (* String c s1 ++ s2 = String c (s1 ++ s2). *)
  Lemma string_cons_app
    : forall c s1 s2,                   (* For any character and two strings... *)
      String c s1 ++ s2 = String c (s1 ++ s2).  (* ...cons distributes. *)
  Proof.
    reflexivity.                        (* This is true by definition of ++. *)
  Qed.

  (* nat_to_string_aux_app_gen: General form of aux append property. *)
  (* Building with acc1++acc2 equals building with acc1 then appending acc2. *)
  Lemma nat_to_string_aux_app_gen
    : forall f n acc1 acc2,             (* For any fuel, number, and accumulators... *)
      nat_to_string_aux f n (acc1 ++ acc2) =  (* Building with concatenated acc... *)
      nat_to_string_aux f n acc1 ++ acc2.     (* ...equals building then appending. *)
  Proof.
    induction f.                        (* Induction on fuel. *)
    - intros n acc1 acc2.               (* Base: no fuel. *)
      reflexivity.                      (* Both sides return the accumulator. *)
    - intros n acc1 acc2.               (* Inductive: fuel = S f'. *)
      cbn -[Nat.div Nat.modulo].        (* Simplify, but don't unfold div/mod. *)
      destruct (n / 10).                (* Case split on quotient. *)
      + reflexivity.                    (* Quotient 0: done, just return acc'. *)
      + rewrite <- string_cons_app.     (* Quotient > 0: use cons distribution. *)
        apply IHf.                      (* Apply induction hypothesis. *)
  Qed.

  (* nat_to_string_aux_app': Specialized version starting with empty accumulator. *)
  Lemma nat_to_string_aux_app'
    : forall f n acc,                   (* For any fuel, number, and accumulator... *)
      nat_to_string_aux f n acc =       (* Building with acc... *)
      nat_to_string_aux f n "" ++ acc.  (* ...equals building from "" then appending. *)
  Proof.
    intros f n acc.                     (* Introduce f, n, acc. *)
    change acc with ("" ++ acc).        (* Rewrite acc as "" ++ acc. *)
    apply nat_to_string_aux_app_gen.    (* Apply the general lemma. *)
  Qed.

  (* div10_lt: Dividing a positive number by 10 yields a smaller number. *)
  (* Key lemma for termination arguments. *)
  Lemma div10_lt
    : forall n,                         (* For any n... *)
      n > 0 ->                          (* ...if n is positive... *)
      n / 10 < n.                       (* ...then n/10 < n. *)
  Proof.
    intros n Hn.                        (* Introduce n and positivity. *)
    apply Nat.div_lt.                   (* Standard library lemma. *)
    - lia.                              (* n > 0. *)
    - lia.                              (* 10 > 1. *)
  Qed.

  (* digit_to_string_length: A digit string has length 1. *)
  Lemma digit_to_string_length
    : forall d,                         (* For any digit d... *)
      String.length (digit_to_string d) = 1.  (* ...its string has length 1. *)
  Proof.
    intro d.                            (* Introduce d. *)
    unfold digit_to_string.             (* Expand definition. *)
    reflexivity.                        (* String c "" has length 1 by definition. *)
  Qed.

  (* string_app_length_early: Length of concatenation is sum of lengths. *)
  Lemma string_app_length_early
    : forall s1 s2,                     (* For any two strings... *)
      String.length (s1 ++ s2) = String.length s1 + String.length s2.  (* ...lengths add. *)
  Proof.
    induction s1.                       (* Induction on s1. *)
    - intro s2.                         (* Base: s1 is empty. *)
      simpl.                            (* length "" = 0; 0 + length s2 = length s2. *)
      reflexivity.                      (* Both sides equal length s2. *)
    - intro s2.                         (* Inductive: s1 = String a s1'. *)
      simpl.                            (* length (String a ...) = S (length ...). *)
      rewrite IHs1.                     (* Apply induction hypothesis. *)
      reflexivity.                      (* S (... + ...) = S ... + ... by arithmetic. *)
  Qed.

  (* nat_to_string_aux_nonempty: With positive fuel, result is nonempty. *)
  Lemma nat_to_string_aux_nonempty
    : forall f n,                       (* For any fuel and number... *)
      f > 0 ->                          (* ...if fuel is positive... *)
      String.length (nat_to_string_aux f n "") > 0.  (* ...result is nonempty. *)
  Proof.
    intros f n Hf.                      (* Introduce f, n, and fuel bound. *)
    destruct f.                         (* Case split on f. *)
    - lia.                              (* f = 0 contradicts Hf. *)
    - unfold nat_to_string_aux.         (* Expand one level. *)
      fold nat_to_string_aux.           (* Re-fold recursive calls. *)
      destruct (n / 10).                (* Case split on quotient. *)
      + unfold digit_to_string.         (* Quotient 0: result is single digit. *)
        simpl.                          (* length (String c "") = 1. *)
        lia.                            (* 1 > 0. *)
      + rewrite nat_to_string_aux_app'. (* Quotient > 0: use append property. *)
        rewrite string_app_length_early.  (* Length of append = sum of lengths. *)
        unfold digit_to_string.         (* Expand digit_to_string. *)
        simpl.                          (* Simplify length. *)
        lia.                            (* Sum includes 1, so > 0. *)
  Qed.

  (* nat_to_string_aux_first_char_digit: First character of result is always a digit. *)
  (* Important for distinguishing numbers from other text. *)
  Lemma nat_to_string_aux_first_char_digit
    : forall f n,                       (* For any fuel and number... *)
      f > 0 ->                          (* ...if fuel is positive... *)
      exists c rest,                    (* ...there exist a character and rest... *)
        nat_to_string_aux f n "" = String c rest /\  (* ...result is String c rest... *)
        exists d, d < 10 /\ c = digit_to_char d.     (* ...and c is a digit character. *)
  Proof.
    intro f.                            (* Introduce f. *)
    induction f as [f IH] using (well_founded_induction lt_wf).  (* Strong induction. *)
    intros n Hf.                        (* Introduce n and fuel bound. *)
    destruct f.                         (* Case split on f. *)
    - lia.                              (* f = 0 contradicts Hf. *)
    - unfold nat_to_string_aux.         (* Expand one level. *)
      fold nat_to_string_aux.           (* Re-fold recursive calls. *)
      destruct (n / 10) eqn:Hr.         (* Case split on quotient, remembering equation. *)
      + exists (digit_to_char (n mod 10)), "".  (* Quotient 0: single digit result. *)
        split.                          (* Prove both parts of conjunction. *)
        * reflexivity.                  (* The string equality is definitional. *)
        * exists (n mod 10).            (* Witness: the digit is n mod 10. *)
          split.                        (* Prove both parts. *)
          -- apply Nat.mod_upper_bound. (* n mod 10 < 10 when 10 ≠ 0. *)
             lia.                       (* 10 ≠ 0. *)
          -- reflexivity.               (* c = digit_to_char (n mod 10). *)
      + rewrite nat_to_string_aux_app'. (* Quotient > 0: use append property. *)
        destruct f.                     (* Subcase on remaining fuel. *)
        * simpl.                        (* f = 0: just the digit. *)
          exists (digit_to_char (n mod 10)), "".
          split.
          -- reflexivity.
          -- exists (n mod 10).
             split.
             ++ apply Nat.mod_upper_bound.
                lia.
             ++ reflexivity.
        * destruct (nat_to_string_aux (S f) (S n0) "") eqn:Haux.  (* Get result of recursive call. *)
          -- exfalso.                   (* Empty result is impossible. *)
             assert (Hlen : String.length (nat_to_string_aux (S f) (S n0) "") > 0).
             { apply nat_to_string_aux_nonempty.
               lia. }
             rewrite Haux in Hlen.      (* Substitute empty string. *)
             simpl in Hlen.             (* length "" = 0. *)
             lia.                       (* 0 > 0 is false. *)
          -- exists a, (s ++ digit_to_string (n mod 10)).  (* Result starts with a. *)
             split.
             ++ reflexivity.            (* String equality holds. *)
             ++ destruct (IH (S f)) with (n := S n0) as [c' [rest' [Heq' [d' [Hd' Hc']]]]].
                ** lia.                 (* S f < S (S f). *)
                ** lia.                 (* S f > 0. *)
                ** rewrite Heq' in Haux.  (* Substitute into equation. *)
                   injection Haux as Ha Hs.  (* Extract equalities. *)
                   exists d'.           (* Same digit d' works. *)
                   split.
                   --- exact Hd'.       (* d' < 10. *)
                   --- congruence.      (* a = c' = digit_to_char d'. *)
  Qed.

  (* char_to_digit_digit_to_char_Some: Applying both functions yields Some. *)
  Lemma char_to_digit_digit_to_char_Some
    : forall d,                         (* For any digit d... *)
      d < 10 ->                         (* ...if d is valid... *)
      exists k,                         (* ...there exists some k... *)
        char_to_digit (digit_to_char d) = Some k.  (* ...such that parsing succeeds. *)
  Proof.
    intros d Hd.                        (* Introduce d and bound. *)
    exists d.                           (* The k is just d itself. *)
    apply char_to_digit_to_char.        (* Use the round-trip lemma. *)
    exact Hd.                           (* d < 10. *)
  Qed.

  (* nat_to_string_aux_value: Parsing the aux result recovers the original number. *)
  (* The main correctness theorem for the auxiliary conversion function. *)
  Lemma nat_to_string_aux_value
    : forall n f,                       (* For any number n and fuel f... *)
      n > 0 ->                          (* ...if n is positive... *)
      f >= n ->                         (* ...and we have enough fuel... *)
      string_to_nat (nat_to_string_aux f n "") = Some n.  (* ...parsing recovers n. *)
  Proof.
    intro n.                            (* Introduce n. *)
    induction n as [n IH] using (well_founded_induction lt_wf).  (* Strong induction on n. *)
    intros f Hn Hf.                     (* Introduce fuel, positivity, and bound. *)
    destruct f.                         (* Case split on fuel. *)
    - lia.                              (* f = 0 but f >= n > 0: contradiction. *)
    - unfold nat_to_string_aux.         (* Expand one level of aux. *)
      fold nat_to_string_aux.           (* Re-fold recursive calls. *)
      destruct (n / 10) eqn:Hr.         (* Case split on quotient. *)
      + assert (Hmod : n mod 10 = n).   (* If n/10 = 0, then n < 10, so n mod 10 = n. *)
        { apply Nat.mod_small.          (* Lemma: if n < 10 then n mod 10 = n. *)
          apply Nat.div_small_iff.      (* n/10 = 0 iff n < 10. *)
          - lia.                        (* 10 ≠ 0. *)
          - exact Hr. }                 (* n/10 = 0 by hypothesis. *)
        assert (Hn_bound : n < 10).     (* n < 10 follows from n/10 = 0. *)
        { apply Nat.div_small_iff in Hr.
          - lia.
          - lia. }
        unfold string_to_nat, digit_to_string.  (* Expand definitions. *)
        rewrite Hmod.                   (* n mod 10 = n. *)
        simpl.                          (* Simplify the string operations. *)
        rewrite char_to_digit_to_char by lia.  (* Round-trip on digit. *)
        reflexivity.                    (* Some n = Some n. *)
      + rewrite nat_to_string_aux_app'. (* n/10 > 0: use append property. *)
        assert (Hr_pos : S n0 > 0) by lia.  (* S n0 is positive. *)
        assert (Hr_lt : S n0 < n).      (* S n0 < n because S n0 = n/10. *)
        { rewrite <- Hr.                (* Rewrite to n/10. *)
          apply div10_lt.               (* n/10 < n when n > 0. *)
          lia. }
        assert (Hd_bound : n mod 10 < 10).  (* The digit is < 10. *)
        { apply Nat.mod_upper_bound.
          lia. }
        assert (Hf_r : f >= S n0) by lia.  (* Remaining fuel suffices. *)
        destruct (nat_to_string_aux f (S n0) "") eqn:Haux.  (* Get recursive result. *)
        * exfalso.                      (* Empty result is impossible. *)
          assert (Hlen : String.length (nat_to_string_aux f (S n0) "") > 0).
          { apply nat_to_string_aux_nonempty.
            lia. }
          rewrite Haux in Hlen.
          simpl in Hlen.
          lia.
        * assert (Haux_val : string_to_nat (String a s) = Some (S n0)).  (* Recursive call correct. *)
          { rewrite <- Haux.
            apply IH.
            - lia.                      (* S n0 < n. *)
            - lia.                      (* S n0 > 0. *)
            - lia. }                    (* f >= S n0. *)
          unfold string_to_nat in Haux_val.  (* Expand string_to_nat. *)
          destruct (char_to_digit a) eqn:Hchar.  (* Case on first character. *)
          -- unfold string_to_nat.      (* Expand for main goal. *)
             cbn -[Nat.modulo].         (* Simplify, preserving modulo. *)
             rewrite Hchar.             (* Substitute first digit. *)
             rewrite string_to_nat_aux_app.  (* Use concatenation lemma. *)
             rewrite Haux_val.          (* Substitute recursive result. *)
             unfold digit_to_string.    (* Expand digit string. *)
             cbn -[Nat.modulo].         (* Simplify. *)
             rewrite char_to_digit_to_char by assumption.  (* Round-trip. *)
             f_equal.                   (* Just need to prove n = S n0 * 10 + n mod 10. *)
             pose proof (Nat.div_mod_eq n 10) as Heq.  (* n = 10*(n/10) + n mod 10. *)
             rewrite Hr in Heq.         (* n/10 = S n0. *)
             lia.                       (* Arithmetic gives n = S n0 * 10 + n mod 10. *)
          -- discriminate Haux_val.     (* If char_to_digit a = None, Haux_val is contradictory. *)
  Qed.

  (* nat_to_string_to_nat: The main round-trip theorem. *)
  (* Converting n to string and back yields n (for positive n). *)
  Theorem nat_to_string_to_nat
    : forall n,                         (* For any natural number n... *)
      n > 0 ->                          (* ...if n is positive... *)
      string_to_nat (nat_to_string n) = Some n.  (* ...round-trip recovers n. *)
  Proof.
    intros n Hn.                        (* Introduce n and positivity. *)
    unfold nat_to_string.               (* Expand nat_to_string. *)
    destruct n.                         (* Case split on n. *)
    - lia.                              (* n = 0 contradicts Hn. *)
    - apply nat_to_string_aux_value.    (* Use the auxiliary lemma. *)
      + lia.                            (* S n > 0. *)
      + lia.                            (* S n >= S n. *)
  Qed.

  (* nat_to_string_inj: nat_to_string is injective on positive numbers. *)
  (* Different positive numbers produce different strings. *)
  Theorem nat_to_string_inj
    : forall n1 n2,                     (* For any n1 and n2... *)
      n1 > 0 ->                         (* ...if n1 is positive... *)
      n2 > 0 ->                         (* ...and n2 is positive... *)
      nat_to_string n1 = nat_to_string n2 ->  (* ...and they have the same string... *)
      n1 = n2.                          (* ...then they're equal. *)
  Proof.
    intros n1 n2 H1 H2 Heq.             (* Introduce hypotheses. *)
    apply (f_equal string_to_nat) in Heq.  (* Apply string_to_nat to both sides. *)
    rewrite nat_to_string_to_nat in Heq by assumption.  (* Left side becomes Some n1. *)
    rewrite nat_to_string_to_nat in Heq by assumption.  (* Right side becomes Some n2. *)
    injection Heq as Heq.               (* Some n1 = Some n2 implies n1 = n2. *)
    exact Heq.                          (* The conclusion. *)
  Qed.

  (* first_char: Extracts the first character of a string, if any. *)
  Definition first_char (s : string)    (* Takes a string. *)
    : option ascii                      (* Returns Some c or None. *)
    := match s with                     (* Pattern match on the string. *)
       | EmptyString => None            (* Empty string has no first character. *)
       | String c _ => Some c           (* Non-empty: return the first character. *)
       end.

  (* canonical_nat_string: A string is "canonical" if it's "0" or starts with non-zero digit. *)
  (* This rules out leading zeros like "007". *)
  Definition canonical_nat_string (s : string)  (* Takes a string. *)
    : Prop                              (* Returns a proposition. *)
    := s = "0" \/                       (* Either it's exactly "0"... *)
       (s <> EmptyString /\             (* ...or it's nonempty... *)
        forall c, first_char s = Some c -> c <> "0"%char).  (* ...and doesn't start with '0'. *)

  (* nat_to_string_pos_not_zero_char: Positive numbers don't start with '0'. *)
  Lemma nat_to_string_pos_not_zero_char
    : forall n,                         (* For any n... *)
      n > 0 ->                          (* ...if n is positive... *)
      n <= 99 ->                        (* ...and at most 99 (for computation)... *)
      forall c,                         (* ...for any character c... *)
        first_char (nat_to_string n) = Some c ->  (* ...if c is the first char... *)
        c <> "0"%char.                  (* ...then c is not '0'. *)
  Proof.
    intros n Hpos Hle c Hfc Heq.        (* Introduce all hypotheses. *)
    destruct n.                         (* Case split on n. *)
    - lia.                              (* n = 0 contradicts Hpos. *)
    - do 99 (destruct n; [simpl in Hfc; injection Hfc as <-; discriminate Heq|]).
      (* Try n = 0, 1, ..., 98; each gives first char ≠ '0'. *)
      lia.                              (* n >= 99 contradicts Hle. *)
  Qed.

  (* nat_to_string_canonical: nat_to_string produces canonical strings. *)
  Lemma nat_to_string_canonical
    : forall n,                         (* For any n... *)
      n <= 99 ->                        (* ...up to 99... *)
      canonical_nat_string (nat_to_string n).  (* ...the result is canonical. *)
  Proof.
    intros n Hle.                       (* Introduce n and bound. *)
    destruct n as [|n'].                (* Case split: n = 0 or n = S n'. *)
    - left.                             (* n = 0: nat_to_string 0 = "0". *)
      reflexivity.
    - right.                            (* n > 0: prove it's nonempty and no leading zero. *)
      split.                            (* Prove both conjuncts. *)
      + unfold nat_to_string.           (* Expand definition. *)
        destruct (nat_to_string_aux_first_char_digit (S n') (S n') ltac:(lia))
          as [c [rest [Heq _]]].        (* Get that result is String c rest. *)
        rewrite Heq.                    (* Substitute. *)
        discriminate.                   (* String c rest ≠ EmptyString. *)
      + intros c Hfc.                   (* Introduce c and first_char hypothesis. *)
        apply (nat_to_string_pos_not_zero_char (S n')).  (* Use the previous lemma. *)
        * lia.                          (* S n' > 0. *)
        * lia.                          (* S n' <= 99. *)
        * exact Hfc.                    (* first_char gives c. *)
  Qed.

  (* string_to_nat_aux_ge: Parsing always yields a result >= accumulator. *)
  Lemma string_to_nat_aux_ge
    : forall s acc n,                   (* For any string, accumulator, and result... *)
      string_to_nat_aux s acc = Some n ->  (* ...if parsing succeeds... *)
      n >= acc.                         (* ...then result >= accumulator. *)
  Proof.
    induction s.                        (* Induction on the string. *)
    - intros acc n H.                   (* Base: empty string. *)
      simpl in H.                       (* aux "" acc = Some acc. *)
      injection H as H.                 (* Extract acc = n. *)
      lia.                              (* n >= n. *)
    - intros acc n H.                   (* Inductive: String a s. *)
      simpl in H.                       (* Expand aux. *)
      destruct (char_to_digit a).       (* Case on first character. *)
      + apply IHs in H.                 (* a is digit: apply IH. *)
        lia.                            (* Result >= acc*10+d >= acc. *)
      + discriminate H.                 (* a not digit: H is contradictory. *)
  Qed.

  (* string_to_nat_first_zero_implies_zero: If parsing gives 0, string starts with '0'. *)
  Lemma string_to_nat_first_zero_implies_zero
    : forall s,                         (* For any string s... *)
      string_to_nat s = Some 0 ->       (* ...if it parses to 0... *)
      exists rest,                      (* ...there exists a rest... *)
        s = String "0"%char rest /\     (* ...such that s starts with '0'... *)
        string_to_nat_aux rest 0 = Some 0.  (* ...and rest also parses to 0. *)
  Proof.
    intros s H.                         (* Introduce s and hypothesis. *)
    destruct s as [|c rest].            (* Case split on s. *)
    - discriminate H.                   (* Empty string: string_to_nat "" = None. *)
    - unfold string_to_nat in H.        (* Expand string_to_nat. *)
      destruct (char_to_digit c) eqn:Hcd.  (* Case on first character. *)
      + destruct n.                     (* Case on the digit value. *)
        * exists rest.                  (* Digit is 0. *)
          destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].  (* Destruct character. *)
          destruct b0, b1, b2, b3, b4, b5, b6, b7;  (* All 256 cases. *)
            try discriminate Hcd.       (* Most aren't '0'. *)
          split.
          -- reflexivity.               (* s = String "0" rest. *)
          -- exact H.                   (* rest parses to 0. *)
        * simpl in H.                   (* Digit > 0. *)
          pose proof (string_to_nat_aux_ge rest (S n) 0 H).  (* Result >= S n. *)
          lia.                          (* But result = 0 < S n: contradiction. *)
      + discriminate H.                 (* Not a digit: H is contradictory. *)
  Qed.

  (* string_to_nat_nat_to_string_roundtrip: Explicit name for the round-trip property. *)
  Theorem string_to_nat_nat_to_string_roundtrip
    : forall n,                         (* For any n... *)
      n > 0 ->                          (* ...if positive... *)
      string_to_nat (nat_to_string n) = Some n.  (* ...round-trip works. *)
  Proof.
    intros n Hn.                        (* Introduce n and positivity. *)
    apply nat_to_string_to_nat.         (* Use the main theorem. *)
    lia.                                (* n > 0. *)
  Qed.

  (* string_to_nat_zero: Parsing "0" gives 0. *)
  Lemma string_to_nat_zero
    : string_to_nat "0" = Some 0.       (* "0" parses to 0. *)
  Proof.
    reflexivity.                        (* Coq computes this. *)
  Qed.

  (** ===================================================================== *)
  (** PART VII: LEADING NUMBER EXTRACTION                                   *)
  (** ===================================================================== *)
  (** For parsing verses, we need to extract numbers from the beginning of  *)
  (** strings that may contain non-digit suffixes (e.g., "99 bottles").     *)
  (** This is more permissive than string_to_nat which requires all digits. *)
  (** ===================================================================== *)

  (* leading_nat_aux: Extracts leading digits, stopping at first non-digit. *)
  (* Like string_to_nat_aux but doesn't fail on non-digits—just stops. *)
  Fixpoint leading_nat_aux (s : string) (* The string to scan. *)
                           (acc : nat)  (* Accumulated value. *)
    : nat                               (* Returns the accumulated number. *)
    := match s with                     (* Pattern match on string. *)
       | EmptyString => acc             (* Empty: return accumulator. *)
       | String c rest =>               (* Non-empty: check first character. *)
           match char_to_digit c with   (* Try to parse as digit. *)
           | None => acc                (* Not a digit: stop and return acc. *)
           | Some d => leading_nat_aux rest (acc * 10 + d)  (* Digit: continue. *)
           end
       end.

  (* leading_nat: Extracts the leading natural number from a string. *)
  (* Returns None if string doesn't start with a digit. *)
  Definition leading_nat (s : string)   (* Takes a string. *)
    : option nat                        (* Returns Some n or None. *)
    := match s with                     (* Pattern match on string. *)
       | EmptyString => None            (* Empty string: no number. *)
       | String c rest =>               (* Non-empty: check first char. *)
           match char_to_digit c with   (* Try to parse first char. *)
           | None => None               (* Not a digit: no leading number. *)
           | Some d => Some (leading_nat_aux rest d)  (* Digit: extract number. *)
           end
       end.

  (* is_digit: Boolean predicate testing if a character is '0'-'9'. *)
  (* Useful for deciding whether to continue parsing. *)
  Definition is_digit (c : ascii)       (* Takes a character. *)
    : bool                              (* Returns true iff c is a digit. *)
    := match c with                     (* Pattern match on character. *)
       | "0" | "1" | "2" | "3" | "4"    (* Digits 0-4. *)
       | "5" | "6" | "7" | "8" | "9"    (* Digits 5-9. *)
         => true                        (* These are digits. *)
       | _ => false                     (* Everything else is not. *)
       end%char.                        (* %char for character literals. *)

  (* leading_nat_aux_app_non_digit: Non-digit stops extraction. *)
  (* If we hit a non-digit, the suffix doesn't matter. *)
  Lemma leading_nat_aux_app_non_digit
    : forall s1 s2 acc c,               (* For strings s1, s2, accumulator, and char c... *)
        is_digit c = false ->           (* ...if c is not a digit... *)
        leading_nat_aux (s1 ++ String c s2) acc =  (* ...extracting from s1++c++s2... *)
        leading_nat_aux s1 acc.         (* ...equals extracting from just s1. *)
  Proof.
    induction s1.                       (* Induction on s1. *)
    - intros s2 acc c Hc.               (* Base: s1 is empty. *)
      simpl.                            (* "" ++ String c s2 = String c s2. *)
      unfold is_digit in Hc.            (* Expand is_digit. *)
      destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].  (* Destruct character into bits. *)
      destruct b0, b1, b2, b3, b4, b5, b6, b7;  (* All 256 cases. *)
        try discriminate Hc;            (* Digits have is_digit = true; skip. *)
        reflexivity.                    (* Non-digits: char_to_digit = None. *)
    - intros s2 acc c Hc.               (* Inductive: s1 = String a s1'. *)
      simpl.                            (* Simplify both sides. *)
      destruct (char_to_digit a) eqn:Ha.  (* Case on first character of s1. *)
      + apply IHs1.                     (* a is digit: recurse. *)
        exact Hc.                       (* c is still not a digit. *)
      + reflexivity.                    (* a not digit: both sides return acc. *)
  Qed.

  (* all_digits: Boolean predicate—are all characters in the string digits? *)
  Fixpoint all_digits (s : string)      (* Takes a string. *)
    : bool                              (* Returns true iff all chars are digits. *)
    := match s with                     (* Pattern match on string. *)
       | EmptyString => true            (* Empty string: vacuously true. *)
       | String c rest =>               (* Non-empty: check first and recurse. *)
           is_digit c && all_digits rest  (* Both must be true. *)
       end.

  (* leading_nat_aux_string_to_nat_aux: On all-digit strings, both functions agree. *)
  (* When there are no non-digits to stop at, leading_nat_aux = string_to_nat_aux. *)
  Lemma leading_nat_aux_string_to_nat_aux
    : forall s acc,                     (* For any string and accumulator... *)
        all_digits s = true ->          (* ...if all characters are digits... *)
        string_to_nat_aux s acc = Some (leading_nat_aux s acc).  (* ...functions agree. *)
  Proof.
    induction s.                        (* Induction on string. *)
    - intros acc Hd.                    (* Base: empty string. *)
      simpl.                            (* Both return acc. *)
      reflexivity.                      (* Some acc = Some acc. *)
    - intros acc Hd.                    (* Inductive: String a s. *)
      simpl in Hd.                      (* Expand all_digits. *)
      destruct (is_digit a) eqn:Ha.     (* Case on is_digit a. *)
      + simpl in Hd.                    (* is_digit a = true, so check rest. *)
        unfold is_digit in Ha.          (* Expand is_digit to find char_to_digit. *)
        destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].  (* Destruct character. *)
        destruct b0, b1, b2, b3, b4, b5, b6, b7;  (* All cases. *)
          try discriminate Ha;          (* Non-digits have is_digit = false. *)
          simpl;                        (* Simplify both sides. *)
          apply IHs;                    (* Apply induction hypothesis. *)
          exact Hd.                     (* Rest is all digits. *)
      + simpl in Hd.                    (* is_digit a = false. *)
        discriminate.                   (* But all_digits requires is_digit a = true. *)
  Qed.

  (* is_digit_digit_to_char: digit_to_char always produces a digit character. *)
  Lemma is_digit_digit_to_char
    : forall d,                         (* For any d... *)
      d < 10 ->                         (* ...if d is a valid digit... *)
      is_digit (digit_to_char d) = true.  (* ...digit_to_char d is a digit char. *)
  Proof.
    intros d Hd.                        (* Introduce d and bound. *)
    do 10 (destruct d; [reflexivity|]). (* Try d = 0..9; each works. *)
    lia.                                (* d >= 10 contradicts Hd. *)
  Qed.

  (* all_digits_app: all_digits distributes over concatenation. *)
  Lemma all_digits_app
    : forall s1 s2,                     (* For any two strings... *)
      all_digits (s1 ++ s2) =           (* ...all_digits of concatenation... *)
      (all_digits s1 && all_digits s2)%bool.  (* ...equals AND of each. *)
  Proof.
    induction s1.                       (* Induction on s1. *)
    - intro s2.                         (* Base: s1 is empty. *)
      simpl.                            (* "" ++ s2 = s2; all_digits "" = true. *)
      reflexivity.                      (* true && all_digits s2 = all_digits s2. *)
    - intro s2.                         (* Inductive: s1 = String a s1'. *)
      simpl.                            (* Expand all_digits on both sides. *)
      rewrite IHs1.                     (* Apply induction hypothesis. *)
      destruct (is_digit a).            (* Case on is_digit a. *)
      + simpl.                          (* true && x = x. *)
        reflexivity.                    (* (x && y) = (x && y). *)
      + simpl.                          (* false && x = false. *)
        reflexivity.                    (* false = false. *)
  Qed.

  (* all_digits_digit_to_string: A single digit string is all digits. *)
  Lemma all_digits_digit_to_string
    : forall d,                         (* For any d... *)
      d < 10 ->                         (* ...if valid... *)
      all_digits (digit_to_string d) = true.  (* ...its string is all digits. *)
  Proof.
    intros d Hd.                        (* Introduce d and bound. *)
    unfold digit_to_string.             (* Expand definition. *)
    simpl.                              (* all_digits (String c "") = is_digit c && true. *)
    rewrite is_digit_digit_to_char by exact Hd.  (* is_digit (digit_to_char d) = true. *)
    reflexivity.                        (* true && true = true. *)
  Qed.

  (* is_digit_digit_to_char_any: digit_to_char always produces digit, even for d >= 10. *)
  (* Because the default case maps to '9', which is still a digit. *)
  Lemma is_digit_digit_to_char_any
    : forall d,                         (* For any d (no bound needed)... *)
      is_digit (digit_to_char d) = true.  (* ...digit_to_char d is a digit. *)
  Proof.
    intro d.                            (* Introduce d. *)
    do 10 (destruct d; [reflexivity|]). (* d = 0..9 are explicit. *)
    reflexivity.                        (* d >= 10 defaults to '9', also a digit. *)
  Qed.

  (* nat_to_string_aux_all_digits_gen: aux result with digit acc is all digits. *)
  Lemma nat_to_string_aux_all_digits_gen
    : forall f n acc,                   (* For any fuel, number, and accumulator... *)
      all_digits acc = true ->          (* ...if acc is all digits... *)
      all_digits (nat_to_string_aux f n acc) = true.  (* ...so is the result. *)
  Proof.
    induction f.                        (* Induction on fuel. *)
    - intros n acc Hacc.                (* Base: no fuel. *)
      exact Hacc.                       (* Result is just acc. *)
    - intros n acc Hacc.                (* Inductive: fuel = S f'. *)
      cbn -[Nat.div Nat.modulo].        (* Simplify, preserving div/mod. *)
      destruct (n / 10) eqn:Hr.         (* Case on quotient. *)
      + unfold digit_to_string.         (* Quotient 0: prepend one digit. *)
        simpl.                          (* Expand all_digits. *)
        rewrite is_digit_digit_to_char_any.  (* First char is digit. *)
        simpl.                          (* true && acc = acc. *)
        exact Hacc.                     (* acc is all digits. *)
      + apply IHf.                      (* Quotient > 0: recurse. *)
        unfold digit_to_string.         (* New acc has digit prepended. *)
        simpl.                          (* Expand all_digits. *)
        rewrite is_digit_digit_to_char_any.  (* Prepended char is digit. *)
        simpl.                          (* true && acc = acc. *)
        exact Hacc.                     (* Original acc is all digits. *)
  Qed.

  (* nat_to_string_aux_all_digits: aux with empty acc produces all-digit string. *)
  Lemma nat_to_string_aux_all_digits
    : forall f n,                       (* For any fuel and number... *)
      all_digits (nat_to_string_aux f n "") = true.  (* ...result is all digits. *)
  Proof.
    intros f n.                         (* Introduce f and n. *)
    apply nat_to_string_aux_all_digits_gen.  (* Use general lemma. *)
    reflexivity.                        (* all_digits "" = true. *)
  Qed.

  (* nat_to_string_all_digits: nat_to_string always produces all-digit strings. *)
  Lemma nat_to_string_all_digits
    : forall n,                         (* For any n... *)
      all_digits (nat_to_string n) = true.  (* ...its string is all digits. *)
  Proof.
    intro n.                            (* Introduce n. *)
    unfold nat_to_string.               (* Expand definition. *)
    destruct n.                         (* Case on n. *)
    - reflexivity.                      (* n = 0: "0" is all digits. *)
    - apply nat_to_string_aux_all_digits.  (* n > 0: use aux lemma. *)
  Qed.

  (* leading_nat_nat_to_string: Extracting leading nat from nat_to_string recovers n. *)
  Lemma leading_nat_nat_to_string
    : forall n,                         (* For any n... *)
      n > 0 ->                          (* ...if positive... *)
      leading_nat (nat_to_string n) = Some n.  (* ...leading_nat recovers n. *)
  Proof.
    intros n Hn.                        (* Introduce n and positivity. *)
    pose proof (nat_to_string_to_nat n Hn) as H.  (* Round-trip via string_to_nat. *)
    pose proof (nat_to_string_all_digits n) as Hd.  (* nat_to_string is all digits. *)
    unfold string_to_nat in H.          (* Expand string_to_nat. *)
    unfold leading_nat.                 (* Expand leading_nat. *)
    destruct (nat_to_string n) eqn:Ens. (* Case on the string. *)
    - unfold nat_to_string in Ens.      (* String is empty? *)
      destruct n.                       (* Case on n. *)
      + lia.                            (* n = 0 contradicts Hn. *)
      + pose proof (nat_to_string_aux_nonempty (S n) (S n) ltac:(lia)) as Hne.
        rewrite Ens in Hne.             (* Substitute empty string. *)
        simpl in Hne.                   (* length "" = 0. *)
        lia.                            (* 0 > 0 is false. *)
    - destruct (char_to_digit a) eqn:Ha.  (* Case on first character. *)
      + f_equal.                        (* Both sides are Some _; prove insides equal. *)
        simpl in Hd.                    (* Expand all_digits. *)
        destruct (is_digit a) eqn:Hdig. (* Case on is_digit a. *)
        * simpl in Hd.                  (* is_digit a = true. *)
          rewrite leading_nat_aux_string_to_nat_aux in H by exact Hd.
          (* leading_nat_aux = string_to_nat_aux on all-digit strings. *)
          injection H as H.             (* Extract equality. *)
          exact H.                      (* The values are equal. *)
        * simpl in Hd.                  (* is_digit a = false. *)
          discriminate Hd.              (* But Hd says all_digits = true. *)
      + discriminate H.                 (* char_to_digit a = None contradicts H. *)
  Qed.

  (* leading_nat_app_non_digit: Non-digit suffix doesn't affect leading_nat. *)
  Lemma leading_nat_app_non_digit
    : forall s1 s2 c,                   (* For strings s1, s2 and character c... *)
        is_digit c = false ->           (* ...if c is not a digit... *)
        leading_nat (s1 ++ String c s2) =  (* ...leading_nat of s1++c++s2... *)
        leading_nat s1.                 (* ...equals leading_nat of s1. *)
  Proof.
    intros s1 s2 c Hc.                  (* Introduce hypotheses. *)
    destruct s1 as [|a s1'].            (* Case on s1. *)
    - simpl.                            (* s1 empty: leading_nat (String c s2). *)
      unfold is_digit in Hc.            (* Expand is_digit. *)
      destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].  (* Destruct c. *)
      destruct b0, b1, b2, b3, b4, b5, b6, b7;  (* All 256 cases. *)
        try discriminate Hc;            (* Digits have is_digit = true. *)
        reflexivity.                    (* Non-digits: char_to_digit = None. *)
    - simpl.                            (* s1 = String a s1'. *)
      destruct (char_to_digit a).       (* Case on first char of s1. *)
      + f_equal.                        (* Both are Some _. *)
        apply leading_nat_aux_app_non_digit.  (* Use aux lemma. *)
        exact Hc.                       (* c is not a digit. *)
      + reflexivity.                    (* First char not digit: both None. *)
  Qed.

  (** ===================================================================== *)
  (** PART VIII: VERSE GENERATION                                           *)
  (** ===================================================================== *)
  (** Now we can generate the actual song lyrics. Each verse follows a      *)
  (** pattern based on the bottle count, with special handling for 0 and 1. *)
  (** ===================================================================== *)

  (* bottle_word: Returns "bottle" or "bottles" based on count. *)
  (* English grammar: 1 bottle, 2 bottles, 0 bottles. *)
  Definition bottle_word (n : nat)      (* Takes the bottle count. *)
    : string                            (* Returns the appropriate word. *)
    := match n with                     (* Pattern match on n. *)
       | 1 => "bottle"                  (* Singular for exactly 1. *)
       | _ => "bottles"                 (* Plural for 0, 2, 3, ... *)
       end.

  (* count_phrase: Generates "N bottle(s)" or "No more bottles". *)
  Definition count_phrase (n : nat)     (* Takes the bottle count. *)
    : string                            (* Returns the count phrase. *)
    := match n with                     (* Pattern match on n. *)
       | 0 => "No more bottles"         (* Zero gets special text. *)
       | _ => nat_to_string n ++ " " ++ bottle_word n  (* N + space + bottle(s). *)
       end.

  (* verse: Generates a complete verse of the song. *)
  (* Takes starting count (for the final verse) and current count. *)
  Definition verse (start n : nat)      (* start = original count, n = current. *)
    : string                            (* Returns the verse text. *)
    := match n with                     (* Pattern match on current count. *)
       | 0 =>                           (* Zero bottles: final verse. *)
           "No more bottles of beer on the wall, no more bottles of beer. " ++
           "Go to the store and buy some more, " ++
           nat_to_string start ++ " bottles of beer on the wall."
       | S k =>                         (* n > 0: standard verse. *)
           count_phrase n ++ " of beer on the wall, " ++
           count_phrase n ++ " of beer. " ++
           "Take one down and pass it around, " ++
           count_phrase k ++ " of beer on the wall."
       end.

  (* current_verse: Gets the verse for the current state. *)
  (* Convenience wrapper using state's starting_count and on_wall. *)
  Definition current_verse (s : State)  (* Takes a state. *)
    : string                            (* Returns the appropriate verse. *)
    := verse (starting_count s) (on_wall s).  (* Use state's counts. *)

  (* full_song_aux: Builds the complete song as a list of verses. *)
  (* Recursively generates verses from n down to 0. *)
  Fixpoint full_song_aux (start n : nat)  (* start = original, n = current count. *)
                         (acc : list string)  (* Accumulated verses so far. *)
    : list string                       (* Returns complete list of verses. *)
    := match n with                     (* Pattern match on current count. *)
       | 0 => acc ++ [verse start 0]    (* Zero: append final verse. *)
       | S k => full_song_aux start k (acc ++ [verse start (S k)])
         (* n > 0: append verse n, then recurse for verses k..0. *)
       end.

  (* full_song: Generates the complete song starting from n bottles. *)
  Definition full_song (start : nat)    (* Takes starting bottle count. *)
    : list string                       (* Returns list of all verses. *)
    := full_song_aux start start [].    (* Start with n, empty accumulator. *)

  (* verse_one_singular: Verse for 1 bottle uses singular "bottle". *)
  Theorem verse_one_singular
    : forall start,                     (* For any starting count... *)
      verse start 1 =                   (* ...verse 1 is... *)
        "1 bottle of beer on the wall, 1 bottle of beer. " ++
        "Take one down and pass it around, No more bottles of beer on the wall.".
  Proof.
    intro.                              (* Introduce start (unused). *)
    reflexivity.                        (* Definitional equality. *)
  Qed.

  (* verse_two_plural: Verse for 2 bottles uses plural "bottles". *)
  Theorem verse_two_plural
    : forall start,                     (* For any starting count... *)
      verse start 2 =                   (* ...verse 2 is... *)
        "2 bottles of beer on the wall, 2 bottles of beer. " ++
        "Take one down and pass it around, 1 bottle of beer on the wall.".
  Proof.
    intro.                              (* Introduce start. *)
    reflexivity.                        (* Definitional equality. *)
  Qed.

  (* verse_99: The opening verse of the classic song. *)
  Theorem verse_99
    : verse 99 99 =                     (* Verse 99 of 99-bottle song is... *)
        "99 bottles of beer on the wall, 99 bottles of beer. " ++
        "Take one down and pass it around, 98 bottles of beer on the wall.".
  Proof.
    reflexivity.                        (* Coq computes this. *)
  Qed.

  (* verse_0_uses_start: Final verse references the starting count. *)
  Theorem verse_0_uses_start
    : forall start,                     (* For any starting count... *)
      verse start 0 =                   (* ...verse 0 mentions going to store... *)
        "No more bottles of beer on the wall, no more bottles of beer. " ++
        "Go to the store and buy some more, " ++
        nat_to_string start ++ " bottles of beer on the wall.".
  Proof.
    intro.                              (* Introduce start. *)
    reflexivity.                        (* Definitional equality. *)
  Qed.

  (* verse_50_0: Example: starting with 50, verse 0 says "50 bottles". *)
  Theorem verse_50_0
    : verse 50 0 =                      (* Verse 0 of 50-bottle song... *)
        "No more bottles of beer on the wall, no more bottles of beer. " ++
        "Go to the store and buy some more, 50 bottles of beer on the wall.".
  Proof.
    reflexivity.                        (* Coq computes this. *)
  Qed.

  (* full_song_length: The song has exactly n+1 verses (n down to 0). *)
  Theorem full_song_length
    : forall n,                         (* For any starting count n... *)
      List.length (full_song n) = S n.  (* ...song has n+1 verses. *)
  Proof.
    intro n.                            (* Introduce n. *)
    unfold full_song.                   (* Expand definition. *)
    assert (H : forall start m acc,     (* Helper: aux adds m+1 verses to acc. *)
              List.length (full_song_aux start m acc) = List.length acc + S m).
    { intros start.                     (* Introduce start. *)
      induction m.                      (* Induction on m. *)
      - intro acc.                      (* Base: m = 0. *)
        simpl.                          (* full_song_aux _ 0 acc = acc ++ [verse _ 0]. *)
        rewrite app_length.             (* length (acc ++ [x]) = length acc + length [x]. *)
        simpl.                          (* length [x] = 1. *)
        lia.                            (* length acc + 1 = length acc + S 0. *)
      - intro acc.                      (* Inductive: m = S k. *)
        simpl.                          (* Expand full_song_aux. *)
        rewrite IHm.                    (* Apply induction hypothesis. *)
        rewrite app_length.             (* Length of append. *)
        simpl.                          (* Simplify. *)
        lia. }                          (* Arithmetic. *)
    rewrite H.                          (* Apply helper. *)
    simpl.                              (* length [] = 0. *)
    lia.                                (* 0 + S n = S n. *)
  Qed.

  (* ninety_nine_bottles_100_verses: The classic song has exactly 100 verses. *)
  Theorem ninety_nine_bottles_100_verses
    : List.length (full_song 99) = 100. (* 99-bottle song has 100 verses. *)
  Proof.
    apply full_song_length.             (* 99 + 1 = 100. *)
  Qed.

  (* full_song_nth: The k-th verse of the song corresponds to count (n-k). *)
  Theorem full_song_nth
    : forall k,                         (* For any index k... *)
      k <= 99 ->                        (* ...from 0 to 99... *)
      nth k (full_song 99) "" =         (* ...the k-th verse... *)
      verse 99 (99 - k).                (* ...is verse (99-k). *)
  Proof.
    intro k.                            (* Introduce k. *)
    do 100 (destruct k; [reflexivity|]).  (* Try k = 0..99; each computes correctly. *)
    lia.                                (* k > 99 contradicts hypothesis. *)
  Qed.

  (** ===================================================================== *)
  (** PART IX: VERSE STRUCTURE LEMMAS                                       *)
  (** ===================================================================== *)
  (** We prove structural properties of verses needed for the injectivity   *)
  (** theorem: different bottle counts produce different verses.            *)
  (** ===================================================================== *)

  (* digit_to_char_inj: digit_to_char is injective on valid digits. *)
  Lemma digit_to_char_inj
    : forall d1 d2,                     (* For any digits d1 and d2... *)
      d1 < 10 ->                        (* ...if d1 is valid... *)
      d2 < 10 ->                        (* ...and d2 is valid... *)
      digit_to_char d1 = digit_to_char d2 ->  (* ...and they map to same char... *)
      d1 = d2.                          (* ...then they're equal. *)
  Proof.
    intros d1 d2 H1 H2.                 (* Introduce hypotheses. *)
    do 10 (destruct d1;                 (* Try d1 = 0..9. *)
           [do 10 (destruct d2;         (* For each, try d2 = 0..9. *)
                   [reflexivity ||      (* Same digit: equal. *)
                    intro H; inversion H|]);  (* Different: discriminate. *)
            lia|]).                     (* d2 >= 10: contradiction. *)
    lia.                                (* d1 >= 10: contradiction. *)
  Qed.

  (* digit_to_string_inj: digit_to_string is injective on valid digits. *)
  Lemma digit_to_string_inj
    : forall d1 d2,                     (* For any digits d1 and d2... *)
      d1 < 10 ->                        (* ...if both valid... *)
      d2 < 10 ->
      digit_to_string d1 = digit_to_string d2 ->  (* ...and same string... *)
      d1 = d2.                          (* ...then equal. *)
  Proof.
    intros d1 d2 H1 H2 Heq.             (* Introduce hypotheses. *)
    unfold digit_to_string in Heq.      (* Expand definition. *)
    inversion Heq.                      (* String c "" = String c' "" implies c = c'. *)
    apply digit_to_char_inj.            (* Use character injectivity. *)
    - assumption.                       (* d1 < 10. *)
    - assumption.                       (* d2 < 10. *)
    - assumption.                       (* digit_to_char d1 = digit_to_char d2. *)
  Qed.

  (* single_digit: Predicate for numbers 0-9. *)
  Definition single_digit (n : nat)     (* Takes a number. *)
    : Prop                              (* Returns a proposition. *)
    := n < 10.                          (* True iff n is a single digit. *)

  (* double_digit: Predicate for numbers 10-99. *)
  Definition double_digit (n : nat)     (* Takes a number. *)
    : Prop                              (* Returns a proposition. *)
    := 10 <= n < 100.                   (* True iff n has two digits. *)

  (* single_digit_length: Single-digit numbers produce 1-character strings. *)
  Lemma single_digit_length
    : forall n,                         (* For any n... *)
      single_digit n ->                 (* ...if single digit... *)
      String.length (nat_to_string n) = 1.  (* ...string has length 1. *)
  Proof.
    intros n Hsd.                       (* Introduce n and hypothesis. *)
    unfold single_digit in Hsd.         (* Expand: n < 10. *)
    do 10 (destruct n; [reflexivity|]). (* Try n = 0..9; each has length 1. *)
    lia.                                (* n >= 10 contradicts Hsd. *)
  Qed.

  (* double_digit_length: Double-digit numbers produce 2-character strings. *)
  Lemma double_digit_length
    : forall n,                         (* For any n... *)
      double_digit n ->                 (* ...if double digit... *)
      String.length (nat_to_string n) = 2.  (* ...string has length 2. *)
  Proof.
    intros n [Hlo Hhi].                 (* Introduce n and bounds. *)
    do 10 (destruct n; [lia|]).         (* Skip n = 0..9 (too small). *)
    do 90 (destruct n; [reflexivity|]). (* Try n = 10..99; each has length 2. *)
    lia.                                (* n >= 100 contradicts Hhi. *)
  Qed.

  (* string_cons_inj: String constructor is injective. *)
  Lemma string_cons_inj
    : forall c1 c2 s1 s2,               (* For any chars and strings... *)
      String c1 s1 = String c2 s2 ->    (* ...if String c1 s1 = String c2 s2... *)
      c1 = c2 /\ s1 = s2.               (* ...then c1 = c2 and s1 = s2. *)
  Proof.
    intros c1 c2 s1 s2 H.               (* Introduce hypotheses. *)
    inversion H.                        (* Invert the equality. *)
    split.                              (* Prove both parts. *)
    - reflexivity.                      (* c1 = c2 from inversion. *)
    - reflexivity.                      (* s1 = s2 from inversion. *)
  Qed.

  (* digit_char_neq_N: Digit characters are not 'N'. *)
  (* Important for distinguishing "99..." from "No more...". *)
  Lemma digit_char_neq_N
    : forall d,                         (* For any d... *)
      d < 10 ->                         (* ...if valid digit... *)
      digit_to_char d <> "N"%char.      (* ...it's not 'N'. *)
  Proof.
    intros d Hd Heq.                    (* Introduce hypotheses. *)
    do 10 (destruct d; [discriminate Heq|]).  (* Try d = 0..9; none equal 'N'. *)
    lia.                                (* d >= 10 contradicts Hd. *)
  Qed.

  (* digit_to_char_is_digit: digit_to_char produces digit characters. *)
  (* Alias for is_digit_digit_to_char with clearer name. *)
  Lemma digit_to_char_is_digit
    : forall d,                         (* For any d... *)
      d < 10 ->                         (* ...if valid... *)
      is_digit (digit_to_char d) = true.  (* ...result is a digit char. *)
  Proof.
    intros d Hd.                        (* Introduce hypotheses. *)
    do 10 (destruct d; [reflexivity|]). (* Try d = 0..9. *)
    lia.                                (* d >= 10 contradicts Hd. *)
  Qed.

  (* is_digit_neq_N: Digit characters are not 'N'. *)
  Lemma is_digit_neq_N
    : forall c,                         (* For any character c... *)
      is_digit c = true ->              (* ...if c is a digit... *)
      c <> "N"%char.                    (* ...then c ≠ 'N'. *)
  Proof.
    intros c Hdig Heq.                  (* Introduce hypotheses. *)
    rewrite Heq in Hdig.                (* Substitute 'N' for c. *)
    discriminate Hdig.                  (* is_digit 'N' = false, contradiction. *)
  Qed.

  (* nat_to_string_starts_with_digit: Positive numbers start with a digit. *)
  Lemma nat_to_string_starts_with_digit
    : forall n,                         (* For any n... *)
      n > 0 ->                          (* ...if positive... *)
      n <= 99 ->                        (* ...and at most 99... *)
      exists c rest,                    (* ...there exist c and rest... *)
        nat_to_string n = String c rest /\  (* ...such that string is c::rest... *)
        is_digit c = true.              (* ...and c is a digit. *)
  Proof.
    intros n Hpos Hle.                  (* Introduce hypotheses. *)
    unfold nat_to_string.               (* Expand definition. *)
    destruct n.                         (* Case on n. *)
    - lia.                              (* n = 0 contradicts Hpos. *)
    - destruct (nat_to_string_aux_first_char_digit (S n) (S n))
        as [c [rest [Heq [d [Hd Hc]]]]].  (* Get first char info. *)
      + lia.                            (* S n > 0. *)
      + exists c, rest.                 (* Witness c and rest. *)
        rewrite Heq, Hc.                (* Substitute. *)
        split.
        * reflexivity.                  (* String equality. *)
        * apply digit_to_char_is_digit. (* c = digit_to_char d is a digit. *)
          exact Hd.                     (* d < 10. *)
  Qed.

  (* N_not_digit: 'N' is not a digit character. *)
  Lemma N_not_digit
    : is_digit "N"%char = false.        (* 'N' is not a digit. *)
  Proof.
    reflexivity.                        (* By computation. *)
  Qed.

  (* first_char_app: First char of concatenation is first char of first string. *)
  Lemma first_char_app
    : forall c s1 s2,                   (* For any char and strings... *)
      first_char (String c s1 ++ s2) = Some c.  (* ...first char is c. *)
  Proof.
    intros.                             (* Introduce all. *)
    reflexivity.                        (* By definition of ++ and first_char. *)
  Qed.

  (* first_char_eq: Equal strings have equal first characters. *)
  Lemma first_char_eq
    : forall s1 s2,                     (* For any strings... *)
      s1 = s2 ->                        (* ...if equal... *)
      first_char s1 = first_char s2.    (* ...first chars are equal. *)
  Proof.
    intros s1 s2 H.                     (* Introduce hypotheses. *)
    rewrite H.                          (* Substitute. *)
    reflexivity.                        (* first_char s2 = first_char s2. *)
  Qed.

  (* count_phrase_first_char_digit: For n > 0, count_phrase starts with digit. *)
  Lemma count_phrase_first_char_digit
    : forall n,                         (* For any n... *)
      n > 0 ->                          (* ...if positive... *)
      n <= 99 ->                        (* ...and at most 99... *)
      exists c,                         (* ...there exists c... *)
        first_char (count_phrase n) = Some c /\  (* ...first char is c... *)
        is_digit c = true.              (* ...and c is a digit. *)
  Proof.
    intros n Hpos Hle.                  (* Introduce hypotheses. *)
    unfold count_phrase.                (* Expand definition. *)
    destruct n.                         (* Case on n. *)
    - lia.                              (* n = 0 contradicts Hpos. *)
    - destruct (nat_to_string_starts_with_digit (S n) Hpos Hle)
        as [c [rest [Heq Hdig]]].       (* Get first char of nat_to_string. *)
      exists c.                         (* Witness c. *)
      rewrite Heq.                      (* Substitute string form. *)
      simpl.                            (* first_char (String c rest ++ ...) = Some c. *)
      split.
      + reflexivity.                    (* First char is c. *)
      + exact Hdig.                     (* c is a digit. *)
  Qed.

  (* verse_first_char_0: Verse 0 starts with 'N' (from "No more"). *)
  Lemma verse_first_char_0
    : forall start,                     (* For any starting count... *)
      first_char (verse start 0) = Some "N"%char.  (* ...verse 0 starts with 'N'. *)
  Proof.
    intro.                              (* Introduce start. *)
    reflexivity.                        (* By computation. *)
  Qed.

  (* verse_first_char_Sn: Verse (S n) for n <= 98 starts with a digit. *)
  Lemma verse_first_char_Sn
    : forall start n,                   (* For any start and n... *)
      n <= 98 ->                        (* ...if n <= 98... *)
      exists c,                         (* ...there exists c... *)
        first_char (verse start (S n)) = Some c /\  (* ...first char is c... *)
        is_digit c = true.              (* ...and c is a digit. *)
  Proof.
    intros start n Hle.                 (* Introduce hypotheses. *)
    assert (Hpos : S n > 0) by lia.     (* S n is positive. *)
    assert (Hle2 : S n <= 99) by lia.   (* S n <= 99. *)
    destruct (nat_to_string_starts_with_digit (S n) Hpos Hle2)
      as [c [rest [Heq Hdig]]].         (* Get first char info. *)
    exists c.                           (* Witness c. *)
    unfold verse, count_phrase.         (* Expand definitions. *)
    rewrite Heq.                        (* Substitute string form. *)
    simpl.                              (* Simplify first_char. *)
    split.
    - reflexivity.                      (* First char is c. *)
    - exact Hdig.                       (* c is a digit. *)
  Qed.

  (* verse_0_ne_Sn: Verse 0 is different from verse (S n) for n <= 98. *)
  (* Key lemma: "No more..." ≠ "N bottles..." because first chars differ. *)
  Lemma verse_0_ne_Sn
    : forall start n,                   (* For any start and n... *)
      n <= 98 ->                        (* ...if n <= 98... *)
      verse start 0 <> verse start (S n).  (* ...verse 0 ≠ verse (S n). *)
  Proof.
    intros start n Hle H.               (* Introduce hypotheses; H is equality. *)
    pose proof (verse_first_char_0 start) as H0.  (* Verse 0 starts with 'N'. *)
    pose proof (verse_first_char_Sn start n Hle) as [c [HSn Hdig]].  (* Verse Sn starts with digit. *)
    apply first_char_eq in H.           (* Equal verses have equal first chars. *)
    rewrite H0, HSn in H.               (* Substitute first chars. *)
    inversion H as [Hc].                (* Some 'N' = Some c implies 'N' = c. *)
    rewrite <- Hc in Hdig.              (* Substitute in is_digit. *)
    simpl in Hdig.                      (* is_digit 'N' = false. *)
    discriminate Hdig.                  (* false = true is contradiction. *)
  Qed.

  (* string_neq_first_char: Strings with different first chars are different. *)
  Lemma string_neq_first_char
    : forall c1 c2 s1 s2,               (* For any chars and strings... *)
      c1 <> c2 ->                       (* ...if chars differ... *)
      String c1 s1 <> String c2 s2.     (* ...strings differ. *)
  Proof.
    intros c1 c2 s1 s2 Hneq Heq.        (* Introduce hypotheses. *)
    injection Heq as Hc _.              (* Extract c1 = c2 from string equality. *)
    exact (Hneq Hc).                    (* Contradicts Hneq. *)
  Qed.

  (* verse_leading_nat: The leading number in verse n is n (for 0 < n <= 99). *)
  Lemma verse_leading_nat
    : forall start n,                   (* For any start and n... *)
      n > 0 ->                          (* ...if positive... *)
      n <= 99 ->                        (* ...and at most 99... *)
      leading_nat (verse start n) = Some n.  (* ...leading_nat extracts n. *)
  Proof.
    intros start n Hpos Hle.            (* Introduce hypotheses. *)
    destruct n.                         (* Case on n. *)
    - lia.                              (* n = 0 contradicts Hpos. *)
    - do 99 (destruct n as [|n]; [reflexivity|]).  (* Try n = 0..98; each computes. *)
      lia.                              (* n >= 99 contradicts Hle. *)
  Qed.

  (** ===================================================================== *)
  (** PART X: VERSE INJECTIVITY                                             *)
  (** ===================================================================== *)
  (** The key theorem: different bottle counts produce different verses.    *)
  (** This means each verse uniquely identifies its position in the song.   *)
  (** ===================================================================== *)

  (* verse_inj: Different bottle counts produce different verses. *)
  (* The main injectivity theorem for verse generation. *)
  Theorem verse_inj
    : forall start n1 n2,               (* For any start and counts n1, n2... *)
      n1 <= 99 ->                       (* ...if n1 is in range... *)
      n2 <= 99 ->                       (* ...and n2 is in range... *)
      verse start n1 = verse start n2 ->  (* ...and verses are equal... *)
      n1 = n2.                          (* ...then counts are equal. *)
  Proof.
    intros start n1 n2 H1 H2 Heq.       (* Introduce hypotheses. *)
    destruct n1 as [|n1'], n2 as [|n2'].  (* Case split on both counts. *)
    - reflexivity.                      (* Both 0: trivially equal. *)
    - exfalso.                          (* 0 vs S n2': impossible. *)
      apply (verse_0_ne_Sn start n2').  (* Use verse_0_ne_Sn. *)
      + lia.                            (* n2' <= 98 since S n2' <= 99. *)
      + exact Heq.                      (* Heq says they're equal. *)
    - exfalso.                          (* S n1' vs 0: impossible. *)
      apply (verse_0_ne_Sn start n1').  (* Use verse_0_ne_Sn. *)
      + lia.                            (* n1' <= 98 since S n1' <= 99. *)
      + symmetry.                       (* Flip equality direction. *)
        exact Heq.                      (* Heq says they're equal. *)
    - assert (Hln1 : leading_nat (verse start (S n1')) = Some (S n1')).
      (* Extract leading nat from verse (S n1'). *)
      { apply verse_leading_nat.        (* Use verse_leading_nat lemma. *)
        - lia.                          (* S n1' > 0. *)
        - lia. }                        (* S n1' <= 99. *)
      assert (Hln2 : leading_nat (verse start (S n2')) = Some (S n2')).
      (* Extract leading nat from verse (S n2'). *)
      { apply verse_leading_nat.        (* Use verse_leading_nat lemma. *)
        - lia.                          (* S n2' > 0. *)
        - lia. }                        (* S n2' <= 99. *)
      rewrite Heq in Hln1.              (* Substitute equal verses. *)
      rewrite Hln1 in Hln2.             (* Now Some (S n1') = Some (S n2'). *)
      injection Hln2 as Hln2.           (* Extract n1' = n2'. *)
      f_equal.                          (* Reduce S n1' = S n2' to n1' = n2'. *)
      exact Hln2.                       (* The conclusion. *)
  Qed.

  (* NoDup_app_iff: List.NoDup of concatenation iff both List.NoDup and disjoint. *)
  (* We prove this helper since it's not in the standard library. *)
  Lemma NoDup_app_iff
    : forall (A : Type) (l1 l2 : list A),
      List.NoDup (l1 ++ l2) <->
      List.NoDup l1 /\ List.NoDup l2 /\ (forall x, In x l1 -> ~In x l2).
  Proof.
    intros A l1 l2.                     (* Introduce type and lists. *)
    split.                              (* Prove both directions. *)
    - intro H.                          (* Forward direction. *)
      repeat split.                     (* Split into three parts. *)
      + now apply List.NoDup_app_remove_r in H.  (* List.NoDup l1. *)
      + now apply List.NoDup_app_remove_l in H.  (* List.NoDup l2. *)
      + intros x Hx1 Hx2.               (* Disjointness. *)
        induction l1 as [|a l1' IH].    (* Induction on l1. *)
        * inversion Hx1.                (* x not in []. *)
        * simpl in H.                   (* Expand List.NoDup (a :: l1' ++ l2). *)
          inversion H as [|? ? Hnin Hnd']; subst.  (* Destruct. *)
          destruct Hx1 as [Hxa|Hx1'].   (* x = a or x in l1'. *)
          -- subst.                     (* x = a. *)
             apply Hnin.                (* a not in l1' ++ l2. *)
             apply in_or_app.           (* In a (l1' ++ l2). *)
             right; exact Hx2.          (* a in l2. *)
          -- apply IH.                  (* x in l1': use IH. *)
             ++ exact Hnd'.             (* List.NoDup (l1' ++ l2). *)
             ++ exact Hx1'.             (* x in l1'. *)
    - intros [Hnd1 [Hnd2 Hdisj]].       (* Backward direction. *)
      induction l1 as [|a l1' IH].      (* Induction on l1. *)
      + exact Hnd2.                     (* [] ++ l2 = l2. *)
      + simpl.                          (* a :: l1' ++ l2. *)
        constructor.                    (* Prove List.NoDup (a :: ...). *)
        * intro Ha.                     (* Assume a in l1' ++ l2. *)
          apply in_app_or in Ha.        (* Either in l1' or l2. *)
          destruct Ha as [Ha|Ha].       (* Case split. *)
          -- inversion Hnd1; subst.     (* a not in l1' by Hnd1. *)
             contradiction.
          -- apply (Hdisj a).           (* a in l1 but also in l2: contradiction. *)
             ++ left; reflexivity.      (* a in a::l1'. *)
             ++ exact Ha.               (* a in l2. *)
        * apply IH.                     (* List.NoDup (l1' ++ l2). *)
          -- now inversion Hnd1.        (* List.NoDup l1'. *)
          -- intros x Hx.               (* Disjointness for l1'. *)
             apply Hdisj.               (* Use original disjointness. *)
             right; exact Hx.           (* x in l1' implies x in a::l1'. *)
  Qed.

  (* full_song_aux_NoDup: Helper lemma for proving song has no duplicates. *)
  Lemma full_song_aux_NoDup
    : forall start m acc,               (* For any start, count m, and accumulator... *)
      m <= start ->                     (* ...if m <= start... *)
      start <= 99 ->                    (* ...and start <= 99... *)
      List.NoDup acc ->                      (* ...and acc has no duplicates... *)
      (forall v, In v acc ->            (* ...and every verse in acc... *)
         exists k, k > m /\ k <= start /\ v = verse start k) ->  (* ...is for some k > m... *)
      List.NoDup (full_song_aux start m acc).  (* ...then result has no duplicates. *)
  Proof.
    intros start.                       (* Introduce start. *)
    induction m.                        (* Induction on m. *)
    - intros acc Hm Hs Hnd Hacc.        (* Base: m = 0. *)
      simpl.                            (* full_song_aux _ 0 acc = acc ++ [verse _ 0]. *)
      apply NoDup_app_iff.              (* List.NoDup of append requires three conditions. *)
      repeat split.                     (* Split into parts. *)
      + exact Hnd.                      (* acc has no duplicates. *)
      + constructor.                    (* [verse _ 0] has no duplicates. *)
        * intro H; inversion H.         (* verse _ 0 not in []. *)
        * constructor.                  (* [] has no duplicates. *)
      + intros v Hv1 Hv2.               (* If v is in both acc and [verse _ 0]... *)
        destruct Hv2 as [Hv2|Hv2].      (* v is in [verse _ 0] means v = verse _ 0. *)
        * destruct (Hacc v Hv1) as [k [Hk1 [Hk2 Hk3]]].  (* v = verse _ k for some k > 0. *)
          rewrite Hk3 in Hv2.           (* verse _ k = verse _ 0. *)
          assert (Hkinj : k = 0).       (* By injectivity, k = 0. *)
          { apply (verse_inj start).
            - lia.                      (* k <= 99 since k <= start <= 99. *)
            - lia.                      (* 0 <= 99. *)
            - symmetry; exact Hv2. }    (* verse _ k = verse _ 0. *)
          lia.                          (* But k > 0, contradiction. *)
        * inversion Hv2.                (* Hv2 : In v [] is impossible. *)
    - intros acc Hm Hs Hnd Hacc.        (* Inductive: for S m. *)
      simpl.                            (* Expand full_song_aux. *)
      apply IHm.                        (* Apply induction hypothesis. *)
      + lia.                            (* m <= start. *)
      + lia.                            (* start <= 99. *)
      + apply NoDup_app_iff.            (* acc ++ [verse _ (S m)] has no duplicates. *)
        repeat split.                   (* Split into parts. *)
        * exact Hnd.                    (* acc has no duplicates. *)
        * constructor.                  (* Singleton list has no duplicates. *)
          -- intro H; inversion H.
          -- constructor.
        * intros v Hv1 Hv2.             (* If v in both... *)
          destruct Hv2 as [Hv2|Hv2].
          -- destruct (Hacc v Hv1) as [k [Hk1 [Hk2 Hk3]]].
             rewrite Hk3 in Hv2.        (* verse _ k = verse _ (S m). *)
             assert (Hkinj : k = S m).  (* By injectivity. *)
             { apply (verse_inj start).
               - lia.
               - lia.
               - symmetry; exact Hv2. }
             lia.                       (* But k > S m, contradiction. *)
          -- inversion Hv2.
      + intros v Hv.                    (* For v in acc ++ [verse _ (S m)]... *)
        apply in_app_or in Hv.          (* Either in acc or in singleton. *)
        destruct Hv as [Hv|Hv].
        * destruct (Hacc v Hv) as [k [Hk1 [Hk2 Hk3]]].  (* v = verse _ k for k > S m. *)
          exists k.                     (* Same witness works. *)
          split; [lia|].                (* k > m since k > S m. *)
          split; [lia|].                (* k <= start. *)
          exact Hk3.                    (* v = verse _ k. *)
        * destruct Hv as [Hv|Hv].       (* v in [verse _ (S m)] means v = verse _ (S m). *)
          -- exists (S m).              (* Witness is S m. *)
             split; [lia|].             (* S m > m. *)
             split; [lia|].             (* S m <= start. *)
             symmetry; exact Hv.        (* v = verse _ (S m). *)
          -- inversion Hv.              (* [] has no elements. *)
  Qed.

  (* full_song_all_distinct: All verses in the complete song are distinct. *)
  Theorem full_song_all_distinct
    : forall n,                         (* For any starting count n... *)
      n <= 99 ->                        (* ...up to 99... *)
      List.NoDup (full_song n).              (* ...the song has no duplicate verses. *)
  Proof.
    intros n Hn.                        (* Introduce n and bound. *)
    unfold full_song.                   (* Expand definition. *)
    apply full_song_aux_NoDup.          (* Use the helper lemma. *)
    - lia.                              (* n <= n. *)
    - exact Hn.                         (* n <= 99. *)
    - constructor.                      (* [] has no duplicates. *)
    - intros v Hv.                      (* No v is in []. *)
      inversion Hv.                     (* Contradiction. *)
  Qed.

  (** ===================================================================== *)
  (** PART XI: BISIMULATION AND TRAJECTORY-SONG CORRESPONDENCE              *)
  (** ===================================================================== *)
  (** We prove bisimulation-style theorems: the state machine execution     *)
  (** corresponds exactly to counting down bottles, and each step through   *)
  (** the state machine produces the verse at the corresponding position    *)
  (** in the song.                                                          *)
  (** ===================================================================== *)

  (* run_on_wall_aux: Helper relating run to on_wall decrease. *)
  (* The key insight: on_wall only depends on initial on_wall and steps taken. *)
  Lemma run_on_wall_aux
    : forall k w p st,                  (* For any fuel and state components... *)
      on_wall (run k {| on_wall := w; passed_around := p; starting_count := st |}) =
      w - Nat.min k w.                  (* ...on_wall decreases by min(k, w). *)
  Proof.
    induction k as [|k' IHk'].          (* Induction on fuel k. *)
    - intros w p st.                    (* Base case: k = 0. *)
      simpl.                            (* run 0 s = s. *)
      lia.                              (* w - min(0, w) = w - 0 = w. *)
    - intros w p st.                    (* Inductive case: k = S k'. *)
      destruct w as [|w'].              (* Case split on bottles. *)
      + simpl.                          (* w = 0: step is identity. *)
        specialize (IHk' 0 p st).       (* IH for 0 bottles. *)
        exact IHk'.                     (* Goal matches IH exactly. *)
      + change (on_wall (run k' (step {| on_wall := S w'; passed_around := p;
                                            starting_count := st |})) =
                S w' - Nat.min (S k') (S w')).  (* Restate goal explicitly. *)
        unfold step.                    (* Expand step definition. *)
        simpl on_wall.                  (* Simplify on_wall accessor. *)
        rewrite (IHk' w' (S p) st).     (* Substitute IH result. *)
        simpl.                          (* Simplify min. *)
        lia.                            (* Arithmetic completes proof. *)
  Qed.

  (* bisimulation: Characterizes the state after k steps. *)
  (* After k steps from initial n: on_wall = n - min(k, n). *)
  Theorem bisimulation
    : forall n k,                       (* For any starting count n and steps k... *)
      on_wall (run k (initial n)) =     (* ...bottles on wall after k steps... *)
      n - Nat.min k n.                  (* ...equals n minus min(k, n). *)
  Proof.
    intros n k.                         (* Introduce n and k. *)
    unfold initial.                     (* Expand initial to record literal. *)
    apply run_on_wall_aux.              (* Apply the helper lemma. *)
  Qed.

  (** ----- Trajectory-Song Correspondence ----- *)

  (* state_verse_consistent: A state has valid bounds for verse generation. *)
  Definition state_verse_consistent (s : State)  (* Takes a state. *)
    : Prop                              (* Returns a proposition. *)
    := on_wall s <= starting_count s /\  (* Bottles on wall <= starting count... *)
       starting_count s <= 99.          (* ...and starting count <= 99. *)

  (* initial_verse_consistent: Initial states are verse-consistent. *)
  Lemma initial_verse_consistent
    : forall n,                         (* For any n... *)
      n <= 99 ->                        (* ...if n <= 99... *)
      state_verse_consistent (initial n).  (* ...initial n is verse-consistent. *)
  Proof.
    intros n Hn.                        (* Introduce n and bound. *)
    unfold state_verse_consistent, initial.  (* Expand definitions. *)
    simpl.                              (* Simplify projections. *)
    lia.                                (* n <= n and n <= 99. *)
  Qed.

  (* step_verse_consistent: Step preserves verse-consistency. *)
  Lemma step_verse_consistent
    : forall s,                         (* For any state s... *)
      state_verse_consistent s ->       (* ...if s is verse-consistent... *)
      state_verse_consistent (step s).  (* ...so is step s. *)
  Proof.
    intros [w p st] [Hw Hst].           (* Destruct s and hypothesis. *)
    unfold state_verse_consistent, step.  (* Expand definitions. *)
    simpl in *.                         (* Simplify. *)
    destruct w.                         (* Case on w. *)
    - simpl.                            (* w = 0: step doesn't change state. *)
      lia.                              (* Same bounds hold. *)
    - simpl.                            (* w = S k: on_wall decreases. *)
      lia.                              (* k <= st since S k <= st. *)
  Qed.

  (* run_verse_consistent: Run preserves verse-consistency. *)
  Lemma run_verse_consistent
    : forall fuel s,                    (* For any fuel and state s... *)
      state_verse_consistent s ->       (* ...if s is verse-consistent... *)
      state_verse_consistent (run fuel s).  (* ...so is run fuel s. *)
  Proof.
    induction fuel.                     (* Induction on fuel. *)
    - intro s.                          (* Base: fuel = 0. *)
      exact (fun H => H).               (* run 0 s = s; same state. *)
    - intros s Hvc.                     (* Inductive: fuel = S k. *)
      simpl.                            (* run (S k) s = run k (step s). *)
      apply IHfuel.                     (* Apply IH. *)
      apply step_verse_consistent.      (* step preserves consistency. *)
      exact Hvc.                        (* s is consistent. *)
  Qed.

  (* trajectory_verses_match: State machine trajectory matches song verses. *)
  (* The k-th state in the trajectory produces the k-th verse of the song. *)
  Theorem trajectory_verses_match
    : forall n k,                       (* For any starting count n and index k... *)
      n <= 99 ->                        (* ...if n <= 99... *)
      k <= n ->                         (* ...and k <= n... *)
      current_verse (run k (initial n)) =  (* ...the verse for state after k steps... *)
      verse n (n - k).                  (* ...equals verse (n-k). *)
  Proof.
    intros n k Hn Hk.                   (* Introduce hypotheses. *)
    unfold current_verse.               (* Expand: verse (starting_count _) (on_wall _). *)
    rewrite run_preserves_starting_count.  (* starting_count (run k _) = starting_count _. *)
    rewrite bisimulation.               (* Use bisimulation: on_wall (run k (initial n)) = n - min k n. *)
    unfold initial; simpl.              (* Expand initial and simplify. *)
    replace (n - Nat.min k n) with (n - k) by lia.  (* min k n = k when k <= n. *)
    reflexivity.                        (* verse n (n - k) = verse n (n - k). *)
  Qed.

  (* trajectory_full_song_correspondence: Complete correspondence theorem. *)
  (* For the 99-bottle song, the k-th trajectory state produces the k-th song verse. *)
  Theorem trajectory_full_song_correspondence
    : forall k,                         (* For any index k... *)
      k <= 99 ->                        (* ...from 0 to 99... *)
      current_verse (run k (initial 99)) =  (* ...the verse from state machine... *)
      nth k (full_song 99) "".          (* ...equals the k-th verse in the song list. *)
  Proof.
    intros k Hk.                        (* Introduce k and bound. *)
    rewrite trajectory_verses_match.    (* Use trajectory-verse correspondence. *)
    - rewrite full_song_nth.            (* Use full_song indexing theorem. *)
      + reflexivity.                    (* verse 99 (99 - k) = verse 99 (99 - k). *)
      + exact Hk.                       (* k <= 99. *)
    - lia.                              (* 99 <= 99. *)
    - exact Hk.                         (* k <= 99. *)
  Qed.

  (* final_verse_is_terminal: The verse at step n is the terminal verse. *)
  Theorem final_verse_is_terminal
    : forall n,                         (* For any starting count n... *)
      n <= 99 ->                        (* ...up to 99... *)
      current_verse (run n (initial n)) =  (* ...the verse after n steps... *)
      verse n 0.                        (* ...is the final verse (verse 0). *)
  Proof.
    intros n Hn.                        (* Introduce n and bound. *)
    rewrite trajectory_verses_match.    (* Use trajectory-verse correspondence. *)
    - f_equal.                          (* Just need n - n = 0. *)
      lia.                              (* Arithmetic. *)
    - exact Hn.                         (* n <= 99. *)
    - lia.                              (* n <= n. *)
  Qed.

  (* song_complete: The state machine visits every verse in order. *)
  (* Combining termination, correspondence, and verse count. *)
  Theorem song_complete
    : forall n,                         (* For any starting count n... *)
      n <= 99 ->                        (* ...up to 99... *)
      (forall k, k <= n ->              (* ...for every k from 0 to n... *)
        current_verse (run k (initial n)) =  (* ...the k-th state's verse... *)
        nth k (full_song n) "") /\      (* ...matches the k-th song entry... *)
      terminal (run n (initial n)).     (* ...and n steps reaches terminal. *)
  Proof.
    intros n Hn.                        (* Introduce n and bound. *)
    split.                              (* Prove both parts. *)
    - intros k Hk.                      (* First part: correspondence. *)
      rewrite trajectory_verses_match by lia.  (* State verse = verse n (n-k). *)
      symmetry.                         (* Flip equality. *)
      do 100 (destruct n; [do 101 (destruct k; [reflexivity | try lia])|]).
      lia.                              (* n >= 100 contradicts Hn. *)
    - pose proof (sufficient_fuel_reaches_terminal (initial n)) as H.
      unfold initial in H; simpl in H.  (* Simplify: on_wall (initial n) = n. *)
      exact H.                          (* terminal (run n (initial n)). *)
  Qed.

  (** ===================================================================== *)
  (** PART XII: PARAMETRICITY                                               *)
  (** ===================================================================== *)
  (** Some theorems hold for ANY starting count n, while others require     *)
  (** n ≤ 99 for string parsing reasons. We make this distinction explicit. *)
  (** ===================================================================== *)

  (** ----- Theorems that hold for ANY n ----- *)

  (* general_termination: The song terminates for ANY starting count. *)
  (* No bound on n required—the state machine always reaches terminal. *)
  Theorem general_termination
    : forall n,                         (* For ANY natural number n... *)
      terminal (run n (initial n)).     (* ...n steps from initial n is terminal. *)
  Proof.
    intro n.                            (* Introduce n (no bound needed). *)
    pose proof (sufficient_fuel_reaches_terminal (initial n)) as H.  (* Get termination. *)
    unfold initial in H.                (* Expand initial. *)
    simpl in H.                         (* on_wall {| on_wall := n; ... |} = n. *)
    exact H.                            (* Exactly what we need. *)
  Qed.

  (* general_conservation: Conservation holds for ANY starting count. *)
  (* Bottles are conserved regardless of how many we start with. *)
  Theorem general_conservation
    : forall n s,                       (* For ANY n and state s... *)
      Reachable (initial n) s ->        (* ...if s is reachable from initial n... *)
      on_wall s + passed_around s = n.  (* ...then bottles are conserved. *)
  Proof.
    intros n s Hreach.                  (* Introduce n, s, and reachability. *)
    apply conservation_law.             (* Use the general conservation law. *)
    exact Hreach.                       (* Provide the reachability proof. *)
  Qed.

  (* general_invariant: The invariant holds for ANY starting count. *)
  (* This is the most fundamental property—no bounds needed. *)
  Theorem general_invariant
    : forall n fuel,                    (* For ANY n and fuel... *)
      invariant (run fuel (initial n)). (* ...the invariant holds after running. *)
  Proof.
    intros n fuel.                      (* Introduce n and fuel. *)
    apply run_preserves_invariant.      (* Use invariant preservation. *)
    apply initial_satisfies_invariant.  (* Initial state satisfies invariant. *)
  Qed.

  (* general_all_bottles_passed: All bottles get passed for ANY n. *)
  (* At termination, passed_around equals the starting count. *)
  Theorem general_all_bottles_passed
    : forall n,                         (* For ANY natural number n... *)
      passed_around (run n (initial n)) = n.  (* ...all n bottles get passed. *)
  Proof.
    intro n.                            (* Introduce n. *)
    apply all_bottles_passed_at_end.    (* Use the general theorem. *)
  Qed.

  (** ----- Theorems requiring n ≤ 99 ----- *)

  (* The following theorems require n ≤ 99 because they depend on:         *)
  (* 1. String parsing: nat_to_string_to_nat uses computation bounded by n *)
  (* 2. Verse injectivity: proved by brute-force case analysis up to 99    *)
  (* 3. leading_nat extraction: requires digits to fit in computable range *)
  (*                                                                       *)
  (* These theorems ARE provable for larger n, but would require:          *)
  (* - More sophisticated string parsing proofs                            *)
  (* - General injectivity arguments instead of case analysis              *)
  (* For pedagogical clarity, we stick to the classic 99-bottle bound.     *)

  (* bounded_verse_injectivity: Different counts give different verses. *)
  (* Requires n ≤ 99 for the leading_nat extraction to compute. *)
  Theorem bounded_verse_injectivity
    : forall start n1 n2,               (* For any start and counts... *)
      n1 <= 99 ->                       (* ...if n1 is bounded... *)
      n2 <= 99 ->                       (* ...and n2 is bounded... *)
      verse start n1 = verse start n2 ->  (* ...and verses are equal... *)
      n1 = n2.                          (* ...then counts are equal. *)
  Proof.
    exact verse_inj.                    (* This is just verse_inj. *)
  Qed.

  (* bounded_song_NoDup: The song has no duplicate verses. *)
  (* Requires n ≤ 99 because it depends on verse injectivity. *)
  Theorem bounded_song_NoDup
    : forall n,                         (* For any n... *)
      n <= 99 ->                        (* ...if bounded... *)
      List.NoDup (full_song n).         (* ...the song has no duplicates. *)
  Proof.
    exact full_song_all_distinct.       (* This is just full_song_all_distinct. *)
  Qed.

  (** ===================================================================== *)
  (** PART XIII: THE SONG ITSELF                                            *)
  (** ===================================================================== *)
  (** Finally, we prove that our verified machinery produces the actual     *)
  (** song. Each theorem below is a certificate that a specific verse       *)
  (** computes to exactly the text we expect. Coq verifies each by          *)
  (** computation—no trust required.                                        *)
  (** ===================================================================== *)

  (* the_song_verse_99: The first verse of the song. *)
  Theorem the_song_verse_99
    : nth 0 (full_song 99) "" =         (* The 0th entry of the 99-bottle song... *)
      "99 bottles of beer on the wall, 99 bottles of beer. " ++
      "Take one down and pass it around, 98 bottles of beer on the wall.".
  Proof. reflexivity. Qed.              (* Verified by computation. *)

  (* the_song_verse_98: The second verse. *)
  Theorem the_song_verse_98
    : nth 1 (full_song 99) "" =         (* The 1st entry (verse for 98 bottles)... *)
      "98 bottles of beer on the wall, 98 bottles of beer. " ++
      "Take one down and pass it around, 97 bottles of beer on the wall.".
  Proof. reflexivity. Qed.              (* Verified by computation. *)

  (* the_song_verse_97: The third verse. *)
  Theorem the_song_verse_97
    : nth 2 (full_song 99) "" =         (* The 2nd entry (verse for 97 bottles)... *)
      "97 bottles of beer on the wall, 97 bottles of beer. " ++
      "Take one down and pass it around, 96 bottles of beer on the wall.".
  Proof. reflexivity. Qed.              (* Verified by computation. *)

  (* the_song_verse_50: The middle of the song. *)
  Theorem the_song_verse_50
    : nth 49 (full_song 99) "" =        (* The 49th entry (verse for 50 bottles)... *)
      "50 bottles of beer on the wall, 50 bottles of beer. " ++
      "Take one down and pass it around, 49 bottles of beer on the wall.".
  Proof. reflexivity. Qed.              (* Verified by computation. *)

  (* the_song_verse_10: Getting close to the end. *)
  Theorem the_song_verse_10
    : nth 89 (full_song 99) "" =        (* The 89th entry (verse for 10 bottles)... *)
      "10 bottles of beer on the wall, 10 bottles of beer. " ++
      "Take one down and pass it around, 9 bottles of beer on the wall.".
  Proof. reflexivity. Qed.              (* Verified by computation. *)

  (* the_song_verse_3: Three bottles remain. *)
  Theorem the_song_verse_3
    : nth 96 (full_song 99) "" =        (* The 96th entry (verse for 3 bottles)... *)
      "3 bottles of beer on the wall, 3 bottles of beer. " ++
      "Take one down and pass it around, 2 bottles of beer on the wall.".
  Proof. reflexivity. Qed.              (* Verified by computation. *)

  (* the_song_verse_2: Two bottles remain—last plural verse. *)
  Theorem the_song_verse_2
    : nth 97 (full_song 99) "" =        (* The 97th entry (verse for 2 bottles)... *)
      "2 bottles of beer on the wall, 2 bottles of beer. " ++
      "Take one down and pass it around, 1 bottle of beer on the wall.".
  Proof. reflexivity. Qed.              (* Verified by computation. *)

  (* the_song_verse_1: One bottle remains—the singular verse. *)
  Theorem the_song_verse_1
    : nth 98 (full_song 99) "" =        (* The 98th entry (verse for 1 bottle)... *)
      "1 bottle of beer on the wall, 1 bottle of beer. " ++
      "Take one down and pass it around, No more bottles of beer on the wall.".
  Proof. reflexivity. Qed.              (* Verified by computation. *)

  (* the_song_verse_0: No more bottles—the final verse. *)
  Theorem the_song_verse_0
    : nth 99 (full_song 99) "" =        (* The 99th entry (verse for 0 bottles)... *)
      "No more bottles of beer on the wall, no more bottles of beer. " ++
      "Go to the store and buy some more, 99 bottles of beer on the wall.".
  Proof. reflexivity. Qed.              (* Verified by computation. *)

  (* the_song_is_complete: The song has exactly 100 verses, all verified. *)
  Theorem the_song_is_complete
    : List.length (full_song 99) = 100 /\    (* 100 verses total... *)
      List.NoDup (full_song 99) /\           (* ...all distinct... *)
      terminal (run 99 (initial 99)).   (* ...and the state machine terminates. *)
  Proof.
    split.                              (* Split first conjunct. *)
    - apply ninety_nine_bottles_100_verses.  (* 100 verses. *)
    - split.                            (* Split remaining conjuncts. *)
      + apply full_song_all_distinct.   (* All distinct. *)
        lia.                            (* 99 <= 99. *)
      + apply song_terminates.          (* Terminates. *)
  Qed.

  (* the_song_matches_execution: Every verse matches state machine execution. *)
  Theorem the_song_matches_execution
    : forall k,                         (* For every index k... *)
      k <= 99 ->                        (* ...from 0 to 99... *)
      nth k (full_song 99) "" =         (* ...the k-th song verse... *)
      current_verse (run k (initial 99)).  (* ...equals the k-th execution state's verse. *)
  Proof.
    intros k Hk.                        (* Introduce k and bound. *)
    symmetry.                           (* Flip equality direction. *)
    apply trajectory_full_song_correspondence.  (* Use the correspondence theorem. *)
    exact Hk.                           (* k <= 99. *)
  Qed.

  (** And thus, we have not merely claimed the song is correct—we have     *)
  (** PROVEN it. Each verse above is a machine-checked certificate.         *)
  (** The song computes correctly. The bottles are conserved. The state     *)
  (** machine terminates. Mathematics guarantees it.                        *)

(** ======================================================================= *)
(** CONCLUSION                                                              *)
(** ======================================================================= *)
(** We have formally verified the "99 Bottles of Beer" song:                *)
(**                                                                         *)
(** 1. TERMINATION: The song always ends (song_terminates)                  *)
(** 2. CONSERVATION: Bottles are neither created nor destroyed              *)
(**    (conservation_law)                                                   *)
(** 3. CORRECTNESS: Each verse correctly reflects the bottle count          *)
(**    (trajectory_full_song_correspondence)                                *)
(** 4. UNIQUENESS: Every verse is distinct (full_song_all_distinct)         *)
(** 5. COMPLETENESS: The state machine visits every verse (song_complete)   *)
(**                                                                         *)
(** This development demonstrates key verification techniques:              *)
(**   - State machine modeling                                              *)
(**   - Inductive invariants                                                *)
(**   - Well-founded recursion                                              *)
(**   - String manipulation with round-trip proofs                          *)
(**   - Injectivity arguments                                               *)
(**                                                                         *)
(** The familiar song provides intuition; the proofs provide certainty.     *)
(** ======================================================================= *)

End Bottles.

(** ======================================================================= *)
(** PART XIV: EXTRACTION                                                    *)
(** ======================================================================= *)
(** Coq can extract verified code to OCaml, Haskell, or Scheme. This        *)
(** allows running the song we've proven correct. The extraction mechanism  *)
(** preserves the computational content while discarding proofs.            *)
(** ======================================================================= *)

Require Import Extraction.             (* Load extraction machinery. *)
Require Import ExtrOcamlBasic.         (* Basic OCaml extraction settings. *)
Require Import ExtrOcamlString.        (* Extract Coq strings to OCaml strings. *)

(* Set up extraction to produce readable OCaml code. *)
Extraction Language OCaml.             (* Target language is OCaml. *)

(* Extract key types to native OCaml equivalents for efficiency. *)
Extract Inductive bool => "bool" [ "true" "false" ].  (* bool → bool. *)
Extract Inductive nat => "int"         (* nat → int for efficiency. *)
  [ "0" "(fun x -> x + 1)" ]           (* O → 0, S → increment. *)
  "(fun fO fS n -> if n = 0 then fO () else fS (n - 1))".  (* Pattern match. *)

(* The song itself: extract full_song to generate all verses. *)
(* Usage after extraction: Bottles.full_song 99 returns the complete song. *)

(* Recursive Extraction Bottles.full_song. *)
(* Uncomment the line above to extract full_song and all dependencies. *)

(* To extract to a file, use: *)
(* Extraction "bottles.ml" Bottles.full_song. *)

(* Example: Extract just the verse function for testing. *)
(* Extraction Bottles.verse. *)

(* After extraction, compile and run with: *)
(*   ocamlopt -o bottles bottles.ml *)
(*   ./bottles *)

(* Or in the OCaml REPL: *)
(*   #use "bottles.ml";; *)
(*   List.iter print_endline (Bottles.full_song 99);; *)

(** The extracted code is guaranteed correct by construction—it inherits   *)
(** all the properties we proved: termination, conservation, and verse     *)
(** correctness. The proofs are erased, but their guarantees remain.       *)
