(******************************************************************************)
(*                                                                            *)
(*                   99 Bottles of Beer: Verified Termination                 *)
(*                                                                            *)
(*     State machine model with conservation invariant, trajectory analysis,  *)
(*     verse generation, and bisimulation. Proves the song terminates after   *)
(*     exactly 100 verses with all bottles accounted for.                     *)
(*                                                                            *)
(*     "Anything can happen, child. Anything can be."                         *)
(*     — Shel Silverstein                                                     *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 2025                                                    *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Program.Wf.
Require Import Coq.Bool.Bool.
Import ListNotations.

Open Scope string_scope.

Module Bottles.

  Record State
    := mkState
         { on_wall : nat
         ; passed_around : nat
         ; starting_count : nat
         }.

  Definition initial (n : nat)
    : State
    := {| on_wall := n; passed_around := 0; starting_count := n |}.

  Definition terminal (s : State)
    : Prop
    := on_wall s = 0.

  Definition step (s : State)
    : State
    := match on_wall s with
       | O => s
       | S k => {| on_wall := k
                 ; passed_around := S (passed_around s)
                 ; starting_count := starting_count s
                 |}
       end.

  Definition invariant (s : State)
    : Prop
    := on_wall s + passed_around s = starting_count s.

  Theorem initial_satisfies_invariant
    : forall n, invariant (initial n).
  Proof.
    intro n; unfold invariant, initial; simpl; lia.
  Qed.

  Theorem step_preserves_invariant
    : forall s, invariant s -> invariant (step s).
  Proof.
    intros [w p st] H; unfold invariant, step in *; simpl in *.
    destruct w; simpl; lia.
  Qed.

  Theorem step_preserves_starting_count
    : forall s, starting_count (step s) = starting_count s.
  Proof.
    intros [w p st]; unfold step; simpl; destruct w; reflexivity.
  Qed.

  Theorem step_decreases_or_terminal
    : forall s, terminal s \/ on_wall (step s) < on_wall s.
  Proof.
    intros [w p st]; unfold terminal, step; simpl.
    destruct w.
    - left; reflexivity.
    - right; apply Nat.lt_succ_diag_r.
  Qed.

  Theorem terminal_is_fixpoint
    : forall s, terminal s -> step s = s.
  Proof.
    intros [w p st] H; unfold terminal, step in *; simpl in *.
    rewrite H; reflexivity.
  Qed.

  Fixpoint run (fuel : nat) (s : State)
    : State
    := match fuel with
       | O => s
       | S k => run k (step s)
       end.

  Theorem run_preserves_invariant
    : forall fuel s, invariant s -> invariant (run fuel s).
  Proof.
    induction fuel; intros s H; simpl.
    - exact H.
    - apply IHfuel, step_preserves_invariant, H.
  Qed.

  Theorem run_preserves_starting_count
    : forall fuel s, starting_count (run fuel s) = starting_count s.
  Proof.
    induction fuel; intro s; simpl.
    - reflexivity.
    - rewrite IHfuel; apply step_preserves_starting_count.
  Qed.

  Lemma run_reaches_zero
    : forall w p st, on_wall (run w {| on_wall := w; passed_around := p; starting_count := st |}) = 0.
  Proof.
    induction w; intros p st; simpl.
    - reflexivity.
    - apply IHw.
  Qed.

  Theorem sufficient_fuel_reaches_terminal
    : forall s, terminal (run (on_wall s) s).
  Proof.
    intros [w p st]; unfold terminal; simpl; apply run_reaches_zero.
  Qed.

  Theorem song_terminates
    : terminal (run 99 (initial 99)).
  Proof. reflexivity. Qed.

  Theorem all_bottles_passed_at_end
    : forall n, passed_around (run n (initial n)) = n.
  Proof.
    intro n.
    pose proof (run_preserves_invariant n (initial n) (initial_satisfies_invariant n)) as Hinv.
    pose proof (sufficient_fuel_reaches_terminal (initial n)) as Hterm.
    pose proof (run_preserves_starting_count n (initial n)) as Hst.
    unfold initial, invariant, terminal in *; simpl in *.
    rewrite Hst in Hinv; simpl in Hinv.
    lia.
  Qed.

  Definition monotonic_decreasing (f : nat -> State)
    : Prop
    := forall i j, i <= j -> on_wall (f j) <= on_wall (f i).

  Definition trajectory (s : State)
    : nat -> State
    := fun i => run i s.

  Lemma step_nonincreasing
    : forall s, on_wall (step s) <= on_wall s.
  Proof.
    intros [w p st]; unfold step; simpl; destruct w.
    - apply Nat.le_refl.
    - apply Nat.le_succ_diag_r.
  Qed.

  Theorem no_bottles_created
    : forall s fuel, on_wall (run fuel s) <= on_wall s.
  Proof.
    intros s fuel; revert s; induction fuel; intro s; simpl.
    - lia.
    - specialize (IHfuel (step s)).
      pose proof (step_nonincreasing s); lia.
  Qed.

  Lemma on_wall_run_step
    : forall fuel s, on_wall (run fuel (step s)) <= on_wall (run fuel s).
  Proof.
    induction fuel; intro s; simpl.
    - apply step_nonincreasing.
    - apply IHfuel.
  Qed.

  Lemma run_succ_le
    : forall fuel s, on_wall (run (S fuel) s) <= on_wall (run fuel s).
  Proof.
    intros fuel s; simpl; apply on_wall_run_step.
  Qed.

  Theorem trajectory_monotonic
    : forall s, monotonic_decreasing (trajectory s).
  Proof.
    intros s i j Hij; unfold trajectory.
    induction Hij.
    - lia.
    - pose proof (run_succ_le m s); lia.
  Qed.

  Inductive Reachable (s0 : State)
    : State -> Prop
    := | reach_refl
         : Reachable s0 s0
       | reach_step s s'
         : Reachable s0 s -> s' = step s -> Reachable s0 s'.

  Lemma reachable_trans
    : forall s0 s1 s2, Reachable s0 s1 -> Reachable s1 s2 -> Reachable s0 s2.
  Proof.
    intros s0 s1 s2 H1 H2; induction H2.
    - exact H1.
    - apply reach_step with s; [exact IHReachable | exact H].
  Qed.

  Theorem reachable_run
    : forall fuel s, Reachable s (run fuel s).
  Proof.
    induction fuel; intro s; simpl.
    - apply reach_refl.
    - apply reachable_trans with (step s).
      + apply reach_step with s; [apply reach_refl | reflexivity].
      + apply IHfuel.
  Qed.

  Theorem terminal_reachable_from_any_start
    : forall n, exists s, Reachable (initial n) s /\ terminal s.
  Proof.
    intro n; exists (run n (initial n)); split.
    - apply reachable_run.
    - pose proof (sufficient_fuel_reaches_terminal (initial n)) as H.
      unfold initial in *; simpl in *; exact H.
  Qed.

  Theorem reachable_preserves_invariant
    : forall s0 s, invariant s0 -> Reachable s0 s -> invariant s.
  Proof.
    intros s0 s Hinv Hreach; induction Hreach.
    - exact Hinv.
    - rewrite H; apply step_preserves_invariant; exact IHHreach.
  Qed.

  Theorem reachable_preserves_starting_count
    : forall s0 s, Reachable s0 s -> starting_count s = starting_count s0.
  Proof.
    intros s0 s Hreach; induction Hreach.
    - reflexivity.
    - rewrite H, step_preserves_starting_count; exact IHHreach.
  Qed.

  Theorem conservation_law
    : forall n s, Reachable (initial n) s -> on_wall s + passed_around s = n.
  Proof.
    intros n s Hreach.
    pose proof (reachable_preserves_invariant (initial n) s) as Hinv.
    pose proof (reachable_preserves_starting_count (initial n) s Hreach) as Hst.
    unfold invariant, initial in *; simpl in *.
    rewrite Hst in Hinv.
    apply Hinv.
    - unfold invariant, initial; simpl; lia.
    - exact Hreach.
  Qed.

  Definition digit_to_char (d : nat) : ascii :=
    match d with
    | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
    | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
    end.

  Definition digit_to_string (d : nat) : string :=
    String (digit_to_char d) EmptyString.

  Fixpoint nat_to_string_aux (fuel n : nat) (acc : string) : string :=
    match fuel with
    | O => acc
    | S f =>
        let d := n mod 10 in
        let r := n / 10 in
        let acc' := digit_to_string d ++ acc in
        match r with
        | O => acc'
        | _ => nat_to_string_aux f r acc'
        end
    end.

  Definition nat_to_string (n : nat) : string :=
    match n with
    | O => "0"
    | _ => nat_to_string_aux n n ""
    end.

  Lemma nat_to_string_0 : nat_to_string 0 = "0".
  Proof. reflexivity. Qed.

  Lemma nat_to_string_1 : nat_to_string 1 = "1".
  Proof. reflexivity. Qed.

  Lemma nat_to_string_10 : nat_to_string 10 = "10".
  Proof. reflexivity. Qed.

  Lemma nat_to_string_99 : nat_to_string 99 = "99".
  Proof. reflexivity. Qed.

  Lemma nat_to_string_42 : nat_to_string 42 = "42".
  Proof. reflexivity. Qed.

  Definition char_to_digit (c : ascii) : option nat :=
    match c with
    | "0" => Some 0 | "1" => Some 1 | "2" => Some 2 | "3" => Some 3 | "4" => Some 4
    | "5" => Some 5 | "6" => Some 6 | "7" => Some 7 | "8" => Some 8 | "9" => Some 9
    | _ => None
    end%char.

  Lemma char_to_digit_to_char
    : forall d, d < 10 -> char_to_digit (digit_to_char d) = Some d.
  Proof.
    intros d Hd.
    do 10 (destruct d; [reflexivity|]).
    lia.
  Qed.

  Lemma digit_to_char_to_digit
    : forall c d, char_to_digit c = Some d -> digit_to_char d = c.
  Proof.
    intros c d H.
    destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
    destruct b0, b1, b2, b3, b4, b5, b6, b7;
      simpl in H; try discriminate H; injection H as <-; reflexivity.
  Qed.

  Fixpoint string_to_nat_aux (s : string) (acc : nat) : option nat :=
    match s with
    | EmptyString => Some acc
    | String c rest =>
        match char_to_digit c with
        | None => None
        | Some d => string_to_nat_aux rest (acc * 10 + d)
        end
    end.

  Definition string_to_nat (s : string) : option nat :=
    match s with
    | EmptyString => None
    | String c rest =>
        match char_to_digit c with
        | None => None
        | Some d => string_to_nat_aux rest d
        end
    end.

  Lemma string_to_nat_aux_app
    : forall s1 s2 acc,
        string_to_nat_aux (s1 ++ s2) acc =
        match string_to_nat_aux s1 acc with
        | None => None
        | Some n => string_to_nat_aux s2 n
        end.
  Proof.
    induction s1; intros s2 acc; simpl.
    - reflexivity.
    - destruct (char_to_digit a); [|reflexivity].
      apply IHs1.
  Qed.

  Lemma string_to_nat_single
    : forall d, d < 10 -> string_to_nat (digit_to_string d) = Some d.
  Proof.
    intros d Hd.
    unfold string_to_nat, digit_to_string.
    rewrite char_to_digit_to_char by assumption.
    reflexivity.
  Qed.

  Lemma string_to_nat_aux_single
    : forall d acc, d < 10 -> string_to_nat_aux (digit_to_string d) acc = Some (acc * 10 + d).
  Proof.
    intros d acc Hd.
    unfold digit_to_string.
    simpl.
    rewrite char_to_digit_to_char by assumption.
    reflexivity.
  Qed.

  Lemma string_app_assoc
    : forall s1 s2 s3 : string, (s1 ++ (s2 ++ s3) = (s1 ++ s2) ++ s3)%string.
  Proof.
    induction s1; intros s2 s3; simpl.
    - reflexivity.
    - rewrite IHs1.
      reflexivity.
  Qed.

  Lemma string_cons_app
    : forall c s1 s2, String c s1 ++ s2 = String c (s1 ++ s2).
  Proof.
    reflexivity.
  Qed.

  Lemma nat_to_string_aux_app_gen
    : forall f n acc1 acc2,
      nat_to_string_aux f n (acc1 ++ acc2) = nat_to_string_aux f n acc1 ++ acc2.
  Proof.
    induction f; intros n acc1 acc2.
    - reflexivity.
    - cbn -[Nat.div Nat.modulo].
      destruct (n / 10).
      + reflexivity.
      + rewrite <- string_cons_app.
        apply IHf.
  Qed.

  Lemma nat_to_string_aux_app'
    : forall f n acc,
      nat_to_string_aux f n acc = nat_to_string_aux f n "" ++ acc.
  Proof.
    intros f n acc.
    change acc with ("" ++ acc).
    apply nat_to_string_aux_app_gen.
  Qed.

  Lemma div10_lt
    : forall n, n > 0 -> n / 10 < n.
  Proof.
    intros n Hn.
    apply Nat.div_lt; lia.
  Qed.

  Lemma digit_to_string_length
    : forall d, String.length (digit_to_string d) = 1.
  Proof.
    intro d.
    unfold digit_to_string.
    reflexivity.
  Qed.

  Lemma string_app_length_early
    : forall s1 s2, String.length (s1 ++ s2) = String.length s1 + String.length s2.
  Proof.
    induction s1; intro s2; simpl.
    - reflexivity.
    - rewrite IHs1.
      reflexivity.
  Qed.

  Lemma nat_to_string_aux_nonempty
    : forall f n, f > 0 -> String.length (nat_to_string_aux f n "") > 0.
  Proof.
    intros f n Hf.
    destruct f; [lia|].
    unfold nat_to_string_aux; fold nat_to_string_aux.
    destruct (n / 10).
    - unfold digit_to_string; simpl.
      lia.
    - rewrite nat_to_string_aux_app'.
      rewrite string_app_length_early.
      unfold digit_to_string; simpl.
      lia.
  Qed.

  Lemma nat_to_string_aux_first_char_digit
    : forall f n,
      f > 0 ->
      exists c rest, nat_to_string_aux f n "" = String c rest /\
                     exists d, d < 10 /\ c = digit_to_char d.
  Proof.
    intro f.
    induction f as [f IH] using (well_founded_induction lt_wf).
    intros n Hf.
    destruct f; [lia|].
    unfold nat_to_string_aux; fold nat_to_string_aux.
    destruct (n / 10) eqn:Hr.
    - exists (digit_to_char (n mod 10)), "".
      split; [reflexivity|].
      exists (n mod 10).
      split; [apply Nat.mod_upper_bound; lia | reflexivity].
    - rewrite nat_to_string_aux_app'.
      destruct f.
      + simpl.
        exists (digit_to_char (n mod 10)), "".
        split; [reflexivity|].
        exists (n mod 10).
        split; [apply Nat.mod_upper_bound; lia | reflexivity].
      + destruct (nat_to_string_aux (S f) (S n0) "") eqn:Haux.
        * exfalso.
          assert (Hlen : String.length (nat_to_string_aux (S f) (S n0) "") > 0).
          { apply nat_to_string_aux_nonempty; lia. }
          rewrite Haux in Hlen; simpl in Hlen; lia.
        * exists a, (s ++ digit_to_string (n mod 10)).
          split; [reflexivity|].
          destruct (IH (S f)) with (n := S n0) as [c' [rest' [Heq' [d' [Hd' Hc']]]]].
          -- lia.
          -- lia.
          -- rewrite Heq' in Haux.
             injection Haux as Ha Hs.
             exists d'.
             split; [exact Hd' | congruence].
  Qed.

  Lemma char_to_digit_digit_to_char_Some
    : forall d, d < 10 -> exists k, char_to_digit (digit_to_char d) = Some k.
  Proof.
    intros d Hd.
    exists d.
    apply char_to_digit_to_char.
    exact Hd.
  Qed.

  Lemma nat_to_string_aux_value
    : forall n f,
      n > 0 -> f >= n ->
      string_to_nat (nat_to_string_aux f n "") = Some n.
  Proof.
    intro n.
    induction n as [n IH] using (well_founded_induction lt_wf).
    intros f Hn Hf.
    destruct f; [lia|].
    unfold nat_to_string_aux; fold nat_to_string_aux.
    destruct (n / 10) eqn:Hr.
    - assert (Hmod : n mod 10 = n).
      { apply Nat.mod_small.
        apply Nat.div_small_iff; [lia | exact Hr]. }
      assert (Hn_bound : n < 10).
      { apply Nat.div_small_iff in Hr; lia. }
      unfold string_to_nat, digit_to_string.
      rewrite Hmod.
      simpl.
      rewrite char_to_digit_to_char by lia.
      reflexivity.
    - rewrite nat_to_string_aux_app'.
      assert (Hr_pos : S n0 > 0) by lia.
      assert (Hr_lt : S n0 < n).
      { rewrite <- Hr; apply div10_lt; lia. }
      assert (Hd_bound : n mod 10 < 10).
      { apply Nat.mod_upper_bound; lia. }
      assert (Hf_r : f >= S n0) by lia.
      destruct (nat_to_string_aux f (S n0) "") eqn:Haux.
      + exfalso.
        assert (Hlen : String.length (nat_to_string_aux f (S n0) "") > 0).
        { apply nat_to_string_aux_nonempty; lia. }
        rewrite Haux in Hlen; simpl in Hlen; lia.
      + assert (Haux_val : string_to_nat (String a s) = Some (S n0)).
        { rewrite <- Haux; apply IH; lia. }
        unfold string_to_nat in Haux_val.
        destruct (char_to_digit a) eqn:Hchar.
        * unfold string_to_nat.
          cbn -[Nat.modulo].
          rewrite Hchar.
          rewrite string_to_nat_aux_app.
          rewrite Haux_val.
          unfold digit_to_string.
          cbn -[Nat.modulo].
          rewrite char_to_digit_to_char by assumption.
          f_equal.
          pose proof (Nat.div_mod_eq n 10) as Heq.
          rewrite Hr in Heq.
          lia.
        * discriminate Haux_val.
  Qed.

  Theorem nat_to_string_to_nat
    : forall n, n > 0 -> string_to_nat (nat_to_string n) = Some n.
  Proof.
    intros n Hn.
    unfold nat_to_string.
    destruct n; [lia|].
    apply nat_to_string_aux_value; lia.
  Qed.

  Theorem nat_to_string_inj
    : forall n1 n2, n1 > 0 -> n2 > 0 ->
      nat_to_string n1 = nat_to_string n2 -> n1 = n2.
  Proof.
    intros n1 n2 H1 H2 Heq.
    apply (f_equal string_to_nat) in Heq.
    rewrite nat_to_string_to_nat in Heq by assumption.
    rewrite nat_to_string_to_nat in Heq by assumption.
    injection Heq as Heq.
    exact Heq.
  Qed.

  Definition first_char (s : string) : option ascii :=
    match s with
    | EmptyString => None
    | String c _ => Some c
    end.

  Definition canonical_nat_string (s : string) : Prop :=
    s = "0" \/ (s <> EmptyString /\ forall c, first_char s = Some c -> c <> "0"%char).

  Lemma nat_to_string_pos_not_zero_char
    : forall n, n > 0 -> n <= 99 ->
        forall c, first_char (nat_to_string n) = Some c -> c <> "0"%char.
  Proof.
    intros n Hpos Hle c Hfc Heq.
    destruct n; [lia|].
    do 99 (destruct n; [simpl in Hfc; injection Hfc as <-; discriminate Heq|]).
    lia.
  Qed.

  Lemma nat_to_string_canonical
    : forall n, n <= 99 -> canonical_nat_string (nat_to_string n).
  Proof.
    intros n Hle.
    destruct n as [|n'].
    - left; reflexivity.
    - right.
      split.
      + unfold nat_to_string.
        destruct (nat_to_string_aux_first_char_digit (S n') (S n') ltac:(lia))
          as [c [rest [Heq _]]].
        rewrite Heq.
        discriminate.
      + intros c Hfc.
        apply (nat_to_string_pos_not_zero_char (S n')); [lia | lia | exact Hfc].
  Qed.

  Lemma string_to_nat_aux_ge
    : forall s acc n, string_to_nat_aux s acc = Some n -> n >= acc.
  Proof.
    induction s; intros acc n H; simpl in H.
    - injection H as H; lia.
    - destruct (char_to_digit a); [|discriminate H].
      apply IHs in H; lia.
  Qed.

  Lemma string_to_nat_first_zero_implies_zero
    : forall s, string_to_nat s = Some 0 ->
        exists rest, s = String "0"%char rest /\ string_to_nat_aux rest 0 = Some 0.
  Proof.
    intros s H.
    destruct s as [|c rest]; [discriminate H|].
    unfold string_to_nat in H.
    destruct (char_to_digit c) eqn:Hcd; [|discriminate H].
    destruct n.
    - exists rest.
      destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
      destruct b0, b1, b2, b3, b4, b5, b6, b7; try discriminate Hcd.
      split; [reflexivity | exact H].
    - simpl in H.
      pose proof (string_to_nat_aux_ge rest (S n) 0 H); lia.
  Qed.

  Theorem string_to_nat_nat_to_string_roundtrip
    : forall n, n > 0 -> string_to_nat (nat_to_string n) = Some n.
  Proof.
    intros n Hn.
    apply nat_to_string_to_nat; lia.
  Qed.

  Lemma string_to_nat_zero : string_to_nat "0" = Some 0.
  Proof. reflexivity. Qed.

  Fixpoint leading_nat_aux (s : string) (acc : nat) : nat :=
    match s with
    | EmptyString => acc
    | String c rest =>
        match char_to_digit c with
        | None => acc
        | Some d => leading_nat_aux rest (acc * 10 + d)
        end
    end.

  Definition leading_nat (s : string) : option nat :=
    match s with
    | EmptyString => None
    | String c rest =>
        match char_to_digit c with
        | None => None
        | Some d => Some (leading_nat_aux rest d)
        end
    end.

  Definition is_digit (c : ascii) : bool :=
    match c with
    | "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" => true
    | _ => false
    end%char.

  Lemma leading_nat_aux_app_non_digit
    : forall s1 s2 acc c,
        is_digit c = false ->
        leading_nat_aux (s1 ++ String c s2) acc = leading_nat_aux s1 acc.
  Proof.
    induction s1; intros s2 acc c Hc; simpl.
    - unfold is_digit in Hc.
      destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
      destruct b0, b1, b2, b3, b4, b5, b6, b7;
        try discriminate Hc; reflexivity.
    - destruct (char_to_digit a) eqn:Ha.
      + apply IHs1; exact Hc.
      + reflexivity.
  Qed.

  Fixpoint all_digits (s : string) : bool :=
    match s with
    | EmptyString => true
    | String c rest => is_digit c && all_digits rest
    end.

  Lemma leading_nat_aux_string_to_nat_aux
    : forall s acc,
        all_digits s = true ->
        string_to_nat_aux s acc = Some (leading_nat_aux s acc).
  Proof.
    induction s; intros acc Hd; simpl.
    - reflexivity.
    - simpl in Hd.
      destruct (is_digit a) eqn:Ha; simpl in Hd; [|discriminate].
      unfold is_digit in Ha.
      destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
      destruct b0, b1, b2, b3, b4, b5, b6, b7;
        try discriminate Ha; simpl; apply IHs; exact Hd.
  Qed.

  Lemma is_digit_digit_to_char
    : forall d, d < 10 -> is_digit (digit_to_char d) = true.
  Proof.
    intros d Hd.
    do 10 (destruct d; [reflexivity|]); lia.
  Qed.

  Lemma all_digits_app
    : forall s1 s2, all_digits (s1 ++ s2) = (all_digits s1 && all_digits s2)%bool.
  Proof.
    induction s1; intro s2; simpl.
    - reflexivity.
    - rewrite IHs1.
      destruct (is_digit a); simpl; reflexivity.
  Qed.

  Lemma all_digits_digit_to_string
    : forall d, d < 10 -> all_digits (digit_to_string d) = true.
  Proof.
    intros d Hd.
    unfold digit_to_string; simpl.
    rewrite is_digit_digit_to_char by exact Hd.
    reflexivity.
  Qed.

  Lemma is_digit_digit_to_char_any
    : forall d, is_digit (digit_to_char d) = true.
  Proof.
    intro d.
    do 10 (destruct d; [reflexivity|]).
    reflexivity.
  Qed.

  Lemma nat_to_string_aux_all_digits_gen
    : forall f n acc, all_digits acc = true ->
        all_digits (nat_to_string_aux f n acc) = true.
  Proof.
    induction f; intros n acc Hacc.
    - exact Hacc.
    - cbn -[Nat.div Nat.modulo].
      destruct (n / 10) eqn:Hr.
      + unfold digit_to_string; simpl.
        rewrite is_digit_digit_to_char_any.
        simpl.
        exact Hacc.
      + apply IHf.
        unfold digit_to_string; simpl.
        rewrite is_digit_digit_to_char_any.
        simpl.
        exact Hacc.
  Qed.

  Lemma nat_to_string_aux_all_digits
    : forall f n, all_digits (nat_to_string_aux f n "") = true.
  Proof.
    intros f n.
    apply nat_to_string_aux_all_digits_gen.
    reflexivity.
  Qed.

  Lemma nat_to_string_all_digits
    : forall n, all_digits (nat_to_string n) = true.
  Proof.
    intro n; unfold nat_to_string.
    destruct n; [reflexivity|].
    apply nat_to_string_aux_all_digits.
  Qed.

  Lemma leading_nat_nat_to_string
    : forall n, n > 0 -> leading_nat (nat_to_string n) = Some n.
  Proof.
    intros n Hn.
    pose proof (nat_to_string_to_nat n Hn) as H.
    pose proof (nat_to_string_all_digits n) as Hd.
    unfold string_to_nat in H.
    unfold leading_nat.
    destruct (nat_to_string n) eqn:Ens.
    - unfold nat_to_string in Ens.
      destruct n; [lia|].
      pose proof (nat_to_string_aux_nonempty (S n) (S n) ltac:(lia)) as Hne.
      rewrite Ens in Hne; simpl in Hne; lia.
    - destruct (char_to_digit a) eqn:Ha.
      + f_equal.
        simpl in Hd.
        destruct (is_digit a) eqn:Hdig; simpl in Hd; [|discriminate].
        rewrite leading_nat_aux_string_to_nat_aux in H by exact Hd.
        injection H as H.
        exact H.
      + discriminate H.
  Qed.

  Lemma leading_nat_app_non_digit
    : forall s1 s2 c,
        is_digit c = false ->
        leading_nat (s1 ++ String c s2) = leading_nat s1.
  Proof.
    intros s1 s2 c Hc.
    destruct s1 as [|a s1']; simpl.
    - unfold is_digit in Hc.
      destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
      destruct b0, b1, b2, b3, b4, b5, b6, b7;
        try discriminate Hc; reflexivity.
    - destruct (char_to_digit a); [|reflexivity].
      f_equal.
      apply leading_nat_aux_app_non_digit.
      exact Hc.
  Qed.

  Definition bottle_word (n : nat) : string :=
    match n with
    | 1 => "bottle"
    | _ => "bottles"
    end.

  Definition count_phrase (n : nat) : string :=
    match n with
    | 0 => "No more bottles"
    | _ => nat_to_string n ++ " " ++ bottle_word n
    end.

  Definition verse (start n : nat) : string :=
    match n with
    | 0 => "No more bottles of beer on the wall, no more bottles of beer. " ++
           "Go to the store and buy some more, " ++
           nat_to_string start ++ " bottles of beer on the wall."
    | S k => count_phrase n ++ " of beer on the wall, " ++
             count_phrase n ++ " of beer. " ++
             "Take one down and pass it around, " ++
             count_phrase k ++ " of beer on the wall."
    end.

  Definition current_verse (s : State) : string :=
    verse (starting_count s) (on_wall s).

  Fixpoint full_song_aux (start n : nat) (acc : list string) : list string :=
    match n with
    | 0 => acc ++ [verse start 0]
    | S k => full_song_aux start k (acc ++ [verse start (S k)])
    end.

  Definition full_song (start : nat) : list string :=
    full_song_aux start start [].

  Theorem verse_one_singular
    : forall start, verse start 1 = "1 bottle of beer on the wall, 1 bottle of beer. " ++
                "Take one down and pass it around, No more bottles of beer on the wall.".
  Proof. intro; reflexivity. Qed.

  Theorem verse_two_plural
    : forall start, verse start 2 = "2 bottles of beer on the wall, 2 bottles of beer. " ++
                "Take one down and pass it around, 1 bottle of beer on the wall.".
  Proof. intro; reflexivity. Qed.

  Theorem verse_99
    : verse 99 99 = "99 bottles of beer on the wall, 99 bottles of beer. " ++
                 "Take one down and pass it around, 98 bottles of beer on the wall.".
  Proof. reflexivity. Qed.

  Theorem verse_0_uses_start
    : forall start, verse start 0 = "No more bottles of beer on the wall, no more bottles of beer. " ++
           "Go to the store and buy some more, " ++
           nat_to_string start ++ " bottles of beer on the wall.".
  Proof. intro; reflexivity. Qed.

  Theorem verse_50_0
    : verse 50 0 = "No more bottles of beer on the wall, no more bottles of beer. " ++
           "Go to the store and buy some more, 50 bottles of beer on the wall.".
  Proof. reflexivity. Qed.

  Theorem full_song_length
    : forall n, List.length (full_song n) = S n.
  Proof.
    intro n; unfold full_song.
    assert (H : forall start m acc, List.length (full_song_aux start m acc) = List.length acc + S m).
    { intros start; induction m; intro acc; simpl.
      - rewrite app_length; simpl; lia.
      - rewrite IHm, app_length; simpl; lia. }
    rewrite H; simpl; lia.
  Qed.

  Theorem ninety_nine_bottles_100_verses
    : List.length (full_song 99) = 100.
  Proof. apply full_song_length. Qed.

  Theorem full_song_nth
    : forall k, k <= 99 -> nth k (full_song 99) "" = verse 99 (99 - k).
  Proof.
    intro k.
    do 100 (destruct k; [reflexivity|]); lia.
  Qed.

  Lemma digit_to_char_inj
    : forall d1 d2, d1 < 10 -> d2 < 10 -> digit_to_char d1 = digit_to_char d2 -> d1 = d2.
  Proof.
    intros d1 d2 H1 H2.
    do 10 (destruct d1; [do 10 (destruct d2; [reflexivity || intro H; inversion H|]); lia|]).
    lia.
  Qed.

  Lemma digit_to_string_inj
    : forall d1 d2, d1 < 10 -> d2 < 10 -> digit_to_string d1 = digit_to_string d2 -> d1 = d2.
  Proof.
    intros d1 d2 H1 H2 Heq.
    unfold digit_to_string in Heq.
    inversion Heq.
    apply digit_to_char_inj; assumption.
  Qed.

  Definition single_digit (n : nat) : Prop := n < 10.
  Definition double_digit (n : nat) : Prop := 10 <= n < 100.

  Lemma single_digit_length
    : forall n, single_digit n -> String.length (nat_to_string n) = 1.
  Proof.
    intros n Hsd; unfold single_digit in Hsd.
    do 10 (destruct n; [reflexivity|]); lia.
  Qed.

  Lemma double_digit_length
    : forall n, double_digit n -> String.length (nat_to_string n) = 2.
  Proof.
    intros n [Hlo Hhi].
    do 10 (destruct n; [lia|]).
    do 90 (destruct n; [reflexivity|]); lia.
  Qed.

  Lemma string_cons_inj
    : forall c1 c2 s1 s2, String c1 s1 = String c2 s2 -> c1 = c2 /\ s1 = s2.
  Proof.
    intros c1 c2 s1 s2 H.
    inversion H.
    split; reflexivity.
  Qed.

  Lemma digit_char_neq_N
    : forall d, d < 10 -> digit_to_char d <> "N"%char.
  Proof.
    intros d Hd Heq.
    do 10 (destruct d; [discriminate Heq|]).
    lia.
  Qed.

  Lemma digit_to_char_is_digit
    : forall d, d < 10 -> is_digit (digit_to_char d) = true.
  Proof.
    intros d Hd.
    do 10 (destruct d; [reflexivity|]); lia.
  Qed.

  Lemma is_digit_neq_N
    : forall c, is_digit c = true -> c <> "N"%char.
  Proof.
    intros c Hdig Heq.
    rewrite Heq in Hdig.
    discriminate Hdig.
  Qed.

  Lemma nat_to_string_starts_with_digit
    : forall n, n > 0 -> n <= 99 ->
        exists c rest, nat_to_string n = String c rest /\ is_digit c = true.
  Proof.
    intros n Hpos Hle.
    unfold nat_to_string.
    destruct n; [lia|].
    destruct (nat_to_string_aux_first_char_digit (S n) (S n)) as [c [rest [Heq [d [Hd Hc]]]]]; [lia|].
    exists c, rest.
    rewrite Heq, Hc.
    split; [reflexivity|].
    apply digit_to_char_is_digit.
    exact Hd.
  Qed.

  Lemma N_not_digit : is_digit "N"%char = false.
  Proof. reflexivity. Qed.

  Lemma first_char_app
    : forall c s1 s2, first_char (String c s1 ++ s2) = Some c.
  Proof. intros; reflexivity. Qed.

  Lemma first_char_eq
    : forall s1 s2, s1 = s2 -> first_char s1 = first_char s2.
  Proof. intros s1 s2 H; rewrite H; reflexivity. Qed.

  Lemma count_phrase_first_char_digit
    : forall n, n > 0 -> n <= 99 ->
        exists c, first_char (count_phrase n) = Some c /\ is_digit c = true.
  Proof.
    intros n Hpos Hle.
    unfold count_phrase.
    destruct n; [lia|].
    destruct (nat_to_string_starts_with_digit (S n) Hpos Hle) as [c [rest [Heq Hdig]]].
    exists c.
    rewrite Heq.
    simpl.
    split; [reflexivity | exact Hdig].
  Qed.

  Lemma verse_first_char_0
    : forall start, first_char (verse start 0) = Some "N"%char.
  Proof. intro; reflexivity. Qed.

  Lemma verse_first_char_Sn
    : forall start n, n <= 98 ->
        exists c, first_char (verse start (S n)) = Some c /\ is_digit c = true.
  Proof.
    intros start n Hle.
    assert (Hpos : S n > 0) by lia.
    assert (Hle2 : S n <= 99) by lia.
    destruct (nat_to_string_starts_with_digit (S n) Hpos Hle2) as [c [rest [Heq Hdig]]].
    exists c.
    unfold verse, count_phrase.
    rewrite Heq.
    simpl.
    split; [reflexivity | exact Hdig].
  Qed.

  Lemma verse_0_ne_Sn
    : forall start n, n <= 98 -> verse start 0 <> verse start (S n).
  Proof.
    intros start n Hle H.
    pose proof (verse_first_char_0 start) as H0.
    pose proof (verse_first_char_Sn start n Hle) as [c [HSn Hdig]].
    apply first_char_eq in H.
    rewrite H0, HSn in H.
    inversion H as [Hc].
    rewrite <- Hc in Hdig.
    simpl in Hdig.
    discriminate Hdig.
  Qed.

  Lemma string_neq_first_char
    : forall c1 c2 s1 s2, c1 <> c2 -> String c1 s1 <> String c2 s2.
  Proof.
    intros c1 c2 s1 s2 Hneq Heq.
    injection Heq as Hc _.
    exact (Hneq Hc).
  Qed.

  Lemma verse_leading_nat
    : forall start n, n > 0 -> n <= 99 ->
        leading_nat (verse start n) = Some n.
  Proof.
    intros start n Hpos Hle.
    destruct n; [lia|].
    do 99 (destruct n as [|n]; [reflexivity|]).
    lia.
  Qed.

  Lemma verse_Sn_inj
    : forall start n1 n2, S n1 <= 99 -> S n2 <= 99 ->
        verse start (S n1) = verse start (S n2) -> S n1 = S n2.
  Proof.
    intros start n1 n2 H1 H2 Heq.
    apply (f_equal leading_nat) in Heq.
    rewrite verse_leading_nat in Heq by lia.
    rewrite verse_leading_nat in Heq by lia.
    congruence.
  Qed.

  Theorem verse_inj
    : forall start n1 n2, n1 <= 99 -> n2 <= 99 ->
        verse start n1 = verse start n2 -> n1 = n2.
  Proof.
    intros start n1 n2 H1 H2 Heq.
    destruct n1 as [|n1']; destruct n2 as [|n2'].
    - reflexivity.
    - exfalso; apply (verse_0_ne_Sn start n2'); [lia | exact Heq].
    - exfalso; apply (verse_0_ne_Sn start n1'); [lia | symmetry; exact Heq].
    - apply (verse_Sn_inj start); assumption.
  Qed.

  Theorem full_song_all_distinct
    : forall i j, i <= 99 -> j <= 99 -> i <> j ->
        nth i (full_song 99) "" <> nth j (full_song 99) "".
  Proof.
    intros i j Hi Hj Hneq.
    rewrite full_song_nth by lia.
    rewrite full_song_nth by lia.
    intro Heq.
    apply verse_inj in Heq; lia.
  Qed.

  Lemma run_decreases_on_wall
    : forall k w p st, k <= w ->
        on_wall (run k {| on_wall := w; passed_around := p; starting_count := st |}) = w - k.
  Proof.
    induction k; intros w p st Hle.
    - simpl; lia.
    - destruct w as [|w'].
      + lia.
      + change (on_wall (run k {| on_wall := w'; passed_around := S p; starting_count := st |}) = S w' - S k).
        rewrite IHk by lia.
        lia.
  Qed.

  Theorem bisimulation
    : forall k n, k <= n -> on_wall (run k (initial n)) = n - k.
  Proof.
    intros k n Hle.
    unfold initial.
    apply run_decreases_on_wall.
    exact Hle.
  Qed.

  Theorem bisimulation_passed
    : forall k n, k <= n -> passed_around (run k (initial n)) = k.
  Proof.
    intros k n Hle.
    pose proof (run_preserves_invariant k (initial n) (initial_satisfies_invariant n)) as Hinv.
    pose proof (bisimulation k n Hle) as Hwall.
    unfold invariant, initial in *; simpl in *.
    rewrite run_preserves_starting_count in Hinv; simpl in Hinv.
    lia.
  Qed.

  Definition step_fuel (s : State) : nat := on_wall s.

  Lemma step_fuel_decreases
    : forall s, ~ terminal s -> step_fuel (step s) < step_fuel s.
  Proof.
    intros [w p st] Hnt; unfold terminal, step_fuel, step in *; simpl in *.
    destruct w.
    - contradict Hnt; reflexivity.
    - apply Nat.lt_succ_diag_r.
  Qed.

  Definition wf_step_rel : State -> State -> Prop :=
    fun s' s => step_fuel s' < step_fuel s.

  Lemma wf_step_rel_wf : well_founded wf_step_rel.
  Proof.
    unfold wf_step_rel.
    apply well_founded_ltof.
  Qed.

  Definition run_wf_F (s : State)
                       (rec : forall s', wf_step_rel s' s ->
                              { s'' : State | terminal s'' /\ Reachable s' s'' })
    : { s' : State | terminal s' /\ Reachable s s' }.
  Proof.
    destruct (Nat.eq_dec (on_wall s) 0) as [Hz | Hnz].
    - exists s; split.
      + unfold terminal; exact Hz.
      + apply reach_refl.
    - assert (Hrel : wf_step_rel (step s) s).
      { unfold wf_step_rel.
        apply step_fuel_decreases.
        unfold terminal; intro H; apply Hnz; exact H. }
      destruct (rec (step s) Hrel) as [s' [Hterm Hreach]].
      exists s'; split.
      + exact Hterm.
      + apply reachable_trans with (step s).
        * apply reach_step with s; [apply reach_refl | reflexivity].
        * exact Hreach.
  Defined.

  Definition run_wf (s : State) : { s' : State | terminal s' /\ Reachable s s' } :=
    Fix wf_step_rel_wf (fun s => { s' : State | terminal s' /\ Reachable s s' }) run_wf_F s.

  Theorem run_wf_correct
    : forall s, let (s', _) := run_wf s in terminal s' /\ Reachable s s'.
  Proof.
    intro s.
    destruct (run_wf s) as [s' [Ht Hr]].
    split; assumption.
  Qed.

  Definition state_verse_consistent (s : State) : Prop :=
    on_wall s <= starting_count s /\ starting_count s <= 99.

  Theorem initial_verse_consistent
    : forall n, n <= 99 -> state_verse_consistent (initial n).
  Proof.
    intros n Hle; unfold state_verse_consistent, initial; simpl; lia.
  Qed.

  Theorem step_preserves_verse_consistency
    : forall s, state_verse_consistent s -> state_verse_consistent (step s).
  Proof.
    intros [w p st] [Hle Hst]; unfold state_verse_consistent, step in *; simpl in *.
    destruct w; simpl; lia.
  Qed.

  Theorem reachable_verse_consistent
    : forall n s, n <= 99 -> Reachable (initial n) s -> state_verse_consistent s.
  Proof.
    intros n s Hn Hreach.
    induction Hreach.
    - apply initial_verse_consistent; exact Hn.
    - rewrite H; apply step_preserves_verse_consistency; exact IHHreach.
  Qed.

  Definition valid_verse_number (start n : nat) : Prop :=
    n <= start /\ start <= 99.

  Theorem reachable_valid_verse
    : forall n s, n <= 99 -> Reachable (initial n) s ->
        valid_verse_number (starting_count s) (on_wall s).
  Proof.
    intros n s Hn Hreach.
    pose proof (reachable_verse_consistent n s Hn Hreach) as [Hle Hst].
    pose proof (reachable_preserves_starting_count (initial n) s Hreach) as Heq.
    unfold valid_verse_number, initial in *; simpl in *.
    rewrite Heq; split; lia.
  Qed.

  Theorem current_verse_well_defined
    : forall n s, n <= 99 -> Reachable (initial n) s ->
        exists v, current_verse s = v /\
                  (on_wall s > 0 -> exists k, on_wall s = S k /\
                   v = count_phrase (on_wall s) ++ " of beer on the wall, " ++
                       count_phrase (on_wall s) ++ " of beer. " ++
                       "Take one down and pass it around, " ++
                       count_phrase k ++ " of beer on the wall.") /\
                  (on_wall s = 0 ->
                   v = "No more bottles of beer on the wall, no more bottles of beer. " ++
                       "Go to the store and buy some more, " ++
                       nat_to_string (starting_count s) ++ " bottles of beer on the wall.").
  Proof.
    intros n s Hn Hreach.
    exists (current_verse s).
    split; [reflexivity|].
    split.
    - intro Hpos.
      destruct (on_wall s) eqn:Ew.
      + lia.
      + exists n0; split; [reflexivity|].
        unfold current_verse, verse.
        rewrite Ew; reflexivity.
    - intro Hz.
      unfold current_verse, verse.
      rewrite Hz; reflexivity.
  Qed.

  Theorem step_advances_verse
    : forall s, ~ terminal s ->
        exists k, on_wall s = S k /\ on_wall (step s) = k /\
                  current_verse (step s) = verse (starting_count s) k.
  Proof.
    intros [w p st] Hnt.
    unfold terminal in Hnt; simpl in Hnt.
    destruct w.
    - contradict Hnt; reflexivity.
    - exists w.
      split; [reflexivity|].
      split; [reflexivity|].
      unfold current_verse, step; simpl; reflexivity.
  Qed.

  Lemma full_song_aux_last
    : forall start m acc, last (full_song_aux start m acc) "" = verse start 0.
  Proof.
    intros start; induction m; intro acc; simpl.
    - rewrite last_last; reflexivity.
    - apply IHm.
  Qed.

  Theorem final_verse_is_zero
    : forall n, last (full_song n) "" = verse n 0.
  Proof.
    intro n; unfold full_song; apply full_song_aux_last.
  Qed.

  Theorem song_ends_with_store_trip
    : forall n, exists prefix,
        last (full_song n) "" =
        prefix ++ "Go to the store and buy some more, " ++
        nat_to_string n ++ " bottles of beer on the wall.".
  Proof.
    intro n.
    exists "No more bottles of beer on the wall, no more bottles of beer. ".
    rewrite final_verse_is_zero.
    reflexivity.
  Qed.

  Theorem trajectory_verses_match
    : forall n k, k <= n -> n <= 99 ->
        current_verse (run k (initial n)) = verse n (n - k).
  Proof.
    intros n k Hk Hn.
    unfold current_verse.
    rewrite run_preserves_starting_count.
    rewrite bisimulation by lia.
    unfold initial; simpl.
    reflexivity.
  Qed.

  Theorem full_trajectory_coverage
    : forall n, n <= 99 ->
        forall k, k <= n ->
          exists s, Reachable (initial n) s /\
                    on_wall s = n - k /\
                    current_verse s = verse n (n - k).
  Proof.
    intros n Hn k Hk.
    exists (run k (initial n)).
    split; [apply reachable_run|].
    split.
    - apply bisimulation; lia.
    - apply trajectory_verses_match; lia.
  Qed.

  Theorem trajectory_full_song_correspondence
    : forall k, k <= 99 ->
        current_verse (run k (initial 99)) = nth k (full_song 99) "".
  Proof.
    intros k Hk.
    rewrite trajectory_verses_match by lia.
    rewrite full_song_nth by lia.
    reflexivity.
  Qed.

End Bottles.
