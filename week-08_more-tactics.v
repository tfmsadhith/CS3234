(* week-08_more-tactics.v *)
(* LPP 2024 - CS3234 2023-2024, Sem2 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 15 Mar 2024 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

(* ********** *)

Lemma foo :
  forall n : nat,
    1 + n = n + 1.
Proof.
  intro n.
  simpl.
(*
  n : nat
  ============================
  S n = n + 1
*)
Abort.

Print Nat.add.
(*
Nat.add = fix add (n m : nat) {struct n} : nat := match n with
                                                  | 0 => m
                                                  | S p => S (add p m)
                                                  end
     : nat -> nat -> nat
*)

Definition fold_unfold_add_O := Nat.add_0_l.
Definition fold_unfold_add_S := plus_Sn_m.

Lemma foo :
  forall n : nat,
    1 + n = n + 1.
Proof.
  intro n.
  rewrite -> (fold_unfold_add_S 0 n).
  rewrite -> (fold_unfold_add_O n).
(*
  n : nat
  ============================
  S n = n + 1
*)
  rewrite <- (plus_n_Sm n 0).
  rewrite -> (Nat.add_0_r n).
  reflexivity.
Qed.

(* ********** *)

(* Exercise 01 *)

(* ***** *)

Definition test_fac (candidate: nat -> nat) : bool :=
  (candidate 0 =? 1)
  &&
  (candidate 1 =? 1 * 1)
  &&
  (candidate 2 =? 1 * 1 * 2)
  &&
  (candidate 3 =? 1 * 1 * 2 * 3)
  &&
  (candidate 4 =? 1 * 1 * 2 * 3 * 4)
  &&
  (candidate 5 =? 1 * 1 * 2 * 3 * 4 * 5)
  (* etc. *)
  .

Fixpoint fac (n : nat) : nat :=
  match n with
  | O =>
    1
  | S n' =>
    n * fac n'
  end.

Compute (test_fac fac).

Lemma fold_unfold_fac_O :
  fac 0 =
  1.
Proof.
  fold_unfold_tactic fac.
Qed.

Lemma fold_unfold_fac_S :
  forall n' : nat,
    fac (S n') =
    S n' * fac n'.
Proof.
  fold_unfold_tactic fac.
Qed.

(* ***** *)

Definition test_exp2 (candidate: nat -> nat) : bool :=
  (candidate 0 =? 1)
  &&
  (candidate 1 =? 2 * 1)
  &&
  (candidate 2 =? 2 * 2 * 1)
  &&
  (candidate 3 =? 2 * 2 * 2 * 1)
  &&
  (candidate 4 =? 2 * 2 * 2 * 2 * 1)
  &&
  (candidate 5 =? 2 * 2 * 2 * 2 * 2 * 1)
  (* etc. *)
  .

Fixpoint exp2 (n : nat) : nat :=
  match n with
  | O =>
    1
  | S n' =>
    2 * exp2 n'
  end.

Compute (test_exp2 exp2).

Lemma fold_unfold_exp2_O :
  exp2 0 =
  1.
Proof.
  fold_unfold_tactic exp2.
Qed.

Lemma fold_unfold_exp2_S :
  forall n' : nat,
    exp2 (S n') =
    2 * exp2 n'.
Proof.
  fold_unfold_tactic exp2.
Qed.

(* ***** *)

(*
Property on_the_relative_growth_of_the_powers_of_two_and_of_the_factorial_numbers :
  forall n : nat,
    ...
Abort.
*)

(* ********** *)

(* end of week-08_more-tactics.v *)
