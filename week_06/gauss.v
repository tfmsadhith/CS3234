Require Import Arith Nat Bool.
Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.


(* Returns the sum of integers from 1 to n *)

Fixpoint sum_int (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n + sum_int n'
  end.


Lemma fold_unfold_sum_int_0:
  sum_int 0 = 0.

Proof.
  fold_unfold_tactic sum_int.
Qed.

Lemma fold_unfold_sum_int_S:
  forall n' : nat,
    sum_int (S n') = (S n') + sum_int n'. 

Proof.
  fold_unfold_tactic sum_int.
Qed.

  
Theorem gauss_sum :
  forall n : nat,
    (n * (S n)) / 2 = sum_int (n).

Proof.
  intro n.
  induction n as [ | n' IHn'].

  * rewrite -> fold_unfold_sum_int_0.
    simpl.
    reflexivity.

  * rewrite -> fold_unfold_sum_int_S.
    rewrite <- (Nat.add_1_r (S n')).
    rewrite <- (Nat.add_1_r n') at 2.
    rewrite <- (Nat.add_assoc n' 1 1).
    rewrite -> (Nat.add_1_l 1).
    rewrite -> (Nat.mul_add_distr_l (S n') n' 2).
    rewrite -> (Nat.mul_comm (S n') n').
    rewrite -> (Nat.add_comm (n' * S n') (S n' * 2)).
    Search ((_ + _) / _).

    rewrite -> (Nat.div_add_l (S n') 2 (n' * S n')).
    rewrite -> IHn'.
    reflexivity.
    discriminate.
Qed.

