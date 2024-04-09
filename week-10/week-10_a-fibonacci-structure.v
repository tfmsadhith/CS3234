(* week-10_a-fibonacci-structure.v *)
(* LPP 2024 - CS3233 2023-2024, Sem2 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 04 Apr 2024 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith.

(* ********** *)

(* The Fibonacci structure: *)

Definition Fibonacci (career : Type)
                     (add : career -> career -> career)
                     (fib_0 : career)
                     (fib_1 : career)
                     (fib : nat -> career) :=
  (fib 0 = fib_0)
  /\
  (fib 1 = fib_1)
  /\
  (forall n : nat,
     fib (S (S n)) = add (fib n) (fib (S n))).

(* ********** *)

(* The standard Fibonacci function over nats: *)

Fixpoint fib_nat (n : nat) : nat :=
  match n with
    0 => 0
  | S n' => match n' with
              0 => 1
            | S n'' => fib_nat n'' + fib_nat n'
            end
  end.

(* The standard fold-unfold lemmas: *)

Lemma fold_unfold_fib_nat_O :
  fib_nat 0 =
  0.
Proof.
  fold_unfold_tactic fib_nat.
Qed.

Lemma fold_unfold_fib_nat_S :
  forall n' : nat,
    fib_nat (S n') =
    match n' with
      0 => 1
    | S n'' => fib_nat n'' + fib_nat n'
    end.
Proof.
  fold_unfold_tactic fib_nat.
Qed.

(* Two dedicated fold-unfold lemmas: *)

Lemma fold_unfold_fib_nat_1 :
  fib_nat 1 =
  1.
Proof.
  exact (fold_unfold_fib_nat_S 0).
Qed.

Lemma fold_unfold_fib_nat_SS :
  forall n'' : nat,
    fib_nat (S (S n'')) =
    fib_nat n'' + fib_nat (S n'').
Proof.
  intro n''.
  exact (fold_unfold_fib_nat_S (S n'')).
Qed.

(* The standard Fibonacci function over nats fits the Fibonacci structure: *)

Theorem fib_nat_fits_Fibonacci :
  Fibonacci nat Nat.add 0 1 fib_nat.
Proof.
  unfold Fibonacci.
  split.
    exact fold_unfold_fib_nat_O.
  split.
    exact fold_unfold_fib_nat_1.
  exact fold_unfold_fib_nat_SS.
Qed.

(* ********** *)

(* Computing Fibonacci numbers by exponentiating a 2x2 matrix of nats: *)

Inductive m22_nat : Type :=
  | M22_nat : nat -> nat -> nat -> nat -> m22_nat.

Property componential_equality_m22_nat :
  forall x11 x12 x21 x22 y11 y12 y21 y22 : nat,
    M22_nat x11 x12
            x21 x22 =
    M22_nat y11 y12
            y21 y22
    <->
    x11 = y11 /\ x12 = y12 /\ x21 = y21 /\ x22 = y22.
Proof.
  intros x11 x12 x21 x22 y11 y12 y21 y22.
  split.

  - intro H_tmp.
    injection H_tmp as H11 H12 H21 H22.
    rewrite -> H11.
    rewrite -> H12.
    rewrite -> H21.
    rewrite -> H22.
    split; [reflexivity | split; [reflexivity | split; [reflexivity | reflexivity]]].

  - intros [H11 [H12 [H21 H22]]].
    rewrite -> H11.
    rewrite -> H12.
    rewrite -> H21.
    rewrite -> H22.
    reflexivity.
Qed.

Definition zero_m22_nat := M22_nat 0 0
                                   0 0.

Definition add_m22_nat (x y : m22_nat) : m22_nat :=
  match (x, y) with
    (M22_nat x11 x12
             x21 x22,
     M22_nat y11 y12
             y21 y22) =>
    M22_nat (x11 + y11) (x12 + y12)
            (x21 + y21) (x22 + y22)
  end.

Lemma add_m22_nat_assoc :
  forall x y z : m22_nat,
    add_m22_nat x (add_m22_nat y z) =
    add_m22_nat (add_m22_nat x y) z.
Proof.
  intros [x11 x12
          x21 x22]
         [y11 y12
          y21 y22]
         [z11 z12
          z21 z22].
  unfold add_m22_nat.
  rewrite ->4 Nat.add_assoc.
  reflexivity.
Qed.

Lemma add_m22_nat_0_l :
  forall x : m22_nat,
    add_m22_nat zero_m22_nat x = 
    x.
Proof.
  intros [x11 x12
          x21 x22].
  unfold add_m22_nat, zero_m22_nat.
  rewrite ->4 Nat.add_0_l.
  reflexivity.
Qed.

Lemma add_m22_nat_0_r :
  forall x : m22_nat,
    add_m22_nat x zero_m22_nat =
    x.
Proof.
  intros [x11 x12
          x21 x22].
  unfold add_m22_nat, zero_m22_nat.
  rewrite ->4 Nat.add_0_r.
  reflexivity.
Qed.

Definition one_m22_nat := M22_nat 1 0 
                                  0 1.

Definition mul_m22_nat (x y : m22_nat) : m22_nat :=
  match (x, y) with
    (M22_nat x11 x12
             x21 x22,
     M22_nat y11 y12
             y21 y22) =>
    (M22_nat (x11 * y11 + x12 * y21) (x11 * y12 + x12 * y22)
             (x21 * y11 + x22 * y21) (x21 * y12 + x22 * y22))
  end.

Lemma mul_m22_nat_assoc :
  forall x y z : m22_nat,
    mul_m22_nat x (mul_m22_nat y z) =
    mul_m22_nat (mul_m22_nat x y) z.
Proof.
Admitted.

Lemma mul_m22_nat_1_l :
  forall x : m22_nat,
    mul_m22_nat one_m22_nat x = x.
Proof.
  intros [x11 x12
          x21 x22].
  unfold mul_m22_nat, one_m22_nat.
  rewrite ->4 Nat.mul_0_l.
  rewrite ->2 Nat.add_0_l.
  rewrite ->2 Nat.add_0_r.
  rewrite ->4 Nat.mul_1_l.
  reflexivity.
Qed.

Lemma mul_m22_nat_1_r :
  forall x : m22_nat,
    mul_m22_nat x one_m22_nat =
    x.
Proof.
  intros [x11 x12
          x21 x22].
  unfold mul_m22_nat, one_m22_nat.
  rewrite ->4 Nat.mul_0_r.
  rewrite ->2 Nat.add_0_r.
  rewrite ->2 Nat.add_0_l.
  rewrite ->4 Nat.mul_1_r.
  reflexivity.
Qed.

Lemma mul_m22_nat_0_l :
  forall x : m22_nat,
    mul_m22_nat zero_m22_nat x =
    zero_m22_nat.
Proof.
  intros [x11 x12
          x21 x22].
  unfold mul_m22_nat, zero_m22_nat.
  rewrite ->4 Nat.mul_0_l.
  rewrite -> Nat.add_0_l.
  reflexivity.
Qed.

Lemma mul_m22_0_r :
  forall x : m22_nat,
    mul_m22_nat x zero_m22_nat =
    zero_m22_nat.
Proof.
  intros [x11 x12
          x21 x22].
  unfold mul_m22_nat, zero_m22_nat.
  rewrite ->4 Nat.mul_0_r.
  rewrite -> Nat.add_0_r.
  reflexivity.
Qed.

Fixpoint power_m22_nat (x : m22_nat) (n : nat) : m22_nat:=
  match n with
    0 =>
    one_m22_nat
  | S n' =>
    mul_m22_nat x (power_m22_nat x n')
  end.

Lemma fold_unfold_power_m22_nat_O :
  forall x : m22_nat,
    power_m22_nat x 0 =
    one_m22_nat.
Proof.
  fold_unfold_tactic power_m22_nat.
Qed.

Lemma fold_unfold_power_m22_nat_S :
  forall (x : m22_nat)
         (n' : nat),
    power_m22_nat x (S n') =
    mul_m22_nat x (power_m22_nat x n').
Proof.
  fold_unfold_tactic power_m22_nat.
Qed.

Property about_exponentiating_2x2_matrices_of_nats :
  forall (x : m22_nat)
         (p q : nat),
    power_m22_nat x (p + q) =
    mul_m22_nat (power_m22_nat x p) (power_m22_nat x q).
Proof.
  intros x p.
  induction p as [ | p' IHp']; intro q.

  - rewrite -> Nat.add_0_l.
    rewrite -> fold_unfold_power_m22_nat_O.
    rewrite -> mul_m22_nat_1_l.
    reflexivity.

  - rewrite -> plus_Sn_m.
    rewrite -> fold_unfold_power_m22_nat_S.
    rewrite -> (IHp' q).
    rewrite -> fold_unfold_power_m22_nat_S.
    apply mul_m22_nat_assoc.
Qed.

(* The Fibonacci matrix: *)

Definition F_nat := M22_nat 0 1 
                            1 1.

Definition F_nat_0 := power_m22_nat F_nat 0.
Compute F_nat_0.  (* = M22_nat 1 0 0 1 *)
Definition F_nat_1 := power_m22_nat F_nat 1.
Compute F_nat_1.  (* = M22_nat 0 1 1 1 *)
Definition F_nat_2 := power_m22_nat F_nat 2.
Compute F_nat_2.  (* = M22_nat 1 1 1 2 *)
Definition F_nat_3 := power_m22_nat F_nat 3.
Compute F_nat_3.  (* = M22_nat 1 2 2 3 *)
Definition F_nat_4 := power_m22_nat F_nat 4.
Compute F_nat_4.  (* = M22_nat 2 3 3 5 *)

Proposition about_exponentiating_F_nat :
  forall n : nat,
    power_m22_nat F_nat (S n) =
    M22_nat (fib_nat n)     (fib_nat (S n))
            (fib_nat (S n)) (fib_nat (S (S n))).
Proof.
  intro n.
  induction n as [ | n' IHn'].

  - rewrite -> fold_unfold_power_m22_nat_S.
    rewrite -> fold_unfold_power_m22_nat_O.
    rewrite -> mul_m22_nat_1_r.
    unfold F_nat.
    rewrite -> fold_unfold_fib_nat_SS.
    rewrite -> fold_unfold_fib_nat_O.
    rewrite -> fold_unfold_fib_nat_1.
    rewrite -> Nat.add_0_l.
    reflexivity.

  - rewrite -> fold_unfold_power_m22_nat_S.
    rewrite -> IHn'.
    unfold F_nat.
    unfold mul_m22_nat.
    rewrite -> Nat.mul_0_l.
    rewrite -> Nat.add_0_l.
    rewrite -> Nat.mul_1_l.
    rewrite -> Nat.mul_0_l.
    rewrite -> Nat.add_0_l.
    rewrite -> Nat.mul_1_l.
    rewrite -> Nat.mul_1_l.
    rewrite <- fold_unfold_fib_nat_SS.
    rewrite <- fold_unfold_fib_nat_SS.
    reflexivity.
Qed.

(* The following property is a corollary of
     Property about_exponentiating_2x2_matrices_of_nats
   and
     Proposition about_exponentiating_F_nat
   about the first cell of
     mult_m22 (power_m22_nat F_nat (S p)) (power_m22_nat F_nat (S q))
   for any nat p and q:
*)

Corollary an_identity_about_Fibonacci_numbers :
  forall p q : nat,
    fib_nat (S (p + q)) =
    fib_nat p * fib_nat q + fib_nat (S p) * fib_nat (S q).
Proof.
Abort.

(* ********** *)

(* A perhaps unexpected property: *)

Property as_luck_has_it :
  forall n : nat,
    power_m22_nat F_nat (S (S n)) =
    add_m22_nat (power_m22_nat F_nat n) (power_m22_nat F_nat (S n)).
Proof.
Admitted.

Definition fib_m22_nat (n : nat) : m22_nat :=
  power_m22_nat F_nat n.

Compute fib_m22_nat 0. (* = M22_nat 1 0 0 1 *)
Compute fib_m22_nat 1. (* = M22_nat 0 1 1 1 *)
Compute fib_m22_nat 2. (* = M22_nat 1 1 1 2 *)
Compute fib_m22_nat 3. (* = M22_nat 1 2 2 3 *)

(* Let's make our own luck with fortuitous fold_unfold_lemmas: *)

Lemma fold_unfold_fib_m22_nat_0 :
    fib_m22_nat 0 =
    one_m22_nat.
Proof.
  unfold fib_m22_nat.
  apply fold_unfold_power_m22_nat_O.
Qed.

Lemma fold_unfold_fib_m22_nat_1 :
  fib_m22_nat 1 =
  F_nat.
Proof.
  unfold fib_m22_nat.
  rewrite -> fold_unfold_power_m22_nat_S.
  rewrite -> fold_unfold_power_m22_nat_O.
  apply mul_m22_nat_1_r.
Qed.

Lemma fold_unfold_fib_m22_nat_SS :
  forall (n : nat),
    fib_m22_nat (S (S n)) =
    add_m22_nat (fib_m22_nat n) (fib_m22_nat (S n)).
Proof.
  intro n.
  unfold fib_m22_nat.
  apply as_luck_has_it.
Qed.

(* So successive exponents of F_nat fit the Fibonacci structure: *)

Theorem fib_m22_nat_fits_Fibonacci :
  Fibonacci m22_nat add_m22_nat one_m22_nat F_nat fib_m22_nat.
Proof.
  unfold Fibonacci.
  split.
    exact fold_unfold_fib_m22_nat_0.
  split.
    exact fold_unfold_fib_m22_nat_1.
  exact fold_unfold_fib_m22_nat_SS.
Qed.

(* Can this property be generalized? *)

(* ********** *)

(* Polymorphic 2x2 matrices: *)

Inductive pm22 (V : Type) :=
  | PM22 : V -> V -> V -> V -> pm22 V.

(* ***** *)

(* For example, 2x2 matrices of nats: *)

Check (pm22 nat).

(* For example, 2x2 matrices of 2x2 matrices of nats: *)

Check (pm22 (pm22 nat)).

(* ***** *)

Definition zero_pm22 (V : Type) (zero : V) : pm22 V :=
  PM22 V
       zero zero
       zero zero.

Definition add_pm22 (V : Type) (add : V -> V -> V) (x y : pm22 V) : pm22 V :=
  match (x, y) with
    (PM22 _
          x11 x12
          x21 x22,
     PM22 _
          y11 y12
          y21 y22) =>
    PM22 V
         (add x11 y11) (add x12 y12)
         (add x21 y21) (add x22 y22)
  end.

Property add_pm22_assoc :
  forall (V : Type)
         (add : V -> V -> V),
    (forall x y z : V,
        add x (add y z) = add (add x y) z) ->
    forall x y z : pm22 V,
      add_pm22 V add x (add_pm22 V add y z) =
      add_pm22 V add (add_pm22 V add x y) z.
Proof.
  intros V add H_add_assoc
         [x11 x12
          x21 x22]
         [y11 y12
          y21 y22]
         [z11 z12
          z21 z22].
  unfold add_pm22.
  rewrite ->4 H_add_assoc.
  reflexivity.
Qed.

Property add_pm22_0_l :
  forall (V : Type)
         (add : V -> V -> V)
         (zero : V),
    (forall v : V,
        add zero v = v) ->
    forall x : pm22 V,
      add_pm22 V add (zero_pm22 V zero) x =
      x.
Proof.
  intros V add zero H_add_0_l
         [x11 x12
          x21 x22].
  unfold add_pm22, zero_pm22.
  rewrite ->4 H_add_0_l.
  reflexivity.
Qed.

Property add_pm22_0_r :
  forall (V : Type)
         (add : V -> V -> V)
         (zero : V),
    (forall v : V,
        add v zero = v) ->
    forall x : pm22 V,
      add_pm22 V add x (zero_pm22 V zero) =
      x.
Proof.
  intros V add zero H_add_0_r
         [x11 x12
          x21 x22].
  unfold add_pm22, zero_pm22.
  rewrite ->4 H_add_0_r.
  reflexivity.
Qed.

Definition one_pm22 (V : Type) (zero : V) (one : V) : pm22 V :=
  PM22 V
       one zero
       zero one.

Definition mul_pm22 (V : Type) (add : V -> V -> V) (mul : V -> V -> V) (x y : pm22 V) : pm22 V :=
  match (x, y) with
    (PM22 _
          x11 x12
          x21 x22,
     PM22 _
          y11 y12
          y21 y22) =>
    PM22 V
         (add (mul x11 y11) (mul x12 y21)) (add (mul x11 y12) (mul x12 y22))
         (add (mul x21 y11) (mul x22 y21)) (add (mul x21 y12) (mul x22 y22))
  end.

Property mul_pm22_assoc :
  forall (V : Type)
         (add : V -> V -> V),
    (forall x y z : V,
        add x (add y z) = add (add x y) z) ->
    (forall x y : V,
        add x y = add y x) ->
    forall mul : V -> V -> V,
      (forall x y z : V,
          mul x (mul y z) = mul (mul x y) z) ->
      (forall x y z : V,
          mul x (add y z) = add (mul x y) (mul x z)) ->
      (forall x y z : V,
          mul (add x y) z = add (mul x z) (mul y z)) ->
      forall x y z : pm22 V,
        mul_pm22 V add mul x (mul_pm22 V add mul y z) =
        mul_pm22 V add mul (mul_pm22 V add mul x y) z.
Proof.
Admitted.

Property mul_pm22_1_l :
  forall (V : Type)
         (add : V -> V -> V)
         (mul : V -> V -> V)
         (zero : V),
    (forall v : V,
        add zero v = v) ->
    (forall v : V,
        add v zero = v) ->
    (forall v : V,
        mul zero v = zero) ->
    forall (one : V),
      (forall v : V,
          mul one v = v) ->
      forall x : pm22 V,
        mul_pm22 V add mul (one_pm22 V zero one) x =
        x.
Proof.
  intros V add mul zero H_add_0_l H_add_0_r H_mul_0_l one H_mul_1_l
         [x11 x12
          x21 x22].
  unfold mul_pm22, one_pm22.
  rewrite ->4 H_mul_0_l.
  rewrite ->2 H_add_0_l.
  rewrite ->2 H_add_0_r.
  rewrite ->4 H_mul_1_l.
  reflexivity.
Qed.

Property mul_pm22_1_r :
  forall (V : Type)
         (add : V -> V -> V)
         (mul : V -> V -> V)
         (zero : V),
    (forall v : V,
        add zero v = v) ->
    (forall v : V,
        add v zero = v) ->
    (forall v : V,
        mul v zero = zero) ->
    forall (one : V),
      (forall v : V,
          mul v one = v) ->
  forall x : pm22 V,
    mul_pm22 V add mul x (one_pm22 V zero one) =
    x.
Proof.
  intros V add mul zero H_add_0_l H_add_0_r H_mul_0_r one H_mul_1_r
         [x11 x12
          x21 x22].
  unfold mul_pm22, one_pm22.
  rewrite ->4 H_mul_0_r.
  rewrite ->2 H_add_0_l.
  rewrite ->2 H_add_0_r.
  rewrite ->4 H_mul_1_r.
  reflexivity.
Qed.

Property mul_pm22_0_l :
  forall (V : Type)
         (add : V -> V -> V)
         (mul : V -> V -> V)
         (zero : V),
    (forall v : V,
        add zero v = v) ->
    (forall v : V,
        mul zero v = zero) ->
    forall x : pm22 V,
      mul_pm22 V add mul (zero_pm22 V zero) x =
      zero_pm22 V zero.
Proof.
  intros V add mul zero H_add_0_l H_mul_0_l
         [x11 x12
          x21 x22].
  unfold mul_pm22, zero_pm22.
  rewrite ->4 H_mul_0_l.
  rewrite -> H_add_0_l.
  reflexivity.
Qed.

Property mul_pm22_0_r :
  forall (V : Type)
         (add : V -> V -> V)
         (mul : V -> V -> V)
         (zero : V),
    (forall v : V,
        add v zero = v) ->
    (forall v : V,
        mul v zero = zero) ->
  forall x : pm22 V,
    mul_pm22 V add mul x (zero_pm22 V zero) =
    zero_pm22 V zero.
Proof.
  intros V add mul zero H_add_0_r H_mul_0_r
         [x11 x12
          x21 x22].
  unfold mul_pm22, zero_pm22.
  rewrite ->4 H_mul_0_r.
  rewrite -> H_add_0_r.
  reflexivity.
Qed.

(* power_pm22 : forall V : Type, (V -> V -> V) -> (V -> V -> V) -> V -> V -> pm22 V -> nat -> pm22 V *)
Fixpoint power_pm22 (V : Type) (add mul : V -> V -> V) (zero one : V) (x : pm22 V) (n : nat) : pm22 V :=
  match n with
    0 =>
    one_pm22 V zero one
  | S n' =>
    mul_pm22 V add mul x (power_pm22 V add mul zero one x n')
  end.

Lemma fold_unfold_power_pm22_O :
  forall (V : Type)
         (add mul : V -> V -> V)
         (zero one : V)
         (x : pm22 V),
    power_pm22 V add mul zero one x 0 =
    one_pm22 V zero one.
Proof.
  fold_unfold_tactic power_pm22.
Qed.

Lemma fold_unfold_power_pm22_S :
  forall (V : Type)
         (add mul : V -> V -> V)
         (zero one : V)
         (x : pm22 V)
         (n' : nat),
    power_pm22 V add mul zero one x (S n') =
    mul_pm22 V add mul x (power_pm22 V add mul zero one x n').
Proof.
  fold_unfold_tactic power_pm22.
Qed.

Definition F_pm22 (V : Type) (zero : V) (one : V) : pm22 V :=
  PM22 V
       zero one
        one one.

Definition fib_pm22 (V : Type) (add mul : V -> V -> V) (zero one : V) (n : nat) : pm22 V :=
  power_pm22 V add mul zero one (F_pm22 V zero one) n.

Lemma fold_unfold_fib_pm22_0 :
  forall (V : Type)
         (add mul : V -> V -> V)
         (zero one : V),
    fib_pm22 V add mul zero one 0 =
    one_pm22 V zero one.
Proof.
  intros V add mul zero one.
  unfold fib_pm22.
  exact (fold_unfold_power_pm22_O V add mul zero one (F_pm22 V zero one)).
Qed.

Lemma fold_unfold_fib_pm22_1 :
  forall (V : Type)
         (add mul : V -> V -> V)
         (zero : V),
    (forall v : V,
        add zero v = v) ->
    (forall v : V,
        add v zero = v) ->
    (forall v : V,
        mul v zero = zero) ->
    forall (one : V),
      (forall v : V,
          mul v one = v) ->
        fib_pm22 V add mul zero one 1 =
        F_pm22 V zero one.
Proof.
  intros V add mul zero H_add_0_l H_add_0_r H_mul_0_r one H_mul_1_r.
  unfold fib_pm22.
  rewrite -> fold_unfold_power_pm22_S.
  rewrite -> fold_unfold_power_pm22_O.
  rewrite -> (mul_pm22_1_r V add mul zero H_add_0_l H_add_0_r H_mul_0_r one H_mul_1_r).
  reflexivity.
Qed.

Lemma fold_unfold_fib_pm22_SS :
  forall (V : Type)
         (add mul : V -> V -> V)
         (zero : V),
    (forall v : V,
        add zero v = v) ->
    (forall v : V,
        mul zero v = zero) ->
    forall (one : V),
      (forall v : V,
          mul one v = v) ->
      forall (n : nat),
        fib_pm22 V add mul zero one (S (S n)) =
        add_pm22 V
                 add
                 (fib_pm22 V add mul zero one n)
                 (fib_pm22 V add mul zero one (S n)).
Proof.
  intros V add mul zero H_add_0_l H_mul_0_l one H_mul_1_l n.
  unfold fib_pm22.
  rewrite -> fold_unfold_power_pm22_S.
  rewrite -> fold_unfold_power_pm22_S.
  destruct (power_pm22 V add mul zero one (F_pm22 V zero one) n) as [x11 x12
                                                                     x21 x22] eqn:H_the_guy.
  unfold F_pm22.
  unfold mul_pm22, add_pm22.
  repeat (rewrite -> H_mul_0_l).
  repeat (rewrite -> H_mul_1_l).
  repeat (rewrite -> H_add_0_l).
  reflexivity.
Qed.

Theorem fib_pm22_fits_Fibonacci :
  forall (V : Type)
         (zero one : V)
         (add mul : V -> V -> V),
    (forall v : V,
        add zero v = v) ->
    (forall v : V,
        add v zero = v) ->
    (forall v : V,
        mul zero v = zero) ->
    (forall v : V,
        mul v zero = zero) ->
    (forall v : V,
        mul one v = v) ->
    (forall v : V,
        mul v one = v) ->
    Fibonacci (pm22 V)
              (add_pm22 V add)
              (one_pm22 V zero one)
              (F_pm22 V zero one)
              (fib_pm22 V add mul zero one).
Proof.
  intros V zero one add mul add_0_l add_0_r mul_0_l mul_0_r mul_1_l mul_1_r.
  unfold Fibonacci.
  split.
    exact (fold_unfold_fib_pm22_0 V add mul zero one).
  split.
    exact (fold_unfold_fib_pm22_1 V add mul zero add_0_l add_0_r mul_0_r one mul_1_r).
  exact (fold_unfold_fib_pm22_SS V add mul zero add_0_l mul_0_l one mul_1_l).
Qed.

(* ********** *)

(* Revisiting 2x2 matrices of nats: *)

Definition pm22_nat := pm22 nat.

Definition zero_pm22_nat := zero_pm22 nat 0.

Definition add_pm22_nat := add_pm22 nat Nat.add.

Lemma add_pm22_nat_assoc :
  forall x y z : pm22_nat,
    add_pm22_nat x (add_pm22_nat y z) =
    add_pm22_nat (add_pm22_nat x y) z.
Proof.
  exact (add_pm22_assoc nat Nat.add Nat.add_assoc).
Qed.

Lemma add_pm22_nat_0_l :
  forall x : pm22_nat,
    add_pm22_nat zero_pm22_nat x =
    x.
Proof.
  exact (add_pm22_0_l nat Nat.add 0 Nat.add_0_l).
Qed.

Lemma add_pm22_nat_0_r :
  forall x : pm22_nat,
    add_pm22_nat x zero_pm22_nat =
    x.
Proof.
  exact (add_pm22_0_r nat Nat.add 0 Nat.add_0_r).
Qed.

Definition one_pm22_nat := one_pm22 nat 0 1.

Definition mul_pm22_nat := mul_pm22 nat Nat.add Nat.mul.

Lemma mul_pm22_nat_assoc :
  forall x y z : pm22_nat,
    mul_pm22_nat x (mul_pm22_nat y z) =
    mul_pm22_nat (mul_pm22_nat x y) z.
Proof.
  exact (mul_pm22_assoc nat Nat.add Nat.add_assoc Nat.add_comm Nat.mul Nat.mul_assoc Nat.mul_add_distr_l Nat.mul_add_distr_r).
Qed.

Lemma mul_pm22_nat_1_l :
  forall x : pm22_nat,
    mul_pm22_nat one_pm22_nat x =
    x.
Proof.
  exact (mul_pm22_1_l nat Nat.add Nat.mul 0 Nat.add_0_l Nat.add_0_r Nat.mul_0_l 1 Nat.mul_1_l).
Qed.

Lemma mul_pm22_nat_1_r :
  forall x : pm22_nat,
    mul_pm22_nat x one_pm22_nat =
    x.
Proof.
  exact (mul_pm22_1_r nat Nat.add Nat.mul 0 Nat.add_0_l Nat.add_0_r Nat.mul_0_r 1 Nat.mul_1_r).
Qed.

Lemma mul_pm22_nat_0_l :
  forall x : pm22_nat,
    mul_pm22_nat zero_pm22_nat x =
    zero_pm22_nat.
Proof.
  exact (mul_pm22_0_l nat Nat.add Nat.mul 0 Nat.add_0_l Nat.mul_0_l).
Qed.

Lemma mul_pm22_nat_0_r :
  forall x : pm22_nat,
    mul_pm22_nat x zero_pm22_nat =
    zero_pm22_nat.
Proof.
  exact (mul_pm22_0_r nat Nat.add Nat.mul 0 Nat.add_0_r Nat.mul_0_r).
Qed.

Definition power_pm22_nat := power_pm22 nat Nat.add Nat.mul 0 1.

Lemma fold_unfold_power_pm22_nat_O :
  forall x : pm22_nat,
    power_pm22_nat x 0 =
    one_pm22_nat.
Proof.
  exact (fold_unfold_power_pm22_O nat Nat.add Nat.mul 0 1).
Qed.

Lemma fold_unfold_power_pm22_nat_S :
  forall (x : pm22_nat)
         (n' : nat),
    power_pm22_nat x (S n') =
    mul_pm22_nat x (power_pm22_nat x n').
Proof.
  exact (fold_unfold_power_pm22_S nat Nat.add Nat.mul 0 1).
Qed.

Definition F_pm22_nat := F_pm22 nat 0 1.

(*
Definition fib_pm22_nat (n : nat) : pm22_nat :=
  power_pm22_nat F_pm22_nat n.
*)

Definition fib_pm22_nat := fib_pm22 nat Nat.add Nat.mul 0 1.

Lemma fold_unfold_fib_pm22_nat_0 :
  fib_pm22_nat 0 =
  one_pm22_nat.
Proof.
  exact (fold_unfold_fib_pm22_0 nat Nat.add Nat.mul 0 1).
Qed.

Lemma fold_unfold_fib_pm22_nat_1 :
  fib_pm22_nat 1 =
  F_pm22_nat.
Proof.
  exact (fold_unfold_fib_pm22_1 nat Nat.add Nat.mul 0 Nat.add_0_l Nat.add_0_r Nat.mul_0_r 1 Nat.mul_1_r).
Qed.

Lemma fold_unfold_fib_pm22_nat_SS :
  forall n : nat,
    fib_pm22_nat (S (S n)) =
    add_pm22_nat (fib_pm22_nat n) (fib_pm22_nat (S n)).
Proof.
  exact (fold_unfold_fib_pm22_SS nat Nat.add Nat.mul 0 Nat.add_0_l Nat.mul_0_l 1 Nat.mul_1_l).
Qed.

Corollary fib_pm22_nat_fits_Fibonacci :
  Fibonacci pm22_nat add_pm22_nat one_pm22_nat F_pm22_nat fib_pm22_nat.
Proof.
  exact (fib_pm22_fits_Fibonacci nat 0 1 Nat.add Nat.mul Nat.add_0_l Nat.add_0_r Nat.mul_0_l Nat.mul_0_r Nat.mul_1_l Nat.mul_1_r).
Qed.

(* ********** *)

Theorem about_layering :
  forall (V : Type)
         (zero one : V)
         (add mul : V -> V -> V),
    (forall v : V,
        add zero v = v) ->
    (forall v : V,
        add v zero = v) ->
    (forall v : V,
        mul zero v = zero) ->
    (forall v : V,
        mul v zero = zero) ->
    (forall v : V,
        mul one v = v) ->
    (forall v : V,
        mul v one = v) ->
    forall fib : nat -> V,
      Fibonacci V add zero one fib ->
      Fibonacci (pm22 V)
                (add_pm22 V add)
                (one_pm22 V (fib 0) (fib 1))
                (F_pm22 V (fib 0) (fib 1))
                (fib_pm22 V add mul (fib 0) (fib 1)).
Proof.
  intros V zero one add mul add_0_l add_0_r mul_0_l mul_0_r mul_1_l mul_1_r fib.
  unfold Fibonacci.
  intros [H_fib_0 [H_fib_1 H_fib_SS]].
  split.
  - rewrite -> fold_unfold_fib_pm22_0.
    reflexivity.
  - split.
    + rewrite -> H_fib_0.
      rewrite -> H_fib_1.
      Check (fold_unfold_fib_pm22_1 V add mul zero add_0_l add_0_r mul_0_r one mul_1_r).
      exact (fold_unfold_fib_pm22_1 V add mul zero add_0_l add_0_r mul_0_r one mul_1_r).
    + rewrite -> H_fib_0.
      rewrite -> H_fib_1.
      Check (fold_unfold_fib_pm22_SS V add mul zero add_0_l mul_0_l one mul_1_l).
      exact (fold_unfold_fib_pm22_SS V add mul zero add_0_l mul_0_l one mul_1_l).
Qed.

(* ********** *)

Proposition about_fib_pm22_nat :
  forall n : nat,
    fib_pm22_nat (S n) =
    PM22 nat
         (fib_nat n)     (fib_nat (S n))
         (fib_nat (S n)) (fib_nat (S (S n))).
Proof.
  intro n.
  unfold fib_pm22_nat.
  unfold fib_pm22.
  induction n as [ | n' IHn'].

  - rewrite -> fold_unfold_power_pm22_nat_S.
    rewrite -> fold_unfold_power_pm22_nat_O.
    rewrite -> mul_pm22_nat_1_r.
    unfold F_pm22_nat.
    unfold F_pm22.
    rewrite ->3 fold_unfold_fib_nat_S.
    rewrite -> fold_unfold_fib_nat_O.
    rewrite -> Nat.add_0_l.
    reflexivity.

  - rewrite -> fold_unfold_power_pm22_nat_S.
    unfold power_pm22_nat.
    rewrite -> IHn'.
    unfold mul_pm22_nat, mul_pm22, F_pm22_nat, F_pm22.
    rewrite -> Nat.mul_0_l.
    rewrite -> Nat.mul_1_l.
    rewrite -> Nat.add_0_l.
    rewrite -> Nat.mul_0_l.
    rewrite -> Nat.mul_1_l.
    rewrite -> Nat.add_0_l.
    rewrite -> Nat.mul_1_l.
    rewrite <-2 fold_unfold_fib_nat_SS.
    reflexivity.
Qed.

Compute (fib_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul) (zero_pm22 nat 0) (F_pm22 nat 0 1) 0).
(* = PM22 (pm22 nat) (PM22 nat 0 1 1 1) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 0 1 1 1) *)

Compute (fib_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul) (zero_pm22 nat 0) (F_pm22 nat 0 1) 1).
(* = PM22 (pm22 nat) (PM22 nat 0 0 0 0) (PM22 nat 1 1 1 2) (PM22 nat 1 1 1 2) (PM22 nat 1 1 1 2) *)

Compute (fib_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul) (zero_pm22 nat 0) (F_pm22 nat 0 1) 2).
(* = PM22 (pm22 nat) (PM22 nat 1 2 2 3) (PM22 nat 1 2 2 3) (PM22 nat 1 2 2 3) (PM22 nat 2 4 4 6) *)

Compute (fib_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul) (zero_pm22 nat 0) (F_pm22 nat 0 1) 3).
(* = PM22 (pm22 nat) (PM22 nat 2 3 3 5) (PM22 nat 4 6 6 10) (PM22 nat 4 6 6 10) (PM22 nat 6 9 9 15) *)

Compute (fib_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul) (one_pm22 nat 0 1) (F_pm22 nat 0 1) 0).
(* = PM22 (pm22 nat) (PM22 nat 0 1 1 1) (PM22 nat 1 0 0 1) (PM22 nat 1 0 0 1) (PM22 nat 0 1 1 1) *)

Compute (fib_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul) (one_pm22 nat 0 1) (F_pm22 nat 0 1) 1).
(* = PM22 (pm22 nat) (PM22 nat 0 2 2 2) (PM22 nat 2 1 1 3) (PM22 nat 1 2 2 3) (PM22 nat 1 2 2 3) *)

Compute (fib_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul) (one_pm22 nat 0 1) (F_pm22 nat 0 1) 2).
(* = PM22 (pm22 nat) (PM22 nat 2 5 5 7) (PM22 nat 4 4 4 8) (PM22 nat 4 5 5 9) (PM22 nat 3 6 6 9) *)

Compute (fib_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul) (one_pm22 nat 0 1) (F_pm22 nat 0 1) 3).
(* = PM22 (pm22 nat) (PM22 nat 7 14 14 21) (PM22 nat 10 13 13 23) (PM22 nat 10 16 16 26) (PM22 nat 10 17 17 27) *)

Property as_luck_has_it_too :
  forall n : nat,
    fib_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul) (zero_pm22 nat 0) (one_pm22 nat 0 1) (S n) =
    PM22 (pm22 nat)
         (PM22 nat (fib_nat n) 0 0 (fib_nat n))
         (PM22 nat (fib_nat (S n)) 0 0 (fib_nat (S n)))
         (PM22 nat (fib_nat (S n)) 0 0 (fib_nat (S n)))
         (PM22 nat (fib_nat (S (S n))) 0 0 (fib_nat (S (S n)))).
Proof.
  intro n.
  induction n as [ | n' IHn'].

  - rewrite -> (fold_unfold_fib_pm22_1 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul) (zero_pm22 nat 0) (add_pm22_0_l nat Nat.add 0 Nat.add_0_l) (add_pm22_0_r nat Nat.add 0 Nat.add_0_r) (mul_pm22_0_r nat Nat.add Nat.mul 0 Nat.add_0_r Nat.mul_0_r) (one_pm22 nat 0 1) (mul_pm22_1_r nat Nat.add Nat.mul 0 Nat.add_0_l Nat.add_0_r Nat.mul_0_r 1 Nat.mul_1_r)).
    unfold one_pm22.
    unfold zero_pm22.
    unfold F_pm22.
    repeat (rewrite -> fold_unfold_fib_nat_SS).
    repeat (rewrite -> fold_unfold_fib_nat_1).
    repeat (rewrite -> fold_unfold_fib_nat_O).
    repeat (rewrite -> Nat.add_0_l).
    reflexivity.

  - unfold fib_pm22.
    unfold fib_pm22 in IHn'.
    rewrite -> fold_unfold_power_pm22_S.
    rewrite -> IHn'.
    unfold F_pm22.
    unfold zero_pm22.
    unfold one_pm22.
    unfold mul_pm22.
    unfold add_pm22.
    repeat (rewrite -> Nat.add_0_l).
    repeat (rewrite -> Nat.mul_0_l).
    repeat (rewrite -> Nat.mul_1_l).
    repeat (rewrite -> Nat.add_0_r).
    rewrite <- fold_unfold_fib_nat_SS.
    rewrite <- fold_unfold_fib_nat_SS.
    reflexivity.
Qed.

Compute (fib_pm22 nat Nat.add Nat.mul 0 1 0).  (* = PM22 nat 1 0 0 1 *)
Compute (fib_pm22 nat Nat.add Nat.mul 0 1 1).  (* = PM22 nat 0 1 1 1 *)
Compute (fib_pm22 nat Nat.add Nat.mul 0 1 2).  (* = PM22 nat 1 1 1 2 *)
Compute (fib_pm22 nat Nat.add Nat.mul 0 1 3).  (* = PM22 nat 1 2 2 3 *)
Compute (fib_pm22 nat Nat.add Nat.mul 0 1 4).  (* = PM22 nat 2 3 3 5 *)

Compute (fib_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul) (zero_pm22 nat 0) (one_pm22 nat 0 1) 0).
(* = PM22 (pm22 nat) (PM22 nat 1 0 0 1) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 1 0 0 1) *)

Compute (fib_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul) (zero_pm22 nat 0) (one_pm22 nat 0 1) 1).
(* = PM22 (pm22 nat) (PM22 nat 0 0 0 0) (PM22 nat 1 0 0 1) (PM22 nat 1 0 0 1) (PM22 nat 1 0 0 1) *)

Compute (fib_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul) (zero_pm22 nat 0) (one_pm22 nat 0 1) 2).
(* = PM22 (pm22 nat) (PM22 nat 1 0 0 1) (PM22 nat 1 0 0 1) (PM22 nat 1 0 0 1) (PM22 nat 2 0 0 2) *)

Compute (fib_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul) (zero_pm22 nat 0) (one_pm22 nat 0 1) 3).
(* = PM22 (pm22 nat) (PM22 nat 1 0 0 1) (PM22 nat 2 0 0 2) (PM22 nat 2 0 0 2) (PM22 nat 3 0 0 3) *)

Compute (fib_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul) (zero_pm22 nat 0) (one_pm22 nat 0 1) 4).
(* = PM22 (pm22 nat) (PM22 nat 2 0 0 2) (PM22 nat 3 0 0 3) (PM22 nat 3 0 0 3) (PM22 nat 5 0 0 5) *)

Compute (fib_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul) (zero_pm22 nat 0) (one_pm22 nat 0 1) 5).
(* = PM22 (pm22 nat) (PM22 nat 3 0 0 3) (PM22 nat 5 0 0 5) (PM22 nat 5 0 0 5) (PM22 nat 8 0 0 8) *)

Compute (fib_pm22 (pm22 (pm22 nat)) (add_pm22 (pm22 nat) (add_pm22 nat Nat.add)) (mul_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul)) (zero_pm22 (pm22 nat) (zero_pm22 nat 0)) (one_pm22 (pm22 nat) (zero_pm22 nat 0) (one_pm22 nat 0 1)) 0).
(* PM22 (pm22 (pm22 nat))
        (PM22 (pm22 nat) (PM22 nat 1 0 0 1) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 1 0 0 1))
        (PM22 (pm22 nat) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0))
        (PM22 (pm22 nat) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0))
        (PM22 (pm22 nat) (PM22 nat 1 0 0 1) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 1 0 0 1)) *)

Compute (fib_pm22 (pm22 (pm22 nat)) (add_pm22 (pm22 nat) (add_pm22 nat Nat.add)) (mul_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul)) (zero_pm22 (pm22 nat) (zero_pm22 nat 0)) (one_pm22 (pm22 nat) (zero_pm22 nat 0) (one_pm22 nat 0 1)) 1).
(* PM22 (pm22 (pm22 nat))
        (PM22 (pm22 nat) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0))
        (PM22 (pm22 nat) (PM22 nat 1 0 0 1) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 1 0 0 1))
        (PM22 (pm22 nat) (PM22 nat 1 0 0 1) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 1 0 0 1))
        (PM22 (pm22 nat) (PM22 nat 1 0 0 1) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 1 0 0 1)) *)

Compute (fib_pm22 (pm22 (pm22 nat)) (add_pm22 (pm22 nat) (add_pm22 nat Nat.add)) (mul_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul)) (zero_pm22 (pm22 nat) (zero_pm22 nat 0)) (one_pm22 (pm22 nat) (zero_pm22 nat 0) (one_pm22 nat 0 1)) 2).
(* PM22 (pm22 (pm22 nat))
        (PM22 (pm22 nat) (PM22 nat 1 0 0 1) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 1 0 0 1))
        (PM22 (pm22 nat) (PM22 nat 1 0 0 1) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 1 0 0 1))
        (PM22 (pm22 nat) (PM22 nat 1 0 0 1) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 1 0 0 1))
        (PM22 (pm22 nat) (PM22 nat 2 0 0 2) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 2 0 0 2)) *)

Compute (fib_pm22 (pm22 (pm22 nat)) (add_pm22 (pm22 nat) (add_pm22 nat Nat.add)) (mul_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul)) (zero_pm22 (pm22 nat) (zero_pm22 nat 0)) (one_pm22 (pm22 nat) (zero_pm22 nat 0) (one_pm22 nat 0 1)) 3).
(* PM22 (pm22 (pm22 nat))
        (PM22 (pm22 nat) (PM22 nat 1 0 0 1) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 1 0 0 1))
        (PM22 (pm22 nat) (PM22 nat 2 0 0 2) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 2 0 0 2))
        (PM22 (pm22 nat) (PM22 nat 2 0 0 2) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 2 0 0 2))
        (PM22 (pm22 nat) (PM22 nat 3 0 0 3) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 3 0 0 3)) *)

Compute (fib_pm22 (pm22 (pm22 nat)) (add_pm22 (pm22 nat) (add_pm22 nat Nat.add)) (mul_pm22 (pm22 nat) (add_pm22 nat Nat.add) (mul_pm22 nat Nat.add Nat.mul)) (zero_pm22 (pm22 nat) (zero_pm22 nat 0)) (one_pm22 (pm22 nat) (zero_pm22 nat 0) (one_pm22 nat 0 1)) 4).
(* = PM22 (pm22 (pm22 nat))
          (PM22 (pm22 nat) (PM22 nat 2 0 0 2) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 2 0 0 2))
          (PM22 (pm22 nat) (PM22 nat 3 0 0 3) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 3 0 0 3))
          (PM22 (pm22 nat) (PM22 nat 3 0 0 3) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 3 0 0 3))
          (PM22 (pm22 nat) (PM22 nat 5 0 0 5) (PM22 nat 0 0 0 0) (PM22 nat 0 0 0 0) (PM22 nat 5 0 0 5)) *)

Proposition about_fib_pm22_ground :
  forall n : nat,
    fib_pm22 nat Nat.add Nat.mul 0 1 (S n) =
    PM22 nat
         (fib_nat n)     (fib_nat (S n))
         (fib_nat (S n)) (fib_nat (S (S n))).
Proof.
  intro n.
  unfold fib_pm22.
  induction n as [ | n' IHn'].

  - rewrite -> fold_unfold_power_pm22_S.
    rewrite -> fold_unfold_power_pm22_O.
    unfold F_pm22.
    unfold one_pm22.
    unfold mul_pm22.
    repeat (rewrite -> Nat.add_0_l).
    repeat (rewrite -> Nat.add_0_r).
    repeat (rewrite -> Nat.mul_1_l).
    rewrite -> fold_unfold_fib_nat_SS.
    rewrite -> fold_unfold_fib_nat_S.
    rewrite -> fold_unfold_fib_nat_O.
    rewrite -> Nat.add_0_l.
    reflexivity.

  - rewrite -> fold_unfold_power_pm22_S.
    rewrite -> IHn'.
    unfold mul_pm22, F_pm22.
    rewrite ->2 Nat.mul_0_l.
    rewrite ->2 Nat.add_0_l.
    rewrite ->3 Nat.mul_1_l.
    rewrite <-2 fold_unfold_fib_nat_SS.
    reflexivity.
Qed.

Proposition about_fib_pm22_base_case :
  forall (V : Type)
         (add mul : V -> V -> V)
         (zero one : V),
    (forall v : V,
        add zero v = v) ->
    (forall v : V,
        add v zero = v) ->
    (forall v : V,
        mul zero v = zero) ->
    (forall v : V,
        mul v zero = zero) ->
    (forall v : V,
        mul one v = v) -> 
    (forall v : V,
        mul v one = v) -> 
    forall (fib : nat -> V),
      Fibonacci V add zero one fib ->
      forall n : nat,
        fib_pm22 V add mul (fib 0) (fib 1) (S n) =
        PM22 V
             (fib n)     (fib (S n))
             (fib (S n)) (fib (S (S n))).
Proof.
  intros V add mul zero one add_0_l add_0_r mul_0_l mul_0_r mul_1_l mul_1_r fib [H_fib_0 [H_fib_1 H_fib_SS]] n.
  unfold fib_pm22.
  induction n as [ | n' IHn'].

  - rewrite -> fold_unfold_power_pm22_S.
    rewrite -> fold_unfold_power_pm22_O.
    rewrite -> H_fib_SS.
    rewrite -> H_fib_0.
    rewrite -> H_fib_1.
    rewrite -> add_0_l.
    unfold F_pm22.
    Check (mul_pm22_1_r V add mul zero add_0_l add_0_r mul_0_r one mul_1_r (PM22 V zero one one one)).
    exact (mul_pm22_1_r V add mul zero add_0_l add_0_r mul_0_r one mul_1_r (PM22 V zero one one one)).

  - rewrite -> fold_unfold_power_pm22_S.
    rewrite -> IHn'.
    unfold F_pm22, mul_pm22.
    rewrite -> H_fib_0.
    rewrite -> H_fib_1.
    rewrite ->2 mul_0_l.
    rewrite ->3 mul_1_l.
    rewrite ->2 add_0_l.
    rewrite <-2 H_fib_SS.
    reflexivity.
Qed.

Proposition about_fib_pm22_ground' :
  forall n : nat,
    fib_pm22 nat Nat.add Nat.mul 0 1 (S n) =
    PM22 nat
         (fib_nat n)     (fib_nat (S n))
         (fib_nat (S n)) (fib_nat (S (S n))).
Proof.
  exact (about_fib_pm22_base_case nat Nat.add Nat.mul 0 1 Nat.add_0_l Nat.add_0_r Nat.mul_0_l Nat.mul_0_r Nat.mul_1_l Nat.mul_1_r fib_nat fib_nat_fits_Fibonacci).
Qed.

(* ********** *)

Definition scalar_mul_pm22 (V : Type) (mul : V -> V -> V) (v : V) (x : pm22 V) : pm22 V :=
  match x with
    PM22 _
         x11 x12
         x21 x22 =>
    PM22 V
         (mul v x11) (mul v x12)
         (mul v x21) (mul v x22)
  end.

Proposition about_fib_pm22_induction_step :
  forall (V : Type)
         (add mul : V -> V -> V)
         (zero one : V),
    (forall v : V,
        add zero v = v) ->
    (forall v : V,
        add v zero = v) ->
    (forall v : V,
        mul zero v = zero) ->
    (forall v : V,
        mul v zero = zero) ->
    (forall v : V,
        mul one v = v) -> 
    (forall v : V,
        mul v one = v) -> 
    forall (fib : nat -> V),
      Fibonacci V add zero one fib ->
      forall n : nat,
        fib_pm22 (pm22 V) (add_pm22 V add) (mul_pm22 V add mul) (zero_pm22 V (fib 0)) (one_pm22 V (fib 0) (fib 1)) (S n) =
        PM22 (pm22 V)
             (scalar_mul_pm22 V mul (fib n)     (one_pm22 V zero one)) (scalar_mul_pm22 V mul (fib (S n))     (one_pm22 V zero one))
             (scalar_mul_pm22 V mul (fib (S n)) (one_pm22 V zero one)) (scalar_mul_pm22 V mul (fib (S (S n))) (one_pm22 V zero one)).
Proof.
  intros V add mul zero one add_0_l add_0_r mul_0_l mul_0_r mul_1_l mul_1_r fib [H_fib_0 [H_fib_1 H_fib_SS]] n.
  rewrite -> H_fib_0.
  rewrite -> H_fib_1.
  induction n as [ | n' IHn'].

  - Check (fold_unfold_fib_pm22_1 (pm22 V) (add_pm22 V add) (mul_pm22 V add mul) (zero_pm22 V zero) (add_pm22_0_l V add zero add_0_l) (add_pm22_0_r V add zero add_0_r) (mul_pm22_0_r V add mul zero add_0_r mul_0_r) (one_pm22 V zero one) (mul_pm22_1_r V add mul zero add_0_l add_0_r mul_0_r one mul_1_r)).
    rewrite -> (fold_unfold_fib_pm22_1 (pm22 V) (add_pm22 V add) (mul_pm22 V add mul) (zero_pm22 V zero) (add_pm22_0_l V add zero add_0_l) (add_pm22_0_r V add zero add_0_r) (mul_pm22_0_r V add mul zero add_0_r mul_0_r) (one_pm22 V zero one) (mul_pm22_1_r V add mul zero add_0_l add_0_r mul_0_r one mul_1_r)).
    unfold F_pm22, zero_pm22, one_pm22, scalar_mul_pm22.
    rewrite ->3 mul_1_r.
    rewrite ->3 mul_0_r.
    repeat (rewrite -> H_fib_SS).
    rewrite -> H_fib_1.
    rewrite -> H_fib_0.
    rewrite -> add_0_l.
    reflexivity.

  - unfold fib_pm22.
    unfold fib_pm22 in IHn'.
    rewrite -> fold_unfold_power_pm22_S.
    rewrite -> IHn'.
    unfold F_pm22, zero_pm22, one_pm22, mul_pm22, add_pm22, scalar_mul_pm22.
    repeat (rewrite -> add_0_l).
    repeat (rewrite -> mul_0_l).
    repeat (rewrite -> mul_1_l).
    repeat (rewrite -> add_0_r).
    repeat (rewrite -> add_0_l).
    repeat (rewrite -> mul_1_r).
    repeat (rewrite -> mul_0_r).
    repeat (rewrite -> add_0_l).
    rewrite <- H_fib_SS.
    rewrite <- H_fib_SS.
    reflexivity.
Qed.

(* ********** *)

(* end of week-10_a-fibonacci-structure.v *)
