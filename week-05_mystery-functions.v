(* week-05_mystery-functions.v *)
(* LPP 2024 - CS3234 2023-2024, Sem2 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 16 Feb 2024 *)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Bool Arith.

Check Nat.eqb.
Check (fun i j => Nat.eqb i j).
(* so "X =? Y" is syntactic sugar for "Nat.eqb X Y" *)

Check Bool.eqb.
Check (fun b1 b2 => Bool.eqb b1 b2).
(* so eqb stands for Bool.eqb *)

(* ********** *)

Definition specification_of_mystery_function_00 (mf : nat -> nat) :=
  mf 0 = 1 /\ forall i j : nat, mf (S (i + j)) = mf i + mf j.

(* ***** *)

Proposition there_is_at_most_one_mystery_function_00 :
  forall f g : nat -> nat,
    specification_of_mystery_function_00 f ->
    specification_of_mystery_function_00 g ->
    forall n : nat,
      f n = g n.
Proof.
Abort.

(* ***** *)

Definition unit_test_for_mystery_function_00a (mf : nat -> nat) :=
  (mf 0 =? 1) (* etc. *).

Definition unit_test_for_mystery_function_00b (mf : nat -> nat) :=
  (mf 0 =? 1) && (mf 1 =? 2) (* etc. *).

Definition unit_test_for_mystery_function_00c (mf : nat -> nat) :=
  (mf 0 =? 1) && (mf 1 =? 2) && (mf 2 =? 3) (* etc. *).

Definition unit_test_for_mystery_function_00d (mf : nat -> nat) :=
  (mf 0 =? 1) && (mf 1 =? 2) && (mf 2 =? 3) && (mf 3 =? 4)
  (* etc. *).

(* ***** *)

Definition mystery_function_00 := S.

Definition less_succinct_mystery_function_00 (n : nat) : nat :=
  S n.

Compute (unit_test_for_mystery_function_00d mystery_function_00).

Theorem there_is_at_least_one_mystery_function_00 :
  specification_of_mystery_function_00 mystery_function_00.
Proof.
  unfold specification_of_mystery_function_00, mystery_function_00.
  split.
  - reflexivity.
  - intros i j.
    rewrite -> (plus_Sn_m i (S j)).
    rewrite <- (plus_n_Sm i j).
    reflexivity.
Qed.

(* ***** *)

Definition mystery_function_00_alt := fun (n : nat) => n + 1.

Theorem there_is_at_least_one_mystery_function_00_alt :
  specification_of_mystery_function_00 mystery_function_00_alt.
Proof.
Abort.

(* ********** *)

Definition specification_of_mystery_function_11 (mf : nat -> nat) :=
  mf 1 = 1
  /\
  forall i j : nat,
    mf (i + j) = mf i + 2 * i * j + mf j.

(* ********** *)

Definition specification_of_mystery_function_04 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  forall n' : nat,
    mf (S n') = mf n' + S (2 * n').

(* ********** *)

Definition specification_of_mystery_function_15 (mf : nat -> nat * nat) :=
  mf 0 = (0, 1)
  /\
  forall n' : nat,
    mf (S n') = let (x, y) := mf n'
                in (S x, y * S x).

(* ********** *)

Definition specification_of_mystery_function_16 (mf : nat -> nat * nat) :=
  mf 0 = (0, 1)
  /\
  forall n' : nat,
    mf (S n') = let (x, y) := mf n'
                in (y, x + y).

(* ********** *)

Definition specification_of_mystery_function_17 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 1
  /\
  mf 2 = 2
  /\
  forall p q : nat,
    mf (S (p + q)) = mf (S p) * mf (S q) + mf p * mf q.

Theorem there_is_at_most_one_mystery_function_17:
  forall f g : nat -> nat,
    specification_of_mystery_function_17 f ->
    specification_of_mystery_function_17 g ->
    forall n : nat,
      f n = g n.

Proof.
  intros f g S_f S_g.

  assert (S_f_temp := S_f).
  unfold specification_of_mystery_function_17 in S_f_temp.
  destruct S_f_temp as [S_f_0 [S_f_1 [S_f_2 S_f_S]]].

  assert (S_g_temp := S_g).
  unfold specification_of_mystery_function_17 in S_g_temp.
  destruct S_g_temp as [S_g_0 [S_g_1 [S_g_2 S_g_S]]].
  intro n.

  assert (both : (f n = g n) /\ f (S n) = g (S n)).

  *  induction n as [ | n' IHn'].
     
  -  split.
     + rewrite -> S_f_0.
       rewrite -> S_g_0.
       reflexivity.
     + rewrite -> S_f_1.
       rewrite -> S_g_1.
       reflexivity.
   -   destruct IHn' as [H_n H_S_n].
       split.
     + rewrite -> H_S_n.
       reflexivity.
     + rewrite <- (Nat.add_1_l n').
       rewrite -> (S_f_S 1 n').
       rewrite -> (S_g_S 1 n').
       rewrite -> S_f_2.
       rewrite -> S_f_1.
       rewrite-> S_g_2.
       rewrite -> S_g_1.
       rewrite -> H_S_n.
       rewrite -> H_n.
       reflexivity.

  * destruct both as [H _].
    exact H.
Qed.
       
Fixpoint mystery_function_17 (n : nat) : nat :=
  match n with
  | 0 =>
    0
  | 1 =>
    1
  | 2 =>
    2
  | S n' => match n' with
            | 0 =>
              1
            | 1 =>
              2
            | S n'' =>
              2 * mystery_function_17 n' + mystery_function_17 n''
            end  
  end.   

Lemma fold_unfold_mf_17_0 :
  mystery_function_17 0 = 0.

Proof.
  fold_unfold_tactic mystery_function_17.
Qed.

Lemma fold_unfold_mf_17_1 :
  mystery_function_17 1 = 1.

Proof.
  fold_unfold_tactic mystery_function_17.
Qed.

Lemma fold_unfold_mf_17_2:
  mystery_function_17 2 = 2.

Proof.
  fold_unfold_tactic mystery_function_17.
Qed.

  
Theorem there_is_at_least_one_mystery_function_17:
  specification_of_mystery_function_17 mystery_function_17.

Proof.
  unfold specification_of_mystery_function_17.

  split.
  exact fold_unfold_mf_17_0.

  split.
  exact fold_unfold_mf_17_1.

  split.
  exact fold_unfold_mf_17_2.
  
  intro p.
  induction p as [ | p' IHp'].

  * intro q.

    rewrite -> fold_unfold_mf_17_0.
    rewrite -> fold_unfold_mf_17_1.
    rewrite -> (Nat.mul_1_l (mystery_function_17 (S q))).
    rewrite -> (Nat.mul_0_l (mystery_function_17 q)).
    rewrite -> (Nat.add_0_r (mystery_function_17 (S q))).
    rewrite -> (Nat.add_0_l q).
    reflexivity.
    (* ********** *)   
  * 


Definition specification_of_mystery_function_18 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 1
  /\
  mf 2 = 1
  /\
  forall n''' : nat,
    mf n''' + mf (S (S (S n'''))) = 2 * mf (S (S n''')).

(* ********** *)

Definition specification_of_mystery_function_03 (mf : nat -> nat -> nat) :=
  mf 0 0 = 0
  /\
  (forall i j: nat, mf (S i) j = S (mf i j))
  /\
  (forall i j: nat, S (mf i j) = mf i (S j)).

(* ********** *)

Definition specification_of_mystery_function_42 (mf : nat -> nat) :=
  mf 1 = 42
  /\
  forall i j : nat,
    mf (i + j) = mf i + mf j.

(* ********** *)

Definition specification_of_mystery_function_07 (mf : nat -> nat -> nat) :=
  (forall j : nat, mf 0 j = j)
  /\
  (forall i : nat, mf i 0 = i)
  /\
  (forall i j k : nat, mf (i + k) (j + k) = (mf i j) + k).

(* ********** *)

Definition specification_of_mystery_function_08 (mf : nat -> nat -> bool) :=
  (forall j : nat, mf 0 j = true)
  /\
  (forall i : nat, mf (S i) 0 = false)
  /\
  (forall i j : nat, mf (S i) (S j) = mf i j).

(* ********** *)

Definition specification_of_mystery_function_23 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 0
  /\
  forall n'' : nat,
    mf (S (S n'')) = S (mf n'').

(* ********** *)

Definition specification_of_mystery_function_24 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 1
  /\
  forall n'' : nat,
    mf (S (S n'')) = S (mf n'').

(* ********** *)

Definition specification_of_mystery_function_13 (mf : nat -> nat) :=
  (forall q : nat, mf (2 * q) = q)
  /\
  (forall q : nat, mf (S (2 * q)) = q).

(* ********** *)

Definition specification_of_mystery_function_25 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  (forall q : nat,
      mf (2 * (S q)) = S (mf (S q)))
  /\
  mf 1 = 0
  /\
  (forall q : nat,
      mf (S (2 * (S q))) = S (mf (S q))).

(* ****** *)

Definition specification_of_mystery_function_20 (mf : nat -> nat -> nat) :=
  (forall j : nat, mf O j = j)
  /\
  (forall i j : nat, mf (S i) j = S (mf i j)).

(* ****** *)

Definition specification_of_mystery_function_21 (mf : nat -> nat -> nat) :=
  (forall j : nat, mf O j = j)
  /\
  (forall i j : nat, mf (S i) j = mf i (S j)).

(* ****** *)

Definition specification_of_mystery_function_22 (mf : nat -> nat -> nat) :=
  forall i j : nat,
    mf O j = j
    /\
    mf (S i) j = mf i (S j).

(* 22 is just addition *)


Definition unit_test_for_mystery_function_22 (candidate : nat -> nat -> nat) : bool :=
  (Nat.eqb (candidate 0 1) 1)
  &&
  (Nat.eqb (candidate 0 2) 2)
  &&
  (Nat.eqb (candidate 0 23) 23)
  &&
  (Nat.eqb (candidate 1 0) 1)
  &&
  (Nat.eqb (candidate 2 1) 3)
  &&
  (Nat.eqb (candidate 1 2) 3).


Definition mystery_function_22 (i j : nat) : nat :=
  i + j.

Compute unit_test_for_mystery_function_22 mystery_function_22.

Theorem there_is_at_least_one_mystery_function_22:
  specification_of_mystery_function_22 mystery_function_22.

Proof.
  unfold specification_of_mystery_function_22.
  split.

  * unfold mystery_function_22.
    rewrite -> (Nat.add_0_l j).
    reflexivity.

  * unfold mystery_function_22.
    rewrite <- (Nat.add_1_r i).
    rewrite <- (Nat.add_1_l j).
    rewrite -> (Nat.add_assoc i 1 j).
    reflexivity.
Qed.

Proposition there_is_at_most_one_mystery_function_22:
  forall f g : nat -> nat -> nat,
    specification_of_mystery_function_22 f ->
    specification_of_mystery_function_22 g ->
    forall i j  : nat,
      f i j = g i j.

Proof.
  intros f g S_f S_g i.

  induction i as [ | i' IHi'].

  * intro j.
    unfold specification_of_mystery_function_22 in S_f.
    destruct (S_f 0 j) as [S_f_0 _].

    unfold specification_of_mystery_function_22 in S_g.
    destruct (S_g 0 j) as [S_g_0 _].

    rewrite -> S_f_0.
    rewrite -> S_g_0.
    reflexivity.

 * intro j.
   unfold specification_of_mystery_function_22 in S_f.
   destruct (S_f i' j) as [_ S_f_S].

   unfold specification_of_mystery_function_22 in S_g.
   destruct (S_g i' j) as [_ S_g_S].

   rewrite -> S_f_S.
   rewrite -> S_g_S.
   rewrite -> (IHi' (S j)).
   reflexivity.
Qed.

(* ********** *)

(* Binary trees of natural numbers: *)

Inductive tree : Type :=
  | Leaf : nat -> tree
  | Node : tree -> tree -> tree.

Definition specification_of_mystery_function_19 (mf : tree -> tree) :=
  (forall n : nat,
     mf (Leaf n) = Leaf n)
  /\
  (forall (n : nat) (t : tree),
     mf (Node (Leaf n) t) = Node (Leaf n) (mf t))
  /\
  (forall t11 t12 t2 : tree,
     mf (Node (Node t11 t12) t2) = mf (Node t11 (Node t12 t2))).

(* You might not manage to prove
   that at most one function satisfies this specification (why?),
   but consider whether the following function does.
   Assuming it does, what does this function do?
   And what is the issue here?
*)

Fixpoint mystery_function_19_aux (t a : tree) : tree :=
  match t with
  | Leaf n =>
     Node (Leaf n) a
  | Node t1 t2 =>
     mystery_function_19_aux t1 (mystery_function_19_aux t2 a)
  end.

Fixpoint mystery_function_19 (t : tree) : tree :=
  match t with
  | Leaf n =>
     Leaf n
  | Node t1 t2 =>
     mystery_function_19_aux t1 (mystery_function_19 t2)
  end.

(* ********** *)

Definition specification_of_mystery_function_05 (mf : nat -> nat) :=
  mf 0 = 1
  /\
  forall i j : nat,
    mf (S (i + j)) = 2 * mf i * mf j.

(* ********** *)

Definition specification_of_mystery_function_06 (mf : nat -> nat) :=
  mf 0 = 2
  /\
  forall i j : nat,
    mf (S (i + j)) = mf i * mf j.


(* mf (S (n 0)) = mf n * mf 0
                = mf n * 2

  mf (S (0 + 0)) = mf 0 * mf 0
                 = 2 * 2
                 = 4

  mf (S (1 + 0)) = mf 1 * mf 0
                 = mf (S 0) * 2
                 = 4 * 2
                 = 8

  mf (S (2 + 0)) = mf 2 * mf 0
                 = mf (S 1) * 2
                 = 8 * 2
                 = 16

  We make a conjecture that the mystery function
  is given by 2^(n+1).

 *)
Definition mystery_function_06 (n : nat) : nat :=
  2^(n + 1).

Theorem there_is_at_least_one_mystery_function_06:
  specification_of_mystery_function_06 mystery_function_06.

Proof.
  unfold specification_of_mystery_function_06.

  split.

 *  unfold mystery_function_06. (* Make sure I know what I am computing *)
    compute.
    reflexivity.

 *  intro i.
    induction i as [ | i' IHi'].

    - intro j.
      rewrite -> (Nat.add_0_l j).
      rewrite <- (Nat.add_1_r j).

      unfold mystery_function_06.

      rewrite -> (Nat.add_0_l 1).
      Search (_ ^ _).

      rewrite -> (Nat.pow_add_r 2 (j+1) 1).
      rewrite -> (Nat.mul_comm (2 ^ (j + 1)) (2 ^ 1)).
      reflexivity.

    - intro j.
      rewrite <- (Nat.add_1_r i').
      rewrite <- (Nat.add_assoc i' 1 j).
      rewrite -> (IHi' (1 + j)).

      unfold mystery_function_06.
      rewrite <- (Nat.pow_add_r 2 (i'+1) (1+j+1)).
      rewrite <- (Nat.pow_add_r 2 (i' + 1 + 1) (j + 1)).

      (* Bracket shuffling *)
      rewrite -> Nat.add_assoc.
      rewrite -> Nat.add_assoc.
      rewrite -> Nat.add_assoc.
      reflexivity.
Qed.

Theorem there_is_at_most_one_mystery_function_06:
  forall f g : nat -> nat,
    specification_of_mystery_function_06 f ->
    specification_of_mystery_function_06 g ->
    forall n : nat,
      f n = g n.

Proof.
  intros f g S_f S_g.

  unfold specification_of_mystery_function_06 in S_f.
  destruct (S_f) as [S_f_0 S_f_S].

  unfold specification_of_mystery_function_06 in S_g.
  destruct (S_g) as [S_g_0 S_g_S].

  intro n.
  induction n as [ | n' IHn'].

  * rewrite -> S_f_0.
    rewrite -> S_g_0.
    reflexivity.

  * rewrite <- (Nat.add_0_r n').
    rewrite -> (S_f_S n' 0).
    rewrite -> (S_g_S n' 0).
    rewrite -> S_f_0.
    rewrite -> S_g_0.
    rewrite-> IHn'.
    reflexivity.
Qed.


(* ********** *)

Definition specification_of_mystery_function_09 (mf : nat -> bool) :=
  mf 0 = false
  /\
  mf 1 = true
  /\
  forall i j : nat,
    mf (i + j) = xorb (mf i) (mf j).

(* mf (S n') = xorb (mf n') (mf 1)
             = xorb (mf n') true

   On a few small numbers.

   mf (1 + 1) = xorb (mf 1) (mf 1)
              = false.

   mf (2 + 0) = xorb (mf 2) (mf 0)
              = xorb (mf 2) false
              = xorb false false
              = false.

   mf (2 + 1) = xorb (mf 2) (mf 1)
              = xorb true false
              = true.

  So this is an odd number checker. *)


Definition mystery_function_09 (n : nat) : bool :=
  if (Nat.eqb (n mod 2) 0) then false else true.

(* The Lemma is to show that adding 1 to a natural
   number flips its parity *)

Lemma about_the_mystery_function_09:
  forall n : nat,
    mystery_function_09 n = negb (mystery_function_09 (S n)).

Proof.
  intro n.
  induction n as [ | n' IHn'].

  * compute.
    reflexivity.

  * Search (negb _ = _).
    rewrite <- (negb_involutive (mystery_function_09 (S n'))).
    rewrite <- IHn'.

    (* This part of the proof is basically saying,
       "Adding two to a number does not change its parity" *)

    unfold mystery_function_09 at 2.
    rewrite <- (Nat.add_1_l (S n')).
    rewrite <- (Nat.add_1_r n').
    rewrite -> (Nat.add_comm).
    rewrite <- (Nat.add_assoc n' 1 1).
    rewrite -> (Nat.add_1_l 1).
    rewrite <- (Nat.mul_1_l 2) at 1.

    Search (_ mod _).
    rewrite -> (Nat.Div0.mod_add).
    fold (mystery_function_09 n').
    reflexivity.
Qed.
    
Theorem there_is_at_least_one_mystery_function_09:
  specification_of_mystery_function_09 mystery_function_09.
  unfold specification_of_mystery_function_09.

  assert (mf_0 : (mystery_function_09 0) = false).
  compute.
  reflexivity.

  assert (mf_1 : (mystery_function_09 1) = true).
  compute.
  reflexivity.

  split.
  * compute.
    reflexivity.

  * split.

    - compute.
      reflexivity.

    - intro i.
      induction i as [ | i' IHi'].

      + intro j.

        rewrite -> mf_0.
        rewrite -> (xorb_false_l (mystery_function_09 j)).
        rewrite -> (Nat.add_0_l j).
        reflexivity.

      + intro j.
        case j as [ | j' IHj'].

        ** rewrite -> mf_0.  
           rewrite -> (xorb_false_r (mystery_function_09 (S i'))).
           rewrite -> (Nat.add_0_r (S i')).
           reflexivity.

        ** rewrite <- (Nat.add_1_r i') at 1.
           rewrite <- (Nat.add_assoc i' 1 (S j')).
           rewrite -> (Nat.add_1_l (S j')).
           rewrite -> (IHi' (S (S j'))).
           rewrite -> (about_the_mystery_function_09 (S j')).
           rewrite -> (about_the_mystery_function_09 i').
           
           Search (xorb (negb _) _).

           rewrite <- (negb_xorb_l (mystery_function_09 (S i')) (mystery_function_09 (S (S j')))).
           rewrite <- (negb_xorb_r (mystery_function_09 (S i')) (mystery_function_09 (S (S j')))).

           reflexivity.
Qed.

Theorem there_is_at_most_one_mystery_function_09 :
  forall f g : nat -> bool,
    specification_of_mystery_function_09 f ->
    specification_of_mystery_function_09 g ->
    forall n : nat,
      f n = g n.

Proof.
  intros f g S_f S_g.
  
  assert (S_f_temp := S_f).
  unfold specification_of_mystery_function_09 in S_f_temp.
  destruct S_f_temp as [S_f_0 [S_f_1  S_f_S]].

  assert (S_g_temp := S_g).
  unfold specification_of_mystery_function_09 in S_g_temp.
  destruct S_g_temp as [S_g_0 [S_g_1 S_g_S]].

  intro n.
  induction n as [ | n' IHn'].

  * rewrite -> S_f_0.
    rewrite -> S_g_0.
    reflexivity.

  * rewrite <- (Nat.add_1_r n').
    rewrite -> (S_f_S n' 1).
    rewrite -> S_f_1.
    Search (xorb _ true).
    rewrite -> (xorb_true_r (f n')).
    
    rewrite -> (S_g_S n' 1).
    rewrite -> (S_g_1).
    rewrite -> (xorb_true_r (g n')).

    rewrite -> IHn'.
    reflexivity.
 Qed.

    
Definition specification_of_mystery_function_10 (mf : nat -> bool) :=
  mf 0 = false
  /\
  mf 1 = true
  /\
  forall i j : nat,
    mf (i + j) = Bool.eqb (mf i) (mf j).

(* ********** *)

Definition specification_of_mystery_function_12 (mf : nat -> nat) :=
  mf 1 = 1
  /\
  forall i : nat,
    mf (S (S i)) = (S (S i)) * mf (S i).

(* Factorial *)


(* ********** *)

Definition specification_of_mystery_function_14 (mf : nat -> bool) :=
  (forall q : nat, mf (2 * q) = true)
  /\
  (forall q : nat, mf (S (2 * q)) = false).

(* ********** *)

Definition specification_of_mystery_function_29 (mf : nat -> bool) :=
  (mf 0 = true)
  /\
  (mf 1 = false)
  /\
  (forall n'' : nat, mf (S (S n'')) = mf n'').

Definition unit_test_for_mystery_function_29 (candidate : nat -> bool) : bool :=
  (Bool.eqb (candidate 0) true)
  &&
  (Bool.eqb (candidate 1) false)
  &&
  (Bool.eqb (candidate (S 1)) true)
  &&
  (Bool.eqb (candidate (S (S 0))) true)
  &&
  (Bool.eqb (candidate 23) false)
  &&
  (Bool.eqb (candidate 22) true).               

(* It is clear that this specification can be satisfied by the
   even number checking function. For a change, we try writing it
   using modular arithmetic. *)

Definition mystery_function_29 (n : nat) : bool :=
 if (Nat.eqb (n mod 2) 0) then true else false.

Compute unit_test_for_mystery_function_29 mystery_function_29.

Theorem there_is_at_least_one_mystery_function_29:
  specification_of_mystery_function_29 mystery_function_29.

Proof.
 unfold specification_of_mystery_function_29.
 split.

 * unfold mystery_function_29.
   compute.
   reflexivity.

 * split.

   - unfold mystery_function_29.
     compute.
     reflexivity.

   - unfold mystery_function_29.
     intro n.
     case n as [ | n' IHn'].

     + compute.
       reflexivity.

     + rewrite <- (Nat.add_1_l (S (S n'))).
       rewrite <- (Nat.add_1_l (S n')).
       rewrite -> (Nat.add_assoc 1 1 (S n')).
       rewrite -> (Nat.add_comm (1 + 1) (S n')).
       rewrite -> (Nat.add_1_l 1).
       rewrite <- (Nat.mul_1_l 2) at 1.
       rewrite -> (Nat.Div0.mod_add (S n') 1 2).
       reflexivity.
Qed.



Theorem there_is_at_most_one_mystery_function_29:
  forall f g: nat -> bool,
    specification_of_mystery_function_29 f ->
    specification_of_mystery_function_29 g ->
    forall n : nat,
      f n = g n.


(* ********** *)
       
Require Import String.

Inductive arithmetic_expression : Type :=
  Literal : nat -> arithmetic_expression
| Error : string -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

Inductive expressible_value : Type :=
  Expressible_nat : nat -> expressible_value
| Expressible_msg : string -> expressible_value.

Definition specification_of_mystery_function_30 (mf : arithmetic_expression -> expressible_value) :=
  (forall n : nat,
     mf (Literal n) = Expressible_nat n)
  /\
  (forall s : string,
     mf (Error s) = Expressible_msg s)
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       mf ae1 = Expressible_nat n1 ->
       mf ae2 = Expressible_nat n2 ->
       mf (Plus ae1 ae2) = Expressible_nat (n1 + n2))
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       mf ae1 = Expressible_msg s1 ->
       mf (Plus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (s2 : string),
       mf ae2 = Expressible_msg s2 ->
       mf (Plus ae1 ae2) = Expressible_msg s2)).

(* ********** *)

(* Simple examples of specifications: *)

(* ***** *)

Definition specification_of_the_factorial_function (fac : nat -> nat) :=
  fac 0 = 1
  /\
  forall n' : nat, fac (S n') = S n' * fac n'.

(* ***** *)

Definition specification_of_the_fibonacci_function (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  forall n'' : nat,
    fib (S (S n'')) = fib n'' + fib (S n'').

(* ********** *)

(* end of week-05_mystery-functions.v *)
