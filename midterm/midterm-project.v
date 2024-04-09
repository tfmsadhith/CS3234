(* midterm-projct.v *)
(* LPP 2024 - CS3234 2023-2024, Sem2 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 22 Feb 2024 *)

(* ********** *)

(* A study of polymorphic lists. *)

(* members of the group:
   date: 

   please upload one .v file and one .pdf file containing a project report

   desiderata:
   - the file should be readable, i.e., properly indented and using items or {...} for subgoals
   - each use of a tactic should achieve one proof step
   - all lemmas should be applied to all their arguments
   - there should be no occurrences of admit, Admitted, and Abort
*)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

(* ********** *)

Definition eqb_option (V : Type) (eqb_V : V -> V -> bool) (ov1 ov2 : option V) : bool :=
  match ov1 with
    Some v1 =>
    match ov2 with
      Some v2 =>
      eqb_V v1 v2
    | None =>
      false
    end
  | None =>
    match ov2 with
      Some v2 =>
      false
    | None =>
      true
    end
  end.

(* ********** *)

Fixpoint eqb_list (V : Type) (eqb_V : V -> V -> bool) (v1s v2s : list V) : bool :=
  match v1s with
    nil =>
    match v2s with
      nil =>
      true
    | v2 :: v2s' =>
      false
    end
  | v1 :: v1s' =>
    match v2s with
      nil =>
      false
    | v2 :: v2s' =>
      eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
    end
  end.

Lemma fold_unfold_eqb_list_nil :
  forall (V : Type)
         (eqb_V : V -> V -> bool)
         (v2s : list V),
    eqb_list V eqb_V nil v2s =
    match v2s with
      nil =>
      true
    | v2 :: v2s' =>
      false
    end.
Proof.
  fold_unfold_tactic eqb_list.
Qed.

Lemma fold_unfold_eqb_list_cons :
  forall (V : Type)
         (eqb_V : V -> V -> bool)
         (v1 : V)
         (v1s' v2s : list V),
    eqb_list V eqb_V (v1 :: v1s') v2s =
    match v2s with
      nil =>
      false
    | v2 :: v2s' =>
      eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
    end.
Proof.
  fold_unfold_tactic eqb_list.
Qed.

(* ***** *)

(* Task 1: *)

Theorem soundness_of_equality_over_lists :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        eqb_V v1 v2 = true -> v1 = v2) ->
    forall v1s v2s : list V,
      eqb_list V eqb_V v1s v2s = true ->
      v1s = v2s.
(*
  Sketch:

  After inducting on v1, we need to consider
  the cases of v2s. 

  In the base case, if v2 is not nil, an 
  absurdity is derived.

  In the inductive case, if v2s is nil, then 
  we can derive an absurdity and use
  discriminate.
  
  Notice that the absurdities show up when we are
  trying to deal with lists of unequal lengths.
  (While traversing down the lists, we hit nil on
   one side first).

  We did not need to do a case analysis to check
  if the values at the head of the list were equal,
  because this was one of our assumptions.

  If the equality function explicitly required the
  lists to be of the same length, there would be
  no need for a case analysis.

*)


Proof.
  (* TODO: Is this a correct use of A,
     or should a different naming convention
     be used *)
  intros V eqb_V A_eqb_V v1s.

  induction v1s as [ | v1 v1s' IHv1s'].

  * intros [ | v2 v2s'].
   
    - intro H_eqb_list_V.
      reflexivity.

    - rewrite -> (fold_unfold_eqb_list_nil V eqb_V (v2 :: v2s')).
      intro H_absurd.
      discriminate H_absurd.
      
  * intros [ | v2  v2s'].

    - rewrite -> (fold_unfold_eqb_list_cons V eqb_V v1 v1s' nil).
      intro H_absurd.
      discriminate H_absurd.
      
    - rewrite -> (fold_unfold_eqb_list_cons V eqb_V v1 v1s' (v2 :: v2s')).
      rewrite -> (andb_true_iff (eqb_V v1 v2) (eqb_list V eqb_V v1s' v2s')).
      (* TODO : Find better names for these *)
      intros [H_eqb_V H_eqb_list_V].

      rewrite -> (A_eqb_V v1 v2 H_eqb_V).
      rewrite -> (IHv1s' v2s' H_eqb_list_V).
      reflexivity.
Qed.

Theorem completeness_of_equality_over_lists :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        v1 = v2 -> eqb_V v1 v2 = true) ->
    forall v1s v2s : list V,
      v1s = v2s ->

      eqb_list V eqb_V v1s v2s = true.

(*

 These two proofs have the same shape, the
 reason being that the cases considered are
 exactly the same.
 
*) 


Proof.
  intros V eqb_V H_v1_equals_v2.

  intro v1s.
  induction v1s as [ | v1 v1s' IHv1s'].

  * intro v2.

    case v2 as [ | v2].

    - intro H_nil.
      rewrite -> (fold_unfold_eqb_list_nil V eqb_V nil).
      reflexivity.

    - intro H_absurd.
      discriminate H_absurd.

  * intro v2.

    case v2 as [ | v2 v2s'].

    - intro H_absurd.
      discriminate H_absurd.

    - intro H_equal.
      rewrite <- H_equal.
      rewrite -> fold_unfold_eqb_list_cons.
      rewrite -> (H_v1_equals_v2 v1 v1 (eq_refl v1)).
      rewrite -> (IHv1s' v1s' (eq_refl v1s')).
      simpl (true && true = true).
      reflexivity.
Qed.
   
      
  (* ********** *)

(* A study of the polymorphic length function: *)

Definition specification_of_list_length (length : forall V : Type, list V -> nat) :=
  (forall V : Type,
      length V nil = 0)
  /\
  (forall (V : Type)
          (v : V)
          (vs' : list V),
     length V (v :: vs') = S (length V vs')).

(* Unit-test function: *)

Definition test_list_length (candidate : forall V : Type, list V -> nat) :=
  (candidate nat nil =? 0) &&
  (candidate bool nil =? 0) &&
  (candidate nat (1 :: nil) =? 1) &&
  (candidate bool (true :: nil) =? 1) &&
  (candidate nat (2 :: 1 :: nil) =? 2) &&
  (candidate bool (false :: true :: nil) =? 2) &&
  (candidate nat (3 :: 2 :: 1 :: nil) =? 3) &&
  (candidate bool (false :: false :: true :: nil) =? 3) &&
  (candidate (list nat) ((1 :: nil) :: (2 :: nil) :: nil) =? 2).

(* The specification specifies at most one length function: *)

Theorem there_is_at_most_one_list_length_function :
  forall (V : Type)
         (list_length_1 list_length_2 : forall V : Type, list V -> nat),
    specification_of_list_length list_length_1 ->
    specification_of_list_length list_length_2 ->
    forall vs : list V,
      list_length_1 V vs = list_length_2 V vs.
Proof.
  intros V list_length_1 list_length_2.
  unfold specification_of_list_length.
  intros [S_list_length_1_nil S_list_length_1_cons]
         [S_list_length_2_nil S_list_length_2_cons]
         vs.
  induction vs as [ | v vs' IHvs'].

  - Check (S_list_length_2_nil V).
    rewrite -> (S_list_length_2_nil V).
    Check (S_list_length_1_nil V).
    exact (S_list_length_1_nil V).

  - Check (S_list_length_1_cons V v vs').
    rewrite -> (S_list_length_1_cons V v vs').
    rewrite -> (S_list_length_2_cons V v vs').
    rewrite -> IHvs'.
    reflexivity.
Qed.

(* Recursive implementation of the length function: *)

Fixpoint list_length (V : Type) (vs : list V) : nat :=
  match vs with
    nil =>
    0
  | v :: vs' =>
    S (list_length V vs')
  end.

Compute (test_list_length list_length).

(* Associated fold-unfold lemmas: *)

Lemma fold_unfold_list_length_nil :
  forall V : Type,
    list_length V nil =
    0.
Proof.
  fold_unfold_tactic list_length.
Qed.

Lemma fold_unfold_list_length_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    list_length V (v :: vs') =
    S (list_length V vs').
Proof.
  fold_unfold_tactic list_length.
Qed.

(* The specification specifies at least one length function: *)

Theorem list_length_satisfies_the_specification_of_list_length :
  specification_of_list_length list_length.
Proof.
  unfold specification_of_list_length.
  exact (conj fold_unfold_list_length_nil fold_unfold_list_length_cons).
Qed.

(* ***** *)

(* Task 2: *)

(* Implement the length function using an accumulator. *)

Fixpoint list_length_acc (V : Type) (vs : list V) (a : nat) :=
  match vs with
  | nil =>
    a
  | v :: vs' => list_length_acc V vs' (S a)
end.                               

Definition list_length_alt (V : Type) (vs : list V) : nat :=
  list_length_acc V vs 0.

Compute (test_list_length list_length_alt).

Lemma fold_unfold_list_length_acc_nil :
  forall (V : Type) (a : nat),
    list_length_acc V nil a =
    a.

Proof.
  fold_unfold_tactic list_length_acc.
Qed.

Lemma fold_unfold_list_length_acc_cons: 
  forall (V : Type)
         (v : V)
         (vs' : list V)
         (a : nat),
    list_length_acc V (v :: vs') a =
    list_length_acc V vs' (S a).

Proof.
   fold_unfold_tactic list_length_acc.
Qed.

Lemma list_length_acc_reset:
  forall (V : Type)
         (vs : list V)
         (a : nat),
     list_length_acc V vs (S a) =
     1 + (list_length_acc V vs a).

Proof.
  intros V vs.
  induction vs as [ | v' vs'].

  * intro a.
    rewrite -> (fold_unfold_list_length_acc_nil V (S a)).
    rewrite -> (fold_unfold_list_length_acc_nil V a).
    rewrite <- (Nat.add_1_l a).
    reflexivity.
    
  * intro a.
    rewrite -> (fold_unfold_list_length_acc_cons V v' vs' (S a)).
    rewrite -> (fold_unfold_list_length_acc_cons V v' vs' a).
    rewrite -> (IHvs' (S a)).
    reflexivity.
Qed.    
    
  
Theorem list_length_alt_satisfies_the_specification_of_list_length :
  specification_of_list_length list_length_alt.

(*
  list_length_acc V (v :: vs) 0 = S (list_length_acc V vs 0).

  The accumulator is keeping track of how many elements we have
  already gone past.

  We could try to prove a more general invariant first in this
  case to show

  list_length_acc V (v :: vs) a = a + (list_length_acc V vs 0).

  We call this trick an accumulator reset.

  The decision to write an accumulator reset came about naturally.
  Trying to prove the special case a = 0 would get one caught in
  a bind since as you keep unfolding, the value of the accumulator
  would keep increasing. The difference between the accumulator on
  each side was however, exactly the same.

  This suggested writing an inductive proof to show that for all
  possible states of the accumulator, adding an element to the list
  would cause the final value returned to increase by one.
*)

Proof.
  unfold specification_of_list_length.
  unfold list_length_alt.

  split.

  * intro V.
    exact (fold_unfold_list_length_acc_nil V 0).

  * intros V v vs.
    rewrite -> (fold_unfold_list_length_acc_cons V v vs 0).
    exact (list_length_acc_reset V vs 0).
Qed.    
    
    
    
      
      
(* ********** *)

(* A study of the polymorphic copy function: *)

Definition specification_of_list_copy (copy : forall V : Type, list V -> list V) :=
  (forall V : Type,
      copy V nil = nil)
  /\
  (forall (V : Type)
          (v : V)
          (vs' : list V),
     copy V (v :: vs') = v :: (copy V vs')).

Definition test_list_copy (candidate : forall V : Type, list V -> list V) :=
  (eqb_list nat Nat.eqb (candidate nat nil) nil) &&
  (eqb_list bool Bool.eqb (candidate bool nil) nil) &&
  (eqb_list nat Nat.eqb (candidate nat (1 :: nil)) (1 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (true :: nil)) (true :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat (2 :: 1 :: nil)) (2 :: 1 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (false :: true :: nil)) (false :: true :: nil)).


(* ***** *)

(* Task 3: *)

(*
   a. Expand the unit-test function for copy with a few more tests.
*)

(*
   b. Implement the copy function recursively.
*)

Fixpoint list_copy (V : Type) (vs : list V) : list V :=
  match vs  with
  | nil =>
    nil
  | v :: vs' =>
    v :: (list_copy V vs')
  end.

Compute test_list_copy list_copy.

(*
   c. State its associated fold-unfold lemmas.
*)

Lemma fold_unfold_list_copy_nil:
  forall V : Type,
    list_copy V nil = nil.

Proof.
  fold_unfold_tactic list_copy.
Qed.

Lemma fold_unfold_list_copy_cons:
  forall (V : Type)
         (v : V)
         (vs' : list V),
         list_copy V (v :: vs') = v :: list_copy V vs'.

Proof.
  fold_unfold_tactic list_copy.
Qed.


(*
   d. Prove whether your implementation satisfies the specification.
*)


(*
  Some specifications directly correspond
  to a computational process..

  In that case we can write the recursive
  function easily and take the conjunction
  of the fold-unfold lemmass for the proof.
*)


Theorem list_copy_satisfies_the_specification_of_list_copy:
  specification_of_list_copy list_copy.  

Proof.
  unfold specification_of_list_copy.

  exact (conj fold_unfold_list_copy_nil fold_unfold_list_copy_cons).
Qed.  



(*
   e. Prove whether copy is idempotent.
*)


Proposition list_copy_is_idempotent :
  forall (V : Type)
         (vs : list V),
    list_copy V (list_copy V vs) = list_copy V vs.

Proof.
  intros V vs.

  induction vs as [ | v vs' IHvs'].

  * rewrite -> (fold_unfold_list_copy_nil V).
    rewrite -> (fold_unfold_list_copy_nil V).
    reflexivity.

  * rewrite -> (fold_unfold_list_copy_cons V v vs').
    rewrite -> (fold_unfold_list_copy_cons V v (list_copy V vs')).
    rewrite -> IHvs'.
    reflexivity.
Qed.


(*
   f. Prove whether copying a list preserves its length.
*)


Proposition list_copy_preserves_list_length :
  forall (V : Type)
         (vs : list V),
    list_length V (list_copy V vs) = list_length V vs.

Proof.
  intros V vs.

  induction vs as [ | v vs' IHvs'].

  * rewrite -> (fold_unfold_list_length_nil V).
    rewrite -> (fold_unfold_list_copy_nil V).
    rewrite -> (fold_unfold_list_length_nil V).
    reflexivity.

  * rewrite -> (fold_unfold_list_length_cons V).
    rewrite -> (fold_unfold_list_copy_cons V).
    rewrite -> (fold_unfold_list_length_cons V).
    rewrite -> IHvs'.
    reflexivity.
Qed.    

(*
  When writing the proof for the inductive step,
  without thinking, the first approach was to
  copy the steps in the base case and simply change
  "nil" to "cons".

  This almost worked, all that needed to be done
  was to use the induction hypothesis.

  Now we can reflect, think and see why this shot
  in the dark hit the mark.. 

  When translating a recursive specification that
  directly gives a recursive function, we can make
  u


*)


(*
   g. Subsidiary question: can you think of a strikingly simple implementation of the copy function?
      if so, pray show that it satisfies the specification of copy;
      is it equivalent to your recursive implementation?
*)

(* ********** *)

(* A study of the polymorphic append function: *)

Definition specification_of_list_append (append : forall V : Type, list V -> list V -> list V) :=
  (forall (V : Type)
          (v2s : list V),
      append V nil v2s = v2s)
  /\
  (forall (V : Type)
          (v1 : V)
          (v1s' v2s : list V),
      append V (v1 :: v1s') v2s = v1 :: append V v1s' v2s).

(* ***** *)

(* Task 4: *)

(*
   a. Define a unit-test function for list_append.
*)

(*
   b. Implement the list_append function recursively.
*)

(*
Fixpoint list_append (V : Type) (v1s v2s : list V) : list V :=
  ...
*)

(*
   c. State its associated fold-unfold lemmas.
*)

(*
   d. Prove that your implementation satisfies the specification.
*)

(*
   e. Prove whether nil is neutral on the left of list_append.
*)

(*
   f. Prove whether nil is neutral on the right of list_append.
*)

(*
   g. Prove whether list_append is commutative.
*)

(*
   h. Prove whether list_append is associative.
*)

(*
   i. Prove whether appending two lists preserves their length.
*)

(*
Proposition list_append_and_list_length_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    list_length V (list_append V v1s v2s) = list_length V v1s + list_length V v2s.
Proof.
Abort.
*)

(*
   j. Prove whether list_append and list_copy commute with each other.
*)

(*
Proposition list_append_and_list_copy_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    list_copy V (list_append V v1s v2s) = list_append V (list_copy V v1s) (list_copy V v2s).
Proof.
Abort.
*)

(* ********** *)

(* A study of the polymorphic reverse function: *)

Definition specification_of_list_reverse (reverse : forall V : Type, list V -> list V) :=
  forall append : forall W : Type, list W -> list W -> list W,
    specification_of_list_append append ->
    (forall V : Type,
        reverse V nil = nil)
    /\
    (forall (V : Type)
            (v : V)
            (vs' : list V),
        reverse V (v :: vs') = append V (reverse V vs') (v :: nil)).

(* ***** *)

(* Task 5: *)

(*
   a. Define a unit-test function for an implementation of the reverse function.
*)

(*
   b. Implement the reverse function recursively, using list_append.
*)

(*
Fixpoint list_reverse (V : Type) (vs : list V) : list V :=
...
*)

(*
   c. State the associated fold-unfold lemmas.
*)

(*
   d. Prove whether your implementation satisfies the specification.
*)

(*
   e. Prove whether list_reverse is involutory.
*)

(*
Proposition list_reverse_is_involutory :
  forall (V : Type)
         (vs : list V),
    list_reverse V (list_reverse V vs) = vs.
Proof.
Abort.
*)

(*
   f. Prove whether reversing a list preserves its length.
*)

(*
   g. Do list_append and list_reverse commute with each other (hint: yes they do) and if so how?
*)

(*
   h. Implement the reverse function using an accumulator instead of using list_append.
*)

(*
Definition list_reverse_alt (V : Type) (vs : list V) : list V :=
...
*)

(*
   i. Revisit the propositions above (involution, preservation of length, commutation with append)
      and prove whether reverse_v1 satisfies them.
      Two proof strategies are possible:
      (1) self-contained proofs with Eureka lemmas, and
      (2) proofs that hinge on the equivalence of list_reverse_alt and list_reverse.
      This subtask is very instructive, but optional.
*)

(* ********** *)

(* A study of the polymorphic map function: *)

Definition specification_of_list_map (map : forall V W : Type, (V -> W) -> list V -> list W) :=
  (forall (V W : Type)
          (f : V -> W),
      map V W f nil = nil)
  /\
  (forall (V W : Type)
          (f : V -> W)
          (v : V)
          (vs' : list V),
      map V W f (v :: vs') = f v :: map V W f vs').

(* ***** *)

(* Task 6:

   a. Prove whether the specification specifies at most one map function.
*)

Proposition there_is_at_most_one_list_map_function :
  forall list_map1 list_map2 : forall V W : Type, (V -> W) -> list V -> list W,
      specification_of_list_map list_map1 ->
      specification_of_list_map list_map2 ->
      forall (V W : Type)
             (f : V -> W)
             (vs : list V),
        list_map1 V W f vs = list_map2 V W f vs.
Proof.
  intros list_map1 list_map2 S_list_map1 S_list_map2 V W f vs.
  induction vs as [ | v vs' IHvs'].
  - unfold specification_of_list_map in S_list_map1.
    destruct S_list_map1 as [fold_unfold_list_map1_nil _].
    destruct S_list_map2 as [fold_unfold_list_map2_nil _].
    rewrite -> (fold_unfold_list_map2_nil V W f).
    exact (fold_unfold_list_map1_nil V W f).
  - unfold specification_of_list_map in S_list_map1.
    destruct S_list_map1 as [_ fold_unfold_list_map1_cons].
    destruct S_list_map2 as [_ fold_unfold_list_map2_cons].
    rewrite -> (fold_unfold_list_map1_cons V W f v vs').
    rewrite -> (fold_unfold_list_map2_cons V W f v vs').
    rewrite -> IHvs'.
    reflexivity.
Qed.

(*
   b. Implement the map function recursively.
*)

Fixpoint list_map (V W : Type) (f : V -> W) (vs : list V) : list W :=
  match vs with
    nil =>
    nil
  | v :: vs' =>
    f v :: list_map V W f vs'
  end.

(*
   c. State the associated fold-unfold lemmas.
*)

Lemma fold_unfold_list_map_nil :
  forall (V W : Type)
         (f : V -> W),
    list_map V W f nil =
    nil.
Proof.
  fold_unfold_tactic list_map.
Qed.

Lemma fold_unfold_list_map_cons :
  forall (V W : Type)
         (f : V -> W)
         (v : V)
         (vs' : list V),
    list_map V W f (v :: vs') =
    f v :: list_map V W f vs'.
Proof.
  fold_unfold_tactic list_map.
Qed.

(*
   d. Prove whether your implementation satisfies the specification.
*)

Proposition list_map_satisfies_the_specification_of_list_map :
  specification_of_list_map list_map.
Proof.
  unfold specification_of_list_map.
  exact (conj fold_unfold_list_map_nil fold_unfold_list_map_cons).
Qed.

(*
   e. Implement the copy function as an instance of list_map.
*)

(*
Definition list_copy_as_list_map (V : Type) (vs : list V) : list V :=
  ...
*)

(*
Hint: Does list_copy_as_list_map satisfy the specification of list_copy?
*)

(*
   f. Prove whether mapping a function over a list preserves the length of this list.
*)

(*
   g. Do list_map and list_append commute with each other and if so how?
*)

(*
   h. Do list_map and list_reverse commute with each other and if so how?
*)

(*
   i. Do list_map and list_reverse_alt commute with each other and if so how?
*)

(*
   j. Define a unit-test function for the map function
      and verify that your implementation satisfies it.
*)

(* ********** *)

(* A study of the polymorphic fold-right and fold-left functions: *)

Definition specification_of_list_fold_right (fold_right : forall V W : Type, W -> (V -> W -> W) -> list V -> W) :=
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W),
     fold_right V W nil_case cons_case nil =
     nil_case)
  /\
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W)
          (v : V)
          (vs' : list V),
     fold_right V W nil_case cons_case (v :: vs') =
     cons_case v (fold_right V W nil_case cons_case vs')).

Definition specification_of_list_fold_left (fold_left : forall V W : Type, W -> (V -> W -> W) -> list V -> W) :=
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W),
     fold_left V W nil_case cons_case nil =
     nil_case)
  /\
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W)
          (v : V)
          (vs' : list V),
     fold_left V W nil_case cons_case (v :: vs') =
     fold_left V W (cons_case v nil_case) cons_case vs').

(* ***** *)

(* Task 7:

   a. Implement the fold-right function recursively.
*)

Fixpoint list_fold_right (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  match vs with
    nil =>
    nil_case
  | v :: vs' =>
    cons_case v (list_fold_right V W nil_case cons_case vs')
  end.

(*
   b. Implement the fold-left function recursively.
*)

Fixpoint list_fold_left (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  match vs with
    nil =>
    nil_case
  | v :: vs' =>
    list_fold_left V W (cons_case v nil_case) cons_case vs'
  end.

(*
   c. state the fold-unfold lemmas associated to list_fold_right and to list_fold_left
*)

Lemma fold_unfold_list_fold_right_nil :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W),
    list_fold_right V W nil_case cons_case nil =
    nil_case.
Proof.
  fold_unfold_tactic list_fold_right.
Qed.

Lemma fold_unfold_list_fold_right_cons :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v : V)
         (vs' : list V),
    list_fold_right V W nil_case cons_case (v :: vs') =
    cons_case v (list_fold_right V W nil_case cons_case vs').
Proof.
  fold_unfold_tactic list_fold_right.
Qed.

Lemma fold_unfold_list_fold_left_nil :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W),
    list_fold_left V W nil_case cons_case nil =
    nil_case.
Proof.
  fold_unfold_tactic list_fold_left.
Qed.

Lemma fold_unfold_list_fold_left_cons :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v : V)
         (vs' : list V),
    list_fold_left V W nil_case cons_case (v :: vs') =
    list_fold_left V W (cons_case v nil_case) cons_case vs'.
Proof.
  fold_unfold_tactic list_fold_left.
Qed.

(*
   d. Prove that each of your implementations satisfies the corresponding specification.
*)

(*
   e. Which function do foo and bar (defined just below) compute?
*)

(*
Definition foo (V : Type) (vs : list V) :=
  list_fold_right V (list V) nil (fun v vs => v :: vs) vs.
*)

(*
Definition bar (V : Type) (vs : list V) :=
  list_fold_left V (list V) nil (fun v vs => v :: vs) vs.
*)

(*
   f. Implement the length function either as an instance of list_fold_right or as an instance of list_fold_left, and justify your choice.
*)

(*
   g. Implement the copy function either as an instance of list_fold_right or as an instance of list_fold_left, and justify your choice.
*)

(*
   h. Implement the append function either as an instance of list_fold_right or as an instance of list_fold_left, and justify your choice.
*)

(*
   i. Implement the reverse function either as an instance of list_fold_right or as an instance of list_fold_left, and justify your choice.
*)

(*
   j. Implement the map function either as an instance of list_fold_right or as an instance of list_fold_left, and justify your choice.
*)

(*
   k. Implement eqb_list either as an instance of list_fold_right or as an instance of list_fold_left, and justify your choice.
*)

(*
   l. Implement list_fold_right as an instance of list_fold_left, using list_reverse.
*)

(*
   m. Implement list_fold_left as an instance of list_fold_right, using list_reverse.
*)

(*
   n. Implement list_fold_right as an instance of list_fold_left, without using list_reverse.
*)

(*
Definition list_fold_right_left (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  ...
*)

(*
   o. Implement list_fold_left as an instance of list_fold_right, without using list_reverse.
*)

(*
Definition list_fold_left_right (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  ...
*)

(*
   p. Show that
      if the cons case is a function that is left permutative (defined just below),
      applying list_fold_left and applying list_fold_right
      to a nil case, this cons case, and a list
      give the same result
*)
  
Definition is_left_permutative (V W : Type) (op2 : V -> W -> W) :=
  forall (v1 v2 : V)
         (w : W),
    op2 v1 (op2 v2 w) = op2 v2 (op2 v1 w).

(*
Theorem folding_left_and_right_over_lists :
  forall (V W : Type)
         (cons_case : V -> W -> W),
    is_left_permutative V W cons_case ->
    forall (nil_case : W)
           (vs : list V),
      list_fold_left  V W nil_case cons_case vs =
      list_fold_right V W nil_case cons_case vs.
Proof.
Abort.
*)

(*
   q. Can you think of corollaries of this property?
*)

Lemma plus_is_left_permutative :
  is_left_permutative nat nat plus.
Proof.
Abort.

(*
Corollary example_for_plus :
  forall ns : list nat,
    list_fold_left nat nat 0 plus ns = list_fold_right nat nat 0 plus ns.
Proof.
  Check (folding_left_and_right_over_lists nat nat plus plus_is_left_permutative 0).
  exact (folding_left_and_right_over_lists nat nat plus plus_is_left_permutative 0).
Qed.
*)

(* What do you make of this corollary?
   Can you think of more such corollaries?
*)

(*
   r. Subsidiary question: does the converse of Theorem folding_left_and_right_over_lists hold?
*)

(*
Theorem folding_left_and_right_over_lists_converse :
  forall (V W : Type)
         (cons_case : V -> W -> W),
    (forall (nil_case : W)
            (vs : list V),
        list_fold_left  V W nil_case cons_case vs =
        list_fold_right V W nil_case cons_case vs) ->
    is_left_permutative V W cons_case.
Proof.
Abort.
*)

(* ********** *)

(* Task 8: *)

Fixpoint nat_fold_right (V : Type) (zero_case : V) (succ_case : V -> V) (n : nat) : V :=
  match n with
    O =>
    zero_case
  | S n' =>
    succ_case (nat_fold_right V zero_case succ_case n')
  end.

Lemma fold_unfold_nat_fold_right_O :
  forall (V : Type)
         (zero_case : V)
         (succ_case : V -> V),
    nat_fold_right V zero_case succ_case O =
    zero_case.
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

Lemma fold_unfold_nat_fold_right_S :
  forall (V : Type)
         (zero_case : V)
         (succ_case : V -> V)
         (n' : nat),
    nat_fold_right V zero_case succ_case (S n') =
    succ_case (nat_fold_right V zero_case succ_case n').
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

Fixpoint nat_fold_left (V : Type) (zero_case : V) (succ_case : V -> V) (n : nat) : V :=
  match n with
    O =>
    zero_case
  | S n' =>
    nat_fold_left V (succ_case zero_case) succ_case n'
  end.

Lemma fold_unfold_nat_fold_left_O :
  forall (V : Type)
         (zero_case : V)
         (succ_case : V -> V),
    nat_fold_left V zero_case succ_case O =
    zero_case.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

Lemma fold_unfold_nat_fold_left_S :
  forall (V : Type)
         (zero_case : V)
         (succ_case : V -> V)
         (n' : nat),
    nat_fold_left V zero_case succ_case (S n') =
    nat_fold_left V (succ_case zero_case) succ_case n'.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

(* ***** *)

(* The addition function: *)

Definition recursive_specification_of_addition (add : nat -> nat -> nat) :=
  (forall y : nat,
      add O y = y)
  /\
  (forall x' y : nat,
      add (S x') y = S (add x' y)).

Definition tail_recursive_specification_of_addition (add : nat -> nat -> nat) :=
  (forall y : nat,
      add O y = y)
  /\
  (forall x' y : nat,
      add (S x') y = add x' (S y)).

Definition test_add (candidate: nat -> nat -> nat) : bool :=
  (Nat.eqb (candidate 0 0) 0)
  &&
  (Nat.eqb (candidate 0 1) 1)
  &&
  (Nat.eqb (candidate 1 0) 1)
  &&
  (Nat.eqb (candidate 1 1) 2)
  &&
  (Nat.eqb (candidate 1 2) 3)
  &&
  (Nat.eqb (candidate 2 1) 3)
  &&
  (Nat.eqb (candidate 2 2) 4)
  &&
  (* commutativity: *)
  (Nat.eqb (candidate 2 10) (candidate 10 2))
  &&
  (* associativity: *)
  (Nat.eqb (candidate 2 (candidate 5 10))
           (candidate (candidate 2 5) 10))
  (* etc. *)
  .

(* Testing the unit-test function: *)

Compute (test_add Nat.add).

Fixpoint r_add (x y : nat) : nat :=
  match x with
    O =>
    y
  | S x' =>
    S (r_add x' y)
  end.

Lemma fold_unfold_r_add_O :
  forall y : nat,
    r_add O y =
    y.
Proof.
  fold_unfold_tactic r_add.
Qed.

Lemma fold_unfold_r_add_S :
  forall x' y : nat,
    r_add (S x') y =
    S (r_add x' y).
Proof.
  fold_unfold_tactic r_add.
Qed.

(* Implement the addition function as an instance of nat_fold_right or nat_fold_left, your choice. *)

Definition r_add_right (x y : nat) : nat :=
  nat_fold_right nat y (fun ih => S ih) x.

Compute (test_add r_add_right).

Proposition r_add_satisfies_the_recursive_specification_of_addition :
  recursive_specification_of_addition r_add_right.
Proof.
  unfold recursive_specification_of_addition, r_add_right.
  split.
  - intro y.
    exact (fold_unfold_nat_fold_right_O nat y (fun ih => S ih)).
  - intros x' y.
    exact (fold_unfold_nat_fold_right_S nat y (fun ih => S ih) x').
Qed.

(*
Definition r_add_left (x y : nat) : nat :=
  ... nat_fold_left ... ... ... x ... .
*)

(* ***** *)

(* The power function: *)

Definition recursive_specification_of_power (power : nat -> nat -> nat) :=
  (forall x : nat,
      power x 0 = 1)
  /\
  (forall (x : nat)
          (n' : nat),
      power x (S n') = x * power x n').

Definition test_power (candidate : nat -> nat -> nat) : bool :=
  (candidate 2 0 =? 1) &&
  (candidate 10 2 =? 10 * 10) &&
  (candidate 3 2 =? 3 * 3).

Fixpoint r_power (x n : nat) : nat :=
  match n with
    O =>
    1
  | S n' =>
    x * r_power x n'
  end.

Compute (test_power r_power).

Lemma fold_unfold_r_power_O :
  forall x : nat,
    r_power x O =
    1.
Proof.
  fold_unfold_tactic r_power.
Qed.

Lemma fold_unfold_r_power_S :
  forall x n' : nat,
    r_power x (S n') =
    x * r_power x n'.
Proof.
  fold_unfold_tactic r_power.
Qed.

Fixpoint tr_power_aux (x n a : nat) : nat :=
  match n with
    O =>
    a
  | S n' =>
    tr_power_aux x n' (x * a)
  end.

Lemma fold_unfold_tr_power_aux_O :
  forall x a : nat,
    tr_power_aux x 0 a =
    a.
Proof.
  fold_unfold_tactic tr_power_aux.
Qed.

Lemma fold_unfold_tr_power_v1_S :
  forall x n' a : nat,
    tr_power_aux x (S n') a =
    tr_power_aux x n' (x * a).
Proof.
  fold_unfold_tactic tr_power_aux.
Qed.

Definition tr_power (x n : nat) : nat :=
  tr_power_aux x n 1.

Compute (test_power tr_power).

(*
Definition r_power_right (x n : nat) : nat :=
  ... nat_fold_right ... ... ... n ... .

Compute (test_power r_power_right).
*)

(*
Definition r_power_left (x n : nat) : nat :=
  ... nat_fold_left ... ... ... n ... .

Compute (test_power r_power_left).
*)

(*
Definition tr_power_right (x n : nat) : nat :=
  ... nat_fold_right ... ... ... n ... .

Compute (test_power tr_power_right).
*)

(*
Definition tr_power_left (x n : nat) : nat :=
  ... nat_fold_left ... ... ... n ... .

Compute (test_power tr_power_left).
*)

(* ***** *)

(* The factorial function: *)

Definition recursive_specification_of_the_factorial_function (fac : nat -> nat) :=
  (fac 0 = 1)
  /\
  (forall n' : nat,
    fac (S n') = S n' * fac n').

Definition test_fac (candidate : nat -> nat) : bool :=
  (candidate 0 =? 1)
  &&
  (candidate 1 =? 1 * 1)
  &&
  (candidate 2 =? 2 * 1 * 1)
  &&
  (candidate 3 =? 3 * 2 * 1 * 1)
  &&
  (candidate 4 =? 4 * 3 * 2 * 1 * 1)
  &&
  (candidate 5 =? 5 * 4 * 3 * 2 * 1 * 1).

Fixpoint r_fac (n : nat) : nat :=
  match n with
    O =>
    1
  | S n' =>
    S n' * r_fac n'
  end.

Compute (test_fac r_fac).

Lemma fold_unfold_r_fac_O :
  r_fac 0 =
  1.
Proof.
  fold_unfold_tactic r_fac.
Qed.

Lemma fold_unfold_r_fac_S :
  forall n' : nat,
    r_fac (S n') =
    S n' * r_fac n'.
Proof.
  fold_unfold_tactic r_fac.
Qed.

Proposition r_fac_satisfies_the_recursive_specification_of_the_factorial_function :
  recursive_specification_of_the_factorial_function r_fac.
Proof.
  unfold recursive_specification_of_the_factorial_function.
  exact (conj fold_unfold_r_fac_O fold_unfold_r_fac_S).
Qed.

(* Re-implement r_fac as an instance of nat_fold_right or nat_fold_left, your choice: *)

(*
Definition r_fac_right (n : nat) : nat :=
  ... nat_fold_right ... ... ... n ... .

Compute (test_fac r_fac_right).

Definition fac_left (n : nat) : nat :=
  ... nat_fold_left ... ... ... n ... .

Compute (test_fac r_fac_left).
*)

Fixpoint tr_fac_aux (n a : nat) : nat :=
  match n with
    O =>
    a
  | S n' =>
    tr_fac_aux n' (S n' * a)
  end.

Definition tr_fac (n : nat) : nat :=
  tr_fac_aux n 1.

Compute (test_fac tr_fac).

Lemma fold_unfold_tr_fac_aux_O :
  forall a : nat,
    tr_fac_aux 0 a =
    a.
Proof.
  fold_unfold_tactic tr_fac_aux.
Qed.

Lemma fold_unfold_tr_fac_aux_S :
  forall n' a : nat,
    tr_fac_aux (S n') a =
    tr_fac_aux n' (S n' * a).
Proof.
  fold_unfold_tactic tr_fac_aux.
Qed.

Proposition tr_fac_satisfies_the_recursive_specification_of_the_factorial_function :
  recursive_specification_of_the_factorial_function tr_fac.
Proof.
  unfold recursive_specification_of_the_factorial_function.
Abort.

(* Re-implement tr_fac as an instance of nat_fold_right or nat_fold_left, your choice: *)

(*
Definition tr_fac_right (n : nat) : nat :=
  ... nat_fold_right ... ... ... n ... .

Compute (test_fac tr_fac_right).

Definition tr_fac_left (n : nat) : nat :=
  ... nat_fold_left ... ... ... n ... .

Compute (test_fac tr_fac_alt).
*)

(* ***** *)

Definition specification_of_the_fibonacci_function (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  forall n'' : nat,
    fib (S (S n'')) = fib (S n'') + fib n''.

Definition test_fib (candidate: nat -> nat) : bool :=
  (candidate 0 =? 0)
  &&
  (candidate 1 =? 1)
  &&
  (candidate 2 =? 1)
  &&
  (candidate 3 =? 2)
  &&
  (candidate 4 =? 3)
  &&
  (candidate 5 =? 5)
  (* etc. *).

Fixpoint r_fib (n : nat) : nat :=
  match n with
    0 =>
    0
  | S n' =>
    match n' with
      0 =>
      1
    | S n'' =>
      r_fib n' + r_fib n''
    end
  end.

Compute (test_fib r_fib).

Lemma fold_unfold_r_fib_O :
  r_fib O =
  0.
Proof.
  fold_unfold_tactic r_fib.
Qed.

Lemma fold_unfold_r_fib_S :
  forall n' : nat,
    r_fib (S n') =
    match n' with
      0 =>
      1
    | S n'' =>
      r_fib n' + r_fib n''
    end.
Proof.
  fold_unfold_tactic r_fib.
Qed.

Corollary fold_unfold_r_fib_SO :
  r_fib 1 =
  1.
Proof.
  rewrite -> (fold_unfold_r_fib_S 0).
  reflexivity.
Qed.

Corollary fold_unfold_r_fib_SS :
  forall n'' : nat,
    r_fib (S (S n'')) =
    r_fib (S n'') + r_fib n''.
Proof.
  intro n''.
  rewrite -> (fold_unfold_r_fib_S (S n'')).
  reflexivity.
Qed.

Proposition r_fib_satisfies_the_specification_of_the_fibonacci_function :
  specification_of_the_fibonacci_function r_fib.
Proof.
  unfold specification_of_the_fibonacci_function.
  exact (conj fold_unfold_r_fib_O (conj fold_unfold_r_fib_SO fold_unfold_r_fib_SS)).
Qed.

(* Implement the Fibonacci function as an instance of nat_fold_right or nat_fold_left, your choice: *)

(*
Definition fib_right (n : nat) : nat :=
  ... nat_fold_right ... ... ... n ... .

Compute (test_fib tr_fib_right).

Definition fib_left (n : nat) : nat :=
  ... nat_fold_left ... ... ... n ... .

Compute (test_fib fib_left).
*)

(* ********** *)

(* Task 9 *)

(* Under which conditions -- if any -- are nat_fold_right and nat_fold_left equivalent? *)

(* ********** *)

(* end of midterm-project.v *)
