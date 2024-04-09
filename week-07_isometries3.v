(* week-07_isometries3.v *)
(* LPP 2024 - CS3234 2023-2024, Sem2 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 08 Mar 2024 *)

(* ********** *)

(* A formal study of isometries of the equilateral triangle, *)
(* after Chantal Keller, Damien Pous and Sylvain Chevillard. *)

(* ********** *)

Inductive Rotation : Type :=
  R000 : Rotation  (* 0 degrees (identity) *)
| R120 : Rotation  (* 120 degrees *)
| R240 : Rotation. (* 240 degrees *)

(* ********** *)

(* Performing two rotations in a row, clockwise. *)
(* "RaR" stands for "a Rotation after a Rotation" *)

(*
Definition RaR (r2 r1: Rotation) : ... :=
  match r1 with
    R000 => match r2 with
              R000 => ...
            | R120 => ...
            | R240 => ...
            end
  | R120 => match r2 with
              R000 => ...
            | R120 => ...
            | R240 => ...
            end
  | R240 => match r2 with
              R000 => ...
            | R120 => ...
            | R240 => ...
            end
  end.
*)

(* Some properties: *)

(*
Proposition R000_is_neutral_for_RaR_on_the_left :
  forall r : Rotation,
    RaR R000 r = r.
Proof.
Abort.

Proposition R000_is_neutral_for_RaR_on_the_right :
  forall r : Rotation,
    RaR r R000 = r.
Proof.
Abort.

Proposition RaR_is_commutative :
  forall r1 r2 : Rotation,
    RaR r2 r1 = RaR r1 r2.
Proof.
Abort.

Proposition RaR_is_associative :
  forall r1 r2 r3 : Rotation,
    RaR (RaR r3 r2) r1 = RaR r3 (RaR r2 r1).
Proof.
Abort.

Proposition RaR_is_nilpotent_with_order_??? :
  forall r : Rotation,
    ...
Proof.
Abort.
*)

(* ********** *)

(* The following symmetries are indexed by the invariant vertex: *)

Inductive Reflection : Type :=
  S_NN : Reflection  (* North, at the top *)
| S_SW : Reflection  (* South-West, at the bottom left *)
| S_SE : Reflection. (* South-East, at the bottom right *)

(* These reflections are symmetries here. *)

(* Performing two reflections in a row. *)
(* "SaS" stands for "a Symmetry after a Symmetry" *)

(*
Definition SaS (s2 s1 : Reflection) : ... :=
  match s1 with
    S_NN => match s2 with
              S_NN => ...
            | S_SW => ...
            | S_SE => ...
            end
  | S_SW => match s2 with
              S_NN => ...
            | S_SW => ...
            | S_SE => ...
            end
  | S_SE => match s2 with
              S_NN => ...
            | S_SW => ...
            | S_SE => ...
            end
  end.
*)

(* is SaS commutative? *)
(* is SaS associative? *)
(* is SaS nilpotent?   *)

(* ********** *)

(* Performing a rotation and then a reflection in a row. *)
(* "SaR" stands for "a Symmetry after a Rotation" *)

(*
Definition SaR (s : Reflection) (r : Rotation) : Reflection :=
  match r with
    R000 => match s with
              S_NN => ...
            | S_SW => ...
            | S_SE => ...
            end
  | R120 => match s with
              S_NN => ...
            | S_SW => ...
            | S_SE => ...
            end
  | R240 => match s with
              S_NN => ...
            | S_SW => ...
            | S_SE => ...
            end
  end.
*)

(* ********** *)

(* Performing a reflection and then a rotation in a row. *)
(* "RaS" stands for "a Rotation after a Symmetry" *)

(*
Definition RaS (r : Rotation) (s : Reflection) : Reflection :=
  match s with
    S_NN => match r with
              R000 => ...
            | R120 => ...
            | R240 => ...
            end
  | S_SW => match r with
              R000 => ...
            | R120 => ...
            | R240 => ...
            end
  | S_SE => match r with
              R000 => ...
            | R120 => ...
            | R240 => ...
            end
  end.
*)

(* ********** *)

Inductive Isomorphism : Type :=
| IR : Rotation -> Isomorphism
| IS : Reflection -> Isomorphism.

(* Identity: *)

Definition Id : Isomorphism := IR R000.

(* Composition: *)

(*
Definition C (i2 i1 : Isomorphism) : Isomorphism :=
  match i1 with
    IR r1 => match i2 with
               IR r2 => IR (RaR r2 r1)
             | IS s2 => IS (SaR s2 r1)
             end
  | IS s1 => match i2 with
               IR r2 => IS (RaS r2 s1)
             | IS s2 => IR (SaS s2 s1)
             end
  end.

Proposition Id_is_neutral_on_the_left_of_C :
  forall i : Isomorphism,
    C Id i = i.
Proof.
Abort.

Proposition Id_is_neutral_on_the_right_of_C :
  forall i : Isomorphism,
    C i Id = i.
Proof.
Abort.

Proposition C_is_associative :
  forall i1 i2 i3 : Isomorphism,
    C i3 (C i2 i1) = C (C i3 i2) i1.
Proof.
Abort.

Lemma composing_an_isomorphism_is_injective_on_the_right :
  forall i x y : Isomorphism,
    C i x = C i y -> x = y.
Proof.
Abort.

Lemma composing_an_isomorphism_is_injective_on_the_left :
  forall i x y : Isomorphism,
    C x i = C y i -> x = y.
Proof.
Abort.

Lemma composing_an_isomorphism_is_surjective_on_the_right :
  forall i2 i3 : Isomorphism,
    exists i1 : Isomorphism,
      C i2 i1 = i3.
Proof.
Abort.

Lemma composing_an_isomorphism_is_surjective_on_the_left :
  forall i1 i3 : Isomorphism,
    exists i2 : Isomorphism,
      C i2 i1 = i3.
Proof.
Abort.

Proposition C_over_rotations_is_nilpotent_with_order_3 :
  forall r : Rotation,
    C (C (IR r) (IR r)) (IR r) = Id.
Proof.
Abort.

Proposition C_over_symmetries_is_nilpotent_with_order_2 :
  forall s : Reflection,
    C (IS s) (IS s) = Id.
Proof.
Abort.

Proposition C_is_nilpotent_with_order_??? :
  forall i : Isomorphism,
    ...
Proof.
Abort.
*)

(* ********** *)

(* Let us now introduce the vertices: *)

Inductive Vertex : Type := (* enumerated clockwise *)
  NN : Vertex
| SW : Vertex
| SE : Vertex.

(* And let us define the effect of applying an isomorphism
   to a vertex: *)

Definition A (i : Isomorphism) (v : Vertex) : Vertex :=
  match i with
    IR r => match r with
              R000 => match v with
                        NN => NN
                      | SW => SW
                      | SE => SE
                      end
            | R120 => match v with
                        NN => SW
                      | SW => SE
                      | SE => NN
                      end
            | R240 => match v with
                        NN => SE
                      | SE => SW
                      | SW => NN
                      end
            end
  | IS s => match s with
              S_NN => match v with
                        NN => NN
                      | SW => SE
                      | SE => SW
                      end
            | S_SE => match v with
                        NN => SW
                      | SW => NN
                      | SE => SE
                      end
            | S_SW => match v with
                        NN => SE
                      | SW => SW
                      | SE => NN
                      end
              end
  end.

(*
Proposition A_is_equivalent_to_C :
  forall (i1 i2 : Isomorphism) (v : Vertex),
    A i2 (A i1 v) = A (C i2 i1) v.
Proof.
Abort.

Proposition applying_an_isomorphism_is_injective :
  forall (i : Isomorphism) (v1 v2 : Vertex),
    (A i v1 = A i v2) -> v1 = v2.
Proof.
Abort.

Proposition applying_an_isomorphism_is_surjective :
  forall (i : Isomorphism) (v2 : Vertex),
    exists v1 : Vertex,
      A i v1 = v2.
Proof.
Abort.
*)

(* ********** *)

(* Intensional equality:
   two isomorphisms are equal
   iff
   they are are constructed alike.
 *)

Definition intensional_equality (i1 i2: Isomorphism) : Prop :=
  i1 = i2.

(* Extensional equality:
   two isomorphisms are equal
   iff
   their graphs are the same.
 *)

Definition extensional_equality (i1 i2: Isomorphism) : Prop :=
  forall v : Vertex,
    A i1 v = A i2 v.

(* The two notions of equalities coincide: *)

Proposition the_two_equalities_are_the_same :
  forall i1 i2 : Isomorphism,
    intensional_equality i1 i2 <-> extensional_equality i1 i2.
Proof.
Abort.

(* ********** *)

(*
Lemma isomorphism_equality_in_context_on_the_left :
  forall x y i : Isomorphism,
    x = y -> C x i = C y i.
Proof.
Abort.

Proposition take_five :
  forall i : Isomorphism,
    extensional_equality (C (C (C (C i i) i) i) i) Id
    ->
    i = Id.
Proof.
Abort.

Proposition characteristic_property_of_Id :
  forall i : Isomorphism,
    i = Id <-> forall v : Vertex, A i v = v.
Proof.
Abort.

Proposition one_for_the_road :
  forall i : Isomorphism,
    (forall v : Vertex, A i v = v)
    ->
    C i i = Id.
Proof.
Abort.

Proposition notable_property_of_Id :
  exists i : Isomorphism,
    exists v : Vertex,
      not (A i v = v -> i = Id).
Proof.
Abort.

Proposition notable_property_of_Id' :
  not (forall (i : Isomorphism) (v : Vertex),
         A i v = v -> i = Id).
Proof.
Abort.

Proposition notable_property_of_symmetries :
  forall (i : Isomorphism)
         (v : Vertex),
    A i v = v ->
    ((i = IR R0)
     \/
     (exists s : Reflection,
        i = IS s)).
Proof.
Abort.

Proposition notable_property_of_symmetries' :
  forall i : Isomorphism,
    (exists v : Vertex,
       A i v = v) ->
    ((i = IR R0)
     \/
     (exists s : Reflection,
        i = IS s)).
Proof.
Abort.

Proposition one_more_for_the_road :
  forall (i : Isomorphism) (v : Vertex),
    A i v = v -> C i i = Id.
Proof.
Abort.
*)

(* ********** *)

(* end of week-07_isometries3.v *)
