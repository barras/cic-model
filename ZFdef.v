Require Export basic.

(** This module defines interfaces implementing various flavour
   of set theory, from Zermelo to IZF_R and IZF_C (ZF)
 *)
Reserved Notation "x ∈ y" (at level 60).
Reserved Notation "x == y" (at level 70).
Reserved Notation "x ⊆ y" (at level 70).

(************************************************************************)
(** * A generic set theory signature *)
Require Import Sublogic.

Module Type SetTheory.

Parameter
 (set : Type)
 (eq_set : set -> set -> Prop)
 (in_set : set -> set -> Prop).

Notation "x ∈ y" := (in_set x y).
Notation "x == y" := (eq_set x y).

Parameter
 (eq_set_ax : forall a b, a == b <-> (forall x, x ∈ a <-> x ∈ b))
 (in_reg : forall a a' b, a == a' -> a ∈ b -> a' ∈ b).

End SetTheory.

(** ...and with well-foundation axiom.
   Plays the role of regularity axiom, but in an intutionistic
   setting (regularity is classical). *)
Module Type WfSetTheory (L:SublogicTheory).
Include SetTheory.

Parameter
 (wf_ax: forall P:set->Prop,
    (forall x, L.isL (P x)) ->
    (forall x, (forall y, y ∈ x -> P y) -> P x) ->
    forall x, P x).

End WfSetTheory.

(************************************************************************)
(** * Zermelo set theory:
   - empty set
   - pair axiom
   - union axiom
   - separation axiom
   - powerset axiom
   - infinity
 *)

Module Type Zermelo_sig (L:SublogicTheory).

Include WfSetTheory L.
Import L.

Parameter
 (empty : set)
 (pair : set -> set -> set)
 (union : set -> set)
 (subset : set -> (set -> Prop) -> set)
 (infinite : set)
 (power : set -> set).

Parameter
 (empty_ax: forall x, x ∈ empty -> #False)
 (pair_ax: forall a b x, x ∈ pair a b <-> #(x == a \/ x == b))
 (union_ax: forall a x, x ∈ union a <-> #exists2 y, x ∈ y & y ∈ a)
 (subset_ax : forall a P x,
    x ∈ subset a P <-> (x ∈ a /\ #exists2 x', x==x' & P x'))
 (infinity_ax1: empty ∈ infinite)
 (infinity_ax2: forall x,
                x ∈ infinite -> union (pair x (pair x x)) ∈ infinite)
 (power_ax: forall a x, x ∈ power a <-> (forall y, y ∈ x -> y ∈ a)).

End Zermelo_sig.

(** ** Existential version *)
Module Type Zermelo_Ex_sig (L:SublogicTheory).
Include WfSetTheory L.
Import L.

Parameter
 (empty_ex: L.Tr(exists empty, forall x, x ∈ empty -> #False))
 (pair_ex: forall a b, #exists c, forall x, x ∈ c <-> #(x == a \/ x == b))
 (union_ex: forall a, #exists b,
    forall x, x ∈ b <-> #exists2 y, x ∈ y & y ∈ a)
 (subset_ex : forall a P, #exists b,
    forall x, x ∈ b <-> (x ∈ a /\ exists2 x', x==x' & P x'))
 (infinity_ex: #exists2 infinite,
    #exists2 empty, (forall x, x ∈ empty -> L.Tr False) &
        empty ∈ infinite &
    (forall x, x ∈ infinite ->
     #exists2 y, (forall z, z ∈ y <-> (z == x \/ z ∈ x)) &
       y ∈ infinite))
 (power_ex: forall a, #exists b,
     forall x, x ∈ b <-> (forall y, y ∈ x -> y ∈ a)).

End Zermelo_Ex_sig.

(************************************************************************)
(** * IZF_R, Myhill's version of IZF:
   - regularity is stated as a well-foundation axiom
   - we use replacement, not collection
 *)

(** Skolemized version of IZF_R *)

Module Type IZF_R_sig (L:SublogicTheory).

Include Zermelo_sig L.
Import L.

Parameter
 (repl : set -> (set -> set -> Prop) -> set).

Parameter
 (repl_mono: forall a a',
    (forall z, z ∈ a -> z ∈ a') ->
    forall (R R':set->set->Prop),
    (forall x x', x==x' -> forall y y', y==y' -> (R x y <-> R' x' y')) ->
    forall z, z ∈ repl a R -> z ∈ repl a' R')
 (repl_ax: forall a (R:set->set->Prop),
    (forall x x' y y', x ∈ a -> R x y -> R x' y' -> x == x' -> y == y') ->
    forall x, x ∈ repl a R <->
      #exists2 y, y ∈ a & exists2 x', x == x' & R y x').

End IZF_R_sig.


(** Existential versions (Zermelo still skolemized) *)

Module Type IZF_R_HalfEx_sig (L:SublogicTheory).

Include Zermelo_sig L.
Import L.

Parameter
 (repl_ex : forall a (R:set->set->Prop),
    (forall x x' y y', x ∈ a -> R x y -> R x' y' -> x == x' -> y == y') ->
    #exists b, forall x, x ∈ b <-> #exists2 y, y ∈ a & exists2 x', x == x' & R y x').

End IZF_R_HalfEx_sig.

(** Fully existential version *)

Module Type IZF_R_Ex_sig (L:SublogicTheory).

Include Zermelo_Ex_sig L.
Import L.

Parameter
 (repl_ex : forall a (R:set->set->Prop),
    (forall x x' y y', x ∈ a -> R x y -> R x' y' -> x == x' -> y == y') ->
    #exists b, forall x, x ∈ b <-> #exists2 y, y ∈ a & exists2 x', x == x' & R y x').

End IZF_R_Ex_sig.

(************************************************************************)
(** * Collection and ZF *)

Module Type IZF_C_sig (L:SublogicTheory).

Include Zermelo_sig L.
Import L.

Parameter
 (coll_ex : forall A (R:set->set->Prop), 
    Proper (eq_set ==> eq_set ==> iff) R ->
    #exists B, forall x, x ∈ A ->
         (#exists y, R x y) -> #exists2 y, y ∈ B & R x y).

End IZF_C_sig.

(** With skolemized collection *)
Module Type ZF_sig (L:SublogicTheory).

Include Zermelo_sig L.
Import L.

Parameter
 (coll : set -> (set->set->Prop) -> set)
 (coll_ax : forall A R, 
    Proper (eq_set==>eq_set==>iff) R ->
    forall x, x ∈ A ->
      (#exists y, R x y) -> #exists2 y, y ∈ coll A R & R x y).

End ZF_sig.

(************************************************************************)
(*
 -----
 *)

Module Type Choice_Sig (L:SublogicTheory) (S:SetTheory).
Import L S.
Parameter
  (choose : set -> set)
  (choose_morph : forall x x', x == x' -> choose x == choose x')
  (choose_ax : forall a, (#exists x, x ∈ a) -> choose a ∈ a).
End Choice_Sig.
