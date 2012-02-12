Require Export basic.

(* This module defines interfaces implementing various flavour
   of set theory, from Zermelo to IZF_R and IZF_C (ZF)
 *)
Reserved Notation "x \in y" (at level 60).
Reserved Notation "x == y" (at level 70).
Reserved Notation "x \incl y" (at level 70).

(************************************************************************)
(* A generic set theory signature *)

Module Type SetTheory.

Parameter
 (set : Type)
 (eq_set : set -> set -> Prop)
 (in_set : set -> set -> Prop).

Notation "x \in y" := (in_set x y).
Notation "x == y" := (eq_set x y).

Parameter
 (eq_set_ax : forall a b, a == b <-> (forall x, x \in a <-> x \in b))
 (in_reg : forall a a' b, a == a' -> a \in b -> a' \in b).

End SetTheory.

(* ...and with well-foundation axiom.
   Plays the role of regularity axiom, but in an intutionistic
   setting (regularity is classical). *)
Module Type WfSetTheory.
Include SetTheory.

Parameter
 (wf_ax: forall P:set->Prop,
    (forall x, (forall y, y \in x -> P y) -> P x) ->
    forall x, P x).

End WfSetTheory.

(************************************************************************)
(* Zermelo set theory:
   - empty set
   - pair axiom
   - union axiom
   - separation axiom
   - powerset axiom
   - infinity
 *)

Module Type Zermelo_sig.

Include WfSetTheory.

Parameter
 (empty : set)
 (pair : set -> set -> set)
 (union : set -> set)
 (infinite : set)
 (power : set -> set).

Parameter
 (empty_ax: forall x, ~ x \in empty)
 (pair_ax: forall a b x, x \in pair a b <-> (x == a \/ x == b))
 (union_ax: forall a x, x \in union a <-> (exists2 y, x \in y & y \in a))
 (infinity_ax1: empty \in infinite)
 (infinity_ax2: forall x,
                x \in infinite -> union (pair x (pair x x)) \in infinite)
 (power_ax: forall a x, x \in power a <-> (forall y, y \in x -> y \in a)).

End Zermelo_sig.

(* Existential version *)
Module Type Zermelo_Ex_sig.
Include WfSetTheory.

Parameter
 (empty_ex: exists empty, forall x, ~ x \in empty)
 (pair_ex: forall a b, exists c, forall x, x \in c <-> (x == a \/ x == b))
 (union_ex: forall a, exists b,
    forall x, x \in b <-> (exists2 y, x \in y & y \in a))
 (infinity_ex: exists2 infinite,
    (exists2 empty, (forall x, ~ x \in empty) & empty \in infinite) &
    (forall x, x \in infinite ->
     exists2 y, (forall z, z \in y <-> (z == x \/ z \in x)) &
       y \in infinite))
 (power_ex: forall a, exists b,
     forall x, x \in b <-> (forall y, y \in x -> y \in a)).

End Zermelo_Ex_sig.

(************************************************************************)
(*
  IZF_R, Myhill's version of IZF:
   - regularity is stated as a well-foundation axiom
   - we use replacement, not collection
 *)

(* Skolemized version of IZF_R *)

Module Type IZF_R_sig.

Include Zermelo_sig.

Parameter
 (repl : set -> (set -> set -> Prop) -> set).

Parameter
 (repl_mono: forall a a',
    (forall z, z \in a -> z \in a') ->
    forall (R R':set->set->Prop),
    (forall x x', x==x' -> forall y y', y==y' -> (R x y <-> R' x' y')) ->
    forall z, z \in repl a R -> z \in repl a' R')
 (repl_ax: forall a (R:set->set->Prop),
    (forall x x' y y', x \in a -> R x y -> R x' y' -> x == x' -> y == y') ->
    forall x, x \in repl a R <-> (exists2 y, y \in a & exists2 x', x == x' & R y x')).

End IZF_R_sig.


(* Existential versions (Zermelo still skolemized) *)

Module Type IZF_R_HalfEx_sig.

Include Zermelo_sig.

Parameter
 (repl_ex:
    forall a (R:set->set->Prop),
    (forall x x' y y', x \in a -> R x y -> R x' y' -> x == x' -> y == y') ->
    exists b, forall x, x \in b <-> (exists2 y, y \in a & exists2 x', x == x' & R y x')).

End IZF_R_HalfEx_sig.

(* Fully existential version *)

Module Type IZF_R_Ex_sig.

Include Zermelo_Ex_sig.

Parameter
 (repl_ex:
    forall a (R:set->set->Prop),
    (forall x x' y y', x \in a -> R x y -> R x' y' -> x == x' -> y == y') ->
    exists b, forall x, x \in b <-> (exists2 y, y \in a & exists2 x', x == x' & R y x')).

End IZF_R_Ex_sig.

(************************************************************************)
(* Collection and ZF *)

Module Type IZF_C_sig.

Include Zermelo_sig.

Parameter
 (coll_ax : forall A (R:set->set->Prop), 
    (forall x x' y y', x \in A -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x, x \in A -> exists y, R x y) ->
    exists B, forall x, x \in A -> exists2 y, y \in B & R x y).

End IZF_C_sig.

(************************************************************************)

Module Type Choice_Sig (S:SetTheory).
Import S.
Parameter
  (choose : set -> set)
  (choose_morph : forall x x', x == x' -> choose x == choose x')
  (choose_ax : forall a, (exists x, x \in a) -> choose a \in a).
End Choice_Sig.
