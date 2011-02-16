Require Export Setoid.

(* This module defines interfaces implementing Myhill's version of IZF:
   - regularity is stated as a well-foundation axiom
   - we use replacement, not collection
 *)

(* Skolemized version of IZF *)

Module Type IZF_sig.

Parameter
 (set : Type)
 (empty : set)
 (pair : set -> set -> set)
 (union : set -> set)
 (infinite : set)
 (power : set -> set)
 (repl : set -> (set -> set -> Prop) -> set)
 (eq_set : set -> set -> Prop)
 (in_set : set -> set -> Prop).

Notation "x \in y" := (in_set x y) (at level 60).
Notation "x == y" := (eq_set x y) (at level 70).

Parameter
 (eq_set_ax : forall a b, a == b <-> (forall x, x \in a <-> x \in b))
 (in_reg : forall a a' b, a == a' -> a \in b -> a' \in b)

 (empty_ax: forall x, ~ x \in empty)
 (pair_ax: forall a b x, x \in pair a b <-> (x == a \/ x == b))
 (union_ax: forall a x, x \in union a <-> (exists2 y, x \in y & y \in a))
 (infinity_ax1: empty \in infinite)
 (infinity_ax2: forall x,
                x \in infinite -> union (pair x (pair x x)) \in infinite)
 (power_ax: forall a x, x \in power a <-> (forall y, y \in x -> y \in a))
 (repl_mono: forall a a',
    (forall z, z \in a -> z \in a') ->
    forall (R R':set->set->Prop),
    (forall x x', x==x' -> forall y y', y==y' -> (R x y <-> R' x' y')) ->
    forall z, z \in repl a R -> z \in repl a' R')
 (repl_ax:
    forall a (R:set->set->Prop),
    (forall x x' y y', x \in a -> R x y -> R x' y' -> x == x' -> y == y') ->
    forall x, x \in repl a R <-> (exists2 y, y \in a & exists2 x', x == x' & R y x'))
 (wf_ax: forall P:set->Prop,
    (forall x, (forall y, y \in x -> P y) -> P x) ->
    forall x, P x).

End IZF_sig.


(* Existential *)

Module Type IZF_Ex_sig.

Parameter
 (set : Type)
 (eq_set : set -> set -> Prop)
 (in_set : set -> set -> Prop).

Notation "x \in y" := (in_set x y) (at level 60).
Notation "x == y" := (eq_set x y) (at level 70).

Parameter
 (eq_set_ax : forall a b, a == b <-> (forall x, x \in a <-> x \in b))
 (in_reg : forall a a' b, a == a' -> a \in b -> a' \in b)

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
     forall x, x \in b <-> (forall y, y \in x -> y \in a))
 (repl_ex:
    forall a (R:set->set->Prop),
    (forall x x' y y', x \in a -> R x y -> R x' y' -> x == x' -> y == y') ->
    exists b, forall x, x \in b <-> (exists2 y, y \in a & exists2 x', x == x' & R y x'))
 (wf_ax: forall P:set->Prop,
    (forall x, (forall y, y \in x -> P y) -> P x) ->
    forall x, P x).

End IZF_Ex_sig.

Module Type Choice_Sig (S:IZF_sig).
Import S.
Parameter
  (choose : set -> set)
  (choose_morph : forall x x', x == x' -> choose x == choose x')
  (choose_ax : forall a, (exists x, x \in a) -> choose a \in a).
End Choice_Sig.
