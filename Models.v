Require Export basic.
Require Export Setoid Morphisms.

Reserved Notation "x ∈ y" (at level 60).
Reserved Notation "x == y" (at level 70).

(** Abstract term model of CC *)
Module Type CC_Terms.

Parameter X : Type.
Parameter inX : X -> X -> Prop.
Parameter eqX : X -> X -> Prop.
Parameter eqX_equiv : Equivalence eqX.
Notation "x ∈ y" := (inX x y).
Notation "x == y" := (eqX x y).

Parameter in_ext: Proper (eqX ==> eqX ==> iff) inX.

Parameter props : X.
Parameter app : X -> X -> X.
Parameter lam : X -> (X -> X) -> X.
Parameter prod : X -> (X -> X) -> X.

Definition eq_fun (x:X) (f1 f2:X->X) :=
  forall y1 y2, y1 ∈ x -> y1 == y2 -> f1 y1 == f2 y2.

Parameter lam_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  lam x1 f1 == lam x2 f2.

Parameter app_ext: Proper (eqX ==> eqX ==> eqX) app.

Parameter prod_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  prod x1 f1 == prod x2 f2.

Parameter beta_eq:
  forall dom F x,
  eq_fun dom F F ->
  x ∈ dom ->
  app (lam dom F) x == F x.

Existing Instance eqX_equiv.
Existing Instance in_ext.
Existing Instance app_ext.


End CC_Terms.

(** Abstract model of CC *)
Module Type CC_Model.

Include CC_Terms.

Parameter prod_intro : forall dom f F,
  eq_fun dom f f ->
  eq_fun dom F F ->
  (forall x, x ∈ dom -> f x ∈ F x) ->
  lam dom f ∈ prod dom F.

Parameter prod_elim : forall dom f x F,
  eq_fun dom F F ->
  f ∈ prod dom F ->
  x ∈ dom ->
  app f x ∈ F x.

Parameter impredicative_prod : forall dom F,
  eq_fun dom F F ->
  (forall x, x ∈ dom -> F x ∈ props) ->
  prod dom F ∈ props.

End CC_Model.

(** Extension of CC_Model to ensure we can automatically derive
   the strong normalization model.
 *)
Module Type CC_Daimon.
  Include CC_Model.

  Parameter daimon : X.
  Parameter app_daimon : forall x, app daimon x == daimon.

  Parameter dec_ty : X -> X.
  Parameter dec_ty_morph : Proper (eqX==>eqX) dec_ty.
  Parameter enc_round : forall T x,
    x ∈ dec_ty T <-> x == daimon \/ x ∈ T.

  Parameter dec_prop :
    forall P, P ∈ dec_ty props -> dec_ty P ∈ props.
Existing Instance dec_ty_morph.

End CC_Daimon.

(** Model of ECC: CC + universe hierarchy *)

Module Type ECC_Model.

  Declare Module CC : CC_Model.
  Import CC.

  Parameter u_card : nat -> X.
  Parameter u_card_in1 : props ∈ u_card 0.
  Parameter u_card_in2 : forall n, u_card n ∈ u_card (S n).
  Parameter u_card_incl : forall n x, x ∈ u_card n -> x ∈ u_card (S n).
  Parameter u_card_prod : forall n X Y,
    eq_fun X Y Y ->
    X ∈ u_card n ->
    (forall x, x ∈ X -> Y x ∈ u_card n) ->
    prod X Y ∈ u_card n.
  Parameter u_card_prod2 : forall n X Y,
    eq_fun X Y Y ->
    X ∈ props ->
    (forall x, x ∈ X -> Y x ∈ u_card n) ->
    prod X Y ∈ u_card n.

End ECC_Model.

(** A CC model where kinds form an element of the model. *)

Module Type CC_Model2.

Include CC_Terms.

Parameter kinds : X.

Parameter props_typ : props ∈ kinds.

Parameter prod_typ : forall dom F s1 s2,
  s1 == props \/ s1 == kinds ->
  s2 == props \/ s1 == kinds ->
  eq_fun dom F F ->
  dom ∈ s1 ->
  (forall x, x ∈ dom -> F x ∈ s2) ->
  prod dom F ∈ s2.

Parameter prod_intro : forall dom f F s1,
  eq_fun dom f f ->
  eq_fun dom F F ->
  s1 == props \/ s1 == kinds ->
  dom ∈ s1 ->
  (forall x, x ∈ dom -> f x ∈ F x) ->
  lam dom f ∈ prod dom F.

Parameter prod_elim : forall dom f x F,
  eq_fun dom F F ->
  f ∈ prod dom F ->
  x ∈ dom ->
  app f x ∈ F x.

End CC_Model2.

