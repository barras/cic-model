
Require Export basic.
Require Export Setoid Morphisms.

Module Type CC_Model.

Parameter X : Type.
Parameter inX : X -> X -> Prop.
Parameter eqX : X -> X -> Prop.
Parameter eqX_equiv : Equivalence eqX.
Notation "x \in y" := (inX x y) (at level 60).
Notation "x == y" := (eqX x y) (at level 70).

Parameter in_ext: Proper (eqX ==> eqX ==> iff) inX.

Parameter props : X.
Parameter app : X -> X -> X.
Parameter lam : X -> (X -> X) -> X.
Parameter prod : X -> (X -> X) -> X.

Definition eq_fun (x:X) (f1 f2:X->X) :=
  forall y1 y2, y1 \in x -> y1 == y2 -> f1 y1 == f2 y2.

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

Parameter prod_intro : forall dom f F,
  eq_fun dom f f ->
  eq_fun dom F F ->
  (forall x, x \in dom -> f x \in F x) ->
  lam dom f \in prod dom F.

Parameter prod_elim : forall dom f x F,
  eq_fun dom F F ->
  f \in prod dom F ->
  x \in dom ->
  app f x \in F x.

Parameter impredicative_prod : forall dom F,
  eq_fun dom F F ->
  (forall x, x \in dom -> F x \in props) ->
  prod dom F \in props.

Parameter beta_eq:
  forall dom F x,
  eq_fun dom F F ->
  x \in dom ->
  app (lam dom F) x == F x.

Existing Instance eqX_equiv.
Existing Instance in_ext.
Existing Instance app_ext.

End CC_Model.


Module Type ECC_Model.

  Declare Module CC : CC_Model.
  Import CC.

  Parameter u_card : nat -> X.
  Parameter u_card_in1 : props \in u_card 0.
  Parameter u_card_in2 : forall n, u_card n \in u_card (S n).
  Parameter u_card_incl : forall n x, x \in u_card n -> x \in u_card (S n).
  Parameter u_card_prod : forall n X Y,
    eq_fun X Y Y ->
    X \in u_card n ->
    (forall x, x \in X -> Y x \in u_card n) ->
    prod X Y \in u_card n.
  Parameter u_card_prod2 : forall n X Y,
    eq_fun X Y Y ->
    X \in props ->
    (forall x, x \in X -> Y x \in u_card n) ->
    prod X Y \in u_card n.

End ECC_Model.

Module Type CC_Model2.

Parameter X : Type.
Parameter inX : X -> X -> Prop.
Parameter eqX : X -> X -> Prop.
Parameter eqX_equiv : Equivalence eqX.
Notation "x \in y" := (inX x y) (at level 60).
Notation "x == y" := (eqX x y) (at level 70).

Parameter in_ext: Proper (eqX ==> eqX ==> iff) inX.

Parameter props : X.
Parameter kinds : X.
Parameter app : X -> X -> X.
Parameter lam : X -> (X -> X) -> X.
Parameter prod : X -> (X -> X) -> X.

Definition eq_fun (x:X) (f1 f2:X->X) :=
  forall y1 y2, y1 \in x -> y1 == y2 -> f1 y1 == f2 y2.

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

Parameter props_typ : props \in kinds.

Parameter prod_typ : forall dom F s1 s2,
  s1 == props \/ s1 == kinds ->
  s2 == props \/ s1 == kinds ->
  eq_fun dom F F ->
  dom \in s1 ->
  (forall x, x \in dom -> F x \in s2) ->
  prod dom F \in s2.

Parameter prod_intro : forall dom f F s1,
  eq_fun dom f f ->
  eq_fun dom F F ->
  s1 == props \/ s1 == kinds ->
  dom \in s1 ->
  (forall x, x \in dom -> f x \in F x) ->
  lam dom f \in prod dom F.

Parameter prod_elim : forall dom f x F,
  eq_fun dom F F ->
  f \in prod dom F ->
  x \in dom ->
  app f x \in F x.

Parameter beta_eq:
  forall dom F x,
  eq_fun dom F F ->
  x \in dom ->
  app (lam dom F) x == F x.

Existing Instance eqX_equiv.
Existing Instance in_ext.
Existing Instance app_ext.

End CC_Model2.
