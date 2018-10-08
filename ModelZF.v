Require Import basic.
Require Import Sublogic.
Require Import Models GenModelSyntax.
Require Import ZF ZFcoc.

(** Set-theoretical model of the Calculus of Constructions in IZF *)

Module ZFsets <: Sets.

  Definition X := set.
Definition inX : X -> X -> Prop := in_set.
Definition eqX : X -> X -> Prop := eq_set.
Definition inclX : X -> X -> Prop := incl_set.
Definition eqX_equiv : Equivalence eqX := eq_set_equiv.
Notation "x ∈ y" := (inX x y).
Notation "x == y" := (eqX x y).

Lemma in_ext: Proper (eqX ==> eqX ==> iff) inX.
Proof in_set_morph.

Definition eq_fun (x:X) (f1 f2:X->X) :=
  forall y1 y2, y1 ∈ x -> y1 == y2 -> f1 y1 == f2 y2.

End ZFsets.

(** * Instantiation of the abstract model of CC *)

Module CCM <: CC_Model.

Include ZFsets.

Definition props : X := props.
Definition app : X -> X -> X := cc_app.
Definition lam : X -> (X -> X) -> X := cc_lam.
Definition prod : X -> (X -> X) -> X := cc_prod.

Lemma lam_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  lam x1 f1 == lam x2 f2.
Proof.
intros.
apply cc_lam_ext; intros; trivial.
Qed.

Lemma app_ext:
  forall x1 x2 : X, x1 == x2 ->
  forall x3 x4 : X, x3 == x4 ->
  app x1 x3 == app x2 x4.
Proof cc_app_morph.

Lemma prod_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  prod x1 f1 == prod x2 f2.
Proof.
intros.
apply cc_prod_ext; intros; trivial.
Qed.

Lemma prod_intro : forall dom f F,
  eq_fun dom f f ->
  eq_fun dom F F ->
  (forall x, x ∈ dom -> f x ∈ F x) ->
  lam dom f ∈ prod dom F.
Proof cc_prod_intro.

Lemma prod_elim : forall dom f x F,
  eq_fun dom F F ->
  f ∈ prod dom F ->
  x ∈ dom ->
  app f x ∈ F x.
Proof fun dom f x F _ H H0 => cc_prod_elim dom f x F H H0.


Lemma impredicative_prod : forall dom F,
  eq_fun dom F F ->
  (forall x, x ∈ dom -> F x ∈ props) ->
  prod dom F ∈ props.
Proof fun dom F _ => cc_impredicative_prod dom F.

Lemma beta_eq:
  forall dom F x,
  eq_fun dom F F ->
  x ∈ dom ->
  app (lam dom F) x == F x.
Proof cc_beta_eq.

End CCM.
