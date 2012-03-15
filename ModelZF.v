Require Import basic.
Require Import Sublogic.
Require Import Models GenModelSyntax.
Require Import ZF ZFcoc.

(** Set-theoretical model of the Calculus of Constructions in IZF *)

(** * Instantiation of the abstract model of CC *)

Module CCM <: CC_Model.

Definition X := set.
Definition inX : X -> X -> Prop := in_set.
Definition eqX : X -> X -> Prop := eq_set.
Definition eqX_equiv : Equivalence eqX := eq_set_equiv.
Notation "x \in y" := (inX x y).
Notation "x == y" := (eqX x y).

Lemma in_ext: Proper (eqX ==> eqX ==> iff) inX.
Proof in_set_morph.

Definition props : X := props.
Definition app : X -> X -> X := cc_app.
Definition lam : X -> (X -> X) -> X := cc_lam.
Definition prod : X -> (X -> X) -> X := cc_prod.

Definition eq_fun (x:X) (f1 f2:X->X) :=
  forall y1 y2, y1 \in x -> y1 == y2 -> f1 y1 == f2 y2.

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
  (forall x, x \in dom -> f x \in F x) ->
  lam dom f \in prod dom F.
Proof cc_prod_intro.

Lemma prod_elim : forall dom f x F,
  eq_fun dom F F ->
  f \in prod dom F ->
  x \in dom ->
  app f x \in F x.
Proof fun dom f x F _ H H0 => cc_prod_elim dom f x F H H0.


Lemma impredicative_prod : forall dom F,
  eq_fun dom F F ->
  (forall x, x \in dom -> F x \in props) ->
  prod dom F \in props.
Proof fun dom F _ => cc_impredicative_prod dom F.

Lemma beta_eq:
  forall dom F x,
  eq_fun dom F F ->
  x \in dom ->
  app (lam dom F) x == F x.
Proof cc_beta_eq.

End CCM.

(** * Instantiating the generic model construction *)

Module BuildModel := MakeModel(CCM).

Require Import Term Env.
Require Import TypeJudge.
Load "template/Library.v".

(** Consistency of CC *)
Lemma cc_consistency : forall M M', ~ eq_typ nil M M' FALSE.
Proof.
unfold FALSE; red in |- *; intros.
specialize BuildModel.int_sound with (1 := H); intro.
destruct H0 as (H0,_).
red in H0; simpl in H0.
setoid_replace (CCM.prod CCM.props (fun x => x)) with empty in H0.
 eapply empty_ax; apply H0 with (i:=fun _ => empty).
 red; intros.
 destruct n; discriminate.

 apply empty_ext; red; intros.
 assert (empty \in props) by
   (unfold props; apply empty_in_power).
 specialize cc_prod_elim with (1:=H1) (2:=H2); intro.
 apply empty_ax with (1:=H3).
Qed.

(*begin hide*)
Module TypChoice (C : Choice_Sig CoqSublogicThms IZF).

Import C.
Import BuildModel.
Import CCM.
Import T J R.

Require Import ZFrepl.

Definition CH_spec a f1 f2 z :=
     a == empty /\ z == app f2 (lam empty (fun _ => empty))
  \/ (exists w, w \in a) /\ z == app f1 (choose a).

Parameter CH_spec_u : forall a f1 f2, uchoice_pred (CH_spec a f1 f2).

Definition CH : term.
left; exists (fun i => uchoice (CH_spec (i 3) (i 1) (i 0))).
admit.
Defined.

(* forall X, X + (X->False) is inhabited *)
Lemma typ_choice :
  typ
    ((*f1*)Prod (Prod (*X*)(Ref 2) (Prod prop (Ref 0))) (*P*)(Ref 2) ::
     (*f2*)Prod (*X*)(Ref 1) (*P*)(Ref 1) ::
     (*P*)kind::(*X*)kind::nil)
    CH (*P*)(Ref 2).
red; simpl; intros.
generalize (H 0 _ (eq_refl _)); simpl; unfold V.lams, V.shift; simpl; intros.
generalize (H 1 _ (eq_refl _)); simpl; unfold V.lams, V.shift; simpl; intros.
clear H.
set (P := i 2) in *; clearbody P.
set (Y := i 3) in *; clearbody Y.
generalize (uchoice_def _ (CH_spec_u Y (i 1) (i 0))).
set (w := uchoice (CH_spec Y (i 1) (i 0))) .
clearbody w; unfold CH_spec; intros.
destruct H.
 destruct H.
 rewrite H2.
 refine (prod_elim _ _ _ _ _ H0 _).
  admit.
 apply eq_elim with (prod empty (fun _ => prod props (fun P=>P))).
  apply prod_ext.
   auto with *.

   red; reflexivity.
 apply prod_intro; intros.
  admit.
  admit.
 elim empty_ax with x; trivial.

 destruct H.
 rewrite H2.
 refine (prod_elim _ _ _ _ _ H1 _).
  admit.
 apply choose_ax; trivial.
Qed.

End TypChoice.
(*end hide*)