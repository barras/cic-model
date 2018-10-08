Require Import basic.
Require Import Sublogic.
Require Import Models GenModelSyntax.
Require Import ZF ZFcoc.

(** Set-theoretical model of the Classical Calculus of Constructions in IZF *)

(** * Instantiation of the abstract model of CC *)

Module ClassicCCM <: CC_Model.

Definition X := set.
Definition inX : X -> X -> Prop := in_set.
Definition eqX : X -> X -> Prop := eq_set.
Definition inclX : X -> X -> Prop := incl_set.
Definition eqX_equiv : Equivalence eqX := eq_set_equiv.
Notation "x ∈ y" := (inX x y).
Notation "x == y" := (eqX x y).

Lemma in_ext: Proper (eqX ==> eqX ==> iff) inX.
Proof in_set_morph.

Definition props : X := cl_props.
Definition app : X -> X -> X := cc_app.
Definition lam : X -> (X -> X) -> X := cc_lam.
Definition prod : X -> (X -> X) -> X := cc_prod.

Definition eq_fun (x:X) (f1 f2:X->X) :=
  forall y1 y2, y1 ∈ x -> y1 == y2 -> f1 y1 == f2 y2.

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
Proof cc_cl_impredicative_prod.

Lemma beta_eq:
  forall dom F x,
  eq_fun dom F F ->
  x ∈ dom ->
  app (lam dom F) x == F x.
Proof cc_beta_eq.

End ClassicCCM.

(** * Instantiating the generic model construction *)

Module BuildModel := MakeModel(ClassicCCM).

Import BuildModel T J R.

Lemma El_int_arr T U i :
  int (Prod T (lift 1 U)) i == cc_arr (int T i) (int U i).
simpl.
apply cc_prod_ext.
 reflexivity.

 red; intros.
 rewrite simpl_int_lift.
 rewrite lift0_term; reflexivity.
Qed.

(** The model in ZF implies the consistency of CC *)

Require Import Term Env.
Require Import TypeJudge.
Load "template/Library.v".

Lemma mt_cl_props: empty ∈ cl_props.
Proof.
apply subset_intro.
 unfold props; apply empty_in_power.
 unfold p2P.

 intros [ ].
 intro in_mt.
 apply empty_ax in in_mt; trivial.
Qed.
Hint Resolve mt_cl_props.

Lemma em_consistent :
  let FF := T.Prod T.prop (T.Ref 0) in
  let N p := T.Prod p FF in
  let EM := T.Prod T.prop (T.Prod (N (N (T.Ref 0))) (T.Ref 1)) in
  val_ok (EM::nil) (fun _ => empty).
intros; red; intros.
destruct n as [ | [|?]]; try discriminate.
injection H; clear H; intros; subst T.
simpl. unfold ClassicCCM.prod, ClassicCCM.props.
red.
apply cc_forall_intro.
 do 2 red; intros.
 apply cc_arr_morph; trivial.
 apply cc_arr_morph; [|reflexivity].
 apply cc_arr_morph; [trivial|reflexivity].
intros P Pty.
assert (Pty' := Pty).
apply subset_ax in Pty'; destruct Pty' as (Pty',(P',eqP,Pcl)).
rewrite <- eqP in Pcl.
apply cc_forall_intro; [auto with *|].
intros prf nnpty.
apply Pcl.
intro.
apply cc_prod_elim with (x:=empty) in nnpty.
 apply cc_prod_elim with (2:=mt_cl_props) in nnpty.
 apply empty_ax in nnpty; trivial.

 apply cc_forall_intro; auto with *.
 intros p pty. 
 elim H.
 rewrite props_proof_irrelevance with (P:=P) (x:=p) in pty; trivial.
Qed.

Lemma cl_cc_consistency M M': ~ eq_typ (EM::nil) M M' FALSE.
Proof.
unfold FALSE; red in |- *; intros.
specialize BuildModel.int_sound with (1 := H); intro.
destruct H0 as (H0,_).
simpl in H0.
apply abstract_theory_consistency with (1:=mt_cl_props) (4:=H0).
 exists (fun _ => empty).
 apply em_consistent.

 red; intros.
 apply empty_ax with (1:=H1).
Qed.
