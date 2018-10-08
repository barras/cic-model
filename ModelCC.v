Require Import basic.
Require Import Sublogic.
Require Import Models GenModelSyntax.
Require Import ZF ZFrelations ZFcoc ModelZF.

(** Set-theoretical model of the Calculus of Constructions in IZF *)

(** * Instantiating the generic model construction *)

Module BuildModel := MakeModel(CCM).

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
(** Subtyping *)

(*
Definition sub_typ_covariant : forall e U1 U2 V1 V2,
  U1 <> kind ->
  eq_typ e U1 U2 ->
  sub_typ (U1::e) V1 V2 ->
  sub_typ e (Prod U1 V1) (Prod U2 V2).
intros.
apply sub_typ_covariant; trivial.
intros.
unfold eqX, lam, app.
unfold inX in H2.
unfold prod, ZFuniv_real.prod in H2; rewrite El_def in H2.
apply cc_eta_eq in H2; trivial.
Qed.
*)

(** Universes *)
(*
Lemma cumul_Type : forall e n, sub_typ e (type n) (type (S n)).
red; simpl; intros.
red; intros.
apply ecc_incl; trivial.
Qed.

Lemma cumul_Prop : forall e, sub_typ e prop (type 0).
red; simpl; intros.
red; intros.
apply G_trans with props; trivial.
 apply (grot_succ_typ gr).

 apply (grot_succ_in gr).
Qed.
*)


(** The model in ZF implies the consistency of CC *)

Require Import Term Env.
Require Import TypeJudge.
Load "template/Library.v".

Lemma cc_consistency : forall M M', ~ eq_typ nil M M' FALSE.
Proof.
unfold FALSE; red in |- *; intros.
specialize BuildModel.int_sound with (1 := H); intro.
destruct H0 as (H0,_).
simpl in H0.
apply abstract_consistency with (M:=int_trm(unmark_app M)) (FF:=empty); trivial.
 unfold props; apply empty_in_power.

 red; intros.
 apply empty_ax with (1:=H1); trivial.
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
  \/ (exists w, w ∈ a) /\ z == app f1 (choose a).

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