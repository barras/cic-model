(** Model construction (entailing consistency) for ECC based on
    ZF + infinitely many Grothendieck universes.
*)

Require Import List Bool Models.
Require Import ZF ZFsum ZFnats ZFrelations ZFord ZFfix ZFgrothendieck ZFcoc ZFecc.
Require Import ModelZF.

Import BuildModel.
Import T J R.

Lemma sub_typ_covariant e U1 U2 V1 V2 :
  U1 <> kind ->
  eq_typ e U1 U2 ->
  sub_typ (U1::e) V1 V2 ->
  sub_typ e (Prod U1 V1) (Prod U2 V2).
red; intros.
revert H3; apply cc_prod_covariant.
 do 2 red; intros.
 rewrite H4; reflexivity.

 apply H0; trivial.

 red; intros.
 revert H4; apply H1.
 apply vcons_add_var; trivial.
Qed.

(** Universes: version where type 0 is a universe of hereditarily
    finite sets (HF). Hence it does not contain nat. It is a model
    of ECC.
 *)

Module WithFinitistUniverse.

Definition type (n:nat) := cst (ecc n).

Lemma typ_Prop : forall e, typ e prop (type 0).
red; intros; simpl.
apply (ecc_in1 0).
Qed.

Lemma typ_Type : forall e n, typ e (type n) (type (S n)).
red; intros; simpl.
apply (ecc_in2 n).
Qed.

Lemma cumul_Type : forall e n, sub_typ e (type n) (type (S n)).
red; simpl; intros.
red; intros.
apply ecc_incl; trivial.
Qed.

Lemma cumul_Prop : forall e, sub_typ e prop (type 0).
red; simpl; intros.
red; intros.
apply G_trans with props; trivial.
 apply (ecc_grot 0).

 apply (ecc_in1 0).
Qed.

Lemma typ_prod2 : forall e n T U,
  typ e T (type n) ->
  typ (T :: e) U (type n) ->
  typ e (Prod T U) (type n).
Proof.
unfold typ, Prod; simpl; red; intros e n T U ty_T ty_U i is_val.
apply G_cc_prod.
 apply ecc_grot.

 red; red; intros.
 rewrite H0; auto with *.

 apply ty_T; trivial.

 intros.
 apply ty_U.
 apply vcons_add_var; auto.
Qed.

End WithFinitistUniverse.


(** Universes: version where type 0 contains an infinite set,
    hence nat can be in type 0.
 *)

Module WithoutFinitistUniverse.

Definition type (n:nat) := cst (ecc (S n)).

Lemma typ_Prop : forall e, typ e prop (type 0).
red; intros; simpl.
apply G_trans with (grot_succ (ZFcoc.props)); auto.
 apply (ecc_grot 1).

 apply (ecc_in1 0).

 apply (ecc_in2 0).
Qed.

Lemma typ_Type : forall e n, typ e (type n) (type (S n)).
red; intros; simpl.
apply (ecc_in2 (S n)).
Qed.

Lemma cumul_Type : forall e n, sub_typ e (type n) (type (S n)).
red; simpl; intros.
red; intros.
apply ecc_incl with (n:=S n); trivial.
Qed.

Lemma cumul_Prop : forall e, sub_typ e prop (type 0).
red; simpl; intros.
red; intros.
apply G_trans with ZFcoc.props; trivial.
 apply (ecc_grot 1).
apply G_trans with (grot_succ ZFcoc.props); trivial.
 apply (ecc_grot 1).

 apply (ecc_in1 0).

 apply (ecc_in2 0).
Qed.

Lemma typ_prod2 : forall e n T U,
  typ e T (type n) ->
  typ (T :: e) U (type n) ->
  typ e (Prod T U) (type n).
Proof.
red; intros e n T U ty_T ty_U i is_val.
apply G_cc_prod.
 apply ecc_grot.

 red; red; intros.
 rewrite H0; auto with *.

 apply ty_T; trivial.

 intros.
 red in ty_U.
 change (int (type n) i) with (int (type n) (V.cons x i)).
 apply in_int_not_kind.
 2:discriminate.
 apply ty_U.
 apply vcons_add_var; auto.
Qed.

End WithoutFinitistUniverse.

(** By default we take the second version (without universe of HF) *)
Export WithoutFinitistUniverse.
