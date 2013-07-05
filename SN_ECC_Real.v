Require Export basic.
Require Import Sat.
Require Import ZF ZFcoc ZFuniv_real ZFecc ZFlambda.

Require SN_CC_Real.
Import SN_CC_Real.SN_CC_Model SN_CC_Real.SN.
Export SN_CC_Real.

(** Strong normalization proof of the Extended Calculus of Constructions.
    It is an extension of SN_CC_Real, so it does support strong eliminations.
    Inhabitation of all types is obtained by adding the empty set in every
    type (cf ZFuniv). The product is interpreted by the set of *partial*
    functions.
 *)

Set Implicit Arguments.

(** * Predicative universes: inference rules *)

Definition type (n:nat) : trm := SN_CC_Real.cst (sn_sort (ecc (S n))).

Lemma cumul_Type : forall e n, sub_typ e (type n) (type (S n)).
unfold type.
red; intros.
destruct H0.
unfold int, cst, iint in *.
rewrite Real_sort_sn in H1; trivial.
apply and_split; intros.
 revert H0; apply sort_incl.
 red; apply ecc_incl.

 rewrite Real_sort_sn; trivial.
Qed.

Lemma cumul_Prop : forall e, sub_typ e prop (type 0).
unfold type.
red; intros.
destruct H0.
unfold int, cst, iint.
simpl int in H0,H1.
unfold props,sn_props in H0,H1.
rewrite Real_sort_sn in H1; trivial.
apply and_split; intros.
 revert H0; apply sort_incl.
 transitivity (ecc 0); red; [apply ecc_incl_prop|apply ecc_incl].

 rewrite Real_sort_sn; trivial.
Qed.


Lemma typ_prop_type0 e :
  typ e prop (type 0).
red; intros.
apply in_int_intro; intros; try discriminate.
apply and_split; intros.
 apply sn_sort_in_type; trivial.
 apply ecc_incl.
 apply ecc_in1.

 simpl.
 unfold SN_CC_addon.Real; rewrite Real_sort_sn; trivial.
 apply snSAT_intro.
 apply Lambda.sn_K.
Qed.

Lemma typ_type_type e n :
  typ e (type n) (type (S n)).
red; intros.
apply in_int_intro; intros; try discriminate.
apply and_split; intros.
 apply sn_sort_in_type; trivial.
 apply ecc_in2.

 simpl int; simpl tm.
 unfold SN_CC_addon.Real; rewrite Real_sort_sn; trivial.
 apply snSAT_intro.
 apply Lambda.sn_K.
Qed.

Lemma typ_prop_cumul e T :
  typ e T prop ->
  typ e T (type 0).
red; intros.
apply H in H0.
destruct H0.
destruct H1.
apply in_int_intro; intros; trivial; try discriminate.
apply and_split; intros.
 revert H1; apply sort_incl.
 transitivity (ecc 0); red; intros; [apply ecc_incl_prop|apply ecc_incl]; trivial.

 revert H2; simpl int.
 unfold SN_CC_addon.Real, props, sn_props.
 rewrite Real_sort_sn; trivial.
 rewrite Real_sort_sn; trivial.
Qed.

Lemma typ_type_cumul e T n :
  typ e T (type n) ->
  typ e T (type (S n)).
red; intros.
apply H in H0.
destruct H0.
destruct H1.
apply in_int_intro; intros; trivial; try discriminate.
apply and_split; intros.
 revert H1; apply sort_incl.
 red; intros; apply ecc_incl; trivial.

 revert H2; simpl int.
 unfold SN_CC_addon.Real, props, sn_props.
 rewrite Real_sort_sn; trivial.
 rewrite Real_sort_sn; trivial.
Qed.

Lemma typ_type_cumul_le e T m n :
  le m n ->
  typ e T (type m) ->
  typ e T (type n).
induction 1; intros; auto.
apply typ_type_cumul; auto.
Qed.

Lemma typ_predicative_prod e T U n :
  typ e T (type n) ->
  typ (T::e) U (type n) ->
  typ e (Prod T U) (type n).
unfold typ; intros.
specialize H with (1:=H1).
destruct H as (?,(?,?)); trivial.
apply in_int_intro; intros; try discriminate.
apply and_split; intros.
 apply predicative_prod; trivial.
  red; red; intros.
  rewrite H5; reflexivity.

  intros.
  specialize vcons_add_var_daimon with (1:=H1) (2:=H4) (3:=H);
    intros in_U.
  apply H0 in in_U.
  apply in_int_not_kind in in_U;[|discriminate].
  destruct in_U; trivial.

  specialize vcons_add_var_daimon with (1:=H1) (2:=empty_El _) (3:=H);
    intros in_U.
  apply H0 in in_U.
  destruct in_U  as (_,(in_U,satU)).
  unfold SN_CC_addon.Real in *; simpl int in *.
  rewrite Real_sort_sn in H3,satU|-*; auto.
  rewrite tm_subst_cons in satU.
  apply sat_sn in satU.
  apply Lambda.sn_subst in satU.
  apply KSAT_intro with (A:=snSAT); auto.
Qed.

