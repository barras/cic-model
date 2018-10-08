Require Export basic.
Require Import Sat.
Require Import ZF ZFcoc ZFuniv_real ZFecc ZFlambda.
Require Export SN_CC_Real.
Import CC_Real.

(** Strong normalization proof of the Extended Calculus of Constructions.
    It is an extension of SN_CC_Real, so it does support strong eliminations.
    Inhabitation of all types is obtained by adding the empty set in every
    type (cf ZFuniv). The product is interpreted by the set of *partial*
    functions.
 *)

Set Implicit Arguments.

(** * Predicative universes: inference rules *)

Definition type (n:nat) : term := SN_CC_Real.cst (sn_sort (ecc (S n))).

Lemma cumul_Type e n : sub_typ e (type n) (type (S n)).
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

Lemma cumul_Prop e : sub_typ e prop (type 0).
unfold type.
red; intros.
destruct H0.
unfold int, cst, iint.
simpl int in H0,H1.
unfold props in H0,H1.
rewrite Real_sort_sn in H1; trivial.
apply and_split; intros.
 revert H0; apply sort_incl.
 transitivity (ecc 0); red; [apply ecc_incl_prop|apply ecc_incl].

 rewrite Real_sort_sn; trivial.
Qed.

Lemma cumul_Prod e A B B' :
  A <> kind ->
  sub_typ (A::e) B B' ->
  sub_typ e (Prod A B) (Prod A B').
intros Ank.
unfold sub_typ; intros.
destruct H1.
unfold int, Prod, iint.
simpl int in H1,H2.
unfold inX, props in H1,H2.
assert (m1 : forall a b, ext_fun a (fun x0 => int b (V.cons x0 i))).
 do 2 red; intros.
 rewrite H4; reflexivity.
rewrite Real_prod in H2; trivial.
apply and_split; intros.
 unfold inX; rewrite El_prod; trivial.
 rewrite El_prod in H1; trivial.
 revert H1; apply cc_prod_covariant; auto with *.
  do 2 red; intros; apply El_morph.
  rewrite H3; reflexivity.

  intros a tya b tyb.
  apply H with (i:=V.cons a i) (j:=I.cons SatSet.daimon j) (x:=b)(t:=SatSet.daimon).
   apply vcons_add_var_daimon; trivial.

   split; trivial.
   apply varSAT.

 rewrite Real_prod; trivial.
 revert t H2; apply piSAT0_mono with (f:=fun x => x); auto with *.
 intros a tya u ru.
 apply H with (i:=V.cons a i) (j:=I.cons SatSet.daimon j) (x:=cc_app x a)(t:=u).
  apply vcons_add_var_daimon; trivial.

  split; trivial.
  red.
  eapply prod_elim with (2:=H1) (3:=tya).
  apply m1.
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
 rewrite Real_sort_sn; trivial.
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
 rewrite Real_sort_sn; trivial.
 apply snSAT_intro.
 apply Lambda.sn_K.
Qed.

Lemma typ_prop_cumul e T :
  typ e T prop ->
  typ e T (type 0).
intros.
apply typ_subsumption with (1:=H); try discriminate.
apply cumul_Prop.
Qed.

Lemma typ_type_cumul e T n :
  typ e T (type n) ->
  typ e T (type (S n)).
intros.
apply typ_subsumption with (1:=H); try discriminate.
apply cumul_Type.
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
  simpl int in *.
  rewrite Real_sort_sn in H3,satU|-*; auto.
  rewrite tm_subst_cons in satU.
  apply sat_sn in satU.
  apply Lambda.sn_subst in satU.
  apply KSAT_intro with (A:=snSAT); auto.
Qed.

