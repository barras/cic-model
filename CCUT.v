Require Import Models.
Require Import GenModelSN.
Require Import ZF.
Require Import ZFind_nat.

Require Import SN_CC.

Import CCSN SN_CC_Model SN_CC_addon SN.

Parameter Symb : Type.
Parameter isCstr : Symb -> Prop.


Inductive foterm :=
| V (_:nat)
| APP (h:Symb) (args:list foterm).

Parameter eqT : foterm -> foterm -> Prop.

Import Sat.

Lemma inSAT_Real : forall x t S,
  inSAT t S ->
  inSAT t (Real (mkTY x S)).
intros.
destruct S; simpl in *.
split.
 apply (Can.incl_sn x0); trivial.

 destruct x1; simpl.
 destruct x1; simpl in *.
 apply i0.
  apply (Can.incl_sn x0); trivial.

  unfold mkTY.
  rewrite ZFpairs.snd_def.
  apply subset_intro.
   apply ZFlambda.iLAM_typ.

   exists t; auto with *.
Qed.

Lemma inSAT_Real_rev : forall x t S,
  inSAT t (Real (mkTY x S)) ->
  inSAT t S.
intros.
destruct S; simpl in *.
destruct H.
pose (S' := exist _ x0 i : SAT).
apply (fun h => H0 (exist _ S' h)).
intros.
unfold mkTY in H2; rewrite ZFpairs.snd_def in H2.
apply subset_elim2 in H2.
destruct H2.
destruct H3.
rewrite H4 in H2.
apply ZFlambda.iLAM_inj in H2.
subst x2.
trivial.
Qed.

Definition natSAT :=
  interSAT (fun S:SAT =>
     prodSAT S (prodSAT (prodSAT S S) S)).


Definition T : trm.
left.
exists (fun _ => mkTY (singl empty) natSAT) (fun _ => Lc.K).
 do 2 red; reflexivity.
 do 2 red; reflexivity.
 red; reflexivity.
 red; reflexivity.
Defined.

Definition ZE := Lc.Abs (Lc.Abs (Lc.Ref 1)).

Lemma ZE_inSAT : inSAT ZE natSAT.
unfold natSAT, ZE.
apply interSAT_intro; [exact snSAT|].
intros.
apply prodSAT_intro; intros.
apply prodSAT_intro; intros.
simpl.
unfold Lambda.subst; rewrite Lambda.simpl_subst; auto.
rewrite Lambda.lift0; trivial.
Qed.

Definition SU := Lc.Abs (Lc.Abs (Lc.Abs
    (Lc.App (Lc.Ref 0) (Lc.App2 (Lc.Ref 2) (Lc.Ref 1) (Lc.Ref 0))))).

Lemma SU_inSAT : inSAT SU (prodSAT natSAT natSAT).
unfold SU, natSAT.
apply prodSAT_intro; intros.
unfold Lambda.subst; simpl Lambda.subst_rec.
apply interSAT_intro; [exact snSAT|].
intros.
apply prodSAT_intro; intros.
unfold Lambda.subst; simpl Lambda.subst_rec.
rewrite Lambda.simpl_subst; auto.
apply prodSAT_intro; intros.
unfold Lambda.subst; simpl Lambda.subst_rec.
rewrite Lambda.simpl_subst; auto.
rewrite Lambda.simpl_subst; auto.
do 3 rewrite Lambda.lift0.
apply prodSAT_elim with (1:=H1).
apply prodSAT_elim with (prodSAT x x); trivial.
apply prodSAT_elim with (2:=H0).
apply interSAT_elim with (1:=H).
Qed.


Definition Zero : trm.
left; exists (fun _ => empty) (fun _ => ZE).
 do 2 red; reflexivity.
 do 2 red; reflexivity.
 red; reflexivity.
 red; reflexivity.
Defined.


Definition Succ : trm.
left; exists (fun _ => lam (mkTY (singl empty) natSAT) (fun x => x)) (fun _ => SU).
 do 2 red; reflexivity.
 do 2 red; reflexivity.
 red; reflexivity.
 red; reflexivity.
Defined.

Definition NatRec (f g n:trm) : trm.
left; exists (fun i => int i f)
             (fun j => Lc.App2 (tm j n) (tm j f) (Lc.App (tm j g) ZE)).
 do 2 red; intros.
 rewrite H; reflexivity.

 do 2 red; intros.
 rewrite H; auto.

 red; intros; simpl.
 repeat rewrite tm_liftable; trivial.

 red; intros; simpl.
 repeat rewrite tm_substitutive; trivial.
Defined.


Lemma typ_0 : forall e, typ e Zero T.
split. 
 discriminate.

 split.
  simpl.
  unfold inX, El, mkTY. 
  rewrite ZFpairs.fst_def.
  apply singl_intro.

  simpl int.
  apply inSAT_Real.
  apply ZE_inSAT.
Qed.

Lemma typ_S : forall e, typ e Succ (Prod T (lift 1 T)).
split.
 discriminate.

 split.
  simpl.
  apply prod_intro.
   red; intros; auto with *.

   red; intros; reflexivity.

   intros; auto.

  simpl int.
  unfold prod, sn_prod.
  apply inSAT_Real.
  unfold piSAT.
  simpl tm.
  unfold SU.
  apply prodSAT_intro; intros.
  unfold Lambda.subst; simpl Lambda.subst_rec.
  apply interSAT_intro; intros.
   exists empty.
   unfold El, mkTY; rewrite ZFpairs.fst_def.
   apply singl_intro.
  apply inSAT_Real.
unfold natSAT.
apply interSAT_intro; intros.
 exact snSAT.
apply prodSAT_intro; intros.
unfold Lambda.subst; simpl Lambda.subst_rec.
rewrite Lambda.simpl_subst; auto.
apply prodSAT_intro; intros.
unfold Lambda.subst; simpl Lambda.subst_rec.
rewrite Lambda.simpl_subst; auto.
rewrite Lambda.simpl_subst; auto.
do 3 rewrite Lambda.lift0.
apply prodSAT_elim with (1:=H2).
apply prodSAT_elim with (prodSAT x0 x0); trivial.
apply prodSAT_elim with (2:=H1).
apply inSAT_Real_rev in H0.
apply interSAT_elim with (1:=H0).
Qed.

Lemma prodSAT_mono : Proper (inclSAT --> inclSAT ==> inclSAT) prodSAT.
do 4 red; intros.
simpl.
red; intros.
simpl in H1.
red in H1.
apply H0.
apply H1.
apply H; trivial.
Qed.

Lemma typ_Nrect : forall e n f g P,
  typ e n T ->
  typ e P (Prod T prop) -> 
  typ e f (App P Zero) ->
  typ e g (Prod T (Prod (App (lift 1 P) (Ref 0))
              (App (lift 2 P) (App Succ (Ref 1))))) ->
  typ e (NatRec f g n) (App P n).
red; red; intros.
split.
 discriminate.
split.
 simpl.
 assert (int i n == empty).
  apply H in H3.
  destruct H3 as (_,(H3,_)).
  simpl in H3.
  unfold inX, El, mkTY in H3; rewrite ZFpairs.fst_def in H3.
  apply singl_elim in H3; trivial.
 apply H1 in H3.
 destruct H3.
 destruct H5.
 simpl in H5.
 revert H5; apply in_ext; auto with *.
 rewrite H4.
 reflexivity.

 simpl tm.
 specialize (H _ _ H3).
 destruct H as (_,(n_ty,H)). 
 simpl in n_ty.
 unfold inX, El, mkTY in n_ty; rewrite ZFpairs.fst_def in n_ty.
 apply singl_elim in n_ty.
 simpl int in H.
 apply inSAT_Real_rev in H.
 specialize (H1 _ _ H3).
 destruct H1 as (_,(f_ty,H1)). 
 simpl in f_ty.
 specialize (H2 _ _ H3).
 destruct H2 as (_,(_,H2)). 
 simpl int in H2.
 unfold prod, sn_prod in H2.
 apply inSAT_Real_rev in H2.
 unfold piSAT at 1 in H2.
 destruct H.
 specialize (H4 (Real (app (int i P) (int i n)))).
 simpl int.
 apply prodSAT_elim with
   (prodSAT (Real (app (int i P) (int i n))) (Real (app (int i P) (int i n)))).
 apply prodSAT_elim with (Real (app (int i P) (int i n))).
  trivial.

  revert H1; apply inSAT_morph; auto.
  apply Real_morph.
  rewrite n_ty; reflexivity.

 apply prodSAT_elim with natSAT.
 2:apply ZE_inSAT.
 revert H2; apply prodSAT_mono.
  red; red; intros.
  apply inSAT_Real; trivial.

  red; intros.
  generalize (fun h => interSAT_elim H2 (exist _ (int i n) h)); clear H2; intro H2.
  simpl proj1_sig in H2.
  lapply H2.
   clear H2; intros H2.
   apply inSAT_Real_rev in H2.
   unfold piSAT in H2.
   revert H2; apply prodSAT_mono.
    red; red; intros u.
    apply inSAT_morph; trivial.
    apply Real_morph.
    rewrite int_cons_lift_eq; auto with *.

    red; intros.
    generalize (fun h => interSAT_elim H2 (exist _ (int i f) h)); clear H2; intro H2.
    simpl proj1_sig in H2.
    lapply H2.
     apply inSAT_morph; auto.
     apply Real_morph.
     rewrite split_lift.
     do 2 rewrite int_cons_lift_eq.
     rewrite beta_eq; auto with *.
      red; intros; auto.

      unfold inX, El, mkTY; rewrite ZFpairs.fst_def.
      rewrite n_ty; apply singl_intro.

    rewrite int_cons_lift_eq.
    rewrite n_ty.
    trivial.

  unfold inX, El, mkTY; rewrite ZFpairs.fst_def.
  rewrite n_ty; apply singl_intro.
Qed.

Lemma all_conv_allowed : forall e M M',
  typ e M T ->
  typ e M' T ->
  eq_typ e M M'.
red; intros.
specialize (H _ _ H1).
destruct H as (_,(H,_)).
simpl in H.
specialize (H0 _ _ H1).
destruct H0 as (_,(H0,_)).
simpl in H0.
unfold inX, El, mkTY in H,H0; rewrite ZFpairs.fst_def in H,H0.
apply singl_elim in H; apply singl_elim in H0.
rewrite H; rewrite H0; reflexivity.
Qed.
