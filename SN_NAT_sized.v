(** Strong normalization of the model of CC+NAT in the type-based
    termination presentation.

    This is a copy of SN_W, but in a simpler case.
*)
Require Import basic Models.
Require SN_ECC_Real.
Import ZFgrothendieck.
Import ZF ZFsum ZFnats ZFrelations ZFord ZFfix.
Require Import ZFfunext ZFfixrec ZFcoc ZFecc ZFuniv_real ZFind_natbot SATtypes SATnat_real.

Import SN_CC_Real.SN_CC_Model SN_CC_Real.SN SN_ECC_Real.
Opaque Real.
Import Sat Sat.SatSet.


(** Ordinals *)

Require Import SN_ord.

(** Judgments with variance *)

Require Import SN_variance.

(** NAT *)

Section NAT_typing.

Variable e:env.

Definition NatI (O:trm) : trm.
(*begin show*)
left; exists (fun i => mkTY (TI NATf' (int O i)) cNAT)
             (fun j => tm O j).
(*end show*)
 do 2 red; intros.
 apply mkTY_ext; intros.
  apply TI_morph_gen; auto with *.
  
   do 2 red; intros; apply NATf_morph.
   apply cc_bot_morph; trivial.

   apply int_morph; auto with *.

  apply cNAT_morph; trivial.
 (**)
 do 2 red; intros.
 rewrite H; reflexivity.
 (**)
 red; intros.
 rewrite <- tm_liftable.
 reflexivity.
 (**)
 red; intros.
 rewrite <- tm_substitutive.
 reflexivity.
Defined.

Lemma El_int_NatI O i :
  El (int (NatI O) i) == cc_bot (TI NATf' (int O i)).
simpl.
rewrite El_def; reflexivity.
Qed.
Lemma Real_int_NatI O i x :
  x ∈ cc_bot (TI NATf' (int O i)) ->
  eqSAT (Real (int (NatI O) i) x) (cNAT x).
simpl; intros.
rewrite Real_def; auto with *.
intros.
rewrite H1; reflexivity.
Qed.

Lemma typ_NatI O :
  typ_ord e O ->
  typ e (NatI O) kind.
intros tyO i j valok; simpl.
red in tyO; specialize tyO with (1:=valok).
split;[|split].
 discriminate.

 exists nil; exists (NatI O);[reflexivity|].
 exists empty; simpl; auto.
 red; auto.

 simpl.
 apply tyO.
Qed.

Lemma typ_NatI_type n O :
  typ_ord e O ->
  typ e (NatI O) (type n).
intros tyO i j is_val; simpl.
red in tyO; specialize tyO with (1:=is_val).
destruct tyO as (o_o,osn).
apply in_int_intro;[discriminate|discriminate|].
apply and_split; intros.
 red; change (int (type n) i) with (sn_sort (ecc (S n))).
 simpl int.
 apply sn_sort_intro.
  intros.
  apply cNAT_morph; auto with *.

  apply G_incl with NAT'; trivial.
   apply G_TI; auto with *.
    intros.
    apply G_NATf'; auto.

    apply NATf'_stages; auto.

 red in H.
 change (int (type n) i) with (sn_sort (ecc (S n))).
 rewrite Real_sort_sn; trivial.
Qed.

(** Constructors *)

Definition Zero : trm.
(* begin show *)
left; exists (fun i => ZERO)
             (fun j => ZE).
(* end show *)
 do 2 red; intros; reflexivity.
 (**)
 do 2 red; intros; reflexivity.
 (**)
 red; intros.
 reflexivity.
 (**)
 red; intros.
 reflexivity.
Defined.


Lemma typ_0 O :
  typ_ord e O ->
  typ e Zero (NatI (OSucc O)).
red; intros.
apply in_int_intro; try discriminate.
red in H; specialize H with (1:=H0); destruct H as (oo,osn).
assert (ZERO ∈ TI NATf' (osucc (int O i))).
 apply TI_intro with (int O i); auto with *.
 apply ZERO_typ_gen. 
split.
 red; rewrite El_int_NatI; auto.

 rewrite Real_int_NatI; auto.
 simpl.
 rewrite cNAT_eq.
  apply Real_ZERO_gen.
  revert H; apply NATf'_stages; auto.
Qed.

Definition Succ (O:trm) : trm.
(* begin show *)
left; exists (fun i => lam (mkTY (TI NATf' (int O i)) cNAT) SUCC)
             (fun j => Lc.App2 Lc.K (Lc.Abs (SU (Lc.Ref 0))) (tm O j)).
(* end show *)
 do 2 red; intros; apply cc_lam_morph; auto with *.
  rewrite !El_def.
  rewrite H; reflexivity.

  apply inr_morph.
 (**)
 do 2 red; intros.
 rewrite H; reflexivity.
 (**)
 red; intros.
 simpl.
 rewrite <- tm_liftable.
 reflexivity.
 (**)
 red; intros.
 simpl.
 rewrite <- tm_substitutive.
 reflexivity.
Defined.


Lemma typ_S O :
  typ_ord e O ->
  typ e (Succ O) (Prod (NatI O) (lift 1 (NatI (OSucc O)))).
red; intros tyO i j valok.
red in tyO; specialize tyO with (1:=valok); destruct tyO as (oo,snO).
apply in_int_intro; try discriminate.
assert (lam (mkTY (TI NATf' (int O i)) cNAT) SUCC ∈
        cc_arr (cc_bot (TI NATf' (int O i))) (cc_bot (TI NATf' (osucc (int O i))))).
 eapply in_reg.
 2:apply cc_arr_intro.
  apply cc_lam_ext.
   rewrite El_def; reflexivity.

   do 2 red; intros; apply inr_morph.
   exact H0.

  do 2 red; intros; apply inr_morph; trivial.

  intros.
  apply cc_bot_intro.
  apply TI_intro with (int O i); auto with *.
  apply SUCC_typ_gen; trivial.
apply and_split.
 red; simpl.
 rewrite El_prod.
 revert H; apply in_set_morph; auto with *.
 apply cc_prod_ext.
  rewrite El_def; reflexivity.

  red; intros.
  rewrite El_def.
  rewrite V.lams0.
  reflexivity.
 do 2 red; intros.
 apply mkTY_ext; intros.
  rewrite !V.lams0; reflexivity.
  apply cNAT_morph; trivial.

 intros tyS.
 simpl.
 rewrite Real_prod; trivial.
 2:do 2 red; intros; apply mkTY_ext; [
  rewrite !V.lams0; reflexivity |
  intros; apply cNAT_morph; trivial].
 apply piSAT0_intro'.
 2:exists empty; auto.
 intros.
 rewrite El_def in H0.
 eapply inSAT_context.
  intros.
  apply KSAT_intro; trivial.
  exact H2.
 rewrite Real_def in H1; trivial.
 2:intros; apply cNAT_morph; trivial.
 assert (cc_app (lam (mkTY (TI NATf' (int O i)) cNAT) SUCC) x == SUCC x).
  apply beta_eq.
   do 2 red; intros; apply inr_morph; trivial.
   red; rewrite El_def; trivial.
 rewrite H2.
 rewrite Real_def.
 2:intros; apply cNAT_morph; trivial.

 apply inSAT_exp.
  apply sat_sn in H1; auto.
 unfold Lc.subst; simpl.
 apply Real_SUCC_cNAT; trivial.
 revert H0; apply cc_bot_mono.
 apply NATf'_stages; auto.

 apply cc_bot_intro.
 rewrite V.lams0.
 apply TI_intro with (int O i); auto with *.
 apply SUCC_typ_gen; trivial.
Qed.

(* Case analysis *)

Definition NatCase (b0 bS n : trm) : trm.
(*begin show*)
left; exists (fun i => NATCASE (int b0 i) (fun x => int bS (V.cons x i)) (int n i))
             (fun j => NCASE (tm b0 j) (Lc.Abs (tm bS (Lc.ilift j))) (tm n j)).
(*end show*)
do 2 red; intros.
unfold NATCASE.
apply union2_morph; apply cond_set_morph.
 rewrite H; reflexivity.
 rewrite H; reflexivity.
 setoid_rewrite H; reflexivity.
 rewrite H; reflexivity.
(**)
do 2 red; intros.
rewrite H; reflexivity.
(**)
unfold NCASE; red; intros; simpl.
apply f_equal3 with (f:=Lc.App2).
 rewrite <- (tm_liftable j n); reflexivity.

 rewrite (tm_liftable _ b0).
 rewrite Lc.permute_lift.
 reflexivity.

 rewrite <- (tm_liftable _ bS).
 rewrite !Lc.ilift_binder_lift.
 reflexivity.
(**)
unfold NCASE; red; intros; simpl.
apply f_equal3 with (f:=Lc.App2).
 rewrite <- (tm_substitutive _ n); reflexivity.

 rewrite (tm_substitutive _ b0).
 rewrite Lc.commut_lift_subst.
 reflexivity.

 rewrite <- (tm_substitutive _ bS).
 rewrite Lc.ilift_binder.
 reflexivity.
Defined.

Instance NatCase_morph :
  Proper (eq_trm ==> eq_trm ==> eq_trm ==> eq_trm) NatCase.
do 4 red; intros.
split; red; simpl; intros.
 unfold NATCASE.
 apply union2_morph; apply cond_set_morph.
  rewrite H1, H2; reflexivity.
  rewrite H, H2; reflexivity.
  setoid_rewrite H1; setoid_rewrite H2; reflexivity.
  rewrite H0, H1, H2; reflexivity.

 rewrite H.
 rewrite H0.
 rewrite H1.
 rewrite H2.
 reflexivity.
Qed.

Lemma NatCase_iota_0 B0 BS :
  eq_typ e (NatCase B0 BS Zero) B0.
red; intros.
simpl.
rewrite NATCASE_ZERO; reflexivity.
Qed.

Lemma NatCase_iota_S B0 BS O N :
  typ e N (NatI O) ->
  eq_typ e (NatCase B0 BS (App (Succ O) N)) (subst N BS).
red; intros.
simpl.
red.
assert (BSm : morph1 (fun x => int BS (V.cons x i))).
 do 2 red; intros.
 rewrite H1; reflexivity.
eapply transitivity.
 apply NATCASE_morph.
  reflexivity.

  intros ? ? h.
  apply int_morph;[reflexivity|].
  apply V.cons_morph;[exact h|reflexivity].

  apply beta_eq.
   do 2 red; intros; apply inr_morph; trivial.
  apply H in H0.
  apply in_int_not_kind in H0.
  2:discriminate.
  destruct H0; trivial.
rewrite NATCASE_SUCC.
 apply int_subst_eq.

 intros.
 rewrite H1; reflexivity.
Qed.

Lemma typ_NatCase P O B0 BS n :
  typ_ord e O ->
  typ e B0 (App P Zero) ->
  typ (NatI O::e) BS (App (lift 1 P) (App (lift 1 (Succ O)) (Ref 0))) ->
  typ e n (NatI (OSucc O)) ->
  typ e (NatCase B0 BS n) (App P n).
red; intros tyO tyB0 tyBS tyn i j valok.
red in tyO; specialize tyO with (1:=valok); destruct tyO as (oo,osn).
red in tyB0; specialize tyB0 with (1:=valok).
apply in_int_not_kind in tyB0;[|discriminate].
destruct tyB0 as (tyB0,satB0); red in tyB0.
red in tyn; specialize tyn with (1:=valok).
apply in_int_not_kind in tyn;[|discriminate].
destruct tyn as (tyN,satN); red in tyN.
assert (BSm : morph1 (fun x => int BS (V.cons x i))).
 do 2 red; intros.
 rewrite H; reflexivity.
assert (ok' : forall x u, x ∈ cc_bot (TI NATf' (int O i)) -> inSAT u (cNAT x) ->
  val_ok (NatI O::e) (V.cons x i) (I.cons u j)).
 intros.
 apply vcons_add_var; auto.
 2:discriminate.
 split.
  red; rewrite El_int_NatI; trivial.
  rewrite Real_int_NatI; trivial.
apply in_int_intro; try discriminate.
rewrite El_int_NatI in tyN.
rewrite Real_int_NatI in satN; trivial.
apply and_split; intros.
 red; simpl.
 rewrite cc_bot_ax in tyN; destruct tyN.
  (* empty set *)
  apply in_reg with empty; auto.
  unfold NATCASE.
  rewrite H.
  rewrite !cond_set_mt.
   symmetry; apply empty_ext.
   red; intros.
   apply union2_elim in H0; destruct H0; apply empty_ax in H0; trivial.

   intros (k,h).
   rewrite H in h.
   apply discr_mt_pair in h; trivial.

   apply discr_mt_pair.   

  (* constructor case *)
  simpl in H; rewrite TI_mono_succ in H; auto with *.
  unfold NATCASE.
  apply sum_ind with (3:=H); intros.
   apply ZFind_basic.unit_elim in H0.
   rewrite H0 in H1.
   rewrite cond_set_ok; trivial.
   rewrite cond_set_mt.
    apply in_reg with (int B0 i).
     apply eq_set_ax; intros z.
     rewrite union2_ax.
     split; auto.
     destruct 1; trivial.
     apply empty_ax in H2; contradiction.

     rewrite H1.
     trivial.     

    intros (k,h); rewrite H1 in h.
    apply NATf_discr in h; trivial.

   rewrite cond_set_mt.
   2:intros h; rewrite H1 in h; symmetry in h; apply NATf_discr in h; trivial.
   rewrite cond_set_ok; eauto.
   apply in_reg with (int BS (V.cons y i)).
    apply eq_set_ax; intros z.
    rewrite union2_ax.
    rewrite H1.
    rewrite dest_sum_inr.
    split; auto.
    destruct 1; trivial.
    apply empty_ax in H2; contradiction.

    rewrite H1.
    specialize ok' with (1:=H0) (2:=varSAT _).
    red in tyBS; specialize tyBS with (1:=ok').
    apply in_int_not_kind in tyBS;[|discriminate].
    destruct tyBS as (tyBS,_).    
    revert tyBS; apply eq_elim.
    apply El_morph.
    apply cc_app_morph.
     rewrite int_lift_eq; reflexivity.
    simpl.
    apply beta_eq.
     do 2 red; intros; apply inr_morph; trivial.

     red; rewrite El_def; trivial.
     rewrite V.lams0.
     trivial.

 (* Reducibility *)
 simpl in H|-*.
 rewrite cc_bot_ax in tyN; destruct tyN.
  (* neutral case *)
  rewrite H0 in satN.
  eapply prodSAT_elim.
   eapply prodSAT_elim.
    eapply fNATi_neutral with (o:=omega); trivial.

    apply prodSAT_intro with (A:=snSAT).
    intros.
    unfold Lc.subst; rewrite Lc.simpl_subst, Lc.lift0; auto with arith.
    apply satB0.

   apply prodSAT_intro.
   intros.
   unfold Lc.subst; simpl.
   fold (Lc.subst v (tm BS (Lc.ilift j))).
   rewrite <- tm_subst_cons.
   assert (ty_mt : empty ∈ cc_bot (TI NATf' (int O i))) by auto.
   specialize ok' with (1:=ty_mt) (2:=H1).
   red in tyBS; specialize tyBS with (1:=ok').
   apply in_int_not_kind in tyBS;[|discriminate].
   destruct tyBS as (_,satBS).
   exact satBS.

  (* regular case *)
  apply Real_NATCASE with (o:=int O i)(C:=fun k =>Real (app (int P i) k)
    (NATCASE (int B0 i) (fun x => int BS (V.cons x i)) k)); auto.
   do 2 red; intros.
   apply Real_morph.
    rewrite H1; reflexivity.

    apply NATCASE_morph; auto with *.

   rewrite fNATi_stages; auto with *.

   rewrite NATCASE_ZERO.
   trivial.

   apply piSAT0_intro'.
   2:exists empty; auto.
   intros.
   apply inSAT_exp.
    apply sat_sn in H2; auto.
   rewrite <- tm_subst_cons.
   rewrite fNATi_stages in H2; auto.
   specialize ok' with (1:=H1) (2:=H2).
   red in tyBS; specialize tyBS with (1:=ok').
   apply in_int_not_kind in tyBS;[|discriminate].
   destruct tyBS as (tyBS,satBS).
   revert satBS; apply inSAT_morph; auto with *.
   apply Real_morph.
    simpl.
    rewrite int_lift_eq.
    apply cc_app_morph; [reflexivity|].
    unfold app,lam; rewrite beta_eq; auto with *.
     red; intros; apply inr_morph; trivial.

     red; rewrite El_def.     
     rewrite V.lams0.
     trivial.

    rewrite NATCASE_SUCC; auto with *.
Qed.
Print Assumptions typ_NatCase.

Lemma typ_NatCase' P O B0 BS n T :
  T <> kind ->
  typ_ord e O ->
  sub_typ e (App P n) T ->
  typ e B0 (App P Zero) ->
  typ (NatI O::e) BS (App (lift 1 P) (App (lift 1 (Succ O)) (Ref 0))) ->
  typ e n (NatI (OSucc O)) ->
  typ e (NatCase B0 BS n) T.
intros.
apply typ_subsumption with (App P n); auto.
2:discriminate.
apply typ_NatCase with O; trivial.
Qed.

End NAT_typing.

(*****************************************************************************)
(** Recursor (without case analysis) *)

(* NatFix O M is a fixpoint of domain NatI O with body M *)
Definition NatFix (O M:trm) : trm.
(*begin show*)
left.
exists (fun i =>
         NATREC' (fun o' f => int M (V.cons f (V.cons o' i))) (int O i))
       (fun j => NATFIX (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j))))).
(*end show*)
 do 2 red; intros.
 unfold NATREC', NATREC.
 unfold REC.
 apply TR_morph.
 2:rewrite H; reflexivity.
 do 2 red; intros.
 apply sup_morph; trivial.
 red; intros.
 apply squash_morph.
 apply int_morph; auto with *.
 apply V.cons_morph.
  apply H0; trivial.
 apply V.cons_morph; trivial.

 (* *)
 do 2 red; intros.
 rewrite H; reflexivity.

 (* *)
 red; intros.
 replace (Lc.lift_rec 1
     (NATFIX (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j))))) k) with
   (NATFIX (Lc.lift_rec 1 (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j)))) k)).
  simpl.
  f_equal.
  f_equal.
  rewrite <- tm_liftable.
  apply tm_morph; auto with *.
  rewrite <- Lc.ilift_binder_lift.
  apply Lc.ilift_morph.
  intros [|k']; simpl; trivial.
  apply tm_liftable.

  generalize  (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j)))); intro.
  unfold NATFIX, FIXP; simpl.
  rewrite <- Lc.permute_lift.
  reflexivity.

 (* *)
 red; intros.
 replace (Lc.subst_rec u
     (NATFIX (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j))))) k) with
   (NATFIX (Lc.subst_rec u (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j)))) k)).
  simpl.
  f_equal.
  f_equal.
  rewrite <- tm_substitutive.
  apply tm_morph; auto with *.
  rewrite <- Lc.ilift_binder.
  apply Lc.ilift_morph.
  intros [|k']; simpl; trivial.
  apply tm_substitutive.

  generalize  (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j)))); intro.
  unfold NATFIX, FIXP; simpl.
  rewrite <- Lc.commut_lift_subst.
  reflexivity.
Defined.


(** Typing rules of NatFix *)

Section NatFixRules.

  Variable E : fenv.
  Let e := tenv E.
  Variable O U M : trm.

  Hypothesis ty_O : typ_ord e O.
  Hypothesis ty_M : typ (Prod (NatI (Ref 0)) U::OSucct O::e)
    M (Prod (NatI (OSucc (Ref 1)))
         (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U)))).

  Hypothesis stab : fx_extends
    (push_fun (push_ord E (OSucct O)) (NatI (Ref 0)) U)
    (NatI (OSucc (Ref 1)))
    M.

  Let Nati o := cc_bot (TI NATf' o).
  Let F i := fun o' f => squash (int M (V.cons f (V.cons o' i))).
  Let U' i := fun o' x => El (int U (V.cons x (V.cons o' i))).

  Local Instance U'morph : forall i, morph2 (U' i).
do 3 red; intros; unfold U'.
rewrite H; rewrite H0; reflexivity.
Qed.
  Instance morph_fix_body : forall i, morph2 (F i).
unfold F; do 3 red; intros.
apply squash_morph.
rewrite H; rewrite H0; reflexivity.
Qed.
  Lemma ext_fun_ty : forall o i,
    ext_fun (Nati o) (U' i o).
do 2 red; intros.
rewrite H0;reflexivity.
Qed.
  Hint Resolve U'morph morph_fix_body ext_fun_ty.


  Hypothesis fx_sub_U :
    fx_sub (push_var (push_ord E (OSucct O)) (NatI (OSucc (Ref 0)))) U.


  Lemma val_mono_1 i i' j j' y y' f g:
    val_mono E i j i' j' ->
    isOrd (int O i) ->
    isOrd (int O i') ->
    int O i ⊆ int O i' ->
    isOrd y ->
    isOrd y' ->
    y ⊆ int O i ->
    y' ⊆ int O i' ->
    y ⊆ y' ->
    f ∈ cc_prod (Nati y) (U' i y) ->
    g ∈ cc_prod (Nati y') (U' i' y') ->
    fcompat (Nati y) f g ->
    val_mono (push_fun (push_ord E (OSucct O)) (NatI (Ref 0)) U)
      (V.cons f (V.cons y i)) (I.cons daimon (I.cons daimon j))
      (V.cons g (V.cons y' i')) (I.cons daimon (I.cons daimon j')).
intros is_val Oo Oo' oo' yo y'o yO y'O yy' fty gty eqfg.
apply val_push_fun.
 apply val_push_ord; auto.
 3:discriminate.
  split;[|apply varSAT].
  red; rewrite El_int_osucc.
  apply ole_lts; trivial.

  split;[|apply varSAT].
  red; rewrite El_int_osucc.
  apply ole_lts; trivial.

 split;[|apply varSAT].
 red; rewrite El_int_prod.
 revert fty; apply eq_elim; apply cc_prod_ext; intros.
  simpl; rewrite El_def; auto with *.
  reflexivity.

  apply ext_fun_ty.

 split;[|apply varSAT].
 red; rewrite El_int_prod.
 revert gty; apply eq_elim; apply cc_prod_ext; intros.
  simpl; rewrite El_def; auto with *.
  reflexivity.

  apply ext_fun_ty.

 simpl; rewrite El_def; auto with *.
Qed.

  Lemma val_mono_2 i j y y' n n':
    val_ok e i j ->
    isOrd (int O i) ->
    isOrd y ->
    isOrd y' ->
    y ⊆ y' ->
    y' ⊆ int O i ->
    n ∈ Nati y ->
    n == n' ->
    val_mono (push_var (push_ord E (OSucct O)) (NatI (OSucc (Ref 0))))
      (V.cons n (V.cons y i)) (I.cons daimon (I.cons daimon j))
      (V.cons n' (V.cons y' i)) (I.cons daimon (I.cons daimon j)).
Proof.
intros.
apply val_push_var; auto with *.
 4:discriminate.
 apply val_push_ord; auto with *.
  4:discriminate.
  apply val_mono_refl; trivial.

  split;[|apply varSAT].
  red; rewrite El_int_osucc.
  apply ole_lts; auto.
  transitivity y'; trivial.

  split;[|apply varSAT].
  red; rewrite El_int_osucc.
  apply ole_lts; auto.

 split;[|apply varSAT].
 red; simpl; rewrite El_def.
 revert H5; apply cc_bot_mono.
 apply TI_incl; simpl; auto.

 split;[|apply varSAT].
 red; simpl; rewrite El_def.
 rewrite <- H6.
 revert H5; apply cc_bot_mono.
 apply TI_incl; simpl; auto.
 apply ole_lts; trivial.
Qed.


Let F2m : forall i T, morph2 (fun o' f => int T (V.cons f (V.cons o' i))).
do 3 red; intros.
apply int_morph; [reflexivity|].
repeat apply V.cons_morph; trivial.
reflexivity.
Qed.
Let U2m : forall i T, morph2 (fun o' f => El (int T (V.cons f (V.cons o' i)))).
do 3 red; intros.
apply El_morph; apply F2m; trivial.
Qed.
Set Implicit Arguments.

Let Unmt : forall i o x, empty ∈ U' i o x.
unfold U'; auto.
Qed.
Let Mty i j :
 isOrd (int O i) ->
 val_ok e i j ->
 forall o',
 isOrd o' ->
 o' ⊆ int O i ->
 forall f,
 f ∈ cc_prod (Nati o') (U' i o') ->
 int M (V.cons f (V.cons o' i)) ∈ cc_prod (Nati (osucc o')) (U' i (osucc o')).
intros ordo ok o' oo' leo f tyf.
assert (lto : o' ∈ osucc (int O i)).
 apply le_lt_trans with (int O i); auto.
 apply ole_lts; trivial.
assert (ok': val_ok (Prod (NatI (Ref 0)) U :: OSucct O :: e)
          (V.cons f (V.cons o' i)) (I.cons daimon (I.cons daimon j))).
 apply vcons_add_var_daimon; [| |discriminate].
  apply vcons_add_var_daimon; [trivial| |discriminate].
  red; simpl; rewrite El_def; auto.

  red; rewrite El_int_prod.
  revert tyf; apply eq_elim; apply cc_prod_ext.
   simpl; rewrite El_def; reflexivity.

   apply ext_fun_ty.
apply ty_M in ok'.
apply in_int_not_kind in ok'.
2:discriminate.
destruct ok' as (ok',_).
red in ok'; rewrite El_int_prod in ok'.
revert ok'; apply eq_elim; apply cc_prod_ext.
 simpl; rewrite El_def; reflexivity.

 red; intros.
 rewrite int_lift_rec_eq.
 rewrite int_subst_rec_eq.
 rewrite int_lift_rec_eq.
 apply El_morph; apply int_morph; auto with *.
 intros [|[|k]].
  compute; trivial.
  simpl; reflexivity.
  compute; fold minus.
  replace (k-0) with k; auto with *.
Qed.

Let Mirr : forall i j,
  val_ok e i j ->
  NAT_ord_irrel' (int O i)
     (fun o' f => int M (V.cons f (V.cons o' i))) 
     (U' i).
red; intros.
destruct ty_O with (1:=H) as (Oo,_).
assert (val_mono (push_fun (push_ord E (OSucct O)) (NatI (Ref 0)) U)
         (V.cons f (V.cons o i)) (I.cons daimon (I.cons daimon j))
         (V.cons g (V.cons o' i)) (I.cons daimon (I.cons daimon j))).
 apply val_mono_1; auto with *.
  apply val_mono_refl; trivial.

  transitivity o'; trivial.

apply stab in H7.
simpl in H7; rewrite El_def in H7; trivial.
Qed.

Let Usub : forall i j,
 val_ok e i j ->
 forall o' o'' x,
 isOrd o' ->
 o' ⊆ o'' ->
 o'' ∈ osucc (int O i) ->
 x ∈ Nati o' ->
 U' i o' x ⊆ U' i o'' x.
intros.
destruct ty_O with (1:=H) as (Oo,_).
assert (o'' ⊆ int O i).
 apply olts_le in H2; trivial.
eapply El_sub with (1:=fx_sub_U).
apply val_mono_2; auto with *.
 apply val_mono_refl; eexact H.

 eauto using isOrd_inv.
Qed.


Lemma typ_natfix :
  typ e (NatFix O M) (Prod (NatI O) (subst_rec O 1 U)).
red; intros.
destruct ty_O with (1:=H).
apply in_int_intro.
discriminate.
discriminate.
apply and_split; intros.
 red; rewrite El_int_prod.
 eapply eq_elim.
 2:simpl; apply NATREC'_typ with (ord:=int O i) (U:=U' i); eauto with *.
 apply cc_prod_ext.
  simpl; rewrite El_def; reflexivity.

  red; intros.
  rewrite int_subst_rec_eq.
  rewrite <- V.cons_lams.
  2:apply V.cons_morph; reflexivity.
  rewrite V.lams0.
  rewrite H3; reflexivity.

(**)
 set (m:=Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j)))).
 red in H2; rewrite El_int_prod in H2.
 rewrite Real_int_prod; trivial.
 cut (inSAT (NATFIX m)
       (piSAT0 (fun x => x ∈ Nati (int O i))
         (fNATi (int O i))
         (fun x =>
            Real (int U (V.cons x (V.cons (int O i) i))) 
              (cc_app (NATREC (F i) (int O i)) x)))).
  apply piSAT0_morph; intros; auto with *.
   red; simpl; intros; rewrite El_def; reflexivity.

   rewrite Real_int_NatI; auto with *.
   symmetry; apply fNATi_stages; auto.

   apply Real_morph; simpl;[|reflexivity].
   rewrite int_subst_rec_eq.
   apply int_morph; auto with *.
   intros [|[|k]]; reflexivity.

 apply NATFIX_sat with
   (X:=fun o n => Real (int U (V.cons n (V.cons o i)))
     (cc_app (NATREC (F i) o) n)); trivial.
  red; intros.
  apply cc_bot_intro in H7.
  apply fx_sub_U with (V.cons n (V.cons y i))
     (I.cons daimon (I.cons daimon j)) (I.cons daimon (I.cons daimon j)).
   apply val_mono_2; auto with *.

   assert (cc_app (NATREC (F i) y) n == cc_app (NATREC (F i) y') n).
    apply NATREC'_irr with (ord:=int O i) (U:=U' i); eauto with *.
   apply and_split; intros.
    red; rewrite <- H9.
    apply cc_prod_elim with (dom:=Nati y) (F:=U' i y); trivial.
    apply NATREC'_typ with (ord:=int O i) (U:=U' i);eauto with *.
    transitivity y'; trivial.

    rewrite <- H9; trivial.

  (* sat body *)
  apply piSAT0_intro'.
  2:exists (int O i).
  2:apply lt_osucc; auto.
  intros o' u lto satu.
  apply inSAT_exp.
   right; apply sat_sn in satu; trivial.
  rewrite <- tm_subst_cons.
  assert (ok': val_ok (Prod (NatI (Ref 0)) U::OSucct O::e)
            (V.cons (NATREC (F i) o') (V.cons o' i)) (I.cons u (I.cons (tm O j) j))).
   apply vcons_add_var.
   3:discriminate.
    apply vcons_add_var; trivial.
    2:discriminate.
    split.
     red; rewrite El_int_osucc; trivial.

     simpl; rewrite Real_def; auto with *.

     assert (NATREC (F i) o' ∈ cc_prod (Nati o') (U' i o')).
      apply NATREC'_typ with (ord:=int O i) (U:=U' i); eauto with *.
       apply isOrd_inv with (2:=lto); auto.
       apply olts_le in lto; trivial.
     apply and_split; intros.
      red; rewrite El_int_prod.
      revert H3; apply eq_elim; apply cc_prod_ext.
       simpl; rewrite El_def; reflexivity.

       apply ext_fun_ty.

      red in H4; rewrite El_int_prod in H4; trivial.
      rewrite Real_int_prod; trivial.
      revert satu; apply piSAT0_morph; intros; auto with *.
       red; simpl; intros; rewrite El_def; reflexivity.

       rewrite Real_int_NatI; trivial.
       rewrite fNATi_stages; auto with *.
       apply isOrd_inv with (2:=lto); auto.
 assert (ty_M' := ty_M _ _ ok').
 apply in_int_not_kind in ty_M'.
 2:discriminate.
 destruct ty_M' as (ty_M',sat_M').
 red in ty_M'; rewrite El_int_prod in ty_M'.
 rewrite Real_int_prod in sat_M'; trivial.
 apply piSAT0_intro.
  apply sat_sn in sat_M'; trivial.
 intros x v tyx satv.
 change (NATREC (F i) (osucc o')) with
   (NATREC' (fun o' f => int M (V.cons f (V.cons o' i))) (osucc o')).
 rewrite NATREC'_unfold with (ord:=int O i) (U:=U' i); eauto with *.
 2:eauto using isOrd_inv.
 2:apply olts_le; trivial.
 apply piSAT0_elim' in sat_M'; red in sat_M'.
 specialize sat_M' with (x:=x) (u0:=v).
 eapply Real_morph.
 3:apply sat_M'.
  rewrite int_lift_rec_eq.
  rewrite int_subst_rec_eq.
  rewrite int_lift_rec_eq.
  apply int_morph; auto with *.
  intros [|[|k]]; unfold V.lams,V.shift; simpl; try reflexivity.
   replace (k-0) with k; auto with *.

  reflexivity.

  simpl; rewrite El_def; auto.

  rewrite Real_int_NatI; auto.
  rewrite fNATi_stages in satv; auto.
  apply isOrd_succ; apply isOrd_inv with (2:=lto); auto.
Qed.
Print Assumptions typ_natfix.

(** Fixpoint equation holds only when applied to a constructor,
    because of the realizability part of the interpretation.
 *)
Lemma natfix_eq_0 :
  let N := Zero in
  typ e N (NatI O) ->
  eq_typ e (App (NatFix O M) N)
           (App (subst O (subst (lift 1 (NatFix O M)) M)) N).
intros N tyN.
red; intros.
destruct ty_O with (1:=H).

change
 (app (NATREC (F i) (int O i)) (int N i) ==
  app (int (subst O (subst (lift 1 (NatFix O M)) M)) i) (int N i)).
do 2 rewrite <- int_subst_eq.
rewrite int_cons_lift_eq.
change (NATREC (F i) (int O i)) with
   (NATREC' (fun o' f => int M (V.cons f (V.cons o' i))) (int O i)).
apply NATREC'_eqn with (ord:=int O i) (U:=U' i); eauto with *.
red in tyN; specialize tyN with (1:=H).
apply in_int_not_kind in tyN.
2:discriminate.
destruct tyN as (tyN,satN).
red in tyN.
simpl in tyN; rewrite El_def in tyN.
rewrite cc_bot_ax in tyN; destruct tyN; trivial.
symmetry in H2; apply discr_mt_pair in H2; contradiction.
Qed.

Lemma natfix_eq_S : forall X,
  let N := App (Succ O) X in
  typ e X (NatI O) ->
  typ e N (NatI O) ->
  eq_typ e (App (NatFix O M) N)
           (App (subst O (subst (lift 1 (NatFix O M)) M)) N).
intros X N tyX tyN.
red; intros.
destruct ty_O with (1:=H).
change
 (app (NATREC (F i) (int O i)) (int N i) ==
  app (int (subst O (subst (lift 1 (NatFix O M)) M)) i) (int N i)).
do 2 rewrite <- int_subst_eq.
rewrite int_cons_lift_eq.
change (NATREC (F i) (int O i)) with
   (NATREC' (fun o' f => int M (V.cons f (V.cons o' i))) (int O i)).
apply NATREC'_eqn with (ord:=int O i) (U:=U' i); eauto with *.
red in tyN; specialize tyN with (1:=H).
apply in_int_not_kind in tyN.
2:discriminate.
destruct tyN as (tyN,satN).
red in tyN.
simpl in tyN; rewrite El_def in tyN.
rewrite cc_bot_ax in tyN; destruct tyN; trivial.
rewrite beta_eq in H2; auto with *.
 symmetry in H2; apply discr_mt_pair in H2; contradiction.

 red; intros; apply inr_morph; trivial.

 red in tyX; specialize tyX with (1:=H).
 apply in_int_not_kind in tyX.
 2:discriminate.
 destruct tyX as (tyX,satX).
 trivial.
Qed.

Lemma natfix_extend :
  fx_subval E O ->
  fx_extends E (NatI O) (NatFix O M).
intro subO.
do 2 red; intros.
simpl in H0; rewrite El_def in H0.
assert (isval := proj1 H).
assert (isval' := proj1 (proj2 H)).
destruct ty_O with (1:=isval) as (oo,_).
destruct ty_O with (1:=isval') as (oo',_).
assert (inclo: int O i ⊆ int O i').
 apply subO in H; trivial.
clear subO.
simpl.
revert x H0.
elim oo using isOrd_ind; intros.
rewrite cc_bot_ax in H3; destruct H3.
 rewrite H3.
 rewrite NATREC'_strict with (ord:=int O i) (U:=U' i); eauto with *.
 rewrite NATREC'_strict with (ord:=int O i')(U:=U' i'); eauto with *.

 apply TI_inv in H3; trivial.
 destruct H3 as (o',?,?).
 assert (o_o' : isOrd o') by eauto using isOrd_inv.
 assert (o'_y : osucc o' ⊆ y).
  red; intros; apply le_lt_trans with o'; auto.
 rewrite <- NATREC'_irr with (ord:=int O i)(U:=U' i) (o:=osucc o')(o':=y); eauto with *.
 rewrite NATREC'_unfold with (ord:=int O i)(U:=U' i); eauto with *.
 rewrite NATREC'_eqn with (ord:=int O i') (U:=U' i'); eauto with *.
  do 2 red in stab; eapply stab.
  2:simpl; rewrite El_def; auto with *.
  apply val_mono_1 with (1:=H); auto with *.
   apply NATREC'_typ with (ord:=int O i) (U:=U' i); eauto with *.

   apply NATREC'_typ with (ord:=int O i') (U:=U' i'); eauto with *.

   red; intros.
   eapply H2; auto.

 revert H4; apply TI_mono; auto with *.
 red; intros; apply le_lt_trans with o'; auto.
 apply inclo; apply H1; trivial.
Qed.

Lemma natfix_equals :
  fx_equals E O ->
  fx_equals E (NatFix O M).
red; intros.
assert (isval := proj1 H0).
assert (isval' := proj1 (proj2 H0)).
destruct ty_O with (1:=proj1 H0) as (Oo,_); trivial.
assert (fxs: fx_subval E O).
 apply fx_equals_subval; trivial.
red in H; specialize H with (1:=H0).
apply natfix_extend in fxs.
red in fxs.
specialize fxs with (1:=H0).
apply fcompat_typ_eq with (3:=fxs).
 simpl El; rewrite El_def.
 eapply cc_prod_is_cc_fun.
 apply NATREC'_typ with (ord:=int O i) (U:=U' i); eauto with *.

 simpl El; rewrite El_def.
 rewrite H in Oo|-*.
 eapply cc_prod_is_cc_fun.
 apply NATREC'_typ with (ord:=int O i') (U:=U' i'); eauto with *.
Qed.

End NatFixRules.

Print Assumptions natfix_eq_S.
Print Assumptions natfix_extend.

Lemma typ_natfix' : forall e O U M T,
       T <> kind ->
       typ_ord e O ->
       typ (Prod (NatI (Ref 0)) U :: OSucct O :: e) M
         (Prod (NatI (OSucc (Ref 1)))
         (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U)))) ->
       fx_extends (push_fun (push_ord (tinj e) (OSucct O)) (NatI (Ref 0)) U)
         (NatI (OSucc (Ref 1))) M ->
       fx_sub (push_var (push_ord (tinj e) (OSucct O)) (NatI (OSucc (Ref 0)))) U ->
       sub_typ e (Prod (NatI O) (subst_rec O 1 U)) T ->
       typ e (NatFix O M) T.
intros.
apply typ_subsumption with (Prod (NatI O) (subst_rec O 1 U)); auto.
2:discriminate.
change e with (tenv (tinj e)).
apply typ_natfix; trivial.
Qed.


(** Variance results *)

  Lemma NatI_sub : forall e O,
    typ_ord (tenv e) O ->
    fx_subval e O ->
    fx_sub e (NatI O).
unfold fx_sub, fx_subval.
intros e O tyO subO i i' j j' val_m x t (xreal,xsat).
destruct tyO with (1:=proj1 val_m).
destruct tyO with (1:=proj1 (proj2 val_m)).
specialize subO with (1:=val_m).
red in xreal; simpl in xreal; rewrite El_def in xreal.
rewrite Real_int_NatI in xsat; trivial.
assert (cc_bot (TI NATf' (int O i)) ⊆ cc_bot (TI NATf' (int O i'))).
 apply cc_bot_mono.
 apply TI_mono; auto with *.
split.
 red; simpl; rewrite El_def; auto with *.

 rewrite Real_int_NatI; auto.
Qed.


Lemma typ_natfix'' e O U M T :
       T <> kind ->
       sub_typ (tenv e) (Prod (NatI O) (subst_rec O 1 U)) T ->
       typ_ord (tenv e) O ->
       typ_mono (push_var (push_ord e (OSucct O)) (NatI (OSucc (Ref 0)))) U ->
       typ_ext (push_fun (push_ord e (OSucct O)) (NatI (Ref 0)) U)
         M (NatI (OSucc (Ref 1)))
           (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
       typ (tenv e) (NatFix O M) T.
intros.
destruct H2; destruct H3.
apply typ_subsumption with (2:=H0); trivial.
2:discriminate.
apply typ_natfix; trivial.
Qed.

  Lemma typ_ext_fix e O U M :
    typ_ord_mono e O ->
    typ_ext (push_fun (push_ord e (OSucct O)) (NatI (Ref 0)) U) M
      (NatI (OSucc (Ref 1)))
      (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    fx_sub (push_var (push_ord e (OSucct O)) (NatI (OSucc (Ref 0)))) U ->
    typ_ext e (NatFix O M) (NatI O) (subst_rec O 1 U).
intros tyO tyM tyU.
destruct tyO as (inclO,tyO).
destruct tyM as (extM,tyM).
assert (tyF: typ (tenv e) (NatFix O M) (Prod (NatI O) (subst_rec O 1 U))).
 apply typ_natfix; trivial.
split; trivial.
red; intros.
generalize i i' j j' H; change (fx_extends e (NatI O) (NatFix O M)).
apply natfix_extend with U; trivial.
Qed.

  Lemma typ_impl_fix e O U M :
    typ_ord_impl e O ->
    typ_ext (push_fun (push_ord e (OSucct O)) (NatI (Ref 0)) U) M
      (NatI (OSucc (Ref 1)))
      (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    fx_sub (push_var (push_ord e (OSucct O)) (NatI (OSucc (Ref 0)))) U ->
    typ_impl e (NatFix O M) (Prod (NatI O) (subst_rec O 1 U)).
intros (inclO,tyO) (extM,tyM) tyU.
assert (tyF: typ (tenv e) (NatFix O M) (Prod (NatI O) (subst_rec O 1 U))).
 apply typ_natfix; trivial.
split; trivial.
red; intros.
generalize i i' j j' H; change (fx_equals e (NatFix O M)).
apply natfix_equals with U; trivial.
Qed.

