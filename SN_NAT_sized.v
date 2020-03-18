(** Strong normalization of the model of CC+NAT in the type-based
    termination presentation.

    This is a copy of SN_W, but in a simpler case.
*)
Require Import basic Models.
Require SN_ECC_Real.
Import ZFgrothendieck.
Import ZF ZFsum ZFnats ZFrelations ZFord ZFfix.
Require Import ZFfunext ZFcoc ZFecc SATtypes SATnat_real.
Require Import ZFrecbot.

Import ZFuniv_real SN_ECC_Real.
Opaque Real.
Import Sat Sat.SatSet.


(** Ordinals *)

Require Import SN_ord.

Definition infty := cst omega.

Lemma typ_infty : forall e, typ_ord e infty.
split; simpl; auto.
exact Lc.sn_K.
Qed.

Hint Resolve typ_infty.

(** Judgments with variance *)

Require Import SN_variance.

(*Definition push e T o dom :=
  Build_fenv (T::tenv e) (B.cons o (ords e)) (OT.cons dom (fixs e)).
Lemma val_mono_shift1 e i j i' j' T  o dom :
  val_mono (push e T o dom) i j i' j' ->
  val_mono e (V.shift 1 i) (I.shift 1 j) (V.shift 1 i') (I.shift 1 j').
Admitted.*)
(*Lemma typ_impl_varS e n T o dom U U' :
  typ_impl e (Ref n) U ->
  eq_term (lift 1 U) U' ->
  typ_impl (push e T o dom) (Ref (S n)) U'.
Admitted.*)

Module Type PartialNats.
  Include Nats.

  (* Partial model *)
  Parameter NATf': set -> set.
  Parameter NATf'_mono : Proper (incl_set ==> incl_set) NATf'.
  Existing Instance NATf'_mono.
  Parameter zero_typ : forall X, zero ∈ NATf' X.
  Parameter succ_typ : forall X n, n ∈ cc_bot X -> succ n ∈ NATf' X.
  Definition NAT' := TI NATf' omega.
  Parameter NAT_eqn : TI NATf' omega == NATf' (TI NATf' omega).
  Parameter G_NATf' : forall U X,
    grot_univ U ->
    X ∈ U -> NATf' X ∈ U.
  Parameter NATf'_elim : forall X n, 
    n ∈ NATf' X -> isNat X n.
  
  Parameter natfix : (set -> set -> set) -> set -> set.
  Parameter natfix_morph : Proper ((eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) natfix.

  Parameter natfix_rec : forall o M U,
      typed_bot_recursor_hyps (singl empty) (TI NATf') U M o ->
      typed_bot_recursor_spec (singl empty) (TI NATf') U M (natfix M) o.
End PartialNats.

Module Make (M:PartialNats).

  Module SATN := SATnat_real.Make M.
  Import SATN.

  Module NFacts := SATnat_real.NatFacts M.
  Import NFacts.

Lemma NATf'm : morph1 (TI NATf').
apply TI_morph; auto.
Qed.

Lemma NATf'_cont : ZFfixrec.continuous (TI NATf').
red; intros.
apply TI_mono_eq; auto with *.
Qed.

Lemma NATf'_nmt o : isOrd o -> ~ empty ∈ TI NATf' o.
red; intros.
apply TI_elim in H0; auto with *.
destruct H0 as (o',?,Hmt).
apply NATf'_elim in Hmt.
apply isNat_nmt in Hmt.
apply Hmt; reflexivity.
Qed.

Hint Resolve NATf'm NATf'_cont NATf'_nmt.

(** NAT *)

Section NAT_typing.

Definition NatI (O:term) : term.
(*begin show*)
left; exists (fun i => mkTY (TI NATf' (int O i)) cNAT)
             (fun j => tm O j).
(*end show*)
 do 2 red; intros.
 apply mkTY_ext; intros.
  apply TI_morph_gen; auto with *.

  apply Fmono_morph; auto with *.

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

Global Instance NatI_morph : Proper (eq_term==>eq_term) NatI.
do 2 red; intros.
apply eq_term_intro; simpl; trivial; intros.
 apply mkTY_ext.
  rewrite H; reflexivity.

  intros.
  apply cNAT_morph; trivial.

 rewrite H; reflexivity.
Qed.
Lemma eq_sb_NatI A k O :
     eq_term (subst_rec A k (NatI O)) (NatI (subst_rec A k O)).
apply eq_term_intro; simpl; trivial.
 intros; apply mkTY_ext; intros.
  rewrite int_subst_rec_eq; reflexivity.

  apply cNAT_morph; trivial.

 intros.
 rewrite tm_subst_rec_eq; trivial.
Qed.
Lemma eq_lft_NatI n k O :
     eq_term (lift_rec n k (NatI O)) (NatI (lift_rec n k O)).
apply eq_term_intro; simpl; trivial.
 intros; apply mkTY_ext; intros.
  rewrite int_lift_rec_eq; reflexivity.

  apply cNAT_morph; trivial.

 intros.
 rewrite tm_lift_rec_eq; trivial.
Qed.

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

Lemma typ_NatI e O :
  typ_ord e O ->
  typ e (NatI O) kind.
intros tyO i j valok; simpl.
red in tyO; specialize tyO with (1:=valok).
split;[|split].
 discriminate.

 exists nil; exists (NatI O);[reflexivity|].
 exists empty; simpl; auto.
(* red; auto.*)

 simpl.
 apply tyO.
Qed.

Lemma typ_NatI_type e n O :
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

    apply TI_pre_fix; auto with *.
    unfold NAT'; rewrite <- NAT_eqn; reflexivity.

 red in H.
 change (int (type n) i) with (sn_sort (ecc (S n))).
 rewrite Real_sort_sn; trivial.
Qed.

Lemma NatI_sub_infty e O :
  typ_ord e O ->
  sub_typ e (NatI O) (NatI infty).
red; intros.
destruct H with (1:=H0).
destruct H1.
red in H1; simpl in H1; rewrite El_def in H1.
apply and_split.
 red; simpl; rewrite El_def.
 revert H1; apply cc_bot_mono.
 apply TI_pre_fix; auto with *.
 rewrite <- NAT_eqn; auto with *.

 simpl in *; intros.
 red in H5; rewrite El_def in H5.
 rewrite Real_def in H4|-*; trivial.
  intros; apply cNAT_morph; trivial.
  intros; apply cNAT_morph; trivial.
Qed.

Lemma NatI_sub_osucc e O :
  typ_ord e O ->
  sub_typ e (NatI O) (NatI (OSucc O)).
red; intros.
destruct H with (1:=H0).
destruct H1.
red in H1; simpl in H1; rewrite El_def in H1.
apply and_split.
 red; simpl; rewrite El_def.
 revert H1; apply cc_bot_mono.
 apply TI_mono; auto with *.
 red; intros; apply isOrd_trans with (int O i); auto with *.

 simpl in *; intros.
 red in H5; rewrite El_def in H5.
 rewrite Real_def in H4|-*; trivial.
  intros; apply cNAT_morph; trivial.
  intros; apply cNAT_morph; trivial.
Qed.

  Lemma NatI_sub e O :
    typ_ord (tenv e) O ->
    fx_subval e O ->
    fx_sub e (NatI O).
unfold fx_sub, fx_subval.
intros tyO subO i i' j j' val_m x t (xreal,xsat).
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


(** Constructors *)

Definition Zero : term.
(* begin show *)
left; exists (fun i => M.zero)
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


Lemma typ_0 e O :
  typ_ord e O ->
  typ e Zero (NatI (OSucc O)).
red; intros.
apply in_int_intro; try discriminate.
red in H; specialize H with (1:=H0); destruct H as (oo,osn).
assert (M.zero ∈ TI NATf' (osucc (int O i))).
 apply TI_intro with (int O i); auto with *.
 apply zero_typ. 
split.
 red; rewrite El_int_NatI; auto.

 rewrite Real_int_NatI; auto.
 simpl.
 apply Real_ZERO.
Qed.

Definition Succ (O:term) : term.
(* begin show *)
left; exists (fun i => lam (mkTY (TI NATf' (int O i)) cNAT) succ)
             (fun j => Lc.App2 Lc.K (Lc.Abs (SU (Lc.Ref 0))) (tm O j)).
(* end show *)
 do 2 red; intros; apply cc_lam_morph; auto with *.
  rewrite !El_def.
  rewrite H; reflexivity.
  apply succ_morph.
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


Lemma typ_S e O :
  typ_ord e O ->
  typ e (Succ O) (Prod (NatI O) (lift 1 (NatI (OSucc O)))).
red; intros tyO i j valok.
red in tyO; specialize tyO with (1:=valok); destruct tyO as (oo,snO).
apply in_int_intro; try discriminate.
assert (lam (mkTY (TI NATf' (int O i)) cNAT) succ ∈
        cc_arr (cc_bot (TI NATf' (int O i))) (cc_bot (TI NATf' (osucc (int O i))))).
 eapply in_reg.
 2:apply cc_arr_intro.
  apply cc_lam_ext.
   rewrite El_def; reflexivity.

   do 2 red; intros; apply succ_morph.
   exact H0.

  do 2 red; intros; apply succ_morph; trivial.

  intros.
  apply cc_bot_intro.
  apply TI_intro with (int O i); auto with *.
  apply succ_typ; trivial.
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
 assert (cc_app (lam (mkTY (TI NATf' (int O i)) cNAT) succ) x == succ x).
  apply beta_eq.
   do 2 red; intros; apply succ_morph; trivial.
   red; rewrite El_def; trivial.
 rewrite H2.
 rewrite Real_def.
 2:intros; apply cNAT_morph; trivial.

 apply inSAT_exp.
  apply sat_sn in H1; auto.
 unfold Lc.subst; simpl.
 apply Real_SUCC; trivial.

 apply cc_bot_intro.
 rewrite V.lams0.
 apply TI_intro with (int O i); auto with *.
 apply succ_typ; trivial.
Qed.

Lemma ext_S e O :
  typ_ord (tenv e) O ->
  fx_subval e O ->
  fx_extends e (NatI O) (Succ O).
red; red; simpl; intros.
rewrite beta_eq; trivial.
2:red; intros; apply succ_morph; trivial.
rewrite beta_eq; auto with *.
 red; intros; apply succ_morph; trivial.
red; rewrite El_def in H2|-*.
revert H2; apply cc_bot_mono.
destruct H with (1:=proj1 H1) as (?,_).
destruct H with (1:=proj1 (proj2 H1)) as (?,_).
apply TI_mono; auto.
auto with *.

apply H0 with (1:=H1).
Qed.

(* Case analysis *)

Definition NatCase (b0 bS n : term) : term.
(*begin show*)
left; exists (fun i => natcase (int b0 i) (fun x => int bS (V.cons x i)) (int n i))
             (fun j => NCASE (tm b0 j) (Lc.Abs (tm bS (Lc.ilift j))) (tm n j)).
(*end show*)
do 2 red; intros.
apply natcase_morph.
 rewrite H; reflexivity.

 red; intros.
 rewrite H,H0; reflexivity.

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
  Proper (eq_term ==> eq_term ==> eq_term ==> eq_term) NatCase.
split; red; simpl; intros.
 apply natcase_morph.
  apply int_morph; trivial.

  red; intros.
  apply int_morph; trivial.
  apply V.cons_morph; trivial.

  apply int_morph; trivial.

 rewrite H.
 rewrite H0.
 rewrite H1.
 rewrite H2.
 reflexivity.
Qed.


Lemma NatCase_iota_0 e B0 BS :
  eq_typ e (NatCase B0 BS Zero) B0.
red; intros.
simpl.
rewrite natcase_zero; reflexivity.
Qed.


Lemma NatCase_iota_S e B0 BS O N :
  typ e N (NatI O) ->
  eq_typ e (NatCase B0 BS (App (Succ O) N)) (subst N BS).
red; intros.
simpl.
red.
assert (BSm : morph1 (fun x => int BS (V.cons x i))).
 do 2 red; intros.
 rewrite H1; reflexivity.
eapply transitivity.
 apply natcase_morph.
  reflexivity.

  intros ? ? h.
  apply int_morph;[reflexivity|].
  apply V.cons_morph;[exact h|reflexivity].

  apply beta_eq.
   do 2 red; intros; apply succ_morph; trivial.
  apply H in H0.
  apply in_int_not_kind in H0.
  2:discriminate.
  destruct H0; trivial.
rewrite natcase_succ; trivial.
apply int_subst_eq.
Qed.

Lemma typ_NatCase e P O B0 BS n :
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
 apply cc_bot_ax in tyN; destruct tyN.
  (* neutral case *)
  apply in_reg with empty; auto.
  symmetry; apply natcase_outside; trivial.

  (* constructor case *)
  simpl in H; rewrite TI_mono_succ in H; auto with *.
  apply NATf'_elim in H; destruct H.
   rewrite H.
   rewrite natcase_zero.
   trivial.

   destruct H.
   rewrite H0.
   rewrite natcase_succ; auto with *.
   specialize ok' with (1:=H) (2:=varSAT _).
   red in tyBS; specialize tyBS with (1:=ok').
   apply in_int_not_kind in tyBS;[|discriminate].
   destruct tyBS as (tyBS,_).    
   revert tyBS; apply eq_elim.
   apply El_morph.
   apply cc_app_morph.
    rewrite int_lift_eq; reflexivity.
   simpl.
   apply beta_eq.
    do 2 red; intros; apply succ_morph; trivial.

    red; rewrite El_def; trivial.
    rewrite V.lams0.
    trivial.

 (* Reducibility *)
 simpl in H|-*.
 apply cc_bot_ax in tyN; destruct tyN.
  (* neutral case *)
  eapply prodSAT_elim.
   eapply prodSAT_elim.
    apply neuSAT_def.
    rewrite cNAT_neutral in satN; trivial.

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
  apply Real_NATCASE with (X:=TI NATf' (int O i))(C:=fun k =>Real (app (int P i) k)
    (natcase (int B0 i) (fun x => int BS (V.cons x i)) k)); auto.
   do 2 red; intros.
   apply Real_morph.
    rewrite H1; reflexivity.

    apply natcase_morph; auto with *.

   apply NATf'_elim.
   simpl in H0.
   rewrite TI_mono_succ in H0; auto with *.
   
   rewrite natcase_zero.
   trivial.

   apply piSAT0_intro'.
   2:exists empty; auto.
   intros.
   apply inSAT_exp.
    apply sat_sn in H2; auto.
   rewrite <- tm_subst_cons.
   specialize ok' with (1:=H1) (2:=H2).
   red in tyBS; specialize tyBS with (1:=ok').
   apply in_int_not_kind in tyBS;[|discriminate].
   destruct tyBS as (tyBS,satBS).
   revert satBS; apply inSAT_morph; auto with *.
   apply Real_morph.
    simpl.
    rewrite int_lift_eq.
    apply cc_app_morph; [reflexivity|].
    rewrite beta_eq; auto with *.
     red; intros; apply succ_morph; trivial.

     red; rewrite El_def.     
     rewrite V.lams0.
     trivial.

    rewrite natcase_succ; auto with *.

Qed.

Lemma typ_NatCase' e P O B0 BS n T :
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


  Lemma impl_NatCase e O b0 bS n P :
  typ_ord_mono e O ->
  typ_impl e b0 (App P Zero) ->
  typ_impl (push_var e (NatI O)) bS (App (lift 1 P) (App (lift 1 (Succ O)) (Ref 0))) ->
  typ_impl e n (NatI (OSucc O)) ->
  typ_impl e (NatCase b0 bS n) (App P n).
intros.
split.
 red; simpl; intros.
 apply natcase_ext with (X:=TI NATf' (int O i)); auto with *.
  do 2 red; intros.
  rewrite H4; reflexivity.

  do 2 red; intros.
  rewrite H4; reflexivity.

  destruct H2.
  assert (aux := H4 _ _ (proj1 H3)).
  apply in_int_not_kind in aux;[|discriminate].
  destruct aux.
  simpl in H5; red in H5; rewrite El_def in H5; trivial.
  apply cc_bot_ax in H5; destruct H5;[auto|].
  rewrite TI_mono_succ in H5; auto with *.
   right; apply NATf'_elim; trivial.

   apply (proj1 (proj2 H _ _ (proj1 H3))).

  apply (proj1 H2 _ _ _ _ H3).

  apply (proj1 H0 _ _ _ _ H3).

  red; intros.
  destruct H1.
  apply H1 with (I.cons daimon j) (I.cons daimon j').
  apply val_push_var; trivial.
   split;[|apply varSAT].
   red; simpl; rewrite El_def; trivial.

   split;[|apply varSAT].
   red; simpl; rewrite El_def; trivial.
   rewrite <- H5; revert H4; apply cc_bot_mono.
   destruct H.
   apply TI_mono; auto with *.
    apply H4 with (1:=proj1 (proj2 H3)).
    apply H4 with (1:=proj1 H3).
    apply H with (1:=H3).

   discriminate.

 eapply typ_NatCase with (1:=proj2 H).
  apply H0.
  apply H1.
  apply H2.
Qed.

Lemma impl_NatCase' e O0 b0 bS n P :
   P <> kind ->
   typ_ord_mono e O0 ->
       typ_impl e b0 (subst Zero P) ->
       typ_impl (push_var e (NatI O0)) bS
         (subst (App (lift 1 (Succ O0)) (Ref 0)) (lift1 1 P)) ->
       typ_impl e n (NatI (OSucc O0)) ->
       typ_impl e (NatCase b0 bS n) (subst n P).
intros Pnk tyO tyb0 tybS tyn.
apply typ_impl_subsumption with (App (Abs (NatI (OSucc O0)) P) n).
3:discriminate.
3:destruct P;[discriminate|elim Pnk; trivial].
 
 apply impl_NatCase with (O0:=O0); trivial.
  apply typ_impl_subsumption with (subst Zero P); trivial.
  2:destruct P;[discriminate|elim Pnk; trivial].
  2:discriminate.
  apply sub_refl.
  symmetry; apply eq_typ_betar.
  2:discriminate.
  apply typ_0.
  apply tyO.

  apply typ_impl_subsumption with
    (subst (App (lift 1 (Succ O0)) (Ref 0)) (lift1 1 P)); trivial.
  2:destruct P;[discriminate|elim Pnk; trivial].
  2:discriminate.
  unfold lift at 2.
  rewrite red_lift_abs.
  apply sub_refl.
  symmetry; apply eq_typ_betar.
  2:discriminate.
  apply typ_subsumption with (subst (Ref 0)(lift 1 (lift 1 (NatI (OSucc O0))))).
  3:discriminate.
  3:discriminate.
   apply typ_app with (lift 1 (NatI O0)).
   3:discriminate.
   3:discriminate.
    apply typ_var.
    reflexivity.

    eapply typ_subsumption.
    apply weakening.
    apply typ_S.
    apply tyO.
    2:discriminate.
    2:discriminate.
    apply sub_refl; apply eq_term_eq_typ.
    unfold lift; rewrite red_lift_prod.
    apply Prod_morph; auto with *.
    apply eq_term_intro; [| |simpl; trivial].
     intros; rewrite !int_lift_rec_eq.
     apply int_morph; auto with *.
     intros [|k]; reflexivity.

     intros; rewrite !tm_lift_rec_eq.
     apply tm_morph; auto with *.
     intros [|k]; reflexivity.

apply sub_refl; apply eq_term_eq_typ.
fold (lift 1 (NatI (OSucc O0))).
apply eq_term_intro.
 intros i.
 rewrite <- int_subst_eq.
 rewrite !int_lift_eq.
 apply int_morph; auto with *.
 reflexivity.

 intros j.
 unfold subst; rewrite tm_subst_rec_eq.
 unfold lift; rewrite !tm_lift_rec_eq. 
 apply tm_morph; auto with *.
 rewrite !I.lams0.
 reflexivity.

 exact I.

 apply sub_refl.
 apply eq_typ_betar; trivial.
 apply tyn.
 discriminate.
Qed.

End NAT_typing.

(*****************************************************************************)
(** Recursor (without case analysis) *)

(* NatFix O M is a fixpoint of domain NatI O with body M *)
Definition NatFix (O M:term) : term.
(*begin show*)
left.
exists (fun i =>
         natfix (fun o' f => int M (V.cons f (V.cons o' i))) (int O i))
       (fun j => NATFIX (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j))))).
(*end show*)
 do 2 red; intros.
 apply natfix_morph.
  do 2 red; intros.
  apply int_morph; auto with *.
  apply V.cons_morph; trivial.
  apply V.cons_morph; trivial.

  apply int_morph; auto with *.

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
  Variable O U M : term.

  Hypothesis ty_O : typ_ord e O.
  Hypothesis ty_M : typ (Prod (NatI (Ref 0)) U::OSucct O::e)
    M (Prod (NatI (OSucc (Ref 1)))
         (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U)))).

  Hypothesis stab : fx_extends
    (push_fun (push_ord E (OSucct O)) (NatI (Ref 0)) U)
    (NatI (OSucc (Ref 1)))
    M.

  Hypothesis fx_sub_U :
    fx_sub (push_var (push_ord E (OSucct O)) (NatI (OSucc (Ref 0)))) U.

  Let Nati o := cc_bot (TI NATf' o).
  Let F i := fun o' f => squash (int M (V.cons f (V.cons o' i))).
  Let U' i := fun o' x => El (int U (V.cons x (V.cons o' i))).
  Notation F' i := (fun o' f => int M (V.cons f (V.cons o' i))).

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

  Lemma val_ok_1 i j o ot f u :
    val_ok e i j ->
    isOrd (int O i) ->
    isOrd o ->
    o ∈ cc_bot (int O i) ->
    f ∈ (Π w ∈ Nati o, U' i o w) ->
    Lc.sn ot ->
    inSAT u
          (piSAT0 (fun n => n ∈ Nati o) cNAT
                  (fun n => Real (int U (V.cons n (V.cons o i))) (cc_app f n))) ->
    val_ok (Prod (NatI (Ref 0)) U::OSucct O::e)
            (V.cons f (V.cons o i)) (I.cons u (I.cons ot j)).
intros ok Oo oo tyo tyf sato satu.
apply vcons_add_var.
3:discriminate.
 apply vcons_add_var; trivial.
 2:discriminate.
 split; simpl.
  red; rewrite El_def.
  revert tyo; apply cc_bot_mono.
  red; intros; apply isOrd_trans with (int O i); auto.

  rewrite Real_def; auto.
   reflexivity.
  revert tyo; apply cc_bot_mono.
  red; intros; apply isOrd_trans with (int O i); auto.

 apply int_Prod_intro.
  revert tyf; apply eq_set_ax.
  apply cc_prod_ext.
   apply El_int_NatI; auto with *.

   red; intros.
   unfold U'.
   rewrite H0; reflexivity.

  intros.
  destruct H.
  red in H; rewrite El_int_NatI in H.
  rewrite Real_int_NatI in H1; trivial.
  apply piSAT0_elim' in satu.
  apply satu; trivial.
Qed.

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
  red; rewrite El_int_osucct.
  apply ole_lts; trivial.

  split;[|apply varSAT].
  red; rewrite El_int_osucct.
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
  red; rewrite El_int_osucct.
  apply ole_lts; auto.
  transitivity y'; trivial.

  split;[|apply varSAT].
  red; rewrite El_int_osucct.
  apply ole_lts; auto.

 split;[|apply varSAT].
 red; simpl; rewrite El_def.
 revert H5; apply cc_bot_mono.
 apply TI_incl; simpl; auto with *.

 split;[|apply varSAT].
 red; simpl; rewrite El_def.
 rewrite <- H6.
 revert H5; apply cc_bot_mono.
 apply TI_incl; simpl; auto with *.
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
(*
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
*)
Let Mirr : forall i j,
 val_ok e i j ->
 forall o' o'' f g,
 isOrd o' ->
 o' ⊆ o'' ->
 o'' ∈ osucc (int O i) ->
 f ∈ cc_prod (Nati o') (U' i o') ->
 g ∈ cc_prod (Nati o'') (U' i o'') ->
 fcompat (Nati o') f g ->
 fcompat (Nati (osucc o')) (int M (V.cons f (V.cons o' i))) (int M (V.cons g (V.cons o'' i))).
intros.
assert (Oo: isOrd (int O i)).
 apply ty_O with (1:=H).
assert (o'' ⊆ int O i).
 apply olts_le in H2; trivial.
assert (val_mono (push_fun (push_ord E (OSucct O)) (NatI (Ref 0)) U)
         (V.cons f (V.cons o' i)) (I.cons daimon (I.cons daimon j))
         (V.cons g (V.cons o'' i)) (I.cons daimon (I.cons daimon j))).
 apply val_mono_1; auto with *.
  apply val_mono_refl; trivial.

  eauto using isOrd_inv.

  transitivity o''; auto.
apply stab in H7.
simpl in *.
rewrite El_def in H7; trivial.
Qed.
Let Usub : forall i j,
 val_ok e i j ->
 forall o' o'' x x',
 isOrd o' ->
 o' ⊆ o'' ->
 o'' ∈ osucc (int O i) ->
 x ∈ Nati o' ->
 x == x' ->
 U' i o' x ⊆ U' i o'' x'.
intros.
destruct ty_O with (1:=H) as (Oo,_).
assert (o'' ⊆ int O i).
 apply olts_le in H2; trivial.
eapply El_sub with (1:=fx_sub_U).
apply val_mono_2; auto with *.
 apply val_mono_refl; eexact H.

 eauto using isOrd_inv.
Qed.

Lemma Mok i j :
  val_ok e i j ->
  typed_bot_recursor_spec (singl empty) (TI NATf') (U' i) (F' i) (natfix (F' i)) (int O i).
intros.
assert (Oo: isOrd (int O i)).
 apply ty_O with (1:=H).
apply natfix_rec.
split; auto.
 intros.
 apply singl_elim in H1; rewrite H1 in H2.
 apply NATf'_nmt with o'; trivial.

 intros.
 apply Usub with (1:=H); trivial.

 intros; apply Mty with (2:=H); trivial.
  apply isOrd_inv with (osucc (int O i)); auto.  

  apply isOrd_trans with (int O i); auto.

  apply ord_lt_le; trivial.
(*  apply olts_le in H0; trivial.*)

 intros.
 apply Mirr with (1:=H); trivial.
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
 2:simpl; apply typed_bot_rec_typ with (1:=Mok H); auto with *.
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
         cNAT
         (fun x =>
            Real (int U (V.cons x (V.cons (int O i) i))) 
              (cc_app (natfix (F' i) (int O i)) x)))).
 { apply piSAT0_morph; intros; auto with *.
   red; simpl; intros; rewrite El_def; reflexivity.

   apply Real_int_NatI; auto with *.

   apply Real_morph; simpl;[|reflexivity].
   rewrite int_subst_rec_eq.
   apply int_morph; auto with *.
   intros [|[|k]]; reflexivity.
 }
assert (ok := Mok H).
eapply recursor_sat with (6:=Mok H)
   (RU:= fun o w => Real (int U (V.cons w (V.cons o i)))); auto with *.
 apply WHEN_SUM_neutral2.

 intros.
 apply WHEN_SUM_satnat with (1:=H5); trivial.

 (* *)
 intros.
 apply union2_ax in H5; destruct H5.
  apply singl_elim in H5.
  left.
  apply cNAT_neutral; trivial.

  right.
  apply TI_inv in H5; auto with *.
  
 (* *)
 intros; exists empty.
 apply union2_intro1; apply singl_intro.

 (**)
 do 4 red; intros; apply Real_morph; auto with *.
 apply int_morph; auto with *.
 repeat apply V.cons_morph; auto with *.

 (**)
 red; intros.
 apply fx_sub_U with (V.cons x (V.cons o' i))
     (I.cons daimon (I.cons daimon j)) (I.cons daimon (I.cons daimon j)).
  apply val_mono_2; auto with *.
  unfold Nati; auto.

  split.
   rewrite <- H9; trivial.
   rewrite <- H9; trivial.

 (**)
 intros.
 apply inSAT_exp;[right;apply sat_sn in H6;trivial|].
 replace (Lc.subst u (tm M (Lc.ilift (I.cons (tm O j) j)))) with
     (tm M (I.cons u (I.cons (tm O j) j))).
 2:unfold Lc.subst; rewrite <- tm_substitutive.
 2:apply tm_morph; auto with *.
 2:intros [|[|k]]; unfold Lc.ilift,I.cons; simpl.
 2:rewrite Lc.lift0; reflexivity.
 2:rewrite Lc.simpl_subst; trivial.
 2:rewrite Lc.lift0; trivial.
 2:rewrite Lc.simpl_subst; trivial.
 2:rewrite Lc.lift0; trivial.
 assert (ok': val_ok (Prod (NatI (Ref 0)) U::OSucct O::e)
            (V.cons f (V.cons o' i)) (I.cons u (I.cons (tm O j) j))).
  apply val_ok_1; trivial.
 assert (ty_M' := ty_M _ _ ok').
 apply in_int_not_kind in ty_M'.
 2:discriminate.
 destruct ty_M' as (ty_M',sat_M').
 red in ty_M'; rewrite El_int_prod in ty_M'.
 rewrite Real_int_prod in sat_M'; trivial.
 revert sat_M'; apply piSAT0_morph.
  red; intros.
  rewrite El_int_NatI; auto.

  intros.
  symmetry; apply Real_int_NatI; auto.

  intros.
  apply Real_morph; auto with *.
  rewrite int_lift_rec_eq.
  rewrite int_subst_rec_eq.
  rewrite int_lift_rec_eq.
  apply int_morph; auto with *.
  intros [|[|k]]; try reflexivity.
  unfold V.cons, V.lams,V.shift; simpl.
  replace (k-0) with k; auto with *.
Qed.

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
 (app (natfix (F' i) (int O i)) (int N i) ==
  app (int (subst O (subst (lift 1 (NatFix O M)) M)) i) (int N i)).
do 2 rewrite <- int_subst_eq.
rewrite int_cons_lift_eq.
apply typed_bot_rec_eqn with (1:=Mok H); eauto with *.
red in tyN; specialize tyN with (1:=H).
apply in_int_not_kind in tyN.
2:discriminate.
destruct tyN as (tyN,satN).
red in tyN.
simpl in tyN; rewrite El_def in tyN.
apply cc_bot_ax in tyN; destruct tyN; auto.
apply zero_nmt in H2; contradiction.
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
 (app (natfix (F' i) (int O i)) (int N i) ==
  app (int (subst O (subst (lift 1 (NatFix O M)) M)) i) (int N i)).
do 2 rewrite <- int_subst_eq.
rewrite int_cons_lift_eq.
apply typed_bot_rec_eqn with (1:=Mok H); auto with *.
red in tyN; specialize tyN with (1:=H).
apply in_int_not_kind in tyN.
2:discriminate.
destruct tyN as (tyN,satN).
red in tyN.
simpl in tyN; rewrite El_def in tyN.
apply cc_bot_ax in tyN; destruct tyN; trivial.
assert (int X i ∈ cc_bot (TI NATf' (int O i))).
 red in tyX; specialize tyX with (1:=H).
 apply in_int_not_kind in tyX.
 2:discriminate.
 destruct tyX as (tyX,satX).
 simpl in tyX.
 red in tyX; rewrite El_def in tyX; trivial.
rewrite beta_eq in H2; auto with *.
 apply succ_nmt in H2; contradiction.

 red; intros; apply succ_morph; trivial.

 red; rewrite El_def; trivial.
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
apply typed_bot_rec_ext with (6:=Mok isval) (7:=Mok isval'); auto with *.
intros.
red; intros.
do 2 red in stab; eapply stab.
 apply val_mono_1 with (1:=H); auto with *.
 transitivity (int O i); trivial.

 simpl.
 rewrite El_def; auto.
Qed.

Lemma natfix_equals :
  fx_equals E O ->
  fx_equals E (NatFix O M).
red; intros.
assert (isval := proj1 H0).
assert (isval' := proj1 (proj2 H0)).
assert (Oo : isOrd (int O i)).
 apply ty_O with (1:=isval).
assert (fxs: fx_subval E O).
 apply fx_equals_subval; trivial.
red in H; specialize H with (1:=H0).
apply natfix_extend in fxs.
red in fxs.
specialize fxs with (1:=H0).
apply fcompat_typ_eq with (3:=fxs).
 rewrite El_int_NatI.
 eapply cc_prod_is_cc_fun.
 apply typed_bot_rec_typ with (1:=Mok isval); auto with *.

 rewrite El_int_NatI.
 simpl.
 rewrite H in Oo|-*.
 eapply cc_prod_is_cc_fun.
 apply typed_bot_rec_typ with (1:=Mok isval'); auto with *.
Qed.

End NatFixRules.


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

(** Variance results *)

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


Module Examples.

(************************************************************************)
(** Two examples of derived principles:
    - the standard recursor for Nat
    - subtraction with size information
*)
Section Example.


Definition nat_ind_typ :=
   Prod (Prod (NatI infty) prop) (* P : nat -> Prop *)
  (Prod (App (Ref 0) Zero)
  (Prod (Prod (NatI infty) (Prod (App (Ref 2) (Ref 0))
                        (App (Ref 3) (App (Succ infty) (Ref 1)))))
  (Prod (NatI infty) (App (Ref 3) (Ref 0))))).

Definition nat_ind :=
   Abs (*P*)(Prod (NatI infty) prop) (* P : nat -> Prop *)
  (Abs (*fZ*) (App (Ref 0) Zero)
  (Abs (*fS*) (Prod (*n*)(NatI infty) (Prod (App (Ref 2) (Ref 0))
                                   (App (Ref 3) (App (Succ infty) (Ref 1)))))
  (NatFix infty
    (*o,Hrec*)
    (Abs (*n*)(NatI (OSucc (Ref 1)))
      (NatCase
        (Ref 4)
        (*k*)(App (App (Ref 4) (Ref 0))
                  (App (Ref 2) (Ref 0)))
        (Ref 0)))))).



Lemma nat_ind_def :
  forall e, typ e nat_ind nat_ind_typ.
unfold nat_ind, nat_ind_typ; intros.
apply typ_abs; try discriminate.
 left.
 apply typ_prod; auto.
  left.
  apply typ_NatI; trivial.

  apply typ_prop.
apply typ_abs; try discriminate.
 right.
 apply typ_subsumption with (subst Zero prop); try discriminate.
  apply typ_app with (NatI infty); try discriminate.
   apply typ_subsumption with (NatI (OSucc infty)); try discriminate.
    apply typ_0; trivial.

    apply sub_refl.
    red; simpl; intros.
    apply mkTY_ext.
     rewrite TI_mono_succ; auto with *.
     rewrite <- NAT_eqn; auto with *.

     intros.
     rewrite H1; reflexivity.

    apply typ_var0.
    split;[discriminate|].
    apply sub_refl; apply eq_term_eq_typ.
    apply eq_term_intro; simpl; auto; try reflexivity.

    apply sub_refl; apply eq_term_eq_typ.
    apply eq_term_intro; simpl; auto; try reflexivity.
(*
 left.
 split;[discriminate|].
 split;[apply kind_ok_trivial|].
 simpl. 
 destruct (H 0 _ eq_refl) as (_,?).
 simpl in H0. 
 destruct rprod_elim with (2:=H0) (x:=zero)(u:=ZE).
  red; reflexivity.

  admit.

  apply sat_sn in H2; trivial.*)
apply typ_abs; try discriminate.
 right.
 apply typ_prod; auto.
  left.
  apply typ_NatI; trivial.
 apply typ_prod; auto.
  right.
  eapply typ_subsumption with (subst (Ref 0) prop); try discriminate.
   apply typ_app with (NatI infty); try discriminate.
    apply typ_var0.
    split;[discriminate|].
    apply sub_refl; apply eq_term_eq_typ.
    split; simpl; red; intros; auto with *.

    apply typ_var0.
    split;[discriminate|].
    apply sub_refl; apply eq_term_eq_typ.
    apply eq_term_intro; simpl; auto; try reflexivity.

   apply sub_refl; apply eq_term_eq_typ.
   apply eq_term_intro; simpl; auto; try reflexivity.

  eapply typ_subsumption with (subst (App (Succ infty) (Ref 1)) prop); try discriminate.
   apply typ_app with (NatI infty); try discriminate.
    eapply typ_subsumption with (subst (Ref 1) (lift 1 (NatI (OSucc infty)))); try discriminate.
     apply typ_app with (NatI infty); try discriminate.
      apply typ_var0.
      split;[discriminate|].
      apply sub_refl; apply eq_term_eq_typ.
      apply eq_term_intro; simpl; auto; try reflexivity.

      apply typ_S; trivial.

     apply sub_refl; apply eq_term_eq_typ.
     apply eq_term_intro; intros; simpl; auto; try reflexivity.
     apply mkTY_ext; trivial.
      rewrite TI_mono_succ; auto with *.
      rewrite <- NAT_eqn; auto with *.

      intros; apply cNAT_morph; trivial.

    apply typ_var0.
    split;[discriminate|].
    apply sub_refl; apply eq_term_eq_typ.
    apply eq_term_intro; intros; simpl; auto; try reflexivity.

   apply sub_refl; apply eq_term_eq_typ.
   split; simpl; red; intros; auto with *.

set (E0 := Prod (NatI infty)
                 (Prod (App (Ref 2) (Ref 0))
                    (App (Ref 3) (App (Succ infty) (Ref 1))))
               :: App (Ref 0) Zero :: Prod (NatI infty) prop :: e) in |-*.
change E0 with (tenv (tinj E0)).
apply typ_natfix'' with (U:=App (Ref 4) (Ref 0)); auto.
 discriminate.

 (* sub *)
 apply sub_refl.
 apply eq_typ_prod.
 3:discriminate.
  reflexivity.
  apply eq_term_eq_typ.
  rewrite red_sigma_app.
  rewrite red_sigma_var_gt; auto with arith.
  rewrite red_sigma_var_lt; auto with arith.
  reflexivity.

 (* codom mono *)
 split.
  apply fx_equals_sub.
  apply fx_eq_noc.
  apply noc_app.
   apply noc_var; reflexivity.
   apply noc_var; reflexivity.

  right.
  eapply typ_subsumption with (subst (Ref 0) prop); try discriminate.
   apply typ_app with (NatI infty); try discriminate.
    apply typ_var0.
    split;[discriminate|].
    apply sub_trans with (NatI (OSucc (Ref 1))).
     apply sub_refl; apply eq_term_eq_typ.
     split; red; simpl; intros.
      apply mkTY_ext.
      apply TI_morph; auto with *.
      apply osucc_morph.
      apply H.

      intros; apply cNAT_morph; trivial.

      apply H.

     apply NatI_sub_infty.
     apply OSucc_typ.
     apply typ_ord_varS.
     apply typ_ord_var0; trivial.

    apply typ_var0.
    split;[discriminate|].
    apply sub_refl; apply eq_term_eq_typ.
    apply eq_term_intro; intros; simpl; auto; try reflexivity.

   apply sub_refl; apply eq_term_eq_typ.
   apply eq_term_intro; intros; simpl; auto; try reflexivity.

 (* fix body *)
 apply ext_abs; try discriminate.
  split.
   apply NatI_sub.
    apply OSucc_typ.
    red; simpl; intros.
    destruct (H 1 _ eq_refl).
    simpl in H1.
    destruct H1.
    red in H1; rewrite El_def in H1.
    rewrite Real_def in H2; trivial.
    2:reflexivity.
    apply sat_sn in H2; split; trivial.
    apply cc_bot_ax in H1; destruct H1.
     rewrite H1; auto.
     apply isOrd_inv with (osucc omega); auto.

    apply OSucc_subval.
     apply typ_ord_varS.
     apply typ_ord_var0; trivial.

   apply var_sub; simpl; trivial.

  left.
  apply typ_NatI; auto.
  apply OSucc_typ.
  apply typ_ord_varS.
  apply typ_ord_var0; trivial.

rewrite red_lift_app.
rewrite eq_term_lift_ref_fv; auto with arith.

rewrite red_lift_ref_bound; auto with arith.
rewrite red_sigma_app.
rewrite red_sigma_var_gt; auto with arith.
rewrite red_sigma_var_lt; auto with arith.
rewrite red_lift_app.
rewrite eq_term_lift_ref_fv; auto with arith.
rewrite red_lift_ref_bound; auto with arith.

  apply impl_NatCase with (O0:=Ref 2); auto.
   split.
    apply var_sub; simpl; trivial.
   apply typ_ord_varS.
   apply typ_ord_varS.
   apply typ_ord_var0; trivial.

   (* branch 0 *)
   eapply typ_var_impl.
    compute; reflexivity.
    simpl nth_error.
    reflexivity.
    discriminate.
    discriminate.

    apply sub_refl; red; simpl; intros.
    unfold V.lams, V.shift; simpl.
    reflexivity.
(*
  apply typ_impl_varS with (App (Ref 4) Zero).
  apply typ_impl_varS with (App (Ref 3) Zero).
  apply typ_impl_varS with (App (Ref 2) Zero).
  apply typ_impl_inj.
  apply typ_var0.
  split.
   discriminate.
   apply sub_refl.
   apply eq_term_eq_typ.
   unfold lift; rewrite red_lift_app.
   apply App_morph.
    rewrite eq_term_lift_ref_fv; auto with *.
    reflexivity.

    simpl; split; red; auto with *.

   unfold lift; rewrite red_lift_app, eq_term_lift_ref_fv; auto with arith;
     apply App_morph;[reflexivity|split;red;simpl; auto with *].
   unfold lift; rewrite red_lift_app, eq_term_lift_ref_fv; auto with arith;
     apply App_morph;[reflexivity|split;red;simpl; auto with *].
   unfold lift; rewrite red_lift_app, eq_term_lift_ref_fv; auto with arith;
     apply App_morph;[reflexivity|split;red;simpl; auto with *].*)

   (* branch S *)
   apply impl_app with (App (Ref 6) (Ref 0)) (* P n *)
     (App (Ref 7) (App (Succ (Ref 4)) (Ref 1))); (* P (S n) *)
     try discriminate.
    apply sub_refl; red; intros; simpl.
    unfold V.lams, V.shift; simpl.
    reflexivity.

    apply impl_app with (NatI infty)
     (Prod (App (Ref 7) (Ref 0)) (App (Ref 8) (App (Succ infty) (Ref 1))));
      try discriminate.
     apply sub_refl.
     unfold subst; rewrite red_sigma_prod, !red_sigma_app, !red_sigma_ref; try discriminate.
     simpl lt_eq_lt_dec; cbv beta iota; simpl Peano.pred.
     rewrite lift0.
     apply eq_typ_prod; [| |discriminate].
      apply refl.
     apply eq_typ_app; [apply refl|].
     apply trans with (App (Succ infty) (Ref 1)).
      apply eq_term_eq_typ.
      split; simpl; red; intros.
       apply app_ext; auto with *.
       apply H.

       rewrite <- (H 1); reflexivity.

     red; intros; simpl.
     assert (i 1 ∈ cc_bot (TI NATf' (i 4))).
      destruct (H 1 _ eq_refl) as (_,(?,_)).
      red in H0; simpl in H0.
      rewrite El_def in H0.
      trivial.
     (* Succ irrel: *)
     rewrite beta_eq. 2:red; intros; apply succ_morph; trivial.
     rewrite beta_eq. 2:red; intros; apply succ_morph; trivial.
      reflexivity.

      red; rewrite El_def; trivial.

      destruct (H 4 _ eq_refl) as (_,(?,_)).
      red in H1; simpl in H1; rewrite El_def in H1.
      assert (i 4 ∈ osucc omega).
       apply cc_bot_ax in H1; destruct H1; trivial.
       rewrite H1; apply ole_lts; auto.
      red; rewrite El_def.
      revert H0; apply cc_bot_mono.
      apply TI_mono; auto with *.
       apply isOrd_inv with (osucc omega); auto.
       apply olts_le; trivial.

     eapply typ_var_impl.
      compute; reflexivity.
      simpl; reflexivity.
      discriminate.
      discriminate.

      apply sub_refl.
      apply eq_term_eq_typ.
      unfold lift; rewrite !red_lift_prod, !red_lift_app, !red_lift_ref.
      simpl Ref.
      apply Prod_morph.
       split; red; simpl; auto with *.
      apply Prod_morph; auto with *.
      apply App_morph; auto with *.
      apply App_morph; auto with *.
      split; red; simpl; auto with *.

     eapply typ_var_impl.
      compute; reflexivity.
      simpl; reflexivity.
      discriminate.
      discriminate.

      apply sub_trans with (NatI (Ref 3)).
       apply sub_refl; apply eq_term_eq_typ.
       split; red; simpl; intros.
        apply mkTY_ext.
         apply TI_morph; auto with *.
         apply H.

         intros; apply cNAT_morph; trivial.

        apply H.

     apply NatI_sub_infty.
     apply typ_ord_varS.
     apply typ_ord_varS.
     apply typ_ord_varS.
     apply typ_ord_var0; trivial.

    eapply impl_call.
     compute; trivial.
     simpl; reflexivity.
     discriminate.
     discriminate.
     2:simpl; reflexivity.
     discriminate.

     apply sub_refl; apply eq_term_eq_typ.
     unfold subst; rewrite red_lift_app, red_sigma_app.
     rewrite !red_lift_ref, !red_sigma_ref; try discriminate.
     simpl lt_eq_lt_dec; cbv beta iota.
     rewrite lift0.
     reflexivity.

     eapply typ_var_impl.
      compute; reflexivity.
      simpl; reflexivity.
      discriminate.
      discriminate.

      apply sub_refl; red; intros; simpl.
      reflexivity.

   (* Scrutinee *)
   eapply typ_var_impl.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.
    discriminate.

    apply sub_refl; red; intros; simpl.
    reflexivity.
Qed.


(* Subtraction *)

Definition minus O :=
  NatFix O
    (*o,Hrec*)
    (Abs (*n*) (NatI (OSucc (Ref 1)))
    (Abs (*m*) (NatI infty)
    (NatCase
       Zero
       (*n'*)
       (NatCase
         (Ref 2)
         (*m'*)
         (App (App (Ref 4) (Ref 1)) (Ref 0))
         (Ref 1))
       (Ref 1)))).

Definition minus_typ O := Prod (NatI O) (Prod (NatI infty) (NatI (lift 2 O))).

(*

Lemma minus_def :
  forall e infty O,
  isOrd infty ->
  typ e O (Ord infty) ->
  typ e (minus O) (minus_typ O).
intros.
unfold minus, minus_typ.
change e with (tenv (tinj e)).
apply typ_nat_fix'' with infty (Prod (NatI infty) (NatI (Ref 2))); auto.
 (* sub *)
 apply sub_refl.
 apply eq_typ_prod.
  reflexivity.

  rewrite eq_subst_prod.
  apply eq_typ_prod.
   red; intros; simpl; reflexivity.

   red; intros; simpl.
   unfold lift; rewrite int_lift_rec_eq.
   rewrite V.lams0.
   unfold V.lams, V.shift; simpl; reflexivity.

 (* codom mono *)
 split;[|red; intros; simpl; exact I].
 apply fx_sub_prod.
  apply fx_eq_noc.
  red; simpl; reflexivity.

  apply NATi_sub with infty; trivial.
  simpl.
  apply typ_var0; split; [discriminate|].
  red; intros; simpl.
  unfold lift in H2; rewrite int_lift_rec_eq in H2.
  rewrite V.lams0 in H2.
  simpl in H2.
  apply le_lt_trans with (2:=H2); trivial.
  apply H0.
  red; intros.
  generalize (H1 (3+n) _ H3).
  destruct T as [(T,Tm)|]; simpl; trivial.

  apply var_sub.
  compute; reflexivity.

 (* fix body *)
 apply ext_abs; try discriminate.
  apply NATi_fx_sub with (o:=osucc infty); auto.
  apply OSucc_fx_sub; auto.
  eapply typ_var_mono.
   compute; reflexivity.
   simpl; reflexivity.
   discriminate.
  red; simpl; intros; trivial.
  apply weakening0 in H0; apply weakeningS with (A:=OSucct O) in H0.
  apply weakeningS with (A:=Prod(NatI(Ref 0))(Prod(NatIinfty)(NatI(Ref 2)))) in H0.
  apply H0 in H1.
  simpl in H1.
  unfold lift in H1; rewrite int_lift_rec_eq in H1.
  apply le_lt_trans with (3:=H1); trivial.

 rewrite eq_lift_prod.
 rewrite eq_subst_prod.
 unfold lift1; rewrite eq_lift_prod.
 apply impl_abs.
  discriminate.

  red; intros; simpl.
  reflexivity.

  red; intros; simpl; auto with *.

 match goal with |- typ_impl ?e _ _ => set (E:=e) end.
 assert (typ_impl E (Ref 1) (NatI (OSucc (Ref 3)))).
  eapply typ_var_impl.
   compute; reflexivity.
   simpl; reflexivity.
   discriminate.
  apply sub_refl.
  red; intros; simpl; reflexivity.
 apply impl_natcase with infty (Ref 3)
    (Abs (NatI (OSucc (Ref 3))) (NatI (OSucc (Ref 4)))); auto.
  Focus 2.
  apply sub_refl.
  rewrite eq_typ_betar.
  3:discriminate.
   red; intros; simpl.
   unfold V.lams, V.shift; simpl.
   reflexivity.

   apply H1.

  (* ord *)
  eapply typ_var_mono.
   compute;reflexivity.
   simpl; reflexivity.
   discriminate.
  red; intros; simpl.
  unfold lift in H3; rewrite int_lift_rec_eq in H3.
  rewrite V.lams0 in H3.
  simpl in H3.
  apply le_lt_trans with (2:=H3); trivial.
  apply H0.
  red; intros.
  generalize (H2 (4+n) _ H4).
  destruct T as [(T,Tm)|]; simpl; auto.

  (* branch 0 *)
  split.
   red; intros; simpl; reflexivity.
  assert (tyz : typ (tenv E) Zero (NatI (OSucc (Ref 3)))).
    apply typ_Zero with infty; trivial.
    apply typ_var0; split; [discriminate|].
    red; intros; simpl.
    unfold lift in H3; rewrite int_lift_rec_eq in H3.
    rewrite V.lams0 in H3.
    simpl in H3.
    apply le_lt_trans with (2:=H3); trivial.
    apply H0.
    red; intros.
    generalize (H2 (4+n) _ H4).
    destruct T as [(T,Tm)|]; simpl; trivial.
  apply typ_conv with (NatI (OSucc (Ref 3))); trivial.
  2:discriminate.
  rewrite eq_typ_betar; trivial.
  2:discriminate.
  red; intros; simpl.
  reflexivity.

  (* branch S *)
  assert (typ_impl (push_var E (NatI (Ref 3))) (Ref 1) (NatI (Ord (osucc omega)))).
   eapply typ_var_impl.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.
   apply sub_refl.
   red; intros; simpl.
   unfold NATi at 2; rewrite TI_mono_succ; auto.
   apply NAT_eq.
  apply impl_natcase with (osucc omega) infty
     (Abs (NatI (OSucct infty)) (NatI (OSucc (Ref 5)))); auto.
   Focus 2.
   apply sub_refl.
   rewrite eq_typ_betar.
   3:discriminate.
    unfold lift; rewrite eq_lift_abs.
    rewrite eq_typ_betar.
    3:discriminate.
     red; intros; simpl; reflexivity.
     apply typ_conv with (NatI (OSucc (lift_rec 1 0 (Ref 3)))).
     3:discriminate.
      apply typ_SuccI with (o:=infty); trivial.
      apply typ_var0; split;[discriminate|].
      red; intros; simpl.
      unfold lift in H4; rewrite int_lift_rec_eq in H4.
      rewrite V.lams0 in H4.
      simpl in H4.
      apply le_lt_trans with (2:=H4); trivial.
      apply H0.
      red; intros.
      generalize (H3 (5+n) _ H5).
      destruct T as [(T,Tm)|]; simpl; trivial.

      apply typ_var0; split;[discriminate|].
      apply sub_refl; red; intros; simpl.
      reflexivity.

     red; intros; simpl.
     reflexivity.

     apply H2.

   (* ord *)
   split.
    red; intros; simpl; reflexivity.

    red; intros; simpl.
    apply lt_osucc; trivial.

  (* branch 0 *)
  eapply typ_var_impl.
   compute; reflexivity.
   simpl; reflexivity.
   discriminate.
  apply sub_refl.
  rewrite eq_typ_betar.
  3:discriminate.
   red; intros; simpl.
   unfold V.lams, V.shift; simpl; reflexivity.

   eapply typ_Zero with (osucc omega); auto.
   red; intros; simpl.
   apply lt_osucc; trivial.

  (* branch S *)    
  apply impl_app with (NatI infty) (NatI (OSucc (Ref 6))).
   discriminate.
   discriminate.

   unfold lift; rewrite eq_lift_abs.
   apply sub_refl.
   rewrite eq_typ_betar.
   3:discriminate.
    red; intros; simpl.
    unfold V.lams, V.shift; simpl.
    reflexivity.

    apply typ_conv with (NatI (OSucc (lift_rec 1 0 infty))).
    3:discriminate.
     apply typ_SuccI with (o:=osucc omega); auto.
      red; intros; simpl.
      apply lt_osucc; trivial.

      apply typ_var0; split;[discriminate|].
      apply sub_refl; red; intros; simpl.
      reflexivity.

     red; intros; simpl.
     reflexivity.

   eapply impl_call.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.
    2:simpl; reflexivity.
    discriminate.

    unfold subst, lift1; rewrite eq_lift_prod.
    rewrite eq_subst_prod.
    apply sub_typ_covariant.
     red; intros; simpl; reflexivity.

     red; intros; simpl.
     rewrite int_subst_rec_eq in H4.
     simpl in H4; unfold V.lams, V.shift in H4; simpl in H4.
     assert (isOrd (i 6)).
      generalize (H3 6 _ (reflexivity _)).
      simpl; intro.
      rewrite V.lams0 in H5.
      apply isOrd_inv with (2:=H5).      
      apply isOrd_succ.
      assert (val_ok e (V.shift 7 i)).
       red; intros.
       generalize (H3 (7+n) _ H6).
       destruct T as [(T,Tm)|]; simpl; auto.
      apply H0 in H6.
      simpl in H6.
      apply isOrd_inv with infty; trivial.
     revert H4; apply TI_incl; auto.

    eapply typ_var_impl.
     compute; reflexivity.
     simpl; reflexivity.
     discriminate.

     apply sub_refl.
     red; intros; simpl.
     reflexivity.

     eapply typ_var_impl.
      compute; reflexivity.
      simpl; reflexivity.
      discriminate.

      apply sub_refl.
      red; intros; simpl.
      reflexivity.
Qed.

End Example.

Print Assumptions minus_def.
*)

(* "Map" is size-preserving *)

Definition map O :=
  NatFix O
    (*o,Hrec*)
    (Abs (*n*) (NatI (OSucc (Ref 1)))
    (NatCase
       Zero
       (*n'*)
       (App(Succ (Ref 3)) (App (Ref 2) (Ref 0))) (* S(Hrec n') *)
       (Ref 0))).

Definition map_typ O := Prod (NatI O) (NatI (lift 1 O)).

Lemma map_def e O :
  O <> kind ->
  typ_ord e O ->
  typ e (map O) (map_typ O).
unfold map, map_typ; intros Onk tyO.
change e with (tenv (tinj e)).
apply typ_natfix'' with (U:=NatI (Ref 1)); auto.
 discriminate.

 (* sub *)
 apply sub_refl; apply eq_term_eq_typ.
 apply Prod_morph;[reflexivity|].
 rewrite eq_sb_NatI.
 apply NatI_morph; rewrite red_sigma_ref; trivial.
 reflexivity.

 (* codom mono *)
 split.
  apply NatI_sub.
   apply typ_ord_varS.
   apply typ_ord_var0_ord; trivial.

   apply var_sub; reflexivity.

  left.
  apply typ_NatI.   
  apply typ_ord_varS.
  apply typ_ord_var0_ord; trivial.

 (* fix body *)
 apply ext_abs; try discriminate.
  split.
   apply NatI_sub.
    apply OSucc_typ.
    apply typ_ord_varS.
    apply typ_ord_var0_ord; trivial.

    apply OSucc_subval.
     apply typ_ord_varS.
     apply typ_ord_var0_ord; trivial.

     apply var_sub; reflexivity.

   left.
   apply typ_NatI.   
   apply OSucc_typ.
   apply typ_ord_varS.
   apply typ_ord_var0_ord; trivial.

 apply typ_impl_subsumption with (subst (Ref 0) (NatI(OSucc(Ref 3)))).
 3:discriminate.
 3:discriminate.
  apply impl_NatCase' with (O0:=Ref 2).
   discriminate.

  (* ord mono *)
  split.
   apply var_sub; simpl; trivial.

   apply typ_ord_varS.
   apply typ_ord_varS.
   apply typ_ord_var0_ord; trivial.
 
  (* branch 0 *)
  split.
   apply fx_eq_noc.
   red; simpl; reflexivity.

   apply typ_subsumption with (NatI (OSucc (Ref 2))).
   3:discriminate.
   3:discriminate.
    apply typ_0.
    apply typ_ord_varS.
    apply typ_ord_varS.
    apply typ_ord_var0_ord; trivial.

    apply sub_refl; apply eq_term_eq_typ.
    unfold subst; rewrite eq_sb_NatI; apply NatI_morph.
    apply eq_term_intro; simpl; trivial.    
    reflexivity.

  (* branch S *)
  split.
  apply fx_eq_app_irr with (NatI (Ref 3)).
    discriminate.
   apply ext_S.
    apply typ_ord_varS.
    apply typ_ord_varS.
    apply typ_ord_varS.
    apply typ_ord_var0_ord; trivial.
   apply var_sub; reflexivity.

   apply fx_eq_rec_call with (NatI (Ref 0)) (NatI (Ref 4)); trivial.
    discriminate.

    apply typ_var0; split;[discriminate|].
    apply sub_refl; apply eq_term_eq_typ.
    unfold lift; rewrite red_lift_prod.
    apply Prod_morph.
     apply eq_term_intro; trivial; reflexivity.
     apply eq_term_intro; trivial; reflexivity.
   
    apply fx_eq_noc; apply noc_var; auto.
   
    apply typ_var0; split;[discriminate|].
    apply sub_refl; apply eq_term_eq_typ.
    apply eq_term_intro; trivial; reflexivity.

    eapply typ_subsumption.
     eapply typ_app.
      apply typ_var; reflexivity.
    apply typ_var0; split;[discriminate|].
    apply sub_refl; apply eq_term_eq_typ.
    unfold lift; rewrite red_lift_prod.
    apply Prod_morph;[|reflexivity].
    apply eq_term_intro; trivial; reflexivity.
     discriminate.
     discriminate.
     2:discriminate.
     2:discriminate.

    apply sub_refl; apply eq_term_eq_typ.
    apply eq_term_intro; trivial; reflexivity.

  eapply typ_subsumption.
   eapply typ_app.
   2:apply typ_S.  
3:discriminate.
3:discriminate.
4:discriminate.
4:discriminate.
    2:apply typ_ord_varS.
    2:apply typ_ord_varS.
    2:apply typ_ord_varS.
    2:apply typ_ord_var0_ord; trivial.

  eapply typ_subsumption.
   eapply typ_app.
    eapply typ_var;reflexivity.
2:discriminate.
5:discriminate.
apply typ_var0.
split.
 discriminate.
  apply sub_refl; apply eq_term_eq_typ.
   unfold lift; rewrite red_lift_prod.
   apply Prod_morph;[|reflexivity].
2:discriminate.
3:discriminate.   
  apply eq_term_intro; trivial; reflexivity.

  apply sub_refl; apply eq_term_eq_typ.
  apply eq_term_intro; trivial; reflexivity.

  apply sub_refl; apply eq_term_eq_typ.
  apply eq_term_intro; trivial; reflexivity.
  
  (* scrutinee *)
  eapply typ_var_impl. 2:reflexivity.
  2:discriminate.
  2:discriminate.
  reflexivity.

  apply sub_refl; apply eq_term_eq_typ.
  apply eq_term_intro; simpl; auto.
  reflexivity.

 (* sub case pred *)
 apply sub_refl; apply eq_term_eq_typ.
 apply eq_term_intro; trivial; reflexivity.
Qed.

End Example.
End Examples.

End Make.

(** Create an instance of SizedNats based on ZFind_natbot *)
Module NATM <: PartialNats.

Require Import ZFind_natbot.

Definition NATf' := NATf'.
Definition NATf'_mono := NATf'_mono.
Existing Instance NATf'_mono.

  (** N is the type of natural numbers including neutral values.
      Nbot is a decidable subet of N. *)
(*  Parameter N Nbot : set.
  Parameter N_Nbot : N ⊆ Nbot.
  Parameter Ndec : forall n, n ∈ Nbot -> n∈N \/ ~n∈N.*)

Definition zero := ZERO.
Definition succ := SUCC.
Definition succ_morph : morph1 succ := inr_morph.
Existing Instance succ_morph.

  (** Constructors produce non-neutral values *)
Lemma zero_nmt : ~ zero == empty.
apply couple_mt_discr.
Qed.
Lemma succ_nmt n : ~ succ n == empty.
apply couple_mt_discr.
Qed.

Lemma zero_typ : forall X, zero ∈ NATf' X.
intros.
apply ZERO_typ_gen.
Qed.
Lemma succ_typ : forall X n, n ∈ cc_bot X -> succ n ∈ NATf' X.
intros.
apply SUCC_typ_gen; trivial.
Qed.

Definition isNat X n := n==zero \/ exists2 m, m ∈ cc_bot X & n == succ m.
Lemma NATf'_elim X n : n ∈ NATf' X -> isNat X n.
red.
intros.
apply sum_ind with (3:=H); [left|right]; eauto.
apply ZFind_basic.unit_elim in H0.
rewrite H0 in H1; trivial.
Qed.

Definition NAT' := TI NATf' omega.
Lemma NAT_eqn : TI NATf' omega == NATf' (TI NATf' omega).
Proof NAT'_eq.

  (** Case-analysis *)
Definition natcase : set -> (set -> set) -> set -> set := NATCASE.
Instance natcase_morph : Proper (eq_set==>(eq_set==>eq_set)==>eq_set==>eq_set) natcase.
Proof NATCASE_morph.

Lemma natcase_zero : forall b0 bS,
  natcase b0 bS zero == b0.
apply NATCASE_ZERO.
Qed.

Lemma natcase_succ : forall n b0 bS,
  morph1 bS ->
  natcase b0 bS (succ n) == bS n.
intros.
apply NATCASE_SUCC.
intros.
apply H; trivial.
Qed.

Lemma natcase_outside : forall b0 bS n,
  n == empty ->
  natcase b0 bS n == empty.
intros.
unfold natcase, NATCASE.
apply empty_ext; red; intros.
rewrite union2_ax in H0; do 2 rewrite cond_set_ax in H0.
destruct H0 as [(_,?)|(_,(k,?))].
 (* ~ empty == ZERO *)
 rewrite H0 in H; apply zero_nmt in H; trivial.

 (* ~ empty == SUCC _ *)
 rewrite H0 in H; apply succ_nmt in H; trivial.
Qed.

  (** Fixpoint *)

Definition natfix : (set -> set -> set) -> set -> set := REC' (singl empty).

Lemma natfix_morph : Proper ((eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) natfix.
apply REC'_morph; reflexivity.
Qed.

Lemma natfix_rec: forall o M U,
    typed_bot_recursor_hyps (singl empty) (TI NATf') U M o ->
    typed_bot_recursor_spec (singl empty) (TI NATf') U M (natfix M) o.
intros; apply REC'_typed_bot_recursor_spec; auto with *.
Qed.

(** Universes *)
Lemma G_NATf' : forall U X, grot_univ U -> X ∈ U -> NATf' X ∈ U.
intros; apply G_NATf'; trivial.
Qed.
  
End NATM.

(** The final instantiation *)

Module NAT_SN := Make NATM.
Export NAT_SN.

Definition test := (
  typ_NatCase,
  typ_natfix,
  natfix_extend,
  natfix_eq_S,
  Examples.nat_ind_def,
  Examples.map_def
).

Print Assumptions test.
