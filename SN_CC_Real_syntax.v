
(** The semantic construction *)

Require Import basic SN_CC_Real.
Import ZFuniv_real CC_Real.

(***********************************************************************************************)
(** * Strong Normalization on actual syntax *)

Require TypeJudge.

Module Ty := TypeJudge.
Module Tm := Term.

Fixpoint int_term t :=
  match t with
  | Tm.Srt Tm.prop => SN.T.prop
  | Tm.Srt Tm.kind => SN.T.kind
  | Tm.Ref n => SN.T.Ref n
  | Tm.App u v => SN.T.App (int_term u) (int_term v)
  | Tm.Abs T M => SN.T.Abs (int_term T) (int_term M)
  | Tm.Prod T U => SN.T.Prod (int_term T) (int_term U)
  end.
Definition interp t := int_term (Ty.unmark_app t).
Definition int_env := List.map interp.

Section LiftAndSubstEquiv.
(* Proof that lift and subst at both levels (SN and Tm) are equivalent. *)

Lemma int_lift_rec : forall n t k,
  eq_term (lift_rec n k (int_term t)) (int_term (Tm.lift_rec n t k)).
induction t; simpl int_term; intros.
 destruct s; simpl; trivial.
 split; red; intros; reflexivity.

 simpl; unfold V.lams, I.lams, V.shift, I.shift.
 destruct (le_gt_dec k n0); simpl.
  replace (k+(n+(n0-k))) with (n+n0) by omega.
  split; red; auto.

  split; red; auto.

 rewrite red_lift_abs; rewrite IHt1; rewrite IHt2; reflexivity.
 rewrite red_lift_app; rewrite IHt1; rewrite IHt2; reflexivity.
 rewrite red_lift_prod; rewrite IHt1; rewrite IHt2; reflexivity.
Qed.

Lemma int_lift : forall n t,
  eq_term (int_term (Tm.lift n t)) (lift n (int_term t)).
intros.
symmetry.
unfold Tm.lift, lift.
apply int_lift_rec.
Qed.


Lemma int_subst_rec : forall arg,
  int_term arg <> kind ->
  forall t k,
  eq_term (subst_rec (int_term arg) k (int_term t)) (int_term (Tm.subst_rec arg t k)).
intros arg not_knd.
induction t; simpl int_term; intros.
 destruct s; simpl; trivial.
 split; red; intros; reflexivity.

 simpl Tm.subst_rec.
 destruct (lt_eq_lt_dec k n) as [[fv|eqv]|bv]; simpl int_term.
  simpl int_term.
  destruct n; [inversion fv|].
  rewrite SN.T.red_sigma_var_gt; auto with arith.
  reflexivity.

  subst k; rewrite SN.T.red_sigma_var_eq; trivial.
  symmetry; apply int_lift.

  rewrite SN.T.red_sigma_var_lt; trivial.
  reflexivity.

 rewrite SN.T.red_sigma_abs.
 rewrite IHt1; rewrite IHt2; reflexivity.

 rewrite SN.T.red_sigma_app.
 rewrite IHt1; rewrite IHt2; reflexivity.

 rewrite SN.T.red_sigma_prod.
 rewrite IHt1; rewrite IHt2; reflexivity.
Qed.


Lemma int_subst : forall u t,
  int_term u <> kind ->
  eq_term (int_term (Tm.subst u t)) (subst (int_term u) (int_term t)).
unfold Tm.subst; symmetry; apply int_subst_rec; trivial.
Qed.

Lemma int_not_kind : forall T, T <> Tm.Srt Tm.kind -> interp T <> kind.
red; intros.
apply H.
destruct T; try discriminate.
destruct s; trivial; discriminate.
destruct T1; discriminate.
Qed.

End LiftAndSubstEquiv.

Hint Resolve int_not_kind Ty.eq_typ_not_kind.

(** Proof that beta-reduction at the Lc level simulates beta-reduction
   at the Tm level. One beta at the Tm level may require several
   (but not zero) steps at the Lc level, because of the encoding
   of type-carrying lambda abstractions.
 *)
Lemma red1_sound : forall x y,
  Tm.red1 x y -> ~ Tm.mem_sort Tm.kind x ->
  SN.T.red_term (int_term x) (int_term y).
induction 1; simpl; intros.
 rewrite int_subst.
  apply SN.T.red_term_beta.

  destruct N; try discriminate.
  destruct s; try discriminate.
  elim H; auto.

 apply SN.T.red_term_abs_l; auto 10.
 apply SN.T.red_term_abs_r; auto 10.
 apply SN.T.red_term_app_l; auto 10.
 apply SN.T.red_term_app_r; auto 10.
 apply SN.T.red_term_prod_l; auto 10.
 apply SN.T.red_term_prod_r; auto 10.
Qed.

Import Wellfounded.

Lemma sn_sound : forall M,
  Acc (transp _ red_term) (interp M) ->
  ~ Tm.mem_sort Tm.kind (Ty.unmark_app M) ->
  Tm.sn (Ty.unmark_app M).
intros M accM.
apply Acc_inverse_image with (f:=int_term) in accM.
induction accM; intros.
constructor; intros.
apply H0; trivial.
 apply red1_sound; trivial.

 intro; apply H1; apply Tm.exp_sort_mem with (1:=H2); trivial.
Qed.

(** Soundness of the typing rules *)

Lemma int_sound : forall e M M' T,
  Ty.eq_typ e M M' T ->
  SN.J.typ (int_env e) (interp M) (interp T) /\
  SN.J.eq_typ (int_env e) (interp M) (interp M').
induction 1; simpl; intros.
 (* Srt *)
 split.
  apply SN.R.typ_prop.
  apply SN.R.refl.
 (* Ref *)
 split.
  destruct H0.
  subst t.
  unfold Tm.lift, interp; rewrite Ty.unmark_lift.
  fold (Tm.lift (S v) (Ty.unmark_app x)); rewrite int_lift.
  simpl.
  apply SN.R.typ_var.
  elim H1; simpl; auto.

  apply SN.R.refl.
 (* Abs *)
 destruct IHeq_typ1.
 clear IHeq_typ2.
 destruct IHeq_typ3.
 unfold interp; simpl; fold (interp T) (interp M) (interp U).
 split.
  apply SN.R.typ_abs; eauto.
  destruct s1; red; auto.

  apply SN.R.eq_typ_abs; eauto.
 (* App *)
 destruct IHeq_typ1.
 destruct IHeq_typ3.
 clear IHeq_typ2 IHeq_typ4.
 unfold interp; simpl; fold (interp u) (interp v) (interp Ur).
 split.
  rewrite Ty.unmark_subst0 with (1:=H2).
  rewrite int_subst; fold (interp v); eauto.
  fold (interp Ur).
  apply SN.R.typ_app with (interp V); eauto.

  apply SN.R.eq_typ_app; trivial.
 (* Prod *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 unfold interp; simpl; fold (interp T) (interp U) (interp T') (interp U').
 split.
  apply SN.R.typ_prod; trivial.
   destruct s2; auto.

   destruct s1; red; auto.

  apply SN.R.eq_typ_prod; eauto.
 (* Beta *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 destruct IHeq_typ3.
 clear IHeq_typ4.
 unfold interp; simpl; fold (interp T) (interp M) (interp U) (interp N).
 split.
  rewrite Ty.unmark_subst0 with (1:=H2).
  rewrite int_subst; fold (interp N); eauto.
  fold (interp U).
  apply SN.R.typ_app with (V:=interp T); eauto.
  apply SN.R.typ_abs; eauto.
  destruct s1; red; auto.

  rewrite Ty.unmark_subst0 with (1:=Ty.typ_refl2 _ _ _ _ H1).
  rewrite int_subst; fold (interp N').
  2:assert (h := Ty.typ_refl2 _ _ _ _ H); eauto.
  apply SN.R.eq_typ_beta; eauto.
 (* Red *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 split; trivial.
 apply SN.R.typ_conv with (interp T); eauto.
 apply Ty.typ_refl2 in H0; eauto.
 (* Exp *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 split; trivial.
 apply SN.R.typ_conv with (int_term (Ty.unmark_app T')); eauto.
  apply SN.R.sym; trivial.

  fold (interp T').
  apply Ty.typ_refl2 in H0; eauto.
Qed.

  Lemma interp_wf : forall e, Ty.wf e -> SN.J.wf (int_env e).
induction e; simpl; intros.
 apply SN.R.wf_nil.

 inversion_clear H.
 assert (wfe := Ty.typ_wf _ _ _ _ H0).
 apply int_sound in H0.
 destruct H0 as (H0,_).
 apply SN.R.wf_cons; auto.
 destruct s; [left|right]; assumption.
Qed.

Lemma interp_sound : forall e M M' T,
  Ty.eq_typ e M M' T ->
  SN.J.wf (int_env e) /\ SN.J.typ (int_env e) (interp M) (interp T).
intros.
assert (wfe := Ty.typ_wf _ _ _ _ H).
apply interp_wf in wfe.
apply int_sound in H; destruct H; auto.
Qed.

(** The main theorem: strong normalization *)
Theorem strong_normalization : forall e M M' T,
  Ty.eq_typ e M M' T ->
  Tm.sn (Ty.unmark_app M).
Proof.
intros.
assert (~ Tm.mem_sort Tm.kind (Ty.unmark_app M)).
 apply Ty.eq_typ_typ in H.
 red; intro Hm; apply (Types.typ_mem_kind _ _ _ Hm H).
apply interp_sound in H; destruct H as (wfe,ty).
apply SN.model_strong_normalization in ty; trivial.
apply sn_sound; trivial.
Qed.

(** Print the assumptions made to derive strong normalization of CC:
   the axioms of ZF. (In fact we don't need full replacement, only the
   functional version, so we should be able to have the SN theorem without
   assumption.)
 *)
Print Assumptions strong_normalization.
