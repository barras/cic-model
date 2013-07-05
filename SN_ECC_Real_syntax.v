Require Lambda.
Require Import ZF ZFuniv_real Sat SN_ECC_Real.
Import SN SN_CC_Model.

(** * Mapping from syntactic entities to their semantic counterparts. *)

(** syntax of ECC *)
Require TypeJudgeECC.
Module Ty := TypeJudgeECC.
Module Tm := TermECC.
Module Lc := Lambda.


(** Terms *)
Fixpoint int_trm t :=
  match t with
  | Tm.Srt Tm.prop => prop
  | Tm.Srt (Tm.kind n) => type n
  | Tm.Ref n => Ref n
  | Tm.App u v => App (int_trm u) (int_trm v)
  | Tm.Abs T M => Abs (int_trm T) (int_trm M)
  | Tm.Prod T U => Prod (int_trm T) (int_trm U)
  end.
Definition interp t := int_trm t.
Definition int_env := List.map interp.

Lemma interp_nk : forall T, interp T <> kind.
induction T; simpl; intros; try discriminate.
destruct s; discriminate.
Qed.
Hint Resolve interp_nk.

Section LiftAndSubstEquiv.
(* Proof that lift and subst at both levels (SN and Tm) are equivalent. *)

Lemma int_lift_rec : forall n t k,
  eq_trm (lift_rec n k (int_trm t)) (int_trm (Tm.lift_rec n t k)).
induction t; simpl int_trm; intros.
 destruct s; simpl; trivial.
 split; red; intros; reflexivity.

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
  eq_trm (int_trm (Tm.lift n t)) (lift n (int_trm t)).
intros.
symmetry.
unfold Tm.lift, lift.
apply int_lift_rec.
Qed.

Lemma int_subst_rec : forall arg,
  int_trm arg <> kind ->
  forall t k,
  eq_trm (subst_rec (int_trm arg) k (int_trm t)) (int_trm (Tm.subst_rec arg t k)).
intros arg not_knd.
induction t; simpl int_trm; intros.
 destruct s; simpl; trivial.
 split; red; intros; reflexivity.

 split; red; intros; reflexivity.

 simpl Tm.subst_rec.
 destruct (lt_eq_lt_dec k n) as [[fv|eqv]|bv]; simpl int_trm.
  simpl int_trm.
  destruct n; [inversion fv|].
  rewrite red_sigma_var_gt; auto with arith.
  reflexivity.

  subst k; rewrite red_sigma_var_eq; trivial.
  symmetry; apply int_lift.

  rewrite red_sigma_var_lt; trivial.
  reflexivity.

 rewrite red_sigma_abs.
 rewrite IHt1; rewrite IHt2; reflexivity.

 rewrite red_sigma_app.
 rewrite IHt1; rewrite IHt2; reflexivity.

 rewrite red_sigma_prod.
 rewrite IHt1; rewrite IHt2; reflexivity.
Qed.


Lemma int_subst : forall u t,
  int_trm u <> kind ->
  eq_trm (int_trm (Tm.subst u t)) (subst (int_trm u) (int_trm t)).
unfold Tm.subst; symmetry; apply int_subst_rec; trivial.
Qed.

End LiftAndSubstEquiv.
(* Proof that beta-reduction at the Lc level simulates beta-reduction
   at the Tm level. One beta at the Tm level may require several
   (but not zero) steps at the Lc level, because of the encoding
   of type-carrying lambda abstractions.
 *)
Lemma red1_sound : forall x y,
  Tm.red1 x y ->
  red_term (int_trm x) (int_trm y).
induction 1; simpl; intros.
 rewrite int_subst.
  apply red_term_beta.

  destruct N; try discriminate.
  destruct s; try discriminate.

 apply red_term_abs_l; auto 10.
 apply red_term_abs_r; auto 10.
 apply red_term_app_l; auto 10.
 apply red_term_app_r; auto 10.
 apply red_term_prod_l; auto 10.
 apply red_term_prod_r; auto 10.
Qed.

Lemma sn_sound : forall M,
  Acc (transp _ red_term) (interp M) ->
  Tm.sn M.
intros M accM.
apply Acc_inverse_image with (f:=int_trm) in accM.
induction accM; intros.
constructor; intros.
apply H0; trivial.
 apply red1_sound; trivial.
Qed.


(** Soundness of the typing rules *)

Lemma typ_sort_type_ok e T s : 
  T <> kind ->
  typ e T (interp (TermECC.Srt s)) ->
  type_ok e T.
split; trivial.
intros; apply and_split; intros.
 apply H0 in H1.
 apply in_int_sn in H1; trivial.

 exists empty; split.
  red; auto.
  apply varSAT.
Qed.

Lemma int_sound : forall e M M' T,
  Ty.eq_typ e M M' T ->
  typ (int_env e) (interp M) (interp T) /\
  eq_typ (int_env e) (interp M) (interp M').
induction 1; simpl; intros.
 (* Srt *)
 split.
  apply typ_prop_type0.
  apply refl.
 split.
  apply typ_type_type.
  apply refl.
 (* Ref *)
 split.
  destruct H0.
  subst t.
  unfold Tm.lift, interp.
  fold (Tm.lift (S v) x); rewrite int_lift.
  simpl.
  apply typ_var.
  elim H1; simpl; auto.

  apply refl.
 (* Abs *)
 destruct IHeq_typ1.
 clear IHeq_typ2.
 destruct IHeq_typ3.
 unfold interp; simpl; fold (interp T) (interp M) (interp U).
 split.
  apply typ_abs_ok; eauto.
  apply typ_sort_type_ok in H3; auto.

  apply eq_typ_abs; eauto.
 (* App *)
 destruct IHeq_typ1.
 destruct IHeq_typ3.
 clear IHeq_typ2 IHeq_typ4.
 unfold interp; simpl; fold (interp u) (interp v) (interp Ur).
 split.
  rewrite int_subst; fold (interp v); eauto.
  fold (interp Ur).
  apply typ_app with (interp V); eauto.

  apply eq_typ_app; trivial.
 (* Prod *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 unfold interp; simpl; fold (interp T) (interp U) (interp T') (interp U').
 split.
  destruct s2; simpl in H1.
   (* predicative case *)
   destruct s1.
    destruct s3; try discriminate.
    destruct (eq_nat_dec (max n n0) n1); try discriminate.
    subst n1.
    apply typ_predicative_prod.
     apply typ_type_cumul_le with n0; auto with *.
     apply typ_type_cumul_le with n; auto with *.

    destruct s3; try discriminate.
    destruct (eq_nat_dec n n0); try discriminate.
    subst n0.
    apply typ_predicative_prod; trivial.
    apply typ_type_cumul_le with 0; auto with *.
    apply typ_prop_cumul; trivial.

   (* impredicative case *)
   destruct s3; try discriminate.
   apply typ_prod_prop; auto.
   apply typ_sort_type_ok in H2; auto.

  apply eq_typ_prod; eauto.
 (* Beta *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 destruct IHeq_typ3.
 clear IHeq_typ4.
 unfold interp; simpl; fold (interp T) (interp M) (interp U) (interp N).
 split.
  rewrite int_subst; fold (interp N); eauto.
  fold (interp U).
  apply typ_beta_ok; auto.
  apply typ_sort_type_ok in H6; auto.

  rewrite int_subst; fold (interp N').
  2:assert (h := Ty.typ_refl2 _ _ _ _ H); eauto.
  apply eq_typ_beta; eauto.
 (* Red *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 split; trivial.
 apply typ_conv with (interp T); eauto.
 (* Exp *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 split; trivial.
 apply typ_conv with (int_trm T'); eauto.
 apply sym; trivial.
Qed.

  Lemma interp_wf : forall e, Ty.wf e -> wf (int_env e).
induction e; simpl; intros.
 apply wf_nil.

 inversion_clear H.
 assert (wfe := Ty.typ_wf _ _ _ _ H0).
 apply int_sound in H0.
 destruct H0 as (H0,_).
 apply wf_cons_ok; auto.
 apply typ_sort_type_ok in H0; auto.
Qed.

Lemma interp_sound : forall e M M' T,
  Ty.eq_typ e M M' T ->
  wf (int_env e) /\ typ (int_env e) (interp M) (interp T).
intros.
assert (wfe := Ty.typ_wf _ _ _ _ H).
apply interp_wf in wfe.
apply int_sound in H; destruct H; auto.
Qed.

(***********)
(*
----
*)

(** The main theorem: strong normalization of CC *)

Lemma strong_normalization : forall e M M' T,
  Ty.eq_typ e M M' T ->
  Tm.sn M.
Proof.
intros.
apply interp_sound in H.
destruct H as (wfe,ty).
apply model_strong_normalization in ty; trivial.
apply sn_sound; trivial.
Qed.

(* Print the assumptions made to derive strong normalization of ECC:
   the axioms of ZF, and the existence of Grothendieck universes.
   In fact we don't need full replacement, only the functional version,
   so we have the SN theorem with only the axiom about Grothendieck universes.
 *)
Print Assumptions strong_normalization.
