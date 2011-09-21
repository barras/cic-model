Require Import List.
Require Import Models.
Require Import TypeJudge.
Require GenModel.

(* Finally introducing the syntax... *)

Module MakeModel (M : CC_Model).

Include GenModel.MakeModel M.
Import T.
Import Term.

Fixpoint int_trm t :=
  match t with
  | Srt prop => T.prop
  | Srt kind => T.kind
  | Ref n => T.Ref n
  | App u v => T.App (int_trm u) (int_trm v)
  | Abs T M => T.Abs (int_trm T) (int_trm M)
  | Prod T U => T.Prod (int_trm T) (int_trm U)
  end.

Definition int_env := List.map int_trm.

Lemma int_lift_rec : forall n t k,
  eq_term (T.lift_rec n k (int_trm t)) (int_trm (Term.lift_rec n t k)).
induction t; intros.
 destruct s; simpl; trivial.
 red; intros; reflexivity.

 simpl; unfold V.lams, V.shift.
 destruct (le_gt_dec k n0); simpl.
  replace (k+(n+(n0-k))) with (n+n0) by omega.
  red; auto.

  red; auto.

 simpl; red; intros.
 apply M.lam_ext; intros.
  rewrite H; rewrite <- IHt1.
  rewrite int_lift_rec_eq.
  reflexivity.

  red; intros.
  rewrite H; rewrite <- IHt2.
  rewrite int_lift_rec_eq.
  rewrite V.cons_lams; eauto with *.
  rewrite H1; reflexivity.

 simpl; red; intros.
 do 2 rewrite <- int_lift_rec_eq.
 rewrite H; rewrite IHt1; rewrite IHt2; reflexivity.

 simpl; red; intros.
 apply M.prod_ext; intros.
  rewrite H; rewrite <- IHt1.
  rewrite int_lift_rec_eq.
  reflexivity.

  red; intros.
  rewrite H; rewrite <- IHt2.
  rewrite int_lift_rec_eq.
  rewrite V.cons_lams; eauto with *.
  rewrite H1; reflexivity.
Qed.


Lemma int_lift : forall n t,
  eq_term (int_trm (lift n t)) (T.lift n (int_trm t)).
intros.
unfold lift, T.lift.
symmetry; apply int_lift_rec.
Qed.


Lemma int_subst_rec : forall arg,
  int_trm arg <> T.kind ->
  forall t k,
  eq_term (T.subst_rec (int_trm arg) k (int_trm t)) (int_trm (subst_rec arg t k)).
intros arg not_knd.
induction t; intros.
 destruct s; simpl; trivial.
 red; intros; reflexivity.

 simpl subst_rec.
 destruct (lt_eq_lt_dec k n) as [[fv|eqv]|bv]; simpl.
  simpl; unfold V.lams, V.shift;
   destruct (le_gt_dec k n); try (apply False_ind; omega; fail).
  replace (n-k) with (S(pred n-k)) by omega; simpl.
  replace (k+(pred n-k)) with (pred n) by omega; red; auto.

  case_eq (int_trm (lift k arg)); [intros (a,am) arg_eq;simpl|intro arg_eq].
   red; intros.
   subst k.
   unfold V.lams; simpl.
   destruct (le_gt_dec n n).
   2:apply False_ind; omega.
   replace (n-n) with 0; auto with arith; simpl.
   setoid_replace (V.shift n x) with (V.lams 0 (V.shift n) x).
   2:symmetry; apply V.lams0.
   rewrite <- int_lift_rec_eq.
   fold (T.lift n (int_trm arg)).
   rewrite <- int_lift.
   rewrite arg_eq; simpl.
   apply am.
   exact H.

   destruct arg; simpl; try discriminate.
   destruct s.
    elim not_knd; reflexivity.
    discriminate.

  simpl; unfold V.lams, V.shift;
   destruct (le_gt_dec k n); try (apply False_ind; omega; fail).
  red; intros; auto.

 simpl; red; intros.
 apply M.lam_ext.
  rewrite H; rewrite <- IHt1.
  rewrite int_subst_rec_eq.
  reflexivity.

  red; intros.
  rewrite H; rewrite <- IHt2.
  rewrite int_subst_rec_eq.
  rewrite V.cons_lams; eauto with *.
  rewrite H1; reflexivity.

 simpl; red; intros.
 do 2 rewrite <- int_subst_rec_eq.
 rewrite H; rewrite IHt1; rewrite IHt2; reflexivity.

 simpl; red; intros.
 apply M.prod_ext; intros.
  rewrite H; rewrite <- IHt1.
  rewrite int_subst_rec_eq.
  reflexivity.

  red; intros.
  rewrite H; rewrite <- IHt2.
  rewrite int_subst_rec_eq.
  rewrite V.cons_lams; eauto with *.
  rewrite H1; reflexivity.
Qed.

Lemma int_subst : forall u t,
  int_trm u <> T.kind ->
  eq_term (int_trm (subst u t)) (T.subst (int_trm u) (int_trm t)).
intros.
symmetry; apply int_subst_rec; trivial.
Qed.

Lemma int_not_kind : forall T, T <> Srt kind -> int_trm (unmark_app T) <> T.kind.
red; intros.
apply H.
destruct T; try discriminate.
destruct s; trivial; discriminate.
destruct T1; discriminate.
Qed.

Hint Resolve int_not_kind eq_typ_not_kind.


Lemma int_sound : forall e M M' T,
  eq_typ e M M' T ->
  J.typ (int_env (unmark_env e)) (int_trm (unmark_app M)) (int_trm (unmark_app T)) /\
  J.eq_typ (int_env (unmark_env e)) (int_trm (unmark_app M)) (int_trm (unmark_app M')).
induction 1; simpl; intros.
 (* Srt *)
 split.
  apply R.typ_prop.
  apply R.refl.
 (* Ref *)
 split.
  destruct H0.
  subst t.
  unfold lift; rewrite unmark_lift.
  fold (lift (S v) (unmark_app x)); rewrite int_lift.
  apply R.typ_var.
  elim H1; simpl; auto.

  apply R.refl.
 (* Abs *)
 destruct IHeq_typ1.
 clear IHeq_typ2.
 destruct IHeq_typ3.
 split.
  apply R.typ_abs; eauto.
  apply R.eq_typ_abs; trivial.
 (* App *)
 destruct IHeq_typ1.
 destruct IHeq_typ3.
 split.
  rewrite unmark_subst0 with (1:=H2).
  rewrite int_subst; eauto.
  apply R.typ_app with (int_trm (unmark_app V)); eauto.
  apply R.eq_typ_app; trivial.
 (* Prod *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 split.
  apply R.typ_prod; trivial.
  destruct s2; auto.

  apply R.eq_typ_prod; trivial.
 (* Beta *)
 destruct IHeq_typ1.
 destruct IHeq_typ3.
 split.
  rewrite unmark_subst0 with (1:=H2).
  rewrite int_subst; eauto.
  apply R.typ_beta; eauto.

  rewrite unmark_subst0 with (1:=typ_refl2 _ _ _ _ H1).
  rewrite int_subst.
   apply R.eq_typ_beta; eauto.
   apply typ_refl2 in H; eauto.
 (* Red *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 split; trivial.
 apply R.typ_conv with (int_trm (unmark_app T)); eauto.
 (* Exp *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 split; trivial.
 apply typ_refl2 in H0.
 apply R.typ_conv with (int_trm (unmark_app T')); eauto.
 apply R.sym; trivial.
Qed.

(***********)

Load "template/Library.v".

(*
  Lemma valid_context_ok : forall e,
    valid_context e = true -> forall M M', ~ eq_typ e M M' FALSE.
*)

  Lemma non_provability : forall T,
    (forall x, ~ el (int_trm (unmark_app T)) vnil x) ->
    forall M M', ~ eq_typ nil M M' T.
red in |- *; intros.
apply int_sound in H0.
destruct H0 as (H0,_).
red in H0.
apply H with (int (int_trm (unmark_app M)) vnil).
apply H0.
red; intros.
destruct n; discriminate.
Qed.

End MakeModel.