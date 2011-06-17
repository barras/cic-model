Require Export Relations Wellfounded Compare_dec.
Require Import Sat.
Require Import ZF ZFcoc.
Require Import ZFlambda.
Import IZF.

Set Implicit Arguments.

(***********************************************************************)
(* Proving the SN requirements *)

Module CCSN.

Definition mkTY x S := couple x (iSAT S).
Definition El T := fst T.
Definition Red T := sSAT (snd T) .

Definition piSAT A (F:set->SAT) :=
  prodSAT (Red A) (interSAT (fun p:{y|y \in El A} => F (proj1_sig p))).

Definition sn_prod A F :=
  mkTY (cc_prod (El A) (fun x => El (F x)))
       (piSAT A (fun x => Red (F x))).

Definition sn_lam A F := cc_lam (El A) F.

Lemma sn_prod_intro : forall dom f F,
  ext_fun (El dom) f ->
  ext_fun (El dom) F ->
  (forall x, x \in El dom -> f x \in El (F x)) ->
  sn_lam dom f \in El (sn_prod dom F).
intros.
unfold sn_lam, sn_prod, mkTY, El.
rewrite fst_def.
apply cc_prod_intro; intros; auto.
do 2 red; intros.
apply fst_morph; auto.
Qed.


Lemma sn_prod_elim : forall dom f x F,
  f \in El (sn_prod dom F) ->
  x \in El dom ->
  cc_app f x \in El (F x).
intros.
unfold sn_prod, mkTY, El in H.
rewrite fst_def in H.
apply cc_prod_elim with (dom:=El dom) (F:=fun x => El(F x)); trivial.
Qed.

Lemma cc_impredicative_prod_non_empty : forall dom F,
  ext_fun dom F ->
  (forall x, x \in dom -> F x == singl prf_trm) ->
  cc_prod dom F == singl prf_trm.
Proof.
intros.
apply singl_ext; intros.
 rewrite <- (cc_impredicative_lam dom (fun x => prf_trm)); intros.
 2:do 2 red; reflexivity.
  apply cc_prod_intro; intros; auto.
  apply H0 in H1; rewrite H1.
  apply singl_intro.

  reflexivity.

 unfold cc_prod in H1.
 rewrite replf_ax in H1; intros.
  destruct H1 as (f,f_fun,z_lam).
  rewrite z_lam; clear z z_lam.
  apply cc_impredicative_lam; intros.
   do 2 red; intros.
   rewrite H2; reflexivity.

   apply singl_elim.
   fold prf_trm.
   rewrite <- (H0 _ H1).
   apply dep_func_elim with (1:=f_fun); trivial.

  do 2 red; intros.
  apply cc_lam_ext; try reflexivity.
  red; intros.
  apply app_morph; trivial.
Qed.


Definition sn_props :=
  mkTY (replSAT(fun A => mkTY (singl prf_trm) A)) snSAT.

Lemma prop_repl_morph :
  Proper (eqSAT ==> eq_set) (fun A => couple (singl prf_trm) (iSAT A)).
do 2 red; intros.
apply couple_morph; try reflexivity.
apply iSAT_morph; trivial.
Qed.
Hint Resolve prop_repl_morph.

Lemma sn_impredicative_prod : forall dom F,
  ext_fun (El dom) F ->
  (forall x, x \in El dom -> F x \in El sn_props) ->
  sn_prod dom F \in El sn_props.
unfold sn_props, mkTY, El; intros.
rewrite fst_def.
rewrite replSAT_ax; trivial.
unfold sn_prod, mkTY.
exists (piSAT dom (fun x : set => Red (F x))).
apply couple_morph; try reflexivity.
apply cc_impredicative_prod_non_empty; intros.
 do 2 red; intros.
 unfold El; apply fst_morph; auto.

 specialize H0 with (1:=H1).
 rewrite fst_def in H0.
 rewrite replSAT_ax in H0; trivial.
 destruct H0.
 rewrite H0; unfold El; rewrite fst_def.
 reflexivity.
Qed.

  Lemma sn_proof_of_false : prf_trm \in El (sn_prod sn_props (fun P => P)).
setoid_replace prf_trm with (cc_lam (El sn_props) (fun _ => prf_trm)).
 unfold sn_prod, mkTY, El; rewrite fst_def.
 apply cc_prod_intro; intros.
  do 2 red; reflexivity.

  do 2 red; intros; apply fst_morph; trivial.
  unfold sn_props, mkTY in H.
  rewrite fst_def in H.
  rewrite replSAT_ax in H; trivial.
  destruct H as (A, eq_x).
  rewrite eq_x.
  rewrite fst_def.
  apply singl_intro.

 symmetry.
 apply cc_impredicative_lam; intros.
  do 2 red; intros; reflexivity.
  reflexivity.
Qed.

End CCSN.
Import CCSN.

(* Building the CC model *)

Require Import Models.
Module SN_CC_Model <: CC_Model.

Definition X := set.
Definition inX x y := x \in El y.
Definition eqX := eq_set.
Lemma eqX_equiv : Equivalence eqX.
Proof eq_set_equiv.

Lemma in_ext: Proper (eqX ==> eqX ==> iff) inX.
do 3 red; intros.
unfold inX, El, eqX in *.
rewrite H; rewrite H0; reflexivity.
Qed.

Definition props := sn_props.
Definition app := cc_app.
Definition lam := sn_lam.
Definition prod := sn_prod.

Notation "x \in y" := (inX x y) (at level 60).
Notation "x == y" := (eqX x y) (at level 70).

Definition eq_fun (x:X) (f1 f2:X->X) :=
  forall y1 y2, y1 \in x -> y1 == y2 -> f1 y1 == f2 y2.

Lemma lam_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  lam x1 f1 == lam x2 f2.
unfold lam, sn_lam, eqX; intros.
apply cc_lam_ext; trivial.
unfold El; rewrite H; reflexivity.
Qed.

Lemma app_ext: Proper (eqX ==> eqX ==> eqX) app.
Proof cc_app_morph.

Lemma prod_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  prod x1 f1 == prod x2 f2.
unfold prod, sn_prod, eqX, mkTY, El; intros.
apply couple_morph.
 apply cc_prod_ext; intros.
  rewrite H; reflexivity.
  red; intros.
  apply fst_morph; apply H0; trivial.

 apply iSAT_morph.
 unfold piSAT, Red.
 apply prodSAT_morph.
  apply sSAT_morph; apply snd_morph; trivial.

  apply interSAT_morph_subset; simpl; intros.
   unfold El; rewrite H; reflexivity.

   apply sSAT_morph; apply snd_morph; apply H0; trivial; reflexivity.
Qed.

Lemma prod_intro : forall dom f F,
  eq_fun dom f f ->
  eq_fun dom F F ->
  (forall x, x \in dom -> f x \in F x) ->
  lam dom f \in prod dom F.
Proof sn_prod_intro.

Lemma prod_elim : forall dom f x F,
  eq_fun dom F F ->
  f \in prod dom F ->
  x \in dom ->
  app f x \in F x.
intros.
eapply sn_prod_elim; eauto.
Qed.

Lemma impredicative_prod : forall dom F,
  eq_fun dom F F ->
  (forall x, x \in dom -> F x \in props) ->
  prod dom F \in props.
Proof sn_impredicative_prod.

Lemma beta_eq:
  forall dom F x,
  eq_fun dom F F ->
  x \in dom ->
  app (lam dom F) x == F x.
unfold app, lam, inX, eqX, El; intros.
apply cc_beta_eq; trivial.
Qed.

End SN_CC_Model.

Import SN_CC_Model.

(***********************************************************************)
(* Building the SN addon *)

Module SN_CC_addon.

  Definition Red : X -> SAT := Red.

  Lemma Red_morph : Proper (eqX ==> eqSAT) Red.
do 2 red; intros.
apply sSAT_morph.
apply snd_morph; trivial.
Qed.

  Lemma Red_sort : eqSAT (Red props) snSAT.
unfold Red, CCSN.Red, props, sn_props, mkTY.
rewrite snd_def.
rewrite iSAT_id.
reflexivity.
Qed.

  Lemma Red_prod : forall A B,
    eqSAT (Red (prod A B))
     (prodSAT (Red A)
        (interSAT (fun p:{y|y\in A} => Red (B (proj1_sig p))))).
unfold Red, CCSN.Red, prod, sn_prod, piSAT, mkTY; intros.
rewrite snd_def.
rewrite iSAT_id.
reflexivity.
Qed.

  Definition daemon := empty.

  Lemma daemon_false : daemon \in prod props (fun P => P).
Proof sn_proof_of_false.

End SN_CC_addon.

(***********************************************************************)

Require GenModelSN TypeJudge.

Module Ty := TypeJudge.
Module Tm := Term.
Module Lc := Lambda.

Module SN := GenModelSN.MakeModel SN_CC_Model SN_CC_addon.


Fixpoint int_trm t :=
  match t with
  | Tm.Srt Tm.prop => SN.prop
  | Tm.Srt Tm.kind => SN.kind
  | Tm.Ref n => SN.Ref n
  | Tm.App u v => SN.App (int_trm u) (int_trm v)
  | Tm.Abs T M => SN.Abs (int_trm T) (int_trm M)
  | Tm.Prod T U => SN.Prod (int_trm T) (int_trm U)
  end.
Definition interp t := int_trm (Ty.unmark_app t).
Definition int_env := List.map interp.

Section LiftAndSubstEquiv.
(* Proof that lift and subst at both levels (SN and Tm) are equivalent. *)

(* Locally Import this module *)
Import SN.

Lemma int_lift_rec : forall n t k,
  eq_trm (lift_rec n k (int_trm t)) (int_trm (Tm.lift_rec n t k)).
induction t; intros.
 destruct s; simpl; trivial.
 split; red; intros; reflexivity.

 simpl; unfold V.lams, I.lams, V.shift, I.shift.
 destruct (le_gt_dec k n0); simpl.
  replace (k+(n+(n0-k))) with (n+n0) by omega.
  split; red; auto.

  split; red; auto.

 simpl lift_rec; simpl int_trm.
 rewrite <- IHt1.
 rewrite <- IHt2.
 simpl; split; red; intros.
  apply lam_ext; intros.
   rewrite H.
   symmetry; apply int_lift_rec_eq.

   red; intros.
   rewrite <- H; rewrite <- H1.
   rewrite int_lift_rec_eq.
   rewrite V.cons_lams; auto with *.
   do 2 red; intros.
   rewrite H2; reflexivity.

  f_equal.
   rewrite H.
   rewrite tm_lift_rec_eq.
   rewrite <- ilift_lams; trivial.
   unfold I.shift; auto.

   rewrite H.
   symmetry; apply tm_lift_rec_eq.

 simpl; split; red; intros.
   rewrite H; rewrite <- IHt1; rewrite <- IHt2.
   do 2 rewrite int_lift_rec_eq.
   reflexivity.

   rewrite H; rewrite <- IHt1; rewrite <- IHt2.
   do 2 rewrite tm_lift_rec_eq.
   reflexivity.

 simpl lift_rec; simpl int_trm.
 rewrite <- IHt1.
 rewrite <- IHt2.
 simpl; split; red; intros.
  apply prod_ext; intros.
   rewrite H.
   symmetry; apply int_lift_rec_eq.

   red; intros.
   rewrite <- H; rewrite <- H1.
   rewrite int_lift_rec_eq.
   rewrite V.cons_lams; auto with *.
   do 2 red; intros.
   rewrite H2; reflexivity.

  f_equal.
   rewrite H.
   symmetry; apply tm_lift_rec_eq.

   f_equal.
   rewrite H.
   rewrite tm_lift_rec_eq.
   rewrite <- ilift_lams; trivial.
   unfold I.shift; auto.
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
induction t; intros.
 destruct s; simpl; trivial.
 split; red; intros; reflexivity.

 simpl Tm.subst_rec.
 destruct (lt_eq_lt_dec k n) as [[fv|eqv]|bv].
  simpl; unfold V.lams, I.lams, V.shift, I.shift;
   destruct (le_gt_dec k n); try (apply False_ind; omega; fail).
  replace (n-k) with (S(pred n-k)) by omega; simpl.
  replace (k+(pred n-k)) with (pred n) by omega; split; red; auto.

  rewrite int_lift.
  simpl; unfold V.lams, I.lams, V.shift, I.shift;
   destruct (le_gt_dec k n); try (apply False_ind; omega; fail).
  destruct (int_trm arg); simpl; auto.
  clear l; subst k.
  replace (n-n) with 0 by omega.
  simpl.
  split; red; intros.
   rewrite V.lams0.
   change (V.shift n (fun k => y k)) with (V.shift n y).
   rewrite <- H; reflexivity.

   rewrite I.lams0.
   change (I.shift n (fun k => y k)) with (I.shift n y).
   rewrite <- H; reflexivity.

  simpl; unfold V.lams, I.lams, V.shift, I.shift;
   destruct (le_gt_dec k n); try (apply False_ind; omega; fail).
  split; red; intros; auto.

 simpl Tm.subst_rec; simpl int_trm.
 rewrite <- IHt1.
 rewrite <- IHt2.
 simpl; split; red; intros.
  apply lam_ext; intros.
   rewrite H.
   symmetry; apply int_subst_rec_eq.

   red; intros.
   rewrite <- H; rewrite <- H1.
   rewrite int_subst_rec_eq.
   rewrite V.cons_lams.
    rewrite V.shift_split; rewrite V.shift_cons.
    reflexivity.

    do 2 red; intros.
    rewrite H2; reflexivity.

  f_equal.
   rewrite H.
   rewrite tm_subst_rec_eq.
   (* beware! arguments of ilams must reflect the right dependency
      w.r.t the substitution *)
   change
     (I.lams (S k) (I.cons (tm (I.shift (S k) (ilift y)) (int_trm arg))) (ilift y))
   with (I.lams (S k) (fun j => I.cons (tm j (int_trm arg)) j) (ilift y)).
   rewrite <- ilift_lams; intros; auto.
   destruct a; simpl; auto.
   unfold Lc.lift.
   rewrite <- tm_liftable.
   apply tm_morph; auto.
   reflexivity.

   rewrite H.
   symmetry; apply tm_subst_rec_eq.

 simpl Tm.subst_rec; simpl int_trm.
 rewrite <- IHt1.
 rewrite <- IHt2.
 simpl; split; red; intros.
  rewrite H.
  apply app_ext; symmetry; apply int_subst_rec_eq.

  rewrite H; do 2 rewrite <- tm_subst_rec_eq; trivial.

 simpl subst_rec; simpl int_trm.
 rewrite <- IHt1.
 rewrite <- IHt2.
 simpl; split; red; intros.
  apply prod_ext; intros.
   rewrite H.
   symmetry; apply int_subst_rec_eq.

   red; intros.
   rewrite <- H; rewrite <- H1.
   rewrite int_subst_rec_eq.
   rewrite V.cons_lams.
    rewrite V.shift_split; rewrite V.shift_cons.
    reflexivity.

    do 2 red; intros.
    rewrite H2; reflexivity.

  f_equal.
   rewrite H.
   symmetry; apply tm_subst_rec_eq.

   f_equal.
   rewrite H.
   rewrite tm_subst_rec_eq.
   (* beware! arguments of I.lams must reflect the right dependency
      w.r.t the substitution *)
   change
     (I.lams (S k) (I.cons (tm (I.shift (S k) (ilift y)) (int_trm arg))) (ilift y))
   with (I.lams (S k) (fun j => I.cons (tm j (int_trm arg)) j) (ilift y)).
   rewrite <- ilift_lams; intros; auto.
   destruct a; simpl; auto.
   unfold Lc.lift.
   rewrite <- tm_liftable.
   apply tm_morph; auto.
   reflexivity.
Qed.


Lemma int_subst : forall u t,
  int_trm u <> kind ->
  eq_trm (int_trm (Tm.subst u t)) (subst (int_trm u) (int_trm t)).
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

(* Soundness of the typing rules *)

Lemma int_sound : forall e M M' T,
  Ty.eq_typ e M M' T ->
  SN.typ (int_env e) (interp M) (interp T) /\
  SN.eq_typ (int_env e) (interp M) (interp M').
induction 1; simpl; intros.
 (* Srt *)
 split.
  apply SN.typ_prop.
  apply SN.refl.
 (* Ref *)
 split.
  destruct H0.
  subst t.
  unfold Tm.lift, interp; rewrite Ty.unmark_lift.
  fold (Tm.lift (S v) (Ty.unmark_app x)); rewrite int_lift.
  simpl.
  apply SN.typ_var.
  elim H1; simpl; auto.

  apply SN.refl.
 (* Abs *)
 destruct IHeq_typ1.
 clear IHeq_typ2.
 destruct IHeq_typ3.
 unfold interp; simpl; fold (interp T) (interp M) (interp U).
 split.
  apply SN.typ_abs; eauto.
  destruct s1; red; auto.

  apply SN.eq_typ_abs; eauto.
 (* App *)
 destruct IHeq_typ1.
 destruct IHeq_typ3.
 clear IHeq_typ2 IHeq_typ4.
 unfold interp; simpl; fold (interp u) (interp v) (interp Ur).
 split.
  rewrite Ty.unmark_subst0 with (1:=H2).
  rewrite int_subst; fold (interp v); eauto.
  fold (interp Ur).
  apply SN.typ_app with (interp V); eauto.

  apply SN.eq_typ_app; trivial.
 (* Prod *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 unfold interp; simpl; fold (interp T) (interp U) (interp T') (interp U').
 split.
  apply SN.typ_prod; trivial.
   destruct s2; auto.

   destruct s1; red; auto.

  apply SN.eq_typ_prod; eauto.
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
  apply SN.typ_beta; eauto.
  destruct s1; red; auto.

  rewrite Ty.unmark_subst0 with (1:=Ty.typ_refl2 _ _ _ _ H1).
  rewrite int_subst; fold (interp N').
  2:assert (h := Ty.typ_refl2 _ _ _ _ H); eauto.
  apply SN.eq_typ_beta; eauto.
 (* Red *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 split; trivial.
 apply SN.typ_conv with (interp T); eauto.
 apply Ty.typ_refl2 in H0; eauto.
 (* Exp *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 split; trivial.
 apply SN.typ_conv with (int_trm (Ty.unmark_app T')); eauto.
  apply SN.sym; trivial.

  fold (interp T').
  apply Ty.typ_refl2 in H0; eauto.
Qed.

  Lemma interp_wf : forall e, Ty.wf e -> SN.wf (int_env e).
induction e; simpl; intros.
 apply SN.wf_nil.

 inversion_clear H.
 assert (wfe := Ty.typ_wf _ _ _ _ H0).
 apply int_sound in H0.
 destruct H0 as (H0,_).
 apply SN.wf_cons; auto.
 destruct s; [left|right]; assumption.
Qed.

Lemma interp_sound : forall e M M' T,
  Ty.eq_typ e M M' T ->
  SN.wf (int_env e) /\ SN.typ (int_env e) (interp M) (interp T).
intros.
assert (wfe := Ty.typ_wf _ _ _ _ H).
apply interp_wf in wfe.
apply int_sound in H; destruct H; auto.
Qed.

(***********)

Hint Resolve Lc.redp_app_r Lc.redp_app_l Lc.redp_abs
  Lc.redp_lift_rec.

(* Proof that beta-reduction at the Lc level simulates beta-reduction
   at the Tm level. One beta at the Tm level may require several
   (but not zero) steps at the Lc level, because of the encoding
   of type-carrying lambda abstractions.
 *)
Lemma tm_red1 : forall x y,
  Tm.red1 x y -> ~ Tm.mem_sort Tm.kind x ->
  forall j, Lc.redp (SN.tm j (int_trm x)) (SN.tm j (int_trm y)).
induction 1; simpl; intros; unfold Lc.App2; auto 10.
apply t_trans with 
  (Lc.App (Lc.Abs (SN.tm (SN.ilift j) (int_trm M)))
     (SN.tm j (int_trm N))).
 apply Lc.redp_app_l.
 apply Lc.redp_K.

 apply t_step; apply Lc.red1_beta.
 rewrite int_subst.
  rewrite SN.tm_subst_eq; trivial.

  destruct N; try discriminate.
  destruct s; try discriminate.
  elim H; auto.
Qed.

(* stdlib! *)
Lemma clos_trans_transp : forall A R x y,
  clos_trans A R x y ->
  clos_trans A (transp _ R) y x.
induction 1.
 apply t_step; trivial.
 apply t_trans with y; trivial.
Qed.

Lemma sn_tm : forall t j,
  ~ Tm.mem_sort Tm.kind t -> Lc.sn (SN.tm j (int_trm t)) -> Tm.sn t.
assert (forall x, Lc.sn x -> forall t j, x = SN.tm j (int_trm t) ->
        ~ Tm.mem_sort Tm.kind t -> Tm.sn t); eauto.
intros x snx.
elim (Acc_clos_trans _ _ _ snx); intros.
constructor; intros.
unfold transp in *.
apply H0 with (j:=j) (2:=eq_refl _).
 subst x0.
 apply clos_trans_transp.
 apply tm_red1; trivial.

 red; intro; apply H2; eapply Tm.exp_sort_mem; eauto.
Qed.

Lemma strong_normalization : forall e M M' T,
  Ty.eq_typ e M M' T ->
  Tm.sn (Ty.unmark_app M).
Proof.
intros.
assert (~ Tm.mem_sort Tm.kind (Ty.unmark_app M)).
 apply Ty.eq_typ_typ in H.
 red; intro Hm; apply (Types.typ_mem_kind _ _ _ Hm H).
apply interp_sound in H.
destruct H as (wfe,ty).
apply SN.typ_sn in ty; trivial.
destruct ty as (j,sn_j).
apply sn_tm in sn_j; trivial.
Qed.

(* Print the assumptions made to derive strong normalization of CC:
   the axioms of ZF.
 *)
Print Assumptions strong_normalization.