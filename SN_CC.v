Require Export Relations Wellfounded Compare_dec.
Require Import Sat.
Require Import ZF ZFcoc.
Require Import ZFlambda.

(** Another strong normalization proof of the Calculus of Constructions *)

Set Implicit Arguments.

(***********************************************************************)
(** * Proving the SN requirements *)

Module CCSN.

Definition mkTY x S := couple x (iSAT S).
Definition El T := fst T.
Definition Real T := sSAT (snd T) .

Definition piSAT A (F:set->SAT) :=
  prodSAT (Real A) (interSAT (fun p:{y|y ∈ El A} => F (proj1_sig p))).

Definition sn_prod A F :=
  mkTY (cc_prod (El A) (fun x => El (F x)))
       (piSAT A (fun x => Real (F x))).

Definition sn_lam A F := cc_lam (El A) F.

Lemma sn_prod_intro : forall dom f F,
  ext_fun (El dom) f ->
  ext_fun (El dom) F ->
  (forall x, x ∈ El dom -> f x ∈ El (F x)) ->
  sn_lam dom f ∈ El (sn_prod dom F).
intros.
unfold sn_lam, sn_prod, mkTY, El.
rewrite fst_def.
apply cc_prod_intro; intros; auto.
do 2 red; intros.
apply fst_morph; auto.
Qed.


Lemma sn_prod_elim : forall dom f x F,
  f ∈ El (sn_prod dom F) ->
  x ∈ El dom ->
  cc_app f x ∈ El (F x).
intros.
unfold sn_prod, mkTY, El in H.
rewrite fst_def in H.
apply cc_prod_elim with (dom:=El dom) (F:=fun x => El(F x)); trivial.
Qed.

Lemma cc_impredicative_prod_non_empty : forall dom F,
  ext_fun dom F ->
  (forall x, x ∈ dom -> F x == singl prf_trm) ->
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
  (forall x, x ∈ El dom -> F x ∈ El sn_props) ->
  sn_prod dom F ∈ El sn_props.
unfold sn_props, mkTY, El; intros.
rewrite fst_def.
rewrite replSAT_ax; trivial.
unfold sn_prod, mkTY.
exists (piSAT dom (fun x : set => Real (F x))).
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

  Lemma sn_proof_of_false : prf_trm ∈ El (sn_prod sn_props (fun P => P)).
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

(** * Building the CC abstract SN model *)

Require Import Models.
Module SN_CC_Model <: CC_Model.

Definition X := set.
Definition inX x y := x ∈ El y.
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

Notation "x ∈ y" := (inX x y).
Notation "x == y" := (eqX x y).

Definition eq_fun (x:X) (f1 f2:X->X) :=
  forall y1 y2, y1 ∈ x -> y1 == y2 -> f1 y1 == f2 y2.

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
 unfold piSAT, Real.
 apply prodSAT_morph.
  apply sSAT_morph; apply snd_morph; trivial.

  apply interSAT_morph_subset; simpl; intros.
   unfold El; rewrite H; reflexivity.

   apply sSAT_morph; apply snd_morph; apply H0; trivial; reflexivity.
Qed.

Lemma prod_intro : forall dom f F,
  eq_fun dom f f ->
  eq_fun dom F F ->
  (forall x, x ∈ dom -> f x ∈ F x) ->
  lam dom f ∈ prod dom F.
Proof sn_prod_intro.

Lemma prod_elim : forall dom f x F,
  eq_fun dom F F ->
  f ∈ prod dom F ->
  x ∈ dom ->
  app f x ∈ F x.
intros.
eapply sn_prod_elim; eauto.
Qed.

Lemma impredicative_prod : forall dom F,
  eq_fun dom F F ->
  (forall x, x ∈ dom -> F x ∈ props) ->
  prod dom F ∈ props.
Proof sn_impredicative_prod.

Lemma beta_eq:
  forall dom F x,
  eq_fun dom F F ->
  x ∈ dom ->
  app (lam dom F) x == F x.
unfold app, lam, inX, eqX, El; intros.
apply cc_beta_eq; trivial.
Qed.

End SN_CC_Model.

Import SN_CC_Model.

(***********************************************************************)
(** Building the SN addon *)

Module SN_CC_addon.

  Definition Real : X -> SAT := Real.

  Lemma Real_morph : Proper (eqX ==> eqSAT) Real.
do 2 red; intros.
apply sSAT_morph.
apply snd_morph; trivial.
Qed.

  Lemma Real_sort : eqSAT (Real props) snSAT.
unfold Real, CCSN.Real, props, sn_props, mkTY.
rewrite snd_def.
rewrite iSAT_id.
reflexivity.
Qed.

  Lemma Real_prod : forall A B,
    eqSAT (Real (prod A B))
     (prodSAT (Real A)
        (interSAT (fun p:{y|y∈ A} => Real (B (proj1_sig p))))).
unfold Real, CCSN.Real, prod, sn_prod, piSAT, mkTY; intros.
rewrite snd_def.
rewrite iSAT_id.
reflexivity.
Qed.

  Definition daimon := empty.

  Lemma daimon_false : daimon ∈ prod props (fun P => P).
Proof sn_proof_of_false.

End SN_CC_addon.

(***********************************************************************)
(*
----
*)


Require GenModelSN.
Module SN := GenModelSN.MakeModel SN_CC_Model SN_CC_addon.

(** ** Extendability *)
Definition cst (x:set) : SN.trm.
left; exists (fun _ =>x) (fun _ =>Lambda.K).
 do 2 red; reflexivity.
 do 2 red; reflexivity.
 red; reflexivity.
 red; reflexivity.
Defined.

Definition mkSET (x:set) := cst (mkTY x snSAT).

Lemma mkSET_kind e x :
  (exists w, in_set w x) ->
  SN.typ e (mkSET x) SN.kind.
intros (w,?); red; intros.
split;[discriminate|].
simpl.
split;[|apply Lambda.sn_K].
exists nil; exists (mkSET x).
 reflexivity.

 exists w; simpl; intros _.
 unfold SN_CC_Model.inX, mkTY, El.
 rewrite fst_def; trivial.
Qed.

Lemma cst_typ e x y :
  in_set x y ->
  SN.typ e (cst x) (mkSET y).
red; intros.
apply SN.in_int_intro; try discriminate.
 simpl.
 unfold SN_CC_Model.inX, mkTY, El.
 rewrite fst_def; trivial.

 unfold SN_CC_addon.Real, Real, SN.tm, SN.int, mkSET, cst, SN.iint, SN.itm.
 unfold mkTY; rewrite snd_def.
 rewrite iSAT_id.
 apply Lambda.sn_K.
Qed.

Lemma cst_typ_inv x y :
  SN.typ nil (cst x) (mkSET y) ->
  in_set x y.
intros.
assert (SN.val_ok nil (SN.V.nil empty) (SN.I.nil Lambda.K)).
 red; intros.
 destruct n; inversion H0.
apply H in H0.
apply SN.in_int_not_kind in H0.
2:discriminate.
destruct H0 as (H0,_ ); simpl in H0.
unfold SN_CC_Model.inX, mkTY, El in H0.
rewrite fst_def in H0; trivial.
Qed.

Lemma cst_eq_typ e x y :
  x == y ->
  SN.eq_typ e (cst x) (cst y).
red; simpl; intros; trivial.
Qed.

Lemma cst_eq_typ_inv x y :
  SN.eq_typ nil (cst x) (cst y) ->
  x == y.
intros.
assert (SN.val_ok nil (SN.V.nil empty) (SN.I.nil Lambda.K)).
 red; intros.
 destruct n; inversion H0.
apply H in H0.
simpl in H0; trivial.
Qed.

Lemma mkSET_eq_typ e x y :
  x == y ->
  SN.eq_typ e (mkSET x) (mkSET y).
red; simpl; intros; trivial.
unfold mkTY; rewrite H; reflexivity.
Qed.

Lemma mkSET_eq_typ_inv x y :
  SN.eq_typ nil (mkSET x) (mkSET y) ->
  x == y.
intros.
assert (SN.val_ok nil (SN.V.nil empty) (SN.I.nil Lambda.K)).
 red; intros.
 destruct n; inversion H0.
apply H in H0.
simpl in H0; trivial.
apply couple_injection in H0; destruct H0; trivial.
Qed.


(** * Mapping semantic entities to the syntactic ones. *)

(** syntax *)
Require TypeJudge.
Module Ty := TypeJudge.
Module Tm := Term.
Module Lc := Lambda.


(** Terms *)
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
induction t; simpl int_trm; intros.
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

 simpl Tm.subst_rec.
 destruct (lt_eq_lt_dec k n) as [[fv|eqv]|bv]; simpl int_trm.
  simpl int_trm.
  destruct n; [inversion fv|].
  rewrite SN.red_sigma_var_gt; auto with arith.
  reflexivity.

  subst k; rewrite SN.red_sigma_var_eq; trivial.
  symmetry; apply int_lift.

  rewrite SN.red_sigma_var_lt; trivial.
  reflexivity.

 rewrite SN.red_sigma_abs.
 rewrite IHt1; rewrite IHt2; reflexivity.

 rewrite SN.red_sigma_app.
 rewrite IHt1; rewrite IHt2; reflexivity.

 rewrite SN.red_sigma_prod.
 rewrite IHt1; rewrite IHt2; reflexivity.
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
(* Proof that beta-reduction at the Lc level simulates beta-reduction
   at the Tm level. One beta at the Tm level may require several
   (but not zero) steps at the Lc level, because of the encoding
   of type-carrying lambda abstractions.
 *)
Lemma red1_sound : forall x y,
  Tm.red1 x y -> ~ Tm.mem_sort Tm.kind x ->
  SN.red_term (int_trm x) (int_trm y).
induction 1; simpl; intros.
 rewrite int_subst.
  apply SN.red_term_beta.

  destruct N; try discriminate.
  destruct s; try discriminate.
  elim H; auto.

 apply SN.red_term_abs_l; auto 10.
 apply SN.red_term_abs_r; auto 10.
 apply SN.red_term_app_l; auto 10.
 apply SN.red_term_app_r; auto 10.
 apply SN.red_term_prod_l; auto 10.
 apply SN.red_term_prod_r; auto 10.
Qed.

Lemma sn_sound : forall M,
  Acc (transp _ SN.red_term) (interp M) ->
  ~ Tm.mem_sort Tm.kind (Ty.unmark_app M) ->
  Tm.sn (Ty.unmark_app M).
intros M accM.
apply Acc_inverse_image with (f:=int_trm) in accM.
induction accM; intros.
constructor; intros.
apply H0; trivial.
 apply red1_sound; trivial.

 intro; apply H1; apply Tm.exp_sort_mem with (1:=H2); trivial.
Qed.

Hint Resolve int_not_kind Ty.eq_typ_not_kind.

(** Soundness of the typing rules *)

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
(*
----
*)

(** The main theorem: strong normalization of CC *)

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
apply SN.model_strong_normalization in ty; trivial.
apply sn_sound; trivial.
Qed.

(* Print the assumptions made to derive strong normalization of CC:
   the axioms of ZF. (In fact we don't need full replacement, only the
   functional version, so we should be able to have the SN theorem without
   assumption.)
 *)
Print Assumptions strong_normalization.
