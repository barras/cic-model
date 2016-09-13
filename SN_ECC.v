Require Export Relations Wellfounded.
Require Import Sat.
Require Import ZF ZFcoc ZFuniv ZFecc.
Require Import ZFlambda.

(** Strong normalization proof of the Extended Calculus of Constructions.
    It is based on GenModelSN, so it does not support strong eliminations.
    Inhabitation of all types is obtained by adding the empty set in every
    type (cf ZFuniv). The product is interpreted by the set of *partial*
    functions.
 *)

Set Implicit Arguments.

(** * Building the CC abstract SN model *)

Require Import Models.
Module SN_ECC_Model <: CC_Model.

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

Definition eq_fun (x:X) (f1 f2:X->X) :=
  forall y1 y2, inX y1 x -> y1 == y2 -> f1 y1 == f2 y2.

Lemma eq_fun_El x f1 f2 : eq_fun x f1 f2 -> ZF.eq_fun (El x) f1 f2.
do 2 red; intros.
apply H; auto.
Qed.
Hint Resolve eq_fun_El.

Lemma lam_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  lam x1 f1 == lam x2 f2.
unfold lam, sn_lam, eqX; intros.
apply cc_lam_ext; auto.
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
  apply union2_morph; auto with *.
  apply fst_morph; apply H0; auto.
  red; auto.

 apply iSAT_morph.
 unfold piSAT, Real.
 apply prodSAT_morph.
  apply sSAT_morph; apply snd_morph; trivial.

  apply interSAT_morph_subset; simpl; intros.
   unfold El; rewrite H; reflexivity.

   apply sSAT_morph; apply snd_morph; apply H0; auto; reflexivity.
Qed.

Lemma prod_intro : forall dom f F,
  eq_fun dom f f ->
  eq_fun dom F F ->
  (forall x, inX x dom -> inX (f x) (F x)) ->
  inX (lam dom f) (prod dom F).
Proof sn_prod_intro.

Lemma prod_elim : forall dom f x F,
  eq_fun dom F F ->
  inX f (prod dom F) ->
  inX x dom ->
  inX (app f x) (F x).
intros.
eapply sn_prod_elim; eauto.
Qed.

Lemma impredicative_prod : forall dom F,
  eq_fun dom F F ->
  (forall x, inX x dom -> inX (F x) props) ->
  inX (prod dom F) props.
Proof sn_impredicative_prod.

Lemma beta_eq:
  forall dom F x,
  eq_fun dom F F ->
  inX x dom ->
  app (lam dom F) x == F x.
unfold app, lam, inX, eqX; intros.
apply cc_beta_eq; auto.
Qed.

End SN_ECC_Model.

Import SN_ECC_Model.

(***********************************************************************)
(** Building the SN addon *)

Module SN_ECC_addon.

  Definition Real : X -> SAT := Real.

  Lemma Real_morph : Proper (eqX ==> eqSAT) Real.
do 2 red; intros.
apply sSAT_morph.
apply snd_morph; trivial.
Qed.

  Lemma Real_sort : eqSAT (Real props) snSAT.
apply Real_sort_sn.
Qed.

  Lemma Real_prod : forall A B,
    eqSAT (Real (prod A B))
     (prodSAT (Real A)
        (interSAT (fun p:{y|inX y A} => Real (B (proj1_sig p))))).
unfold Real, ZFuniv.Real, prod, sn_prod, piSAT, mkTY; intros.
rewrite snd_def.
rewrite iSAT_id.
reflexivity.
Qed.

  Definition daimon := empty.

  Lemma daimon_false : inX daimon (prod props (fun P => P)).
red; auto.
Qed.

End SN_ECC_addon.

(***********************************************************************)
(*
----
*)

Require GenModelSN.
Module SN := GenModelSN.MakeModel SN_ECC_Model SN_ECC_addon.

(** ** Extendability *)
Definition cst (x:set) : SN.T.term.
left; exists (fun _ =>x);[|exact Lambda.K].
 do 2 red; reflexivity.
Defined.

Definition mkSET (x:set) := cst (mkTY x snSAT).

Lemma mkSET_kind e x :
  SN.J.typ e (mkSET x) SN.T.kind.
red; intros.
split;[discriminate|].
split;[|apply Lambda.sn_K].
exists nil; exists (mkSET x).
 reflexivity.

 exists empty; simpl; intros _.
 apply union2_intro1.
 apply singl_intro.
Qed.

Lemma cst_typ e x y :
  in_set x y ->
  SN.J.typ e (cst x) (mkSET y).
red; intros.
apply SN.in_int_intro; try discriminate.
 simpl.
 apply Elt_El.
 unfold mkTY, Elt.
 rewrite fst_def; trivial. 

 unfold SN_ECC_addon.Real, Real, SN.T.tm, SN.T.int, mkSET, cst, SN.T.iint, SN.T.itm.
 unfold mkTY; rewrite snd_def.
 rewrite iSAT_id.
 apply Lambda.sn_K.
Qed.

Lemma cst_typ_inv x y :
  SN.J.typ nil (cst x) (mkSET y) ->
  x == empty \/ in_set x y.
intros.
assert (SN.val_ok nil (SN.V.nil empty) (SN.I.nil Lambda.K)).
 red; intros.
 destruct n; inversion H0.
apply H in H0.
apply SN.in_int_not_kind in H0.
2:discriminate.
destruct H0 as (H0,_ ); simpl in H0.
apply union2_elim in H0; destruct H0.
 apply singl_elim in H0; auto.

 unfold Elt, mkTY in H0; rewrite fst_def in H0; auto.
Qed.
Lemma cst_eq_typ e x y :
  x == y ->
  SN.J.eq_typ e (cst x) (cst y).
red; simpl; intros; trivial.
Qed.

Lemma cst_eq_typ_inv x y :
  SN.J.eq_typ nil (cst x) (cst y) ->
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
  SN.J.eq_typ e (mkSET x) (mkSET y).
red; simpl; intros; trivial.
unfold mkTY; rewrite H; reflexivity.
Qed.

Lemma mkSET_eq_typ_inv x y :
  SN.J.eq_typ nil (mkSET x) (mkSET y) ->
  x == y.
intros.
assert (SN.val_ok nil (SN.V.nil empty) (SN.I.nil Lambda.K)).
 red; intros.
 destruct n; inversion H0.
apply H in H0.
simpl in H0; trivial.
apply couple_injection in H0; destruct H0; trivial.
Qed.

(** * Predicative universes: inference rules *)

Definition type (n:nat) : SN.T.term := cst (sn_sort (ecc (S n))).

Lemma typ_prop_type0 e :
  SN.J.typ e SN.T.prop (type 0).
red; intros.
apply SN.in_int_intro.
 apply sn_sort_in_type; trivial.
 apply ecc_incl.
 apply ecc_in1.

 simpl SN.T.int; simpl SN.T.tm.
 unfold SN_ECC_addon.Real; rewrite Real_sort_sn.
 apply snSAT_intro.
 apply Lambda.sn_K.

 discriminate.
 discriminate.
Qed.

Lemma typ_type_type e n :
  SN.J.typ e (type n) (type (S n)).
red; intros.
apply SN.in_int_intro.
 apply sn_sort_in_type; trivial.
 apply ecc_in2.

 simpl SN.T.int; simpl SN.T.tm.
 unfold SN_ECC_addon.Real; rewrite Real_sort_sn.
 apply snSAT_intro.
 apply Lambda.sn_K.

 discriminate.
 discriminate.
Qed.

Lemma typ_prop_cumul e T :
  SN.J.typ e T SN.T.prop ->
  SN.J.typ e T (type 0).
red; intros.
apply H in H0.
destruct H0.
split; trivial.
destruct H1.
split.
 revert H1; apply sort_incl.
 transitivity (ecc 0); red; intros; [apply ecc_incl_prop|apply ecc_incl]; trivial.

 revert H2; simpl SN.T.int.
 unfold SN_ECC_addon.Real, props, sn_props; do 2 rewrite Real_sort_sn; trivial.
Qed.

Lemma typ_type_cumul e T n :
  SN.J.typ e T (type n) ->
  SN.J.typ e T (type (S n)).
red; intros.
apply H in H0.
destruct H0.
split; trivial.
destruct H1.
split.
 revert H1; apply sort_incl.
 red; intros; apply ecc_incl; trivial.

 revert H2; simpl SN.T.int.
 unfold SN_ECC_addon.Real, props, sn_props; do 2 rewrite Real_sort_sn; trivial.
Qed.

Lemma typ_type_cumul_le e T m n :
  le m n ->
  SN.J.typ e T (type m) ->
  SN.J.typ e T (type n).
induction 1; intros; auto.
apply typ_type_cumul; auto.
Qed.

Lemma typ_predicative_prod e T U n :
  SN.J.typ e T (type n) ->
  SN.J.typ (T::e) U (type n) ->
  SN.J.typ e (SN.T.Prod T U) (type n).
unfold SN.J.typ; intros.
specialize H with (1:=H1).
destruct H as (?,(?,?)); trivial.
split;[discriminate|].
split.
 apply sn_predicative_prod; trivial.
  red; red; intros.
  rewrite H5; reflexivity.

  intros.
  specialize SN.vcons_add_var0 with (1:=H1) (2:=H4) (3:=H);
    intros in_U.
  apply H0 in in_U.
  apply SN.in_int_not_kind in in_U;[|discriminate].
  destruct in_U; trivial.

  specialize SN.vcons_add_var0 with (1:=H1) (2:=empty_El _) (3:=H);
    intros in_U.
  apply H0 in in_U.
  destruct in_U  as (_,(_,satU)).
  unfold SN_ECC_addon.Real in *; simpl SN.T.int in *.
  rewrite Real_sort_sn in *.
  simpl in satU|-*.
  rewrite <- !SN.T.tm_tmm.
  rewrite SN.T.tm_subst_cons in satU.
  apply sat_sn in satU.
  apply Lambda.sn_subst in satU.
  apply KSAT_intro with (A:=snSAT); auto.
Qed.

(** * Mapping from syntactic entities to their semantic counterparts. *)

(** syntax of ECC *)
Require TypeJudgeECC.
Module Ty := TypeJudgeECC.
Module Tm := TermECC.
Module Lc := Lambda.


(** Terms *)
Fixpoint int_term t :=
  match t with
  | Tm.Srt Tm.prop => SN.T.prop
  | Tm.Srt (Tm.kind n) => type n
  | Tm.Ref n => SN.T.Ref n
  | Tm.App u v => SN.T.App (int_term u) (int_term v)
  | Tm.Abs T M => SN.T.Abs (int_term T) (int_term M)
  | Tm.Prod T U => SN.T.Prod (int_term T) (int_term U)
  end.
Definition interp t := int_term t.
Definition int_env := List.map interp.

Lemma interp_nk : forall T, interp T <> SN.T.kind.
induction T; simpl; intros; try discriminate.
destruct s; discriminate.
Qed.
Hint Resolve interp_nk.

Section LiftAndSubstEquiv.
(* Proof that lift and subst at both levels (SN and Tm) are equivalent. *)

(* Locally Import this module *)
Import SN.

Lemma int_lift_rec : forall n t k,
  eq_term (lift_rec n k (int_term t)) (int_term (Tm.lift_rec n t k)).
induction t; simpl int_term; intros.
 destruct s; simpl; trivial.
 split; [red|]; intros; reflexivity.

 split; [red|]; intros; reflexivity.

 simpl; unfold V.lams, I.lams, V.shift, I.shift.
 destruct (le_gt_dec k n0); simpl.
  replace (k+(n+(n0-k))) with (n+n0) by omega.
  split; [red|]; auto.

  split; [red|]; auto.

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
 split; [red|]; intros; reflexivity.

 split; [red|]; intros; reflexivity.

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

End LiftAndSubstEquiv.
(* Proof that beta-reduction at the Lc level simulates beta-reduction
   at the Tm level. One beta at the Tm level may require several
   (but not zero) steps at the Lc level, because of the encoding
   of type-carrying lambda abstractions.
 *)
Lemma red1_sound : forall x y,
  Tm.red1 x y ->
  SN.T.red_term (int_term x) (int_term y).
induction 1; simpl; intros.
 rewrite int_subst.
  apply SN.T.red_term_beta.

  destruct N; try discriminate.
  destruct s; try discriminate.

 apply SN.T.red_term_abs_l; auto 10.
 apply SN.T.red_term_abs_r; auto 10.
 apply SN.T.red_term_app_l; auto 10.
 apply SN.T.red_term_app_r; auto 10.
 apply SN.T.red_term_prod_l; auto 10.
 apply SN.T.red_term_prod_r; auto 10.
Qed.

Lemma sn_sound : forall M,
  Acc (transp _ SN.T.red_term) (interp M) ->
  Tm.sn M.
intros M accM.
apply Acc_inverse_image with (f:=int_term) in accM.
induction accM; intros.
constructor; intros.
apply H0; trivial.
 apply red1_sound; trivial.
Qed.


(** Soundness of the typing rules *)

Lemma typ_sort_type_ok e T s : 
  T <> SN.T.kind ->
  SN.J.typ e T (interp (TermECC.Srt s)) ->
  SN.type_ok e T.
split; trivial.
split.
 apply H0 in H1.
 apply SN.in_int_sn in H1; trivial.

 exists empty; red; auto. 
Qed.

Lemma int_sound : forall e M M' T,
  Ty.eq_typ e M M' T ->
  SN.J.typ (int_env e) (interp M) (interp T) /\
  SN.J.eq_typ (int_env e) (interp M) (interp M').
induction 1; simpl; intros.
 (* Srt *)
 split.
  apply typ_prop_type0.
  apply SN.refl.
 split.
  apply typ_type_type.
  apply SN.refl.
 (* Ref *)
 split.
  destruct H0.
  subst t.
  unfold Tm.lift, interp.
  fold (Tm.lift (S v) x); rewrite int_lift.
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
  apply SN.typ_abs_ok; eauto.
  apply typ_sort_type_ok in H3; auto.

  apply SN.eq_typ_abs; eauto.
 (* App *)
 destruct IHeq_typ1.
 destruct IHeq_typ3.
 clear IHeq_typ2 IHeq_typ4.
 unfold interp; simpl; fold (interp u) (interp v) (interp Ur).
 split.
  rewrite int_subst; fold (interp v); eauto.
  fold (interp Ur).
  apply SN.typ_app with (interp V); eauto.

  apply SN.eq_typ_app; trivial.
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
   apply SN.typ_prod_prop; auto.
   apply typ_sort_type_ok in H2; auto.

  apply SN.eq_typ_prod; eauto.
 (* Beta *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 destruct IHeq_typ3.
 clear IHeq_typ4.
 unfold interp; simpl; fold (interp T) (interp M) (interp U) (interp N).
 split.
  rewrite int_subst; fold (interp N); eauto.
  fold (interp U).
  apply SN.typ_beta_ok; auto.
  apply typ_sort_type_ok in H6; auto.

  rewrite int_subst; fold (interp N').
  2:assert (h := Ty.typ_refl2 _ _ _ _ H); eauto.
  apply SN.eq_typ_beta; eauto.
 (* Red *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 split; trivial.
 apply SN.typ_conv with (interp T); eauto.
 (* Exp *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 split; trivial.
 apply SN.typ_conv with (int_term T'); eauto.
 apply SN.sym; trivial.
Qed.

  Lemma interp_wf : forall e, Ty.wf e -> SN.J.wf (int_env e).
induction e; simpl; intros.
 apply SN.wf_nil.

 inversion_clear H.
 assert (wfe := Ty.typ_wf _ _ _ _ H0).
 apply int_sound in H0.
 destruct H0 as (H0,_).
 apply SN.wf_cons_ok; auto.
 apply typ_sort_type_ok in H0; auto.
Qed.

Lemma interp_sound : forall e M M' T,
  Ty.eq_typ e M M' T ->
  SN.J.wf (int_env e) /\ SN.J.typ (int_env e) (interp M) (interp T).
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
apply SN.model_strong_normalization in ty; trivial.
apply sn_sound; trivial.
Qed.

(* Print the assumptions made to derive strong normalization of ECC:
   the axioms of ZF, and the existence of Grothendieck universes.
   In fact we don't need full replacement, only the functional version,
   so we have the SN theorem with only the axiom about Grothendieck universes.
 *)
Print Assumptions strong_normalization.
