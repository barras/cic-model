Require Import Sat.
Require Import ZF ZFcoc ZFlambda.
Require GenRealSN.

Set Implicit Arguments.

(***********************************************************************************************)
(** * Proving the SN model requirements *)

Module CCSN.

(** Types are coded by a carrier set X and a realizability relation R
   assigning a reducibility candidate to each element of the
   domain.
   This means that even non-computable functions have "realizers",
   but no closed ones (it is the set of neutral terms).
 *)
Definition mkTY X R := couple X (cc_lam X (fun x => iSAT (R x))).

Lemma mkTY_ext : forall X Y R R',
  X == Y ->
  (forall x x', x ∈ X -> x == x' -> eqSAT (R x) (R' x')) ->
  mkTY X R == mkTY Y R'.
unfold mkTY; intros.
apply couple_morph; trivial.
apply cc_lam_ext; auto.
red; intros.
apply iSAT_morph.
auto.
Qed.

(* Accessing the set of values of a type.
   The official membership relation of the model (see inX below) will be
   x ∈ El T, which reads "x is a value of type T"
 *)
Definition El T := fst T.

(* Accessing the realizability relation.
   inSAT t (Real T x), means that t is a realizer of x in type T. It
   implicitely requires x ∈ El T. 
 *)
Definition Real T x := sSAT (cc_app (snd T) x) .

Instance El_morph : morph1 El.
Proof fst_morph.

Instance Real_morph : Proper (eq_set==>eq_set==>eqSAT) Real.
do 3 red; intros.
unfold Real.
apply sSAT_morph.
rewrite H; rewrite H0; reflexivity.
Qed.

Lemma El_def : forall X R, El (mkTY X R) == X.
unfold El,mkTY; intros.
apply fst_def.
Qed.

Lemma Real_def : forall x X R,
  (forall x x', x ∈ X -> x == x' -> eqSAT (R x) (R x')) ->
  x ∈ X ->
  eqSAT (Real (mkTY X R) x) (R x).
intros.
unfold Real, mkTY.
rewrite snd_def.
rewrite cc_beta_eq; auto.
 apply iSAT_id.

 do 2 red; intros.
 apply iSAT_morph; auto.
Qed.

(** The realizability relation of a dependent product of domain type A
   and co-domain family of types F for a  function f:
   it is the intersection of all reducibility candidates {x}A -> {f(x)}F(x)
   when x ranges A.
   Note: {x}A -> {f(x)}F(x) is the set of that map any realizer of x (in A) to a
   realizer of f(x) (in F(x)). So the intersection of these sets when x ranges El(A)
   is the set of terms that realize f (in forall x:A. F(x)).
 *)
Definition piSAT A (F:set->set) (f:set->set) :=
  piSAT0 (fun x => x ∈ El A) (Real A) (fun x => Real (F x) (f x)).

Lemma piSAT_morph : forall A B F F' f f',
  A == B ->
  eq_fun (El A) F F' ->
  eq_fun (El A) f f' -> 
  eqSAT (piSAT A F f) (piSAT B F' f').
unfold piSAT; intros.
apply piSAT0_morph; intros.
 red; intros.
 rewrite H; reflexivity.

 rewrite H; reflexivity.

 apply Real_morph; auto with *.
Qed.

Definition prod A F :=
  mkTY (cc_prod (El A) (fun x => El (F x))) (fun f => piSAT A F (cc_app f)).

Lemma Real_prod : forall dom f F,
    eq_fun (El dom) F F ->
    f ∈ El (prod dom F) ->
    eqSAT (Real (prod dom F) f) (piSAT dom F (cc_app f)).
unfold prod; intros.
rewrite El_def in H0; rewrite Real_def; trivial.
 reflexivity.

 do 2 red; intros.
 apply piSAT_morph; auto with *.
 red; intros; apply cc_app_morph; trivial.
Qed.

Definition lam A F := cc_lam (El A) F.

Definition app := cc_app.

Lemma prod_intro : forall dom f F,
  ext_fun (El dom) f ->
  ext_fun (El dom) F ->
  (forall x, x ∈ El dom -> f x ∈ El (F x)) ->
  lam dom f ∈ El (prod dom F).
intros.
unfold lam, prod, mkTY, El.
rewrite fst_def.
apply cc_prod_intro; intros; auto.
do 2 red; intros.
apply fst_morph; auto.
Qed.


Lemma prod_elim : forall dom f x F,
  eq_fun (El dom) F F ->
  f ∈ El (prod dom F) ->
  x ∈ El dom ->
  cc_app f x ∈ El (F x).
intros dom f x F _ H.
unfold prod, mkTY, El in H.
rewrite fst_def in H.
apply cc_prod_elim with (dom:=El dom) (F:=fun x => El(F x)); trivial.
Qed.

(** ** The type of propositions:
   - propositions are types and do not interact with their surrounding context (they
     are neutral), so the set of realizers of any proposition is SN;
   - all propositions are non-empty (and have the same values as True), but their set of
     realizers must depend on the syntax of the propositions, because proofs compute.
     The realizer sets can be any reducibility candidate.
   Remark: we cannot have that all propositions are equal (they can differ on the
   set of realizers). Otherwise True=(True->True) wold allow non normalizing terms
   (e.g. Y).
 *)

(** Injecting reducibility candidates into propositions *)
Definition mkProp S := mkTY (singl empty) (fun _ => S).

Instance mkProp_morph : Proper (eqSAT ==> eq_set) mkProp.
unfold mkProp; do 2 red; intros.
apply mkTY_ext; auto with *.
Qed.

Lemma El_mkProp : forall S, El (mkProp S) == singl empty.
unfold mkProp; intros; rewrite El_def; auto with *.
Qed.

Lemma Real_mkProp S x : x == empty -> eqSAT (Real (mkProp S) x) S.
unfold mkProp; intros.
rewrite Real_def; auto with *.
rewrite H; apply singl_intro.
Qed.

(** The sort of propositions *)
Definition props :=
  mkTY
    (* The domain of props *)
    (replSAT (fun S:SAT => mkProp S))
    (* realizers of prop *)
    (fun _ => snSAT).

Lemma El_props_def P :
  P ∈ El props <-> exists S, P == mkProp S.
unfold props; rewrite El_def.
rewrite replSAT_ax; eauto with *.
Qed.

  Lemma Real_sort : forall x, x ∈ El props -> eqSAT (Real props x) snSAT.
intros.
rewrite El_props_def in H; destruct H as (S,H).
unfold props; rewrite Real_def; auto with *.
rewrite replSAT_ax; eauto with *.
Qed.

(* Re-doing the impredicativity property in the case where we have no
   empty propositions. (Could be moved to ZFcoc.) *)
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

Lemma impredicative_prod : forall dom F,
  ext_fun (El dom) F ->
  (forall x, x ∈ El dom -> F x ∈ El props) ->
  prod dom F ∈ El props.
intros.
rewrite El_props_def.
exists (piSAT dom F (fun _ => prf_trm)).
assert (forall x, x ∈ El dom -> El (F x) == singl prf_trm).
 intros.
 specialize H0 with (1:=H1).
 rewrite El_props_def in H0; destruct H0 as (S,H0).
 rewrite H0; apply El_mkProp.
unfold prod, mkProp.
apply mkTY_ext.
 apply cc_impredicative_prod_non_empty; trivial.
 do 2 red; intros; apply El_morph; apply H; trivial.

 intros.
 apply piSAT_morph; auto with *.
 red; intros.
 apply cc_prod_elim with (2:=H4) in H2.
 rewrite H1 in H2; trivial.
 apply singl_elim in H2; trivial.
Qed.

(* All propositions are inhabited: *)
  Definition daimon := prf_trm.
  Lemma daimon_false : prf_trm ∈ El (prod props (fun P => P)).
assert (prod props (fun P => P) ∈ El props).
 apply impredicative_prod; auto with *.
 do 2 red; auto.
rewrite El_props_def in H; destruct H as (S,H).
rewrite H.
rewrite El_mkProp; apply singl_intro.
Qed.

(* Module bureaucracy *)
Definition X:=set.
Definition eqX := eq_set.
Definition eqX_equiv := eq_set_equiv.
Definition inX x y := x ∈ El y.
Instance in_ext : Proper (eq_set==>eq_set==>iff) inX.
apply morph_impl_iff2; auto with *.
unfold inX; do 4 red; intros.
rewrite <- H; rewrite <- H0; trivial.
Qed.

Definition eq_fun (x:X) (f1 f2:X->X) :=
  forall y1 y2, y1 ∈ El x -> y1 == y2 -> f1 y1 == f2 y2.

Lemma lam_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  lam x1 f1 == lam x2 f2.
unfold lam; intros.
apply cc_lam_ext; trivial.
apply El_morph; trivial.
Qed.

Lemma app_ext: Proper (eqX ==> eqX ==> eqX) app.
Proof cc_app_morph.

Lemma prod_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  prod x1 f1 == prod x2 f2.
unfold prod; intros.
apply mkTY_ext; intros.
 apply cc_prod_ext; auto.
  apply El_morph; trivial.

  red; intros.
  apply El_morph; auto.

 apply piSAT_morph; intros; auto.
 red; intros.
 apply cc_app_morph; trivial.
Qed.

Lemma beta_eq:
  forall dom F x,
  eq_fun dom F F ->
  x ∈ El dom ->
  app (lam dom F) x == F x.
intros.
unfold app, lam.
rewrite cc_beta_eq; auto with *.
Qed.

End CCSN.
Import CCSN.

(* Checking module instantiation. *)
(*
Module __ <: CC_Model.
  Include CCSN.
End __.
Module ___ <: RealSN_addon CCSN.
  Include CCSN.
End ___.
*)


(***********************************************************************************************)

(** * Building the generic model *)
Module SN := GenRealSN.MakeModel CCSN CCSN.
Import SN.

Module Lc := Lambda.

(***********************************************************************************************)

(** * Consistency out of the strong normalization model *)

(** If t belongs to all reducibility candidates, then it has a free variable *)
Lemma neutral_not_closed :
  forall t, (forall S, inSAT t S) -> exists k, Lc.occur k t.
intros.
assert (neu := H (exist _ _ Can.neutral_is_cand : SAT)).
simpl in neu.
destruct neu.
destruct H1.
destruct H2.
destruct Lc.nf_neutral_open with (1:=H2) (2:=H3).
exists x0.
apply Lc.red_closed with x; auto.
Qed.

(** Another consistency proof. *)

(** What is original is that it is based on the strong normalization model which
   precisely inhabits all types and propositions. We get out of this by noticing that
   non provable propositions contain no closed realizers. So, by a substitutivity
   invariant (realizers of terms typed in the empty context cannot introduce free
   variables), we derive the impossibility to derive absurdity in the empty context.

   The result is at the level of the model. See below for the proof that the actual syntax
   (libraries Term and TypeJudge) can be mapped to the model.
 *)
Theorem consistency : forall M, ~ typ List.nil M (Prod prop (Ref 0)).
red; intros.
red in H.
(* The valuation below contains only closed terms, and it interprets the
   empty context *) 
assert (val_ok List.nil (V.nil props) (I.nil (Lc.Abs (Lc.Ref 0)))).
 red; intros.
 destruct n; discriminate H0.
apply H in H0.
clear H.
red in H0; simpl in_int in H0.
destruct H0 as (_,H0).
simpl int in H0.
destruct H0.
set (prf := tm (I.nil (Lc.Abs (Lc.Ref 0))) M) in H0.
assert (forall S, inSAT (Lc.App prf (Lc.Abs (Lc.Ref 0))) S).
 intros.
 assert ([mkProp S, Lc.Abs (Lc.Ref 0)] \real props). 
  assert (mkProp S ∈ El props).
   rewrite El_props_def.
   exists S; reflexivity.
  split; trivial.
  rewrite Real_sort; auto.
  apply Lc.sn_abs; auto.
 assert (H2 := @prod_elim props (int(V.nil props) M) (mkProp S) (fun P=>P) prf (Lc.Abs (Lc.Ref 0))).
 destruct H2; trivial.
  red; auto.

  split; trivial.
 rewrite Real_mkProp in H3; trivial.
 unfold inX, prod in H.
 rewrite El_def in H.
 apply singl_elim.
 rewrite <- (El_mkProp S).
 apply cc_prod_elim with (1:=H).
 rewrite El_props_def.
  exists S; reflexivity.
destruct (neutral_not_closed _ H1).
inversion_clear H2.
 apply tm_closed in H3.
 apply H3.
 red; intros.
 unfold I.nil in H2; simpl in H2.
 inversion_clear H2.
 inversion H4.

 inversion_clear H3.
 inversion H2.
Qed.

Print Assumptions consistency.

(***********************************************************************************************)
(** * Strong Normalization on actual syntax *)

Require TypeJudge.

Module Ty := TypeJudge.
Module Tm := Term.

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

Hint Resolve int_not_kind Ty.eq_typ_not_kind.

(** Proof that beta-reduction at the Lc level simulates beta-reduction
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

Import Wellfounded.

Lemma sn_sound : forall M,
  Acc (transp _ red_term) (interp M) ->
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
  apply SN.typ_app with (V:=interp T); eauto.
  apply SN.typ_abs; eauto.
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
