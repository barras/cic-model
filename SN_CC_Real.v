Require Export Relations Wellfounded.
Require Import Sat.
Require Import ZF ZFcoc ZFuniv_real.
Require Import ZFlambda.

(** Strong normalization proof of the Calculus of Constructions.
    It is based on GenRealSN, so it does support strong eliminations.
    Inhabitation of all types is obtained by adding the empty set in every
    type (cf ZFuniv_real). The product is interpreted by the set of *partial*
    functions.
 *)

Set Implicit Arguments.

(***********************************************************************)
(** First the model requirements *)

Require Import Models.
Module SN_CC_Model <: CC_Model.

Definition X:=set.
Definition inX x y := x ∈ El y.
Definition eqX := eq_set.
Lemma eqX_equiv : Equivalence eqX.
Proof eq_set_equiv.

Lemma in_ext: Proper (eqX ==> eqX ==> iff) inX.
do 3 red; intros.
unfold inX, El, eqX in *.
rewrite H; rewrite H0; reflexivity.
Qed.

Definition eq_fun (x:X) (f1 f2:X->X) :=
  forall y1 y2, inX y1 x -> y1 == y2 -> f1 y1 == f2 y2.


Definition lam := lam.
Definition app := app.

Lemma lam_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  lam x1 f1 == lam x2 f2.
intros.
apply cc_lam_ext; trivial.
apply El_morph; trivial.
Qed.

Definition app_ext := cc_app_morph.

Lemma prod_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  prod x1 f1 == prod x2 f2.
unfold prod, eqX, mkTY; intros.
apply couple_morph.
 apply cc_prod_ext; intros.
  apply El_morph; trivial.
  red; intros.
  apply El_morph; auto.

 apply cc_lam_ext.
  apply cc_bot_morph.
  apply cc_prod_ext; intros.
   apply El_morph; trivial.
   red; intros.
   apply El_morph; auto.

  red; intros.
  apply iSAT_morph.
  unfold piSAT.
  apply interSAT_morph_subset; simpl; intros.
   rewrite H; reflexivity.

   apply prodSAT_morph.
    apply Real_morph; auto with *.

    apply Real_morph; auto with *.
    rewrite H2; reflexivity.
Qed.

Definition prod_intro := prod_intro.
Definition prod_elim := prod_elim.
Definition prod := prod.
Definition props := sn_props.
Definition impredicative_prod := impredicative_prod.

Lemma beta_eq:
  forall dom F x,
  eq_fun dom F F ->
  inX x dom ->
  app (lam dom F) x == F x.
unfold app, lam, inX, eqX, El; intros.
apply cc_beta_eq; trivial.
Qed.

End SN_CC_Model.
Import SN_CC_Model.

(***********************************************************************)
(** Building the SN addon *)

Module SN_CC_addon.

  Definition Real : X -> X -> SAT := Real.

  Lemma Real_morph : Proper (eqX ==> eqX ==> eqSAT) Real.
Proof Real_morph.

  Lemma Real_sort P : inX P props -> eqSAT (Real props P) snSAT.
intros.
apply Real_sort_sn; trivial.
Qed.

  Lemma Real_prod : forall dom f F,
    eq_fun dom F F ->
    inX f (prod dom F) ->
    eqSAT (Real (prod dom F) f) (piSAT dom F (app f)).
Proof Real_prod.

  Definition daimon := empty.

  Lemma daimon_false : inX daimon (prod props (fun P => P)).
red; auto.
Qed.

Definition piSAT A (F:set->set) (f:set->set) :=
  interSAT (fun p:{x|x ∈ El A} =>
    prodSAT (Real A (proj1_sig p)) (Real (F (proj1_sig p)) (f (proj1_sig p)))).

End SN_CC_addon.


(***********************************************************************)
(*
----
*)

Require GenRealSN.
Module SN := GenRealSN.MakeModel SN_CC_Model SN_CC_addon.
Import SN.

(** Derived properties *)

Lemma val_ok_cons_default e T i j :
  val_ok e i j ->
  T <> kind ->
  val_ok (T::e) (V.cons empty i) (I.cons daimon j).
intros.
apply vcons_add_var; trivial.
split.
 red; auto.
 apply varSAT.
Qed.

Lemma El_int_prod U V i :
  El (int (Prod U V) i) == cc_prod (El (int U i)) (fun x => El (int V (V.cons x i))).
simpl.
apply El_prod.
do 2 red; intros.
rewrite H0; reflexivity.
Qed.

Lemma El_int_arr U V i :
  El (int (Prod U (lift 1 V)) i) == cc_arr (El (int U i)) (El (int V i)).
rewrite El_int_prod.
apply cc_prod_morph; auto with *.
red; intros.
rewrite int_cons_lift_eq; reflexivity.
Qed.

Lemma Real_int_prod U V i f :
  f ∈ cc_prod (El (int U i)) (fun x => El (int V (V.cons x i))) ->
  eqSAT (Real (int (Prod U V) i) f)
        (piSAT (int U i) (fun x => int V (V.cons x i)) (cc_app f)).
simpl; intros.
apply Real_prod.
 do 2 red; intros.
 rewrite H1; reflexivity.

 change (f ∈ El (int (Prod U V) i)).
 rewrite El_int_prod; trivial.
Qed.

Lemma Real_int_arr U V i f :
  f ∈ cc_arr (El (int U i)) (El (int V i)) ->
  eqSAT (Real (int (Prod U (lift 1 V)) i) f)
        (piSAT (int U i) (fun _ => int V i) (cc_app f)).
intros.
rewrite Real_int_prod.
 apply piSAT_morph; auto with *.
  red; intros.
  apply int_cons_lift_eq.

  red; intros; apply cc_app_morph; auto with *.

 revert H; apply eq_elim; apply cc_prod_ext; auto with *.
 red; intros.
 symmetry; apply El_morph; apply int_cons_lift_eq.
Qed.


(** ** Extendability *)
Definition cst (x:set) : trm.
(* begin show *)
left; exists (fun _ =>x) (fun _ =>Lambda.K).
(* end show *)
 do 2 red; reflexivity.
 do 2 red; reflexivity.
 red; reflexivity.
 red; reflexivity.
Defined.

Definition mkSET (x:set) := cst (mkTY x (fun _ => snSAT)).

Lemma mkSET_kind e x :
  typ e (mkSET x) kind.
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
  typ e (cst x) (mkSET y).
red; intros.
apply in_int_intro; intros; try discriminate.
apply and_split; intros.
 simpl.
 red; rewrite El_def.
 apply union2_intro2; trivial.

 simpl.
 unfold SN_CC_addon.Real; rewrite Real_def.
  apply Lambda.sn_K.

  reflexivity.

  apply union2_intro2; trivial.
Qed.
Lemma cst_eq_typ e x y :
  x == y ->
  eq_typ e (cst x) (cst y).
red; simpl; intros; trivial.
Qed.

Lemma cst_eq_typ_inv x y :
  eq_typ nil (cst x) (cst y) ->
  x == y.
intros.
assert (val_ok nil (V.nil empty) (I.nil Lambda.K)).
 red; intros.
 destruct n; inversion H0.
apply H in H0.
simpl in H0; trivial.
Qed.

Lemma mkSET_eq_typ e x y :
  x == y ->
  eq_typ e (mkSET x) (mkSET y).
red; simpl; intros; trivial.
apply mkTY_ext; auto with *.
Qed.

Lemma mkSET_eq_typ_inv x y :
  eq_typ nil (mkSET x) (mkSET y) ->
  x == y.
intros.
assert (val_ok nil (V.nil empty) (I.nil Lambda.K)).
 red; intros.
 destruct n; inversion H0.
apply H in H0.
simpl in H0.
apply couple_injection in H0; destruct H0; trivial.
Qed.


Definition sub_typ_covariant : forall e U1 U2 V1 V2,
  U1 <> kind ->
  eq_typ e U1 U2 ->
  sub_typ (U1::e) V1 V2 ->
  sub_typ e (Prod U1 V1) (Prod U2 V2).
intros.
apply sub_typ_covariant; trivial.
unfold eqX, inX; intros.
rewrite El_prod in H3; trivial.
apply cc_eta_eq in H3; trivial.
Qed.

(***********************************************************************************************)

(** * Consistency out of the strong normalization model *)

Module Lc := Lambda.

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

   The result is at the level of the model. See SN_CC_Real_syntax for the proof that
   the actual syntax (libraries Term and TypeJudge) can be mapped to the model
   and thus deriving the metatheoretical properties on the actual type of derivation.
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
set (prf := tm M (I.nil (Lc.Abs (Lc.Ref 0)))) in H0.
assert (forall S, inSAT (Lc.App prf (Lc.Abs (Lc.Ref 0))) S).
 intros.
 assert ([mkTY (singl empty) (fun _ => S), Lc.Abs (Lc.Ref 0)] \real props). 
  apply and_split; intros.
   red; apply sn_sort_intro; auto with *.

   unfold props, sn_props.
   rewrite Real_sort_sn; trivial.
   apply snSAT_intro; apply Lc.sn_abs; apply Lc.sn_var.
 assert (H2 := @prod_elim props (int M (V.nil props)) (mkTY (singl empty) (fun _ => S))
                  (fun P=>P) prf (Lc.Abs (Lc.Ref 0))).
 destruct H2; trivial.
  red; auto.

  split; trivial.

  rewrite Real_def in H3; auto with *.
  red in H2; rewrite El_def in H2; trivial.
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
