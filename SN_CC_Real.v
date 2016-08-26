Require Export Relations Wellfounded.
Require Import Sat.
Require Import ZF ZFcoc ZFuniv_real.
Require Import ZFlambda.
Require Import Models SnModels.
Require GenRealSN.
Set Implicit Arguments.

(** Strong normalization proof of the Calculus of Constructions.
    It is based on GenRealSN, so it does support strong eliminations.
    Inhabitation of all types is obtained by adding the empty set in every
    type (cf ZFuniv_real). The product is interpreted by the set of *partial*
    functions.
 *)

Module SN := GenRealSN.MakeModel CC_Real.
Export SN.
Hint Unfold inX.
Existing Instance in_ext.

(** Derived properties *)

Notation daimont := Sat.SatSet.daimon.

Lemma val_ok_cons_default e T i j :
  val_ok e i j ->
  T <> kind ->
  val_ok (T::e) (V.cons empty i) (I.cons daimont j).
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

Lemma kind_ok_trivial T : kind_ok T.
exists nil.
exists T; simpl; auto with *.
exists empty; auto with *.
Qed.
Hint Resolve kind_ok_trivial.

(** ** Extendability *)
Definition cst (x:set) : term.
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
split; trivial.
apply Lambda.sn_K.
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
 rewrite Real_def.
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

   unfold CC_Real.props.
   rewrite Real_sort_sn; trivial.
   apply snSAT_intro; apply Lc.sn_abs; apply Lc.sn_var.
 assert (H2 := @rprod_elim props (int M (V.nil props)) (mkTY (singl empty) (fun _ => S))
                  (fun P=>P) prf (Lc.Abs (Lc.Ref 0))).
 destruct H2; trivial.
  do 2 red; auto.

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
