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

(** Another consistency proof. *)

Theorem consistency : forall M, ~ typ List.nil M (Prod prop (Ref 0)).
red; intros.
apply model_consistency with (FF:=mkTY (singl prf_trm) (fun _ => neuSAT)) in H;
  trivial.
 apply sn_sort_intro.
  reflexivity.

  apply one_in_props.

 intros.
 red in H0; rewrite El_def  in H0.
 rewrite Real_def; auto with *.
Qed.

Print Assumptions consistency.
