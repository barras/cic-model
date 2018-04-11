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

(** ** Choice *)
(*Require Import ZFcoc SATtypes.
Module Lc:=Lambda.

Definition Ch (X:term) : term.
(* begin show *)
left;
exists (fun i => mkTY (trunc (El(int X i)))
                      (fun _ => depSAT(fun Y=>forall x,x ∈El(int X i)->
                                 inclSAT(cartSAT(Real (int X i) x)unitSAT) Y)
                                      (fun Y=>Y)))
       (fun j => tm X j).
(* end show *)
do 2 red; intros.
apply mkTY_ext; intros.
 rewrite H; auto with *.

 apply interSAT_morph_subset; simpl; intros; auto with *.
 apply fa_morph; intros z.
 rewrite H; reflexivity.

do 2 red; intros; apply tm_morph; auto with *.

red; intros; apply tm_liftable.
red; intros; apply tm_substitutive.
Defined.


Definition ChI (W:term) : term.
(* begin show *)
left; exists (fun i => empty) (fun j => COUPLE (tm W j) ID).
(* end show *)
do 2 red; intros; reflexivity.

do 2 red; intros.
f_equal; trivial.
apply tm_morph; auto with *.

 (**)
 red; intros.
 unfold COUPLE; simpl.
 rewrite tm_liftable.
 rewrite Lc.permute_lift; reflexivity.
 (**)
 red; intros.
 unfold COUPLE; simpl.
 rewrite tm_substitutive.
 rewrite Lc.commut_lift_subst; reflexivity.
Defined.

Lemma ChI_typ e X W :
  X <> kind ->
  typ e W X ->
  typ e (ChI W) (Ch X).
unfold typ.
intros Xnk tyW; intros.
apply in_int_intro; try discriminate.
apply and_split; simpl; intros.
 red; auto.

 red in H0; rewrite El_def in H0.
 specialize tyW with (1:=H).
 apply in_int_not_kind in tyW; trivial.
 destruct tyW.
 rewrite Real_def; intros; auto.
 2:apply interSAT_morph_subset; simpl; auto with *.
 apply interSAT_intro.
  exists snSAT; intros.
  red; intros; apply snSAT_intro.
  apply sat_sn in H4; trivial.

  intros (Y,?); simpl.
  apply i0 with (int W i); trivial.
  apply cartSAT_intro; trivial.
  apply ID_intro.
Qed.

Definition ChE (X C:term) : term.
  left; exists (fun i => ZFrepl.uchoice (fun x => x ∈ Elt (int X i)))
               (fun j => Lc.App (tm C j) (Lc.Abs (Lc.Abs (Lc.Ref 1)))).
  admit.
  admit.
  admit.
  admit.
Defined.

Lemma ChE_typ e W X :
  X <> kind ->
  typ e W (Ch X) ->
  typ e (ChE X W) X.
unfold typ; intros Xnk tyW i j valok.
specialize tyW with (1:=valok).
apply in_int_not_kind in tyW;[|discriminate].                     
destruct tyW as (tyW,satW).
red in tyW; simpl in tyW; rewrite El_def in tyW.
simpl in satW; rewrite Real_def in satW; trivial.
apply in_int_intro; trivial; try discriminate.
apply and_split; intros.
 red; simpl.
 apply cc_bot_intro.
 apply ZFrepl.uchoice_def.
 split.
  intros.
  rewrite <- H; trivial.
 split; intros.
  admit.
  admit.

 simpl.
 red in H; simpl in H.
 set (w:=ZFrepl.uchoice (fun x => x ∈ Elt(int X i))) in *.
 clearbody w.
 apply depSAT_elim' in satW.
 red in satW.
 eapply cartSAT_case with (X:=Real(int X i) w) (Y:=unitSAT).
 apply satW; intros.
 intros ? h; apply h.
 reflexivity.
 
 eexact (fun _ h => h). 
 assert (inSAT (tm W j) ; rewrite El_def in H.
split.

(** ** Unique choice *)

Definition Tr (X:term) : term.
(* begin show *)
left;
exists (fun i => mkTY (ZFcoc.trunc (El(int X i)))
                      (fun _ => interSAT(fun Y:{Y|forall x,x ∈El(int X i)->
                                           inclSAT(Real (int X i) x) Y}=>proj1_sig Y)))
       (fun j => tm X j).
(* end show *)
do 2 red; intros.
apply mkTY_ext; intros.
 rewrite H; auto with *.

 apply interSAT_morph_subset; simpl; intros; auto with *.
 apply fa_morph; intros z.
 rewrite H; reflexivity.

do 2 red; intros; apply tm_morph; auto with *.

red; intros; apply tm_liftable.
red; intros; apply tm_substitutive.
Defined.

Definition TrI (W:term) : term.
(* begin show *)
left; exists (fun i => empty) (fun j => tm W j).
(* end show *)
do 2 red; intros; reflexivity.

do 2 red; intros; apply tm_morph; auto with *.

red; intros; apply tm_liftable.
red; intros; apply tm_substitutive.
Defined.

Lemma TrI_typ e X W :
  X <> kind ->
  typ e W X ->
  typ e (TrI W) (Tr X).
unfold typ.
intros Xnk tyW; intros.
apply in_int_intro; try discriminate.
apply and_split; simpl; intros.
 red; auto.

 red in H0; rewrite El_def in H0.
 specialize tyW with (1:=H).
 apply in_int_not_kind in tyW; trivial.
 destruct tyW.
 rewrite Real_def; intros; auto.
  apply interSAT_intro' with (F:=fun X=>X); intros.
   apply sat_sn in H2; trivial.

   apply (H3 (int W i)); trivial.

  apply interSAT_morph_subset; simpl; auto with *.
Qed.

Definition TrE (X P F W:term) : term.
(* begin show *)
  left; exists (fun i => cond_set (int W i ∈ Elt (int (Tr X) i))
                                  (trunc_descr (El(int P i))))
               (fun j => Lambda.App (tm F j) (tm W j)).
(* end show *)
do 2 red; intros; rewrite H; reflexivity.

do 2 red; intros; rewrite H; reflexivity.

red; intros.
do 2 rewrite tm_liftable.
reflexivity.

red; intros.
do 2 rewrite tm_substitutive.
reflexivity.
Defined.

Definition EQ A t1 t2 :=
  Prod (Prod A prop) (Prod (App (Ref 0) (lift 1 t1)) (App (Ref 1) (lift 2 t2))).

Definition IsProp X :=
  Prod X (Prod (lift 1 X) (EQ (lift 2 X) (Ref 1) (Ref 0))).

Lemma TrE_typ e X P Pp F W :
  P <> kind ->
  typ e Pp (IsProp P) ->
  typ e F (Prod X (lift 1 P)) ->
  typ e W (Tr X) ->
  typ e (TrE X P F W) P.
unfold typ; intros Pnk tyPp tyF tyW i j valok.
specialize tyPp with (1:=valok); apply in_int_not_kind in tyPp;[|discriminate].
specialize tyF with (1:=valok); apply in_int_not_kind in tyF;[|discriminate].
specialize tyW with (1:=valok); apply in_int_not_kind in tyW;[|discriminate].
clear valok.
destruct tyPp as (isPp,_).
destruct tyF as (tyF,satF).
destruct tyW as (tyW,satW).  
apply in_int_intro; trivial; try discriminate.
split; simpl.
 red.
 rewrite Elt_def.
 red in tyW; simpl in tyW; rewrite El_def in tyW.
 apply cc_bot_ax in tyW; destruct tyW.
  admit.
 rewrite cond_set_ok; trivial.
 apply trunc_ind with (El(int X i)) (fun x => cc_app (int F i) x) (int W i); trivial.
  admit. (*!*)

  red; intros.
  admit.

 rewrite Elt_def.
  red; intros.

*)

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
