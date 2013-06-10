(** Strong normalization of the model of CC+W in the type-based
  termination presentation.
*)

Require Import List Bool Models.
Require SN_ECC_Real.
Import ZFgrothendieck.
Import ZF ZFsum ZFnats ZFrelations ZFord ZFfix.
Require Import ZFfunext ZFfixrec ZFecc ZFuniv_real ZFind_w SATtypes SATw2.

Import SN_ECC_Real.
Import SN_ECC_Real.SN_CC_Model.
Import SN_ECC_Real.SN.
Opaque Real.
Import Sat Sat.SatSet.
Opaque inSAT.
Notation "'int0' x y" := (int y x) (at level 10, x at level 9, y at level 9).


Import ZFcoc.

Lemma cc_dec_intro x :
  x ⊆ cc_dec x.
red; intros.
apply union2_intro2; trivial.
Qed.

Lemma cc_prod_mt U V :
  ext_fun U V ->
  (forall x, x ∈ U -> empty ∈ V x) ->
  cc_dec (cc_prod U V) == cc_prod U V.
intros Vm Vmt.
unfold cc_dec.
apply eq_intro; intros.
 apply union2_elim in H; destruct H; trivial.
 apply singl_elim in H; rewrite H.
 assert (cc_lam U (fun _ => empty) == empty).
  apply cc_impredicative_lam; auto with *.
 rewrite <- H0.
 apply cc_prod_intro; auto with *.

 apply cc_dec_intro; trivial.
Qed.

Lemma cc_prod_ext_mt U V f :
  ext_fun (cc_dec U) V ->
  empty ∈ V empty ->
  ~ empty ∈ U ->
  f ∈ cc_prod U V ->
  f ∈ cc_prod (cc_dec U) V.
intros.
assert (f == cc_lam (cc_dec U) (cc_app f)).
 apply cc_prod_is_cc_fun in H2.
 apply eq_set_ax; intros z.
 rewrite cc_lam_def.
 2:do 2 red; intros; apply cc_app_morph; auto with *.
 split; intros.
  destruct (H2 _ H3).
  exists (fst z); [apply cc_dec_intro;trivial|].
  exists (snd z); trivial.
  rewrite <- couple_in_app.
  rewrite H4 in H3; trivial.

  destruct H3 as (x,xty,(y,yty,eqc)).
  rewrite eqc.
  rewrite couple_in_app; trivial.
rewrite H3; apply cc_prod_intro; trivial.
 do 2 red; intros; apply cc_app_morph; auto with *.

 intros.
 apply union2_elim in H4; destruct H4.
  apply singl_elim in H4.
  rewrite cc_app_outside_domain.
  2:apply cc_prod_is_cc_fun in H2; eexact H2.
   apply eq_elim with (V empty); trivial.
   apply H; auto with *.
   apply union2_intro1; apply singl_intro.

   rewrite H4; trivial.

 apply cc_prod_elim with (1:=H2); trivial.
Qed.



(*
Lemma Real_ax x t T R :
  (forall x x', x ∈ cc_dec T -> x==x' -> eqSAT (R x) (R x')) ->
  ([x,t] \real mkTY T R <-> x ∈ cc_dec T /\ inSAT t (R x)).
intros.
unfold inX; rewrite El_def.
split; destruct 1; split; trivial; rewrite Real_def in *; auto with *.
Qed.
*)


Lemma El_int_prod U V i :
  El (int0 (Prod U V) i) == cc_prod (El (int0 U i)) (fun x => El (int0 V (V.cons x i))).
simpl.
unfold prod, ZFuniv_real.prod.
rewrite El_def.
rewrite cc_prod_mt; auto with *.
do 2 red; intros.
rewrite H0; reflexivity.
Qed.

Lemma El_int_arr U V i :
  El (int0 (Prod U (lift 1 V)) i) == cc_arr (El (int0 U i)) (El (int0 V i)).
rewrite El_int_prod.
apply cc_prod_morph; auto with *.
red; intros.
rewrite int_cons_lift_eq; reflexivity.
Qed.

Lemma Real_int_prod U V i f :
  f ∈ cc_prod (El (int0 U i)) (fun x => El (int0 V (V.cons x i))) ->
  eqSAT (Real (int0 (Prod U V) i) f)
        (piSAT (int0 U i) (fun x => int0 V (V.cons x i)) (cc_app f)).
simpl; intros.
rewrite Real_prod.
 reflexivity.

 red; intros.
 rewrite H1; reflexivity.

 change (f ∈ El (int0 (Prod U V) i)).
 rewrite El_int_prod; trivial.
Qed.
Lemma Real_int_arr U V i f :
  f ∈ cc_arr (El (int0 U i)) (El (int0 V i)) ->
  eqSAT (Real (int0 (Prod U (lift 1 V)) i) f)
        (piSAT (int0 U i) (fun _ => int0 V i) (cc_app f)).
simpl; intros.
rewrite Real_prod.
 apply piSAT_morph; auto with *.
  red; intros.
  apply int_cons_lift_eq.

  red; intros; apply cc_app_morph; auto with *.

 red; intros.
 rewrite H1; reflexivity.

 change (f ∈ El (int0 (Prod U (lift 1 V)) i)).
 rewrite El_int_arr; trivial.
Qed.

(** Derived rules of the basic judgements *)

Lemma eq_typ_betar : forall e N T M,
  typ e N T ->
  T <> kind ->
  eq_typ e (App (Abs T M) N) (subst N M).
intros.
apply eq_typ_beta; trivial.
 reflexivity.
 reflexivity.
Qed.

Lemma typ_var0 : forall e n T,
  match T, nth_error e n with
    Some _, value T' => T' <> kind /\ sub_typ e (lift (S n) T') T
  | _,_ => False end ->
  typ e (Ref n) T.
intros.
case_eq T; intros.
 rewrite H0 in H.
case_eq (nth_error e n); intros.
 rewrite H1 in H.
 destruct H.
 apply typ_subsumption with (lift (S n) t); auto.
  apply typ_var; trivial.

  destruct t as [(t,tm)|]; simpl; try discriminate.
  elim H; trivial.

  discriminate.

 rewrite H1 in H; contradiction.
 rewrite H0 in H; contradiction.
Qed.


(** Subtyping *)

(*
Definition sub_typ_covariant : forall e U1 U2 V1 V2,
  U1 <> kind ->
  eq_typ e U1 U2 ->
  sub_typ (U1::e) V1 V2 ->
  sub_typ e (Prod U1 V1) (Prod U2 V2).
intros.
apply sub_typ_covariant; trivial.
intros.
unfold eqX, lam, app.
unfold inX in H2.
unfold prod, ZFuniv_real.prod in H2; rewrite El_def in H2.
apply cc_eta_eq in H2; trivial.
Qed.
*)

(** Universes *)
(*
Lemma cumul_Type : forall e n, sub_typ e (type n) (type (S n)).
red; simpl; intros.
red; intros.
apply ecc_incl; trivial.
Qed.

Lemma cumul_Prop : forall e, sub_typ e prop (type 0).
red; simpl; intros.
red; intros.
apply G_trans with props; trivial.
 apply (grot_succ_typ gr).

 apply (grot_succ_in gr).
Qed.
*)

(** Ordinals *)

Definition Ordt (o:set) : trm :=
  cst (mkTY o (fun _ => snSAT)) Lc.K (fun _ _ => eq_refl) (fun _ _ _ => eq_refl).

Definition typ_ord_kind : forall e o, typ e (Ordt o) kind.
red; simpl; intros.
split; [|split]; simpl.
 discriminate.

 exists nil; exists (Ordt o);[reflexivity|].
 exists zero; intros; simpl.
 unfold inX; rewrite El_def; trivial.

 apply union2_intro1.
 apply singl_intro.

 apply Lc.sn_K.
Qed.

Lemma El_int_ord o i :
  zero ∈ o ->
  El (int0 (Ordt o) i) == o.
intros; simpl.
rewrite El_def.
apply eq_intro; intros.
 apply union2_elim in H0; destruct H0; trivial.
 apply singl_elim in H0; rewrite H0; trivial.

 apply union2_intro2; trivial.
Qed.

Definition OSucc : trm -> trm.
(*begin show*)
intros o; left; exists (fun i => osucc (int i o)) (fun j => tm j o).
(*end show*)
 do 2 red; intros.
 rewrite H; reflexivity.
 (**)
 do 2 red; intros.
 rewrite H; reflexivity.
 (**)
 red; intros.
 apply tm_liftable.
 (**)
 red; intros.
 apply tm_substitutive.
Defined.

Definition OSucct : trm -> trm.
(*begin show*)
intros o; left; exists (fun i => mkTY (osucc (int i o)) (fun _ => snSAT)) (fun j => tm j o).
(*end show*)
 do 2 red; intros.
 apply mkTY_ext; auto with *.
 rewrite H; reflexivity.
 (**)
 do 2 red; intros.
 rewrite H; reflexivity.
 (**)
 red; intros.
 apply tm_liftable.
 (**)
 red; intros.
 apply tm_substitutive.
Defined.

Lemma El_int_osucc O' i :
  El (int0 (OSucct O') i) == osucc (int0 O' i).
simpl; rewrite El_def.
apply eq_intro; intros.
 apply union2_elim in H; destruct H; trivial.
 apply singl_elim in H; rewrite H.
 apply ole_lts; auto.
 red; intros.
 apply empty_ax in H0; contradiction.

 apply union2_intro2; trivial.
Qed.

Lemma tyord_inv : forall e i j o o',
  isOrd o' ->
  zero ∈ o' ->
  typ e o (Ordt o') ->
  val_ok e i j ->
  isOrd (int i o) /\ int i o < o' /\ Lc.sn (tm j o).
unfold typ; intros.
specialize H1 with (1:=H2).
apply in_int_not_kind in H1.
2:discriminate.
destruct H1.
red in H1; rewrite El_int_ord in H1; trivial.
split;[apply isOrd_inv with o'; trivial|].
split; trivial.
apply sat_sn in H3; trivial.
Qed.

(** W *)

Lemma TR_morph_gen' F F' o o' :
  (forall f f' oo oo',
   (forall ooo ooo', isOrd ooo -> ooo==ooo' -> f ooo == f' ooo') ->
   isOrd oo ->
   oo == oo' ->
   F f oo == F' f' oo') ->
 isOrd o ->
 o == o' ->
 TR F o == TR F' o'.
intros.
unfold TR.
apply ZFrepl.uchoice_morph_raw.
red; intros.
unfold TR_rel.
apply and_iff_morphism.
 rewrite H1; reflexivity.
apply fa_morph; intro P.
apply fa_morph; intro Pm.
apply impl_morph; intros.
 apply fa_morph; intro oo.
 apply fa_morph; intro f.
 apply fa_morph; intro oo_.
 apply impl_morph; [rewrite H1;auto with *|intro].
 apply impl_morph; [auto with *|intro fm].
 apply impl_morph; [auto with *|intros _].
 apply Pm; auto with *.

 rewrite H1; rewrite H2; reflexivity.
Qed.

Instance TR_morph_gen :
  Proper (((eq_set==>eq_set)==>eq_set==>eq_set)==>eq_set==>eq_set) TR.
do 4 red; intros.
unfold TR.
apply ZFrepl.uchoice_morph_raw.
red; intros.
unfold TR_rel.
apply and_iff_morphism.
 rewrite H0; reflexivity.
apply fa_morph; intro P.
apply fa_morph; intro Pm.
apply impl_morph; intros.
 apply fa_morph; intro o'.
 apply fa_morph; intro f.
 apply impl_morph; [auto with *|intro].
 apply impl_morph; [auto with *|intro].
  rewrite H0; reflexivity.
 apply fa_morph; intros fm.
 apply fa_morph; intros _.
 apply Pm; auto with *.
 apply H; auto with *.

 rewrite H1; rewrite H0; reflexivity.
Qed.

Instance TI_morph_gen :
  Proper ((eq_set==>eq_set)==>eq_set==>eq_set) TI.
do 3 red; intros.
unfold TI.
apply TR_morph_gen; trivial.
do 2 red; intros.
apply sup_morph; trivial.
red; intros.
apply H; apply H1; trivial.
Qed.


Lemma rWi_ext X X' Y Y' RX RX' RY RY' o o' x x' :
  X == X' ->
  ZF.eq_fun X Y Y' ->
  (eq_set==>eqSAT)%signature RX RX' ->
  (forall x x', x ∈ X -> x==x' -> (eq_set==>eqSAT)%signature (RY x) (RY' x')) ->
  isOrd o ->
  o == o' ->
  x == x' ->
  eqSAT (rWi X Y RX RY o x) (rWi X' Y' RX' RY' o' x').
intros.
unfold rWi.
unfold tiSAT.
apply ZFlambda.sSAT_morph.
apply cc_app_morph; trivial.
apply TR_morph_gen'; intros; auto with *.
apply sup_morph; auto.
red; intros.
apply cc_lam_ext.
 apply TI_morph_gen.
  red; intros.
  apply W_F_ext; trivial.
  apply cc_dec_morph; trivial.

  apply osucc_morph; trivial.

 red; intros.
 assert (x0o: isOrd x0) by eauto using isOrd_inv.
 apply ZFlambda.iSAT_morph.
 unfold rW.
 unfold sigmaReal.
 apply interSAT_morph.
 apply indexed_relation_id; intros C.
 apply prodSAT_morph; auto with *.
 apply piSAT0_morph; intros.
  red; intros.
  rewrite H12; reflexivity.

  apply H1; reflexivity.

  assert (x2 ∈ X).
   assert (ext_fun X Y).
    apply eq_fun_ext in H0; trivial.
   apply TI_elim in H11; auto with *.
    destruct H11 as (ooo,?,?).
    apply W_F_elim in H16; trivial.
    destruct H16 as (?,_).
    rewrite H13 in H16.
    rewrite fst_def in H16; trivial.

    do 2 red; intros.
    apply W_F_morph; trivial.
    rewrite H16; reflexivity.
  apply prodSAT_morph; auto with *.
  apply piSAT0_morph; intros.
   red; intros.
   apply eq_set_ax.
   apply H0; auto with *.

   apply H2; auto with *.

   apply condSAT_morph.
    rewrite H12; reflexivity.

    apply ZFlambda.sSAT_morph.
    apply cc_app_morph.
     apply H6; trivial.

     rewrite H12; reflexivity.
Qed.

Instance rWi_morph_gen : Proper
  (eq_set==>(eq_set==>eq_set)==>(eq_set==>eqSAT)==>(eq_set==>eq_set==>eqSAT)==>eq_set==>eq_set==>eqSAT) rWi.
do 7 red; intros.
unfold rWi.
unfold tiSAT.
apply ZFlambda.sSAT_morph.
apply cc_app_morph; trivial.
apply TR_morph_gen; trivial.
do 3 red; intros.
apply sup_morph; auto.
red; intros.
apply cc_lam_ext.
 apply TI_morph_gen.
  red; intros.
  apply W_F_ext; trivial.
   red; intros; auto with *.

   apply cc_dec_morph; trivial.

  apply osucc_morph; trivial.

 red; intros.
 apply ZFlambda.iSAT_morph.
 unfold rW.
 unfold sigmaReal.
 apply interSAT_morph.
 apply indexed_relation_id; intros C.
 apply prodSAT_morph; auto with *.
 apply piSAT0_morph; intros.
  red; intros.
  rewrite H10; reflexivity.

  apply H1; reflexivity.

  apply prodSAT_morph; auto with *.
  apply piSAT0_morph; intros.
   red; intros.
   apply eq_set_ax.
   apply H0; reflexivity.

   apply H2; reflexivity.

   apply condSAT_morph.
    rewrite H10; reflexivity.

    apply ZFlambda.sSAT_morph.
    apply cc_app_morph.
     apply H5; trivial.

     rewrite H10; reflexivity.
Qed.

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


Section Wtypes_typing.

Variable o : set.
Hypothesis oo : isOrd o.
Hypothesis oz : zero ∈ o.

Variable e:env.

Variable A B:trm.
Hypothesis Atyp : typ e A kind.
Hypothesis Btyp : typ (A::e) B kind.

Let Aw i := El (int0 A i).
Let Bw i x := El (int0 B (V.cons x i)).
Let Ww i := W (Aw i) (Bw i).

Let RAw i a := Real (int0 A i) a.
Let RBw i a b := Real (int0 B (V.cons a i)) b.

Definition WF' i X := W_F (Aw i) (Bw i) (cc_dec X).

Definition RW i o w := rWi (Aw i) (Bw i) (RAw i) (RBw i) o w.

Instance Aw_morph : Proper (eq_val==>eq_set) Aw.
do 2 red; intros.
apply El_morph.
apply int_morph; auto with *.
Qed.

Instance Bw_morph : Proper (eq_val==>eq_set==>eq_set) Bw.
do 3 red; intros.
apply El_morph.
rewrite H; rewrite H0; reflexivity.
Qed.

Instance RAw_morph : Proper (eq_val ==> eq_set ==> eqSAT) RAw.
do 3 red; intros.
unfold RAw.
rewrite H; rewrite H0; reflexivity.
Qed.

Instance RBw_morph : Proper (eq_val ==> eq_set ==> eq_set ==> eqSAT) RBw.
do 4 red; intros.
unfold RBw.
rewrite H; rewrite H0; rewrite H1; reflexivity.
Qed.


Instance WF'_morph : Proper (eq_val ==> eq_set ==> eq_set) WF'.
do 3 red; intros.
unfold WF', W_F.
apply sigma_morph.
 apply Aw_morph; trivial.

 red; intros.
 apply cc_arr_morph.
  apply Bw_morph; trivial.

  apply union2_morph; auto with *.
Qed.

Instance RW_morph : Proper (eq_val ==> eq_set ==> eq_set ==> eqSAT) RW.
do 4 red; intros.
unfold RW.
apply rWi_morph_gen; auto with *.
 apply Aw_morph; trivial.
 apply Bw_morph; trivial.
 apply RAw_morph; trivial.
 apply RBw_morph; trivial.
Qed.

Definition WI (O:trm) : trm.
(*begin show*)
left; exists (fun i => mkTY (TI (WF' i) (int0 O i)) (RW i (int0 O i)))
             (fun j => Lc.App2 Lc.K (tm j A) (Lc.App2 Lc.K (Lc.Abs(tm (Lc.ilift j) B)) (tm j O))).
(*end show*)
 do 2 red; intros.
 apply mkTY_ext; intros.
  apply TI_morph_gen.
   apply WF'_morph; trivial.
   rewrite H; reflexivity.

  apply RW_morph; trivial.
  rewrite H; reflexivity.
 (**)
 do 2 red; intros.
 rewrite H; reflexivity.
 (**)
 red; intros.
 simpl.
 rewrite <- tm_liftable.
 rewrite <- tm_liftable.
 rewrite <- tm_liftable.
 unfold Lc.App2.
 f_equal.
 f_equal.
 f_equal.
 f_equal.
 apply tm_morph; auto with *.
 apply Lc.ilift_binder_lift.
 (**)
 red; intros.
 simpl.
 rewrite <- tm_substitutive.
 rewrite <- tm_substitutive.
 rewrite <- tm_substitutive.
 unfold Lc.App2.
 f_equal.
 f_equal.
 f_equal.
 f_equal.
 apply tm_morph; auto with *.
 apply Lc.ilift_binder.
Defined.

Lemma El_int_W O i :
  El (int0 (WI O) i) == cc_dec (TI (WF' i) (int0 O i)).
simpl.
rewrite El_def; reflexivity.
Qed.
Lemma Real_int_W O i x :
  x ∈ cc_dec (TI (WF' i) (int0 O i)) ->
  eqSAT (Real (int0 (WI O) i) x) (RW i (int0 O i) x).
simpl; intros.
rewrite Real_def; auto with *.
intros.
rewrite H1; reflexivity.
Qed.

Lemma typ_WI : forall eps O,
  isOrd eps ->
  typ e O (Ordt eps) ->
  typ e (WI O) kind.
red; intros; simpl.
red in H0; specialize H0 with (1:=H1).
assert (tyA := Atyp _ _ H1).
apply in_int_not_kind in H0.
2:discriminate.
destruct tyA as (Ank,(_,snA)).
destruct (Btyp _ _ (val_ok_cons_default _ _ _ _ H1 Ank)) as (Bnk,(_,snB)).
split;[|split].
 discriminate.

 exists nil; exists (WI O);[reflexivity|].
 exists empty; simpl; auto.
 red; auto.

 simpl.
 apply real_sn in H0.
 apply Lc.sn_K2; trivial.
 apply Lc.sn_K2; trivial.
 apply Lc.sn_abs.
 rewrite tm_subst_cons in snB.
 apply Lc.sn_subst in snB; trivial.
Qed.
(** Constructor *)

Definition Wc (x:trm) (f:trm) : trm.
(* begin show *)
left; exists (fun i => couple (int0 x i) (int0 f i))
             (fun j => WC (tm j x) (tm j f)).
(* end show *)
 do 2 red; intros; apply couple_morph; apply int_morph; auto with *.
 (**)
 do 2 red; intros.
 rewrite H; reflexivity.
 (**)
 red; intros.
 unfold WC, COUPLE; simpl.
 do 2 rewrite tm_liftable.
 do 2 rewrite Lc.permute_lift; reflexivity.
 (**)
 red; intros.
 unfold WC, COUPLE; simpl.
 do 2 rewrite tm_substitutive.
 do 2 rewrite Lc.commut_lift_subst; reflexivity.
Defined.



Lemma typ_Wc : forall O X F,
  typ e O (Ordt o) ->
  typ e X A ->
  typ e F (Prod (subst X B) (lift 1 (WI O))) ->
  typ e (Wc X F) (WI (OSucc O)).
red; intros.
red in H0; specialize H0 with (1:=H2).
apply in_int_not_kind in H0.
2:destruct (Atyp _ _ H2); trivial.
red in H1; specialize H1 with (1:=H2).
apply in_int_not_kind in H1.
2:discriminate.
destruct tyord_inv with (3:=H)(4:=H2) as (?,(?,_)); trivial.
apply in_int_intro; try discriminate.
assert (couple (int0 X0 i) (int0 F i) ∈ TI (WF' i) (osucc (int0 O i))).
 apply TI_intro with (int0 O i); auto.
  apply WF'_morph; reflexivity.

  unfold W_F.
  apply couple_intro_sigma.
   do 2 red; intros.
   rewrite H6; reflexivity.

   apply H0.

   destruct H1.
   red in H1; rewrite El_int_arr in H1.
   rewrite El_int_W in H1.
   rewrite <- int_subst_eq in H1.
   trivial.
split.
 red; rewrite El_int_W.
 apply union2_intro2; trivial.

 rewrite Real_int_W; trivial.
 2:apply union2_intro2; trivial.
 simpl.
 unfold RW; apply Real_WC; auto with *.
  apply Bw_morph; reflexivity.
  apply RAw_morph; reflexivity.
  apply RBw_morph; reflexivity.

  rewrite fst_def.
  apply H0.

  destruct H1.
  red in H1; rewrite El_int_prod in H1.
  rewrite Real_int_prod in H6; trivial.
  revert H6; apply piSAT0_morph; intros.
   red; intros.
   rewrite fst_def.
   rewrite <- int_subst_eq; reflexivity.

   rewrite fst_def.
   rewrite <- int_subst_eq; reflexivity.

   rewrite int_cons_lift_eq.
   rewrite Real_int_W.
    unfold RW; apply rWi_morph; auto with *.
     apply RAw_morph; reflexivity.

     rewrite snd_def; reflexivity.

    apply cc_prod_elim with (2:=H7) in H1.
    rewrite int_cons_lift_eq in H1.
    rewrite El_int_W in H1; trivial.
Qed.

(* Case analysis *)


Definition W_CASE b w :=
  sigma_case (fun x f => app (app b x) f) w.

Definition Wcase (b n : trm) : trm.
(*begin show*)
left; exists (fun i => sigma_case (fun x f => app (app (int0 b i) x) f) (int0 n i))
             (fun j => WCASE (tm j b) (tm j n)).
(*end show*)
do 2 red; intros.
apply cond_set_morph.
 rewrite H; reflexivity.
 rewrite H; reflexivity.
(**)
do 2 red; intros.
unfold WCASE; rewrite H; reflexivity.
(**)
red; intros; simpl.
unfold WCASE; simpl.
do 2 rewrite tm_liftable; reflexivity.
(**)
red; intros; simpl.
unfold WCASE; simpl.
do 2 rewrite tm_substitutive; reflexivity.
Defined.

Instance Wcase_morph :
  Proper (eq_trm ==> eq_trm ==> eq_trm) Wcase.
do 3 red; intros.
split; red; simpl; intros.
 unfold sigma_case.
 apply cond_set_morph.
  rewrite H0; rewrite H1; reflexivity.
  rewrite H; rewrite H0; rewrite H1; reflexivity.

 rewrite H; rewrite H0; rewrite H1; reflexivity.
Qed.

Existing Instance Wcase_morph.

Lemma Wcase_iota : forall X F G,
  eq_typ e (Wcase G (Wc X F)) (App (App G X) F).
red; intros.
simpl.
rewrite sigma_case_couple with (a:=int0 X0 i) (b:=int0 F i).
 reflexivity.

 do 3 red; intros.
 rewrite H0; rewrite H1; reflexivity.

 reflexivity.
Qed.


Lemma typ_Wcase : forall P O G n,
  typ e O (Ordt o) ->
  typ e G (Prod A (Prod (Prod B (lift 2 (WI O))) (App (lift 2 P) (Wc (Ref 1) (Ref 0))))) ->
  typ e n (WI (OSucc O)) ->
  typ e (Wcase G n) (App P n).
red; intros.
destruct tyord_inv with (3:=H)(4:=H2) as (?,(?,_ )); trivial.
red in H0; specialize H0 with (1:=H2).
apply in_int_not_kind in H0;[|discriminate].
red in H1; specialize H1 with (1:=H2).
apply in_int_not_kind in H1;[|discriminate].
apply in_int_intro; try discriminate.
destruct H0; red in H0.
rewrite El_int_prod in H0.
rewrite Real_int_prod in H5; trivial.
destruct H1; red in H1.
rewrite El_int_W in H1.
rewrite Real_int_W in H6; trivial.
apply and_split; intros.
 red; simpl.
 apply union2_elim in H1; destruct H1.
  apply singl_elim in H1.
  unfold sigma_case.
  rewrite H1.
  rewrite cond_set_mt.
   apply union2_intro1; apply singl_intro.

   apply discr_mt_pair.   

  simpl in H1; rewrite TI_mono_succ in H1; auto with *.
  2:apply Wf_mono; trivial.
  2:apply Bw_morph; reflexivity.
  assert (fst (int0 n i) ∈ Aw i).
   apply fst_typ_sigma in H1; trivial.
  assert (snd (int0 n i) ∈ cc_arr (Bw i (fst (int0 n i))) (cc_dec (TI (WF' i) (int0 O i)))).
   apply snd_typ_sigma with (y:=fst(int0 n i)) in H1; auto with *.
   do 2 red; intros.
   rewrite H9; reflexivity.
  assert (int0 n i == couple (fst (int0 n i)) (snd (int0 n i))).
   apply (surj_pair _ _ _ (subset_elim1 _ _ _ H1)).
  unfold sigma_case.
  rewrite cond_set_ok; trivial.
  specialize cc_prod_elim with (1:=H0) (2:=H7); clear H0; intro H0.
  rewrite El_int_prod in H0.
  apply eq_elim with (El
     (app (int0 (lift 2 P) (V.cons (snd (int0 n i)) (V.cons (fst (int0 n i)) i)))
        (couple (fst (int0 n i)) (snd (int0 n i))))).
   apply El_morph.
   apply app_ext; auto with *.
   rewrite split_lift; do 2 rewrite int_cons_lift_eq; reflexivity.

   apply cc_prod_elim with (1:=H0).
   rewrite split_lift.
   rewrite El_int_arr.
   revert H8; apply eq_elim.
   apply cc_arr_morph.
    reflexivity.

    rewrite int_cons_lift_eq.
    rewrite El_int_W; reflexivity.

 simpl in H6|-*.
 apply union2_elim in H1; destruct H1.
  (* neutral case *)
  apply singl_elim in H1.
  rewrite H1 in H6.
  unfold WCASE.
  eapply prodSAT_elim;[|apply H5].
  revert H6; unfold RW; apply rWi_neutral; auto with *.
   apply Bw_morph; reflexivity.
   apply RAw_morph; reflexivity.

  (* regular case *)
  eapply Real_WCASE with (5:=H1) (6:=H6)
    (C:=fun x => Real (app (int0 P i) x) (sigma_case (fun x f => app (app (int0 G i) x) f) x));
     auto with *.
   apply Bw_morph; reflexivity.
   apply RAw_morph; reflexivity.

   do 2 red; intros.
   unfold sigma_case.
   rewrite H8.
   reflexivity.

   revert H5; apply piSAT0_morph; intros.
    red; intros; reflexivity.

    reflexivity.

    specialize cc_prod_elim with (1:=H0) (2:=H8); clear H0; intro H0.
    rewrite El_int_prod in H0.
    rewrite Real_int_prod; trivial.
    apply piSAT0_morph; intros.
     red; intros.
     rewrite split_lift.
     rewrite El_int_arr.
     apply in_set_morph; auto with *.
     apply cc_arr_morph.
      reflexivity.

      rewrite int_cons_lift_eq.
      rewrite El_int_W; reflexivity.

     rewrite split_lift.
     rewrite Real_int_arr; trivial.
      apply piSAT0_morph; intros.
       red; intros.
       reflexivity.

       reflexivity.

       specialize cc_arr_elim with (1:=H9) (2:=H11); clear H9; intro H9.
       rewrite int_cons_lift_eq.
       rewrite Real_int_W; trivial.
       reflexivity.

      revert H10; apply eq_elim.
      rewrite split_lift.
      rewrite El_int_arr; reflexivity.

     apply Real_morph.
      simpl.
      rewrite split_lift; do 2 rewrite int_cons_lift_eq.
      reflexivity.

      rewrite sigma_case_couple; [| |reflexivity].
       reflexivity.

       do 3 red; intros.
       rewrite H11; rewrite H12; reflexivity.
Qed.
(*Print Assumptions typ_Wcase.*)

Lemma typ_Wcase' : forall P O G n T,
  T <> kind ->
  typ e O (Ordt o) ->
  sub_typ e (App P n) T -> 
  typ e G (Prod A (Prod (Prod B (lift 2 (WI O))) (App (lift 2 P) (Wc (Ref 1) (Ref 0))))) ->
  typ e n (WI (OSucc O)) ->
  typ e (Wcase G n) T.
intros.
apply typ_subsumption with (App P n); auto.
2:discriminate.
apply typ_Wcase with O; trivial.
Qed.

End Wtypes_typing.

(********************************************************************************)
(** Occurrences *)


  (* Non-occurrence : interp do not depend on variables in set [f] *)
  Definition noccur (f:nat->bool) (T:trm) : Prop :=
    forall i i',
    (forall n, if f n then True else i n == i' n) ->
    int i T == int i' T.

  Lemma noc_var : forall f n, f n = false -> noccur f (Ref n).
red; simpl; intros.
specialize (H0 n).
rewrite H in H0; trivial.
Qed.

  Lemma noc_kind : forall f, noccur f kind.
red; simpl; reflexivity.
Qed.

  Lemma noc_prop : forall f, noccur f prop.
red; simpl; reflexivity.
Qed.

  Lemma noc_app : forall f a b,
    noccur f a -> noccur f b -> noccur f (App a b).
unfold noccur; simpl; intros.
rewrite (H _ _ H1).
rewrite (H0 _ _ H1).
reflexivity.
Qed.


(********************************************************************************)
(** Judgements with variance *)

Module Beq.
Definition t := bool.
Definition eq := @eq bool.
Definition eq_equiv : Equivalence eq := eq_equivalence.
Existing Instance eq_equiv.
End Beq.
Module B := VarMap.Make(Beq).

Module OTeq.
Definition t := option trm.
Definition eq := @eq (option trm).
Definition eq_equiv : Equivalence eq := eq_equivalence.
Existing Instance eq_equiv.
End OTeq.
Module OT := VarMap.Make(OTeq).

(* Environments with tags on ordinal and recursive function variables *)
Record fenv := {
  tenv : env;
  ords : B.map; (* variables denoting ordinals *)
  fixs : OT.map (* variables denoting recursive functions with their domain *)
}.

Definition tinj e :=
  Build_fenv e (B.nil false) (OT.nil None).

Definition push_var e T :=
  Build_fenv (T::tenv e) (B.cons false (ords e)) (OT.cons None (fixs e)).

Definition push_fun e dom rng :=
  Build_fenv (Prod dom rng::tenv e)
    (B.cons false (ords e)) (OT.cons (Some dom) (fixs e)).

Definition push_ord e T :=
  Build_fenv (T::tenv e) (B.cons true (ords e)) (OT.cons None (fixs e)).


(* Additional judgments for fix body *)
Definition val_mono (e:fenv) i j i' j' :=
    val_ok (tenv e) i j /\
    val_ok (tenv e) i' j' /\
    forall n,
    if ords e n then i n ⊆ i' n
    else match fixs e n with
      Some T => forall x, x ∈ El(int (V.shift (S n) i) T) -> app (i n) x == app (i' n) x
    | _ => i n == i' n
    end.

Lemma val_mono_refl : forall e i j,
  val_ok (tenv e) i j -> val_mono e i j i j.
split;[idtac|split]; simpl; auto with *.
intro n.
destruct (ords e n); auto with *.
destruct (fixs e n); auto with *.
Qed.

Lemma val_push_var : forall e i j i' j' x t x' t' T,
  val_mono e i j i' j' ->
  x == x' ->
  [x,t] \real int i T ->
  [x',t'] \real int i' T ->
  T <> kind ->
  val_mono (push_var e T) (V.cons x i) (I.cons t j) (V.cons x' i') (I.cons t' j').
destruct 1 as (?&?&?); split;[idtac|split]; trivial.
 unfold push_var; simpl.
 apply vcons_add_var; trivial.

 unfold push_var; simpl.
 apply vcons_add_var; trivial.

 destruct n as [|n]; simpl; auto.
 generalize (H1 n).
 destruct (ords e n); trivial.
Qed.

Lemma val_push_ord : forall e i j i' j' x t x' t' T,
  val_mono e i j i' j' ->
  x ⊆ x' ->
  [x,t] \real int i T ->
  [x',t'] \real int i' T ->
  T <> kind ->
  val_mono (push_ord e T) (V.cons x i) (I.cons t j) (V.cons x' i') (I.cons t' j').
destruct 1 as (?&?&?); split;[idtac|split]; trivial.
 unfold push_ord; simpl.
 apply vcons_add_var; trivial.

 unfold push_ord; simpl.
 apply vcons_add_var; trivial.

 destruct n as [|n]; simpl; auto.
 generalize (H1 n).
 destruct (ords e n); trivial.
Qed.


Lemma val_push_fun : forall e i j i' j' f tf g tg T U,
  val_mono e i j i' j' ->
  [f,tf] \real int0 (Prod T U) i ->
  [g,tg] \real int0 (Prod T U) i' ->
  fcompat (El(int i T)) f g ->
  val_mono (push_fun e T U) (V.cons f i) (I.cons tf j) (V.cons g i') (I.cons tg j').
destruct 1 as (?&?&?); split;[idtac|split]; trivial.
 unfold push_fun; simpl.
 apply vcons_add_var; trivial.
 discriminate.

 unfold push_fun; simpl.
 apply vcons_add_var; trivial.
 discriminate.

 destruct n as [|n]; simpl; auto.
 generalize (H1 n).
 destruct (ords e n); trivial.
Qed.

(** Function Extension judgment *)
Definition fx_extends e dom M :=
  forall i i' j j', val_mono e i j i' j' ->
  fcompat (El(int i dom)) (int i M) (int i' M).

(** Covariance judgment *)
Definition fx_sub e M :=
  forall i i' j j', val_mono e i j i' j' ->
  forall x t, [x,t] \real int i M -> [x,t] \real int i' M.

Definition fx_subval e M :=
  forall i i' j j', val_mono e i j i' j' -> int i M ⊆ int i' M.

(** Invariance *)
Definition fx_equals e M :=
  forall i i' j j', val_mono e i j i' j' -> int i M == int i' M.


Lemma El_sub e T i j i' j':
  fx_sub e T ->
  val_mono e i j i' j' ->
  El (int0 T i) ⊆ El (int0 T i').
intros.
apply H in H0.
red; intros.
apply H0 with daimon.
split;[trivial|apply varSAT].
Qed.
Lemma El_eq e T i j i' j':
  fx_equals e T ->
  val_mono e i j i' j' ->
  El (int0 T i) == El (int0 T i').
intros.
apply H in H0.
rewrite H0; reflexivity.
Qed.


Definition spec_var e n :=
  ords e n || match fixs e n with Some _ => true | _ => false end.

  Lemma fx_eq_noc : forall e t,
    noccur (spec_var e) t ->
    fx_equals e t.
unfold noccur, fx_equals, spec_var; intros.
apply H; intros.
destruct H0 as (_,(_,H0)).
generalize (H0 n).
destruct (ords e n); simpl; trivial.
destruct (fixs e n); simpl; trivial.
Qed.

  Lemma fx_eq_app : forall e u v,
    fx_equals e u ->
    fx_equals e v ->
    fx_equals e (App u v).
unfold fx_equals; intros.
specialize H with (1:=H1).
specialize H0 with (1:=H1).
simpl.
rewrite H; rewrite H0; reflexivity.
Qed.

  Lemma fx_eq_abs : forall e T M,
    T <> kind ->
    fx_equals e T ->
    fx_equals (push_var e T) M ->
    fx_equals e (Abs T M).
unfold fx_equals; intros.
simpl.
apply lam_ext; eauto.
red; intros.
apply H1 with (I.cons daimon j) (I.cons daimon j').
specialize H0 with (1:=H2).
apply val_push_var; auto.
 split; trivial.
 apply varSAT.

 split.
 2:apply varSAT.
 unfold inX; rewrite <- H4; rewrite <- H0; trivial.
Qed.

  Lemma fx_eq_rec_call : forall e n x T U,
    ords e n = false ->
    fixs e n = Some T ->
    T <> kind ->
    typ (tenv e) (Ref n) (Prod (lift (S n) T) U) ->
    fx_equals e x ->
    typ (tenv e) x (lift (S n) T) ->
    fx_equals e (App (Ref n) x).
unfold fx_equals; intros.
simpl.
specialize H3 with (1:=H5).
rewrite <- H3.
destruct H5 as (Hty,(Hty',Hrec)).
specialize Hrec with n.
rewrite H in Hrec; rewrite H0 in Hrec.
apply Hrec.
red in H4; specialize H4 with (1:=Hty); trivial.
apply in_int_not_kind in H4; trivial.
2:destruct T;[discriminate|elim H1;reflexivity].
destruct H4 as (?,_ ).
unfold inX in H4.
unfold lift in H4; rewrite int_lift_rec_eq in H4.
rewrite V.lams0 in H4; trivial.
Qed.

  (* Covariance *)

  Lemma fx_equals_subval : forall e M, fx_equals e M -> fx_subval e M.
unfold fx_subval, fx_equals; intros.
apply H in H0.
rewrite <- H0; reflexivity.
Qed.

  Lemma fx_equals_sub : forall e M, fx_equals e M -> fx_sub e M.
unfold fx_sub, fx_equals; intros.
apply H in H0.
destruct H1.
split.
 red.
 rewrite <- H0; trivial.

 rewrite <- H0; trivial.
Qed.

  Lemma var_sub : forall e n,
    ords e n = true ->
    fx_subval e (Ref n).
unfold fx_subval; intros.
destruct H0 as (_,(_,H0)).
generalize (H0 n); rewrite H.
simpl; trivial.
Qed.

Lemma fx_sub_prod : forall e T U,
  T <> kind ->
  fx_equals e T ->
  fx_sub (push_var e T) U ->
  fx_sub e (Prod T U).
red; intros.
red in H0; specialize H0 with (1:=H2).
destruct H3.
red in H3.
rewrite El_int_prod in H3.
rewrite Real_int_prod in H4; trivial.
apply and_split; intros.
 red; rewrite El_int_prod.
 revert H3; apply cc_prod_covariant; intros.
  do 2 red; intros.
  rewrite H5; reflexivity.

  rewrite H0; reflexivity.

  apply El_sub with (1:=H1) (j:=I.cons daimon j) (j':=I.cons daimon j').
  apply val_push_var; auto with *.
   split;[trivial|apply varSAT].
   split;[|apply varSAT].
   red; rewrite <- H0; trivial.

 red in H5; rewrite El_int_prod in H5.
 rewrite Real_int_prod; trivial.
 apply interSAT_intro' with
   (F:=fun v => prodSAT(Real(int i' T) v)(Real(int(V.cons v i') U)(cc_app x v))).
  apply sat_sn in H4; trivial.
 intros.
 rewrite <- H0 in H6.
 specialize interSAT_elim with (1:=H4) (x:=exist (fun x=> x ∈ El(int0 T i)) x0 H6); simpl proj1_sig; intros.
 revert H7; apply prodSAT_mono.
  do 2 red; intros.
  rewrite <- H0 in H7; trivial.

  red; intros.
  apply H1 with (i:=V.cons x0 i) (j:=I.cons daimon j) (j':=I.cons daimon j').
   apply val_push_var; auto with *.
   split; trivial; apply varSAT.
   split.
    red; rewrite <- H0; trivial.
    apply varSAT.

   split; trivial.
   unfold inX; apply cc_prod_elim with (1:=H3); trivial.
Qed.


  Lemma Wi_sub : forall e o A B O,
    isOrd o ->
    zero ∈ o ->
    A <> kind ->
    typ (tenv e) O (Ordt o) ->
    fx_equals e A ->
    fx_equals (push_var e A) B ->
    fx_subval e O ->
    fx_sub e (WI A B O).
unfold fx_sub, fx_subval.
intros e o A B O oo oz Ank tyO eqA eqB subO i i' j j' val_m x t (xreal,xsat).
destruct tyord_inv with (3:=tyO) (4:=proj1 val_m); trivial.
destruct tyord_inv with (3:=tyO) (4:=proj1 (proj2 val_m)); trivial.
red in eqA; specialize eqA with (1:=val_m).
specialize subO with (1:=val_m).
red in xreal; rewrite El_int_W in xreal.
rewrite Real_int_W in xsat; trivial.
assert (cc_dec (TI (WF' A B i) (int0 O i)) ⊆ cc_dec (TI (WF' A B i') (int0 O i'))).
 apply union2_mono; auto with *.
 transitivity (TI (WF' A B i') (int0 O i)).
  intro; apply eq_elim.
  apply TI_morph_gen; auto with *.
  red; intros.
  apply W_F_ext; auto with *.
   apply El_morph; trivial.

   red; intros.
   apply El_morph.
   apply eqB with (I.cons daimon j) (I.cons daimon j').
    apply val_push_var; auto with *.
    split; [trivial|apply varSAT].
    rewrite H5 in H4.
    rewrite eqA in H4.
    split; [trivial|apply varSAT].

   apply cc_dec_morph; trivial.

  destruct H0; destruct H2.
  apply TI_mono; trivial.
  do 2 red; intros; apply W_F_mono.
   do 2 red; intros.
   rewrite H7; reflexivity.

   apply union2_mono; auto with *.
split.
 red; rewrite El_int_W; auto.

 rewrite Real_int_W; auto.
 apply union2_elim in xreal; destruct xreal as [H4|xreal].
  apply singl_elim in H4.
  assert (eqSAT (RW A B i (int0 O i) x) (RW A B i (int0 O i) empty)).
   unfold RW; apply rWi_morph; auto with *.
   do 2 red; intros.
   rewrite H5; reflexivity.
 rewrite H5 in xsat.
 revert xsat; unfold RW; apply rWi_neutral; trivial.
  apply Bw_morph; reflexivity.
  apply RAw_morph; reflexivity.

 setoid_replace (RW A B i' (int0 O i') x) with (RW A B i (int0 O i) x); trivial.
 symmetry; transitivity (RW A B i (int0 O i') x).
  unfold RW; apply rWi_mono; trivial.
   apply Bw_morph; reflexivity.
   apply RAw_morph; reflexivity.

  unfold RW; apply rWi_ext; trivial; intros.
   apply El_morph; trivial.

   red; intros.
   eapply El_eq with (1:=eqB).
   apply val_push_var; eauto.
    split;[trivial|apply varSAT].
    split;[rewrite eqA in H4;rewrite H5 in H4;trivial|apply varSAT].
 
   do 2 red; intros.
   rewrite eqA; rewrite H4; reflexivity.

   do 2 red; intros.
   apply Real_morph; trivial.
   eapply eqB.
   apply val_push_var; eauto.
    split;[trivial|apply varSAT].
    split;[rewrite eqA in H4;rewrite H5 in H4;trivial|apply varSAT].

  reflexivity.
  reflexivity.
Qed.

  Lemma OSucc_sub : forall e O,
    fx_subval e O ->
    fx_subval e (OSucc O).
unfold fx_subval; simpl; intros.
unfold osucc.
red; intros.
rewrite subset_ax in H1 |-*.
destruct H1; split; auto.
revert H1; apply power_mono.
eauto.
Qed.

  (* Function subtyping *)

  Lemma fx_abs : forall e U T M,
    T <> kind ->
    fx_sub e T ->
    fx_equals (push_var e T) M ->
    typ (T::tenv e) M U ->
    U <> kind ->
    fx_extends e T (Abs T M).
unfold fx_equals, fx_extends; intros.
specialize El_sub with (1:=H0)(2:=H4); clear H0; intro H0.
simpl.
red; intros.
rewrite beta_eq; try assumption.
 assert (H5' := H0 _ H5).
 rewrite beta_eq; trivial.
  apply H1 with (I.cons daimon j) (I.cons daimon j').
  apply val_push_var; auto with *.
   split; [trivial|apply varSAT].

   split; [trivial|apply varSAT].

  red; red; intros.
  rewrite H7; reflexivity.

 red; red; intros.
 rewrite H7; reflexivity.
Qed.

(*****************************************************************************)
(** Recursor (without case analysis) *)

(* WFix O M is a fixpoint of domain WI O with body M *)
Definition WFix (O M:trm) : trm.
(*begin show*)
left.
exists (fun i =>
         WREC (fun o' f => int (V.cons f (V.cons o' i)) M) (int i O))
       (fun j => WFIX (Lc.Abs (tm (Lc.ilift (I.cons (tm j O) j)) M))).
(*end show*)
 do 2 red; intros.
 unfold WREC.
 unfold REC.
 apply TR_morph_gen.
 2:rewrite H; reflexivity.
 do 2 red; intros.
 apply sup_morph; trivial.
 red; intros.
 apply int_morph; auto with *.
 apply V.cons_morph.
  apply H0; trivial.
 apply V.cons_morph; trivial.

 (* *)
 do 2 red; intros.
 rewrite H; reflexivity.

 (* *)
 red; intros.
 replace (Lc.lift_rec 1
     (WFIX (Lc.Abs (tm (Lc.ilift (I.cons (tm j O) j)) M))) k) with
   (WFIX (Lc.lift_rec 1 (Lc.Abs (tm (Lc.ilift (I.cons (tm j O) j)) M)) k)).
  simpl.
  f_equal.
  f_equal.
  rewrite <- tm_liftable.
  apply tm_morph; auto with *.
  rewrite <- Lc.ilift_binder_lift.
  apply Lc.ilift_morph.
  intros [|k']; simpl; trivial.
  apply tm_liftable.

  generalize  (Lc.Abs (tm (Lc.ilift (I.cons (tm j O) j)) M)); intro.
  unfold WFIX, FIXP; simpl.
  rewrite <- Lc.permute_lift.
  reflexivity.

 (* *)
 red; intros.
 replace (Lc.subst_rec u
     (WFIX (Lc.Abs (tm (Lc.ilift (I.cons (tm j O) j)) M))) k) with
   (WFIX (Lc.subst_rec u (Lc.Abs (tm (Lc.ilift (I.cons (tm j O) j)) M)) k)).
  simpl.
  f_equal.
  f_equal.
  rewrite <- tm_substitutive.
  apply tm_morph; auto with *.
  rewrite <- Lc.ilift_binder.
  apply Lc.ilift_morph.
  intros [|k']; simpl; trivial.
  apply tm_substitutive.

  generalize  (Lc.Abs (tm (Lc.ilift (I.cons (tm j O) j)) M)); intro.
  unfold WFIX, FIXP; simpl.
  rewrite <- Lc.commut_lift_subst.
  reflexivity.
Defined.


(** Typing rules of WFix *)

Section WFixRules.

  Variable infty : set.
  Hypothesis infty_ord : isOrd infty.
  Hypothesis infty_nz : zero ∈ infty.
  Variable E : fenv.
  Let e := tenv E.
  Variable A B O U M : trm.
  Hypothesis A_nk : A <> kind.
  Hypothesis Aeq : fx_equals E A.
  Hypothesis Beq : fx_equals (push_var E A) B.

  Definition WIL n := WI (lift n A) (lift_rec n 1 B).

  Hypothesis ty_O : typ e O (Ordt infty).
  Hypothesis ty_M : typ (Prod (WIL 1 (Ref 0)) U::OSucct O::e)
    M (Prod (WIL 2 (OSucc (Ref 1)))
         (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U)))).

  Hypothesis stab : fx_extends
    (push_fun (push_ord E (OSucct O)) (WIL 1 (Ref 0)) U)
    (WIL 2 (OSucc (Ref 1)))
    M.

Definition squash f := subset f (fun c => ~ fst c == empty).

Instance squash_morph : morph1 squash.
do 2 red; intros.
apply subset_morph; auto with *.
Qed.

  Let Wi i o := cc_dec (TI (WF' A B i) o).
  Let F i := fun o' f =>
    squash (int (V.cons f (V.cons o' i)) M).

  Lemma morph_fix_body : forall i, morph2 (F i).
unfold F; do 3 red; intros.
rewrite H; rewrite H0; reflexivity.
Qed.

  Lemma ext_fun_ty : forall o i,
    ext_fun (Wi i o) (fun x => int (V.cons x (V.cons o i)) U).
do 2 red; intros.
rewrite H0;reflexivity.
Qed.

  Hypothesis fx_sub_U :
    fx_sub (push_var (push_ord E (OSucct O)) (WIL 1 (OSucc (Ref 0)))) U.


Lemma El_int_W_lift O' n i :
  El (int0 (WIL n O') i) == cc_dec (TI (WF' A B (V.shift n i)) (int0 O' i)).
unfold WIL; rewrite El_int_W.
apply cc_dec_morph.
apply TI_morph_gen; auto with *.
red; intros.
unfold WF'; apply W_F_ext; auto with *.
 rewrite int_lift_eq; reflexivity.

 red; intros.
 rewrite int_lift_rec_eq.
 rewrite <- V.cons_lams.
 2:apply V.shift_morph; trivial.
 rewrite V.lams0.
 rewrite H1; reflexivity.

 rewrite H; reflexivity.
Qed.

Lemma Real_int_W_lift O' n i x :
  x ∈ cc_dec (TI (WF' A B (V.shift n i)) (int0 O' i)) ->
  eqSAT (Real (int0 (WIL n O') i) x) (RW A B (V.shift n i) (int0 O' i) x).
intros.
unfold WIL; rewrite Real_int_W.
 unfold RW.
 apply rWi_morph_gen; auto with *.
  rewrite int_lift_eq; reflexivity.

  red; intros.
  rewrite int_lift_rec_eq.
  rewrite <- V.cons_lams.
  2:apply V.shift_morph; trivial.
  rewrite V.lams0.
  rewrite H0; reflexivity.

  red; intros.
  rewrite H0; rewrite int_lift_eq; reflexivity.

  do 2 red; intros.
  rewrite H1; rewrite int_lift_rec_eq.
  rewrite <- V.cons_lams.
  2:apply V.shift_morph; trivial.
  rewrite V.lams0.
  rewrite H0; reflexivity.

 revert H; apply eq_elim.
 apply cc_dec_morph.
 apply TI_morph_gen; auto with *.
 red; intros.
 unfold WF'; apply W_F_ext.
  rewrite int_lift_eq; reflexivity.

  red; intros.
  rewrite H1; rewrite int_lift_rec_eq.
  rewrite <- V.cons_lams.
  2:apply V.shift_morph; trivial.
  rewrite V.lams0.
  reflexivity.

  apply cc_dec_morph; trivial.
Qed.



  Lemma val_mono_2 i j y y' n n':
    val_ok e i j ->
    isOrd (int0 O i) ->
    isOrd y ->
    isOrd y' ->
    y ⊆ y' ->
    y' ⊆ int0 O i ->
    n ∈ Wi i y ->
    n == n' ->
    val_mono (push_var (push_ord E (OSucct O)) (WIL 1 (OSucc (Ref 0))))
      (V.cons n (V.cons y i)) (I.cons daimon (I.cons daimon j))
      (V.cons n' (V.cons y' i)) (I.cons daimon (I.cons daimon j)).
Proof.
intros.
apply val_push_var; auto with *.
 4:discriminate.
 apply val_push_ord; auto with *.
  4:discriminate.
  apply val_mono_refl; trivial.

  split;[|apply varSAT].
  red; rewrite El_int_osucc.
  apply ole_lts; auto.
  transitivity y'; trivial.

  split;[|apply varSAT].
  red; rewrite El_int_osucc.
  apply ole_lts; auto.

 split;[|apply varSAT].
 red; rewrite El_int_W_lift.
 revert H5; apply cc_dec_mono.
 apply TI_incl; simpl; auto.
 do 2 red; intros; apply W_F_mono; auto with *.
  do 2 red; intros.
  rewrite H8; reflexivity.

  apply cc_dec_mono; trivial.

 split;[|apply varSAT].
 red; rewrite El_int_W_lift.
 rewrite <- H6.
 revert H5; apply cc_dec_mono.
 apply TI_incl; simpl; auto.
  do 2 red; intros; apply W_F_mono; auto with *.
   do 2 red; intros.
   rewrite H8; reflexivity.

   apply cc_dec_mono; trivial.

  apply ole_lts; trivial.
Qed.


  Lemma fix_codom_mono : forall o o' x x' i j,
   val_ok e i j ->
   isOrd o' ->
   o' ⊆ int i O ->
   isOrd o ->
   o ⊆ o' ->
   x ∈ Wi i o ->
   x == x' ->
   El (int (V.cons x (V.cons o i)) U) ⊆ El(int (V.cons x' (V.cons o' i)) U).
Proof.
intros.
red in fx_sub_U.
assert (val_mono (push_var (push_ord E (OSucct O)) (WIL 1(OSucc(Ref 0))))
  (V.cons x (V.cons o i)) (I.cons daimon (I.cons daimon j))
  (V.cons x' (V.cons o' i)) (I.cons daimon (I.cons daimon j))).
 apply val_mono_2; trivial.
 apply ty_O in H.
 apply in_int_not_kind in H;[|discriminate].
 destruct H; red in H; rewrite El_int_ord in H; trivial.
 apply isOrd_inv with infty; auto.
red; intros.
apply fx_sub_U with (x:=z)(t:=daimon) in H6.
 destruct H6; trivial.

 split; trivial.
 apply varSAT.
Qed.

  Lemma ty_fix_body : forall i j o f,
   val_ok e i j ->
   o < osucc (int i O) ->
   f ∈ cc_prod (Wi i o) (fun x => El(int (V.cons x (V.cons o i)) U)) ->
   F i o f ∈
   cc_prod (Wi i (osucc o)) (fun x => El(int (V.cons x (V.cons (osucc o) i)) U)).
unfold F; intros.
destruct tyord_inv with (3:=ty_O) (4:=H); trivial.
assert (val_ok (Prod (WIL 1 (Ref 0)) U::OSucct O::e)
  (V.cons f (V.cons o i)) (I.cons daimon (I.cons daimon j))).
 apply vcons_add_var; auto.
 3:discriminate.
  apply vcons_add_var; auto.
  2:discriminate.
  split;[|apply varSAT].
  red; simpl; rewrite El_def; apply union2_intro2; trivial.

  split;[|apply varSAT].
  red; rewrite El_int_prod.
  revert H1; apply eq_elim.
  apply cc_prod_ext.
   rewrite El_int_W_lift.
   reflexivity.

   red; intros.
   rewrite H4; reflexivity.
red in ty_M.
specialize ty_M with (1:=H4).
apply in_int_not_kind in ty_M.
2:discriminate.
destruct ty_M as (?,_).
red in H5; rewrite El_int_prod in H5.
revert H5; apply eq_elim.
symmetry; apply cc_prod_ext.
 rewrite El_int_W_lift.
 reflexivity.

 red; intros.
 rewrite int_lift_rec_eq.
 rewrite int_subst_rec_eq.
 rewrite int_lift_rec_eq.
 apply El_morph; apply int_morph; auto with *.
 do 2 red.
 intros [|[|k]].
  compute; trivial.

  unfold V.lams, V.shift; simpl.
  reflexivity.

  unfold V.lams, V.shift; simpl.
  replace (k-0) with k; auto with *.
Qed.



  Lemma fix_body_irrel : forall i j,
    val_ok e i j ->
    Wi_ord_irrel' (El (int0 A i))
      (fun x => El (int0 B (V.cons x i))) (int i O) (F i) (fun o' x => El(int0 U (V.cons x (V.cons o' i)))).
red; intros.
assert (isOrd (int0 O i)).
 apply ty_O in H.
 apply isOrd_inv with infty; auto.
 apply in_int_not_kind in H;[|discriminate].
 destruct H.
 red in H; rewrite El_int_ord in H; trivial.
red in stab.
assert (Hstab := stab (V.cons f (V.cons o i)) (V.cons g (V.cons o' i))).
red in Hstab.
red; intros.
eapply Hstab; clear Hstab; trivial.
 apply val_push_fun.
  apply val_push_ord; auto.
   apply val_mono_refl; exact H.

   split;[|apply varSAT].
   red; rewrite El_int_osucc.
   apply ole_lts; trivial.
   transitivity o'; trivial.

   split;[|apply varSAT].
   red; rewrite El_int_osucc.
   apply ole_lts; trivial.

   discriminate.

  split;[|apply varSAT].
  red; rewrite El_int_prod.
  apply cc_prod_ext_mt in H4.
   revert H4; apply eq_elim; apply cc_prod_ext; intros.
    rewrite El_int_W_lift; reflexivity.

    red; intros.
    rewrite H9; reflexivity.

   do 2 red; intros.
   rewrite H10; reflexivity.

   apply union2_intro1; apply singl_intro.

   intro h; apply mt_not_in_W_F in h; auto with *.
   do 2 red; intros.
   rewrite H9; reflexivity.

  split;[|apply varSAT].
  red; rewrite El_int_prod.
  apply cc_prod_ext_mt in H5.
   revert H5; apply eq_elim; apply cc_prod_ext; intros.
    rewrite El_int_W_lift; reflexivity.

    red; intros.
    rewrite H9; reflexivity.

   do 2 red; intros.
   rewrite H10; reflexivity.

   apply union2_intro1; apply singl_intro.

   intro h; apply mt_not_in_W_F in h; auto with *.
   do 2 red; intros.
   rewrite H9; reflexivity.

  red; intros.
  rewrite El_int_W_lift in H9.
  apply union2_elim in H9; destruct H9.
   apply singl_elim in H9.
   rewrite H9.
   rewrite cc_app_outside_domain with (1:=cc_prod_is_cc_fun _ _ _ H4).
    rewrite cc_app_outside_domain with (1:=cc_prod_is_cc_fun _ _ _ H5);[reflexivity|].
    intro.
    apply mt_not_in_W_F in H10; auto with *.
    apply Bw_morph; reflexivity.

    intro.
    apply mt_not_in_W_F in H10; auto with *.
    apply Bw_morph; reflexivity.

   apply H6; trivial.

 rewrite El_int_W_lift.
 apply cc_dec_intro; trivial.
Qed.

  Hint Resolve morph_fix_body ext_fun_ty ty_fix_body fix_codom_mono fix_body_irrel.


Let fix_typ o i j:
  val_ok e i j ->
  isOrd o ->
  isOrd (int i O) ->
  o ⊆ int i O ->
  WREC (F i) o
   ∈ cc_prod (Wi i o) (fun n => El (int (V.cons n (V.cons o i)) U)).
intros.
apply cc_prod_ext_mt.
 do 2 red; intros.
 rewrite H4; reflexivity.

 apply union2_intro1; apply singl_intro.

 intro h; apply mt_not_in_W_F in h; auto with *.
 do 2 red; intros.
 rewrite H3; reflexivity.
eapply WREC_wt' with (U':=fun o n => El(int(V.cons n (V.cons o i))U)); trivial.
 do 2 red; intros.
 apply Bw_morph; auto with *.

 intros.
 apply fix_codom_mono with (1:=H); trivial.
 transitivity o; trivial.
 apply cc_dec_intro; trivial.

 intros.

 admit. (* F.. empty == empty *)
(* intros; apply ty_fix_body with (1:=H); trivial.
 apply isOrd_plump with (int i O); auto.
  transitivity o; trivial.

  apply lt_osucc; trivial.*)

 red; intros; apply fix_body_irrel with (1:=H); trivial.
 transitivity o; trivial.
Qed.

  Lemma fix_irr i j o o' x :
    val_ok e i j ->
    isOrd o ->
    isOrd o' ->
    isOrd (int i O) ->
    o ⊆ o' ->
    o' ⊆ int i O ->
    x ∈ Wi i o ->
    cc_app (WREC (F i) o) x == cc_app (WREC (F i) o') x.
intros.
assert (WRECi := WREC_irrel').
red in WRECi.
apply union2_elim in H5; destruct H5.
 apply singl_elim in H5.
admit.
(* rewrite cc_app_outside_domain with (dom:=TI (WF' A B i) o).
  symmetry; eapply cc_app_outside_domain with (TI (WF' A B i) o').
  eapply cc_prod_is_cc_fun.
  eapply WREC_wt' with (U':=fun o n => El(int(V.cons n (V.cons o i))U)); trivial.
   do 2 red; intros.
   rewrite H7; reflexivity.

   intros.
   apply fix_codom_mono with (1:=H); trivial.
    transitivity o'; trivial.
    apply cc_dec_intro; trivial.

   intros.
   apply ty_fix_body with (1:=H).*)

apply WRECi with 
  (A:=El (int0 A i)) (B:=fun x=>El(int0 B (V.cons x i)))
  (ord:=int i O)
  (U':=fun o x => El (int0 U (V.cons x (V.cons o i)))); auto with *.
 do 2 red; intros.
 rewrite H7; reflexivity.

 intros.
 apply fix_codom_mono with (1:=H); trivial.
 apply cc_dec_intro.
 trivial.

 intros.
(* apply ty_fix_body with (1:=H); trivial.
*)
 admit. (* Pb *)
(* apply isOrd_plump with (int i O); auto.
 apply lt_osucc; trivial.*)

 red; intros.
 apply fix_body_irrel with (1:=H); trivial.
Qed.



Lemma fix_eqn : forall i j o n,
  val_ok e i j ->
  isOrd o ->
  isOrd (int i O) ->
  o ⊆ int i O ->
  n ∈ Wi i (osucc o) ->
  cc_app (WREC (F i) (osucc o)) n ==
  cc_app (int (V.cons (WREC (F i) o) (V.cons o i)) M) n.
intros.
unfold WREC at 1.
rewrite REC_eq; auto with *.
apply cc_app_morph; auto with *.
apply incl_eq.
 red; intros.
 rewrite sup_ax in H4; auto with *.
 destruct H4.
 assert (xo : isOrd x) by eauto using isOrd_inv.
 assert (xle : x ⊆ o) by (apply olts_le; auto).
 assert (xle' : x ⊆ int i O) by (transitivity o; trivial).
 assert (F i x (REC (F i) x) ∈ 
         cc_prod (Wi i (osucc x)) (fun n => El (int (V.cons n (V.cons (osucc x) i)) U))).
  apply ty_fix_body with (1:=H); trivial.
   apply ole_lts; auto.

   apply fix_typ with (1:=H); trivial.
 assert (F i o (WREC (F i) o) ∈ 
         cc_prod (Wi i (osucc o)) (fun n => El (int (V.cons n (V.cons (osucc o) i)) U))).
  apply ty_fix_body with (1:=H).
   apply ole_lts; trivial.

   apply fix_typ with (1:=H); trivial.
 rewrite cc_eta_eq with (1:=H6) in H5.
 unfold F at 1 in H7; rewrite cc_eta_eq with (1:=H7).
 rewrite cc_lam_def in H5|-*.
  destruct H5.
  destruct H8.
  exists x0.
   revert H5; apply cc_dec_mono; apply TI_mono; auto with *.
    do 2 red; intros; apply W_F_mono.
     do 2 red; intros.
     rewrite H11; reflexivity.

     apply cc_dec_mono; trivial.

    apply osucc_mono; auto.
  exists x1; trivial.
  revert H8; apply eq_elim.
  do 2 red in stab.
  apply stab with (I.cons daimon (I.cons daimon j)) (I.cons daimon (I.cons daimon j)).
   apply val_push_fun.
    apply val_push_ord; trivial.
     apply val_mono_refl; trivial.

     split;[|apply varSAT].
     unfold inX; rewrite El_int_osucc.
     apply ole_lts; auto.

     split;[|apply varSAT].
     unfold inX; rewrite El_int_osucc.
     apply ole_lts; auto.

     discriminate.

    split;[|apply varSAT].
    red; rewrite El_int_prod.
    eapply eq_elim.
    2:eapply fix_typ with (1:=H); auto.
    apply cc_prod_ext.
     rewrite El_int_W_lift.
     reflexivity.

     red; intros.
     rewrite H10; reflexivity.

    split;[|apply varSAT].
    red; rewrite El_int_prod.
    eapply eq_elim.
    2:eapply fix_typ with (1:=H); auto.
    apply cc_prod_ext.
     rewrite El_int_W_lift.
     reflexivity.

     red; intros.
     rewrite H10; reflexivity.

    red; intros.
    apply fix_irr with (1:=H); auto with *.
    rewrite El_int_W_lift in H8; trivial.

   rewrite El_int_W_lift; simpl; trivial.

  do 2 red; intros; apply cc_app_morph; auto with *.
  do 2 red; intros; apply cc_app_morph; auto with *.

 apply sup_incl with (F:=fun o'=>F i o'(REC (F i) o')); auto with *.
 apply lt_osucc; trivial.
Qed.


Lemma wfix_eqn : forall i j,
  val_ok e i j ->
  WREC (F i) (int i O) ==
  cc_lam (Wi i (int i O))
    (fun x => cc_app (F i (int i O) (WREC (F i) (int i O))) x).
intros.
destruct tyord_inv with (3:=ty_O) (4:=H); trivial.
admit.
(*apply WREC_eqn with
  (A:=El(int0 A i))(B:=fun x => El(int0 B (V.cons x i))) 
  (ord:=int i O)
  (U:=fun o x => El (int0 U (V.cons x (V.cons o i)))); auto.
 intros.
 apply fix_codom_mono with (1:=H); trivial.

 intros; apply ty_fix_body with (1:=H); trivial.
 apply isOrd_plump with (int i O); auto.
 apply lt_osucc; trivial.

 red; intros; apply fix_body_irrel with (1:=H); trivial.
*)
Qed.


Lemma typ_wfix :
  typ e (WFix O M) (Prod (WI A B O) (subst_rec O 1 U)).
red; intros.
destruct tyord_inv with (3:=ty_O)(4:=H); trivial.
apply in_int_intro.
discriminate.
discriminate.
apply and_split; intros.
 red; rewrite El_int_prod.
 eapply eq_elim.
 2:simpl.
 2:apply fix_typ with (1:=H); auto with *.
 apply cc_prod_ext.
  rewrite El_int_W.
  reflexivity.

  red; intros.
  rewrite int_subst_rec_eq.
  rewrite <- V.cons_lams.
  2:apply V.cons_morph; reflexivity.
  rewrite V.lams0.
  rewrite H3; reflexivity.

 red in H2; rewrite El_int_prod in H2; trivial.
 rewrite Real_int_prod; trivial.
 simpl tm.
 cut (inSAT (WFIX (Lc.Abs (tm (Lc.ilift (I.cons (tm j O) j)) M)))
       (piSAT0 (fun n => n ∈ Wi i (int0 O i)) (RW A B i (int0 O i))
          (fun n =>Real (int0 U (V.cons n (V.cons (int0 O i) i)))
                    (cc_app (WREC (F i) (int0 O i)) n)))).
  unfold piSAT.
  apply interSAT_morph_subset; intros.
   rewrite El_int_W; reflexivity.

   apply prodSAT_morph.
    rewrite Real_int_W; simpl; trivial.
    reflexivity.

    simpl.
    rewrite int_subst_rec_eq.
    apply Real_morph.
     apply int_morph; auto with *.
     intros [|[|k]]; reflexivity.

     reflexivity.

unfold RW.
apply WFIX_sat with
   (X:=fun o n => Real (int0 U (V.cons n (V.cons o i)))
     (cc_app (WREC (F i) o) n)); trivial.
 do 2 red; intros.
 rewrite H3; reflexivity.

 do 2 red; intros.
 rewrite H3; reflexivity.

 red; intros.
 apply fx_sub_U with (V.cons n (V.cons y i))
    (I.cons daimon (I.cons daimon j)) (I.cons daimon (I.cons daimon j)).
  apply val_mono_2; auto with *.

  apply and_split; intros.
   red; rewrite <- fix_irr with (1:=H) (o:=y); auto.
   apply cc_prod_elim with (dom:=Wi i y) (F:=fun n=>El(int(V.cons n (V.cons y i))U)); trivial.
   apply fix_typ with (1:=H); trivial.
   transitivity y'; trivial.

   rewrite <- fix_irr with (1:=H) (o:=y); auto.

  (* sat body *)
  apply piSAT0_intro'.
  2:exists (int0 O i).
  2:apply lt_osucc; auto.
  intros o' u ? ?.
  apply inSAT_exp.
   right; apply sat_sn in H4; trivial.
  replace (Lc.subst u (tm (Lc.ilift (I.cons (tm j O) j)) M)) with
     (tm (I.cons u (I.cons (tm j O) j)) M).
  2:unfold Lc.subst; rewrite <- tm_substitutive.
  2:apply tm_morph; auto with *.
  2:intros [|[|k]]; unfold Lc.ilift,I.cons; simpl.
  2:rewrite Lc.lift0; reflexivity.
  2:rewrite Lc.simpl_subst; trivial.
  2:rewrite Lc.lift0; trivial.
  2:rewrite Lc.simpl_subst; trivial.
  2:rewrite Lc.lift0; trivial.
(*  apply piSAT0_intro'.
  2:exists empty; apply union2_intro1; apply singl_intro.
  intros x v ? ?.*)
  assert (val_ok (Prod (WIL 1 (Ref 0)) U::OSucct O::e)
            (V.cons (WREC (F i) o') (V.cons o' i)) (I.cons u (I.cons (tm j O) j))).
   apply vcons_add_var.
   3:discriminate.
    apply vcons_add_var; trivial.
    2:discriminate.
    split.
     red; rewrite El_int_osucc; trivial.

     simpl; rewrite Real_def; auto with *.
      apply ty_O in H.
      apply in_int_sn in H; trivial.

      apply union2_intro2; trivial.

     assert (WREC (F i) o' ∈ cc_prod (Wi i o')
               (fun x => El(int(V.cons x(V.cons o' i)) U))).
      apply fix_typ with (1:=H); trivial.
       eauto using isOrd_inv.
       apply olts_le in H3; trivial.
     apply and_split; intros.
      red; rewrite El_int_prod.
      revert H5; apply eq_elim; apply cc_prod_ext.
       rewrite El_int_W_lift; reflexivity.

       red; intros.
       rewrite H6; reflexivity.

      rewrite Real_int_prod.
       revert H4; apply interSAT_morph_subset; simpl proj1_sig; intros.
        rewrite El_int_W_lift; reflexivity.

        apply prodSAT_morph; auto with *.
        rewrite Real_int_W_lift; trivial.
        reflexivity.

       revert H5; apply eq_elim; apply cc_prod_ext.
        rewrite El_int_W_lift; reflexivity.

        red; intros.
        rewrite H7; reflexivity.

  red in ty_M; specialize ty_M with (1:=H5).
  apply in_int_not_kind in ty_M.
  2:discriminate.
  destruct ty_M.
  red in H6; rewrite El_int_prod in H6.
  rewrite Real_int_prod in H7; trivial.
  revert H7; apply interSAT_morph_subset; simpl proj1_sig; intros.
   rewrite El_int_W_lift; reflexivity.
   apply prodSAT_morph.
    rewrite Real_int_W_lift; trivial.
    reflexivity.

   apply Real_morph; auto with *.
    rewrite int_lift_rec_eq.
    rewrite int_subst_rec_eq.
    rewrite int_lift_rec_eq.
    apply int_morph; auto with *.
    intros [|[|k]]; unfold V.lams,V.shift; simpl; try reflexivity.
    replace (k-0) with k; auto with *.

    apply fix_eqn with (1:=H); auto.
     eauto using isOrd_inv.
     apply olts_le; trivial.
Qed.

Lemma wfix_eq : forall N,
  typ e N (WI A B O) ->
  eq_typ e (App (WFix O M) N)
           (App (subst O (subst (lift 1 (WFix O M)) M)) N).
red; intros.
unfold eqX.
change
 (app (WREC (F i) (int i O)) (int i N) ==
  app (int i (subst O (subst (lift 1 (WFix O M)) M))) (int i N)).
do 2 rewrite <- int_subst_eq.
rewrite int_cons_lift_eq.
red in H; specialize H with (1:=H0).
apply in_int_not_kind in H.
2:discriminate.
destruct H.
red in H; rewrite El_int_W in H; trivial.
rewrite wfix_eqn with (1:=H0); trivial.
rewrite cc_beta_eq.
 reflexivity.

 do 2 red; intros.
 rewrite H3; reflexivity.

 trivial.
Qed.

Lemma wfix_extend :
  fx_subval E O ->
  fx_extends E (WI A B O) (WFix O M).
intro subO.
do 2 red; intros.
rewrite El_int_W in H0.
assert (isval := proj1 H).
assert (isval' := proj1 (proj2 H)).
assert (oo: isOrd (int i O)).
 destruct tyord_inv with (3:=ty_O) (4:=isval); trivial.
assert (oo': isOrd (int i' O)).
 destruct tyord_inv with (3:=ty_O) (4:=isval'); trivial.
assert (inclo: int i O ⊆ int i' O).
 apply subO in H; trivial.
clear subO.
change (cc_app (WREC (F i) (int i O)) x == cc_app (WREC (F i') (int i' O)) x).
revert x H0.
elim oo using isOrd_ind; intros.
apply union2_elim in H3; destruct H3.
 apply singl_elim in H3.
 rewrite cc_app_outside_domain with (dom:=TI (WF' A B i) y).
  symmetry; apply cc_app_outside_domain with (dom:=TI (WF' A B i') (int0 O i')).
   admit.

   intro; revert H3.
   apply mt_not_in_W_F in H4; trivial.
   do 2 red; intros.
   rewrite H3; reflexivity.

  admit.

  intro; revert H3.
  apply mt_not_in_W_F in H4; trivial.
  do 2 red; intros.
  rewrite H3; reflexivity.

 apply TI_elim in H3; auto.
 destruct H3 as (o',?,?).
 assert (o_o' : isOrd o') by eauto using isOrd_inv.
 assert (o'_y : osucc o' ⊆ y).
  red; intros.
  apply isOrd_plump with o'; trivial.
   apply isOrd_inv with (osucc o'); auto.
   apply olts_le in H5; trivial.
 rewrite <- TI_mono_succ in H4; auto with *.
  rewrite <- fix_irr with (1:=isval) (o:=osucc o'); auto.
  2:apply cc_dec_intro; trivial.
  rewrite fix_eqn with (1:=isval); auto.
  2:apply cc_dec_intro; trivial.
  assert (forall o', isOrd o' -> TI (WF' A B i) o' == TI (WF' A B i') o').
   intros.
   apply TI_morph_gen; auto with *.
   red; intros.
   unfold WF'; apply W_F_ext; auto with *.
    rewrite (Aeq _ _ _ _ H); reflexivity.

    red; intros.
    apply El_morph; eapply Beq.
    apply val_push_var with (1:=H); trivial.
     split;[trivial|apply varSAT].
     rewrite H8 in H7;split;[trivial|apply varSAT].
     red; rewrite <- (Aeq _ _ _ _ H); trivial.

   apply cc_dec_morph; trivial.

  rewrite <- fix_irr with (1:=isval') (o:=osucc o'); auto with *.
  2:transitivity y; trivial.
  2:transitivity (int0 O i); trivial.
  2:unfold Wi; rewrite <- H5; auto; apply cc_dec_intro; trivial.
  rewrite fix_eqn with (1:=isval'); auto.
  2:unfold Wi; rewrite <- H5; auto; apply cc_dec_intro; trivial.
  do 2 red in stab.
  apply stab with (I.cons daimon (I.cons daimon j)) (I.cons daimon (I.cons daimon j')).
   apply val_push_fun.
    apply val_push_ord; auto with *.
     split;[|apply varSAT].
     red; rewrite El_int_osucc; auto.
     apply ole_lts; auto.

     split;[|apply varSAT].
     red; rewrite El_int_osucc; auto.
     apply ole_lts; auto.

     discriminate.

    split;[|apply varSAT].
    red; rewrite El_int_prod.
    eapply eq_elim.
    2:eapply fix_typ with (1:=isval); auto.
    apply cc_prod_ext.
     rewrite El_int_W_lift; reflexivity.

     red; intros.
     rewrite H7; reflexivity.

    split;[|apply varSAT].
    red; rewrite El_int_prod.
    eapply eq_elim.
    2:eapply fix_typ with (1:=isval'); auto.
    apply cc_prod_ext.
     rewrite El_int_W_lift; reflexivity.

     red; intros.
     rewrite H7; reflexivity.

    red; intros.
    rewrite El_int_W_lift in H6.
    rewrite fix_irr with (1:=isval') (o':=int i' O).
     auto.
     trivial.
     trivial.
     trivial.
     red; intros.
     apply isOrd_trans with o'; trivial.
     apply inclo; apply H1; trivial.
     reflexivity.
     unfold Wi; rewrite <- H5; trivial.

   rewrite El_int_W_lift; trivial.
   apply cc_dec_intro; trivial.

  do 2 red; intros.
  apply W_F_mono.
   do 2 red; intros.
   rewrite H7; reflexivity.

   apply cc_dec_mono; trivial.

 do 2 red; intros.
 apply W_F_morph.
  do 2 red; intros.
  rewrite H6; reflexivity.

  apply cc_dec_morph; trivial.
Qed.

Lemma wfix_equals :
  fx_equals E O ->
  fx_equals E (WFix O M).
red; intros.
assert (fxs: fx_subval E O).
 apply fx_equals_subval; trivial.
apply wfix_extend in fxs.
red in fxs.
specialize fxs with (1:=H0).
apply fcompat_typ_eq with (3:=fxs).
 eapply cc_prod_is_cc_fun.
 assert (h := typ_wfix _ _ (proj1 H0)).
 apply in_int_not_kind in h.
 2:discriminate.
 destruct h.
 red in H1; rewrite El_int_prod in H1; eexact H1.

 setoid_replace (int i (WI A B O)) with (int i' (WI A B O)).
  eapply cc_prod_is_cc_fun.
  assert (h := typ_wfix _ _ (proj1 (proj2 H0))).
  apply in_int_not_kind in h.
  2:discriminate.
  destruct h.
  red in H1; rewrite El_int_prod in H1; eexact H1.

  do 2 red.
  assert (h:= H _ _ _ _ H0).
  apply mkTY_ext.
   apply TI_morph_gen; auto with *.
   red; intros.
   apply W_F_ext.
    apply El_morph; apply (Aeq _ _ _ _ H0).

    red; intros.
    apply El_morph; eapply Beq.
    apply val_push_var with (1:=H0); trivial.
     split;[trivial|apply varSAT].
     rewrite H3 in H2;split;[trivial|apply varSAT].
     red; rewrite <- (Aeq _ _ _ _ H0); trivial.

   apply cc_dec_morph; trivial.

  intros.
  unfold RW; apply rWi_ext; trivial.
   apply El_morph; apply (Aeq _ _ _ _ H0).

   red; intros.
   apply El_morph; eapply Beq.
   apply val_push_var with (1:=H0); trivial.
    split;[trivial|apply varSAT].
    rewrite H4 in H3;split;[trivial|apply varSAT].
    red; rewrite <- (Aeq _ _ _ _ H0); trivial.

  red; intros.
  apply Real_morph; trivial.
  apply (Aeq _ _ _ _ H0).

  red; intros.
  apply Real_morph; trivial.
  eapply Beq.
  apply val_push_var with (1:=H0); trivial.
   split;[trivial|apply varSAT].
   rewrite H4 in H3;split;[trivial|apply varSAT].
   red; rewrite <- (Aeq _ _ _ _ H0); trivial.

  destruct tyord_inv with (3:=ty_O) (4:=proj1 H0); trivial.
Qed.

End WFixRules.

Print Assumptions typ_wfix.


Lemma typ_wfix' : forall infty e A B O U M T,
       T <> kind ->
       isOrd infty ->
       zero ∈ infty ->
       A <> kind ->
       typ e O (Ordt infty) ->
       typ (Prod (WIL A B 1 (Ref 0)) U :: OSucct O :: e) M
         (Prod (WIL A B 2 (OSucc (Ref 1)))
         (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U)))) ->
       fx_extends (push_fun (push_ord (tinj e) (OSucct O)) (WIL A B 1 (Ref 0)) U)
         (WIL A B 2 (OSucc (Ref 1))) M ->
       fx_sub (push_var (push_ord (tinj e) (OSucct O)) (WIL A B 1 (OSucc (Ref 0)))) U ->
       sub_typ e (Prod (WI A B O) (subst_rec O 1 U)) T ->
       typ e (WFix O M) T.
intros.
apply typ_subsumption with (Prod (WI A B O) (subst_rec O 1 U)); auto.
2:discriminate.
change e with (tenv (tinj e)).
apply typ_wfix with (infty:=infty); trivial.
Qed.

(****************************************************************************************)
(** Compound judgements : typing + variance *)

Definition typ_ext e M A B :=
  fx_extends e A M /\ typ (tenv e) M (Prod A B).

Definition typ_mono e M :=
  fx_sub e M /\ typs (tenv e) M.

Definition typ_monoval e M T :=
  fx_subval e M /\ typ (tenv e) M T.

Definition typ_impl e M T :=
  fx_equals e M /\ typ (tenv e) M T.

Instance typ_impl_morph e : Proper (eq_trm ==> eq_trm ==> iff) (typ_impl e).
apply morph_impl_iff2; auto with *.
do 4 red; intros.
destruct H1; split.
 red; intros.
 rewrite <- H; eauto.

 rewrite <- H; rewrite <- H0; eauto.
Qed.

Lemma typ_var_impl : forall e n t T,
    spec_var e n = false ->
    nth_error (tenv e) n = value t ->
    t <> kind ->
    T <> kind ->
    sub_typ (tenv e) (lift (S n) t) T ->
    typ_impl e (Ref n) T.
intros.
split.
 apply fx_eq_noc; apply noc_var; trivial.

 apply typ_subsumption with (lift (S n) t); trivial.
  apply typ_var; trivial.

  destruct t as [(t,tm)|]; simpl in *; auto.
  discriminate.
Qed.

  Lemma impl_abs : forall e s1 U T T' M,
    T <> kind ->
    U <> kind ->
    s1=prop \/ s1=kind ->
    eq_typ (tenv e) T T' ->
    typ_impl e T s1 ->
    typ_impl (push_var e T) M U ->
    typ_impl e (Abs T M) (Prod T' U).
intros.
destruct H3; destruct H4.
split.
 apply fx_eq_abs; trivial.

 apply typ_conv with (Prod T U); auto.
  apply typ_abs; trivial.
  destruct H1; subst s1; red; auto.

  apply eq_typ_prod; trivial.
  reflexivity.

  discriminate.

  discriminate.
Qed.

Lemma impl_app : forall e u v V Ur T,
  T <> kind ->
  V <> kind ->
  Ur <> kind ->
  sub_typ (tenv e) (subst v Ur) T ->
  typ_impl e u (Prod V Ur) ->
  typ_impl e v V ->
  typ_impl e (App u v) T.
intros.
destruct H3.
destruct H4.
split.
 apply fx_eq_app; trivial.

 apply typ_subsumption with (subst v Ur); trivial.
  apply typ_app with V; auto.

  destruct Ur as [(Ur,Urm)|]; simpl; trivial.
  discriminate.
Qed.

  Lemma Wi_fx_sub : forall e o A B O,
    isOrd o ->
    zero ∈ o ->
    typ_impl e A kind ->
    typ_impl (push_var e A) B kind ->
    typ_monoval e O (Ordt o) ->
    fx_sub e (WI A B O).
intros.
red; intros.
destruct H1.
red in H6; specialize H6 with (1:=proj1 H4).
destruct H6 as (?,_).
destruct H2.
destruct H3.
revert i i' j j' H4 x t H5.
change (fx_sub e (WI A B O)).
apply Wi_sub with (o:=o); trivial.
Qed.

  Lemma OSucc_fx_sub : forall e O o,
    isOrd o ->
    zero ∈ o ->
    typ_monoval e O (Ordt o)->
    typ_monoval e (OSucc O) (Ordt (osucc o)).
destruct 3.
split.
 apply OSucc_sub; trivial.

 red; simpl; intros.
 apply in_int_intro; try discriminate.
 destruct tyord_inv with (3:=H2)(4:=H3) as (_,(?,_)); trivial.
 assert (osucc (int i O) ∈ El (int i (Ordt (osucc o)))).
  rewrite El_int_ord.
  apply lt_osucc_compat; trivial.
  apply ole_lts; auto.
 split; trivial.
 unfold int at 1, Ordt, cst, iint.
 rewrite Real_def; auto with *.
  assert (h:= H2 _ _ H3).
  apply in_int_sn in h.
  simpl; trivial.

  simpl.
  apply cc_dec_intro.
  apply lt_osucc_compat; trivial.
Qed.

  Lemma typ_var_mono : forall e n t T,
    ords e n = true ->
    nth_error (tenv e) n = value t ->
    T <> kind ->
    t <> kind ->
    sub_typ (tenv e) (lift (S n) t) T ->
    typ_monoval e (Ref n) T.
intros.
split.
 apply var_sub; trivial.

 apply typ_subsumption with (lift (S n) t); trivial.
  apply typ_var; trivial.

  destruct t as [(t,tm)|]; simpl in *; auto.
  discriminate.
Qed.

  Lemma ext_abs : forall e U T M,
    T <> kind ->
    U <> kind ->
    typ_mono e T ->
    typ_impl (push_var e T) M U ->
    typ_ext e (Abs T M) T U.
intros.
destruct H1; destruct H2; split.
 apply fx_abs with U; trivial.

 apply typ_abs; trivial.
Qed.

(*************)

  Lemma impl_call : forall e n x t u T,
    ords e n = false ->
    fixs e n = Some t ->
    T <> kind ->
    t <> kind ->
    u <> kind ->
    nth_error (tenv e) n = value (Prod t u) ->
    sub_typ (tenv e) (subst x (lift_rec (S n) 1 u)) T ->
    typ_impl e x (lift (S n) t) ->
    typ_impl e (App (Ref n) x) T.
intros.
destruct H6.
assert (typ (tenv e) (Ref n) (Prod (lift (S n) t) (lift_rec (S n) 1 u))).
 apply typ_var0; rewrite H4; split;[discriminate|].
 apply sub_refl.

 unfold lift; rewrite red_lift_prod.
 reflexivity.
split.
 apply fx_eq_rec_call with t (lift_rec (S n) 1 u); trivial.

 apply typ_subsumption with (subst x (lift_rec (S n) 1 u)); auto.
 2:destruct u as [(u,um)|]; trivial.
 2:discriminate.
 apply typ_app with (lift (S n) t); trivial.
 destruct t as [(t,tm)|]; trivial.
 discriminate.
 destruct u as [(u,um)|]; trivial.
 discriminate.
Qed.


Lemma typ_wfix'' : forall infty e A B O U M T,
       isOrd infty ->
       zero ∈ infty ->
       T <> kind ->
       sub_typ (tenv e) (Prod (WI A B O) (subst_rec O 1 U)) T ->
       typ (tenv e) O (Ordt infty) ->
       typ_mono (push_var (push_ord e (OSucct O)) (WI (lift 1 A) (lift_rec 1 1 B) (OSucc (Ref 0)))) U ->
       typ_ext (push_fun (push_ord e (OSucct O)) (WI (lift 1 A) (lift_rec 1 1 B) (Ref 0)) U)
         M (WI (lift 2 A) (lift_rec 2 1 B) (OSucc (Ref 1)))
           (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
       typ (tenv e) (WFix O M) T.
intros.
destruct H4; destruct H5.
apply typ_subsumption with (2:=H2); trivial.
2:discriminate.
apply typ_wfix with infty; trivial.
Qed.

  Lemma typ_ext_fix : forall eps e A B O U M,
    isOrd eps ->
    zero ∈ eps ->
    typ_impl e A kind ->
    typ_impl (push_var e A) B kind ->
    typ_monoval e O (Ordt eps) ->
    typ_ext (push_fun (push_ord e (OSucct O)) (WI (lift 1 A) (lift_rec 1 1 B) (Ref 0)) U) M
      (WI (lift 2 A) (lift_rec 2 1 B) (OSucc (Ref 1)))
      (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    fx_sub (push_var (push_ord e (OSucct O)) (WI (lift 1 A) (lift_rec 1 1 B) (OSucc (Ref 0)))) U ->
    typ_ext e (WFix O M) (WI A B O) (subst_rec O 1 U).
intros eps e A B O U M eps_ord eps_nz tyA tyB tyO tyM tyU.
destruct tyO as (inclO,tyO).
destruct tyM as (extM,tyM).
assert (tyF: typ (tenv e) (WFix O M) (Prod (WI A B O) (subst_rec O 1 U))).
 apply typ_wfix with eps; trivial.
split; trivial.
red; intros.
generalize i i' j j' H; change (fx_extends e (WI A B O) (WFix O M)).
destruct tyA as (eqA,tyA).
destruct (tyA _ _ (proj1 H)) as (Ank,_).
destruct tyB as (eqB,_).
apply wfix_extend with eps U; trivial.
Qed.

  Lemma typ_impl_fix : forall eps e A B O U M,
    isOrd eps ->
    zero ∈ eps ->
    typ_impl e A kind ->
    typ_impl (push_var e A) B kind ->
    typ_impl e O (Ordt eps) ->
    typ_ext (push_fun (push_ord e (OSucct O)) (WI (lift 1 A) (lift_rec 1 1 B) (Ref 0)) U) M
      (WI (lift 2 A) (lift_rec 2 1 B) (OSucc (Ref 1)))
      (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    fx_sub (push_var (push_ord e (OSucct O)) (WI (lift 1 A) (lift_rec 1 1 B) (OSucc (Ref 0)))) U ->
    typ_impl e (WFix O M) (Prod (WI A B O) (subst_rec O 1 U)).
intros eps e A B O U M eps_ord eps_nz (eqA,tyA) (eqB,_) (inclO,tyO) (extM,tyM) tyU.
assert (tyF: typ (tenv e) (WFix O M) (Prod (WI A B O) (subst_rec O 1 U))).
 apply typ_wfix with eps; trivial.
split; trivial.
red; intros.
generalize i i' j j' H; change (fx_equals e (WFix O M)).
destruct (tyA _ _ (proj1 H)) as (Ank,_).
apply wfix_equals with eps A B U; trivial.
Qed.


(*
(************************************************************************)
(** One example of derived principles:
    - the standard recursor for W
*)
Section Example.

Definition nat_ind_typ :=
   Prod (Prod (NatI (Ord omega)) prop) (* P : nat -> Prop *)
  (Prod (App (Ref 0) Zero)
  (Prod (Prod (NatI (Ord omega)) (Prod (App (Ref 2) (Ref 0))
                        (App (Ref 3) (App (Succ (Ord omega)) (Ref 1)))))
  (Prod (NatI (Ord omega)) (App (Ref 3) (Ref 0))))).

Definition nat_ind :=
   Abs (*P*)(Prod (NatI (Ord omega)) prop) (* P : nat -> Prop *)
  (Abs (*fZ*) (App (Ref 0) Zero)
  (Abs (*fS*) (Prod (*n*)(NatI (Ord omega)) (Prod (App (Ref 2) (Ref 0))
                                   (App (Ref 3) (App (Succ (Ord omega)) (Ref 1)))))
  (NatFix (Ord omega)
    (*o,Hrec*)
    (Abs (*n*)(NatI (OSucc (Ref 1)))
      (Natcase
        (Ref 4)
        (*k*)(App (App (Ref 4) (Ref 0))
                  (App (Ref 2) (Ref 0)))
        (Ref 0)))))).



Lemma nat_ind_def :
  forall e, typ e nat_ind nat_ind_typ.
assert (eq_trm Nat (NatI (Ord omega))).
 red; simpl.
 red; unfold NAT; reflexivity.
unfold nat_ind, nat_ind_typ; intros.
apply typ_abs; try discriminate.
apply typ_abs; try discriminate.
apply typ_abs; try discriminate.

set (E0 := Prod (NatI (Ord omega))
                 (Prod (App (Ref 2) (Ref 0))
                    (App (Ref 3) (App (SuccI (Ord omega)) (Ref 1))))
               :: App (Ref 0) Zero :: Prod (NatI (Ord omega)) prop :: e) in |-*.
change E0 with (tenv (tinj E0)).
apply typ_nat_fix'' with (osucc omega) (App (Ref 4) (Ref 0)); auto.
 (* sub *)
 apply sub_refl.
 apply eq_typ_prod.
  reflexivity.

  eapply eq_typ_morph;[reflexivity| |reflexivity].
  simpl; do 2 red; simpl; intros.
  unfold V.lams, V.shift; simpl.
  apply cc_app_morph; apply H0.

 (* ord *)
 red; simpl; intros.
 apply lt_osucc; trivial.

 (* codom mono *)
 split.
  apply fx_equals_sub.
  apply fx_eq_noc.
  apply noc_app.
   apply noc_var; reflexivity.
   apply noc_var; reflexivity.

  red; intros; simpl; exact I.

 (* fix body *)
 apply ext_abs; try discriminate.
  apply Wi_fx_sub with (o:=osucc (osucc omega)); auto.
  apply OSucc_fx_sub; auto.
  apply typ_var_mono with (OSucct (Ord omega)); auto; try discriminate.
  red; simpl; intros; trivial.

  apply impl_natcase with (osucc omega) (Ref 2) (Ref 5); auto.
   eapply typ_var_mono.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.

    simpl tenv; apply sub_refl.
    red; simpl; intros; reflexivity.

   simpl tenv.
   apply sub_refl.
   red; simpl; intros.
   unfold V.lams, V.shift; simpl.
   reflexivity.

   (* branch 0 *)
   eapply typ_var_impl.
    compute; reflexivity.
    simpl nth_error.
    reflexivity.
    discriminate.

    apply sub_refl; red; simpl; intros.
    unfold V.lams, V.shift; simpl.
    reflexivity.

   (* branch S *)
   apply impl_app with (App (Ref 6) (Ref 0))
     (App (Ref 7) (App (SuccI (Ref 4)) (Ref 1))); try discriminate.
    simpl tenv.
    apply sub_refl; red; intros; simpl.
    unfold V.lams, V.shift; simpl.
    reflexivity.

    apply impl_app with (NatI (Ord omega))
      (Prod (App (Ref 7) (Ref 0)) (App (Ref 8) (App (SuccI (Ord omega)) (Ref 1))));
      try discriminate.
     simpl tenv.
     unfold subst; rewrite eq_subst_prod.
     apply sub_typ_covariant.
      red; simpl; intros; reflexivity.

     apply sub_refl.
     red; intros; simpl.
     apply cc_app_morph; [reflexivity|].
     assert (i 1 ∈ Wi (i 4)).
      generalize (H0 1 _ (eq_refl _)); simpl.
      unfold V.lams, V.shift; simpl.
      trivial.
     rewrite beta_eq.
      rewrite beta_eq; auto with *.
       reflexivity.
       red; intros; apply inr_morph; trivial.

      red; intros; apply inr_morph; trivial.

      apply Wi_NAT in H1; trivial.
      generalize (H0 4 _ (eq_refl _)); simpl; intro.
      apply isOrd_inv with (osucc omega); auto.

     eapply typ_var_impl.
      compute; reflexivity.
      simpl; reflexivity.
      discriminate.

      apply sub_refl.
      red; intros; simpl.
      unfold V.lams, V.shift; simpl.
      reflexivity.

     eapply typ_var_impl.
      compute; reflexivity.
      simpl; reflexivity.
      discriminate.

      red; intros; simpl.
      simpl in H1.
      unfold V.lams, V.shift in H1; simpl in H1.
      apply Wi_NAT in H1; trivial.
      generalize (H0 3 _ (eq_refl _)); simpl; intro.
      apply isOrd_inv with (osucc omega); auto.

    eapply impl_call.
     compute; trivial.
     simpl; reflexivity.
     discriminate.
     2:simpl; reflexivity.
     discriminate.

     apply sub_refl; red; intros; simpl.
     unfold V.lams, V.shift; simpl.
     reflexivity.

     eapply typ_var_impl.
      compute; reflexivity.
      simpl; reflexivity.
      discriminate.

      apply sub_refl; red; intros; simpl.
      reflexivity.

   (* Scrutinee *)
   eapply typ_var_impl.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.

    apply sub_refl; red; intros; simpl.
    reflexivity.
Qed.


