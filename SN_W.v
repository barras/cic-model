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

Lemma Real_intro x t T :
  x ∈ El T ->
  (x ∈ El T -> inSAT t (Real T x)) ->
  [x,t] \real T.
split; auto.
Qed.

Import ZFcoc.
Lemma Real_ax x t T R :
  (forall x x', x ∈ cc_dec T -> x==x' -> eqSAT (R x) (R x')) ->
  ([x,t] \real mkTY T R <-> x ∈ cc_dec T /\ inSAT t (R x)).
intros.
unfold inX; rewrite El_def.
split; destruct 1; split; trivial; rewrite Real_def in *; auto with *.
Qed.

Lemma Real_intro2 x t T R :
  (forall x x', x ∈ cc_dec T -> x==x' -> eqSAT (R x) (R x')) ->
  x ∈ cc_dec T ->
  (x ∈ cc_dec T -> inSAT t (R x)) ->
  [x,t] \real mkTY T R.
split.
 unfold inX; rewrite El_def; trivial.

 rewrite Real_def; auto.
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

Definition Ord (o:set) : trm := SN_ECC_Real.cst o.

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


Definition typ_ord_ord : forall e o o',
  o < o' -> typ e (Ord o) (Ordt o').
red; simpl; intros.
apply in_int_intro; try discriminate.
simpl.
rewrite Real_ax;[split|]; auto with *.
 apply union2_intro2; trivial.

 apply Lc.sn_K.
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
simpl in H1.
rewrite Real_ax in H1; auto with *.
destruct H1.
apply union2_elim in H1; destruct H1.
 apply singl_elim in H1; rewrite H1; auto.

 eauto using isOrd_inv.
Qed.

(** W *)

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


Section Wtypes_typing.

Variable A B:trm.
Variable e:env.
Hypothesis Atyp : typ e A kind.
Hypothesis Btyp : typ (A::e) B kind.

Let Aw i := El (int0 A i).
Let Bw i x := El (int0 B (V.cons x i)).
Let Ww i := W (Aw i) (Bw i).

Let RAw i a := Real (int0 A i) a.
Let RBw i a b := Real (int0 B (V.cons a i)) b.

Let WF' i X := W_F (Aw i) (Bw i) (cc_dec X).

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
  unfold W_F.
  apply sigma_morph; trivial.
  red; intros.
  apply cc_arr_morph; trivial.
   apply H0; trivial.
   apply union2_morph; auto with *.

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

Definition WI (o:trm) : trm.
(*begin show*)
left; exists (fun i => mkTY (TI (WF' i) (int0 o i))
                            (rWi (Aw i) (Bw i) (RAw i) (RBw i) (int0 o i)))
             (fun j => Lc.App2 Lc.K (tm j A) (Lc.App2 Lc.K (Lc.Abs(tm (Lc.ilift j) B)) (tm j o))).
(*end show*)
 do 2 red; intros.
 apply mkTY_ext; intros.
  apply TI_morph_gen.
   apply WF'_morph; trivial.
   rewrite H; reflexivity.

  apply rWi_morph_gen; trivial.
   apply Aw_morph; trivial.
   apply Bw_morph; trivial.
   apply RAw_morph; trivial.
   apply RBw_morph; trivial.
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

Lemma val_ok_cons_default T i j :
  val_ok e i j ->
  T <> kind ->
  val_ok (T::e) (V.cons empty i) (I.cons daimon j).
intros.
apply vcons_add_var; trivial.
split.
 red; auto.
 apply varSAT.
Qed.

Lemma typ_WI : forall eps o,
  isOrd eps ->
  typ e o (Ordt eps) ->
  typ e (WI o) kind.
red; intros; simpl.
red in H0; specialize H0 with (1:=H1).
assert (tyA := Atyp _ _ H1).
apply in_int_not_kind in H0.
2:discriminate.
destruct tyA as (Ank,(_,snA)).
destruct (Btyp _ _ (val_ok_cons_default _ _ _ H1 Ank)) as (Bnk,(_,snB)).
split;[|split].
 discriminate.

 exists nil; exists (WI o);[reflexivity|].
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

(*
Lemma realNati_def x t i O :
 isOrd (int i O) ->
 ([x,t] \real int i (NatI O) <->
  x ∈ NATi (int i O) /\ inSAT t (fNATi (int i O) x)).
intros.
simpl.
rewrite Real_ax; auto with *.
intros.
rewrite H1; reflexivity.
Qed.
*)
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

 apply union2_intro2; trivial.
Qed.



Lemma El_prod A0 Ar B0 Br :
  ext_fun (cc_dec A0) B0 ->
  El (prod(mkTY A0 Ar) (fun x => mkTY (B0 x) (Br x))) ==
  cc_dec (cc_prod (cc_dec A0) (fun x => cc_dec (B0 x))).
intros.
unfold prod, ZFuniv_real.prod; rewrite El_def.
apply union2_morph; auto with *.
apply cc_prod_ext.
 rewrite El_def; reflexivity.

 red; intros.
 rewrite El_def.
 apply union2_morph; auto with *.
 apply H; trivial.
 rewrite El_def in H0; trivial.
Qed.
(*
 Lemma prodReal :
  [x,t] \real prod (mkTY A Ar) (fun x => mkTY (B x) (Br x)) <->
  x ∈ cc_prod
*)
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


Lemma El_prod_elim f U V :
  ext_fun (El U) V ->
  f ∈ El (prod U V) ->
  f ∈ cc_prod (El U) (fun x => El (V x)).
intros.
unfold prod, ZFuniv_real.prod in H0.
rewrite El_def in H0.
rewrite <- cc_prod_mt; trivial.
do 2 red; intros.
apply El_morph; apply H; trivial.
Qed.

Lemma typ_Wc : forall o e O X F,
  isOrd o ->
  zero ∈ o ->
  typ e O (Ordt o) ->
  typ e X A ->
  typ e F (Prod (subst X B) (lift 1 (WI O))) ->
  typ e (Wc X F) (WI (OSucc O)).
red; intros.
red in H2; specialize H2 with (1:=H4).
apply in_int_not_kind in H2.
2:admit.
red in H3; specialize H3 with (1:=H4).
apply in_int_not_kind in H3.
2:discriminate.
destruct tyord_inv with (3:=H1)(4:=H4) as (?,(?,_)); trivial.
apply in_int_intro; try discriminate.
assert (couple (int0 X0 i) (int0 F i) ∈ TI (WF' i) (osucc (int0 O i))).
 apply TI_intro with (int0 O i); auto.
  apply WF'_morph; reflexivity.

  unfold W_F.
  apply couple_intro_sigma.
   do 2 red; intros.
   rewrite H8; reflexivity.

   apply H2.

   destruct H3.
   simpl in H3.
   apply El_prod_elim in H3.
   2:admit.
   unfold V.lams, V.cons, V.shift in H3; simpl in H3.
   revert H3; apply eq_elim; apply cc_arr_morph.
    rewrite <- int_subst_eq; reflexivity.

    rewrite El_def.
    apply union2_morph; auto with *.
    assert (eq_val i (fun k => i (k-0))).
     intros [|k]; simpl; reflexivity.
    rewrite <- H3; reflexivity.
split.
 red; simpl.
 rewrite El_def.
 apply union2_intro2; trivial.

 simpl.
 unfold SN_CC_addon.Real; rewrite Real_def.
  apply Real_WC; trivial.
   apply Bw_morph; reflexivity.
   apply RAw_morph; reflexivity.
   apply RBw_morph; reflexivity.

   rewrite fst_def.
   apply H2.

   destruct H3.
   unfold SN_CC_addon.Real in H8; simpl in H8.
   rewrite Real_prod in H8.
    unfold piSAT in H8.
    revert H8; apply piSAT0_morph; intros.
     red; intros.
     rewrite fst_def.
     rewrite <- int_subst_eq; reflexivity.

     rewrite fst_def.
     rewrite <- int_subst_eq; reflexivity.

     unfold V.lams, V.cons, V.shift; simpl.
     rewrite snd_def.
     assert (eq_val i (fun k => i (k-0))).
      intros [|k]; simpl; reflexivity.
     rewrite Real_def.
      apply rWi_morph_gen; trivial.
       apply Aw_morph; trivial.
       apply Bw_morph; trivial.
       apply RAw_morph; trivial.
       apply RBw_morph; trivial.
       rewrite H10; reflexivity.
       reflexivity.

     intros.
     apply rWi_morph; auto with *.
     apply RAw_morph; reflexivity.

     red in H3; simpl in H3.
     apply El_prod_elim in H3.
      specialize cc_prod_elim with (1:=H3) (2:=H9); intro.
      rewrite El_def in H11.
      trivial.

      admit.

     red; intros.
     reflexivity.

    exact H3.

    intros.
    rewrite H9; reflexivity.

 apply union2_intro2; trivial.
Qed.

(* Case analysis *)


Definition sigma_case b c :=
  cond_set (c == couple (fst c) (snd c)) (b (fst c) (snd c)).

Lemma sigma_case_couple f a b c :
  morph2 f ->
  c == couple a b ->
  sigma_case f c == f a b.
intros.
unfold sigma_case.
rewrite cond_set_ok.
 rewrite H0; rewrite fst_def; rewrite snd_def; reflexivity.

 rewrite H0; rewrite fst_def; rewrite snd_def; reflexivity.
Qed.

Lemma sigma_case_mt f c :
  c == empty -> 
  sigma_case f c == empty.
intros.
unfold sigma_case.
apply empty_ext; red; intros.
rewrite cond_set_ax in H0.
destruct H0.
rewrite H1 in H.
assert (singl (fst c) ∈ couple (fst c) (snd c)).
 apply pair_intro1.
rewrite H in H2.
apply empty_ax in H2; trivial.


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

Lemma Wcase_iota : forall e X F G,
  eq_typ e (Wcase G (Wc X F)) (App (App G X) F).
red; intros.
simpl.
rewrite sigma_case_couple with (a:=int0 X0 i) (b:=int0 F i).
 reflexivity.

 do 3 red; intros.
 rewrite H0; rewrite H1; reflexivity.

 reflexivity.
Qed.

Lemma fst_mt : fst empty == empty.
apply empty_ext; red; intros.
unfold fst in H.
apply union_elim in H; destruct H.
apply subset_elim1 in H0.
apply union_elim in H0; destruct H0.
apply empty_ax in H1; trivial.
Qed.
Lemma snd_mt : snd empty == empty.
apply empty_ext; red; intros.
unfold snd in H.
apply union_elim in H; destruct H.
apply subset_elim1 in H0.
apply union_elim in H0; destruct H0.
apply empty_ax in H1; trivial.
Qed.
Lemma cc_dec_mono : Proper (incl_set==>incl_set) cc_dec.
do 3 red; intros.
apply union2_elim in H0; destruct H0.
 apply union2_intro1; trivial.
 apply union2_intro2; auto.
Qed.

Lemma fst_WF_inv x o U V :
  ext_fun (El U) V ->
  isOrd o ->
  x ∈ cc_dec (TI (fun X => W_F (El U) V (cc_dec X)) (osucc o)) ->
  fst x ∈ El U.
intros.
apply union2_elim in H1; destruct H1.
 apply singl_elim in H1; rewrite H1.
 rewrite fst_mt.
 apply union2_intro1; apply singl_intro.

 apply TI_elim in H1; auto.
  destruct H1.
  apply fst_typ_sigma in H2; trivial.

  do 2 red; intros; apply W_F_morph; trivial.
  apply union2_morph; auto with *.
Qed.
(*Lemma fst_WF_inv x o U V :
  ext_fun U V ->
  isOrd o ->
  x ∈ cc_dec (TI (fun X => W_F U V (cc_dec X)) (osucc o)) ->
  fst x ∈ cc_dec U.
intros.
apply union2_elim in H1; destruct H1.
 apply singl_elim in H1; rewrite H1.
 rewrite fst_mt.
 apply union2_intro1; apply singl_intro.

 apply union2_intro2.
 apply TI_elim in H1; auto.
  destruct H1.
  apply fst_typ_sigma in H2; trivial.

  do 2 red; intros; apply W_F_morph; trivial.
  apply union2_morph; auto with *.
Qed.
*)
Lemma snd_WF_inv x o U V :
  ext_fun U V ->
  isOrd o ->
  x ∈ cc_dec (TI (fun X => W_F U V (cc_dec X)) (osucc o)) ->
  snd x ∈ cc_arr (V (fst x)) (cc_dec (TI (fun X => W_F U V (cc_dec X)) o)).
intros.
apply union2_elim in H1; destruct H1.
 apply singl_elim in H1.
 setoid_replace (snd x) with empty; trivial.
 2:rewrite H1; rewrite snd_mt; reflexivity.
 unfold cc_arr; rewrite <- cc_prod_mt; auto.
  apply union2_intro1; apply singl_intro.

  intros; apply union2_intro1; apply singl_intro.

 apply TI_elim in H1; auto.
  destruct H1.
(*  specialize fst_typ_sigma with (1:=H2); intros.*)
  apply snd_typ_sigma with (y:=fst x) in H2; auto with *.
  revert H2; apply cc_prod_covariant; auto with *.
  intros.
  apply cc_dec_mono.
  apply TI_mono; auto.
   do 2 red; intros.
   apply W_F_mono; auto.
   apply cc_dec_mono; trivial.

   apply isOrd_inv with (osucc o); auto.
   apply olts_le; trivial.

   do 2 red; intros.
   apply W_F_morph; auto.
   unfold cc_dec; rewrite H2; reflexivity.
Qed.

Lemma typ_Wcase : forall o e P O G n,
  isOrd o ->
  zero ∈ o ->
  typ e O (Ordt o) ->
  typ e G (Prod A (Prod (Prod B (WI (lift 2 O))) (App (lift 2 P) (Wc (Ref 1) (Ref 0))))) ->
  typ e n (WI (OSucc O)) ->
  typ e (Wcase G n) (App P n).
red; intros.
destruct tyord_inv with (3:=H1)(4:=H4) as (?,(?,_ )); trivial.
red in H2; specialize H2 with (1:=H4).
apply in_int_not_kind in H2;[|discriminate].
red in H3; specialize H3 with (1:=H4).
apply in_int_not_kind in H3;[|discriminate].
apply in_int_intro; try discriminate.
destruct H2; red in H2.
destruct H3; red in H3.
split.
 red.
 simpl.
 simpl in H2.
 apply El_prod_elim in H2.
 2:admit.
 simpl in H3.
 rewrite El_def in H3.
 assert (H3':=H3).
 apply fst_WF_inv in H3; trivial.
 2:do 2 red; intros; apply Bw_morph; auto with *.
 specialize cc_prod_elim with (1:=H2) (2:=H3); clear H2; intro H2.
 apply snd_WF_inv in H3'; trivial.
 2:do 2 red; intros; apply Bw_morph; auto with *.
 apply El_prod_elim in H2.
 2:admit.
 apply eq_elim with (El
      (app (int0 (lift 2 P) (V.cons (snd (int0 n i)) (V.cons (fst (int0 n i)) i)))
         (couple (fst (int0 n i)) (snd (int0 n i))))).
  apply El_morph.
  apply app_ext.
   admit.
   admit.


  2:apply fst_def.
; auto with *.
  apply cc_prod_elim with (1:=H2).
 specialize cc_prod_elim with (1:=H2) (2:=H3); clear H2; intro H2.
 appl



with (3:=H3).
in H3.
rewrite realNati_def in H3; simpl in H3|-*; auto.
destruct H3.
apply Real_intro; intros.
 apply NATCASE_typ with (o:=int i O) (P:=fun n => El(app (int i P) n)); intros; trivial.
  do 2 red; intros.
  rewrite H9; reflexivity.

  do 2 red; intros.
  rewrite H9; reflexivity.

  assert (val_ok (NatI O :: e) (V.cons n0 i) (I.cons daimon j)).
   apply vcons_add_var; trivial.
   2:discriminate.
   rewrite realNati_def; auto with *.
   split; trivial.
   apply varSAT.
  apply H2 in H10; clear H1; simpl in H10.
  apply in_int_not_kind in H10;[|discriminate].
  destruct H10 as(H10,_ ).
  revert H10; apply eq_elim; simpl.
  rewrite int_cons_lift_eq.
  rewrite beta_eq; auto with *.
   red; intros; apply inr_morph; auto.

   rewrite El_def.
   rewrite int_cons_lift_eq; trivial.

 apply Real_NATCASE with
   (C:=fun n => Real (app (int0 P i) n) (NATCASE (int0 fZ i) (fun k => int0 fS (V.cons k i)) n)) (o:=int0 O i); auto.
  do 2 red; intros.
  apply Real_morph.
   rewrite H10; reflexivity.

   apply NATCASE_morph; auto with *.
   red; intros.
   rewrite H11; reflexivity.

  rewrite NATCASE_ZERO; trivial.

  apply piSAT0_intro.
   apply typ_abs in H2.
   3:discriminate.
   2:left.
   2:apply typ_natI with o; trivial.
   apply H2 in H4.
   apply in_int_sn in H4.
   eapply Lc.subterm_sn.
   eapply Lc.subterm_sn.
   eexact H4.
   apply Lc.sbtrm_app_l.
   apply Lc.sbtrm_app_r.

   intros.
   apply inSAT_exp; [apply sat_sn in H11; auto|].
   rewrite <- tm_subst_cons.
   rewrite NATCASE_SUCC.
   2:intros ? e'; rewrite e'; reflexivity.
   assert (val_ok (NatI O :: e) (V.cons x i) (I.cons u j)).
    apply vcons_add_var; trivial.
    2:discriminate.
    rewrite realNati_def; auto with *.
   apply H2 in H12.
   apply in_int_not_kind in H12.
   2:discriminate.
   destruct H12 as (_,H12).
   simpl in H12.
   rewrite int_lift_eq in H12.
   revert H12; apply inSAT_morph; trivial.
   apply Real_morph; auto with *.
   apply cc_app_morph; [reflexivity|].
   unfold app, lam; rewrite cc_beta_eq; auto with *.
   rewrite El_def.
   rewrite int_lift_eq; trivial.
Qed.
Print Assumptions typ_natcase.

Lemma typ_natcase' : forall o e O P fZ fS n T,
  isOrd o ->
  T <> kind ->
  typ e O (Ordt o) ->
  sub_typ e (App P n) T -> 
  typ e fZ (App P Zero) ->
  typ (NatI O :: e) fS
    (App (lift 1 P) (App (Succ (lift 1 O)) (Ref 0))) ->
  typ e n (NatI (OSucc O)) ->
  typ e (Natcase fZ fS n) T.
intros.
apply typ_subsumption with (App P n); auto.
2:discriminate.
apply typ_natcase with o O; trivial.
Qed.

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
  [f,tf] \real prod (int i T) (fun x => int (V.cons x i) U) ->
  [g,tg] \real prod (int i' T) (fun x => int (V.cons x i') U) ->
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
rewrite intProd_eq in H3|-*.
specialize (H0 _ _ _ _ H2).
destruct H3.
unfold inX in H3.
rewrite Real_prod in H4; trivial.
 unfold prod in H3; rewrite El_def in H3.
 assert (x ∈ El(prod (int i' T) (fun x0 : X => int (V.cons x0 i') U))).
  unfold prod, inX; rewrite El_def.
  revert H3; apply cc_prod_covariant.
   do 2 red; intros.
   rewrite H5; reflexivity.

   rewrite H0; reflexivity.

   intros.
   red in H1.
   assert (val_mono (push_var e T) (V.cons x0 i) (I.cons daimon j) (V.cons x0 i') (I.cons daimon j')).
    apply val_push_var; auto with *.
    split; trivial; apply varSAT.
    split.
     rewrite <- H0; trivial.
     apply varSAT.
   specialize (H1 _ _ _ _ H5).
   red; intros.
   destruct H1 with z daimon; trivial.
   split; trivial.
   apply varSAT.
 split; trivial.
 rewrite Real_prod; trivial.
  unfold piSAT.
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
      rewrite <- H0; trivial.
      apply varSAT.

     split; trivial.
     unfold inX; apply cc_prod_elim with (1:=H3); trivial.

  red; intros.
  rewrite H7; reflexivity.

 red; intros.
 rewrite H6; reflexivity.
Qed.

  Lemma NATi_sub : forall e o O,
    isOrd o ->
    typ (tenv e) O (Ordt o) ->
    fx_subval e O ->
    fx_sub e (NatI O).
unfold fx_sub, fx_subval; intros.
destruct tyord_inv with (2:=H0) (3:=proj1 H2); trivial.
destruct tyord_inv with (2:=H0) (3:=proj1 (proj2 H2)); trivial.
specialize H1 with (1:=H2).
rewrite realNati_def in H3|-*; trivial.
destruct H3.
split.
 revert H3; apply TI_mono; auto.

 rewrite <- fNATi_mono with (3:=H1); auto.
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
unfold fx_sub, fx_equals, fx_extends; intros.
specialize H0 with (1:=H4).
simpl.
red; intros.
fold app.
rewrite beta_eq; try assumption.
 rewrite beta_eq.
  apply H1 with (I.cons daimon j) (I.cons daimon j').
  apply val_push_var; auto with *.
   split; [trivial|apply varSAT].

   split; [trivial|apply varSAT].
   destruct H0 with x daimon; trivial.
   split; [trivial|apply varSAT].

  red; red; intros.
  rewrite H7; reflexivity.

  apply H0 with (x:=x) (t:=daimon); trivial.
  split; [trivial|apply varSAT].

 red; red; intros.
 rewrite H7; reflexivity.
Qed.

(*
Lemma Natcase_fx_eq : forall o e O f1 f2 c,
  isOrd o ->
  typ (tenv e) O (Ord o) ->
  fx_sub e O ->
  fx_equals e f1 ->
  fx_equals (push_var e (NatI O)) f2 ->
  typ (tenv e) c (NatI (OSucc O)) ->
  fx_equals e c ->
  fx_equals e (Natcase f1 f2 c).
red; intros o e O f1 f2 c H tyO H0 H1 H2 tyc H3 i i' H4.
simpl.
assert (ord : isOrd (int O i)).
 destruct H4 as (H4,_); apply tyO in H4.
 apply isOrd_inv with o; trivial.
assert (ord' : isOrd (int O i')).
 destruct H4 as (_,(H4,_)); apply tyO in H4.
 apply isOrd_inv with o; trivial.
assert (int c i ∈ NATi (osucc (int O i))).
 destruct H4 as (H4,_).
 apply tyc in H4; trivial.
apply NATCASE_morph_gen; intros; auto.
 apply H3; trivial.

 apply H1; trivial.

 apply H2.
 red in H0; specialize H0 with (1:=H4).
 rewrite H6 in H5.
 apply SUCCi_inv_typ in H5; auto.
 apply val_push_var; simpl; auto.
 rewrite <- H7.
 clear H6 H7 x'; revert x H5.
 apply TI_mono; auto.
Qed.

*)

(*****************************************************************************)
(** Recursor (without case analysis) *)

(* NatFix O M is a fixpoint of domain Nati O with body M *)
Definition NatFix (O M:trm) : trm.
(*begin show*)
left.
exists (fun i =>
         NATREC (fun o' f => int (V.cons f (V.cons o' i)) M) (int i O))
       (fun j => NATFIX (Lc.Abs (tm (Lc.ilift (I.cons (tm j O) j)) M))).
(*end show*)
 do 2 red; intros.
 apply NATREC_morph.
  do 2 red; intros.
  apply int_morph; auto with *.
  apply V.cons_morph; trivial.
  apply V.cons_morph; trivial.

  apply int_morph; auto with *.

 (* *)
 do 2 red; intros.
 rewrite H; reflexivity.

 (* *)
 red; intros.
 replace (Lc.lift_rec 1
     (NATFIX (Lc.Abs (tm (Lc.ilift (I.cons (tm j O) j)) M))) k) with
   (NATFIX (Lc.lift_rec 1 (Lc.Abs (tm (Lc.ilift (I.cons (tm j O) j)) M)) k)).
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
  unfold NATFIX, FIXP; simpl.
  rewrite <- Lc.permute_lift.
  reflexivity.

 (* *)
 red; intros.
 replace (Lc.subst_rec u
     (NATFIX (Lc.Abs (tm (Lc.ilift (I.cons (tm j O) j)) M))) k) with
   (NATFIX (Lc.subst_rec u (Lc.Abs (tm (Lc.ilift (I.cons (tm j O) j)) M)) k)).
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
  unfold NATFIX, FIXP; simpl.
  rewrite <- Lc.commut_lift_subst.
  reflexivity.
Defined.


(** Typing rules of NatFix *)

Section NatFixRules.

  Variable infty : set.
  Hypothesis infty_ord : isOrd infty.
  Variable E : fenv.
  Let e := tenv E.
  Variable O U M : trm.
  Hypothesis M_nk : ~ eq_trm M kind.
  Hypothesis ty_O : typ e O (Ordt infty).
  Hypothesis ty_M : typ (Prod (NatI (Ref 0)) U::OSucct O::e)
    M (Prod (NatI (OSucc (Ref 1)))
         (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U)))).

  Hypothesis stab : fx_extends
    (push_fun (push_ord E (OSucct O)) (NatI (Ref 0)) U)
    (NatI (OSucc (Ref 1)))
    M.

  Let F i := fun o' f => int (V.cons f (V.cons o' i)) M.

  Lemma morph_fix_body : forall i, morph2 (F i).
unfold F; do 3 red; intros.
rewrite H; rewrite H0; reflexivity.
Qed.

  Lemma ext_fun_ty : forall o i,
    ext_fun (NATi o) (fun x => int (V.cons x (V.cons o i)) U).
do 2 red; intros.
rewrite H0;reflexivity.
Qed.

  Hypothesis fx_sub_U :
    fx_sub (push_var (push_ord E (OSucct O)) (NatI (OSucc (Ref 0)))) U.

  Lemma ty_fix_body : forall i j o f,
   val_ok e i j ->
   o < osucc (int i O) ->
   f ∈ cc_prod (NATi o) (fun x => El(int (V.cons x (V.cons o i)) U)) ->
   F i o f ∈
   cc_prod (NATi (osucc o)) (fun x => El(int (V.cons x (V.cons (osucc o) i)) U)).
unfold F; intros.
destruct tyord_inv with (2:=ty_O) (3:=H); trivial.
red in ty_M.
assert (val_ok (Prod (NatI(Ref 0)) U::OSucct O::e)
  (V.cons f (V.cons o i)) (I.cons daimon (I.cons daimon j))).
 apply vcons_add_var; auto.
 3:discriminate.
  apply vcons_add_var; auto.
  2:discriminate.
  split;[|apply varSAT].
  unfold inX; simpl; rewrite El_def; trivial.

  split;[|apply varSAT].
  rewrite intProd_eq.
  unfold inX, prod; rewrite El_def.
  revert H1; apply eq_elim.
  apply cc_prod_ext.
   simpl; rewrite El_def; reflexivity.

   red; intros.
   rewrite H4; reflexivity.
specialize ty_M with (1:=H4).
apply in_int_not_kind in ty_M.
2:discriminate.
destruct ty_M as (?,_).
rewrite intProd_eq in H5; unfold inX in H5.
unfold prod in H5; rewrite El_def in H5.
revert H5; apply eq_elim.
symmetry; apply cc_prod_ext.
 simpl; rewrite El_def.
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
    NAT_ord_irrel (int i O) (F i) (fun o' x => El(int (V.cons x (V.cons o' i)) U)).
red; red; intros.
assert (isOrd (int0 O i)).
 apply ty_O in H.
 apply isOrd_inv with infty; auto.
 apply in_int_not_kind in H;[|discriminate].
 destruct H; simpl in H.
 red in H; rewrite El_def in H; trivial.
red in stab.
assert (Hstab := stab (V.cons f (V.cons o i)) (V.cons g (V.cons o' i))).
simpl in Hstab.
red in Hstab.
eapply Hstab; clear Hstab; trivial.
2:rewrite El_def; auto.
apply val_push_fun.
 apply val_push_ord; auto.
  apply val_mono_refl; exact H.

  split;[|apply varSAT].
  red; simpl.
  rewrite El_def.
  apply ole_lts; trivial.
  transitivity o'; trivial.

  split;[|apply varSAT].
  red; simpl.
  rewrite El_def.
  apply ole_lts; trivial.

  discriminate.

 split;[|apply varSAT].
 red; simpl.
 unfold prod; rewrite El_def.
 revert H4; apply eq_elim; apply cc_prod_ext.
  rewrite El_def; reflexivity.

  red; intros.
  rewrite H9; reflexivity.

 split;[|apply varSAT].
 red; simpl.
 unfold prod; rewrite El_def.
 revert H5; apply eq_elim; apply cc_prod_ext.
  rewrite El_def; reflexivity.

  red; intros.
  rewrite H9; reflexivity.

 red; intros.
 simpl in H9; rewrite El_def in H9.
 auto.
Qed.

  Lemma val_mono_2 i j y y' n n':
    val_ok e i j ->
    isOrd (int0 O i) ->
    isOrd y ->
    isOrd y' ->
    y ⊆ y' ->
    y' ⊆ int0 O i ->
    n ∈ NATi y ->
    n == n' ->
    val_mono (push_var (push_ord E (OSucct O)) (NatI (OSucc (Ref 0))))
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
  unfold inX; simpl; rewrite El_def; apply ole_lts; auto.
  transitivity y'; trivial.

  split;[|apply varSAT].
  unfold inX; simpl; rewrite El_def; apply ole_lts; auto.

 rewrite realNati_def.
 2:simpl; auto.
 split;[|apply varSAT].
 simpl.
 revert H5; apply TI_incl; auto with *.

 rewrite realNati_def.
 2:simpl; auto.
 split;[|apply varSAT].
 simpl.
 rewrite <- H6; revert H5; apply TI_incl; auto with *.
 apply isOrd_plump with y'; auto with *.
 apply lt_osucc; trivial.
Qed.


  Lemma fix_codom_mono : forall o o' x x' i j,
   val_ok e i j ->
   isOrd o' ->
   o' ⊆ int i O ->
   isOrd o ->
   o ⊆ o' ->
   x ∈ NATi o ->
   x == x' ->
   El (int (V.cons x (V.cons o i)) U) ⊆ El(int (V.cons x' (V.cons o' i)) U).
Proof.
intros.
red in fx_sub_U.
assert (val_mono (push_var (push_ord E (OSucct O)) (NatI(OSucc(Ref 0))))
  (V.cons x (V.cons o i)) (I.cons daimon (I.cons daimon j))
  (V.cons x' (V.cons o' i)) (I.cons daimon (I.cons daimon j))).
 apply val_mono_2; trivial.
 apply ty_O in H.
 apply in_int_not_kind in H;[|discriminate].
 destruct H; red in H; simpl in H.
 rewrite El_def in H.
 apply isOrd_inv with infty; auto.

red; intros.
apply fx_sub_U with (x:=z)(t:=daimon) in H6.
 destruct H6; trivial.

 split; trivial.
 apply varSAT.
Qed.
  Hint Resolve morph_fix_body ext_fun_ty ty_fix_body fix_codom_mono fix_body_irrel.


Let fix_typ o i j:
  val_ok e i j ->
  isOrd o ->
  isOrd (int i O) ->
  o ⊆ int i O ->
  NATREC (F i) o
   ∈ cc_prod (NATi o) (fun n => El (int (V.cons n (V.cons o i)) U)).
intros.
eapply NATREC_wt with (U:=fun o n => El(int(V.cons n (V.cons o i))U)); trivial.
 intros.
 apply fix_codom_mono with (1:=H); trivial.
 transitivity o; trivial.

 intros; apply ty_fix_body with (1:=H); trivial.
 apply isOrd_plump with (int i O); auto.
  transitivity o; trivial.

  apply lt_osucc; trivial.

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
    x ∈ NATi o ->
    cc_app (NATREC (F i) o) x == cc_app (NATREC (F i) o') x.
intros.
apply NATREC_ord_irrel with 
  (ord:=int i O)
  (U:=fun o x => El (int0 U (V.cons x (V.cons o i)))); auto.
 intros.
 apply fix_codom_mono with (1:=H); trivial.

 intros; apply ty_fix_body with (1:=H); trivial.
 apply isOrd_plump with (int i O); auto.
 apply lt_osucc; trivial.

 red; intros; apply fix_body_irrel with (1:=H); trivial.
Qed.



Lemma fix_eqn : forall i j o n,
  val_ok e i j ->
  isOrd o ->
  isOrd (int i O) ->
  o ⊆ int i O ->
  n ∈ NATi (osucc o) ->
  cc_app (NATREC (F i) (osucc o)) n ==
  cc_app (int (V.cons (NATREC (F i) o) (V.cons o i)) M) n.
intros.
unfold NATREC at 1.
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
         cc_prod (NATi (osucc x)) (fun n => El (int (V.cons n (V.cons (osucc x) i)) U))).
  apply ty_fix_body with (1:=H); trivial.
   apply ole_lts; auto.

   apply fix_typ with (1:=H); trivial.
 assert (F i o (NATREC (F i) o) ∈ 
         cc_prod (NATi (osucc o)) (fun n => El (int (V.cons n (V.cons (osucc o) i)) U))).
  apply ty_fix_body with (1:=H).
   apply ole_lts; trivial.

   apply fix_typ with (1:=H); trivial.
 rewrite cc_eta_eq with (1:=H6) in H5.
 unfold F at 1 in H7; rewrite cc_eta_eq with (1:=H7).
 rewrite cc_lam_def in H5|-*.
  destruct H5.
  destruct H8.
  exists x0.
   revert H5; apply TI_mono; auto with *.
   apply osucc_mono; auto.
  exists x1; trivial.
  revert H8; apply eq_elim.
  do 2 red in stab.
  apply stab with (I.cons daimon (I.cons daimon j)) (I.cons daimon (I.cons daimon j)).
   apply val_push_fun.
    apply val_push_ord; trivial.
     apply val_mono_refl; trivial.

     split;[|apply varSAT].
     unfold inX; simpl; rewrite El_def; apply ole_lts; auto.

     split;[|apply varSAT].
     unfold inX; simpl; rewrite El_def; apply ole_lts; auto.

     discriminate.

    split;[|apply varSAT].
    unfold inX,prod; rewrite El_def.
    eapply eq_elim.
    2:eapply fix_typ with (1:=H); auto.
    apply cc_prod_ext.
     simpl; rewrite El_def; reflexivity.

     red; intros.
     rewrite H10; reflexivity.

    split;[|apply varSAT].
    unfold inX,prod; rewrite El_def.
    eapply eq_elim.
    2:eapply fix_typ with (1:=H); auto.
    apply cc_prod_ext.
     simpl; rewrite El_def; reflexivity.

     red; intros.
     rewrite H10; reflexivity.

    red; intros.
    apply fix_irr with (1:=H); auto with *.
    simpl in H8; rewrite El_def in H8; trivial.

   simpl; rewrite El_def; trivial.

  do 2 red; intros; apply cc_app_morph; auto with *.
  do 2 red; intros; apply cc_app_morph; auto with *.

 apply sup_incl with (F:=fun o'=>F i o'(REC (F i) o')); auto with *.
 apply lt_osucc; trivial.
Qed.


Lemma nat_fix_eqn : forall i j,
  val_ok e i j ->
  NATREC (F i) (int i O) ==
  cc_lam (NATi (int i O))
    (fun x => cc_app (F i (int i O) (NATREC (F i) (int i O))) x).
intros.
destruct tyord_inv with (2:=ty_O) (3:=H); trivial.
apply NATREC_eqn with
  (ord:=int i O)
  (U:=fun o x => El (int0 U (V.cons x (V.cons o i)))); auto.
 intros.
 apply fix_codom_mono with (1:=H); trivial.

 intros; apply ty_fix_body with (1:=H); trivial.
 apply isOrd_plump with (int i O); auto.
 apply lt_osucc; trivial.

 red; intros; apply fix_body_irrel with (1:=H); trivial.
Qed.


(*
Lemma equiv_piSAT_piNAT o B B' f:
isOrd o ->
(forall n, n ∈ NATi o -> eqSAT (Real (B n) (f n)) (B' n)) ->
eqSAT (piSAT (mkTY (NATi o) cNAT) B f)
      (piNATi (fun n => prodSAT (cNAT n) (B' n)) o).
intros.
red; intro.
unfold piSAT, piNATi.
apply interSAT_morph.
split; intros.
 destruct x as (n,xty); simpl proj1_sig.
 simpl in xty; rewrite El_def in xty.
 exists (exist (fun n=>n ∈ NATi o) n xty); simpl proj1_sig.
 apply prodSAT_morph; auto.
 rewrite Real_def; auto with *.
 intros; apply fam_mrph; trivial.
 revert H1; apply NATi_NAT; simpl; auto.

 destruct y as (n,xty); simpl proj1_sig.
 assert (nty : n ∈ El (mkTY (NATi o) cNAT)).
  rewrite El_def; trivial.
 exists (exist (fun n=>n ∈ El(mkTY (NATi o) cNAT)) n nty); simpl proj1_sig.
 apply prodSAT_morph; auto.
 rewrite Real_def; auto with *.
 intros; apply fam_mrph; trivial.
 revert H1; apply NATi_NAT; simpl; auto.
Qed.
*)
(*
Lemma indexed_relation_equiv A B (R:B->B->Prop) (P P':A->Prop) (G G':A->B) :
  (forall x:A, P x <-> P' x) -> 
  (forall x:A, P x -> R (G x) (G' x)) ->
  indexed_relation R (fun x:sig P => G (proj1_sig x)) (fun x:sig P' => G' (proj1_sig x)).
split; intros (i,?); simpl.
 pose (p' := p).
 apply H in p'.
 exists (exist _ i p').
 simpl; auto.

 apply H in p.
 exists (exist _ i p); simpl; auto.
Qed.
*)
Lemma typ_nat_fix :
  typ e (NatFix O M) (Prod (NatI O) (subst_rec O 1 U)).
red; intros.
destruct tyord_inv with (2:=ty_O)(3:=H); trivial.
apply in_int_intro.
discriminate.
discriminate.
assert (int i (NatFix O M) ∈ El(int i (Prod (NatI O) (subst_rec O 1 U)))).
 rewrite intProd_eq.
 eapply eq_elim.
 2:simpl.
 2:apply fix_typ with (1:=H); auto with *.
 unfold prod; rewrite El_def; apply cc_prod_ext.
  simpl; rewrite El_def; auto with *.

  red; intros.
  rewrite int_subst_rec_eq.
  apply El_morph.
  apply int_morph; auto with *.
  intros [|[|k]]; try reflexivity.
  exact H3.
split; trivial.
rewrite intProd_eq.
rewrite Real_prod; trivial.
2:red; intros ? ? ? eqn; rewrite eqn; reflexivity.
simpl tm.
unfold piSAT.
cut (inSAT (NATFIX (Lc.Abs (tm (Lc.ilift (I.cons (tm j O) j)) M)))
       (piSAT0 (fun n => n ∈ NATi (int0 O i)) (fNATi (int0 O i))
          (fun n =>Real (int0 U (V.cons n (V.cons (int0 O i) i)))
                    (cc_app (NATREC (F i) (int0 O i)) n)))).
 apply interSAT_morph_subset.
  intros; simpl; rewrite El_def; reflexivity.

  simpl; intros.  
  apply prodSAT_morph.
   rewrite Real_def; trivial.
    reflexivity.

    intros.
    rewrite H4; reflexivity.

   apply Real_morph; [|reflexivity].
   rewrite int_subst_rec_eq.
   apply int_morph; auto with *.
   intros [|[|k]]; reflexivity.

apply NATFIX_sat with (X:=fun o n => Real (int0 U (V.cons n (V.cons o i)))
   (cc_app (NATREC (F i) o) n)); trivial.
 red; intros.
 red in fx_sub_U.
 apply fx_sub_U with (V.cons n (V.cons y i))
    (I.cons daimon (I.cons daimon j)) (I.cons daimon (I.cons daimon j)).
  apply val_mono_2; auto with *.
  rewrite <- fix_irr with (1:=H) (o:=y); auto.
  split; trivial.
  unfold inX.
  apply cc_prod_elim with (dom:=NATi y) (F:=fun n=>El(int(V.cons n (V.cons y i))U)); trivial.
  apply fix_typ with (1:=H); trivial.
  transitivity y'; trivial.

 (* sat body *)
 apply interSAT_intro.
  exists (int i O); auto.
  apply lt_osucc; auto.

  intros.
  destruct x as (o',?); simpl proj1_sig.
  cbv zeta.
  apply prodSAT_intro; intros.
  assert (val_ok (Prod (NatI(Ref 0)) U::OSucct O::e)
    (V.cons (NATREC (F i) o') (V.cons o' i)) (I.cons v (I.cons (tm j O) j))).
   apply vcons_add_var.
    3:discriminate.
    apply vcons_add_var; trivial.
    2:discriminate.
    split.
     unfold inX; simpl; rewrite El_def; trivial.

     simpl int; rewrite Real_def; auto with *.
     apply ty_O in H.
     apply in_int_sn in H; trivial.

    rewrite intProd_eq.
    assert (NATREC (F i) o' ∈ cc_prod (NATi o')
              (fun x => El(int(V.cons x(V.cons o' i)) U))).
     apply fix_typ with (1:=H); trivial.
      eauto using isOrd_inv.
      apply olts_le in i0; trivial.
    split.
     unfold inX, prod; rewrite El_def.
     revert H4; apply eq_elim; apply cc_prod_ext.
      simpl; rewrite El_def; reflexivity.

      red; intros.
      rewrite H5; reflexivity.

     rewrite Real_prod.
      revert H3; apply interSAT_morph_subset.
       simpl; intros; rewrite El_def; auto.

       simpl; intros.
       apply prodSAT_morph.
        rewrite Real_def; auto with *.
        intros ? ? ? eqn; rewrite eqn; reflexivity.

        reflexivity.

      red; intros.
      rewrite H6; reflexivity.

      eapply eq_elim.
      2:apply fix_typ with (1:=H); auto with *.
      2:   eauto using isOrd_inv.
      2:   apply olts_le; trivial.
      unfold prod; rewrite El_def; apply cc_prod_ext.
       simpl; rewrite El_def; auto with *.

       red; intros.
       rewrite H6; reflexivity.

  red in ty_M; specialize ty_M with (1:=H4).
  apply in_int_not_kind in ty_M.
  2:discriminate.
  destruct ty_M.
  replace (Lc.subst v (tm (Lc.ilift (I.cons (tm j O) j)) M))
     with (tm (I.cons v (I.cons (tm j O) j)) M).
   rewrite intProd_eq in H6.
   rewrite Real_prod in H6; trivial.
    revert H6; apply interSAT_morph_subset.
     simpl; intros.
     rewrite El_def; reflexivity.

     simpl; intros.
     apply prodSAT_morph.
      rewrite Real_def; trivial.
       reflexivity.

       intros ? ? ? eqn; rewrite eqn; reflexivity.

      apply Real_morph.
       rewrite int_lift_rec_eq.
       rewrite int_subst_rec_eq.
       rewrite int_lift_rec_eq.
       apply int_morph; auto with *.
       intros [|[|k]]; try reflexivity.
       compute; fold minus.
       replace (k-0) with k; auto with *.

       apply fix_eqn with (1:=H); auto.
        eauto using isOrd_inv.
        apply olts_le; trivial.

    red; intros.
    rewrite H8; reflexivity.

   unfold Lc.subst; rewrite <- tm_substitutive.
   apply tm_morph; auto with *.
   intros [|[|k]].
    unfold Lc.ilift,I.cons; simpl.
    rewrite Lc.lift0; trivial.

    unfold Lc.ilift,I.cons; simpl.
    rewrite Lc.simpl_subst; trivial.
    rewrite Lc.lift0; trivial.

    unfold Lc.ilift,I.cons; simpl.
    rewrite Lc.simpl_subst; trivial.
    rewrite Lc.lift0; trivial.
Qed.


Lemma nat_fix_eq : forall N,
  typ e N (NatI O) ->
  eq_typ e (App (NatFix O M) N)
           (App (subst O (subst (lift 1 (NatFix O M)) M)) N).
red; intros.
unfold eqX.
change
 (app (NATREC (F i) (int i O)) (int i N) ==
  app (int i (subst O (subst (lift 1 (NatFix O M)) M))) (int i N)).
do 2 rewrite <- int_subst_eq.
rewrite int_cons_lift_eq.
rewrite nat_fix_eqn with (1:=H0); trivial.
rewrite cc_beta_eq.
 reflexivity.

 do 2 red; intros.
 rewrite H2; reflexivity.

 red in H; specialize H with (1:=H0).
 apply in_int_not_kind in H.
  destruct H.
  unfold inX in H; simpl in H; rewrite El_def in H; trivial.

  discriminate.
Qed.

Lemma nat_fix_extend :
  fx_subval E O ->
  fx_extends E (NatI O) (NatFix O M).
intro subO.
do 2 red; intros.
simpl in H0; rewrite El_def in H0.
assert (isval := proj1 H).
assert (isval' := proj1 (proj2 H)).
assert (oo: isOrd (int i O)).
 destruct tyord_inv with (2:=ty_O) (3:=isval); trivial.
assert (oo': isOrd (int i' O)).
 destruct tyord_inv with (2:=ty_O) (3:=isval'); trivial.
assert (inclo: int i O ⊆ int i' O).
 apply subO in H; trivial.
clear subO.
change (cc_app (NATREC (F i) (int i O)) x == cc_app (NATREC (F i') (int i' O)) x).
revert x H0.
elim oo using isOrd_ind; intros.
apply TI_elim in H3; auto.
destruct H3 as (o',?,?).
assert (o_o' : isOrd o') by eauto using isOrd_inv.
rewrite <- TI_mono_succ in H4; auto with *.
rewrite <- fix_irr with (1:=isval) (o:=osucc o'); auto.
 rewrite fix_eqn with (1:=isval); auto.
 rewrite <- fix_irr with (1:=isval') (o:=osucc o'); auto with *.
  rewrite fix_eqn with (1:=isval'); auto.
  do 2 red in stab.
  apply stab with (I.cons daimon (I.cons daimon j)) (I.cons daimon (I.cons daimon j')).
   apply val_push_fun.
    apply val_push_ord; auto with *.
     split;[|apply varSAT].
     unfold inX; simpl; rewrite El_def; apply ole_lts; auto.

     split;[|apply varSAT].
     unfold inX; simpl; rewrite El_def; apply ole_lts; auto.

     discriminate.

    split;[|apply varSAT].
    unfold inX,prod; rewrite El_def.
    eapply eq_elim.
    2:eapply fix_typ with (1:=isval); auto.
    apply cc_prod_ext.
     simpl; rewrite El_def; reflexivity.

     red; intros.
     rewrite H6; reflexivity.

    split;[|apply varSAT].
    unfold inX,prod; rewrite El_def.
    eapply eq_elim.
    2:eapply fix_typ with (1:=isval'); auto.
    apply cc_prod_ext.
     simpl; rewrite El_def; reflexivity.

     red; intros.
     rewrite H6; reflexivity.

    red; intros.
    simpl in H5; rewrite El_def in H5.
    rewrite fix_irr with (1:=isval') (o':=int i' O); auto with *.


   simpl; rewrite El_def; trivial.

  red; intros.
  apply inclo; apply H1.
  apply le_lt_trans with o'; trivial.

 red; intros.
 apply le_lt_trans with o'; trivial.
Qed.

Lemma nat_fix_equals :
  fx_equals E O ->
  fx_equals E (NatFix O M).
red; intros.
assert (fxs: fx_subval E O).
 apply fx_equals_subval; trivial.
apply nat_fix_extend in fxs.
red in fxs.
specialize fxs with (1:=H0).
apply fcompat_typ_eq with (3:=fxs).
 eapply cc_prod_is_cc_fun.
 assert (h := typ_nat_fix _ _ (proj1 H0)).
 apply in_int_not_kind in h.
 2:discriminate.
 destruct h.
 rewrite intProd_eq in H1.
 unfold inX, prod in H1; rewrite El_def in H1.
 eexact H1.

 setoid_replace (int i (NatI O)) with (int i' (NatI O)).
  eapply cc_prod_is_cc_fun.
  assert (h := typ_nat_fix _ _ (proj1 (proj2 H0))).
  apply in_int_not_kind in h.
  2:discriminate.
  destruct h.
  rewrite intProd_eq in H1.
  unfold inX, prod in H1; rewrite El_def in H1.
  eexact H1.

  do 2 red.
  assert (h:= H _ _ _ _ H0).
  apply mkTY_ext.
   rewrite h; reflexivity.

   intros; apply fNATi_morph; trivial.
Qed.

End NatFixRules.

Print Assumptions typ_nat_fix.


Lemma typ_nat_fix' : forall infty e O U M T,
       T <> kind ->
       isOrd infty ->
       typ e O (Ordt infty) ->
       typ (Prod (NatI (Ref 0)) U :: OSucct O :: e) M
         (Prod (NatI (OSucc (Ref 1)))
           (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U)))) ->
       fx_extends (push_fun (push_ord (tinj e) (OSucct O)) (NatI (Ref 0)) U)
         (NatI (OSucc (Ref 1))) M ->
       fx_sub (push_var (push_ord (tinj e) (OSucct O)) (NatI (OSucc (Ref 0)))) U ->
       sub_typ e (Prod (NatI O) (subst_rec O 1 U)) T ->
       typ e (NatFix O M) T.
intros.
apply typ_subsumption with (Prod (NatI O) (subst_rec O 1 U)); auto.
2:discriminate.
change e with (tenv (tinj e)).
apply typ_nat_fix with (infty:=infty); trivial.
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

  Lemma NATi_fx_sub : forall e o O,
    isOrd o ->
    typ_monoval e O (Ordt o) ->
    fx_sub e (NatI O).
destruct 2.
apply NATi_sub with (o:=o); trivial.
Qed.

  Lemma OSucc_fx_sub : forall e O o,
    isOrd o ->
    typ_monoval e O (Ordt o)->
    typ_monoval e (OSucc O) (Ordt (osucc o)).
destruct 2.
split.
 apply OSucc_sub; trivial.

 red; simpl; intros.
 apply in_int_intro; try discriminate.
 assert (osucc (int i O) ∈ El (int i (Ordt (osucc o)))).
  simpl; rewrite El_def.
  apply lt_osucc_compat; trivial.
  destruct tyord_inv with (2:=H1)(3:=H2) as (_,(?,_)); trivial.
 split; trivial.
 unfold int at 1, Ordt, cst, iint.
 rewrite Real_def; auto with *.
  assert (h:= H1 _ _ H2).
  apply in_int_sn in h.
  simpl; trivial.

  simpl.
  apply lt_osucc_compat; trivial.
  destruct tyord_inv with (2:=H1)(3:=H2) as (_,(?,_)); trivial.
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
(*
Lemma impl_natcase : forall o e O P fZ fS n T,
       isOrd o ->
       typ_mono e O (Ordt o) ->
       sub_typ (tenv e) (App P n) T -> 
       typ_impl e fZ (App P Zero) ->
       typ_impl (push_var e (NatI O)) fS
         (App (lift 1 P) (App (Succ (lift 1 O)) (Ref 0))) ->
       typ_impl e n (NatI (OSucc O)) ->
       typ_impl e (Natcase fZ fS n) T.
intros.
destruct H0.
destruct H2.
destruct H3.
simpl in H7.
destruct H4.
split.
 apply Natcase_fx_eq with o O; trivial.

 apply typ_natcase' with o O P; trivial.
Qed.
*)

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


Lemma typ_nat_fix'' : forall infty e O U M T,
       isOrd infty ->
       T <> kind ->
       sub_typ (tenv e) (Prod (NatI O) (subst_rec O 1 U)) T ->
       typ (tenv e) O (Ordt infty) ->
       typ_mono (push_var (push_ord e (OSucct O)) (NatI (OSucc (Ref 0)))) U ->
       typ_ext (push_fun (push_ord e (OSucct O)) (NatI (Ref 0)) U)
         M (NatI (OSucc (Ref 1)))
           (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
       typ (tenv e) (NatFix O M) T.
intros.
destruct H3; destruct H4.
apply typ_subsumption with (2:=H1); trivial.
2:discriminate.
apply typ_nat_fix with infty; trivial.
Qed.

  Lemma typ_ext_fix : forall eps e O U M,
    isOrd eps ->
    typ_monoval e O (Ordt eps) ->
    typ_ext (push_fun (push_ord e (OSucct O)) (NatI (Ref 0)) U) M
      (NatI (OSucc (Ref 1))) (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    fx_sub (push_var (push_ord e (OSucct O)) (NatI (OSucc (Ref 0)))) U ->
    typ_ext e (NatFix O M) (NatI O) (subst_rec O 1 U).
intros eps e O U M eps_ord tyO tyM tyU.
destruct tyO as (inclO,tyO).
destruct tyM as (extM,tyM).
assert (tyF: typ (tenv e) (NatFix O M) (Prod (NatI O) (subst_rec O 1 U))).
 apply typ_nat_fix with eps; trivial.
split; trivial.
apply nat_fix_extend with eps U; trivial.
Qed.

  Lemma typ_impl_fix : forall eps e O U M,
    isOrd eps ->
    typ_impl e O (Ordt eps) ->
    typ_ext (push_fun (push_ord e (OSucct O)) (NatI (Ref 0)) U) M
      (NatI (OSucc (Ref 1))) (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    fx_sub (push_var (push_ord e (OSucct O)) (NatI (OSucc (Ref 0)))) U ->
    typ_impl e (NatFix O M) (Prod (NatI O) (subst_rec O 1 U)).
intros eps e O U M eps_ord tyO tyM tyU.
destruct tyO as (inclO,tyO).
destruct tyM as (extM,tyM).
assert (tyF: typ (tenv e) (NatFix O M) (Prod (NatI O) (subst_rec O 1 U))).
 apply typ_nat_fix with eps; trivial.
split; trivial.
apply nat_fix_equals with eps U; trivial.
Qed.


(*
(************************************************************************)
(** Two examples of derived principles:
    - the standard recursor for Nat
    - subtraction with size information
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
  apply NATi_fx_sub with (o:=osucc (osucc omega)); auto.
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
     assert (i 1 ∈ NATi (i 4)).
      generalize (H0 1 _ (eq_refl _)); simpl.
      unfold V.lams, V.shift; simpl.
      trivial.
     rewrite beta_eq.
      rewrite beta_eq; auto with *.
       reflexivity.
       red; intros; apply inr_morph; trivial.

      red; intros; apply inr_morph; trivial.

      apply NATi_NAT in H1; trivial.
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
      apply NATi_NAT in H1; trivial.
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


(* Subtraction *)

Definition minus O :=
  NatFix O
    (*o,Hrec*)
    (Abs (*n*) (NatI (OSucc (Ref 1)))
    (Abs (*m*) (NatI (Ord omega))
    (Natcase
       Zero
       (*n'*)
       (Natcase
         (Ref 2)
         (*m'*)
         (App (App (Ref 4) (Ref 1)) (Ref 0))
         (Ref 1))
       (Ref 1)))).

Definition minus_typ O := Prod (NatI O) (Prod (NatI (Ord omega)) (NatI (lift 2 O))).



Lemma minus_def :
  forall e infty O,
  isOrd infty ->
  typ e O (Ord infty) ->
  typ e (minus O) (minus_typ O).
intros.
unfold minus, minus_typ.
change e with (tenv (tinj e)).
apply typ_nat_fix'' with infty (Prod (NatI (Ord omega)) (NatI (Ref 2))); auto.
 (* sub *)
 apply sub_refl.
 apply eq_typ_prod.
  reflexivity.

  rewrite eq_subst_prod.
  apply eq_typ_prod.
   red; intros; simpl; reflexivity.

   red; intros; simpl.
   unfold lift; rewrite int_lift_rec_eq.
   rewrite V.lams0.
   unfold V.lams, V.shift; simpl; reflexivity.

 (* codom mono *)
 split;[|red; intros; simpl; exact I].
 apply fx_sub_prod.
  apply fx_eq_noc.
  red; simpl; reflexivity.

  apply NATi_sub with infty; trivial.
  simpl.
  apply typ_var0; split; [discriminate|].
  red; intros; simpl.
  unfold lift in H2; rewrite int_lift_rec_eq in H2.
  rewrite V.lams0 in H2.
  simpl in H2.
  apply le_lt_trans with (2:=H2); trivial.
  apply H0.
  red; intros.
  generalize (H1 (3+n) _ H3).
  destruct T as [(T,Tm)|]; simpl; trivial.

  apply var_sub.
  compute; reflexivity.

 (* fix body *)
 apply ext_abs; try discriminate.
  apply NATi_fx_sub with (o:=osucc infty); auto.
  apply OSucc_fx_sub; auto.
  eapply typ_var_mono.
   compute; reflexivity.
   simpl; reflexivity.
   discriminate.
  red; simpl; intros; trivial.
  apply weakening0 in H0; apply weakeningS with (A:=OSucct O) in H0.
  apply weakeningS with (A:=Prod(NatI(Ref 0))(Prod(NatI(Ord omega))(NatI(Ref 2)))) in H0.
  apply H0 in H1.
  simpl in H1.
  unfold lift in H1; rewrite int_lift_rec_eq in H1.
  apply le_lt_trans with (3:=H1); trivial.

 rewrite eq_lift_prod.
 rewrite eq_subst_prod.
 unfold lift1; rewrite eq_lift_prod.
 apply impl_abs.
  discriminate.

  red; intros; simpl.
  reflexivity.

  red; intros; simpl; auto with *.

 match goal with |- typ_impl ?e _ _ => set (E:=e) end.
 assert (typ_impl E (Ref 1) (NatI (OSucc (Ref 3)))).
  eapply typ_var_impl.
   compute; reflexivity.
   simpl; reflexivity.
   discriminate.
  apply sub_refl.
  red; intros; simpl; reflexivity.
 apply impl_natcase with infty (Ref 3)
    (Abs (NatI (OSucc (Ref 3))) (NatI (OSucc (Ref 4)))); auto.
  Focus 2.
  apply sub_refl.
  rewrite eq_typ_betar.
  3:discriminate.
   red; intros; simpl.
   unfold V.lams, V.shift; simpl.
   reflexivity.

   apply H1.

  (* ord *)
  eapply typ_var_mono.
   compute;reflexivity.
   simpl; reflexivity.
   discriminate.
  red; intros; simpl.
  unfold lift in H3; rewrite int_lift_rec_eq in H3.
  rewrite V.lams0 in H3.
  simpl in H3.
  apply le_lt_trans with (2:=H3); trivial.
  apply H0.
  red; intros.
  generalize (H2 (4+n) _ H4).
  destruct T as [(T,Tm)|]; simpl; auto.

  (* branch 0 *)
  split.
   red; intros; simpl; reflexivity.
  assert (tyz : typ (tenv E) Zero (NatI (OSucc (Ref 3)))).
    apply typ_Zero with infty; trivial.
    apply typ_var0; split; [discriminate|].
    red; intros; simpl.
    unfold lift in H3; rewrite int_lift_rec_eq in H3.
    rewrite V.lams0 in H3.
    simpl in H3.
    apply le_lt_trans with (2:=H3); trivial.
    apply H0.
    red; intros.
    generalize (H2 (4+n) _ H4).
    destruct T as [(T,Tm)|]; simpl; trivial.
  apply typ_conv with (NatI (OSucc (Ref 3))); trivial.
  2:discriminate.
  rewrite eq_typ_betar; trivial.
  2:discriminate.
  red; intros; simpl.
  reflexivity.

  (* branch S *)
  assert (typ_impl (push_var E (NatI (Ref 3))) (Ref 1) (NatI (Ord (osucc omega)))).
   eapply typ_var_impl.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.
   apply sub_refl.
   red; intros; simpl.
   unfold NATi at 2; rewrite TI_mono_succ; auto.
   apply NAT_eq.
  apply impl_natcase with (osucc omega) (Ord omega)
     (Abs (NatI (OSucct (Ord omega))) (NatI (OSucc (Ref 5)))); auto.
   Focus 2.
   apply sub_refl.
   rewrite eq_typ_betar.
   3:discriminate.
    unfold lift; rewrite eq_lift_abs.
    rewrite eq_typ_betar.
    3:discriminate.
     red; intros; simpl; reflexivity.
     apply typ_conv with (NatI (OSucc (lift_rec 1 0 (Ref 3)))).
     3:discriminate.
      apply typ_SuccI with (o:=infty); trivial.
      apply typ_var0; split;[discriminate|].
      red; intros; simpl.
      unfold lift in H4; rewrite int_lift_rec_eq in H4.
      rewrite V.lams0 in H4.
      simpl in H4.
      apply le_lt_trans with (2:=H4); trivial.
      apply H0.
      red; intros.
      generalize (H3 (5+n) _ H5).
      destruct T as [(T,Tm)|]; simpl; trivial.

      apply typ_var0; split;[discriminate|].
      apply sub_refl; red; intros; simpl.
      reflexivity.

     red; intros; simpl.
     reflexivity.

     apply H2.

   (* ord *)
   split.
    red; intros; simpl; reflexivity.

    red; intros; simpl.
    apply lt_osucc; trivial.

  (* branch 0 *)
  eapply typ_var_impl.
   compute; reflexivity.
   simpl; reflexivity.
   discriminate.
  apply sub_refl.
  rewrite eq_typ_betar.
  3:discriminate.
   red; intros; simpl.
   unfold V.lams, V.shift; simpl; reflexivity.

   eapply typ_Zero with (osucc omega); auto.
   red; intros; simpl.
   apply lt_osucc; trivial.

  (* branch S *)    
  apply impl_app with (NatI (Ord omega)) (NatI (OSucc (Ref 6))).
   discriminate.
   discriminate.

   unfold lift; rewrite eq_lift_abs.
   apply sub_refl.
   rewrite eq_typ_betar.
   3:discriminate.
    red; intros; simpl.
    unfold V.lams, V.shift; simpl.
    reflexivity.

    apply typ_conv with (NatI (OSucc (lift_rec 1 0 (Ord omega)))).
    3:discriminate.
     apply typ_SuccI with (o:=osucc omega); auto.
      red; intros; simpl.
      apply lt_osucc; trivial.

      apply typ_var0; split;[discriminate|].
      apply sub_refl; red; intros; simpl.
      reflexivity.

     red; intros; simpl.
     reflexivity.

   eapply impl_call.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.
    2:simpl; reflexivity.
    discriminate.

    unfold subst, lift1; rewrite eq_lift_prod.
    rewrite eq_subst_prod.
    apply sub_typ_covariant.
     red; intros; simpl; reflexivity.

     red; intros; simpl.
     rewrite int_subst_rec_eq in H4.
     simpl in H4; unfold V.lams, V.shift in H4; simpl in H4.
     assert (isOrd (i 6)).
      generalize (H3 6 _ (reflexivity _)).
      simpl; intro.
      rewrite V.lams0 in H5.
      apply isOrd_inv with (2:=H5).      
      apply isOrd_succ.
      assert (val_ok e (V.shift 7 i)).
       red; intros.
       generalize (H3 (7+n) _ H6).
       destruct T as [(T,Tm)|]; simpl; auto.
      apply H0 in H6.
      simpl in H6.
      apply isOrd_inv with infty; trivial.
     revert H4; apply TI_incl; auto.

    eapply typ_var_impl.
     compute; reflexivity.
     simpl; reflexivity.
     discriminate.

     apply sub_refl.
     red; intros; simpl.
     reflexivity.

     eapply typ_var_impl.
      compute; reflexivity.
      simpl; reflexivity.
      discriminate.

      apply sub_refl.
      red; intros; simpl.
      reflexivity.
Qed.

End Example.

Print Assumptions minus_def.
*)