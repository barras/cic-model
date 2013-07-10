(** Strong normalization of the model of CC+W in the type-based
  termination presentation.
*)
Require Import basic Models.
Require SN_ECC_Real.
Import ZFgrothendieck.
Import ZF ZFsum ZFnats ZFrelations ZFord ZFfix.
Require Import ZFfunext ZFfixrec ZFcoc ZFecc ZFuniv_real ZFind_wbot SATtypes SATw.

Import SN_CC_Real.SN_CC_Model SN_CC_Real.SN SN_ECC_Real.
Opaque Real.
Import Sat Sat.SatSet.


(** Ordinals *)

Require Import SN_ord.

(** Judgments with variance *)

Require Import SN_variance.

(** W *)

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

Let Aw i := El (int A i).
Let Bw i x := El (int B (V.cons x i)).
Let RAw i a := Real (int A i) a.
Let RBw i a b := Real (int B (V.cons a i)) b.

Definition WF' i X := W_F (Aw i) (Bw i) (cc_bot X).
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

  apply cc_bot_morph; auto with *.
Qed.

  Lemma WF'mono i : Proper (incl_set==>incl_set) (WF' i).
do 2 red; intros.
unfold WF'.
apply W_F_mono.
 do 2 red; intros; apply Bw_morph; auto with *.
 apply cc_bot_mono; trivial.
Qed.
  Hint Resolve WF'mono.

Instance RW_morph : Proper (eq_val ==> eq_set ==> eq_set ==> eqSAT) RW.
do 4 red; intros.
unfold RW.
apply rWi_morph_gen; auto with *.
 apply Aw_morph; trivial.
 apply Bw_morph; trivial.
 apply RAw_morph; trivial.
 apply RBw_morph; trivial.
Qed.

Lemma TI_inv i x :
  isOrd o ->
  x ∈ TI (WF' i) o ->
  exists2 o', o' ∈ o & x ∈ TI (WF' i) (osucc o').
intros.
apply TI_elim in H0; auto.
destruct H0.
exists x0; trivial.
rewrite TI_mono_succ; trivial.
apply isOrd_inv with o; trivial.
Qed.

Definition WI (O:trm) : trm.
(*begin show*)
left; exists (fun i => mkTY (TI (WF' i) (int O i)) (RW i (int O i)))
             (fun j => Lc.App2 Lc.K (tm A j) (Lc.App2 Lc.K (Lc.Abs(tm B (Lc.ilift j))) (tm O j))).
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
  El (int (WI O) i) == cc_bot (TI (WF' i) (int O i)).
simpl.
rewrite El_def; reflexivity.
Qed.
Lemma Real_int_W O i x :
  x ∈ cc_bot (TI (WF' i) (int O i)) ->
  eqSAT (Real (int (WI O) i) x) (RW i (int O i) x).
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
left; exists (fun i => couple (int x i) (int f i))
             (fun j => WC (tm x j) (tm f j)).
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
assert (couple (int X0 i) (int F i) ∈ TI (WF' i) (osucc (int O i))).
 apply TI_intro with (int O i); auto.
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
 red; rewrite El_int_W; auto.

 rewrite Real_int_W; auto.
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
left; exists (fun i => W_CASE (int b i) (int n i))
             (fun j => WCASE (tm b j) (tm n j)).
(*end show*)
do 2 red; intros.
unfold W_CASE.
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

Lemma Wcase_iota : forall X F G,
  eq_typ e (Wcase G (Wc X F)) (App (App G X) F).
red; red; intros.
simpl.
unfold W_CASE.
rewrite sigma_case_couple with (a:=int X0 i) (b:=int F i).
 reflexivity.

 do 3 red; intros.
 rewrite H0; rewrite H1; reflexivity.

 reflexivity.
Qed.


Lemma typ_Wcase P O G n :
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
 rewrite cc_bot_ax in H1; destruct H1.
  unfold W_CASE, sigma_case.
  rewrite H1.
  rewrite cond_set_mt; auto.
  apply discr_mt_pair.   

  simpl in H1; rewrite TI_mono_succ in H1; auto with *.
  assert (fst (int n i) ∈ Aw i).
   apply fst_typ_sigma in H1; trivial.
  assert (snd (int n i) ∈ cc_arr (Bw i (fst (int n i))) (cc_bot (TI (WF' i) (int O i)))).
   apply snd_typ_sigma with (y:=fst(int n i)) in H1; auto with *.
   do 2 red; intros.
   rewrite H9; reflexivity.
  assert (int n i == couple (fst (int n i)) (snd (int n i))).
   apply (surj_pair _ _ _ (subset_elim1 _ _ _ H1)).
  unfold W_CASE, sigma_case.
  rewrite cond_set_ok; trivial.
  specialize cc_prod_elim with (1:=H0) (2:=H7); clear H0; intro H0.
  rewrite El_int_prod in H0.
  apply eq_elim with (El
     (app (int (lift 2 P) (V.cons (snd (int n i)) (V.cons (fst (int n i)) i)))
        (couple (fst (int n i)) (snd (int n i))))).
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
 rewrite cc_bot_ax in H1; destruct H1.
  (* neutral case *)
  rewrite H1 in H6.
  unfold WCASE.
  eapply prodSAT_elim;[|apply H5].
  revert H6; unfold RW; apply rWi_neutral; auto with *.
   apply Bw_morph; reflexivity.
   apply RAw_morph; reflexivity.

  (* regular case *)
  eapply Real_WCASE with (5:=H1) (6:=H6)
    (C:=fun x => Real (app (int P i) x) (sigma_case (fun x f => app (app (int G i) x) f) x));
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
Hint Resolve WF'mono.

Lemma typ_WI_type n eps e A B O :
  isOrd eps ->
  zero ∈ eps ->
  A <> kind ->
  typ e O (Ordt eps) ->
  typ e A (type n) ->
  typ (A::e) B (type n) ->
  typ e (WI A B O) (type n).
red; intros epso eps_nz Ank tyO tyA tyB i j is_val; simpl.
destruct tyord_inv with (3:=tyO)(4:=is_val) as (oo,(_,osn)); trivial.
clear tyO.
red in tyA; specialize tyA with (1:=is_val).
apply in_int_not_kind in tyA.
2:discriminate.
destruct tyA as (Aty,Asn).
red in Aty.
change (int (type n) i) with (sn_sort (ecc (S n))) in Aty.
apply El_in_grot in Aty; auto.
split;[discriminate|].
assert (G_B : forall a, a ∈ El (int A i) -> El (int B (V.cons a i)) ∈ ecc (S n)).
 intros.
 assert (val_ok (A::e) (V.cons a i) (I.cons daimon j)).
  apply vcons_add_var_daimon; trivial.
 apply tyB in H0.
 destruct H0; trivial.
 destruct H1; trivial.
 red in H1; change (int (type n) (V.cons a i)) with (sn_sort (ecc (S n))) in H1.
 apply El_in_grot in H1; trivial.
apply and_split; intros.
 red; change (int (type n) i) with (sn_sort (ecc (S n))).
 simpl int.
 apply sn_sort_intro.
  intros.
  apply RW_morph; auto with *.

  apply G_incl with (TI (WF' A B i) (W_ord' (El(int A i)) (fun x => El(int B (V.cons x i))))); trivial.
   apply G_TI; trivial.
    apply WF'_morph; auto with *.

    unfold W_ord'.
    apply Ffix_o_o; auto with *.
     apply Wf_mono'.
     do 2 red; intros.
     rewrite H; reflexivity.
     apply Wf_typ'.
     do 2 red; intros.
     rewrite H; reflexivity.

    apply G_W_ord'; auto.
    do 2 red; intros.
    rewrite H; reflexivity.

    intros.
    apply G_W_F'; auto.
    do 2 red; intros.
    rewrite H0; reflexivity.

   apply W_stages'; auto.
   do 2 red; intros.
   rewrite H; reflexivity.

 red in H.
 destruct (tyB _ _ (val_ok_cons_default _ _ _ _ is_val Ank)) as (Bnk,(_,snB)).
 change (int (type n) i) with (sn_sort (ecc (S n))).
 rewrite Real_sort_sn; trivial.
 apply sat_sn in Asn.
 apply sat_sn in snB.
 rewrite tm_subst_cons in snB.
 apply Lc.sn_subst in snB.
 simpl.
 apply snSAT_intro.
 apply Lc.sn_K2; trivial.
 apply Lc.sn_K2; trivial.
 apply Lc.sn_abs; trivial.
Qed.


(*****************************************************************************)
(** Recursor (without case analysis) *)

(* WFix O M is a fixpoint of domain WI O with body M *)
Definition WFix (O M:trm) : trm.
(*begin show*)
left.
exists (fun i =>
         WREC (fun o' f => squash (int M (V.cons f (V.cons o' i)))) (int O i))
       (fun j => WFIX (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j))))).
(*end show*)
 do 2 red; intros.
 unfold WREC.
 unfold REC.
 apply TR_morph.
 2:rewrite H; reflexivity.
 do 2 red; intros.
 apply sup_morph; trivial.
 red; intros.
 apply squash_morph.
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
     (WFIX (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j))))) k) with
   (WFIX (Lc.lift_rec 1 (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j)))) k)).
  simpl.
  f_equal.
  f_equal.
  rewrite <- tm_liftable.
  apply tm_morph; auto with *.
  rewrite <- Lc.ilift_binder_lift.
  apply Lc.ilift_morph.
  intros [|k']; simpl; trivial.
  apply tm_liftable.

  generalize  (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j)))); intro.
  unfold WFIX, FIXP; simpl.
  rewrite <- Lc.permute_lift.
  reflexivity.

 (* *)
 red; intros.
 replace (Lc.subst_rec u
     (WFIX (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j))))) k) with
   (WFIX (Lc.subst_rec u (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j)))) k)).
  simpl.
  f_equal.
  f_equal.
  rewrite <- tm_substitutive.
  apply tm_morph; auto with *.
  rewrite <- Lc.ilift_binder.
  apply Lc.ilift_morph.
  intros [|k']; simpl; trivial.
  apply tm_substitutive.

  generalize  (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j)))); intro.
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


  Let Wi i o := cc_bot (TI (WF' A B i) o).
  Let F i := fun o' f => squash (int M (V.cons f (V.cons o' i))).
  Let U' i := fun o' x => El (int U (V.cons x (V.cons o' i))).

  Local Instance U'morph : forall i, morph2 (U' i).
do 3 red; intros; unfold U'.
rewrite H; rewrite H0; reflexivity.
Qed.
  Instance morph_fix_body : forall i, morph2 (F i).
unfold F; do 3 red; intros.
apply squash_morph.
rewrite H; rewrite H0; reflexivity.
Qed.
  Lemma ext_fun_ty : forall o i,
    ext_fun (Wi i o) (U' i o).
do 2 red; intros.
rewrite H0;reflexivity.
Qed.
  Hint Resolve U'morph morph_fix_body ext_fun_ty.


  Hypothesis fx_sub_U :
    fx_sub (push_var (push_ord E (OSucct O)) (WIL 1 (OSucc (Ref 0)))) U.


Lemma El_int_W_lift O' n i :
  El (int (WIL n O') i) == cc_bot (TI (WF' A B (V.shift n i)) (int O' i)).
unfold WIL; rewrite El_int_W.
apply cc_bot_morph.
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
  x ∈ cc_bot (TI (WF' A B (V.shift n i)) (int O' i)) ->
  eqSAT (Real (int (WIL n O') i) x) (RW A B (V.shift n i) (int O' i) x).
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
 apply cc_bot_morph.
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

  apply cc_bot_morph; trivial.
Qed.

Lemma Elt_int_W_lift O' n i :
  Elt (int (WIL n O') i) == TI (WF' A B (V.shift n i)) (int O' i).
simpl; rewrite Elt_def.
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

Lemma wnot_mt o i :
  isOrd o ->
  ~ empty ∈ TI (WF' A B i) o.
intros oo h; apply mt_not_in_W_F' in h; auto with *.
apply Bw_morph; reflexivity.
Qed.

Lemma wprod_ext_mt o i f :
  isOrd o ->
  f ∈ cc_prod (TI (WF' A B i) o) (U' i o) ->
  f ∈ cc_prod (Wi i o) (U' i o).
intros oo fty.
apply cc_prod_ext_mt in fty; trivial.
 apply ext_fun_ty.

 apply cc_bot_bot.

 apply wnot_mt; trivial.
Qed.

  Lemma val_mono_1 i i' j j' y y' f g:
    val_mono E i j i' j' ->
    isOrd (int O i) ->
    isOrd (int O i') ->
    int O i ⊆ int O i' ->
    isOrd y ->
    isOrd y' ->
    y ⊆ int O i ->
    y' ⊆ int O i' ->
    y ⊆ y' ->
    f ∈ cc_prod (Wi i y) (U' i y) ->
    g ∈ cc_prod (Wi i' y') (U' i' y') ->
    fcompat (Wi i y) f g ->
    val_mono (push_fun (push_ord E (OSucct O)) (WIL 1 (Ref 0)) U)
      (V.cons f (V.cons y i)) (I.cons daimon (I.cons daimon j))
      (V.cons g (V.cons y' i')) (I.cons daimon (I.cons daimon j')).
intros is_val Oo Oo' oo' yo y'o yO y'O yy' fty gty eqfg.
apply val_push_fun.
 apply val_push_ord; auto.
 3:discriminate.
  split;[|apply varSAT].
  red; rewrite El_int_osucc.
  apply ole_lts; trivial.

  split;[|apply varSAT].
  red; rewrite El_int_osucc.
  apply ole_lts; trivial.

 split;[|apply varSAT].
 red; rewrite El_int_prod.
 revert fty; apply eq_elim; apply cc_prod_ext; intros.
  rewrite El_int_W_lift; reflexivity.

  apply ext_fun_ty.

 split;[|apply varSAT].
 red; rewrite El_int_prod.
 revert gty; apply eq_elim; apply cc_prod_ext; intros.
  rewrite El_int_W_lift; reflexivity.

  apply ext_fun_ty.

 rewrite El_int_W_lift.
 trivial.
Qed.

  Lemma val_mono_2 i j y y' n n':
    val_ok e i j ->
    isOrd (int O i) ->
    isOrd y ->
    isOrd y' ->
    y ⊆ y' ->
    y' ⊆ int O i ->
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
 revert H5; apply cc_bot_mono.
 apply TI_incl; simpl; auto.

 split;[|apply varSAT].
 red; rewrite El_int_W_lift.
 rewrite <- H6.
 revert H5; apply cc_bot_mono.
 apply TI_incl; simpl; auto.
 apply ole_lts; trivial.
Qed.


  Lemma fix_codom_mono : forall o o' x x' i j,
   val_ok e i j ->
   isOrd o' ->
   o' ⊆ int O i ->
   isOrd o ->
   o ⊆ o' ->
   x ∈ Wi i o ->
   x == x' ->
   U' i o x ⊆ U' i o' x'.
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

  Lemma ty_fix_body0 : forall i j o f,
   val_ok e i j ->
   o < osucc (int O i) ->
   f ∈ cc_prod (Wi i o) (U' i o) ->
   int M (V.cons f (V.cons o i)) ∈
   cc_prod (Wi i (osucc o)) (U' i (osucc o)).
unfold F; intros.
destruct tyord_inv with (3:=ty_O) (4:=H); trivial.
assert (val_ok (Prod (WIL 1 (Ref 0)) U::OSucct O::e)
  (V.cons f (V.cons o i)) (I.cons daimon (I.cons daimon j))).
 apply vcons_add_var; auto.
 3:discriminate.
  apply vcons_add_var; auto.
  2:discriminate.
  split;[|apply varSAT].
  red; simpl; rewrite El_def; auto.

  split;[|apply varSAT].
  red; rewrite El_int_prod.
  revert H1; apply eq_elim.
  apply cc_prod_ext.
   rewrite El_int_W_lift.
   reflexivity.

   apply ext_fun_ty.
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

  Lemma ty_fix_body : forall i j o f,
   val_ok e i j ->
   o < osucc (int O i) ->
   f ∈ cc_prod (TI (WF' A B i) o) (U' i o) ->
   F i o f ∈
   cc_prod (TI (WF' A B i) (osucc o)) (U' i (osucc o)).
unfold F; intros.
destruct tyord_inv with (3:=ty_O) (4:=H); trivial.
apply squash_typ.
 apply ext_fun_ty.

 apply wnot_mt.
 eauto using isOrd_inv.

 apply ty_fix_body0 with (1:=H); trivial.
 apply wprod_ext_mt in H1; trivial.
 simpl; eauto using isOrd_inv. 
Qed.


  Lemma fix_body_irrel0 : forall i j,
    val_ok e i j ->
    Wi_ord_irrel' (El (int A i))
      (fun x => El (int B (V.cons x i))) (int O i)
      (fun o' f => int M (V.cons f (V.cons o' i))) (U' i).
red; intros.
assert (isOrd (int O i)).
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
 apply val_mono_1; auto with *.
  apply val_mono_refl; exact H.

  transitivity o'; trivial.

  apply wprod_ext_mt; trivial.

  apply wprod_ext_mt; trivial.

  red; intros.
  apply cc_bot_ax in H9; destruct H9.
   rewrite cc_app_outside_domain with (1:=cc_prod_is_cc_fun _ _ _ H4).
    rewrite cc_app_outside_domain with (1:=cc_prod_is_cc_fun _ _ _ H5);[reflexivity|].
    rewrite H9; apply wnot_mt; trivial.
   rewrite H9; apply wnot_mt; trivial.

   apply H6; trivial.

 rewrite El_int_W_lift; auto.
Qed.


  Lemma fix_body_irrel : forall i j,
    val_ok e i j ->
    Wi_ord_irrel' (El (int A i))
      (fun x => El (int B (V.cons x i))) (int O i) (F i) (U' i).
red; intros.
assert (isOrd (int O i)).
 apply ty_O in H.
 apply isOrd_inv with infty; auto.
 apply in_int_not_kind in H;[|discriminate].
 destruct H.
 red in H; rewrite El_int_ord in H; trivial.
red; intros.
unfold F.
rewrite squash_eq.
3:apply ty_fix_body0 with (1:=H).
 rewrite squash_eq.
 3:apply ty_fix_body0 with (1:=H).
  rewrite cc_beta_eq; trivial.
   rewrite cc_beta_eq; trivial.
    assert (Wirr := fix_body_irrel0).
    do 2 red in Wirr.
    apply Wirr with (1:=H); trivial.

    do 2 red; intros.
    rewrite H10; reflexivity.

    revert H8; apply TI_mono; auto with *.
    apply osucc_mono; trivial.

   do 2 red; intros.
   rewrite H10; reflexivity.

  apply wnot_mt; auto.

  apply ole_lts; trivial.

  apply wprod_ext_mt; trivial.

 apply wnot_mt; auto.

 apply ole_lts; trivial.
 transitivity o'; trivial.

 apply wprod_ext_mt; trivial.
Qed.

  Hint Resolve morph_fix_body ext_fun_ty ty_fix_body fix_codom_mono fix_body_irrel.


Let fix_typ0 o i j:
  val_ok e i j ->
  isOrd o ->
  isOrd (int O i) ->
  o ⊆ int O i ->
  WREC (F i) o ∈ cc_prod (TI (WF' A B i) o) (U' i o).
intros.
eapply WREC_wt' with (U':=U' i); trivial.
 do 2 red; intros.
 apply Bw_morph; auto with *.

 intros.
 apply fix_codom_mono with (1:=H); trivial.
  transitivity o; auto.
  unfold Wi; auto.

 intros.
 apply ty_fix_body with (1:=H); trivial.
 apply ole_lts; trivial.
 transitivity o; trivial.

 red; intros; apply fix_body_irrel with (1:=H); trivial.
 transitivity o; trivial.
Qed.

Let fix_typ o i j:
  val_ok e i j ->
  isOrd o ->
  isOrd (int O i) ->
  o ⊆ int O i ->
  WREC (F i) o ∈ cc_prod (Wi i o) (U' i o).
intros.
apply wprod_ext_mt; trivial.
apply fix_typ0 with (1:=H); trivial.
Qed.


  Lemma fix_irr i j o o' x :
    val_ok e i j ->
    isOrd o ->
    isOrd o' ->
    isOrd (int O i) ->
    o ⊆ o' ->
    o' ⊆ int O i ->
    x ∈ Wi i o ->
    cc_app (WREC (F i) o) x == cc_app (WREC (F i) o') x.
intros.
assert (WRECi := WREC_irrel').
red in WRECi.
apply cc_bot_ax in H5; destruct H5.
 rewrite cc_app_outside_domain with (dom:=TI (WF' A B i) o).
  symmetry; eapply cc_app_outside_domain with (TI (WF' A B i) o').
   eapply cc_prod_is_cc_fun.
   apply fix_typ0 with (1:=H); trivial.

   rewrite H5; apply wnot_mt; trivial.

  eapply cc_prod_is_cc_fun.
  apply fix_typ0 with (1:=H); trivial.
  transitivity o'; trivial.

  rewrite H5; apply wnot_mt; trivial.
  
apply WRECi with 
  (A:=El (int A i)) (B:=fun x=>El(int B (V.cons x i)))
  (ord:=int O i) (U':=U' i); auto with *.
 do 2 red; intros; apply Bw_morph; auto with *.

 intros.
 apply fix_codom_mono with (1:=H); trivial.
 apply cc_bot_intro; trivial.

 intros.
 apply ty_fix_body with (1:=H); trivial.
 apply ole_lts; trivial.

 apply fix_body_irrel with (1:=H).
Qed.

Lemma fix_eqn0 : forall i j o,
  val_ok e i j ->
  isOrd o ->
  isOrd (int O i) ->
  o ⊆ int O i ->
  WREC (F i) (osucc o) == F i o (WREC (F i) o).
intros.
unfold WREC at 1.
rewrite REC_eq; auto with *.
rewrite eq_set_ax; intros z.
rewrite sup_ax; auto with *.
split; intros.
 destruct H3 as (o',o'lt,zty).
 assert (o'o : isOrd o') by eauto using isOrd_inv.
 assert (o'le : o' ⊆ o) by (apply olts_le; auto).
 assert (o'le' : o' ⊆ int O i) by (transitivity o; trivial).
 assert (F i o' (WREC (F i) o') ∈ cc_prod (TI (WF' A B i) (osucc o')) (U' i (osucc o'))).
  apply ty_fix_body with (1:=H); trivial.
   apply ole_lts; auto.

   apply fix_typ0 with (1:=H); trivial.
 assert (F i o (WREC (F i) o) ∈ cc_prod (TI (WF' A B i) (osucc o)) (U' i (osucc o))).
  apply ty_fix_body with (1:=H); trivial.
   apply ole_lts; auto.

   apply fix_typ0 with (1:=H); trivial.
 rewrite cc_eta_eq with (1:=H3) in zty.
 rewrite cc_eta_eq with (1:=H4).
 rewrite cc_lam_def in zty|-*.
 2:intros ? ? _ eqn; rewrite eqn; reflexivity.
 2:intros ? ? _ eqn; rewrite eqn; reflexivity.
 destruct zty as (n', n'ty, (y, yty, eqz)).
 exists n'.
  revert n'ty; apply TI_mono; auto with *.
  apply osucc_mono; auto.
 exists y; trivial.
 revert yty; apply eq_elim.
 assert (firrel := fix_body_irrel).
 do 2 red in firrel.
 apply firrel with (1:=H); auto.
  apply fix_typ0 with (1:=H); auto.
  apply fix_typ0 with (1:=H); auto.

  clear firrel.
  red; intros.
  apply fix_irr with (1:=H); trivial.
  apply cc_bot_intro; trivial.

 exists o;[apply lt_osucc;trivial|trivial].
Qed.

Lemma fix_eqn : forall i j o n,
  val_ok e i j ->
  isOrd o ->
  isOrd (int O i) ->
  o ⊆ int O i ->
  n ∈ TI (WF' A B i) (osucc o) ->
  cc_app (WREC (F i) (osucc o)) n ==
  cc_app (int M (V.cons (WREC (F i) o) (V.cons o i))) n.
intros.
rewrite fix_eqn0 with (1:=H); trivial.
unfold F.
rewrite squash_beta with (3:=H3).
 reflexivity.

 apply wnot_mt; auto.

 apply ty_fix_body0 with (1:=H).
  apply ole_lts; trivial.

  apply fix_typ with (1:=H); trivial.
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
(**)
 set (m:=Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j)))).
 cut (inSAT (WFIX m)
       (piSAT0 (fun x => x ∈ Wi i (int O i))
         (RW A B i (int O i))
         (fun x =>
            Real (int U (V.cons x (V.cons (int O i) i))) 
              (cc_app (WREC (F i) (int O i)) x)))).
  apply interSAT_morph_subset; simpl proj1_sig; intros.
   rewrite El_int_W; reflexivity.

   apply prodSAT_morph.
    rewrite Real_int_W; auto with *.

    apply Real_morph; simpl;[|reflexivity].
    rewrite int_subst_rec_eq.
    apply int_morph; auto with *.
    intros [|[|k]]; reflexivity.

 unfold RW.
 apply WFIX_sat with
   (X:=fun o n => Real (int U (V.cons n (V.cons o i)))
     (cc_app (WREC (F i) o) n)); trivial.
  apply Bw_morph; reflexivity.
  apply RAw_morph; reflexivity.

  red; intros.
  apply cc_bot_intro in H7.
  apply fx_sub_U with (V.cons n (V.cons y i))
     (I.cons daimon (I.cons daimon j)) (I.cons daimon (I.cons daimon j)).
   apply val_mono_2; auto with *.

   apply and_split; intros.
    red; rewrite <- fix_irr with (1:=H) (o:=y); auto.
    apply cc_prod_elim with (dom:=Wi i y) (F:=U' i y); trivial.
    apply fix_typ with (1:=H); trivial.
    transitivity y'; trivial.

    rewrite <- fix_irr with (1:=H) (o:=y); auto.

  (* sat body *)
  apply piSAT0_intro'.
  2:exists (int O i).
  2:apply lt_osucc; auto.
  intros o' u ? ?.
  apply inSAT_exp.
   right; apply sat_sn in H4; trivial.
  replace (Lc.subst u (tm M (Lc.ilift (I.cons (tm O j) j)))) with
     (tm M (I.cons u (I.cons (tm O j) j))).
  2:unfold Lc.subst; rewrite <- tm_substitutive.
  2:apply tm_morph; auto with *.
  2:intros [|[|k]]; unfold Lc.ilift,I.cons; simpl.
  2:rewrite Lc.lift0; reflexivity.
  2:rewrite Lc.simpl_subst; trivial.
  2:rewrite Lc.lift0; trivial.
  2:rewrite Lc.simpl_subst; trivial.
  2:rewrite Lc.lift0; trivial.
  assert (val_ok (Prod (WIL 1 (Ref 0)) U::OSucct O::e)
            (V.cons (WREC (F i) o') (V.cons o' i)) (I.cons u (I.cons (tm O j) j))).
   apply vcons_add_var.
   3:discriminate.
    apply vcons_add_var; trivial.
    2:discriminate.
    split.
     red; rewrite El_int_osucc; trivial.

     simpl; rewrite Real_def; auto with *.
      apply ty_O in H.
      apply in_int_sn in H; trivial.

     assert (WREC (F i) o' ∈ cc_prod (Wi i o') (U' i o')).
      apply fix_typ with (1:=H); trivial.
      eauto using isOrd_inv.
      apply olts_le in H3; trivial.
     apply and_split; intros.
      red; rewrite El_int_prod.
      revert H5; apply eq_elim; apply cc_prod_ext.
       rewrite El_int_W_lift; reflexivity.

       apply ext_fun_ty.

      rewrite Real_int_prod.
       revert H4; apply interSAT_morph_subset; simpl proj1_sig; intros.
        rewrite El_int_W_lift; reflexivity.

        apply prodSAT_morph; auto with *.
        rewrite Real_int_W_lift; trivial.
        reflexivity.

       revert H5; apply eq_elim; apply cc_prod_ext.
        rewrite El_int_W_lift; reflexivity.

        apply ext_fun_ty.
 assert (ty_M' := ty_M _ _ H5).
 apply in_int_not_kind in ty_M'.
 2:discriminate.
 destruct ty_M'.
 red in H6; rewrite El_int_prod in H6.
 rewrite Real_int_prod in H7; trivial.
 apply piSAT0_intro.
  apply sat_sn in H7; trivial.
 intros x v ? ?.
 rewrite fix_eqn with (1:=H); trivial.
 2:eauto using isOrd_inv.
 2:apply olts_le; trivial.
 apply piSAT0_elim' in H7; red in H7.
 specialize H7 with (x:=x) (u0:=v).
 eapply Real_morph.
 3:apply H7.
  rewrite int_lift_rec_eq.
  rewrite int_subst_rec_eq.
  rewrite int_lift_rec_eq.
  apply int_morph; auto with *.
  intros [|[|k]]; unfold V.lams,V.shift; simpl; try reflexivity.
   replace (k-0) with k; auto with *.

  reflexivity.

  rewrite El_int_W_lift; auto.

  rewrite Real_int_W_lift; auto.
Qed.


(** Fixpoint equation holds only when applied to a constructor,
    because of the realizability part of the interpretation.
 *)
Lemma wfix_eq : forall X G,
  let N := Wc X G in
  typ e N (WI A B O) ->
  eq_typ e (App (WFix O M) N)
           (App (subst O (subst (lift 1 (WFix O M)) M)) N).
intros X G N tyN.
red; intros.
unfold eqX.
change
 (app (WREC (F i) (int O i)) (int N i) ==
  app (int (subst O (subst (lift 1 (WFix O M)) M)) i) (int N i)).
do 2 rewrite <- int_subst_eq.
rewrite int_cons_lift_eq.
red in tyN; specialize tyN with (1:=H).
apply in_int_not_kind in tyN.
2:discriminate.
destruct tyN.
red in H0; rewrite El_int_W in H0.
rewrite cc_bot_ax in H0; destruct H0.
 simpl in H0.
 symmetry in H0; apply discr_mt_pair in H0; contradiction.
destruct tyord_inv with (3:=ty_O)(4:=H); trivial.
apply TI_inv in H0; trivial.
destruct H0 as (o,oly,nty).
assert (oo: isOrd o) by eauto using isOrd_inv.
rewrite <- fix_irr with (1:=H)(o:=osucc o); auto with *.
2:apply olts_le.
2:apply lt_osucc_compat; auto.
2:apply cc_bot_intro; trivial.
rewrite fix_eqn with (1:=H); auto with *.
eapply fix_body_irrel0 with (1:=H); auto with *.
 apply fix_typ0 with (1:=H); trivial.
 red; intros; apply isOrd_trans with o; trivial.

 simpl.
 apply fix_typ0 with (1:=H); auto with *.

 red; simpl; intros.
 apply fix_irr with (1:=H); auto with *.
 apply cc_bot_intro; trivial.
Qed.

Lemma wfix_extend :
  fx_subval E O ->
  fx_extends E (WI A B O) (WFix O M).
intro subO.
do 2 red; intros.
rewrite El_int_W in H0.
assert (isval := proj1 H).
assert (isval' := proj1 (proj2 H)).
assert (oo: isOrd (int O i)).
 destruct tyord_inv with (3:=ty_O) (4:=isval); trivial.
assert (oo': isOrd (int O i')).
 destruct tyord_inv with (3:=ty_O) (4:=isval'); trivial.
assert (inclo: int O i ⊆ int O i').
 apply subO in H; trivial.
clear subO.
change (cc_app (WREC (F i) (int O i)) x == cc_app (WREC (F i') (int O i')) x).
revert x H0.
elim oo using isOrd_ind; intros.
rewrite cc_bot_ax in H3; destruct H3.
 rewrite cc_app_outside_domain with (dom:=TI (WF' A B i) y).
  symmetry; apply cc_app_outside_domain with (dom:=TI (WF' A B i') (int O i')).
   eapply cc_prod_is_cc_fun.
   apply fix_typ0 with (1:=proj1(proj2 H)); auto with *.

   rewrite H3; apply wnot_mt; trivial.

  eapply cc_prod_is_cc_fun.
  apply fix_typ0 with (1:=proj1 H); auto with *.

  rewrite H3; apply wnot_mt; trivial.

 apply TI_inv in H3; trivial.
 destruct H3 as (o',?,?).
 assert (o_o' : isOrd o') by eauto using isOrd_inv.
 assert (o'_y : osucc o' ⊆ y).
  red; intros; apply le_lt_trans with o'; auto.
 rewrite <- fix_irr with (1:=isval) (o:=osucc o'); auto.
 2:apply cc_bot_intro; trivial.
 rewrite fix_eqn with (1:=isval); auto.
 assert (TIeq: forall o', isOrd o' -> TI (WF' A B i) o' == TI (WF' A B i') o').
  intros; apply TI_morph_gen; auto with *.
  red; intros.
  apply W_F_ext.
   apply El_morph.
   apply (Aeq _ _ _ _ H).

   red; intros.
   apply El_morph.
   eapply Beq.
   apply val_push_var with (1:=H); trivial.
    split;[trivial|apply varSAT].
    rewrite (Aeq _ _ _ _ H) in H7.
    rewrite H8 in H7.
    split;[trivial|apply varSAT].

   apply cc_bot_morph; trivial.
 assert (x ∈ TI (WF' A B i') (osucc o')).
  rewrite <- TIeq; auto.
 rewrite <- fix_irr with (1:=isval') (o:=osucc o'); auto with *.
 2:red; intros; apply le_lt_trans with o' ;auto.
 2:apply inclo; apply H1; trivial.
 2:apply cc_bot_intro; trivial.
 rewrite fix_eqn with (1:=isval'); auto.
 assert (irr := stab).
 do 2 red in irr.
 eapply irr.
 2:rewrite El_int_W_lift.
 2:apply cc_bot_intro; exact H4.
 apply val_mono_1 with (1:=H); auto with *.
  apply fix_typ with (1:=proj1 H); trivial.
  red; intros; apply isOrd_trans with o'; auto.
  apply H1; trivial.

  apply fix_typ with (1:=proj1 (proj2 H)); trivial.
  red; intros; apply isOrd_trans with o'; auto.
  apply inclo; apply H1; trivial.

 do 2 red; intros.
 rewrite H2; trivial.
 symmetry; apply fix_irr with (1:=proj1(proj2 H)); auto with *.
 revert H6; apply eq_elim; apply cc_bot_morph.
 apply TIeq; trivial.
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

 setoid_replace (int (WI A B O) i) with (int (WI A B O) i').
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

   apply cc_bot_morph; trivial.

  intros.
  unfold RW; apply rWi_ext; trivial.
   do 2 red; intros.
   rewrite H3; reflexivity.

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


(** Variance results *)

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
assert (cc_bot (TI (WF' A B i) (int O i)) ⊆ cc_bot (TI (WF' A B i') (int O i'))).
 apply cc_bot_mono.
 transitivity (TI (WF' A B i') (int O i)).
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

   apply cc_bot_morph; trivial.

  destruct H0; destruct H2.
  apply TI_mono; trivial.
split.
 red; rewrite El_int_W; auto.

 rewrite Real_int_W; auto.
 rewrite cc_bot_ax in xreal; destruct xreal as [H4|xreal].
  assert (eqSAT (RW A B i (int O i) x) (RW A B i (int O i) empty)).
   unfold RW; apply rWi_morph; auto with *.
   do 2 red; intros.
   rewrite H5; reflexivity.
 rewrite H5 in xsat.
 revert xsat; unfold RW; apply rWi_neutral; trivial.
  apply Bw_morph; reflexivity.
  apply RAw_morph; reflexivity.

 setoid_replace (RW A B i' (int O i') x) with (RW A B i (int O i) x); trivial.
 symmetry; transitivity (RW A B i (int O i') x).
  unfold RW; apply rWi_mono; trivial.
   apply Bw_morph; reflexivity.
   apply RAw_morph; reflexivity.

  unfold RW; apply rWi_ext; trivial; intros.
   do 2 red; intros.
   rewrite H4; reflexivity.

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
*)