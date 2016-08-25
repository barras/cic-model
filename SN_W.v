(** Strong normalization of the model of CC+W in the type-based
  termination presentation.
*)
Require Import basic Models.
Require SN_ECC_Real.
Import ZFgrothendieck.
Import ZF ZFsum ZFnats ZFrelations ZFord ZFfix.
Require Import ZFfunext ZFfixrec ZFcoc ZFecc ZFuniv_real SATtypes SATw.

Import SN_CC_Real.SN_CC_Model SN_CC_Real.SN SN_ECC_Real.
Opaque Real.
Import Sat Sat.SatSet.

(** Typing rules related to ordinals *)

Require Import SN_ord.

(** Judgments with variance *)

Require Import SN_variance.

(** W *)

(** The abstract model construction is a functor based on any
    abstract set-theoretical model of W-types. *)
Module Make(W:W_PartialModel).

Module Wsat := SATw.Make(W).
Import W Wsat.

Section Wtypes_typing.

Variable o : set.
Hypothesis oo : isOrd o.
Hypothesis oz : zero ∈ o.

Variable e:env.

Variable A B:term.
Hypothesis Atyp : typ e A kind.
Hypothesis Btyp : typ (A::e) B kind.

Let Aw i := El (int A i).
Let Bw i x := El (int B (V.cons x i)).
Let RAw i a := Real (int A i) a.
Let RBw i a b := Real (int B (V.cons a i)) b.

Definition WF i X := W_F (Aw i) (Bw i) X.
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
Instance Bwi_morph i : morph1 (Bw i).
apply Bw_morph; reflexivity.
Qed.

Instance RAw_morph : Proper (eq_val ==> eq_set ==> eqSAT) RAw.
do 3 red; intros.
unfold RAw.
rewrite H; rewrite H0; reflexivity.
Qed.
Instance RAwi_morph i : Proper (eq_set ==> eqSAT) (RAw i).
apply RAw_morph; reflexivity.
Qed.

Instance RBw_morph : Proper (eq_val ==> eq_set ==> eq_set ==> eqSAT) RBw.
do 4 red; intros.
unfold RBw.
rewrite H; rewrite H0; rewrite H1; reflexivity.
Qed.
Instance RBwi_morph i : Proper (eq_set ==> eq_set ==> eqSAT) (RBw i).
apply RBw_morph; reflexivity.
Qed.

Instance WF_morph : Proper (eq_val ==> eq_set ==> eq_set) WF.
do 3 red; intros.
apply W_F_ext; trivial.
 apply Aw_morph; trivial.

 red; intros.
 apply Bw_morph; trivial.
Qed.

  Lemma WF_mono i : Proper (incl_set==>incl_set) (WF i).
do 2 red; intros.
unfold WF.
apply W_F_mono; auto with *.
Qed.
  Hint Resolve WF_mono.

Instance RW_morph : Proper (eq_val ==> eq_set ==> eq_set ==> eqSAT) RW.
do 4 red; intros.
unfold RW.
apply rWi_morph_gen; auto with *.
 apply Aw_morph; trivial.
 apply Bw_morph; trivial.
 apply RAw_morph; trivial.
 apply RBw_morph; trivial.
Qed.

Definition WI (O:term) : term.
(*begin show*)
left; exists (fun i => mkTY (TI (WF i) (int O i)) (RW i (int O i)))
             (fun j => Lc.App2 Lc.K (tm A j) (Lc.App2 Lc.K (Lc.Abs(tm B (Lc.ilift j))) (tm O j))).
(*end show*)
 do 2 red; intros.
 apply mkTY_ext; intros.
  apply TI_morph_gen.
   apply WF_morph; trivial.
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
  El (int (WI O) i) == cc_bot (TI (WF i) (int O i)).
simpl.
rewrite El_def; reflexivity.
Qed.
Lemma Real_int_W O i x :
  x ∈ cc_bot (TI (WF i) (int O i)) ->
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
destruct (Btyp _ _ (val_ok_cons_default H1 Ank)) as (Bnk,(_,snB)).
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

Definition Wc (x:term) (f:term) : term.
(* begin show *)
left; exists (fun i => mkw (int x i) (int f i))
             (fun j => WC (tm x j) (tm f j)).
(* end show *)
 do 2 red; intros; apply mkw_morph; apply int_morph; auto with *.
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
assert (mkw (int X0 i) (int F i) ∈ TI (WF i) (osucc (int O i))).
 apply TI_intro with (int O i); auto.
 apply W_F_intro.
  apply Bw_morph; auto with *.

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
  rewrite w1_eq.
  apply H0.

  destruct H1.
  red in H1; rewrite El_int_prod in H1.
  rewrite Real_int_prod in H6; trivial.
  revert H6; apply piSAT0_morph; intros.
   red; intros.
   rewrite w1_eq.
   rewrite <- int_subst_eq; reflexivity.

   rewrite w1_eq.
   rewrite <- int_subst_eq; reflexivity.

   rewrite int_cons_lift_eq.
   rewrite Real_int_W.
    unfold RW; apply rWi_morph; auto with *.
     rewrite w2_eq; reflexivity.

     apply cc_prod_elim with (2:=H7) in H1.
     rewrite int_cons_lift_eq in H1.
     rewrite El_int_W in H1; trivial.
Qed.

(* Case analysis *)

Definition mkw_case (b : set -> set -> set) c :=
  cond_set (c == mkw (w1 c) (w2 c)) (b (w1 c) (w2 c)).

Definition W_CASE b w :=
  mkw_case (fun x f => app (app b x) f) w.

Definition Wcase (b n : term) : term.
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
  Proper (eq_term ==> eq_term ==> eq_term) Wcase.
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
unfold mkw_case; rewrite cond_set_ok.
 rewrite w1_eq, w2_eq; reflexivity.
 rewrite w1_eq, w2_eq; reflexivity.
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
  unfold W_CASE, mkw_case.
  rewrite H1.
  rewrite cond_set_mt; auto.
  apply discr_mt_mkw.

  simpl in H1; rewrite TI_mono_succ in H1; auto with *.
  apply W_F_elim in H1.
  2:apply Bw_morph; auto with *.
  destruct H1 as (ty1,(ty2,eqn)).
  unfold W_CASE, mkw_case.
  rewrite cond_set_ok; trivial.
  specialize cc_prod_elim with (1:=H0) (2:=ty1); clear H0; intro H0.
  rewrite El_int_prod in H0.
  apply eq_elim with (El
     (app (int (lift 2 P) (V.cons (w2 (int n i)) (V.cons (w1 (int n i)) i)))
        (mkw (w1 (int n i)) (w2 (int n i))))).
   apply El_morph.
   apply app_ext; auto with *.
   rewrite split_lift; do 2 rewrite int_cons_lift_eq; reflexivity.

   apply cc_prod_elim with (1:=H0).
   rewrite split_lift.
   rewrite El_int_arr.
   revert ty2; apply eq_elim.
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
  unfold RW in H6; rewrite rWi_neutral in H6; auto with *.
  apply neuSAT_def; trivial.

  (* regular case *)
  eapply Real_WCASE with (6:=H1) (7:=H6)
    (C:=fun x => Real (app (int P i) x) (mkw_case (fun x f => app (app (int G i) x) f) x));
     auto with *.
  do 2 red; intros.
   unfold mkw_case.
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

      unfold mkw_case; rewrite cond_set_ok.
       rewrite w1_eq, w2_eq; reflexivity.
       rewrite w1_eq, w2_eq; reflexivity.
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
Hint Resolve WF_mono.

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

  apply G_incl with (TI (WF A B i) (W_ord (El(int A i)) (fun x => El(int B (V.cons x i))))); trivial.
   apply G_TI; trivial.
    apply WF_morph; auto with *.

    apply W_ord_ord.
    do 2 red; intros.
    rewrite H; reflexivity.

    apply G_W_ord; auto.
    do 2 red; intros.
    rewrite H; reflexivity.

    intros.
    apply G_W_F; auto.
    do 2 red; intros.
    rewrite H0; reflexivity.

   apply W_stages; auto.
   do 2 red; intros.
   rewrite H; reflexivity.

 red in H.
 destruct (tyB _ _ (val_ok_cons_default is_val Ank)) as (Bnk,(_,snB)).
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
Definition WFix (O M:term) : term.
(*begin show*)
left.
exists (fun i => WREC (fun o' f => int M (V.cons f (V.cons o' i))) (int O i))
       (fun j => WFIX (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j))))).
(*end show*)
 do 2 red; intros.
 apply WREC_morph.
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
  Variable A B O U M : term.
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


  Let Wi i o := cc_bot (TI (WF A B i) o).
  Let F i := fun o' f => squash (int M (V.cons f (V.cons o' i))).
  Let U' i := fun o' x => El (int U (V.cons x (V.cons o' i))).
  Notation F' i := (fun o' f => int M (V.cons f (V.cons o' i))).

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
  El (int (WIL n O') i) == cc_bot (TI (WF A B (V.shift n i)) (int O' i)).
unfold WIL; rewrite El_int_W.
apply cc_bot_morph.
apply TI_morph_gen; auto with *.
red; intros.
unfold WF; apply W_F_ext; auto with *.
 rewrite int_lift_eq; reflexivity.

 red; intros.
 rewrite int_lift_rec_eq.
 rewrite <- V.cons_lams.
 2:apply V.shift_morph; trivial.
 rewrite V.lams0.
 rewrite H1; reflexivity.
(*
 rewrite H; reflexivity.*)
Qed.

Lemma Real_int_W_lift O' n i x :
  x ∈ cc_bot (TI (WF A B (V.shift n i)) (int O' i)) ->
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
 unfold WF; apply W_F_ext.
  rewrite int_lift_eq; reflexivity.

  red; intros.
  rewrite H1; rewrite int_lift_rec_eq.
  rewrite <- V.cons_lams.
  2:apply V.shift_morph; trivial.
  rewrite V.lams0.
  reflexivity.

  (*apply cc_bot_morph;*) trivial.
Qed.

Lemma Elt_int_W_lift O' n i :
  Elt (int (WIL n O') i) == TI (WF A B (V.shift n i)) (int O' i).
simpl; rewrite Elt_def.
apply TI_morph_gen; auto with *.
red; intros.
unfold WF; apply W_F_ext; auto with *.
 rewrite int_lift_eq; reflexivity.

 red; intros.
 rewrite int_lift_rec_eq.
 rewrite <- V.cons_lams.
 2:apply V.shift_morph; trivial.
 rewrite V.lams0.
 rewrite H1; reflexivity.

(* rewrite H; reflexivity.*)
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


Let F2m : forall i T, morph2 (fun o' f => int T (V.cons f (V.cons o' i))).
do 3 red; intros.
apply int_morph; [reflexivity|].
repeat apply V.cons_morph; trivial.
reflexivity.
Qed.
Let U2m : forall i T, morph2 (fun o' f => El (int T (V.cons f (V.cons o' i)))).
do 3 red; intros.
apply El_morph; apply F2m; trivial.
Qed.
Set Implicit Arguments.

Let Mty : forall i j,
 val_ok e i j ->
 forall o',
 o' ∈ osucc (int O i) ->
 forall f,
 f ∈ cc_prod (Wi i o') (U' i o') ->
 int M (V.cons f (V.cons o' i)) ∈ cc_prod (Wi i (osucc o')) (U' i (osucc o')).
intros.
assert (val_ok (Prod (WIL 1 (Ref 0)) U :: OSucct O :: e)
          (V.cons f (V.cons o' i)) (I.cons daimon (I.cons daimon j))).
 apply vcons_add_var_daimon; [| |discriminate].
  apply vcons_add_var_daimon; [trivial| |discriminate].
  red; simpl; rewrite El_def; auto.

  red; rewrite El_int_prod.
  revert H1; apply eq_elim; apply cc_prod_ext.
   rewrite El_int_W_lift; reflexivity.

   apply ext_fun_ty.
apply ty_M in H2.
apply in_int_not_kind in H2.
2:discriminate.
destruct H2 as (H2,_).
red in H2; rewrite El_int_prod in H2.
revert H2; apply eq_elim; apply cc_prod_ext.
 rewrite El_int_W_lift; reflexivity.

 red; intros.
 rewrite int_lift_rec_eq.
 rewrite int_subst_rec_eq.
 rewrite int_lift_rec_eq.
 apply El_morph; apply int_morph; auto with *.
 intros [|[|k]].
  compute; trivial.
  simpl; reflexivity.
  compute; fold minus.
  replace (k-0) with k; auto with *.
Qed.

Let Mirr : forall i j,
 val_ok e i j ->
 forall o' o'' f g,
 isOrd o' ->
 o' ⊆ o'' ->
 o'' ∈ osucc (int O i) ->
 f ∈ cc_prod (Wi i o') (U' i o') ->
 g ∈ cc_prod (Wi i o'') (U' i o'') ->
 fcompat (Wi i o') f g ->
 fcompat (Wi i (osucc o')) (int M (V.cons f (V.cons o' i))) (int M (V.cons g (V.cons o'' i))).
intros.
assert (Oo: isOrd (int O i)).
 destruct tyord_inv with (3:=ty_O)(4:=H); trivial.
assert (o'' ⊆ int O i).
 apply olts_le in H2; trivial.
assert (val_mono (push_fun (push_ord E (OSucct O)) (WIL 1 (Ref 0)) U)
         (V.cons f (V.cons o' i)) (I.cons daimon (I.cons daimon j))
         (V.cons g (V.cons o'' i)) (I.cons daimon (I.cons daimon j))).
 apply val_mono_1; auto with *.
  apply val_mono_refl; trivial.

  eauto using isOrd_inv.

  transitivity o''; auto.
apply stab in H7.
rewrite El_int_W_lift in H7; trivial.
Qed.

Let Usub : forall i j,
 val_ok e i j ->
 forall o' o'' x,
 isOrd o' ->
 o' ⊆ o'' ->
 o'' ∈ osucc (int O i) ->
 x ∈ Wi i o' ->
 U' i o' x ⊆ U' i o'' x.
intros.
assert (Oo: isOrd (int O i)).
 destruct tyord_inv with (3:=ty_O)(4:=H); trivial.
assert (o'' ⊆ int O i).
 apply olts_le in H2; trivial.
eapply El_sub with (1:=fx_sub_U).
apply val_mono_2; auto with *.
 apply val_mono_refl; eexact H.

 eauto using isOrd_inv.
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
 2:apply WREC_typ with (O:=int O i) (6:=Mty H) (7:=Mirr H) (8:=Usub H); auto with *.
 apply cc_prod_ext.
  rewrite El_int_W.
  reflexivity.

  red; intros.
  rewrite int_subst_rec_eq.
  rewrite <- V.cons_lams.
  2:apply V.cons_morph; reflexivity.
  rewrite V.lams0.
  rewrite H3; reflexivity.

 apply Bw_morph; reflexivity.

 unfold U'; auto.
(**)
 set (m:=Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j)))).
 red in H2; rewrite El_int_prod in H2.
 rewrite Real_int_prod; trivial.
 cut (inSAT (WFIX m)
       (piSAT0 (fun x => x ∈ Wi i (int O i))
         (RW A B i (int O i))
         (fun x =>
            Real (int U (V.cons x (V.cons (int O i) i))) 
              (cc_app (WREC (F' i) (int O i)) x)))).
  apply piSAT0_morph; intros; auto with *.
   red; intros; rewrite El_int_W; reflexivity.

   rewrite Real_int_W; auto with *.

   apply Real_morph; simpl;[|reflexivity].
   rewrite int_subst_rec_eq.
   apply int_morph; auto with *.
   intros [|[|k]]; reflexivity.

 unfold RW.
 apply WFIX_sat with
   (X:=fun o n => Real (int U (V.cons n (V.cons o i)))
     (cc_app (WREC (F' i) o) n)); trivial.
  apply Bw_morph; reflexivity.
  apply RAw_morph; reflexivity.
  do 3 red; intros; apply Real_morph; auto with *.
  rewrite H3; reflexivity.

  red; intros.
  apply cc_bot_intro in H7.
  apply fx_sub_U with (V.cons n (V.cons y i))
     (I.cons daimon (I.cons daimon j)) (I.cons daimon (I.cons daimon j)).
   apply val_mono_2; auto with *.

   assert (cc_app (WREC (F' i) y) n == cc_app (WREC (F' i) y') n).
    apply WREC_irr with (O:=int O i) (6:=Mty H) (7:=Mirr H) (8:=Usub H); auto with *.
     apply Bw_morph; reflexivity.
     unfold U'; auto.
   apply and_split; intros.
    red; rewrite <- H9.
    apply cc_prod_elim with (dom:=Wi i y) (F:=U' i y); trivial.
    apply WREC_typ with (O:=int O i) (6:=Mty H) (7:=Mirr H) (8:=Usub H); auto with *.
     apply Bw_morph; reflexivity.
     unfold U'; auto.
     transitivity y'; trivial.

    rewrite <- H9; trivial.

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
            (V.cons (WREC (F' i) o') (V.cons o' i)) (I.cons u (I.cons (tm O j) j))).
   apply vcons_add_var.
   3:discriminate.
    apply vcons_add_var; trivial.
    2:discriminate.
    split.
     red; rewrite El_int_osucc; trivial.

     simpl; rewrite Real_def; auto with *.
      apply ty_O in H.
      apply in_int_sn in H; trivial.

     assert (WREC (F' i) o' ∈ cc_prod (Wi i o') (U' i o')).
      apply WREC_typ with (O:=int O i) (6:=Mty H) (7:=Mirr H) (8:=Usub H); auto with *.
       apply Bw_morph; reflexivity.
       unfold U'; auto.
       eauto using isOrd_inv.
       apply olts_le in H3; trivial.
     apply and_split; intros.
      red; rewrite El_int_prod.
      revert H5; apply eq_elim; apply cc_prod_ext.
       rewrite El_int_W_lift; reflexivity.

       apply ext_fun_ty.

      rewrite Real_int_prod.
       revert u H4; apply piSAT0_morph; auto with *.
        red; intros.
        rewrite El_int_W_lift; reflexivity.

        intros.
        rewrite Real_int_W_lift; trivial.
        reflexivity.

        intros.
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
 rewrite WREC_unfold with (O:=int O i) (6:=Mty H) (7:=Mirr H) (8:=Usub H); auto with *.
 2:apply Bw_morph; reflexivity.
 2:unfold U'; auto.
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
 (app (WREC (F' i) (int O i)) (int N i) ==
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
 symmetry in H0; apply discr_mt_mkw in H0; contradiction.
destruct tyord_inv with (3:=ty_O)(4:=H); trivial.
apply WREC_eqn with (O:=int O i) (6:=Mty H) (7:=Mirr H) (8:=Usub H); auto with *.
 apply Bw_morph; reflexivity.

(* unfold U'; auto.*)
Qed.

Lemma TIeq: forall i i' j j' o',
  val_mono E i j i' j' ->
  isOrd o' ->
  TI (WF A B i) o' == TI (WF A B i') o'.
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
  rewrite (Aeq _ _ _ _ H) in H2.
  rewrite H3 in H2.
  split;[trivial|apply varSAT].

 (*apply cc_bot_morph;*) trivial.
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
simpl.
revert x H0.
elim oo using isOrd_ind; intros.
rewrite cc_bot_ax in H3; destruct H3.
 rewrite H3.
 rewrite WREC_strict with (O:=int O i) (6:=Mty isval) (7:=Mirr isval) (8:=Usub isval); auto with *.
 2:apply Bw_morph; reflexivity.
 2:unfold U'; auto.
 rewrite WREC_strict with (O:=int O i') (6:=Mty isval') (7:=Mirr isval') (8:=Usub isval'); auto with *.
  apply Bw_morph; reflexivity.
  unfold U'; auto.

 apply TI_inv in H3; trivial.
 destruct H3 as (o',?,?).
 assert (o_o' : isOrd o') by eauto using isOrd_inv.
 assert (o'_y : osucc o' ⊆ y).
  red; intros; apply le_lt_trans with o'; auto.
 assert (xty' : x ∈ TI (WF A B i') (osucc o')).
  rewrite <- TIeq with (1:=H); auto.
 rewrite <- WREC_irr with (O:=int O i) (6:=Mty isval) (7:=Mirr isval) (8:=Usub isval) (o:=osucc o'); auto with *.
 2:apply Bw_morph; reflexivity.
(* 2:unfold U'; auto.*)
 rewrite WREC_unfold with (O:=int O i) (6:=Mty isval) (7:=Mirr isval) (8:=Usub isval); auto with *.
 2:apply Bw_morph; reflexivity.
(* 2:unfold U'; auto.*)
 rewrite WREC_eqn with (O:=int O i') (6:=Mty isval') (7:=Mirr isval') (8:=Usub isval'); auto with *.
 2:apply Bw_morph; reflexivity.
(* 2:unfold U'; auto.*)
  do 2 red in stab; eapply stab.
  2:rewrite El_int_W_lift.
  2:apply cc_bot_intro; exact H4.
  apply val_mono_1 with (1:=H); auto with *.
   apply WREC_typ with (O:=int O i) (6:=Mty isval) (7:=Mirr isval) (8:=Usub isval); auto with *.
    apply Bw_morph; reflexivity.
(*    unfold U'; auto.*)

   apply WREC_typ with (O:=int O i') (6:=Mty isval') (7:=Mirr isval') (8:=Usub isval'); auto with *.
    apply Bw_morph; reflexivity.
(*    unfold U'; auto.*)

   red; intros.
   eapply H2; auto.

  revert xty'; apply TI_mono; auto with *.
   apply W_F_mono.
   apply Bw_morph; reflexivity.

   red; intros; apply le_lt_trans with o'; auto.
   apply inclo; apply H1; trivial.
Qed.

Lemma wfix_equals :
  fx_equals E O ->
  fx_equals E (WFix O M).
red; intros.
assert (isval := proj1 H0).
assert (isval' := proj1 (proj2 H0)).
destruct tyord_inv with (3:=ty_O) (4:=proj1 H0) as (Oo,_); trivial.
assert (fxs: fx_subval E O).
 apply fx_equals_subval; trivial.
red in H; specialize H with (1:=H0).
apply wfix_extend in fxs.
red in fxs.
specialize fxs with (1:=H0).
apply fcompat_typ_eq with (3:=fxs).
 rewrite El_int_W.
 eapply cc_prod_is_cc_fun.
 apply WREC_typ with (O:=int O i) (6:=Mty isval) (7:=Mirr isval) (8:=Usub isval); auto with *.
  apply Bw_morph; reflexivity.
(*  unfold U'; auto.*)

 rewrite El_int_W.
 rewrite TIeq with (1:=H0); trivial.
 rewrite H in Oo|-*.
 eapply cc_prod_is_cc_fun.
 apply WREC_typ with (O:=int O i') (6:=Mty isval') (7:=Mirr isval') (8:=Usub isval'); auto with *.
  apply Bw_morph; reflexivity.
(*  unfold U'; auto.*)
Qed.

End WFixRules.

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
assert (RBm : Proper (eq_set ==> eq_set ==> eqSAT)
          (fun a b => Real (int B (V.cons a i)) b)).
 do 3 red; intros.
 rewrite H,H0; reflexivity.
destruct tyord_inv with (3:=tyO) (4:=proj1 val_m); trivial.
destruct tyord_inv with (3:=tyO) (4:=proj1 (proj2 val_m)); trivial.
red in eqA; specialize eqA with (1:=val_m).
specialize subO with (1:=val_m).
red in xreal; rewrite El_int_W in xreal.
rewrite Real_int_W in xsat; trivial.
assert (cc_bot (TI (WF A B i) (int O i)) ⊆ cc_bot (TI (WF A B i') (int O i'))).
 apply cc_bot_mono.
 transitivity (TI (WF A B i') (int O i)).
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

(*   apply cc_bot_morph; trivial.*)

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
    do 2 red; intros.
    rewrite H5; reflexivity.
  rewrite H5 in xsat.
  apply neuSAT_def.
  unfold RW in xsat; rewrite rWi_neutral in xsat; auto with *.
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

End Make.

(** * Instantiation of the abstract model construction with ZFind_wbot. *)

(** ZFind_wbot is an instance of the above signature *)
Require ZFind_wbot.
Module W_Model : W_PartialModel.
  Import ZFind_wbot.

  Definition mkw := couple.
  Definition mkw_morph := couple_morph.
  Definition w1 := fst.
  Definition w1_morph := fst_morph.
  Definition w2 := snd.
  Definition w2_morph := snd_morph.
  Definition w1_eq := fst_def.
  Definition w2_eq := snd_def.
  Definition discr_mt_mkw := fun x f => discr_mt_pair (singl x) (pair x f).

  Definition W_F := W_F'.
  Definition W_F_mono := W_F'_mono.
  Definition W_F_ext :=
    fun A A' B B' X X' eqA eqB eqX =>
    W_F_ext A A' B B' (cc_bot X) (cc_bot X') eqA eqB (cc_bot_morph _ _ eqX).
(*  Definition W_F_elim A B Bm X := W_F_elim A B Bm (cc_bot X).*)
  Lemma W_F_elim A B :
    morph1 B ->
    forall X x,
    x ∈ W_F A B X ->
    w1 x ∈ A /\ w2 x ∈ (Π _ ∈ B (w1 x), cc_bot X) /\ x == mkw (w1 x) (w2 x).
intros Bm X x tyx.
destruct sigma_elim with (2:=tyx) as (eqx,(ty1,ty2)); auto.
Qed.
  Lemma W_F_intro A B :
    morph1 B ->
    forall X x f,
    x ∈ A ->
    f ∈ (Π i ∈ B x, cc_bot X) ->
    couple x f ∈ W_F A B X.
intros Bm X x f tyx tyf.
apply couple_intro_sigma; trivial.
do 2 red; intros.
rewrite H0; reflexivity.
Qed.

  Lemma W_F_def : forall A B X,
    W_F A B X == Σ x ∈ A, Π i ∈ B x, cc_bot X.
  reflexivity.
  Qed.
  Definition W_ord := W_ord'.
  Definition W_fix := W_fix'.
  Definition mt_not_in_W_F := mt_not_in_W_F'.
  Definition W_stages := W_stages'.
  Lemma W_ord_ord : forall A B, morph1 B ->
    isOrd (W_ord A B).
intros A B Bm.
unfold W_ord.
unfold ZFind_wbot.W_ord'.
apply Ffix_o_o.
 apply Wf_mono'; trivial.

 apply Wf_typ'; trivial.
Qed.
  Definition G_W_ord := G_W_ord'.
  Definition G_W_F := G_W_F'.

  Definition WREC := WREC'.
  Lemma WREC_morph : Proper ((eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) WREC.
do 3 red; intros.
apply TR_morph; trivial.
do 2 red; intros.
apply sup_morph; trivial.
red; intros.
apply squash_morph.
apply H; auto with *.
Qed.
  Definition WREC_typ := WREC'_typ.
  Definition WREC_eqn := WREC'_eqn.
  Definition WREC_irr := WREC'_irr.
  Definition WREC_unfold := WREC'_unfold.
  Definition WREC_strict := WREC'_strict.


End W_Model.

(** All that remains to do is apply the functor... *)
Module SN_W := Make(W_Model).
Export SN_W.
Print Assumptions typ_wfix.

