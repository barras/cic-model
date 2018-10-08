Require Import List Bool Models.
Require Import ZFfunext ZFecc ZFind_nat.
Import ZF ZFsum ZFnats ZFrelations ZFord ZFfix ZFgrothendieck.
Require ModelCC.

Import ModelZF.CCM.
Import ModelCC.BuildModel.
Import T R J.

Require Import Model_variance.

(** * Ordinals *)

(** Closure ordinal *)
Definition Infty := cst omega.

(** A special judgment (class of ordinals). It is not a set but kind does not
    restrict to ordinals *)
Definition typ_ord e O := forall i, val_ok e i -> isOrd (int O i).

Lemma typ_ord_lift e n O :
  typ_ord (List.skipn n e) O ->
  typ_ord e (lift n O).
red; intros.
unfold lift; rewrite int_lift_rec_eq.
rewrite V.lams0.
apply H.
red; intros.
assert (nth_error e (n+n0) = value T).
 clear H H0; revert e H1.
 elim n; simpl; intros; trivial.
 destruct e; auto.
 destruct n0; discriminate H1.
generalize (H0 _ _ H2).
destruct T as [(T,Tm)|]; simpl; trivial.
do 2 rewrite V.lams0.
unfold V.shift.
apply in_set_morph; auto with *.
apply Tm.
do 2 red; intros.
simpl.
replace (n+(S(n0+a))) with (S (n+n0+a)); auto with *.
Qed.

  Lemma typ_Infty e : typ_ord e Infty.
red; simpl; intros; auto.
Qed.

  Lemma typ_ord_ref : forall e n T,
    nth_error e n = value T ->
    T <> kind ->
    typ_ord e (lift (S n) T) ->
    typ_ord e (Ref n).
red; simpl; intros.
generalize (H2 _ _ H); simpl.
red in H1; specialize H1 with (1:=H2); simpl in H1.
destruct T as [(T,Tm)|]; simpl in *.
 eauto using isOrd_inv.

 elim H0; trivial.
Qed.

(** Ordinal successor (also type of ordinals less or equal to the argument) *)
Definition OSucc : term -> term.
(*begin show*)
intros o; left; exists (fun i => osucc (int o i)).
(*end show*)
do 2 red; intros.
rewrite H; reflexivity.
Defined.

Lemma typ_OSucc e O :
  typ_ord e O ->
  typ_ord e (OSucc O).
red; simpl; intros.
apply H in H0.
auto.
Qed.

Lemma typ_ord_le e O O':
  typ_ord e O ->
  typ e O' (OSucc O) ->
  typ_ord e O'.
red; simpl; intros.
red in H; specialize H with (1:=H1); simpl in H.
red in H0; specialize H0 with (1:=H1); simpl in H0.
apply isOrd_inv with (2:=H0); auto.
Qed.

Lemma typ_le_inv i e O O':
  typ e O' (OSucc O) ->
  val_ok e i ->
  int O' i ⊆ int O i.
intros.
apply H in H0; simpl in H0.
apply olts_le; trivial.
Qed.

(** O ≤ O *)
Lemma typ_ord_max e O :
  typ_ord e O ->
  typ e O (OSucc O).
red; simpl; intros.
apply lt_osucc.
apply H; trivial.
Qed.

(** * Nat *)

Definition Nat := cst NAT.

Definition NatI : term -> term.
(*begin show*)
intros o.
left; exists (fun i => NATi (int o i)).
(*end show*)
do 2 red; intros.
apply NATi_morph.
rewrite H; reflexivity.
Defined.

Require ModelECC.
Import ModelECC.WithoutFinitistUniverse.

Lemma typ_natI_type : forall e O,
  typ_ord e O ->
  typ e (NatI O) (type 0).
red; intros.
apply H in H0.
change (NATi (int O i) ∈ ecc 1).
apply G_incl with NAT; trivial.
2:apply NATi_NAT; trivial.
apply G_TI; intros; auto with *.
unfold NATf.
apply G_sum; trivial.
 apply G_union2; trivial.
Qed.

Lemma typ_natI : forall e o,
  typ e (NatI o) kind.
red; intros; simpl; trivial.
Qed.

(* Zero *)

Definition Zero := cst ZERO.

Lemma typ_Zero : forall e O,
  typ_ord e O ->
  typ e Zero (NatI (OSucc O)).
red; simpl; intros.
apply H in H0.
apply ZEROi_typ; trivial.
Qed.

(* Successor *)

Definition SuccI : term -> term.
(*begin show*)
intros o.
apply (Abs (NatI o)).
left; exists (fun i => SUCC (i 0)).
(*end show*)
do 2 red; intros.
unfold SUCC.
unfold eqX.
apply inr_morph.
apply H.
Defined.

Lemma typ_SuccI : forall e O,
  typ_ord e O ->
  typ e (SuccI O) (Prod (NatI O) (NatI (OSucc (lift 1 O)))).
red; simpl; intros.
apply H in H0.
apply cc_prod_intro; intros; auto with *.
 do 2 red; intros.
 apply NATi_morph.
 apply osucc_morph.
 apply int_morph; auto with *.
 do 2 red; intros.
 rewrite H2; reflexivity.

 unfold lift; rewrite int_lift_rec_eq.
 rewrite V.lams0.
 apply SUCCi_typ; auto.
Qed.

Lemma typ_app_SuccI : forall e i n,
  typ_ord e i ->
  typ e n (NatI i) ->
  typ e (App (SuccI i) n) (NatI (OSucc i)). 
intros.
apply typ_conv with (subst n (NatI (OSucc (lift 1 i)))).
3:discriminate.
 apply typ_app with (NatI i); trivial.
 2:discriminate.
 apply typ_SuccI; trivial.

 red; intros; simpl.
 unfold lift; rewrite int_lift_rec_eq.
 rewrite V.lams0.
 reflexivity.
Qed.

(* Case analysis *)

Definition Natcase (fZ fS n : term) : term.
(*begin show*)
left; exists (fun i => NATCASE (int fZ i) (fun k => int fS (V.cons k i)) (int n i)).
(*end show*)
do 2 red; intros.
red.
apply NATCASE_morph.
 rewrite H; reflexivity.
(**)
 red; intros.
 rewrite H; rewrite H0; reflexivity.
(**)
 rewrite H; reflexivity.
Defined.

Instance Natcase_morph :
  Proper (eq_term ==> eq_term ==> eq_term ==> eq_term) Natcase.
do 4 red; intros.
simpl; red; intros.
apply NATCASE_morph_gen; intros.
 rewrite H1; rewrite H2; reflexivity.
 rewrite H; rewrite H2; reflexivity.
 rewrite H0; rewrite H4; rewrite H2; reflexivity.
Qed.

Lemma Natcase_succ : forall O e n fZ fS,
  typ_ord e O ->
  typ e n (NatI O) ->
  eq_typ e (Natcase fZ fS (App (SuccI O) n)) (subst n fS).
red; intros.
red in H; specialize H with (1:=H1).
red in H0; specialize H0 with (1:=H1).
simpl in *.
rewrite <- (fun e1 e2 => NATCASE_morph (int fZ i) (int fZ i) e1
  (fun k => int fS(V.cons k i)) (fun k => int fS(V.cons k i)) e2
  (SUCC (int n (fun k => i k)))); auto with *.
 rewrite NATCASE_SUCC; auto.
  rewrite int_subst_eq; reflexivity.

  intros.
  rewrite H2; reflexivity.

 red; intros.
 rewrite H2; reflexivity.

 rewrite beta_eq; auto with *.
 red; intros.
 unfold SUCC; apply inr_morph; trivial.
Qed.

Existing Instance NATi_morph.

Lemma typ_natcase : forall e O P fZ fS n,
  typ_ord e O ->
  typ e fZ (App P Zero) ->
  typ (NatI O :: e) fS (App (lift 1 P) (App (SuccI (lift 1 O)) (Ref 0))) ->
  typ e n (NatI (OSucc O)) ->
  typ e (Natcase fZ fS n) (App P n).
red; intros.
red in H; specialize H with (1:=H3).
simpl in H; red in H.
red in H0; specialize H0 with (1:=H3).
simpl in H0; red in H0.
red in H2; specialize H2 with (1:=H3).
simpl in H2; red in H2.
simpl; red.
apply NATCASE_typ with (o:=int O i) (P:=fun n => app (int P i) n); trivial.
 do 2 red; intros.
 rewrite H4; reflexivity.

 do 2 red; intros.
 rewrite H4; reflexivity.

 intros.
 assert (val_ok (NatI O :: e) (V.cons n0 i)).
  apply vcons_add_var; trivial.
 apply H1 in H5; clear H1; simpl in H5.
 change (fun k => V.cons n0 i k) with (V.cons n0 i) in H5.
 rewrite beta_eq in H5; trivial.
  rewrite simpl_int_lift1 in H5; trivial.

  red; intros.
  unfold SUCC; apply inr_morph; trivial.

  rewrite simpl_int_lift1; auto.
Qed.

Lemma typ_natcase' : forall e O P fZ fS n T,
  typ_ord e O ->
  sub_typ e (App P n) T -> 
  typ e fZ (App P Zero) ->
  typ (NatI O :: e) fS
    (App (lift 1 P) (App (SuccI (lift 1 O)) (Ref 0))) ->
  typ e n (NatI (OSucc O)) ->
  typ e (Natcase fZ fS n) T.
intros.
apply typ_subsumption with (App P n); auto.
2:discriminate.
apply typ_natcase with O; trivial.
Qed.

  Lemma var_eq_NATi : forall e O,
    typ_ord (tenv e) O ->
    var_equals e O ->
    var_equals e (NatI O).
unfold var_equals; intros.
simpl.
apply NATi_morph; apply H0; trivial.
Qed.

  Lemma var_eq_OSucc : forall e O,
    var_equals e O ->
    var_equals e (OSucc O).
unfold var_equals; simpl; intros.
apply osucc_morph; apply H; trivial.
Qed.

  Lemma var_eq_Natcase : forall e O f1 f2 c,
    typ_ord (tenv e) O ->
    var_mono e O ->
    var_equals e f1 ->
    var_equals (push_var e (NatI O)) f2 ->
    typ (tenv e) c (NatI (OSucc O)) ->
    var_equals e c ->
    var_equals e (Natcase f1 f2 c).
red; intros e O f1 f2 c tyO H0 H1 H2 tyc H3 i i' H4.
simpl.
change (fun k => i k) with i.
change (fun k => i' k) with i'.
assert (ord : isOrd (int O i)).
 apply (tyO _ (proj1 H4)).
assert (ord' : isOrd (int O i')).
 apply (tyO _ (proj1 (proj2 H4))).
assert (int c i ∈ NATi (osucc (int O i))).
 destruct H4 as (H4,_).
 apply tyc in H4; trivial.
apply NATCASE_morph_gen; intros; auto.
apply H2.
red in H0; specialize H0 with (1:=H4).
rewrite H5 in H.
apply SUCCi_inv_typ in H; auto.
apply val_push_var; simpl; auto.
rewrite <- H6.
clear H5 H6 x'; revert x H.
apply TI_mono; auto.
Qed.

  Lemma var_ext_Succ e O :
    typ_ord (tenv e) O ->
    var_mono e O ->
    var_ext e (NatI O) (SuccI O).
do 2 red; simpl; intros.
red in H, H0.
specialize H0 with (1:=H1).
rewrite cc_beta_eq; auto with *.
rewrite cc_beta_eq; auto with *.
revert H2; apply TI_mono; auto with *.
 apply H; apply H1.
 apply H; apply H1.
Qed.

  Lemma var_mono_NATi : forall e O,
    typ_ord (tenv e) O ->
    var_mono e O ->
    var_mono e (NatI O).
unfold var_mono; intros.
simpl.
assert (oo : isOrd (int O i)).
 apply (H _ (proj1 H1)).
assert (oo' : isOrd (int O i')).
 apply (H _ (proj1 (proj2 H1))).
clear H.
apply TI_mono; auto.
Qed.

  Lemma var_mono_OSucc : forall e O,
    var_mono e O ->
    var_mono e (OSucc O).
unfold var_mono; simpl; intros.
red; intros.
unfold osucc in *.
apply subset_intro.
 apply power_intro; intros.
 apply H with (1:=H0); trivial.
 apply power_elim with z; trivial.
 apply subset_elim1 in H1; trivial.

 apply subset_elim2 in H1.
 destruct H1.
 rewrite H1; trivial.
Qed.


(*****************************************************************************)
(** ** Recursor (without case analysis) *)

(* NatFix O M is a fixpoint of domain Nati O with body M *)
Definition NatFix (O M:term) : term.
(*begin show*)
left.
exists (fun i =>
  NATREC (fun o' f => int M (V.cons f (V.cons o' i))) (int O i)).
(*end show*)
red; red; intros.
apply NATREC_morph.
 do 2 red; intros.
 rewrite H; rewrite H0; rewrite H1; reflexivity.
(**)  
 rewrite H.
 reflexivity.
Defined.


(** Typing rules of NatFix *)

Section NatFixRules.

  Variable E : fenv.
  Let e := tenv E.
  Variable O U M : term.
  Hypothesis M_nk : ~ eq_term M kind.
  Hypothesis ty_O : typ_ord e O.
  Hypothesis ty_M : typ (Prod (NatI (Ref 0)) U::OSucc O::e)
    M (Prod (NatI (OSucc (Ref 1)))
         (lift1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U)))).

  Hypothesis stab : var_ext
    (push_fun (push_ord E (OSucc O)) (NatI (Ref 0)) U)
    (NatI (OSucc (Ref 1)))
    M.

  Let F i := fun o' f => int M (V.cons f (V.cons o' i)).

  Lemma morph_fix_body : forall i, morph2 (F i).
unfold F; do 3 red; intros.
rewrite H; rewrite H0; reflexivity.
Qed.

  Lemma ext_fun_ty : forall o i,
    ext_fun (NATi o) (fun x => int U (V.cons x (V.cons o i))).
do 2 red; intros.
rewrite H0;reflexivity.
Qed.

  Hypothesis var_mono_U :
    var_mono (push_var (push_ord E (OSucc O)) (NatI (OSucc (Ref 0)))) U.


  Lemma ty_fix_body : forall i o f,
    val_ok e i ->
    o < osucc (int O i) ->
    f ∈ prod (NATi o) (fun x => int U (V.cons x (V.cons o i))) ->
    F i o f ∈
    prod (NATi (osucc o)) (fun x => int U (V.cons x (V.cons (osucc o) i))).
unfold F; intros.
specialize (ty_O _ H); simpl in ty_O.
assert (isOrd (int O i)).
 auto.
refine (eq_elim _ _ _ _ (ty_M (V.cons f (V.cons o i)) _)); simpl.
 apply prod_ext; auto with *.
 red; intros.
 change (fun k => V.cons f (V.cons o i) k) with (V.cons f (V.cons o i)).
 rewrite simpl_lift1; rewrite lift10.
 rewrite int_subst_rec_eq.
 rewrite <- V.cons_lams.
  rewrite V.lams0.
  rewrite int_lift_rec_eq.
  rewrite <- V.cons_lams.
   rewrite <- V.cons_lams.
    rewrite V.lams0.
    simpl.
    unfold V.shift; simpl.
    rewrite H4; reflexivity.

    red; red; intros.
    rewrite H5; reflexivity.

   red; red; intros.
   rewrite H5; reflexivity.

  red; red; intros.
  rewrite H5; reflexivity.

 apply vcons_add_var; auto.
 apply vcons_add_var; simpl; auto.
Qed.

  Lemma fix_body_irrel : forall i,
    val_ok e i ->
    NAT_ord_irrel (int O i) (F i) (fun o' x => int U (V.cons x (V.cons o' i))).
red; red; intros.
assert (isOrd (int O i)).
 auto.
red in stab.
assert (Hstab := stab (V.cons f (V.cons o i)) (V.cons g (V.cons o' i))).
simpl in Hstab.
apply Hstab; clear Hstab; trivial.
apply val_push_fun; auto.
apply ole_lts in H1; trivial.
apply val_push_ord; auto.
 apply val_mono_refl; trivial.

 simpl.
 apply isOrd_plump with o'; auto.
Qed.

  Lemma fix_codom_mono : forall o o' x x' i,
   val_ok e i ->
   isOrd o' ->
   o' ⊆ int O i ->
   isOrd o ->
   o ⊆ o' ->
   x ∈ NATi o ->
   x == x' ->
   int U (V.cons x (V.cons o i)) ⊆ int U (V.cons x' (V.cons o' i)).
intros.
apply var_mono_U.
apply val_push_var; simpl; auto.
 apply val_push_ord; simpl; auto; change (int O (fun k => i k)) with (int O i).
  apply val_mono_refl; trivial.

  apply ole_lts; auto.
  transitivity o'; trivial.

  apply ole_lts; auto.

 revert H4; apply TI_incl; auto.

 rewrite <- H5.
 revert H4; apply TI_incl; auto.
 apply ole_lts; auto.
Qed.

  Hint Resolve morph_fix_body ext_fun_ty ty_fix_body fix_codom_mono fix_body_irrel.

  Lemma nat_fix_eqn : forall i,
    val_ok e i ->
    NATREC (F i) (int O i) ==
    cc_lam (NATi (int O i))
      (fun x => cc_app (F i (int O i) (NATREC (F i) (int O i))) x).
intros.
assert (oi : isOrd (int O i)).
 auto.
apply NATREC_eqn with
  (ord:=int O i)
  (U:=fun o x => int U (V.cons x (V.cons o i))); auto.
intros.
apply ty_fix_body; trivial.
apply ole_lts; auto.
Qed.


  Lemma typ_nat_fix : typ e (NatFix O M) (Prod (NatI O) (subst_rec O 1 U)).
red; intros.
simpl.
assert (isOrd (int O i)).
 auto.
apply eq_elim with
   (prod (NATi (int O i)) (fun x => int U (V.cons x (V.cons (int O i) i)))).
 apply prod_ext.
  reflexivity.
  red; intros.
  rewrite int_subst_rec_eq.
  rewrite V.shift_cons.
  rewrite <- V.cons_lams.
   rewrite V.lams0.
   rewrite H2; reflexivity.

   do 2 red; intros.
   rewrite H3; reflexivity.
apply NATREC_wt with (F:=F i)
  (ord := int O i)
  (U:=fun o x => int U (V.cons x (V.cons o i))); intros; auto.
apply ty_fix_body; trivial.
apply ole_lts; trivial.
Qed.


  Lemma nat_fix_eq : forall N,
    typ e N (NatI O) ->
    eq_typ e (App (NatFix O M) N)
             (App (subst O (subst (lift 1 (NatFix O M)) M)) N).
red; intros.
change
 (app (NATREC (F i) (int O i)) (int N i) ==
  app (int (subst O (subst (lift 1 (NatFix O M)) M)) i) (int N i)).
do 2 rewrite int_subst_eq.
rewrite simpl_int_lift.
rewrite lift0_term.
simpl.
change (int O (fun k => i k)) with (int O i).
assert (O_lt := @ty_O _ H0).
simpl in O_lt.
rewrite nat_fix_eqn; trivial.
rewrite beta_eq.
 reflexivity.

 red; intros.
 rewrite H2; reflexivity.

 apply H; trivial.
Qed.

  Lemma var_ext_fix :
    var_mono E O ->
    var_ext E (NatI O) (NatFix O M).
intro subO.
do 2 red; intros.
assert (isval := proj1 H).
assert (isval' := proj1 (proj2 H)).
assert (oo: isOrd (int O i)).
 auto.
assert (oo': isOrd (int O i')).
 auto.
assert (inclo: int O i ⊆ int O i').
 apply subO in H; trivial.
clear subO.
assert (tyfx' :
  NATREC (F i') (int O i') ∈
  prod (NATi (int O i')) (fun x1 => int U (V.cons x1 (V.cons (int O i') i')))).
 apply NATREC_wt with
   (ord := int O i')
   (U:=fun o x => int U (V.cons x (V.cons o i'))); intros; auto.
 apply ty_fix_body; trivial.
 apply ole_lts; trivial.
assert (NATREC (F i) (int O i) ==
  cc_lam (NATi (int O i)) (cc_app (NATREC (F i') (int O i')))).
 apply NATREC_ext with  (ord := int O i)
  (U:=fun o x => int U (V.cons x (V.cons o i))); intros; auto.
  apply ty_fix_body; trivial.
  apply ole_lts; trivial.

  apply is_cc_fun_lam.
  do 2 red; intros; apply cc_app_morph; auto with *.

  red; intros.
  rewrite cc_beta_eq.
  eapply transitivity.
   apply cc_app_morph;[|reflexivity].
   apply nat_fix_eqn; trivial.
  rewrite cc_beta_eq.
   symmetry; apply stab.
   apply val_push_fun; trivial.
    apply val_push_ord; simpl; auto.
     apply isOrd_trans with (int O i); auto.

     apply lt_osucc; auto.

    apply cc_prod_intro; intros.
     do 2 red; intros; apply cc_app_morph; auto with *.

     do 2 red; intros.
     rewrite H5; reflexivity.

     rewrite cc_beta_eq; trivial.
      assert (tyfx1 : NATREC (F i) o' ∈
         prod (NATi o') (fun x1 => int U (V.cons x1 (V.cons o' i)))).
       apply NATREC_wt with
        (ord := o')
        (U:=fun o x => int U (V.cons x (V.cons o i))); intros; auto.
        apply isOrd_inv with (int O i); auto.

        apply fix_codom_mono; trivial.
        transitivity o'; trivial.
        transitivity (int O i); trivial.
        red; intros; apply isOrd_trans with o'; auto.

        reflexivity.

        apply ty_fix_body; trivial.
        apply ole_lts; trivial.
        red; intros; apply isOrd_trans with o'; auto.
        red; auto.

        red; intros.
        apply fix_body_irrel; trivial.
        transitivity o'; trivial.
        red; intros; apply isOrd_trans with o'; auto.
       rewrite H2 in tyfx1.
       specialize cc_prod_elim with (1:=tyfx1) (2:=H4); intro.
       rewrite cc_beta_eq in H5; trivial.
        rewrite cc_beta_eq in H5; trivial.
         do 2 red; intros; apply cc_app_morph; auto with *.

         revert H4; simpl; apply TI_incl; auto.

        do 2 red; intros; apply cc_app_morph; auto with *.

       do 2 red; intros; apply cc_app_morph; auto with *.

      revert H4; simpl; apply TI_incl; auto.

    red; intros.
    rewrite cc_beta_eq; auto.
     rewrite cc_beta_eq; auto with *.
      do 2 red; intros; apply cc_app_morph; auto with *.

      revert H4; simpl; apply TI_incl; auto. 

     do 2 red; intros; apply cc_app_morph; auto with *.

     simpl; trivial.

   do 2 red; intros; apply cc_app_morph; auto with *.

   revert H3; apply TI_mono; auto. 
    eauto using isOrd_inv.

    red; intros.
    apply inclo.
    apply isOrd_plump with o'; eauto using isOrd_inv, olts_le.

  do 2 red; intros; apply cc_app_morph; auto with *.

  revert H3; apply TI_mono; auto. 
   eauto using isOrd_inv.

   red; intros.
   apply isOrd_plump with o'; eauto using isOrd_inv, olts_le.
simpl in H1|-*; unfold F in H1 at 1; rewrite H1.
rewrite cc_beta_eq; auto with *.
 reflexivity.

 do 2 red; intros; apply cc_app_morph; auto with *.
Qed.

  Lemma var_eq_fix :
    var_equals E O ->
    var_equals E (NatFix O M).
red; intros.
assert (ty1 := typ_nat_fix _ (proj1 H0)); simpl in ty1.
assert (ty2 := typ_nat_fix _ (proj1 (proj2 H0))); simpl in ty2.
simpl.
rewrite cc_eta_eq with (1:=ty1).
rewrite cc_eta_eq with (1:=ty2).
apply cc_lam_ext; auto with *.
 apply NATi_morph.
 apply H; trivial.

 red; intros.
 rewrite <- H2.
 apply var_ext_fix; trivial.
 apply var_eq_sub; trivial.
Qed.

End NatFixRules.

Print Assumptions typ_nat_fix.

  Lemma typ_eq_Zero e O :
    typ_ord (tenv e) O ->
    typ_equals e Zero (NatI (OSucc O)).
split; simpl.
 red; reflexivity.
 apply typ_Zero; trivial.
Qed.


  Lemma typ_eq_Succ e O :
    typ_ord (tenv e) O ->
    var_equals e O ->
    typ_equals e (SuccI O) (Prod (NatI O) (NatI (OSucc (lift 1 O)))).
split; simpl.
 red; simpl; intros.
 apply cc_lam_ext.
  apply NATi_morph.
  apply H0; trivial.

  red; intros. 
  rewrite H3; reflexivity.

 apply typ_SuccI; trivial.
Qed.

  Lemma typ_ext_Succ e O :
    typ_ord (tenv e) O ->
    var_mono e O ->
    typ_ext e (SuccI O) (NatI O) (NatI (OSucc (lift 1 O))).
split; simpl.
 do 2 red; simpl; intros.
 rewrite cc_beta_eq; auto with *.
 rewrite cc_beta_eq; auto with *.
 change (x ∈ NATi (int O i')).
 revert H2; apply TI_mono; auto with *.
  apply H; apply H1.
  apply H; apply H1.

 apply typ_SuccI; trivial.
Qed.


(** Case-analysis *)
  Lemma typ_eq_natcase : forall e O P fZ fS n T,
    typ_ord (tenv e) O ->
    var_mono e O ->
    sub_typ (tenv e) (App P n) T -> 
    typ_equals e fZ (App P Zero) ->
    typ_equals (push_var e (NatI O)) fS
      (App (lift 1 P) (App (SuccI (lift 1 O)) (Ref 0))) ->
    typ_equals e n (NatI (OSucc O)) ->
    typ_equals e (Natcase fZ fS n) T.
intros.
destruct H2.
destruct H3.
simpl in H6.
destruct H4.
split.
 apply var_eq_Natcase with O; trivial.

 apply typ_natcase' with O P; trivial.
Qed.

(** Fixpoint *)

  Lemma typ_ext_fix : forall e O U M,
    typ_ord (tenv e) O ->
    var_mono e O ->
    typ_ext (push_fun (push_ord e (OSucc O)) (NatI (Ref 0)) U) M
      (NatI (OSucc (Ref 1))) (lift1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    var_mono (push_var (push_ord e (OSucc O)) (NatI (OSucc (Ref 0)))) U ->
    typ_ext e (NatFix O M) (NatI O) (subst_rec O 1 U).
intros e O U M tyO inclO (extM,tyM) tyU.
split.
 apply var_ext_fix with U; trivial.

 apply typ_nat_fix; trivial.
Qed.

  Lemma typ_eq_fix : forall e O U M,
    typ_ord (tenv e) O ->
    var_equals e O ->
    typ_ext (push_fun (push_ord e (OSucc O)) (NatI (Ref 0)) U) M
      (NatI (OSucc (Ref 1))) (lift1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    var_mono (push_var (push_ord e (OSucc O)) (NatI (OSucc (Ref 0)))) U ->
    typ_equals e (NatFix O M) (Prod (NatI O) (subst_rec O 1 U)).
intros e O U M tyO inclO (extM,tyM) tyU.
split.
 apply var_eq_fix with U; trivial.

 apply typ_nat_fix; trivial.
Qed.

  Lemma typ_eq_fix' : forall e O U M T,
    sub_typ (tenv e) (Prod (NatI O) (subst_rec O 1 U)) T ->
    typ_ord (tenv e) O ->
    var_equals e O ->
    var_mono (push_var (push_ord e (OSucc O)) (NatI (OSucc (Ref 0)))) U ->
    typ_ext (push_fun (push_ord e (OSucc O)) (NatI (Ref 0)) U) M
      (NatI (OSucc (Ref 1))) (lift1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    typ_equals e (NatFix O M) T.
intros.
apply typ_eq_subsumption with (2:=H).
2:discriminate.
apply typ_eq_fix; trivial.
Qed.



(************************************************************************)
(** Two examples of derived principles:
    - the standard recursor for Nat
    - subtraction with size information
*)

Section Example.

Definition nat_ind_typ K :=
   Prod (Prod (NatI Infty) K) (* P : nat -> Prop *)
  (Prod (App (Ref 0) Zero)
  (Prod (Prod (NatI Infty) (Prod (App (Ref 2) (Ref 0))
                        (App (Ref 3) (App (SuccI Infty) (Ref 1)))))
  (Prod (NatI Infty) (App (Ref 3) (Ref 0))))).

Definition nat_ind K :=
   Abs (*P*)(Prod (NatI Infty) K) (* P : nat -> Prop *)
  (Abs (*fZ*) (App (Ref 0) Zero)
  (Abs (*fS*) (Prod (*n*)(NatI Infty) (Prod (App (Ref 2) (Ref 0))
                                   (App (Ref 3) (App (SuccI Infty) (Ref 1)))))
  (NatFix Infty
    (*o,Hrec*)
    (Abs (*n*)(NatI (OSucc (Ref 1)))
      (Natcase
        (Ref 4)
        (*k*)(App (App (Ref 4) (Ref 0))
                  (App (Ref 2) (Ref 0)))
        (Ref 0)))))).

Lemma nat_ind_def e K (cK:forall f, noccur(B.cons false f)K) :
  typ_equals e (nat_ind K) (nat_ind_typ K).
assert (eq_term Nat (NatI Infty)).
 red; simpl.
 red; unfold NAT; reflexivity.
unfold nat_ind, nat_ind_typ.
apply typ_eq_abs with (s1:=kind); try discriminate; auto.
 reflexivity.

 split.
  apply var_eq_noc; noc_tac.
  trivial.

  red; simpl; trivial.
(* *)
apply typ_eq_abs with (s1:=kind); try discriminate; auto.
 reflexivity.

 split.
  apply var_eq_noc; noc_tac.
  red; simpl; trivial.
(* *)
apply typ_eq_abs with (s1:=kind); try discriminate; auto.
 reflexivity.

 split.
  apply var_eq_noc; noc_tac.
  red; simpl; trivial.
(* *)
apply typ_eq_fix' with (U:=App (Ref 4) (Ref 0)); auto.
 red; simpl; intros.
 exact H1.
 (* Infty : ord *)
 apply typ_Infty.
 (* Infty mono *)
 apply var_eq_noc; noc_tac.
 (* codom mono *)
 apply var_eq_sub; apply var_eq_noc; noc_tac.
(* fix body *)
apply typ_ext_abs; try discriminate.
 split;[|red;simpl;trivial].
 apply var_mono_NATi.
  apply typ_OSucc.
  apply typ_ord_ref with (OSucc Infty); auto.
   discriminate.
   red; simpl; auto.

  apply var_mono_OSucc.
  apply var_mono_ref; reflexivity.
(* case *)
apply typ_eq_natcase with (Ref 2) (Ref 5); auto.
 eapply typ_ord_ref.
  simpl; reflexivity.
  discriminate.
  red; simpl; auto.

 apply var_mono_ref; simpl; reflexivity.

 (* sub *)
 simpl tenv; apply sub_refl.
 red; simpl; intros; reflexivity.

 (* branch 0 *)
 eapply typ_eq_ref'.
  compute; reflexivity.
  simpl; reflexivity.
  discriminate.
 (* eqtrm *)
 red; intros; exact H1.

 (* branch S *)
 apply typ_eq_app with (App (Ref 6) (Ref 0))
   (App (Ref 7) (App (SuccI Infty) (Ref 1))); try discriminate.
  simpl tenv.
  apply sub_refl; red; intros; simpl.
  (* conversion (succ domain) *)
  unfold V.lams, V.shift; simpl.
  assert (i 0 ∈ NATi (i 3)).
   generalize (H0 0 _ (eq_refl _)); simpl.
   unfold V.lams, V.shift; simpl; trivial.
  rewrite beta_eq.
   rewrite beta_eq; auto with *.
   red; intros; apply inr_morph; trivial.

    red; intros; apply inr_morph; trivial.

   apply NATi_NAT in H1; trivial.
   generalize (H0 3 _ (eq_refl _)); simpl; intro.
   apply isOrd_inv with (osucc omega); auto.

  (**)
  apply typ_eq_app with (NatI Infty)
    (Prod (App (Ref 7) (Ref 0)) (App (Ref 8) (App (SuccI Infty) (Ref 1))));
    try discriminate.
   (* eqtrm *)
   red; simpl; intros.
   exact H1.

   eapply typ_eq_ref'.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.
    (* eqtrm *)
    red; simpl; intros; assumption.

   eapply typ_eq_ref'.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.
    (* subtyping: nat -> infty *)
    red; simpl; intros.
    unfold V.lams, V.shift in H1; simpl in H1.
    apply NATi_NAT in H1; trivial.
    generalize (H0 3 _ (eq_refl _)); simpl; intro.
    apply isOrd_inv with (osucc omega); auto.

  (**)
  eapply typ_ext_app.
   compute; trivial.
   simpl; reflexivity.
   discriminate.
   discriminate.
   2:simpl; reflexivity.
   discriminate.
   (* eqtrm *)
   red; simpl; intros; assumption.

   eapply typ_eq_ref'.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.
    (* eqtrm *)
    red; simpl; intros; assumption.

 (* Scrutinee *)
 eapply typ_eq_ref'.
  compute; reflexivity.
  simpl; reflexivity.
  discriminate.
  (* eqtrm *)
  red; simpl; intros; assumption.
Qed.


(** Subtraction *)

Definition minus O :=
  NatFix O
    (*o,Hrec*)
    (Abs (*n*) (NatI (OSucc (Ref(*o*)1)))
    (Abs (*m*) (NatI Infty)
    (Natcase
       Zero
       (*n'*)
       (Natcase
         (Ref 2)
         (*m'*)
         (App (App (Ref(*minus*)4) (Ref(*n'*)1)) (Ref(*m'*)0))
         (Ref(*m*)1))
       (Ref(*n*)1)))).

Definition minus_typ O := Prod (NatI O) (Prod (NatI Infty) (NatI (lift 2 O))).

Lemma minus_def e O :
  typ_ord (tenv e) O ->
  var_equals e O ->
  typ_equals e (minus O) (minus_typ O).
intros tyO eqO.
unfold minus, minus_typ.
apply typ_eq_fix' with (Prod (NatI Infty) (NatI (Ref 2))); auto.
 (* sub *)
 rewrite eq_subst_prod.
 apply sub_refl.
 apply eq_typ_prod.
  reflexivity.
 apply eq_typ_prod.
  red; intros; simpl; reflexivity.

  red; intros; simpl.
  unfold lift; rewrite int_lift_rec_eq.
  rewrite V.lams0.
  unfold V.lams, V.shift; simpl; reflexivity.

 (* codom mono *)
 apply var_mono_prod.
  apply var_eq_noc; noc_tac.

  apply var_mono_NATi; trivial.
   eapply typ_ord_ref.
    simpl; reflexivity.
    discriminate.

    apply typ_ord_lift; simpl.
    apply typ_OSucc; trivial.

   apply var_mono_ref.
   compute; reflexivity.

 (* fix body *)
 apply typ_ext_abs; try discriminate.
  split;[|red;simpl; trivial].
  apply var_mono_NATi.
   apply typ_OSucc.
   eapply typ_ord_ref.
    simpl; reflexivity.
    discriminate.

    apply typ_ord_lift; simpl.
    apply typ_OSucc; trivial.

   apply var_mono_OSucc; auto.
   apply var_mono_ref.
   compute; reflexivity.

 (* 2nd abs *)
 rewrite eq_lift_prod.
 rewrite eq_subst_prod.
 unfold lift1; rewrite eq_lift_prod.
 eapply typ_eq_subsumption.
 apply typ_eq_abs with (s1:=kind); try discriminate; auto.
  6:discriminate.
  5:apply sub_refl; reflexivity.
  discriminate.
  red; intros; simpl; reflexivity.

  split;[|red;simpl;trivial].
  apply var_eq_noc; noc_tac.

 (**)
 apply typ_eq_natcase with (Ref 3)
    (Abs (NatI (OSucc (Ref 3))) (NatI (OSucc (Ref 4)))); auto.
  eapply typ_ord_ref.
   simpl; reflexivity.
   discriminate.

   apply typ_ord_lift; simpl.
   apply typ_OSucc; trivial.

  apply var_mono_ref.
  compute; reflexivity.

  (* conversion *)
  apply sub_refl.
  rewrite eq_typ_betar.
  3:discriminate.
   red; intros; simpl.
   unfold V.lams, V.shift; simpl.
   reflexivity.

   apply typ_var0; split; [discriminate|].
   apply sub_refl.
   red; simpl; reflexivity.

  (* branch 0 *)
  eapply typ_eq_subsumption.
   apply typ_eq_Zero.
   eapply typ_ord_ref with (n:=3).
    simpl; reflexivity.
    discriminate.
    apply typ_ord_lift; simpl.
    apply typ_OSucc; trivial.

   2:discriminate.
   apply sub_refl.
   rewrite eq_typ_betar.
   3:discriminate.
    red; simpl; reflexivity.

    apply typ_Zero.
    eapply typ_ord_ref.
     simpl; reflexivity.
     discriminate.
     apply typ_ord_lift; simpl.
     apply typ_OSucc; trivial.

  (* branch S *)
  apply typ_eq_natcase with Infty
     (Abs (NatI (OSucc Infty)) (NatI (OSucc (Ref 5)))); auto.
   apply typ_Infty.

   red; simpl; reflexivity.

   apply sub_refl.
   rewrite eq_typ_betar.
   3:discriminate.
    unfold lift; rewrite eq_lift_abs.
    rewrite eq_typ_betar.
    3:discriminate.
     red; intros; simpl; reflexivity.

     apply typ_conv with (NatI (OSucc (lift_rec 1 0 (Ref 3)))).
     3:discriminate.
      apply typ_app_SuccI; trivial.
       apply typ_ord_lift; simpl.
       eapply typ_ord_ref.
        simpl; reflexivity.
        discriminate.
        apply typ_ord_lift; simpl.
        apply typ_OSucc; trivial.

       apply typ_var0; split;[discriminate|].
       apply sub_refl; red; intros; simpl.
       reflexivity.

     red; intros; simpl.
     reflexivity.

    apply typ_var0; split;[discriminate|].
    (* subtyping infty < infty+ *)
    red; simpl; intros.
    revert H0; apply TI_incl; auto with *.

  (* branch 0 *)
  eapply typ_eq_ref'.
   compute; reflexivity.
   simpl; reflexivity.
   discriminate.

   apply sub_refl.
   rewrite eq_typ_betar.
   3:discriminate.
    red; intros; simpl.
    unfold V.lams, V.shift; simpl; reflexivity.

    eapply typ_Zero; auto.
    apply typ_Infty.

  (* branch S *)    
  apply typ_eq_app with (NatI Infty) (NatI (Ref 6)).
   discriminate.
   discriminate.

   unfold lift; rewrite eq_lift_abs.
   apply sub_trans with (NatI (OSucc (Ref 5))).
    (* sub nat(o) < nat(o+) *)
    red; simpl; intros.
    unfold V.lams, V.cons, V.shift in H; simpl in H0.
    assert (isOrd (i 5)).
     assert (h := H 5 _ (refl_equal _)); simpl in h.
     apply isOrd_inv with (2:=h).
     apply isOrd_succ.
     rewrite <- int_lift_rec_eq.
     revert H; apply typ_ord_lift; simpl; trivial.
    revert H0; apply TI_incl; auto with *.

    apply sub_refl.
    rewrite eq_typ_betar.
    3:discriminate.
     red; intros; simpl.
     unfold V.lams, V.shift; simpl.
     reflexivity.

     apply typ_conv with (NatI (OSucc (lift_rec 1 0 Infty))).
     3:discriminate.
      apply typ_app_SuccI; auto.
       apply typ_Infty.

      apply typ_var0; split;[discriminate|].
      apply sub_refl; red; intros; simpl.
      reflexivity.

     red; intros; simpl.
     reflexivity.

   eapply typ_ext_app.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.
    discriminate.
    2:simpl; reflexivity.
    discriminate.

    apply sub_refl.
    unfold subst, lift1; rewrite eq_lift_prod.
    rewrite eq_subst_prod.
    red; intros; simpl; reflexivity.

    eapply typ_eq_ref'.
     compute; reflexivity.
     simpl; reflexivity.
     discriminate.

     apply sub_refl.
     red; intros; simpl; reflexivity.

     eapply typ_eq_ref'.
      compute; reflexivity.
      simpl; reflexivity.
      discriminate.

      apply sub_refl.
      red; intros; simpl; reflexivity.

   (**)
   eapply typ_eq_ref'.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.
    (* infty < infty+ *)
    red; simpl; intros.
    revert H0; apply TI_incl; auto with *.

  (**)
  eapply typ_eq_ref'.
   compute; reflexivity.
   simpl; reflexivity.
   discriminate.

   apply sub_refl.
   red; intros; simpl; reflexivity.
Qed.

End Example.

(* begin hide *)
Print Assumptions minus_def.
(* end hide *)
