(** Model of ECC+W in the type-based termination presentation.
*)

Require Import List Bool Models TypModels.
Require Import ZF ZFsum ZFnats ZFrelations ZFord ZFfix ZFgrothendieck.
Require Import ZFfunext ZFind_w.
Require Import ModelCC ModelECC.


(** Importing the common model constructions + variance judgments *)

Import BuildModel.
Import T J R.

Require Import Model_variance.
Module V <: Variance BuildModel := Model_variance.

(** Ordinals *)

Definition Ordt (o:set) : term := cst o.

Definition typ_ord_kind : forall e o, typ e (Ordt o) kind.
red; simpl; trivial.
Qed.

Lemma tyord_inv : forall e i o o',
  isOrd o' ->
  typ e o (Ordt o') ->
  val_ok e i ->
  isOrd (int o i) /\ int o i < o'.
unfold typ; simpl; intros.
unfold ZFnats.lt.
red in H0.
split; auto.
apply isOrd_inv with o'; trivial.
apply H0; trivial.
Qed.

Definition OSucc : term -> term.
(*begin show*)
intros o; left; exists (fun i => osucc (int o i)).
(*end show*)
do 2 red; intros.
rewrite H; reflexivity.
Defined.

  Lemma var_mono_OSucc : forall e O,
    var_mono e O ->
    var_mono e (OSucc O).
unfold var_mono; red; simpl; intros.
unfold osucc in H1|-*.
rewrite subset_ax in H1 |-*.
destruct H1; split; auto.
revert H1; apply power_mono.
red; intros; eauto.
revert H1; apply H; trivial.
Qed.

  Lemma typ_mono_OSucc : forall e O o,
    isOrd o ->
    typ_mono e O (Ordt o)->
    typ_mono e (OSucc O) (Ordt (osucc o)).
destruct 2.
split.
 apply var_mono_OSucc; trivial.

 red; simpl; intros.
 red.
 destruct tyord_inv with (2:=H1)(3:=H2) as (_,?); trivial.
 apply lt_osucc_compat; trivial.
Qed.

(** W *)

Section Wtypes_typing.

Variable o : set.
Hypothesis oo : isOrd o.

Variable e:env.

Variable A B:term.
Hypothesis Ank : A <> kind.
Hypothesis Bnk : B <> kind.

Let Aw i := int A i.
Let Bw i x := int B (V.cons x i).
Let Ww i := W (Aw i) (Bw i).

Definition WF' i := W_F (Aw i) (Bw i).

Instance Aw_morph : Proper (eq_val==>eq_set) Aw.
do 2 red; intros.
apply int_morph; auto with *.
Qed.

Instance Bw_morph : Proper (eq_val==>eq_set==>eq_set) Bw.
do 3 red; intros.
unfold Bw.
rewrite H; rewrite H0; reflexivity.
Qed.

Instance WF'_morph : Proper (eq_val ==> eq_set ==> eq_set) WF'.
do 3 red; intros.
unfold WF'.
apply W_F_ext; trivial.
 apply Aw_morph; trivial.

 red; intros.
 apply Bw_morph; trivial.
Qed.

Definition WI (O:term) : term.
(*begin show*)
left; exists (fun i => TI (WF' i) (int O i)).
(*end show*)
do 3 red; intros.
apply TI_morph_gen.
 apply WF'_morph; trivial.

 rewrite H; reflexivity.
Defined.

Lemma typ_WI : forall eps O,
  isOrd eps ->
  typ e O (Ordt eps) ->
  typ e (WI O) kind.
red; simpl; trivial.
Qed.

(** Constructor *)

Require Import ZFpairs.

Definition Wc (x:term) (f:term) : term.
(* begin show *)
left; exists (fun i => couple (int x i) (int f i)).
(* end show *)
do 2 red; intros; apply couple_morph; apply int_morph; auto with *.
Defined.

Lemma typ_Wc : forall O X F,
  typ e O (Ordt o) ->
  typ e X A ->
  typ e F (Prod (subst X B) (lift 1 (WI O))) ->
  typ e (Wc X F) (WI (OSucc O)).
red; intros.
red in H0; specialize H0 with (1:=H2).
apply in_int_not_kind in H0; trivial.
red in H1; specialize H1 with (1:=H2).
apply in_int_not_kind in H1.
2:discriminate.
destruct tyord_inv with (2:=H)(3:=H2) as (?,?); trivial.
apply in_int_el.
assert (couple (int X i) (int F i) ∈ TI (WF' i) (osucc (int O i))).
 apply TI_intro with (int O i); auto.
  apply WF'_morph; reflexivity.

  unfold WF'.
  apply couple_intro_sigma.
   do 2 red; intros.
   rewrite H6; reflexivity.

   apply H0.

   rewrite El_int_arr in H1.
   rewrite int_subst_eq in H1.
   trivial.
assumption.
Qed.


(* Case analysis *)

Definition W_CASE b w :=
  sigma_case (fun x f => cc_app (cc_app b x) f) w.

Definition Wcase (b n : term) : term.
(*begin show*)
left; exists (fun i => W_CASE (int b i) (int n i)).
(*end show*)
do 3 red; intros.
apply sigma_case_morph.
 do 2 red; intros.
 rewrite H; rewrite H0; rewrite H1; reflexivity.

 rewrite H; reflexivity.
Defined.

Instance Wcase_morph :
  Proper (eq_term ==> eq_term ==> eq_term) Wcase.
do 3 red; simpl; intros.
red; intros.
 unfold sigma_case.
 apply cond_set_morph.
  rewrite H0; rewrite H1; reflexivity.
  rewrite H; rewrite H0; rewrite H1; reflexivity.
Qed.

Existing Instance Wcase_morph.

Lemma Wcase_iota : forall X F G,
  eq_typ e (Wcase G (Wc X F)) (App (App G X) F).
red; intros.
simpl.
unfold W_CASE.
rewrite sigma_case_couple with (a:=int X i) (b:=int F i).
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
destruct tyord_inv with (2:=H)(3:=H2) as (?,?); trivial.
red in H0; specialize H0 with (1:=H2).
apply in_int_not_kind in H0;[|discriminate].
red in H1; specialize H1 with (1:=H2).
apply in_int_not_kind in H1;[|discriminate].
apply in_int_el.
simpl int in H0.
simpl in H1.
red; simpl.
rewrite TI_mono_succ in H1; auto with *.
2:apply W_F_mono; trivial.
2:apply Bw_morph; reflexivity.
assert (fst (int n i) ∈ Aw i).
 apply fst_typ_sigma in H1; trivial.
 assert (snd (int n i) ∈ cc_arr (Bw i (fst (int n i))) (TI (WF' i) (int O i))).
  apply snd_typ_sigma with (y:=fst(int n i)) in H1; auto with *.
  do 2 red; intros.
  rewrite H7; reflexivity.
 assert (int n i == couple (fst (int n i)) (snd (int n i))).
  apply (surj_pair _ _ _ (subset_elim1 _ _ _ H1)).
 unfold W_CASE, sigma_case.
 rewrite cond_set_ok; trivial.
 specialize cc_prod_elim with (1:=H0) (2:=H5); clear H0; intro H0.
 apply eq_elim with
    (cc_app (int (lift 2 P) (V.cons (snd (int n i)) (V.cons (fst (int n i)) i)))
       (couple (fst (int n i)) (snd (int n i)))).
  apply cc_app_morph; auto with *.
  do 2 rewrite simpl_int_lift.
  rewrite lift0_term; reflexivity.

  apply cc_prod_elim with (1:=H0).
  revert H6; apply eq_elim.
  apply cc_prod_ext.
   reflexivity.

   red; intros.
   rewrite V.lams0.
   reflexivity.
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

  Lemma var_mono_Wi : forall e o A B O,
    isOrd o ->
    A <> kind ->
    typ (tenv e) O (Ordt o) ->
    var_equals e A ->
    var_equals (push_var e A) B ->
    var_mono e O ->
    var_mono e (WI A B O).
unfold var_mono.
intros e o A B O oo Ank tyO eqA eqB subO i i' val_m x xty.
destruct tyord_inv with (2:=tyO) (3:=proj1 val_m); trivial.
destruct tyord_inv with (2:=tyO) (3:=proj1 (proj2 val_m)); trivial.
red in eqA; specialize eqA with (1:=val_m).
specialize subO with (1:=val_m).
assert (x ∈ TI (WF' A B i') (int O i)).
 revert xty; simpl; apply eq_elim.
 apply TI_morph_gen; auto with *.
  red; intros.
  apply W_F_ext; auto with *.
  red; intros.
  apply eqB.
  apply val_push_var; auto with *.
  rewrite H5 in H4.
  rewrite eqA in H4; trivial.

  reflexivity.

 revert H3; apply TI_mono; trivial.
 apply W_F_morph.
 apply Bw_morph; reflexivity.
Qed.

  Lemma var_mono_Wi' : forall e o A B O,
    isOrd o ->
    A <> kind ->
    typ_equals e A kind ->
    typ_equals (push_var e A) B kind ->
    typ_mono e O (Ordt o) ->
    var_mono e (WI A B O).
intros e o A B O oo Ank (eqA,_) (eqB,_) (subO,tyO).
apply var_mono_Wi with (o:=o); trivial.
Qed.

(*****************************************************************************)
(** Recursor (without case analysis) *)

(* WFix O M is a fixpoint of domain WI O with body M *)
Definition WFix (O M:term) : term.
(*begin show*)
left.
exists (fun i =>
         WREC (fun o' f => int M (V.cons f (V.cons o' i))) (int O i)).
(*end show*)
do 2 red; intros.
unfold WREC.
unfold ZFfixrec.REC.
apply TR_morph.
2:rewrite H; reflexivity.
do 2 red; intros.
apply sup_morph; trivial.
red; intros.
apply int_morph; auto with *.
apply V.cons_morph.
 apply H0; trivial.
apply V.cons_morph; trivial.
Defined.


(** Typing rules of WFix *)

Section WFixRules.

  Variable infty : set.
  Hypothesis infty_ord : isOrd infty.
  Variable E : fenv.
  Let e := tenv E.
  Variable A B O U M : term.
  Hypothesis A_nk : A <> kind.
  Hypothesis Aeq : var_equals E A.
  Hypothesis Beq : var_equals (push_var E A) B.

  Definition WIL n := WI (lift n A) (lift_rec n 1 B).

  Hypothesis ty_O : typ e O (Ordt infty).
  Hypothesis ty_M : typ (Prod (WIL 1 (Ref 0)) U::OSucc O::e)
    M (Prod (WIL 2 (OSucc (Ref 1)))
         (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U)))).

  Hypothesis stab : var_ext
    (push_fun (push_ord E (OSucc O)) (WIL 1 (Ref 0)) U)
    (WIL 2 (OSucc (Ref 1)))
    M.

  Lemma WF'mono i : Proper (incl_set==>incl_set) (WF' A B i).
do 2 red; intros.
unfold WF'.
apply W_F_mono; trivial.
do 2 red; intros; apply Bw_morph; auto with *.
Qed.
  Hint Resolve WF'mono.

  Let Wi i o := TI (WF' A B i) o.
  Let F i := fun o' f => int M (V.cons f (V.cons o' i)).
  Let U' i := fun o' x => int U (V.cons x (V.cons o' i)).

  Local Instance U'morph : forall i, morph2 (U' i).
do 3 red; intros; unfold U'.
rewrite H; rewrite H0; reflexivity.
Qed.
  Instance morph_fix_body : forall i, morph2 (F i).
unfold F; do 3 red; intros.
rewrite H; rewrite H0; reflexivity.
Qed.
  Lemma ext_fun_ty : forall o i,
    ext_fun (Wi i o) (U' i o).
do 2 red; intros.
rewrite H0;reflexivity.
Qed.
  Hint Resolve U'morph morph_fix_body ext_fun_ty.


  Hypothesis var_mono_U :
    var_mono (push_var (push_ord E (OSucc O)) (WIL 1 (OSucc (Ref 0)))) U.


Lemma El_int_W_lift O' n i :
  int (WIL n O') i == TI (WF' A B (V.shift n i)) (int O' i).
unfold WIL; simpl.
apply TI_morph_gen; auto with *.
2:reflexivity.
red; intros.
unfold WF'; apply W_F_ext; auto with *.
 unfold lift; rewrite int_lift_rec_eq; rewrite V.lams0; reflexivity.

 red; intros.
 rewrite int_lift_rec_eq.
 rewrite <- V.cons_lams.
 2:apply V.shift_morph; trivial.
 rewrite V.lams0.
 rewrite H1; reflexivity.
Qed.

  Lemma val_mono_1 i i' y y' f g:
    val_mono E i i' ->
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
    val_mono (push_fun (push_ord E (OSucc O)) (WIL 1 (Ref 0)) U)
      (V.cons f (V.cons y i)) (V.cons g (V.cons y' i')).
intros is_val Oo Oo' oo' yo y'o yO y'O yy' fty gty eqfg.
apply val_push_fun.
 apply val_push_ord; auto.
  apply ole_lts; trivial.

  apply ole_lts; trivial.

 revert fty; apply eq_elim; apply cc_prod_ext; intros.
  rewrite El_int_W_lift; reflexivity.

  apply ext_fun_ty.

 revert gty; apply eq_elim; apply cc_prod_ext; intros.
  rewrite El_int_W_lift; reflexivity.

  apply ext_fun_ty.

 rewrite El_int_W_lift.
 trivial.
Qed.

  Lemma val_mono_2 i y y' n n':
    val_ok e i ->
    isOrd (int O i) ->
    isOrd y ->
    isOrd y' ->
    y ⊆ y' ->
    y' ⊆ int O i ->
    n ∈ Wi i y ->
    n == n' ->
    val_mono (push_var (push_ord E (OSucc O)) (WIL 1 (OSucc (Ref 0))))
      (V.cons n (V.cons y i)) (V.cons n' (V.cons y' i)).
Proof.
intros.
apply val_push_var; auto with *.
 apply val_push_ord; auto with *.
  apply val_mono_refl; trivial.

  apply ole_lts; auto.
  transitivity y'; trivial.

  apply ole_lts; auto.

 red; rewrite El_int_W_lift.
 revert H5; apply TI_incl; simpl; auto.

 red; rewrite El_int_W_lift.
 rewrite <- H6.
 revert H5; apply TI_incl; simpl; auto.
 apply ole_lts; trivial.
Qed.


  Lemma fix_codom_mono : forall o o' x x' i,
   val_ok e i ->
   isOrd o' ->
   o' ⊆ int O i ->
   isOrd o ->
   o ⊆ o' ->
   x ∈ Wi i o ->
   x == x' ->
   U' i o x ⊆ U' i o' x'.
Proof.
intros.
red in var_mono_U.
assert (val_mono (push_var (push_ord E (OSucc O)) (WIL 1(OSucc(Ref 0))))
  (V.cons x (V.cons o i)) (V.cons x' (V.cons o' i))).
 apply val_mono_2; trivial.
 apply ty_O in H.
 apply in_int_not_kind in H;[|discriminate].
 apply isOrd_inv with infty; auto.
apply var_mono_U in H6; trivial.
Qed.

  Lemma ty_fix_body : forall i o f,
   val_ok e i ->
   o < osucc (int O i) ->
   f ∈ cc_prod (Wi i o) (U' i o) ->
   F i o f ∈ cc_prod (Wi i (osucc o)) (U' i (osucc o)).
unfold F; intros.
destruct tyord_inv with (2:=ty_O) (3:=H); trivial.
assert (val_ok (Prod (WIL 1 (Ref 0)) U::OSucc O::e) (V.cons f (V.cons o i))).
 apply vcons_add_var; auto.
  apply vcons_add_var; auto.

  red; revert H1; apply eq_elim.
  apply cc_prod_ext.
   rewrite El_int_W_lift.
   reflexivity.

   apply ext_fun_ty.
red in ty_M.
specialize ty_M with (1:=H4).
apply in_int_not_kind in ty_M.
2:discriminate.
revert ty_M; apply eq_elim.
symmetry; apply cc_prod_ext.
 rewrite El_int_W_lift.
 reflexivity.

 red; intros.
 rewrite int_lift_rec_eq.
 rewrite int_subst_rec_eq.
 rewrite int_lift_rec_eq.
 apply int_morph; auto with *.
 do 3 red.
 intros [|[|k]].
  compute; trivial.

  unfold V.lams, V.shift; simpl.
  reflexivity.

  unfold V.lams, V.shift; simpl.
  replace (k-0) with k; auto with *.
Qed.

  Lemma fix_body_irrel : forall i,
    val_ok e i ->
    Wi_ord_irrel (int A i)
      (fun x => int B (V.cons x i)) (int O i)
      (F i) (U' i).
red; intros.
assert (isOrd (int O i)).
 apply ty_O in H.
 apply isOrd_inv with infty; auto.
red in stab.
assert (Hstab := stab (V.cons f (V.cons o i)) (V.cons g (V.cons o' i))).
red in Hstab.
red; intros.
eapply Hstab; clear Hstab; trivial.
 apply val_mono_1; auto with *.
  apply val_mono_refl; exact H.

  transitivity o'; trivial.

 rewrite El_int_W_lift; auto.
Qed.

  Hint Resolve morph_fix_body ext_fun_ty ty_fix_body fix_codom_mono fix_body_irrel.


Let fix_typ o i:
  val_ok e i ->
  isOrd o ->
  isOrd (int O i) ->
  o ⊆ int O i ->
  WREC (F i) o ∈ cc_prod (Wi i o) (U' i o).
intros.
eapply WREC_wt with (U:=U' i); trivial.
 do 2 red; intros.
 apply Bw_morph; auto with *.

 intros.
 apply fix_codom_mono with (1:=H); trivial.
 transitivity o; auto.

 intros.
 apply ty_fix_body with (1:=H); trivial.
 apply ole_lts; trivial.
 transitivity o; trivial.
 apply ord_lt_le; auto.
 
 red; intros; apply fix_body_irrel with (1:=H); trivial.
 transitivity o; trivial.
Qed.


  Lemma fix_irr i o o' x :
    val_ok e i ->
    isOrd o ->
    isOrd o' ->
    isOrd (int O i) ->
    o ⊆ o' ->
    o' ⊆ int O i ->
    x ∈ Wi i o ->
    cc_app (WREC (F i) o) x == cc_app (WREC (F i) o') x.
intros.
assert (WRECi := WREC_irrel).
red in WRECi.
apply WRECi with 
  (A:=int A i) (B:=fun x=>int B (V.cons x i))
  (ord:=int O i) (U:=U' i); auto with *.
 do 2 red; intros; apply Bw_morph; auto with *.

 intros.
 apply ty_fix_body with (1:=H); trivial.
 apply ole_lts; trivial.
 apply ord_lt_le; auto.
Qed.

Lemma fix_eqn0 : forall i o,
  val_ok e i ->
  isOrd o ->
  isOrd (int O i) ->
  o ⊆ int O i ->
  WREC (F i) (osucc o) == F i o (WREC (F i) o).
intros.
unfold WREC at 1.
rewrite ZFfixrec.REC_eq; auto with *.
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

   apply fix_typ with (1:=H); trivial.
 assert (F i o (WREC (F i) o) ∈ cc_prod (TI (WF' A B i) (osucc o)) (U' i (osucc o))).
  apply ty_fix_body with (1:=H); trivial.
   apply ole_lts; auto.

   apply fix_typ with (1:=H); trivial.
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
  apply fix_typ with (1:=H); auto.
  apply fix_typ with (1:=H); auto.

  clear firrel.
  red; intros.
  apply fix_irr with (1:=H); trivial.

 exists o;[apply lt_osucc;trivial|trivial].
Qed.

Lemma fix_eqn : forall i o n,
  val_ok e i ->
  isOrd o ->
  isOrd (int O i) ->
  o ⊆ int O i ->
  n ∈ TI (WF' A B i) (osucc o) ->
  cc_app (WREC (F i) (osucc o)) n ==
  cc_app (F i o (WREC (F i) o)) n.
intros.
rewrite fix_eqn0 with (1:=H); trivial.
unfold F.
reflexivity.
Qed.

Lemma typ_wfix :
  typ e (WFix O M) (Prod (WI A B O) (subst_rec O 1 U)).
red; intros.
destruct tyord_inv with (2:=ty_O)(3:=H); trivial.
apply in_int_el.
eapply eq_elim.
2:simpl.
2:apply fix_typ with (1:=H); auto with *.
2:reflexivity.
apply cc_prod_ext.
 reflexivity.

 red; intros.
 rewrite int_subst_rec_eq.
 rewrite <- V.cons_lams.
 2:apply V.cons_morph; reflexivity.
 rewrite V.lams0.
 rewrite H3; reflexivity.
Qed.

(** Fixpoint equation. *)
Lemma wfix_eq : forall N,
  typ e N (WI A B O) ->
  eq_typ e (App (WFix O M) N)
           (App (subst O (subst (lift 1 (WFix O M)) M)) N).
intros N tyN.
red; intros.
red.
change
 (cc_app (WREC (F i) (int O i)) (int N i) ==
  cc_app (int (subst O (subst (lift 1 (WFix O M)) M)) i) (int N i)).
do 2 rewrite int_subst_eq.
rewrite simpl_int_lift.
rewrite lift0_term.
red in tyN; specialize tyN with (1:=H).
apply in_int_not_kind in tyN.
2:discriminate.
destruct tyord_inv with (2:=ty_O)(3:=H); trivial.
simpl in tyN.
apply TI_elim in tyN; auto.
destruct tyN as (o,oly,nty).
assert (oo: isOrd o) by eauto using isOrd_inv.
rewrite <- TI_mono_succ in nty; auto with *.
rewrite <- fix_irr with (1:=H)(o:=osucc o); auto with *.
2:apply olts_le.
2:apply lt_osucc_compat; auto.
rewrite fix_eqn with (1:=H); auto with *.
eapply fix_body_irrel with (1:=H); auto with *.
 apply fix_typ with (1:=H); trivial.
 red; intros; apply isOrd_trans with o; trivial.

 simpl.
 apply fix_typ with (1:=H); auto with *.

 red; simpl; intros.
 apply fix_irr with (1:=H); auto with *.
 reflexivity.
Qed.


Lemma wfix_extend :
  var_mono E O ->
  var_ext E (WI A B O) (WFix O M).
intro subO.
do 2 red; intros.
assert (isval := proj1 H).
assert (isval' := proj1 (proj2 H)).
assert (oo: isOrd (int O i)).
 destruct tyord_inv with (2:=ty_O) (3:=isval); trivial.
assert (oo': isOrd (int O i')).
 destruct tyord_inv with (2:=ty_O) (3:=isval'); trivial.
assert (inclo: int O i ⊆ int O i').
 apply subO in H; trivial.
clear subO.
change (cc_app (WREC (F i) (int O i)) x == cc_app (WREC (F i') (int O i')) x).
revert x H0.
change (int (WI A B O) i) with (Wi i (int O i)).
elim oo using isOrd_ind; intros.
simpl in H3; apply TI_elim in H3; auto.
destruct H3 as (o',?,?).
assert (o_o' : isOrd o') by eauto using isOrd_inv.
assert (o'_y : osucc o' ⊆ y).
 red; intros; apply le_lt_trans with o'; auto.
rewrite <- TI_mono_succ in H4; auto.
rewrite <- fix_irr with (1:=isval) (o:=osucc o'); auto.
rewrite fix_eqn with (1:=isval); auto.
 assert (TIeq: forall o', isOrd o' -> TI (WF' A B i) o' == TI (WF' A B i') o').
  intros; apply TI_morph_gen; auto with *.
  red; intros.
  apply W_F_ext; trivial.
   apply (Aeq _ _ H).

   red; intros.
   eapply Beq.
   apply val_push_var with (1:=H); trivial.
    rewrite (Aeq _ _ H) in H7.
    rewrite H8 in H7; trivial.

assert (x ∈ TI (WF' A B i') (osucc o')).
 rewrite <- TIeq; auto.
rewrite <- fix_irr with (1:=isval') (o:=osucc o'); auto with *.
2:red; intros; apply le_lt_trans with o' ;auto.
2:apply inclo; apply H1; trivial.
rewrite fix_eqn with (1:=isval'); auto.
assert (irr := stab).
do 2 red in irr.
eapply irr.
2:rewrite El_int_W_lift; trivial.
apply val_mono_1 with (1:=H); auto with *.
do 2 red; intros.
rewrite H2; trivial.
symmetry; apply fix_irr with (1:=proj1(proj2 H)); auto with *.
revert H6; apply eq_elim.
apply TIeq; trivial.
Qed.


Lemma wfix_equals :
  var_equals E O ->
  var_equals E (WFix O M).
red; intros.
assert (fxs: var_mono E O).
 apply var_eq_sub; trivial.
apply wfix_extend in fxs.
red in fxs.
specialize fxs with (1:=H0).
apply fcompat_typ_eq with (3:=fxs).
 eapply cc_prod_is_cc_fun.
 assert (h := typ_wfix _ (proj1 H0)).
 apply in_int_not_kind in h.
 2:discriminate.
 exact h.

 setoid_replace (int (WI A B O) i) with (int (WI A B O) i').
  eapply cc_prod_is_cc_fun.
  assert (h := typ_wfix _ (proj1 (proj2 H0))).
  apply in_int_not_kind in h.
  2:discriminate.
  exact h.
 do 2 red.
 assert (h:= H _ _ H0).
 apply TI_morph_gen; auto with *.
 red; intros.
 apply W_F_ext; trivial.
  apply (Aeq _ _ H0).

  red; intros.
  apply Beq.
  apply val_push_var with (1:=H0); trivial.
   rewrite H3 in H2.
   rewrite <- (Aeq _ _ H0); trivial.
Qed.

End WFixRules.

Print Assumptions typ_wfix.


Lemma typ_wfix' : forall infty e A B O U M T,
       T <> kind ->
       isOrd infty ->
       A <> kind ->
       typ e O (Ordt infty) ->
       typ (Prod (WIL A B 1 (Ref 0)) U :: OSucc O :: e) M
         (Prod (WIL A B 2 (OSucc (Ref 1)))
         (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U)))) ->
       var_ext (push_fun (push_ord (tinj e) (OSucc O)) (WIL A B 1 (Ref 0)) U)
         (WIL A B 2 (OSucc (Ref 1))) M ->
       var_mono (push_var (push_ord (tinj e) (OSucc O)) (WIL A B 1 (OSucc (Ref 0)))) U ->
       sub_typ e (Prod (WI A B O) (subst_rec O 1 U)) T ->
       typ e (WFix O M) T.
intros.
apply typ_subsumption with (Prod (WI A B O) (subst_rec O 1 U)); auto.
2:discriminate.
change e with (tenv (tinj e)).
apply typ_wfix with (infty:=infty); trivial.
Qed.

Lemma typ_wfix'' : forall infty e A B O U M T,
       isOrd infty ->
       T <> kind ->
       sub_typ (tenv e) (Prod (WI A B O) (subst_rec O 1 U)) T ->
       typ (tenv e) O (Ordt infty) ->
       typ_mono (push_var (push_ord e (OSucc O)) (WI (lift 1 A) (lift_rec 1 1 B) (OSucc (Ref 0)))) U kind ->
       typ_ext (push_fun (push_ord e (OSucc O)) (WI (lift 1 A) (lift_rec 1 1 B) (Ref 0)) U)
         M (WI (lift 2 A) (lift_rec 2 1 B) (OSucc (Ref 1)))
           (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
       typ (tenv e) (WFix O M) T.
intros.
destruct H3; destruct H4.
apply typ_subsumption with (2:=H1); trivial.
2:discriminate.
apply typ_wfix with infty; trivial.
Qed.

  Lemma typ_ext_fix : forall eps e A B O U M,
    isOrd eps ->
    A <> kind ->
    typ_equals e A kind ->
    typ_equals (push_var e A) B kind ->
    typ_mono e O (Ordt eps) ->
    typ_ext (push_fun (push_ord e (OSucc O)) (WI (lift 1 A) (lift_rec 1 1 B) (Ref 0)) U) M
      (WI (lift 2 A) (lift_rec 2 1 B) (OSucc (Ref 1)))
      (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    var_mono (push_var (push_ord e (OSucc O)) (WI (lift 1 A) (lift_rec 1 1 B) (OSucc (Ref 0)))) U ->
    typ_ext e (WFix O M) (WI A B O) (subst_rec O 1 U).
intros eps e A B O U M eps_ord Ank tyA tyB tyO tyM tyU.
destruct tyO as (inclO,tyO).
destruct tyM as (extM,tyM).
assert (tyF: typ (tenv e) (WFix O M) (Prod (WI A B O) (subst_rec O 1 U))).
 apply typ_wfix with eps; trivial.
split; trivial.
destruct tyB as (eqB,_).
destruct tyA as (eqA,tyA).
apply wfix_extend with eps U; trivial.
Qed.

  Lemma typ_equals_fix : forall eps e A B O U M,
    isOrd eps ->
    A <> kind ->
    typ_equals e A kind ->
    typ_equals (push_var e A) B kind ->
    typ_equals e O (Ordt eps) ->
    typ_ext (push_fun (push_ord e (OSucc O)) (WI (lift 1 A) (lift_rec 1 1 B) (Ref 0)) U) M
      (WI (lift 2 A) (lift_rec 2 1 B) (OSucc (Ref 1)))
      (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    var_mono (push_var (push_ord e (OSucc O)) (WI (lift 1 A) (lift_rec 1 1 B) (OSucc (Ref 0)))) U ->
    typ_equals e (WFix O M) (Prod (WI A B O) (subst_rec O 1 U)).
intros eps e A B O U M eps_ord Ank (eqA,tyA) (eqB,_) (inclO,tyO) (extM,tyM) tyU.
assert (tyF: typ (tenv e) (WFix O M) (Prod (WI A B O) (subst_rec O 1 U))).
 apply typ_wfix with eps; trivial.
split; trivial.
apply wfix_equals with eps A B U; trivial.
Qed.

(** * W-types and universes. *)

Lemma typ_WI_type n eps e A B O :
  isOrd eps ->
  A <> kind ->
  typ e O (Ordt eps) ->
  typ e A (type n) ->
  typ (A::e) B (type n) ->
  typ e (WI A B O) (type n).
red; intros epso Ank tyO tyA tyB i is_val.
red.
destruct tyord_inv with (2:=tyO)(3:=is_val) as (oo,_); trivial.
clear tyO.
red in tyA; specialize tyA with (1:=is_val).
apply in_int_not_kind in tyA.
2:discriminate.
assert (G_B : forall a, a ∈ int A i -> int B (V.cons a i) ∈ ZFecc.ecc (S n)).
 intros.
 assert (val_ok (A::e) (V.cons a i)).
  apply vcons_add_var; trivial.
 apply tyB in H0.
 apply in_int_not_kind in H0.
 2:discriminate.
 trivial.
apply G_incl with (TI (WF' A B i) (W_ord (int A i) (fun x => int B (V.cons x i)))); trivial.
 apply (ZFecc.ecc_grot (S n)).

 apply G_TI; trivial.
  apply (ZFecc.ecc_grot (S n)).

  apply WF'_morph; auto with *.

  unfold W_ord.
  apply Ffix_o_o; auto with *.
   apply Wf_mono.
   apply Bw_morph; reflexivity.

   red; intros.
   revert H0; apply Wf_typ; trivial.
   apply Bw_morph; reflexivity.

  apply G_W_ord; auto.
   apply Bw_morph; reflexivity.

   apply (ZFecc.ecc_grot (S n)).

   change (omega ∈ ZFecc.ecc (S n)); auto.

  intros.
  apply G_W_F; auto.
   apply Bw_morph; reflexivity.

   apply (ZFecc.ecc_grot (S n)).

 apply W_post; trivial.
 apply Bw_morph; reflexivity.
Qed.
