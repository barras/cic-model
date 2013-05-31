
Require Import ZF ZFpairs ZFsum ZFrelations ZFord ZFfix ZFind_w Sat SATtypes.
Require Import ZFlambda.
Require Import Lambda.
Module Lc:=Lambda.

Set Implicit Arguments.

(** W-types *)

Section Wtypes.

Variable A : set.
Variable B : set -> set.
Hypothesis B_morph : morph1 B.
Let Bext : ext_fun A B.
auto with *.
Qed.

Let Wf := W_F A B.

Variable RA : set -> SAT.
Variable RB : set -> set -> SAT.
Hypothesis RA_morph : Proper (eq_set ==> eqSAT) RA.
Hypothesis RB_morph : Proper (eq_set ==> eq_set ==> eqSAT) RB.

Definition rW (X:set->SAT) : set->SAT :=
  sigmaReal RA (fun x f => piSAT0 (fun i => i ∈ B x) (RB x) (fun i => X (cc_app f i))).

Lemma rW_morph :
   Proper ((eq_set ==> eqSAT) ==> eq_set ==> eqSAT) rW.
do 3 red; intros.
unfold rW.
unfold sigmaReal.
apply interSAT_morph.
apply indexed_relation_id; intros S.
apply prodSAT_morph; auto with *.
apply prodSAT_morph.
 apply RA_morph; apply fst_morph; trivial.

 apply prodSAT_morph; auto with *.
 apply piSAT0_morph; intros.
  red; intros.
  rewrite H0; reflexivity.

  apply RB_morph; auto with *.
  apply fst_morph; auto.

  apply H.
  rewrite H0; reflexivity.
Qed.
Hint Resolve rW_morph.

Lemma rW_irrel (R R' : set -> SAT) (o : set) :
 isOrd o ->
 (forall x x' : set, x ∈ TI Wf o -> x == x' -> eqSAT (R x) (R' x')) ->
 forall x x' : set,
 x ∈ TI Wf (osucc o) -> x == x' -> eqSAT (rW R x) (rW R' x').
intros.
unfold rW.
unfold sigmaReal.
apply interSAT_morph.
apply indexed_relation_id; intros S.
apply prodSAT_morph; auto with *.
apply prodSAT_morph.
 apply RA_morph; apply fst_morph; trivial.

 apply prodSAT_morph; auto with *.
 apply piSAT0_morph; intros.
  red; intros.
  rewrite H2; reflexivity.

  apply RB_morph; auto with *.
  apply fst_morph; auto.

  apply H0.
   rewrite TI_mono_succ in H1; auto.
   2:apply W_F_mono; trivial.
   unfold Wf in H1.
   apply W_F_elim in H1; trivial.
   destruct H1 as (_,(?,_)); auto.

   rewrite H2; reflexivity.
Qed.

Definition WC x f := COUPLE x f.

Parameter sigmaReal_morph : forall X Y,
  Proper (eq_set ==> eqSAT) X ->
  Proper (eq_set ==> eq_set ==> eqSAT) Y ->
  Proper (eq_set ==> eqSAT) (sigmaReal X Y).
Existing Instance sigmaReal_morph.

Lemma Real_WC_gen X RX a b x f :
  Proper (eq_set==>eqSAT) RX ->
  couple a b ∈ Wf X ->
  inSAT x (RA a) ->
  inSAT f (piSAT0 (fun i => i ∈ B a) (RB a) (fun i => RX (cc_app b i))) ->
  inSAT (WC x f) (rW RX (couple a b)).
intros.
unfold rW, WC.
apply Real_couple; trivial.
do 3 red; intros.
apply piSAT0_morph; intros.
 red; intros.
 rewrite H3; reflexivity.

 apply RB_morph; auto with *.

 rewrite H4; reflexivity.
Qed.

Definition WCASE b n := Lc.App n b.

Lemma WC_iota b x f :
  Lc.redp (WCASE b (WC x f)) (Lc.App2 b x f).
unfold WCASE, WC.
apply COUPLE_iota.
Qed.


Lemma Real_WCASE_gen X RX C n nt bt:
  Proper (eq_set ==> eqSAT) C ->
  n ∈ Wf X ->
  inSAT nt (rW RX n) ->
  inSAT bt (piSAT0 (fun x => x ∈ A) RA (fun x =>
            piSAT0 (fun f => f ∈ cc_arr (B x) X)
                   (fun f => piSAT0 (fun i => i ∈ B x) (RB x) (fun i => RX (cc_app f i)))
                   (fun f => C (couple x f)))) ->
  inSAT (WCASE bt nt) (C n).
intros Cm nty xreal breal.
unfold Wf in nty.
apply Real_sigma_elim' with (3:=nty) (4:=xreal); trivial.
do 2 red; intros.
rewrite H0; reflexivity.
Qed.

Definition rWi o := tiSAT Wf rW o.

Instance rWi_morph :
  Proper (eq_set ==> eq_set ==> eqSAT) rWi.
apply tiSAT_morph; auto.
Qed.

Lemma rWi_mono o1 o2:
  isOrd o1 ->
  isOrd o2 ->
  o1 ⊆ o2 ->
  forall x,
  x ∈ TI Wf o1 ->
  eqSAT (rWi o1 x) (rWi o2 x).
intros.
apply tiSAT_mono; trivial.
 apply W_F_mono; trivial.

 intros; apply rW_irrel with (o:=o'); trivial.
Qed.

Lemma rWi_succ_eq o x :
  isOrd o ->
  x ∈ TI Wf (osucc o) ->
  eqSAT (rWi (osucc o) x) (rW (rWi o) x).
intros.
apply tiSAT_succ_eq; auto.
 apply W_F_mono; trivial.

 intros; apply rW_irrel with (o:=o'); trivial.
Qed.
(*
Lemma rWi_fix x :
  x ∈ W_F A B ->
  eqSAT (rWi W_omega x) (rW (rWi omega) x).
intros.
apply tiSAT_eq; auto with *.
 apply W_F_mono; trivial.

 
intros; apply rW_irrel with (o:=o'); trivial.
Qed.
*)

Lemma Real_WC o n x f :
  isOrd o ->
  n ∈ TI Wf (osucc o) ->
  inSAT x (RA (fst n)) ->
  inSAT f (piSAT0 (fun i => i ∈ B (fst n)) (RB (fst n)) (fun i => rWi o (cc_app (snd n) i))) ->
  inSAT (WC x f) (rWi (osucc o) n).
intros.
rewrite rWi_succ_eq; trivial.
rewrite TI_mono_succ in H0; trivial.
2:apply W_F_mono; trivial.
assert (nty := H0).
unfold Wf in H0; apply W_F_elim in H0; trivial.
destruct H0 as (?,(?,?)).
assert (eqSAT (rW (rWi o) n) (rW (rWi o) (couple (fst n) (cc_lam (B (fst n)) (cc_app (snd n)))))).
 apply rW_morph; trivial.
 apply rWi_morph; reflexivity.
rewrite H5; clear H5.
apply Real_WC_gen with (TI Wf o); trivial.
 apply rWi_morph; reflexivity.

 rewrite <- H4; trivial.

 revert H2; apply piSAT0_morph; intros.
  red; reflexivity.
  reflexivity.
  apply rWi_morph;[reflexivity|].
  apply cc_beta_eq; auto.
  do 2 red; intros; apply cc_app_morph; auto with *.
Qed.

Lemma Real_WCASE o C n nt bt:
  isOrd o ->
  Proper (eq_set ==> eqSAT) C ->
  n ∈ TI Wf (osucc o) ->
  inSAT nt (rWi (osucc o) n) ->
  inSAT bt (piSAT0 (fun x => x ∈ A) RA (fun x =>
            piSAT0 (fun f => f ∈ cc_arr (B x) (TI Wf o))
                   (fun f => piSAT0 (fun i => i ∈ B x) (RB x) (fun i => rWi o (cc_app f i)))
                   (fun f => C (couple x f)))) ->
  inSAT (WCASE bt nt) (C n).
intros oo Cm nty nreal breal.
rewrite rWi_succ_eq in nreal; trivial.
rewrite TI_mono_succ in nty; auto.
2:apply W_F_mono; trivial.
apply Real_WCASE_gen with (2:=nty) (3:=nreal); trivial.
Qed.

(** * Structural fixpoint: *)

Definition guard_couple :=
  Lc.Abs (Lc.Abs (Lc.App2 (Lc.App (Lc.Ref 0) (Lc.Abs (Lc.Abs (Lc.Ref 3)))) (Lc.Ref 1) (Lc.Ref 0))).

(** (G m n) reduces to (m m n) when n is a constructor. Note that
    n need not be closed. *)
Lemma G_sim : forall m n,
  (exists t1 t2, n = Lc.Abs (Lc.App2 (Lc.Ref 0) t1 t2)) ->
  Lc.redp (Lc.App2 guard_couple m n) (Lc.App2 m m n).
intros m n (t1,(t2,eqn)).
unfold guard_couple.
eapply t_trans.
 apply Lc.redp_app_l.
 apply t_step.
 apply Lc.beta.
unfold Lc.subst; simpl.
eapply t_trans.
 apply t_step.
 apply Lc.beta.
unfold Lc.subst; simpl.
repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
rewrite eqn.
eapply t_trans.
 apply Lc.redp_app_l.
 apply Lc.redp_app_l.
 apply t_step.
 apply Lc.beta.
apply Lc.redp_app_l.
apply Lc.redp_app_l.
unfold Lc.subst; simpl.
rewrite Lc.lift0.
eapply t_trans.
 apply Lc.redp_app_l.
 apply t_step.
 apply Lc.beta.
unfold Lc.subst; simpl.
repeat rewrite Lc.simpl_subst; auto.
apply t_step.
apply Lc.red1_beta.
unfold Lc.subst; simpl.
repeat rewrite Lc.simpl_subst; auto.
rewrite Lc.lift0; trivial.
Qed.

Lemma G_WC m x f :
  Lc.redp (Lc.App2 guard_couple m (WC x f)) (Lc.App2 m m (WC x f)).
apply G_sim.
do 2 econstructor; reflexivity.
Qed.

Lemma G_sn m :
  sn m -> sn (Lc.App guard_couple m).
unfold guard_couple; intros.
apply sat_sn with snSAT.
apply inSAT_exp; auto.
unfold Lc.subst; simpl.
apply sn_abs.
apply sat_sn with snSAT.
apply prodSAT_elim with snSAT;[|apply varSAT].
apply prodSAT_elim with snSAT;[|apply sn_lift;trivial].
apply prodSAT_elim with snSAT;[|do 2 apply sn_abs;apply sn_lift;trivial].
apply varSAT.
Qed.

Lemma G_sat o x t m (X:SAT):
  isOrd o ->
  x ∈ TI Wf o ->
  inSAT t (rWi o x) ->
  inSAT (Lc.App2 m m t) X ->
  inSAT (Lc.App2 guard_couple m t) X.
intros.
unfold guard_couple.
eapply inSAT_context.
 intros.
 apply inSAT_exp with (2:=H3).
 simpl; auto.
unfold Lc.subst; simpl Lc.subst_rec.
apply inSAT_exp; simpl; auto.
unfold Lc.subst; simpl Lc.subst_rec.
repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
revert X H2; apply inSAT_context; apply inSAT_context; intros.
apply TI_elim in H0; auto.
2:apply W_F_morph; trivial.
destruct H0 as (o',?,?).
assert (isOrd o') by eauto using isOrd_inv.
assert (osucc o' ⊆ o).
 red; intros.
 apply isOrd_plump with o'; trivial.
  eauto using isOrd_inv.
  apply olts_le; trivial.
rewrite <- TI_mono_succ in H3; auto.
2:apply W_F_mono; trivial.
rewrite <- rWi_mono with (o1:=osucc o') in H1; auto.
apply Real_WCASE with (o:=o')(n:=x)(C:=fun _=>S); auto.
 do 2 red; reflexivity.

 apply piSAT0_intro.
  do 2 apply sn_abs; apply sn_lift; apply sat_sn in H2; trivial.
 intros.
 apply inSAT_exp; [apply sat_sn in H7; auto|].
 unfold Lc.subst; simpl Lc.subst_rec.
 rewrite Lc.simpl_subst; auto.
 apply piSAT0_intro.
  apply sn_abs; apply sn_lift; apply sat_sn in H2; trivial.
 intros.
 apply inSAT_exp; [apply sat_sn in H9; auto|].
 unfold Lc.subst; simpl Lc.subst_rec.
 rewrite Lc.simpl_subst; auto.
 rewrite lift0; trivial.
Qed.


(* specialized fix *)

Definition WFIX := FIXP guard_couple.

Lemma WFIX_sim : forall m n,
  (exists t1 t2, n = Lc.Abs (Lc.App2 (Lc.Ref 0) t1 t2)) ->
  Lc.redp (Lc.App (WFIX m) n) (Lc.App2 m (WFIX m) n).
intros.
apply FIXP_sim.
intros.
apply G_sim; trivial.
Qed.

Lemma WC_iotafix m x f :
  Lc.redp (Lc.App (WFIX m) (WC x f)) (Lc.App2 m (WFIX m) (WC x f)).
apply WFIX_sim.
econstructor; econstructor; reflexivity.
Qed.

Lemma WFIX_sat : forall o m X,
  let FIX_ty o := piSAT0 (fun n => n ∈ TI Wf o) (rWi o) (X o) in
  isOrd o ->
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ TI Wf y ->
   inclSAT (X y n) (X y' n)) ->
  inSAT m (piSAT0 (fun o' => o' ∈ osucc o)
             (fun o1 => FIX_ty o1) (fun o1 => FIX_ty (osucc o1))) ->
  inSAT (WFIX m) (FIX_ty o).
intros.
apply FIXP_sat; trivial.
 exact G_sn.

 exact G_sat.

 intros.
 apply TI_elim in H4; auto.
 2:apply W_F_morph; trivial.
 destruct H4 as (o',?,?); exists o'; trivial.
 rewrite <- TI_mono_succ in H5; eauto using isOrd_inv.
 apply W_F_mono; trivial.

 intros.
 apply rWi_mono; trivial.
Qed.

End Wtypes.