
Require Import ZF ZFpairs ZFsum ZFrelations ZFord ZFfix ZFind_w Sat SATtypes.
Require Import ZFlambda.
Require Import Lambda.
Module Lc:=Lambda.
Require Import ZFcoc.

Set Implicit Arguments.

(** W-types *)

Section Wtypes.

Variable A : set.
Variable B : set -> set.
Hypothesis B_morph : morph1 B.
Let Bext : ext_fun A B.
auto with *.
Qed.

Let Wf X := W_F A B (cc_dec X).

Local Instance Wf_mono : Proper (incl_set ==> incl_set) Wf.
do 2 red; intros.
unfold Wf; apply W_F_mono; trivial.
apply union2_mono; auto with *.
Qed.


Lemma mt_not_in_W_F o x :
  isOrd o ->
  x ∈ TI Wf o ->
  ~ x == empty.
red; intros.
apply TI_elim in H0; auto with *.
destruct H0 as (o',?,?).
unfold Wf in H2.
apply W_F_elim in H2; trivial.
destruct H2 as (_,(_,?)).
rewrite H1 in H2.
apply discr_mt_pair in H2; trivial.
Qed.


Variable RA : set -> SAT.
Variable RB : set -> set -> SAT.
Hypothesis RA_morph : Proper (eq_set ==> eqSAT) RA.
Hypothesis RB_morph : Proper (eq_set ==> eq_set ==> eqSAT) RB.

Definition rW (X:set->SAT) : set->SAT :=
  sigmaReal RA (fun x f => piSAT0 (fun i => i ∈ B x) (RB x)
    (fun i => condSAT (~cc_app f i==empty) (X (cc_app f i)))).

Lemma rW_morph :
   Proper ((eq_set ==> eqSAT) ==> eq_set ==> eqSAT) rW.
do 3 red; intros.
unfold rW.
unfold sigmaReal.
apply interSAT_morph.
apply indexed_relation_id; intros S.
apply prodSAT_morph; auto with *.
apply piSAT0_morph; intros; auto with *.
 red; intros.
 rewrite H0; reflexivity.

 apply prodSAT_morph; auto with *.
 apply piSAT0_morph; intros; auto with *.
 apply condSAT_morph.
  rewrite H0; reflexivity.

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
apply piSAT0_morph; intros; auto with *.
 red; intros.
 rewrite H2; reflexivity.

 apply prodSAT_morph; auto with *.
 apply piSAT0_morph; intros; auto with *.
 apply condSAT_morph_gen.
  rewrite H2; reflexivity.

  intros.
  apply H0.
   rewrite TI_mono_succ in H1; auto with *.
   unfold Wf in H1.
   apply W_F_elim in H1; trivial.
   destruct H1 as (_,(?,_)); auto.
   apply fst_morph in H3; rewrite fst_def in H3.
   rewrite <- H3 in H5.
   specialize H1 with (1:=H5).
   apply union2_elim in H1; destruct H1; trivial.
   apply singl_elim in H1; contradiction.

   rewrite H2; reflexivity.
Qed.

Definition WC x f := COUPLE x f.

Lemma Real_WC_gen X RX a b x f :
  Proper (eq_set==>eqSAT) RX ->
  couple a b ∈ Wf X ->
  inSAT x (RA a) ->
  inSAT f (piSAT0 (fun i => i ∈ B a) (RB a)
            (fun i => condSAT (~cc_app b i==empty) (RX (cc_app b i)))) ->
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
            piSAT0 (fun f => f ∈ cc_arr (B x) (cc_dec X))
                   (fun f => piSAT0 (fun i => i ∈ B x) (RB x)
                      (fun i => condSAT (~cc_app f i==empty) (RX (cc_app f i))))
                   (fun f => C (couple x f)))) ->
  inSAT (WCASE bt nt) (C n).
intros Cm nty xreal breal.
unfold Wf in nty.
apply Real_sigma_elim with (3:=nty) (4:=xreal); trivial.
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
 apply Wf_mono; trivial.

 intros; apply rW_irrel with (o:=o'); trivial.
Qed.

Lemma rWi_succ_eq o x :
  isOrd o ->
  x ∈ TI Wf (osucc o) ->
  eqSAT (rWi (osucc o) x) (rW (rWi o) x).
intros.
apply tiSAT_succ_eq; auto.
 apply Wf_mono; trivial.

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

Lemma rWi_neutral o S :
  isOrd o ->
  inclSAT (rWi o empty) S.
intros.
apply tiSAT_outside_domain; auto with *.
 intros; apply rW_irrel with (o:=o'); trivial.

 intro.
 apply mt_not_in_W_F in H0; auto with *.
Qed.



Lemma Real_WC o n x f :
  isOrd o ->
  n ∈ TI Wf (osucc o) ->
  inSAT x (RA (fst n)) ->
  inSAT f (piSAT0 (fun i => i ∈ B (fst n)) (RB (fst n)) (fun i => rWi o (cc_app (snd n) i))) ->
  inSAT (WC x f) (rWi (osucc o) n).
intros.
rewrite rWi_succ_eq; trivial.
rewrite TI_mono_succ in H0; trivial.
2:apply Wf_mono; trivial.
assert (nty := H0).
unfold Wf in H0; apply W_F_elim in H0; trivial.
destruct H0 as (?,(?,?)).
rewrite (rW_morph (rWi_morph (reflexivity o)) H4).
apply Real_WC_gen with (TI Wf o); auto with *.
 apply rWi_morph; reflexivity.
 rewrite <- H4; trivial.

 apply piSAT0_intro; intros.
  apply sat_sn in H2; trivial.
 rewrite cc_beta_eq; auto with *.
 2:do 2 red; intros; apply cc_app_morph; auto with *.
 specialize H3 with (1:=H5).
 apply piSAT0_elim' in H2; red in H2.
 specialize H2 with (1:=H5) (2:=H6).
 apply union2_elim in H3; destruct H3.
  apply singl_elim in H3.
  rewrite H3 in H2.
  revert H2; apply rWi_neutral; trivial.

  rewrite condSAT_ok; trivial.
  apply mt_not_in_W_F in H3; trivial.
Qed.


Lemma Real_WCASE o C n nt bt:
  isOrd o ->
  Proper (eq_set ==> eqSAT) C ->
  n ∈ TI Wf (osucc o) ->
  inSAT nt (rWi (osucc o) n) ->
  inSAT bt (piSAT0 (fun x => x ∈ A) RA (fun x =>
            piSAT0 (fun f => f ∈ cc_arr (B x) (cc_dec (TI Wf o)))
                   (fun f => piSAT0 (fun i => i ∈ B x) (RB x) (fun i => rWi o (cc_app f i)))
                   (fun f => C (couple x f)))) ->
  inSAT (WCASE bt nt) (C n).
intros oo Cm nty nreal breal.
rewrite rWi_succ_eq in nreal; trivial.
rewrite TI_mono_succ in nty; auto with *.
apply Real_WCASE_gen with (2:=nty) (3:=nreal); trivial.
revert bt breal.
apply interSAT_mono.
intros (x,xty); simpl proj1_sig.
apply prodSAT_mono; auto with *.
apply interSAT_mono.
intros (f,fty); simpl proj1_sig.
apply prodSAT_mono; auto with *.
apply interSAT_mono.
intros (i,ity); simpl proj1_sig.
apply prodSAT_mono; auto with *.
apply condSAT_smaller.
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

Lemma G_sn' m S :
  sn m -> inSAT (Lc.App guard_couple m) (prodSAT (interSAT(fun S=>S)) S).
unfold guard_couple; intros.
apply inSAT_exp; auto.
unfold Lc.subst; simpl Lc.subst_rec.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
eapply prodSAT_elim;[|apply H0].
apply prodSAT_elim with snSAT;[|trivial].
apply prodSAT_elim with snSAT;[|do 2 apply sn_abs;apply sn_lift;trivial].
apply interSAT_elim with (1:=H0).
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

Lemma guard_couple_neutral u v S :
  inSAT u snSAT ->
  inSAT v (interSAT(fun S => S)) ->
  inSAT (Lc.App2 guard_couple u v) S.
intros.
eapply prodSAT_elim;[|apply H0].
eapply prodSAT_elim;[|apply H].
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
repeat rewrite simpl_subst; auto with arith.
repeat rewrite Lc.lift0.
eapply prodSAT_elim;[|apply H2].
eapply prodSAT_elim;[|apply H1].
eapply prodSAT_elim with snSAT.
 apply interSAT_elim with (1:=H2).

 do 2 apply sn_abs; apply sn_lift.
 apply sat_sn in H1; trivial.
Qed.


Lemma G_sat o x t m (X:SAT):
  isOrd o ->
  x ∈ cc_dec (TI Wf o) ->
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
apply union2_elim in H0; destruct H0.
 apply singl_elim in H0.
 rewrite H0 in H1.

 apply prodSAT_elim with snSAT.
  apply rWi_neutral with (2:=H1); trivial.

  do 2 apply sn_abs.
  apply Lc.sn_lift.
  apply sat_sn in H2; trivial.

 apply TI_elim in H0; auto with *.
 destruct H0 as (o',?,?).
 assert (isOrd o') by eauto using isOrd_inv.
 assert (osucc o' ⊆ o).
  red; intros.
  apply isOrd_plump with o'; trivial.
   eauto using isOrd_inv.
   apply olts_le; trivial.
 rewrite <- TI_mono_succ in H3; auto with *.
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
  let FIX_ty o := piSAT0 (fun n => n ∈ cc_dec (TI Wf o)) (rWi o) (X o) in
  isOrd o ->
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ cc_dec (TI Wf y) ->
   inclSAT (X y n) (X y' n)) ->
  inSAT m (piSAT0 (fun o' => o' ∈ osucc o)
             (fun o1 => FIX_ty o1) (fun o1 => FIX_ty (osucc o1))) ->
  inSAT (WFIX m) (FIX_ty o).
intros o m X FIX_ty oo Xmono msat.
elim oo using isOrd_ind; intros.
apply piSAT0_intro'.
2:exists empty; apply union2_intro1; apply singl_intro.
intros x u xty0 ureal.
apply union2_elim in xty0; destruct xty0.
 (* neutral case *)
 apply singl_elim in H2.
 rewrite H2 in ureal.
 unfold WFIX, FIXP.
 apply guard_couple_neutral.
 2:apply rWi_neutral with (2:=ureal); trivial.
 apply sat_sn with (prodSAT (interSAT(fun S=>S)) snSAT).
 apply prodSAT_intro; intros.
 unfold Lc.subst; simpl Lc.subst_rec.
 rewrite simpl_subst; auto with arith.
 repeat rewrite Lc.lift0.
 change (Lc.sn (App m (App guard_couple v))).
 apply piSAT0_elim' in msat; red in msat.
 apply msat with (x:=y).
  apply ole_lts; trivial.
 apply piSAT0_intro'; intros.
 2:exists empty; apply union2_intro1; apply singl_intro.
 apply union2_elim in H4; destruct H4.
  (* rec. call on neutral term *)
  apply singl_elim in H4.
  rewrite H4 in H5.
  apply guard_couple_neutral.
  2:apply rWi_neutral with y; trivial.
  apply sat_sn in H3; trivial.

  (* rec. call on regular value *)
  apply TI_elim in H4; auto with *.
  destruct H4 as (z,?,?).
  specialize H1 with (1:=H4).
  assert (zo : isOrd z).
   apply isOrd_inv with y; trivial.
  assert (osucc z ⊆ y).
   red; intros.
   apply isOrd_plump with z; trivial.
    eauto using isOrd_inv.
    apply olts_le; trivial.
  rewrite <- TI_mono_succ in H6; auto with *.
  assert (ureal' : inSAT u0 (rWi (osucc z) x0)).
   apply rWi_mono with (3:=H7); auto.
  apply G_sat with (osucc z) x0; auto.
   apply union2_intro2; trivial.

   eapply prodSAT_elim;[|apply H5].
   eapply prodSAT_elim;[|apply H3].
   apply interSAT_elim with (1:=H3).

 (* reducible case *)
 apply TI_elim in H2; auto with *.
 destruct H2 as (z,?,?).
 specialize H1 with (1:=H2).
 assert (zo : isOrd z).
  apply isOrd_inv with y; trivial.
 assert (osucc z ⊆ y).
  red; intros.
  apply isOrd_plump with z; trivial.
   eauto using isOrd_inv.
   apply olts_le; trivial.
 rewrite <- TI_mono_succ in H3; auto with *.
 assert (ureal' : inSAT u (rWi (osucc z) x)).
  apply rWi_mono with (3:=H4); auto.
 apply G_sat with (osucc z) x; auto.
  apply union2_intro2; trivial.

  eapply inSAT_context; intros.
   apply inSAT_exp.
    left; simpl.
    apply Bool.orb_true_r.

    unfold subst; simpl subst_rec.
    repeat rewrite simpl_subst; auto.
    repeat rewrite lift0.
    change (inSAT (App m (WFIX m)) S).
    eexact H5.
apply Xmono with (osucc z); auto.
 apply union2_intro2; auto.
assert (z ∈ osucc o).
 apply isOrd_trans with o; auto.
 apply H0; trivial.
apply piSAT0_elim' in msat; red in msat.
specialize msat with (1:=H5) (2:=H1).
apply piSAT0_elim' in msat; red in msat.
apply msat; trivial.
apply union2_intro2; trivial.
Qed.

End Wtypes.