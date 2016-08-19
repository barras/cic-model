
(** A theory about realizability of natural numbers.
    It is similar to SATnat, but it supports type-based termination
 *)

Require Import ZF ZFpairs ZFsum ZFord ZFfix ZFcoc ZFind_natbot Sat SATtypes.
Require Import ZFlambda.
Require Import Lambda.
Module Lc:=Lambda.

Set Implicit Arguments.

(** NAT *)

Definition fNAT (A:set->SAT) : set->SAT :=
  sumReal (fun _ => unitSAT) (fun a => condSAT (~ a == empty) (A a)).

Lemma fNAT_morph :
   Proper ((eq_set ==> eqSAT) ==> eq_set ==> eqSAT) fNAT.
do 3 red; intros.
unfold fNAT.
unfold sumReal.
apply interSAT_morph.
apply indexed_relation_id.
intros.
apply prodSAT_morph.
 apply piSAT0_morph; intros; auto with *.
 red; intros; rewrite H0; reflexivity.

 apply prodSAT_morph; auto with *.
 apply piSAT0_morph; intros; auto with *.
  red; intros; rewrite H0; reflexivity.

  apply condSAT_morph; auto with *.
Qed.
Hint Resolve fNAT_morph.

Lemma fNAT_irrel (R R' : set -> SAT) (o : set) :
 isOrd o ->
 (forall x x' : set, x ∈ TI NATf' o -> x == x' -> eqSAT (R x) (R' x')) ->
 forall x x' : set,
 x ∈ TI NATf' (osucc o) -> x == x' -> eqSAT (fNAT R x) (fNAT R' x').
intros.
unfold fNAT.
unfold sumReal.
apply interSAT_morph.
apply indexed_relation_id; intros S.
apply prodSAT_morph.
 apply piSAT0_morph; intros; auto with *.
 red; intros.
 rewrite H2; reflexivity.

 apply prodSAT_morph; auto with *.
 apply piSAT0_morph; intros; auto with *.
  red; intros.
  rewrite H2; reflexivity.

  apply condSAT_morph_gen; intros; auto with *.
  apply H0; auto with *.
  rewrite TI_mono_succ in H1; auto with *.
  rewrite H3 in H1.
  apply SUCC_inv_typ_gen in H1.
  apply cc_bot_ax in H1; destruct H1; trivial.
  contradiction.
Qed.

Definition ZE := INL ID.

Lemma Real_ZERO_gen A :
  inSAT ZE (fNAT A ZERO).
apply Real_inl.
 do 2 red; reflexivity.

 apply ID_intro.
Qed.

Definition SU := INR.

Lemma Real_SUCC_gen A n t :
  Proper (eq_set==>eqSAT) A ->
  ~ n == empty ->
  inSAT t (A n) ->
  inSAT (SU t) (fNAT A (SUCC n)).
intros.
unfold fNAT.
apply Real_inr.
 do 2 red; intros; apply condSAT_morph; auto.
 rewrite H2; reflexivity.

 rewrite condSAT_ok; auto.
Qed.

Definition NCASE f g n := Lc.App2 n (Lc.Abs (Lc.lift 1 f)) g.

Lemma ZE_iota t1 t2 :
  Lc.redp (NCASE t1 t2 ZE) t1.
unfold NCASE, ZE.
eapply t_trans.
 apply INL_iota.
apply t_step; apply Lc.red1_beta.
unfold Lc.subst; rewrite Lc.simpl_subst; trivial.
rewrite Lc.lift0; trivial.
Qed.

Lemma SU_iota n t1 t2 :
  Lc.redp (NCASE t1 t2 (SU n)) (Lc.App t2 n).
unfold NCASE, SU.
apply INR_iota.
Qed.


Lemma Real_NATCASE_gen X A C n nt ft gt:
  Proper (eq_set ==> eqSAT) C ->
  n ∈ NATf X ->
  inSAT nt (fNAT A n) ->
  inSAT ft (C ZERO) ->
  inSAT gt (piSAT0 (fun x => x ∈ X) (fun a => condSAT (~a==empty) (A a))
                (fun x => C (SUCC x))) ->
  inSAT (NCASE ft gt nt) (C n).
intros Cm nty nreal freal greal.
apply Real_sum_case with ZFind_basic.UNIT X n
    (fun _ => unitSAT) (fun a => condSAT (~a==empty) (A a)); trivial.
 apply piSAT0_intro.
  apply Lc.sn_abs.
  apply Lc.sn_lift.
  apply sat_sn in freal; trivial.

  intros x u eqn ureal.
  rewrite eqn in nty; apply sum_inv_l in nty.
  apply ZFind_basic.unit_elim in nty.
  rewrite nty in eqn.
  apply inSAT_exp; [right; apply sat_sn in ureal;trivial|].
  unfold Lc.subst; rewrite Lc.simpl_subst; auto.
  rewrite Lc.lift0; trivial.
  rewrite eqn; trivial.

 apply piSAT0_intro.
  apply sat_sn in greal; trivial.

  intros.
  rewrite H in nty; apply sum_inv_r in nty.
  rewrite H.
  apply piSAT0_elim with (1:=greal); trivial.
Qed.


Definition fNATi o := tiSAT NATf' fNAT o.

Instance fNATi_morph :
  Proper (eq_set ==> eq_set ==> eqSAT) fNATi.
apply tiSAT_morph; auto.
Qed.

Hint Resolve NATf'_mono.

Lemma fNATi_mono o1 o2:
  isOrd o1 ->
  isOrd o2 ->
  o1 ⊆ o2 ->
  forall x,
  x ∈ TI NATf' o1 ->
  eqSAT (fNATi o1 x) (fNATi o2 x).
intros.
apply tiSAT_mono; trivial.
intros; apply fNAT_irrel with (o:=o'); trivial.
Qed.

Lemma fNATi_succ_eq o x :
  isOrd o ->
  x ∈ TI NATf' (osucc o) ->
  eqSAT (fNATi (osucc o) x) (fNAT (fNATi o) x).
intros.
apply tiSAT_succ_eq; auto.
intros; apply fNAT_irrel with (o:=o'); trivial.
Qed.

Lemma fNATi_neutral o S :
  isOrd o ->
  inclSAT (fNATi o empty) S.
intros.
apply tiSAT_outside_domain; auto with *.
 intros; apply fNAT_irrel with (o:=o'); trivial.

 intro.
 apply mt_not_in_NATf' in H0; auto with *.
Qed.

Lemma fNATi_mt : forall o,
  isOrd o ->
  eqSAT (fNATi o empty) (interSAT(fun S=>S)).
intros.
red; split.
 apply fNATi_neutral; trivial.

 intros h; apply interSAT_elim with (1:=h).
Qed.

Lemma Real_ZERO o :
  isOrd o ->
  inSAT ZE (fNATi (osucc o) ZERO).
intros.
rewrite fNATi_succ_eq; trivial.
 apply Real_ZERO_gen.

 apply TI_intro with o; auto.
 apply ZERO_typ_gen.
Qed.


(*
Lemma Real_SUCC o n t :
  isOrd o ->
  n ∈ cc_bot (TI NATf' o) ->
  inSAT t (fNATi o n) ->
  inSAT (SU t) (fNATi (osucc o) (SUCC n)).
intros.
rewrite fNATi_succ_eq; trivial.
 unfold SU, fNAT.
 apply Real_inr; trivial.
admit.
(*  apply fNATi_morph; reflexivity.*)

  apply cc_bot_ax in H0; destruct H0.
   rewrite H0 in H1; revert H1.
   apply fNATi_neutral; trivial.

   rewrite condSAT_ok; trivial.
   apply mt_not_in_NATf' in H0; auto.

 apply TI_intro with o; auto.
 apply SUCC_typ_gen; trivial.
Qed.
*)

Lemma Real_NATCASE o C n nt ft gt:
  isOrd o ->
  Proper (eq_set ==> eqSAT) C ->
  n ∈ TI NATf' (osucc o) ->
  inSAT nt (fNATi (osucc o) n) ->
  inSAT ft (C ZERO) ->
  inSAT gt (piSAT0 (fun x => x ∈ cc_bot (TI NATf' o)) (fNATi o) (fun x => C (SUCC x))) ->
  inSAT (NCASE ft gt nt) (C n).
intros oo Cm nty nreal freal greal.
rewrite fNATi_succ_eq in nreal; trivial.
unfold NATi in nty; rewrite TI_mono_succ in nty; auto.
apply Real_NATCASE_gen with (2:=nty) (3:=nreal); auto.
revert gt greal.
apply piSAT0_mono with (fun x => x); auto with *.
intros x xty.
apply condSAT_smaller.
Qed.


(** Introducing the fixpoint of fNATi *)

Definition cNAT := fNATi omega.

Instance cNAT_morph : Proper (eq_set ==> eqSAT) cNAT.
do 2 red; intros.
apply fNATi_morph; auto with *.
Qed.

Lemma cNAT_eq x :
  x ∈ NAT' ->
  eqSAT (cNAT x) (fNAT cNAT x).
intros.
apply tiSAT_eq; auto with *.
intros; apply fNAT_irrel with (o:=o'); trivial.
Qed.

Lemma fNATi_stages : forall o x,
       isOrd o ->
       x ∈ cc_bot (TI NATf' o) -> eqSAT (fNATi o x) (cNAT x).
intros.
apply cc_bot_ax in H0.
destruct H0.
 rewrite H0.
 transitivity (interSAT(fun S=>S)).
  apply fNATi_mt; trivial.
  symmetry; apply fNATi_mt; trivial.

 transitivity (fNATi (osup2 o omega) x).
  apply fNATi_mono; auto with *.
   apply isOrd_osup2; auto.

   apply osup2_incl1; auto.

  symmetry; apply fNATi_mono; auto with *.
   apply isOrd_osup2; auto.

   apply osup2_incl2; auto.

   revert H0; apply NATf'_stages; trivial.
Qed.

Lemma Real_SUCC_cNAT n t :
  n ∈ cc_bot NAT' ->
  inSAT t (cNAT n) ->
  inSAT (SU t) (cNAT (SUCC n)).
intros.
rewrite cNAT_eq.
 unfold fNAT.
 apply Real_inr; auto with *.
  do 2 red; intros; apply condSAT_morph; auto with *.
  rewrite H1; reflexivity.
  apply cNAT_morph; trivial.

  apply cc_bot_ax in H; destruct H.  
   rewrite H in H0.
   revert H0; apply fNATi_neutral; auto.

   rewrite condSAT_ok; trivial.
   apply mt_not_in_NATf' in H; auto.

 apply SUCC_typ'; trivial.
Qed.

(** * Structural fixpoint: *)

(** NATFIX m n --> m (NATFIX m) n when n is a (sum) constructor.
   let G m := "\n. (match n with inl _ => m | inr _ => m end) m n"
   let G m := \n. n (\_.m) (\_.m) m n
    G m -/-> ; G m (inl a) --> m m (inl a); G m (inr b) --> m m (inr b)
   NATFIX m n := G (\x. m (G x)) n
     --> (\x. m (G x)) (\x. m (G x)) n
     --> m (G (\x. m (G x))) n == m (NATFIX m) n
 *)
(*
Definition guard_sum m :=
  Lc.Abs (Lc.App2 (Lc.App2 (Lc.Ref 0) (Lc.Abs (Lc.lift 2 m)) (Lc.Abs (Lc.lift 2 m))) (Lc.lift 1 m) (Lc.Ref 0)).

(** (G m n) reduces to (m m n) when n is a constructor. Note that
    n need not be closed. *)
Lemma G_sim : forall m n,
  (exists t c, (c=0\/c=1) /\ n = Lc.Abs (Lc.Abs (Lc.App (Lc.Ref c) t))) ->
  Lc.redp (Lc.App (guard_sum m) n) (Lc.App2 m m n).
intros m n (t,(c,(eqc,eqn))).
unfold guard_sum.
eapply t_trans.
 apply t_step.
 apply Lc.beta.
unfold Lc.subst; simpl.
repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
apply Lc.redp_app_l.
apply Lc.redp_app_l.
rewrite eqn.
eapply t_trans.
 apply t_step.
 apply Lc.app_red_l.
 apply Lc.beta.
destruct eqc; subst c.
 unfold Lc.subst; simpl.
 eapply t_trans.
  apply t_step.
  apply Lc.beta.
 unfold Lc.subst; simpl.
 rewrite Lc.lift0.
 apply t_step.
 apply Lc.red1_beta.
 unfold Lc.subst; rewrite Lc.simpl_subst; auto.
 rewrite Lc.lift0; trivial.

 unfold Lc.subst; simpl.
 eapply t_trans.
  apply t_step.
  apply Lc.beta.
 unfold Lc.subst; simpl; rewrite Lc.simpl_subst_rec; auto.
 rewrite Lc.lift_rec0.
 apply t_step.
 apply Lc.red1_beta.
 unfold Lc.subst; rewrite Lc.simpl_subst; auto.
 rewrite Lc.lift0; trivial.
Qed.

Lemma G_INL m a :
  Lc.redp (Lc.App (guard_sum m) (INL a)) (Lc.App2 m m (INL a)).
apply G_sim.
econstructor; exists 1; split; auto.
reflexivity.
Qed.
Lemma G_INR m a :
  Lc.redp (Lc.App (guard_sum m) (INR a)) (Lc.App2 m m (INR a)).
apply G_sim.
econstructor; exists 0; split; auto.
reflexivity.
Qed.
*)
(*
Lemma G_sn m :
  sn m -> sn (App guard_sum m).
unfold guard_sum; intros.
apply sat_sn with snSAT.

apply sn_abs.
apply sat_sn with snSAT.
apply prodSAT_elim with snSAT;[|apply varSAT].
apply prodSAT_elim with snSAT;[|apply snSAT_intro;apply sn_lift;trivial].
apply prodSAT_elim with snSAT;[|apply snSAT_intro;apply sn_abs;apply sn_lift;trivial].
apply prodSAT_elim with snSAT;[|apply snSAT_intro;apply sn_abs;apply sn_lift;trivial].
apply varSAT.
Qed.
*)

(*
Lemma G_sat_gen A k m t X :
  k ∈ NAT ->
  inSAT t (fNAT A k) ->
  inSAT (Lc.App2 m m t) X ->
  inSAT (Lc.App2 guard_sum m t) X.
intros.
unfold guard_sum.
apply GUARD_sat.
revert H1; apply inSAT_context.
apply inSAT_context.
intros.
rewrite NAT_eq in H.
apply WHEN_SUM_sat with (1:=H) (2:=H0); trivial.
Qed.
*)

(*
Lemma sn_G_inv m : Lc.sn (guard_sum m) -> Lc.sn m.
intros.
unfold guard_sum in H.
eapply subterm_sn in H;[|constructor].
eapply subterm_sn in H;[|apply sbtrm_app_l].
eapply subterm_sn in H;[|apply sbtrm_app_r].
apply sn_lift_inv with (1:=H) (2:=eq_refl).
Qed.
*)

(**)
(*
Lemma G_sat o x t m (X:SAT):
  isOrd o ->
  x ∈ NATi o ->
  inSAT t (fNATi o x) ->
  inSAT (Lc.App2 m m t) X ->
  inSAT (Lc.App2 guard_sum m t) X.
intros.
assert (x ∈ NAT).
 apply NATi_NAT in H0; trivial.
apply TI_elim in H0; auto.
destruct H0 as (o',?,?).
assert (isOrd o') by eauto using isOrd_inv.
assert (osucc o' ⊆ o).
 red; intros.
 apply isOrd_plump with o'; trivial.
  eauto using isOrd_inv.
  apply olts_le; trivial.
rewrite <- TI_mono_succ in H4; auto.
rewrite <- fNATi_mono with (o1:=osucc o') in H1; auto.
rewrite fNATi_succ_eq in H1; auto.
apply G_sat_gen with (2:=H1); trivial.
Qed.
*)

(* specialized fix *)

Definition NATFIX := FIXP WHEN_SUM.

Lemma ZE_iotafix m :
  Lc.redp (Lc.App (NATFIX m) ZE) (Lc.App2 m (NATFIX m) ZE).
apply FIXP_sim.
intros.
apply WHEN_SUM_INL.
Qed.
Lemma SU_iotafix m n :
  Lc.redp (Lc.App (NATFIX m) (SU n)) (Lc.App2 m (NATFIX m) (SU n)).
apply FIXP_sim.
intros.
apply WHEN_SUM_INR.
Qed.

Lemma NATFIX_sat : forall o m X,
  let FIX_ty o := piSAT0 (fun n => n ∈ cc_bot (TI NATf' o)) (fNATi o) (X o) in
  let FIX_ty' o := piSAT0 (fun n => n ∈ TI NATf' o) (fNATi o) (X o) in
  isOrd o ->
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ TI NATf' y ->
   inclSAT (X y n) (X y' n)) ->
  inSAT m (piSAT0 (fun o' => o' ∈ osucc o)
             (fun o1 => FIX_ty o1) (fun o1 => FIX_ty' (osucc o1))) ->
  inSAT (NATFIX m) (FIX_ty o).
intros o m X FIX_ty FIX_ty' oo Xmono msat.
apply FIXP_sat0
   with (T:=TI NATf') (U:=fun o => cc_bot (TI NATf' o)) (RT:=fNATi); trivial.
 intros.
 rewrite cc_bot_ax in H1; destruct H1.
  left; red; intros.
  rewrite H1 in H2.
  revert H2; apply fNATi_neutral; trivial.

  right.
  apply TI_elim in H1; auto with *.
  destruct H1 as (z,zty,xty).
  exists z; trivial.
  rewrite TI_mono_succ; auto with *.
  apply isOrd_inv with y; trivial.

 exists empty; trivial.

 intros.
 apply fNATi_mono; trivial.

 intros.
 apply WHEN_SUM_neutral; trivial.

 intros.
 apply TI_elim in H0; auto with *.
 destruct H0 as (z,zty,xty).
 assert (oz: isOrd z).
  apply isOrd_inv with o0; auto.
 assert (xty' := xty).
 rewrite <-TI_mono_succ in xty'; auto.
 rewrite <- fNATi_mono with (o1:=osucc z) in H1; auto.
  rewrite fNATi_succ_eq in H1; auto.
  apply WHEN_SUM_sat with (1:=xty) (2:=H1); trivial.

  red; intros.
  apply le_lt_trans with z; trivial.
Qed.
