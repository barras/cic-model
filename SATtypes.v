
Require Import ZF ZFpairs ZFsum Sat.
Require Import ZFlambda.
Require Import Lambda.

Set Implicit Arguments.

(** Unit type *)

Definition unitSAT :=
  interSAT (fun C => prodSAT C C).

Definition ID := Abs (Ref 0).

Lemma ID_intro : inSAT ID unitSAT.
apply interSAT_intro with (1:=snSAT).
intros.
apply prodSAT_intro; intros.
unfold subst; simpl subst_rec.
rewrite lift0.
trivial.
Qed.

(** Disjoint sum *)

Definition INL (t:term) :=
  Abs (Abs (App (Ref 1) (lift 2 t))).
Definition INR (t:term) :=
  Abs (Abs (App (Ref 0) (lift 2 t))).

Lemma INL_iota t1 t2 a :
  redp (App2 (INL a) t1 t2) (App t1 a).
unfold INL.
eapply t_trans;[apply redp_app_l;apply t_step;apply red1_beta; reflexivity|].
unfold subst; simpl.
rewrite simpl_subst; trivial.
apply t_step; apply red1_beta.
unfold subst; simpl.
repeat rewrite simpl_subst; trivial.
repeat rewrite lift0; trivial.
Qed.

Lemma INR_iota t1 t2 a :
  redp (App2 (INR a) t1 t2) (App t2 a).
unfold INR.
eapply t_trans;[apply redp_app_l;apply t_step;apply red1_beta; reflexivity|].
unfold subst; simpl.
rewrite simpl_subst; trivial.
apply t_step; apply red1_beta.
unfold subst; simpl.
rewrite simpl_subst; trivial.
repeat rewrite lift0; trivial.
Qed.

Definition WHEN_SUM :=
  Abs (App (App (Ref 0) (Abs (Abs (Ref 0)))) (Abs (Abs (Ref 0)))).

Definition WHEN_SUM_INL a u :
  redp (App2 WHEN_SUM (INL a) u) u.
unfold WHEN_SUM.
eapply t_trans.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
rewrite lift0.
eapply t_trans.
 apply redp_app_l.
 apply INL_iota.
eapply t_trans.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
apply t_step; apply red1_beta.
unfold subst; simpl.
rewrite lift0; reflexivity.
Qed.

Definition WHEN_SUM_INR a u :
  redp (App2 WHEN_SUM (INR a) u) u.
unfold WHEN_SUM.
eapply t_trans.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
rewrite lift0.
eapply t_trans.
 apply redp_app_l.
 apply INR_iota.
eapply t_trans.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
apply t_step; apply red1_beta.
unfold subst; simpl.
rewrite lift0; reflexivity.
Qed.

Lemma WHEN_SUM_neutral t S :
  inSAT t (interSAT(fun S => S)) ->
  inSAT (App WHEN_SUM t) S.
intros.
unfold WHEN_SUM.
apply inSAT_exp;[simpl;auto|].
unfold subst; simpl; rewrite lift0.
apply prodSAT_elim with snSAT.
2:apply snSAT_intro; auto.
apply prodSAT_elim with snSAT.
2:apply snSAT_intro; auto.
apply interSAT_elim with (1:=H).
Qed.

Definition sumReal (X Y:set->SAT) (a:set) : SAT :=
  interSAT (fun C =>
     prodSAT (piSAT0 (fun x => a==inl x) X (fun _ => C))
    (prodSAT (piSAT0 (fun x => a==inr x) Y (fun _ => C))
     C)).

Lemma Real_sum_case X Y a RX RY C t b1 b2 :
  a ∈ sum X Y ->
  inSAT t (sumReal RX RY a) ->
  inSAT b1 (piSAT0 (fun x => a==inl x) RX (fun _ => C)) ->
  inSAT b2 (piSAT0 (fun x => a==inr x) RY (fun _ => C)) ->
  inSAT (App2 t b1 b2) C.
intros.
apply interSAT_elim with (x:=C) in H0.
eapply prodSAT_elim;[apply prodSAT_elim with (1:=H0)|]; trivial.
Qed.


Lemma Real_inl RX RY x t :
  Proper (eq_set ==> eqSAT) RX ->
  inSAT t (RX x) ->
  inSAT (INL t) (sumReal RX RY (inl x)).
intros.
apply interSAT_intro; auto.
intros.
apply prodSAT_intro; intros.
unfold subst; simpl subst_rec.
unfold subst; rewrite simpl_subst; auto.
apply prodSAT_intro; intros.
unfold subst; simpl subst_rec.
unfold subst; repeat rewrite simpl_subst; auto.
repeat rewrite lift0.
apply piSAT0_elim with (x:=x) (u:=t) in H1; auto with *.
Qed.

Lemma Real_inr RX RY x t :
  Proper (eq_set ==> eqSAT) RY ->
  inSAT t (RY x) ->
  inSAT (INR t) (sumReal RX RY (inr x)).
intros.
apply interSAT_intro; auto.
intros.
apply prodSAT_intro; intros.
unfold subst; simpl subst_rec.
unfold subst; rewrite simpl_subst; auto.
apply prodSAT_intro; intros.
unfold subst; simpl subst_rec.
unfold subst; repeat rewrite simpl_subst; auto.
repeat rewrite lift0.
apply piSAT0_elim with (x:=x) (u:=t) in H2; auto with *.
Qed.


Lemma WHEN_SUM_sat A B RA RB S x t m :
  x ∈ sum A B ->
  inSAT t (sumReal RA RB x) ->
  inSAT m S ->
  inSAT (App2 WHEN_SUM t m) S.
intros xty xsat msat.
unfold WHEN_SUM.
eapply inSAT_context.
 intros.
 apply inSAT_exp;[simpl;auto|].
 unfold subst; simpl.
 rewrite lift0.
 exact H.
apply prodSAT_elim with S; trivial.
apply Real_sum_case with (1:=xty) (2:=xsat); auto.
 apply piSAT0_intro; intros; auto.
 apply inSAT_exp;[right; apply sat_sn in H0;trivial|].
 unfold subst; simpl.
 apply prodSAT_intro; intros.
 unfold subst; simpl; rewrite lift0.
 trivial.

 apply piSAT0_intro; intros; auto.
 apply inSAT_exp;[right; apply sat_sn in H0;trivial|].
 unfold subst; simpl.
 apply prodSAT_intro; intros.
 unfold subst; simpl; rewrite lift0.
 trivial.
Qed.

(*
Definition guard_sum m :=
  Abs (App2 (App2 (Ref 0) (Abs (lift 2 m)) (Abs (lift 2 m))) (lift 1 m) (Ref 0)).

(** (G m n) reduces to (m m n) when n is a constructor. Note that
    n need not be closed. *)
Lemma G_sim : forall m n,
  (exists t c, (c=0\/c=1) /\ n = Abs (Abs (App (Ref c) t))) ->
  redp (App (guard_sum m) n) (App2 m m n).
intros m n (t,(c,(eqc,eqn))).
unfold guard_sum.
eapply t_trans.
 apply t_step.
 apply beta.
unfold subst; simpl.
repeat rewrite simpl_subst; auto.
repeat rewrite lift0.
apply redp_app_l.
apply redp_app_l.
rewrite eqn.
eapply t_trans.
 apply t_step.
 apply app_red_l.
 apply beta.
destruct eqc; subst c.
 unfold subst; simpl.
 eapply t_trans.
  apply t_step.
  apply beta.
 unfold subst; simpl.
 rewrite lift0.
 apply t_step.
 apply red1_beta.
 unfold subst; rewrite simpl_subst; auto.
 rewrite lift0; trivial.

 unfold subst; simpl.
 eapply t_trans.
  apply t_step.
  apply beta.
 unfold subst; simpl; rewrite simpl_subst_rec; auto.
 rewrite lift_rec0.
 apply t_step.
 apply red1_beta.
 unfold subst; rewrite simpl_subst; auto.
 rewrite lift0; trivial.
Qed.

Lemma G_INL m a :
  redp (App (guard_sum m) (INL a)) (App2 m m (INL a)).
apply G_sim.
econstructor; exists 1; split; auto.
reflexivity.
Qed.
Lemma G_INR m a :
  redp (App (guard_sum m) (INR a)) (App2 m m (INR a)).
apply G_sim.
econstructor; exists 0; split; auto.
reflexivity.
Qed.
*)



(** * Sigma-types *)

Definition COUPLE t1 t2 :=
  Abs (App2 (Ref 0) (lift 1 t1) (lift 1 t2)).

Lemma COUPLE_iota t1 t2 b:
  redp (App (COUPLE t1 t2) b) (App2 b t1 t2).
unfold COUPLE.
apply t_step; apply red1_beta.
unfold subst; simpl.
repeat rewrite simpl_subst; trivial.
repeat rewrite lift0; trivial.
Qed.

Definition is_couple t := exists a b, t = Abs (App2 (Ref 0) a b).


(** (WHEN_COUPLE t) reduces to the identity when t is a couple, or is
    neutral when t is. *)
Definition WHEN_COUPLE :=
  Abs (App (Ref 0) (Abs (Abs (Abs (Ref 0))))).

Lemma WHEN_COUPLE_iota t u :
  is_couple t ->
  redp (App2 WHEN_COUPLE t u) u.
intros (a,(b,eqt)).
subst t.
unfold WHEN_COUPLE.
eapply t_trans.
 apply redp_app_l.
 apply t_step.
 apply beta.
unfold subst; simpl.
rewrite lift0.
eapply t_trans.
 apply redp_app_l.
 apply t_step.
 apply beta.
unfold subst; simpl.
rewrite lift0.
eapply t_trans.
 apply redp_app_l.
 apply redp_app_l.
 apply t_step.
 apply beta.
unfold subst; simpl.
eapply t_trans.
 apply redp_app_l.
 apply t_step.
 apply beta.
unfold subst; simpl.
apply t_step; apply red1_beta.
unfold subst; simpl.
rewrite lift0; reflexivity.
Qed.

Lemma WHEN_COUPLE_neutral t S :
  inSAT t (interSAT(fun S => S)) ->
  inSAT (App WHEN_COUPLE t) S.
intros.
unfold WHEN_COUPLE.
apply inSAT_exp;[simpl;auto|].
unfold subst; simpl; rewrite lift0.
apply prodSAT_elim with snSAT.
2:apply snSAT_intro; auto.
apply interSAT_elim with (1:=H).
Qed.

(*
(** Self-application guarded by a couple *)
Definition guard_couple :=
  Abs (Abs (App2 (App2 WHEN_COUPLE (Ref 0) (Ref 1)) (Ref 1) (Ref 0))).

Lemma guard_couple_sim : forall m n,
  is_couple n ->
  redp (App2 guard_couple m n) (App2 m m n).
unfold guard_couple, App2.
intros m n is_c.
eapply t_trans.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
fold WHEN_COUPLE.
eapply t_trans.
 apply t_step; apply beta.
unfold subst; simpl.
fold WHEN_COUPLE.
rewrite simpl_subst; auto.
rewrite !lift0.
apply redp_app_l.
apply redp_app_l.
apply WHEN_COUPLE_iota; trivial.
Qed.

(** (guard_couple m n) reduces to (m m n) when n is a constructor. Note that
    n need not be closed. *)
Lemma guard_couple_sim : forall m n,
  is_couple n ->
  redp (App2 guard_couple m n) (App2 m m n).
intros m n (t1,(t2,eqn)).
unfold guard_couple.
eapply t_trans.
 apply redp_app_l.
 apply t_step.
 apply beta.
unfold subst; simpl.
eapply t_trans.
 apply t_step.
 apply beta.
unfold subst; simpl.
repeat rewrite simpl_subst; auto.
repeat rewrite lift0.
rewrite eqn.
eapply t_trans.
 apply redp_app_l.
 apply redp_app_l.
 apply t_step.
 apply beta.
apply redp_app_l.
apply redp_app_l.
unfold subst; simpl.
rewrite lift0.
eapply t_trans.
 apply redp_app_l.
 apply t_step.
 apply beta.
unfold subst; simpl.
repeat rewrite simpl_subst; auto.
apply t_step.
apply red1_beta.
unfold subst; simpl.
repeat rewrite simpl_subst; auto.
rewrite lift0; trivial.
Qed.

*)
(*
(** Self-application guarded by a couple *)
Definition guard_couple :=
  Abs (Abs (App2 (App (Ref 0) (Abs (Abs (Ref 3)))) (Ref 1) (Ref 0))).

(** (guard_couple m n) reduces to (m m n) when n is a constructor. Note that
    n need not be closed. *)
Lemma guard_couple_sim : forall m n,
  (exists t1 t2, n = Abs (App2 (Ref 0) t1 t2)) ->
  redp (App2 guard_couple m n) (App2 m m n).
intros m n (t1,(t2,eqn)).
unfold guard_couple.
eapply t_trans.
 apply redp_app_l.
 apply t_step.
 apply beta.
unfold subst; simpl.
eapply t_trans.
 apply t_step.
 apply beta.
unfold subst; simpl.
repeat rewrite simpl_subst; auto.
repeat rewrite lift0.
rewrite eqn.
eapply t_trans.
 apply redp_app_l.
 apply redp_app_l.
 apply t_step.
 apply beta.
apply redp_app_l.
apply redp_app_l.
unfold subst; simpl.
rewrite lift0.
eapply t_trans.
 apply redp_app_l.
 apply t_step.
 apply beta.
unfold subst; simpl.
repeat rewrite simpl_subst; auto.
apply t_step.
apply red1_beta.
unfold subst; simpl.
repeat rewrite simpl_subst; auto.
rewrite lift0; trivial.
Qed.
*)
Definition sigmaReal (X:set->SAT) (Y:set->set->SAT) (a:set) : SAT :=
  interSAT (fun C => prodSAT
     (piSAT0 (fun x => a==couple x (snd a)) X (fun x => prodSAT (Y x (snd a)) C))
     C).

Instance sigmaReal_morph X Y :
  Proper (eq_set ==> eqSAT) X ->
  Proper (eq_set ==> eq_set ==> eqSAT) Y ->
  Proper (eq_set ==> eqSAT) (sigmaReal X Y).
do 2 red; intros.
apply interSAT_morph.
apply indexed_relation_id; intros C.
apply prodSAT_morph; auto with *.
apply piSAT0_morph; intros; auto with *.
 red; intros.
 rewrite H1; reflexivity.

 apply prodSAT_morph; auto with *.
 rewrite H1; reflexivity.
Qed.

Lemma Real_couple x y X Y t1 t2 :
  Proper (eq_set ==> eqSAT) X ->
  Proper (eq_set ==> eq_set ==> eqSAT) Y ->
  inSAT t1 (X x) ->
  inSAT t2 (Y x y) ->
  inSAT (COUPLE t1 t2) (sigmaReal X Y (couple x y)).
intros.
apply interSAT_intro.
 exact snSAT.
intros C.
apply prodSAT_intro; intros.
unfold subst; simpl subst_rec.
repeat rewrite simpl_subst; auto.
repeat rewrite lift0.
apply piSAT0_elim' in H3; red in H3.
apply prodSAT_elim with (2:=H2).
rewrite <- (snd_def x y).
apply H3; trivial.
rewrite snd_def; reflexivity.
Qed.
(*
Lemma Real_sigma_elim X Y a C t b :
  inSAT t (sigmaReal X Y a) ->
  inSAT b (prodSAT (X (fst a)) (prodSAT (Y (fst a) (snd a)) C)) ->
  inSAT (App t b) C.
intros.
apply interSAT_elim with (x:=C) in H.
apply prodSAT_elim with (1:=H) (2:=H0).
Qed.
*)
Lemma Real_sigma_elim X Y RX RY a C t b :
  ext_fun X Y ->
  Proper (eq_set ==> eqSAT) C ->
  a ∈ sigma X Y ->
  inSAT t (sigmaReal RX RY a) ->
  inSAT b (piSAT0 (fun x => x∈X) RX
           (fun x => piSAT0 (fun y => y ∈ Y x) (RY x) (fun y => C(couple x y)))) ->
  inSAT (App t b) (C a).
intros.
assert (eqa := surj_pair _ _ _ (subset_elim1 _ _ _ H1)).
rewrite eqa.
unfold sigmaReal in H2.
refine (prodSAT_elim _ (interSAT_elim H2 _) _).
apply piSAT0_intro; intros.
 apply sat_sn in H3; trivial.
apply prodSAT_intro'; intros.
rewrite eqa in H4; apply couple_injection in H4; destruct H4 as (?,_).
rewrite H4.
refine (piSAT0_elim' (piSAT0_elim' H3 x _ _ H5) (snd a) _ _ H6).
 apply fst_typ_sigma in H1; rewrite H4 in H1; trivial.

 apply snd_typ_sigma with (A:=X); auto with *.
Qed.

Lemma WHEN_COUPLE_sat A' B' RA' RB' S x t m :
  morph1 B' ->
  x ∈ sigma A' B' ->
  inSAT t (sigmaReal RA' RB' x) ->
  inSAT m S ->
  inSAT (App2 WHEN_COUPLE t m) S.
intros Bm xty xsat msat.
unfold WHEN_COUPLE.
eapply inSAT_context.
 intros.
 apply inSAT_exp;[simpl;auto|].
 unfold subst; simpl.
 rewrite lift0.
 exact H.
apply prodSAT_elim with S; trivial.
apply Real_sigma_elim with (3:=xty) (4:=xsat)(C:=fun _ => prodSAT S S); auto.
 do 2 red; reflexivity.

 apply piSAT0_intro; intros; auto.
 apply inSAT_exp;[right; apply sat_sn in H0;trivial|].
 unfold subst; simpl.
 apply piSAT0_intro; intros; auto.
 apply inSAT_exp;[right; apply sat_sn in H2;trivial|].
 unfold subst; simpl.
 apply prodSAT_intro; intros.
 unfold subst; simpl; rewrite lift0.
 trivial.
Qed.

(** * Structural fixpoint. *)

(** To avoid non-termination, we need to insert a "guard" operator G to control
    the self-application of the fixpoint.
 *)


Definition GUARD G :=
  Abs (Abs (App (App (App (App (lift 2 G) (Ref 0)) (Ref 1)) (Ref 1)) (Ref 0))).

Lemma GUARD_sim G m t :
  (forall u, redp (App2 G t u) u) ->
  redp (App2 (GUARD G) m t) (App2 m m t).
intros; unfold GUARD.
eapply t_trans.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
rewrite simpl_subst; auto.
eapply t_trans.
 apply t_step; apply beta.
unfold subst; simpl.
rewrite !simpl_subst; trivial.
rewrite !lift0.
apply redp_app_l.
apply redp_app_l.
apply H.
Qed.
  
Lemma GUARD_neutral G m t S :
  sn m ->
  inSAT (App G t) (interSAT(fun S=>S)) ->
  inSAT (App2 (GUARD G) m t) S.
unfold GUARD; intros.
apply snSAT_intro in H.
eapply inSAT_context.
 intros.
 apply inSAT_exp; [simpl;auto|].
 unfold subst; simpl.
 rewrite simpl_subst; auto.
 exact H1.
apply inSAT_exp.
 left; simpl.
 rewrite Bool.orb_true_r; trivial.
unfold subst; simpl.
rewrite !simpl_subst; trivial.
rewrite !lift0.
apply prodSAT_elim with snSAT.
apply prodSAT_elim with (2:=H).
apply prodSAT_elim with (2:=H).
apply interSAT_elim with (1:=H0).
apply snSAT_intro.
apply sat_sn in H0.
apply subterm_sn with (1:=H0); auto.
Qed.

Lemma GUARD_sat G m t S :
  inSAT (App2 (App2 G t m) m t) S ->
  inSAT (App2 (GUARD G) m t) S.
intros.
eapply inSAT_context.
 intros.
 apply inSAT_exp;[simpl;rewrite Bool.orb_true_r;auto|].
 unfold subst; simpl.
 rewrite simpl_subst; auto.
 exact H0.
apply inSAT_exp;[simpl;rewrite Bool.orb_true_r;auto|].
unfold subst; simpl subst_rec.
repeat rewrite simpl_subst; auto.
repeat rewrite lift0.
trivial.
Qed.



Definition guard_sum := GUARD WHEN_SUM.

Lemma guard_sum_INL : forall m n,
  redp (App2 guard_sum m (INL n)) (App2 m m (INL n)).
intros.
apply GUARD_sim.
intro; apply WHEN_SUM_INL.
Qed.
Lemma guard_sum_INR : forall m n,
  redp (App2 guard_sum m (INR n)) (App2 m m (INR n)).
intros.
apply GUARD_sim.
intro; apply WHEN_SUM_INR.
Qed.

Lemma guard_sum_neutral m t S :
  sn m ->
  inSAT t (interSAT(fun S => S)) ->
  inSAT (App2 guard_sum m t) S.
unfold guard_sum; intros.
apply GUARD_neutral; trivial.
apply WHEN_SUM_neutral; trivial.
Qed.

Definition guard_couple := GUARD WHEN_COUPLE.

Lemma guard_couple_iota : forall m a b,
  redp (App2 guard_couple m (COUPLE a b)) (App2 m m (COUPLE a b)).
intros.
apply GUARD_sim.
intro; apply WHEN_COUPLE_iota.
unfold is_couple, COUPLE; eauto.
Qed.

Lemma guard_couple_neutral m t S :
  sn m ->
  inSAT t (interSAT(fun S => S)) ->
  inSAT (App2 guard_couple m t) S.
unfold guard_couple; intros.
apply GUARD_neutral; trivial.
apply WHEN_COUPLE_neutral; trivial.
Qed.


Definition FIXP G m :=
  App (GUARD G) (Abs (App (lift 1 m) (App (lift 1 (GUARD G)) (Ref 0)))).

(** when the guard expands when applied to n (e.g. when it's a constructor),
    then the fixpoint unrolls once. *)
Lemma FIXP_sim : forall G m n,
  (forall u, redp (App2 G n u) u) ->
  redp (App (FIXP G m) n) (App2 m (FIXP G m) n).
intros G m n Gsim.
unfold FIXP at 1.
eapply t_trans.
 apply GUARD_sim; trivial.
apply redp_app_l.
apply t_step.
apply red1_beta.
set (t1 := Abs (App (lift 1 m) (App (lift 1 (GUARD G)) (Ref 0)))).
unfold subst; simpl.
rewrite !simpl_subst; auto.
rewrite simpl_subst_rec; auto.
rewrite !lift0.
rewrite lift_rec0.
reflexivity.
Qed.

Lemma FIXP_sn G m:
  (forall m, sn m -> sn (App (GUARD G) m)) ->
  sn (App m (App (GUARD G) (Ref 0))) ->
  sn (FIXP G m).
intros snG satm.
unfold FIXP.
apply snG; trivial.
apply sn_abs.
apply sn_subst with (Ref 0).
unfold subst; simpl.
rewrite simpl_subst; auto.
rewrite simpl_subst_rec; auto.
rewrite lift0.
rewrite lift_rec0.
exact satm.
Qed.

Require Import ZFord.

Lemma FIXP_sat0 G o T U RT m X :
  let FIX_bot o := piSAT0 (fun n => n ∈ U o) (RT o) (X o) in
  let FIX_strict o := piSAT0 (fun n => n ∈ T o) (RT o) (X o) in
  isOrd o ->
  (* strict domain values form a continuous sequence *)
  (forall y n, isOrd y -> y ⊆ o -> n ∈ U y ->
   (forall S, inclSAT (RT y n) S) \/ exists2 y', y' ∈ y & n ∈ T (osucc y')) ->
  (* U is not empty *)
  (forall o, isOrd o -> exists w, w ∈ U o) ->
  (* monotonicity of RT and X *)
  (forall y y' n, isOrd y -> isOrd y' -> n ∈ T y -> y ⊆ y' -> y' ⊆ o ->
   eqSAT (RT y n) (RT y' n)) ->
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ T y ->
   inclSAT (X y n) (X y' n)) ->
  (* Saturation property of guard G *)
  (forall t (X:SAT),
   inSAT t (interSAT(fun S=>S)) ->
   inSAT (App G t) X) ->
  (forall o x t m (X:SAT),
   isOrd o -> x ∈ T o ->
   inSAT t (RT o x) ->
   inSAT m X ->
   inSAT (App2 G t m) X) ->
  inSAT m (piSAT0 (fun o' => o' ∈ osucc o)
    (fun o' => FIX_bot o') (fun o' => FIX_strict (osucc o'))) ->
  inSAT (FIXP G m) (FIX_bot o).
intros FIX_bot FIX_strict oo Tcont Ubot Rirrel Xmono Gneutr Gsat msat.
elim oo using isOrd_ind; intros.
apply piSAT0_intro'; [|apply  Ubot;trivial].
intros x u xty0 ureal.
unfold FIXP.
(*assert (Gsat' : forall y x u v, 
  isOrd y ->
  x ∈ U y ->
  sn v ->
  inSAT u (RT y x) ->
  inSAT (App (App (GUARD G) v) u) (X y x)).
 intros.
 apply GUARD_sat.
 eapply prodSAT_elim;[|apply H5].
 eapply prodSAT_elim;[|apply (snSAT_intro H4)].
 apply Tcont in H3; trivial.
 destruct H3 as [?|(y',?,?)].
  rewrite H3 in H5.
  eapply prodSAT_elim;[|apply (snSAT_intro H4)].
  apply Gneutr; trivial.

  assert (isOrd y') by eauto using isOrd_inv.
  apply Gsat with (2:=H6); auto.
   rewrite Rirrel with (y':=y0); auto.
    red; intros; apply le_lt_trans with y'; trivial.
    admit.

    apply interSAT_elim with (1:=vsat).*)
assert (sn (Abs (App (lift 1 m) (App (lift 1 (GUARD G)) (Ref 0))))).
 (* neutral case *)
 eapply sat_sn.
 apply prodSAT_intro with (A:=interSAT(fun S=>S)).
 intros v vsat.
 match goal with |- inSAT _ ?T =>
   change (inSAT (App (subst v (lift 1 m)) (App (subst v (lift 1 (GUARD G))) (lift 0 v))) T)
 end.
 unfold subst; rewrite !simpl_subst; trivial.
 rewrite !lift0.
 apply piSAT0_elim' in msat; red in msat.
 apply msat with (x:=y); auto with *.
  apply ole_lts; auto.

  apply piSAT0_intro'; intros; [|apply Ubot; trivial].
  apply GUARD_sat.
  eapply prodSAT_elim;[|apply H3].
  eapply prodSAT_elim;[|apply vsat].
  apply Tcont in H2; trivial.
  destruct H2 as [?|(y',?,?)].
   eapply prodSAT_elim;[|apply vsat].
   apply Gneutr.
   apply H2; trivial.

   assert (isOrd y') by eauto using isOrd_inv.
   apply Gsat with (2:=H4); auto.
    rewrite Rirrel with (y':=y); auto.
    red; intros; apply le_lt_trans with y'; trivial.

    apply interSAT_elim with (1:=vsat).
apply GUARD_sat.
apply Tcont in xty0; trivial.
destruct xty0 as [?|(y',?,?)].
 apply prodSAT_elim with (2:=ureal).
 apply prodSAT_elim with (2:=snSAT_intro H2).
 eapply prodSAT_elim;[|apply (snSAT_intro H2)].
 apply Gneutr; trivial.
 apply H3; trivial.

 specialize H1 with (1:=H3).
 assert (isOrd y') by eauto using isOrd_inv.
 assert (zlt : osucc y' ⊆ y).
  red; intros; apply le_lt_trans with y'; auto.
 assert (ureal' : inSAT u (RT (osucc y') x)).
  rewrite <- Rirrel with (3:=H4) in ureal; auto.
 eapply inSAT_context.
  apply inSAT_context.
  intros.
  apply Gsat with (2:=H4); auto.
  exact H6.
 eapply inSAT_context.
  intros.
  apply inSAT_exp.
   left; simpl; rewrite !Bool.orb_true_r; trivial.
  unfold subst; simpl.
  rewrite simpl_subst; auto.
  rewrite simpl_subst_rec; auto.
  rewrite !lift0.
  rewrite !lift_rec0.
  change (inSAT (App m (FIXP G m)) S).
  exact H6.
 apply Xmono with (osucc y'); auto.
 assert (y' ∈ osucc o).
  apply isOrd_trans with o; auto.
  apply H0; trivial.
 apply piSAT0_elim' in msat; red in msat.
 specialize msat with (1:=H6) (2:=H1).
 apply piSAT0_elim' in msat; red in msat.
 apply msat; trivial.
Qed.


(* OLD: 
Definition FIXP G m :=
  App G (Abs (App (lift 1 m) (App (lift 1 G) (Ref 0)))).

(** when the guard expands when applied to n (e.g. when it's a constructor),
    then the fixpoint unrolls once. *)
Lemma FIXP_sim : forall G m n,
  (forall m, redp (App2 G m n) (App2 m m n)) ->
  redp (App (FIXP G m) n) (App2 m (FIXP G m) n).
intros G m n Gsim.
unfold FIXP at 1.
eapply t_trans.
 apply Gsim.
apply redp_app_l.
apply t_step.
apply red1_beta.
set (t1 := Abs (App (lift 1 m) (App (lift 1 G) (Ref 0)))).
unfold subst; simpl.
repeat rewrite simpl_subst; auto.
repeat rewrite lift0.
reflexivity.
Qed.

Lemma FIXP_sn G m:
  (forall m, sn m -> sn (App G m)) ->
  sn (App m (App G (Ref 0))) ->
  sn (FIXP G m).
intros snG satm.
unfold FIXP.
apply snG; trivial.
apply sn_abs.
apply sn_subst with (Ref 0).
unfold subst; simpl.
repeat rewrite simpl_subst; auto.
repeat rewrite lift0; auto.
Qed.

Require Import ZFord.

Lemma FIXP_sat0 G o T U RT m X :
  let FIX_bot o := piSAT0 (fun n => n ∈ U o) (RT o) (X o) in
  let FIX_strict o := piSAT0 (fun n => n ∈ T o) (RT o) (X o) in
  isOrd o ->
  (* strict domain values form a continuous sequence *)
  (forall y n, isOrd y -> y ⊆ o -> n ∈ T y -> exists2 y', y' ∈ y & n ∈ T (osucc y')) ->
  (* U is not empty *)
  (forall o, isOrd o -> exists w, w ∈ U o) ->
  (* monotonicity of RT and X *)
  (forall y y' n, isOrd y -> isOrd y' -> n ∈ T y -> y ⊆ y' -> y' ⊆ o ->
   eqSAT (RT y n) (RT y' n)) ->
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ T y ->
   inclSAT (X y n) (X y' n)) ->
  (* Saturation property of guard G *)
  (forall o x t m (X:SAT), isOrd o -> x ∈ U o ->
   inSAT t (RT o x) ->
   sn m ->
   (x ∈ T o -> inSAT (App2 m m t) X) ->
   inSAT (App2 G m t) X) ->

  inSAT m (piSAT0 (fun o' => o' ∈ osucc o)
    (fun o' => FIX_bot o') (fun o' => FIX_strict (osucc o'))) ->
  inSAT (FIXP G m) (FIX_bot o).
intros FIX_bot FIX_strict oo Tcont Ubot Rirrel Xmono Gsat msat.
elim oo using isOrd_ind; intros.
(*
apply piSAT0_intro; intros.
 eapply sat_sn.
 unfold FIXP.
 eapply prodSAT_intro'; intros.
eapply Gsat.

 apply FIXP_sn.
*)
apply piSAT0_intro'; [|apply  Ubot;trivial].
intros x u xty0 ureal.
apply Gsat with (2:=xty0); trivial.
 (* neutral case *)
 eapply sat_sn.
 apply prodSAT_intro with (A:=interSAT(fun S=>S)).
 intros v vsat.
 unfold subst; simpl subst_rec.
 rewrite !simpl_subst; trivial.
 rewrite !lift0.
 match goal with |- inSAT _ ?S =>
   change (inSAT (App m (App G v)) S)
 end.
 apply piSAT0_elim' in msat; red in msat.
 apply msat with (x:=y); auto with *.
  apply ole_lts; auto.

  apply piSAT0_intro'; intros; [|apply Ubot; trivial].
  eapply Gsat with (2:=H2); trivial.
   apply sat_sn in vsat; trivial.

   intros _.
   eapply prodSAT_elim;[|apply H3].
   eapply prodSAT_elim;[|apply vsat].
   apply interSAT_elim with (1:=vsat).

 (* closed case *)
 intros xty.
 eapply inSAT_context; intros.
  apply inSAT_exp; simpl.
    left; simpl.
    rewrite Bool.orb_true_r.
    apply Bool.orb_true_r.

    unfold subst; simpl subst_rec.
    repeat rewrite simpl_subst; auto.
    repeat rewrite lift0.
    change (inSAT (App m (FIXP G m)) S).
    eexact H2.
 apply Tcont in xty; trivial.
 destruct xty as (z,zty,xty).
 specialize H1 with (1:=zty).
 assert (zo : isOrd z).
  apply isOrd_inv with y; trivial.
 assert (zlt : osucc z ⊆ y).
  red; intros; apply le_lt_trans with z; auto.
 assert (ureal' : inSAT u (RT (osucc z) x)).
  rewrite <- Rirrel with (3:=xty) in ureal; auto.
 apply Xmono with (osucc z); auto.
 assert (z ∈ osucc o).
  apply isOrd_trans with o; auto.
  apply H0; trivial.
 apply piSAT0_elim' in msat; red in msat.
 specialize msat with (1:=H2) (2:=H1).
 apply piSAT0_elim' in msat; red in msat.
 apply msat; trivial.
Qed.
*)

(* deprecated: *)
Lemma FIXP_sat G o T RT m X :
  let FIX_ty o := piSAT0 (fun n => n ∈ T o) (RT o) (X o) in
  isOrd o ->
  (forall m, sn m -> sn (App (GUARD G) m)) ->
  (forall o x t m (X:SAT), isOrd o -> x ∈ T o ->
   inSAT t (RT o x) ->
   inSAT (App2 m m t) X ->
   inSAT (App2 (GUARD G) m t) X) ->
  (forall y n, isOrd y -> y ⊆ o -> n ∈ T y -> exists2 y', y' ∈ y & n ∈ T (osucc y')) ->
  (forall y y' n, isOrd y -> isOrd y' -> n ∈ T y -> y ⊆ y' -> y' ⊆ o ->
   eqSAT (RT y n) (RT y' n)) ->

  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ T y ->
   inclSAT (X y n) (X y' n)) ->
  inSAT m (piSAT0 (fun o' => o' ∈ osucc o) (fun o' => FIX_ty o') (fun o' => FIX_ty (osucc o'))) ->
  inSAT (FIXP G m) (FIX_ty o).
intros FIX_ty oo snG Gsat Tcont Rirrel Xmono msat.
elim oo using isOrd_ind; intros.
apply piSAT0_intro.
 apply FIXP_sn; trivial.
 apply piSAT0_elim' in msat; red in msat.
 eapply sat_sn; apply msat with (x:=o).
  apply lt_osucc; trivial.

  apply piSAT0_intro; intros.
   apply snG.
   apply sn_var.

   apply Gsat with (2:=H2); trivial.
   eapply prodSAT_elim; [|eexact H3].
   apply prodSAT_elim with snSAT;apply varSAT.

intros x u xty0 ureal.
destruct Tcont with (3:=xty0) as (z,?,?); trivial.
specialize H1 with (1:=H2).
assert (zo : isOrd z).
 apply isOrd_inv with y; trivial.
assert (osucc z ⊆ y).
 red; intros.
 apply isOrd_plump with z; trivial.
  eauto using isOrd_inv.
  apply olts_le; trivial.

assert (ureal' : inSAT u (RT (osucc z) x)).
 apply Rirrel with (3:=H3) (4:=H4); auto.
unfold FIXP.
apply Gsat with (2:=H3)(3:=ureal') (x:=x); auto.
eapply inSAT_context; intros.
 apply inSAT_exp.
  left; simpl.
  rewrite Bool.orb_true_r.
  apply Bool.orb_true_r.

  unfold subst; simpl subst_rec.
  repeat rewrite simpl_subst; auto.
  rewrite simpl_subst_rec; auto.
  repeat rewrite lift0.
  rewrite lift_rec0.
  change (inSAT (App m (FIXP G m)) S).
  eexact H5.
apply Xmono with (osucc z); auto.
assert (z ∈ osucc o).
 apply isOrd_trans with o; auto.
 apply H0; trivial.
apply piSAT0_elim' in msat; red in msat.
specialize msat with (1:=H5) (2:=H1).
apply piSAT0_elim' in msat; red in msat; auto.
Qed.


(** Transfinite iteration *)

Require Import ZFfixrec.
Require Import ZFrelations.
Require Import ZFord ZFfix.

Definition tiSAT (F:set->set) (A:(set->SAT)->set->SAT) (o:set) (x:set) : SAT :=
  sSAT (cc_app (REC (fun o' f => cc_lam (TI F (osucc o'))
                                   (fun y => iSAT (A (fun z => sSAT (cc_app f z)) y))) o) x).

Lemma tiSAT_ext1 A F f o :
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  ext_fun (TI F (osucc o)) (fun y => iSAT (A (fun z => sSAT (cc_app f z)) y)).
do 2 red; intros.
apply iSAT_morph.
apply H; trivial.
red; intros.
apply sSAT_morph.
rewrite H2; reflexivity.
Qed.
Hint Resolve tiSAT_ext1.

Instance tiSAT_morph F A :
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  Proper (eq_set ==> eq_set ==> eqSAT) (tiSAT F A).
do 3 red; intros.
unfold tiSAT.
apply sSAT_morph.
apply cc_app_morph; trivial.
apply REC_morph; trivial.
do 3 red; intros.
apply cc_lam_ext; auto with *.
 rewrite H2; reflexivity.

 red; intros.
 apply iSAT_morph.
 apply H; trivial.
 red; intros.
 rewrite H3; rewrite H6; reflexivity.
Qed.

Lemma tiSAT_recursor o A F :
  Proper (incl_set==>incl_set) F ->
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  (forall R R' o', isOrd o' -> o' ⊆ o -> (forall x x', x ∈ TI F o' -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o ->
  recursor o (TI F)
    (fun o f => forall x, x∈TI F o -> cc_app f x == iSAT(sSAT(cc_app f x)))
    (fun o' f => cc_lam (TI F (osucc o')) (fun y => iSAT (A (fun z => sSAT (cc_app f z)) y))).
intros Fm Am Aext oo.
split; intros.
 apply TI_morph.

 apply TI_mono_eq; trivial.

 red in H2.
 rewrite <- H1 in H4.
 rewrite <- H2; auto.

 apply TI_elim in H3; auto.
 destruct H3.
 rewrite <- TI_mono_succ in H4; trivial.
 2:apply isOrd_inv with o0; trivial.
 eauto.

 do 3 red; intros.
 apply cc_lam_ext.
  rewrite H; reflexivity.

  red; intros.
  apply iSAT_morph.
  apply Am; trivial.
  red; intros.
  rewrite H0; rewrite H3; reflexivity.

 split; intros.
  apply is_cc_fun_lam; auto.

  rewrite cc_beta_eq; auto.
  rewrite iSAT_id; reflexivity.

 red; red; intros.
 rewrite cc_beta_eq; auto.
 rewrite cc_beta_eq; auto.
  apply iSAT_morph.
  apply Aext with o0; auto with *.
   apply H1.
   transitivity o'; trivial.
  intros.
  apply sSAT_morph.
  rewrite <- H6.
  apply H3; trivial.

  revert H4; apply TI_mono; auto with *.
   apply isOrd_succ; apply H2.
   apply isOrd_succ; apply H1.
   apply osucc_mono; trivial.
    apply H1.
    apply H2.
Qed.


Lemma tiSAT_eq o A F :
  Proper (incl_set==>incl_set) F ->
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  (forall R R' o', isOrd o' -> o' ⊆ o -> (forall x x', x ∈ TI F o' -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o ->
  forall x,
  x ∈ TI F o ->
  eqSAT (tiSAT F A o x) (A (tiSAT F A o) x).
intros.
unfold tiSAT.
specialize tiSAT_recursor with (1:=H) (2:=H0) (3:=H1) (4:=H2); intro rec.
rewrite REC_expand with (1:=H2) (2:=rec) (3:=H3).
rewrite cc_beta_eq.
 rewrite iSAT_id.
 reflexivity.

 do 2 red; intros.
 apply iSAT_morph.
 apply H0; trivial.
 red; intros.
 apply sSAT_morph.
 apply cc_app_morph; trivial.
 reflexivity.

 revert H3; apply TI_incl; auto.
Qed.


Lemma tiSAT_outside_domain o A F S :
  Proper (incl_set==>incl_set) F ->
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  (forall R R' o', isOrd o' -> o' ⊆ o -> (forall x x', x ∈ TI F o' -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o ->
  forall x,
  ~ x ∈ TI F o ->
  inclSAT (tiSAT F A o x) S.
intros.
specialize tiSAT_recursor with (1:=H) (2:=H0) (3:=H1) (4:=H2); intro rec.
unfold tiSAT.
red; intros.
rewrite REC_eqn with (2:=rec) in H4; trivial.
fold (tiSAT F A o) in H4.
rewrite cc_app_outside_domain with (dom:=TI F o) in H4; trivial.
2:apply is_cc_fun_lam.
2:do 2 red; intros; apply cc_app_morph; auto with *.
unfold sSAT,complSAT in H4.
assert (H4' := fun h => interSAT_elim H4 (exist _ S h)); clear H4; simpl in H4'.
apply H4'; intros.
apply empty_ax in H5; contradiction.
Qed.


Lemma tiSAT_mono o1 o2 A F:
  Proper (incl_set==>incl_set) F ->
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  (forall R R' o', isOrd o' -> o' ⊆ o2 -> (forall x x', x ∈ TI F o' -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o1 ->
  isOrd o2 ->
  o1 ⊆ o2 ->
  forall x,
  x ∈ TI F o1 ->
  eqSAT (tiSAT F A o1 x) (tiSAT F A o2 x).
intros.
specialize tiSAT_recursor with (1:=H) (2:=H0) (3:=H1) (4:=H3); intro rec.
unfold tiSAT at 2.
rewrite <- REC_ord_irrel with (2:=rec) (o:=o1); auto with *.
reflexivity.
Qed.

Lemma tiSAT_succ_eq o A F :
  Proper (incl_set==>incl_set) F ->
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  (forall R R' o', isOrd o' -> o' ⊆ osucc o -> (forall x x', x ∈ TI F o' -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o ->
  forall x,
  x ∈ TI F (osucc o) ->
  eqSAT (tiSAT F A (osucc o) x) (A (tiSAT F A o) x).
intros.
rewrite tiSAT_eq; auto.
apply H1 with o; auto with *.
 red; intros; apply isOrd_trans with o; auto.
intros.
transitivity (tiSAT F A o x0).
 symmetry; apply tiSAT_mono; auto with *.
 red; intros; apply isOrd_trans with o; auto.

 apply tiSAT_morph; auto with *.
Qed.

(* useful ?
Lemma FIXP_TI_sat G o F A m X :
  let FIX_ty o := piSAT0 (fun n => n ∈ TI F o) (tiSAT F A o) (X o) in
  Proper (incl_set ==> incl_set) F ->
  Proper ((eq_set ==> eqSAT) ==> eq_set ==> eqSAT) A ->
  (forall R R' o', isOrd o' -> o' ⊆ o -> (forall x x', x ∈ TI F o' -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o ->
  (forall m, sn m -> sn (App G m)) ->
  (forall o x t m (X:SAT), isOrd o -> x ∈ TI F o ->
   inSAT t (tiSAT F A o x) ->
   inSAT (App2 m m t) X ->
   inSAT (App2 G m t) X) ->
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ TI F y ->
   inclSAT (X y n) (X y' n)) ->
  inSAT m (piSAT0 (fun o' => o' ∈ osucc o)
             (fun o1 => FIX_ty o1) (fun o1 => FIX_ty (osucc o1))) ->
  inSAT (FIXP G m) (FIX_ty o).
intros.
apply FIXP_sat; trivial.
 intros.
 apply TI_elim in H9; auto.
 destruct H9 as (o',?,?); exists o'; trivial.
 rewrite TI_mono_succ; eauto using isOrd_inv.

 intros.
 apply tiSAT_mono; trivial.
 intros.
 apply H1 with (o':=o'); trivial.
 transitivity y'; trivial.
Qed.

*)
