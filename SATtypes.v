
Require Import ZF ZFpairs ZFsum Sat.
Require Import ZFlambda.
Require Import Lambda.

Set Implicit Arguments.

(** Unit type *)

Definition unitSAT :=
  interSAT (fun C => prodSAT C C).

Definition ID := Abs (Ref 0).

Lemma ID_intro0 S : inSAT ID (prodSAT S S).
apply prodSAT_intro; intros.
unfold subst; simpl subst_rec.
rewrite lift0.
trivial.
Qed.

Lemma ID_intro : inSAT ID unitSAT.
apply interSAT_intro with (1:=snSAT).
apply ID_intro0.
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
  Abs (App2 (Ref 0) (Abs ID) (Abs ID)).

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

Lemma WHEN_SUM_neutral t :
  inSAT t (prodSAT snSAT (prodSAT snSAT neuSAT)) ->
  inSAT (App WHEN_SUM t) neuSAT.
intros.
unfold WHEN_SUM.
apply inSAT_exp;[simpl;auto|].
unfold subst; simpl; rewrite lift0.
apply prodSAT_elim with snSAT.
2:apply snSAT_intro; auto.
apply prodSAT_elim with snSAT; trivial.
apply snSAT_intro; auto.
Qed.
(*
Definition sumSAT X Y : SAT :=
  interSAT (fun C => prodSAT (prodSAT X C) (prodSAT (prodSAT Y C) C)).

Lemma sumSAT_intro1 X Y t :
  inSAT t X ->
  inSAT (INL t) (sumSAT X Y).
intros tsat.
apply interSAT_intro;[exact snSAT|].
intros C.
apply prodSAT_intro; intros b1 b1sat.
unfold subst; simpl.
rewrite simpl_subst; auto with *.
apply prodSAT_intro; intros b2 b2sat.
unfold subst; simpl.
rewrite !simpl_subst, !lift0; auto with *.
apply prodSAT_elim with X; trivial.
Qed.

Lemma sumSAT_intro2 X Y t :
  inSAT t Y ->
  inSAT (INR t) (sumSAT X Y).
intros tsat.
apply interSAT_intro;[exact snSAT|].
intros C.
apply prodSAT_intro; intros b1 b1sat.
unfold subst; simpl.
rewrite simpl_subst; auto with *.
apply prodSAT_intro; intros b2 b2sat.
unfold subst; simpl.
rewrite !simpl_subst, !lift0; auto with *.
apply prodSAT_elim with Y; trivial.
Qed.

Lemma sumSAT_case X Y C t b1 b2 :
  inSAT t (sumSAT X Y) ->
  inSAT b1 (prodSAT X C) ->
  inSAT b2 (prodSAT Y C) ->
  inSAT (App2 t b1 b2) C.
intros tsat b1sat b2sat.
apply prodSAT_elim with (2:=b2sat).
apply prodSAT_elim with (2:=b1sat).
apply interSAT_elim with (1:=tsat).
Qed.


Definition sumReal (X Y:set->SAT) (a:set) : SAT :=
  sumSAT
    (depSAT (fun x => a==inl x) X)
    (depSAT (fun y => a==inr y) Y).
 
Lemma Real_inl RX RY x t :
  Proper (eq_set ==> eqSAT) RX ->
  inSAT t (RX x) ->
  inSAT (INL t) (sumReal RX RY (inl x)).
intros Xm tsat.
apply sumSAT_intro1.
apply depSAT_intro; eauto using sat_sn.
intros x' eqs; apply couple_injection in eqs; destruct eqs as (_,eqx).
rewrite <- eqx; trivial.
Qed.

Lemma Real_inr RX RY x t :
  Proper (eq_set ==> eqSAT) RY ->
  inSAT t (RY x) ->
  inSAT (INR t) (sumReal RX RY (inr x)).
intros Ym tsat.
apply sumSAT_intro2.
apply depSAT_intro; eauto using sat_sn.
intros x' eqs; apply couple_injection in eqs; destruct eqs as (_,eqx).
rewrite <- eqx; trivial.
Qed.

Lemma Real_sum_case X Y a RX RY C t b1 b2 :
  a ∈ sum X Y ->
  inSAT t (sumReal RX RY a) ->
  inSAT b1 (piSAT0 (fun x => a==inl x) RX (fun _ => C)) ->
  inSAT b2 (piSAT0 (fun x => a==inr x) RY (fun _ => C)) ->
  inSAT (App2 t b1 b2) C.
intros.
apply sum_ind with (3:=H); intros.
 apply sumSAT_case with (1:=H0).
  apply prodSAT_intro'; intros.
  apply piSAT0_elim with (1:=H1) (2:=H4); auto.
  apply depSAT_elim' in H5; red in H5; auto.

  apply prodSAT_intro'; intros.

  apply sum_ind with (3:=H); intros.


apply sumSAT_case with (1:=H0).
 apply prodSAT_intro'; intros.
 apply depSAT_elim' in H3; red in H3.
 apply sum_ind with (3:=H); intros.
 apply piSAT0_elim with (1:=H1) (2:=H5); auto.


Definition sumReal (X Y:set->SAT) (a:set) : SAT :=
  sumSAT
    (condSAT (a==inl (dest_sum a)) (X (dest_sum a)))
    (condSAT (a==inr (dest_sum a)) (Y (dest_sum a))).
 
Lemma Real_inl RX RY x t :
  Proper (eq_set ==> eqSAT) RX ->
  inSAT t (RX x) ->
  inSAT (INL t) (sumReal RX RY (inl x)).
intros Xm tsat.
apply sumSAT_intro1.
rewrite condSAT_ok.
 rewrite dest_sum_inl; trivial.
 rewrite dest_sum_inl; reflexivity.
Qed.

Lemma Real_inr RX RY x t :
  Proper (eq_set ==> eqSAT) RY ->
  inSAT t (RY x) ->
  inSAT (INR t) (sumReal RX RY (inr x)).
intros Ym tsat.
apply sumSAT_intro2.
rewrite condSAT_ok.
 rewrite dest_sum_inr; trivial.
 rewrite dest_sum_inr; reflexivity.
Qed.

Lemma Real_sum_case X Y a RX RY C t b1 b2 :
  a ∈ sum X Y ->
  inSAT t (sumReal RX RY a) ->
  inSAT b1 (piSAT0 (fun x => a==inl x) RX (fun _ => C)) ->
  inSAT b2 (piSAT0 (fun x => a==inr x) RY (fun _ => C)) ->
  inSAT (App2 t b1 b2) C.
intros.
apply sumSAT_case with (1:=H0).
 apply prodSAT_intro'; intros.
 apply sum_ind with (3:=H); intros.
  rewrite condSAT_ok in H3.
  apply piSAT0_elim' in H1.
  rewrite H5 in H3.

 apply depSAT_elim' in H3.

 rewrite condSAT_def in H3.

apply interSAT_elim with (x:=C) in H0.
eapply prodSAT_elim;[apply prodSAT_elim with (1:=H0)|]; trivial.
Qed.
*)
Definition sumReal (X Y:set->SAT) (a:set) : SAT :=
  interSAT (fun C =>
     prodSAT (piSAT0 (fun x => a==inl x) X (fun _ => C))
    (prodSAT (piSAT0 (fun x => a==inr x) Y (fun _ => C))
     C)).

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

Lemma Real_sum_case a RX RY C t b1 b2 :
  inSAT t (sumReal RX RY a) ->
  inSAT b1 (piSAT0 (fun x => a==inl x) RX (fun _ => C)) ->
  inSAT b2 (piSAT0 (fun x => a==inr x) RY (fun _ => C)) ->
  inSAT (App2 t b1 b2) C.
intros.
apply interSAT_elim with (x:=C) in H.
eapply prodSAT_elim;[apply prodSAT_elim with (1:=H)|]; trivial.
Qed.

Lemma sumReal_mt RX RY :
  inclSAT (sumReal RX RY empty) (prodSAT snSAT (prodSAT snSAT neuSAT)).
red; intros.
apply prodSAT_intro'; intros.
apply sat_sn in H0.
apply prodSAT_intro'; intros.
apply sat_sn in H1.
apply Real_sum_case with (1:=H).
 apply piSAT0_intro; trivial.
 intros.
 apply discr_mt_couple in H2; contradiction.

 apply piSAT0_intro; trivial.
 intros.
 apply discr_mt_couple in H2; contradiction.
Qed.

Lemma WHEN_SUM_sat RA RB S x t m :
  inSAT t (sumReal RA RB x) ->
  inSAT m S ->
  inSAT (App2 WHEN_SUM t m) S.
intros tsat msat.
unfold WHEN_SUM.
eapply inSAT_context.
 intros.
 apply inSAT_exp;[simpl;auto|].
 unfold subst; simpl.
 rewrite lift0.
 exact H.
apply prodSAT_elim with S; trivial.
apply Real_sum_case with (1:=tsat); auto.
 apply piSAT0_intro; intros; auto.
 apply inSAT_exp;[right; apply sat_sn in H0;trivial|].
 unfold subst; simpl.
 apply ID_intro0.

 apply piSAT0_intro; intros; auto.
 apply inSAT_exp;[right; apply sat_sn in H0;trivial|].
 unfold subst; simpl.
 apply ID_intro0.
Qed.


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
  Abs (App (Ref 0) (Abs (Abs ID))).

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

Lemma WHEN_COUPLE_neutral t :
  inSAT t (prodSAT snSAT neuSAT) ->
  inSAT (App WHEN_COUPLE t) neuSAT.
intros.
unfold WHEN_COUPLE.
apply inSAT_exp;[simpl;auto|].
unfold subst; simpl; rewrite lift0.
apply prodSAT_elim with snSAT; trivial.
apply snSAT_intro; auto.
Qed.

Definition cartSAT (X Y:SAT) : SAT :=
  interSAT (fun C => prodSAT (prodSAT X (prodSAT Y C)) C).

Instance cartSAT_mono : Proper (inclSAT ==> inclSAT ==> inclSAT) cartSAT.
unfold cartSAT.
do 3 red; intros.
apply interSAT_mono; intros C.
apply prodSAT_mono; auto with *.
apply prodSAT_mono; auto with *.
apply prodSAT_mono; auto with *.
Qed.

Instance cartSAT_morph : Proper (eqSAT ==> eqSAT ==> eqSAT) cartSAT.
do 3 red; intros.
apply interSAT_morph.
apply indexed_relation_id.
intros C.
rewrite H,H0; reflexivity.
Qed.


Lemma cartSAT_intro X Y t1 t2 :
  inSAT t1 X ->
  inSAT t2 Y ->
  inSAT (COUPLE t1 t2) (cartSAT X Y).
intros.
apply interSAT_intro.
 exact snSAT.
intros C.
apply prodSAT_intro; intros.
unfold subst; simpl subst_rec.
repeat rewrite simpl_subst; auto.
repeat rewrite lift0.
apply prodSAT_elim with (2:=H0).
apply prodSAT_elim with (2:=H).
trivial.
Qed.

Lemma cartSAT_case X Y C t b :
  inSAT t (cartSAT X Y) ->
  inSAT b (prodSAT X (prodSAT Y C)) ->
  inSAT (App t b) C.
intros.
apply prodSAT_elim with (2:=H0).
apply interSAT_elim with (1:=H).
Qed.

Lemma WHEN_COUPLE_sat A B S t m :
  inSAT t (cartSAT A B) ->
  inSAT m S ->
  inSAT (App2 WHEN_COUPLE t m) S.
intros tsat msat.
unfold WHEN_COUPLE.
eapply inSAT_context.
 intros.
 apply inSAT_exp;[simpl;auto|].
 unfold subst; simpl.
 rewrite lift0.
 exact H.
apply prodSAT_elim with S; trivial.
apply cartSAT_case with (1:=tsat).
apply prodSAT_intro; intros a asat.
unfold subst; simpl.
apply prodSAT_intro; intros b bsat.
unfold subst; simpl.
apply prodSAT_intro; intros c csat.
unfold subst; simpl.
rewrite lift0; trivial.
Qed.


Definition sigmaReal (X:set->SAT) (Y:set->set->SAT) (a:set) : SAT :=
  cartSAT (X (fst a)) (Y (fst a) (snd a)).

Instance sigmaReal_morph_gen :
  Proper ((eq_set ==> eqSAT) ==> (eq_set ==> eq_set ==> eqSAT) ==>
          eq_set ==> eqSAT) sigmaReal.
do 4 red; intros.
apply cartSAT_morph.
 apply H; rewrite H1; reflexivity.
 apply H0; rewrite H1; reflexivity.
Qed.

Instance sigmaReal_morph X Y :
  Proper (eq_set ==> eqSAT) X ->
  Proper (eq_set ==> eq_set ==> eqSAT) Y ->
  Proper (eq_set ==> eqSAT) (sigmaReal X Y).
intros; apply sigmaReal_morph_gen; auto with *.
Qed.

Lemma Real_couple x y X Y t1 t2 :
  Proper (eq_set ==> eqSAT) X ->
  Proper (eq_set ==> eq_set ==> eqSAT) Y ->
  inSAT t1 (X x) ->
  inSAT t2 (Y x y) ->
  inSAT (COUPLE t1 t2) (sigmaReal X Y (couple x y)).
intros.
unfold sigmaReal.
rewrite fst_def,snd_def.
apply cartSAT_intro; trivial.
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
apply sigma_elim in H1; auto with *.
destruct H1 as (eqa,(ty1,ty2)).
apply cartSAT_case with (1:=H2).
apply prodSAT_intro'.
intros ta asat.
apply piSAT0_elim with (2:=ty1)(3:=asat) in H3.
apply prodSAT_intro'.
intros tb bsat.
apply piSAT0_elim with (2:=ty2)(3:=bsat) in H3.
rewrite <- eqa in H3.
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

Lemma GUARD_neutral G m t :
  sn m ->
  inSAT (App G t) (prodSAT snSAT (prodSAT snSAT (prodSAT snSAT neuSAT))) ->
  inSAT (App2 (GUARD G) m t) neuSAT.
intros.
apply GUARD_sat.
apply snSAT_intro in H.
apply prodSAT_elim with snSAT.
 apply prodSAT_elim with (2:=H).
 apply prodSAT_elim with (2:=H).
 trivial.
apply snSAT_intro.
apply sat_sn in H0.
apply subterm_sn with (1:=H0); auto.
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

Lemma guard_sum_neutral m t :
  sn m ->
  inSAT t (prodSAT snSAT (prodSAT snSAT neuSAT)) ->
  inSAT (App2 guard_sum m t) neuSAT.
unfold guard_sum; intros.
apply GUARD_neutral; trivial.
apply neuSAT_def.
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

Lemma guard_couple_neutral m t :
  sn m ->
  inSAT t (prodSAT snSAT neuSAT) ->
  inSAT (App2 guard_couple m t) neuSAT.
unfold guard_couple; intros.
apply GUARD_neutral; trivial.
apply neuSAT_def.
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
(*
Lemma FIXP_neutral G m t S A B C:
  (exists w, w ∈ A) ->
  (forall t, inSAT t (piSAT0 (fun x => x ∈ A) B C) -> sn (App m t)) ->
  (forall S, inSAT G (piSAT0 (fun x => x ∈ A) B (fun _ => prodSAT S S))) ->
  inSAT (App G t) (interSAT (fun S => S)) ->
  inSAT (App (FIXP G m) t) S.
intros Awit msat Gsat Gneutr.
apply GUARD_neutral; trivial.
eapply sat_sn with (prodSAT (interSAT(fun S=>S)) _).
apply prodSAT_intro; intros.
unfold subst, subst_rec; fold subst_rec.
rewrite !simpl_subst, !lift0; auto.
simpl.
apply snSAT_intro.
apply msat.
apply piSAT0_intro'; intros; trivial.
apply GUARD_sat.
apply prodSAT_elim with (2:=H1).
apply prodSAT_elim with (2:=H).
unfold piSAT0 in Gsat.
unfold depSAT in Gsat.
eapply piSAT0_elim' in Gsat.
red in Gsat; specialize Gsat with (1:=H0) (2:=H1).
apply prodSAT_elim with (2:=H).
exact Gsat.
eapply Gsat.

apply Gsat with (2:=H1); trivial.
apply interSAT_elim with (1:=H).
Qed.
*)

Lemma FIXP_neutral G m t A B C:
  (exists w, w ∈ A) ->
  (forall t, inSAT t (piSAT0 (fun x => x ∈ A) B C) -> sn (App m t)) ->
  (forall x n t S,
   x ∈ A ->
   inSAT n (B x) -> inSAT t S -> inSAT (App2 G n t) S) ->
  inSAT (App G t) (prodSAT snSAT (prodSAT snSAT (prodSAT snSAT neuSAT))) ->
  inSAT (App (FIXP G m) t) neuSAT.
intros Awit msat Gsat Gneutr.
apply GUARD_neutral; trivial.
eapply sat_sn with (prodSAT neuSAT _).
apply prodSAT_intro; intros.
unfold subst, subst_rec; fold subst_rec.
rewrite !simpl_subst, !lift0; auto.
simpl.
apply snSAT_intro.
apply msat.
apply piSAT0_intro'; intros; trivial.
apply GUARD_sat.
apply prodSAT_elim with (2:=H1).
apply prodSAT_elim with (2:=H).
apply Gsat with (2:=H1); trivial.
apply neuSAT_def; trivial.
Qed.

(*Require Import ZFcoc.*)

Section FIXP_Reducibility.

(*Lemma FIXP_sat0 G o T U RT m X :
  let FIX_bot o := piSAT0 (fun n => n ∈ U o) (RT o) (X o) in
  let FIX_strict o := piSAT0 (fun n => n ∈ T o) (RT o) (X o) in
  isOrd o ->
  (* strict domain values form a continuous sequence *)
  (forall y n, isOrd y -> y ⊆ o -> n ∈ U y ->
   ~ n ∈ T y  \/ exists2 y', y' ∈ y & n ∈ T (osucc y')) ->
  (* U is not empty *)
  (forall o, isOrd o -> exists w, w ∈ U o) ->
  (* monotonicity of RT and X *)
  (forall y y' n, isOrd y -> isOrd y' -> n ∈ T y -> y ⊆ y' -> y' ⊆ o ->
   eqSAT (RT y n) (RT y' n)) ->
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ T y ->
   inclSAT (X y n) (X y' n)) ->
  (* Saturation property of guard G *)
  (forall o (X:SAT),
   isOrd o ->
   inSAT G (piSAT0 (fun x => x ∈ U o) (RT o) (fun x => condSAT (x ∈ T o) (prodSAT X X)))) ->
  inSAT m (piSAT0 (fun o' => o' ∈ osucc o)
    (fun o' => FIX_bot o') (fun o' => FIX_strict (osucc o'))) ->
  inSAT (FIXP G m) (FIX_bot o).
intros FIX_bot FIX_strict oo Tcont Ubot Rirrel Xmono Gsat msat.
assert (Gneutr:  forall o x t (X:SAT),
   isOrd o ->
   x ∈ U o ->
   ~ x ∈ T o ->
   inSAT t (RT o x) ->
   inSAT (App G t) X).
 intros.
 specialize Gsat with (1:=H) (X:=X0).
 specialize piSAT0_elim with (1:=Gsat)(2:=H0)(3:=H2).
 clear Gsat; intros Gsat.
 apply condSAT_neutral with (S:=X0) in Gsat; trivial.
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
 apply msat with (x:=o); auto with *.
  apply lt_osucc; auto.

  apply piSAT0_intro'; intros; [|apply Ubot; trivial].
  apply GUARD_sat.
  eapply prodSAT_elim;[|apply H0].
  eapply prodSAT_elim;[|apply vsat].
  specialize Gsat with (1:=oo)(X:=interSAT(fun S=>S)).
 specialize piSAT0_elim with (1:=Gsat)(2:=H)(3:=H0).
 clear Gsat; intros Gsat.
  apply condSAT_smaller in Gsat.
  specialize prodSAT_elim with (1:=Gsat)(2:=vsat).
  intros.
  apply interSAT_elim with (1:=H1).
elim oo using isOrd_ind; intros.
(*apply piSAT0_intro.
 unfold FIXP.
 eapply sat_sn.  
 eapply prodSAT_intro'.
 intros.
 apply GUARD_sat.

 apply FIXP_sn.
  intros.
  eapply sat_sn.  
  eapply prodSAT_intro'.
  intros.
  apply GUARD_neutral; trivial.
*)
apply piSAT0_intro'; [|apply  Ubot;trivial].
intros x u xty0 ureal.
unfold FIXP.
apply GUARD_sat.
assert (xty:=xty0).
apply Tcont in xty0; trivial.
destruct xty0 as [?|(y',?,?)].
 apply prodSAT_elim with (2:=ureal).
 apply prodSAT_elim with (2:=snSAT_intro H).
 eapply prodSAT_elim;[|apply (snSAT_intro H)].
 apply Gneutr with (1:=H0)(2:=xty)(3:=H3); trivial.

 specialize H2 with (1:=H3).
 assert (isOrd y') by eauto using isOrd_inv.
 assert (zlt : osucc y' ⊆ y).
  red; intros; apply le_lt_trans with y'; auto.
 assert (ureal' : inSAT u (RT (osucc y') x)).
  rewrite <- Rirrel with (3:=H4) in ureal; auto.
 eapply inSAT_context.
  apply inSAT_context.
  intros.
apply prodSAT_elim with S.
eapply condSAT_smaller.
eapply piSAT0_elim with (1:=Gsat _ _ H0) (2:=xty) (3:=ureal).
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
  apply H1; trivial.
 apply piSAT0_elim' in msat; red in msat.
 specialize msat with (1:=H6) (2:=H2).
 apply piSAT0_elim' in msat; red in msat.
 apply msat; trivial.
Qed.
*)


(* no osucc...
Lemma FIXP_sat0 G o T U RT m X :
  let FIX_bot o := piSAT0 (fun n => n ∈ U o) (RT o) (X o) in
  let FIX_strict o := piSAT0 (fun n => n ∈ T o) (RT o) (X o) in
  isOrd o ->
  (* strict domain values form a continuous sequence *)
  (forall y n, isOrd y -> y ⊆ o -> n ∈ U y ->
   eqSAT (RT y n) neuSAT \/ exists2 y', y' ∈ y & n ∈ T (osucc y')) ->
  (* U is not empty *)
  (forall o, isOrd o -> exists w, w ∈ U o) ->
  (* monotonicity of RT and X *)
  (forall y y' n, isOrd y -> isOrd y' -> n ∈ T y -> y ⊆ y' -> y' ⊆ o ->
   eqSAT (RT y n) (RT y' n)) ->
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ T y ->
   inclSAT (X y n) (X y' n)) ->
  (* Saturation property of guard G *)
  (forall t,
   inSAT t neuSAT ->
   inSAT (App G t) (prodSAT snSAT (prodSAT snSAT (prodSAT snSAT neuSAT)))) ->
  (forall o x t m (X:SAT),
   isOrd o -> x ∈ T o ->
   inSAT t (RT o x) ->
   inSAT m X ->
   inSAT (App2 G t m) X) ->
  inSAT m (piSAT0 (fun o' => o' ∈ o)
    (fun o' => FIX_bot o') (fun o' => FIX_strict (osucc o'))) ->
  inSAT (FIXP G m) (FIX_bot o).
intros FIX_bot FIX_strict oo Tcont Ubot Rirrel Xmono Gneutr Gsat msat.
elim oo using isOrd_ind; intros.
apply piSAT0_intro'; [|apply  Ubot;trivial].
intros x u xty0 ureal.
unfold FIXP.

assert (sn (Abs (App (lift 1 m) (App (lift 1 (GUARD G)) (Ref 0))))).
 (* neutral case *)
 eapply sat_sn.
 apply prodSAT_intro with (A:=neuSAT).
 intros v vsat.
 match goal with |- inSAT _ ?T =>
   change (inSAT (App (subst v (lift 1 m)) (App (subst v (lift 1 (GUARD G))) (lift 0 v))) T)
 end.
 unfold subst; rewrite !simpl_subst; trivial.
 rewrite !lift0.
assert (aux : inSAT m (prodSAT (prodSAT neuSAT neuSAT) snSAT)).
admit.
apply prodSAT_elim with (1:=aux).
apply prodSAT_intro'; intros.
apply GUARD_neutral.
 apply sat_sn in vsat; trivial.
 apply Gneutr; trivial.
(* apply piSAT0_elim' in msat; red in msat.
 apply msat with (x:=y); auto with *.
  apply ole_lts; auto.

  apply piSAT0_intro'; intros; [|apply Ubot; trivial].
  apply GUARD_sat.
  eapply prodSAT_elim;[|apply H3].
  eapply prodSAT_elim;[|apply vsat].
  apply Tcont in H2; trivial.
  destruct H2 as [?|(y',?,?)].
   eapply prodSAT_elim;[|apply vsat].
   rewrite H2 in H3.
   specialize Gneutr with (1:=H3).
   revert Gneutr; apply prodSAT_mono; auto with *.
    apply neuSAT_inf.
   apply prodSAT_mono; auto with *.
    apply neuSAT_inf.
   apply prodSAT_mono; auto with *.
    red; red; intros.
    apply sat_sn in H4; trivial.
   apply neuSAT_inf.

   assert (isOrd y') by eauto using isOrd_inv.
   apply Gsat with (2:=H4); auto.
    rewrite Rirrel with (y':=y); auto.
    red; intros; apply le_lt_trans with y'; trivial.

    apply neuSAT_def; trivial.*)
apply GUARD_sat.
apply Tcont in xty0; trivial.
destruct xty0 as [?|(y',?,?)].
 apply prodSAT_elim with (2:=ureal).
 apply prodSAT_elim with (2:=snSAT_intro H2).
 eapply prodSAT_elim;[|apply (snSAT_intro H2)].
 rewrite H3 in ureal.
 specialize Gneutr with (1:=ureal); revert Gneutr.
 apply prodSAT_mono; auto with *.
 apply prodSAT_mono; auto with *.
 apply prodSAT_mono; auto with *.
  red; red; intros.
  apply sat_sn in H4; trivial.
 apply neuSAT_inf.

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
 assert (y' ∈ o).
  apply H0; trivial.
 apply piSAT0_elim' in msat; red in msat.
 specialize msat with (1:=H6) (2:=H1).
 apply piSAT0_elim' in msat; red in msat.
 apply msat; trivial.
Qed.
*)



Lemma FIXP_sat0 G o T U RT m X :
  let FIX_bot o := piSAT0 (fun n => n ∈ U o) (RT o) (X o) in
  let FIX_strict o := piSAT0 (fun n => n ∈ T o) (RT o) (X o) in
  isOrd o ->
  (* strict domain values form a continuous sequence *)
  (forall y n, isOrd y -> y ⊆ o -> n ∈ U y ->
   eqSAT (RT y n) neuSAT \/ exists2 y', y' ∈ y & n ∈ T (osucc y')) ->
  (* U is not empty *)
  (forall o, isOrd o -> exists w, w ∈ U o) ->
  (* monotonicity of RT and X *)
  (forall y y' n, isOrd y -> isOrd y' -> n ∈ T y -> y ⊆ y' -> y' ⊆ o ->
   eqSAT (RT y n) (RT y' n)) ->
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ T y ->
   inclSAT (X y n) (X y' n)) ->
  (* Saturation property of guard G *)
  (forall t,
   inSAT t neuSAT ->
   inSAT (App G t) (prodSAT snSAT (prodSAT snSAT (prodSAT snSAT neuSAT)))) ->
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
 apply prodSAT_intro with (A:=neuSAT).
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
   rewrite H2 in H3.
   specialize Gneutr with (1:=H3).
   revert Gneutr; apply prodSAT_mono; auto with *.
    apply neuSAT_inf.
   apply prodSAT_mono; auto with *.
    apply neuSAT_inf.
   apply prodSAT_mono; auto with *.
    red; red; intros.
    apply sat_sn in H4; trivial.
   apply neuSAT_inf.

   assert (isOrd y') by eauto using isOrd_inv.
   apply Gsat with (2:=H4); auto.
    rewrite Rirrel with (y':=y); auto.
    red; intros; apply le_lt_trans with y'; trivial.

    apply neuSAT_def; trivial.
apply GUARD_sat.
apply Tcont in xty0; trivial.
destruct xty0 as [?|(y',?,?)].
 apply prodSAT_elim with (2:=ureal).
 apply prodSAT_elim with (2:=snSAT_intro H2).
 eapply prodSAT_elim;[|apply (snSAT_intro H2)].
 rewrite H3 in ureal.
 specialize Gneutr with (1:=ureal); revert Gneutr.
 apply prodSAT_mono; auto with *.
 apply prodSAT_mono; auto with *.
 apply prodSAT_mono; auto with *.
  red; red; intros.
  apply sat_sn in H4; trivial.
 apply neuSAT_inf.

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

(* Case when RT is independent from ordinals *)
Lemma FIXP_sat' G o T U RT m X :
  let FIX_bot o := piSAT0 (fun n => n ∈ U o) RT (X o) in
  let FIX_strict o := piSAT0 (fun n => n ∈ T o) RT (X o) in
  isOrd o ->
  (* strict domain values form a continuous sequence *)
  (forall y n, isOrd y -> y ⊆ o -> n ∈ U y ->
   eqSAT (RT n) neuSAT \/ exists2 y', y' ∈ y & n ∈ T (osucc y')) ->
  (* U is not empty *)
  (forall o, isOrd o -> exists w, w ∈ U o) ->
  (* monotonicity of RT and X *)
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ T y ->
   inclSAT (X y n) (X y' n)) ->
  (* Reducibility property of guard G *)
  (forall t,
   inSAT t neuSAT ->
   inSAT (App G t) neuSAT) ->
  (forall o x t m (X:SAT),
   isOrd o -> x ∈ T o ->
   inSAT t (RT x) ->
   inSAT m X ->
   inSAT (App2 G t m) X) ->
  (* Reducibility property of body m *)
  inSAT m (piSAT0 (fun o' => o' ∈ osucc o)
    (fun o' => FIX_bot o') (fun o' => FIX_strict (osucc o'))) ->
  inSAT (FIXP G m) (FIX_bot o).
Proof.
intros FIX_bot FIX_strict oo Tcont Uwit Xmono Gneutr Gsat msat.
apply FIXP_sat0 with (T:=T) (U:=U) (RT:=fun _ => RT); trivial.
reflexivity.
  intros ; apply neuSAT_def; apply Gneutr; trivial.
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

End FIXP_Reducibility.

(** Fixpoint *)

Definition inclFam A (F G:set->SAT) :=
  forall x, x ∈ A -> inclSAT (F x) (G x).

Definition fixSAT (FX:set) (A:(set->SAT)->set->SAT) (x:set) : SAT :=
  interSAT (fun X:{X|Proper(eq_set==>eqSAT)X /\ inclFam FX (A X) X} =>
            proj1_sig X x).

Lemma fixSAT_lower_bound FX A X :
  Proper (eq_set==>eqSAT) X ->
  inclFam FX (A X) X ->
  inclFam FX (fixSAT FX A) X.
red; intros.
red; intros.
apply interSAT_elim with
  (x:=existT (fun X=>Proper (eq_set==>eqSAT) X /\inclFam FX (A X) X)
         X (conj H H0)) in H2; simpl in H2.
trivial.
Qed.

Instance fixSAT_morph0 FX A :
  Proper (eq_set ==> eqSAT) (fixSAT FX A).
do 2 red; intros.
apply interSAT_morph_subset.
 reflexivity.
simpl.
intros X _ (Xm, Xpost).
auto.
Qed.

Instance fixSAT_morph : Proper (eq_set==>
  ((eq_set==>eqSAT)==>eq_set==>eqSAT)==>eq_set==>eqSAT) fixSAT.
do 4 red; intros.
apply interSAT_morph_subset; simpl.
 intros X.
 split; destruct 1; apply and_split; trivial.
  red; red; intros.
  apply H3.
   rewrite H; trivial.
  revert H6; apply H0; auto with *.

  red; red; intros.
  apply H3.
   rewrite <- H; trivial.
  revert H6; apply H0; auto with *.
 intros X (Xm,_) _; auto.
Qed.

Lemma post_fix_lfp FX A :
  (forall X X', inclFam FX X X' -> inclFam FX (A X) (A X')) ->
  inclFam FX (A (fixSAT FX A)) (fixSAT FX A).
intros Amono x tyx.
red; intros.
unfold fixSAT.
eapply interSAT_intro.
 exists (fun _ => snSAT).
 split.
  do 2 red; reflexivity.
 red; red; intros.
 apply snSAT_intro.
 apply sat_sn in H1; trivial.
intros (X,(Xm,Xpost)); simpl. 
apply Xpost; trivial.
apply Amono with (X:=fixSAT FX A); trivial.
apply fixSAT_lower_bound; trivial.
Qed.

Lemma pre_fix_lfp FX A :
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  (forall X X', inclFam FX X X' -> inclFam FX (A X) (A X')) ->
  inclFam FX (fixSAT FX A) (A (fixSAT FX A)).
intros Am Amono.
apply fixSAT_lower_bound; trivial.
 do 2 red; intros.
 apply Am; trivial.
 apply fixSAT_morph0.
apply Amono; trivial.
apply post_fix_lfp; trivial.
Qed.

Lemma fixSAT_eq FX A :
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  (forall X X', inclFam FX X X' -> inclFam FX (A X) (A X')) ->
  forall x, x ∈ FX ->
  eqSAT (fixSAT FX A x) (A (fixSAT FX A) x).
split.
 apply pre_fix_lfp; trivial.
 apply post_fix_lfp; trivial.
Qed.

Lemma fixSAT_outside_domain FX A x S :
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  (forall X X', inclFam FX X X' -> inclFam FX (A X) (A X')) ->
  ~ x ∈ FX ->
  inclSAT (fixSAT FX A x) S.
intros Am Amono.
red; intros.
pose (X:=fun x => condSAT (x ∈ FX) (fixSAT FX A x)).
assert (Xm : Proper (eq_set==>eqSAT) X).
 do 2 red; intros.
 apply condSAT_morph.
  rewrite H1; auto with *.
 apply fixSAT_morph0; trivial.
assert (Xpost : inclFam FX (A X) X).
 clear x H H0.
 red; intros.
 unfold X at 2.
 rewrite condSAT_ok; trivial.
 rewrite fixSAT_eq; auto with *.
 apply Amono; trivial.
 red; intros.
 apply condSAT_smaller.
apply interSAT_elim with
  (x:=existT (fun X=>Proper (eq_set==>eqSAT) X /\inclFam FX (A X) X)
         X (conj Xm Xpost)) in H0; simpl in H0.
revert H0; apply condSAT_neutral; trivial.
Qed.


(** Transfinite iteration *)

Require Import ZFfixrec.
Require Import ZFrelations.
Require Import ZFord ZFfix.

(* –> ZFlambda *)
Lemma sSAT_mt : eqSAT (sSAT empty) neuSAT.
unfold sSAT,complSAT.
apply neuSAT_ext.
red; intros.
assert (h : forall t, sn t -> iLAM t ∈ empty -> inSAT t neuSAT).
 intros.
 apply empty_ax in H1; contradiction.
assert (H' := fun h => interSAT_elim H (exist _ neuSAT h));
   clear H; simpl in H'.
auto.
Qed.

Section SAT_Recursor.

Variable F:set->set.
Hypothesis Fmono : Proper (incl_set==>incl_set) F.
Variable A:(set->SAT)->set->SAT.  
Hypothesis Am : Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A.

Definition tiSAT (o:set) (x:set) : SAT :=
  sSAT (cc_app (REC (fun o' f => cc_lam (TI F (osucc o'))
                                   (fun y => iSAT (A (fun z => sSAT (cc_app f z)) y))) o) x).

Lemma tiSAT_ext1 f o :
  ext_fun (TI F (osucc o)) (fun y => iSAT (A (fun z => sSAT (cc_app f z)) y)).
do 2 red; intros.
apply iSAT_morph.
apply Am; trivial.
red; intros.
apply sSAT_morph.
rewrite H1; reflexivity.
Qed.
Hint Resolve tiSAT_ext1.

Instance tiSAT_morph : Proper (eq_set ==> eq_set ==> eqSAT) tiSAT.
do 3 red; intros.
unfold tiSAT.
apply sSAT_morph.
apply cc_app_morph; trivial.
apply REC_morph; trivial.
do 3 red; intros.
apply cc_lam_ext; auto with *.
 rewrite H1; reflexivity.

 red; intros.
 apply iSAT_morph.
 apply Am; trivial.
 red; intros.
 rewrite H2; rewrite H5; reflexivity.
Qed.

Lemma tiSAT_recursor o :
  (forall R R' o', isOrd o' -> o' ⊆ o ->
   (forall x x', x ∈ TI F o' \/ ~ x ∈ TI F o -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o ->
  recursor o (TI F)
    (fun o f => forall x, x∈TI F o -> cc_app f x == iSAT(sSAT(cc_app f x)))
    (fun o' f => cc_lam (TI F (osucc o')) (fun y => iSAT (A (fun z => sSAT (cc_app f z)) y))).
intros Aext oo.
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
   destruct H5.
    apply sSAT_morph.
    rewrite <- H6.
    apply H3; trivial.

    rewrite cc_app_outside_domain with (x:=x0)(dom:=TI F o0).
     rewrite cc_app_outside_domain with (x:=x')(dom:=TI F o').
      reflexivity.

      apply H2.

      rewrite <- H6.
      intros h; apply H5; revert h; apply TI_mono; auto with *.
      apply H2.

     apply H1.
     intros h; apply H5; revert h; apply TI_mono; auto with *.
      apply H1.
      transitivity o'; trivial.  

  revert H4; apply TI_mono; auto with *.
   apply isOrd_succ; apply H2.
   apply isOrd_succ; apply H1.
   apply osucc_mono; trivial.
    apply H1.
    apply H2.
Qed.

Lemma tiSAT_eq o :
  (forall R R' o', isOrd o' -> o' ⊆ o ->
   (forall x x', x ∈ TI F o' \/ ~ x ∈ TI F o -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o ->
  forall x,
  x ∈ TI F o ->
  eqSAT (tiSAT o x) (A (tiSAT o) x).
intros.
unfold tiSAT.
specialize tiSAT_recursor with (1:=H) (2:=H0); intro rec.
rewrite REC_expand with (1:=H0) (2:=rec) (3:=H1).
rewrite cc_beta_eq.
 rewrite iSAT_id.
 reflexivity.

 do 2 red; intros.
 apply iSAT_morph.
 apply Am; trivial.
 red; intros.
 apply sSAT_morph.
 apply cc_app_morph; trivial.
 reflexivity.

 revert H1; apply TI_incl; auto.
Qed.


Lemma tiSAT_outside_domain o :
  (forall R R' o', isOrd o' -> o' ⊆ o ->
   (forall x x', x ∈ TI F o' \/ ~ x ∈ TI F o -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o ->
  forall x,
  ~ x ∈ TI F o ->
  eqSAT (tiSAT o x) neuSAT.
intros.
specialize tiSAT_recursor with (1:=H) (2:=H0); intro rec.
unfold tiSAT.
rewrite REC_eqn with (2:=rec); trivial.
fold (tiSAT o).
rewrite cc_app_outside_domain with (dom:=TI F o); trivial.
 apply sSAT_mt.

 apply is_cc_fun_lam.
 do 2 red; intros; apply cc_app_morph; auto with *.
Qed.


Lemma tiSAT_mono o1 o2 :
  (forall R R' o', isOrd o' -> o' ⊆ o2 ->
   (forall x x', x ∈ TI F o' \/ ~ x ∈ TI F o2 -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o1 ->
  isOrd o2 ->
  o1 ⊆ o2 ->
  forall x,
  x ∈ TI F o1 ->
  eqSAT (tiSAT o1 x) (tiSAT o2 x).
intros.
specialize tiSAT_recursor with (1:=H) (2:=H1); intro rec.
unfold tiSAT at 2.
rewrite <- REC_ord_irrel with (2:=rec) (o:=o1); auto with *.
reflexivity.
Qed.

Lemma tiSAT_succ_eq o :
  (forall R R' o', isOrd o' -> o' ⊆ osucc o ->
   (forall x x', x ∈ TI F o' \/ ~ x ∈ TI F (osucc o) -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o ->
  forall x,
  x ∈ TI F (osucc o) ->
  eqSAT (tiSAT (osucc o) x) (A (tiSAT o) x).
intros.
rewrite tiSAT_eq; auto.
apply H with o; auto with *.
 red; intros; apply isOrd_trans with o; auto.

 intros.
 assert (o ⊆ osucc o).
  red; intros; apply isOrd_trans with o; auto.
 transitivity (tiSAT o x0);[symmetry|].
  destruct H2.
   apply tiSAT_mono; auto with *.

   rewrite tiSAT_outside_domain; auto.
    rewrite tiSAT_outside_domain; auto with *.

    intros.
    apply H with o'; trivial.  
     transitivity o; trivial.

     intros.
     apply H7; trivial.
     destruct H10; [left|right]; trivial.
     intros h; apply H10; revert h; apply TI_mono; auto with *.

    intros h; apply H2; revert h; apply TI_mono; auto with *.
   
  apply tiSAT_morph; auto with *.
Qed.

End SAT_Recursor.

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
