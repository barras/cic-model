
Require Import ZF ZFpairs ZFsum ZFord ZFfix ZFind_nat Sat SATtypes.
Require Import ZFlambda.
Require Import Lambda.
Module Lc:=Lambda.

Set Implicit Arguments.

(** NAT *)

Definition fNAT (A:set->SAT) : set->SAT :=
  sumReal (fun _ => unitSAT) A.

Lemma fNAT_morph :
   Proper ((eq_set ==> eqSAT) ==> eq_set ==> eqSAT) fNAT.
do 3 red; intros.
unfold fNAT.
unfold sumReal.
apply interSAT_morph.
apply indexed_relation_id.
intros.
apply prodSAT_morph.
 unfold depSAT.
 apply interSAT_morph_subset; intros; auto with *.
 rewrite H0; reflexivity.

 apply prodSAT_morph; auto with *.
 unfold depSAT.
 apply interSAT_morph_subset; simpl; intros; auto with *.
  rewrite H0; reflexivity.

  apply prodSAT_morph; auto with *.
Qed.
Hint Resolve fNAT_morph.

Lemma fNAT_irrel (R R' : set -> SAT) (o : set) :
 isOrd o ->
 (forall x x' : set, x ∈ TI NATf o -> x == x' -> eqSAT (R x) (R' x')) ->
 forall x x' : set,
 x ∈ TI NATf (osucc o) -> x == x' -> eqSAT (fNAT R x) (fNAT R' x').
intros.
unfold fNAT.
apply interSAT_morph.
apply indexed_relation_id; intro C.
apply prodSAT_morph.
 apply interSAT_morph_subset; simpl; intros; auto with *.
 rewrite H2; reflexivity.

 apply prodSAT_morph; auto with *.
 apply interSAT_morph_subset; simpl; intros; auto with *.
  rewrite H2; reflexivity.

  apply prodSAT_morph; auto with *.
  apply H0; auto with *.
  rewrite TI_mono_succ in H1; auto.
  rewrite Px in H1; apply sum_inv_r in H1; trivial.
Qed.

Lemma Real_ZERO_gen A :
  inSAT (INL ID) (fNAT A ZERO).
apply Real_inl.
 do 2 red; reflexivity.

 apply ID_intro.
Qed.

Lemma Real_SUCC_gen A n t :
  Proper (eq_set==>eqSAT) A ->
  inSAT t (A n) ->
  inSAT (INR t) (fNAT A (SUCC n)).
intros.
apply Real_inr; trivial.
Qed.

Definition NCASE f g n := Lc.App2 n (Lc.Abs (Lc.lift 1 f)) g.

Lemma Real_NATCASE_gen X A C n nt ft gt:
  Proper (eq_set ==> eqSAT) C ->
  n ∈ NATf X ->
  inSAT nt (fNAT A n) ->
  inSAT ft (C ZERO) ->
  inSAT gt (piSAT0 (fun x => x ∈ X) A (fun x => C (SUCC x))) ->
  inSAT (NCASE ft gt nt) (C n).
intros Cm nty nreal freal greal.
apply Real_sum_case with ZFind_basic.UNIT X n (fun _ => unitSAT) A; trivial.
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

Definition fNATi o := tiSAT NATf fNAT o.

Instance fNATi_morph :
  Proper (eq_set ==> eq_set ==> eqSAT) fNATi.
apply tiSAT_morph; auto.
Qed.

Lemma fNATi_mono o1 o2:
  isOrd o1 ->
  isOrd o2 ->
  o1 ⊆ o2 ->
  forall x,
  x ∈ NATi o1 ->
  eqSAT (fNATi o1 x) (fNATi o2 x).
intros.
apply tiSAT_mono; trivial.
intros; apply fNAT_irrel with (o:=o'); trivial.
Qed.

Lemma fNATi_succ_eq o x :
  isOrd o ->
  x ∈ NATi (osucc o) ->
  eqSAT (fNATi (osucc o) x) (fNAT (fNATi o) x).
intros.
apply tiSAT_succ_eq; auto.
intros; apply fNAT_irrel with (o:=o'); trivial.
Qed.

Lemma fNATi_fix x :
  x ∈ NAT ->
  eqSAT (fNATi omega x) (fNAT (fNATi omega) x).
intros.
apply tiSAT_eq; auto with *.
intros; apply fNAT_irrel with (o:=o'); trivial.
Qed.

Lemma Real_ZERO o :
  isOrd o ->
  inSAT (INL ID) (fNATi (osucc o) ZERO).
intros.
rewrite fNATi_succ_eq; trivial.
 apply Real_ZERO_gen.

 apply ZEROi_typ; trivial.
Qed.

Lemma Real_SUCC o n t :
  isOrd o ->
  n ∈ NATi o ->
  inSAT t (fNATi o n) ->
  inSAT (INR t) (fNATi (osucc o) (SUCC n)).
intros.
rewrite fNATi_succ_eq; trivial.
 apply Real_inr; trivial.
 apply fNATi_morph; reflexivity.

 apply SUCCi_typ; trivial.
Qed.


Lemma Real_NATCASE o C n nt ft gt:
  isOrd o ->
  Proper (eq_set ==> eqSAT) C ->
  n ∈ NATi (osucc o) ->
  inSAT nt (fNATi (osucc o) n) ->
  inSAT ft (C ZERO) ->
  inSAT gt (piSAT0 (fun x => x ∈ NATi o) (fNATi o) (fun x => C (SUCC x))) ->
  inSAT (NCASE ft gt nt) (C n).
intros oo Cm nty nreal freal greal.
rewrite fNATi_succ_eq in nreal; trivial.
unfold NATi in nty; rewrite TI_mono_succ in nty; auto.
apply Real_NATCASE_gen with (2:=nty) (3:=nreal); auto.
Qed.

(* TODO: reduction of NCASE *)

(** * Structural fixpoint: *)

(** NATFIX m n --> m (NATFIX m) n when n is a (sum) constructor.
   let G m := "\n. (match n with inl _ => m | inr _ => m end) m n"
   let G m := \n. n (\_.m) (\_.m) m n
    G m -/-> ; G m (inl a) --> m m (inl a); G m (inr b) --> m m (inr b)
   NATFIX m n := G (\x. m (G x)) n
     --> (\x. m (G x)) (\x. m (G x)) n
     --> m (G (\x. m (G x))) n == m (NATFIX m) n
 *)

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

(*
Definition guard_couple m :=
  Lc.Abs (Lc.App2 (Lc.App (Lc.Ref 0) (Lc.Abs (Lc.Abs (Lc.lift 3 m)))) (Lc.lift 1 m) (Lc.Ref 0)).

(** (G m n) reduces to (m m n) when n is a constructor. Note that
    n need not be closed. *)
Lemma G_sim : forall m n,
  (exists t1 t2, n = Lc.Abs (Lc.App2 (Lc.Ref 0) t1 t2)) ->
  Lc.redp (Lc.App (guard_couple m) n) (Lc.App2 m m n).
intros m n (t1,(t2,eqn)).
unfold guard_couple.
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
 apply Lc.beta.
unfold Lc.subst; simpl.
rewrite Lc.lift0.
eapply t_trans.
 apply t_step.
 apply Lc.app_red_l.
 apply Lc.beta.
unfold Lc.subst; simpl.
rewrite Lc.simpl_subst; auto.
apply t_step.
apply Lc.red1_beta.
unfold Lc.subst; simpl.
rewrite Lc.simpl_subst; auto.
rewrite Lc.lift0; trivial.
Qed.
*)

Lemma G_sat A k m t X :
  k ∈ NAT ->
  inSAT t (fNAT A k) ->
  inSAT (Lc.App2 m m t) X ->
  inSAT (Lc.App (guard_sum m) t) X.
intros.
unfold guard_sum.
apply inSAT_exp; intros.
 right; apply sat_sn in H0; trivial.
unfold Lc.subst; simpl Lc.subst_rec.
repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
revert X H1; apply inSAT_context.
apply inSAT_context.
intros.
apply Real_NATCASE_gen with (X:=NAT) (A:=A) (C:=fun _ => S) (n:=k); auto.
 do 2 red; reflexivity.

 rewrite NAT_eq in H; trivial.

 apply piSAT0_intro; intros.
  apply Lc.sn_abs.
  apply Lc.sn_lift.
  apply sat_sn in H1; trivial.

  apply inSAT_exp;[right;apply sat_sn in H3; trivial|].
  unfold Lc.subst; simpl Lc.subst_rec.
  rewrite Lc.simpl_subst; auto.
  rewrite Lc.lift0; trivial.
Qed.

Lemma sn_G_inv m : Lc.sn (guard_sum m) -> Lc.sn m.
intros.
unfold guard_sum in H.
eapply subterm_sn in H;[|constructor].
eapply subterm_sn in H;[|apply sbtrm_app_l].
eapply subterm_sn in H;[|apply sbtrm_app_r].
apply sn_lift_inv with (1:=H) (2:=eq_refl).
Qed.


Definition NATFIX m :=
  guard_sum (Lc.Abs (Lc.App  (Lc.lift 1 m) (guard_sum (Lc.Ref 0)))).

(** NATFIX reduces as a fixpoint combinator when applied to a constructor *)
Lemma NATFIX_sim : forall m n,
  (exists t c, (c=0\/c=1) /\ n = Lc.Abs (Lc.Abs (Lc.App (Lc.Ref c) t))) ->
  Lc.redp (Lc.App (NATFIX m) n) (Lc.App2 m (NATFIX m) n).
intros.
unfold NATFIX at 1.
eapply t_trans.
 apply G_sim; trivial.
apply Lc.redp_app_l.
apply t_step.
apply Lc.red1_beta.
set (t1 := Lc.Abs (Lc.App (Lc.lift 1 m) (guard_sum (Lc.Ref 0)))).
unfold Lc.subst; simpl.
rewrite Lc.simpl_subst; auto.
rewrite Lc.lift0.
reflexivity.
Qed.

(** The guard is needed mainly here: NATFIX m does not reduce *)
Lemma sn_natfix o m X B:
  isOrd o ->
  inSAT m (piSAT0 (fun o' => o' ∈ osucc o)
        (fun o1 => piSAT0 (fun n => n ∈ NATi o1) (fNATi o1) (X o1)) B) ->
  sn (NATFIX m).
intros.
assert (empty ∈ osucc o).
 apply isOrd_plump with o; auto with *.
  red; intros.
  apply empty_ax in H1; contradiction.
  apply lt_osucc; trivial.
unfold NATFIX.
assert (sn (Lc.Abs (Lc.App (Lc.lift 1 m) (guard_sum (Lc.Ref 0))))).
 apply sn_abs.
 assert (inSAT (guard_sum (Lc.Ref 0)) (piSAT0(fun n => n ∈ NATi empty) (fNATi empty) (X empty))).
  apply piSAT0_intro; intros.
   apply sn_abs.
   constructor; intros.
   apply nf_norm in H2; try contradiction.
   repeat constructor.

   eapply G_sat with (A:=fNATi empty) (k:=x).
    revert H2; apply NATi_NAT; auto with *.

    unfold fNATi.
    rewrite <- tiSAT_succ_eq; auto.
     2:intros; apply fNAT_irrel with (o:= o'); trivial.
     2:revert H2; apply TI_incl; auto.
    rewrite fNATi_mono with (o2:=osucc empty) in H3; auto.
    red; intros.
    apply empty_ax in H4; contradiction.

    eapply prodSAT_elim; [|eexact H3].
    apply prodSAT_elim with snSAT;apply varSAT.

 specialize piSAT0_elim with (1:=H0)(2:=H1)(3:=H2); intro.
 apply sat_sn in H3; trivial.
 apply sn_subst with (Ref 0).
 unfold Lc.subst; simpl.
 rewrite simpl_subst; auto.
 rewrite lift0; auto.

apply sn_abs.
apply prodSAT_elim with (A:=snSAT) (B:=snSAT).
2:simpl; auto with *.
apply prodSAT_elim with (A:=snSAT).
 apply prodSAT_elim with (A:=snSAT).
  apply prodSAT_elim with (A:=snSAT).
   apply varSAT.
   apply sn_abs; apply sn_lift; trivial.
  apply sn_abs; apply sn_lift; trivial.
 apply sn_lift; trivial.
Qed.

Lemma NATFIX_sat : forall o m X,
  isOrd o ->
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ NATi y ->
   inclSAT (X y n) (X y' n)) ->
  inSAT m (piSAT0 (fun o' =>o' ∈ osucc o) 
             (fun o1 => piSAT0 (fun n => n ∈ NATi o1) (fNATi o1) (X o1))
             (fun o1 => let o2 := osucc o1 in
                        piSAT0 (fun n => n ∈ NATi o2) (fNATi o2) (X o2))) ->
  inSAT (NATFIX m) (piSAT0 (fun n => n ∈ NATi o) (fNATi o) (X o)).
intros o m X oo Xmono msat.
elim oo using isOrd_ind; intros.
apply piSAT0_intro.
 apply sn_natfix with (o:=o) (X:=X) (2:=msat); trivial.

intros x u xty0 ureal.
assert (tyx : x ∈ NAT).
 apply NATi_NAT with y; trivial.
apply TI_elim in xty0; auto with *.
destruct xty0 as (z,?,?).
specialize H1 with (1:=H2).
assert (zo : isOrd z).
 apply isOrd_inv with y; trivial.
unfold NATFIX.
rewrite <- ZFfix.TI_mono_succ in H3; auto with *.
assert (ureal' : inSAT u (fNAT (fNATi z) x)).
 rewrite <- fNATi_succ_eq; trivial.
 rewrite fNATi_mono with (o2:=y); auto.
 red; intros.
 apply isOrd_plump with z; trivial.
  apply isOrd_inv with (osucc z); auto.
  apply olts_le in H4; trivial.
apply G_sat with (2:=ureal'); trivial.
eapply inSAT_context; intros.
 apply inSAT_exp.
  left; simpl.
  apply Bool.orb_true_r.

  unfold Lc.subst; simpl Lc.subst_rec.
  repeat rewrite Lc.simpl_subst; auto.
  rewrite Lc.lift0.
  change (inSAT (Lc.App m (NATFIX m)) S).
  eexact H4.
rewrite <- fNATi_succ_eq in ureal'; trivial.
apply Xmono with (osucc z); eauto using isOrd_inv.
 red; intros.
 apply isOrd_plump with z; trivial.
  eauto using isOrd_inv.
  apply olts_le; trivial.
assert (z ∈ osucc o).
 apply isOrd_trans with o; auto.
 apply H0; trivial.
assert (h := piSAT0_elim _ _ msat H4 H1).
apply (piSAT0_elim _ _ h H3 ureal').
Qed.
