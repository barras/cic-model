
(** A theory about realizability of natural numbers.
    It is similar to SATnat, but it supports type-based termination
 *)

Require Import ZF ZFpairs ZFsum ZFord ZFfix ZFgrothendieck ZFcoc Sat SATtypes.
Require Import ZFlambda.
Require Import Lambda.
Module Lc:=Lambda.

Set Implicit Arguments.

(** An abstract strong normalization model of natural numbers, set-
    theoretical interpretation. *)
Module Type Nats.

  Parameter zero : set.
  Parameter succ : set -> set.
  Parameter succ_morph : morph1 succ.
  Existing Instance succ_morph.

  (** Constructors produce neutral values *)
  Parameter zero_nmt : ~ zero == empty.
  Parameter succ_nmt : forall n, ~ succ n == empty.
  
  Parameter natcase : set -> (set -> set) -> set -> set.
  Parameter natcase_morph : Proper (eq_set==>(eq_set==>eq_set)==>eq_set==>eq_set) natcase.
  Parameter natcase_zero : forall b0 bS,
      natcase b0 bS zero == b0.
  Parameter natcase_succ : forall n b0 bS,
      morph1 bS ->
      natcase b0 bS (succ n) == bS n.
  Parameter natcase_outside : forall b0 bS n,
      n == empty ->
      natcase b0 bS n == empty.

  Definition isNat X n := n==zero \/ exists2 m, m ∈ cc_bot X & n == succ m.

End Nats.

(** Derived properties *)
Module NatFacts (M:Nats).
Import M.

Lemma isNat_nmt X n : isNat X n -> ~ n == empty.
destruct 1.
 rewrite H; apply zero_nmt.

 destruct H as (m,?,?).
 rewrite H0; apply succ_nmt.
Qed. 

Definition NATf2sum n :=
  natcase (inl empty) inr n.

Instance NATf2sum_morph : morph1 NATf2sum.
do 2 red; intros.
apply natcase_morph; auto with *.
apply inr_morph.
Qed.

Lemma zero_inv_typ : forall n x X,
  isNat X n -> NATf2sum n == inl x ->
  n == zero.
intros.
destruct H as [?|(m,?,?)];[trivial|].
rewrite H1 in H0.
unfold NATf2sum in H0; rewrite natcase_succ in H0; auto with *.
symmetry in H0; apply discr_sum in H0; contradiction.
Qed.
Lemma succ_inv_typ : forall n x X,
  isNat X n -> NATf2sum n == inr x ->
  x ∈ cc_bot X /\ n == succ x.
intros.
destruct H as [?|(m,?,?)].
 rewrite H in H0.
 unfold NATf2sum in H0; rewrite natcase_zero in H0; auto with *.
 apply discr_sum in H0; contradiction.
 rewrite H1 in H0.
 unfold NATf2sum in H0; rewrite natcase_succ in H0; auto with *.
 apply inr_inj in H0.
 rewrite <- H0; auto.
Qed.

Lemma natcase_ext X b0 b0' bS bS' n n' :
 morph1 bS ->
 morph1 bS' ->
 n == empty \/ isNat X n ->
 n == n' ->
 b0 == b0' ->
 ZF.eq_fun (cc_bot X) bS bS' ->
 natcase b0 bS n == natcase b0' bS' n'.
intros mS mS' tyn eqn eq0 eqS.
destruct tyn as [?|[?|(m,tym,?)]].
 rewrite natcase_outside; trivial.
 rewrite natcase_outside.
  reflexivity.
  rewrite <- eqn; trivial.
  
 rewrite <- eqn, H, !natcase_zero; trivial.

 rewrite <- eqn, H, !natcase_succ; trivial.
 apply eqS; auto with *.
Qed.  

End NatFacts.

(** NAT *)

Module Make (M:Nats).
Export M.

Module NF := NatFacts M.
Export NF.

Definition fNAT (A:set->SAT) (n:set) : SAT :=
  condSAT (~ n == empty)
          (sumReal (fun _ => unitSAT) A (NATf2sum n)).

Lemma fNAT_morph :
   Proper ((eq_set ==> eqSAT) ==> eq_set ==> eqSAT) fNAT.
do 3 red; intros.
unfold fNAT.
apply condSAT_morph; auto.
 rewrite H0; reflexivity.
apply sumReal_morph; auto with *.
 red; intros; reflexivity.

 rewrite H0; reflexivity.
Qed.
Hint Resolve fNAT_morph.

Lemma fNAT_mono : monoFam fNAT.
red; red; intros.
unfold fNAT.
apply condSAT_mono.
 red; trivial.
apply sumReal_mono; trivial.
red; reflexivity.
Qed.


Definition ZE := INL ID.

Lemma Real_ZERO_gen A :
  inSAT ZE (fNAT A zero).
unfold fNAT, NATf2sum.
rewrite condSAT_ok.
2:apply zero_nmt.
apply Real_inl with empty.
 do 2 red; reflexivity.

 apply ID_intro.

 apply natcase_zero.
Qed.

Definition SU := INR.


Lemma Real_SUCC_gen A n t :
  Proper (eq_set==>eqSAT) A ->
  inSAT t (A n) ->
  inSAT (SU t) (fNAT A (succ n)).
intros.
unfold fNAT, NATf2sum.
rewrite condSAT_ok.
2:apply succ_nmt.
apply Real_inr with n; trivial.
apply natcase_succ; auto with *.
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
  isNat X n ->
  inSAT nt (fNAT A n) ->
  inSAT ft (C zero) ->
  inSAT gt (piSAT0 (fun x => x ∈ cc_bot X) A (fun x => C (succ x))) ->
  inSAT (NCASE ft gt nt) (C n).
intros Cm nty nreal freal greal.
apply Real_sum_case with (NATf2sum n) (fun _ => unitSAT) A; trivial.
 unfold fNAT in nreal; rewrite condSAT_ok in nreal; eauto.
 apply isNat_nmt in nty ;trivial.
 
 apply piSAT0_intro.
  apply Lc.sn_abs.
  apply Lc.sn_lift.
  apply sat_sn in freal; trivial.

  intros x u eqn ureal.
  apply inSAT_exp; [right; apply sat_sn in ureal;trivial|].
  unfold Lc.subst; rewrite Lc.simpl_subst; auto.
  rewrite Lc.lift0; trivial.

  rewrite zero_inv_typ with (1:=nty) (2:=eqn); trivial.

 apply piSAT0_intro.
  apply sat_sn in greal; trivial.

  intros.
  apply succ_inv_typ with (1:=nty) in H.
  destruct H.
  rewrite H1.
  apply piSAT0_elim with (1:=greal); trivial.
Qed.

Definition cNAT := fixSAT fNAT.

Instance cNAT_morph :
  Proper (eq_set ==> eqSAT) cNAT.
apply fixSAT_morph; auto.
apply fNAT_morph.
Qed.

Lemma cNAT_eq x :
  eqSAT (cNAT x) (fNAT cNAT x).
intros.
apply fixSAT_eq; auto.
apply fNAT_mono.
Qed. 

Lemma cNAT_neutral x :
  x == empty ->
  eqSAT (cNAT x) neuSAT.
intros.
rewrite cNAT_eq.
apply neuSAT_ext.
apply condSAT_neutral; trivial.
intro; auto.
Qed.

Lemma Real_ZERO :
  inSAT ZE (cNAT zero).
intros.
rewrite cNAT_eq; trivial.
apply Real_ZERO_gen.
Qed.

Lemma Real_SUCC n t :
  inSAT t (cNAT n) ->
  inSAT (SU t) (cNAT (succ n)).
intros.
rewrite cNAT_eq.
unfold SU, fNAT.
rewrite condSAT_ok.
2:apply succ_nmt.
apply Real_inr with n; auto with *.
unfold NATf2sum; apply natcase_succ; auto with *.
Qed.

Lemma Real_NATCASE X C n nt ft gt:
  Proper (eq_set ==> eqSAT) C ->
  isNat X n ->
  inSAT nt (cNAT n) ->
  inSAT ft (C zero) ->
  inSAT gt (piSAT0 (fun x => x ∈ cc_bot X) cNAT (fun x => C (succ x))) ->
  inSAT (NCASE ft gt nt) (C n).
intros Cm nty nreal freal greal.
rewrite cNAT_eq in nreal; trivial.
apply Real_NATCASE_gen with (2:=nty) (3:=nreal); auto.
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

Lemma WHEN_SUM_satnat x t m X :
 inSAT t (cNAT x) -> inSAT m X -> inSAT (Lc.App2 WHEN_SUM t m) X.
intros.
rewrite cNAT_eq in H.
apply condSAT_smaller in H; auto.
apply WHEN_SUM_sat with (1:=H); trivial.
Qed.

End Make.
