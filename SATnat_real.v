
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
Qed.
Hint Resolve fNAT_morph.

Lemma sumReal_mono X X' Y Y':
  inclFam X X' ->
  inclFam Y Y' ->
  inclFam (sumReal X Y) (sumReal X' Y').
red; intros.
unfold sumReal.
apply interSAT_mono; intros C.
apply prodSAT_mono.
 red; apply piSAT0_mono with (f:=fun x=>x); auto with *.
apply prodSAT_mono; auto with *.
red; apply piSAT0_mono with (f:=fun x=>x); auto with *.
Qed.
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

Lemma NATFIX_sat o m X U :
  (forall y n, isOrd y -> n ∈ X y -> exists2 y', y' ∈ y & n ∈ X (osucc y'))->
  let FIX_ty o := piSAT0 (fun n => n ∈ cc_bot (X o)) cNAT (U o) in
  let FIX_ty' o := piSAT0 (fun n => n ∈ X o) cNAT (U o) in
  isOrd o ->
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ X y ->
   inclSAT (U y n) (U y' n)) ->
  inSAT m (piSAT0 (fun o' => o' ∈ o)
             (fun o1 => FIX_ty o1) (fun o1 => FIX_ty' (osucc o1))) ->
  inSAT m (prodSAT (FIX_ty empty) snSAT) ->
  inSAT (NATFIX m) (FIX_ty o).
intros Xinv FIX_ty FIX_ty' oo Umono msat mneutr.
apply FIXP_sat
   with (T:=X) (U:=fun o => cc_bot (X o)) (RT:=cNAT); trivial.
 intros.
 apply cc_bot_ax in H1; destruct H1.
  left.
  apply cNAT_neutral; trivial.

  right.
  apply Xinv; trivial.

 exists empty; trivial.

 intros.
 apply neuSAT_def.
 apply WHEN_SUM_neutral; trivial.
 apply neuSAT_def; trivial.

 intros.
 rewrite cNAT_eq in H1.
 apply condSAT_smaller in H1.
 apply WHEN_SUM_sat with (1:=H1) (2:=H2); trivial.
Qed.

Require Import ZFrecbot.  
Lemma NATREC_sat o X F RF U RU natfix :
  morph1 X ->
  (forall o, isOrd o -> X o == sup o (fun o' => X (osucc o'))) ->
  rec X U F natfix o ->
  (forall y n, isOrd y -> n ∈ X y -> exists2 y', y' ∈ y & n ∈ X (osucc y'))->
  Proper (eq_set ==> eq_set ==> eq_set ==> eqSAT) RU ->
  isOrd o ->
  (forall o' o'' x y y',
      isOrd o' ->
      isOrd o'' ->
      o' ⊆ o'' ->
      o'' ⊆ o ->
      x ∈ X o' -> y ∈ U o' x -> y == y' -> inclSAT (RU o' x y) (RU o'' x y')) ->
  let FIX_ty o' f:=
      piSAT0 (fun n => n ∈ cc_bot (X o')) cNAT (fun n => RU o' n (cc_app f n)) in
  (forall o' f u,
      isOrd o' ->
      o' ∈ cc_bot o ->
      f ∈ (Π w ∈ cc_bot (X o'), U o' w) ->
      inSAT u (FIX_ty o' f) -> inSAT (Lc.App RF u) (FIX_ty (osucc o') (F o' f))) ->
  inSAT (NATFIX RF) (FIX_ty o (natfix o)).
intros Xm Xcont isrec Xinv RUm oo RUmono FIX_ty satF.
eapply NATFIX_sat with
   (U:=fun o n => RU o n (cc_app (natfix o) n)); trivial.
{intros.
 apply RUmono; auto.
  apply cc_prod_elim with (dom := cc_bot (X y)) (F := U y); auto.
  apply rec_typ with (1:=isrec); auto.
  transitivity y'; trivial.

  apply rec_irr with (3:=isrec); auto. }
{apply piSAT0_intro.
  assert (inSAT (Lc.App RF daimon) (FIX_ty (osucc empty) (F empty (natfix empty)))).
   apply satF; auto.
    apply rec_typ with (1:=isrec); auto.
    apply varSAT.
  apply sat_sn in H.
  apply Lc.subterm_sn with (Lc.App RF daimon); auto.
 intros.
 assert (xo : isOrd x) by eauto using isOrd_inv.
 assert (Wty : natfix x ∈ Π w ∈ cc_bot (X x), U x w).
  apply rec_typ with (1:=isrec); trivial.
  red; intros; apply isOrd_trans with x; auto.
 specialize satF with (1:=xo)(2:=cc_bot_intro _ _ H)(3:=Wty)(4:=H0).
 revert satF; apply piSAT0_mono with (f:=fun x=>x); auto with *.
 intros.
 rewrite rec_eqn_succ with (2:=isrec); auto with *. }

{apply prodSAT_intro'; intros.
 assert (inSAT (Lc.App RF v) (FIX_ty (osucc empty) (F empty (natfix empty)))).
  apply satF; auto.
  apply rec_typ with (1:=isrec); auto.

  apply snSAT_intro.
  apply sat_sn with (1:=H0). }
Qed.

End Make.
