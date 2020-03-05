
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
Module Type SizedNats.
  Parameter NATf': set -> set.
  Parameter NATf'_mono : Proper (incl_set ==> incl_set) NATf'.
  Existing Instance NATf'_mono.

  Parameter zero : set.
  Parameter succ : set -> set.
  Parameter succ_morph : morph1 succ.
  Existing Instance succ_morph.

  (** Constructors produce non-neutral values *)
  Parameter zero_typ : forall X, zero ∈ NATf' X.
  Parameter succ_typ : forall X n, n ∈ cc_bot X -> succ n ∈ NATf' X.

  Parameter NATf'_elim : forall n X,
    n ∈ NATf' X ->
    n == zero \/ exists2 x, x ∈ cc_bot X & n == succ x.
  Parameter neutr_dec' : forall n o,
    isOrd o ->
    n ∈ cc_bot (TI NATf' o) ->
    n ∈ TI NATf' o \/ ~ exists Y, n ∈ NATf' Y.

  Parameter NAT_eqn : TI NATf' omega == NATf' (TI NATf' omega).

  Parameter G_NATf' : forall U X,
    grot_univ U ->
    X ∈ U -> NATf' X ∈ U.

Parameter natcase : set -> (set -> set) -> set -> set.
Parameter natcase_morph : Proper (eq_set==>(eq_set==>eq_set)==>eq_set==>eq_set) natcase.
Parameter natcase_zero : forall b0 bS,
  natcase b0 bS zero == b0.
Parameter natcase_succ : forall n b0 bS,
  morph1 bS ->
  natcase b0 bS (succ n) == bS n.
Parameter natcase_outside : forall b0 bS n,
  (forall X, ~ n ∈ NATf' X) ->
  natcase b0 bS n == empty.

Parameter natfix : (set -> set -> set) -> set -> set.
Parameter natfix_morph : Proper ((eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) natfix.

(*Parameter natfix_hyps : set -> (set -> set -> set) -> (set -> set -> set) -> Prop.*)
Require Import ZFfunext.
  Record natfix_hyps O M U : Prop := natfix_intro {
    Wo : isOrd O;
    WMm : morph2 M;
    WUm : morph2 U;
    WU_mt : forall o x, empty ∈ U o x;
    WMtyp : forall o,
        o ∈ osucc O ->
        forall f,
        f ∈ (Π x ∈ cc_bot (TI NATf' o), U o x) ->
        M o f
        ∈ (Π x ∈ cc_bot (TI NATf' (osucc o)), U (osucc o) x);
    WMirr : forall o o' f g,
        isOrd o ->
        o ⊆ o' ->
        o' ∈ osucc O ->
        f ∈ (Π x ∈ cc_bot (TI NATf' o), U o x) ->
        g ∈ (Π x ∈ cc_bot (TI NATf' o'), U o' x) ->
        fcompat (cc_bot (TI NATf' o)) f g ->
        fcompat (cc_bot (TI NATf' (osucc o))) (M o f) (M o' g);
    WUmono : forall o o' x,
        isOrd o ->
        o ⊆ o' ->
        o' ∈ osucc O ->
        x ∈ cc_bot (TI NATf' o) ->
        U o x ⊆ U o' x
  }.

  Parameter natfix_typ : forall O M U,
    natfix_hyps O M U ->
    forall o, isOrd o -> o ⊆ O ->
    natfix M o ∈ (Π x ∈ cc_bot (TI NATf' o), U o x).
  Parameter natfix_irr : forall O M U,
    natfix_hyps O M U ->
    forall o o' x, isOrd o -> isOrd o' -> o ⊆ o' -> o' ⊆ O ->
    x ∈ cc_bot (TI NATf' o) ->
    cc_app (natfix M o) x == cc_app (natfix M o') x.
  Parameter natfix_eqn : forall O M U,
    natfix_hyps O M U ->
    forall o n, isOrd o -> o ⊆ O ->
    n ∈ TI NATf' o ->
    cc_app (natfix M o) n == cc_app (M o (natfix M o)) n.
(*  Parameter natfix_def : forall O M U,
    natfix_hyps O M U ->
    forall o n, isOrd o -> o ∈ O ->
    n ∈ TI NATf' (osucc o) ->
    cc_app (natfix M (osucc o)) n == cc_app (M o (natfix M o)) n.*)
  Parameter natfix_strict : forall O M U n,
    natfix_hyps O M U ->
    ~ (exists X, n ∈ NATf' X) ->
    forall o,
       isOrd o -> o ⊆ O -> cc_app (natfix M o) n == empty.


End SizedNats.

(** Derived properties *)
Module NatFacts (M:SizedNats).
Import M.


Definition NATf2sum n :=
  natcase (inl empty) inr n.

Instance NATf2sum_morph : morph1 NATf2sum.
do 2 red; intros.
apply natcase_morph; auto with *.
apply inr_morph.
Qed.

Lemma zero_inv_typ : forall n x X,
  n ∈ NATf' X -> NATf2sum n == inl x ->
  n == zero.
intros.
apply NATf'_elim in H; destruct H; trivial.
destruct H.
rewrite H1 in H0.
unfold NATf2sum in H0; rewrite natcase_succ in H0; auto with *.
symmetry in H0; apply discr_sum in H0; contradiction.
Qed.
Lemma succ_inv_typ : forall n x X,
  n ∈ NATf' X -> NATf2sum n == inr x ->
  x ∈ cc_bot X /\ n == succ x.
intros.
apply NATf'_elim in H; destruct H; trivial.
 rewrite H in H0.
 unfold NATf2sum in H0; rewrite natcase_zero in H0.
 apply discr_sum in H0; contradiction.

 destruct H.
 rewrite H1 in H0.
 unfold NATf2sum in H0; rewrite natcase_succ in H0; auto with *.
 apply inr_inj in H0.
 rewrite <- H0; auto.
Qed.

Lemma natcase_ext o b0 b0' bS bS' n n' :
 morph1 bS ->
 morph1 bS' ->
 isOrd o ->
 n ∈ cc_bot (TI NATf' (osucc o)) ->
 n == n' ->
 b0 == b0' ->
 ZF.eq_fun (cc_bot (TI NATf' o)) bS bS' ->
 natcase b0 bS n == natcase b0' bS' n'.
intros.
rewrite <- H3.
apply neutr_dec' in H2; auto.
destruct H2.
 rewrite TI_mono_succ in H2; auto with *.
 apply NATf'_elim in H2.
 destruct H2 as [?|(m,?,?)].
  rewrite H2, !natcase_zero; trivial.

  rewrite H6, !natcase_succ; auto with *.

 rewrite natcase_outside.
 rewrite natcase_outside.
  reflexivity.

  red; intros; apply H2; econstructor; eauto.
  red; intros; apply H2; econstructor; eauto.
Qed.

Require Import ZFfunext.

Lemma natfix_ext F F' U U' o o' :
  isOrd o ->
  isOrd o' ->
  o ⊆ o' ->
  natfix_hyps o F U ->
  natfix_hyps o' F' U' ->
  (forall z, isOrd z -> z ⊆ o ->
   forall f f',
   f ∈ (Π x ∈ cc_bot (TI NATf' z), U z x) ->
   f' ∈ (Π x ∈ cc_bot (TI NATf' o'), U' o' x) ->
   fcompat (cc_bot (TI NATf' z)) f f' ->
   fcompat (TI NATf' (osucc z)) (F z f) (F' o' f')) -> 
  fcompat (cc_bot (TI NATf' o)) (natfix F o) (natfix F' o').
intros oo oo' ole oko oko' eqF.
elim oo using isOrd_ind; intros.
red; intros.
apply neutr_dec' in H2; trivial.
destruct H2.
 apply TI_inv in H2; auto with *.
 destruct H2 as (o'',?,?).
 assert (o_o'' : isOrd o'') by eauto using isOrd_inv.
 assert (o''_y : osucc o'' ⊆ y).
  red; intros; apply le_lt_trans with o''; auto.
 rewrite natfix_eqn with (1:=oko'); auto with *.
  transitivity (cc_app (F o'' (natfix F o'')) x).
   rewrite natfix_eqn with (1:=oko); auto with *.
    symmetry; apply (WMirr oko); auto with *.
     apply ole_lts; trivial.
     apply natfix_typ with (1:=oko); auto with *.
     apply natfix_typ with (1:=oko); auto with *.

     red; intros.
     apply natfix_irr with (1:=oko); auto with *.

    revert H3; apply TI_mono; auto with *.

   red in eqF; apply eqF; auto with *.
    apply natfix_typ with (1:=oko); auto with *.
    apply natfix_typ with (1:=oko'); auto with *.

  revert H3; apply TI_mono; auto with *.
  transitivity y; trivial.
  transitivity o; trivial.

 rewrite natfix_strict with (1:=oko); auto with *.
 rewrite natfix_strict with (1:=oko'); auto with *.
Qed.

End NatFacts.

(** NAT *)

Module Make (M:SizedNats).
Export M.

Module NF := NatFacts M.
Export NF.

Definition fNAT (A:set->SAT) (n:set) : SAT :=
  condSAT (exists X, n ∈ NATf' X)
          (sumReal (fun _ => unitSAT) A (NATf2sum n)).

Lemma fNAT_morph :
   Proper ((eq_set ==> eqSAT) ==> eq_set ==> eqSAT) fNAT.
do 3 red; intros.
unfold fNAT.
apply condSAT_morph; auto.
 apply ex_morph.
 red; intros; rewrite H0; reflexivity.
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
2:exists empty; apply zero_typ.
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
2:exists (singl n); apply succ_typ; apply cc_bot_intro; apply singl_intro.
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
  n ∈ NATf' X ->
  inSAT nt (fNAT A n) ->
  inSAT ft (C zero) ->
  inSAT gt (piSAT0 (fun x => x ∈ cc_bot X) A (fun x => C (succ x))) ->
  inSAT (NCASE ft gt nt) (C n).
intros Cm nty nreal freal greal.
apply Real_sum_case with (NATf2sum n) (fun _ => unitSAT) A; trivial.
 unfold fNAT in nreal; rewrite condSAT_ok in nreal; eauto.

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

Hint Resolve NATf'_mono.

Lemma cNAT_eq x :
  eqSAT (cNAT x) (fNAT cNAT x).
intros.
apply fixSAT_eq; auto.
apply fNAT_mono.
Qed. 

Lemma cNAT_neutral x :
  ~ (exists X, x ∈ NATf' X) ->
  eqSAT (cNAT x) neuSAT.
intros.
rewrite cNAT_eq.
apply neuSAT_ext.
apply condSAT_neutral; trivial.
Qed.

Lemma Real_ZERO :
  inSAT ZE (cNAT zero).
intros.
rewrite cNAT_eq; trivial.
apply Real_ZERO_gen.
Qed.

Lemma Real_SUCC o n t :
  isOrd o ->
  n ∈ cc_bot (TI NATf' o) ->
  inSAT t (cNAT n) ->
  inSAT (SU t) (cNAT (succ n)).
intros.
rewrite cNAT_eq.
unfold SU, fNAT.
rewrite condSAT_ok.
2:exists (TI NATf' o); apply succ_typ; trivial.
apply Real_inr with n; auto with *.
unfold NATf2sum; apply natcase_succ; auto with *.
Qed.

Lemma Real_NATCASE o C n nt ft gt:
  isOrd o ->
  Proper (eq_set ==> eqSAT) C ->
  n ∈ TI NATf' (osucc o) ->
  inSAT nt (cNAT n) ->
  inSAT ft (C zero) ->
  inSAT gt (piSAT0 (fun x => x ∈ cc_bot (TI NATf' o)) cNAT (fun x => C (succ x))) ->
  inSAT (NCASE ft gt nt) (C n).
intros oo Cm nty nreal freal greal.
rewrite cNAT_eq in nreal; trivial.
rewrite TI_mono_succ in nty; auto.
apply Real_NATCASE_gen with (2:=nty) (3:=nreal); auto.
Qed.


(** Introducing the fixpoint of NATf' *)

Definition NAT' := TI NATf' omega.

Lemma Real_SUCC_cNAT n t :
  n ∈ cc_bot NAT' ->
  inSAT t (cNAT n) ->
  inSAT (SU t) (cNAT (succ n)).
intros.
apply Real_SUCC with (o:=omega); auto.
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

Lemma NATFIX_sat o m X :
  let FIX_ty o := piSAT0 (fun n => n ∈ cc_bot (TI NATf' o)) cNAT (X o) in
  let FIX_ty' o := piSAT0 (fun n => n ∈ TI NATf' o) cNAT (X o) in
  isOrd o ->
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ TI NATf' y ->
   inclSAT (X y n) (X y' n)) ->
  inSAT m (piSAT0 (fun o' => o' ∈ o)
             (fun o1 => FIX_ty o1) (fun o1 => FIX_ty' (osucc o1))) ->
  inSAT m (prodSAT (FIX_ty empty) snSAT) ->
  inSAT (NATFIX m) (FIX_ty o).
intros FIX_ty FIX_ty' oo Xmono msat mneutr.
apply FIXP_sat
   with (T:=TI NATf') (U:=fun o => cc_bot (TI NATf' o)) (RT:=cNAT); trivial.
 intros.
 apply neutr_dec' in H1; trivial.
 destruct H1.
  right.
  apply TI_elim in H1; auto with *.
  destruct H1 as (z,zty,xty).
  exists z; trivial.
  rewrite TI_mono_succ; auto with *.
  apply isOrd_inv with y; trivial.

  left; apply cNAT_neutral; trivial.

 exists empty; trivial.

 intros.
 apply neuSAT_def.
 apply WHEN_SUM_neutral; trivial.
 apply neuSAT_def; trivial.

 intros.
 apply TI_elim in H0; auto with *.
 destruct H0 as (z,zty,xty).
 assert (oz: isOrd z).
  apply isOrd_inv with o0; auto.
 assert (xty' := xty).
 rewrite <-TI_mono_succ in xty'; auto.
 rewrite cNAT_eq in H1.
 apply condSAT_smaller in H1.
 apply WHEN_SUM_sat with (1:=H1) (2:=H2); trivial.
Qed.

Lemma NATREC_sat o F RF U RU :
  Proper (eq_set ==> eq_set ==> eq_set ==> eqSAT) RU ->
  isOrd o ->
  natfix_hyps o F U ->
  (forall o' o'' x y y',
      isOrd o' ->
      isOrd o'' ->
      o' ⊆ o'' ->
      o'' ⊆ o ->
      x ∈ TI NATf' o' -> y ∈ U o' x -> y == y' -> inclSAT (RU o' x y) (RU o'' x y')) ->
  let FIX_ty o' f:=
      piSAT0 (fun n => n ∈ cc_bot (TI NATf' o')) cNAT (fun n => RU o' n (cc_app f n)) in
  (forall o' f u,
      isOrd o' ->
      o' ∈ cc_bot o ->
      f ∈ (Π w ∈ cc_bot (TI NATf' o'), U o' w) ->
      inSAT u (FIX_ty o' f) -> inSAT (Lc.App RF u) (FIX_ty (osucc o') (F o' f))) ->
  inSAT (NATFIX RF) (FIX_ty o (natfix F o)).
intros RUm oo ty RUmono FIX_ty satF.
eapply NATFIX_sat with
   (X:=fun o n => RU o n (cc_app (natfix F o) n)); trivial.
 intros.
 apply RUmono; auto.
  apply cc_prod_elim with (dom := cc_bot (TI NATf' y)) (F := U y); auto.
  apply natfix_typ with (1:=ty); trivial.
  transitivity y'; trivial.

  eapply natfix_irr with (1:=ty); auto.

 apply piSAT0_intro.
  assert (inSAT (Lc.App RF daimon) (FIX_ty (osucc empty) (F empty (natfix F empty)))).
  apply satF; auto.
   apply natfix_typ with (1:=ty); auto.

   apply varSAT.

  apply sat_sn in H.
  apply Lc.subterm_sn with (Lc.App RF daimon); auto.
 intros.
 assert (xo : isOrd x) by eauto using isOrd_inv.
(* apply olts_le in H.*)
 assert (Wty : natfix F x ∈ Π w ∈ cc_bot (TI NATf' x), U x w).
  apply natfix_typ with (1:=ty); trivial.
  red; intros; apply isOrd_trans with x; auto.
 specialize satF with (1:=xo)(2:=cc_bot_intro _ _ H)(3:=Wty)(4:=H0).
 revert satF; apply piSAT0_mono with (f:=fun x=>x); auto with *.
 intros.
 rewrite natfix_eqn with (1:=ty); auto with *.
 2:red; intros; apply le_lt_trans with x; auto.
 assert (aux := WMirr ty).
 red in aux.
 rewrite aux with (o':=osucc x) (g:=natfix F (osucc x)); auto.
  reflexivity.

  red; intros; apply isOrd_trans with x; auto.

  apply lt_osucc_compat; auto.

  apply natfix_typ with (1:=ty); auto.
  red; intros; apply le_lt_trans with x; auto.

  red; intros.
  apply natfix_irr with (1:=ty); auto.
   red; intros; apply isOrd_trans with x; auto.

   red; intros; apply le_lt_trans with x; auto.

 apply prodSAT_intro'; intros.
 assert (inSAT (Lc.App RF v) (FIX_ty (osucc empty) (F empty (natfix F empty)))).
  apply satF; auto.
  apply natfix_typ with (1:=ty); auto.

  apply snSAT_intro.
  apply sat_sn with (1:=H0).
Qed.

End Make.
