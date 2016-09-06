
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
(*Parameter neutr_dec : forall n X,
  n ∈ cc_bot (NATf' X) ->
  n ∈ NATf' X \/ ~ exists Y, n ∈ NATf' Y.*)
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
  Parameter natfix_unfold : forall O M U,
    natfix_hyps O M U ->
    forall o n, isOrd o -> o ⊆ O ->
    n ∈ TI NATf' (osucc o) ->
    cc_app (natfix M (osucc o)) n == cc_app (M o (natfix M o)) n.
  Parameter natfix_strict : forall O M U n,
    natfix_hyps O M U ->
    ~ (exists X, n ∈ NATf' X) ->
    forall o,
       isOrd o -> o ⊆ O -> cc_app (natfix M o) n == empty.


End SizedNats.

(** Derived properties *)
Module NatFacts (M:SizedNats).
Import M.


(*
Lemma neutr_dec' : forall n o,
  isOrd o ->
  n ∈ cc_bot (TI NATf' o) ->
  n ∈ TI NATf' o \/ ~ exists Y, n ∈ NATf' Y.
intros.
apply cc_bot_ax in H0; destruct H0; auto.
destruct neutr_dec with n empty; auto.

 rewrite H0; auto.

 admit.

admit.


Admitted.
*)

Lemma neutr_TI x o :
  isOrd o ->
  ~ (exists X, x ∈ NATf' X) ->
  ~ x ∈ TI NATf' o.
red; intros.
apply H0.
apply TI_elim in H1; auto with *.
destruct H1.
exists (TI NATf' x0); auto.
Qed.



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

Lemma natfix_eqn : forall O M U,
    natfix_hyps O M U ->
    forall o n,
       isOrd o ->
       o ⊆ O ->
       n ∈ TI NATf' o ->
       cc_app (natfix M o) n == cc_app (M o (natfix M o)) n.
intros.
apply TI_inv in H2; auto with *.
destruct H2 as (o',lto,tyn).
assert (oo' : isOrd o') by eauto using isOrd_inv.
assert (leo : o' ⊆ O).
 red; intros; apply isOrd_trans with o'; auto.
  apply Wo with (1:=H).
  apply H1; trivial.
rewrite <- natfix_irr with (1:=H)(o:=osucc o'); auto with *.
 rewrite natfix_unfold with (1:=H)(4:=tyn); auto with *.
apply (WMirr H); auto with *.
 apply ole_lts; trivial.
 apply natfix_typ with (1:=H); auto.
 apply natfix_typ with (1:=H); auto.

 red; intros.
 apply natfix_irr with (1:=H); auto with *.

red; intros.
apply isOrd_plump with o'; trivial.
 apply isOrd_inv with (osucc o'); auto.
 apply olts_le; trivial.
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
  sumReal (fun _ => unitSAT) (fun a => condSAT (exists X, a ∈ NATf' X) (A a))
    (NATf2sum n).

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
  apply succ_inv_typ with (2:=H3) in H1.
  destruct H1.
  apply neutr_dec' in H1; trivial.
  destruct H1;[trivial|contradiction].
Qed.

Lemma Real_inl' RX RY x y t :
  Proper (eq_set ==> eqSAT) RX ->
  inSAT t (RX x) ->
  y == inl x ->
  inSAT (INL t) (sumReal RX RY y).
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
apply piSAT0_elim with (2:=H1) (3:=H0) in H2; trivial.
Qed.
Lemma Real_inr' RX RY x y t :
  Proper (eq_set ==> eqSAT) RY ->
  inSAT t (RY x) ->
  y == inr x ->
  inSAT (INR t) (sumReal RX RY y).
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
apply piSAT0_elim with (2:=H1) (3:=H0) in H3; auto with *.
Qed.


Definition ZE := INL ID.

Lemma Real_ZERO_gen A :
  inSAT ZE (fNAT A zero).
unfold fNAT, NATf2sum.
apply Real_inl' with empty.
 do 2 red; reflexivity.

 apply ID_intro.

 apply natcase_zero.
Qed.

Definition SU := INR.


Lemma Real_SUCC_gen A n t :
  Proper (eq_set==>eqSAT) A ->
  (exists X, n ∈ NATf' X) ->
  inSAT t (A n) ->
  inSAT (SU t) (fNAT A (succ n)).
intros.
unfold fNAT, NATf2sum.
apply Real_inr' with n.
 do 2 red; intros; apply condSAT_morph; auto.
 apply ex_morph; intro.
 rewrite H2; reflexivity.

 rewrite condSAT_ok; auto.

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
  inSAT gt (piSAT0 (fun x => x ∈ cc_bot X) (fun a => condSAT (exists Y, a ∈ NATf' Y) (A a))
                (fun x => C (succ x))) ->
  inSAT (NCASE ft gt nt) (C n).
intros Cm nty nreal freal greal.
apply Real_sum_case with (NATf2sum n)
    (fun _ => unitSAT) (fun a => condSAT (exists Y, a ∈ NATf' Y) (A a)); trivial.
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

Lemma fNATi_neutral o x :
  isOrd o ->
  ~ x ∈ TI NATf' o ->
  eqSAT (fNATi o x) neuSAT.
intros.
apply tiSAT_outside_domain; auto with *.
 intros; apply fNAT_irrel with (o:=o'); trivial.
Qed.

Lemma fNATi_neutral' o x :
  isOrd o ->
  ~ (exists X, x ∈ NATf' X) ->
  eqSAT (fNATi o x) neuSAT.
intros.
apply tiSAT_outside_domain; auto with *.
 intros; apply fNAT_irrel with (o:=o'); trivial.

 apply neutr_TI with (2:=H0); trivial.
Qed.


(*
Lemma fNATi_neutral o :
  isOrd o ->
  eqSAT (fNATi o empty) neuSAT.
intros.
apply tiSAT_outside_domain; auto with *.
 intros; apply fNAT_irrel with (o:=o'); trivial.

 intro.
 apply mt_not_in_NATf' in H0; auto with *.
Qed.
*)
Lemma Real_ZERO o :
  isOrd o ->
  inSAT ZE (fNATi (osucc o) zero).
intros.
rewrite fNATi_succ_eq; trivial.
 apply Real_ZERO_gen.

 apply TI_intro with o; auto.
 apply zero_typ.
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
  inSAT ft (C zero) ->
  inSAT gt (piSAT0 (fun x => x ∈ cc_bot (TI NATf' o)) (fNATi o) (fun x => C (succ x))) ->
  inSAT (NCASE ft gt nt) (C n).
intros oo Cm nty nreal freal greal.
rewrite fNATi_succ_eq in nreal; trivial.
(*unfold NATi in nty;*) rewrite TI_mono_succ in nty; auto.
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

Definition NAT' := TI NATf' omega.

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
apply neutr_dec' in H0; trivial.
destruct H0.
 transitivity (fNATi (osup2 o omega) x);[|symmetry]; apply fNATi_mono;
   auto with *.

  apply isOrd_osup2; auto.

  apply osup2_incl1; auto.

  apply isOrd_osup2; auto.

  apply osup2_incl2; auto.

  revert H0; apply TI_pre_fix; auto with *.
  rewrite <- NAT_eqn; reflexivity.

 transitivity neuSAT;[|symmetry]; apply fNATi_neutral'; trivial.
Qed.

Lemma Real_SUCC_cNAT n t :
  n ∈ cc_bot NAT' ->
  inSAT t (cNAT n) ->
  inSAT (SU t) (cNAT (succ n)).
intros.
rewrite cNAT_eq.
 apply Real_inr' with n; auto with *.
  do 2 red; intros; apply condSAT_morph; auto with *.
  apply ex_morph; intro.
  rewrite H1; reflexivity.
  apply cNAT_morph; trivial.

  apply neutr_dec' in H; auto.
  destruct H.
   rewrite condSAT_ok; trivial.
   exists NAT'.
   unfold NAT'; rewrite <- NAT_eqn; trivial.

   apply neuSAT_def.
   revert H0; apply fNATi_neutral'; auto.

  unfold NATf2sum; apply natcase_succ; auto with *.

 unfold NAT'; rewrite NAT_eqn.
 apply succ_typ; trivial.
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
 apply neutr_dec' in H1; trivial.
 destruct H1.
  right.
  apply TI_elim in H1; auto with *.
  destruct H1 as (z,zty,xty).
  exists z; trivial.
  rewrite TI_mono_succ; auto with *.
  apply isOrd_inv with y; trivial.

  left; apply fNATi_neutral'; trivial.

 exists empty; trivial.

 intros.
 apply fNATi_mono; trivial.

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
 rewrite <- fNATi_mono with (o1:=osucc z) in H1; auto.
  rewrite fNATi_succ_eq in H1; auto.
  apply WHEN_SUM_sat with (1:=H1) (2:=H2); trivial.

  red; intros.
  apply le_lt_trans with z; trivial.
Qed.

End Make.
