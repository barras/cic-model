Require Export basic.
Require Import ZF ZFnats.

(** Theory about well-founded sets *)
Section WellFoundedSets.

(** Can this be defined without higher-order ? *)
Definition isWf x :=
  forall P : set -> Prop,
  (forall a,(forall b, b \in a -> P b)-> P a) -> P x.

Lemma isWf_intro : forall x,
  (forall a, a \in x -> isWf a) -> isWf x.
red; intros.
apply H0; intros.
red in H.
apply H; trivial.
Qed.

Lemma isWf_inv : forall a b,
  isWf a -> b \in a -> isWf b.
intros a b H; revert b.
red in H; apply H; intros.
apply isWf_intro; eauto.
Qed.

Lemma isWf_ext : forall x x', x == x' -> isWf x -> isWf x'.
intros.
apply isWf_intro; intros.
rewrite <- H in H1.
apply isWf_inv with x; trivial.
Qed.

Instance isWf_morph : Proper (eq_set ==> iff) isWf.
apply morph_impl_iff1; auto with *.
do 4 red; intros.
apply isWf_ext with x; auto.
Qed.

Lemma isWf_ind :
  forall P : set -> Prop,
  (forall a, isWf a -> (forall b, b \in a -> P b)-> P a) ->
  forall x, isWf x ->  P x.
intros.
cut (isWf x /\ P x).
 destruct 1; trivial.
apply H0; intros.
assert (isWf a).
 apply isWf_intro; intros; apply H1; trivial.
split; trivial.
apply H; intros; trivial.
apply H1; trivial.
Qed.

(* The class of well-founded sets form a model od IZF (without foundation axiom) *)

Lemma isWf_zero: isWf zero.
apply isWf_intro; intros.
apply empty_ax in H; contradiction.
Qed.

Lemma isWf_pair : forall x y,
  isWf x -> isWf y -> isWf (pair x y).
intros.
apply isWf_intro; intros.
elim pair_elim with (1:=H1); intros.
 rewrite H2; trivial.
 rewrite H2; trivial.
Qed.

Lemma isWf_power : forall x, isWf x -> isWf (power x).
intros.
apply isWf_intro; intros.
apply isWf_intro; intros.
apply isWf_inv with x; trivial.
apply power_elim with a; trivial.
Qed.

Lemma isWf_union : forall x, isWf x -> isWf (union x).
intros.
apply isWf_intro; intros.
elim union_elim with (1:=H0); intros.
apply isWf_inv with x0; trivial.
apply isWf_inv with x; trivial.
Qed.

Lemma isWf_incl x y : isWf x -> y \incl x -> isWf y.
intros.
apply isWf_intro; intros.
apply isWf_inv with x; auto.
Qed.

Lemma isWf_subset : forall x P, isWf x -> isWf (subset x P).
intros.
apply isWf_incl with x; trivial.
red; intros.
apply subset_elim1 in H0; trivial.
Qed.

Lemma isWf_succ : forall n, isWf n -> isWf (succ n).
intros.
apply isWf_intro; intros.
elim le_case with (1:=H0); clear H0; intros.
 apply isWf_ext with n; trivial.
 symmetry; trivial.

 apply isWf_inv with n; trivial.
Qed.

Require Import ZFrepl.

Lemma isWf_repl : forall x R,
  repl_rel x R ->
  (forall a b, a \in x -> R a b -> isWf b) ->
  isWf (repl x R).
intros.
apply isWf_intro; intros.
elim repl_elim with (1:=H) (2:=H1); intros; eauto.
Qed.

(* A well-founded set does not belong to itself. *)
Lemma isWf_antirefl : forall x, isWf x -> ~ x \in x.
intros.
elim H using isWf_ind; clear x H; intros.
red; intros.
apply H0 with a; trivial.
Qed.

(* Transitive closure *)

Definition tr x p :=
  x \in p /\
  (forall a b, a \in b -> b \in p -> a \in p).

Instance tr_morph : Proper (eq_set ==> eq_set ==> iff) tr.
unfold tr.
apply morph_impl_iff2; auto with *.
do 4 red; intros.
destruct H1; split; intros.
 rewrite <- H; rewrite <- H0; trivial.

 rewrite <- H0 in H4|-*; eauto.
Qed.

Definition isTransClos x y :=
  tr x y /\ (forall p, tr x p -> y \incl p).

Instance isTransClos_morph : Proper (eq_set ==> eq_set ==> iff) isTransClos.
apply morph_impl_iff2; auto with *.
do 5 red; intros.
destruct H1.
split; intros.
 rewrite <- H; rewrite <- H0; trivial.
 rewrite <- H in H3; rewrite <- H0; auto.
Qed.

Lemma isTransClos_fun x y y' :
  isTransClos x y ->
  isTransClos x y' -> y == y'.
unfold isTransClos; intros.
destruct H; destruct H0.
apply incl_eq; auto.
Qed.

Lemma isTransClos_def x :
  isWf x -> exists y, isTransClos x y.
induction 1 using isWf_ind.
assert (ch : forall b, b \in a -> uchoice_pred (isTransClos b)).
 intros.
 split; [|split; intros]; auto.
  intros.
  rewrite <- H2; trivial.

  apply isTransClos_fun with b; trivial.
assert (Hrec : forall b, b \in a -> isTransClos b (uchoice (isTransClos b))).
 intros.
 apply uchoice_def; auto.
exists (union2 (singl a) (sup a (fun a' => uchoice (isTransClos a')))).
split; intros.
 split; intros.
  apply union2_intro1.
  apply singl_intro.

  apply union2_intro2.
  apply union2_elim in H2; destruct H2.
   apply singl_elim in H2.
   rewrite H2 in H1.
   rewrite sup_ax.
   2:admit.
   exists a0; trivial.
   apply Hrec; trivial.

   rewrite sup_ax in H2.
   2:admit.
   destruct H2.
   rewrite sup_ax.
   2:admit.
   exists x; trivial.
   destruct Hrec with (1:=H2).
   destruct H4; eauto.

 red; intros.
 destruct H1.
 apply union2_elim in H2; destruct H2.
  apply singl_elim in H2.
  rewrite H2; trivial.

  rewrite sup_ax in H2.
  2:admit.
  destruct H2.
  destruct Hrec with (1:=H2).
  apply H6; auto.
  split; eauto.
Qed.

Definition trClos x := uchoice (isTransClos x).

(*
Lemma isTransClosStart : isWf x -> x \in trClos x.

Lemma isTransClosStep : isWf x ->
*)

(** Transfinite iteration *)

Section TransfiniteRecursion.

  Variable F : (set -> set) -> set -> set.
  Hypothesis Fm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) F.
  Hypothesis Fmorph : forall x f f', eq_fun x f f' -> F f x == F f' x.

Require Import ZFpairs ZFrelations.

  Definition isTR_rel F P :=
    forall o y,
    couple o y \in P ->
    exists2 f, (forall n, n \in o -> couple n (cc_app f n) \in P) &
      y == F (cc_app f) o.

  Lemma isTR_rel_fun P P' o y y':
    isWf o ->
    isTR_rel F P ->
    isTR_rel F P' -> 
    couple o y \in P ->
    couple o y' \in P' ->
    y == y'.
intros wfo istr istr' inP inP'; revert y y' inP inP'; elim wfo using isWf_ind; intros.
destruct istr with (1:=inP) as (f,?,?).
destruct istr' with (1:=inP') as (f',?,?).
rewrite H2; rewrite H4; apply Fmorph; auto.
red; intros.
rewrite <- H6; clear x' H6.
apply H0 with x; auto.
Qed.

  Instance isTR_rel_morph_gen :
    Proper (((eq_set ==> eq_set) ==> eq_set ==> eq_set) ==> eq_set ==> iff) isTR_rel.
do 3 red; intros.
unfold isTR_rel.
apply fa_morph; intro o.
apply fa_morph; intro y'.
rewrite H0.
apply fa_morph; intros ?.
apply ex2_morph; red; intros; auto with *.
 apply fa_morph; intros n.
 rewrite H0; reflexivity.

 split; intros h;rewrite h;[|symmetry]; (apply H; [apply cc_app_morph|];auto with *).
Qed.

  Instance isTR_rel_morph : Proper (eq_set==>iff) (isTR_rel F).
do 2 red; intros.
apply fa_morph; intro o.
apply fa_morph; intro y'.
rewrite H.
apply fa_morph; intros ?.
apply ex2_morph; red; intros; auto with *.
apply fa_morph; intros n.
rewrite H; reflexivity.
Qed.

  Definition TRP_rel F o P :=
    isTR_rel F P /\
    (exists y, couple o y \in P) /\
    forall P' y, isTR_rel F P' -> couple o y \in P' -> P \incl P'.

  Instance TRP_rel_morph_gen :
    Proper (((eq_set ==> eq_set) ==> eq_set ==> eq_set) ==> eq_set ==> eq_set ==> iff) TRP_rel.
do 4 red; intros.
unfold TRP_rel.
apply and_iff_morphism.
 apply isTR_rel_morph_gen; trivial.
apply and_iff_morphism.
 apply ex_morph; red; intros; rewrite H0; rewrite H1; reflexivity.

 apply fa_morph; intros P'.
 apply fa_morph; intros w.
 apply impl_morph.
  apply isTR_rel_morph_gen; auto with *.

  intros; rewrite H0; rewrite H1; reflexivity.
Qed.

  Instance TRP_rel_morph : Proper (eq_set==>eq_set==>iff) (TRP_rel F).
do 3 red; intros.
unfold TRP_rel.
apply and_iff_morphism.
 rewrite H0; reflexivity.
apply and_iff_morphism.
 apply ex_morph; red; intros; rewrite H; rewrite H0; reflexivity.

 apply fa_morph; intros P'.
 apply fa_morph; intros w.
 rewrite H; rewrite H0; reflexivity.
Qed.

  Lemma TR_img_ex x P : isWf x ->
    TRP_rel F x P ->
    uchoice_pred (fun y => couple x y \in P).
intros.
split;[|split]; intros.
 rewrite <- H1; trivial.

 destruct H0 as (_,(?,_)); trivial.

 destruct H0 as (?,(?,?)).
 apply isTR_rel_fun with (2:=H0)(3:=H0)(4:=H1)(5:=H2); trivial.
Qed.


  Lemma TR_rel_ex o :
    isWf o -> uchoice_pred (TRP_rel F o).
intro wfo; elim wfo using isWf_ind; clear o wfo; intros.
split;[|split]; intros.
 revert H2; apply TRP_rel_morph; auto with *.

 pose (P:=union2 (singl(couple a (F (fun b=> uchoice(fun y => couple b y \in uchoice(TRP_rel F b))) a)))
            (sup a (fun b => uchoice(TRP_rel F b)))).
 assert (Pax:forall z, z \in P <->
     z == couple a (F (fun b=> uchoice(fun y => couple b y \in uchoice(TRP_rel F b))) a) \/
     exists2 b, b \in a & z \in uchoice(TRP_rel F b)).
  intros; unfold P; rewrite union2_ax; apply or_iff_morphism.
   split; intros.
    apply singl_elim in H1; trivial.
    rewrite H1; apply singl_intro.

   rewrite sup_ax.
    reflexivity.

    do 2 red; intros; apply uchoice_morph_raw.
    apply TRP_rel_morph; trivial.
 assert (ychm : morph1 (fun b =>
      uchoice (fun y0 => couple b y0 \in uchoice (TRP_rel F b)))).
  do 2 red; intros.
  apply uchoice_morph_raw.
  red; intros.
  rewrite H1; rewrite H2; reflexivity.
 exists P.
 split;[|split]; intros.
  red; intros.
  rewrite Pax in H1; destruct H1 as [?|(b,?,?)].
   apply couple_injection in H1; destruct H1.
   exists (cc_lam o (fun b=> uchoice
            (fun y : set => couple b y \in uchoice(TRP_rel F b)))); intros.
    rewrite cc_beta_eq; trivial.
     rewrite Pax; right.
     rewrite H1 in H3; exists n; trivial.
     apply uchoice_def.
     apply TR_img_ex.
      apply isWf_inv with a; trivial.

      apply uchoice_def; auto.

     do 2 red; intros; apply uchoice_morph_raw; red; intros.
     rewrite H5; rewrite H6; reflexivity.
     
    rewrite H1; rewrite H2; apply Fmorph.
    red; intros.
    rewrite <- H4.
    rewrite cc_beta_eq; auto with *.

   destruct (uchoice_def _ (H0 _ H1)) as (?,trp').
   destruct H3 with (1:=H2) as (f,?,?).
   exists f; trivial; intros.
   rewrite Pax; right.
   exists b; auto.

  exists (F (fun b => uchoice (fun y => couple b y \in uchoice (TRP_rel F b))) a).
  rewrite Pax; left; reflexivity.

  red; intros.
  rewrite Pax in H3; destruct H3 as [?|(y',?,?)].
   destruct H1 with (1:=H2) as (f,?,?).
   rewrite H5 in H2; rewrite H3; revert H2; apply in_reg.
   apply couple_morph; auto with *.
   apply Fmorph; red; intros.
   apply uchoice_ext; auto.
    rewrite H6 in H2; auto.
    apply TR_img_ex.
     apply isWf_inv with a; trivial.

     apply uchoice_def; auto.

    rewrite <- H6; clear x' H6.
    specialize H0 with (1:=H2).
    apply uchoice_def in H0.
    destruct H0 as (?,((yx,?),_)).
    specialize H4 with (1:=H2).
    rewrite isTR_rel_fun with (2:=H1) (3:=H0) (4:=H4) (5:=H6); trivial.
    apply isWf_inv with a; trivial.

  specialize H0 with (1:=H3).
  apply uchoice_def in H0; destruct H0 as (?,((w,?),?)).
  assert (z == couple (fst z) (snd z)).
   assert (z \in subset (uchoice(TRP_rel F y')) (fun z => z == couple (fst z) (snd z))).
    apply H6 with w; trivial.
     red; intros.
     apply subset_elim1 in H7.
     destruct H0 with (1:=H7) as (f',?,?).
     exists f'; intros; trivial.
     apply subset_intro; auto.
     rewrite fst_def; rewrite snd_def; reflexivity.

     apply subset_intro; trivial.
     rewrite fst_def; rewrite snd_def; reflexivity.
   apply subset_elim2 in H7; destruct H7.
   rewrite H7; trivial.
  rewrite H7 in H4|-*.
  destruct H1 with (1:=H2) as (f0,?,_).
  specialize H8 with (1:=H3).
  apply H6 with (cc_app f0 y'); trivial.

 destruct H1 as (?,((y,?),?)).
 destruct H2 as (?,((y',?),?)).
 apply incl_eq; eauto.
Qed.

  Definition TR x := uchoice (fun y => couple x y \in uchoice(TRP_rel F x)).

  Lemma TR_eqn x : isWf x -> TR x == F TR x.
unfold TR; intros.
specialize TR_rel_ex with (1:=H); intro.
apply uchoice_def in H0.
generalize H0; intros (?,_).
apply TR_img_ex in H0; trivial.
apply uchoice_def in H0.
destruct H1 with (1:=H0) as (f,?,?).
rewrite H3; apply Fmorph; red; intros.
rewrite H5 in H4|-*; clear x0 H5.
assert (isWf x') by eauto using isWf_inv.
specialize H2 with (1:=H4).
specialize TR_rel_ex with (1:=H5); intro.
apply uchoice_def in H6.
generalize H6; intros (?,_).
apply TR_img_ex in H6; trivial.
apply uchoice_def in H6.
apply isTR_rel_fun with (4:=H2) (5:=H6); trivial.
Qed.

  Lemma TR_ind : forall x (P:set->set->Prop),
    Proper (eq_set ==> eq_set ==> iff) P ->
    isWf x ->
    (forall y, isWf y ->
     (forall x, lt x y -> P x (TR x)) ->
     P y (F TR y)) ->
    P x (TR x).
intros x P Pm wfx Hrec.
induction wfx using isWf_ind; intros.
rewrite TR_eqn; trivial.
apply Hrec; auto with *; intros.
Qed.

  Global Instance TR_morph0 : morph1 TR.
do 2 red; intros.
unfold TR.
apply uchoice_morph_raw.
red; intros.
rewrite H; rewrite H0; reflexivity.
Qed.

End TransfiniteRecursion.

  Global Instance TR_morph :
    Proper (((eq_set ==> eq_set) ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) TR.
do 3 red; intros.
unfold TR.
apply uchoice_morph_raw; red; intros.
rewrite (couple_morph _ _ H0 _ _ H1).
split; apply eq_elim; [|symmetry]; apply uchoice_morph_raw; red; intros.
 apply TRP_rel_morph_gen; trivial.
 apply TRP_rel_morph_gen; trivial.
Qed.

End WellFoundedSets.

Hint Resolve isWf_morph.

Lemma isWf_N : isWf N.
apply isWf_intro; intros.
elim H using N_ind; intros.
 apply isWf_ext with n; trivial.
 apply isWf_zero.
 apply isWf_succ; trivial.
Qed.
