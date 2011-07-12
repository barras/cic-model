Require Import ZF ZFnats.
Import IZF.


Section WellFoundedSets.

Definition isWf x :=
  forall P : set -> Prop,
  (forall x x', x == x' -> P x -> P x') ->
  (forall a,(forall b, b \in a -> P b)-> P a) -> P x.

Lemma isWf_intro : forall x,
  (forall a, a \in x -> isWf a) -> isWf x.
red; intros.
apply H1; intros.
red in H.
apply H; trivial.
Qed.

Lemma isWf_ext : forall x x', x == x' -> isWf x -> isWf x'.
unfold isWf; intros.
apply H1 with x; trivial.
apply H0; auto.
Qed.

Lemma isWf_inv : forall a b,
  isWf a -> b \in a -> isWf b.
intros a b H; generalize b; clear b.
red in H; apply H; intros.
 apply H1; rewrite H0; trivial.
 apply isWf_intro; eauto.
Qed.

Lemma isWf_ind :
  forall P : set -> Prop,
  (forall a, isWf a -> (forall b, b \in a -> P b)-> P a) ->
  forall x, isWf x ->  P x.
intros.
cut (forall y, y == x -> isWf y /\ P y).
 intro h; apply h; reflexivity.
apply H0; intros.
 rewrite <- H1 in H3; auto.

 assert (isWf y).
  apply isWf_intro; intros.
  apply H1 with a0; auto with *.
  rewrite <- H2; trivial.
 split; trivial.
 apply H; intros; auto.
 apply H1 with b; auto with *.
 rewrite <- H2; trivial.
Qed.

Lemma isWf_zero: isWf zero.
red; intros.
apply H0; intros.
elim empty_ax with b; trivial.
Qed.

Lemma isWf_pair : forall x y,
  isWf x -> isWf y -> isWf (pair x y).
intros.
apply isWf_intro; intros.
elim pair_elim with (1:=H1); intros.
 apply isWf_ext with x; trivial.
 symmetry; trivial.

 apply isWf_ext with y; trivial.
 symmetry; trivial.
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

Lemma isWf_subset : forall x P, isWf x -> isWf (subset x P).
intros.
apply isWf_intro; intros.
apply isWf_inv with x; trivial.
apply subset_elim1 with (1:=H0).
Qed.

Lemma isWf_succ : forall n, isWf n -> isWf (succ n).
intros.
apply isWf_intro; intros.
elim le_case with (1:=H0); clear H0; intros.
 apply isWf_ext with n; trivial.
 symmetry; trivial.

 apply isWf_inv with n; trivial.
Qed.

Lemma isWf_antirefl : forall x, isWf x -> ~ x \in x.
intros.
elim H using isWf_ind; clear x H; intros.
red; intros.
apply H0 with a; trivial.
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

(* Transfinite iteration *)

Require Export basic.
Require Import Relations.


  Inductive tr_clos x y : Prop :=
  | Tc_refl (_:x==y)
  | Tc_trans x' (_:x\in x') (_:tr_clos x' y).

  Lemma tc_trans2 x y z : tr_clos x y -> y \in z -> tr_clos x z.
intro h; revert z; induction h; intros.
 rewrite <- H in H0.
 apply Tc_trans with z;[trivial|apply Tc_refl;reflexivity].

 apply Tc_trans with x'; auto.
Qed.

  Instance tr_clos_morph : Proper (eq_set ==> eq_set ==> iff) tr_clos.
Admitted.

  Lemma tr_clos_wf x y : tr_clos x y -> isWf y -> isWf x.
induction 1; intros.
 apply isWf_ext with y; auto with *.

 apply isWf_inv with x'; auto.
Qed.


Section TransfiniteRecursion.

  Variable F : (set -> set) -> set -> set.
  Hypothesis Fmorph : forall x x' f g, x == x' -> eq_fun x f g -> F f x == F g x'.

  Definition TR_rel o y := isWf o /\
    forall (P:set->set->Prop),
    Proper (eq_set ==> eq_set ==> iff) P ->
    (forall o' f, isWf o' (*tr_clos o' o*) -> morph1 f ->
     (forall n, n \in o' -> P n (f n)) ->
     P o' (F f o')) ->
    P o y.

  Instance TR_rel_morph : Proper (eq_set ==> eq_set ==> iff) TR_rel.
apply morph_impl_iff2; auto with *.
do 4 red; unfold TR_rel; intros.
destruct H1 as (H1,Hrec).
split; intros.
 apply isWf_ext with x; trivial.
 rewrite <- H; rewrite <- H0.
 apply Hrec; auto.
(* intros; apply H3; trivial.
 destruct H4.
  left; rewrite <- H; trivial.

  apply Tc_trans with x'; trivial.
  rewrite <- H; trivial.*)
Qed.

  Lemma TR_rel_intro : forall x f,
    isWf x ->
    morph1 f ->
    (forall y, y \in x -> TR_rel y (f y)) ->
    TR_rel x (F f x).
red; intros.
split; intros; auto.
apply H3; intros; auto with *.
(* apply Tc_refl; reflexivity.*)
apply H1; intros; trivial.
apply H3; trivial.
(*apply tc_trans2 with n; trivial.*)
Qed.

  Lemma TR_rel_inv : forall x y,
    TR_rel x y ->
    exists2 f,
      morph1 f /\ (forall y, y \in x -> TR_rel y (f y)) &
      y == F f x.
intros.
apply (@proj2 (TR_rel x y)).
destruct H as (H,H0).
apply H0; intros.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 destruct H3; split.
  rewrite <- H1; rewrite <- H2; trivial.

  destruct H4 as (f,(fm,eqf),eqF); exists f; trivial.
   split; trivial.
   intros.
   rewrite <- H1 in H4; auto.

   rewrite <- H2; rewrite eqF; auto.
   apply Fmorph; trivial.
   red; intros; apply fm; trivial.
assert (TR_relsub := fun n h => proj1 (H3 n h)); clear H3.
split.
 apply TR_rel_intro; trivial.
(* apply tr_clos_wf with x; trivial.*)

 exists f; auto with *.
Qed.


  Lemma TR_rel_fun :
    forall x y, TR_rel x y -> forall y', TR_rel x y' -> y == y'.
intros x y (xo,H).
apply H; intros.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 rewrite <- H1; rewrite <- H0 in H3; auto.
apply TR_rel_inv in H3; destruct H3.
destruct H3.
rewrite H4; clear y' H4.
apply Fmorph; intros; auto with *.
red; intros.
apply H2; trivial.
rewrite H6 in H4|-*; auto.
Qed.

Require Import ZFrepl.

  Lemma TR_rel_repl_rel :
    forall x, repl_rel x TR_rel.
split; intros.
 rewrite <- H0; rewrite <- H1; trivial.

 apply TR_rel_fun with x0; trivial.
Qed.

  Lemma TR_rel_def : forall o, isWf o -> exists y, TR_rel o y.
induction 1 using isWf_ind; intros.
assert (forall z, z \in a -> uchoice_pred (fun y => TR_rel z y)).
 intros.
 destruct H0 with z; trivial.
 split; intros.
  rewrite <- H3; trivial.
 split; intros.
  exists x; trivial.
 apply TR_rel_fun with z; trivial.
exists (F (fun z => uchoice (fun y => TR_rel z y)) a).
apply TR_rel_intro; intros; trivial.
 do 2 red; intros.
 apply uchoice_morph_raw; intros; auto.
 red; intros.
 apply TR_rel_morph; trivial.
apply uchoice_def; auto.
Qed.

  Lemma TR_rel_choice_pred : forall o, isWf o -> uchoice_pred (fun y => TR_rel o y).
split; intros.
 rewrite <- H0; trivial.
split; intros.
 apply TR_rel_def; trivial.
apply TR_rel_fun with o; trivial.
Qed.

  Definition TR x := uchoice (fun y => TR_rel x y).

  Lemma TR_eqn : forall o, isWf o -> TR o == F TR o.
intros.
specialize TR_rel_choice_pred with (1:=H); intro.
apply uchoice_def in H0.
apply TR_rel_inv in H0.
destruct H0.
destruct H0.
unfold TR at 1.
rewrite H1.
apply Fmorph; intros; auto with *.
red; intros.
apply TR_rel_fun with x'.
 rewrite <- H4; auto.

 unfold TR; apply uchoice_def.
 apply TR_rel_choice_pred.
 apply isWf_inv with o; trivial.
 rewrite <- H4; trivial.
Qed.


End TransfiniteRecursion.


  Instance TR_morph :
    Proper (((eq_set==>eq_set)==>eq_set==>eq_set)==>eq_set ==> eq_set) TR.
do 3 red; intros.
unfold TR.
apply uchoice_morph_raw.
red; intros.
revert x y H x0 y0 H0 x1 y1 H1; apply morph_impl_iff3; auto with *.
do 5 red; intros.
red; intros.
destruct H2; split; intros.
 apply isWf_ext with x0; trivial.

 rewrite <- H0; rewrite <- H1; apply H3; intros; auto.
 rewrite (H _ _ H7 _ _ (reflexivity o')); auto.
Qed.


  Instance TR_morph1 : forall F, morph1 (TR F).
do 2 red; intros.
unfold TR.
apply uchoice_morph_raw.
red; intros.
apply TR_rel_morph; trivial. 
Qed.

(*
Section BoundedRecursion.

  Variable F : (set->set)->set->set.
  Variable o : set.
  Hypothesis Fmorph : forall x x' f g, tr_clos x o -> x == x' -> eq_fun x f g -> F f x == F g x'.

  Let F' f y := cond_set (tr_clos y o) (F f y).

  Definition TRb := 
  Lemma 
  Variable Fm : forall 
*)

End WellFoundedSets.


Lemma isWf_N : isWf N.
apply isWf_intro; intros.
elim H using N_ind; intros.
 apply isWf_ext with n; trivial.
 apply isWf_zero.
 apply isWf_succ; trivial.
Qed.
