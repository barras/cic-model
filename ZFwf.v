Require Import ZF ZFnats.
Import IZF.


Section WellFoundedSets.

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

(* Transfinite iteration *)

Require Export basic.
Require Import Relations.
(*
Section TransfiniteRecursion.

  Variable F : (set -> set) -> set -> set.
  Hypothesis Fm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) F.

  Hypothesis Fmorph :
    forall x f f', isWf x -> eq_fun x f f' -> F f x == F f' x.

  Definition TR_rel o y :=
    isWf o /\
    forall (P:set->set->Prop),
    Proper (eq_set ==> eq_set ==> iff) P ->
    (forall o' f, isWf o' -> morph1 f ->
     (forall n, n \in o' -> P n (f n)) ->
     P o' (F f o')) ->
    P o y.

  Instance TR_rel_morph : Proper (eq_set ==> eq_set ==> iff) TR_rel.
apply morph_impl_iff2; auto with *.
do 4 red; unfold TR_rel; intros.
destruct H1 as (wfx,Hrec); split; intros.
 rewrite <- H; auto.

 cut (P x x0).
  do 3 red in H1.
  apply -> H1; trivial.
 apply Hrec; auto.
Qed.

  Lemma TR_rel_intro : forall x f,
    isWf x ->
    morph1 f ->
    (forall y, y \in x -> TR_rel y (f y)) ->
    TR_rel x (F f x).
red; intros.
split; intros; auto.
apply H3; trivial; intros.
apply H1; trivial.
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
   split; intros; trivial.
   rewrite <- H1 in H4; auto.

   rewrite <- H2; rewrite eqF.
   apply Fm; trivial.
assert (TR_relsub := fun n h => proj1 (H3 n h)); clear H3.
split.
 apply TR_rel_intro; trivial.

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
 split;[|split]; intros; eauto.
  rewrite <- H3; trivial.
  apply TR_rel_fun with z; trivial.
exists (F (fun z => uchoice (fun y => TR_rel z y)) a).
apply TR_rel_intro; intros; trivial.
 do 2 red; intros.
 apply uchoice_morph_raw; red; intros.
 apply TR_rel_morph; trivial.
apply uchoice_def; auto.
Qed.

  Lemma TR_rel_choice_pred : forall o, isWf o -> uchoice_pred (fun y => TR_rel o y).
split; [|split]; intros.
 rewrite <- H0; trivial.

 apply TR_rel_def; trivial.

 apply TR_rel_fun with o; trivial.
Qed.

  Definition TR o := uchoice (fun y => TR_rel o y).

  Lemma TR_eqn0 : forall o, isOrd o -> o \incl ord ->
     uchoice (fun y => TR_rel o y) == F (fun o => uchoice (fun y => TR_rel o y)) o.
intros.
specialize TR_rel_choice_pred with (1:=H) (2:=H0); intro.
apply uchoice_def in H1.
apply TR_rel_inv in H1.
destruct H1.
destruct H1.
rewrite H2.
apply Fmorph; intros; auto with *.
red; intros.
apply TR_rel_fun with x'.
 rewrite <- H5; auto.

 apply uchoice_def.
 apply TR_rel_choice_pred.
 rewrite <- H5; apply isOrd_inv with o; trivial.
 red; intros; apply H0; apply isOrd_trans with x'; trivial.
 rewrite <- H5; trivial.
Qed.

End TransfiniteRecursion.

  Lemma TR_rel_irrel : forall F b1 b2 o y,
    o \incl b2 ->
    TR_rel F b1 o y -> TR_rel F b2 o y.
intros.
revert H; apply H0; intros.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 rewrite <- H in H3.
 generalize (H2 H3).
 apply TR_rel_morph; auto with *.

 apply TR_rel_intro; trivial; intros.
 apply H3; trivial.
 transitivity o'; trivial.
 red; intros; apply isOrd_trans with y0; trivial.
Qed.

  Instance TR_morph0 : forall F, morph1 (TR F).
do 2 red; intros.
unfold TR.
apply uchoice_morph_raw.
red; intros.
transitivity (TR_rel F x y y0).
 apply TR_rel_morph; trivial. 

 split; apply TR_rel_irrel; auto with *.
 rewrite H; reflexivity.
Qed.

  Instance TR_morph :
    Proper (((eq_set ==> eq_set) ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) TR.
do 3 red; intros.
unfold TR.
apply uchoice_morph_raw; red; intros.
unfold TR_rel.
apply and_iff_morphism.
 rewrite H0; reflexivity.

 apply fa_morph; intro P.
 apply fa_morph; intro Pm.
 apply impl_morph; [|intro Hrec].
  split; intros.
   rewrite <- H0 in H4.
   apply Pm with o' (x f o'); auto with *.
   symmetry; apply H; auto with *.
   
   apply Pm with o' (y f o'); auto with *.
    apply H; auto with *.

    rewrite H0 in H4; auto with *.
 rewrite H0; rewrite H1; reflexivity.
Qed.

Section TransfiniteRec.

  Variable F : (set -> set) -> set -> set.
  Hypothesis Fm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) F.

  Lemma TR_eqn o :
    isOrd o ->
    (forall x f f', isOrd x -> x \incl o -> eq_fun x f f' -> F f x == F f' x) ->
    TR F o == F (TR F) o.
intros oo Fmorph.
unfold TR; rewrite TR_eqn0; eauto with *.
apply Fmorph; auto with *.
red; intros.
apply uchoice_morph_raw.
red; intros.
transitivity (TR_rel F o x' y).
 apply TR_rel_morph; trivial.

 rewrite H0 in H.
 split; apply TR_rel_irrel; auto with *.
Qed.

  Lemma TR_ind : forall o (P:set->set->Prop),
    Proper (eq_set ==> eq_set ==> iff) P ->
    isOrd o ->
    (forall x f f', isOrd x -> x \incl o -> eq_fun x f f' -> F f x == F f' x) ->
    (forall y, isOrd y -> y \incl o ->
     (forall x, lt x y -> P x (TR F x)) ->
     P y (F (TR F) y)) ->
    P o (TR F o).
intros o P Pm oo Fmorph.
revert Fmorph; induction oo using isOrd_ind; intros.
rewrite TR_eqn; trivial.
apply H1; auto with *; intros.
apply H0; intros; trivial.
 assert (x0 \incl y).
  transitivity x; auto.
 auto.
apply H1; trivial.
transitivity x; auto.
Qed.

  Lemma TR_typ : forall o X,
    isOrd o ->
    (forall x f f', isOrd x -> x \incl o -> eq_fun x f f' -> F f x == F f' x) ->
    morph1 X ->
    (forall y f, morph1 f -> isOrd y -> y \incl o ->
     (forall z, lt z y -> f z \in X z) -> F f y \in X y) ->
    TR F o \in X o.
intros o X oo Fmorph Xm Hrec.
apply TR_ind with (o:=o); intros; trivial.
 do 3 red; intros.
 rewrite H; rewrite H0; reflexivity.

 apply Fmorph; trivial.

 apply Hrec; trivial; intros.
 apply TR_morph0.
Qed.

End TransfiniteRec.
*)

(* Old *)

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

Hint Resolve isWf_morph.

Lemma isWf_N : isWf N.
apply isWf_intro; intros.
elim H using N_ind; intros.
 apply isWf_ext with n; trivial.
 apply isWf_zero.
 apply isWf_succ; trivial.
Qed.
