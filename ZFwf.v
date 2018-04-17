Require Export basic.
Require Import ZF.

(** Theory about well-founded sets *)

(** Definition of well-founded sets. Could be Acc in_set... *)
(** Note: uses higher-order logic, although it could be done in first-order *)
Definition isWf x :=
  forall P : set -> Prop,
  (forall a,(forall b, b ∈ a -> P b)-> P a) -> P x.

Lemma isWf_intro : forall x,
  (forall a, a ∈ x -> isWf a) -> isWf x.
red; intros.
apply H0; intros.
red in H.
apply H; trivial.
Qed.

Lemma isWf_inv : forall a b,
  isWf a -> b ∈ a -> isWf b.
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

Global Instance isWf_morph : Proper (eq_set ==> iff) isWf.
apply morph_impl_iff1; auto with *.
do 4 red; intros.
apply isWf_ext with x; auto.
Qed.

Lemma isWf_acc x : isWf x <-> Acc in_set x.
split; intros.
 apply H; intros; constructor; auto.

 elim H; intros; apply isWf_intro; auto.
Qed.

Lemma isWf_ind :
  forall P : set -> Prop,
  (forall a, isWf a -> (forall b, b ∈ a -> P b)-> P a) ->
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

(** The class of well-founded sets form a model of IZF+foundation axiom *)

Lemma isWf_zero: isWf empty.
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

Lemma isWf_incl x y : isWf x -> y ⊆ x -> isWf y.
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

Require Import ZFrepl.

Lemma isWf_repl : forall x R,
  repl_rel x R ->
  (forall a b, a ∈ x -> R a b -> isWf b) ->
  isWf (repl x R).
intros.
apply isWf_intro; intros.
elim repl_elim with (1:=H) (2:=H1); intros; eauto.
Qed.

Lemma isWf_inter2 : forall x y, isWf x -> isWf y -> isWf (x ∩ y).
unfold inter2; intros.
unfold inter.
apply isWf_subset.
apply isWf_union.
apply isWf_pair; trivial.
Qed.

(** A well-founded set does not belong to itself. *)
Lemma isWf_antirefl : forall x, isWf x -> ~ x ∈ x.
intros.
elim H using isWf_ind; clear x H; intros.
red; intros.
apply H0 with a; trivial.
Qed.

(** * Defining well-founded sets without resorting to higher-order *)

Module FirstOrder.

(** Transitive closure *)

Definition tr x p :=
  x ∈ p /\
  (forall a b, a ∈ b -> b ∈ p -> a ∈ p).

Instance tr_morph : Proper (eq_set ==> eq_set ==> iff) tr.
unfold tr.
apply morph_impl_iff2; auto with *.
do 4 red; intros.
destruct H1; split; intros.
 rewrite <- H; rewrite <- H0; trivial.

 rewrite <- H0 in H4|-*; eauto.
Qed.

Definition isTransClos x y :=
  tr x y /\ (forall p, tr x p -> y ⊆ p).

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

Lemma isTransClos_intro a f :
  morph1 f ->
  (forall b, b ∈ a -> isTransClos b (f b)) ->
  isTransClos a (singl a ∪ sup a f).
split; intros.
 split; intros.
  apply union2_intro1.
  apply singl_intro.

  apply union2_intro2.
  rewrite sup_ax; auto with *.
  apply union2_elim in H2; destruct H2.
   apply singl_elim in H2.
   rewrite H2 in H1.
   exists a0; trivial.
   apply H0; trivial.

   rewrite sup_ax in H2; auto with *.
   destruct H2.
   exists x; trivial.
   destruct H0 with (1:=H2).
   destruct H4; eauto.

 red; intros.
 destruct H1.
 apply union2_elim in H2; destruct H2.
  apply singl_elim in H2.
  rewrite H2; trivial.

  rewrite sup_ax in H2; auto with *.
  destruct H2.
  destruct H0 with (1:=H2).
  apply H6; auto.
  split; eauto.
Qed.


(** Alternative definition, only using first-order quantification *)
Definition isWf' x :=
  exists2 c:set, isTransClos x c &
  forall p:set, 
    (forall a:set, a ⊆ c -> a ⊆ p -> a ∈ p) -> x ∈ p.

(** The equivalence result *)
Lemma isWf_equiv x :
  isWf x <-> isWf' x.
split; intros.
 apply H; intros.
 assert (Hm : ext_fun a (fun b => uchoice (isTransClos b))).
  do 2 red; intros.
  apply uchoice_morph_raw; red; intros.
  apply isTransClos_morph; trivial.
 assert (Hch : forall b, b ∈ a -> uchoice_pred (isTransClos b)).
  split; [|split; intros]; auto.
   intros.
   rewrite <- H2; trivial.

   destruct H0 with (1:=H1).
   exists x0; trivial.

   apply isTransClos_fun with b; trivial.
 exists (singl a ∪ sup a (fun b => uchoice (isTransClos b))).
  apply isTransClos_intro.
   do 2 red; intros.
   apply uchoice_morph_raw; red; intros.
   apply isTransClos_morph; trivial.

   intros.
   apply uchoice_def; auto.

  intros.
  apply H1; intros; trivial.
   red; intros; apply union2_intro2.
   rewrite sup_ax; trivial.
   exists z; trivial.
   assert (isTransClos z (uchoice (isTransClos z))).
    apply uchoice_def; auto.
   destruct H3.
   destruct H3; trivial.

   red; intros.
   destruct H0 with (1:=H2).
   apply H4; intros.
   apply H1; trivial.
   red; intros; apply union2_intro2.
   rewrite sup_ax; trivial.
   exists z; trivial.
   rewrite <- uchoice_ext with (x:=x0); auto.

 red; intros.
 destruct H as (c,?,?).
 destruct H.
 cut (x ∈ subset (power c) (fun x' => forall x'', x' == x'' -> P x'')).
  rewrite subset_ax; destruct 1 as (?,(x',?,?)).
  auto with *.
 apply H1; intros.
 apply subset_intro; intros.
  apply power_intro; auto.

  apply H0; intros.
  rewrite <- H5 in H6; clear x'' H5.
  generalize (H4 _ H6); rewrite subset_ax; intros (_,(b',?,?)); auto with *.
Qed.

Lemma isWf_clos_ex x : isWf x -> uchoice_pred (isTransClos x).
split;[|split]; intros.
 rewrite <- H0; trivial.

 rewrite isWf_equiv in H; destruct H; eauto.

 apply isTransClos_fun with x; trivial.
Qed.

Definition trClos x := uchoice (isTransClos x).

Global Instance trClos_morph : morph1 trClos.
do 2 red; intros; unfold trClos.
apply uchoice_morph_raw; red; intros.
apply isTransClos_morph; trivial.
Qed.

Lemma trClos_intro1 x : isWf x -> x ∈ trClos x.
intro.
specialize isWf_clos_ex with (1:=H); intro.
apply uchoice_def in H0.
destruct H0 as ((?,_),_); trivial.
Qed.

Lemma trClos_intro2 x y z : isWf x -> y ∈ trClos x -> z ∈ y -> z ∈ trClos x.
intros.
specialize isWf_clos_ex with (1:=H); intro.
apply uchoice_def in H2.
destruct H2 as ((_,?),_); eauto.
Qed.

Lemma trClos_ind x (P:set->Prop) :
  isWf x ->
  (forall x', x==x' -> P x') ->
  (forall y z, y ∈ trClos x -> P y -> z ∈ y -> P z) ->
  forall y,
  y ∈ trClos x ->
  P y.
intros.
specialize isWf_clos_ex with (1:=H); intro.
apply uchoice_def in H3.
destruct H3 as (?,?).
assert (y ∈ subset (trClos x) (fun z => forall z', z==z' -> P z')).
 apply H4; trivial.
 split; intros.
  apply subset_intro; trivial.
  apply trClos_intro1; trivial.

  rewrite subset_ax in H6; destruct H6.
  destruct H7.
  rewrite H7 in H5,H6.
  apply subset_intro.
   apply trClos_intro2 with x0; auto.

   intros; apply H1 with x0; auto with *.
   rewrite <- H9; trivial.
rewrite subset_ax in H5; destruct H5.
destruct H6.
eauto with *.
Qed.

Lemma isWf_trClos x : isWf x -> isWf (trClos x).
intros.
apply isWf_intro; intros.
elim H0 using trClos_ind; intros; trivial.
 rewrite <- H1; trivial.

 apply isWf_inv with y; trivial.
Qed.

Lemma trClos_trans x y z : isWf x -> y ∈ trClos x -> z ∈ trClos y -> z ∈ trClos x.
intros.
revert z H1; elim H0 using trClos_ind; intros; trivial.
 rewrite H1; trivial.

 apply H2.
 assert (isWf y0).
  apply isWf_inv with (trClos x); auto.
  apply isWf_trClos; trivial.
 elim H4 using trClos_ind; intros; trivial.
  apply isWf_inv with y0; trivial.

  rewrite <- H6; apply trClos_intro2 with y0; trivial.
  apply trClos_intro1; trivial.

  apply trClos_intro2 with y1; trivial.
Qed.

Hint Resolve isWf_trClos trClos_intro1 trClos_intro2.


Lemma isWf_ind2 x (P : set -> Prop) :
  (forall a, a ∈ trClos x -> (forall b, b ∈ a -> P b)-> P a) ->
  isWf x ->  P x.
intros.
generalize (trClos_intro1 _ H0).
pattern x at 1 3; elim H0 using isWf_ind; intros; eauto.
Qed.

End FirstOrder.

(*Module WellFoundedRecursion.
(** Well-founded recursion *)
(*
Section WellFoundedRecursion.


  (** Note: although we do not require {y|yRx} to be a set for all x,
      we cannot exploit relations with ordinal too big to fit in the isOrd class,
      because F(f) can only use f on inputs that form a set...
   *)
  Variable R : set -> set -> Prop.
  Hypothesis Rm : Proper (eq_set ==> eq_set ==> iff) R.
  
  Variable F : (set -> set) -> set -> set.
  Hypothesis Fm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) F.
Section Bounded.
  Variable xo : set.
  Hypothesis Fext : forall x f f', clos_refl_trans _ R x xo ->
    (forall y y', R y x -> y==y' -> f y == f' y') -> F f x == F f' x.

  Definition WFR_rel o y :=
    forall (P:set->set->Prop),
    Proper (eq_set ==> eq_set ==> iff) P ->
    (forall o' f, clos_refl_trans _ R o' xo -> morph1 f -> (forall n, R n o' -> P n (f n)) ->
     P o' (F f o')) ->
    P o y.

  Instance WFR_rel_morph : Proper (eq_set ==> eq_set ==> iff) WFR_rel.
apply morph_impl_iff2; auto with *.
do 4 red; unfold WFR_rel; intros.
rewrite <- H, <-H0; auto.
apply H1; auto.
Qed.

  Lemma WFR_rel_intro : forall x f,
    clos_refl_trans _ R x xo ->
    morph1 f ->
    (forall y, R y x -> WFR_rel y (f y)) ->
    WFR_rel x (F f x).
red; intros.
apply H3; trivial.
intros.
apply H1; trivial.
Qed.

  Lemma WFR_rel_inv : forall x y,
    WFR_rel x y ->
    exists2 f, morph1 f &
      (forall y, R y x -> WFR_rel y (f y)) /\
      y == F f x.
intros.
apply (@proj2 (WFR_rel x y)).
apply H; intros.
 do 3 red; intros.
 apply and_iff_morphism.
  apply WFR_rel_morph; auto with *.

  apply ex2_morph'; intros; auto with *.
  apply and_iff_morphism.
   apply fa_morph; intros y2.
   rewrite H0; reflexivity.

   rewrite H0,H1; reflexivity.
assert (WFR_relsub := fun n h => proj1 (H2 n h)); clear H2.
split.
 apply WFR_rel_intro; trivial.

 exists f; auto with *.
Qed.


  Lemma WFR_rel_fun :
    forall x y, WFR_rel x y -> forall y', WFR_rel x y' -> y == y'.
intros x y H.
apply H; intros.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 rewrite <- H1; rewrite <- H0 in H3; auto.
apply WFR_rel_inv in H3; destruct H3.
destruct H4.
rewrite H5; clear y' H5.
apply Fext; intros; auto with *.
apply H2; trivial.
rewrite H6 in H5|-*; auto.
Qed.

  Lemma WFR_rel_repl_rel :
    forall x, repl_rel x WFR_rel.
split; intros.
 rewrite <- H0; rewrite <- H1; trivial.

 apply WFR_rel_fun with x0; trivial.
Qed.

  Lemma WFR_rel_def : forall o, Acc R o -> clos_refl_trans _ R o xo -> exists y, WFR_rel o y.
induction 1; intros.
assert (forall z, R z x -> uchoice_pred (fun y => WFR_rel z y)).
 intros.
 destruct H0 with z; trivial.
  apply rt_trans with x; auto with *.
 split; intros.
  rewrite <- H4; trivial.
 split; intros.
  exists x0; trivial.
 apply WFR_rel_fun with z; trivial.
exists (F (fun z => uchoice (fun y => WFR_rel z y)) x).
apply WFR_rel_intro; intros; trivial.
 do 2 red; intros.
 apply uchoice_morph_raw; red; intros.
 apply WFR_rel_morph; trivial.
apply uchoice_def; auto.
Qed.

  Lemma WFR_rel_choice_pred : forall o, Acc R o -> clos_refl_trans _ R o xo ->
    uchoice_pred (fun y => WFR_rel o y).
split; intros.
 rewrite <- H1; trivial.
split; intros.
 apply WFR_rel_def; trivial.
 apply WFR_rel_fun with o; trivial.
Qed.

End Bounded.
  Definition WFR x := uchoice (fun y => WFR_rel x x y).

  Lemma WFR_eqn : forall o, Acc R o ->
     WFR o == F WFR o.
intros.
specialize WFR_rel_choice_pred with (1:=H); intro.
apply uchoice_def in H0.
apply WFR_rel_inv in H0.
destruct H0 as (f,fm,(?,?)).
unfold WFR at 1; rewrite H1.
apply Fext; intros; auto with *.
apply WFR_rel_fun with y; auto.
rewrite H3.
unfold WFR.
apply uchoice_def.
apply WFR_rel_choice_pred.
apply Acc_inv with o; trivial.
rewrite <- H3; trivial.
Qed.

  Lemma WFR_ind : forall x (P:set->set->Prop),
    Proper (eq_set ==> eq_set ==> iff) P ->
    Acc R x ->
    (forall y, clos_refl_trans _ R y x ->
     (forall x, R x y -> P x (WFR x)) ->
     P y (F WFR y)) ->
    P x (WFR x).
intros x P Pm wfx Hrec.
induction wfx; intros.
apply Acc_intro in H.
rewrite WFR_eqn; trivial.
apply Hrec; auto with *; intros.
Qed.

  Global Instance WFR_morph0 : morph1 WFR.
do 2 red; intros.
unfold WFR.
apply uchoice_morph_raw.
red; intros.
rewrite H; rewrite H0; reflexivity.
Qed.


End WellFoundedRecursion.
*)
Section WellFoundedRecursion.
(*Section WFR.*)
  Variable K : set -> Prop.
  Hypothesis Km : Proper (eq_set==>iff) K.
  
  Variable R : set -> set -> Prop.
  Hypothesis Rm : Proper (eq_set ==> eq_set ==> iff) R.

  Hypothesis Kacc : forall x, K x -> Acc R x.
  Hypothesis Ksub : forall x y, R x y -> K y -> K x.
  
  Variable F : (set -> set) -> set -> set.
  Hypothesis Fm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) F.
  Hypothesis Fext : forall x f f', K x ->
    (forall y y', R y x -> y==y' -> f y == f' y') -> F f x == F f' x.

  Definition WFR_rel o y :=
    forall (P:set->set->Prop),
    Proper (eq_set ==> eq_set ==> iff) P ->
    (forall o' f, K o' -> morph1 f -> (forall n, R n o' -> P n (f n)) ->
     P o' (F f o')) ->
    P o y.

  Instance WFR_rel_morph : Proper (eq_set ==> eq_set ==> iff) WFR_rel.
apply morph_impl_iff2; auto with *.
do 4 red; unfold WFR_rel; intros.
rewrite <- H, <-H0; auto.
apply H1; auto.
Qed.

  Lemma WFR_rel_intro x f :
    K x ->
    morph1 f ->
    (forall y, R y x -> WFR_rel y (f y)) ->
    WFR_rel x (F f x).
red; intros.
apply H3; trivial.
intros.
apply H1; trivial.
Qed.

  Lemma WFR_rel_inv x y :
    WFR_rel x y ->
    exists2 f, morph1 f &
      (forall y, R y x -> WFR_rel y (f y)) /\
      y == F f x.
clear Fext.
intros.
apply (@proj2 (WFR_rel x y)).
apply H; intros.
 do 3 red; intros.
 apply and_iff_morphism.
  apply WFR_rel_morph; auto with *.

  apply ex2_morph'; intros; auto with *.
  apply and_iff_morphism.
   apply fa_morph; intros y2.
   rewrite H0; reflexivity.

   rewrite H0,H1; reflexivity.
assert (WFR_relsub := fun n h => proj1 (H2 n h)); clear H2.
split.
 apply WFR_rel_intro; trivial.

 exists f; auto with *.
Qed.

  (** Particular case of bottom values: needs less assumptions... *)
  Lemma WFR_rel_inv_bot x y :
    (forall f f' x', x==x' -> F f x == F f' x') ->
    WFR_rel x y ->
    (forall y, ~ R y x) ->
    y == F (fun x => x) x.
clear Fm Fext.
intros Fm r bot.
generalize (@reflexivity _ eq_set _ x).
pattern x at 1 3, y.
apply r; intros.
 do 3 red; intros.
 apply impl_morph.
  rewrite H; reflexivity.
  intros eqx.
  apply eq_set_morph; trivial.
  transitivity (F (fun x => x) x);[symmetry|].
   apply Fm; auto with *.
   apply Fm; auto with *.
   rewrite <- eqx; trivial.
transitivity (F f x);[symmetry|].
 apply Fm; auto with *.
 apply Fm; auto with *.
Qed.

  Lemma WFR_rel_fun x y :
    WFR_rel x y -> forall y', WFR_rel x y' -> y == y'.
intros H.
apply H; intros.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 rewrite <- H1; rewrite <- H0 in H3; auto.
apply WFR_rel_inv in H3; auto.
destruct H3 as (f',?,(?,?)).
rewrite H5; clear y' H5.
apply Fext; intros; auto with *.
apply H2; trivial.
rewrite H6 in H5|-*; auto.
Qed.

  Lemma WFR_rel_repl_rel x : repl_rel x WFR_rel.
split; intros.
 rewrite <- H0; rewrite <- H1; trivial.

 apply WFR_rel_fun with x0; auto.
Qed.

  Lemma WFR_rel_def : forall o, K o -> exists y, WFR_rel o y.
intros o ko; generalize ko.
apply Kacc in ko.
induction ko; intros.
assert (forall z, R z x -> uchoice_pred (fun y => WFR_rel z y)).
 intros.
 destruct H0 with z; eauto.
 split; intros.
  rewrite <- H3; trivial.
 split; intros.
  exists x0; trivial.
 apply WFR_rel_fun with z; trivial.
exists (F (fun z => uchoice (fun y => WFR_rel z y)) x).
apply WFR_rel_intro; intros; trivial.
 do 2 red; intros.
 apply uchoice_morph_raw; red; intros.
 apply WFR_rel_morph; trivial.
apply uchoice_def; auto.
Qed.

  Lemma WFR_rel_choice_pred : forall o, K o ->
    uchoice_pred (fun y => WFR_rel o y).
split; intros.
 rewrite <- H0; trivial.
split; intros.
apply WFR_rel_def; trivial.
apply WFR_rel_fun with o; trivial.
Qed.

  Definition WFR x := uchoice (fun y => WFR_rel x y).

  (** Particular case of bottom values: needs less assumptions... *)
  Lemma WFR_eqn_bot o :
    K o ->
    (forall f f' x', o==x' -> F f o == F f' x') ->
    (forall o', ~ R o' o) ->
    WFR o == F (fun x => x) o.
clear Rm Fm Fext Kacc Ksub.
intros Ko Fm bot.
assert (WFR_rel o (F (fun x => x) o)).
 red; intros.
 apply H0; trivial.
  do 2 red; trivial.

  intros.
  elim bot with (1:=H1).
assert (u: forall x x', WFR_rel o x -> WFR_rel o x' -> x==x').
 intros.
 transitivity (F (fun x => x) o).
  apply WFR_rel_inv_bot with (2:=H0); trivial.
  symmetry; apply WFR_rel_inv_bot with (2:=H1); trivial.
symmetry; apply ZFrepl.uchoice_ext.
 split; intros.
  revert H1; apply iff_impl; apply WFR_rel_morph; auto with *.
 split; intros.
  exists (F (fun x => x) o); trivial.
 apply u; trivial.

 trivial.
Qed.
  
Lemma WFR_eqn : forall o, K o ->
     WFR o == F WFR o.
intros.
specialize WFR_rel_choice_pred with (1:=H); intro.
apply uchoice_def in H0.
apply WFR_rel_inv in H0; trivial.
destruct H0 as (f,fm,(?,?)).
unfold WFR at 1; rewrite H1.
apply Fext; intros; auto with *.
apply WFR_rel_fun with y; auto.
rewrite H3.
unfold WFR.
apply uchoice_def.
apply WFR_rel_choice_pred.
apply Ksub with o; trivial.
rewrite <- H3; trivial.
Qed.

  Lemma WFR_ind : forall x (P:set->set->Prop),
    Proper (eq_set ==> eq_set ==> iff) P ->
    K x ->
    (forall y, K y ->
     (forall x, R x y -> P x (WFR x)) ->
     P y (F WFR y)) ->
    P x (WFR x).
intros x P Pm wfx Hrec.
generalize wfx.
apply Kacc in wfx.
induction wfx; intros.
(*apply Acc_intro in H.*)
rewrite WFR_eqn; trivial.
apply Hrec; auto with *; intros.
apply H0; eauto.
Qed.

  Global Instance WFR_morph0 : morph1 WFR.
do 2 red; intros.
unfold WFR.
apply uchoice_morph_raw.
red; intros.
rewrite H; rewrite H0; reflexivity.
Qed.

End WellFoundedRecursion.

Global Instance WFR_morph :
    Proper ((eq_set==>iff)==>(eq_set==>eq_set==>iff)==>((eq_set ==> eq_set) ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) WFR.
do 5 red; intros.
apply uchoice_morph_raw.
red; intros.
unfold WFR_rel.
apply fa_morph; intros P.
apply fa_morph; intros Pm.
apply impl_morph.
2:intros; apply Pm; trivial.
apply fa_morph; intros o'.
apply fa_morph; intros f.
apply impl_morph; auto with *.
intros _.
apply fa_morph; intros fm.
apply impl_morph.
 apply fa_morph; intros n.
 apply impl_morph; auto with *.
 apply H0; auto with *.
intros _.
apply Pm; auto with *.
apply H1; auto with *.
Qed.

End WellFoundedRecursion.
*)
Hint Resolve isWf_morph.
