Require Import ZF ZFnats ZFord.
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
  (forall x x', x == x' -> P x -> P x') ->
  (forall a, isWf a -> (forall b, b \in a -> P b)-> P a) ->
  forall x, isWf x ->  P x.
intros.
apply proj2 with (isWf x).
red in H1.
pattern x; apply H1; clear x H1; intros.
 destruct H2; split.
  apply isWf_ext with x; trivial.
  apply H with x; trivial.

 assert (isWf a).
  apply isWf_intro; intros.
  elim H1 with a0; trivial.
 split; trivial.
 apply H0; intros; trivial.
 elim H1 with b; trivial.
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

Lemma isWf_N : isWf N.
apply isWf_intro; intros.
elim H using N_ind; intros.
 apply isWf_ext with n; trivial.
 apply isWf_zero.
 apply isWf_succ; trivial.
Qed.

Lemma isWf_antirefl : forall x, isWf x -> ~ x \in x.
intros.
elim H using isWf_ind; clear x H; intros.
 rewrite <- H; trivial.

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


End WellFoundedSets.

