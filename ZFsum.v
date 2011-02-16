Require Import ZFnats.
Require Import ZFpairs.
Import IZF.

Definition inl x := couple zero x.
Definition inr y := couple (succ zero) y.
Definition dest_sum p := snd p.

Instance inl_morph : morph1 inl.
unfold inl; do 2 red; intros.
rewrite H; reflexivity.
Qed.
Instance inr_morph : morph1 inr.
unfold inr; do 2 red; intros.
rewrite H; reflexivity.
Qed.
Instance dest_sum_morph : morph1 dest_sum.
Proof snd_morph.

Lemma discr_sum : forall x y, ~ inl x == inr y.
unfold inl, inr; red; intros.
apply (discr zero).
rewrite <- (fst_def (succ zero) y).
rewrite <- H.
rewrite fst_def; reflexivity.
Qed.

Lemma dest_sum_inl : forall x, dest_sum (inl x) == x.
unfold dest_sum, inl; intros.
apply snd_def.
Qed.

Lemma dest_sum_inr : forall y, dest_sum (inr y) == y.
unfold dest_sum, inr; intros.
apply snd_def.
Qed.

Lemma inl_inj : forall x y, inl x == inl y -> x == y.
intros.
rewrite <- (dest_sum_inl x).
rewrite <- (dest_sum_inl y).
rewrite H; reflexivity.
Qed.

Lemma inr_inj : forall x y, inr x == inr y -> x == y.
intros.
rewrite <- (dest_sum_inr x).
rewrite <- (dest_sum_inr y).
rewrite H; reflexivity.
Qed.

Definition sum X Y :=
  subset (prodcart (succ (succ zero)) (union2 X Y))
    (fun p => (fst p == zero /\ snd p \in X) \/
              (fst p == succ zero /\ snd p \in Y)).

Instance sum_morph : morph2 sum.
do 3 red; unfold sum; intros.
apply subset_morph; trivial.
 rewrite H; rewrite H0; reflexivity.

 red; intros.
 rewrite H; rewrite H0; reflexivity.
Qed.

Lemma inl_typ : forall X Y x, x \in X -> inl x \in sum X Y.
unfold inl, sum; intros.
apply subset_intro.
 apply couple_intro.
  apply succ_intro2; apply succ_intro1; reflexivity.

  apply union2_intro1; trivial.

 left.
 split.
  apply fst_def.

  rewrite snd_def; trivial.
Qed.

Lemma inr_typ : forall X Y y, y \in Y -> inr y \in sum X Y.
unfold inr, sum; intros.
apply subset_intro.
 apply couple_intro.
  apply succ_intro1; reflexivity.

  apply union2_intro2; trivial.

 right.
 split.
  apply fst_def.

  rewrite snd_def; trivial.
Qed.

Lemma sum_ind : forall X Y a (P:Prop),
  (forall x, x \in X -> a == inl x -> P) ->
  (forall y, y \in Y -> a == inr y -> P) ->
  a \in sum X Y -> P.
unfold sum, inl, inr; intros.
elim subset_elim2 with (1:=H1); intros.
rewrite <- H2 in H3.
clear x H2.
destruct H3 as [(eq1,eq2)|(eq1,eq2)].
 apply H with (snd a); trivial.
 rewrite <- eq1.
 apply surj_pair with (succ (succ zero)) (union2 X Y).
 apply subset_elim1 with (1:=H1).

 apply H0 with (snd a); trivial.
 rewrite <- eq1.
 apply surj_pair with (succ (succ zero)) (union2 X Y).
 apply subset_elim1 with (1:=H1).
Qed.

Lemma sum_mono : forall X X' Y Y',
  X \incl X' -> Y \incl Y' -> sum X Y \incl sum X' Y'.
red; intros.
elim H1 using sum_ind; intros.
 rewrite H3.
 apply inl_typ; auto.

 rewrite H3.
 apply inr_typ; auto.
Qed.
