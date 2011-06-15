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

Lemma sum_mono : forall X X' Y Y',
  X \incl X' -> Y \incl Y' -> sum X Y \incl sum X' Y'.
red; intros.
elim H1 using sum_ind; intros.
 rewrite H3.
 apply inl_typ; auto.

 rewrite H3.
 apply inr_typ; auto.
Qed.

  Definition sum_case f g x :=
    union
   (union2 (subset (singl (f (snd x))) (fun _ => fst x == zero))
           (subset (singl (g (snd x))) (fun _ => fst x == succ zero))).

Lemma sum_case_ext : forall A1 A2 B1 B2 B1' B2',
  eq_fun A1 B1 B1' ->
  eq_fun A2 B2 B2' ->
  eq_fun (sum A1 A2) (sum_case B1 B2) (sum_case B1' B2').
red; intros.
unfold sum_case.
apply union_morph.
apply union2_morph.
 assert (fst x == zero -> snd x \in A1).
  apply sum_ind with (3:=H1); intros.
   rewrite H4; unfold inl; rewrite snd_def; trivial.

   rewrite H4 in H5; unfold inr in H5; rewrite fst_def in H5.
   apply discr in H5; contradiction.
 apply subset_ext; intros.
  apply subset_intro.
  2:rewrite H2; trivial.
  revert H4; apply eq_elim; apply singl_morph.
  rewrite <- H2 in H5.
  symmetry; apply H; auto.
  apply snd_morph; trivial.

  rewrite subset_ax in H4; destruct H4.
  destruct H5.
  revert H4; apply eq_elim; apply singl_morph; apply H; auto with *.
  apply snd_morph; trivial.

  exists x0; auto with *.
  rewrite subset_ax in H4; destruct H4.
  destruct H5.
  rewrite <- H2; trivial.

 assert (fst x == succ zero -> snd x \in A2).
  apply sum_ind with (3:=H1); intros.
   rewrite H4 in H5; unfold inl in H5; rewrite fst_def in H5.
   symmetry in H5; apply discr in H5; contradiction.

   rewrite H4; unfold inr; rewrite snd_def; trivial.
 apply subset_ext; intros.
  apply subset_intro.
  2:rewrite H2; trivial.
  revert H4; apply eq_elim; apply singl_morph.
  rewrite <- H2 in H5.
  symmetry; apply H0; auto.
  apply snd_morph; trivial.

  rewrite subset_ax in H4; destruct H4.
  destruct H5.
  revert H4; apply eq_elim; apply singl_morph; apply H0; auto with *.
  apply snd_morph; trivial.

  exists x0; auto with *.
  rewrite subset_ax in H4; destruct H4.
  destruct H5.
  rewrite <- H2; trivial.
Qed.

Lemma sum_case_inl0 : forall f g x,
  (exists a, x == inl a) ->
  sum_case f g x == f (dest_sum x).
intros.
destruct H as (a,H).
unfold sum_case.
apply eq_intro; intros.
 rewrite union_ax in H0; destruct H0.
 apply union2_elim in H1; destruct H1.
  apply subset_elim1 in H1.
  apply singl_elim in H1.
  change snd with dest_sum in H1.
  rewrite <- H1; trivial.

  apply subset_elim2 in H1; destruct H1. 
  rewrite H in H2; unfold inl in H2; rewrite fst_def in H2.
  symmetry in H2; apply discr in H2; contradiction.

 apply union_intro with (f (dest_sum x)); trivial.
 apply union2_intro1.
 apply subset_intro.
  apply singl_intro.
  rewrite H; unfold inl; rewrite fst_def; reflexivity.
Qed.

Lemma sum_case_inr0 : forall f g x,
  (exists b, x == inr b) ->
  sum_case f g x == g (dest_sum x).
intros.
destruct H as (b,H).
unfold sum_case.
apply eq_intro; intros.
 rewrite union_ax in H0; destruct H0.
 apply union2_elim in H1; destruct H1.
  apply subset_elim2 in H1; destruct H1. 
  rewrite H in H2; unfold inr in H2; rewrite fst_def in H2.
  apply discr in H2; contradiction.

  apply subset_elim1 in H1.
  apply singl_elim in H1.
  change snd with dest_sum in H1.
  rewrite <- H1; trivial.

 apply union_intro with (g (dest_sum x)); trivial.
 apply union2_intro2.
 apply subset_intro.
  apply singl_intro.
  rewrite H; unfold inr; rewrite fst_def; reflexivity.
Qed.

Lemma sum_case_ind0 :
  forall A B f g x (P:set->Prop),
  Proper (eq_set ==> iff) P ->
  x \in sum A B ->
  (forall a, a \in A -> x == inl a -> P (f (dest_sum x))) ->
  (forall b, b \in B -> x == inr b -> P (g (dest_sum x))) ->
  P (sum_case f g x).
intros.
apply sum_ind with (3:=H0); intros.
 rewrite sum_case_inl0; eauto.
 rewrite sum_case_inr0; eauto.
Qed.



Instance sum_case_morph : Proper
  ((eq_set ==> eq_set) ==> (eq_set ==> eq_set) ==> eq_set ==> eq_set)
  sum_case.
do 4 red; intros.
unfold sum_case.
apply union_morph; apply union2_morph.
 apply subset_morph.
  apply singl_morph; apply H; rewrite H1; reflexivity.
  red; intros; rewrite H1; reflexivity.
 apply subset_morph.
  apply singl_morph; apply H0; rewrite H1; reflexivity.
  red; intros; rewrite H1; reflexivity.
Qed.

Lemma sum_case_inl : forall f g a, morph1 f ->
  sum_case f g (inl a) == f a.
intros.
unfold sum_case.
apply eq_intro; intros.
 rewrite union_ax in H0; destruct H0.
 apply union2_elim in H1; destruct H1.
  apply subset_elim1 in H1.
  apply singl_elim in H1.
  change snd with dest_sum in H1.
  rewrite dest_sum_inl in H1.
  rewrite <- H1; trivial.

  apply subset_elim2 in H1; destruct H1. 
  unfold inl in H2; rewrite fst_def in H2.
  symmetry in H2; apply discr in H2; contradiction.

 apply union_intro with (f a); trivial.
 apply union2_intro1.
 apply subset_intro.
  unfold inl; rewrite snd_def; apply singl_intro.
  unfold inl; rewrite fst_def; reflexivity.
Qed.

Lemma sum_case_inr : forall f g b, morph1 g ->
  sum_case f g (inr b) == g b.
intros.
unfold sum_case.
apply eq_intro; intros.
 rewrite union_ax in H0; destruct H0.
 apply union2_elim in H1; destruct H1.
  apply subset_elim2 in H1; destruct H1. 
  unfold inr in H2; rewrite fst_def in H2.
  apply discr in H2; contradiction.

  apply subset_elim1 in H1.
  apply singl_elim in H1.
  change snd with dest_sum in H1.
  rewrite dest_sum_inr in H1.
  rewrite <- H1; trivial.

 apply union_intro with (g b); trivial.
 apply union2_intro2.
 apply subset_intro.
  unfold inr; rewrite snd_def; apply singl_intro.
  unfold inr; rewrite fst_def; reflexivity.
Qed.

Lemma sum_case_ind :
  forall A B f g (P:set->Prop),
  Proper (eq_set ==> iff) P ->
  morph1 f ->
  morph1 g ->
  (forall a, a \in A -> P (f a)) ->
  (forall b, b \in B -> P (g b)) ->
  forall x,
  x \in sum A B ->
  P (sum_case f g x).
intros.
apply sum_ind with (3:=H4); intros.
 rewrite H6.
 rewrite sum_case_inl; auto.

 rewrite H6.
 rewrite sum_case_inr; auto.
Qed.

