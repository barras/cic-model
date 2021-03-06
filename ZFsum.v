Require Import ZFnats.
Require Import ZFpairs.
Require Import ZFstable.

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
  prodcart (singl zero) X ∪ prodcart (singl (succ zero)) Y.

Instance sum_morph : morph2 sum.
do 3 red; unfold sum; intros.
rewrite H; rewrite H0; reflexivity.
Qed.

Lemma sum_ind : forall X Y a (P:Prop),
  (forall x, x ∈ X -> a == inl x -> P) ->
  (forall y, y ∈ Y -> a == inr y -> P) ->
  a ∈ sum X Y -> P.
unfold sum, inl, inr; intros.
apply union2_elim in H1; destruct H1.
 apply H with (snd a).
  apply snd_typ in H1; trivial.

  setoid_replace zero with (fst a).
   apply surj_pair with (1:=H1).

   apply fst_typ in H1; apply singl_elim in H1; auto with *.

 apply H0 with (snd a).
  apply snd_typ in H1; trivial.

  setoid_replace (succ zero) with (fst a).
   apply surj_pair with (1:=H1).

   apply fst_typ in H1; apply singl_elim in H1; auto with *.
Qed.

Lemma inl_typ : forall X Y x, x ∈ X -> inl x ∈ sum X Y.
unfold inl, sum; intros.
apply union2_intro1.
apply couple_intro; trivial.
apply singl_intro.
Qed.

Lemma inr_typ : forall X Y y, y ∈ Y -> inr y ∈ sum X Y.
unfold inr, sum; intros.
apply union2_intro2.
apply couple_intro; trivial.
apply singl_intro.
Qed.

Lemma sum_mono : forall X X' Y Y',
  X ⊆ X' -> Y ⊆ Y' -> sum X Y ⊆ sum X' Y'.
red; intros.
elim H1 using sum_ind; intros.
 rewrite H3.
 apply inl_typ; auto.

 rewrite H3.
 apply inr_typ; auto.
Qed.

Lemma sum_inv_l X Y x :
  inl x ∈ sum X Y -> x ∈ X.
intros.
apply sum_ind with (3:=H); intros.
 apply couple_injection in H1; destruct H1.
 rewrite H2; trivial.

 apply discr_sum in H1; contradiction.
Qed.
Lemma sum_inv_r X Y y :
  inr y ∈ sum X Y -> y ∈ Y.
intros.
apply sum_ind with (3:=H); intros.
 symmetry in H1; apply discr_sum in H1; contradiction.

 apply couple_injection in H1; destruct H1.
 rewrite H2; trivial.
Qed.

  Definition sum_case f g x :=
    cond_set (fst x == zero) (f (dest_sum x)) ∪
    cond_set (fst x == succ zero) (g (dest_sum x)).

Lemma sum_case_inl0 : forall f g x,
  (exists a, x == inl a) ->
  sum_case f g x == f (dest_sum x).
intros.
destruct H as (a,H).
assert (fst x == zero).
 rewrite H; unfold inl; rewrite fst_def; reflexivity.
unfold sum_case.
apply eq_intro; intros.
 apply union2_elim in H1; destruct H1; rewrite cond_set_ax in H1; destruct H1; trivial.
 rewrite H2 in H0; apply discr in H0; contradiction.

 apply union2_intro1.
 rewrite cond_set_ax; split; trivial.
Qed.

Lemma sum_case_inr0 : forall f g x,
  (exists b, x == inr b) ->
  sum_case f g x == g (dest_sum x).
intros.
destruct H as (b,H).
assert (fst x == succ zero).
 rewrite H; unfold inr; rewrite fst_def; reflexivity.
unfold sum_case.
apply eq_intro; intros.
 apply union2_elim in H1; destruct H1; rewrite cond_set_ax in H1; destruct H1; trivial.
 rewrite H0 in H2; apply discr in H2; contradiction.

 apply union2_intro2.
 rewrite cond_set_ax; split; trivial.
Qed.

Lemma sum_case_ext : forall A1 A2 B1 B2 B1' B2',
  eq_fun A1 B1 B1' ->
  eq_fun A2 B2 B2' ->
  eq_fun (sum A1 A2) (sum_case B1 B2) (sum_case B1' B2').
red; intros.
apply sum_ind with (3:=H1); intros.
 rewrite sum_case_inl0.
 2:exists x0; trivial.
 rewrite sum_case_inl0.
 2:exists x0; rewrite <- H2; trivial.
 apply H.
 2:rewrite H2; reflexivity.
 rewrite H4; rewrite dest_sum_inl; trivial.

 rewrite sum_case_inr0.
 2:exists y; trivial.
 rewrite sum_case_inr0.
 2:exists y; rewrite <- H2; trivial.
 apply H0.
 2:rewrite H2; reflexivity.
 rewrite H4; rewrite dest_sum_inr; trivial.
Qed.

Instance sum_case_morph : Proper
  ((eq_set ==> eq_set) ==> (eq_set ==> eq_set) ==> eq_set ==> eq_set)
  sum_case.
do 4 red; intros.
unfold sum_case.
apply union2_morph; (apply cond_set_morph2; [rewrite H1; reflexivity|intros]).
 apply H; apply snd_morph; trivial.
 apply H0; apply snd_morph; trivial.
Qed.

Lemma sum_case_ind0 :
  forall A B f g x (P:set->Prop),
  Proper (eq_set ==> iff) P ->
  x ∈ sum A B ->
  (forall a, a ∈ A -> x == inl a -> P (f (dest_sum x))) ->
  (forall b, b ∈ B -> x == inr b -> P (g (dest_sum x))) ->
  P (sum_case f g x).
intros.
apply sum_ind with (3:=H0); intros.
 rewrite sum_case_inl0; eauto.
 rewrite sum_case_inr0; eauto.
Qed.


Lemma sum_case_inl : forall f g a, morph1 f ->
  sum_case f g (inl a) == f a.
intros.
rewrite sum_case_inl0.
 rewrite dest_sum_inl; reflexivity.

 exists a; reflexivity.
Qed.

Lemma sum_case_inr : forall f g b, morph1 g ->
  sum_case f g (inr b) == g b.
intros.
rewrite sum_case_inr0.
 rewrite dest_sum_inr; reflexivity.

 exists b; reflexivity.
Qed.

Lemma sum_case_ind :
  forall A B f g (P:set->Prop),
  Proper (eq_set ==> iff) P ->
  morph1 f ->
  morph1 g ->
  (forall a, a ∈ A -> P (f a)) ->
  (forall b, b ∈ B -> P (g b)) ->
  forall x,
  x ∈ sum A B ->
  P (sum_case f g x).
intros.
apply sum_ind with (3:=H4); intros.
 rewrite H6.
 rewrite sum_case_inl; auto.

 rewrite H6.
 rewrite sum_case_inr; auto.
Qed.


Lemma sum_is_ext : forall o F G,
  ext_fun o F ->
  ext_fun o G ->
  ext_fun o (fun y => sum (F y) (G y)).
do 2 red; intros.
rewrite (H x x'); trivial.
rewrite (H0 x x'); trivial.
reflexivity.
Qed.
Hint Resolve sum_is_ext.

Lemma sum_stable_class K F G :
  morph1 F ->
  morph1 G ->
  stable_class K F ->
  stable_class K G ->
  stable_class K (fun y => sum (F y) (G y)).
intros Fm Gm Fs Gs.
red; red ;intros.
destruct inter_wit with (2:=H0) as (w,winX).
 do 2 red; intros.
 rewrite H1; reflexivity.
assert (forall x, x ∈ X -> z ∈ sum (F x) (G x)).
 intros.
 apply inter_elim with (1:=H0).
 rewrite replf_ax.
  exists x; auto with *.

  red; red; intros.
  rewrite H3; reflexivity.
clear H0.
assert (z ∈ sum (F w) (G w)) by auto.
apply sum_ind with (3:=H0); intros.
 rewrite H3; apply inl_typ.
 apply Fs; eauto.
 apply inter_intro.
  intros.
  rewrite replf_ax in H4.
  2:red;red;intros;apply Fm; trivial.
  destruct H4.
  rewrite H5; clear H5 y.
  assert (z ∈ sum (F x0) (G x0)) by auto.
  apply sum_ind with (3:=H5); intros.
   rewrite H7 in H3; apply inl_inj in H3; rewrite <-H3; trivial.

   rewrite H3 in H7; apply discr_sum in H7; contradiction.

  exists (F w).
  rewrite replf_ax.
  2:red;red;intros;apply Fm;trivial.
  exists w; auto with *.

 rewrite H3; apply inr_typ.
 apply Gs; eauto.
 apply inter_intro.
  intros.
  rewrite replf_ax in H4.
  2:red;red;intros;apply Gm; trivial.
  destruct H4.
  rewrite H5; clear H5 y0.
  assert (z ∈ sum (F x) (G x)) by auto.
  apply sum_ind with (3:=H5); intros.
   rewrite H7 in H3; apply discr_sum in H3; contradiction.

   rewrite H7 in H3; apply inr_inj in H3; rewrite <-H3; trivial.

  exists (G w).
  rewrite replf_ax.
  2:red;red;intros;apply Gm;trivial.
  exists w; auto with *.
Qed.
