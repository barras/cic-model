Require Export basic.
Require Import ZF ZFpairs ZFrelations ZFnats.

(** Building a function by compatible union of functions
*)

Definition fcompat dom f g :=
  forall x, x ∈ dom -> cc_app f x == cc_app g x.
Instance fext_morph :
  Proper (eq_set ==> eq_set ==> eq_set ==> iff) fcompat.
apply morph_impl_iff3; auto with *.
do 5 red; intros.
unfold fcompat.
intros.
rewrite <- H0; rewrite <- H1.
apply H2.
rewrite H; trivial.
Qed.


Lemma fext_lam : forall A B f g,
    ext_fun A f ->
    ext_fun B g ->
    (forall x, x ∈ A -> x ∈ B) ->
    (forall x, x ∈ A -> f x == g x) ->
    fcompat A (cc_lam A f) (cc_lam B g).
red; intros.
rewrite cc_beta_eq; trivial.
rewrite cc_beta_eq; auto.
Qed.

Lemma fcompat_typ_eq : forall A f f',
  is_cc_fun A f ->
  is_cc_fun A f' ->
  fcompat A f f' ->
  f == f'.
intros.
rewrite cc_eta_eq' with (1:=H).
rewrite cc_eta_eq' with (1:=H0).
apply cc_lam_ext; auto with *.
red; intros.
rewrite <- H3; auto.
Qed.


Section ExtendFamily.

  Variable I : set.

  Variable A F : set -> set.
  Hypothesis extA : ext_fun I A.
  Hypothesis extF : ext_fun I F.

  Hypothesis in_prod : forall x, x ∈ I -> is_cc_fun (A x) (F x).

  Definition fdirected :=
    forall x y, x ∈ I -> y ∈ I -> fcompat (A x ∩ A y) (F x) (F y).

  Hypothesis fcomp : fdirected.

  Lemma fdir :
    forall x0 x1 x z,
    x0 ∈ I ->
    x1 ∈ I ->
    x ∈ A x0 ->
    z ∈ cc_app (F x1) x ->
    z ∈ cc_app (F x0) x.
intros.
assert (x ∈ A x1).
 rewrite <- couple_in_app in H2.
 specialize in_prod with (1:=H0).
 apply in_prod in H2.
 destruct H2 as (_,H2); rewrite fst_def in H2; trivial.
apply eq_elim with (cc_app (F x1) x); trivial.
apply fcomp; trivial.
rewrite inter2_def; auto.
Qed.

Lemma prd_union : is_cc_fun (sup I A) (sup I F).
red; intros.
rewrite sup_ax in H; trivial.
destruct H.
specialize in_prod with (1:=H).
apply in_prod in H0.
destruct H0; split; trivial.
rewrite sup_ax; eauto.
Qed.


Lemma prd_sup : forall x,
  x ∈ I ->
  fcompat (A x) (F x) (sup I F).
red; intros.
apply eq_intro; intros.
  rewrite <- couple_in_app.
  rewrite sup_ax; trivial.
  exists x; trivial.
  rewrite couple_in_app; trivial.

  rewrite <- couple_in_app in H1.
  rewrite sup_ax in H1; trivial.
  destruct H1.
  rewrite couple_in_app in H2.
  apply fdir with x1; trivial.
Qed.


Lemma prd_sup_lub : forall g,
  (forall x, x ∈ I -> fcompat (A x) (F x) g) ->
  fcompat (sup I A) (sup I F) g.
red; intros.
rewrite sup_ax in H0; trivial; destruct H0.
rewrite <- (prd_sup x0 H0 _); trivial.
apply H; trivial.
Qed.


End ExtendFamily.
