Require Export basic.
Require Import ZF ZFrelations ZFnats ZFord ZFstable ZFcoc.
Import IZF.


Definition is_cc_fun A f :=
  forall c, c \in f -> c == couple (fst c) (snd c) /\ fst c \in A.

Instance is_cc_fun_morph : Proper (eq_set ==> eq_set ==> iff) is_cc_fun.
apply morph_impl_iff2; auto with *.
do 5 red; intros.
rewrite <- H; rewrite <- H0 in H2; auto.
Qed.


Lemma is_cc_fun_lam A F :
  ext_fun A F ->
  is_cc_fun A (cc_lam A F).
intros eF.
unfold cc_lam; red; intros.
apply union_elim in H; destruct H.
rewrite replf_ax in H0.
2:apply cc_lam_fun2; trivial.
destruct H0.
rewrite H1 in H; clear x H1.
rewrite replf_ax in H.
2:apply cc_lam_fun1.
destruct H.
rewrite H1; rewrite fst_def; rewrite snd_def; auto with *.
Qed.

Lemma cc_prod_is_cc_fun : forall A B f,
  f \in cc_prod A B -> is_cc_fun A f.
red; intros.
unfold cc_prod in H.
rewrite replf_ax in H.
2:apply ZFcoc.cc_prod_fun1.
destruct H.
rewrite H1 in H0; clear f H1.
unfold cc_lam in H0.
apply union_elim in H0; destruct H0.
rewrite replf_ax in H1.
2:apply ZFcoc.cc_lam_fun2.
2:red; red; intros.
2:rewrite H3; reflexivity.
destruct H1.
rewrite H2 in H0; clear x0 H2.
rewrite replf_ax in H0.
2:apply ZFcoc.cc_lam_fun1.
destruct H0.
rewrite H2; rewrite fst_def; rewrite snd_def; auto with *.
Qed.
Hint Resolve cc_prod_is_cc_fun.


Lemma couple_in_app : forall x z f,
  couple x z \in f <-> z \in cc_app f x.
unfold cc_app, rel_image; split; intros.
 apply subset_intro.
  apply union_intro with (pair x z).
   apply pair_intro2.

   apply union_intro with (couple x z).
    apply pair_intro2.

    apply subset_intro; trivial.
    apply fst_def.

  exists x.
  red; apply subset_intro; trivial.
  apply fst_def.

 rewrite subset_ax in H; destruct H.
 destruct H0.
 destruct H1.
 red in H1.
 rewrite subset_ax in H1; destruct H1.
 destruct H2.
 rewrite <- H0 in H1.
 rewrite <- H2 in H3; rewrite fst_def in H3.
 rewrite H3 in H1; trivial.
Qed.

Lemma cc_eta_eq' : forall dom f,
  is_cc_fun dom f ->
  f == cc_lam dom (fun x => cc_app f x).
unfold is_cc_fun.
intros.
apply eq_intro; intros.
 specialize H with (1:=H0); destruct H.
 unfold cc_lam.
 eapply union_intro.
 2:rewrite replf_ax.
 3:apply ZFcoc.cc_lam_fun2.
 3:do 2 red; intros; apply cc_app_morph; auto with *.
 2:exists (fst z); trivial.
 2:reflexivity.
 rewrite replf_ax.
 2:apply ZFcoc.cc_lam_fun1.
 exists (snd z); trivial.
 rewrite H in H0; apply couple_in_app; trivial.

 unfold cc_lam in H0.
 apply union_elim in H0; destruct H0.
 rewrite replf_ax in H1.
 2:apply ZFcoc.cc_lam_fun2.
 2:do 2 red; intros; apply cc_app_morph; auto with *.
 destruct H1.
 rewrite H2 in H0; clear x H2.
 rewrite replf_ax in H0.
 2:apply ZFcoc.cc_lam_fun1.
 destruct H0.
 rewrite H2; apply couple_in_app; trivial.
Qed.


Definition fcompat dom f g :=
  forall x, x \in dom -> cc_app f x == cc_app g x.
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
    (forall x, x \in A -> x \in B) ->
    (forall x, x \in A -> f x == g x) ->
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

  Hypothesis in_prod : forall x, x \in I -> is_cc_fun (A x) (F x).

  Definition fdirected :=
    forall x y, x \in I -> y \in I -> fcompat (inter2 (A x) (A y)) (F x) (F y).

  Hypothesis fcomp : fdirected.

  Lemma fdir :
    forall x0 x1 x z,
    x0 \in I ->
    x1 \in I ->
    x \in A x0 ->
    z \in cc_app (F x1) x ->
    z \in cc_app (F x0) x.
intros.
assert (x \in A x1).
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
  x \in I ->
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
  specialize in_prod with (1:=H1).
  apply fdir with x1; trivial.
Qed.


Lemma prd_sup_lub : forall g,
  (forall x, x \in I -> fcompat (A x) (F x) g) ->
  fcompat (sup I A) (sup I F) g.
red; intros.
rewrite sup_ax in H0; trivial; destruct H0.
rewrite <- (prd_sup x0 H0 _); trivial.
apply H; trivial.
Qed.


End ExtendFamily.
