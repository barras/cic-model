Require Export basic.
Require Import ZF ZFrelations ZFnats ZFord ZFstable ZFcoc.
Import IZF.

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

Lemma dep_func_has_couples : forall f A B,
  ext_fun A B ->
  f \in dep_func A B ->
  forall a, a \in f ->
  exists2 x, x \in A & exists2 y, y \in B x & a == couple x y.
unfold dep_func.
intros.
 rewrite subset_ax in H0.
 destruct H0.
 destruct H2.
 assert (f_fun := func_is_function _ _ _ H0).
 unfold func in H0.
 rewrite subset_ax in H0; destruct H0.
 destruct H4.
 destruct H5.
 unfold rel in H0.
 rewrite power_ax in H0.
 specialize H0 with (1:=H1).
 assert (fst a \in A).
  apply fst_typ with (1:=H0).
 exists (fst a); trivial.
 specialize H5 with (1:=H7).
 specialize H3 with (1:=H7).
 destruct H5.
 assert (app x (fst a) == snd a).
  rewrite <- H2.
  apply app_defined; trivial.
  red.
  rewrite <- (surj_pair _ _ _ H0); trivial.
 exists (app x (fst a)); trivial.
 rewrite H9; apply (surj_pair _ _ _ H0); trivial.
Qed.


Lemma cc_prod_couples : forall f a A B,
  ext_fun A B ->
  f \in cc_prod A B ->
  a \in f ->
  exists2 x, x \in A & exists2 y, y \in B x & exists2 z, z \in y & a == couple x z.
unfold cc_prod.
intros.
rewrite replf_ax in H0.
2:apply ZFcoc.cc_prod_fun1.
destruct H0.
rewrite H2 in H1; clear H2 f.
unfold cc_lam in H1.
rewrite union_ax in H1.
destruct H1.
rewrite replf_ax in H2.
2:apply ZFcoc.cc_lam_fun2.
2:red; red; intros.
2:rewrite H4; reflexivity.
destruct H2.
exists x1; trivial.
rewrite H3 in H1; clear H3 x0.
rewrite replf_ax in H1.
2:apply ZFcoc.cc_lam_fun1.
destruct H1.
exists (app x x1).
 apply dep_func_elim with (1:=H0); trivial.

 exists x0; trivial.
Qed.


Lemma cc_prod_intro_couples : forall f A B,
  ext_fun A B ->
  (forall a, a \in f -> exists2 x, x \in A & exists z, a == couple x z) ->
  (forall x, x \in A -> exists2 y, y \in B x &
     forall z, (couple x z \in f <-> z \in y)) ->
  f \in cc_prod A B.
intros.
unfold cc_prod.
rewrite replf_ax.
2:apply ZFcoc.cc_prod_fun1.
exists (lam A (fun x => cc_app f x)).
 apply dep_func_intro; intros; trivial.
  red; red; intros.
  rewrite H3; reflexivity.

  destruct H1 with (1:=H2).
  assert (x0 == cc_app f x).
   apply eq_intro; intros.
    rewrite <- couple_in_app.
    rewrite H4; trivial.

    rewrite <- H4.
    rewrite couple_in_app; trivial.
  rewrite <- H5; trivial.

 apply eq_intro; intros.
  unfold cc_lam.
  destruct (H0 _ H2).
  destruct H4.
  apply union_intro with (replf (cc_app f x) (fun y' => couple x y')).
   apply replf_intro with x0; trivial.
   rewrite <- couple_in_app.
   rewrite <- H4; trivial.

   apply replf_intro with x; auto.
    apply ZFcoc.cc_lam_fun2.
    red; red; intros.
    rewrite H6; reflexivity.

    apply replf_ext; intros; auto.
     rewrite beta_eq in H5; auto.
      apply replf_intro with x1; auto with *.

      red; red; intros.
      rewrite H7; reflexivity.

     rewrite replf_ax in H5; auto.
     destruct H5.
     exists x1; auto.
     rewrite beta_eq; auto.
     red; red; intros.
     rewrite H8; reflexivity.

  unfold cc_lam in H2.
  rewrite union_ax in H2; destruct H2.
  rewrite replf_ax in H3.
   destruct H3.
   rewrite H4 in H2; clear H4 x.
   rewrite replf_ax in H2; auto.
   destruct H2.
   rewrite H4; clear H4 z.
   rewrite beta_eq in H2; auto.
    rewrite couple_in_app; auto.
    red; red; intros.
    rewrite H5; reflexivity.

  apply cc_lam_fun2.
  red; red; intros.
  rewrite H5; reflexivity.
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


Section ExtendFamily.

  Variable I : set.

  Variable A B F : set -> set.
  Hypothesis extA : ext_fun I A.
  Hypothesis extB : forall x, x \in I -> ext_fun (A x) B.
  Hypothesis extF : ext_fun I F.

  Hypothesis in_prod : forall x, x \in I -> F x \in cc_prod (A x) B.

  Definition fdirected :=
    forall x y, x \in I -> y \in I -> fcompat (inter2 (A x) (A y)) (F x) (F y).

  Hypothesis fcomp : fdirected.

  Let extB' : ext_fun (sup I A) B.
red; red; intros.
rewrite sup_ax in H; trivial; destruct H.
apply (extB x0); trivial.
Qed.

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
 destruct cc_prod_couples with (2:=in_prod) (3:=H2); auto.
 destruct H4.
 destruct H5.
 apply couple_injection in H6; destruct H6.
 rewrite H6; trivial.
apply eq_elim with (cc_app (F x1) x); trivial.
apply fcomp; trivial.
rewrite inter2_def; auto.
Qed.

Lemma prd_union : sup I F \in cc_prod (sup I A) B.
apply cc_prod_intro_couples; intros; trivial.
 rewrite sup_ax in H; trivial.
 destruct H.
 specialize in_prod with (1:=H).
 destruct cc_prod_couples with (2:=in_prod) (3:=H0); auto.
 destruct H2.
 destruct H3.
 exists x0.
  rewrite sup_ax; trivial.
  exists x; trivial.

  exists x2; trivial.

 rewrite sup_ax in H; trivial.
 destruct H.
 assert (H1' := in_prod _ H).
 exists (cc_app (F x0) x).
  apply cc_prod_elim with (1:=H1'); trivial.

  intros.
  rewrite sup_ax; trivial.
  split; intros.
   destruct H1.
   rewrite couple_in_app in H2.
   specialize in_prod with (1:=H1).
   apply fdir with x1; trivial.

   exists x0; trivial.
   rewrite couple_in_app; auto.
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
