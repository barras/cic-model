
Require Import Setoid.
Require Export ZF ZFpairs ZFrelations.
Import IZF.

(* CC *)

(* Lambda: Aczel's encoding of functions *)

Definition cc_lam (x:set) (y:set->set) : set :=
  union (replf x
    (fun x' => replf (y x') (fun y' => couple x' y'))).

Lemma cc_lam_fun1 : forall x x',
  ext_fun x (fun y' => couple x' y').
Proof.
do 2 red; intros.
rewrite H0; reflexivity.
Qed.

Lemma cc_lam_fun2 : forall x y,
  ext_fun x y ->
  ext_fun x
    (fun x' => replf (y x') (fun y' => couple x' y')).
Proof.
do 2 red; intros.
apply replf_morph; auto.
red; intros.
rewrite H1; rewrite H3; reflexivity.
Qed.
Hint Resolve cc_lam_fun1 cc_lam_fun2.

Lemma cc_lam_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  cc_lam x1 f1 == cc_lam x2 f2.
unfold cc_lam in |- *; intros.
assert (ext_fun x1 f1).
 apply eq_fun_ext in H0; trivial.
assert (ext_fun x2 f2).
 do 2 red; intros.
 rewrite <-H in H2.
 rewrite <- (H0 x x'); trivial.
 symmetry; apply H0; trivial; try reflexivity.
apply union_morph.
apply replf_morph; auto.
red; intros.
apply replf_morph; auto.
red; intros.
rewrite H4; rewrite H6; reflexivity.
Qed.

Lemma cc_impredicative_lam : forall dom F,
  ext_fun dom F ->
  (forall x, x \in dom -> F x == empty) ->
  cc_lam dom F == empty.
Proof.
unfold cc_lam in |- *; intros.
apply empty_ext.
red in |- *; intros.
elim union_elim with (1 := H1); clear H1; intros.
elim replf_elim with (2 := H2); clear H2; auto; intros.
rewrite H3 in H1; clear H3 x0.
elim replf_elim with (2 := H1); clear H1; intros; trivial.
apply empty_ax with x0.
setoid_replace empty with (F x1); auto.
symmetry; auto.
Qed.

(* Application *)

Definition cc_app (x y:set) : set :=
  rel_image (subset x (fun p => fst p == y)).

Instance cc_app_morph : morph2 cc_app.
do 3 red; unfold cc_app in |- *; intros.
apply rel_image_morph.
apply subset_morph; trivial.
red; intros.
rewrite H0.
reflexivity.
Qed.

(* Beta conversion *)

Lemma cc_beta_eq:
  forall dom F x,
  ext_fun dom F ->
  x \in dom ->
  cc_app (cc_lam dom F) x == F x.
Proof.
intros.
unfold cc_app, cc_lam in |- *.
unfold rel_image, rel_app in |- *.
apply eq_intro; intros.
 elim subset_elim2 with (1:=H1); clear H1; intros.
 destruct H2.
 specialize subset_elim1 with (1:=H2); intro.
 elim subset_elim2 with (1:=H2); clear H2; intro.
 elim union_elim with (1:=H3); clear H3; intros.
 elim replf_elim with (2:=H3); clear H3; intros; auto.
 rewrite <- H1 in H2, H4 |-.
 rewrite H6 in H2; clear H6 x3.
 elim replf_elim with (2:=H2); clear H2; intros; trivial.
 apply couple_injection in H6; destruct H6.
 rewrite <- H4 in H5; rewrite fst_def in H5.
 rewrite H7; rewrite H5 in H6.
 setoid_replace (F x) with (F x4); auto.

 apply subset_intro.
  apply union_intro with (pair x z).
   apply pair_intro2.
   apply union_intro with (couple x z).
    unfold couple.
    apply pair_intro2.

    apply subset_intro.
     apply union_intro
       with (replf (F x) (fun y' => couple x y')).
      apply replf_intro with z; trivial; reflexivity.
      apply replf_intro with x; auto; reflexivity.

     apply fst_def.

  exists x.
  apply subset_intro.
   apply union_intro
     with (replf (F x) (fun y' => couple x y')).
    apply replf_intro with z; trivial; reflexivity.
    apply replf_intro with x; auto; reflexivity.

   apply fst_def.
Qed.

(* Typing: dependent products *)

Definition cc_prod (x:set) (y:set->set) : set :=
  replf (dep_func x y)
    (fun f => cc_lam x (fun x' => app f x')).

Lemma cc_prod_fun1 : forall A x,
  ext_fun A (fun f => cc_lam x (fun x' => app f x')).
Proof.
do 2 red; intros.
apply cc_lam_ext; try reflexivity; red; intros.
apply app_morph; trivial.
Qed.
Hint Resolve cc_prod_fun1.


Lemma cc_prod_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  cc_prod x1 f1 == cc_prod x2 f2.
Proof.
unfold cc_prod in |- *; intros.
apply replf_morph; intros; trivial.
 apply dep_func_ext; trivial.

 red; intros.
 apply cc_lam_ext; auto.
 red; intros.
 apply app_morph; trivial.
Qed.

Lemma cc_prod_intro : forall dom f F,
  ext_fun dom f ->
  ext_fun dom F ->
  (forall x, x \in dom -> f x \in F x) ->
  cc_lam dom f \in cc_prod dom F.
unfold cc_prod in |- *.
intros.
assert (forall x, x \in dom -> f x \in union (dep_image dom F)).
 intros.
 apply union_intro with (F x); auto.
 unfold dep_image.
 apply replf_intro with x; auto.
 reflexivity.
apply replf_intro with (lam dom f); trivial.
 apply dep_func_intro; trivial.

 apply cc_lam_ext; intros.
  reflexivity.

  red; intros.
  rewrite beta_eq; auto.
  rewrite <- H4; trivial.
Qed.

Lemma cc_prod_elim : forall dom f x F,
  f \in cc_prod dom F ->
  x \in dom ->
  cc_app f x \in F x.
intros.
unfold cc_prod in H.
elim replf_elim with (2 := H); clear H; intros; auto.
rewrite H1; clear H1.
rewrite cc_beta_eq; auto.
 apply dep_func_elim with dom; trivial.

 do 2 red; intros.
 rewrite H2; reflexivity.
Qed.

(* Eta: *)
Lemma cc_eta_eq: forall dom F f,
  f \in cc_prod dom F ->
  f == cc_lam dom (fun x => cc_app f x).
unfold cc_prod.
intros.
rewrite replf_ax in H.
 destruct H.
 rewrite H0.
 apply cc_lam_ext; auto with *.
 red; intros.
 rewrite H0.
 rewrite cc_beta_eq.
  apply app_morph; auto with *.

  red; red; intros.
  apply app_morph; auto with *.

  rewrite <- H2; auto.

 red; red; intros.
 apply cc_lam_ext; auto with *.
 red; intros.
 apply app_morph; auto.
Qed.

Lemma cc_prod_covariant : forall dom dom' F G,
  ext_fun dom' G ->
  dom == dom' ->
  (forall x, x \in dom -> F x \incl G x) ->
  cc_prod dom F \incl cc_prod dom' G.
red; intros.
setoid_replace (cc_prod dom' G) with (cc_prod dom G).
 specialize cc_eta_eq with (1:=H2); intro.
 rewrite H3.
 apply cc_prod_intro; trivial.
  red; red; intros.
  rewrite H5; auto with *.

  red; red; intros.
  rewrite H0 in H4; apply H; trivial.

  intros.
  apply H1; trivial.
  apply cc_prod_elim with (1:=H2); trivial.

 apply cc_prod_ext; trivial.
 symmetry; trivial.
Qed.


(* impredicativity *)

Definition prf_trm := empty.
Definition props := power (singl prf_trm).

Lemma cc_impredicative_prod : forall dom F,
  (forall x, x \in dom -> F x \in props) ->
  cc_prod dom F \in props.
Proof.
unfold props in |- *; intros.
apply power_intro; intros.
apply singl_intro_eq.
unfold prf_trm in |- *.
unfold cc_prod in H0.
elim replf_elim with (2 := H0); clear H0; intros; auto.
rewrite H1; clear H1 z.
apply cc_impredicative_lam.
 do 2 red; intros; apply app_morph; trivial; reflexivity.
intros.
specialize dep_func_elim with (1 := H0) (2 := H1); intro.
specialize H with (1 := H1).
specialize power_elim with (1 := H) (2 := H2); intro.
apply singl_elim; trivial.
Qed.
