
Require Import ZFpairs ZFstable.

(** * Relations *)

Definition is_relation x :=
  forall p, p ∈ x -> p == couple (fst p) (snd p).

Definition rel_domain r :=
  subset (union (union r)) (fun x => exists y, couple x y ∈ r).

Definition rel_image r :=
  subset (union (union r)) (fun y => exists x, couple x y ∈ r).

Instance rel_image_morph : morph1 rel_image.
do 2 red; intros.
unfold rel_image in |- *.
apply subset_morph.
 rewrite H; reflexivity.

 split; intros.
  destruct H1.
  exists x1.
  rewrite <- H; trivial.

  destruct H1.
  exists x1.
  rewrite H; trivial.
Qed.

Lemma rel_image_ex r x : x ∈ rel_domain r -> exists y, couple x y ∈ r.
Proof.
unfold rel_domain; intros.
elim subset_elim2 with (1:=H); intros.
destruct H1.
rewrite <- H0 in H1.
exists x1; trivial.
Qed.

Lemma rel_domain_intro : forall r x y, couple x y ∈ r -> x ∈ rel_domain r.
Proof.
unfold rel_domain in |- *; intros.
apply subset_intro.
 red in H.
 destruct union_elim with x (couple x y) as (z,?,?).
  rewrite union_couple_eq.
  apply pair_intro1.

  apply union_intro with z; auto.
  apply union_intro with (couple x y); trivial.

 exists y; trivial.
Qed.

Lemma rel_image_intro : forall r x y, couple x y ∈ r -> y ∈ rel_image r.
Proof.
unfold rel_image in |- *; intros.
apply subset_intro.
 red in H.
 destruct union_elim with y (couple x y) as (z,?,?).
  rewrite union_couple_eq; auto.

  apply union_intro with z; auto.
  apply union_intro with (couple x y); trivial.

 exists x; trivial.
Qed.


Definition rel_comp f g := 
  subset (prodcart (rel_domain g) (rel_image f))
    (fun p => exists2 y, couple (fst p) y ∈ g & couple y (snd p) ∈ f).

Lemma rel_comp_intro : forall f g x y z,
  couple x y ∈ g -> couple y z ∈ f -> couple x z ∈ rel_comp f g.
Proof.
intros.
red in |- *.
unfold rel_comp in |- *.
apply subset_intro.
 apply couple_intro.
  apply rel_domain_intro with (1 := H).
  apply rel_image_intro with (1 := H0).
 exists y.
   rewrite fst_def.
    trivial.
   rewrite snd_def; trivial.
Qed.

(** Relation typing *)

Definition rel A B := power (prodcart A B).

Lemma rel_mono :
  Proper (incl_set ==> incl_set ==> incl_set) rel.
unfold rel; do 3 red; intros.
apply power_mono.
apply prodcart_mono; trivial.
Qed.

Instance rel_morph : morph2 rel.
Proof.
do 3 red; intros.
unfold rel.
rewrite H; rewrite H0; reflexivity.
Qed.

Lemma app_typ1 : forall r x y A B, r ∈ rel A B -> couple x y ∈ r -> x ∈ A.
Proof.
unfold rel in |- *; intros.
specialize power_elim with (1 := H) (2 := H0); intro.
rewrite <- (fst_def x y).
apply fst_typ with (1 := H1).
Qed.

Lemma app_typ2 : forall r x y A B, r ∈ rel A B -> couple x y ∈ r -> y ∈ B.
Proof.
unfold rel in |- *; intros.
specialize power_elim with (1 := H) (2 := H0); intro.
rewrite <- (snd_def x y).
apply snd_typ with (1 := H1).
Qed.

Lemma rel_is_relation : forall f A B, f ∈ rel A B -> is_relation f.
Proof.
unfold rel in |- *; red in |- *; intros.
specialize power_elim with (1 := H) (2 := H0); apply surj_pair.
Qed.

Lemma rel_domain_incl : forall r A B, r ∈ rel A B -> rel_domain r ⊆ A.
Proof.
unfold rel_domain in |- *; intros.
red in |- *; intros.
elim subset_elim2 with (1 := H0); intros.
destruct H2 as (y, img_z).
rewrite <- H1 in img_z.
apply app_typ1 with (1 := H) (2 := img_z).
Qed.

Lemma rel_image_incl : forall r A B, r ∈ rel A B -> rel_image r ⊆ B.
Proof.
unfold rel_image in |- *; intros.
red in |- *; intros.
elim subset_elim2 with (1 := H0); intros.
destruct H2 as (x0, img_z).
rewrite <- H1 in img_z.
apply app_typ2 with (1 := H) (2 := img_z).
Qed.

Lemma relation_is_rel :
  forall r A B,
  is_relation r ->
  rel_domain r ⊆ A ->
  rel_image r ⊆ B ->
  r ∈ rel A B.
Proof.
unfold rel in |- *; intros.
red in H.
apply power_intro; intros.
 rewrite (H _ H2).
apply couple_intro.
 apply H0.
   apply rel_domain_intro with (snd z).
   red in |- *.
    rewrite <- (H _ H2); trivial.
 apply H1.
   apply rel_image_intro with (fst z).
   red in |- *.
    rewrite <- (H _ H2); trivial.
Qed.


(* introduces relation R of domain A and codomain B *)
Definition inject_rel R A B :=
  subset (prodcart A B) (fun p => R (fst p) (snd p)).

Lemma inject_rel_is_rel :  forall (R:set->set->Prop) A B,
  inject_rel R A B ∈ rel A B.
Proof.
unfold rel in |- *.
intros.
apply power_intro; intros.
unfold inject_rel in H.
apply subset_elim1 with (1 := H).
Qed.

Lemma inject_rel_intro :
  forall (R:set->set->Prop) A B x y,
  ext_rel A R ->
  x ∈ A ->
  y ∈ B ->
  R x y ->
  couple x y ∈ inject_rel R A B.
Proof.
unfold inject_rel in |- *; intros.
apply subset_intro.
 apply couple_intro; trivial.
 elim (H x (fst (couple x y)) y (snd (couple x y))); intros; auto.
   rewrite fst_def; reflexivity.
   rewrite snd_def; reflexivity.
Qed.

Lemma inject_rel_elim :
  forall (R:set->set->Prop) A B x y,
  ext_rel A R ->
  couple x y ∈ inject_rel R A B ->
  x ∈ A /\ y ∈ B /\ R x y.
Proof.
unfold inject_rel in |- *; intros.
specialize subset_elim1 with (1 := H0); intro.
elim subset_elim2 with (1 := H0); intros.
assert (x ∈ A).
 rewrite <- (fst_def x y).
 apply fst_typ with B; trivial.
split; trivial.
split.
 rewrite <- (snd_def x y).
 apply snd_typ with A; trivial.

elim (H x (fst x0) y (snd x0)); intros; auto.
 rewrite <- H2; symmetry  in |- *; apply fst_def.
 rewrite <- H2; symmetry  in |- *; apply snd_def.
Qed.

(** * Functions *)

Definition is_function f :=
  is_relation f /\
  forall x y y', couple x y ∈ f -> couple x y' ∈ f -> y == y'.

Definition app f x :=
  union (subset (rel_image f) (fun y => couple x y ∈ f)).


Instance app_morph : morph2 app.
Proof.
do 3 red; intros.
unfold app.
apply union_morph.
apply subset_morph.
 apply rel_image_morph; trivial.

 split; intros.
  rewrite <- H.
  rewrite <- H0; trivial.

  rewrite H.
  rewrite H0; trivial.
Qed.


Lemma app_defined : forall f x y,
  is_function f -> couple x y ∈ f -> app f x == y.
Proof.
unfold app, is_function in |- *; intros.
destruct H.
transitivity (union (singl y)).
 apply union_morph.
   apply singl_ext; intros.
  apply subset_intro; trivial.
    apply rel_image_intro with (1 := H0).
  elim subset_elim2 with (1 := H2); intros.
  rewrite <- H3 in H4; eauto.
 apply union_singl_eq.
Qed.

Lemma app_elim : forall f x,
  is_function f -> x ∈ rel_domain f -> couple x (app f x) ∈ f.
Proof.
intros.
elim rel_image_ex with (1 := H0); intros.
 rewrite (app_defined f x x0); trivial.
Qed.

(** Typing *)

Definition func A B :=
  subset (rel A B)
    (fun r =>
       (forall x, x ∈ A -> exists2 y, y ∈ B & couple x y ∈ r) /\
       (forall x y y', couple x y ∈ r -> couple x y' ∈ r -> y == y')).

Instance func_mono :
  Proper (eq_set ==> incl_set ==> incl_set) func.
unfold func; intros A A' eqA B B' inclB z infunc.
specialize subset_elim1 with (1:=infunc); intro.
apply subset_elim2 in infunc.
destruct infunc.
apply subset_intro.
 revert H; apply rel_mono; auto.
 rewrite eqA; reflexivity.

 destruct H1.
 split; intros.
  rewrite <- eqA in H3.
  elim H1 with (1:=H3); intros.
  apply inclB in H4.
  rewrite <- H0 in H5.
  exists x1; auto.

 rewrite H0 in H3,H4|-; eauto.
Qed.

Instance func_morph : morph2 func.
Proof.
do 3 red; intros.
unfold func.
apply subset_morph.
 apply rel_morph; trivial.

 split; intros.
  destruct H2.
  split; intros; eauto.
  rewrite <- H in H4.
  elim H2 with (1:=H4); intros.
  exists x3; trivial.
  rewrite <- H0; trivial.

  destruct H2.
  split; intros; eauto.
  rewrite H in H4.
  elim H2 with (1:=H4); intros.
  exists x3; trivial.
  rewrite H0; trivial.
Qed.

Lemma func_rel_incl : forall A B, func A B ⊆ rel A B.
Proof.
unfold func; red; intros; eapply subset_elim1; eauto.
Qed.

Lemma func_is_function : forall f A B, f ∈ func A B -> is_function f.
Proof.
red in |- *; intros.
split.
 apply rel_is_relation with A B.
   apply func_rel_incl; trivial.
 intros.
   unfold func in H.
   elim subset_elim2 with (1 := H); intros.
   destruct H3.
   apply H4 with x; rewrite <- H2; auto.
Qed.

Lemma fun_domain_func : forall f A B, f ∈ func A B -> rel_domain f == A.
Proof.
intros; apply eq_intro; intros.
 apply rel_domain_incl with f B; trivial.
 unfold func in H.
 apply subset_elim1 with (1 := H).

 unfold rel_domain in |- *.
 unfold func in H.
 elim subset_elim2 with (1 := H); intros.
 destruct H2.
 apply subset_intro.
  specialize subset_elim1 with (1 := H); unfold rel in |- *; intro.
  destruct H2 with (1:=H0) as (y,tyy,rxy).
  destruct union_elim with z (couple z y).
   rewrite union_couple_eq; trivial.

   apply union_intro with x0; trivial.
   apply union_intro with (couple z y); trivial.
   rewrite H1; trivial.

 elim H2 with (1 := H0); intros.
 rewrite <- H1 in H5.
 exists x0; trivial.
Qed.

Lemma app_typ :
  forall f x A B, f ∈ func A B -> x ∈ A -> app f x ∈ B.
Proof.
unfold func in |- *; intros.
specialize subset_elim2 with (1 := H); destruct 1; auto.
apply app_typ2 with f x A.
 apply func_rel_incl; trivial.
 apply app_elim.
  apply func_is_function with A B; trivial.
   rewrite (fun_domain_func _ _ _ H).
    trivial.
Qed.


Lemma func_narrow : forall f A B B',
  f ∈ func A B ->
  (forall x, x ∈ A -> app f x ∈ B') ->
  f ∈ func A B'.
unfold func; intros.
specialize subset_elim1 with (1:=H); intro.
elim subset_elim2 with (1:=H); intros.
destruct H3.
apply subset_intro.
 apply relation_is_rel; intros.
  apply rel_is_relation with A B; trivial.

  apply rel_domain_incl with B; trivial.

  red; intros.
  unfold rel_image in H5.
  elim subset_elim2 with (1:=H5); clear H5; intros.
  destruct H6.
  rewrite H5.
  rewrite H2 in H6.
  rewrite (H4 x1 x0 (app x x1)); trivial.
   rewrite <- H2; apply H0.
   apply app_typ1 with f x0 B; trivial.
   rewrite H2; trivial.

   rewrite (app_defined x x1 x0); trivial.
   apply func_is_function with A B; trivial; rewrite <- H2; trivial.

 split; intros.
  elim H3 with x0; trivial; intros.
  rewrite <- H2 in H7.
  exists x1; trivial.
  rewrite <- (app_defined f x0 x1); auto.
  apply func_is_function with A B; trivial.

  rewrite H2 in H5,H6|-; eauto.
Qed.

Definition lam_rel (F:set->set) A B := inject_rel (fun x y => F x == y) A B.

Lemma lam_rel_is_func : forall A B f, 
  ext_fun A f ->
  (forall x, x ∈ A -> f x ∈ B) ->
  lam_rel f A B ∈ func A B.
Proof.
unfold lam_rel in |- *; intros.
unfold func in |- *.
apply subset_intro.
 apply inject_rel_is_rel.

 split; intros.
  exists (f x); auto.
  apply inject_rel_intro; auto.
   red in |- *; intros.
      rewrite H4.
      rewrite (H _ _ H2 H3).
     split; auto.
   reflexivity.
  elim inject_rel_elim with (2 := H1).
   destruct 2.
     elim inject_rel_elim with (2 := H2).
    destruct 2.
       rewrite <- H5.
       rewrite <- H8.
      reflexivity.
   red in |- *; intros.
      rewrite H8.
      rewrite (H _ _ H6 H7).
     split; auto.
   red in |- *; intros.
      rewrite H5.
      rewrite (H _ _ H3 H4).
     split; auto.
Qed.

Lemma beta_rel_eq : forall f x A B,
  ext_fun A f ->
  x ∈ A -> (forall x, x ∈ A -> f x ∈ B) -> app (lam_rel f A B) x == f x.
Proof.
intros.
apply app_defined.
 apply func_is_function with A B.
   apply lam_rel_is_func; auto.
 unfold lam_rel in |- *.
   apply inject_rel_intro; auto.
  red in |- *; intros.
     rewrite H4.
     rewrite (H _ _ H2 H3); split; auto.
  reflexivity.
Qed.

Definition lam A F := replf A (fun x => couple x (F x)).

Lemma fun_elt_is_ext : forall A f,
  ext_fun A f ->
  ext_fun A (fun x => couple x (f x)).
do 2 red; intros.
apply couple_morph; auto.
Qed.
Hint Resolve fun_elt_is_ext.


Lemma lam_is_function : forall A f, ext_fun A f -> is_function (lam A f).
red; intros.
split; intros.
 red; intros.
 apply replf_elim in H0; auto.
 destruct H0.
 rewrite H1.
 rewrite fst_def; rewrite snd_def; reflexivity. 

 red in H0,H1|-.
 apply replf_elim in H0; auto.
 apply replf_elim in H1; auto.
 destruct H0; destruct H1.
 apply couple_injection in H2; destruct H2.
 apply couple_injection in H3; destruct H3.
 rewrite H2 in H3.
 rewrite H5; rewrite H4; auto.
Qed.

Lemma lam_is_func : forall A B f, 
  ext_fun A f ->
  (forall x, x ∈ A -> f x ∈ B) ->
  lam A f ∈ func A B.
Proof.
unfold lam in |- *; intros.
unfold func in |- *.
apply subset_intro.
 apply relation_is_rel.
  destruct (lam_is_function _ _  H); trivial.

  unfold rel_domain; red; intros.
  apply subset_elim2 in H1; destruct H1.
  destruct H2.
  red in H2.
  apply replf_elim in H2; auto.
  destruct H2.
  apply couple_injection in H3; destruct H3.
  rewrite H1; rewrite H3; trivial.

  unfold rel_image; red; intros.
  apply subset_elim2 in H1; destruct H1.
  destruct H2.
  red in H2.
  apply replf_elim in H2; auto.
  destruct H2.
  apply couple_injection in H3; destruct H3.
  rewrite H1; rewrite H4; auto.


 split; intros.
  exists (f x); auto.
  red.
  apply replf_intro with x; auto.
  reflexivity.

  destruct lam_is_function with (1:=H).
  eauto.
Qed.

Lemma beta_eq : forall f x A,
  ext_fun A f -> x ∈ A -> app (lam A f) x == f x.
Proof.
unfold lam.
intros.
apply app_defined.
 split; intros.
  red; intros.
  apply replf_elim in H1; auto.
  destruct H1.
  rewrite H2.
  rewrite fst_def; rewrite snd_def; reflexivity. 

  destruct lam_is_function with (1:=H); eauto.

 red.
 apply replf_intro with x; auto.
 reflexivity.
Qed.


Lemma func_is_ext : forall x X F,
  ext_fun x F ->
  ext_fun x (fun x => func X (F x)).
do 2 red; intros.
apply func_morph; auto.
reflexivity.
Qed.
Hint Resolve func_is_ext.

Lemma func_stable_class A K :
  stable_class K (func A).
red; red; intros.
destruct inter_wit with (2:=H0); eauto with *.
assert (forall x, x ∈ X -> z ∈ func A x).
 intros.
 apply inter_elim with (1:=H0).
 rewrite replf_ax.
  exists x0; auto with *.

  red; red; intros.
  rewrite H4; reflexivity.
clear H0.
assert (z ∈ func A x) by auto.
apply func_narrow with x; trivial.
intros.
apply inter_intro; eauto.
intros.
apply app_typ with A; auto.
Qed.

(** Dependent typing *)

Definition dep_image (A:set) (B:set->set) := replf A B.

Lemma dep_image_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  dep_image x1 f1 == dep_image x2 f2.
Proof.
intros.
unfold dep_image.
apply replf_morph; trivial.
Qed.

Definition dep_func (A:set) (B:set->set) :=
  subset (func A (union (dep_image A B)))
    (fun f => forall x, x ∈ A -> app f x ∈ B x).

Lemma dep_func_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  dep_func x1 f1 == dep_func x2 f2.
Proof.
intros.
unfold dep_func.
apply subset_morph; trivial.
 apply func_morph; trivial.
 apply union_morph.
 apply dep_image_ext; trivial.

 split; intros.
  rewrite <- H in H3.
  rewrite <- (H0 x0 x0); auto; reflexivity.

  rewrite (H0 x0 x0); trivial; try reflexivity.
  rewrite H in H3; auto.
Qed.

Lemma dep_func_mono : forall A A' F F',
  ext_fun A F ->
  ext_fun A' F' ->
  A == A' ->  
  (forall x, x ∈ A -> F x ⊆ F' x) ->
  dep_func A F ⊆ dep_func A' F'.
unfold dep_func; red; intros A A' F F' eF eF' eqA H z H0.
rewrite subset_ax in H0|-*.
destruct H0; split.
 clear H1; revert z H0; apply func_mono; auto with *.
 red; intros.
 unfold dep_image in H0|-*.
 rewrite union_ax in H0|-*.
 destruct H0.
 rewrite replf_ax in H1; trivial.
 destruct H1.
 exists (F' x0).
  rewrite H2 in H0. 
  apply H; auto.

  rewrite eqA in H1. 
  rewrite replf_ax; auto.
  exists x0; auto with *.

 destruct H1.
 exists x; trivial.
 intros.
 rewrite <- eqA in H3.
 apply H; auto.
Qed.

Lemma dep_func_intro : forall f dom F,
  ext_fun dom f ->
  ext_fun dom F ->
  (forall x, x ∈ dom -> f x ∈ F x) ->
  lam dom f ∈ dep_func dom F.
Proof.
intros.
assert (forall x, x ∈ dom -> f x ∈ union (dep_image dom F)).
 intros.
 apply union_intro with (F x); auto.
 unfold dep_image.
 apply replf_intro with x; trivial.
 reflexivity.
unfold dep_func.
apply subset_intro.
 apply lam_is_func; trivial.

 intros.
 rewrite beta_eq; auto.
Qed.

Lemma func_eta : forall f A B,
  f ∈ func A B ->
  f == lam A (fun x => app f x).
intros.
specialize subset_elim2 with (1:=H); intro.
destruct H0.
destruct H1.
clear H2.
apply eq_intro; intros.
 specialize subset_elim1 with (1:=H); intros is_rel.
 apply power_elim with (2:= H2) in is_rel.
 specialize fst_typ with (1:=is_rel); intros.
 destruct H1 with (1:= H3); clear H1.
 apply surj_pair in is_rel.
 apply func_is_function in H.
 red in H5; rewrite <- H0 in H5; clear x H0.
 specialize app_defined with (1:=H) (2:=H5); intros.
 destruct H.
 rewrite is_rel in H2.
 specialize H1 with (1:=H2) (2:=H5).
 rewrite <- H1 in H0.
 unfold lam.
 apply replf_intro with (fst z); auto.
  do 2 red; intros.
  rewrite H7; reflexivity.
 rewrite H0; trivial.

 apply replf_elim in H2.
  destruct H2.
  rewrite H3.
  apply app_elim.
   apply func_is_function in H; trivial.
  apply H1 in H2.
  destruct H2.
  red in H4; rewrite <- H0 in H4.
  apply rel_domain_intro with x1; trivial.

  do 2 red; intros.
  rewrite H4; reflexivity.
Qed.

Lemma dep_func_eta : forall f dom F,
  f ∈ dep_func dom F ->
  f == lam dom (fun x => app f x).
intros.
apply subset_elim1 in H.
apply func_eta with (1:=H).
Qed.

Lemma dep_func_incl_func : forall A B,
  dep_func A B ⊆ func A (union (dep_image A B)).
Proof.
unfold dep_func in |- *; red in |- *; intros.
apply subset_elim1 with (1 := H).
Qed.

Lemma dep_func_elim :
  forall f x A B, f ∈ dep_func A B -> x ∈ A -> app f x ∈ B x.
Proof.
unfold dep_func in |- *; intros.
elim subset_elim2 with (1 := H); intros.
rewrite H1.
auto.
Qed.

(** * Aczel's encoding of functions *)

(** Characterizing functions *)

Definition is_cc_fun A f :=
  forall c, c ∈ f -> c == couple (fst c) (snd c) /\ fst c ∈ A.

Instance is_cc_fun_morph : Proper (eq_set ==> eq_set ==> iff) is_cc_fun.
apply morph_impl_iff2; auto with *.
do 5 red; intros.
rewrite <- H; rewrite <- H0 in H2; auto.
Qed.

(** Function constructor *)

Definition cc_lam (x:set) (y:set->set) : set :=
  sup x (fun x' => replf (y x') (fun y' => couple x' y')).

Notation "'λ'  x ∈ A , B" :=
  (cc_lam A (fun x => B)) (x ident, at level 200, right associativity).

Instance cc_lam_morph : Proper (eq_set ==> (eq_set ==> eq_set) ==> eq_set) cc_lam.
unfold cc_lam; do 3 red; intros.
apply sup_morph; trivial.
red; intros.
apply replf_morph.
 apply H0; trivial.

 red; intros; apply couple_morph; trivial.
Qed.

Lemma cc_lam_def dom f z :
  ext_fun dom f ->
  (z ∈ cc_lam dom f <->
   exists2 x, x ∈ dom & exists2 y, y ∈ f x & z == couple x y).
unfold cc_lam; intros.
rewrite sup_ax.
 apply ex2_morph; red; intros; auto with *.
 rewrite replf_ax; auto with *.
 do 2 red; intros; apply couple_morph; auto with *.

 do 2 red; intros; apply replf_morph; auto.
 red; intros; apply couple_morph; auto with *.
Qed.
Opaque cc_lam.

Lemma is_cc_fun_lam A F :
  ext_fun A F ->
  is_cc_fun A (cc_lam A F).
red; intros.
rewrite cc_lam_def in H0; trivial; destruct H0 as (x,?,(y,_,?)).
rewrite H1; rewrite fst_def; rewrite snd_def; auto with *.
Qed.

Lemma cc_lam_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  cc_lam x1 f1 == cc_lam x2 f2.
intros.
assert (ext_fun x1 f1).
 apply eq_fun_ext in H0; trivial.
assert (ext_fun x2 f2).
 do 2 red; intros.
 rewrite <-H in H2.
 rewrite <- (H0 x x'); trivial.
 symmetry; apply H0; trivial; try reflexivity.
rewrite eq_set_ax; intros z.
do 2 (rewrite cc_lam_def; trivial).
split; (destruct 1 as (x,?,h); destruct h as (y,?,?); exists x;[|exists y]); trivial.
 rewrite <- H; trivial.
 revert H4; apply eq_elim; apply H0; auto with *.
 rewrite H; auto.
 revert H4; apply eq_elim; symmetry; apply H0; auto with *.
 rewrite H; trivial.
Qed.

Lemma cc_impredicative_lam : forall dom F,
  ext_fun dom F ->
  (forall x, x ∈ dom -> F x == empty) ->
  cc_lam dom F == empty.
Proof.
intros.
apply empty_ext; red in |- *; intros.
rewrite cc_lam_def in H1; trivial; destruct H1 as (z,?,(y,?,?)).
rewrite H0 in H2; trivial.
apply empty_ax with y; trivial.
Qed.

(** Application *)

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

Lemma couple_in_app : forall x z f,
  couple x z ∈ f <-> z ∈ cc_app f x.
unfold cc_app, rel_image; split; intros.
 apply subset_intro.
 destruct union_elim with z (couple x z) as (y,?,?).
  rewrite union_couple_eq; trivial.

  apply union_intro with y; trivial.
  apply union_intro with (couple x z); trivial.
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

Lemma cc_app_empty : forall x, cc_app empty x == empty.
intro.
apply empty_ext; red; intros.
rewrite <- couple_in_app in H.
apply empty_ax in H; trivial.
Qed.
Opaque cc_app.

Lemma cc_app_outside_domain dom f x :
  is_cc_fun dom f ->
  ~ x ∈ dom ->
  cc_app f x == empty.
intros.
apply empty_ext; red; intros.
apply couple_in_app in H1.
apply H in H1.
destruct H1 as (_,?).
rewrite fst_def in H1; auto.
Qed.


(** Beta reduction *)

Lemma cc_beta_eq : forall dom F x,
  ext_fun dom F ->
  x ∈ dom ->
  cc_app (cc_lam dom F) x == F x.
Proof.
intros.
apply eq_intro; intros.
 rewrite <- couple_in_app in H1.
 rewrite cc_lam_def in H1; trivial.
 destruct H1 as (x',?,(y,?,?)).
 apply couple_injection in H3; destruct H3.
 rewrite H4; revert H2; apply eq_elim; apply H; auto with *.

 rewrite <- couple_in_app.
 rewrite cc_lam_def; eauto with *.
Qed.

(** Eta reduction *)

Lemma cc_eta_eq' : forall dom f,
  is_cc_fun dom f ->
  f == λ x ∈ dom, cc_app f x.
unfold is_cc_fun.
intros.
assert (am : ext_fun dom (fun x => cc_app f x)).
 do 2 red; intros; apply cc_app_morph; auto with *.
apply eq_intro; intros.
 specialize H with (1:=H0); destruct H.
 rewrite cc_lam_def; trivial.
 exists (fst z); trivial.
 exists (snd z); trivial.
 rewrite <- couple_in_app; rewrite <- H; trivial.

 rewrite cc_lam_def in H0; trivial.
 destruct H0 as (x,?,(y,?,?)).
 rewrite H2; apply couple_in_app; trivial.
Qed.

(** Typing: dependent products *)

Definition cc_prod (x:set) (y:set->set) : set :=
  replf (dep_func x y)
    (fun f => cc_lam x (fun x' => app f x')).

Notation "'Π'  x ∈ A , B" :=
  (cc_prod A (fun x => B)) (x ident, at level 200, right associativity).

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

Instance cc_prod_morph : Proper (eq_set ==> (eq_set ==> eq_set) ==> eq_set) cc_prod.
do 3 red; intros; apply cc_prod_ext; trivial.
red; intros; apply H0; trivial.
Qed.

Lemma cc_prod_fun1 : forall A x,
  ext_fun A (fun f => cc_lam x (fun x' => app f x')).
Proof.
do 2 red; intros.
apply cc_lam_ext; try reflexivity; red; intros.
apply app_morph; trivial.
Qed.
Hint Resolve cc_prod_fun1.

Lemma cc_prod_is_cc_fun : forall A B f,
  f ∈ cc_prod A B -> is_cc_fun A f.
intros.
unfold cc_prod in H.
rewrite replf_ax in H; auto.
destruct H.
rewrite H0.
apply is_cc_fun_lam; auto.
do 2 red; intros; apply app_morph; auto with *.
Qed.
Hint Resolve cc_prod_is_cc_fun.


Definition cc_arr A B := cc_prod A (fun _ => B).

Instance cc_arr_morph : morph2 cc_arr.
do 3 red; intros.
apply cc_prod_morph; trivial.
red; trivial.
Qed.


Lemma cc_prod_intro : forall dom f F,
  ext_fun dom f ->
  ext_fun dom F ->
  (forall x, x ∈ dom -> f x ∈ F x) ->
  cc_lam dom f ∈ cc_prod dom F.
unfold cc_prod in |- *.
intros.
assert (forall x, x ∈ dom -> f x ∈ union (dep_image dom F)).
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
  f ∈ cc_prod dom F ->
  x ∈ dom ->
  cc_app f x ∈ F x.
intros.
unfold cc_prod in H.
elim replf_elim with (2 := H); clear H; intros; auto.
rewrite H1; clear H1.
rewrite cc_beta_eq; auto.
 apply dep_func_elim with dom; trivial.

 do 2 red; intros.
 rewrite H2; reflexivity.
Qed.

Lemma cc_app_typ f v A B B' :
  f ∈ cc_prod A B ->
  B' == B v ->
  v ∈ A ->
  cc_app f v ∈ B'.
intros.
rewrite H0; apply cc_prod_elim with (1:=H); trivial.
Qed.

Lemma cc_arr_intro : forall A B F,
  ext_fun A F ->
  (forall x, x ∈ A -> F x ∈ B) ->
  cc_lam A F ∈ cc_arr A B.
unfold cc_arr; intros.
apply cc_prod_intro; auto.
Qed.

Lemma cc_arr_elim : forall f x A B,
  f ∈ cc_arr A B -> 
  x ∈ A ->
  cc_app f x ∈ B.
intros.
apply cc_prod_elim with (1:=H); trivial.
Qed.


(* Eta reduction : *)
Lemma cc_eta_eq: forall dom F f,
  f ∈ cc_prod dom F ->
  f == λ x ∈ dom, cc_app f x.
intros.
apply cc_eta_eq'; eauto.
Qed.

Lemma cc_prod_covariant : forall dom dom' F G,
  ext_fun dom' G ->
  dom == dom' ->
  (forall x, x ∈ dom -> F x ⊆ G x) ->
  cc_prod dom F ⊆ cc_prod dom' G.
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

Lemma cc_prod_intro' : forall (dom dom': set) (f F : set -> set),
       ext_fun dom f ->
       ext_fun dom' F ->
       dom == dom' ->
       (forall x : set, x ∈ dom -> f x ∈ F x) ->
       cc_lam dom f ∈ cc_prod dom' F.
intros.
cut (cc_lam dom f ∈ cc_prod dom F).
 apply cc_prod_covariant; auto with *.
apply cc_prod_intro; intros; auto.
do 2 red; intros.
apply H0; trivial.
rewrite <- H1; trivial.
Qed.

Lemma cc_prod_stable_class : forall K dom F,
  (forall y y' x x', y == y' -> x ∈ dom -> x == x' -> F y x == F y' x') ->
  (forall x, x ∈ dom -> stable_class K (fun y => F y x)) ->
  stable_class K (fun y => cc_prod dom (F y)).
intros K dom F Fm Fs.
assert (Hm : morph1 (fun y => cc_prod dom (F y))).
 do 2 red; intros.
 apply cc_prod_ext; auto with *.
 red; intros; apply Fm; auto.
red; red ;intros.
destruct inter_wit with (2:=H0) as (w,winX); trivial.
assert (forall x, x ∈ X -> z ∈ cc_prod dom (F x)).
 intros.
 apply inter_elim with (1:=H0).
 rewrite replf_ax; auto.
 exists x; auto with *.
clear H0.
assert (z ∈ cc_prod dom (F w)) by auto.
rewrite (cc_eta_eq _ _ _ H0).
apply cc_prod_intro.
 red; red; intros; apply cc_app_morph; auto with *.

 red; red; intros; apply Fm; auto with *.

 intros.
 apply Fs; trivial.
 apply inter_intro.
  intros.
  rewrite replf_ax in H3; auto.
  2:red;red;intros;apply Fm; auto with *.
  destruct H3.
  rewrite H4; apply H1 in H3.
  apply cc_prod_elim with (1:=H3); trivial.

  exists (F w x); rewrite replf_ax.
  2:red;red;intros; apply Fm; auto with *.
  eauto with *.
Qed.

Global Opaque func dep_func cc_prod app lam cc_app cc_lam.
