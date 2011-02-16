
Require Import ZFpairs.
Import IZF.

(* relations *)

Definition is_relation x :=
  forall p, p \in x -> p == couple (fst p) (snd p).

Definition rel_app r x y := couple x y \in r.

Instance rel_app_morph :
  Proper (eq_set ==> eq_set ==> eq_set ==> iff) rel_app.
unfold rel_app; do 4 red; intros.
rewrite H; rewrite H0; rewrite H1; reflexivity.
Qed.

Definition rel_domain r :=
  subset (union (union r)) (fun x => exists y, rel_app r x y).

Definition rel_image r :=
  subset (union (union r)) (fun y => exists x, rel_app r x y).

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

Lemma rel_image_ex : forall r x, x \in rel_domain r -> exists y, rel_app r x y.
Proof.
unfold rel_domain; intros.
elim subset_elim2 with (1:=H); intros.
destruct H1.
rewrite <- H0 in H1.
exists x1; trivial.
Qed.

Lemma rel_domain_intro : forall r x y, rel_app r x y -> x \in rel_domain r.
Proof.
unfold rel_domain in |- *; intros.
apply subset_intro.
 red in H.
   apply union_intro with (pair x y); auto.
   apply union_intro with (couple x y); trivial.
   unfold couple in |- *; auto.
 exists y; trivial.
Qed.

Lemma rel_image_intro : forall r x y, rel_app r x y -> y \in rel_image r.
Proof.
unfold rel_image in |- *; intros.
apply subset_intro.
 red in H.
   apply union_intro with (pair x y); auto.
   apply union_intro with (couple x y); trivial.
   unfold couple in |- *; auto.
 exists x; trivial.
Qed.


Definition rel_comp f g := 
  subset (prodcart (rel_domain g) (rel_image f))
    (fun p => exists2 y, rel_app g (fst p) y & rel_app f y (snd p)).

Lemma rel_comp_intro : forall f g x y z,
  rel_app g x y -> rel_app f y z -> rel_app (rel_comp f g) x z.
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

(* - relation typing *)

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

Lemma app_typ1 : forall r x y A B, r \in rel A B -> rel_app r x y -> x \in A.
Proof.
unfold rel, rel_app in |- *; intros.
specialize power_elim with (1 := H) (2 := H0); intro.
rewrite <- (fst_def x y).
apply fst_typ with (1 := H1).
Qed.

Lemma app_typ2 : forall r x y A B, r \in rel A B -> rel_app r x y -> y \in B.
Proof.
unfold rel, rel_app in |- *; intros.
specialize power_elim with (1 := H) (2 := H0); intro.
rewrite <- (snd_def x y).
apply snd_typ with (1 := H1).
Qed.

Lemma rel_is_relation : forall f A B, f \in rel A B -> is_relation f.
Proof.
unfold rel in |- *; red in |- *; intros.
specialize power_elim with (1 := H) (2 := H0); apply surj_pair.
Qed.

Lemma rel_domain_incl : forall r A B, r \in rel A B -> rel_domain r \incl A.
Proof.
unfold rel_domain in |- *; intros.
red in |- *; intros.
elim subset_elim2 with (1 := H0); intros.
destruct H2 as (y, img_z).
rewrite <- H1 in img_z.
apply app_typ1 with (1 := H) (2 := img_z).
Qed.

Lemma rel_image_incl : forall r A B, r \in rel A B -> rel_image r \incl B.
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
  rel_domain r \incl A ->
  rel_image r \incl B ->
  r \in rel A B.
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
  inject_rel R A B \in rel A B.
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
  x \in A ->
  y \in B ->
  R x y ->
  rel_app (inject_rel R A B) x y.
Proof.
unfold inject_rel, rel_app in |- *; intros.
apply subset_intro.
 apply couple_intro; trivial.
 elim (H x (fst (couple x y)) y (snd (couple x y))); intros; auto.
   rewrite fst_def; reflexivity.
   rewrite snd_def; reflexivity.
Qed.

Lemma inject_rel_elim :
  forall (R:set->set->Prop) A B x y,
  ext_rel A R ->
  rel_app (inject_rel R A B) x y ->
  x \in A /\ y \in B /\ R x y.
Proof.
unfold inject_rel, rel_app in |- *; intros.
specialize subset_elim1 with (1 := H0); intro.
elim subset_elim2 with (1 := H0); intros.
assert (x \in A).
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

(* functions *)

Definition is_function f :=
  is_relation f /\
  forall x y y', rel_app f x y -> rel_app f x y' -> y == y'.

Definition app f x :=
  union (subset (rel_image f) (fun y => rel_app f x y)).


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

(*
Lemma repl_fun : forall dom f, repl_rel dom (fun a b => app f a == b).
Proof.
split; intros.
 rewrite <- H0; rewrite <- H1; trivial.
 rewrite <- H0; trivial.
Qed.
*)

Lemma app_defined : forall f x y,
  is_function f -> rel_app f x y -> app f x == y.
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
  is_function f -> x \in rel_domain f -> rel_app f x (app f x).
Proof.
intros.
elim rel_image_ex with (1 := H0); intros.
 rewrite (app_defined f x x0); trivial.
Qed.

(* typing *)

Definition func A B :=
  subset (rel A B)
    (fun r =>
       (forall x, x \in A -> exists2 y, y \in B & rel_app r x y) /\
       (forall x y y', rel_app r x y -> rel_app r x y' -> y == y')).

Instance func_mono :
  Proper (eq_set ==> incl_set ==> incl_set) func.
unfold func; intros A A' eqA B B' inclB z infunc.
specialize subset_elim1 with (1:=infunc); intro.
apply subset_elim2 in infunc.
destruct infunc.
apply subset_intro.
 eapply rel_mono; eauto.
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

Lemma func_rel_incl : forall A B, func A B \incl rel A B.
Proof.
unfold func; red; intros; eapply subset_elim1; eauto.
Qed.

Lemma func_is_function : forall f A B, f \in func A B -> is_function f.
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

Lemma fun_domain_func : forall f A B, f \in func A B -> rel_domain f == A.
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
    apply union_intro with (singl z).
   apply singl_intro.
   elim H2 with (1 := H0); intros.
     red in H6.
     rewrite <- H1 in H6.
     apply union_intro with (2 := H6).
     unfold couple in |- *.
     auto.
  elim H2 with (1 := H0); intros.
    rewrite <- H1 in H5.
    exists x0; trivial.
Qed.

Lemma app_typ :
  forall f x A B, f \in func A B -> x \in A -> app f x \in B.
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
  f \in func A B ->
  (forall x, x \in A -> app f x \in B') ->
  f \in func A B'.
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
  (forall x, x \in A -> f x \in B) ->
  lam_rel f A B \in func A B.
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
  x \in A -> (forall x, x \in A -> f x \in B) -> app (lam_rel f A B) x == f x.
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

(* using replacement axiom *)
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
  (forall x, x \in A -> f x \in B) ->
  lam A f \in func A B.
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
  ext_fun A f -> x \in A -> app (lam A f) x == f x.
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


(* dependent typing *)
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
    (fun f => forall x, x \in A -> app f x \in B x).

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
  (forall x, x \in A -> F x \incl F' x) ->
  dep_func A F \incl dep_func A' F'.
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
  (forall x, x \in dom -> f x \in F x) ->
  lam dom f \in dep_func dom F.
Proof.
intros.
assert (forall x, x \in dom -> f x \in union (dep_image dom F)).
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
  f \in func A B ->
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
  f \in dep_func dom F ->
  f == lam dom (fun x => app f x).
intros.
apply subset_elim1 in H.
apply func_eta with (1:=H).
Qed.

Lemma dep_func_incl_func : forall A B,
  dep_func A B \incl func A (union (dep_image A B)).
Proof.
unfold dep_func in |- *; red in |- *; intros.
apply subset_elim1 with (1 := H).
Qed.

Lemma dep_func_elim :
  forall f x A B, f \in dep_func A B -> x \in A -> app f x \in B x.
Proof.
unfold dep_func in |- *; intros.
elim subset_elim2 with (1 := H); intros.
rewrite H1.
auto.
Qed.
