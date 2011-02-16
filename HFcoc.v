
Require Import Setoid.
Require Export HFrelation.

(* CC *)

Definition ext_fun dom F := eq_hf_fun dom F F.

(* Lambda: Aczel's encoding of functions *)

Definition cc_lam (x:hf) (y:hf->hf) : hf :=
  union (repl x (fun x' => repl (y x') (fun y' => couple x' y'))).

Lemma cc_lam_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_hf_fun x1 f1 f2 ->
  cc_lam x1 f1 == cc_lam x2 f2.
unfold cc_lam in |- *; intros.
apply union_morph.
apply repl_morph; trivial.
red in |- *; intros.
apply repl_morph.
 apply H0; trivial.
 red in |- *; intros.
   apply couple_morph; trivial.
Qed.

(* Application *)

Definition cc_app (x y:hf) : hf :=
  image (subset x (fun p => eq_hf (fst p) y)).

Instance cc_app_morph : morph2 cc_app.
unfold cc_app; do 3 red; intros.
apply image_morph.
apply subset_morph_ext; trivial.
red in |- *; intros.
rewrite H0; rewrite H2; reflexivity.
Qed.

(* Beta conversion *)

Lemma cc_beta_eq:
  forall dom F x,
  eq_hf_fun dom F F ->
  x \in dom ->
  cc_app (cc_lam dom F) x == F x.
Proof.
intros.
unfold cc_app, cc_lam in |- *.
unfold image in |- *.
let t := match goal with |- context[subset ?t _] => t end in
assert (Pm : hf_pred_morph t (fun p => eq_hf (fst p) x)).
 red; intros.
 rewrite <- H3.
 rewrite H2; trivial.
assert (Pm': ext_fun dom
   (fun x' => repl (F x') (fun y' => couple x' y'))).
 red; red; intros.
 apply repl_morph; auto.
 red; intros.
 apply couple_morph; auto.
symmetry.
apply repl_ext; intros.
 red; intros.
 apply snd_morph; trivial.

 specialize subset_elim1 with (1 := H1); intro.
 specialize subset_elim2 with (1:=Pm) (2 := H1); clear H1; intro.
 elim union_elim with (1 := H2); clear H2; intros.
 elim repl_elim with (1:=Pm') (2 := H3); clear H3; intros.
 assert (Pm'': ext_fun (F x1) (fun y' => couple x1 y')).
  red; red; intros; apply couple_morph; trivial; reflexivity.
 rewrite H4 in H2.
 clear H4 x0.
 elim repl_elim with (1:=Pm'') (2 := H2); intros; clear H2.
 rewrite H5 in H1 |- *; rewrite snd_def; rewrite fst_def in H1.
 apply in_hf_reg_r with (F x1); auto.

 exists (couple x y).
  apply subset_intro; trivial.
   apply union_intro with (repl (F x) (fun y' => couple x y')).
    apply repl_intro with y; auto.
     red; intros.
     apply couple_morph; trivial; reflexivity.

     reflexivity.

    apply repl_intro with x; trivial; reflexivity.

    apply fst_def.
  symmetry; apply snd_def.
Qed.


(* Typing: dependent products *)

Definition cc_prod (x:hf) (y:hf->hf) : hf :=
  repl (dep_func x y) (fun f => cc_lam x (fun x' => app f x')).

Lemma beta_morph : forall dom F,
  ext_fun (dep_func dom F)
    (fun f0 : hf => cc_lam dom (fun x' : hf => app f0 x')).
Proof.
red; red; intros.
apply cc_lam_ext; try reflexivity.
red; intros; apply app_morph; trivial.
Qed.
Hint Resolve beta_morph.

Lemma cc_prod_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_hf_fun x1 f1 f2 ->
  cc_prod x1 f1 == cc_prod x2 f2.
Proof.
unfold cc_prod in |- *; intros.
apply repl_morph.
 apply dep_func_ext; trivial.
 red in |- *; intros.
   apply cc_lam_ext; auto.
   red in |- *; intros.
   apply app_morph; auto.
Qed.

Lemma cc_prod_intro : forall dom f F,
  eq_hf_fun dom f f ->
  eq_hf_fun dom F F ->
  (forall x, x \in dom -> f x \in F x) ->
  cc_lam dom f \in cc_prod dom F.
unfold cc_prod in |- *.
intros.
apply repl_intro with (lam dom f); trivial.
 exact (beta_morph dom F).

 apply dep_func_intro; trivial.
 apply cc_lam_ext; intros.
  reflexivity.

  red in |- *; intros.
  symmetry  in |- *.
  transitivity (f y2).
   apply beta_eq; trivial.
   apply in_hf_reg_l with y1; auto.

   symmetry  in |- *.
   apply H; trivial.
Qed.

Lemma cc_prod_elim : forall dom f x F,
  eq_hf_fun dom F F ->
  f \in cc_prod dom F ->
  x \in dom ->
  cc_app f x \in F x.
intros dom f x F Fext ? ?.
unfold cc_prod in H.
elim repl_elim with (1:=beta_morph dom F) (2 := H); clear H; intros.
apply in_hf_reg_l with (cc_app (cc_lam dom (fun x' => app x0 x')) x).
 apply cc_app_morph; auto.
  symmetry  in |- *; trivial.
  reflexivity.
 apply in_hf_reg_l with (app x0 x).
  symmetry  in |- *.
    apply cc_beta_eq; trivial.
    red; red in |- *; intros.
    apply app_morph; trivial.
    reflexivity.
  apply dep_func_elim with (1:=Fext) (2 := H) (3 := H0).
Qed.

(* impredicativity *)

Definition prf_trm := empty.
Definition props := power (singl prf_trm).

Lemma cc_impredicative_lam : forall dom F,
  eq_hf_fun dom F F ->
  (forall x, x \in dom -> F x == prf_trm) ->
  cc_lam dom F == prf_trm.
Proof.
unfold cc_lam in |- *; intros.
apply empty_ext.
red in |- *; intros.
elim union_elim with (1 := H1); clear H1; intros.
assert (ext_fun dom (fun x' => repl (F x') (fun y' => couple x' y'))).
 red; red; intros.
 apply repl_morph; auto.
 red; intros.
 apply couple_morph; auto.
elim repl_elim with (1:=H3) (2 := H2); clear H2; intros.
specialize in_hf_reg_r with (1 := H4) (2 := H1); clear H4 H1 x0.
intro.
assert (ext_fun (F x1) (fun y' => couple x1 y')).
 red; red; intros.
 rewrite H5; reflexivity.
elim repl_elim with (1:=H4) (2 := H1); intros.
apply empty_elim with x0.
apply in_hf_reg_r with (F x1); trivial.
auto.
Qed.

Lemma cc_impredicative_prod : forall dom F,
  eq_hf_fun dom F F ->
  (forall x, x \in dom -> F x \in props) ->
  cc_prod dom F \in props.
Proof.
unfold props in |- *; intros dom F Fext ?.
apply power_intro; red; intros.
apply singl_intro.
unfold prf_trm in |- *.
unfold cc_prod in H0.
elim repl_elim with (1:=beta_morph dom F) (2 := H0); intros.
apply eq_hf_trans with (1 := H2).
apply cc_impredicative_lam.
 red; intros; apply app_morph; trivial; reflexivity.

 intros.
 specialize dep_func_elim with (1:=Fext) (2 := H1) (3 := H3); intro.
 specialize H with (1 := H3).
 specialize power_elim with (1 := H) (2 := H4); intro.
 apply singl_elim; trivial.
Qed.

