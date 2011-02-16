Require Import List.
Require Export HF.

(* functions *)

Definition lam (x:hf) (f:hf->hf) :=
  repl x (fun x => couple x (f x)).


Lemma lam_intro : forall x dom F,
  eq_hf_fun dom F F ->
  x \in dom ->
  couple x (F x) \in lam dom F.
intros.
unfold lam.
apply repl_intro with x; trivial.
 red; intros.
 apply couple_morph; auto.

 reflexivity.
Qed.

Lemma lam_elim : forall p dom F,
  eq_hf_fun dom F F ->
  p \in lam dom F ->
  exists2 x, x \in dom & p == couple x (F x).
unfold lam; intros.
apply repl_elim; trivial. 
red; intros.
apply couple_morph; auto.
Qed.

Lemma lam_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_hf_fun x1 f1 f2 ->
  lam x1 f1 == lam x2 f2.
unfold lam in |- *; intros.
apply repl_morph; trivial.
red in |- *; intros.
apply couple_morph; trivial.
apply H0; trivial.
Qed.

Definition image f := repl f snd.
Definition domain f := repl f fst.

Instance domain_morph : morph1 domain.
unfold domain in |- *; do 2 red; intros.
apply repl_morph; trivial.
red in |- *; intros.
apply fst_morph; trivial.
Qed.

Instance image_morph : morph1 image.
unfold image in |- *; do 2 red; intros.
apply repl_morph; trivial.
red in |- *; intros.
apply snd_morph; trivial.
Qed.

Lemma lam_domain : forall x F,
 eq_hf_fun x F F ->
 domain (lam x F) == x.
unfold domain in |- *.
intros.
assert (M0: eq_hf_fun (lam x F) fst fst).
 red; intros.
 rewrite H1; reflexivity.
assert (M1: eq_hf_fun x
 (fun x : hf => couple x (F x))(fun x : hf => couple x (F x))).
 red; intros.
 apply couple_morph; auto.

symmetry.
apply repl_ext; intros; trivial.
 unfold lam in H0. 
 elim repl_elim with (2 := H0); clear H0; intros.
  rewrite H1; rewrite fst_def; trivial.

  red; intros; apply couple_morph; auto.

  exists (couple y (F y)).
   unfold lam in |- *.
   apply repl_intro with y; trivial.
   reflexivity.

   symmetry  in |- *; apply fst_def.
Qed.

Definition app (x y: hf) :=
  snd (union (subset x (fun p => eq_hf (fst p) y))).

Instance app_morph : morph2 app.
unfold app; do 3 red; intros.
apply snd_morph.
apply union_morph.
apply subset_morph_ext; trivial.
red in |- *; intros.
apply eq_hf_morph; trivial.
apply fst_morph; trivial.
Qed.

Lemma app_def: forall f x y,
  couple x y \in f ->
  (forall p, p \in f -> fst p == x -> p == couple x y) ->
  app f x == y.
unfold app; intros.
rewrite (subset_singl (couple x y)); trivial; intros.
 rewrite union_singl.
 apply snd_def.

 apply fst_def.

 split; intros.
  change (fst x' == x).
  rewrite <- H2.
  apply fst_def.

  symmetry; auto.
Qed.

Lemma beta_eq :
  forall dom F x,
  eq_hf_fun dom F F ->
  x \in dom ->
  app (lam dom F) x == F x.
intros.
apply app_def.
 apply lam_intro; trivial.

 intros.
 apply lam_elim in H1; trivial.
 destruct H1.
 rewrite H3.
 rewrite H3 in H2.
 rewrite fst_def in H2.
 apply couple_morph; auto.
Qed.

Definition func_cons f x y :=
  HF(couple x y::hf_elts f).

Instance func_cons_morph : morph3 func_cons.
unfold func_cons; do 4 red; intros.
apply Eq_hf_cons.
 apply couple_morph; trivial.
 repeat rewrite hf_elts_ext; trivial.
Qed.

Definition func_map_image F x Y :=
  union (repl F (fun f => repl Y (fun y' => func_cons f x y'))).

Lemma df_morph1 : forall dom y a,
  eq_hf_fun dom (fun y' => func_cons y a y')
    (fun y' => func_cons y a y').
red; intros.
rewrite H0; reflexivity.
Qed.

Lemma df_morph2 : forall F a y,
  eq_hf_fun F (fun f => repl y (fun y' => func_cons f a y'))
    (fun f => repl y (fun y' => func_cons f a y')).
red; intros.
apply repl_ext.
 apply df_morph1.

 intros.
 apply repl_intro with y0; trivial.
  apply df_morph1.
  rewrite H0; reflexivity.

 intros.
 elim repl_elim with (2:=H1); intros.
  exists x; trivial.
  rewrite <- H0; trivial.

  apply df_morph1.
Qed.

Lemma func_map_image_intro: forall f x y F Y,
  f \in F ->
  y \in Y ->
  func_cons f x y \in func_map_image F x Y.
intros.
unfold func_map_image.
apply union_intro with
  (repl Y (fun y' => func_cons f x y')).
 apply repl_intro with y; auto.
  apply df_morph1.
  reflexivity.

 apply repl_intro with f; trivial.
  apply df_morph2.
  reflexivity.
Qed.

Lemma func_map_image_elim : forall g x F Y,
  g \in func_map_image F x Y ->
  exists2 f, f \in F &
  exists2 y, y \in Y & g == func_cons f x y.
unfold func_map_image; intros.
elim union_elim with (1:=H); clear H; intros.
elim repl_elim with (2:=H0); clear H0; intros.
2:apply df_morph2.
rewrite H1 in H; clear x0 H1.
exists x1; trivial.
elim repl_elim with (2:=H); clear H; intros.
2:apply df_morph1.
exists x0; trivial.
Qed.

Definition func (x y: hf) :=
  fold_set hf
    (fun x' fs => func_map_image fs x' y)
    x (singl empty).

Definition dep_func (x:hf) (y:hf->hf) :=
  fold_set hf
    (fun x' fs => func_map_image fs x' (y x'))
    x (singl empty).

Lemma dep_func_intro :
  forall f X Y,
  eq_hf_fun X f f ->
  eq_hf_fun X Y Y ->
  (forall x, x \in X -> f x \in Y x) ->
  lam X f \in dep_func X Y.
Proof.
intros f X Y.
unfold lam, dep_func.
set (g:=fun x' fs => func_map_image fs x' (Y x')).
pattern X, (fold_set hf g X (singl empty)).
apply fold_set_ind; intros.
 compute; reflexivity.
 rewrite (@repl_morph (HF(x'::hf_elts y)) y (fun x => couple x (f x))
    (fun x => couple x (f x))).
  apply H1; intros.
   red; intros.
   apply H2; trivial; apply In_hf_tail; trivial.

   red; intros.
   apply H3; trivial; apply In_hf_tail; trivial.

   apply H4; apply In_hf_tail; trivial.

  apply Eq_hf_intro; red; intros.
   elim In_hf_elim with (1:=H5); intros.
    rewrite H6; trivial.
    rewrite hf_elts_ext in H6; trivial.
   apply In_hf_tail; rewrite hf_elts_ext; trivial.

  red; intros.
  apply couple_morph; trivial.
  apply H2; trivial.

 pose (h := repl (HF(hf_elts y)) (fun x => couple x (f x))).
 change (func_cons h x' (f x') \in g x' acc).

 assert (h \in acc).
  apply H1; intros.
   red; intros.
   apply H2; trivial; apply In_hf_tail; trivial.

   red; intros.
   apply H3; trivial; apply In_hf_tail; trivial.

   apply H4; apply In_hf_tail; trivial.
 assert (f x' \in Y x').
  apply H4.
  apply In_hf_head; reflexivity.
 clear H1 H2 H3 H4.
 unfold g.
 apply func_map_image_intro; trivial.
Qed.

Lemma dep_func_elim0 : forall f p X Y,
  f \in dep_func X Y ->
  p \in f ->
  (exists2 x, x \in X &
  exists2 y, y \in Y x &
  p == couple x y) /\
  (forall p', p' \in f -> fst p == fst p' -> p == p').
intros f p X Y.
unfold dep_func.
set (g:=fun x' fs => func_map_image fs x' (Y x')).
generalize f p; clear f p.
pattern X, (fold_set hf g X (singl empty)).
apply fold_set_ind; intros.
 elim empty_elim with p.
 rewrite <- (singl_elim _ _ H); trivial.

 destruct (H1 f p); trivial.
 split; intros; eauto.
  destruct H4.
  destruct H6.
  exists x.
   apply In_hf_tail; rewrite hf_elts_ext; trivial.
   exists x0; trivial.

 subst g; simpl in *.
 elim func_map_image_elim with (1:=H2); intros.
 destruct H5.
 split; intros.
  rewrite H6 in H3; clear f H2 H6.
  unfold func_cons in H3.
  elim In_hf_elim with (1:=H3); clear H3; intros.
   exists x'.
    apply In_hf_head; reflexivity.
    exists x0; trivial.

   rewrite hf_elts_ext in H2.
   elim (H1 x p); trivial; intros.
   destruct H3.
   destruct H7.
   exists x1.
    apply In_hf_tail; trivial.
    exists x2; trivial.

  rewrite H6 in H3,H7|-; clear f H2 H6.
  unfold func_cons in H7,H3|-.
  elim In_hf_elim with (1:=H7); clear H7; intros;
    elim In_hf_elim with (1:=H3); clear H3; intros.
   rewrite H2; trivial.

   elim H0.
   rewrite hf_elts_ext in H3.
   rewrite H2 in H8; clear H2.
   rewrite fst_def in H8.
   rewrite <- H8; intros; clear H8.
   elim H1 with x p; trivial; intros.
   destruct H2.
   destruct H7.
   rewrite H8; rewrite fst_def; trivial.

   elim H0.
   rewrite hf_elts_ext in H2.
   rewrite H3 in H8; clear H3.
   rewrite fst_def in H8.
   rewrite H8; intros; clear H8.
   elim H1 with x p'; trivial; intros.
   destruct H3.
   destruct H7.
   rewrite H8; rewrite fst_def; trivial.

   rewrite hf_elts_ext in H2,H3|-.
   elim H1 with x p; trivial; intros; eauto.
Qed.



Lemma dep_func_total : forall f x X Y,
  f \in dep_func X Y ->
  x \in X ->
  exists2 p, fst p == x & p \in f.
intros f x X Y.
unfold dep_func.
set (g:=fun x' fs => func_map_image fs x' (Y x')).
generalize f x; clear f x.
pattern X, (fold_set hf g X (singl empty)).
apply fold_set_ind; intros.
 elim empty_elim with x; trivial.

 apply H1; trivial.
 elim In_hf_elim with (1:=H3); clear H3; intros.
  rewrite H3; trivial.
  rewrite hf_elts_ext in H3; trivial.

 subst g; simpl in *.
 elim func_map_image_elim with (1:=H2); clear H2; intros.
 destruct H4.
 elim In_hf_elim with (1:=H3); clear H3; intros.
  exists (couple x' x1).
   rewrite fst_def; symmetry; trivial.

   rewrite H5; unfold func_cons.
   apply In_hf_head; reflexivity.

  rewrite hf_elts_ext in H3.
  elim H1 with x0 x; trivial; intros.
  exists x2; trivial.
  rewrite H5; unfold func_cons.
  apply In_hf_tail; trivial.
Qed.

Lemma dep_func_elim : forall f x X Y,
  eq_hf_fun X Y Y ->
  f \in dep_func X Y ->
  x \in X ->
  app f x \in Y x.
intros.
elim dep_func_total with (1:=H0)(2:=H1); intros.
elim dep_func_elim0 with (1:=H0)(2:=H3); intros.
destruct H4.
destruct H6.
rewrite H7 in H2.
rewrite fst_def in H2.
rewrite <- (H _ _ H4 H2); trivial.
rewrite H7 in H3.
rewrite app_def; intros; eauto.
 rewrite <- H2; trivial.

 apply H5 in H8.
  rewrite <- H8.
  rewrite H7.
  rewrite H2; reflexivity.

  rewrite H7; rewrite H9; rewrite fst_def; trivial.
Qed.

Lemma dep_func_eta: forall f X Y,
  f \in dep_func X Y ->
  f == lam X (fun x => app f x).
intros.
unfold lam.
apply repl_ext; intros.
 red; intros.
 rewrite H1; reflexivity.

 elim dep_func_total with (1:=H)(2:=H0); intros.
 elim dep_func_elim0 with (1:=H)(2:=H2); intros.
 destruct H3.
 destruct H5.
 rewrite H6 in H1; rewrite fst_def in H1.
 rewrite H6 in H2.
 rewrite H1 in H2,H6|-.
 rewrite app_def; intros; eauto.
 apply H4 in H7.
  rewrite <- H7; trivial.

  rewrite H6; rewrite H8; apply fst_def.

 elim dep_func_elim0 with (1:=H) (2:=H0); intros.
 destruct H1.
 destruct H3.
 exists x; trivial.
 rewrite app_def; intros; eauto.
  rewrite <- H4; trivial.

  rewrite <- (H2 p); trivial.
  rewrite H4; rewrite fst_def; rewrite H6; reflexivity.
Qed.


Lemma dep_func_ext : forall x1 x2 y1 y2,
  x1 == x2 ->
  eq_hf_fun x1 y1 y2 ->
  dep_func x1 y1 == dep_func x2 y2.
intros.
assert (eq_hf_fun x2 y2 y2).
 generalize (eq_hf_fun_left _ _ _ (eq_hf_fun_sym _ _ _ H0)); intro.
 red; intros; apply H1; trivial.
 rewrite H; trivial.
apply Eq_hf_intro; red; intros.
 setoid_replace a with (lam x2 (fun x => app a x)).
  apply dep_func_intro; intros; trivial.
   red; intros.
   rewrite H4; reflexivity.

   setoid_replace (y2 x) with (y1 x).
    apply dep_func_elim with x1; trivial.
     apply eq_hf_fun_left with y2; trivial.

     rewrite H; trivial.

     symmetry; apply H0; try reflexivity.
     rewrite H; trivial.

  setoid_replace (lam x2 (fun x => app a x))
    with (lam x1 (fun x => app a x)).
   apply dep_func_eta with y1; trivial.

   symmetry; apply lam_ext; trivial.
   red; intros.
   rewrite H4; reflexivity.

 setoid_replace a with (lam x1 (fun x => app a x)).
  apply dep_func_intro; intros; trivial.
   red; intros.
   rewrite H4; reflexivity.

   apply eq_hf_fun_left with y2; trivial.

   setoid_replace (y1 x) with (y2 x).
    apply dep_func_elim with x2; trivial.
     rewrite <- H; trivial.

     apply H0; trivial; try reflexivity.

  setoid_replace (lam x1 (fun x => app a x))
    with (lam x2 (fun x => app a x)).
   apply dep_func_eta with y2; trivial.

   apply lam_ext; trivial.
   red; intros.
   rewrite H4; reflexivity.
Qed.

(* examples *)

(*
Eval compute in (in_hf hf_negb (func hf_bool hf_bool)).

Eval compute in
 (in_hf hf_negb (dep_func hf_bool (fun b => singl(app hf_negb b)))).

*)
