
Require Import Setoid.
Require Export ZF ZFpairs ZFrelations ZFstable.
Import IZF.

(* CC *)

(* Lambda: Aczel's encoding of functions *)

Definition cc_lam (x:set) (y:set->set) : set :=
  union (replf x (fun x' => replf (y x') (fun y' => couple x' y'))).

Instance cc_lam_morph : Proper (eq_set ==> (eq_set ==> eq_set) ==> eq_set) cc_lam.
unfold cc_lam; do 3 red; intros.
apply union_morph; apply replf_morph; trivial.
red; intros.
apply replf_morph.
 apply H0; trivial.

 red; intros; apply couple_morph; trivial.
Qed.

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

Instance cc_prod_morph : Proper (eq_set ==> (eq_set ==> eq_set) ==> eq_set) cc_prod.
unfold cc_prod; do 3 red; intros.
apply replf_morph.
 apply dep_func_ext; trivial.
 red; auto.

 red; intros.
 apply cc_lam_morph; trivial.
 red; intros; apply app_morph; trivial.
Qed.

Definition cc_arr A B := cc_prod A (fun _ => B).

Instance cc_arr_morph : morph2 cc_arr.
do 3 red; intros.
apply cc_prod_morph; trivial.
red; trivial.
Qed.

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

Lemma cc_arr_intro : forall A B F,
  ext_fun A F ->
  (forall x, x \in A -> F x \in B) ->
  cc_lam A F \in cc_arr A B.
unfold cc_arr; intros.
apply cc_prod_intro; trivial.
Qed.

Lemma cc_arr_elim : forall f x A B,
  f \in cc_arr A B -> 
  x \in A ->
  cc_app f x \in B.
intros.
apply cc_prod_elim with (1:=H); trivial.
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

Lemma cc_prod_stable : forall dom F,
  (forall y y' x x', y == y' -> x \in dom -> x == x' -> F y x == F y' x') ->
  (forall x, x \in dom -> stable (fun y => F y x)) ->
  stable (fun y => cc_prod dom (F y)).
intros dom F Fm Fs.
assert (Hm : morph1 (fun y => cc_prod dom (F y))).
 do 2 red; intros.
 apply cc_prod_ext; auto with *.
 red; intros; apply Fm; auto.
red; red ;intros.
destruct inter_wit with (2:=H) as (w,H0); trivial.
assert (forall x, x \in X -> z \in cc_prod dom (F x)).
 intros.
 apply inter_elim with (1:=H).
 rewrite replf_ax; auto.
 exists x; auto with *.
clear H.
assert (z \in cc_prod dom (F w)) by auto.
rewrite (cc_eta_eq _ _ _ H).
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

(* Classical propositions: we also have a model for classical logic *)

Definition cl_props := subset props (fun P => cc_arr (cc_arr P empty) empty \incl P).

Lemma cc_cl_impredicative_prod : forall dom F,
  ext_fun dom F ->
  (forall x, x \in dom -> F x \in cl_props) ->
  cc_prod dom F \in cl_props.
Proof.
intros dom F eF H.
unfold cl_props in H|- *; intros.
apply subset_intro.
 apply cc_impredicative_prod; intros.
 apply H in H0.
 apply subset_elim1 in H0; trivial.

 red; intros.
 assert (z == empty).
  specialize cc_eta_eq with (1:=H0); intro.
  rewrite H1.
  apply cc_impredicative_lam; intros.
   do 2 red; intros; apply cc_app_morph; auto with *.

   destruct (empty_ax (cc_app z x)).
   apply cc_arr_elim with (1:=H0); trivial.
 rewrite H1.
 rewrite <- (cc_impredicative_lam dom (fun x => empty)); auto with *.
 apply cc_prod_intro; intros; auto with *.
 specialize H with (1:=H2).
 rewrite subset_ax in H; destruct H.
 destruct H3.
 rewrite <- H3 in H4; clear x0 H3.
 apply H4.
 apply in_reg with (cc_lam (cc_arr (F x) empty) (fun _ => empty)).
  apply cc_impredicative_lam; auto with *.
 apply cc_arr_intro; intros; auto with *.
 destruct (empty_ax (cc_app z (cc_lam (cc_prod dom F) (fun f => cc_app f x)))).
 apply cc_prod_elim with (1:=H0).
 apply cc_arr_intro; intros.
  do 2 red; intros; apply cc_app_morph; auto with *.

  destruct (empty_ax (cc_app x0 (cc_app x1 x))).
  apply cc_arr_elim with (1:=H3).
  apply cc_prod_elim with (1:=H5); trivial.
Qed.

(* mapping (meta-level) propositions to props *)

Definition P2p (P:Prop) := cond_set P (singl prf_trm).
Definition p2P p := prf_trm \in p.

Lemma P2p_typ : forall P, P2p P \in props.
unfold P2p; intros.
apply power_intro; intros.
rewrite cond_set_ax in H; destruct H; trivial.
Qed.

Lemma P2p2P : forall P, p2P (P2p P) <-> P.
unfold P2p, p2P; intros.
rewrite cond_set_ax.
split; intros.
 destruct H; trivial.

 split; trivial; apply singl_intro.
Qed.

Lemma p2P2p : forall p, p \in props -> P2p (p2P p) == p.
unfold p2P, P2p; intros.
apply eq_intro; intros.
 rewrite cond_set_ax in H0; destruct H0.
 apply singl_elim in H0.
 rewrite H0; trivial.

 rewrite cond_set_ax; split.
  apply power_elim with (1:=H); trivial.

  apply in_reg with z; trivial.
  apply singl_elim.
  apply power_elim with (1:=H); trivial.
Qed.

Lemma P2p_forall A (B:set->Prop) :
   (forall x x', x \in A -> x == x' -> (B x <-> B x')) ->
   P2p (forall x, x \in A -> B x) == cc_prod A (fun x => P2p (B x)).
intros.
unfold P2p.
apply eq_intro; intros.
 rewrite cond_set_ax in H0; destruct H0.
 apply singl_elim in H0.
 rewrite H0.
 unfold prf_trm; rewrite <- (cc_impredicative_lam A (fun _ => prf_trm)); auto with *.
 2:intros; reflexivity.
 apply cc_prod_intro; intros; auto with *.
  do 2 red; intros.
  apply cond_set_morph; auto with *.

  rewrite cond_set_ax; split; auto; apply singl_intro.

 rewrite cond_set_ax.
 split.
  rewrite cc_eta_eq with (1:=H0).
  rewrite cc_impredicative_lam.
   apply singl_intro.

   do 2 red; intros.
   apply cc_app_morph; auto with *.

   intros.
   specialize cc_prod_elim with (1:=H0) (2:=H1); intro.
   rewrite cond_set_ax in H2; destruct H2.
   apply singl_elim in H2; trivial.

  intros.
  specialize cc_prod_elim with (1:=H0) (2:=H1); intro.
  rewrite cond_set_ax in H2; destruct H2; trivial.
Qed.


Require Import ZFgrothendieck.

Section Universe.

  Hypothesis U : set. (* A grothendieck universe... *)
  Hypothesis Ugrot : grot_univ U.

  Lemma G_cc_prod A B :
    ext_fun A B ->
    A \in U ->
    (forall x, x \in A -> B x \in U) ->
    cc_prod A B \in U.
intros.
unfold cc_prod.
apply G_replf; auto with *.
 apply G_dep_func; intros; auto with *.

 intros.
 unfold cc_lam.
 apply G_union; trivial.
 apply G_replf; trivial.
  apply cc_lam_fun2.
  do 2 red; intros; apply app_morph; auto with *.

  intros.
  assert (app x x0 \in U).
   unfold app.
   apply G_union; trivial.
   apply G_subset; trivial.
   unfold rel_image.
   apply G_subset; trivial.
   apply G_union; trivial.
   apply G_union; trivial.
   apply G_trans with (2:=H2); trivial.
   apply G_dep_func; intros; auto with *.
  apply G_replf; intros; trivial.
  apply G_couple; trivial.
   apply G_trans with A; trivial.

   apply G_trans with (app x x0); trivial.
Qed.


Section Equiv_ZF_CICchoice.

(* We assume now that U is a *ZF* universe (not just IZF),
   so it is closed by collection. *)

  Hypothesis coll_axU : forall A (R:set->set->Prop), 
    A \in U ->
    (forall x x' y y', in_set x A ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    exists2 B, B \in U & forall x, in_set x A -> (exists2 y, y \in U & R x y) ->
       exists2 y, in_set y B & y \in U /\ R x y.

  (* The inductive type of sets (cf Ens.set) and its elimination rule *)
  Hypothesis cc_set : set.

Section SetInU.
  (* Here we assume the elimination rule of the ens inductive type *)
  Hypothesis cc_set_ind :
    forall P : set -> Prop,
    (forall y X f, morph1 f ->
     y == couple X (cc_lam X f) ->
     X \in U ->
     (forall x, x \in X -> f x \in cc_set) ->
     (forall x, x \in X -> P (f x)) ->
     P y) ->
    forall x, x \in cc_set -> P x.

(* sets formed by indexes in U belong to U: *)
Lemma cc_set_incl_U : cc_set \incl U.
red; intros.
apply cc_set_ind with (2:=H); intros.
rewrite H1; clear H1 y.
apply G_couple; trivial.
unfold cc_lam.
apply G_union; trivial.
apply G_replf; trivial.
 do 2 red; intros.
 apply replf_morph.
  apply H0; trivial.
  red; intros.
  apply couple_morph; trivial.

 intros.
 apply G_replf; intros; auto.
 apply G_couple; trivial.
  apply G_trans with X; trivial.
  apply G_trans with (f x); auto.
Qed.

End SetInU.

  (* All we need to know about cc_set is that it's included in U, so the ttcoll
     axiom is really an instance of collection for universe U. *)
  Hypothesis cc_set_incl_U : cc_set \incl U.

(* We don't even need the introduction rule for sets:
Hypothesis cc_set_eq : cc_set == sigma U (fun X => cc_arr X cc_set).
*)

(* specialize version of Ens.ttcoll with B:=cc_set *)
Lemma cc_ttcoll A R :
  Proper (eq_set ==> eq_set ==> iff) R ->
  A \in U ->
  (forall x, x \in A -> exists2 y, y \in cc_set & R x y) ->
  exists2 X, X \in U & exists2 f, f \in cc_arr X cc_set &
    forall x, x \in A -> exists2 i, i \in X & R x (cc_app f i).
intros.
destruct coll_axU with (A:=A) (R:=fun x y => y \in cc_set /\ R x y) as (B,HB);
  trivial.
 intros.
 rewrite <- H3; rewrite <- H4; trivial.

 pose (B':= inter2 B cc_set).
 exists B'.
  apply G_incl with B; trivial.
  apply inter2_incl1.
 exists (cc_lam B' (fun x => x)).
  apply cc_arr_intro; intros.
   do 2 red; intros; trivial.
   revert H3; apply inter2_incl2.
 intros.
 destruct H2 with (1:=H3) as (y,yB,(yU,(ys,yR))).
  destruct H1 with (1:=H3).
  exists x0; auto.

  exists y.
   unfold B'; rewrite inter2_def; auto.

   rewrite cc_beta_eq; trivial.
    do 2 red; auto.

    unfold B'; rewrite inter2_def; auto.
Qed.

End Equiv_ZF_CICchoice.

End Universe.
