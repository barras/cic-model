Require Import ZF.
Require Import Setoid.

Parameter repl1 : forall (x:set) (F:{y|in_set y x}->set), set.

Parameter repl1_ax : forall x F z,
  (forall z z', proj1_sig z == proj1_sig z' -> F z == F z') ->
  (z ∈ repl1 x F <-> exists y, z == F y).

Parameter repl1_morph : forall x y F G,
  x == y ->
  (forall x' y', proj1_sig x' == proj1_sig y' -> F x' == G y') ->
  repl1 x F == repl1 y G.


(** Investigations on the relation between the various
   statements of replacement and collection.
 *)

(** 1- Replacement *)

(** Relation is required to be functional only on A *)
Definition rep_bnd A R :=
  Proper (eq_set ==> eq_set ==> iff) R ->
  (forall x, x ∈ A -> exists y, R x y) ->
  (forall x y y', x ∈ A -> R x y -> R x y' -> y == y') ->
  exists B, forall y, (y ∈ B <-> exists x, x ∈ A /\ R x y).

(** Weaker statement (the constraint on R is tighter): the
    relation should be functional on the full class of sets. *)
Definition rep_ubnd A R :=
  Proper (eq_set ==> eq_set ==> iff) R ->
  (forall x, exists y, R x y) ->
  (forall x y y', R x y -> R x y' -> y == y') ->
  exists B, forall y, (y ∈ B <-> exists x, x ∈ A /\ R x y).

(** The bounded version is stronger. *)
Lemma rep_bnd_ubnd : forall A R, rep_bnd A R -> rep_ubnd A R.
red; intros.
apply H; eauto.
Qed.

(** Both versions are equivalent when membership to A can be
   "decided" (in Prop), either because we are in classical logic, or
   because it can be decided. *)
Lemma rep_ubnd_bnd_dec :
  forall A, (forall x, x ∈ A \/ ~ x ∈ A) ->
  (forall R, rep_ubnd A R) -> (forall R, rep_bnd A R).
red; intros.
destruct (H0 (fun x y => (x ∈ A /\ R x y) \/
                         (~ x ∈ A /\ y == empty))).
 do 3 red; intros.
 rewrite H4; rewrite H5; reflexivity.

 intros.
 destruct (H x).
  destruct H2 with x; trivial.
  exists x0; auto.

  exists empty; auto with *.

 intros.
 destruct H4.
  destruct H4.
  destruct H5.
   destruct H5; eauto.

   destruct H5.
   elim H5; trivial.

  destruct H5.
   destruct H4; destruct H5.
   elim H4; trivial.

   destruct H4; destruct H5.
   rewrite H7; trivial.

 exists x; intros.
 rewrite H4.
 split; intros.
  destruct H5.
  exists x0.
  destruct H5 as (?,[?|(?,_)]); auto.
  elim H6; trivial.

  destruct H5.
  destruct H5.
  exists x0; auto.
Qed.

(** A more general presentation, not requiring the relation to be
   functional, but then only the images of inputs where the relation
   is functional are collected.
   It is equivalent to the bounded statement. *)
Definition rep_gen A R :=
  Proper (eq_set ==> eq_set ==> iff) R ->
  exists B, forall y,
    (y ∈ B <->
     exists x, x ∈ A /\ R x y /\ (forall y', R x y' -> y==y')).

Lemma rep_bnd_gen :
  (forall A R, rep_bnd A R) <-> (forall A R, rep_gen A R).
split; red; intros.
 destruct (H (subset A (fun x => (exists y, R x y) /\
                     (forall y y', R x y -> R x y' -> y==y')))
             R); trivial.
  intros.
  apply subset_elim2 in H1.
  destruct H1.
  destruct H2.
  destruct H2.
  exists x1.
  rewrite H1; trivial.

  intros.
  apply subset_elim2 in H1.
  destruct H1.
  destruct H4.
  rewrite H1 in H2,H3; auto.

  exists x; intros.
  rewrite H1.
  split; intros.
   destruct H2.
   exists x0.
   destruct H2.
   split; [|split]; trivial.
    apply subset_elim1 in H2; trivial.

    apply subset_elim2 in H2.
    destruct H2.
    intros.
    destruct H4.
    rewrite H2 in H3,H5; auto.

   destruct H2.
   exists x0.
   destruct H2 as (?,(?,?)).
   split; trivial.
   apply subset_intro; auto.
   split.
    exists y; trivial.

    intros.
    transitivity y; auto.
    symmetry; auto.

 destruct (H A R); trivial.
 exists x; intros.
 rewrite H3.
 split; intros.
  destruct H4 as (x0,(?,(?,_))).
  exists x0; auto.

  destruct H4 as (x0,(?,?)).
  exists x0; split; [|split]; trivial; eauto.
Qed.

(** Summary for replacement:
   rep_gen <--> rep_bnd --> rep_ubnd
                        <-- (if A is decidable)
*)
(*Parameter uch : forall P, Proper (eq_set ==> iff) P ->
  (exists x, P x) ->
  (forall x x', P x -> P x' -> x == x') ->
  exists x{ x | P x }
*)
(*
Parameter uch : forall P, Proper (eq_set ==> iff) P ->
  (exists x, P x) ->
  (forall x x', P x -> P x' -> x == x') ->
  { x | P x }.

Parameter uch_ext :
  forall P Q, (forall x, P x <-> Q x) ->
  forall m1 m2 w1 w2 u1 u2,
  proj1_sig (uch P m1 w1 u1) == proj1_sig (uch Q m2 w2 u2).

Lemma repl : forall A R, rep_ubnd A R.
red; intros.
assert
  (forall x, Proper (eq_set ==> iff) (fun y => R x y)).
 do 2 red; intros.
 rewrite H2; reflexivity.
exists (replf A (fun x => proj1_sig (uch _ (H2 x) (H0 x) (H1 x)))). 
intros.
rewrite replf_ax.
 split; intros.
  destruct H3.
  exists x; split; trivial.
  rewrite H4.
  apply proj2_sig.

  destruct H3.
  destruct H3.
  exists x; trivial.
  apply H1 with x; trivial.
  apply proj2_sig.

 red; red; intros.
 apply uch_ext.
 intros.
 rewrite H4; reflexivity.
Qed.
*)


(** 2- Collection *)

(** The bounded version *)
Definition coll_bnd A R :=
  Proper (eq_set ==> eq_set ==> iff) R ->
  (forall x, x ∈ A -> exists y, R x y) ->
  exists B, forall x, x ∈ A -> exists y, y ∈ B /\ R x y.

(** The unbounded version *)
Definition coll_ubnd A R :=
  Proper (eq_set ==> eq_set ==> iff) R ->
  (forall x, exists y, R x y) ->
  exists B, forall x, x ∈ A -> exists y, y ∈ B /\ R x y.

(** The same relationship between these statements hold for collection: *)
Lemma coll_bnd_ubnd : forall A R, coll_bnd A R -> coll_ubnd A R.
red; intros.
apply H; trivial.
Qed.

Lemma coll_ubnd_bnd_dec :
  forall A, (forall x, x ∈ A \/ ~ x ∈ A) ->
  (forall R, coll_ubnd A R) -> (forall R, coll_bnd A R).
red; intros.
destruct (H0 (fun x y => R x y \/ (~ x ∈ A /\ y == empty))).
 do 3 red; intros.
 rewrite H3; rewrite H4; reflexivity.

 intros.
 destruct (H x).
  destruct H2 with x; trivial.
  exists x0; auto.

  exists empty; auto with *.

 exists x; intros.
 destruct H3 with x0; trivial.
 destruct H5.
 destruct H6.
  exists x1; auto.

  destruct H6.
  elim H6; trivial.
Qed.

(** The "general" version, equivalent to the bounded one. *)
Definition coll_gen A R :=
  Proper (eq_set ==> eq_set ==> iff) R ->
  exists B, forall x, x ∈ A -> (exists y, R x y) -> exists y, y ∈ B /\ R x y.

Lemma coll_bnd_gen :
  (forall A R, coll_bnd A R) <-> (forall A R, coll_gen A R).
split; red; intros.
 destruct (H (subset A (fun x => exists y, R x y)) R); trivial.
  intros.
  apply subset_elim2 in H1.
  destruct H1.
  destruct H2.
  exists x1.
  rewrite H1; trivial.

  exists x; intros.
  apply H1.
  apply subset_intro; auto.

 destruct (H A R); trivial.
 exists x; intros.
 apply H2; auto.
Qed.

(** 3- Collection implies Replacement *)

Lemma coll_repl_bnd : forall A R, coll_bnd A R -> rep_bnd A R.
red; intros.
destruct H; auto.
exists (subset x (fun x' => exists x, x ∈ A /\ R x x')); intros.
split; intros.
 specialize subset_elim2 with (1:=H3); intros.
 destruct H4.
 destruct H5.
 exists x1.
 destruct H5; split; trivial.
 rewrite H4; trivial.

 destruct H3.
 destruct H3.
 apply subset_intro.
  destruct H with (1:=H3).
  destruct H5.
  setoid_replace y with x1; trivial; eauto.

  exists x0; auto.
Qed.

Lemma coll_repl_ubnd : forall A R, coll_ubnd A R -> rep_ubnd A R.
red; intros.
destruct H; auto.
exists (subset x (fun x' => exists x, x ∈ A /\ R x x')); intros.
split; intros.
 specialize subset_elim2 with (1:=H3); intros.
 destruct H4.
 destruct H5.
 exists x1.
 rewrite H4; trivial.

 destruct H3.
 destruct H3.
 apply subset_intro.
  destruct H with (1:=H3).
  destruct H5.
  setoid_replace y with x1; trivial; eauto.

  exists x0; auto.
Qed.

(** 4- Replacement + excluded-middle imples Collection. *)

Section ReplImpliesCollFromExcludedMiddleAndWellFoundation.

Parameter rk : set -> set.

Instance rk_morph : morph1 rk.
Admitted.

Parameter rk_def : forall x z,
  z ∈ rk x <-> exists y, y ∈ x /\ z ∈ power (rk y).

Lemma rk_trans : forall x y z,
  z ∈ y -> y ∈ rk x -> z ∈ rk x.
intros x.
pattern x; apply wf_ax; trivial; clear x; intros.
rewrite rk_def in H1|-*.
destruct H1.
destruct H1.
exists x0; split; trivial.
rewrite power_ax in H2|-*; intros.
apply H with z; auto.
Qed.

Lemma rk_sub : forall x y y',
  y ∈ rk x -> y' ⊆ y -> y' ∈ rk x.
intros x.
pattern x; apply wf_ax; trivial; clear x; intros.
rewrite rk_def in H0|-*.
destruct H0; destruct H0.
exists x0; split; trivial.
rewrite power_ax in H2|-*; intros; auto.
Qed.

Lemma rk_mono : forall x x',
  x ∈ x' -> rk x ∈ rk x'.
intros.
rewrite (rk_def x').
exists x; split; trivial.
apply power_intro; trivial.
Qed.


Lemma rk_compl : forall x z, z ∈ rk x -> rk z ∈ rk x. 
intros x.
pattern x; apply wf_ax; trivial; clear x; intros.
rewrite rk_def in *.
destruct H0; destruct H0.
exists x0; split; trivial.
rewrite power_ax in *; intros.
rewrite rk_def in H2; destruct H2; destruct H2.
specialize H1 with (1:=H2).
assert (rk x1 ∈ rk x0) by auto.
apply rk_sub with (rk x1); trivial.
rewrite power_ax in H3; auto.
Qed.

Lemma rk_pow : forall x, power (rk x) == rk (singl x).
intros.
apply eq_intro; intros.
 rewrite rk_def.
 exists x; split; trivial.
 apply singl_intro.

 rewrite rk_def in H; destruct H; destruct H.
 apply singl_elim  in H.
 rewrite <- H; trivial.
Qed.

Lemma rk_intro :
  forall x, x ∈ power (rk x).
intros.
pattern x; apply wf_ax; trivial; clear x; intros.
rewrite power_ax; intros.
rewrite rk_def.
exists y; split; auto.
Qed.

Lemma rk_idem : forall x, rk (rk x) == rk x.
intros.
apply eq_intro; intros.
 rewrite rk_def in H; destruct H; destruct H.
 rewrite power_ax in H0.
 apply rk_sub with (rk x0); trivial.
 apply rk_compl; trivial.

 apply rk_sub with (rk z).
  apply rk_mono; trivial.
  red; rewrite <- power_ax; apply rk_intro.
Qed.

Lemma rk_induc :
  forall P:set->Prop, (forall x, (forall y, y ∈ rk x -> P y) -> P x) ->
  forall x, P x.
intros.
cut (forall y, rk y ⊆ rk x -> P y).
 intros.
 apply H0.
 red; trivial.
pattern x; apply wf_ax; trivial; clear x; intros.
apply H; intros.
apply H1 in H2.
rewrite rk_def in H2; destruct H2; destruct H2.
rewrite power_ax in H3.
apply H0 with x0; trivial.
red; intros.
rewrite rk_def in H4; destruct H4; destruct H4.
rewrite power_ax in H5.
apply H3 in H4.
apply rk_sub with (rk x1); trivial.
apply rk_compl; trivial.
Qed.

Hypothesis EM : forall P, P \/ ~P.

Lemma rk_total : forall x y, rk x ∈ rk y \/ rk y ⊆ rk x.
intros x y.
revert x.
pattern y; apply wf_ax; trivial; clear y; intros y Hy x.
destruct (EM (exists y', y' ∈ rk y /\ rk x ⊆ y')).
 left.
 destruct H; destruct H.
 apply rk_sub with x0; trivial.

 right; red; intros.
 rewrite rk_def in H0; destruct H0; destruct H0.
 assert (exists w, w ∈ rk x /\ ~ w ∈ rk x0).
  destruct (EM (exists w, w ∈ rk x /\ ~ w ∈ rk x0)); trivial.
  assert (~ rk x ⊆ rk x0).
   red; intros; apply H.
   exists (rk x0); split; trivial.
   apply rk_mono; trivial.
  elim H3; red; intros.
  destruct (EM (z0 ∈ rk x0)); trivial.
  elim H2.
  exists z0; split; trivial.
 destruct H2; destruct H2.
 destruct (Hy _ H0 x1).
  elim H3.
  apply rk_sub with (rk x1); trivial.
  red; rewrite <- power_ax; apply rk_intro.
  apply rk_sub with (rk x1).
   apply rk_compl; trivial.

   rewrite power_ax in H1; red; auto.
Qed.

Definition lst_rk (P:set->Prop) (y:set) :=
  P y /\
  (exists w, y == rk w) /\
  (forall x, (exists w, x == rk w) -> P x -> y ⊆ rk x).

Instance lst_rk_morph : Proper ((eq_set ==> iff) ==> eq_set ==> iff) lst_rk.
apply morph_impl_iff2; auto with *.
do 4 red; intros.
destruct H1 as (?,(?,?)).
split;[|split].
 apply (H _ _ H0); trivial.

 destruct H2.
 exists x1.
 rewrite <- H0; trivial.

 intros.
 rewrite <- H0.
 apply H3; trivial.
 apply (H x1 x1); trivial; reflexivity.
Qed.

Lemma lst_incl : forall P y, lst_rk P y -> P y. 
destruct 1.
trivial.
Qed.

Lemma lst_fun : forall P y y', lst_rk P y -> lst_rk P y' -> y == y'.
destruct 1; destruct 1.
destruct H0; destruct H2.
apply H3 in H1; trivial; apply H4 in H; trivial.
clear H3 H4.
apply eq_intro; intros.
 apply H1 in H3.
 destruct H2.
 rewrite H2 in H3|-*.
 rewrite rk_idem in H3; trivial.

 apply H in H3.
 destruct H0.
 rewrite H0 in H3|-*.
 rewrite rk_idem in H3; trivial.
Qed.

Lemma lst_ex : forall P, Proper (eq_set ==> impl) P ->
  (exists x, P (rk x)) -> exists y, lst_rk P y.
intros P Pm.
destruct 1.
revert H.
pattern x; apply rk_induc; clear x; intros.
destruct (EM (exists z, z ∈ rk x /\ P (rk z))).
 destruct H1.
 destruct H1; eauto.

 exists (rk x).
 split; [|split]; trivial.
  exists x; reflexivity.

  red; intros.
  destruct (rk_total x0 x); auto.
  elim H1.
  destruct H2.
  exists x0; split.
   apply rk_sub with (rk x0); trivial.
   red; rewrite <- power_ax; apply rk_intro.

   apply Pm with x0; trivial.
   rewrite H2; rewrite rk_idem; reflexivity.
Qed.

Lemma repl_coll_ubnd :
  (forall A R, rep_ubnd A R) -> (forall A R, coll_ubnd A R).
red; intros.
pose (P := fun x y => exists z, z ∈ y /\ R x z).
assert (Pm : Proper (eq_set ==> eq_set ==> impl) P).
 do 4 red; intros.
 destruct H4.
 exists x1.
 rewrite <- H2; rewrite <- H3; trivial.
assert (Pwit : forall x, exists y, P x (rk y)). 
 intros.
 destruct (H1 x).
 exists (singl x0); exists x0; split; trivial.
 rewrite <- rk_pow; apply rk_intro.
destruct (@H A (fun x y => lst_rk (P x) y)); simpl; eauto using lst_fun, lst_ex.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 apply lst_rk_morph with (P x) x0; auto with *.
 red; intros.
 apply morph_impl_iff2 with (3:=Pm); auto with *.

 intros.
 apply lst_ex; trivial.
 apply Pm; reflexivity.

 exists (union x); intros.
 destruct lst_ex with (P x0); auto.
  apply Pm; reflexivity.

  specialize lst_incl with (1:=H4).
  destruct 1.
  destruct H5.
  exists x2; split; trivial.
  rewrite union_ax.
  exists x1; trivial.
  rewrite H2.
  exists x0; auto.
Qed.


Lemma repl_coll_bnd :
  (forall A R, rep_bnd A R) -> (forall A R, coll_bnd A R).
red; intros.
pose (P := fun x y => exists z, z ∈ y /\ R x z).
assert (Pm : Proper (eq_set ==> eq_set ==> impl) P).
 do 4 red; intros.
 destruct H4.
 exists x1.
 rewrite <- H2; rewrite <- H3; trivial.
assert (Pwit : forall x, x ∈ A -> exists y, P x (rk y)). 
 intros.
 destruct (H1 x H2).
 exists (singl x0); exists x0; split; trivial.
 rewrite <- rk_pow; apply rk_intro.
destruct (@H A (fun x y => lst_rk (P x) y)); simpl; eauto using lst_fun, lst_ex.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 apply lst_rk_morph with (P x) x0; auto with *.
 red; intros.
 apply morph_impl_iff2 with (3:=Pm); auto with *.

 intros.
 apply lst_ex; auto.
 apply Pm; reflexivity.

 exists (union x); intros.
 destruct lst_ex with (P x0); auto.
  apply Pm; reflexivity.

  specialize lst_incl with (1:=H4).
  destruct 1.
  destruct H5.
  exists x2; split; trivial.
  rewrite union_ax.
  exists x1; trivial.
  rewrite H2.
  exists x0; auto.
Qed.

End ReplImpliesCollFromExcludedMiddleAndWellFoundation.

(** The usual statements found in the litterature. *)

Definition replacement := forall A R, rep_bnd A R.

Definition collection := forall A R, coll_ubnd A R.

