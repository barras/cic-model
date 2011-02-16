Require Import Setoid.

(* In this file we show that Coq universes allows to build
   Grothendieck universes.
   We take two copies of the set type, and we embed the
   "big set" of all the "small sets" (that we call U),
   and we show that U is a Grothendieck universe.
 *)

Require Ens0.
Require Ens.
Module S := Ens0.IZF. (* small sets *)
Module B := Ens.IZF. (* big sets *)

Fixpoint injU (a:S.set) : B.set :=
  match a with
    S.sup X f => B.sup X (fun i => injU (f i))
  end.

Definition U : B.set := B.sup S.set injU.

Notation "x \in y" := (B.in_set x y) (at level 60).
Notation "x == y" := (B.eq_set x y) (at level 70).

Lemma U_elim : forall x, x \in U -> exists x', x == injU x'.
destruct 1.
exists x0; trivial.
Qed.

Lemma U_intro : forall x, injU x \in U.
red; intros.
exists x.
apply B.eq_set_refl.
Qed.

Lemma injU_elim : forall x y, x \in injU y -> x \in U.
destruct y; destruct 1; simpl; intros.
exists (f x0).
assumption.
Qed.

Lemma lift_eq : forall x y, S.eq_set x y -> injU x == injU y.
intros.
revert x y H.
induction x; destruct y; simpl; intros.
destruct H0.
split; intros.
 elim H0 with i; intros.
 exists x.
 apply H; trivial.

 elim H1 with j; intros.
 exists x.
 apply H; trivial.
Qed.

Lemma down_eq : forall x y, injU x == injU y -> S.eq_set x y.
intros.
revert x y H.
induction x; destruct y; simpl; intros.
destruct H0.
split; intros.
 elim (H0 i); intros.
 exists x; auto.

 elim (H1 j); intros.
 exists x; auto.
Qed.

Lemma lift_in : forall x y, S.in_set x y -> injU x \in injU y.
destruct y; simpl; intros.
destruct H; simpl in *.
apply lift_eq in H.
exists x0.
assumption.
Qed.


Lemma down_in : forall x y, injU x \in injU y -> S.in_set x y.
destruct y; simpl; intros.
destruct H.
simpl injU in H.
exists x0.
apply down_eq; trivial.
Qed.

Lemma subset_equiv : forall x P Q,
  (forall x y, y == injU x -> (P x <-> Q y)) ->
  injU (S.subset x P) == B.subset (injU x) Q.
intros.
unfold S.subset, B.subset.
destruct x; simpl.
split; intros.
 destruct i; simpl.
 assert (exists2 x', injU (f x) == x' & Q x').
  destruct e.
  exists (injU x0).
   apply lift_eq; trivial.
   rewrite <- (H x0); trivial.
   apply B.eq_set_refl.
 exists (exist (fun a => exists2 x', injU (f a) == x' & Q x') x H0); simpl.
 apply B.eq_set_refl.

 destruct j; simpl.
 assert (exists2 x', S.eq_set (f x) x' & P x').
  destruct e.
  exists (f x).
   apply S.eq_set_refl.
   rewrite (H (f x) x0); trivial.
   apply B.eq_set_sym; trivial.
 exists (exist (fun a => exists2 x', S.eq_set (f a) x' & P x') x H0); simpl.
 apply B.eq_set_refl.
Qed.


Lemma power_equiv : forall x, B.power (injU x) == injU (S.power x).
intros.
apply B.eq_intro; intros.
 rewrite B.power_ax in H.
 apply B.in_reg with (injU (S.subset x (fun x' => injU x' \in z))).
  apply B.eq_set_trans with (B.subset (injU x) (fun x' => x' \in z)).
   apply subset_equiv; intros.
   split; intros.
    apply B.in_reg with (injU x0); trivial.
    apply B.eq_set_sym; trivial.

    apply B.in_reg with y; trivial.

   apply B.eq_intro; intros.
    rewrite B.subset_ax in H0.
    destruct H0.
    destruct H1.
    apply B.in_reg with x0; trivial.
    apply B.eq_set_sym; trivial.

    rewrite B.subset_ax.
    split; auto.
    exists z0; trivial.
    apply B.eq_set_refl.

  apply lift_in.
  rewrite S.power_ax; intros.
  rewrite S.subset_ax in H0.
  destruct H0; trivial.

 rewrite B.power_ax; intros.
 specialize injU_elim with (1:=H); intro.
 apply U_elim in H1.
 destruct H1.
 assert (y \in injU x0).
  apply B.eq_elim with z; trivial.
 specialize injU_elim with (1:=H2); intro. 
 apply U_elim in H3.
 destruct H3.
 apply B.in_reg with (injU x1).
  apply B.eq_set_sym; trivial.

  apply lift_in.
  assert (S.in_set x0 (S.power x)).
   apply down_in.
   apply B.in_reg with z; trivial.
  rewrite S.power_ax in H4.
  apply H4.
  apply down_in.
  apply B.in_reg with y; trivial.

Qed.

Lemma pair_equiv : forall x y,
  B.pair (injU x) (injU y) == injU (S.pair x y).
intros.
unfold B.pair, S.pair; simpl.
split; intros.
 exists i; destruct i; apply B.eq_set_refl.
 exists j; destruct j; apply B.eq_set_refl.
Qed.

Lemma union_equiv : forall x, B.union (injU x) == injU (S.union x).
intros.
apply B.eq_intro; intros.
 apply B.union_ax in H.
 destruct H.
 specialize injU_elim with (1:=H0); intros.
 apply U_elim in H1; destruct H1.
 assert (z \in injU x1).
  apply B.eq_elim with x0; trivial.
 specialize injU_elim with (1:=H2); intro.
 apply U_elim in H3; destruct H3.
 apply B.in_reg with (injU x2).
  apply B.eq_set_sym; trivial.
 apply lift_in.
 rewrite S.union_ax.
 exists x1.
  apply down_in.
  apply B.in_reg with z; trivial.

  apply down_in.
  apply B.in_reg with x0; trivial.

 rewrite B.union_ax.
 specialize injU_elim with (1:=H); intro.
 apply U_elim in H0; destruct H0.
 assert (S.in_set x0 (S.union x)).
  apply down_in.
  apply B.in_reg with z; trivial.
 rewrite S.union_ax in H1.
 destruct H1.
 exists (injU x1).
  apply B.in_reg with (injU x0).
   apply B.eq_set_sym; trivial.
   apply lift_in; trivial.

  apply lift_in; trivial.
Qed.

Lemma repl1_equiv : forall x f a F,
  a == injU x ->
  (forall x x', proj1_sig x' == injU (proj1_sig x) -> F x' == injU (f x)) ->
  B.repl1 a F == injU (S.repl1 x f).
destruct x; intros.
destruct a as (A,g); simpl in H.
destruct H.
split; simpl; intros.
 elim (H i); intros.
 exists x; simpl.
 apply H0; simpl; trivial.

 elim (H1 j); intros.
 exists x; simpl.
 apply H0; simpl; trivial.
Qed.


Record grot_univ (U:B.set) : Prop := {
  G_trans : forall x y, y \in x -> x \in U -> y \in U;
  G_pair : forall x y, x \in U -> y \in U -> B.pair x y \in U;
  G_power : forall x, x \in U -> B.power x \in U;
  G_union_repl : forall I F,
                 (forall x x', proj1_sig x == proj1_sig x' -> F x == F x') ->
                 I \in U ->
                 (forall x, F x \in U) ->
                 B.union (B.repl1 I F) \in U }.

Lemma U_univ : grot_univ U.
split; intros.
 apply U_elim in H0; destruct H0.
 assert (y \in injU x0).
  apply B.eq_elim with x; trivial.
 apply injU_elim in H1; trivial.

 apply U_elim in H; destruct H.
 apply U_elim in H0; destruct H0.
 apply B.in_reg with (injU (S.pair x0 x1)).
  apply B.eq_set_sym.
  apply B.eq_set_trans with (B.pair (injU x0) (injU x1)).
   apply B.pair_morph; trivial.

   apply pair_equiv.

  apply U_intro.

 apply U_elim in H; destruct H.
 apply B.in_reg with (injU (S.power x0)).
  apply B.eq_set_sym.
  apply B.eq_set_trans with (B.power (injU x0)).
   apply B.power_morph; trivial.

   apply power_equiv.

  apply U_intro.

 apply U_elim in H0; destruct H0.
 assert (forall z, S.in_set z x -> injU z \in I).
  intros.
  apply B.eq_set_sym in H0.
  apply B.eq_elim with (injU x); trivial.
  apply lift_in; trivial.
 (* Here again we need choice *)
 elim (S.choice'_axiom {p|S.in_set p x}
         (fun p y =>
          B.eq_set (F (exist _ (injU(proj1_sig p)) (H2 _ (proj2_sig p)))) (injU y)));
   intros.
  apply B.in_reg with (injU (S.union (S.repl1 x x0))).
   apply B.eq_set_sym.
   apply B.eq_set_trans with (B.union (injU (S.repl1 x x0))).
    apply B.union_morph.
    apply repl1_equiv; trivial; intros.
    apply B.eq_set_trans with (2:=H3 x1).
    apply H; simpl; trivial.

    apply union_equiv.

   apply U_intro.

  apply U_elim.
  apply H1.

  apply down_eq.
  apply B.eq_set_trans with (2:=H4).
  apply B.eq_set_sym; trivial.
Qed.

(* Closure of U under repl is easy (and requires no extra usage of
   the choice axiom)
 *)