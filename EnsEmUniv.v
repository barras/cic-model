Require Import basic.
Require Import Sublogic.

(** In this file we show that Coq universes allows to build
   Grothendieck universes.
   We take two copies of the set type, and we embed the
   "big set" of all the "small sets" (that we call U),
   and we show that U is a Grothendieck universe.
 *)

Module BuildUniverse (L:SublogicTheory).

Import L.

Require EnsEm0.
Require EnsEm.
Module S := EnsEm0.Ensembles L. (* small sets *)
Module B := EnsEm.Ensembles L. (* big sets *)

Notation "x ∈ y" := (B.in_set x y) (at level 60).
Notation "x == y" := (B.eq_set x y) (at level 70).

(** This definition implies that the universe of indexes of small
   sets is lower than (or equal to) the universes of indexes of
   large sets (Ens0.Tlo <= Ens.Tlo)
 *)
Fixpoint injU (a:S.set) : B.set :=
  match a with
    S.sup X f => B.sup X (fun i => injU (f i))
  end.

Lemma lift_eq : forall x y, S.eq_set x y -> injU x == injU y.
intros.
revert x y H.
induction x; destruct y; simpl; intros.
destruct H0.
split; intros.
 Tdestruct (H0 i).
 Texists x.
 apply H; trivial.

 Tdestruct (H1 j).
 Texists x.
 apply H; trivial.
Qed.

Lemma down_eq : forall x y, injU x == injU y -> S.eq_set x y.
intros.
revert x y H.
induction x; destruct y; simpl; intros.
destruct H0.
split; intros.
 Tdestruct (H0 i).
 Texists x; auto.

 Tdestruct (H1 j).
 Texists x; auto.
Qed.

Lemma lift_in : forall x y, S.in_set x y -> injU x ∈ injU y.
destruct y; simpl; intros.
Tdestruct H; simpl in *.
apply lift_eq in H.
Texists x0.
assumption.
Qed.

Lemma down_in : forall x y, injU x ∈ injU y -> S.in_set x y.
destruct y; simpl; intros.
Tdestruct H.
simpl in H.
Texists x0.
apply down_eq; trivial.
Qed.

Lemma down_in_ex  x y y' :
  y == injU y' ->
  x ∈ y ->
  Tr(exists2 x', x == injU x' & S.in_set x' y').
intros.
specialize B.eq_elim with (1:=H0) (2:=H); intro.
Tdestruct H1.
destruct y' as (Y,f).
simpl in x0, H1.
Texists (f x0); trivial.
apply down_in.
apply B.eq_elim with y; trivial.
apply B.in_reg with x; trivial.
Qed.

(** Now the universe of small sets is lower than (or equal to)
   the universe of indexes of big sets (Ens0.Thi <= Ens.Tlo).
 *)
Definition U : B.set := B.sup S.set injU.

Lemma U_elim : forall x, x ∈ U -> Tr(exists x', x == injU x').
intros.
Tdestruct H.
Texists x0; trivial.
Qed.

Lemma U_intro : forall x, injU x ∈ U.
red; intros.
Texists x.
apply B.eq_set_refl.
Qed.

Lemma injU_elim : forall x y, x ∈ injU y -> x ∈ U.
destruct y; simpl; intros.
Tdestruct H.
Texists (f x0).
assumption.
Qed.

(** Equivalence of all set-theoretical constructions *)

Lemma pair_equiv : forall x y,
  B.pair (injU x) (injU y) == injU (S.pair x y).
intros.
unfold B.pair, S.pair; simpl.
split; intros.
 Texists i; destruct i; apply B.eq_set_refl.
 Texists j; destruct j; apply B.eq_set_refl.
Qed.

Lemma union_equiv : forall x, B.union (injU x) == injU (S.union x).
intros.
apply B.eq_intro; intros.
 apply B.union_ax in H.
 Tdestruct H.
 apply down_in_ex with (1:=B.eq_set_refl _) in H0.
 Tdestruct H0.
 apply down_in_ex with (1:=H0) in H; Tdestruct H.
 apply B.in_reg with (injU x2).
  apply B.eq_set_sym; trivial.
 apply lift_in.
 rewrite S.union_ax.
 Texists x1; trivial.

 rewrite B.union_ax.
 apply down_in_ex with (1:=B.eq_set_refl _) in H; Tdestruct H.
 rewrite S.union_ax in H0; Tdestruct H0.
 apply lift_in in H0.
 apply lift_in in H1.
 Texists (injU x1); trivial.
 apply B.in_reg with (injU x0); trivial.
 apply B.eq_set_sym; trivial.
Qed.

Lemma subset_equiv : forall x P Q,
  (forall x y, y == injU x -> (P x <-> Q y)) ->
  injU (S.subset x P) == B.subset (injU x) Q.
intros.
unfold S.subset, B.subset.
destruct x; simpl.
split; intros.
 destruct i as (i,spec); simpl in *.
 assert (Tr(exists2 x', injU (f i) == x' & Q x')).
  Tdestruct spec.
  Texists (injU x).
   apply lift_eq; trivial.
   rewrite <- (H x); trivial.
   apply B.eq_set_refl.
 Texists (B.mkSi (B.sup X (fun i => injU(f i))) _ i H0); simpl.
 apply B.eq_set_refl.

 destruct j as (j,h); simpl in j, h.
 assert (Tr(exists2 x', S.eq_set (f j) x' & P x')).
  Tdestruct h.
  Texists (f j).
   apply S.eq_set_refl.
   rewrite (H (f j) x); trivial.
   apply B.eq_set_sym; trivial.
 Texists (S.mkSi (S.sup X f) _ j H0); simpl.
 apply B.eq_set_refl.
Qed.

Lemma power_equiv : forall x, B.power (injU x) == injU (S.power x).
intros.
apply B.eq_intro; intros.
 rewrite B.power_ax in H.
 apply B.in_reg with (injU (S.subset x (fun x' => injU x' ∈ z))).
  apply B.eq_set_trans with (B.subset (injU x) (fun x' => x' ∈ z)).
   apply subset_equiv; intros.
   split; intros.
    apply B.in_reg with (injU x0); trivial.
    apply B.eq_set_sym; trivial.

    apply B.in_reg with y; trivial.

   apply B.eq_intro; intros.
    rewrite B.subset_ax in H0.
    destruct H0.
    Tdestruct H1.
    apply B.in_reg with x0; trivial.
    apply B.eq_set_sym; trivial.

    rewrite B.subset_ax.
    split; auto.
    Texists z0; trivial.
    apply B.eq_set_refl.

  apply lift_in.
  rewrite S.power_ax; intros.
  rewrite S.subset_ax in H0.
  destruct H0; trivial.

 rewrite B.power_ax; intros.
 specialize injU_elim with (1:=H); intro.
 apply U_elim in H1.
 Tdestruct H1.
 assert (y ∈ injU x0).
  apply B.eq_elim with z; trivial.
 specialize injU_elim with (1:=H2); intro. 
 apply U_elim in H3.
 Tdestruct H3.
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

Lemma repl1_equiv : forall x f a F,
  a == injU x ->
  (forall x x', proj1_sig x' == injU (proj1_sig x) -> F x' == injU (f x)) ->
  B.repl1 a F == injU (S.repl1 x f).
destruct x; intros.
destruct a as (A,g); simpl in H.
destruct H.
split; simpl; intros.
 Tdestruct (H i).
 Texists x; simpl.
 apply H0; simpl; trivial.

 Tdestruct (H1 j).
 Texists x; simpl.
 apply H0; simpl; trivial.
Qed.

(** Closure properties of U *)

Lemma U_trans : forall x y, y ∈ x -> x ∈ U -> y ∈ U.
intros.
apply U_elim in H0; Tdestruct H0.
assert (y ∈ injU x0).
 apply B.eq_elim with x; trivial.
apply injU_elim in H1; trivial.
Qed.

Lemma U_pair : forall x y, x ∈ U -> y ∈ U -> B.pair x y ∈ U.
intros.
apply U_elim in H; Tdestruct H.
apply U_elim in H0; Tdestruct H0.
apply B.in_reg with (injU (S.pair x0 x1)).
 apply B.eq_set_sym.
 apply B.eq_set_trans with (B.pair (injU x0) (injU x1)).
  apply B.pair_morph; trivial.

  apply pair_equiv.

 apply U_intro.
Qed.

Lemma U_power : forall x, x ∈ U -> B.power x ∈ U.
intros.
apply U_elim in H; Tdestruct H.
apply B.in_reg with (injU (S.power x0)).
 apply B.eq_set_sym.
 apply B.eq_set_trans with (B.power (injU x0)).
  apply B.power_morph; trivial.

  apply power_equiv.

 apply U_intro.
Qed.

Lemma U_union : forall x, x ∈ U -> B.union x ∈ U.
intros.
apply U_elim in H; Tdestruct H.
apply B.in_reg with (injU (S.union x0)).
 apply B.eq_set_sym.
 apply B.eq_set_trans with (B.union (injU x0)).
  apply B.union_morph; trivial.

  apply union_equiv.

 apply U_intro.
Qed.


Axiom intuit : forall P, Tr P -> P.

Lemma U_repl : forall a R,
  Proper (B.eq_set==>B.eq_set==>iff) R ->
  a ∈ U ->
  (forall x y y', x ∈ a -> y ∈ U -> y' ∈ U ->
   R x y -> R x y' -> y == y') ->
  Tr(exists2 b, b ∈ U & forall y, y ∈ U ->
                         (y ∈ b <-> Tr(exists2 x, x ∈ a & R x y))).
intros.
apply U_elim in H0; Tdestruct H0.
(* replacement on small sets *)
refine (let (b,Hb) := S.intuit_repl_ax intuit 
          x (fun x y => R (injU x) (injU y)) _ _ in _).
 intros.
 revert H5; apply iff_impl; apply H; apply lift_eq; trivial.

 intros.
 apply down_eq.
 apply H1 with (injU x0); trivial.
  apply B.eq_set_sym in H0.
  apply B.eq_elim with (injU x); trivial.
  apply lift_in; trivial.

  apply U_intro.

  apply U_intro.

 Texists (injU b).
  apply U_intro.

  split; intros. 
   apply U_elim in H2; Tdestruct H2.
   generalize (B.in_reg _ _ _ H2 H3); intro.
   apply down_in in H4.
   rewrite Hb in H4.
   Tdestruct H4.
   Texists (injU x1); trivial.
    apply lift_in in H4.
    apply B.eq_set_sym in H0.
    apply B.eq_elim with (injU x); trivial.

    revert H5; apply iff_impl; apply H; trivial.
    apply B.eq_set_refl.
    apply B.eq_set_sym; trivial.

  Tdestruct H3.
  specialize B.eq_elim with (1:=H3) (2:=H0); intro.
  specialize injU_elim with (1:=H5); intro.
  apply U_elim in H6; Tdestruct H6.
  generalize (B.in_reg _ _ _ H6 H5); intro.
  apply down_in in H7.
  apply U_elim in H2; Tdestruct H2.
  apply B.eq_set_sym in H2.
  apply B.in_reg with (injU x2); trivial.
  apply lift_in.
  rewrite Hb.
  Texists x1; trivial.
  revert H4; apply iff_impl; apply H; trivial.
  apply B.eq_set_sym; trivial.
Qed.

(* If the small sets are closed under collection, then so
   is U. *)
Lemma U_coll : forall a R,
  Proper (B.eq_set==>B.eq_set==>iff) R ->
  a ∈ U ->
  (forall x, x ∈ a -> Tr(exists2 y, y ∈ U & R x y)) ->
  Tr(exists2 b, b ∈ U & forall x, x ∈ a -> Tr(exists2 y, y ∈ b & R x y)).
intros.
apply U_elim in H0; Tdestruct H0 as (a',?).
(* We use collection on small sets *)
destruct S.collection_ax with a' (fun x y => R (injU x) (injU y)) as (B,HB).
 do 3 red; intros.
 apply H; apply lift_eq; trivial.

 Texists (injU B).
  apply U_intro.
 intros.
 Tdestruct (H1 _ H2).
 apply down_in_ex with (1:=H0) in H2.
 Tdestruct H2.
 refine (let h := HB _ H5 _ in _).
  apply U_elim in H3; Tdestruct H3.
  Texists x2.
  revert H4; apply H; apply B.eq_set_sym; trivial.
 Tdestruct h.
 Texists (injU x2).
  apply lift_in; trivial.

  revert H7; apply H; trivial.
  apply B.eq_set_refl.
Qed.

(** Grothendieck universe *)
Record grot_univ (U:B.set) : Prop := {
  G_trans : forall x y, y ∈ x -> x ∈ U -> y ∈ U;
  G_pair : forall x y, x ∈ U -> y ∈ U -> B.pair x y ∈ U;
  G_power : forall x, x ∈ U -> B.power x ∈ U;
  G_union : forall x, x ∈ U -> B.union x ∈ U;
  G_repl : forall a R, Proper (B.eq_set==>B.eq_set==>iff) R ->
           a ∈ U ->
           (forall x y y', x ∈ a -> y ∈ U -> y' ∈ U -> R x y -> R x y' -> y == y') ->
           Tr(exists2 b, b ∈ U & forall y, y ∈ U -> (y ∈ b <-> Tr(exists2 x, x ∈ a & R x y))) }.

Lemma U_univ : grot_univ U.
constructor.
 apply U_trans.
 apply U_pair.
 apply U_power.
 apply U_union.
 apply U_repl.
Qed.

(** Weak Grothendieck universe: closure only under
   *functional* replacement. We still need relational replacement.
 *)
Record grot_univ1 (U:B.set) : Prop := {
  G_trans1 : forall x y, y ∈ x -> x ∈ U -> y ∈ U;
  G_pair1 : forall x y, x ∈ U -> y ∈ U -> B.pair x y ∈ U;
  G_power1 : forall x, x ∈ U -> B.power x ∈ U;
  G_union_repl1 : forall I F,
                 (forall x x', proj1_sig x == proj1_sig x' -> F x == F x') ->
                 I ∈ U ->
                 (forall x, F x ∈ U) ->
                 B.union (B.repl1 I F) ∈ U }.

Lemma U_univ1 : grot_univ1 U.
constructor.
 apply U_trans.
 apply U_pair.
 apply U_power.

 intros.
 apply U_elim in H0; Tdestruct H0.
 assert (forall z, S.in_set z x -> injU z ∈ I).
  intros.
  apply B.eq_set_sym in H0.
  apply B.eq_elim with (injU x); trivial.
  apply lift_in; trivial.
 (* We have F producing big sets in U, and we need a function producing
    small sets to use functional replacement on small sets. We're stuck
    again. Relational replacement does it.
  *)
 destruct S.intuit_repl_ax with x
         (fun x' y => exists h:injU x' ∈ I, F (B.eli I _ h) == injU y)
   as (B,HB).
  exact intuit.

  intros.
  destruct H6.
  assert (injU x' ∈ I).  
   apply B.eq_elim with (injU x).
   2:apply B.eq_set_sym; trivial.
   apply lift_in.
   apply S.in_reg with x0; trivial.
  exists H7.
  apply lift_eq in H5.
  apply B.eq_set_trans with (2:=H5).
  apply B.eq_set_trans with (2:=H6).
  apply H; simpl.
  apply lift_eq; apply S.eq_set_sym; trivial.

  intros.
  destruct H4; destruct H5.
  apply down_eq.
  apply B.eq_set_trans with (1:=B.eq_set_sym _ _ H4).
  apply B.eq_set_trans with (2:=H5).
  apply H; simpl; apply B.eq_set_refl.

  apply B.in_reg with (injU (S.union B)).
  2:apply U_intro.
  apply B.eq_set_sym.
  apply B.eq_set_trans with (2:=union_equiv B).
  apply B.union_morph.
  apply B.eq_set_ax; split; intros.
   apply B.repl1_ax in H3; trivial.
   Tdestruct H3.
   Tdestruct (U_elim _ (H1 x0)).
   apply B.in_reg with (injU x1).
    apply B.eq_set_sym; apply B.eq_set_trans with (F x0); trivial.

    apply lift_in.
    rewrite HB.
    Tdestruct (down_in_ex _ _ _ H0 (proj2_sig x0)).
    Texists x2; trivial.
    exists (H2 _ H6).
    apply B.eq_set_trans with (2:=H4).
    apply H; simpl.
    apply B.eq_set_sym; trivial.

   apply down_in_ex with (1:=B.eq_set_refl _) in H3.
   Tdestruct H3.
   rewrite HB in H4; clear HB.
   Tdestruct H4.
   destruct H5.
   rewrite B.repl1_ax; trivial.
   Texists (B.eli I (injU x1) x2).
   apply B.eq_set_trans with (1:=H3).
   apply B.eq_set_sym; trivial.
Qed.

End BuildUniverse.