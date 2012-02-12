Require Export basic.
Require Import Choice. (* Axiom *)

(* In this file, we give an attempt to build a model of
   classical ZF in Coq.
 *)

Definition excl {A} (P:A->Prop) : Prop :=
  ~ forall x, ~ P x.

Lemma exI A (P:A->Prop) x : P x -> excl P.
do 2 red; intros.
apply (H0 x); trivial.
Qed.

Lemma exE A (P:A->Prop) (Q:Prop) :
  (~ ~ Q -> Q) ->
  (forall x, P x -> Q) ->
  excl P -> Q.
intros.
apply H; intro.
apply H1; red; intros.
eauto.
Qed.


Instance excl_morph A R :
   Reflexive R -> Proper ((R ==> iff) ==> iff) (@excl A).
intros.
split; intros.
 apply exE with (3:=H1); [firstorder|intros].
 apply exI with x0.
 revert H2; apply H0; reflexivity.

 apply exE with (3:=H1); [firstorder|intros].
 apply exI with x0.
 revert H2; apply H0; reflexivity.
Qed.


Definition orcl (P Q:Prop) : Prop := ~ (~P /\ ~Q).

Instance orcl_morph : Proper (iff ==> iff ==> iff) orcl.
firstorder.
Qed.

Lemma orI P Q : P \/ Q -> orcl P Q.
do 2 red; intros.
destruct H0; destruct H; auto.
Qed.

Lemma orE (P Q R:Prop) :
  (~ ~ R -> R) ->
  (P -> R) ->
  (Q -> R) ->
  orcl P Q -> R.
intros.
apply H; intro.
apply H2; auto.
Qed.

Module ZF.

Definition Thi := Type.
Definition Tlo : Thi := Type.
Inductive set_ : Thi :=
  sup (X:Tlo) (f:X->set_).
Definition set := set_.

Definition idx (x:set) := let (X,_) := x in X.
Definition elts (x:set) : idx x -> set :=
  match x return idx x -> set with
  | sup X f => f
  end.

Fixpoint eq_set (x y:set) {struct x} :=
  (forall i, excl(fun j => eq_set (elts x i) (elts y j))) /\
  (forall j, excl(fun i => eq_set (elts x i) (elts y j))).

Lemma eq_set_refl : forall x, eq_set x x.
induction x; simpl.
split; intros.
 apply exI with i; trivial.
 apply exI with j; trivial.
Qed.

Lemma eq_set_sym : forall x y, eq_set x y -> eq_set y x.
induction x; destruct y; simpl; intros.
destruct H0.
split; intros.
 apply exE with (3:=H1 i).
  firstorder.
 intros.
 apply exI with x; auto.

 apply exE with (3:=H0 j).
  firstorder.
 intros.
 apply exI with x; auto.
Qed.

Lemma eq_set_trans : forall x y z,
  eq_set x y -> eq_set y z -> eq_set x z.
induction x; destruct y; destruct z; simpl; intros.
destruct H0.
destruct H1.
split; intros.
 apply exE with (3:=H0 i); intros.
  firstorder.
 apply exE with (3:=H1 x); intros.
  firstorder.
 apply exI with x0; eauto.

 apply exE with (3:=H3 j); intros.
  firstorder.
 apply exE with (3:=H2 x); intros.
  firstorder.
 apply exI with x0; eauto.
Qed.

Lemma eq_set_cl x y : ~ ~ eq_set x y -> eq_set x y.
destruct x; simpl; intros.
split; do 2 red; intros; firstorder.
Qed.

Definition in_set x y :=
  excl (fun j => eq_set x (elts y j)).

Notation "x \in y" := (in_set x y) (at level 60).
Notation "x == y" := (eq_set x y) (at level 70).

Definition incl_set x y := forall z, in_set z x -> in_set z y.

Lemma eq_elim0 : forall x y i,
  eq_set x y -> excl (fun j => eq_set (elts x i) (elts y j)).
destruct x; simpl; intros.
destruct H.
auto.
Qed.

Lemma eq_set_ax : forall x y,
  eq_set x y <-> (forall z, in_set z x <-> in_set z y).
unfold in_set; split; intros.
 split; intros.
  apply exE with (3:=H0); intros.
   firstorder.
  apply exE with (3:=eq_elim0 x y x0 H); intros.
   firstorder.
  apply exI with x1.
  apply eq_set_trans with (elts x x0); trivial.

  apply exE with (3:=H0); intros.
   firstorder.
  apply eq_set_sym in H.
  apply (eq_elim0 y x x0) in H.
  apply exE with (3:=H); intros.
   firstorder.
  apply exI with x1.
  apply eq_set_trans with (elts y x0); trivial.

 destruct x; simpl in *.
 destruct y; simpl in *.
 split; intros.
  destruct (H (f i)).
  apply H0; trivial.
  apply exI with i.
  apply eq_set_refl.

  destruct (H (f0 j)).
  lapply H1; intros.
   apply exE with (3:=H2); intros.
    firstorder.
   apply exI with x.
   apply eq_set_sym; trivial.

   apply exI with j.
   apply eq_set_refl.
Qed.

Definition elts' (x:set) (i:idx x) : {y|in_set y x}.
exists (elts x i).
abstract (apply exI with i; apply eq_set_refl).
Defined.

Lemma in_reg : forall x x' y,
  eq_set x x' -> in_set x y -> in_set x' y.
intros.
apply exE with (3:=H0); intros.
 firstorder.
apply exI with x0.
apply eq_set_trans with x; trivial.
apply eq_set_sym; trivial.
Qed.

Lemma eq_intro : forall x y,
  (forall z, in_set z x -> in_set z y) ->
  (forall z, in_set z y -> in_set z x) ->
  eq_set x y.
intros.
rewrite eq_set_ax.
split; intros; eauto.
Qed.

Lemma eq_elim : forall x y y',
  in_set x y ->
  eq_set y y' ->
  in_set x y'.
intros.
rewrite eq_set_ax in H0.
destruct (H0 x); auto.
Qed.

(* Set induction *)

Lemma wf_ax :
  forall (P:set->Prop),
  (forall x, ~ ~ P x -> P x) -> (* P is classical *)
  (forall x, (forall y, in_set y x -> P y) -> P x) -> forall x, P x.
intros P Pcl H x.
cut (forall x', eq_set x x' -> P x');[auto using eq_set_refl|].
induction x; intros.
apply H; intros.
assert (in_set y (sup X f)).
 apply eq_elim with x'; trivial.
 apply eq_set_sym; trivial.
clear H1 H2.
apply exE with (3:=H3); intros; auto.
simpl in H1.
apply eq_set_sym in H1; eauto.
Qed.

(* *)

Definition empty :=
  sup False (fun x => match x with end).

Lemma empty_ax : forall x, ~ in_set x empty.
unfold in_set, empty; simpl.
red; intros.
apply H.
destruct x0.
Qed.

Definition singl x := sup unit (fun _ => x).

Definition pair x y :=
  sup bool (fun b => if b then x else y).

Lemma pair_ax : forall a b z,
  in_set z (pair a b) <-> orcl (eq_set z a) (eq_set z b).
unfold in_set, pair; simpl.
split; intros.
 apply exE with (3:=H); intros.
  firstorder.
 apply orI.
 destruct x; auto.

 apply orE with (4:=H); intros.
  firstorder.
  apply exI with true; trivial.
  apply exI with false; trivial.
Qed.

Lemma pair_morph :
  forall a a', eq_set a a' -> forall b b', eq_set b b' ->
  eq_set (pair a b) (pair a' b').
intros.
rewrite eq_set_ax; intros.
do 2 rewrite pair_ax.
split; intros.
 apply orE with (4:=H1); intros.
  firstorder.
  apply orI; left; apply eq_set_trans with a; trivial.
  apply orI; right; apply eq_set_trans with b; trivial.

 apply eq_set_sym in H.
 apply eq_set_sym in H0.
 apply orE with (4:=H1); intros.
  firstorder.
  apply orI; left; apply eq_set_trans with a'; trivial.
  apply orI; right; apply eq_set_trans with b'; trivial.
Qed.

Definition union (x:set) :=
  sup {i:idx x & idx (elts x i)}
    (fun p => elts (elts x (projS1 p)) (projS2 p)).

Lemma union_ax : forall a z,
  in_set z (union a) <-> excl(fun b => in_set z b /\ in_set b a).
unfold in_set at 1, union; simpl; intros.
split; intros.
 apply exE with (3:=H);[firstorder|intros].
 destruct x; simpl in *.
 apply exI with (elts a x); split.
  apply exI with i; trivial.

  apply exI with x; apply eq_set_refl.

 apply exE with (3:=H);[firstorder|intros].
 destruct H0.
 apply exE with (3:=H1);[firstorder|intros].
 specialize eq_elim with (1:=H0) (2:=H2); intro.
 apply exE with (3:=H3);[firstorder|intros].
 apply exI with (existT _ x0 x1); simpl; trivial.
Qed.

Lemma union_morph :
  forall a a', eq_set a a' -> eq_set (union a) (union a').
intros.
rewrite eq_set_ax; intros.
rewrite union_ax; rewrite union_ax.
split; intros.
 apply exE with (3:=H0);[firstorder|intros].
 destruct H1.
 apply exI with x; split; trivial.
 apply eq_elim with a; trivial.

 apply eq_set_sym in H.
 apply exE with (3:=H0);[firstorder|intros].
 destruct H1.
 apply exI with x; split; trivial.
 apply eq_elim with a'; trivial.
Qed.

Definition subset (x:set) (P:set->Prop) :=
  sup {a|excl(fun x' => eq_set (elts x a) x' /\ P x')}
    (fun y => elts x (proj1_sig y)).

Lemma subset_ax : forall x P z,
  (in_set z (subset x P) <->
   in_set z x /\ excl(fun z' => eq_set z z' /\ P z')).
intros x P z.
unfold in_set at 1, subset; simpl.
split; intros.
 apply exE with (3:=H);[firstorder|intros].
 destruct x0; simpl in *.
 split.
  apply exI with x0; trivial.

  apply exE with (3:=e);[firstorder|intros].
  destruct H1.
  apply exI with x1; split; trivial.
  apply eq_set_trans with (elts x x0); trivial.

 destruct H.
 apply exE with (3:=H0);[firstorder|intros].
 destruct H1.
 apply exE with (3:=H);[firstorder|intros].
 assert (excl (fun x'=>eq_set (elts x x1) x'/\P x')).
  apply exI with x0; split; trivial.
  apply eq_set_trans with z; trivial.
  apply eq_set_sym; trivial.
 apply exI with (exist _ x1 H4); simpl; trivial.
Qed.

Definition power (x:set) :=
  sup (idx x->Prop)
   (fun P => subset x
         (fun y => excl(fun i =>  eq_set y (elts x i) /\ P i))).

Lemma power_ax : forall x z,
  in_set z (power x) <->
  (forall y, in_set y z -> in_set y x).
unfold in_set at 1, power; simpl; intros.
split; intros.
 apply exE with (3:=H);[firstorder|intros].
 specialize eq_elim with (1:=H0)(2:=H1); intro.
 rewrite subset_ax in H2.
 destruct H2; trivial.

 apply exI with (fun  i => in_set (elts x i) z).
 apply eq_intro; intros.
  rewrite subset_ax.
  split; auto.
  apply exI with z0; split;[apply eq_set_refl|].
  specialize H with (1:=H0).
  apply exE with (3:=H);[firstorder|intros].
  apply exI with x0; split; trivial.
  apply in_reg with z0; trivial.

  rewrite subset_ax in H0.
  destruct H0.
  apply exE with (3:=H1);[firstorder|intros].
  destruct H2.
  apply exE with (3:=H3);[firstorder|intros].
  destruct H4.
  apply in_reg with (elts x x1); trivial.
  apply eq_set_sym.
  apply eq_set_trans with x0; trivial.
Qed.

Lemma power_morph : forall x y,
  eq_set x y -> eq_set (power x) (power y).
intros.
apply eq_set_ax; intros.
do 2 rewrite power_ax.
split; intros.
 apply eq_elim with x; auto.

 apply eq_set_sym in H.
 apply eq_elim with y; auto.
Qed.


Fixpoint num (n:nat) : set :=
  match n with
  | 0 => empty
  | S k => union (pair (num k) (pair (num k) (num k)))
  end.

Definition infinity := sup _ num.

Lemma infty_ax1 : in_set empty infinity.
apply exI with 0.
apply eq_set_refl.
Qed.

Lemma infty_ax2 : forall x, in_set x infinity ->
  in_set (union (pair x (pair x x))) infinity.
intros.
apply exE with (3:=H);[firstorder|intros].
apply exI with (S x0); simpl elts.
apply union_morph.
apply pair_morph; trivial.
apply pair_morph; trivial.
Qed.

(* Replacement *)

Definition repl0 (x:set) (F:set->set) :=
  sup _ (fun i => F (elts x i)).

Lemma repl0_ax : forall x F z,
  (forall z z', in_set z x ->
   eq_set z z' -> eq_set (F z) (F z')) ->
  (in_set z (repl0 x F) <->
   excl (fun y => in_set y x /\ eq_set z (F y))).
unfold in_set at 2, repl0; simpl; intros.
split; intros.
 apply exE with (3:=H0);[firstorder|intros].
 apply exI with (elts x x0); split; trivial.
 apply exI with x0; apply eq_set_refl.

 apply exE with (3:=H0);[firstorder|intros].
 destruct H1.
 apply exE with (3:=H1);[firstorder|intros].
 apply exI with x1.
 apply eq_set_trans with (F x0); trivial.
 apply H; trivial.
Qed.

Definition repl1 (x:set) (F:{y|in_set y x}->set) :=
  sup _ (fun i => F (elts' x i)).

Lemma repl1_ax : forall x F z,
  (forall z z', eq_set (proj1_sig z) (proj1_sig z') ->
   eq_set (F z) (F z')) ->
  (in_set z (repl1 x F) <-> excl (fun y => eq_set z (F y))).
unfold in_set at 6, repl1; simpl; intros.
split; intros.
 apply exE with (3:=H0);[firstorder|intros].
 apply exI with (elts' x x0); trivial.

 apply exE with (3:=H0);[firstorder|intros].
 destruct x0.
 apply exE with (3:=i);[firstorder|intros].
 apply exI with x1.
 apply eq_set_trans with (1:=H1).
 apply H; trivial.
Qed.
 
Lemma repl1_morph : forall x y F G,
  eq_set x y ->
  (forall x' y', eq_set (proj1_sig x') (proj1_sig y') ->
   eq_set (F x') (G y')) ->
  eq_set (repl1 x F) (repl1 y G).
Admitted.
(*intros.
assert (forall z z', eq_set (proj1_sig z) (proj1_sig z') ->
        eq_set (F z) (F z')).
 intros.
 assert (in_set (proj1_sig z') y).
  apply eq_elim with x; trivial.
  apply (proj2_sig z').
 apply eq_set_trans with (G (exist _ (proj1_sig z') H2)).
  apply H0; simpl; trivial.

  apply eq_set_sym; apply H0; simpl; apply eq_set_refl.
assert (forall z z', eq_set (proj1_sig z) (proj1_sig z') ->
        eq_set (G z) (G z')).
 intros.
 apply eq_set_sym in H.
 assert (in_set (proj1_sig z') x).
  apply eq_elim with y; trivial.
  apply (proj2_sig z').
 apply eq_set_trans with (F (exist _ (proj1_sig z') H3)).
  apply eq_set_sym; apply H0; simpl; apply eq_set_sym; trivial.

  apply H0; simpl; apply eq_set_refl.
apply eq_intro; intros.
 rewrite repl1_ax in H3|-*; trivial.
 destruct H3.
 assert (in_set (proj1_sig x0) y).
  apply eq_elim with x; trivial.
  apply (proj2_sig x0).
 exists (exist (fun y' => in_set y' y) (proj1_sig x0) H4). (* regression of unification *)
(* exists (exist _ (proj1_sig x0) H4).*)
 apply eq_set_trans with (1:=H3).
 apply H0; simpl; apply eq_set_refl.

 rewrite repl1_ax in H3|-*; trivial.
 destruct H3.
 assert (in_set (proj1_sig x0) x).
  apply eq_set_sym in H.
  apply eq_elim with y; trivial.
  apply (proj2_sig x0).
 exists (exist (fun y0 => in_set y0 _) (proj1_sig x0) H4). (* unif regression *)
 apply eq_set_trans with (1:=H3).
 apply eq_set_sym; apply H0; simpl; apply eq_set_refl.
Qed.
*)

(* We only use the following instance of choice: *)
(*
Definition choice' := forall a:set, unique_choice {x|in_set x a} set eq_set.

Lemma choice'_axiom : choice'.
red; red; intros; apply choice_axiom; trivial.
Qed.
*)
Lemma choice_axiom_cl_bool :
  let A := bool in
  forall R,
  (forall x:A, excl (fun y:set => R x y)) ->
  excl (fun f => forall x, R x (f x)).
intros.
apply exE with (3:=H true);[firstorder|intros].
apply exE with (3:=H false);[firstorder|intros].
apply exI with (fun b:bool => if b then x else x0).
destruct x1; trivial.
Qed.
Lemma choice_axiom_cl_natb :
  let A := nat in
  forall R,
  (forall x:A, excl (fun y:set => R x y)) ->
  forall n,
  excl (fun f => forall x, x < n -> R x (f x)).
induction n; simpl; intros.
 apply exI with (fun _ => empty).
 intros.
 inversion H0.

 apply exE with (3:=IHn); [firstorder|intros].
 apply exE with (3:=H n); [firstorder|intros].
Require Import Peano_dec.
 apply exI with (fun k =>
   if eq_nat_dec k n then x0 else x k); intros.
 destruct (eq_nat_dec x1 n).
  subst x1; trivial.

  apply H0.
Require Import Omega.
  omega.
Qed.

Axiom choice_axiom_cl : forall A R,
  (forall x:A, excl (fun y:set => R x y)) ->
  excl (fun f => forall x, R x (f x)).

Lemma repl_ax:
    forall a (R:set->set->Prop),
    (forall x x' y y', in_set x a ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x y y', in_set x a -> R x y -> R x y' -> eq_set y y') ->
    excl (fun b => forall x, in_set x b <->
           excl (fun y => in_set y a /\ R y x)).
intros.
pose (a' := {x|in_set x (subset a (fun x => excl(fun y => R x y)))}).
lapply (choice_axiom_cl a' (fun p y => R (proj1_sig p) y)).
 intro.
 apply exE with (3:=H1);[firstorder|intros].
 apply exI with (repl1 _ x); intros.
 rewrite repl1_ax; fold a'.
  split; intros.
   apply exE with (3:=H3);[firstorder|intros].
   apply exI with (proj1_sig x1); split.
    generalize (proj2_sig x1).
    rewrite subset_ax.
    destruct 1; trivial.

    apply H with (4:=H2 x1).
     generalize (proj2_sig x1).
     rewrite subset_ax.
     destruct 1; trivial.

     apply eq_set_refl.

     apply eq_set_sym; trivial.

   apply exE with (3:=H3);[firstorder|intros].
   destruct H4.
   assert (in_set x1 (subset a (fun x' => excl(fun y => R x' y)))).
    rewrite subset_ax; split; trivial.
    apply exI with x1; split;[apply eq_set_refl|].
    apply exI with x0; trivial.
   apply exI with (exist _ x1 H6); simpl.
   apply H0 with x1; trivial.
   apply (H2 (exist _ x1 H6)).

  intros.
  apply H0 with (proj1_sig z); auto.
   generalize (proj2_sig z).
   rewrite subset_ax.
   destruct 1; trivial.

   apply H with (proj1_sig z') (x z'); trivial.
    generalize (proj2_sig z').
    rewrite subset_ax.
    destruct 1; trivial.

    apply eq_set_sym; trivial.

    apply eq_set_refl.

 intros.
 generalize (proj2_sig x).
 rewrite subset_ax.
 destruct 1.
 apply exE with (3:=H2);[firstorder|intros].
 destruct H3.
 apply exE with (3:=H4);[firstorder|intros].
 apply exI with x1.
 apply H with x0 x1; trivial.
  apply in_reg with (proj1_sig x); trivial.

  apply eq_set_sym; trivial.

  apply eq_set_refl.
Qed.

(* Collection *)

(* intuitionistic version *)

Lemma coll0 (X:Tlo) (R:X->set->Prop):
  exists Y, exists g:Y->set,
    forall i, (exists w, R i w) -> exists j:Y, R i (g j).
intros.
destruct (choice_axiom {i:X|exists w, R i w} set (fun i y => R (proj1_sig i) y)) as (f,Hf).
 apply proj2_sig.

 exists {i:X|exists w, R i w}.
 exists f.
 intros.
 exists (existT _ i H).
 apply (Hf (existT _ i H)).
Qed.

(*
Lemma coll10 A (R:set->set->Prop) :
  exists z, forall i, (exists w, R (elts A i) w) ->
            exists j, R (elts A i) (elts z j).
intros.
destruct (coll0 (idx A) (fun i y => R (elts A i) y)) as (Y,(g,Hg)).
exists (sup Y g).
exact Hg.
Qed.
*)

Lemma coll1 A (R:set->set->Prop) :
  exists z, forall i, (exists w, R (elts A i) w) ->
            exists j, R (elts A i) (elts z j).
intros.
destruct (choice_axiom {x':{x'|in_set x' A}| exists y, R (proj1_sig x') y} set
            (fun x y => R (proj1_sig (proj1_sig x)) y)) as (f,Hf).
 destruct x as ((x,?),?); simpl; trivial.

 pose (B:=sup {i:idx A|exists y, R (elts A i) y} (fun i =>
     f (exist _ (elts' A (proj1_sig i)) (proj2_sig i)))).
 exists B; intros i h.
 pose (y:=f(existT _ (elts' A i) h)).
 exists (existT _ i h : idx B); simpl.
 apply (Hf (existT _ (elts' A i) h)).
Qed.

Lemma collection_ax : forall A (R:set->set->Prop), 
    (forall x x' y y', in_set x A ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x, in_set x A -> excl(fun y => R x y)) ->
    exists B, forall x, in_set x A -> excl (fun y => in_set y B /\ R x y).
intros.
destruct coll1 with A R as (B,HB).
exists B; intros x inA.
apply exE with (3:=H0 _  inA); [firstorder|intros w Rxw].
apply exE with (3:=inA);[firstorder|intros i eqx].
assert (R (elts A i) w).
 apply H with (4:=Rxw); trivial.
 apply eq_set_refl.
destruct (HB i) as (j,Rxy).
 exists w; trivial.

 apply exI with (elts B j); split.
  apply (proj2_sig (elts' B j)).

  apply H with (4:=Rxy).
   apply in_reg with x; trivial.

   apply eq_set_sym; trivial.

   apply eq_set_refl.
Qed.

(* Deriving the existentially quantified sets *)

Lemma empty_ex: exists empty, forall x, ~ x \in empty.
exists empty.
exact empty_ax.
Qed.

Lemma pair_ex: forall a b, exists c, forall x, x \in c <-> ~ (~x == a /\ ~x == b).
intros.
exists (pair a b).
apply pair_ax.
Qed.

Lemma union_ex: forall a, exists b,
    forall x, x \in b <-> excl (fun y => x \in y /\ y \in a).
intros.
exists (union a).
apply union_ax.
Qed.

Lemma power_ex: forall a, exists b,
     forall x, x \in b <-> (forall y, y \in x -> y \in a).
intros.
exists (power a).
apply power_ax.
Qed.

(* Infinity *)

Lemma infinity_ex: exists2 infinite,
    (exists2 empty, (forall x, ~ x \in empty) & empty \in infinite) &
    (forall x, x \in infinite ->
     exists2 y, (forall z, z \in y <-> orcl (z == x) (z \in x)) &
       y \in infinite).
exists infinity.
 exists empty.
  exact empty_ax.
  exact infty_ax1.

 intros.
 exists (union (pair x (pair x x))); intros.
  rewrite union_ax.
  split; intros.
   apply exE with (3:=H0);[firstorder|intros].
   destruct H1.
   rewrite pair_ax in H2.
   apply orE with (4:=H2);[firstorder| |]; intros.
    apply orI; right; apply eq_elim with x0; trivial.

    specialize eq_elim with (1:=H1) (2:=H3); intro.
    rewrite pair_ax in H4.
    apply orE with (4:=H4);[firstorder| |]; intros; apply orI; auto.

   apply orE with (4:=H0);[firstorder| |]; intros.
    apply exI with (pair x x); split.
     rewrite pair_ax; apply orI; auto.

     rewrite pair_ax; apply orI; right; apply eq_set_refl.

    apply exI with x; split; trivial.
    rewrite pair_ax; apply orI; left; apply eq_set_refl.

  apply infty_ax2; trivial.
Qed.

End ZF.
