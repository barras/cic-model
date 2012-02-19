Require Export basic.
Require Import Choice. (* Axiom *)
Require Import Logics.

(* In this file, we build a model of classical ZF
   in Coq extended with the Type-Theoretical Collection
   Axiom (TTColl).
 *)

Module Ensembles (L:LogicSig).

Import L.
Notation "P /\ Q" := (And P Q).
Definition Iff P Q := Imp P Q /\ Imp Q P.
Lemma holdsIff P Q :
  holds (Iff P Q) <-> (holds P <-> holds Q).
unfold Iff; rewrite rAnd.
do 2 rewrite rImp.
tauto.
Qed.
Notation "P <-> Q" := (Iff P Q).

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
  Forall(fun i => Exist(fun j => eq_set (elts x i) (elts y j))) /\
  Forall(fun j => Exist(fun i => eq_set (elts x i) (elts y j))).

Lemma eq_set_def x y :
  holds (eq_set x y) <->
  (forall i, holds (Exist (fun j => eq_set (elts x i) (elts y j)))) /\
  (forall j, holds (Exist (fun i => eq_set (elts x i) (elts y j)))).
destruct x; destruct y; simpl; intros.
rewrite rAnd.
do 2 rewrite rForall.
reflexivity.
Qed.

Lemma eq_set_intro x y :
  (forall i, exists j, holds (eq_set (elts x i) (elts y j))) ->
  (forall j, exists i, holds (eq_set (elts x i) (elts y j))) ->
  holds (eq_set x y).
intros.
rewrite eq_set_def; split; intros; apply rExI; auto.
Qed.

Lemma eq_set_refl : forall x, holds (eq_set x x).
induction x.
apply eq_set_intro; simpl; intros i; exists i; trivial.
Qed.

Lemma eq_set_sym : forall x y,
  holds (eq_set x y) -> holds (eq_set y x).
induction x; intros.
rewrite eq_set_def in H0|-*.
destruct H0; split; intros i.
 apply rExE with (2:=H1 i); intros.
 apply rExI; exists x; auto.

 apply rExE with (2:=H0 i); intros.
 apply rExI; exists x; auto.
Qed.

Lemma eq_set_trans : forall x y z,
  holds (eq_set x y) -> holds (eq_set y z) -> holds (eq_set x z).
induction x; destruct y; destruct z; intros.
rewrite eq_set_def in H0,H1|-*.
destruct H0; destruct H1; split; intros i.
 apply rExE with (2:=H0 i); intros.
 apply rExE with (2:=H1 x); intros.
 apply rExI; exists x0; eauto.

 apply rExE with (2:=H3 i); intros.
 apply rExE with (2:=H2 x); intros.
 apply rExI; exists x0; eauto.
Qed.

Definition in_set x y :=
  Exist(fun j => eq_set x (elts y j)).

Notation "x \in y" := (holds(in_set x y)) (at level 60).
Notation "x == y" := (holds (eq_set x y)) (at level 70).

Lemma eq_elim0 : forall x y i,
  x == y -> holds(Exist(fun j => eq_set (elts x i) (elts y j))).
intros.
rewrite eq_set_def in H; destruct H; auto.
Qed.

Lemma eq_set_ax : forall x y,
  x == y <-> (forall z, z \in x <-> z \in y).
intros.
rewrite eq_set_def.
split; intros.
 destruct H; split; intros.
  apply rExE with (2:=H1); intros.
  apply rExE with (2:=H x0); intros.
  apply rExI; exists x1.
  apply eq_set_trans with (elts x x0); trivial.

  apply rExE with (2:=H1); intros.
  apply rExE with (2:=H0 x0); intros.
  apply rExI; exists x1.
  apply eq_set_trans with (elts y x0); trivial.
  apply eq_set_sym; trivial.

 split; intros.
  apply H.
  apply rExI; exists i; apply eq_set_refl.

  assert (elts y j \in y).
   apply rExI; exists j; apply eq_set_refl.
  apply H in H0.
  apply rExE with (2:=H0); intros.
  apply rExI; exists x0.
  apply eq_set_sym; trivial.
Qed.

Definition elts' (x:set) (i:idx x) : {y|y \in x}.
exists (elts x i).
abstract (apply rExI; exists i; apply eq_set_refl).
Defined.

Lemma in_reg : forall x x' y,
  x == x' -> x \in y -> x' \in y.
intros.
apply rExE with (2:=H0); intros.
apply rExI; exists x0.
apply eq_set_trans with x; trivial.
apply eq_set_sym; trivial.
Qed.

Lemma eq_intro : forall x y,
  (forall z, z \in x -> z \in y) ->
  (forall z, z \in y -> z \in x) ->
  x == y.
intros.
rewrite eq_set_ax.
split; intros; eauto.
Qed.

Lemma eq_elim : forall x y y',
  x \in y ->
  y == y' ->
  x \in y'.
intros.
rewrite eq_set_ax in H0.
destruct (H0 x); auto.
Qed.

(* Set induction *)

Lemma wf_ax :
  forall (P:set->prop),
  (forall x, (forall y, y \in x -> holds (P y)) -> holds (P x)) ->
  forall x, holds (P x).
intros P H x.
cut (forall x', x == x' -> holds (P x'));[auto using eq_set_refl|].
induction x; intros.
apply H; intros.
apply eq_set_sym in H1.
apply eq_elim with (2:=H1) in H2.
apply rExE with (2:=H2); intros.
apply H0 with x.
apply eq_set_sym; trivial.
Qed.

(* *)

Definition empty :=
  sup False (fun x => match x with end).

Lemma empty_ax : forall x, ~ x \in empty.
red; intros.
apply rFF.
apply rExE with (2:=H); intros.
contradiction.
Qed.

Definition singl x := sup unit (fun _ => x).

Definition pair x y :=
  sup bool (fun b => if b then x else y).

Lemma pair_ax : forall a b z,
  z \in pair a b <-> holds (Or (eq_set z a) (eq_set z b)).
split; intros.
 apply rExE with (2:=H); intros.
 apply rOrI.
 destruct x; auto.

 apply rOrE with (2:=H); intros.
 destruct H0.
  apply rExI; exists true; trivial.
  apply rExI; exists false; trivial.
Qed.

Lemma pair_morph :
  forall a a', a == a' -> forall b b', b == b' ->
  pair a b == pair a' b'.
intros.
rewrite eq_set_ax; intros.
do 2 rewrite pair_ax.
split; intros.
 apply rOrE with (2:=H1); destruct 1; intros.
  apply rOrI; left; apply eq_set_trans with a; trivial.
  apply rOrI; right; apply eq_set_trans with b; trivial.

 apply eq_set_sym in H.
 apply eq_set_sym in H0.
 apply rOrE with (2:=H1); destruct 1; intros.
  apply rOrI; left; apply eq_set_trans with a'; trivial.
  apply rOrI; right; apply eq_set_trans with b'; trivial.
Qed.

Definition union (x:set) :=
  sup {i:idx x & idx (elts x i)}
    (fun p => elts (elts x (projS1 p)) (projS2 p)).

Lemma union_ax : forall a z,
  z \in union a <-> holds (Exist(fun b => in_set z b /\ in_set b a)).
split; intros.
 apply rExE with (2:=H); intros.
 destruct x; simpl in *.
 apply rExI; exists (elts a x); rewrite rAnd; split.
  apply rExI; exists i; trivial.

  apply rExI; exists x; apply eq_set_refl.

 apply rExE with (2:=H); intros.
 rewrite rAnd in H0; destruct H0.
 apply rExE with (2:=H1); intros.
 specialize eq_elim with (1:=H0) (2:=H2); intro.
 apply rExE with (2:=H3); intros.
 apply rExI; exists (existT _ x0 x1); simpl; trivial.
Qed.

Lemma union_morph :
  forall a a', a == a' -> union a == union a'.
intros.
rewrite eq_set_ax; intros.
rewrite union_ax; rewrite union_ax.
split; intros.
 apply rExE with (2:=H0); intros.
 rewrite rAnd in H1; destruct H1.
 apply rExI; exists x; rewrite rAnd; split; trivial.
 apply eq_elim with a; trivial.

 apply eq_set_sym in H.
 apply rExE with (2:=H0); intros.
 rewrite rAnd in H1; destruct H1.
 apply rExI; exists x; rewrite rAnd; split; trivial.
 apply eq_elim with a'; trivial.
Qed.

Definition subset (x:set) (P:set->prop) :=
  sup {a|holds(Exist(fun x' => eq_set (elts x a) x' /\ P x'))}
    (fun y => elts x (proj1_sig y)).

Lemma subset_ax : forall x P z,
  z \in subset x P <->
  z \in x /\ holds(Exist(fun z' => eq_set z z' /\ P z')).
intros x P z.
split; intros.
 rewrite <- rAnd.
 apply rExE with (2:=H); intros.
 rewrite rAnd.
 destruct x0; simpl in *.
 split.
  apply rExI; exists x0; trivial.

  apply rExE with (2:=h); intros.
  rewrite rAnd in H1; destruct H1.
  apply rExI; exists x1; rewrite rAnd; split; trivial.
  apply eq_set_trans with (elts x x0); trivial.

 destruct H.
 apply rExE with (2:=H0); intros.
 rewrite rAnd in H1; destruct H1.
 apply rExE with (2:=H); intros.
 assert (holds (Exist(fun x'=>eq_set (elts x x1) x'/\P x'))).
  apply rExI; exists x0; rewrite rAnd; split; trivial.
  apply eq_set_trans with z; trivial.
  apply eq_set_sym; trivial.
 apply rExI.
 exists (exist (fun _ =>_) x1 H4); simpl; trivial.
Qed.

Definition power (x:set) :=
  sup (idx x->prop)
   (fun P => subset x
         (fun y => Exist(fun i =>  eq_set y (elts x i) /\ P i))).

Lemma power_ax : forall x z,
  z \in power x <->
  (forall y, y \in z -> y \in x).
split; intros.
 apply rExE with (2:=H); intros.
 specialize eq_elim with (1:=H0)(2:=H1); intro.
 simpl in H2; rewrite subset_ax in H2.
 destruct H2; trivial.

 apply rExI; exists (fun  i => in_set (elts x i) z).
 apply eq_intro; intros.
  simpl; rewrite subset_ax.
  split; auto.
  apply rExI; exists z0; rewrite rAnd; split;[apply eq_set_refl|].
  specialize H with (1:=H0).
  apply rExE with (2:=H); intros.
  apply rExI; exists x0; rewrite rAnd; split; trivial.
  apply in_reg with z0; trivial.

  simpl in H0; rewrite subset_ax in H0.
  destruct H0.
  apply rExE with (2:=H1); intros.
  rewrite rAnd in H2; destruct H2.
  apply rExE with (2:=H3); intros.
  rewrite rAnd in H4; destruct H4.
  apply in_reg with (elts x x1); trivial.
  apply eq_set_sym.
  apply eq_set_trans with x0; trivial.
Qed.


Fixpoint num (n:nat) : set :=
  match n with
  | 0 => empty
  | S k => union (pair (num k) (pair (num k) (num k)))
  end.

Definition infinity := sup _ num.

Lemma infty_ax1 : empty \in infinity.
apply rExI; exists 0.
apply eq_set_refl.
Qed.

Lemma infty_ax2 : forall x, x \in infinity ->
  union (pair x (pair x x)) \in infinity.
intros.
apply rExE with (2:=H); intros.
apply rExI; exists (S x0); simpl elts.
apply union_morph.
apply pair_morph; trivial.
apply pair_morph; trivial.
Qed.


(* Functional Replacement *)

Definition repl0 (x:set) (F:set->set) :=
  sup _ (fun i => F (elts x i)).

Lemma repl0_ax : forall x F z,
  (forall z z', z \in x -> z == z' -> F z == F z') ->
  (z \in repl0 x F <->
   holds(Exist(fun y => in_set y x /\ eq_set z (F y)))).
split; intros.
 apply rExE with (2:=H0); intros.
 apply rExI; exists (elts x x0); rewrite rAnd; split; trivial.
 apply rExI; exists x0; apply eq_set_refl.

 apply rExE with (2:=H0); intros.
 rewrite rAnd in H1; destruct H1.
 apply rExE with (2:=H1); intros.
 apply rExI; exists x1.
 apply eq_set_trans with (F x0); trivial.
 apply H; trivial.
Qed.

Definition repl1 (x:set) (F:{y|y \in x}->set) :=
  sup _ (fun i => F (elts' x i)).

Lemma repl1_ax : forall x F z,
  (forall z z', proj1_sig z == proj1_sig z' -> F z == F z') ->
  (z \in repl1 x F <-> holds(Exist(fun y => eq_set z (F y)))).
split; intros.
 apply rExE with (2:=H0); intros.
 apply rExI; exists (elts' x x0); trivial.

 apply rExE with (2:=H0); intros.
 destruct x0.
 apply rExE with (2:=h); intros.
 apply rExI; exists x1.
 apply eq_set_trans with (1:=H1).
 apply H; trivial.
Qed.

(* Collection *)

(* intuitionistic version *)

(* The intuitionistic collection axiom (TTColl) is a consequence of
   [choice], but it is sufficient to prove collection.
 *)
Lemma ttcoll (X:Tlo) (R:X->set->Prop):
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

(* ttcoll rephrased on sets: *)
Lemma ttcoll_set A (R:set->set->Prop) :
  exists z, forall i, (exists w, R (elts A i) w) ->
            exists j, R (elts A i) (elts z j).
intros.
destruct (ttcoll (idx A) (fun i y => R (elts A i) y)) as (Y,(g,Hg)).
exists (sup Y g); trivial.
Qed.

(* Collection axiom out of TTColl: *)
Lemma collection_ax : forall A (R:set->set->prop), 
    (forall x x' y y', x \in A -> x == x' -> y == y' ->
     holds (R x y) -> holds (R x' y')) ->
    exists B, forall x, x \in A ->
      holds(Exist(fun y => R x y)) ->
      holds(Exist(fun y => in_set y B /\ R x y)).
intros.
destruct ttcoll_set with A (fun x y => holds (R x y)) as (B,HB).
exists B; intros x inA H0.
apply rExE with (2:=H0); intros w Rxw.
apply rExE with (2:=inA); intros i eqx.
assert (holds (R (elts A i) w)).
 apply H with (4:=Rxw); trivial.
 apply eq_set_refl.
destruct (HB i) as (j,Rxy).
 exists w; trivial.

 apply rExI; exists (elts B j); rewrite rAnd; split.
  apply (proj2_sig (elts' B j)).

  apply H with (4:=Rxy).
   apply in_reg with x; trivial.

   apply eq_set_sym; trivial.

   apply eq_set_refl.
Qed.

Lemma collection_ax' : forall A (R:set->set->prop), 
    (forall x x' y y', x \in A -> x == x' -> y == y' ->
     holds (R x y) -> holds (R x' y')) ->
    (forall x, x \in A -> holds(Exist(fun y => R x y))) ->
    exists B, forall x, x \in A -> holds(Exist(fun y => in_set y B /\ R x y)).
intros.
destruct collection_ax with (A:=A)(R:=R) as (B,HB); trivial.
exists B; auto.
Qed.

(* Deriving the existentially quantified sets *)

Lemma empty_ex: exists empty, forall x, ~ x \in empty.
exists empty.
exact empty_ax.
Qed.

Lemma pair_ex: forall a b,
  exists c, forall x, x \in c <-> holds(Or (eq_set x a) (eq_set x b)).
intros.
exists (pair a b).
apply pair_ax.
Qed.

Lemma union_ex: forall a, exists b,
    forall x, x \in b <-> holds(Exist(fun y => in_set x y /\ in_set y a)).
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
     exists2 y,
       (forall z, z \in y <-> holds(Or(eq_set z x) (in_set z x))) &
       y \in infinite).
exists infinity.
 exists empty.
  exact empty_ax.
  exact infty_ax1.

 intros.
 exists (union (pair x (pair x x))); intros.
  rewrite union_ax.
  split; intros.
   apply rExE with (2:=H0); intros.
   rewrite rAnd in H1; destruct H1.
   rewrite pair_ax in H2.
   apply rOrE with (2:=H2); destruct 1.
    apply rOrI; right; apply eq_elim with x0; trivial.

    specialize eq_elim with (1:=H1) (2:=H3); intro.
    rewrite pair_ax in H4.
    apply rOrE with (2:=H4); destruct 1; apply rOrI; auto.

   apply rOrE with (2:=H0); destruct 1.
    apply rExI; exists (pair x x); rewrite rAnd; split.
     rewrite pair_ax; apply rOrI; auto.

     rewrite pair_ax; apply rOrI; right; apply eq_set_refl.

    apply rExI; exists x; rewrite rAnd; split; trivial.
    rewrite pair_ax; apply rOrI; left; apply eq_set_refl.

  apply infty_ax2; trivial.
Qed.

End Ensembles.
