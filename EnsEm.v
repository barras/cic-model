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

Fixpoint isWf x := Forall(fun i => isWf (elts x i)).

Lemma set_isWf x : holds (isWf x).
induction x; simpl.
rewrite rForall; trivial.
Qed.

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

Lemma wf_ax' : forall P : set -> Prop,
  (exists P', forall x, P x <-> holds (P' x)) ->
  (forall x : set,
   (forall y : set, y \in x -> P y) -> P x) ->
  forall x : set, P x.
intros.
destruct H as (P',H).
rewrite H.
apply wf_ax; intros.
rewrite <- H; apply H0; intros.
rewrite H; auto.
Qed.

(***********************************************************)
(* Empty set *)

Definition empty :=
  sup False (fun x => match x with end).

Lemma empty_ax : forall x, ~ x \in empty.
red; intros.
apply rFF.
apply rExE with (2:=H); intros.
contradiction.
Qed.

(* Singleton and pairs *)
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

(* Union *)

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

(* Separation axiom *)
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
 exists (exist (fun i =>holds(Exist(fun x'=>eq_set(elts x i) x'/\P x'))) x1 H4); simpl; trivial.
Qed.

(* Power-set axiom *)

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

Lemma power_morph : forall x x', x == x' -> power x == power x'.
intros.
rewrite eq_set_ax; intros.
do 2 rewrite power_ax.
apply fa_morph; intro y.
apply fa_morph; intros _.
assert (H' := eq_set_sym _ _ H).
split; intros; eapply eq_elim; eassumption.
Qed.

(* Infinity *)

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

Definition replf (x:set) (F:set->set) :=
  sup _ (fun i => F (elts x i)).

Lemma replf_ax : forall x F z,
  (forall z z', z \in x -> z == z' -> F z == F z') ->
  (z \in replf x F <->
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

(* Replacement as a weaker form of collection *)

Lemma repl_ax_from_collection : forall a (R:set->set->prop),
    (forall x x' y y', x \in a -> holds (R x y) -> holds (R x' y') -> x == x' -> y == y') ->
    exists b, forall x, x \in b <-> holds(Exist(fun y => in_set y a /\ Exist(fun x' => eq_set x x' /\ R y x'))).
intros a R Rfun.
destruct collection_ax with (A:=a)
  (R:=fun x y => Exist(fun x'=>eq_set x x'/\Exist(fun y'=>eq_set y y'/\R x' y'))) as (B,HB).
 intros.
 apply rExE with (2:=H2); clear H2; intros x'' H2; rewrite rAnd in H2; destruct H2.
 apply rExE with (2:=H3); clear H3; intros y'' H3; rewrite rAnd in H3; destruct H3.
 apply rExI; exists x''; rewrite rAnd; split.
  apply eq_set_trans with x; trivial.
  apply eq_set_sym; trivial.
 apply rExI; exists y''; rewrite rAnd; split; trivial.
 apply eq_set_trans with y; trivial.
 apply eq_set_sym; trivial.
exists (subset B (fun y => Exist(fun x => in_set x a/\R x y))); split; intros.
 rewrite subset_ax in H; destruct H.
 apply rExE with (2:=H0); clear H0; intros y; rewrite rAnd; intros (?,?).
 apply rExE with (2:=H1); clear H1; intros x'; rewrite rAnd; intros (?,?).
 apply rExI; exists x'; rewrite rAnd; split; trivial.
 apply rExI; exists y; rewrite rAnd; auto.

 apply rExE with (2:=H);clear H; intros x'; rewrite rAnd; intros(?,?).
 apply rExE with (2:=H0);clear H0; intros y; rewrite rAnd; intros(?,?).
 rewrite subset_ax; split.
  refine (rExE _ (HB x' H _)); clear HB;
    [intros y'; rewrite rAnd; intros(?,?)|].
   apply rExE with (2:=H3); clear H3; intros x''; rewrite rAnd; intros(?,?).
   apply rExE with (2:=H4); clear H4; intros y''; rewrite rAnd; intros(?,?).
   apply in_reg with y'; trivial.
   apply eq_set_trans with y''; trivial.
   apply eq_set_trans with y;[|apply eq_set_sym; trivial].
   apply Rfun with x'' x'; trivial.
    apply in_reg with x'; trivial.
    apply eq_set_sym; trivial.

   apply rExI; exists y.
   apply rExI; exists x'; rewrite rAnd; split; [apply eq_set_refl|].
   apply rExI; exists y; rewrite rAnd; auto using eq_set_refl.

 apply rExI; exists y; rewrite rAnd; split; trivial.
 apply rExI; exists x'; rewrite rAnd; auto.
Qed.

Definition repl_ex := repl_ax_from_collection.

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

(* Showing that in classical logic, collection can be made
   deterministic, by building the smallest element of
   Veblen hierarchy containing the images *)


(* Fixpoint *)
Fixpoint wfrec (F:(set->set)->set->set) (x:set) : set :=
  F (fun y => union (sup {i:idx x|elts x i == y}
               (fun i => wfrec F (elts x (proj1_sig i))))) x.
Section FixRec.
Hypothesis F : (set->set)->set->set.
Hypothesis Fext : forall x x' f f',
  (forall y y', y \in x -> y == y' -> f y == f' y') ->
  x == x' ->
  F f x == F f' x'.

Lemma wfrecm x x' : x == x' -> wfrec F x == wfrec F x'.
revert x'; induction x; destruct x'; intros.
simpl wfrec.
apply Fext; trivial.
rewrite eq_set_def in H0; simpl in H0; destruct H0.
intros.
apply union_morph.
rewrite eq_set_def; simpl idx; simpl elts; split; intros (i,e); simpl proj1_sig.
 clear H2.
 apply rExE with (2:=H0 i); intros j ?.
 assert (e' : f0 j == y').
  apply eq_set_trans with y; trivial.
  apply eq_set_trans with (f i); trivial.
  apply eq_set_sym; trivial.
 apply rExI; exists (exist (fun j => f0 j == y') j e'); simpl; auto.

 apply rExE with (2:=H2); clear H2; intros j H2; simpl in j,H2.
 apply eq_set_sym in H2.
 apply rExI; exists (exist (fun i => f i == y) j H2); simpl.
 apply H.
 apply eq_set_trans with y; trivial.
 apply eq_set_trans with y'; trivial.
 apply eq_set_sym; trivial.
Qed.

Lemma wfrec_eqn x :
  wfrec F x == F (wfrec F) x.
destruct x; simpl.
apply Fext.
2:apply eq_set_refl.
intros.
rewrite eq_set_ax.
intros z.
rewrite union_ax.
split; intros.
 apply rExE with (2:=H1); clear H1; intros b h.
 rewrite rAnd in h; destruct h.
 apply rExE with (2:=H2); clear H2; intros (j,e) ?.
 simpl in H2.
 apply eq_elim with b; trivial.
 apply eq_set_trans with (1:=H2).
 apply wfrecm.
 apply eq_set_trans with y; trivial.

 apply rExE with (2:=H); clear H; simpl; intros i H.
 apply eq_set_sym in H0.
 apply rExI; exists (wfrec F (f i)); rewrite rAnd; split.
  apply eq_elim with (1:=H1).
  apply wfrecm.
  apply eq_set_trans with y; trivial.

  apply eq_set_sym in H.
  apply rExI; exists (exist (fun i => (f i == y)) i H).
  simpl.
  apply eq_set_refl.
Qed.
End FixRec.


Section ClassicalCollection.

(* Veblen cumulative hierarchy (applied to any set) *)
Fixpoint V (x:set) := union (replf x (fun x' => power (V x'))).

Lemma V_morph : forall x x', x == x' -> V x == V x'.
induction x; destruct x'; intros.
simpl V; unfold replf; simpl sup.
apply union_morph.
rewrite eq_set_def in H0; simpl in H0.
destruct H0.
apply eq_intro; intros.
 apply rExE with (2:=H2); clear H2; simpl; intros.
 apply rExE with (2:=H0 x); simpl; intros.
 apply rExI; exists x0; simpl.
 apply eq_set_trans with (1:=H2).
 apply power_morph.
 auto.

 apply rExE with (2:=H2); clear H2; simpl; intros.
 apply rExE with (2:=H1 x); simpl; intros.
 apply rExI; exists x0; simpl.
 apply eq_set_trans with (1:=H2).
 apply eq_set_sym.
 apply power_morph.
 auto.
Qed.

Lemma V_def : forall x z,
  z \in V x <-> holds(Exist(fun y => in_set y x /\ in_set z (power (V y)))).
destruct x; simpl; intros.
rewrite union_ax.
unfold replf; simpl.
split; intros.
 apply rExE with (2:=H); clear H; intros.
 rewrite rAnd in H; destruct H.
 apply rExE with (2:=H0); clear H0; simpl; intros.
 apply rExI; exists (f x0); rewrite rAnd; split.
  apply rExI; exists x0; apply eq_set_refl.

  specialize eq_elim with (1:=H) (2:=H0); intro; trivial.

 apply rExE with (2:=H); clear H; intros.
 rewrite rAnd in H; destruct H.
 apply rExE with (2:=H); clear H; simpl; intros.
 apply rExI; exists (power (V x)); rewrite rAnd; split; trivial.
 apply rExI; exists x0; simpl elts.
 apply power_morph.
 apply V_morph; trivial.
Qed.


(* Automatically prove that Prop-predicates based on
   conjunction, universal quantification, implication
   and predicates of the logic remain in the same
   logic. *)
Ltac clause_tac :=
 econstructor; intros; repeat
   (reflexivity||
    (rewrite rAnd; apply and_iff_morphism) ||
    (rewrite rImp; apply fa_morph; intros _) ||
    (rewrite rForall; apply fa_morph; intro)).

Lemma V_trans : forall x y z,
  z \in y -> y \in V x -> z \in V x.
intros x.
apply wf_ax' with (x:=x).
 clause_tac.
clear x; intros.
rewrite V_def in H1|-*.
apply rExE with (2:=H1);clear H1; intros.
rewrite rAnd in H1; destruct H1.
apply rExI; exists x0; rewrite rAnd; split; trivial.
rewrite power_ax in H2|-*; eauto.
Qed.

Lemma V_pow : forall x, power (V x) == V (singl x).
intros.
apply eq_intro; intros.
 rewrite V_def.
 apply rExI; exists x; rewrite rAnd; split; trivial.
 apply rExI; exists tt; apply eq_set_refl.

 rewrite V_def in H.
 apply rExE with (2:=H); clear H; intros.
 rewrite rAnd in H; destruct H.
 apply rExE with (2:=H); clear H; simpl; intros.
 apply eq_elim with (power (V x0)); auto.
 apply power_morph.
 apply V_morph; trivial.
Qed.

Lemma V_mono : forall x x',
  x \in x' -> V x \in V x'.
intros.
rewrite (V_def x').
apply rExI; exists x; rewrite rAnd; split; trivial.
rewrite power_ax; auto.
Qed.

Lemma V_sub : forall x y y',
  y \in V x -> y' \in power y -> y' \in V x.
intros.
rewrite V_def in H|-*.
apply rExE with (2:=H); clear H; intros.
rewrite rAnd in H; destruct H.
apply rExI; exists x0; rewrite rAnd; split; trivial.
rewrite power_ax in H0,H1|-*; auto.
Qed.

Lemma V_compl : forall x z, z \in V x <-> V z \in V x. 
intros x.
pattern x; apply wf_ax'; clear x; intros.
 clause_tac.
repeat rewrite V_def.
split; intros.
 apply rExE with (2:=H0); clear H0; intros.
 rewrite rAnd in H0; destruct H0.
 apply rExI; exists x0; rewrite rAnd; split; trivial.
 rewrite power_ax in H1|-*; intros.
 rewrite V_def in H2.
 apply rExE with (2:=H2); intros.
 rewrite rAnd in H3; destruct H3.
 apply H1 in H3.
 rewrite H in H3; trivial.
 apply V_sub with (V x1); trivial.

 apply rExE with (2:=H0); clear H0; intros.
 rewrite rAnd in H0; destruct H0.
 apply rExI; exists x0; rewrite rAnd; split; trivial.
 rewrite power_ax in H1|-*; intros.
 rewrite H; trivial.
 apply H1.
 apply V_mono; trivial.
Qed.

Lemma V_comp2 x y : x \in power (V y) -> V x \in power (V y).
intros.
apply eq_elim with (V (singl y)).
2:apply eq_set_sym; apply V_pow.
apply -> V_compl.
apply eq_elim with (1:=H).
apply V_pow.
Qed.

Lemma V_intro : forall x, x \in power (V x).
intros x.
rewrite power_ax; intros.
rewrite V_compl; apply V_mono; trivial.
Qed.

Lemma V_idem : forall x, V (V x) == V x.
intros.
apply eq_intro; intros.
 rewrite V_def in H.
 apply rExE with (2:=H); clear H; intros.
 rewrite rAnd in H; destruct H.
 apply V_sub with (V x0); trivial.
 rewrite <- V_compl; trivial.

 apply V_sub with (V z).
  apply V_mono; trivial.
  apply V_intro.
Qed.

Lemma rk_induc :
  forall P:set->Prop,
  (exists P', forall x, P x <-> holds (P' x)) ->
  (forall x, (forall y, y \in V x -> P y) -> P x) ->
  forall x, P x.
intros.
destruct H as (P',H).
cut (forall y, V y \in power (V x) -> P y).
 intros.
 apply H1.
 rewrite power_ax; auto.
apply wf_ax' with (x:=x); intros.
 clause_tac.
 apply H.
apply H0; intros.
rewrite power_ax in H2; specialize H2 with (1:=H3).
rewrite V_def in H2.
rewrite H; apply rExE with (2:=H2); clear H2; intros; rewrite <- H.
rewrite rAnd in H2; destruct H2.
apply H1 with x1; trivial.
apply V_comp2; trivial.
Qed.


Hypothesis EM : forall A, holds (Or A (Not A)).

(* classical *)
Lemma V_total : forall x y, holds (Or (in_set (V x) (V y)) (in_set (V y) (power (V x)))).
intros x y.
revert x.
apply wf_ax' with (x:=y); clear y.
 clause_tac.
 instantiate (1:=fun x0 => Or (in_set (V x0) (V x)) (in_set (V x) (power (V x0)))); reflexivity.
 (* reflexivity should have worked: pattern! *)
intros y Hy x.
apply rOrE with (2:=EM (Exist(fun y' => in_set y' (V y) /\ (in_set (V x) (power y'))))).
destruct 1.
 apply rOrI; left.
 apply rExE with (2:=H); clear H; intros.
 rewrite rAnd in H; destruct H.
 apply V_sub with x0; trivial.

 apply rOrI; right; rewrite power_ax; intros.
 rewrite rNot in H.
 rewrite V_def in H0.
 apply rExE with (2:=H0); clear H0; intros.
 rewrite rAnd in H0; destruct H0.
 assert (holds (Exist(fun w => in_set w (V x) /\ Not (in_set w (V x0))))).
  apply rOrE with (2:=EM (Exist(fun w => in_set w (V x) /\ Not(in_set w (V x0)))));
   destruct 1; trivial.
  rewrite rNot in H2.
  assert (~ V x \in power (V x0)).
   red; intros; apply H.
   apply rExI; exists (V x0); rewrite rAnd; split; trivial.
   apply V_mono; trivial.
  elim H3; rewrite power_ax; intros.
  apply rOrE with (2:=EM (in_set y1 (V x0))); destruct 1; trivial.
  elim H2.
  apply rExI; exists y1; rewrite rAnd; split; trivial.
 apply rExE with (2:=H2); clear H2; intros.
 rewrite rAnd in H2; destruct H2.
 apply rOrE with (2:=Hy _ H0 x1); destruct 1.
  rewrite rNot in H3; elim H3.
  apply V_sub with (V x1); trivial.
  apply V_intro.

  apply V_sub with (V x1).
   apply -> V_compl; trivial.

   rewrite power_ax in H1,H4|-*; auto.
Qed.

Definition lst_rk (P:set->prop) (y:set) :=
  P y /\
  eq_set y (V y) /\
  (Forall(fun x=> Imp(eq_set x (V x))(Imp(P x)(in_set y (power(V x)))))).

Lemma lst_rk_morph :
  forall (P P':set->prop), (forall x x', x == x' -> (holds (P x) <-> holds (P' x'))) ->
  forall y y', y == y' -> holds (lst_rk P y) -> holds (lst_rk P' y').
intros.
unfold lst_rk in H1; repeat rewrite rAnd in H1.
destruct H1.
destruct H2.
rewrite rForall in H3.
unfold lst_rk; repeat rewrite rAnd.
split; [|split].
 revert H1; apply H; trivial.

 apply eq_set_trans with y;[apply eq_set_sym; trivial|].
 apply eq_set_trans with (V y); trivial.
 apply V_morph; trivial.

 rewrite rForall; intros x.
 assert (h:=H3 x); clear H3.
 repeat rewrite rImp in h|-*; intros.
 apply in_reg with y; trivial.
 apply h; trivial.
 revert H4; apply H.
 apply eq_set_refl.
Qed.

Lemma lst_incl : forall P y, holds (lst_rk P y) -> holds (P y). 
intros.
unfold lst_rk in H; rewrite rAnd in H; destruct H; trivial.
Qed.

Lemma lst_fun : forall P y y', holds (lst_rk P y) -> holds (lst_rk P y') -> y == y'.
unfold lst_rk; intros.
repeat rewrite rAnd in H,H0.
destruct H as (p1,(ex1,lst1)); destruct H0 as (p2,(ex2,lst2)).
rewrite rForall in lst1, lst2.
assert (lst1':=lst1 y'); clear lst1.
assert (lst2':=lst2 y); clear lst2.
repeat rewrite rImp in lst1', lst2'.
specialize lst1' with (1:=ex2) (2:=p2).
specialize lst2' with (1:=ex1) (2:=p1).
apply eq_set_trans with (V y); trivial.
apply eq_set_trans with (V y');[|apply eq_set_sym; trivial].
apply V_comp2 in lst1'.
apply V_comp2 in lst2'.
rewrite power_ax in lst1', lst2'.
apply eq_intro; intros; auto.
Qed.

Lemma lst_ex : forall (P:set->prop),
  (forall x x', x == x' -> holds (P x) -> holds (P x')) ->
  holds (Exist(fun x => P (V x))) ->
  holds (Exist(lst_rk P)).
intros P Pm Pex.
apply rExE with (2:=Pex); clear Pex.
intros x.
apply rk_induc with (x:=x); clear x; intros.
 clause_tac.
apply rOrE with (2:=EM (Exist(fun z => in_set z (V x) /\ P (V z)))); destruct 1.
 apply rExE with (2:=H1); clear H1; intros.
 rewrite rAnd in H1; destruct H1.
 eauto.

 apply rExI; exists (V x).
 unfold lst_rk; repeat rewrite rAnd; split; [|split]; trivial.
  apply eq_set_sym; apply V_idem.

  rewrite rForall; intros y.
  repeat rewrite rImp; intros.
  apply rOrE with (2:=V_total y x); destruct 1; auto.
  rewrite rNot in H1; elim H1; clear H1.
  apply rExI; exists y; rewrite rAnd; split.
   apply in_reg with (V y); trivial.
   apply eq_set_sym; trivial.

   revert H3; apply Pm; trivial.
Qed.

Lemma coll_ax_uniq : forall A (R:set->set->prop), 
    (forall x x' y y', x \in A -> x == x' -> y == y' ->
     holds (R x y) -> holds (R x' y')) ->
    holds(Exist(lst_rk (fun B =>
      Forall(fun x => Imp(in_set x A)
      (Imp(Exist(fun y => R x y))
          (Exist(fun y => in_set y B /\ R x y))))))).
intros.
destruct collection_ax with (A:=A) (R:=R); trivial.
apply lst_ex.
 intros a a' eqa.
 do 2 rewrite rForall; apply fa_morph; intros x0.
 repeat rewrite rImp.
 apply fa_morph; intros _.
 apply fa_morph; intros _.
 split; intros.
  apply rExE with (2:=H1); clear H1; intros.
  rewrite rAnd in H1; destruct H1.
  apply rExI; exists x1; rewrite rAnd; split; trivial.
  apply eq_elim with a'; trivial.
  apply eq_set_sym; trivial.

  apply rExE with (2:=H1); clear H1; intros.
  rewrite rAnd in H1; destruct H1.
  apply rExI; exists x1; rewrite rAnd; split; trivial.
  apply eq_elim with a; trivial.

 apply rExI; exists x.
 rewrite rForall; intros a.
 repeat rewrite rImp; intros.
 apply H0 in H2; trivial.
 apply rExE with (2:=H2); clear H2; intros.
 rewrite rAnd in H2; destruct H2.
 apply rExI; exists x0; rewrite rAnd; split; trivial.
 apply V_mono in H2.
 apply V_sub with (V x0); trivial.
 apply V_intro.
Qed.

End ClassicalCollection.

End Ensembles.
