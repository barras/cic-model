Require Import ZFskol.
Require Import Choice. (* Axiom *)
Require Import Sublogic.

(** In this file, we give an attempt to build a model of IZF
   in Coq.
 *)

Module IZF_R <: IZF_R_Ex_sig CoqSublogicThms.

(* The level of indexes *)
Definition Ti := Type.

Inductive set_ : Type :=
  sup (X:Ti) (f:X->set_).
Definition set := set_.

Definition idx (x:set) := let (X,_) := x in X.
Definition elts (x:set) : idx x -> set :=
  match x return idx x -> set with
  | sup X f => f
  end.

Fixpoint eq_set (x y:set) {struct x} :=
  (forall i, exists j, eq_set (elts x i) (elts y j)) /\
  (forall j, exists i, eq_set (elts x i) (elts y j)).

Lemma eq_set_refl : forall x, eq_set x x.
induction x; simpl.
split; intros.
 exists i; trivial.
 exists j; trivial.
Qed.

Lemma eq_set_sym : forall x y, eq_set x y -> eq_set y x.
induction x; destruct y; simpl; intros.
destruct H0.
split; intros.
 elim (H1 i); intros.
 exists x; auto.

 elim (H0 j); intros.
 exists x; auto.
Qed.

Lemma eq_set_trans : forall x y z,
  eq_set x y -> eq_set y z -> eq_set x z.
induction x; destruct y; destruct z; simpl; intros.
destruct H0.
destruct H1.
split; intros.
 elim (H0 i); intros.
 elim (H1 x); intros.
 exists x0; eauto.

 elim (H3 j); intros.
 elim (H2 x); intros.
 exists x0; eauto.
Qed.

Lemma eq_set_def : forall x y,
  (forall i, exists j, eq_set (elts x i) (elts y j)) ->
  (forall j, exists i, eq_set (elts x i) (elts y j)) ->
  eq_set x y.
destruct x; simpl; auto.
Qed.

Definition in_set x y :=
  exists j, eq_set x (elts y j).

Definition incl_set x y := forall z, in_set z x -> in_set z y.

Lemma eq_elim0 : forall x y i,
  eq_set x y ->
  exists j, eq_set (elts x i) (elts y j).
destruct x; simpl; intros.
destruct H.
auto.
Qed.

Lemma eq_set_ax : forall x y,
  eq_set x y <-> (forall z, in_set z x <-> in_set z y).
unfold in_set; split; intros.
 split; intros; destruct H0.
  destruct (eq_elim0 x y x0); trivial.
  exists x1; apply eq_set_trans with (elts x x0); trivial.

  apply eq_set_sym in H.
  destruct (eq_elim0 y x x0); trivial.
  exists x1; apply eq_set_trans with (elts y x0); trivial.

 destruct x; simpl in *.
 destruct y; simpl in *.
 split; intros.
  destruct (H (f i)).
  apply H0.
  exists i; apply eq_set_refl.

  destruct (H (f0 j)).
  destruct H1.
   exists j; apply eq_set_refl.

   exists x; apply eq_set_sym; trivial.
Qed.

Definition elts' (x:set) (i:idx x) : {y|in_set y x}.
exists (elts x i).
abstract (exists i; apply eq_set_refl).
Defined.

Lemma in_reg : forall x x' y,
  eq_set x x' -> in_set x y -> in_set x' y.
destruct 2; intros.
exists x0.
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

Lemma Acc_in_set : forall x, Acc in_set x.
cut (forall x y, eq_set x y -> Acc in_set y).
 intros.
 apply H with x; apply eq_set_refl.
induction x; intros.
constructor; intros.
specialize eq_elim with (1:=H1)(2:=eq_set_sym _ _ H0); intro.
clear y H0 H1.
destruct H2; simpl in *.
apply H with x.
apply eq_set_sym; trivial.
Qed.


Lemma wf_rec :
  forall P : set -> Type,
  (forall x, (forall y, in_set y x -> P y) -> P x) -> forall x, P x.
intros.
elim (Acc_in_set x); intros.
apply X; apply X0.
Defined.


Lemma wf_ax :
  forall (P:set->Prop),
  (forall x, P x -> P x) ->
  (forall x, (forall y, in_set y x -> P y) -> P x) -> forall x, P x.
intros P _ H x.
cut (forall x', eq_set x x' -> P x');[auto using eq_set_refl|].
induction x; intros.
apply H; intros.
assert (in_set y (sup X f)).
 apply eq_elim with x'; trivial.
 apply eq_set_sym; trivial.
clear H1 H2.
destruct H3; simpl in *.
apply eq_set_sym in H1; eauto.
Qed.

(* *)

Definition empty :=
  sup False (fun x => match x with end).

Lemma empty_ax : forall x, ~ in_set x empty.
unfold in_set, empty; simpl.
red; intros.
destruct H.
destruct x0.
Qed.

Definition singl x := sup unit (fun _ => x).

Definition pair x y :=
  sup bool (fun b => if b then x else y).

Lemma pair_ax : forall a b z,
  in_set z (pair a b) <-> eq_set z a \/ eq_set z b.
unfold in_set, pair; simpl.
split; intros.
 destruct H.
 destruct x; auto.

 destruct H.
  exists true; trivial.
  exists false; trivial.
Qed.

Lemma pair_morph :
  forall a a', eq_set a a' -> forall b b', eq_set b b' ->
  eq_set (pair a b) (pair a' b').
unfold pair.
simpl; intros.
split; intros.
 exists i; destruct i; trivial.
 exists j; destruct j; trivial.
Qed.

Definition union (x:set) :=
  sup {i:idx x & idx (elts x i)}
    (fun p => elts (elts x (projS1 p)) (projS2 p)).

Lemma union_ax : forall a z,
  in_set z (union a) <-> exists2 b, in_set z b & in_set b a.
unfold in_set at 1, union; simpl; intros.
split; intros.
 destruct H.
 exists (elts a (projT1 x)).
  exists (projT2 x); trivial.
  exists (projT1 x); apply eq_set_refl.

 destruct H.
 destruct H0.
 assert (in_set z (elts a x0)).
  apply eq_elim with x; trivial.
 destruct H1.
 exists (existT (fun i=>idx(elts a i)) x0 x1); simpl.
 trivial.
Qed.

Lemma union_morph :
  forall a a', eq_set a a' -> eq_set (union a) (union a').
unfold union.
simpl; intros.
split; intros.
 destruct i; simpl.
 assert (in_set (elts a x) a').
  apply eq_elim with a; trivial.
  exists x; apply eq_set_refl.
 destruct H0.
 assert (in_set (elts (elts a x) i) (elts a' x0)).
  apply eq_elim with (elts a x); trivial.
  exists i; apply eq_set_refl. 
 destruct H1.
 exists (existT (fun i=>idx (elts a' i)) x0 x1); simpl.
 trivial.

 destruct j; simpl.
 generalize (eq_set_sym _ _ H); clear H; intro.
 assert (in_set (elts a' x) a).
  apply eq_elim with a'; trivial.
  exists x; apply eq_set_refl.
 destruct H0.
 assert (in_set (elts (elts a' x) i) (elts a x0)).
  apply eq_elim with (elts a' x); trivial.
  exists i; apply eq_set_refl. 
 destruct H1.
 exists (existT (fun i=>idx (elts a i)) x0 x1); simpl.
 apply eq_set_sym; trivial.
Qed.

(* Fixpoint *)
Fixpoint wfrec (F:(set->set)->set->set) (x:set) : set :=
  F (fun y => union (sup {i:idx x|eq_set (elts x i) y}
               (fun i => wfrec F (elts x (proj1_sig i))))) x.
Section FixRec.
Hypothesis F : (set->set)->set->set.
Hypothesis Fext : forall x x' f f',
  (forall y y', in_set y x -> eq_set y y' -> eq_set (f y) (f' y')) ->
  eq_set x x' ->
  eq_set (F f x) (F f' x').

Instance wfrecm : Proper (eq_set==>eq_set) (wfrec F).
do 2 red.
induction x; destruct y; intros.
simpl wfrec.
apply Fext; trivial.
simpl in H0; destruct H0.
intros.
apply union_morph.
simpl.
split; intros.
 clear H2; destruct i as (i,?); simpl.
 destruct (H0 i) as (j,?).
 assert (eq_set (f0 j) y').
  apply eq_set_trans with y; trivial.
  apply eq_set_trans with (f i); trivial.
  apply eq_set_sym; trivial.
 exists (exist _ j H4); simpl.
 apply H; trivial.

 destruct H2 as (i,?H2); simpl in i,H2.
 destruct j as (j,?).
 exists (exist _ i (eq_set_sym _ _ H2)); simpl.
 apply H.
 apply eq_set_sym.
 apply eq_set_trans with y; trivial. 
 apply eq_set_trans with y'; trivial.
 apply eq_set_sym; trivial.
Qed.

Lemma wfrec_eqn x :
  eq_set (wfrec F x) (F (wfrec F) x).
destruct x; simpl.
apply Fext.
2:apply eq_set_refl.
intros.
rewrite eq_set_ax.
intros z.
rewrite union_ax.
split; intros.
 destruct H1 as (b,?,?).
 destruct H2 as ((j,e),?).
 simpl in H2.
 apply eq_elim with b; trivial.
 apply eq_set_trans with (1:=H2).
 apply wfrecm.
 apply eq_set_trans with y; trivial.

 destruct H as (i,H).
 simpl in i,H.
 apply eq_set_sym in H0.
 exists (wfrec F (f i)).
  apply eq_elim with (1:=H1).
  apply wfrecm.
  apply eq_set_trans with y; trivial.

  apply eq_set_sym in H.
  exists (exist _ i H).
  simpl.
  apply eq_set_refl.
Qed.
End FixRec.

Definition subset (x:set) (P:set->Prop) :=
  sup {a|exists2 x', eq_set (elts x a) x' & P x'}
    (fun y => elts x (proj1_sig y)).

Lemma subset_ax : forall x P z,
  in_set z (subset x P) <->
  in_set z x /\ exists2 z', eq_set z z' & P z'.
unfold in_set at 1, subset; simpl.
split; intros.
 destruct H.
 destruct x0; simpl in H.
 split.
  exists x0; trivial.
  destruct e.
  exists x1; trivial.

  apply eq_set_trans with (elts x x0); trivial.

 destruct H.
 destruct H.
 destruct H0.
 assert (exists2 x', eq_set (elts x x0) x' & P x').
  exists x1; trivial.
  apply eq_set_trans with z; trivial.
  apply eq_set_sym; trivial.
 exists
  (@exist _ (fun a=>exists2 x',eq_set (elts x a) x' & P x')
    x0 H2); simpl; trivial.
Qed.

Definition power (x:set) :=
  sup (idx x->Prop)
   (fun P => subset x
         (fun y => exists2 i, eq_set y (elts x i) & P i)).

Lemma power_ax : forall x z,
  in_set z (power x) <->
  (forall y, in_set y z -> in_set y x).
unfold in_set at 1, power; simpl; intros.
split; intros.
 destruct H.
 specialize eq_elim with (1:=H0)(2:=H); intro.
 apply (proj1 (proj1 (subset_ax _ _ _) H1)).

 exists (fun i => in_set (elts x i) z).
 apply eq_intro; intros.
  apply (fun x P z => proj2 (subset_ax x P z)).
  split; auto.
  exists z0.
   apply eq_set_refl.

   elim H with z0; trivial; intros.
   exists x0; trivial.
   apply in_reg with z0; trivial.

  elim (proj2 (proj1 (subset_ax _ _ _) H0)); intros.
  destruct H2.
  apply in_reg with (elts x x1); trivial.
  apply eq_set_sym;
    apply eq_set_trans with x0; trivial.
Qed.

Lemma power_morph : forall x y,
  eq_set x y -> eq_set (power x) (power y).
intros.
apply eq_intro; intros.
 rewrite power_ax in H0|-*; intros.
 apply eq_elim with x; auto.

 apply eq_set_sym in H.
 rewrite power_ax in H0|-*; intros.
 apply eq_elim with y; auto.
Qed.

Fixpoint num (n:nat) : set :=
  match n with
  | 0 => empty
  | S k => union (pair (num k) (pair (num k) (num k)))
  end.

Definition infinity := sup _ num.

Lemma infty_ax1 : in_set empty infinity.
 exists 0.
 unfold elts, infinity, num.
 apply eq_set_refl.
Qed.

Lemma infty_ax2 : forall x, in_set x infinity ->
  in_set (union (pair x (pair x x))) infinity.
intros.
destruct H.
exists (S x0).
simpl elts.
apply union_morph.
apply pair_morph; trivial.
apply pair_morph; trivial.
Qed.

Definition replf (x:set) (F:set->set) :=
  sup _ (fun i => F (elts x i)).

Lemma replf_ax : forall x F z,
  (forall z z', in_set z x ->
   eq_set z z' -> eq_set (F z) (F z')) ->
  (in_set z (replf x F) <->
   exists2 y, in_set y x & eq_set z (F y)).
unfold in_set at 2, replf; simpl; intros.
split; intros.
 destruct H0.
 exists (elts x x0); trivial.
 exists x0; apply eq_set_refl.

 destruct H0.
 destruct H0.
 exists x1.
 apply eq_set_trans with (F x0); trivial.
 apply eq_set_sym.
 apply H.
  exists x1; apply eq_set_refl.
  apply eq_set_sym; trivial.
Qed.


Definition repl1 (x:set) (F:{y|in_set y x}->set) :=
  sup _ (fun i => F (elts' x i)).

Lemma repl1_ax : forall x F z,
  (forall z z', eq_set (proj1_sig z) (proj1_sig z') ->
   eq_set (F z) (F z')) ->
  (in_set z (repl1 x F) <->
   exists y, eq_set z (F y)).
unfold in_set at 6, repl1; simpl; intros.
split; intros.
 destruct H0.
 exists (elts' x x0); trivial.

 destruct H0.
 destruct x0.
 elim i; intros.
 exists x1.
 apply eq_set_trans with (1:=H0).
 apply H; simpl; trivial.
Qed.

Lemma repl1_morph : forall x y F G,
  eq_set x y ->
  (forall x' y', eq_set (proj1_sig x') (proj1_sig y') ->
   eq_set (F x') (G y')) ->
  eq_set (repl1 x F) (repl1 y G).
intros.
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

(* We only use the following instance of unique choice for
   replacement: *)
Definition ttrepl :=
  forall a:set, unique_choice {x|in_set x a} set eq_set.

(* We show it is a consequence of [choice]. *)
Lemma ttrepl_axiom : ttrepl.
red; red; intros; apply choice_axiom; trivial.
Qed.

Lemma repl_ax:
    forall a (R:set->set->Prop),
    (forall x x' y y', in_set x a ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x y y', in_set x a -> R x y -> R x y' -> eq_set y y') ->
    exists b, forall x, in_set x b <->
     (exists2 y, in_set y a & R y x).
intros.
elim (ttrepl_axiom (subset a (fun x=>exists y, R x y))
        (fun p y => R (proj1_sig p) y)); intros.
pose (a' := {x|in_set x (subset a (fun x => exists y, R x y))}).
fold a' in x,H1.
exists (repl1 _ x).
intros.
elim (repl1_ax _ x x0); intros.
 fold a' in H2,H3|-.
 split; intros.
  elim H2; trivial; intros.
  exists (proj1_sig x1).
   apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig x1))).

   apply H with (4:=H1 x1).
    apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig x1))).
    apply eq_set_refl.
    apply eq_set_sym; trivial.

  apply H3.
  destruct H4.
  assert (in_set x1 (subset a (fun x => exists y, R x y))).
   apply (proj2 (subset_ax a (fun x => exists y, R x y) x1)).
   split; trivial.
   exists x1.
    apply eq_set_refl.
    exists x0; trivial.
  pose (x' := exist _ x1 H6 : a').
  exists x'.
  apply H0 with x1; trivial.
  apply (H1 x').

 apply H0 with (proj1_sig z); trivial.
  apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig z))).
  apply H with (proj1_sig z') (x z'); trivial.
   apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig z'))).
   apply eq_set_sym; trivial.
   apply eq_set_refl.

(* side conditions *)
 elim (proj2 (proj1 (subset_ax _ _ _) (proj2_sig x))); intros. 
 destruct H2.
 exists x1; apply H with (4:=H2).
  apply in_reg with (proj1_sig x); trivial.
  apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig x))).

  apply eq_set_sym; trivial.

  apply eq_set_refl.

 assert (in_set (proj1_sig x) a).
  apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig x))).
 split; intros.
  apply H0 with (proj1_sig x); trivial.

  revert H1; apply H; trivial.
  apply eq_set_refl.
Qed.

(* Attempt to prove that choice is necessary for replacement, by deriving
   choice from replacement. Works only for relations that are morphisms for
   set equality... *)
Lemma ttrepl_needed_for_repl :
  forall a:set,
  let A := {x|in_set x a} in
  let eqA (x y:A) := eq_set (proj1_sig x) (proj1_sig y) in
  let B := set in
  let eqB := eq_set in
  forall (R:A->B->Prop),
  Proper (eqA==>eqB==>iff) R ->
  (forall x:A, exists y:B, R x y) ->
  (forall x y y', R x y -> R x y' -> eqB y y') ->
  exists f:A->B, forall x:A, R x (f x).
intros a A eqA B eqB R Rext Rex Runiq.
destruct repl_ax with
  (a:=a) (R:=fun x y => exists h:in_set x a, R (exist _ x h) y).
 intros.
 destruct H2.
 exists (in_reg _ _ _ H0 x0).
 revert H2; apply Rext; apply eq_set_sym; assumption.

 intros x y y' _ (h,Rxy) (h',Rxy').
 apply Runiq with (1:=Rxy).
 revert Rxy'; apply Rext.
  apply eq_set_refl.
  apply eq_set_refl.

 exists (fun y => union (subset x (fun z => R y z))).
 intro.
 destruct Rex with x0.
 apply Rext with (3:=H0);[apply eq_set_refl|].
 apply eq_set_sym.
 apply eq_set_ax; split; intros.
  rewrite union_ax; exists x1; trivial.
  rewrite subset_ax.
  split.
   apply H.
   exists (proj1_sig x0); [apply proj2_sig|].
   exists (proj2_sig x0).
   destruct x0; trivial.

   exists x1; trivial; apply eq_set_refl.

  rewrite union_ax in H1; destruct H1.
  rewrite subset_ax in H2; destruct H2.
  destruct H3.
  apply eq_elim with x2; trivial.
  apply eq_set_trans with (1:=H3).
  apply Runiq with (1:=H4); trivial.
Qed.

Notation "x \in y" := (in_set x y).
Notation "x == y" := (eq_set x y).

(* Deriving the existentially quantified sets *)

Lemma empty_ex: exists empty, forall x, ~ x \in empty.
exists empty.
exact empty_ax.
Qed.

Lemma pair_ex: forall a b, exists c, forall x, x \in c <-> (x == a \/ x == b).
intros.
exists (pair a b).
apply pair_ax.
Qed.

Lemma union_ex: forall a, exists b,
    forall x, x \in b <-> (exists2 y, x \in y & y \in a).
intros.
exists (union a).
apply union_ax.
Qed.

Lemma subset_ex : forall x P, exists b,
  forall z, z \in b <->
  (z \in x /\ exists2 z', z == z' & P z').
intros.
exists (subset x P).
apply subset_ax.
Qed.

Lemma power_ex: forall a, exists b,
     forall x, x \in b <-> (forall y, y \in x -> y \in a).
intros.
exists (power a).
apply power_ax.
Qed.

Lemma repl_ex:
    forall a (R:set->set->Prop),
    (forall x x' y y', x \in a -> R x y -> R x' y' -> x == x' -> y == y') ->
    exists b, forall x, x \in b <-> (exists2 y, y \in a & (exists2 x', x == x' & R y x')).
intros.
elim repl_ax with a
  (fun y' x' => exists2 y, y == y' & exists2 x, x' == x & R y x); intros.
 exists x; intros.
 rewrite H0; clear x H0.
 split; intros.
  destruct H0.
  destruct H1.
  exists x1; trivial.
  apply in_reg with x; trivial.
  apply eq_set_sym; trivial.

  destruct H0.
  exists x; trivial.
  exists x; trivial.
  apply eq_set_refl.

 destruct H3.
 destruct H4.
 exists x0.
  apply eq_set_trans with x; trivial.

  exists x1; trivial.
  apply eq_set_trans with y; trivial.
  apply eq_set_sym; trivial.

 destruct H1.
 destruct H3.
 destruct H2.
 destruct H5.
 apply eq_set_trans with x1; trivial.
 apply eq_set_trans with x3.
 2:apply eq_set_sym; trivial.
 apply H with x0 x2; trivial.
  apply in_reg with x; trivial.
  apply eq_set_sym; trivial.

  apply eq_set_trans with x; trivial.
  apply eq_set_sym; trivial.
Qed.

(* Collection *)
Section Collection.

Section FromTTColl.

(* TTColl is a consequence of choice *)
Lemma ttcoll :
  forall (A:Ti) (R:A->set->Prop),
  (forall x:A, exists y:set, R x y) ->
  exists X:Ti, exists f : X->set,
    forall x:A, exists i:X, R x (f i).
intros.
destruct (choice_axiom A set R) as (f,Hf); trivial.
(* X is A because choice "chooses" just one y for each x *)
exists A; exists f; eauto.
Qed.

Lemma ttcoll' :
  forall (A:Ti) R,
  (forall x:A, exists y:set, R x y) ->
  exists B, forall x:A, exists2 y, y \in B & R x y.
intros.
destruct ttcoll with (1:=H) as (X,(f,Hf)).
exists (sup X f).
intro.
destruct Hf with x.
exists (f x0); trivial.
exists x0; apply eq_set_refl.
Qed.

Lemma coll_ax_ttcoll : forall A (R:set->set->Prop), 
    (forall x x' y y', in_set x A ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x, in_set x A -> exists y, R x y) ->
    exists B, forall x, in_set x A -> exists2 y, in_set y B & R x y.
intros.
destruct (ttcoll (idx A) (fun i y => R (elts A i) y)) as (X,(f,Hf)).
 intro i.
 apply H0.
 exists i; apply eq_set_refl.

 exists (sup X f); intros.
 destruct H1 as (i,?).
 destruct (Hf i) as (j,?).
 exists (f j).
  exists j; apply eq_set_refl.

  revert H2; apply H.
   exists i; apply eq_set_refl.
   apply eq_set_sym; assumption.
   apply eq_set_refl.
Qed.

(* Proving collection requires the specialized version of ttcoll *)
Lemma ttcoll'' : forall A (R:set->set->Prop),
  (forall x x' y y', in_set x A ->
   eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
  (forall x, x \in A -> exists y:set, R x y) ->
  exists f : {x|x\in A} -> {X:Ti & X->set},
    forall x, exists i:projT1 (f x), R (proj1_sig x) (projT2 (f x) i).
intros.
destruct (coll_ax_ttcoll A R H H0) as (B,HB).
exists (fun _ => let (X,f) := B in existT (fun X => X->set) X f).
destruct B; simpl.
destruct x; simpl; intros.
destruct HB with x; trivial.
destruct H1.
exists x1.
apply H with (4:=H2); auto with *.
apply eq_set_refl.
Qed.

End FromTTColl.

Section FromChoice.

Lemma coll_ax_choice : forall A (R:set->set->Prop), 
    (forall x x' y y', in_set x A ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x, in_set x A -> exists y, R x y) ->
    exists B, forall x, in_set x A -> exists y, in_set y B /\ R x y.
intros.
elim (choice_axiom {x|x \in A} set (fun p y => R (proj1_sig p) y)); trivial; intros.
 exists (repl1 A x).
 intros.
 destruct H2.
 exists (x (elts' _ x1)); split.
  exists x1; apply eq_set_refl.

  apply H with (proj1_sig (elts' _ x1)) (x (elts' _ x1)); trivial.
   apply (proj2_sig (elts' _ x1)).
   apply eq_set_sym; trivial.
   apply eq_set_refl.

 apply H0.
 apply (proj2_sig x).
Qed.

End FromChoice.

Section FromReplClassic.

Hypothesis EM : forall A:Prop, A \/ ~A.

(* von Neumann cumulative hierarchy (applied to any set) *)
Fixpoint V (x:set) := union (replf x (fun x' => power (V x'))).

Lemma V_morph : forall x x', eq_set x x' -> eq_set (V x) (V x').
induction x; destruct x'; intros.
simpl V; unfold replf; simpl sup.
apply union_morph.
simpl in H0.
destruct H0.
apply eq_intro; intros.
 destruct H2.
 destruct (H0 x).
 exists x0.
 apply eq_set_trans with (1:=H2).
 simpl elts.
 apply power_morph.
 auto.

 destruct H2.
 destruct (H1 x).
 exists x0.
 apply eq_set_trans with (1:=H2).
 simpl elts.
 apply power_morph.
 apply eq_set_sym; auto.
Qed.

Lemma V_def : forall x z,
  in_set z (V x) <-> exists y, in_set y x /\ incl_set z (V y).
destruct x; simpl; intros.
rewrite union_ax.
unfold replf; simpl.
split; intros.
 destruct H.
 destruct H0; simpl in *.
 exists (f x0); split.
  exists x0; apply eq_set_refl.

  red; rewrite <- power_ax.
  apply eq_elim with x; trivial.

 destruct H.
 destruct H.
 exists (power (V x)).
  rewrite power_ax; trivial.

  destruct H; simpl in *.
  exists x0.
  apply power_morph.
  apply V_morph; trivial.
Qed.

Lemma V_trans : forall x y z,
  z \in y -> y \in V x -> z \in V x.
intros x.
pattern x; apply wf_ax; trivial; clear x; intros.
rewrite V_def in H1|-*.
destruct H1.
destruct H1.
exists x0; split; trivial.
red; intros; eauto.
Qed.

Lemma V_pow : forall x, power (V x) == V (singl x).
intros.
apply eq_intro; intros.
 rewrite power_ax in H.
 rewrite V_def.
 exists x; split; trivial.
 exists tt; apply eq_set_refl.

 rewrite power_ax; intros.
 rewrite V_def in H; destruct H; destruct H.
 destruct H; simpl in *.
 apply eq_elim with (V x0); auto.
 apply V_morph; trivial.
Qed.

Lemma V_mono : forall x x',
  in_set x x' -> in_set (V x) (V x').
intros.
rewrite (V_def x').
exists x; split; trivial.
red; trivial.
Qed.

Lemma V_sub : forall x y y',
  in_set y (V x) -> incl_set y' y -> in_set y' (V x).
intros x.
pattern x; apply wf_ax; trivial; clear x; intros.
rewrite V_def in H0|-*.
destruct H0; destruct H0.
exists x0; split; trivial.
red; auto.
Qed.


Lemma V_compl : forall x z, in_set z (V x) -> in_set (V z) (V x). 
intros x.
pattern x; apply wf_ax; trivial; clear x; intros.
rewrite V_def in *.
destruct H0; destruct H0.
exists x0; split; trivial.
red; intros.
rewrite V_def in H2; destruct H2; destruct H2.
apply H1 in H2.
apply V_sub with (V x1); eauto.
Qed.

Lemma V_intro : forall x, incl_set x (V x).
intros x.
pattern x; apply wf_ax; trivial; clear x; intros.
red; intros.
rewrite V_def.
exists z; split; auto.
Qed.

Lemma V_idem : forall x, V (V x) == V x.
intros.
apply eq_intro; intros.
 rewrite V_def in H; destruct H; destruct H.
 apply V_sub with (V x0); trivial.
 apply V_compl; trivial.

 apply V_sub with (V z).
  apply V_mono; trivial.
  apply V_intro.
Qed.

Lemma rk_induc :
  forall P:set->Prop,
  (forall x, (forall y, y \in V x -> P y) -> P x) ->
  forall x, P x.
intros.
cut (forall y, incl_set (V y) (V x) -> P y).
 intros.
 apply H0.
 red; trivial.
induction x using wf_ax; trivial; intros.
apply H; intros.
apply H1 in H2.
rewrite V_def in H2; destruct H2; destruct H2.
apply H0 with x0; trivial.
red; intros.
rewrite V_def in H4; destruct H4; destruct H4.
apply H3 in H4.
apply V_sub with (V x1); trivial.
apply V_compl; trivial.
Qed.

(* classical *)
Lemma V_total : forall x y, in_set (V x) (V y) \/ incl_set (V y) (V x).
intros x y.
revert x.
pattern y; apply wf_ax; trivial; clear y.
intros y Hy x.
destruct (EM (exists y', y' \in V y /\ incl_set (V x) y')).
left.
destruct H; destruct H.
apply V_sub with x0; trivial.

right; red; intros.
rewrite V_def in H0; destruct H0; destruct H0.
assert (exists w, w \in V x /\ ~ w \in V x0).
 destruct (EM (exists w, w \in V x /\ ~ w \in V x0)); trivial.
 assert (~ incl_set (V x) (V x0)).
  red; intros; apply H.
  exists (V x0); split; trivial.
  apply V_mono; trivial.
 elim H3; red; intros.
 destruct (EM (z0 \in V x0)); trivial.
 elim H2.
 exists z0; split; trivial.
destruct H2; destruct H2.
destruct (Hy _ H0 x1).
 elim H3.
 apply V_sub with (V x1); trivial.
 apply V_intro.

 apply V_sub with (V x1).
  apply V_compl; trivial.

  red; auto.
Qed.

Definition lst_rk (P:set->Prop) (y:set) :=
  P y /\
  (exists w, y == V w) /\
  (forall x, (exists w, x == V w) -> P x -> incl_set y (V x)).

Lemma lst_rk_morph :
  forall (P P':set->Prop), (forall x x', x == x' -> (P x <-> P' x')) ->
  forall y y', y == y' -> lst_rk P y -> lst_rk P' y'.
intros.
destruct H1.
destruct H2.
split; [|split].
 revert H1; apply H; trivial.

 destruct H2.
 exists x.
 apply eq_set_trans with y; trivial.
 apply eq_set_sym; trivial.

 red; intros.
 apply (H3 x); trivial.
 revert H5; apply H; apply eq_set_refl.

 apply eq_elim with y'; trivial.
 apply eq_set_sym; trivial.
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
 apply eq_elim with (V x).
 2:apply eq_set_sym; trivial.
 apply eq_elim with (V (V x)).
 2:apply V_idem.
 apply eq_elim with (V y'); trivial.
 apply V_morph; trivial.

 apply H in H3.
 destruct H0.
 apply eq_elim with (V y); trivial.
 apply eq_set_trans with (V (V x)).
  apply V_morph; trivial.
 apply eq_set_trans with (V x).
  apply V_idem.
 apply eq_set_sym; trivial.
Qed.

Lemma lst_ex : forall (P:set->Prop), (forall x x', eq_set x x' -> P x -> P x') ->
  (exists x, P (V x)) -> exists y, lst_rk P y.
intros P Pm.
destruct 1.
revert H.
pattern x; apply rk_induc; clear x; intros.
destruct (EM (exists z, z \in V x /\ P (V z))).
 destruct H1; destruct H1; eauto.

 exists (V x).
 split; [|split]; trivial.
  exists x; apply eq_set_refl.

  red; intros.
  destruct (V_total x0 x); auto.
  elim H1.
  destruct H2.
  exists x0; split.
   apply V_sub with (V x0); trivial.
   apply V_intro.

   apply Pm with x0; trivial.
   apply eq_set_trans with (V x1); trivial.
   apply eq_set_trans with (V (V x1)).
    apply eq_set_sym; apply V_idem.
   apply eq_set_sym; apply V_morph; trivial.
Qed.


Lemma coll_ax : forall A (R:set->set->Prop), 
    (forall x x' y y', in_set x A ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x, in_set x A -> exists y, R x y) ->
    exists B, forall x, in_set x A -> exists y, in_set y B /\ R x y.
intros.
pose (P := fun x y => x \in A /\ exists z, z \in y /\ R x z).
assert (Pm : forall x x', x \in A -> x == x' -> forall y y', y == y' -> P x y -> P x' y').
 intros.
 destruct H4.
 destruct H5; destruct H5.
 split; [|exists x0;split].
  apply in_reg with x; trivial.

  apply eq_elim with y; trivial.

  apply H with x x0; trivial.
  apply eq_set_refl.
assert (Pwit : forall x, x \in A -> exists y, P x (V y)). 
 intros.
 destruct (H0 x); trivial.
 exists (singl x0); split; trivial.
 exists x0; split; trivial.
 apply V_sub with (V x0).
  apply V_mono; exists tt; apply eq_set_refl.
  apply V_intro.
destruct (@repl_ax A (fun x y => lst_rk (P x) y)); eauto using lst_fun, lst_ex.
 intros.
 apply lst_rk_morph with (P x) y; trivial.
 intros.
 split; intros; eauto.
  apply Pm with x' x'0; trivial.
   apply in_reg with x; trivial.
   apply eq_set_sym; trivial.
   apply eq_set_sym; trivial.

 exists (union x); intros.
 destruct lst_ex with (P x0); auto.
  apply Pm; trivial; apply eq_set_refl.

  specialize lst_incl with (1:=H3).
  destruct 1 as (_,(?,(?,?))).
  exists x2; split; trivial.
  rewrite union_ax.
  exists x1; trivial.
  rewrite H1.
  exists x0; auto.
Qed.

Lemma coll2_ax : forall A (R:set->set->Prop) x,
    (forall x x' y y', in_set x A ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (exists y, R x y) ->
    in_set x A ->
    exists B, exists y, in_set y B /\ R x y.
intros.
assert (forall z, z \in singl x -> z \in A).
 intros.
 destruct H2; simpl in *.
 apply in_reg with x; trivial.
 apply eq_set_sym; trivial.
destruct (coll_ax (singl x) R); intros; eauto.
 destruct H0.
 exists x1.
 apply H with x x1; trivial.
  destruct H3; simpl in *.
  apply eq_set_sym; trivial.

  apply eq_set_refl.

 exists x0.
 apply H3.
 exists tt; apply eq_set_refl.
Qed.
 
End FromReplClassic.

End Collection.


(* Infinity *)

Lemma infinity_ex: exists2 infinite,
    (exists2 empty, (forall x, ~ x \in empty) & empty \in infinite) &
    (forall x, x \in infinite ->
     exists2 y, (forall z, z \in y <-> (z == x \/ z \in x)) &
       y \in infinite).
exists infinity.
 exists empty.
  exact empty_ax.
  exact infty_ax1.

 intros.
 exists (union (pair x (pair x x))); intros.
  rewrite union_ax.
  split; intros.
   destruct H0.
   rewrite pair_ax in H1; destruct H1.
    right.
    unfold in_set.
    apply eq_elim with x0; trivial.

    left.
    specialize eq_elim with (1:=H0) (2:=H1); intro.
    rewrite pair_ax in H2; destruct H2; trivial.

   destruct H0.
    exists (pair x x).
     rewrite pair_ax; auto.

     rewrite pair_ax; right; apply eq_set_refl.

    exists x; trivial.
    rewrite pair_ax; left; apply eq_set_refl.

  apply infty_ax2; trivial.
Qed.


(* Rk: decision of membership implies excluded-middle *)
Lemma set_dec_EM :
  (forall x y, in_set x y \/ ~ in_set x y) ->
  (forall P, P \/ ~ P).
intros.
destruct (H empty (subset (power empty) (fun _ => P))).
 left.
 rewrite subset_ax in H0; destruct H0.
 destruct H1; trivial.
 right; red; intros; apply H0.
 rewrite subset_ax.
 split.
  rewrite power_ax; intros.
  elim empty_ax with y; trivial.

  exists empty; trivial.
  apply eq_set_refl.
Qed.

(* Failed attempt to build (set-theoretical) choice axiom. *)

Section Choice.

Hypothesis C : forall X:Type, X + (X->False).

Lemma impl_choice_ax : forall A B, choice A B.
red; intros.
exists (fun x =>
  match C ({y:B|R x y}) with
  | inl y => proj1_sig y
  | inr h =>
    False_rect B (let (y,r) := H x in h (exist _ y r))
  end).
intros.
destruct (C {y:B|R x y}).
 destruct s; trivial.

 destruct (H x).
 destruct (f (exist (fun y => R x y) x0 r)).
Qed.

Definition choose (x:set) :=
  match C (idx x) with
  | inl i => elts x i
  | _ => empty
  end.

Lemma choose_ax : forall a, (exists x, x \in a) -> choose a \in a.
intros.
unfold choose.
destruct (C (idx a)).
 exists i; apply eq_set_refl.

 destruct H.
 destruct H.
 elim (f x0).
Qed.

(* ... but choose is not a morphism! *)
Lemma choose_not_morph : ~ forall x x', x == x' -> choose x == choose x'.
unfold choose; red; intros.
generalize (H (sup bool (fun b => if b then empty else singl empty))
              (sup bool (fun b => if b then singl empty else empty))).
simpl; intros.
assert (singl empty == empty).
 refine (let H1 := H0 _ in _).
  split; intros.
   exists (negb i).
   destruct i; apply eq_set_refl.

   exists (negb j).
   destruct j; apply eq_set_refl.

  clear H0.
  destruct (C bool).
   destruct b; auto with *.
   apply eq_set_sym; trivial.

   destruct (f true).
elim empty_ax with empty.
apply eq_elim with (singl empty); trivial.
exists tt; apply eq_set_refl.
Qed.

End Choice.

(* Regularity is classical *)

Section Regularity.

Definition regularity :=
  forall a a0, a0 \in a ->
  exists2 b, b \in a & ~(exists2 c, c \in a & c \in b).

Lemma regularity_ax (EM:forall P,P\/~P): regularity.
red.
induction a0; intros.
destruct (EM (exists i:X, f i \in a)).
 destruct H1; eauto.

 exists (sup X f); trivial.
 red; intros; apply H1.
 destruct H2.
 destruct H3; simpl in *.
 exists x0.
 apply in_reg with x; trivial.
Qed.

Lemma regularity_is_classical (reg : regularity) : forall P, P \/ ~P.
intros.
destruct (reg (subset (pair empty (power empty))
           (fun x => x == power empty \/ x == empty /\ P)) (power empty)).
 rewrite subset_ax.
 split.
  rewrite pair_ax; right ;apply eq_set_refl.
  exists (power empty).
   apply eq_set_refl.
   left; apply eq_set_refl.

 rewrite subset_ax in H; destruct H.
 destruct H1.
 destruct H2.
  right ;red; intros.
  apply H0.
  exists empty.
   rewrite subset_ax.
   split.
    rewrite pair_ax; left; apply eq_set_refl.
    exists empty.
     apply eq_set_refl.
     right; split; trivial.
     apply eq_set_refl.

    apply eq_elim with x0.
    2:apply eq_set_sym; trivial.
    apply eq_elim with (power empty).
    2:apply eq_set_sym; trivial.
    rewrite power_ax; trivial.

  destruct H2; auto.
Qed.

End Regularity.

End IZF_R.
