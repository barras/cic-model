Require Export basic.
Require Import Choice. (* Axiom *)
Require Import Sublogic.

(** In this file, we build a model of both intuitionistic and
   classical ZF in Coq extended with the Type-Theoretical Collection
   Axiom (TTColl).
 *)

Module Ensembles (L:Sublogic).

Module Lthms := BuildLogic L.
Export L Lthms.

(** The level of sets *)
Definition Thi := Type.

(** The level of indexes *)
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
  (forall i, Tr(exists j, eq_set (elts x i) (elts y j))) /\
  (forall j, Tr(exists i, eq_set (elts x i) (elts y j))).

Lemma eq_set_def x y :
  eq_set x y <->
  (forall i, Tr(exists j, eq_set (elts x i) (elts y j))) /\
  (forall j, Tr(exists i, eq_set (elts x i) (elts y j))).
destruct x; destruct y; simpl; intros.
reflexivity.
Qed.

Lemma eqset_isL : forall x y, isL(eq_set x y).
intros; rewrite eq_set_def; auto.
Qed.
Global Hint Resolve eqset_isL.

Lemma eq_set_intro x y :
  (forall i, exists j, eq_set (elts x i) (elts y j)) ->
  (forall j, exists i, eq_set (elts x i) (elts y j)) ->
  eq_set x y.
intros.
rewrite eq_set_def; split; intros; Tin; auto.
Qed.

Lemma eq_set_refl : forall x, eq_set x x.
induction x.
apply eq_set_intro; simpl; intros i; exists i; trivial.
Qed.

Lemma eq_set_sym : forall x y,
  eq_set x y -> eq_set y x.
induction x; intros.
rewrite eq_set_def in H0|-*.
destruct H0; split; intros i.
 Tdestruct (H1 i).
 Texists x; auto.

 Tdestruct (H0 i).
 Texists x; auto.
Qed.

Lemma eq_set_trans : forall x y z,
  eq_set x y -> eq_set y z -> eq_set x z.
induction x; destruct y; destruct z; intros.
rewrite eq_set_def in H0,H1|-*.
destruct H0; destruct H1; split; intros i.
 Tdestruct (H0 i).
 Tdestruct (H1 x).
 Texists x0; eauto.

 Tdestruct (H3 i).
 Tdestruct (H2 x).
 Texists x0; eauto.
Qed.

Definition in_set x y :=
  Tr(exists j, eq_set x (elts y j)).

Lemma inset_isL : forall x y, isL (in_set x y).
intros; apply Tr_isL.
Qed.
Global Hint Resolve inset_isL.

Notation "x \in y" := (in_set x y) (at level 60).
Notation "x == y" := (eq_set x y) (at level 70).

Lemma eq_set_ax : forall x y,
  x == y <-> (forall z, z \in x <-> z \in y).
intros.
rewrite eq_set_def.
split; intros.
 destruct H; split; intros.
  Tdestruct H1.
  Tdestruct (H x0).
  Texists x1.
  apply eq_set_trans with (elts x x0); trivial.

  Tdestruct H1.
  Tdestruct (H0 x0).
  Texists x1.
  apply eq_set_trans with (elts y x0); trivial.
  apply eq_set_sym; trivial.

 split; intros.
  apply H.
  Texists i; apply eq_set_refl.

  assert (elts y j \in y).
   Texists j; apply eq_set_refl.
  apply H in H0.
  Tdestruct H0; intros.
  Texists x0.
  apply eq_set_sym; trivial.
Qed.

Lemma in_reg : forall x x' y,
  x == x' -> x \in y -> x' \in y.
intros.
Tdestruct H0.
Texists x0.
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

Instance in_set_morph : Proper (eq_set ==> eq_set ==> iff) in_set.
do 3 red; intros.
split; intros.
 apply in_reg with x; trivial.
 apply eq_elim with x0; trivial.

 apply eq_set_sym in H.
 apply eq_set_sym in H0.
 apply in_reg with y; trivial.
 apply eq_elim with y0; trivial.
Qed.

Definition elts' (x:set) (i:idx x) : {y|y \in x}.
exists (elts x i).
abstract (Texists i; apply eq_set_refl).
Defined.

Lemma eq_elim1 x y :
  {z|z \in x} -> x == y -> {z|z \in y}.
intros z eqxy.
exists (proj1_sig z).
apply eq_elim with x; trivial.
apply proj2_sig.
Defined.

Lemma incl_elim1 x y :
  {z|z \in x} -> (forall z, z \in x -> z \in y) -> {z|z \in y}.
intros z eqxy.
exists (proj1_sig z).
apply eqxy.
apply proj2_sig.
Defined.

(** Set induction *)
(*
Fixpoint isWf x := Forall(fun i => isWf (elts x i)).

Lemma set_isWf x : holds (isWf x).
induction x; simpl.
rewrite rForall; trivial.
Qed.
*)
Lemma wf_ax :
  forall (P:set->Prop),
  (forall x, isL (P x)) ->
  (forall x, (forall y, y \in x -> P y) -> P x) ->
  forall x, P x.
intros P isLP H x.
cut (forall x', x == x' -> P x');[auto using eq_set_refl|].
induction x; intros.
apply H; intros.
apply eq_set_sym in H1.
apply eq_elim with (2:=H1) in H2.
Tdestruct H2.
apply H0 with x.
apply eq_set_sym; trivial.
Qed.

(***********************************************************)
(** Empty set *)

Definition empty :=
  sup False (fun x => match x with end).

Lemma empty_ax : forall x, x \in empty -> Tr False.
red; intros.
Tdestruct H.
Tin; trivial.
Qed.

(** Singleton and pairs *)

Definition singl x := sup unit (fun _ => x).

Definition pair x y :=
  sup bool (fun b => if b then x else y).

Lemma pair_ax : forall a b z,
  z \in pair a b <-> Tr(z == a \/ z == b).
split; intros.
 Tdestruct H.
 Tin; destruct x; auto.

 Tdestruct H.
  Texists true; trivial.
  Texists false; trivial.
Qed.

Lemma pair_morph :
  forall a a', a == a' -> forall b b', b == b' ->
  pair a b == pair a' b'.
intros.
rewrite eq_set_ax; intros.
do 2 rewrite pair_ax.
split; intros.
 Tdestruct H1.
  Tleft; apply eq_set_trans with a; trivial.
  Tright; apply eq_set_trans with b; trivial.

 apply eq_set_sym in H.
 apply eq_set_sym in H0.
 Tdestruct H1.
  Tleft; apply eq_set_trans with a'; trivial.
  Tright; apply eq_set_trans with b'; trivial.
Qed.

(** Union *)

Definition union (x:set) :=
  sup {i:idx x & idx (elts x i)}
    (fun p => elts (elts x (projS1 p)) (projS2 p)).

Lemma union_ax : forall a z,
  z \in union a <-> Tr(exists2 b, z \in b & b \in a).
split; intros.
 Tdestruct H.
 destruct x; simpl in *.
 Texists (elts a x).
  Texists i; trivial.

  Texists x; apply eq_set_refl.

 Tdestruct H.
 Tdestruct H0.
 specialize eq_elim with (1:=H) (2:=H0); intro.
 Tdestruct H1.
 Texists (existT (fun _=>_) x0 x1); simpl; trivial.
Qed.

Lemma union_morph :
  forall a a', a == a' -> union a == union a'.
intros.
rewrite eq_set_ax; intros.
rewrite union_ax; rewrite union_ax.
split; intros.
 Tdestruct H0.
 Texists x; trivial.
 apply eq_elim with a; trivial.

 apply eq_set_sym in H.
 Tdestruct H0.
 Texists x; trivial.
 apply eq_elim with a'; trivial.
Qed.

(** Separation axiom *)

Definition subset (x:set) (P:set->Prop) :=
  sup {a|Tr(exists2 x', elts x a == x' & P x')}
    (fun y => elts x (proj1_sig y)).

Lemma subset_ax : forall x P z,
  z \in subset x P <->
  z \in x /\ Tr(exists2 z', z == z' & P z').
intros x P z.
split; intros.
 Tdestruct H.
 destruct x0; simpl in *.
 split.
  Texists x0; trivial.

  Tdestruct t.
  Texists x1; trivial.
  apply eq_set_trans with (elts x x0); trivial.

 destruct H.
 Tdestruct H0.
 Tdestruct H.
 assert (Tr(exists2 x', elts x x1 == x' & P x')).
  Texists x0; trivial.
  apply eq_set_trans with z; trivial.
  apply eq_set_sym; trivial.
 Texists (exist (fun i =>Tr(exists2 x', elts x i == x' & P x'))
           x1 H2); simpl; trivial.
Qed.

(** Power-set axiom *)

Definition power (x:set) :=
  sup (idx x->Prop)
   (fun P => subset x
         (fun y => Tr(exists2 i, y == elts x i & P i))).

Lemma power_ax : forall x z,
  z \in power x <->
  (forall y, y \in z -> y \in x).
split; intros.
 Tdestruct H.
 specialize eq_elim with (1:=H0)(2:=H); intro.
 simpl in H1; rewrite subset_ax in H1.
 destruct H1; trivial.

 Texists (fun i => elts x i \in z).
 apply eq_intro; intros.
  simpl; rewrite subset_ax.
  split; auto.
  Texists z0;[apply eq_set_refl|].
  specialize H with (1:=H0).
  Tdestruct H.
  Texists x0; trivial.
  apply in_reg with z0; trivial.

  simpl in H0; rewrite subset_ax in H0.
  destruct H0.
  Tdestruct H1.
  Tdestruct H2.
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

(** Infinity *)

Fixpoint num (n:nat) : set :=
  match n with
  | 0 => empty
  | S k => union (pair (num k) (pair (num k) (num k)))
  end.

Definition infinity := sup _ num.

Lemma infty_ax1 : empty \in infinity.
Texists 0.
apply eq_set_refl.
Qed.

Lemma infty_ax2 : forall x, x \in infinity ->
  union (pair x (pair x x)) \in infinity.
intros.
Tdestruct H.
Texists (S x0); simpl elts.
apply union_morph.
apply pair_morph; trivial.
apply pair_morph; trivial.
Qed.


(** Functional Replacement *)

Definition replf (x:set) (F:set->set) :=
  sup _ (fun i => F (elts x i)).

Lemma replf_ax : forall x F z,
  (forall z z', z \in x -> z == z' -> F z == F z') ->
  (z \in replf x F <->
   Tr(exists2 y, y \in x & z == F y)).
split; intros.
 Tdestruct H0.
 Texists (elts x x0); trivial.
 Texists x0; apply eq_set_refl.

 Tdestruct H0.
 assert (h:=H0); Tdestruct h.
 Texists x1.
 apply eq_set_trans with (F x0); trivial.
 apply H; trivial.
Qed.

(** Functional replacement with domain information *)

Definition repl1 (x:set) (F:{y|y \in x}->set) :=
  sup _ (fun i => F (elts' x i)).

Lemma repl1_ax : forall x F z,
  (forall z z', proj1_sig z == proj1_sig z' -> F z == F z') ->
  (z \in repl1 x F <-> Tr(exists y, z == F y)).
split; intros.
 Tdestruct H0.
 Texists (elts' x x0); trivial.

 Tdestruct H0.
 destruct x0.
 Tdestruct i.
 Texists x1.
 apply eq_set_trans with (1:=H0).
 apply H; trivial.
Qed.

Lemma repl1_mono x y F G :
  (forall z, z \in x -> z \in y) ->
  (forall x' y', proj1_sig x' == proj1_sig y' -> F x' == G y') ->
  (forall z, z \in repl1 x F -> z \in repl1 y G).
intros inclxy eqFG.
assert (forall x' y', proj1_sig x' == proj1_sig y' -> F x' == F y').
 intros z z' eqz.
 apply eq_set_trans with (G (incl_elim1 _ _ z' inclxy)).
  apply eqFG; simpl; trivial.

  apply eq_set_sym; apply eqFG; simpl; apply eq_set_refl.
intros.
rewrite repl1_ax in H0; trivial.
Tdestruct H0 as (w,e).
Tdestruct (inclxy _ (proj2_sig w)) as (j, e').
Texists j; simpl.
apply eq_set_trans with (1:=e).
apply eqFG; simpl; trivial.
Qed.

Lemma repl1_morph : forall x y F G,
  x == y ->
  (forall x' y', proj1_sig x' == proj1_sig y' -> F x' == G y') ->
  repl1 x F == repl1 y G.
intros; rewrite eq_set_ax; split; apply repl1_mono; intros; auto.
 apply eq_elim with x; trivial.

 apply eq_elim with y; trivial.
 apply eq_set_sym; trivial.

 apply eq_set_sym; apply H0.
 apply eq_set_sym; trivial.
Qed.

(** Relational replacement *)

(** We only use the following instance of unique choice for
   replacement: *)
Definition ttrepl :=
  forall X:Tlo, unique_choice X set eq_set.

(** We show it is a consequence of [choice]. *)
Lemma ttrepl_axiom : ttrepl.
red; red; intros; apply choice_axiom; trivial.
Qed.

Section NotClassical.

(** This does not work in classial logic... *)
Hypothesis intuit : forall P:Prop, Tr P -> P.

Lemma intuit_repl_ax a (R:set->set->Prop) :
    (forall x x' y y', x \in a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x \in a -> R x y -> R x y' -> y == y') ->
    exists b, forall x, x \in b <-> Tr(exists2 y, y \in a & R y x).
intros.
destruct (ttrepl_axiom {i:idx a|Tr(exists y, R (elts a i) y)}
        (fun i y => Tr(R (elts a (proj1_sig i)) y))) as (f,?); intros.
 destruct x as (i,?); simpl. 
 set (x:=elts a i) in t.
 apply (intuit (exists y, R x y)) in t. (* We use only this instance of intuit *)
 destruct t; subst x; eauto using TrI.

 Telim H1; intro.
 split; intros.
  Telim H2; intro H2.
  apply H0 with (elts a (proj1_sig x)); trivial.
  Texists (proj1_sig x); apply eq_set_refl.

  Tin; revert H1; apply H; trivial.
   Texists (proj1_sig x); apply eq_set_refl.

   apply eq_set_refl.

exists (sup _ f).
unfold in_set at 1; simpl.
split; intros.
 Tdestruct H2 as (j,?).
 Telim (H1 j); intro.
 Texists (elts a (proj1_sig j)).
  apply (proj2_sig (elts' a (proj1_sig j))).

  revert H3; apply H.
   apply (proj2_sig (elts' a (proj1_sig j))).

   apply eq_set_refl.

   apply eq_set_sym; trivial.

  Tdestruct H2.
  assert (h:=H2); Tdestruct h as (i,?).
  assert (R (elts a i) x).
   revert H3; apply H; trivial.
   apply eq_set_refl.
  Texists (exist (fun _ => _) i (TrI (ex_intro (fun _ => _) x H5))).
  Telim (H1 (exist (fun _ => _) i (TrI (ex_intro (fun _ => _) x H5)))); simpl; intro.
  apply H0 with (elts a i); trivial.
  Texists i; apply eq_set_refl.
Qed.
End NotClassical.


(** Collection *)

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
Lemma collection_ax : forall A (R:set->set->Prop), 
    (forall x x' y y', x \in A -> x == x' -> y == y' ->
     R x y -> R x' y') ->
    exists B, forall x, x \in A ->
      Tr (exists y, R x y) ->
      Tr (exists2 y, y \in B & R x y).
intros.
destruct ttcoll_set with A (fun x y => R x y) as (B,HB).
exists B; intros x inA H0.
Tdestruct H0 as (w, Rxw).
assert (h:=inA); Tdestruct h as (i, eqx).
assert (R (elts A i) w).
 apply H with (4:=Rxw); trivial.
 apply eq_set_refl.
destruct (HB i) as (j,Rxy).
 exists w; trivial.

 Texists (elts B j).
  apply (proj2_sig (elts' B j)).

  apply H with (4:=Rxy).
   apply in_reg with x; trivial.

   apply eq_set_sym; trivial.

   apply eq_set_refl.
Qed.

Lemma collection_ax' : forall A (R:set->set->Prop), 
    (forall x x' y y', x \in A -> x == x' -> y == y' ->
     R x y -> R x' y') ->
    (forall x, x \in A -> Tr(exists y, R x y)) ->
    exists B, forall x, x \in A -> Tr(exists2 y, y \in B & R x y).
intros.
destruct collection_ax with (A:=A)(R:=R) as (B,HB); trivial.
exists B; auto.
Qed.

(** Comparison of replacement and collection *)

(** TTColl is stronger than TTRepl *)
Lemma ttrepl_from_ttcoll : ttrepl.
red; red; intros.
destruct (ttcoll X R) as (Y,(g,HB)).
exists (fun i => union (subset (sup Y g) (fun y => R i y))).
intros i.
destruct (H i) as (y,Hy).
assert (y == union (subset (sup Y g) (fun y => R i y))).
 apply eq_intro; intros.
  rewrite union_ax.
  Texists y; trivial.
  rewrite subset_ax.
  split.
   destruct HB with i as (j,?); trivial.
   Texists j; simpl.
   apply H0 with i; trivial.

   Texists y; trivial.
   apply eq_set_refl.

 rewrite union_ax in H1.
 Tdestruct H1 as (b, ?, ?).
 rewrite subset_ax in H2; destruct H2.
 Tdestruct H3 as (b', ?, ?).
 apply eq_elim with b; trivial.
 apply eq_set_trans with b'; trivial.
 apply H0 with i; trivial.
apply H0 with y; trivial.
Qed.

(* Replacement as a weaker form of collection.
   This is stronger than combining the previous lemma with intuit_repl_ax because
   we would need to be intuitionistic
 *)

Lemma repl_ax_from_collection : forall a (R:set->set->Prop),
    (forall x x' y y', x \in a -> R x y -> R x' y' -> x == x' -> y == y') ->
    exists b, forall x, x \in b <-> Tr(exists2 y, y \in a & Tr(exists2 x', x == x' & R y x')).
intros a R Rfun.
destruct collection_ax with (A:=a)
  (R:=fun x y => Tr(exists2 x', x==x' & Tr(exists2 y', y==y' & R x' y'))) as (B,HB).
 intros.
 Tdestruct H2 as (x'',H2,H3).
 Tdestruct H3 as (y'',H3,H4).
 Texists x''.
  apply eq_set_trans with x; trivial.
  apply eq_set_sym; trivial.
 Texists y'';  trivial.
 apply eq_set_trans with y; trivial.
 apply eq_set_sym; trivial.
exists (subset B (fun y => Tr(exists2 x, x \in a & R x y))); split; intros.
 rewrite subset_ax in H; destruct H.
 Tdestruct H0 as (y,?,?).
 Tdestruct H1 as (x',?,?).
 Texists x'; trivial.
 Texists y; auto.

 Tdestruct H as (x',?,?).
 Tdestruct H0 as (y,?,?).
 rewrite subset_ax; split.
  elim HB with x' using Tr_ind; clear HB; trivial.
   intros (y',?,?).
   Tdestruct H3 as (x'',?,?).
   Tdestruct H4 as (y'',?,?).
   apply in_reg with y'; trivial.
   apply eq_set_trans with y''; trivial.
   apply eq_set_trans with y;[|apply eq_set_sym; trivial].
   apply Rfun with x'' x'; trivial.
    apply in_reg with x'; trivial.
    apply eq_set_sym; trivial.

   Texists y.
   Texists x'; [apply eq_set_refl|].
   Texists y; auto using eq_set_refl.

 Texists y; trivial.
 Texists x'; auto.
Qed.

(* *)
Lemma ttrepl_needed_for_replacement : ttrepl.
red; red; intros.
assert (exists2 a, X = idx a & forall i i', elts a i == elts a i' -> i=i') by admit.
destruct H1 as (a,?,elinj); subst X.
destruct repl_ax_from_collection with
  (a:=a) (R:=fun x y => exists2 i, x == elts a i & exists2 y', y == y' & R i y').
 intros.
 destruct H2 as (i,?,(z,?,?)).
 destruct H3 as (i',?,(z',?,?)).
 apply eq_set_trans with z; trivial.
 apply eq_set_trans with z'.
  2:apply eq_set_sym; trivial.
 assert (elts a i == elts a i').
  apply eq_set_trans with x; [apply eq_set_sym; trivial|].
  apply eq_set_trans with x'; trivial.
 apply elinj in H9.
 apply H0 with i'; trivial.
 subst i'; trivial.

 exists (fun y => union (subset x (fun z => R y z))).
 intro.
 destruct H with x0.
 apply H0 with x1; trivial.
 apply eq_set_ax; split; intros.
  rewrite union_ax.
  Texists x1; trivial.
  rewrite subset_ax.
  split.
   rewrite H1.
   Texists (elts a x0).
    Texists x0; apply eq_set_refl.
   Texists x1;[apply eq_set_refl|].
   exists x0;[apply eq_set_refl|].
   exists x1; trivial.
   apply eq_set_refl.

   Texists x1; trivial.
   apply eq_set_refl.

  rewrite union_ax in H3.
  Tdestruct H3.
  rewrite subset_ax in H4; destruct H4.
  Tdestruct H5.
  apply eq_elim with x2; trivial.
  apply eq_set_trans with x3; trivial.
  apply H0 with x0; trivial.
Qed.


Definition repl_ex := repl_ax_from_collection.

(* Deriving the existentially quantified sets *)

Lemma empty_ex: Tr(exists empty, forall x, x \in empty -> Tr False).
Texists empty.
exact empty_ax.
Qed.

Lemma pair_ex: forall a b,
  Tr(exists c, forall x, x \in c <-> Tr(x == a \/ x == b)).
intros.
Texists (pair a b).
apply pair_ax.
Qed.

Lemma union_ex: forall a, Tr(exists b,
    forall x, x \in b <-> Tr(exists2 y, x \in y & y \in a)).
intros.
Texists (union a).
apply union_ax.
Qed.

Lemma subset_ex : forall a P, Tr(exists b,
    forall x, x \in b <-> x \in a /\ Tr(exists2 x', x == x' & P x')).
intros.
Texists (subset a P).
apply subset_ax.
Qed.

Lemma power_ex: forall a, Tr(exists b,
     forall x, x \in b <-> (forall y, y \in x -> y \in a)).
intros.
Texists (power a).
apply power_ax.
Qed.

(* Infinity *)

Lemma infinity_ex: Tr(exists2 infinite,
    (Tr(exists2 empty, (forall x, x \in empty -> Tr False) & empty \in infinite)) &
    (forall x, x \in infinite ->
     Tr(exists2 y,
       (forall z, z \in y <-> Tr(z == x \/ z \in x)) &
       y \in infinite))).
Texists infinity.
 Texists empty.
  exact empty_ax.
  exact infty_ax1.

 intros.
 Texists (union (pair x (pair x x))); intros.
  rewrite union_ax.
  split; intros.
   Tdestruct H0.
   rewrite pair_ax in H1.
   Tdestruct H1.
    Tright; apply eq_elim with x0; trivial.

    specialize eq_elim with (1:=H0) (2:=H1); intro.
    rewrite pair_ax in H2.
    Tdestruct H2; Tin; auto.

   Tdestruct H0.
    Texists (pair x x).
     rewrite pair_ax; Tleft; auto.

     rewrite pair_ax; Tright; apply eq_set_refl.

    Texists x; trivial.
    rewrite pair_ax; Tleft; apply eq_set_refl.

  apply infty_ax2; trivial.
Qed.

(** Fixpoint *)
Fixpoint wfrec (F:(set->set)->set->set) (x:set) : set :=
  F (fun y => union (sup {i:idx x|elts x i == y}
               (fun i => wfrec F (elts x (proj1_sig i))))) x.
Section FixRec.
Hypothesis F : (set->set)->set->set.
Hypothesis Fext : forall x x' f f',
  (forall y y', y \in x -> y == y' -> f y == f' y') ->
  x == x' ->
  F f x == F f' x'.

Instance wfrecm : Proper (eq_set==>eq_set) (wfrec F).
do 2 red; intros x x'; revert x'.
induction x; destruct x' as (Y,g); intros.
simpl wfrec.
apply Fext; trivial.
rewrite eq_set_def in H0; simpl in H0; destruct H0.
intros.
apply union_morph.
rewrite eq_set_def; simpl idx; simpl elts; split; intros (i,e); simpl proj1_sig.
 clear H2.
 Tdestruct (H0 i) as (j,?).
 assert (e' : g j == y').
  apply eq_set_trans with y; trivial.
  apply eq_set_trans with (f i); trivial.
  apply eq_set_sym; trivial.
 Texists (exist (fun j => g j == y') j e'); simpl; auto.

 Tdestruct H2 as (j,H2); simpl in j,H2.
 apply eq_set_sym in H2.
 Texists (exist (fun i => f i == y) j H2); simpl.
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
 Tdestruct H1 as (b,?,?).
 Tdestruct H2 as ((j,e), ?).
 simpl in H2.
 apply eq_elim with b; trivial.
 apply eq_set_trans with (1:=H2).
 apply wfrecm.
 apply eq_set_trans with y; trivial.

 Tdestruct H as (i,H).
 apply eq_set_sym in H0.
 Texists (wfrec F (f i)).
  apply eq_elim with (1:=H1).
  apply wfrecm.
  apply eq_set_trans with y; trivial.

  apply eq_set_sym in H.
  Texists (exist (fun i => (f i == y)) i H).
  simpl.
  apply eq_set_refl.
Qed.

End FixRec.


(** Showing that in classical logic, collection can be made
   deterministic, by building the smallest element of
   Veblen hierarchy containing the images *)

Section ClassicalCollection.

(** Veblen cumulative hierarchy (applied to any set) *)
Fixpoint V (x:set) := union (replf x (fun x' => power (V x'))).

Lemma V_morph : forall x x', x == x' -> V x == V x'.
induction x; destruct x'; intros.
simpl V; unfold replf; simpl sup.
apply union_morph.
rewrite eq_set_def in H0; simpl in H0.
destruct H0.
apply eq_intro; intros.
 Tdestruct H2.
 Tdestruct (H0 x).
 Texists x0; simpl.
 apply eq_set_trans with (1:=H2).
 apply power_morph.
 auto.

 Tdestruct H2.
 Tdestruct (H1 x).
 simpl in *.
 Texists x0; simpl.
 apply eq_set_trans with (1:=H2).
 apply eq_set_sym.
 apply power_morph.
 auto.
Qed.

Lemma V_def : forall x z,
  z \in V x <-> Tr(exists2 y, y \in x & z \in power (V y)).
destruct x; simpl; intros.
rewrite union_ax.
unfold replf; simpl.
split; intros.
 Tdestruct H.
 Tdestruct H0; simpl in *.
 Texists (f x0).
  Texists x0; apply eq_set_refl.

  specialize eq_elim with (1:=H) (2:=H0); intro; trivial.

 Tdestruct H.
 Tdestruct H; simpl in *.
 Texists (power (V x)); trivial.
 Texists x0; simpl elts.
 apply power_morph.
 apply V_morph; trivial.
Qed.


Lemma V_trans : forall x y z,
  z \in y -> y \in V x -> z \in V x.
intros x.
apply wf_ax with (x:=x); auto.
clear x; intros.
rewrite V_def in H1|-*.
Tdestruct H1.
Texists x0; trivial.
rewrite power_ax in H2|-*; eauto.
Qed.

Lemma V_pow : forall x, power (V x) == V (singl x).
intros.
apply eq_intro; intros.
 rewrite V_def.
 Texists x; trivial.
 Texists tt; apply eq_set_refl.

 rewrite V_def in H.
 Tdestruct H.
 Tdestruct H; simpl in *.
 apply eq_elim with (power (V x0)); auto.
 apply power_morph.
 apply V_morph; trivial.
Qed.

Lemma V_mono : forall x x',
  x \in x' -> V x \in V x'.
intros.
rewrite (V_def x').
Texists x; trivial.
rewrite power_ax; auto.
Qed.

Lemma V_sub : forall x y y',
  y \in V x -> y' \in power y -> y' \in V x.
intros.
rewrite V_def in H|-*.
Tdestruct H.
Texists x0; trivial.
rewrite power_ax in H0,H1|-*; auto.
Qed.

Lemma V_compl : forall x z, z \in V x <-> V z \in V x. 
intros x.
pattern x; apply wf_ax; clear x; intros; auto.
repeat rewrite V_def.
split; intros.
 Tdestruct H0.
 Texists x0; trivial.
 rewrite power_ax in H1|-*; intros.
 rewrite V_def in H2.
 Tdestruct H2.
 apply H1 in H2.
 rewrite H in H2; trivial.
 apply V_sub with (V x1); trivial.

 Tdestruct H0.
 Texists x0; trivial.
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
 Tdestruct H.
 apply V_sub with (V x0); trivial.
 rewrite <- V_compl; trivial.

 apply V_sub with (V z).
  apply V_mono; trivial.
  apply V_intro.
Qed.

Lemma rk_induc :
  forall P:set->Prop,
  (forall x, isL (P x)) ->
  (forall x, (forall y, y \in V x -> P y) -> P x) ->
  forall x, P x.
intros.
cut (forall y, V y \in power (V x) -> P y).
 intros.
 apply H1.
 rewrite power_ax; auto.
apply wf_ax with (x:=x); intros; auto.
apply H0; intros.
rewrite power_ax in H2; specialize H2 with (1:=H3).
rewrite V_def in H2.
Tdestruct H2.
apply H1 with x1; trivial.
apply V_comp2; trivial.
Qed.

Hypothesis EM : forall A, Tr(A \/ (A->Tr False)).

(** Classical proof that the rank of a set is totally ordered *)
Lemma V_total : forall x y, Tr(V x \in V y \/ V y \in power (V x)).
intros x y.
revert x.
apply wf_ax with (x:=y); clear y; auto.
intros y Hy x.
Tdestruct (EM (Tr(exists2 y', y' \in V y & V x \in power y'))).
 Tleft.
 Tdestruct H.
 apply V_sub with x0; trivial.

 Tright; rewrite power_ax; intros.
 rewrite V_def in H0.
 Tdestruct H0.
 assert (Tr(exists2 w, w \in V x & w \in V x0 -> Tr False)).
  Tdestruct (EM (Tr(exists2 w, w \in V x & w \in V x0 -> Tr False))); trivial.
  assert (V x \in power (V x0) -> Tr False).
   intros; apply H.
   Texists (V x0); trivial.
   apply V_mono; trivial.
  Tabsurd; apply H3; rewrite power_ax; intros.
  Tdestruct (EM (y1 \in V x0)); trivial.
  Tabsurd; apply H2.
  Texists y1; trivial.
 Tdestruct H2.
 Tdestruct (Hy _ H0 x1).
  Tabsurd; apply H3.
  apply V_sub with (V x1); trivial.
  apply V_intro.

  apply V_sub with (V x1).
   apply -> V_compl; trivial.

   rewrite power_ax in H1,H4|-*; auto.
Qed.

Definition lst_rk (P:set->Prop) (y:set) :=
  P y /\
  y == V y /\
  forall x, x == V x -> P x -> y \in power(V x).

(*
Lemma lst_rk_isL P y : (forall x, isL (P x)) -> isL (lst_rk P y).
unfold lst_rk; auto 10.
Qed.
Global Hint Resolve lst_rk_isL.
*)

Lemma lst_rk_morph :
  forall (P P':set->Prop),
  (forall x x', x == x' -> (P x <-> P' x')) ->
  forall y y', y == y' -> lst_rk P y -> lst_rk P' y'.
intros.
unfold lst_rk in H1|-*.
destruct H1.
destruct H2.
split; [|split].
 revert H1; apply H; trivial.

 apply eq_set_trans with y;[apply eq_set_sym; trivial|].
 apply eq_set_trans with (V y); trivial.
 apply V_morph; trivial.

 intros.
 apply in_reg with y; trivial.
 apply H3; trivial.
 revert H5; apply H.
 apply eq_set_refl.
Qed.

Lemma lst_incl : forall P y, lst_rk P y -> P y. 
intros.
destruct H as (?,_); trivial.
Qed.

Lemma lst_fun : forall P y y', lst_rk P y -> lst_rk P y' -> y == y'.
unfold lst_rk; intros.
destruct H as (p1,(ex1,lst1)); destruct H0 as (p2,(ex2,lst2)).
specialize lst1 with (1:=ex2) (2:=p2).
specialize lst2 with (1:=ex1) (2:=p1).
apply eq_set_trans with (V y); trivial.
apply eq_set_trans with (V y');[|apply eq_set_sym; trivial].
apply V_comp2 in lst1.
apply V_comp2 in lst2.
rewrite power_ax in lst1, lst2.
apply eq_intro; intros; auto.
Qed.

(** Proof that if P is true for some Veblen universe, then
    we can find the least rank satisfying P. *)
Lemma lst_ex : forall (P:set->Prop),
  Proper (eq_set==>iff) P ->
  Tr(exists x, P (V x)) ->
  Tr(exists x, lst_rk P x).
intros P Pm Pex.
Telim Pex; destruct 1.
revert H; apply rk_induc with (x:=x); clear x; intros; auto.
Tdestruct (EM (Tr(exists2 z, z \in V x & P (V z)))).
 Tdestruct H1; eauto.

 Texists (V x).
 unfold lst_rk; split; [|split]; trivial.
  apply eq_set_sym; apply V_idem.

  intros y ? ?.
  Tdestruct (V_total y x); auto.
  Tabsurd; apply H1.
  Texists y.
   apply in_reg with (V y); trivial.
   apply eq_set_sym; trivial.

   do 2 red in Pm.
   revert H3; apply -> Pm; trivial.
Qed.

Axiom nnpp : forall P, ((P->Tr False)->Tr False) -> P.
Lemma ttcoll_from_ttrepl_em (X:Tlo) (R:X->set->Prop):
  exists Y, exists g:Y->set,
    forall i, (exists w, R i w) -> exists j:Y, R i (g j).
intros.
pose (P i v := exists2 x, x \in v & R i x).
destruct (@ttrepl_axiom {i:X|exists y, R i y}
  (fun i y => lst_rk (P (proj1_sig i)) y)) as (f,?).
 destruct x as (i,?); simpl.
 assert (exists x, P i (V x)).
  destruct e.
  exists (singl x).
  red.
  exists x; trivial.
  apply eq_elim with (power (V x)).
   2:apply V_pow.
  apply V_intro.
 apply TrI in H.
 apply lst_ex in H.
  apply nnpp; intro.
  Tdestruct H.
  apply H0.
  exists x; trivial.

  do 2 red; intros.
  unfold P.
  apply ex2_morph; red; intros; auto with *.
  apply in_set_morph; [apply eq_set_refl|trivial].

 split; intros.
  apply lst_fun with (1:=H) (2:=H0).

  revert H; apply lst_rk_morph; intros; trivial.
  unfold P.
  apply ex2_morph; red; intros; auto with *.
  apply in_set_morph; [apply eq_set_refl|trivial].

(* main *)
pose (B := union (sup _ f)).
exists (idx B); exists (elts B).
intros.
specialize H with (exist (fun i => exists y, R i y) i H0); simpl in H.
apply lst_incl in H.
red in H.
destruct H.
assert (x \in B).
 simpl.
 unfold B; rewrite union_ax.
 Tin; econstructor;[eexact H|].
 Tin; econstructor; eapply eq_set_refl.
apply nnpp; intro.
Tdestruct H2 as (j,?).
apply H3; exists j.
admit. (* x == elts B j -> R i x -> R i (elts B j)...*)
Qed.

(*
Lemma coll_ax : forall A (R:set->set->Prop), 
    (forall x x' y y', in_set x A ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x, in_set x A -> exists y, R x y) ->
    exists B, forall x, in_set x A -> exists y, in_set y B /\ R x y.

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
*)

(* We could also try to prove that B grows when A and R do. *)
Lemma coll_ax_uniq : forall A (R:set->set->Prop), 
    (forall x x' y y', x \in A -> x == x' -> y == y' ->
     R x y -> R x' y') ->
    Tr(ex(lst_rk (fun B =>
      forall x, x \in A ->
      Tr(exists y, R x y) ->
      Tr(exists2 y, y \in B & R x y)))).
intros.
destruct collection_ax with (A:=A) (R:=R); trivial.
apply lst_ex.
 intros a a' eqa.
 apply fa_morph; intros x0.
 apply fa_morph; intros _.
 apply fa_morph; intros _.
 apply Tr_morph; apply ex2_morph; intros y; auto with *.
 apply in_set_morph; trivial.
 apply eq_set_refl.

 Texists x.
 intros a ? ?.
 apply H0 in H2; trivial.
 Tdestruct H2.
 Texists x0; trivial.
 apply V_mono in H2.
 apply V_sub with (V x0); trivial.
 apply V_intro.
Qed.

End ClassicalCollection.

End Ensembles.
