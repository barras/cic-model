Require Import ZFskol.
Require Import Sublogic.
(*Import CoqSublogicThms.*)

(*Set Printing Universes.*)

(* The level of sets *)
Definition Tj := Type.
(* The level of indices *)
Definition Ti : Tj := Type.

(******************************************************************************)
(** * The type of intensional sets *)

Module Zermelo (Import L:SublogicTheory) <: Zermelo_sig L.

  Inductive iset :=
    isup (X:Ti) (f:X->iset).
  Definition set := iset.

  Definition idx (x:set) := let (X,_) := x in X.
  Definition elts (x:set) : idx x -> set :=
  match x return idx x -> set with
  | isup X f => f
  end.

  Fixpoint eq_set (x y:set) {struct x} :=
  (forall i, #exists j, eq_set (elts x i) (elts y j)) /\
  (forall j, #exists i, eq_set (elts x i) (elts y j)).
  
  Instance eq_set_refl : Reflexive eq_set.
red; fix rfl 1.
intros (X,f); simpl.
split; intros.
 Texists i; apply rfl.
 Texists j; apply rfl.
Qed.

  Instance eq_set_sym : Symmetric eq_set.
red; fix sym 1.
intros (X,f) (Y,g); simpl.
destruct 1; split; intros.
 Tdestruct (H0 i) as (j,?).
 Texists j. 
 apply sym; assumption.

 Tdestruct (H j) as (i,?).
 Texists i. 
 apply sym; assumption.
Qed.

Instance eq_set_trans : Transitive eq_set.
red; fix trans 1.
intros (X,f) (Y,g) (Z,h) (xy,yx) (yz,zy); simpl.
split; intros.
 Tdestruct (xy i) as (j,?).
 Tdestruct (yz j) as (k,?).
 Texists k.
 apply trans with (g j); assumption.

 Tdestruct (zy j) as (k,?).
 Tdestruct (yx k) as (i,?).
 Texists i.
 apply trans with (g k); assumption.
Qed.


Lemma eq_set_isL x y : isL (eq_set x y).
destruct x; simpl; intros.
apply and_isL;(apply imp_isL || (apply fa_isL; intro)); prove_isL.
Qed.

Lemma eq_set_def : forall x y,
  (forall i, #exists j, eq_set (elts x i) (elts y j)) ->
  (forall j, #exists i, eq_set (elts x i) (elts y j)) ->
  eq_set x y.
destruct x; simpl; auto.
Qed.

Definition in_set x y :=
  #exists j, eq_set x (elts y j).


Lemma in_set_isL x y : isL (in_set x y).
unfold in_set; auto.
Qed.

Lemma in_set_ind P x y :
  isL P ->
  (forall j, eq_set x (elts y j) -> P) ->
  in_set x y -> P.
intros.
Tdestruct H1 as (i,?); eauto.
Qed.

  Definition incl_set x y := forall z, in_set z x -> in_set z y.

Lemma incl_set_isL x y : isL (incl_set x y).
apply fa_isL; auto using in_set_isL.
Qed.
Hint Resolve eq_set_isL incl_set_isL in_set_isL.


Lemma eq_elim0 x y i :
  eq_set x y ->
  in_set (elts x i) y.
destruct x; simpl; intros.
destruct H.
red; auto.
Qed.

Lemma eq_set_ax : forall x y,
  eq_set x y <-> (forall z, in_set z x <-> in_set z y).
unfold in_set; split; intros.
 split; intros h; Tdestruct h.
  elim (eq_elim0 x y x0) using in_set_ind; intros; auto.
  Texists j; apply eq_set_trans with (elts x x0); trivial.

  apply eq_set_sym in H.
  elim (eq_elim0 y x x0) using in_set_ind; intros; auto.
  Texists j; apply eq_set_trans with (elts y x0); trivial.

  apply eq_set_def; intros.
   apply H.
   Texists i; apply eq_set_refl.

   destruct (H (elts y j)).
   elim H1 using in_set_ind; intros; auto.
    Texists j0; apply eq_set_sym; trivial.

    Texists j; apply eq_set_refl.
Qed.

Definition elts' (x:set) (i:idx x) : {y|in_set y x}.
exists (elts x i).
abstract (Texists i; apply eq_set_refl).
Defined.

Lemma in_reg : forall x x' y,
  eq_set x x' -> in_set x y -> in_set x' y.
intros.
elim H0 using in_set_ind; intros; auto.
Texists j.
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

  Lemma wf_ax :
  forall (P:set->Prop),
  (forall x, (forall y, in_set y x -> #P y) -> #P x) -> forall x, #P x.
intros P H x.
cut (forall x', eq_set x x' -> #P x');[auto using eq_set_refl|].
induction x; intros.
apply H; intros.
assert (in_set y (isup X f)).
 apply eq_elim with x'; trivial.
 apply eq_set_sym; trivial.
clear H1 H2.
elim H3 using in_set_ind; intros; auto.
apply eq_set_sym in H1; eauto.
Qed.

Definition empty :=
  isup False (fun x => match x with end).

Lemma empty_ax : forall x, in_set x empty -> #False.
intros.
elim H using in_set_ind; intros; auto.
contradiction.
Qed.

Definition singl x := isup unit (fun _ => x).

Definition pair_spec (a b:set->Prop) (x:set) : Prop :=
  forall z, in_set z x <-> #(a z \/ b z).

Definition pair x y :=
  isup bool (fun b => if b then x else y).

Lemma pair_spec_intro a b :
  pair_spec (fun a' => eq_set a' a) (fun b' => eq_set b' b) (pair a b).
intros z.
unfold pair; simpl.
split; intros.
 elim H using in_set_ind; intros; auto.
 apply TrI.
 destruct j; auto.

 Tdestruct H.
  Texists true; trivial.
  Texists false; trivial.
Qed.

Lemma pair_ax : forall a b z,
  in_set z (pair a b) <-> #(eq_set z a \/ eq_set z b).
Proof pair_spec_intro.


Lemma pair_morph :
  forall a a', eq_set a a' -> forall b b', eq_set b b' ->
  eq_set (pair a b) (pair a' b').
unfold pair.
simpl; intros.
split; intros.
 Texists i; destruct i; trivial.
 Texists j; destruct j; trivial.
Qed.

Definition subset_spec (x:set) (P:set->Prop) (y:set) :=
  forall z,
  in_set z y <->
  in_set z x /\ # (exists2 z', eq_set z z' & P z').

Definition subset (x:set) (P:set->Prop) :=
  isup {a|exists2 x', eq_set (elts x a) x' & P x'}
    (fun y => elts x (proj1_sig y)).

Lemma subset_ax : forall x P, subset_spec x P (subset x P).
red.
unfold subset; simpl.
split; intros.
 elim H using in_set_ind; simpl; intros; auto.
 clear H; destruct j as (j,?); simpl in H0.
 split.
  Texists j; trivial.

  destruct e.
  Texists x0; trivial.
  apply eq_set_trans with (elts x j); trivial.

 destruct H.
 elim H using in_set_ind; auto.
 clear H; intros.
 Tdestruct H0.
 assert (exists2 x', eq_set (elts x j) x' & P x').
  exists x0; trivial.
  apply eq_set_trans with z; trivial.
  apply eq_set_sym; trivial.
 Texists (exist (fun a=>exists2 x',eq_set (elts x a) x' & P x') j H2); simpl; trivial.
Qed.

Definition power (x:set) :=
  isup (idx x->Prop)
   (fun P => subset x (fun y => exists2 i, eq_set y (elts x i) & P i)).

Lemma power_ax : forall x z,
  in_set z (power x) <->
  (forall y, in_set y z -> in_set y x).
unfold power; simpl; intros.
split; intros.
 elim H using in_set_ind; intros; auto.
 simpl in *.
 specialize eq_elim with (1:=H0)(2:=H1); intro.
 apply (proj1 (proj1 (subset_ax _ _ _) H2)).

 Texists (fun i => in_set (elts x i) z); simpl.
 apply eq_intro; intros.
  apply (fun x P z => proj2 (subset_ax x P z)).
  split; auto.
  elim H with z0 using in_set_ind; trivial; intros.
  Texists z0.
   apply eq_set_refl.

   exists j; trivial.
   apply in_reg with z0; trivial.

  Tdestruct (proj2 (proj1 (subset_ax _ _ _) H0)) as (z', ?, (i,?,?)).
  apply in_reg with (elts x i); trivial.
  apply eq_set_sym; apply eq_set_trans with z'; trivial.
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

  
 Definition union (x:set) :=
  isup {i:idx x & idx (elts x i)}
    (fun p => elts (elts x (projS1 p)) (projS2 p)).

Lemma union_ax : forall a z,
  in_set z (union a) <-> #exists2 b, in_set z b & in_set b a.
unfold in_set at 1, union; simpl; intros.
split; intros.
 Tdestruct H.
 Texists (elts a (projT1 x)).
  Texists (projT2 x); trivial.
  Texists (projT1 x); apply eq_set_refl.

 Tdestruct H.
 Tdestruct H0.
 assert (in_set z (elts a x0)).
  apply eq_elim with x; trivial.
 Tdestruct H1.
 Texists (existT (fun i=>idx(elts a i)) x0 x1); simpl.
 trivial.
Qed.

Lemma union_morph :
  forall a a', eq_set a a' -> eq_set (union a) (union a').
intros.
apply eq_set_ax; intros z.
rewrite union_ax.
rewrite union_ax.
split; intros h; Tdestruct h as (b,?,?); Texists b; trivial.
 apply eq_elim with a; trivial.
 apply eq_elim with a'; trivial.
 apply eq_set_sym; trivial.
Qed.


Fixpoint num (n:nat) : set :=
  match n with
  | 0 => empty
  | S k => union (pair (num k) (pair (num k) (num k)))
  end.

Definition infinite := isup _ num.

Lemma infinity_ax1 : in_set empty infinite.
 Texists 0.
 unfold elts, infinite, num.
 apply eq_set_refl.
Qed.

Lemma infinity_ax2 : forall x, in_set x infinite ->
  in_set (union (pair x (pair x x))) infinite.
intros.
elim H using in_set_ind; intros; auto.
Texists (S j).
simpl elts.
apply union_morph.
apply pair_morph; trivial.
apply pair_morph; trivial.
Qed.

Definition replf (x:set) (F:set->set) :=
  isup _ (fun i => F (elts x i)).

Lemma replf_ax : forall x F z,
  (forall z z', in_set z x ->
   eq_set z z' -> eq_set (F z) (F z')) ->
  (in_set z (replf x F) <->
   #exists2 y, in_set y x & eq_set z (F y)).
unfold replf; simpl; intros.
split; intros.
 elim H0 using in_set_ind; intros; auto.
 simpl in *.
 Texists (elts x j); trivial.
 Texists j; apply eq_set_refl.

 Tdestruct H0 as (x',?,?).
 elim H0 using in_set_ind; intros; auto.
 Texists j; simpl.
 apply eq_set_trans with (F x'); trivial.
 apply eq_set_sym.
 apply H.
  Texists j; apply eq_set_refl.
  apply eq_set_sym; trivial.
Qed.

End Zermelo.

