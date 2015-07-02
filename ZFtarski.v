Require Import ZF.

(** Fixpoint theorem about monotonic operators
 *)

(** * Construction of the fixpoint "from above" *)

Class inf_lattice (le : set->set->Prop) (inf : set -> set) := {
  lem :> Proper (eq_set==>eq_set==>iff) le;
  le_pre :> PreOrder le;
  le_anti : forall x y, le x y -> le y x -> x == y;
(*  infm : morph1 inf;*)
  inf_le : forall x z, z ∈ x -> le (inf x) z;
  inf_least : forall x w,
    (exists w0, w0 ∈ x) -> (forall z, z ∈ x -> le w z) -> le w (inf x)
}.

(** A is the top element of pA *)
Class rel_with_top (A pA:set) (le : set->set->Prop) :=
  is_powerA : forall x, le x A -> x ∈ pA.


(** The lattice of subsets *)

Instance inf_lattice_incl : inf_lattice incl_set inter.
split; auto with *; intros.
 apply incl_eq; trivial. 

 red; intros.
 apply inter_elim with x; trivial.

 red; intros.
 apply inter_intro; intros; trivial.
 apply H0; trivial.
Qed.

Instance incl_with_top A : rel_with_top A (power A) incl_set. 
intros x; apply power_intro.
Qed.
 
Section KnasterTarski.

Variable le : set -> set -> Prop.
Variable inf : set -> set.
Hypothesis ilat : inf_lattice le inf.
Infix "⊆" := le.

Variable A : set.
Variable pA : set.
Hypothesis topA : rel_with_top A pA le.

Let pA' := subset pA (fun x => x ⊆ A).
Let is_powerA' x : x ⊆ A <-> x ∈ pA'.
split; intros.
 apply subset_intro; trivial.
 apply is_powerA; trivial.

 apply subset_elim2 in H; destruct H.
 rewrite H; trivial.
Qed.

Let A_pA : A ∈ pA'.
apply is_powerA'; reflexivity.
Qed.

Variable F : set -> set.

Hypothesis Fmono : Proper (le==>le) F.
Hypothesis Ftyp : forall x, x ⊆ A -> F x ⊆ A.

Instance Fm : morph1 F.
do 2 red; intros.
apply le_anti; apply Fmono; rewrite H; reflexivity.
Qed.

Definition is_lfp x :=
  F x == x /\ forall y, (*y ⊆ A ->*) F y ⊆ y -> x ⊆ y.

Lemma lfp_elim x : is_lfp x -> F x == x.
intros h; apply h.
Qed.

Lemma is_lfp_unique x y :
  is_lfp x -> is_lfp y -> x == y.
intros.
apply le_anti.
 apply H.
 rewrite lfp_elim with (1:=H0); reflexivity.

 apply H0.
 rewrite lfp_elim with (1:=H); reflexivity.
Qed.

Definition pre_fix x := x ⊆ F x.
Definition post_fix x := F x ⊆ x.

Lemma post_fix_A : post_fix A.
red; intros.
apply Ftyp; auto with *.
Qed.

Definition M' := subset pA' post_fix.

Lemma member_A : A ∈ M'.
unfold M'.
apply subset_intro; trivial.
apply post_fix_A.
Qed.

Lemma post_fix1 x : x ∈ M' -> F x ⊆ x.
unfold M'; intros.
elim subset_elim2 with (1:=H); intros.
rewrite H0; trivial.
Qed.

Definition FIX := inf M'.

Lemma lfp_typ : FIX ⊆ A.
unfold FIX.
apply inf_le.
apply member_A.
Qed.

Lemma lower_bound x : x ∈ M' -> FIX ⊆ x.
unfold FIX, M'; intros.
apply inf_le; trivial.
Qed.

Lemma post_fix2 x : x ∈ M' -> F FIX ⊆ F x.
intros.
apply Fmono.
apply lower_bound; trivial.
Qed.


Lemma post_fix_lfp : post_fix FIX.
red.
unfold FIX.
apply inf_least; intros.
 exists A; apply member_A.
transitivity (F z).
 apply post_fix2; trivial.
 apply post_fix1; trivial.
Qed.

Lemma incl_f_lfp : F FIX ∈ M'.
unfold M'; intros.
apply subset_intro.
 apply is_powerA'.
 apply Ftyp.
 apply lfp_typ.

 red.
 apply Fmono.
 apply post_fix_lfp.
Qed.

Lemma FIX_eqn : F FIX == FIX.
apply le_anti.
 apply post_fix_lfp.

 apply lower_bound.
 apply incl_f_lfp.
Qed.

Lemma knaster_tarski : is_lfp FIX.
split.
 apply FIX_eqn.

 intros.
 transitivity (inf (pair y A)). 
 2:apply inf_le; apply pair_intro1.
 apply lower_bound.
 unfold M'.
 apply subset_intro; trivial.
  apply is_powerA'.
  apply inf_le; apply pair_intro2.

  red.
  apply inf_least; intros.
   exists y; apply pair_intro1.
  apply pair_elim in H0; destruct H0; rewrite H0.
   transitivity (F y); trivial.
   apply Fmono.
   apply inf_le; apply pair_intro1.

   apply Ftyp.
   apply inf_le; apply pair_intro2.
Qed.

End KnasterTarski.

