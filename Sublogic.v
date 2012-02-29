Require Export basic.
Require Import Logics.

Set Implicit Arguments.

(***************************************************************************)
(** * 1. Sublogics, wrapped in modules and functors *)

Module Type Sublogic.
  Parameter Inline Tr : Prop -> Prop.
  Parameter TrI : forall P:Prop, P -> Tr P.
  Parameter TrP : forall P:Prop, Tr (Tr P) -> Tr P.
  Parameter TrMono : forall (P Q:Prop), (P->Q)->Tr P->Tr Q.

End Sublogic.

(** Family of sublogic *)
Module Type SublogicFamily.
  Parameter T : Type.
  Parameter Inline Tr : T -> Prop -> Prop.
  Parameter TrI : forall x (P:Prop), P -> Tr x P.
  Parameter TrP : forall x (P:Prop), Tr x (Tr x P) -> Tr x P.
  Parameter TrMono : forall x (P Q:Prop), (P->Q)->Tr x P->Tr x Q.
End SublogicFamily.

Module Type Type_sig. Parameter T : Type. End Type_sig.
Module Type Elt_sig (T:Type_sig). Parameter x : T.T. End Elt_sig.

Module InstSublogicFamily (L:SublogicFamily) (X:Elt_sig L) <: Sublogic.
  Import X.
  Definition Tr := L.Tr x.
  Definition TrI := L.TrI x.
  Definition TrP := @L.TrP x.
  Definition TrMono := @L.TrMono x.
End InstSublogicFamily.

Module Type ConsistentSublogic.
Include Sublogic.
Parameter TrCons : ~ Tr False.
End ConsistentSublogic.

(** Sublogics are monads *)
Module AlternativeFormulations.

  Module Type LogicMonad.
    Parameter Inline M : Prop -> Prop.
    Parameter ret : forall P:Prop, P -> M P.
    Parameter bind : forall P Q:Prop, M P -> (P -> M Q) -> M Q.
  End LogicMonad.

  Module SublogicToMonad (M:LogicMonad) : Sublogic with Definition Tr := M.M.
    Import M.
    Definition Tr := M.
    Definition TrI (P:Prop) (p:P) : Tr P := ret p.
    Definition TrP (P:Prop) (p:Tr(Tr P)) : Tr P := bind p (fun x => x).
    Definition TrMono (P Q:Prop) (f:P->Q) (p:Tr P) : Tr Q :=
      bind p (fun x => ret (f x)).
  End SublogicToMonad.
  Module MonadToSublogic (L:Sublogic) : LogicMonad with Definition M := L.Tr.
    Import L.
    Definition M := Tr.
    Definition ret (P:Prop) (p:P) : M P := TrI p.
    Definition bind (P Q:Prop) (p:Tr P) (f:P->Tr Q) : Tr Q :=
      TrP (TrMono f p).
  End MonadToSublogic.

End AlternativeFormulations.
  
(** Sublogic equipped with tools useful for doing logics *)

Module Type SublogicTheory.

Include Sublogic.

Definition isL (P:Prop) := Tr P -> P.

Global Instance Tr_morph : Proper (iff==>iff) Tr.
Admitted.
Global Instance isL_morph : Proper (iff==>iff) isL.
Admitted.

  (* monad bind *)
  Parameter TrB : forall (P Q:Prop), Tr P -> (P -> Tr Q) -> Tr Q.
  Parameter Tr_ind : forall (P Q:Prop) {i:isL Q}, (P -> Q) -> Tr P -> Q.

  (** The set of L-propositions: introduction rules *)
  Parameter Tr_isL : forall P, isL (Tr P).
  Parameter T_isL : forall P:Prop, P -> isL P.
  Parameter and_isL : forall P Q, isL P -> isL Q -> isL (P/\Q).
  Parameter fa_isL : forall A (P:A->Prop),
    (forall x, isL (P x)) -> isL(forall x, P x).
  Parameter imp_isL : forall P Q, isL Q -> isL (P -> Q).
  Parameter iff_isL : forall P Q, isL P -> isL Q -> isL (P <-> Q).

Global Hint Resolve Tr_isL T_isL and_isL fa_isL imp_isL iff_isL.

  Parameter rFF : forall (Q:Prop), Tr False -> Tr Q.
  Parameter rFF': forall (Q:Prop), Tr False -> isL Q -> Q.

(** Introduction tactics *)

Ltac Tin := apply TrI.
Ltac Texists t := Tin; exists t.
Ltac Tleft := Tin; left.
Ltac Tright := Tin; right.

(** Elimination tactics:
    - Tabsurd replaces the current goal with Tr False (ex-falso)
    - Telim H implements rules H:Tr P |- G   -->  |- P->G when G is a L-prop
    - Tdestruct H is the equivalent of destruct on a hypothesis Tr(Ind x).
      The goal shall be an L-prop
 *)

Ltac prove_isL :=
  intros;
  lazymatch goal with
  | |- isL(Tr _) => apply Tr_isL
  | |- isL(_ /\ _) => apply and_isL; prove_isL
  | |- isL True => apply T_isL; exact I
  | |- isL(impl _ _) => apply imp_isL; prove_isL
  | |- isL(iff _ _) => apply iff_isL; prove_isL
  | |- isL(_ -> _) => apply imp_isL; prove_isL
  | |- isL(forall x, _) => apply fa_isL; intro; prove_isL
  | |- isL _ => auto 10; fail "Cannot prove isL side-condition"
  | |- _ => fail "Tactic prove_isL does not apply to this goal"
  end.

Ltac Tabsurd := 
  lazymatch goal with
  | |- Tr _ => apply rFF
  | |- _ => apply rFF';[|auto 10;fail"Cannot prove isL side-condition"]
  end.
Ltac Telim H :=
  lazymatch goal with
  | |- Tr _ => apply TrB with (1:=H); try clear H
  | |- _ => apply Tr_ind with (3:=H);[auto 10;fail"Cannot prove isL side-condition"|]; try clear H
  end.
Tactic Notation "Tdestruct" constr(H) :=
  Telim H; destruct 1.
Tactic Notation "Tdestruct" constr(H) "as" simple_intropattern(p) :=
  Telim H; intros p.

End SublogicTheory.

Module BuildLogic (L:Sublogic) <: SublogicTheory.

Include L.

(** Derived sublogic concepts:
    - more elimination rules (bind of the monad)
    - the set of L-propositions *)

Global Instance Tr_morph : Proper (iff==>iff) Tr.
split; apply TrMono; apply H.
Qed.

Definition isL (P:Prop) := Tr P -> P.

Global Instance isL_morph : Proper (iff==>iff) isL.
do 2 red; intros.
unfold isL; rewrite H; reflexivity.
Qed.

  (* bind *)
  Lemma TrB : forall (P Q:Prop), Tr P -> (P -> Tr Q) -> Tr Q.
intros.
apply TrP; revert H; apply TrMono; auto.
Qed.

  Lemma Tr_ind : forall (P Q:Prop) {i:isL Q}, (P -> Q) -> Tr P -> Q.
intros.
apply i; revert H0; apply TrMono; trivial.
Qed.

(** The set of L-propositions: introduction rules.
    L-props are closed under all connectives of negative
    polarity.
 *)

Lemma Tr_isL : forall P, isL (Tr P).
Proof TrP.

Lemma T_isL : forall P:Prop, P -> isL P.
Proof (fun _ p _ => p).

Lemma and_isL : forall P Q, isL P -> isL Q -> isL (P/\Q).
compute; intros.
split; revert H1; apply Tr_ind; firstorder.
Qed.

Lemma fa_isL : forall A (P:A->Prop),
  (forall x, isL (P x)) -> isL(forall x, P x).
compute; intros.
revert H0; apply Tr_ind; firstorder.
Qed.

Lemma imp_isL : forall P Q, isL Q -> isL (P -> Q).
intros.
apply fa_isL; trivial.
Qed.

Lemma iff_isL : forall P Q, isL P -> isL Q -> isL (P <-> Q).
intros; apply and_isL; apply imp_isL; trivial.
Qed.

Global Hint Resolve Tr_isL T_isL and_isL fa_isL imp_isL iff_isL.

(** Elimination rules for falsity *)

Lemma rFF (Q:Prop) : Tr False -> Tr Q.
apply TrMono; intros; contradiction.
Qed.
Lemma rFF' (Q:Prop) : Tr False -> isL Q -> Q.
intros.
apply H0; apply rFF; trivial.
Qed.

End BuildLogic.

(** The same for consistent logics: False is now an L-prop *)

Module BuildConsistentSublogic (L:ConsistentSublogic).
  Module tmp <: SublogicTheory := BuildLogic L.
  Include tmp.

Lemma FF_isL : isL False.
Proof L.TrCons.

Global Hint Resolve FF_isL.

End BuildConsistentSublogic.

(***************************************************************************)
(** * 2.Examples of sublogic modules *)

(** Coq's intuitionistic logic *)
Module CoqSublogic <: ConsistentSublogic.
Definition Tr P:Prop := P.
Definition TrI (P:Prop) (p:P) : Tr P := p.
Definition TrP (P:Prop) (p:Tr (Tr P)) : Tr P := p.
Definition TrMono (P Q:Prop) (f:P->Q) (p:Tr P) : Tr Q := f p.
Definition TrCons : ~ Tr False := fun h => h.
End CoqSublogic.

Module CoqSublogicThms := BuildConsistentSublogic CoqSublogic.

(** Classical logic through negated translation *)
Module ClassicSublogic <: ConsistentSublogic.
Definition Tr (P:Prop) := ~~P.
Definition TrI (P:Prop) (p:P) : Tr P := fun np => np p.
Definition TrP (P:Prop) (nnnnp:Tr (Tr P)) : Tr P :=
 fun np => nnnnp (fun nnp => nnp np).
Definition TrMono (P Q:Prop) (f:P->Q) (nnp:Tr P) : Tr Q :=
 fun nq => nnp (fun p => nq (f p)). 
Definition TrCons : ~ Tr False := fun h => h (fun x => x).
End ClassicSublogic.

Module ClassicSublogicThms.
  Include BuildConsistentSublogic ClassicSublogic.

  Lemma nnpp (P:Prop) : ((P->False)->False) -> Tr P.
Proof (fun h => h).

  (* excluded-middle: note that P need not be classical, which makes the
     positive case stronger. *)
  Lemma classic : forall P, Tr(P \/ (Tr P -> False)).
intros P nem.
apply nem; right; intro tp.
apply Tr_ind with (3:=tp); intros; trivial.
apply nem; left; assumption.
Qed.
End ClassicSublogicThms.

(** Friedman's A-translation *)

Module ASublogic <: SublogicFamily.
  Definition T:=Prop.
  Definition Tr A P := P \/ A.
  Definition TrI (A P:Prop) (p:P) : Tr A P := or_introl p.
  Definition TrP (A P:Prop) (p:(P\/A)\/A) :=
    match p with
    | or_introl p => p
    | or_intror a => or_intror a
    end.
  Definition TrMono (A P Q:Prop) (f:P->Q) (p:P\/A) :=
    match p with
    | or_introl p => or_introl (f p)
    | or_intror a => or_intror a
    end.
End ASublogic.

Module Type Aprop. Parameter x:Prop. End Aprop.

Module ASublogicThms (A:Aprop) <: SublogicTheory.
  Module Asl := InstSublogicFamily ASublogic A.
  Import Asl.
  Notation A := A.x.
  Include BuildLogic Asl.

Lemma Aconsistency : isL False <-> ~A. 
firstorder.
Qed.

Lemma atom_isL (P:Prop) : (A->P) -> isL P.
firstorder.
Qed.

(* or does not need to be modified *)
Lemma or_isL P Q : isL P \/ isL Q -> isL (P\/Q).
firstorder.
Qed.
Global Hint Resolve or_isL.

(* existential does need to be modified when one of the
   instances is an L-prop. *)
Lemma ex_isL_raw T (P:T->Prop):
  (exists x, isL (P x)) -> isL(ex P).
firstorder.
Qed.

(* A more usable rule (we can expect the foral x, isL (P x) assumption to be provable
   automatically), but which requires T to be inhabited. *)
Lemma ex_isL T (P:T->Prop) :
  T -> (forall x, isL (P x)) -> isL (ex P).
compute; intros.
destruct H0; trivial.
exists X; auto.
Qed.
Global Hint Resolve ex_isL.

Lemma FF_a : Tr False <-> A.
split.
 destruct 1;[contradiction|trivial].
 right; trivial.
Qed.

End ASublogicThms.

(* Example: if ~~exists x. P(x) is derivable, then so is exists x. P(x) *)
Module AtransExample.
Parameter (T:Type) (P : T->Prop).
Module nnex. Definition x:=exists x, P x. End nnex.
Module Atr := ASublogicThms nnex.
Import nnex Atr.

Lemma markov_rule :
  ((Tr(exists x, P x) -> Tr False) -> Tr False) ->
  exists x, P x.
intro.
apply FF_a.
apply H; intro.
apply Tr_ind with (3:=H0); intros; trivial.
 apply Atr.Tr_isL.
apply FF_a.
assumption.
Qed.
End AtransExample.

(** Peirce translation *)

Module PeirceTrans <: SublogicFamily.
  Definition T := Prop.
  Definition Tr (R A:Prop) := (A->R)->A.
  Definition TrI (R A:Prop) (a:A) : Tr R A := fun ar => a.
  Definition TrP (R A:Prop) (tta:Tr R (Tr R A)) : Tr R A :=
   fun ar => tta (fun ara => ar (ara ar)) ar. 
  Definition TrMono (R A B:Prop) (f:A->B) (ta:Tr R A) : Tr R B :=
   fun br => f (ta (fun a => br (f a))).
  Definition TrCons (R:Prop) : ~ Tr R False :=
   fun frf => frf (False_ind R).
End PeirceTrans.

(** Intersection or cartesian product *)

Module Inter (L:SublogicFamily) <: Sublogic.
  Definition Tr P := forall x, L.Tr x P.
  Definition TrI (P:Prop) (p:P) : Tr P := fun x => L.TrI x p.
  Definition TrP (P:Prop) (ttp:Tr(Tr P)) : Tr P :=
    fun x => L.TrP (L.TrMono (fun p => p x) (ttp x)).
  Definition TrMono (P Q:Prop) (f:P->Q) (p:Tr P) : Tr Q :=
    fun x => L.TrMono f (p x).
  (* If a member of the family is consistent, then so is the intersection. *)
  Lemma equiCons : Tr False <-> forall x, L.Tr x False.
    reflexivity.
  Qed.
End Inter.

Module Inter2 (L1 L2:Sublogic) <: Sublogic.
  Definition Tr P := L1.Tr P /\ L2.Tr P.
  Definition TrI (P:Prop) (p:P) : Tr P := conj (L1.TrI p) (L2.TrI p).
  Definition TrP (P:Prop) (ttp:Tr(Tr P)) : Tr P :=
    conj (L1.TrP (L1.TrMono (fun p => proj1 p) (proj1 ttp)))
         (L2.TrP (L2.TrMono (fun p => proj2 p) (proj2 ttp))).
  Definition TrMono (P Q:Prop) (f:P->Q) (p:Tr P) : Tr Q :=
    conj (L1.TrMono f (proj1 p)) (L2.TrMono f (proj2 p)).
  (* If L1 or L2 is consistent, then so is L1/\L2. *)
  Lemma equiCons : Tr False <-> L1.Tr False /\ L2.Tr False.
    reflexivity.
  Qed.
  Lemma isL_intro P : (L1.Tr P -> P) \/ (L2.Tr P -> P) -> (Tr P -> P).
destruct 1; destruct 1; auto.
Qed.

End Inter2.

(***************************************************************************)
(** * 3. Building a higher-order logic with L-props. *)


Module SublogicToHOLogic (L:SublogicTheory) <: HOLogic.
Import L.

Record prop_ := mkP { holds : Prop; isprop : isL holds }.
Definition prop := prop_.

Definition TT : prop.
exists True; auto.
Defined.
Definition FF : prop.
exists (Tr False); trivial.
Defined.
Definition Imp (P Q:prop) : prop.
exists (holds P->holds Q).
apply imp_isL; apply isprop.
Defined.
Definition Not p := Imp p FF.
Definition And (P Q:prop) : prop.
exists (holds P /\ holds Q).
apply and_isL; apply isprop.
Defined.
Definition Or (P Q:prop) : prop.
exists (Tr(holds P \/ holds Q)).
trivial.
Defined.
Definition Forall {A} (P:A->prop) : prop.
exists (forall x, holds (P x)).
apply fa_isL; intros x; apply isprop.
Defined.
Definition Exist {A} (P:A->prop) : prop.
exists (Tr(exists x, holds (P x))).
trivial.
Defined.
Definition Ex2 {A} (P Q:A->prop) : prop.
exists (Tr(exists2 x, holds (P x) & holds (Q x))).
trivial.
Defined.
 
(** Inference rules *)

Lemma rTT : holds TT.
exact I.
Qed.
Lemma rFF P : holds FF -> holds P.
simpl.
apply Tr_ind; [apply isprop|contradiction].
Qed.
Lemma rAnd P Q : holds (And P Q) <-> holds P /\ holds Q.
reflexivity.
Qed.
Lemma rImp P Q : holds (Imp P Q) <-> (holds P -> holds Q).
reflexivity.
Qed.
Lemma rForall A P : holds (Forall P) <-> forall x:A, holds (P x).
reflexivity.
Qed.
Lemma rNot P : holds (Not P) <-> (holds P -> holds FF).
reflexivity.
Qed.
Lemma rOrI P Q : holds P \/ holds Q -> holds (Or P Q).
simpl.
apply TrI.
Qed.
Lemma rOrE P Q C : (holds P \/ holds Q -> holds C) -> holds (Or P Q) -> holds C.
intro; apply Tr_ind; [apply isprop|trivial].
Qed.
Lemma rExI A P : (exists (x:A), holds (P x)) -> holds (Exist P).
destruct 1; simpl; apply TrI; eauto.
Qed.
Lemma rExE A P C : (forall x:A, holds (P x) -> holds C) -> holds (Exist P) -> holds C.
intro; apply Tr_ind; [apply isprop|].
destruct 1; eauto.
Qed.
Lemma rEx2I A (P Q:A->prop) : (exists2 x, holds (P x) & holds (Q x)) -> holds (Ex2 P Q).
destruct 1; simpl; apply TrI; eauto.
Qed.
Lemma rEx2E A P Q C : (forall x:A, holds (P x) -> holds (Q x) -> holds C) -> holds (Ex2 P Q) -> holds C.
intro; apply Tr_ind; [apply isprop|].
destruct 1; eauto.
Qed.

Lemma equiCons : Tr False <-> holds FF.
reflexivity.
Qed.

End SublogicToHOLogic.

(***************************************************************************)
(** * 4. The same ideas but using records and typeclasses *)

Module TypeClasses.

Class sub_logic0 := mkSubLogic0 {
  Tr : Prop -> Prop;
  TrI : forall P:Prop, P -> Tr P;
  TrB : forall P Q:Prop, Tr P -> (P -> Tr Q) -> Tr Q;
  Teq1 (P Q:Prop) (m:Tr P) (f:P->Tr Q) (x:P): TrB (TrI x) f = f x;
  Teq2 (P:Prop) (m:Tr P) : TrB m (@TrI _) = m
}.
Parameter M0 : sub_logic0.
Existing Instance M0.

Definition mono (P Q:Prop) (f:P->Q) (m:Tr P) : Tr Q :=
 TrB _ m (fun x => TrI (f x)).
Definition proj (P:Prop) (m:Tr(Tr P)) : Tr P :=
 TrB _ m (fun x => x).


Class sub_logic := mkSubLogic {
  P2p : Prop -> Prop;
  P2p_mono : Proper (impl ==> impl) P2p;
  P2p_proj : forall P, P2p (P2p P) -> P2p P;
  P2pI : forall P:Prop, P -> P2p P
(*  eq1 (P:Prop) (m:P2p P) : P2p_proj (P2pI m) = m;
  eq2 (P Q:Prop) (f:P->Q) (x:P) : P2p_mono f (P2pI x) = P2pI (f x)*)
}.

Parameter M : sub_logic.
Existing Instance M.

Definition ret (P:Prop) (x:P) : P2p P := P2pI x.
Definition bind (P Q:Prop) (a : P2p P) (b: P -> P2p Q) : P2p Q :=
  P2p_proj _ (P2p_mono b a).

Definition p1 := forall (P Q:Prop) (x:P) (f:P->P2p Q), bind _ (ret x) f = f x.
Definition p2 := forall (P:Prop) (x:P), let m := ret x in bind _ m (fun y => ret y) = m.
Definition p3 := forall (P Q R:Prop) (x:P) (f:P->P2p Q) (g:Q->P2p R),
  let m := ret x in
  bind R (bind Q m f) g = bind _ m (fun x => bind _ (f x) g).
(*
Lemma L1 : p1.
unfold p1, ret, bind; intros.
rewrite eq2.
rewrite eq1.
reflexivity.
Qed.
Lemma L2 : p2.
unfold p2,ret,bind; intros.
rewrite eq2.
rewrite eq1.
reflexivity.
Qed.
Lemma L3 : p3.
unfold p3,ret,bind; intros.
repeat rewrite eq2.
do 2 rewrite eq1.
reflexivity.
Qed.
*)
Section SubLogicFacts.

Hypothesis L : sub_logic.

Instance P2p_morph : Proper (iff ==> iff) P2p.
apply morph_impl_iff1; auto with *.
intros P Q e.
apply P2p_mono; destruct e; trivial.
Qed.

Class isL P : Prop :=
  isFormula : P2p P -> P.

Instance isL_morph : Proper (iff ==> iff) isL.
unfold isL; do 2 red; intros.
rewrite H; reflexivity.
Qed.

Lemma P2p_isL P : isL (P2p P).
red; apply P2p_proj.
Qed.

Lemma P2pE : forall (P Q:Prop), isL Q -> (P -> Q) -> (P2p P -> Q).
intros.
apply H.
revert H1; apply P2p_mono; trivial.
Qed.

(* Building the logic: *)

Lemma T_isL (P:Prop) : P -> isL P.
red; trivial.
Qed.

Lemma and_isL P Q : isL P -> isL Q -> isL (P/\Q).
unfold isL; intros.
split.
 apply H; revert H1; apply P2p_mono.
 red; destruct 1; trivial.

 apply H0; revert H1; apply P2p_mono.
 red; destruct 1; trivial.
Qed.

Lemma forall_isL : forall A (P:A->Prop), (forall x:A, isL (P x)) -> isL (forall x:A, P x).
unfold isL; intros.
apply H.
revert H0; apply P2p_mono; red; auto.
Qed.

Lemma impl_isL : forall P Q,
  isL Q -> isL (P -> Q).
red; intros.
apply H.
revert H0; apply P2p_mono; red; auto.
Qed.

(* Nothing about or, ex, False *)

Definition FF := P2p False.

Definition consistent := ~ FF.

Hypothesis cons : consistent.

Lemma False_isL : isL False.
Proof cons.

Lemma not_isL (P:Prop) : isL (~P).
apply impl_isL; trivial.
Qed.

Definition Or P Q := P2p(P\/Q).

Instance Or_morph : Proper (iff==>iff==>iff) Or.
do 3 red; intros.
apply P2p_morph; apply or_iff_morphism; trivial.
Qed.

Lemma orI P Q : P \/ Q -> Or P Q.
red; intros; apply P2pI; trivial.
Qed.

Lemma orE (P Q C:Prop) :
  (P -> C) -> (Q -> C) -> Or P Q -> isL C -> C.
intros.
apply P2pE with (P \/ Q); trivial.
destruct 1; auto.
Qed.

Definition Ex {A} (P:A->Prop) := P2p(ex P).

Lemma exI A (P:A->Prop) x : P x -> Ex P.
red; intros; apply P2pI.
exists x; trivial.
Qed.

Lemma exE A (P:A->Prop) (C:Prop) : (forall x, P x -> C) -> Ex P -> isL C -> C.
intros.
apply P2pE with (3:=H0); trivial.
destruct 1; eauto.
Qed.

Instance Ex_morph : forall A,
   Proper ((pointwise_relation A iff) ==> iff) (@Ex A).
do 3 red; intros.
apply P2p_morph; apply ex_morph; trivial.
Qed.

Definition Ex2 {A} (P Q:A->Prop) := P2p(ex2 P Q).

Lemma ex2I A (P Q:A->Prop) x : P x -> Q x -> Ex2 P Q.
red; intros; apply P2pI.
exists x; trivial.
Qed.

Lemma ex2E A (P Q:A->Prop) (C:Prop) : (forall x, P x -> Q x -> C) -> Ex2 P Q -> isL C -> C.
intros.
apply P2pE with (3:=H0); trivial.
destruct 1; eauto.
Qed.

Instance Ex2_morph : forall A,
   Proper (pointwise_relation A iff ==> pointwise_relation A iff ==> iff) (@Ex2 A).
do 3 red; intros.
apply P2p_morph; apply ex2_morph; trivial.
Qed.

(* Packaging the logic *)

Record prop := mkP { tr : Prop; isprop : isL tr }.

Definition TT : prop.
exists True.
apply T_isL; trivial.
Defined.
Definition FF' : prop.
exists FF.
unfold isL,FF; apply P2p_proj.
Defined.
Definition Imp (P Q:prop) : prop.
exists (tr P->tr Q).
apply impl_isL; apply isprop.
Defined.
Definition And (P Q:prop) : prop.
exists (tr P /\ tr Q).
apply and_isL; apply isprop.
Defined.
Definition Or' (P Q:prop) : prop.
exists (Or (tr P) (tr Q)).
unfold isL,Or; apply P2p_proj. 
Defined.
Definition Forall {A} (P:A->prop) : prop.
exists (forall x, tr (P x)).
apply forall_isL; intros x; apply isprop.
Defined.
Definition Ex' {A} (P:A->prop) : prop.
exists (Ex (fun x => tr (P x))).
unfold isL,Ex; apply P2p_proj.
Defined.
Definition Not p := Imp p FF'.
 
(** Inference rules *)
Notation holds := tr.
Lemma rTT : holds TT.
exact I.
Qed.
Lemma rFF P : holds FF' -> holds P.
simpl.
apply P2pE.
 apply isprop.
 intros; contradiction.
Qed.
Lemma rAnd P Q : holds (And P Q) <-> holds P /\ holds Q.
reflexivity.
Qed.
Lemma rImp P Q : holds (Imp P Q) <-> (holds P -> holds Q).
reflexivity.
Qed.
Lemma rForall A P : holds (Forall P) <-> forall x:A, holds (P x).
reflexivity.
Qed.
Lemma rNot P : holds (Not P) <-> (holds P -> holds FF').
reflexivity.
Qed.
Lemma rOrI P Q : holds P \/ holds Q -> holds (Or' P Q).
simpl.
apply orI.
Qed.
Lemma rOrE P Q C : (holds P \/ holds Q -> holds C) -> holds (Or' P Q) -> holds C.
intros; apply orE with (3:=H0); auto.
apply isprop.
Qed.
Lemma rExI A P : (exists (x:A), holds (P x)) -> holds (Ex' P).
destruct 1.
apply exI with x; trivial.
Qed.
Lemma rExE A P C : (forall x:A, holds (P x) -> holds C) -> holds (Ex' P) -> holds C.
intros.
apply exE with (2:=H0); auto.
apply isprop; trivial.
Qed.

End SubLogicFacts.

(** Coq logic *)
Section Coq.

Definition coq := fun (P:Prop) => P.
Instance coq_logic : sub_logic := { P2p := coq }.
firstorder.
firstorder.
firstorder.
Defined.
Lemma coq_isL (P:Prop) : isL coq_logic P.
Proof (fun h=>h).

Lemma coq_cons : consistent coq_logic.
Proof (fun h => h).
End Coq.

(** Classical logic *)

Section Classic.
Definition nnt (P:Prop) := ~~P.

Instance classic_logic : sub_logic := { P2p := nnt }.
exact (fun P Q (f:P->Q) (nnp:~~P) (nq:~Q) => nnp(fun p => nq(f p))).
exact (fun P nnnnp np => nnnnp(fun nnp => nnp np)).
exact (fun P p => fun np => np p).
Defined.

Lemma em P : Or classic_logic P (~P).
firstorder.
Qed.

Lemma cl_cons : consistent classic_logic.
Proof (fun h => h(fun x => x)).

Lemma cl_isL P : (~~P->P) -> isL classic_logic P.
Proof (fun h => h).

End Classic.

(** Friedman's A-translation *)
Section Atrans.

Definition Atr A P := P \/ A.

Instance Atrans A : sub_logic := { P2p := Atr A }.
exact (fun P Q (f:P->Q) (p:P\/A) =>
  match p with
  | or_introl p => or_introl (f p)
  | or_intror a => or_intror a
  end).
exact (fun P (p:(P\/A)\/A) =>
  match p with
  | or_introl p => p
  | or_intror a => or_intror a
  end).
exact (fun P (p:P) => or_introl p).
Defined.

Lemma atr_atom (A P:Prop) : (A->P) -> isL (Atrans A) P.
firstorder.
Qed.

(* or does not need to be modified *)
Lemma atr_or_isL A P Q : isL (Atrans A) P \/ isL (Atrans A) Q -> isL (Atrans A) (P\/Q).
firstorder.
Qed.

Lemma atr_a A : FF(Atrans A) <-> A.
split.
 destruct 1;[contradiction|trivial].
 right; trivial.
Qed.

Lemma atr_nnex T (P:T->Prop) :
 (forall A, ((Ex(Atrans A) P) -> FF(Atrans A))->FF(Atrans A)) ->
 exists x:T, P x.
intros.
set (A:=exists x, P x).
apply atr_a.
apply H; intro.
apply (fun P Q => @P2pE (Atrans A) P (P2p Q)) with (3:=H0).
 apply P2p_isL.
apply atr_a.
Qed.

End Atrans.

(** Peirce's translation *)

Section PeirceTrans.

Definition Ptr (R A:Prop) := (A->R)->A.

Instance Ptrans R : sub_logic := { P2p := Ptr R }.
firstorder.
firstorder.
firstorder.
Defined.

Lemma Pcons R : consistent (Ptrans R).
do 2 red.
unfold FF, Ptrans.
unfold P2p.
unfold Ptr.
intros.
apply H; intros.
contradiction.
Qed.

End PeirceTrans.

End TypeClasses.
