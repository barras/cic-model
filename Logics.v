
Set Implicit Arguments.

(** This module declares signature for reasoning with abstract logics. It also
    defines negated translation and A-translation, thus providing a basis
    for interpreting classical logic.
 *)

(** * Abstract Higher-Order Logic *)
Module Type HOLogic.

(** Formulas *)
Parameter
 (prop : Type)
 (TT FF : prop)
 (Not : prop -> prop)
 (Imp And Or : prop -> prop -> prop)
 (Forall Exist: forall {A}, (A -> prop) -> prop)
 (Ex2 : forall {A}, (A -> prop) -> (A -> prop) -> prop).
 
(** Inference rules *)
Parameter
 (holds : prop -> Prop)
 (rTT : holds TT)
 (rFF : forall P, holds FF -> holds P)
 (rAnd : forall P Q, (holds (And P Q) <-> holds P /\ holds Q))
 (rImp : forall P Q, (holds (Imp P Q) <-> (holds P -> holds Q)))
 (rForall : forall A P, (holds (Forall P) <-> forall x:A, holds (P x)))
 (rNot : forall P, holds (Not P) <-> (holds P -> holds FF))
 (rOrI : forall P Q, holds P \/ holds Q -> holds (Or P Q))
 (rOrE : forall P Q C, (holds P \/ holds Q -> holds C) -> holds (Or P Q) -> holds C)
 (rExI : forall A P, (exists (x:A), holds (P x)) -> holds (Exist P))
 (rExE : forall A P C, (forall x:A, holds (P x) -> holds C) -> holds (Exist P) -> holds C)
 (rEx2I : forall A (P Q:A->prop), (exists2 x, holds (P x) & holds (Q x)) -> holds (Ex2 P Q))
 (rEx2E : forall A P Q C, (forall x:A, holds (P x) -> holds (Q x) -> holds C) ->
                         holds (Ex2 P Q) -> holds C).
End HOLogic.

(** A logic is consistent if FF cannot be derived *)
Module Type ConsistentLogic.

Include HOLogic.
Parameter rCons : ~ holds FF.

End ConsistentLogic.

(** An intuitionistic logic is a logic that embeds all of Prop *)

Module Type IntuitionisticLogic.
  Include ConsistentLogic.

  (** prop is isomorphic to Prop up to <-> *)
  Parameter Atom : Prop -> prop.
  Parameter rAtom : forall P, holds (Atom P) <-> P.

End IntuitionisticLogic.

(** A classical logic is a logic that derives ~~P->P forall all P.
    Given a logic, the set of propositions s.t. ~~P->P can be embedded.
 *)

Module Type ClassicalLogic (L:HOLogic).
  Include HOLogic.

  Parameter Atom : forall P:L.prop, (((L.holds P->L.holds L.FF)->L.holds L.FF)->L.holds P) -> prop.
  Parameter rAtom : forall P h, holds (@Atom P h) <-> L.holds P.
  Parameter rClassic : forall P, holds (Not (Not P)) -> holds P.

End ClassicalLogic.


(** * Negated translation: interpretation of classical propositions in intuitionistic ones. *)

(** Negated translation:
   A\/B is ~~(A\/B) and exists x.P(x) is ~~exists x. P(x)
 *)

Require Import Setoid.

Module NegatedTranslation (L:HOLogic) <: ClassicalLogic L.

  Notation Fa := (L.holds L.FF).

  Record _prop : Type := mkp { nnf : L.prop; nnh : ((L.holds nnf->Fa)->Fa) -> L.holds nnf }.
  Definition prop := _prop.
  Definition Atom := mkp.

Definition holds P := L.holds(nnf P).

Lemma rAtom P h : holds (@Atom P h) <-> L.holds P.
reflexivity.
Qed.

Definition TT : prop.
exists L.TT.
intros _; apply L.rTT.
Defined.

Definition FF : prop.
exists L.FF; auto.
Defined.

Definition Imp (P Q:prop) : prop.
exists (L.Imp (nnf P) (nnf Q)).
repeat rewrite L.rImp; intros.
apply nnh.
firstorder.
Defined.
Definition Not P := Imp P FF.

Definition And (P Q:prop) : prop.
exists (L.And (nnf P) (nnf Q)).
rewrite L.rAnd.
split; apply nnh; firstorder.
Defined.

Definition Forall {A} (P:A -> prop) : prop.
exists (L.Forall(fun x=> nnf(P x))).
rewrite L.rForall.
intros; apply nnh; firstorder.
Defined.

(** Disjunction: alternative def ~(~P/\~Q)
   Equivalent since ~~(P\/Q) <-> ~(~P/\~Q) is an
   intuitionistic tautology.
 *)
Definition Or (P Q:prop) : prop.
exists (L.Not (L.Not (L.Or (nnf P) (nnf Q)))).
repeat rewrite L.rNot; firstorder.
Defined.

(** Existential: alternative def ~forall x, ~ P x
   Equivalent since ~~(exists x, P x) <-> ~forall x, ~ P x is an
   intuitionistic tautology.
 *)
Definition Exist {A} (P:A->prop) : prop.
exists (L.Not (L.Not (L.Exist(fun x => nnf (P x))))).
repeat rewrite L.rNot; firstorder.
Defined.

Definition Ex2 {A} P Q := Exist (fun x:A => And (P x) (Q x)).

Lemma rTT : holds TT.
Proof L.rTT.

Lemma rFF P : holds FF -> holds P.
Proof (L.rFF (nnf P)).

Lemma rAnd : forall P Q, (holds (And P Q) <-> holds P /\ holds Q).
intros.
unfold holds; simpl.
rewrite L.rAnd; reflexivity.
Qed.

Lemma rImp : forall P Q, (holds (Imp P Q) <-> (holds P -> holds Q)).
intros.
unfold holds; simpl.
rewrite L.rImp; reflexivity.
Qed.

Lemma rForall : forall A P, (holds (Forall P) <-> forall x:A, holds (P x)).
intros.
unfold holds; simpl.
rewrite L.rForall; reflexivity.
Qed.

Lemma rNot P : holds (Not P) <-> (holds P -> Fa).
unfold holds; simpl.
rewrite L.rImp; reflexivity.
Qed.

Lemma rOrI : forall P Q, holds P \/ holds Q -> holds (Or P Q).
intros.
apply L.rOrI in H.
unfold holds; simpl.
repeat rewrite L.rNot.
firstorder.
Qed.

Lemma rOrE : forall P Q C, (holds P \/ holds Q -> holds C) -> holds (Or P Q) -> holds C.
intros.
unfold holds in *.
simpl in *.
repeat rewrite L.rNot in H0.
apply nnh; intro nC; apply H0; clear H0; intro H0; apply nC; clear nC.
apply L.rOrE with (2:=H0); trivial.
Qed.

Lemma rExI : forall A P, (exists (x:A), holds (P x)) -> holds (Exist P).
unfold holds; simpl; intros.
repeat rewrite L.rNot; intros nex; apply nex; clear nex.
apply L.rExI; trivial.
Qed.

Lemma rExE : forall A P C,
  (forall x:A, holds (P x) -> holds C) -> holds (Exist P) -> holds C.
intros.
unfold holds in *.
simpl in *.
repeat rewrite L.rNot in H0.
apply nnh; intro nC; apply H0; clear H0; intro H0; apply nC; clear nC.
apply L.rExE with (2:=H0); trivial.
Qed.

Lemma rEx2I : forall A (P Q:A->prop),
  (exists2 x, holds (P x) & holds (Q x)) -> holds (Ex2 P Q).
destruct 1 as (x,?,?); apply rExI; exists x; rewrite rAnd; split; trivial.
Qed.

Lemma rEx2E : forall A P Q C,
  (forall x:A, holds (P x) -> holds (Q x) -> holds C) ->
  holds (Ex2 P Q) ->
  holds C.
intros; apply rExE with (2:=H0); clear H0; intros.
rewrite rAnd in H0; destruct H0; eauto.
Qed.

Lemma rClassic : forall P, holds (Not (Not P)) -> holds P.
intros.
do 2 rewrite rNot in H.
apply nnh; trivial.
Qed.

Lemma equiCons : ~ holds FF <-> ~ L.holds L.FF.
reflexivity.
Qed.

End NegatedTranslation.


(** * A couple of instances: intuitionistic and classical logic *)

(** The logic of Coq *)
Module CoqLogic <: IntuitionisticLogic.

Definition prop := Prop.
Definition holds (P:prop) := P.
Definition TT := True.
Definition FF := False.
Definition Not P := ~ P.
Definition Imp (P Q:prop) := P->Q.
Definition And P Q := P /\ Q.
Definition Or P Q := P \/ Q.
Definition Forall {A} (P:A->Prop) := forall x:A, P x.
Definition Exist {A} P := exists x:A, P x.
Definition Ex2 {A} (P Q:A->prop) := exists2 x, P x & Q x. 
Definition Iff := iff.
Definition Atom (P:Prop) := P.
Lemma rAtom : forall P, holds (Atom P) <-> P.
reflexivity.
Qed.

(* Inference rules *)

Lemma rTT : holds TT.
Proof I.

Lemma rFF P : holds FF -> holds P.
Proof (False_ind P).

Lemma rAnd P Q : (holds (And P Q) <-> holds P /\ holds Q).
reflexivity.
Qed.

Lemma rImp P Q : (holds (Imp P Q) <-> (holds P -> holds Q)).
reflexivity.
Qed.

Lemma rForall A P : (holds (Forall P) <-> forall x:A, holds (P x)).
reflexivity.
Qed.

Lemma rNot P : holds (Not P) <-> ~ holds P.
reflexivity.
Qed.

Lemma rOrI P Q : holds P \/ holds Q -> holds (Or P Q).
auto.
Qed.

Lemma rOrE P Q C : (holds P \/ holds Q -> holds C) -> holds (Or P Q) -> holds C.
destruct 2; auto.
Qed.

Lemma rExI A P : (exists (x:A), holds (P x)) -> holds (Exist P).
auto.
Qed.

Lemma rExE A P C : (forall x:A, holds (P x) -> holds C) -> holds (Exist P) -> holds C.
destruct 2; eauto.
Qed.

Lemma rEx2I A (P Q:A->Prop): (exists2 x, holds (P x) & holds (Q x)) -> holds (Ex2 P Q).
auto.
Qed.

Lemma rEx2E A P Q C : (forall x:A, holds (P x) -> holds (Q x) -> holds C) -> holds (Ex2 P Q) -> holds C.
destruct 2; eauto.
Qed.

Lemma rIff P Q : holds (Iff P Q) <-> (holds P <-> holds Q).
reflexivity.
Qed.

Lemma rCons : ~ holds FF.
Proof (fun h => h).

End CoqLogic.

(** Classical logic as the negated translation of intuitionisitc logic *)
Module ClassicLogic <: ClassicalLogic CoqLogic :=
  NegatedTranslation CoqLogic.


(** * A-translation *)

Module Atranslation (L:HOLogic) (*<: HOLogic*).

Record _prop : Type := Prop_inj
  { Atr : L.prop->L.prop;
    Aimpl : forall A:L.prop, L.holds A -> L.holds (Atr A) }.
Definition prop := _prop.

Definition TT : prop := Prop_inj (fun _ => L.TT) (fun _ _ => L.rTT).
Definition FF : prop := Prop_inj (fun A => A) (fun _ a => a).

Definition Atom (P:L.prop) : prop.
exists (fun A => L.Or P A).
intros; apply L.rOrI; auto.
Defined.

Definition Imp (P Q:prop) : prop.
exists (fun A => L.Imp (Atr P A) (Atr Q A)).
intros.
rewrite L.rImp; intros.
apply Aimpl; trivial.
Defined.
Definition Not P := Imp P FF.

Definition And (P Q:prop) : prop.
exists (fun A => L.And (Atr P A) (Atr Q A)).
intros; rewrite L.rAnd; split; apply Aimpl; trivial.
Defined.

Definition Forall {B} (P:B -> prop) : prop.
exists (fun A => L.Forall(fun x => Atr (P x) A)).
intros; rewrite L.rForall; intros; apply Aimpl; trivial.
Defined.

Definition Or (P Q:prop) : prop.
exists (fun A => L.Or (Atr P A) (Atr Q A)).
intros; apply L.rOrI; left; apply Aimpl; trivial.
Defined.

(** Existential: we need to add an extra disjunction to accomodate
    higher-order logics, when the quantified domain might be empty:
    we need (forall x:B. P(x)) -> (exists x:B. P(x)).
    Either we can provide an t:B, or we put an extra disjunction.
 *)
Definition Exist {B} (P:B->prop) : prop.
exists (fun A => L.Or (L.Exist(fun x => Atr (P x) A)) A).
intros; apply L.rOrI; auto.
Defined.

Definition Ex2 {B} (P Q:B->prop) := Exist(fun x => And (P x) (Q x)).
(*
Module Type ASig.
  Parameter A : L.prop.
End ASig.

Module Make (X:ASig).
Import X.
*)

Section Make.
Variable A : L.prop.

Definition holds P := L.holds (Atr P A).

Lemma rTT : holds TT.
apply L.rTT.
Qed.

Lemma rFF : forall Q, holds FF -> holds Q.
simpl; intros.
apply Aimpl; assumption.
Qed.

Lemma rAnd : forall P Q, holds (And P Q) <-> holds P /\ holds Q.
 unfold holds; simpl.
intros; rewrite L.rAnd.
reflexivity.
Qed.

Lemma rImp : forall P Q, (holds (Imp P Q) <-> (holds P -> holds Q)).
unfold holds; simpl; intros.
rewrite L.rImp; reflexivity.
Qed.

Lemma rForall : forall T P, (holds (Forall P) <-> forall x:T, holds (P x)).
unfold holds; simpl; intros.
rewrite L.rForall.
reflexivity.
Qed.

Lemma rNot : forall P, holds (Not P) <-> (holds P -> L.holds A).
unfold holds; simpl; intros.
rewrite L.rImp.
reflexivity.
Qed.

Lemma rOrI : forall P Q, holds P \/ holds Q -> holds (Or P Q).
unfold holds; simpl; intros.
apply L.rOrI; trivial.
Qed.

Lemma rOrE : forall P Q C, (holds P \/ holds Q -> holds C) -> holds (Or P Q) -> holds C.
unfold holds; simpl; intros.
apply L.rOrE with (2:=H0); trivial.
Qed.

Lemma rExI : forall T P, (exists (x:T), holds (P x)) -> holds (Exist P).
unfold holds; simpl; intros.
apply L.rOrI; left; apply L.rExI; auto.
Qed.

Lemma rExE : forall T P C, (forall x:T, holds (P x) -> holds C) -> holds (Exist P) -> holds C.
unfold holds; simpl; intros.
apply L.rOrE with (2:=H0); clear H0; destruct 1.
 apply L.rExE with (2:=H0); trivial.

 apply Aimpl; trivial.
Qed.

Lemma rEx2I : forall T (P Q:T->prop), (exists2 x, holds (P x) & holds (Q x)) -> holds (Ex2 P Q).
destruct 1 as (x,?,?); apply rExI; exists x; rewrite rAnd; auto.
Qed.

Lemma rEx2E : forall T P Q C, (forall x:T, holds (P x) -> holds (Q x) -> holds C) -> holds (Ex2 P Q) -> holds C.
intros; apply rExE with (2:=H0); clear H0; intros.
rewrite rAnd in H0; destruct H0; eauto.
Qed.

(** Specific properties of A-translation
    - it is consistent only for non-derivable A
    - the embedding of atomic propositions adds a disjunction with A *)

Lemma rA : holds FF <-> L.holds A.
simpl; apply iff_refl.
Qed.

Lemma rAtom P : holds (Atom P) <-> L.holds (L.Or P A).
reflexivity.
Qed.

Lemma rAtomI P : L.holds P -> holds (Atom P).
intros; rewrite rAtom; apply L.rOrI; auto.
Qed.

End Make.

Definition holdsA P := forall A, holds A P.

Lemma rConsA : holdsA FF <-> L.holds L.FF.
split; intros.
 exact (H L.FF).

 red; intros.
 apply L.rFF; trivial.
Qed.

(** If ~~exists x, P x is derivable in the A-translated logic,
   then we have a derivation of exists x, P x in the original
   logic.
 *)

Lemma rNotNot T (P:T->L.prop) :
  holdsA (Not (Not (Exist (fun x => Atom (P x))))) ->
  L.holds (L.Exist(fun x => P x)).
intros.
set (A:=L.Exist(fun x => P x)).
red in H.
assert (h:=H A); clear H.
red in h; simpl in h.
repeat rewrite L.rImp in h.
apply h; intros.
apply L.rOrE with (2:=H); clear H; destruct 1; trivial.
apply L.rExE with (2:=H); clear H; intros.
apply L.rOrE with (2:=H); clear H; destruct 1; trivial.
apply L.rExI; exists x; trivial.
Qed.

(** If forall x, P x => ~~exists y, Q x y is derivable (in the
   A-translated logic) then forall x, Px -> exists y, Q x y
   is derivable in the original logic.
 *)
Lemma rDescr T1 T2 (P:T1->L.prop) (Q:T1->T2->L.prop) :
  (holdsA (Forall(fun x => Imp (Atom (P x)) (Not (Not (Exist (fun y => Atom (Q x y)))))))) ->
  forall x, L.holds (P x) -> L.holds (L.Exist(fun y => Q x y)).
intros.
apply rNotNot.
intros A; assert (h :=H A); clear H.
rewrite rForall in h.
assert (h' := h x); clear h.
rewrite rImp in h'.
apply h'.
apply rAtomI; trivial.
Qed.

End Atranslation.
