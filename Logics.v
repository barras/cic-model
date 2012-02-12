
Set Implicit Arguments.

Module Type LogicSig.

(* Formulas *)
Parameter
 (prop : Type)
 (TT FF : prop)
 (Not : prop -> prop)
 (Imp And Or : prop -> prop -> prop)
 (Forall Exist: forall {A}, (A -> prop) -> prop).

(* Inference rules *)
Parameter
 (holds : prop -> Prop)
 (rTT : holds TT)
 (rFF : ~ holds FF)
 (rAnd : forall P Q, (holds (And P Q) <-> holds P /\ holds Q))
 (rImp : forall P Q, (holds (Imp P Q) <-> (holds P -> holds Q)))
 (rForall : forall A P, (holds (Forall P) <-> forall x:A, holds (P x)))
 (rNot : forall P, holds (Not P) <-> ~ holds P)
 (rOrI : forall P Q, holds P \/ holds Q -> holds (Or P Q))
 (rOrE : forall P Q C, (holds P \/ holds Q -> holds C) -> holds (Or P Q) -> holds C)
 (rExI : forall A P, (exists (x:A), holds (P x)) -> holds (Exist P))
 (rExE : forall A P C, (forall x:A, holds (P x) -> holds C) -> holds (Exist P) -> holds C).

End LogicSig.

Module Type IntuitionisticLogicSig.
  Include LogicSig.

  (* prop is isomorphic to Prop up to <-> *)
  Parameter Prop_inj : Prop -> prop.
  Parameter Pintro : forall P, holds (Prop_inj P) <-> P.

End IntuitionisticLogicSig.


Module Type ClassicalLogicSig.
  Include LogicSig.

  Parameter Prop_inj : forall P:Prop, (~ ~ P -> P) -> prop.
  Parameter Pintro : forall P h, holds (@Prop_inj P h) <-> P.
  Parameter rClassic : forall P, holds (Not (Not P)) -> holds P.

End ClassicalLogicSig.


(* Interpretations of classical propositions to intuitionistic ones *)

(* Negative translation:
   A\/B is ~(~A/\~B) and exists x.P(x) is ~forall x.~P(x)
 *)
   
Module ClassicalLogic <: ClassicalLogicSig.

  Record _prop : Type := mkp { holds:Prop; nnf : ~ ~ holds -> holds }.
  Definition prop := _prop.
  Definition Prop_inj := mkp.

Lemma  Pintro P h : holds (@Prop_inj P h) <-> P.
simpl; split; trivial.
Qed.

Definition TT : prop := Prop_inj (fun _ => I).
Definition FF : prop := Prop_inj (fun f => f(fun x=>x):False).

Definition Imp (P Q:prop) : prop.
exists (holds P -> holds Q).
intros.
apply nnf.
firstorder.
Defined.
Definition Not P := Imp P FF.

Definition And (P Q:prop) : prop.
exists (holds P /\ holds Q).
split; apply nnf; firstorder.
Defined.

Definition Forall {A} (P:A -> prop) : prop.
exists (forall x, holds (P x)).
intros; apply nnf; firstorder.
Defined.

(* Disjunction: alternative def ~~(P\/Q)
   Equivalent since ~~(P\/Q) <-> ~(~P/\~Q) is an
   intuitionistic tautology.
 *)
Definition Or P Q := Not (And (Not P) (Not Q)).

(* Existential: alternative def ~~exists x,P x
   Equivalent since ~~(exists x, P x) <-> ~forall x, ~ P x is an
   intuitionistic tautology.
 *)
Definition Exist {A} P := Not (Forall (fun x:A => Not (P x))).

Lemma rTT : holds TT.
Proof I.

Lemma rFF : ~ holds FF.
Proof (fun x => x).

Lemma rAnd : forall P Q, (holds (And P Q) <-> holds P /\ holds Q).
firstorder.
Qed.

Lemma rImp : forall P Q, (holds (Imp P Q) <-> (holds P -> holds Q)).
firstorder.
Qed.

Lemma rForall : forall A P, (holds (Forall P) <-> forall x:A, holds (P x)).
firstorder.
Qed.

Lemma rNot : forall P, holds (Not P) <-> ~ holds P.
intro.
apply iff_refl.
Qed.

Lemma rOrI : forall P Q, holds P \/ holds Q -> holds (Or P Q).
firstorder.
Qed.

Lemma rOrE : forall P Q C, (holds P \/ holds Q -> holds C) -> holds (Or P Q) -> holds C.
intros.
apply nnf; firstorder.
Qed.

Lemma rExI : forall A P, (exists (x:A), holds (P x)) -> holds (Exist P).
firstorder.
Qed.

Lemma rExE : forall A P C,
  (forall x:A, holds (P x) -> holds C) -> holds (Exist P) -> holds C.
intros.
apply nnf.
firstorder.
Qed.

Lemma rClassic : forall P, holds (Not (Not P)) -> holds P.
intros.
apply nnf.
assumption.
Qed.

End ClassicalLogic.


Module Atrans1.

Record prop : Type := Prop_inj
  { holdA : Prop->Prop;
    trA : forall A:Prop, A -> holdA A }.

Definition TT : prop := Prop_inj (fun _ => True) (fun _ _ => I).
Definition FF : prop := Prop_inj (fun A => A) (fun _ a => a).

Definition Atom (P:Prop) : prop.
exists (fun A => P \/ A); firstorder.
Defined.

Definition Imp (P Q:prop) : prop.
exists (fun A:Prop => holdA P A -> holdA Q A).
intros.
apply trA; auto.
Defined.
Definition Not P := Imp P FF.

Definition And (P Q:prop) : prop.
exists (fun A => holdA P A /\ holdA Q A).
split; apply trA; trivial.
Defined.

Definition Forall {B} (P:B -> prop) : prop.
exists (fun A => forall x, holdA (P x) A).
intros; apply trA; trivial.
Defined.

Definition Or (P Q:prop) : prop.
exists (fun A => holdA P A \/ holdA Q A).
left; apply trA; trivial.
Defined.

Definition Exist {B} (P:B->prop) : prop.
exists (fun A => B -> exists x, holdA (P x) A).
intros.
exists X.
apply trA; trivial.
Defined.

Definition holds P := forall A, holdA P A.

Lemma rTT A : holdA TT A.
Proof I.

Lemma rFF A : forall Q, holdA FF A -> holdA Q A.
simpl; intros.
apply trA; trivial.
Qed.

Lemma rAtom A : forall P:Prop, P -> holdA (Atom P) A.
red; simpl; auto.
Qed.

(* Basic property of A-translation: as a consequence,
   A implies any A-translated formula *)
Lemma rA A : holdA FF A <-> A.
simpl; apply iff_refl.
Qed.

Lemma rAnd A : forall P Q, (holdA (And P Q) A <-> holdA P A /\ holdA Q A).
firstorder.
Qed.

Lemma rImp A : forall P Q, (holdA (Imp P Q) A <-> (holdA P A -> holdA Q A)).
firstorder.
Qed.

Lemma rForall A : forall T P, (holdA (Forall P) A <-> forall x:T, holdA (P x) A).
firstorder.
Qed.

Lemma rNot A : forall P, holdA (Not P) A <-> (holdA P A -> A).
firstorder.
Qed.

Lemma rOr A : forall P Q, holdA P A \/ holdA Q A <-> holdA (Or P Q) A.
firstorder.
Qed.

Lemma rEx A : forall T (w:T) P, (exists (x:T), holdA (P x) A) <-> holdA (Exist P) A.
firstorder.
Qed.


Lemma rDescr T1 T2 (w:T2) (P:T1->Prop) (Q:T1->T2->Prop) :
  (forall A, holdA (Forall(fun x => Imp (Atom (P x)) (Not (Not (Exist(fun y => Atom (Q x y))))))) A) ->
  forall x, P x -> exists y, Q x y.
simpl; intros.
apply H with x; intros; auto.
destruct H1; trivial.
destruct H1; eauto.
Qed.


Lemma rDescr2 T1 T2 (w:T2) (P:T1->prop) (Q:T1->T2->Prop) :
  (forall A, holdA (Forall(fun x => Imp (P x) (Not (Not (Exist(fun y => Atom (Q x y))))))) A) ->
  forall x, (forall A, holdA (P x) A) -> exists y, Q x y.
simpl; intros.
apply H with x; intros; auto.
destruct H1; trivial.
destruct H1; eauto.
Qed.

Lemma rDescr3 T1 T2 (w:T2) (P:T1->Prop) (Q:T1->T2->Prop) :
  (forall A, holdA (Forall(fun x => Imp (Atom(P x)) (Not (Not (Exist(fun y => Atom (Q x y))))))) A) ->
  (forall A, holdA (Forall(fun x => Imp (Atom(P x)) (Exist(fun y => Atom (Q x y))))) A).
simpl; intros.
apply H with x; trivial.
 destruct H0; auto.
 right; exists X; auto.

 intros.
 destruct H1; trivial.
 destruct H1; eauto.
Qed.


End Atrans1.


Module Atrans.

  Section S.
  Variable A : Prop.

  Record prop : Type := Prop_inj { holds : Prop; trA : A -> holds }.

Definition TT : prop := Prop_inj (fun _ => I).
Definition FF : prop := Prop_inj (fun a => a).

Definition Atom (P:Prop) : prop.
exists (P \/ A); auto.
Defined.

Definition Imp (P Q:prop) : prop.
exists (holds P -> holds Q).
intros.
apply trA; trivial.
Defined.
Definition Not P := Imp P FF.

Definition And (P Q:prop) : prop.
exists (holds P /\ holds Q).
split; apply trA; trivial.
Defined.

Definition Forall {B} (P:B -> prop) : prop.
exists (forall x, holds (P x)).
intros; apply trA; trivial.
Defined.

Definition Or (P Q:prop) : prop.
exists (holds P \/ holds Q).
left; apply trA; trivial.
Defined.

Definition Exist {B} (w:B) (P:B->prop) : prop.
exists (exists x, holds (P x)).
exists w; apply trA; trivial.
Defined.

Lemma rTT : holds TT.
Proof I.

Lemma rFF : forall Q, holds FF -> holds Q.
simpl; intros.
apply trA; trivial.
Qed.

Lemma rAtom : forall P:Prop, P -> holds (Atom P).
simpl; auto.
Qed.

(* Basic property of A-translation: as a consequence,
   A implies any A-translated formula *)
Lemma rA : holds FF <-> A.
simpl; apply iff_refl.
Qed.

Lemma rAnd : forall P Q, (holds (And P Q) <-> holds P /\ holds Q).
firstorder.
Qed.

Lemma rImp : forall P Q, (holds (Imp P Q) <-> (holds P -> holds Q)).
firstorder.
Qed.

Lemma rForall : forall A P, (holds (Forall P) <-> forall x:A, holds (P x)).
firstorder.
Qed.

Lemma rNot : forall P, holds (Not P) <-> (holds P -> A).
intro.
firstorder.
Qed.

Lemma rOr : forall P Q, holds P \/ holds Q <-> holds (Or P Q).
firstorder.
Qed.

Lemma rEx : forall A P (w:A), (exists (x:A), holds (P x)) <-> holds (Exist w P).
firstorder.
Qed.

  End S.

Lemma rClas A : holds (Not (Not (Atom A A))) -> A.
simpl.
auto.
intros.
apply H.
destruct 1; auto.
Qed.

Lemma rClas2 T P (Q:T->Prop) :
  (forall A, holds (Forall(fun x:T => Imp (Atom A (P x)) (Not (Not (Atom A (Q x))))))) ->
  forall x, P x -> Q x.
intros.
generalize (H (Q x)); simpl; intros.
apply H1 with x; auto.
destruct 1; trivial.
Qed.

Lemma rMarkov A (w:A) (P:A->Prop) :
  holds (Not (Not (Exist w (fun x => Atom (exists x:A,P x) (P x))))) -> exists x:A, P x.
intros.
apply rClas.
simpl in *.
intro; apply H.
intro.
destruct H1.
destruct H1; eauto.
Qed.

Lemma rMarkov2 A (w:A) (P:A->Prop) :
  holds (Not (Not (Exist w (fun x => Atom (exists x:A,P x) (P x))))) ->
  forall C, holds (Exist w (fun x => Atom C (P x))).
simpl; intros.
firstorder.
Qed.


Lemma rM A (P:A->Prop):
  (forall x, holds (Not (Not (Atom (P x) (P x))))) ->
  forall C, holds (Forall (fun x => Atom C (P x))).
simpl; intros.
left; apply H.
destruct 1; trivial.
Qed.

End Atrans.
(*
Module Ctrans.

Record prop (A:Prop->Prop): Type := Prop_inj
 { holds : Prop; trA : forall P, A P -> holds }.

Definition TT A : prop A := Prop_inj _ (fun _ _ => I).
Definition FF A : prop A := Prop_inj _ (fun P H => ex_intro A P H).

Definition Atom A (P:Prop) : prop A.
exists (P \/ exists Q, A Q); eauto.
Defined.

Definition Imp A (P Q:prop A) : prop A.
exists (holds P -> holds Q) .
intros.
apply trA with P0; trivial.
Defined.
Definition Not A P := Imp P (FF A).

Definition And A (P Q:prop A) : prop A.
exists (holds P /\ holds Q).
split; apply trA with P0; trivial.
Defined.

Definition Forall A {B} (P:B -> prop A) : prop A.
exists (forall x, holds (P x)).
intros; apply trA with P0; trivial.
Defined.

Definition Or A (P Q:prop A) : prop A.
exists (holds P \/ holds Q).
left; apply trA with P0; trivial.
Defined.

Definition Exist A {B} (w:B) (P:B->prop A) : prop A.
exists (exists x, holds (P x)).
exists w; apply trA with P0; trivial.
Defined.

Lemma rTT A : holds (TT A).
Proof I.

Lemma rFF : forall A (Q:prop A), holds (FF A) -> holds Q.
simpl; intros.
destruct H.
apply trA with x; trivial.
Qed.

Lemma rAtom : forall A (P:Prop), P -> holds (Atom A P).
simpl; auto.
Qed.

(* Basic property of A-translation: as a consequence,
   A implies any A-translated formula *)
Lemma rA A : holds (FF A) <-> exists P, A P.
simpl; apply iff_refl.
Qed.

Lemma rAnd : forall A (P Q:prop A), (holds (And P Q) <-> holds P /\ holds Q).
firstorder.
Qed.

Lemma rImp : forall A (P Q:prop A), (holds (Imp P Q) <-> (holds P -> holds Q)).
firstorder.
Qed.

Lemma rForall : forall A B (P:B->prop A), (holds (Forall P) <-> forall x:B, holds (P x)).
firstorder.
Qed.

Lemma rNot : forall A (P:prop A), holds (Not P) <-> (holds P -> exists Q, A Q).
intro.
firstorder.
Qed.

Lemma rOr : forall A (P Q:prop A), holds P \/ holds Q <-> holds (Or P Q).
firstorder.
Qed.

Lemma rEx : forall A B (P:B->prop A) (w:B), (exists (x:B), holds (P x)) <-> holds (Exist w P).
firstorder.
Qed.





Inductive form : Type :=
| At (_:Prop)
| Ff 
| Imp (_ _:form)
| Fa {A:Type} (_:A->form)
| Ex {A:Type} (_:A->form).

Fixpoint sem (f:form) :=
match f with 
  At P => P
| Ff => False
| Imp P Q => sem P -> sem Q
| Fa A P => forall x, sem (P x)
| Ex A P => exists x, sem (P x)
end.

(* f -> fst (Ctr f) /\ ~f -> snd(Ctr f) *)
Fixpoint Ctr (f:form) :=
  match f with
  | At P => P,~P
  | Ff => False, True
  | Imp P Q =>
      let (Pp,Pn) := Ctr P in let (Qp,Qn) := Ctr Q in
      ((Pp -> Qp), (Pn \/ Qn))
  | Ex A P => ((exists x, fst (Ctr (P x))), True)
  

  )
~(P->Q) ->

     match Ctr P, Ctr Q with
     | 
Fixpoint Ctr (forall A:Type, A->Prop) (X:Type) (x:X) (f:form) :=
  match f with
  | At P => A X x \/ P
  | Ff => A X x
  | Imp P Q => Ctr A X x P -> Ctr A X x Q
  | Fa Y P => forall y:Y, (Ctr (P x)) 


  End S.

Lemma rClas A : holds (Not (Not (Atom A A))) -> A.
simpl.
auto.
intros.
apply H.
destruct 1; auto.
Qed.

Lemma rM A (P:A->Prop) : holds (Forall(fun x:A=>Not(Not(Atom(forall x,P x)(P x))))) -> forall x,P x.
simpl.
intros.
apply H with x;intros.

firstorder.
Qed.

Lemma rMarkov A (w:A) (P:A->Prop) :
  holds (Not (Not (Exist w (fun x => Atom (exists x:A,P x) (P x))))) -> exists x:A, P x.
simpl; intros.
firstorder.
Qed.

End Ctrans.
*)
