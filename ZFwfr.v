Require Import ZF.
Require ZFrepl.

(* Instance of ZFrepl.WFR when there is no need for an auxiliary fixpoint parameter *)

Section WellFoundedRecursion.

  Variable Rsub : set -> set.
  Hypothesis Rsubm : morph1 Rsub.

  Let R x y := x ∈ Rsub y.
  Local Instance Rm : Proper (eq_set==>eq_set==>iff) R.
do 3 red; intros.
unfold R.
rewrite H,H0; reflexivity.
Qed.

  Variable F : (set -> set) -> set -> set.
  Variable xx : set.
  
  Hypothesis Fext : forall x x' f f',
    ZFrepl.WFRle Rsub x xx ->
    (forall y y', R y x -> y==y' -> f y == f' y') ->
    x==x' ->
    F f x == F f' x'.

  Let F' := fun f x (_:unit) => F (fun x=>f x tt) x.

  Let F'ext : forall x x' a a' f f',
    ZFrepl.WFRle Rsub x xx ->
    (forall y y' a a', R y x -> y==y' -> a=a' -> f y a == f' y' a') ->
    x==x' ->
    F' f x a == F' f' x' a'.
intros.
unfold F'.    
apply Fext; auto.
Qed.

  Definition WFR x := ZFrepl.WFR eq Rsub F' x tt.

  Instance WFR_morph0 : morph1 WFR.
do 2 red; intros.
apply ZFrepl.WFR_morph0; trivial.
Qed.
  
  Lemma WFR_eqn :
    Acc R xx -> WFR xx == F WFR xx.
intros.
unfold WFR; rewrite ZFrepl.WFR_eqn; auto with *.
unfold F'; reflexivity.
Qed.

  Lemma WFR_ext xx' : Acc R xx -> xx == xx' -> WFR xx == WFR xx'.
Proof using Rsubm Fext.
intros.
apply ZFrepl.WFR_ext; auto with *.
Qed.

  Lemma WFR_ind : forall (P:set->set->Prop),
    Proper (eq_set ==> eq_set ==> iff) P ->
    Acc R xx ->
    (forall y, Acc R y ->
     (forall x, R x y -> P x (WFR x)) ->
     P y (F WFR y)) ->
    P xx (WFR xx).
intros P Pm wfx Hrec.
generalize (ZFrepl.WFRle_refl Rsub xx).
pattern xx at 1 3 4; elim wfx; intros.
unfold WFR; rewrite ZFrepl.WFR_eqn; auto with *.
*apply Hrec; [constructor; trivial|intros;apply H0; trivial].
 apply t_trans with x; auto.
*intros; apply F'ext; auto.
 apply t_trans with x; trivial.
*constructor; trivial.
Qed.

  Lemma WFR_non_mt x z : z ∈ WFR x -> Acc R x.
intros.
apply ZFrepl.WFR_non_mt in H; trivial.
Qed.

End WellFoundedRecursion.

Local Notation E:=eq_set (only parsing).

Global Instance WFR_morph :
    Proper ((E==>E)==>((E ==> E) ==> E ==> E) ==> E ==> E) WFR.
do 4 red; intros.
apply ZFrepl.WFR_morph; auto with *.
do 3 red; intros.
apply H0; trivial.
red; intros; apply H2; auto.
Qed.
