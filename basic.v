
(** General purpose definitions that could make it to the standard library *)

Set Implicit Arguments.
(*Require Export Utf8_core.*)
Require Export Minus Peano_dec Compare_dec Max.
Require Export List.
Require Export Relations Relation_Operators Transitive_Closure.
Require Import Wellfounded.
Require Export Coq.Program.Basics.
Require Export Setoid Morphisms Morphisms_Prop.
Export ProperNotations.

Hint Resolve t_step rt_step rt_refl: core.
Hint Unfold transp: core.

Scheme Acc_indd := Induction for Acc Sort Prop.

Definition indexed_relation A A' B (R:B->B->Prop) (f:A->B) (g:A'->B) :=
  (forall x, exists y, R (f x) (g y)) /\
  (forall y, exists x, R (f x) (g y)).

Lemma indexed_relation_id : forall A B (R:B->B->Prop) (F F':A->B),
  (forall x, R (F x) (F' x)) ->
  indexed_relation R F F'.
split; intros; eauto.
Qed.

(** Asymmetric and-split, strengthens the rhs with the proof of the lhs *)
Lemma and_split (A B:Prop) :
  A -> (A->B) -> A/\B.
split; auto.
Qed.

(**********************************************************************************)
(** Setoid and morphisms stuff *)

Lemma impl_morph A A' B B' :
  (A <-> A') ->
  (A -> (B <-> B')) ->
  ((A -> B) <-> (A' -> B')).
split; intros.
 rewrite <- H in H2.
 rewrite <- H0; auto.

 rewrite H0; auto.
 rewrite H in H2; auto.
Qed.

Lemma fa_mono : forall A (B B':A->Prop),
  (forall x, impl (B x) (B' x)) -> impl (forall x, B x) (forall x, B' x).
unfold impl; intros; auto.
Qed.

Lemma fa_morph : forall A (B B':A->Prop),
  (forall x, B x <-> B' x) -> ((forall x, B x) <-> (forall x, B' x)).
split; intros.
 rewrite <- H; trivial.
 rewrite H; trivial.
Qed.

(*Instance ex_mono : forall A,
  Proper (pointwise_relation A impl ==> impl) (@ex A).
do 3 red; intros.
destruct H0.
exists x0.
apply H; trivial.
Qed.*)

Instance ex_morph : forall A,
  Proper (pointwise_relation A iff ==> iff) (@ex A).
do 2 red; intros.
split; intros.
 destruct H0.
 exists x0.
 destruct (H x0); auto.

 destruct H0.
 exists x0.
 destruct (H x0); auto.
Qed.

Instance ex2_mono : forall A,
  Proper (pointwise_relation A impl ==> pointwise_relation A impl ==> impl) (@ex2 A).
do 4 red; intros.
destruct H1.
exists x1.
 apply H; trivial.
 apply H0; trivial.
Qed.

Instance ex2_morph : forall A,
  Proper (pointwise_relation A iff ==> pointwise_relation A iff ==> iff) (@ex2 A).
do 2 red; intros.
split; intros.
 destruct H1.
 exists x1.
  destruct (H x1); auto.
  destruct (H0 x1); auto.

 destruct H1.
 exists x1.
  destruct (H x1); auto.
  destruct (H0 x1); auto.
Qed.

Lemma ex2_morph' : forall A (P P' Q Q':A->Prop),
  (forall x, P x <-> P' x) ->
  (forall x, P x -> (Q x <-> Q' x)) ->
  (ex2 P Q <-> ex2 P' Q').
split; intros (x,Px, Qx); exists x.
 rewrite <- H; trivial.
 rewrite <- H0; trivial.

 rewrite H; trivial.
 rewrite H0; trivial.
 rewrite H; trivial.
Qed.

Lemma iff_morph : Proper (iff ==> iff ==> iff) iff.
auto with *.
Qed.

Lemma iff_impl : forall A B, iff A B -> impl A B.
destruct 1; auto.
Qed.

(* Should be in stdlib ? *)

Lemma morph_impl_iff1 : forall A (R:A->A->Prop) f,
  Symmetric R ->
  Proper (R ==> impl) f ->
  Proper (R ==> iff) f.
split; intros.
 rewrite <- H1; trivial.
 rewrite H1; trivial.
Qed.

Lemma morph_impl_iff2 : forall A (R:A->A->Prop) B (S:B->B->Prop) f,
  Symmetric R ->
  Symmetric S ->
  Proper (R ==> S ==> impl) f ->
  Proper (R ==> S ==> iff) f.
split; intros.
 apply H1 with x x0; trivial.

 apply H1 with y y0; trivial; symmetry; trivial.
Qed.

Lemma morph_impl_iff3 : forall A B C R S T f,
  @Symmetric A R ->
  @Symmetric B S ->
  @Symmetric C T ->
  Proper (R ==> S ==> T ==> impl) f ->
  Proper (R ==> S ==> T ==> iff) f.
split; intros.
 apply H2 with x x0 x1; trivial.

 apply H2 with y y0 y1; trivial; symmetry; trivial.
Qed.

Lemma morph_impl_iff4 : forall A B C D R S T U f,
  @Symmetric A R ->
  @Symmetric B S ->
  @Symmetric C T ->
  @Symmetric D U ->
  Proper (R ==> S ==> T ==> U ==> impl) f ->
  Proper (R ==> S ==> T ==> U ==> iff) f.
split; intros.
 apply H3 with x x0 x1 x2; trivial.

 apply H3 with y y0 y1 y2; trivial; symmetry; trivial.
Qed.

Instance wf_mono_eq A (eqA:A->A->Prop) :
  Reflexive eqA ->
  Proper ((eq==>eqA-->impl) --> eqA ==> impl) (@Acc A).
do 4 red; intros.
revert y0 H1.
induction H2; intros.
apply Acc_intro; intros.
apply H2 with y1; trivial.
apply H0 with (3:=H4); trivial.
Qed.

Instance wf_mono A (eqA:A->A->Prop) :
  Reflexive eqA ->
  Proper ((eqA==>eqA-->impl) --> eqA ==> impl) (@Acc A).
do 3 red; intros.
apply (wf_mono_eq H); trivial.
do 3 red; intros.
subst y1;apply H0; trivial.
Qed.

Instance wf_morph A (eqA:A->A->Prop) :
  Reflexive eqA ->
  Symmetric eqA ->
  Proper ((eqA==>eqA==>iff) ==> eqA ==> iff) (@Acc A).
intros.
apply morph_impl_iff2; auto with *.
 do 3 red; intros.
 symmetry; apply H1; symmetry; trivial.

 do 2 red; intros.
 apply wf_mono; trivial.
 do 3 red; intros.
 red; apply H1; trivial.
 symmetry; trivial.
Qed.

(* Pb: this is not proved automatically:*)
Goal forall A (eqA:A->A->Prop) P F f g ,
  Equivalence eqA ->
  Proper (eqA ==> iff) P ->
  Proper (eqA ==> eqA) F ->
  eqA f g ->
  (P (F f) <-> P (F g)).
intros. rewrite H2. reflexivity.
Qed.
(*rewrite H2. fails
red; rewrite H2.  succeeds
*)


(******************************************************************)
(** Relations additional properties *)

Definition prod_eq A B R1 R2 (p1 p2:A*B) :=
  R1 (fst p1) (fst p2) /\ R2 (snd p1) (snd p2).

Lemma clos_trans_transp : forall A R x y,
  clos_trans A R x y ->
  clos_trans A (transp _ R) y x.
induction 1.
 apply t_step; trivial.
 apply t_trans with y; trivial.
Qed.

Instance prod_equiv A B (R1:relation A) (R2:relation B) :
  Equivalence R1 ->
  Equivalence R2 ->
  Equivalence (prod_eq R1 R2).
intros eq1 eq2.
split; red; intros.
 split; reflexivity.

 destruct H; split; symmetry; trivial.

 destruct H; destruct H0.
 split; [transitivity (fst y)|transitivity (snd y)]; trivial. 
Qed.

Notation list_eq := List.Forall2.

Instance list_eq_refl A (R:relation A) : Reflexive R -> Reflexive (list_eq R).
red; intros.
induction x; simpl; auto.
Qed.

Instance list_eq_sym A (R:relation A) : Symmetric R -> Symmetric (list_eq R).
red; intros.
revert y H0; induction x; destruct y; intros; auto.
 inversion H0.
 inversion H0.
inversion_clear H0.
constructor; auto.
Qed.

Instance list_eq_trans A (R:relation A) : Transitive R -> Transitive (list_eq R).
red.
induction x; destruct y; destruct z; intros; auto.
 inversion H0.
 inversion H1.
 inversion H1.
inversion_clear H0.
inversion_clear H1.
constructor; eauto.
Qed.


(******************************************************************)
(** More arithmetics... *)
Require Import Omega.

Lemma succ_max_distr : forall n m, S (max n m) = max (S n) (S m).
induction n; destruct m; simpl; reflexivity.
Qed.

Lemma max_split1 : forall x y z, z < x -> z < max x y.
induction x; simpl; intros.
 apply False_ind; omega.

 destruct y; trivial.
  destruct z; try omega.
   assert (z < x) by omega. specialize IHx with (1:=H0) (y:=y). omega.
Qed.

Lemma max_split2 : forall x y z, z < y -> z < max x y.
induction x; simpl; intros; trivial.
 destruct y; trivial.
  apply False_ind; omega.
 
  destruct z; try omega.
   assert (z < y) by omega. specialize IHx with (1:=H0). omega.
Qed.

Lemma max_comb : forall x y z, z < max x y -> z < x \/ z < y.
induction x; simpl; intros.
 right; trivial.

 destruct y.
  left; trivial.

  destruct z.
   left; omega.

   assert (z < max x y) by omega.
   specialize IHx with (1:=H0). destruct IHx; [left | right]; omega.
Qed.

Fixpoint plus_rev m n :=
  match m with 0 => n | S m' => plus_rev m' (S n) end.

Lemma plus_rev_def m n :
  plus_rev m n = m+n.
revert n; induction m; simpl; intros; auto.
rewrite IHm; trivial.
rewrite plus_n_Sm; trivial.
Qed.
