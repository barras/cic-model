Require Import Lambda.

Set Implicit Arguments.

Definition indexed_relation A A' B (R:B->B->Prop) (f:A->B) (g:A'->B) :=
  (forall x, exists y, R (f x) (g y)) /\
  (forall y, exists x, R (f x) (g y)).

(* Theory of saturated sets *)

Module Type SAT.
  Parameter SAT : Type.
  Parameter eqSAT : SAT -> SAT -> Prop.
  Parameter inSAT : term -> SAT -> Prop.
  Parameter eqSAT_def : forall X Y,
    eqSAT X Y <-> (forall t, inSAT t X <-> inSAT t Y).
  Definition inclSAT A B := forall t, inSAT t A -> inSAT t B.

  Parameter inSAT_morph : Proper ((@eq term) ==> eqSAT ==> iff) inSAT.

  Parameter sat_sn : forall t S, inSAT t S -> sn t.
  Parameter daimon : term.
  Parameter varSAT : forall S, inSAT daimon S.

  Parameter snSAT : SAT.
  Parameter snSAT_intro : forall t, sn t -> inSAT t snSAT.

  Parameter prodSAT : SAT -> SAT -> SAT.
  Parameter prodSAT_morph : Proper (eqSAT ==> eqSAT ==> eqSAT) prodSAT.
  Parameter prodSAT_intro : forall A B m,
    (forall v, inSAT v A -> inSAT (subst v m) B) ->
    inSAT (Abs m) (prodSAT A B).
  Parameter prodSAT_elim : forall A B u v,
    inSAT u (prodSAT A B) ->
    inSAT v A ->
    inSAT (App u v) B.

  Parameter interSAT : forall A:Type, (A -> SAT) -> SAT.
  Parameter interSAT_morph : forall A A' (F:A->SAT) (G:A'->SAT),
    indexed_relation eqSAT F G ->
    eqSAT (interSAT F) (interSAT G).
  Parameter interSAT_intro : forall A F u,
    A ->
    (forall x:A, inSAT u (F x)) ->
    inSAT u (interSAT F).
  Parameter interSAT_elim : forall A F u,
    inSAT u (interSAT F) ->
    forall x:A, inSAT u (F x).

  Existing Instance inSAT_morph.
  Existing Instance prodSAT_morph.

End SAT.

(* Instantiating this signature with Girard's reducibility candidates *)
Require Import Can.

Module SatSet <: SAT.

  Definition SAT := {P:term->Prop|is_cand P}.
  Definition inSAT t (S:SAT) := proj1_sig S t.
  Definition eqSAT X Y := forall t, inSAT t X <-> inSAT t Y.
  Lemma eqSAT_def : forall X Y,
    eqSAT X Y <-> (forall t, inSAT t X <-> inSAT t Y).
reflexivity.
Qed.

  Instance inSAT_morph : Proper ((@eq term) ==> eqSAT ==> iff) inSAT.
do 3 red; intros; unfold inSAT.
rewrite H.
exact (H0 y).
Qed.

  Definition inclSAT A B := forall t, inSAT t A -> inSAT t B.

  Lemma sat_sn : forall t S, inSAT t S -> sn t.
destruct S; simpl; intros.
apply (incl_sn _ i); trivial.
Qed.

  Definition daimon := Ref 0.

  Lemma varSAT : forall S, inSAT daimon S.
destruct S; simpl; intros.
apply var_in_cand with (1:=i).
Qed.

  Definition snSAT : SAT := exist _ sn cand_sn.

  Lemma snSAT_intro : forall t, sn t -> inSAT t snSAT.
do 3 red; trivial.
Qed.

  Definition prodSAT (X Y:SAT) : SAT.
exists (Arr (proj1_sig X) (proj1_sig Y)).
apply is_cand_Arr; apply proj2_sig.
Defined.

  Instance prodSAT_morph : Proper (eqSAT ==> eqSAT ==> eqSAT) prodSAT.
do 3 red; intros.
destruct x; destruct y; destruct x0; destruct y0;
  unfold prodSAT, eqSAT in *; simpl in *; intros.
apply eq_can_Arr; trivial.
Qed.

  Lemma prodSAT_intro : forall A B m,
    (forall v, inSAT v A -> inSAT (subst v m) B) ->
    inSAT (Abs m) (prodSAT A B).
intros (A,A_can) (B,B_can) m in_subst; simpl in *.
apply Abs_sound_Arr; auto.
Qed.

  Lemma prodSAT_elim : forall A B u v,
    inSAT u (prodSAT A B) ->
    inSAT v A ->
    inSAT (App u v) B.
intros (A,A_can) (B,B_can) u v u_in v_in; simpl in *.
red in u_in.
auto.
Qed.

  Definition interSAT (A:Type) (F:A -> SAT) : SAT :=
    exist _ (Inter A (fun x => proj1_sig (F x)))
      (is_can_Inter _ _ (fun x => proj2_sig (F x))).

  Lemma interSAT_morph : forall A A' (F:A->SAT) (G:A'->SAT),
    indexed_relation eqSAT F G ->
    eqSAT (interSAT F) (interSAT G).
intros A A' F G sim_FG.
unfold eqSAT, interSAT; simpl.
apply eq_can_Inter; trivial.
Qed.

  Lemma interSAT_intro : forall A F u,
    A ->
    (forall x:A, inSAT u (F x)) ->
    inSAT u (interSAT F).
unfold inSAT, interSAT, Inter; simpl; intros.
split; intros; trivial.
apply (incl_sn _ (proj2_sig (F X))); trivial.
Qed.

  Lemma interSAT_elim : forall A F u,
    inSAT u (interSAT F) ->
    forall x:A, inSAT u (F x).
unfold inSAT, interSAT, Inter; simpl; intros.
destruct H; trivial.
Qed.

End SatSet.

Export SatSet.

Instance eqSAT_equiv : Equivalence eqSAT.
split; red; intros.
 rewrite eqSAT_def; reflexivity.
 rewrite eqSAT_def in H|-*; symmetry; trivial.
 rewrite eqSAT_def in H,H0|-*; intros;
   transitivity (inSAT t y); trivial.
Qed.

Lemma interSAT_morph_subset :
  forall A (P Q:A->Prop) (F:sig P->SAT) (G:sig Q->SAT),
  (forall x, P x <-> Q x) ->
  (forall x Px Qx,
   eqSAT (F (exist P x Px)) (G (exist Q x Qx))) ->
  eqSAT (interSAT F) (interSAT G).
intros.
apply interSAT_morph; red; split; intros.
 destruct x; simpl.
 exists (exist Q x (proj1 (H x) p)); auto.

 destruct y; simpl.
 exists (exist P x (proj2 (H x) q)); auto.
Qed.

  Lemma KSAT_intro : forall A t m,
    sn t ->
    inSAT m A ->
    inSAT (App2 K m t) A.
intros.
apply prodSAT_elim with snSAT.
2:apply snSAT_intro; trivial.
apply prodSAT_elim with A; trivial.
apply prodSAT_intro; intros.
unfold subst; simpl subst_rec.
apply prodSAT_intro; intros.
unfold subst; rewrite simpl_subst; trivial.
rewrite lift0; trivial.
Qed.

  Lemma SAT_daimon1 : forall S u,
    sn u ->
    inSAT (App daimon u) S.
destruct S; simpl; intros.
apply (sat1_in_cand 0 x); trivial.
Qed.
