Set Implicit Arguments.
Require Import basic Can Sat.
Require Import ZF ZFind_nat.
Import IZF.
Module Lc:=Lambda.

(* Saturated sets constructions related to natural numbers *)

Record family := mkFam {
  fam :> set -> SAT;
  fam_mrph : forall x y,  x \in NAT -> x == y -> eqSAT (fam x) (fam y)
}.

Definition dflt_family : family.
exists (fun _ => snSAT).
reflexivity.
Defined.

Definition eqfam (A B:family) :=
  forall x y, x \in NAT -> x == y -> eqSAT (A x) (B y).

Definition fNAT (A:family) (k:set) :=
  interSAT
    (fun P:family =>
      prodSAT (P ZERO)
     (prodSAT (interSAT (fun n:{n|n\in NAT} => let n:=proj1_sig n in
               prodSAT (A n) (prodSAT (P n) (P (SUCC n)))))
              (P k))).

Lemma fNAT_morph : forall A B, eqfam A B ->
  forall x y, x \in NAT -> x == y -> eqSAT (fNAT A x) (fNAT B y).
intros.
unfold fNAT.
apply interSAT_morph.
apply indexed_relation_id; intros.
apply prodSAT_morph.
 reflexivity.

 apply prodSAT_morph.
  apply interSAT_morph_subset; simpl proj1_sig; intros; auto with *.
  apply prodSAT_morph; auto with *.

  apply fam_mrph; trivial.
Qed.

Definition fNATf (A:family) : family.
exists (fNAT A).
intros.
apply fNAT_morph; trivial.
exact (fam_mrph A).
Defined.


Lemma fNAT_def : forall t A k,
  inSAT t (fNAT A k) <->
  forall (P:family) f g,
  inSAT f (P ZERO) ->
  (forall n m y, n \in NAT -> inSAT m (A n) -> inSAT y (P n) -> inSAT (Lc.App2 g m y) (P (SUCC n))) ->
  inSAT (Lc.App2 t f g) (P k).
unfold fNAT.
split; intros.
 apply interSAT_elim with (x:=P) in H.
 apply prodSAT_elim with (interSAT (fun n:{n|n\in NAT} =>
    let n:=proj1_sig n in prodSAT (A n) (prodSAT (P n) (P (SUCC n))))).
 apply prodSAT_elim with (2:=H0); trivial.
 apply interSAT_intro; trivial; intros.
  exists ZERO; apply ZERO_typ.
 destruct x as (n,?); simpl.
 do 2 red; intros.
 apply H1; trivial.

 apply interSAT_intro; intros.
  exists (fun _ => snSAT); reflexivity.
 simpl; do 2 red; intros.
 destruct H1.
 apply H; trivial.
 intros.
 apply H2 with (x0:=exist (fun x => x\in NAT) n H3); trivial.
Qed.

Lemma fNAT_mono : forall (A B:family),
  (forall k, inclSAT (A k) (B k)) -> forall k, inclSAT (fNAT A k) (fNAT B k).
unfold inclSAT; intros.
rewrite fNAT_def in H0 |- *; intros.
apply H0; intros; auto.
Qed.

(* Realizability relation of NAT: fixpoint of fNAT *)

Definition cNAT : family.
exists (fun n =>
  interSAT (fun P:{P:family|forall k, inclSAT (fNAT P k) (P k)} =>
    proj1_sig P n)).
intros.
apply interSAT_morph.
split; intros.
 exists x0.
 apply (fam_mrph (proj1_sig x0)); trivial.

 exists y0.
 apply (fam_mrph (proj1_sig y0)); trivial.
Defined.

Lemma cNAT_post : forall k, inclSAT (fNAT cNAT k) (cNAT k).
red; intros.
unfold cNAT.
apply interSAT_intro; intros.
 exists dflt_family; red; intros.
 apply sat_sn in H0; trivial.

 apply (proj2_sig x).
 revert t H.
 apply fNAT_mono.
 red; intros.
 apply interSAT_elim with (1:=H) (x:=x).
Qed.

Lemma cNAT_pre : forall k, inclSAT (cNAT k) (fNAT cNAT k).
red; intros.
apply interSAT_elim with (1:=H)
 (x:=exist (fun P => forall k, inclSAT (fNAT P k) (P k))
       (fNATf cNAT) (@fNAT_mono (fNATf cNAT) cNAT cNAT_post)).
Qed.

Lemma cNAT_eq : forall k, eqSAT (cNAT k) (fNAT cNAT k).
split.
 apply cNAT_pre.
 apply cNAT_post.
Qed.

(* Constructors *)

(* interp of 0 *)
Definition ZE := Lc.Abs (Lc.Abs (Lc.Ref 1)).

Lemma fNAT_ZE : forall A, inSAT ZE (fNAT A ZERO).
unfold fNAT, ZE; intros A.
apply interSAT_intro; trivial.
intro P.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
apply prodSAT_intro; intros.
unfold Lc.subst; rewrite Lc.simpl_subst; trivial; rewrite Lc.lift0; trivial.
Qed.

Lemma cNAT_ZE : inSAT ZE (cNAT ZERO).
rewrite cNAT_eq.
apply fNAT_ZE.
Qed.

(* interp of successor *)
Definition SU := Lc.Abs (Lc.Abs (Lc.Abs
    (Lc.App2 (Lc.Ref 0) (Lc.Ref 2) (Lc.App2 (Lc.Ref 2) (Lc.Ref 1) (Lc.Ref 0))))).

Lemma fNAT_SU : forall (A:family) n t,
  n \in NAT ->
  inSAT t (A n) ->
  inSAT t (fNAT A n) ->
  inSAT (Lc.App SU t) (fNAT A (SUCC n)).
intros A n t tyn H H0.
unfold fNAT, SU.
apply interSAT_intro; trivial.
intros P.
apply prodSAT_elim with (A:=interSAT (fun b:bool => if b then A n else fNAT A n)).
2:apply interSAT_intro; [left|intros [|]; trivial].
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec; rewrite Lc.simpl_subst; trivial.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec; repeat rewrite Lc.simpl_subst; trivial; repeat rewrite Lc.lift0.
specialize interSAT_elim with (x:=exist (fun n=>n\in NAT) n tyn) (1:=H3); simpl proj1_sig; intro.
specialize interSAT_elim with (x:=true) (1:=H1); intro.
specialize interSAT_elim with (x:=false) (1:=H1); intro.
specialize interSAT_elim with (x:=P) (1:=H6); intro.
clear H1.
apply prodSAT_elim with (A:=P n).
 apply prodSAT_elim with (A:=A n); trivial.

 apply prodSAT_elim with (2:=H2) in H7.
 apply prodSAT_elim with (1:=H7); trivial.
Qed.

Lemma cNAT_SU : forall n t, n \in NAT -> inSAT t (cNAT n) -> inSAT (Lc.App SU t) (cNAT (SUCC n)). 
intros.
rewrite cNAT_eq.
apply fNAT_SU; trivial.
rewrite <- cNAT_eq; trivial.
Qed.
