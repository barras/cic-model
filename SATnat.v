(** Saturated sets constructions related to natural numbers: interpreting constructors,
    dependent pattern-matching and fixpoint. Does not support size annotations. *)

Set Implicit Arguments.
Require Import basic Can Sat.
Require Import ZF ZFind_nat.
Module Lc:=Lambda.

(** A family is a realizability relation for natural numbers *)
Record family := mkFam {
  fam :> set -> SAT;
  fam_mrph : forall x y,  x ∈ NAT -> x == y -> eqSAT (fam x) (fam y)
}.

Definition dflt_family : family.
(*begin show*)
exists (fun _ => snSAT).
(*end show*)
reflexivity.
Defined.

Definition eqfam (A B:family) :=
  forall x y, x ∈ NAT -> x == y -> eqSAT (A x) (B y).


(** Denotation of the intersection of (F(n)) expressions when n:Nat *)
Definition piNAT F :=
  interSAT (fun p:{n|n ∈ NAT} => F (proj1_sig p)).

Lemma piNAT_ax t F :
  inSAT t (piNAT F) <-> sn t /\ forall n, n ∈ NAT -> inSAT t (F n).
split; intros.
 split.
  apply sat_sn in H; trivial.

  intros.
  apply interSAT_elim with (x:=exist (fun n=>n ∈ NAT) n H0) in H; trivial.

 destruct H.
 split; trivial.
 destruct x; simpl; intros.
 apply H0; trivial.
Qed.


(** Quantification over families *)
Definition piFAM F :=
  interSAT (fun P:family => F P).

Lemma piFAM_ax t F :
  inSAT t (piFAM F) <-> forall P:family, inSAT t (F P).
split; intros.
 apply interSAT_elim with (x:=P) in H; trivial.

 apply interSAT_intro; auto.
 exact dflt_family.
Qed.

(** * Functional applying constructors of Nat to A *)

Definition fNAT (A:family) (k:set) :=
  piFAM(fun P =>
        prodSAT (P ZERO)
       (prodSAT (piNAT(fun n => prodSAT (A n) (prodSAT (P n) (P (SUCC n)))))
                (P k))).

Lemma fNAT_morph : forall A B, eqfam A B ->
  forall x y, x ∈ NAT -> x == y -> eqSAT (fNAT A x) (fNAT B y).
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
(*begin show*)
exists (fNAT A).
(*end show*)
intros.
apply fNAT_morph; trivial.
exact (fam_mrph A).
Defined.


Lemma fNAT_def : forall t A k,
  inSAT t (fNAT A k) <->
  forall (P:family) f g,
  inSAT f (P ZERO) ->
  inSAT g (piNAT(fun n => prodSAT (A n) (prodSAT (P n) (P (SUCC n))))) ->
  inSAT (Lc.App2 t f g) (P k).
intros.
unfold fNAT.
rewrite piFAM_ax.
apply fa_morph; intros P.
split; intros.
 apply prodSAT_elim with (2:=H0) in H.
 apply prodSAT_elim with (1:=H); trivial.

 intros f satf g satg.
 apply H; trivial.
Qed.

Lemma fNAT_mono : forall (A B:family),
  (forall k, inclSAT (A k) (B k)) -> forall k, inclSAT (fNAT A k) (fNAT B k).
unfold fNAT; intros.
apply interSAT_mono; intro P.
apply prodSAT_mono; auto with *.
apply prodSAT_mono; auto with *.
apply interSAT_mono; intros (n,tyn); simpl proj1_sig.
apply prodSAT_mono; auto with *.
apply H.
Qed.

(** * Realizability relation of Nat: fixpoint of fNAT *)

(** cNAT is intersection of all families that are post-fixpoint (that is,
    P s.t. fNAT P included in P) *)
Definition cNAT : family.
(*begin show*)
exists (fun n =>
  interSAT (fun P:{P:family|forall k, inclSAT (fNAT P k) (P k)} =>
    proj1_sig P n)).
(*end show*)
intros.
apply interSAT_morph.
split; intros.
 exists x0.
 apply (fam_mrph (proj1_sig x0)); trivial.
(**)
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

(** Fixpoint equation *)
Lemma cNAT_eq : forall k, eqSAT (cNAT k) (fNAT cNAT k).
split.
 apply cNAT_pre.
 apply cNAT_post.
Qed.

(** * Constructors *)

(** Interp of 0 *)
Definition ZE := Lc.Abs (Lc.Abs (Lc.Ref 1)).

Lemma ZE_iota t1 t2 :
  Lc.redp (Lc.App2 ZE t1 t2) t1.
unfold ZE.
eapply t_trans;[apply Lc.redp_app_l;apply t_step;apply Lc.red1_beta; reflexivity|].
unfold Lc.subst; simpl.
apply t_step.
apply Lc.red1_beta.
unfold Lc.subst; rewrite Lc.simpl_subst; trivial.
rewrite Lc.lift0; trivial.
Qed.

Lemma fNAT_ZE : forall A, inSAT ZE (fNAT A ZERO).
intros.
rewrite fNAT_def; intros.
unfold ZE.
eapply prodSAT_elim;[|eexact H0].
apply prodSAT_elim with (2:=H).
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
apply prodSAT_intro; intros.
unfold Lc.subst; rewrite Lc.simpl_subst; auto.
rewrite Lc.lift0; auto.
Qed.

(** ZE realizes 0 *)
Lemma cNAT_ZE : inSAT ZE (cNAT ZERO).
rewrite cNAT_eq.
apply fNAT_ZE.
Qed.

(** Interp of successor. Unlike in system F the function corresponding to the successor
    expects two arguments: the predecessor and the usual result of recursive call.
    S(n) is (fun f g => g n (n f g)) instead of the usual (fun f g => g (n f g)).
 *)

Definition SU := Lc.Abs (Lc.Abs (Lc.Abs
    (Lc.App2 (Lc.Ref 0) (Lc.Ref 2) (Lc.App2 (Lc.Ref 2) (Lc.Ref 1) (Lc.Ref 0))))).

Lemma SU_iota n t1 t2 :
  Lc.redp (Lc.App2 (Lc.App SU n) t1 t2) (Lc.App2 t2 n (Lc.App2 n t1 t2)).
unfold SU.
eapply t_trans.
 do 2 apply Lc.redp_app_l.
 apply t_step; apply Lc.red1_beta; reflexivity.
unfold Lc.subst; simpl.
eapply  t_trans.
 apply Lc.redp_app_l.
 apply t_step; apply Lc.red1_beta; reflexivity.
unfold Lc.subst; simpl.
rewrite Lc.simpl_subst; auto.
apply t_step; apply Lc.red1_beta.
unfold Lc.subst; simpl.
rewrite Lc.simpl_subst; auto.
rewrite Lc.simpl_subst; auto.
do 3 rewrite Lc.lift0.
reflexivity.
Qed.

Lemma fNAT_SU : forall (A:family) n t,
  n ∈ NAT ->
  inSAT t (A n) ->
  inSAT t (fNAT A n) ->
  inSAT (Lc.App SU t) (fNAT A (SUCC n)).
intros A n t tyn H H0.
unfold SU.
apply inSAT_exp;[right|].
 apply sat_sn in H0; trivial.
unfold Lc.subst; simpl Lc.subst_rec.
rewrite fNAT_def; intros.
eapply inSAT_context.
 intros.
 apply inSAT_exp; [right|].
  apply sat_sn in H1; trivial.
  eexact H3.
unfold Lc.subst; simpl Lc.subst_rec.
apply inSAT_exp.
 right; apply sat_sn in H2; trivial.
unfold Lc.subst; simpl Lc.subst_rec.
repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
apply prodSAT_elim with (P n).
 apply prodSAT_elim with (2:=H).
 rewrite piNAT_ax in H2; auto.
 destruct H2; auto.

 rewrite fNAT_def in H0.
 apply H0; trivial.
Qed.

(** SU realizes the successor *)
Lemma cNAT_SU : forall n t, n ∈ NAT -> inSAT t (cNAT n) -> inSAT (Lc.App SU t) (cNAT (SUCC n)). 
intros.
rewrite cNAT_eq.
apply fNAT_SU; trivial.
rewrite <- cNAT_eq; trivial.
Qed.

