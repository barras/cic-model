(** Saturated sets constructions related to natural numbers: interpreting constructors,
    dependent pattern-matching and fixpoint. Does not support size annotations. *)

Set Implicit Arguments.
Require Import basic Can Sat.
Require Import ZF ZFind_nat.
Module Lc:=Lambda.


(** Quantification over families *)
Definition piFAM F :=
  depSAT (fun P:set->SAT => Proper (eq_set==>eqSAT)P) F.

Lemma piFAM_ax t F :
  inSAT t (piFAM F) <-> forall P, Proper (eq_set==>eqSAT)P->inSAT t (F P).
split; intros.
 apply depSAT_elim with (1:=H)(x:=P)(2:=H0).

 apply depSAT_intro; auto.
 apply sat_sn with (F (fun _ => snSAT)).
 apply H.
 do 2 red; reflexivity.
Qed.

Instance piFAM_morph : Proper (((eq_set==>eqSAT)==>eqSAT)==>eqSAT) piFAM.
do 2 red; intros.
apply interSAT_morph.
apply indexed_relation_id; intros (P,Pm); simpl; auto.
Qed.

(** * Functional applying constructors of Nat to A *)

Definition fNAT (A:set->SAT) (k:set) :=
  piFAM(fun P =>
        prodSAT (P ZERO)
       (prodSAT (depSAT (fun n => n ∈ NAT) (fun n => prodSAT (A n) (prodSAT (P n) (P (SUCC n)))))
                (P k))).

Instance fNAT_morph : Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) fNAT.
do 3 red; intros.
apply piFAM_morph.
red; intros.
apply prodSAT_morph.
 apply H1; reflexivity.

 apply prodSAT_morph; auto.
 apply interSAT_morph.
 apply indexed_relation_id; intros.
 apply prodSAT_morph; auto with *.
 apply prodSAT_morph; auto with *.
Qed.

Lemma fNAT_def : forall t A k,
  inSAT t (fNAT A k) <->
  forall P f g,
  Proper (eq_set==>eqSAT) P ->
  inSAT f (P ZERO) ->
  inSAT g (depSAT(fun n=>n ∈ NAT)(fun n => prodSAT (A n) (prodSAT (P n) (P (SUCC n))))) ->
  inSAT (Lc.App2 t f g) (P k).
intros.
unfold fNAT.
rewrite piFAM_ax.
apply fa_morph; intros P.
split; intros.
 apply prodSAT_elim with (2:=H1) in H; trivial.
 apply prodSAT_elim with (1:=H); trivial.

 apply prodSAT_intro'; intros f satf.
 apply prodSAT_intro'; intros g satg.
 apply H; trivial.
Qed.

Lemma fNAT_mono : forall A B,
  (forall k, inclSAT (A k) (B k)) -> forall k, inclSAT (fNAT A k) (fNAT B k).
unfold fNAT; intros.
apply interSAT_mono; intro P.
apply prodSAT_mono; auto with *.
apply prodSAT_mono; auto with *.
apply interSAT_mono; intro n.
apply prodSAT_mono; auto with *.
apply H.
Qed.

(** * Realizability relation of Nat: fixpoint of fNAT *)

(** cNAT is intersection of all families that are post-fixpoint (that is,
    P s.t. fNAT P included in P) *)
Definition cNAT n :=
  depSAT (fun P => Proper (eq_set==>eqSAT) P /\ forall k, inclSAT (fNAT P k) (P k)) (fun P => P n).

Instance cNAT_morph : Proper (eq_set==>eqSAT) cNAT.
do 2 red; intros.
apply interSAT_morph.
apply indexed_relation_id; intros (P,(Pm,Pind)); simpl; auto.
Qed.

Lemma cNAT_post : forall k, inclSAT (fNAT cNAT k) (cNAT k).
red; intros.
unfold cNAT.
apply depSAT_intro; intros.
 apply sat_sn in H; trivial.

 apply H0.
 revert t H.
 apply fNAT_mono.
 red; intros.
 eapply depSAT_elim with (F:=fun P => P k0); [apply H|].
 exact H0.
Qed.

Lemma cNAT_pre : forall k, inclSAT (cNAT k) (fNAT cNAT k).
red; intros.
eapply depSAT_elim with (F:=fun P => P k) (1:=H).
split.
 apply fNAT_morph; apply cNAT_morph.

 apply fNAT_mono.
 apply cNAT_post.
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
eapply inSAT_context.
 intros.
 apply inSAT_exp; auto.
 exact H2.
unfold Lc.subst; simpl Lc.subst_rec.
apply inSAT_exp.
 apply sat_sn in H1; auto.
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

Lemma fNAT_SU : forall A n t,
  n ∈ NAT ->
  inSAT t (A n) ->
  inSAT t (fNAT A n) ->
  inSAT (Lc.App SU t) (fNAT A (SUCC n)).
intros A n t nty H H0.
unfold SU.
apply inSAT_exp;[auto|].
unfold Lc.subst; simpl Lc.subst_rec.
rewrite fNAT_def; intros.
eapply inSAT_context.
 intros.
 apply inSAT_exp; [right|].
  apply sat_sn in H2; trivial.
  eexact H4.
unfold Lc.subst; simpl Lc.subst_rec.
apply inSAT_exp; auto.
unfold Lc.subst; simpl Lc.subst_rec.
repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
apply prodSAT_elim with (P n).
 apply prodSAT_elim with (2:=H).
 eapply (depSAT_elim _ H3); trivial.

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

Lemma cNAT_mt t :
  inSAT t (cNAT empty) ->
  inSAT (Lc.App SU t) (cNAT empty).
intros.
assert (tsat := H).
rewrite cNAT_eq in H|-*.
rewrite fNAT_def in H|-*; intros.
eapply inSAT_context; intros.
 eapply inSAT_context; intros.
  apply inSAT_exp;[auto|].
 exact H4.
 unfold Lc.subst; simpl Lc.subst_rec.
 apply inSAT_exp;[right|].
  apply sat_sn in H1; trivial.
 unfold Lc.subst; simpl Lc.subst_rec.
 repeat rewrite Lc.simpl_subst; auto.
 exact H3.
apply inSAT_exp;[right|].
 apply sat_sn in H2; trivial.
unfold Lc.subst; simpl Lc.subst_rec.
repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
apply prodSAT_elim with (P empty).
 apply prodSAT_elim with (cNAT empty); trivial.
 admit.

 apply H; trivial.
Qed.
