(** Saturated sets constructions related to natural numbers: interpreting constructors,
    dependent pattern-matching and fixpoint. Does not support size annotations. *)

Set Implicit Arguments.
Require Import basic Lambda Can Sat.
Require Import ZF.


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


Module Type SimpleNats.
  Parameter N Nbot : set.
  Parameter N_Nbot : N ⊆ Nbot.
  Parameter Ndec : forall n, n ∈ Nbot -> n∈N \/ ~n∈N.

  Parameter zero : set.
  Parameter succ : set -> set.
  Parameter succ_morph : morph1 succ.
  Existing Instance succ_morph.

  Parameter zero_typ : zero ∈ N.
  Parameter succ_typ : forall n, n ∈ Nbot -> succ n ∈ N.
End SimpleNats.
  
Module Make (N:SimpleNats).
  Import N.
  
(** * Functional applying constructors of Nat to A *)

Definition fNAT (A:set->SAT) (k:set) :=
  piFAM(fun P =>
        prodSAT (P zero)
       (prodSAT (depSAT (fun n => n ∈ Nbot) (fun n => prodSAT (A n) (prodSAT (P n) (P (succ n)))))
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

Lemma fNAT_def t A k :
  inSAT t (fNAT A k) <->
  forall P f g,
  Proper (eq_set==>eqSAT) P ->
  inSAT f (P zero) ->
  inSAT g (depSAT(fun n=>n ∈ Nbot)(fun n => prodSAT (A n) (prodSAT (P n) (P (succ n))))) ->
  inSAT (App2 t f g) (P k).
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

Lemma fNAT_mono A B :
  (forall k, k ∈ Nbot -> inclSAT (A k) (B k)) ->
  forall k, inclSAT (fNAT A k) (fNAT B k).
unfold fNAT; intros.
apply interSAT_mono; intro P.
apply prodSAT_mono; auto with *.
apply prodSAT_mono; auto with *.
apply interSAT_mono; intros (n,tyn); simpl.
apply prodSAT_mono; auto with *.
apply H; trivial.
Qed.

(** * Realizability relation of Nat: fixpoint of fNAT *)

(** cNAT is intersection of all families that are post-fixpoint (that is,
    P s.t. fNAT P included in P) *)
Definition cNAT n :=
  depSAT (fun P => Proper (eq_set==>eqSAT) P /\
                   forall k, k ∈ N -> inclSAT (fNAT P k) (P k)) (fun P => P n).

Instance cNAT_morph : Proper (eq_set==>eqSAT) cNAT.
do 2 red; intros.
apply interSAT_morph.
apply indexed_relation_id; intros (P,(Pm,Pind)); simpl; auto.
Qed.

Lemma cNAT_post k :
  k ∈ N ->
  inclSAT (fNAT cNAT k) (cNAT k).
intros tyk t tsat.
unfold cNAT.
apply depSAT_intro; intros.
 apply sat_sn in tsat; trivial.

 apply H; trivial.
 revert t tsat.
 apply fNAT_mono.
 clear k tyk; intros k tyk t tsat.
 eapply depSAT_elim with (F:=fun P => P k); [apply tsat|].
 exact H.
Qed.

Definition fNAT' A k := condSAT (k∈N) (fNAT A k).
                                 
Lemma cNAT_pre_strict k :
  k ∈ N ->
  inclSAT (cNAT k) (fNAT cNAT k).
intros tyk t tsat.
apply condSAT_smaller with (P:=k ∈ N).
eapply depSAT_elim
 with (F:=fun P => P k) (1:=tsat) (x:=fNAT' cNAT).
split.
 do 2 red; intros; apply condSAT_morph.
  rewrite H; reflexivity.
 apply fNAT_morph; trivial; apply cNAT_morph.

 clear; intros k tyk.
 transitivity (fNAT cNAT k).
  apply fNAT_mono; clear; intros k tyk.
  destruct Ndec with (1:=tyk) as [tyk'|tyk'].
   unfold fNAT'; rewrite condSAT_ok; auto.
   apply cNAT_post; trivial.

   apply condSAT_neutral; trivial.

   unfold fNAT'; rewrite condSAT_ok; auto with *.
Qed.
  
Lemma cNAT_out k S :
  ~ k ∈ N ->
  inclSAT (cNAT k) S.
intros notn t tsat.
unfold cNAT, depSAT in tsat.
pose (P:= fun k => condSAT (k∈N) (cNAT k)).
assert (Pm : Proper (eq_set==>eqSAT) P).
 do 2 red; intros.
 apply condSAT_morph.
  rewrite H; reflexivity.
  apply cNAT_morph; trivial.
assert (Ppost:forall k, k ∈ N -> inclSAT (fNAT P k) (P k)).
 clear.
intros.
 transitivity (fNAT cNAT k).
  apply fNAT_mono; clear; intros k tyk.
  unfold P.
  apply condSAT_smaller.

  red; intros; unfold P.
  rewrite condSAT_ok; trivial.
  apply cNAT_post; trivial.
specialize interSAT_elim with (1:=tsat)
    (x:=exist (fun P=>Proper(eq_set==>eqSAT)P/\
                forall k,k∈N->inclSAT(fNAT P k)(P k)) P (conj Pm Ppost)).
simpl.
apply condSAT_neutral; red; auto with *.
Qed.

Lemma cNAT_pre k :
  k ∈ Nbot ->
  inclSAT (cNAT k) (fNAT cNAT k).
intros tyk t tsat.
destruct Ndec with (1:=tyk).
 apply cNAT_pre_strict; trivial.

 revert tsat; apply cNAT_out; trivial.
Qed.

(** Fixpoint equation *)
Lemma cNAT_eq : forall k, k ∈ N -> eqSAT (cNAT k) (fNAT cNAT k).
split.
 apply cNAT_pre; apply N_Nbot; trivial.
 apply cNAT_post; trivial.
Qed.

(** * Constructors *)

(** Interp of 0 *)
Definition ZE := Abs (Abs (Ref 1)).

Lemma ZE_iota t1 t2 :
  redp (App2 ZE t1 t2) t1.
unfold ZE.
eapply t_trans;[apply redp_app_l;apply t_step;apply red1_beta; reflexivity|].
unfold subst; simpl.
apply t_step.
apply red1_beta.
unfold subst; rewrite simpl_subst; trivial.
rewrite lift0; trivial.
Qed.

Lemma fNAT_ZE : forall A, inSAT ZE (fNAT A zero).
intros.
rewrite fNAT_def; intros.
unfold ZE.
eapply inSAT_context.
 intros.
 apply inSAT_exp; auto.
 exact H2.
unfold subst; simpl subst_rec.
apply inSAT_exp.
 apply sat_sn in H1; auto.
unfold subst; rewrite simpl_subst; auto.
rewrite lift0; auto.
Qed.

(** ZE realizes 0 *)
Lemma cNAT_ZE : inSAT ZE (cNAT zero).
rewrite cNAT_eq.
 apply fNAT_ZE.

 apply zero_typ.
Qed.

(** Interp of successor. Unlike in system F the function corresponding to the successor
    expects two arguments: the predecessor and the usual result of recursive call.
    S(n) is (fun f g => g n (n f g)) instead of the usual (fun f g => g (n f g)).
 *)

Definition SU := Abs (Abs (Abs
    (App2 (Ref 0) (Ref 2) (App2 (Ref 2) (Ref 1) (Ref 0))))).

Lemma SU_iota n t1 t2 :
  redp (App2 (App SU n) t1 t2) (App2 t2 n (App2 n t1 t2)).
unfold SU.
eapply t_trans.
 do 2 apply redp_app_l.
 apply t_step; apply red1_beta; reflexivity.
unfold subst; simpl.
eapply  t_trans.
 apply redp_app_l.
 apply t_step; apply red1_beta; reflexivity.
unfold subst; simpl.
rewrite simpl_subst; auto.
apply t_step; apply red1_beta.
unfold subst; simpl.
rewrite simpl_subst; auto.
rewrite simpl_subst; auto.
do 3 rewrite lift0.
reflexivity.
Qed.

Lemma fNAT_SU : forall A n t,
  n ∈ Nbot ->
  inSAT t (A n) ->
  inSAT t (fNAT A n) ->
  inSAT (App SU t) (fNAT A (succ n)).
intros A n t nty H H0.
unfold SU.
apply inSAT_exp;[auto|].
unfold subst; simpl subst_rec.
rewrite fNAT_def; intros.
eapply inSAT_context.
 intros.
 apply inSAT_exp; [right|].
  apply sat_sn in H2; trivial.
  eexact H4.
unfold subst; simpl subst_rec.
apply inSAT_exp; auto.
unfold subst; simpl subst_rec.
repeat rewrite simpl_subst; auto.
repeat rewrite lift0.
apply prodSAT_elim with (P n).
 apply prodSAT_elim with (2:=H).
 eapply (depSAT_elim _ H3); trivial.
 
 rewrite fNAT_def in H0.
 apply H0; trivial.
Qed.

(** SU realizes the successor *)
Lemma cNAT_SU n t :
  n ∈ Nbot ->
  inSAT t (cNAT n) ->
  inSAT (App SU t) (cNAT (succ n)). 
intros.
rewrite cNAT_eq.
 apply fNAT_SU; trivial.
 apply cNAT_pre; trivial.

 apply succ_typ; trivial.
Qed.

End Make.
