(** Saturated sets constructions related to natural numbers: interpreting constructors,
    dependent pattern-matching and fixpoint. Does not support size annotations.

    It uses the representation of natural numbers of ZFnats, which simplifies things since N contains
    the empty set.
 *)

Set Implicit Arguments.
Require Import basic Can Sat.
Require Import ZF ZFcoc ZFind_nat ZFind_natbot.
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
       (prodSAT (depSAT (fun n => n ∈ cc_bot NAT')
                  (fun n => prodSAT (A n) (prodSAT (P n) (P (SUCC n)))))
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


Lemma fNAT_mono : forall A B,
  (forall k, k ∈ cc_bot NAT' -> inclSAT (A k) (B k)) -> forall k, inclSAT (fNAT A k) (fNAT B k).
unfold fNAT; intros.
apply interSAT_mono; intro P.
apply prodSAT_mono; auto with *.
apply prodSAT_mono; auto with *.
apply interSAT_mono; intro n.
apply prodSAT_mono; auto with *.
red; destruct n; simpl; auto.
Qed.


Lemma fNAT_def : forall t A k,
  inSAT t (fNAT A k) <->
  forall P f g,
  Proper (eq_set==>eqSAT) P ->
  inSAT f (P ZERO) ->
  inSAT g (depSAT(fun n=>n ∈ cc_bot NAT')
             (fun n => prodSAT (A n) (prodSAT (P n) (P (SUCC n))))) ->
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

(** * Realizability relation of Nat: fixpoint of fNAT *)

(** cNAT is intersection of all families that are post-fixpoint (that is,
    P s.t. fNAT P included in P) *)
Definition cNAT n :=
  depSAT (fun P => Proper (eq_set==>eqSAT) P /\
            forall k, k ∈ NAT' -> inclSAT (fNAT P k) (P k)) (fun P => P n).

Instance cNAT_morph : Proper (eq_set==>eqSAT) cNAT.
do 2 red; intros.
apply interSAT_morph.
apply indexed_relation_id; intros (P,(Pm,Pind)); simpl; auto.
Qed.

Lemma cNAT_post : forall k, k ∈ NAT' -> inclSAT (fNAT cNAT k) (cNAT k).
red; intros k tyk t tsat.
unfold cNAT.
apply depSAT_intro; intros.
 apply sat_sn in tsat; trivial.

 apply H; trivial.
 revert t tsat.
 apply fNAT_mono.
 red; intros.
 eapply depSAT_elim with (F:=fun P => P k0); [apply H1|].
 exact H.
Qed.


Lemma cNAT_mt S :
  inclSAT (cNAT empty) S.
red; intros.
unfold cNAT, depSAT in H.
pose (P:= fun k => condSAT (~k==empty) (cNAT k)).
assert (Pm : Proper (eq_set==>eqSAT) P).
 do 2 red; intros.
 apply condSAT_morph.
  rewrite H0; reflexivity.
  apply cNAT_morph; trivial.
assert (Ppost:forall k, k ∈ NAT' -> inclSAT (fNAT P k) (P k)).
 intros.
 transitivity (fNAT cNAT k).
  apply fNAT_mono; intros.
  unfold P.
  apply cc_bot_ax in H1; destruct H1.
   apply condSAT_neutral; red; auto.

   red; intros.
   rewrite condSAT_ok in H2; trivial.
   apply mt_not_in_NATf' in H1; auto.

  red; intros; unfold P.
  rewrite condSAT_ok.
   apply cNAT_post; trivial.

   apply mt_not_in_NATf' in H0; auto.

specialize interSAT_elim with (1:=H)
    (x:=exist (fun P=>Proper(eq_set==>eqSAT)P/\
                forall k,k∈NAT'->inclSAT(fNAT P k)(P k)) P (conj Pm Ppost)).
simpl.
apply condSAT_neutral; red; auto with *.
Qed.


Lemma cNAT_pre : forall k, k ∈ NAT' -> inclSAT (cNAT k) (fNAT cNAT k).
red; intros k tyk t tsat.
rewrite <- condSAT_ok with (P:=k ∈ NAT'); trivial.
eapply depSAT_elim with (F:=fun P => P k) (1:=tsat) (x:=fun k=>condSAT(k∈NAT')(fNAT cNAT k)).
split.
 do 2 red; intros; apply condSAT_morph.
  rewrite H; reflexivity.
 apply fNAT_morph; trivial; apply cNAT_morph.

 intros.
 transitivity (fNAT cNAT k0).
  apply fNAT_mono; intros.
   apply cc_bot_ax in H0; destruct H0.
    apply condSAT_neutral.
    intro h; apply mt_not_in_NATf' in h; auto with *.

    intros t'; rewrite condSAT_ok; auto.
    apply cNAT_post; trivial.

  intros t'; rewrite condSAT_ok; auto.
Qed.

(** Fixpoint equation *)
Lemma cNAT_eq : forall k, k ∈ NAT' -> eqSAT (cNAT k) (fNAT cNAT k).
split.
 apply cNAT_pre; trivial.
 apply cNAT_post; trivial.
Qed.

Lemma cNAT'_eq : forall k, k ∈ cc_bot NAT' ->
  eqSAT (cNAT k) (condSAT (k∈NAT') (fNAT cNAT k)).
intros.
apply cc_bot_ax in H; destruct H.
 assert (rmk : ~ k ∈ NAT').
  intro h; apply mt_not_in_NATf' in h; auto with *.
 split.
  rewrite H.
  apply cNAT_mt; trivial.

  apply condSAT_neutral; trivial.

 rewrite condSAT_ok; auto.
 apply cNAT_eq; trivial.
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

 apply ZERO_typ'.
Qed.

(** Interp of successor. Unlike in system F the function corresponding to the successor
    expects two arguments: the predecessor and the usual result of recursive call.
    S(n) is (fun f g => g n (n f g)) instead of the usual (fun f g => g (n f g)).
    However, we need a guarded version, because in the SN proof in SN_NAT, (S ⊥) is not
    a value, the successor of empty needs to be empty.
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
  n ∈ cc_bot NAT' ->
  inSAT t (A n) ->
  inSAT t (fNAT A n) ->
  inSAT (App SU t) (fNAT A (SUCC n)).
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
 eapply (depSAT_elim _ H3); auto.

 rewrite fNAT_def in H0.
 apply H0; trivial.
Qed.

(** SU realizes the successor *)
Lemma cNAT_SU : forall n t, n ∈ cc_bot NAT' -> inSAT t (cNAT n) ->
  inSAT (App SU t) (cNAT (SUCC n)). 
intros.
rewrite cNAT'_eq.
 rewrite condSAT_ok.
  apply fNAT_SU; trivial.
  apply cc_bot_ax in H; destruct H.
   rewrite H in H0.
   revert H0; apply cNAT_mt.

   apply cNAT_pre; trivial.

  apply SUCC_typ'; trivial.

 apply cc_bot_intro; apply SUCC_typ'; trivial.
Qed.

Definition WHEN_NAT :=
  Abs (App2 (Ref 0) (Abs (Ref 0)) (Abs (Abs (Abs (Ref 0))))).

Definition WHEN_NAT_ZE u :
  redp (App2 WHEN_NAT ZE u) u.
unfold WHEN_NAT.
eapply t_trans.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
rewrite lift0.
eapply t_trans.
 apply redp_app_l.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
unfold lift; simpl.
eapply t_trans.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
apply t_step; apply red1_beta.
unfold subst; simpl.
rewrite lift0; reflexivity.
Qed.

Definition WHEN_NAT_SU a u :
  redp (App2 WHEN_NAT (App SU a) u) u.
unfold WHEN_NAT.
eapply t_trans.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
rewrite lift0.
eapply t_trans.
 apply redp_app_l.
 apply SU_iota.
eapply t_trans.
 apply redp_app_l.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
eapply t_trans.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
apply t_step; apply red1_beta.
unfold subst; simpl.
rewrite lift0; reflexivity.
Qed.


(* More complicated def in fNAT, but simpler proofs:

(** * Functional applying constructors of Nat to A *)

Definition fNAT (A:set->SAT) (k:set) :=
  piFAM(fun P =>
        prodSAT (P ZERO)
       (prodSAT (depSAT (fun n => n ∈ cc_bot NAT')
                  (fun n => prodSAT (condSAT (n∈NAT')(A n)) (prodSAT (P n) (P (SUCC n)))))
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
 apply condSAT_morph; auto with *.
 apply prodSAT_morph; auto with *.
Qed.

Instance condSAT_mono :
  Proper (impl ==> inclSAT ==> inclSAT) condSAT.
unfold condSAT, depSAT; do 4 red; intros.
apply interSAT_intro.
 econstructor; reflexivity.
intros (C,?); simpl.
assert (rmk : x -> inclSAT x0 C).
 intros.
 transitivity y0; auto.
apply interSAT_elim with (1:=H1)(x:=exist (fun _=>_) C rmk). 
Qed.

Lemma condSAT_ext (P Q:Prop) S S':
  (P -> Q) ->
  (P -> Q -> inclSAT S S') ->
  inclSAT (condSAT P S) (condSAT Q S').
unfold condSAT, depSAT; red; intros.
apply interSAT_intro.
 econstructor; reflexivity.
intros (C,?); simpl.
assert (rmk : P -> inclSAT S C).
 intros.
 transitivity S'; auto.
apply interSAT_elim with (1:=H1)(x:=exist (fun _=>_) C rmk). 
Qed.


Lemma fNAT_mono : forall A B,
  (forall k, k ∈ NAT' -> inclSAT (A k) (B k)) -> forall k, inclSAT (fNAT A k) (fNAT B k).
unfold fNAT; intros.
apply interSAT_mono; intro P.
apply prodSAT_mono; auto with *.
apply prodSAT_mono; auto with *.
apply interSAT_mono; intro n.
apply prodSAT_mono; auto with *.
apply condSAT_ext; auto.
Qed.


Lemma fNAT_def : forall t A k,
  inSAT t (fNAT A k) <->
  forall P f g,
  Proper (eq_set==>eqSAT) P ->
  inSAT f (P ZERO) ->
  inSAT g (depSAT(fun n=>n ∈ cc_bot NAT')
             (fun n => prodSAT (condSAT (n∈NAT')(A n)) (prodSAT (P n) (P (SUCC n))))) ->
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

(** * Realizability relation of Nat: fixpoint of fNAT *)

(** cNAT is intersection of all families that are post-fixpoint (that is,
    P s.t. fNAT P included in P) *)
Definition cNAT n :=
  depSAT (fun P => Proper (eq_set==>eqSAT) P /\
            forall k, k ∈ NAT' -> inclSAT (fNAT P k) (P k)) (fun P => P n).

Instance cNAT_morph : Proper (eq_set==>eqSAT) cNAT.
do 2 red; intros.
apply interSAT_morph.
apply indexed_relation_id; intros (P,(Pm,Pind)); simpl; auto.
Qed.

Lemma cNAT_post : forall k, k ∈ NAT' -> inclSAT (fNAT cNAT k) (cNAT k).
red; intros k tyk t tsat.
unfold cNAT.
apply depSAT_intro; intros.
 apply sat_sn in tsat; trivial.

 apply H; trivial.
 revert t tsat.
 apply fNAT_mono.
 red; intros.
 eapply depSAT_elim with (F:=fun P => P k0); [apply H1|].
 exact H.
Qed.

Lemma cNAT_pre : forall k, k ∈ NAT' -> inclSAT (cNAT k) (fNAT cNAT k).
red; intros k tyk t tsat.
eapply depSAT_elim with (F:=fun P => P k) (1:=tsat).
split.
 apply fNAT_morph; apply cNAT_morph.

 intros.
 apply fNAT_mono.
 apply cNAT_post.
Qed.

(** Fixpoint equation *)
Lemma cNAT_eq : forall k, k ∈ NAT' -> eqSAT (cNAT k) (fNAT cNAT k).
split.
 apply cNAT_pre; trivial.
 apply cNAT_post; trivial.
Qed.


Lemma cNAT_mt k S :
  ~ k ∈ NAT' ->
  inclSAT (cNAT k) S.
red; intros.
unfold cNAT, depSAT in H0.
pose (P:= fun k => condSAT (k ∈ NAT') (cNAT k)).
assert (Pm : Proper (eq_set==>eqSAT) P).
 do 2 red; intros.
 apply condSAT_morph.
  rewrite H1; reflexivity.
  apply cNAT_morph; trivial.
assert (forall k, k ∈ NAT' -> inclSAT (fNAT P k) (P k)).
 intros.
 transitivity (fNAT cNAT k0).
  apply fNAT_mono; intros.
  unfold P.
  red; intros.
  rewrite condSAT_ok in H3; trivial.

  red; intros; unfold P.
  rewrite condSAT_ok; trivial.
  apply cNAT_post; trivial.
specialize interSAT_elim with (1:=H0)
    (x:=exist (fun P=>Proper(eq_set==>eqSAT)P/\
                forall k,k∈NAT'->inclSAT(fNAT P k)(P k)) P (conj Pm H1)).
simpl.
apply condSAT_neutral; trivial.
Qed.

Lemma cNAT'_eq : forall k, k ∈ cc_bot NAT' ->
  eqSAT (cNAT k) (condSAT (k∈NAT') (fNAT cNAT k)).
intros.
apply cc_bot_ax in H; destruct H.
 assert (rmk : ~ k ∈ NAT').
  intro h; apply mt_not_in_NATf' in h; auto with *.
 split.
  apply cNAT_mt; trivial.

  apply condSAT_neutral; trivial.

 rewrite condSAT_ok; auto.
 apply cNAT_eq; trivial.
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

 apply ZERO_typ'.
Qed.

(** Interp of successor. Unlike in system F the function corresponding to the successor
    expects two arguments: the predecessor and the usual result of recursive call.
    S(n) is (fun f g => g n (n f g)) instead of the usual (fun f g => g (n f g)).
    However, we need a guarded version, because in the SN proof in SN_NAT, (S ⊥) is not
    a value, the successor of empty needs to be empty.
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
  n ∈ cc_bot NAT' ->
  inSAT t (condSAT (n∈NAT') (A n)) ->
  inSAT t (fNAT A n) ->
  inSAT (App SU t) (fNAT A (SUCC n)).
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
 eapply (depSAT_elim _ H3); auto.

 rewrite fNAT_def in H0.
 apply H0; trivial.
Qed.

(** SU realizes the successor *)
Lemma cNAT_SU : forall n t, n ∈ cc_bot NAT' -> inSAT t (cNAT n) ->
  inSAT (App SU t) (cNAT (SUCC n)). 
intros.
rewrite cNAT'_eq.
 rewrite condSAT_ok.
  apply fNAT_SU; trivial.
admit. (* condSAT in fNAT useless *)
   apply cc_bot_ax in H; destruct H.
    revert H0; apply cNAT_mt.
    intro h; apply mt_not_in_NATf' in h; auto with *.

    apply cNAT_pre; trivial.

  apply SUCC_typ'; trivial.

 apply cc_bot_intro; apply SUCC_typ'; trivial.
Qed.

Definition WHEN_NAT :=
  Abs (App2 (Ref 0) (Abs (Ref 0)) (Abs (Abs (Abs (Ref 0))))).

Definition WHEN_NAT_ZE u :
  redp (App2 WHEN_NAT ZE u) u.
unfold WHEN_NAT.
eapply t_trans.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
rewrite lift0.
eapply t_trans.
 apply redp_app_l.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
unfold lift; simpl.
eapply t_trans.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
apply t_step; apply red1_beta.
unfold subst; simpl.
rewrite lift0; reflexivity.
Qed.

Definition WHEN_NAT_SU a u :
  redp (App2 WHEN_NAT (App SU a) u) u.
unfold WHEN_NAT.
eapply t_trans.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
rewrite lift0.
eapply t_trans.
 apply redp_app_l.
 apply SU_iota.
eapply t_trans.
 apply redp_app_l.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
eapply t_trans.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
apply t_step; apply red1_beta.
unfold subst; simpl.
rewrite lift0; reflexivity.
Qed.

*)
