Set Implicit Arguments.
Require Import basic Can Sat.
Require Import ZF ZFind_nat.
Module Lc:=Lambda.

(** Saturated sets constructions related to natural numbers *)

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


Instance prodSAT_mono : Proper (inclSAT --> inclSAT ++> inclSAT) prodSAT.
do 4 red; intros.
intros u satu.
apply H0.
apply prodSAT_elim with (1:=H1); auto.
Qed.

Lemma interSAT_mono A (F G:A->SAT):
  (forall x, inclSAT (F x) (G x)) ->
  inclSAT (interSAT F) (interSAT G).
red; intros.
split; intros.
 apply sat_sn in H0; trivial.
apply H.
apply interSAT_elim with (1:=H0).
Qed.

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



Definition piFAM F :=
  interSAT (fun P:family => F P).

Lemma piFAM_ax t F :
  inSAT t (piFAM F) <-> forall P:family, inSAT t (F P).
split; intros.
 apply interSAT_elim with (x:=P) in H; trivial.

 apply interSAT_intro; auto.
 exact dflt_family.
Qed.

(** Functional applying constructors of Nat to A *)

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

Instance inclSAT_ord : PreOrder inclSAT.
split; red; intros.
 red; trivial.

 red; intros; auto.
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

(** Realizability relation of Nat: fixpoint of fNAT *)

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

Lemma cNAT_eq : forall k, eqSAT (cNAT k) (fNAT cNAT k).
split.
 apply cNAT_pre.
 apply cNAT_post.
Qed.

(** * Constructors *)

(** Interp of 0 *)
Definition ZE := Lc.Abs (Lc.Abs (Lc.Ref 1)).

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

Lemma cNAT_ZE : inSAT ZE (cNAT ZERO).
rewrite cNAT_eq.
apply fNAT_ZE.
Qed.

(** Interp of successor *)
Definition SU := Lc.Abs (Lc.Abs (Lc.Abs
    (Lc.App2 (Lc.Ref 0) (Lc.Ref 2) (Lc.App2 (Lc.Ref 2) (Lc.Ref 1) (Lc.Ref 0))))).

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

Lemma cNAT_SU : forall n t, n ∈ NAT -> inSAT t (cNAT n) -> inSAT (Lc.App SU t) (cNAT (SUCC n)). 
intros.
rewrite cNAT_eq.
apply fNAT_SU; trivial.
rewrite <- cNAT_eq; trivial.
Qed.

(** Pattern-matching *)

Definition NCASE f g n :=
  Lc.App2 n f (Lc.Abs (Lc.Abs (Lc.App (Lc.lift 2 g) (Lc.Ref 1)))).

Lemma NCASE_sim_0 f g :
  Lc.redp (NCASE f g ZE) f.
unfold NCASE, ZE.
eapply t_trans;[apply t_step|].
 apply Lc.app_red_l.
 apply beta.
unfold Lc.subst; simpl.
apply t_step.
apply Lc.red1_beta.
unfold Lc.subst; rewrite Lc.simpl_subst; auto.
rewrite Lc.lift0; trivial.
Qed.

Lemma NCASE_sim_S f g n :
  Lc.redp (NCASE f g (Lc.App SU n)) (Lc.App g n).
unfold NCASE, SU.
eapply t_trans;[apply t_step|].
 do 2 apply Lc.app_red_l.
 apply beta.
unfold Lc.subst; simpl.
eapply t_trans;[apply t_step|].
 apply Lc.app_red_l.
 apply beta.
unfold Lc.subst; simpl.
rewrite Lc.simpl_subst; trivial.
eapply t_trans;[apply t_step|].
 apply beta.
unfold Lc.subst; simpl.
do 2 (rewrite Lc.simpl_subst; trivial).
repeat rewrite Lc.lift0.
eapply t_trans;[apply t_step|].
 apply Lc.app_red_l.
 apply beta.
unfold Lc.subst; simpl.
rewrite Lc.simpl_subst; trivial.
apply t_step.
apply Lc.red1_beta.
unfold Lc.subst; simpl.
do 2 (rewrite Lc.simpl_subst; auto).
repeat rewrite Lc.lift0; trivial.
Qed.

(*
Lemma sn_subst_var u n :
  Lc.sn u -> Lc.sn (Lc.subst (Lc.Ref n) u).
induction 1; intros.
constructor; intros.
unfold transp in *.
clear H.

revert H0; inversion_clear H1; intros.
 admit.

 apply H0; trivial.

 inversion H.
*)
Lemma sn_app_var u n :
  Lc.sn u -> Lc.sn (Lc.App u (Lc.Ref n)).
induction 1; intros.
constructor; intros.
unfold transp in *.
assert (Lc.sn x).
 constructor; trivial.
clear H.
revert H2 H0; inversion_clear H1; intros.
 admit.

 apply H0; trivial.

 inversion H.
Qed.

Lemma NCASE_fNAT f g n k (A B:family) :
  k ∈ NAT ->
  inSAT n (fNAT A k) ->
  inSAT f (B ZERO) ->
  inSAT g (piNAT(fun m => prodSAT (A m) (B (SUCC m)))) ->
  inSAT (NCASE f g n) (B k).
unfold NCASE; intros.
rewrite fNAT_def in H0.
apply H0 with (P:=B); intros; trivial.
rewrite piNAT_ax in H2|-*; intros.
destruct H2 as (sng,H2).
split; intros.
 do 2 apply Lc.sn_abs.
 apply sn_app_var.
 apply Lc.sn_lift; trivial.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
repeat rewrite Lc.simpl_subst; trivial.
do 2 rewrite Lc.lift0.
apply prodSAT_elim with (2:=H4); auto.
Qed.

(** Structural fixpoint: *)

(** NATFIX m n --> m (NATFIX m) n when n is a constructor.
   let G m := "\n. (match n with | 0 => m | S _ => m end) m n"
   let G m := \n. n m (\_.\_.m) m n
    G m -/-> ; G m 0 --> m 0 ; G m (S k) --> m (S k)
   NATFIX m n := G (\x. m (G x)) n
     --> (\x. m (G x)) (\x. m (G x)) n
     --> m (G (\x. m (G x))) n == m (NATFIX m) n
 *)

(** Guard the self-application of m (which would produce a non-strongly
    normalizing term) by a natural number.
 *)
Definition G m :=
 Lc.Abs (Lc.App2 (Lc.App2 (Lc.Ref 0) (Lc.lift 1 m) (Lc.Abs (Lc.Abs (Lc.lift 3 m)))) (Lc.lift 1 m) (Lc.Ref 0)).
Definition NATFIX m :=
  G (Lc.Abs (Lc.App  (Lc.lift 1 m) (G (Lc.Ref 0)))).

(** (G m n) reduces to (m m n) when n is a constructor. Note that
    n need not be closed. *)
Lemma G_sim : forall m n,
  n = ZE \/ (exists t1 t2, n = Lc.Abs (Lc.Abs (Lc.App2 (Lc.Ref 0) t1 t2))) ->
  Lc.redp (Lc.App (G m) n) (Lc.App2 m m n).
intros.
unfold G.
eapply t_trans.
 apply t_step.
 apply Lc.beta.
unfold Lc.subst; simpl.
rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
unfold Lc.lift; rewrite Lc.simpl_subst_rec; auto.
apply Lc.redp_app_l.
apply Lc.redp_app_l.
destruct H as [eqn|(t1,(t2,eqn))]; rewrite eqn.
 eapply t_trans.
  apply t_step.
  apply Lc.app_red_l.
  apply beta.
 unfold Lc.subst; simpl.
 apply t_step.
 apply red1_beta.
 unfold Lc.subst; rewrite Lc.simpl_subst; auto with *.
 rewrite Lc.lift0; trivial.

 eapply t_trans.
  apply t_step.
  apply Lc.app_red_l.
  apply beta.
 unfold Lc.subst; simpl.
 eapply t_trans.
  apply t_step; apply beta. 
 unfold Lc.subst; simpl.
 rewrite Lc.lift0.
 eapply t_trans.
  apply t_step.
  apply Lc.app_red_l.
  apply beta.
 unfold Lc.subst; simpl.
 rewrite Lc.simpl_subst_rec; auto.
 apply t_step.
 apply Lc.red1_beta.
 unfold Lc.subst.
 rewrite Lc.simpl_subst_rec; auto.
 rewrite Lc.lift_rec0; trivial.
Qed.

Lemma G_sat A k m t X :
  k ∈ NAT ->
  inSAT t (fNAT A k) ->
  inSAT (Lc.App2 m m t) X ->
  inSAT (Lc.App (G m) t) X.
intros.
unfold G.
apply inSAT_exp; intros.
 right; apply sat_sn in H0; trivial.
unfold Lc.subst; simpl Lc.subst_rec.
repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
assert (tsat := H0).
rewrite fNAT_def in tsat.
eapply inSAT_context.
 intros.
 eapply inSAT_context.
  intros.
  assert (rS0 : eqSAT S0 S0) by reflexivity.
  pose (G:=mkFam (fun _ => S0) (fun _ _ _ _ => rS0)).
  apply tsat with (P:=G).
  unfold G; simpl.
  eexact H3.
  rewrite piNAT_ax; intros.
   split; intros.
   do 2 apply Lc.sn_abs.
   apply Lc.sn_lift.
   apply sat_sn in H3; trivial.
  apply prodSAT_intro; intros.
  unfold Lc.subst; simpl Lc.subst_rec.
  apply prodSAT_intro; intros.
  unfold Lc.subst; repeat rewrite Lc.simpl_subst; auto.
  rewrite Lc.lift0; trivial.
 eexact H2.
trivial.
Qed.

Lemma NATFIX_sim : forall m n,
  n = ZE \/ (exists t1 t2, n = Lc.Abs (Lc.Abs (Lc.App2 (Lc.Ref 0) t1 t2))) ->
  Lc.redp (Lc.App (NATFIX m) n) (Lc.App2 m (NATFIX m) n).
intros.
unfold NATFIX at 1.
eapply t_trans.
 apply G_sim; trivial.
apply Lc.redp_app_l.
apply t_step.
apply Lc.red1_beta.
set (t1 := Lc.Abs (Lc.App (Lc.lift 1 m) (G (Lc.Ref 0)))).
unfold Lc.subst; simpl.
rewrite Lc.simpl_subst; auto.
rewrite Lc.lift0.
reflexivity.
Qed.

Definition piNATi F o :=
  interSAT (fun p:{n|n ∈ NATi o} => F (proj1_sig p)).

Lemma piNATi_ax t F o :
  inSAT t (piNATi F o) <-> sn t /\ forall n, n ∈ NATi o -> inSAT t (F n).
split; intros.
 split; intros.
  apply sat_sn in H; trivial.
 apply interSAT_elim with (x:=exist (fun n=>n ∈ NATi o) n H0) in H; trivial.

 destruct H.
 split; intros; trivial.
 destruct x; simpl; auto.
 apply H0; trivial.
Qed.

Require Import ZFord.

  Lemma sn_lift_inv : forall M', sn M' -> forall n M k, M' = lift_rec n M k -> sn M.
induction 1; intros.
constructor; intros.
apply H0 with (lift_rec n y k) n k; trivial.
subst x; red.
apply red1_lift; trivial.
Qed.

Lemma sn_G_inv m : Lc.sn (G m) -> Lc.sn m.
intros.
unfold G in H.
eapply subterm_sn in H;[|constructor].
eapply subterm_sn in H;[|apply sbtrm_app_l].
eapply subterm_sn in H;[|apply sbtrm_app_r].
apply sn_lift_inv with (1:=H) (2:=eq_refl).
Qed.


(* The guard is needed mainly here:
   NATFIX m does not reduce *)
Lemma sn_natfix o m X :
  isOrd o ->
  inSAT m (interSAT (fun o':{o'|o' ∈ osucc o} => let o':=proj1_sig o' in
        prodSAT (piNATi(fun n => prodSAT (cNAT n) (X o' n)) o')
                (piNATi(fun n => prodSAT (cNAT n) (X (osucc o') n)) (osucc o')))) ->
  sn (NATFIX m).
intros.
assert (empty ∈ osucc o).
 apply isOrd_plump with o; auto with *.
  red; intros.
  apply empty_ax in H1; contradiction.
  apply lt_osucc; trivial.
apply interSAT_elim with (x:=exist (fun o'=>o'∈ osucc o) empty H1) in H0.
simpl proj1_sig in H0.
unfold NATFIX.
assert (sn (Lc.Abs (Lc.App (Lc.lift 1 m) (G (Lc.Ref 0))))).
 apply sn_abs.
 assert (inSAT (G (Lc.Ref 0)) (piNATi(fun n => prodSAT (cNAT n) (X empty n)) empty)).
  rewrite piNATi_ax.
  split; intros.
   apply sn_abs.
   constructor; intros.
   apply nf_norm in H2; try contradiction.
   repeat constructor.

   intros ? ?.
   eapply G_sat with (A:=cNAT) (k:=n).
    revert H2; apply NATi_NAT; auto with *.

    apply cNAT_pre; trivial.

    apply prodSAT_elim with (A:=snSAT).
    2:apply sat_sn in H3; trivial.
    apply prodSAT_elim with (A:=snSAT).
    apply varSAT.
    apply varSAT.

 specialize prodSAT_elim with (1:=H0)(2:=H2); intro.
 apply sat_sn in H3; trivial.
 apply sn_subst with (Ref 0).
 unfold Lc.subst; simpl.
 rewrite simpl_subst; auto.
 rewrite lift0; auto.

apply sn_abs.
apply prodSAT_elim with (A:=snSAT) (B:=snSAT).
2:simpl; auto with *.
apply prodSAT_elim with (A:=snSAT).
apply prodSAT_elim with (A:=snSAT).
apply prodSAT_elim with (A:=snSAT).
apply varSAT.

simpl; apply sn_lift; trivial.

apply sn_abs; apply sn_abs.
apply sn_lift; trivial.

simpl; apply sn_lift; trivial.
Qed.



Lemma NATFIX_sat : forall o m X,
  isOrd o ->
  (forall o o' n, isOrd o -> isOrd o' -> o ⊆ o' -> n ∈ NAT ->
   inclSAT (X o n) (X o' n)) ->
  inSAT m (interSAT (fun o':{o'|o' ∈ osucc o} => let o':=proj1_sig o' in
        prodSAT (piNATi(fun n => prodSAT (cNAT n) (X o' n)) o')
                (piNATi(fun n => prodSAT (cNAT n) (X (osucc o') n)) (osucc o')))) ->
  inSAT (NATFIX m) (piNATi(fun n => prodSAT (cNAT n) (X o n)) o).
intros o m X H Xmono H0.
elim H using isOrd_ind; intros.
rewrite piNATi_ax.
split.
 apply sn_natfix with (2:=H0); trivial.

intros x i.
assert (tyx : x ∈ NAT).
 apply NATi_NAT with y; trivial.
apply TI_elim in i; auto with *.
destruct i as (z,?,?).
unfold NATFIX.
intros t tty.
apply cNAT_pre in tty.
apply G_sat with (2:=tty); trivial.
eapply inSAT_context; intros.
 apply inSAT_exp.
  left; simpl.
  apply Bool.orb_true_r.

  unfold Lc.subst; simpl Lc.subst_rec.
  repeat rewrite Lc.simpl_subst; auto.
  rewrite Lc.lift0.
  change (inSAT (Lc.App m (NATFIX m)) S).
  eexact H6.

apply Xmono with (osucc z); eauto using isOrd_inv.
 red; intros.
 apply isOrd_plump with z; trivial.
  eauto using isOrd_inv.
  apply olts_le; trivial.
apply prodSAT_elim with (cNAT x).
2:apply cNAT_post; trivial.
assert (z ∈ osucc o).
 apply isOrd_trans with o; auto.
 apply H2; trivial.
apply interSAT_elim with (x:=exist (fun o'=>o' ∈ osucc o) z H6) in H0.
simpl proj1_sig in H0.
specialize H3 with (1:=H4).
specialize prodSAT_elim with (1:=H0) (2:=H3); intro.
rewrite piNATi_ax in H7.
destruct H7 as (_,H7); apply H7.
assert (isOrd z).
 apply isOrd_inv with y; trivial.
apply TI_intro with z; auto with *.
Qed.
