
(* Nat *)
Set Implicit Arguments.

Require Import ZF ZFord ZFcoc ZFind_nat.
Import IZF.
(*Import ZFnats.*)

Require Import basic CanF SatF.
Require Import GenRealSNF.
Module Lc:=LambdaF.
Import MM.

(* Nat *)

Record num := mkNat { number :> set; is_num : number \in NAT }.

Definition eqnum (x y:num) := x == y.

Instance eqnum_eq : Equivalence eqnum.
unfold eqnum; split.
 red; reflexivity.

 red; symmetry; trivial.

 red; intros.
 transitivity y; trivial.
Qed.

Definition ZEROt := mkNat ZERO_typ.
Definition SUCCt n := mkNat (SUCC_typ _ (is_num n)).

Record family := mkFam {
  fam :> num -> SAT;
  fam_mrph : Proper (eqnum ==> eqSAT) fam
}.

Existing Instance fam_mrph.

Definition dflt_family : family.
exists (fun _ => snSAT).
do 2 red; reflexivity.
Defined.

Definition eqfam (A B:family) :=
  forall x y, eqnum x y -> eqSAT (A x) (B y).

Instance eqfam_eq : Equivalence eqfam.
unfold eqfam; split.
 red; intros.
 rewrite H; reflexivity.

 red; intros.
 symmetry in H0|-*; auto.

 red; intros.
 transitivity (y x0); auto with *.
Qed. 

Definition fNAT (A:family) (k:num) :=
  interSAT
    (fun P:family =>
      prodSAT (P ZEROt)
     (prodSAT (interSAT (fun n => prodSAT (A n) (prodSAT (P n) (P (SUCCt n)))))
              (P k))).

Instance fNAT_morph : Proper (eqfam ==> eqnum ==> eqSAT) fNAT.
do 3 red.
intros A B H x y H0.
unfold fNAT.
apply interSAT_morph.
split; intros.
 exists x0.
 apply prodSAT_morph.
  reflexivity.

  apply prodSAT_morph.
   apply interSAT_morph.
   split; intros.
    exists x1.
    apply prodSAT_morph.
     apply H; red; reflexivity.

     reflexivity.

    exists y0.
    apply prodSAT_morph.
     apply H; red; reflexivity.

     reflexivity.

   apply (fam_mrph x0); trivial.

 exists y0.
 apply prodSAT_morph.
  reflexivity.

  apply prodSAT_morph.
   apply interSAT_morph.
   split; intros.
    exists x0.
    apply prodSAT_morph.
     apply H; red; reflexivity.

     reflexivity.

    exists y1.
    apply prodSAT_morph.
     apply H; red; reflexivity.

     reflexivity.

   apply (fam_mrph y0); trivial.
Qed.
(*
Lemma fNAT_morph : forall A B, eqfam A B ->
  forall x y, eqnum x y -> eqSAT (fNAT A x) (fNAT B y).
*)

Definition fNATf (A:family) : family.
exists (fNAT A).
intros.
apply fNAT_morph; trivial.
exact (fam_mrph A).
Defined.


Lemma fNAT_def : forall t A k,
  inSAT t (fNAT A k) <->
  forall (P:family) f g,
  inSAT f (P ZEROt) ->
  (forall n m y, inSAT m (A n) -> inSAT y (P n) -> inSAT (Lc.App2 g m y) (P (SUCCt n))) ->
  inSAT (Lc.App2 t f g) (P k).
unfold fNAT.
split; intros.
 apply interSAT_elim with (x:=P) in H.
 apply prodSAT_elim with (interSAT (fun n => prodSAT (A n) (prodSAT (P n) (P (SUCCt n))))).
  apply prodSAT_elim with (2:=H0); trivial.

  apply interSAT_intro; trivial; intros.
  simpl.
  do 2 red; intros.
  apply H1; trivial.

 apply interSAT_intro; intros.
  exact dflt_family.
 simpl.
 do 2 red; intros.
 apply H with (P:=x); intros; trivial.
 destruct H1.
 do 2 red in H4.
 apply H4; auto.
Qed.


Lemma fNAT_mono : forall (A B:family),
  (forall k, inclSAT (A k) (B k)) -> forall k, inclSAT (fNAT A k) (fNAT B k).
unfold inclSAT; intros.
rewrite fNAT_def in H0 |- *; intros.
apply H0; intros; auto.
Qed.


Definition ZE := Lc.Abs (Lc.Abs (Lc.Ref 1)).

Lemma fNAT_ZE : forall A, inSAT ZE (fNAT A ZEROt).
unfold fNAT, ZE; intros A.
apply interSAT_intro; trivial.
intro P.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
apply prodSAT_intro; intros.
unfold Lc.subst; rewrite Lc.simpl_subst; trivial; rewrite Lc.lift0; trivial.
Qed.

Definition SU := Lc.Abs (Lc.Abs (Lc.Abs
    (Lc.App2 (Lc.Ref 0) (Lc.Ref 2) (Lc.App2 (Lc.Ref 2) (Lc.Ref 1) (Lc.Ref 0))))).

Lemma fNAT_SU : forall (A:family) n t,
  inSAT t (A n) ->
  inSAT t (fNAT A n) ->
  inSAT (Lc.App SU t) (fNAT A (SUCCt n)).
intros.
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
specialize interSAT_elim with (x:=n) (1:=H3); intro.
specialize interSAT_elim with (x:=true) (1:=H1); intro.
specialize interSAT_elim with (x:=false) (1:=H1); intro.
specialize interSAT_elim with (x:=P) (1:=H6); intro.
clear H1.
apply prodSAT_elim with (A:=P n).
 apply prodSAT_elim with (A:=A n); trivial.

 apply prodSAT_elim with (2:=H2) in H7.
 apply prodSAT_elim with (1:=H7); trivial.
Qed.

(* Constructor iteration *)

Definition posti P :=
  Proper (eq_set ==> eqfam) P /\
  forall o o', o \in toOrd o' ->
  forall k, inclSAT (fNAT (P (toOrd o)) k) (P (toOrd o') k).

Lemma posti_dflt : {P|posti P}.
exists (fun _ => dflt_family).
split.
 do 2 red; reflexivity.

 red; red; intros.
 apply sat_sn in H0; trivial.
Qed.
Hint Resolve posti_dflt.

Lemma fNAT_posti : forall (P:set->family),
  posti P -> posti (fun o => fNATf (P o)).
unfold posti; simpl; intros.
destruct H; split; intros.
 do 2 red; intros.
 red; simpl; intros.
 apply fNAT_morph; auto with *.

 apply fNAT_mono; simpl; apply H0; trivial.
Qed.


Definition cNATi (o:set) : family.
exists (fun n => 
  interSAT (fun P:{P:set->family|posti P}=> proj1_sig P (toOrd o) n)).
do 2 red; intros.
apply interSAT_morph.
split; intros.
 exists x0.
 apply (fam_mrph (proj1_sig x0 (toOrd o))); trivial.

 exists y0.
 apply (fam_mrph (proj1_sig y0 (toOrd o))); trivial.
Defined.

Instance cNATi_morph : Proper (eq_set ==> eqfam) cNATi.
unfold cNATi; do 3 red; simpl; intros.
apply interSAT_morph; red; intros.
split; intros.
 exists x1; simpl.
 transitivity (proj1_sig x1 (toOrd x) y0).
  apply (fam_mrph (proj1_sig x1 (toOrd x))); trivial.
  apply (proj2_sig x1); auto with *.
  rewrite H; reflexivity.

 exists y1; simpl.
 transitivity (proj1_sig y1 (toOrd x) y0).
  apply (fam_mrph (proj1_sig y1 (toOrd x))); trivial.
  apply (proj2_sig y1); auto with *.
  rewrite H; reflexivity.
Qed.


Lemma cNATi_incr : forall o o', isOrd o' -> o \in o' -> forall k,
  inclSAT (cNATi o k) (cNATi o' k).
red; intros.
unfold cNATi.
apply interSAT_intro; trivial.
destruct x as (P,Pincl); simpl in Pincl|-*.
apply (proj2 Pincl o).
 rewrite toOrd_ord; auto.

 apply interSAT_elim with (1:=H1) (x:=exist _ _ (fNAT_posti Pincl)).
Qed.

Lemma cNATi_posti : posti cNATi.
split; intros; auto with *.
red; red; intros.
unfold cNATi; apply interSAT_intro; auto.
destruct x as (P,Pincl); simpl proj1_sig in Pincl|-*.
apply Pincl with o.
 rewrite toOrd_ord; auto.
 apply toOrd_isOrd.

 revert t H0; apply fNAT_mono.
 red; intros.
 specialize interSAT_elim with (1:=H0)(x:=exist (fun P=>posti P) P Pincl); intro.
 simpl in H1.
 revert H1.
 apply (proj1 Pincl); auto with *.
 rewrite (toOrd_ord (toOrd o)); auto with *.
 apply toOrd_isOrd.
Qed.

Lemma cNATi_def : forall t o k,
  inSAT t (cNATi o k) <->
  exists2 o', o' \in o & inSAT t (fNAT (cNATi o') k).
Admitted.
(*
Lemma cNATi_elim : forall t o k,
  inSAT t (cNATi o k) ->
  exists2 o', o' \in o & inSAT t (fNAT (cNATi o') k).
intros.
pose (Q o k :=
  interSAT (fun S:{S:SAT| forall o', o' \in o -> inclSAT (cNATi o' k) S} =>
            proj1_sig S)).
assert (forall o x y, eqnum x y -> eqSAT (Q o x) (Q o y)).
 admit.
pose (Q' o := @mkFam (Q o) (H0 o)).
assert (posti Q').
 admit.
specialize interSAT_elim with (1:=H) (x:=exist _ Q' H1); simpl proj1_sig; intro.
generalize (fun P h => interSAT_elim H2 (exist _ P h)); simpl proj1_sig; intros.


simpl in H.
*)

Lemma cNATi_succ : forall o, isOrd o ->
  forall k , eqSAT (cNATi (osucc o) k) (fNAT (cNATi o) k).
split; intros.
 rewrite cNATi_def in H0.
 destruct H0.
 revert H1; apply fNAT_mono.
 red; intros.
 rewrite cNATi_def in H1 |- *.
 destruct H1.
 exists x0; trivial.
 apply olts_le in H0.
 apply H0 in H1; trivial.

 rewrite cNATi_def.
 exists o; trivial.
 apply lt_osucc; trivial.
Qed.


Lemma cNATi_ZE : forall o, isOrd o -> inSAT ZE (cNATi (osucc o) ZEROt).
intros.
rewrite cNATi_succ; trivial.
apply fNAT_ZE.
Qed.

Lemma cNATi_SU : forall o n t,
  isOrd o ->inSAT t (cNATi o n) -> inSAT (Lc.App SU t) (cNATi (osucc o) (SUCCt n)). 
intros.
rewrite cNATi_succ; trivial.
apply fNAT_SU; trivial.
rewrite <- cNATi_succ; trivial.
revert H0; apply cNATi_incr; auto.
apply lt_osucc; trivial.
Qed.


Definition realNati o (n:X) (t:Lc.term) :=
  exists H:n \in NAT, inSAT t (cNATi o (mkNat H)).

Instance realNati_morph : Proper (eq_set ==> eq_set ==> eq ==> iff) realNati.
apply morph_impl_iff3; auto with *.
do 5 red; intros.
subst y1.
destruct H2.
assert (y0 \in NAT).
 rewrite <- H0; trivial.
exists H2.
assert (eqfam (cNATi x) (cNATi y)).
 apply cNATi_morph; trivial.
red in H3.
revert x1 H1.
apply H3.
red; simpl; trivial.
Qed.

Lemma realNati_cand : forall o n,
  n \in NAT -> is_cand (fun t => realNati o n t).
intros.
cut (is_cand (fun t => inSAT t (cNATi o (mkNat H)))).
 apply is_cand_morph; red; intros.
 assert (forall (p : n \in NAT), eqSAT (cNATi o (mkNat p)) (cNATi o (mkNat H))).
  intros.
  apply fam_mrph; red; reflexivity.
 split; intros.
  destruct H1.
  rewrite H0 in H1; trivial.

  exists H; trivial.

 exact (proj2_sig (cNATi o (mkNat H))).
Qed.

Lemma realNati_def : forall o n t,
  (n,t) \real mkTy NAT (realNati o) <-> realNati o n t.
intros.
rewrite mkTy_def0; intros.
 split; intros.
  destruct H; trivial.

  split; trivial.
  destruct H; trivial.

 do 3 red; intros.
 subst y0.
 assert (forall (Hx:x \in NAT) (Hy:y \in NAT),
         eqSAT (cNATi o (mkNat Hx)) (cNATi o (mkNat Hy))).
  intros.
  apply fam_mrph.
  red; trivial.
 split; destruct 1.
  generalize x1; rewrite H; intro.
  exists H2.
  rewrite <- (H0 x1 H2); trivial.

  generalize x1; rewrite <- H; intro.
  exists H2.
  rewrite (H0 H2 x1); trivial.

 apply realNati_cand; trivial.
Qed.


Module NatFixpoint.

(* Fixpoint *)

Definition post P := forall k, inclSAT (fNAT P k) (P k).

Lemma post_dflt : {P|post P}.
exists dflt_family.
red; red; intros.
apply sat_sn in H; trivial.
Qed.
Hint Resolve post_dflt.

Lemma fNAT_post :
 forall P, post P -> post (fNATf P).
unfold post; simpl; intros.
apply fNAT_mono; apply H.
Qed.


Definition cNAT : family.
exists (fun n =>
  interSAT (fun P:{P|post P} => proj1_sig P n)).
do 2 red; intros.
apply interSAT_morph.
split; intros.
 exists x0.
 apply (fam_mrph (proj1_sig x0)); trivial.

 exists y0.
 apply (fam_mrph (proj1_sig y0)); trivial.
Defined.

Lemma cNAT_post : post cNAT.
red; red; intros.
unfold cNAT.
apply interSAT_intro; intros; trivial.
apply (proj2_sig x).
revert t H.
apply fNAT_mono.
red; intros.
apply interSAT_elim with (1:=H) (x:=x).
Qed.

Lemma cNAT_pre : forall k, inclSAT (cNAT k) (fNAT cNAT k).
red; intros.
apply interSAT_elim with (1:=H) (x:=exist _ _ (fNAT_post cNAT_post)).
Qed.

Lemma cNAT_eq : forall k, eqSAT (cNAT k) (fNAT cNAT k).
split.
 apply cNAT_pre.
 apply cNAT_post.
Qed.

(*
Definition incr (P:set->SAT) :=
  forall o o', o \in toOrd o' -> inclSAT (P o) (P o').

Definition unionSAT (P:set->SAT) (h:incr P) (o:set) : SAT.
intros P h o.
exists (fun t => exists2 o', o' \in toOrd o & inSAT t (P o')).
split; intros.
 destruct H.
 apply sat_sn in H0; trivial.

 destruct H.
 exists x; trivial.
 apply (clos_red _ (proj2_sig (P x))) with t; trivial.

 red in h.
*)

Lemma cNATi_incl_cNAT :
  forall o k, isOrd o -> inclSAT (cNATi o k) (cNAT k).
intros o k H; revert k; induction H using isOrd_ind.
red; intros.
rewrite cNATi_def in H2.
destruct H2.
rewrite cNAT_eq.
revert H3; apply fNAT_mono.
auto.
Qed.


Definition realNat (n:X) (t:Lc.term) :=
  exists H:n \in NAT, inSAT t (cNAT (mkNat H)).

Instance realNat_morph : Proper (eq_set ==> eq ==> iff) realNat.
apply morph_impl_iff2; auto with *.
do 4 red; intros.
subst y0.
destruct H1.
assert (y \in NAT).
 rewrite <- H; trivial.
exists H1.
revert x0 H0.
apply (fam_mrph cNAT).
red; simpl; auto with *.
Qed.

Lemma realNat_cand : forall n,
  n \in NAT -> is_cand (fun t => realNat n t).
intros.
cut (is_cand (fun t => inSAT t (cNAT (mkNat H)))).
 apply is_cand_morph; red; intros.
 assert (forall (p : n \in NAT), eqSAT (cNAT (mkNat p)) (cNAT (mkNat H))).
  intros.
  apply fam_mrph; red; reflexivity.
 split; intros.
  destruct H1.
  rewrite H0 in H1; trivial.

  exists H; trivial.

 exact (proj2_sig (cNAT (mkNat H))).
Qed.

Lemma realNat_def : forall n t,
  (n,t) \real mkTy NAT realNat <-> realNat n t.
intros.
rewrite mkTy_def0; intros.
 split; intros.
  destruct H; trivial.

  split; trivial.
  destruct H; trivial.

 do 3 red; intros.
 subst y0.
 assert (forall (Hx:x \in NAT) (Hy:y \in NAT),
         eqSAT (cNAT (mkNat Hx)) (cNAT (mkNat Hy))).
  intros.
  apply fam_mrph.
  red; trivial.
 split; destruct 1.
  generalize x1; rewrite H; intro.
  exists H2.
  rewrite <- (H0 x1 H2); trivial.

  generalize x1; rewrite <- H; intro.
  exists H2.
  rewrite (H0 H2 x1); trivial.

 apply realNat_cand; trivial.
Qed.

End NatFixpoint.

(* copy from GenRealSN *)
Definition cst (x:X) (t:Lc.term)
  (H0 : liftable (fun _ => t)) (H1 : substitutive (fun _ => t)) : trm.
left; exists (fun _ => x) (fun _ => t); trivial.
 do 2 red; reflexivity.
 do 2 red; reflexivity.
Defined.

(* Ordinals *)

Parameter Ord : trm.

Parameter typ_ord_inv : forall e o i j,
  typ e o Ord ->
  val_ok e i j ->
  isOrd (int i o).
Hint Resolve typ_ord_inv.

Parameter OInfty : trm.

Parameter OSucc : trm -> trm.

Parameter osucc_inv : forall i o k,
  inclSAT (fNAT (cNATi (int i o)) k) (cNATi (int i (OSucc o)) k).

Parameter osucc_inv2 : forall e i j o,
  typ e o Ord ->
  val_ok e i j ->
  int i (OSucc o) \incl osucc (int i o).

(*Parameter OSucc_infty : eq_trm (OSucc OInfty) OInfty.*)

(*
Definition Ord (o:set) := @cst o Lc.K (fun _ _ => eq_refl _) (fun _ _ _ => eq_refl _).
(*
Definition typ_ord_kind : forall e o, typ e (Ord o) kind.
red; simpl; intros.
split; simpl.
 discriminate.

 split; auto 
trivial.
Qed.

Definition typ_ord_ord : forall e o o',
  lt o o' -> typ e (Ord o) (Ord o').
red; simpl; intros; trivial.
Qed.
*)

Definition OSucc : trm -> trm.
intros o; left; exists (fun i => osucc (int i o)) (fun j => tm j o).
 do 2 red; intros.
 rewrite H; reflexivity.

 do 2 red; intros.
 rewrite H; trivial.

 red; intros.
 apply tm_liftable.

 red; intros.
 apply tm_substitutive.
Defined.
*)

Definition Zero : trm.
left; exists (fun _ => ZERO) (fun _ => ZE).
 do 2 red; reflexivity.

 do 2 red; reflexivity.

 red; reflexivity.

 red; reflexivity.
Defined.


Definition Succ (o:trm): trm.
left; exists (fun i => lam (mkTy NAT (realNati (int i o))) SUCC) (fun _ => SU).
 do 2 red; intros.
 apply lam_ext.
  apply mkTy_morph; auto with *.
  intros.
  rewrite H; reflexivity.

  red; intros.
  rewrite H1; reflexivity.

 do 2 red; auto.

 red; reflexivity.

 red; reflexivity.
Defined.


Definition Nati (o:trm) : trm.
left; exists (fun i => mkTy NAT (realNati (int i o)))
  (fun j => tm j o).
 do 3 red; intros.
 apply mkTy_morph; auto with *.
 intros.
 rewrite H; reflexivity.

 do 2 red; intros.
 rewrite H; reflexivity.

 red; intros.
 apply tm_liftable.

 red; intros.
 apply tm_substitutive.
Defined.


Lemma typ_N : forall e o, typ e o Ord -> typ e (Nati o) kind.
red; red; simpl; intros.
split.
 discriminate.

 split.
  red.
  exists List.nil.
  exists (Nati o).
   reflexivity.

   exists (ZERO, daimon).
   simpl; intros.
   rewrite realNati_def.
   exists ZERO_typ.
   apply varSAT.

  apply H in H0.
  apply in_int_sn in H0; trivial.
Qed.

Lemma typ_0 : forall e o, typ e o Ord -> typ e Zero (Nati (OSucc o)).
red; red; simpl; intros.
split.
 discriminate.

 rewrite realNati_def.
 exists ZERO_typ.
 fold ZEROt.
 assert (forall k, inclSAT (fNAT (cNATi (int i o)) k) (cNATi (int i (OSucc o)) k)).
  intro; apply osucc_inv.
 apply H1.
 apply fNAT_ZE.
(* destruct Ord_inv with (1:=H) (2:=H0) as (H1,[H2|H2]).
  rewrite H2.
  apply (@cNATi_incl_cNAT (osucc empty)); auto with *.
  apply cNATi_ZE; auto.

  rewrite (cNATi_morph H2 (reflexivity _)).
  apply cNATi_ZE; trivial.*)
Qed.

Lemma typ_S : forall e o, typ e o Ord ->
   typ e (Succ o) (Prod (Nati o) (lift 1 (Nati (OSucc o)))).
red; red; simpl; intros.
split.
 discriminate.

 apply prod_intro.
  red; intros.
  rewrite H2; reflexivity.

  red; intros; reflexivity.

  red; red; intros.
  split; intros.
   unfold SU.
   clear H0.
   constructor; intros.
   inversion_clear H0.
   inversion_clear H1.
   inversion_clear H0.
   inversion_clear H1.
    inversion_clear H0.
     inversion H1.
     inversion H1.
    inversion_clear H0.
     inversion_clear H1.
      inversion H0.
      inversion H0.
     inversion H1.

   red; intros.
   rewrite realNati_def in H1|-*.
   destruct H1.
   exists (SUCC_typ _ x0).
   assert (int (V.lams 0 (V.shift 1) (V.cons x i)) (OSucc o) == int i (OSucc o)).
    rewrite V.lams0.
    apply int_morph; auto with *.
    red; red; intros.
    unfold V.shift, V.cons; simpl; reflexivity.
   rewrite (cNATi_morph H2 (reflexivity _)); clear H2.
   assert (oo : isOrd (int i o)) by eauto.
   assert (forall k, inclSAT (fNAT (cNATi (int i o)) k) (cNATi (int i (OSucc o)) k)).
    intro; apply osucc_inv.
   apply H2.
   change (mkNat (SUCC_typ x x0)) with (SUCCt (mkNat x0)).
   apply fNAT_SU; trivial.
   rewrite <- cNATi_succ; trivial.
   revert H1; apply cNATi_incr; auto.
   apply lt_osucc; trivial.
(*
   destruct Ord_inv with (1:=H)(2:=H0) as (H2,[H3|H3]).
    rewrite H3.
    apply cNATi_SU in H1; trivial.
    revert H1.
    apply cNATi_incl_cNAT; auto.

    rewrite (cNATi_morph H3 (reflexivity _)).
    apply cNATi_SU in H1; auto.*)
Qed.


Definition NatCase (f g n:trm) : trm.
left; exists (fun i => NATCASE (int i f) (fun n => app (int i g) n) (int i n))
             (fun j => Lc.App2 (tm j n) (tm j f)
                (Lc.App (Lc.Abs (Lc.Abs (Lc.Abs (Lc.App (Lc.Ref 2) (Lc.Ref 1)))))
                        (tm j g))).
 do 2 red; intros.
 apply NATCASE_morph.
  rewrite H; reflexivity.

  red; intros.
  rewrite H; rewrite H0; reflexivity.

  rewrite H; reflexivity.

 do 2 red; intros.
 rewrite H; auto.

 red; intros; simpl.
 repeat rewrite tm_liftable; trivial.

 red; intros; simpl.
 repeat rewrite tm_substitutive; trivial.
Defined.


Lemma typ_Ncase : forall e o n f g P,
  typ e o Ord ->
  typ e n (Nati (OSucc o)) ->
  typ e f (App P Zero) ->
  typ e g (Prod (Nati o) (App (lift 1 P) (App (Succ (lift 1 o)) (Ref 0)))) ->
  typ e (NatCase f g n) (App P n).
red; intros.
red in H0; specialize H0 with (1:=H3).
red in H1; specialize H1 with (1:=H3).
red in H2; specialize H2 with (1:=H3).
unfold in_int in H0,H1,H2|-*; simpl in *.
split;[discriminate|].
destruct H0 as (_,H0).
destruct H1 as (_,H1).
destruct H2 as (_,H2).
set (c := int i n) in *; clearbody c.
set (tc := tm j n) in *; clearbody tc; clear n.
set (f0 := int i f) in *; clearbody f0.
set (b0 := tm j f) in *; clearbody b0; clear f.
set (fS := int i g) in *; clearbody fS.
set (bS := tm j g) in *; clearbody bS; clear g.
set (fS' := fun n :set => app fS n) in |-*.
assert (fsm : morph1 fS').
 do 2 red; intros.
 unfold fS'; rewrite H4; reflexivity.
rewrite realNati_def in H0.
destruct H0.
rewrite cNATi_def in H0.
destruct H0 as (o',H0).
rewrite fNAT_def in H4.
assert (forall x tx,
 (x,tx) \real mkTy NAT (realNati (int i o))  ->
 (app fS x, Lc.App bS tx) \real app (int i P) (SUCC x)).
 intros.
 refine (let H' := prod_elim _ H2 H5 in _).
  red; intros.
  apply ZFcoc.cc_app_morph.
   rewrite H7; reflexivity.

   apply ZFcoc.cc_app_morph; auto with *.
   apply ZFcoc.cc_lam_ext.
    apply El_morph.
    apply mkTy_morph; auto with *; intros.
    rewrite H7; reflexivity.

    red; intros.
    rewrite H9; reflexivity.
 clear H2.
 apply inSAT_val with (3:=H'); try reflexivity.
 apply ZFcoc.cc_app_morph.
  unfold lift; rewrite int_lift_rec_eq.
  apply int_morph; try reflexivity.
  red; red; intros.
  destruct a as [|[|a]]; simpl; reflexivity.

  apply beta_eq with tx; trivial.
   red; intros.
   rewrite H6; reflexivity.

   rewrite realNati_def in H5|-*.
   destruct H5.
   exists x1.
   rewrite cNATi_def in H2|-*.
   destruct H2.
   exists x2; trivial.
   unfold lift; rewrite int_lift_rec_eq.
   apply eq_elim with (2:=H2).
   apply int_morph; auto with *.
   red; red ;simpl.
   unfold V.lams, V.shift; simpl.
   destruct a; simpl; reflexivity.
assert (forall x:num, is_cand (fun t => (NATCASE f0 fS' x, t) \real app (int i P) x)).
 destruct x0 as (x0,xnat); simpl; intros.
 intros.
 elim xnat using NAT_ind; intros.
  revert H8; apply is_cand_morph.
  red; intros.
  apply in_ext.
   split; simpl; trivial.
   apply NATCASE_morph; auto with *.

   rewrite H7; reflexivity.

  apply inSAT_CR with b0.
  apply inSAT_val with (3:=H1); try reflexivity.
  rewrite NATCASE_ZERO; reflexivity.

  apply inSAT_CR with (Lc.App bS daimon).
  apply inSAT_val with (fS' n) (app (int i P) (SUCC n)); try reflexivity.
   rewrite NATCASE_SUCC; auto with *.

   apply H5; trivial.
    rewrite realNati_def.
    exists H6; apply varSAT.
pose (F:=fun x => exist _ _ (H6 x) :SAT).
assert (Fm : forall x y, eqnum x y -> eqSAT (F x) (F y)).
 intros.
 unfold F.
 red; simpl; intros.
 apply in_ext.
  split; simpl; trivial.
  apply NATCASE_morph; auto with *.

  red in H7; rewrite H7; reflexivity.
apply H4 with (P:=mkFam Fm) (f:=b0)
     (g:=Lc.App (Lc.Abs (Lc.Abs (Lc.Abs (Lc.App (Lc.Ref 2) (Lc.Ref 1))))) bS).
 simpl.
 apply inSAT_val with (3:=H1); try reflexivity.
 rewrite NATCASE_ZERO; reflexivity.

 intros.
 simpl.
 apply inSAT_val with (fS' n) (app (int i P) (SUCC n)); try reflexivity.
  rewrite NATCASE_SUCC; auto with *.

  apply inSAT_exp_sat2.
   apply inSAT_sn with (1:=H2).

   unfold Lc.subst; simpl.
   apply inSAT_exp_sat1.
    apply (sat_sn _ _ H7).

    unfold Lc.subst; simpl.
    rewrite Lc.simpl_subst; auto.
    apply inSAT_exp_sat.
     apply (sat_sn _ _ H8).

     unfold Lc.subst; simpl.
     repeat rewrite Lc.simpl_subst; auto.
     repeat rewrite Lc.lift0.
     apply H5.
     rewrite realNati_def.
     red.
     exists (is_num n).
     assert (o' \incl int i o).
      apply olts_le.
      revert H0; apply osucc_inv2 with (1:=H)(2:=H3).
     rewrite (cNATi_def m o' n) in H7.
     rewrite (cNATi_def m (int i o) (mkNat (is_num n))).
     destruct H7.
     exists x0; auto.
     destruct n; trivial.
Qed.

Definition NatFix (O M:trm) : trm.
left.
exists (fun i =>
  NATREC (fun o' f => int (V.cons f (V.cons o' i)) M) (int i O))
  (fun j => Lc.Fix (tm (ilift (I.cons (tm j O) j)) M)).
 admit.
 admit.
 admit.
 admit.
Defined.

Infix "::" := List.cons.

Lemma El_Nati : forall o, isOrd o -> El (mkTy NAT (realNati o)) == NATi o.
Admitted.

Lemma inSAT_exp_fx : forall x A m u,
  Lc.sn u ->
  (x,Lc.App (Lc.subst (Lc.Fix m) m) u) \real A ->
  (x,Lc.App (Lc.Fix m) u) \real A.
intros.
assert (Lc.sn m).
 apply inSAT_sn in H0.
 apply Lc.sn_subst with (Lc.Fix m).
 apply Lc.subterm_sn with (1:=H0); auto.
revert m H1 H0.
induction H.
rename x0 into u.
unfold transp in *.
assert (snu : Lc.sn u).
 apply Acc_intro; trivial.
clear H.
induction 1.
rename x0 into m.
unfold transp in *.
assert (snm : Lc.sn m).
 apply Acc_intro; trivial.
clear H.
intros.
apply inSAT_exp with (1:=H2); intros.
 exact I.
inversion H; clear H; subst; auto.
 inversion_clear H6.
 apply H1; auto.
 apply inSAT_red with (1:=H2).
 apply Lc.red_red_app; auto with coc.
 transitivity (Lc.subst (Lc.Fix m) m').
  unfold Lc.subst; auto with coc.

  apply Lc.red1_subst_l; auto with coc.

 apply H0; auto.
 apply inSAT_red with (1:=H2).
 auto with coc.
Qed.


Lemma typ_Fix : forall e O M U,
  typ e O Ord ->
  typ (Prod (Nati (Ref 0)) (App (App (lift 2 U) (Ref 1)) (Ref 0)) :: OSucc O :: e)
    M
    (Prod (Nati (OSucc (Ref 1))) (App (App (lift 3 U) (OSucc (Ref 2))) (Ref 0))) ->
  typ e (NatFix O M) (Prod (Nati O) (App (lift 1 (App U O)) (Ref 0))).
red; red; simpl; intros e O M U tyO tyM i j v_ok.
assert (oo : isOrd (int i O)).
 apply typ_ord_inv with (1:=tyO) (2:=v_ok).
split.
 discriminate.
set (g := fun o' f :set => int (V.cons f (V.cons o' i)) M) in |-*.
set (gt := tm (ilift (I.cons (tm j O) j)) M) in |-*.
assert (gm : morph2 g).
 do 3 red; intros.
 unfold g.
 rewrite H; rewrite H0.
 reflexivity.
assert (Umono_real :
 forall o o', ZFnats.lt o' (osucc (int i O)) -> isOrd o -> o \incl o' ->
 forall x x' z u,
 x \in NATi o -> x == x' ->
 (z,u) \real app (app (int i U) o) x ->
 (z,u) \real app (app (int i U) o') x').
 admit.
assert (Umono :
 forall o o', ZFnats.lt o' (osucc (int i O)) -> isOrd o -> o \incl o' ->
 forall x1 x',
 x1 \in NATi o -> x1 == x' ->
 El (app (app (int i U) o) x1) \incl El (app (app (int i U) o') x')).
 red; intros.
 rewrite El_def in H4|-*.
 destruct H4.
 eauto.
assert (tyg :
 forall o f, isOrd o -> ZFnats.lt (osucc o) (osucc (int i O)) ->
 f \in cc_prod (NATi o) (fun x1 => El (app (app (int i U) o) x1)) ->
 g o f \in
 cc_prod (NATi (osucc o))
   (fun x1 => El (app (app (int i U) (osucc o)) x1))).
 intros.
 do 2 red in tyM.
 destruct tyM with (i:=V.cons f (V.cons o i))
   (j:=I.cons (Lc.Abs (Lc.Ref 1)) (I.cons daimon j)). 
  apply vcons_add_var.
   apply vcons_add_var; trivial.
    admit. (* (o, daimon) \in int O+ *)
    admit. (* discr *)
   simpl.
   rewrite prod_def; split. 
    apply eq_elim with (2:=H1).
    apply cc_prod_ext.
     symmetry; apply El_Nati; eauto using isOrd_inv.

     red; intros.
     rewrite split_lift; rewrite int_cons_lift_eq.
     rewrite int_cons_lift_eq.
     rewrite H3; reflexivity.

    red; red; simpl; intros.
    split.
     apply Lc.sn_abs.
     apply Lc.sn_var.
    red; intros.
    apply inSAT_val with (app f x) (app (app (int i U) o) x); auto with *.
     rewrite split_lift; rewrite int_cons_lift_eq.
     rewrite int_cons_lift_eq.
     reflexivity.

     assert (app f x \in El (app (app (int i U) o) x)).
      apply cc_prod_elim with (1:=H1).
      admit. (* x \in Nati o *)
     rewrite El_def in H3; destruct H3.
     apply inSAT_exp_sat.
      rewrite realNati_def in H2; destruct H2.
      apply (sat_sn _ _ H2).

      unfold Lc.subst; simpl.
      apply inSAT_CR in H3.
      apply var_in_cand with (1:=H3).

   discriminate.

  simpl in H3.
  rewrite prod_def in H3.
  destruct H3 as (H3,_).
  apply eq_elim with (2:=H3).
  apply cc_prod_ext.
   rewrite El_Nati; auto.
    admit. (* osucc *)
    admit. (* osucc *)

   red; intros.
   rewrite split_lift; rewrite int_cons_lift_eq.
   rewrite split_lift; rewrite int_cons_lift_eq.
   rewrite int_cons_lift_eq.
   admit. (* osucc *)
assert (gstab :
 stab_fix_prop (osucc (int i O)) g
   (fun o x1 => El (app (app (int i U) o) x1))).
 admit.
assert (sngt : Lc.sn (Lc.Fix gt)).
 admit.
apply inSAT_val with (NATREC g (int i O))
  (prod (mkTy NAT (realNati (int i O))) (fun x => app (app (int i U) (int i O)) x));
auto with *.
 apply prod_ext; auto with *.
 red; intros.
 rewrite V.lams0.
 unfold V.shift; simpl.
 apply cc_app_morph; trivial.
 apply cc_app_morph; apply int_morph; auto with *.
  red; red; reflexivity.
  red; red; reflexivity.
rewrite prod_def.
split.
 apply eq_elim with (cc_prod (NATi (int i O)) (fun x => El (app (app (int i U) (int i O)) x))).
  apply cc_prod_ext.
   symmetry; apply El_Nati; auto.
   red; intros; rewrite H0; auto with *.
 apply NATREC_wt with (eps:=osucc (int i O)) (U:=fun o x => El (app (app (int i U) o) x));
 auto.

 split; trivial.
 apply isOrd_ind with (2:=oo).
 red; intros.
 red in H1.

rewrite realNati_def in H2; destruct H2 as (h,?).
rewrite cNATi_def in H2; destruct H2.
rewrite <- cNATi_succ with (o:=x0) (k:=mkNat h) in H3;
  eauto using isOrd_inv.

 apply inSAT_val with (app (g x0 (NATREC g x0)) x) (app (app (int i U) y) x);
 auto with *.
  transitivity (app (g y (NATREC g y)) x).
   apply gstab; eauto using isOrd_inv, ole_lts.
    red; intros; apply isOrd_trans with x0; trivial.

    apply NATREC_wt with (eps:=osucc (int i O))
      (U:=fun o x => El (app (app (int i U) o) x)); auto.
    apply isOrd_trans with y; auto.
    apply ole_lts; trivial.

    apply NATREC_wt with (eps:=osucc (int i O))
      (U:=fun o x => El (app (app (int i U) o) x)); auto.
    apply ole_lts; trivial.

    apply fincr_ext with (o:=osucc (int i O))(eps:=osucc (int i O))
      (U:=fun o x => El (app (app (int i U) o) x)); auto with *.
     apply NATREC_inv; auto with *.

     apply isOrd_inv with y; trivial.

     apply ole_lts; trivial.

     red; intros; apply isOrd_trans with x0; trivial.

    admit. (* x \in NATi x0+ *)

   symmetry; apply NATREC_expand
    with (eps:=osucc (int i O)) (U:=fun o x => El (app (app (int i U) o) x)); auto.
   apply ole_lts; trivial.
   admit. (* x \in NATi y *)

  apply inSAT_exp_fx.
   exact (sat_sn _ _ H3).
  replace (Lc.subst (Lc.Fix gt) gt) with
    (tm (I.cons (Lc.Fix gt) (I.cons (tm j O) j)) M).
  apply Umono_real with x0 x; auto with *.
   apply ole_lts; auto.

   apply isOrd_inv with y; trivial.

   red; intros; apply isOrd_trans with x0; trivial.

   admit. (* x \in NATi x0 *)

  do 2 red in tyM.
  destruct tyM with (i:=V.cons (NATREC g x0) (V.cons x0 i))
    (j:=I.cons (Lc.Fix gt) (I.cons (tm j O) j)). 
   apply vcons_add_var.
    apply vcons_add_var; trivial.
     admit. (* (x0, tm j O) \in int O+ *)
     admit. (* discr *)
    simpl.
    rewrite prod_def; split. 
     apply eq_elim with
       (cc_prod (NATi x0) (fun x1 => El (app (app (int i U) x0) x1))).
      apply cc_prod_ext.
       symmetry; apply El_Nati; eauto using isOrd_inv.

       red; intros.
       rewrite split_lift; rewrite int_cons_lift_eq.
       rewrite int_cons_lift_eq.
       rewrite H5; reflexivity.

      apply NATREC_wt with (eps:=osucc (int i O))
         (U:=fun o x => El (app (app (int i U) o) x)); auto with *.
      apply isOrd_trans with y; auto.
      apply ole_lts; trivial.

     red; red; simpl; intros.
     split; trivial.
     red; intros.
     apply inSAT_val with (app (NATREC g x0) x1) (app (app (int i U) x0) x1); auto with *.
     rewrite split_lift; rewrite int_cons_lift_eq.
     rewrite int_cons_lift_eq.
     reflexivity.

    discriminate.

   simpl in H5.
  apply prod_elim with (dom := mkTy NAT (realNati 
    (int (V.cons (NATREC g x0) (V.cons x0 i)) (OSucc (Ref 1)))))
    (F:=fun x => app (app (int i U) (osucc x0)) x); trivial.
   red; intros.
   rewrite H7; reflexivity.

   apply inSAT_val with (3:=H5); auto with *.
    unfold g; reflexivity.

    apply prod_ext; auto with *.
    red; intros.
    rewrite split_lift; rewrite int_cons_lift_eq.
    rewrite split_lift; rewrite int_cons_lift_eq.
    rewrite int_cons_lift_eq.
    rewrite H7.
    admit. (* osucc ok *)

 rewrite realNati_def.
 exists h.
 admit.  (* osucc ok *)

 unfold gt at 3.
 apply tm_subst_cons.
Qed.







 assert (x \in NATi y).
  rewrite <- El_Nati; auto.
  rewrite El_def.
  eauto.
 destruct TI_elim with (3:=H3); auto.
 rewrite <- ZFfix.TI_mono_succ in H5; eauto using isOrd_inv.
 apply inSAT_val with (app (g x0 (NATREC g x0)) x) (app (app (int i U) y) x);
 auto with *.
  transitivity (app (g y (NATREC g y)) x).
   apply gstab; eauto using isOrd_inv, ole_lts.
    red; intros; apply isOrd_trans with x0; trivial.

    apply NATREC_wt with (eps:=osucc (int i O)) (U:=fun o x => El (app (app (int i U) o) x));
 auto.
    apply isOrd_trans with y; auto.
    apply ole_lts; trivial.

    apply NATREC_wt with (eps:=osucc (int i O)) (U:=fun o x => El (app (app (int i U) o) x));
 auto.
    apply ole_lts; trivial.

    apply fincr_ext with (o:=osucc (int i O))(eps:=osucc (int i O)) (U:=fun o x => El (app (app (int i U) o) x));
 auto with *.
     apply NATREC_inv; auto with *.

     apply isOrd_inv with y; trivial.

     apply ole_lts; trivial.

     red; intros; apply isOrd_trans with x0; trivial.

    unfold NATi; rewrite <- ZFfix.TI_mono_succ; auto.
    apply isOrd_inv with y; trivial.

   symmetry; apply NATREC_expand
    with (eps:=osucc (int i O)) (U:=fun o x => El (app (app (int i U) o) x)); auto.
   apply ole_lts; trivial.

  apply inSAT_exp_fx.
   rewrite realNati_def in H2.
   destruct H2.
   exact (sat_sn _ _ H2).
  replace (Lc.subst (Lc.Fix gt) gt) with
    (tm (I.cons (Lc.Fix gt) (I.cons (tm j O) j)) M).
  cut ((app (g x0 (NATREC g x0)) x,
   Lc.App (tm (I.cons (Lc.Fix gt) (I.cons (tm j O) j)) M) u) \real
   app (app (int i U) (osucc x0)) x).
   admit. (* U mono (real) *)
  do 2 red in tyM.
  destruct tyM with (i:=V.cons (NATREC g x0) (V.cons x0 i))
    (j:=I.cons (Lc.Fix gt) (I.cons (tm j O) j)). 
   apply vcons_add_var.
    apply vcons_add_var; trivial.
     admit. (* (x0, tm j O) \in int O+ *)
     admit. (* discr *)
    simpl.
    rewrite prod_def; split. 
     apply eq_elim with
       (cc_prod (NATi x0) (fun x1 => El (app (app (int i U) x0) x1))).
      apply cc_prod_ext.
       symmetry; apply El_Nati; eauto using isOrd_inv.

       red; intros.
       rewrite split_lift; rewrite int_cons_lift_eq.
       rewrite int_cons_lift_eq.
       rewrite H7; reflexivity.

      apply NATREC_wt with (eps:=osucc (int i O))
         (U:=fun o x => El (app (app (int i U) o) x)); auto with *.
      apply isOrd_trans with y; auto.
      apply ole_lts; trivial.

     red; red; simpl; intros.
     split.
      admit. (* sn gt *)

      red; intros.
      apply inSAT_val with (app (NATREC g x0) x1) (app (app (int i U) x0) x1); auto with *.
      rewrite split_lift; rewrite int_cons_lift_eq.
      rewrite int_cons_lift_eq.
      reflexivity.
    discriminate.

   simpl in H7.
  apply prod_elim with (dom := mkTy NAT (realNati 
    (int (V.cons (NATREC g x0) (V.cons x0 i)) (OSucc (Ref 1)))))
    (F:=fun x => app (app (int i U) (osucc x0)) x); trivial.
   red; intros.
   rewrite H9; reflexivity.

   apply inSAT_val with (3:=H7); auto with *.
    unfold g; reflexivity.

    apply prod_ext; auto with *.
    red; intros.
    rewrite split_lift; rewrite int_cons_lift_eq.
    rewrite split_lift; rewrite int_cons_lift_eq.
    rewrite int_cons_lift_eq.
    rewrite H9.
    admit. (* osucc ok *)

 apply inSAT_val with (3:=H2); auto with *.
 rewrite realNati_def in H2.
 destruct H2.


 apply inSAT_val with (app (g y (NATREC g y)) x) (app (app (int i U) y) x);
 auto with *.
  symmetry; apply NATREC_expand
    with (eps:=osucc (int i O)) (U:=fun o x => El (app (app (int i U) o) x)); auto.
   admit. (*morph*)
   admit. (* U mono *)
   admit. (* ty M *)
   admit. (* M mono *)
(*   revert H3; unfold NATi; apply ZFfix.TI_mono; auto with *.*) admit.
 apply inSAT_exp_fx.
  exact (sat_sn _ _ H2).
 replace (Lc.subst (Lc.Fix gt) gt) with
   (tm (I.cons (Lc.Fix gt) (I.cons (tm j O) j)) M).
  apply prod_elim with (dom :=mkTy NAT (realNati y)).
   admit.
   2:rewrite realNati_def.
   2:exists x0; trivial.
  red in tyM.
  assert (in_int (V.cons (NATREC g (int i O)) (V.cons (int i O) i))
           (I.cons (Lc.Fix gt) (I.cons (tm j O) j)) M
   (Prod (Nati (OSucc (Ref 0)))
             (App (App (lift 3 U) (OSucc (Ref 2))) (Ref 0)))).
   apply tyM.
   admit.
  destruct H4 as (_,H4); simpl in H4.



(* Old style *)

Parameter FX : Lc.term.

Parameter FX_red : forall m u,
  Lc.red1 (Lc.App2 FX m (Lc.Abs u)) (Lc.App2 m (Lc.App FX m) (Lc.Abs u)).

Definition NatFix (O M:trm) : trm.
left.
exists (fun i =>
  NATREC (fun o' f => int (V.cons f (V.cons o' i)) M) (int i O))
  (fun j => Lc.App FX (Lc.Abs (tm (ilift (I.cons (tm j O) j)) M))).
 admit.
 admit.
 admit.
 admit.
Defined.

Import List.
Lemma typ_Fix : forall e O M U,
  typ e O Ord ->
  typ (Prod (Nati (Ref 0)) (App (App (lift 2 U) (Ref 1)) (Ref 0)) :: OSucc O :: e)
    M
    (Prod (Nati (OSucc (Ref 0))) (App (App (lift 3 U) (OSucc (Ref 2))) (Ref 0))) ->
  typ e (NatFix O M) (Prod (Nati O) (App (lift 1 (App U O)) (Ref 0))).
red; red; simpl; intros e O M U tyO tyM i j v_ok.
destruct Ord_inv with (1:=tyO) (2:=v_ok) as (Oo,Os).
split.
 discriminate.
rewrite prod_def.
split.
 admit.

 red; intros.
 red; simpl.
 split.
  admit.
 red; intros.
 set (g := fun o' f :set => int (V.cons f (V.cons o' i)) M) in |-*.
 apply inSAT_val with
   (MM.app (g (int i O) (NATREC g (int i O))) x)
   (MM.app (MM.app (int i U) (int i O)) x).
  symmetry.
  apply NATREC_expand with (osucc (int i O))
   (fun o x => El (MM.app (MM.app (int i U) o) x)).
   admit.
   admit.
   admit. (* U mono *)

   intros.
   unfold g.
   assert (val_ok (Prod (Nati (Ref 0)) (App (App (lift 2 U) (Ref 1)) (Ref 0))
         :: OSucc O :: e) (V.cons f (V.cons o i)) (I.cons daimon (I.cons daimon j))).
    apply vcons_add_var; auto.
     apply vcons_add_var; auto.
     2:admit.
     admit.

     simpl.
     rewrite prod_def.
     split.
      apply eq_elim with (2:=H2).
      apply cc_prod_ext.
       apply eq_intro; intros.
        rewrite El_def.
        exists daimon.
        rewrite realNati_def.
        assert (z \in NAT).
         apply NATi_NAT with o; trivial.
        exists H4.
        apply varSAT.

        rewrite El_def in H3.
        destruct H3.
        rewrite realNati_def in H3.
        destruct H3.
        admit.

       red; intros.
       apply El_morph.
       rewrite split_lift.
       rewrite int_cons_lift_eq.
       rewrite int_cons_lift_eq.
       rewrite H4; reflexivity.

      unfold daimon.
      apply var_in_cand with (X:=Pi (mkTy NAT (realNati o))
     (fun x0 : X =>
      MM.app (MM.app (int (V.cons x0 (V.cons o i)) (lift 2 U)) o) x0)
     (fun x0 : X => MM.app f x0)).
      apply is_cand_pi'.
      intros.
      rewrite split_lift.
      rewrite int_cons_lift_eq.
      rewrite int_cons_lift_eq.
      apply cc_prod_elim with (1:=H2).
      admit.

      discriminate.

   red in tyM; specialize tyM with (1:=H3).
   red in tyM; simpl in tyM.
   destruct tyM as (_,tyM).
   rewrite prod_def in tyM.
   destruct tyM as (tyM,_).
   apply eq_elim with (2:=tyM).
   symmetry.
   apply cc_prod_ext.
    admit. (* ... *)

    red; intros.
    do 2 (rewrite split_lift; rewrite int_cons_lift_eq).
    rewrite int_cons_lift_eq.
    admit.

  admit.

  admit.

  admit.

  apply cc_app_morph; auto with *.
  rewrite V.lams0.
  unfold V.shift; simpl.
  apply cc_app_morph; auto with *.
   apply int_morph; auto with *.
   red; red; simpl; reflexivity.

   apply int_morph; auto with *.
   red; red; simpl; reflexivity.

Lemma inSAT_exp_fx : forall x A m u,
  Lc.sn u ->
  (x,Lc.App2 m (Lc.App FX m) (Lc.Abs u)) \real A ->
  (x,Lc.App2 FX m (Lc.Abs u)) \real A. 
Admitted.

assert (val_ok (Prod (Nati (Ref 0)) (App (App (lift 2 U) (Ref 1)) (Ref 0))
           :: OSucc O :: e)
  (V.cons (NATREC g (int i O)) (V.cons (int i O) i))
  (I.cons (Lc.App FX (Lc.Abs (tm (ilift (I.cons (tm j O) j)) M)))
    (I.cons (tm j O) j))).
 admit.
red in tyM; specialize tyM with (1:=H0).
red in tyM; simpl in tyM.
destruct tyM as (_,tyM).
fold (g (int i O) (NATREC g (int i O))) in tyM.
apply prod_elim with (F:=fun x => MM.app (MM.app (int i U) (int i O)) x)
 (dom := mkTy NAT (realNati (int i O))); trivial.
 red; intros.
 rewrite H2; reflexivity.

 


 apply inSAT_exp with daimon.
  admit.

  exact I.

  intros.



  assert
inversion H0.
admit.
  red; simpl.



Lemma prod_intro' : forall dom f F t,
  eq_fun dom F F ->
  f \in ZFcoc.cc_prod (El dom) F ->
  Pi dom F (ZFcoc.cc_app f) t ->
  (f, t) \real prod dom F.
Admitted.

apply prod_intro'.
 red; intros.
 rewrite H2.
 reflexivity.

 admit.
(* eapply NATREC_wt.*)

 red; intros.
red; simpl.
split.
 admit.
red; intros.
red in H; simpl in H.

 apply 

replace (NATREC (fun o' f => int (V.cons f (V.cons o' i)) M) (toOrd (int i O)))
 with (lam (NATi (toOrd (int i O))) (fun x =>
         app (F o NATREC
red; simpl.