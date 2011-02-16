
(* Nat *)
Set Implicit Arguments.

Require Import ZF ZFcoc ZFind_nat.
Import IZF.
(*Import ZFnats.*)

Require Import basic Can Sat GenRealSN.
Module Lc:=Lambda.
Import MM.


Record num := mkNat { number :> set; is_num : number \in NAT }.

Definition eqnum (x y:num) := x == y.

Definition ZEROt := mkNat ZERO_typ.
Definition SUCCt n := mkNat (SUCC_typ _ (is_num n)).

Record family := mkFam {
  fam :> num -> SAT;
  fam_mrph : forall x y, eqnum x y -> eqSAT (fam x) (fam y)
}.

Definition dflt_family : family.
exists (fun _ => snSAT).
reflexivity.
Defined.

Definition eqfam (A B:family) :=
  forall x y, eqnum x y -> eqSAT (A x) (B y).

Definition fNAT (A:family) (k:num) :=
  interSAT
    (fun P:family =>
      prodSAT (P ZEROt)
     (prodSAT (interSAT (fun n => prodSAT (A n) (prodSAT (P n) (P (SUCCt n)))))
              (P k))).

Lemma fNAT_morph : forall A B, eqfam A B ->
  forall x y, eqnum x y -> eqSAT (fNAT A x) (fNAT B y).
intros.
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
  exists (fun _ => snSAT); reflexivity.
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


Lemma cNAT_ZE : inSAT ZE (cNAT ZEROt).
rewrite cNAT_eq.
apply fNAT_ZE.
Qed.

Lemma cNAT_SU : forall n t, inSAT t (cNAT n) -> inSAT (Lc.App SU t) (cNAT (SUCCt n)). 
intros.
rewrite cNAT_eq.
apply fNAT_SU; trivial.
rewrite <- cNAT_eq; trivial.
Qed.

Definition realNat (n:X) (t:Lc.term) :=
  exists H:n \in NAT, inSAT t (cNAT (mkNat H)).

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



Definition Zero : trm.
left; exists (fun _ => ZERO) (fun _ => ZE).
 do 2 red; reflexivity.

 do 2 red; reflexivity.

 red; reflexivity.

 red; reflexivity.
Defined.


Definition Succ : trm.
left; exists (fun _ => lam (mkTy NAT realNat) SUCC) (fun _ => SU).
 do 2 red; reflexivity.

 do 2 red; reflexivity.

 red; reflexivity.

 red; reflexivity.
Defined.

Definition Nat : trm.
left; exists (fun _ => mkTy NAT realNat) (fun _ => Lc.K).
 do 2 red; reflexivity.

 do 2 red; reflexivity.

 red; reflexivity.

 red; reflexivity.
Defined.



Lemma typ_0 : forall e, typ e Zero Nat.
red; red; simpl; intros.
split.
 discriminate.

 rewrite realNat_def.
 exists ZERO_typ.
 apply cNAT_ZE.
Qed.

Lemma typ_S : forall e, typ e Succ (Prod Nat (lift 1 Nat)).
red; red; simpl; intros.
split.
 discriminate.

 apply prod_intro.
  red; intros.
  rewrite H1; reflexivity.

  red; intros; reflexivity.

  red; red; intros.
  split; intros.
   unfold SU.
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
   rewrite realNat_def in H0|-*.
   destruct H0.
   apply cNAT_SU in H0.
   exists (SUCC_typ _ x0).
   trivial.
Qed.

Lemma typ_N : forall e, typ e Nat kind.
red; red; simpl; intros.
split.
 discriminate.

 split.
  red.
  exists List.nil.
  exists Nat.
   reflexivity.

   exists (ZERO, ZE).
   simpl; intros _.
   apply (typ_0 H).

  exact Lc.sn_K.
Qed.

Require Import ZFord.
Require Import ZFrepl.

Definition NREC f g n y :=
  forall P,
  Proper (eq_set ==> eq_set ==> iff) P -> 
  P ZERO f -> (forall m x, P m x -> P (SUCC m) (g m x)) -> P n y.

Lemma NREC_inv : forall f g n y,
  morph2 g ->
  NREC f g n y ->
  NREC f g n y /\
  (n == ZERO -> y == f) /\
  (forall m, n == SUCC m -> exists2 z, NREC f g m z & y == g m z).
intros f g n y gm h; pattern n, y; apply h.
 do 3 red; intros.
 apply and_iff_morphism.
  split; red; intros.
   rewrite <- H; rewrite <- H0; apply H1; trivial. 
   rewrite H; rewrite H0; apply H1; trivial. 
  apply and_iff_morphism.
   rewrite H; rewrite H0; reflexivity.

   apply fa_morph; intro m.
   rewrite H.
   apply fa_morph; intros _.
   apply ex2_morph.
    red; reflexivity.

    red; intros.
    rewrite H0; reflexivity.

 split; [|split]; intros.
  red; auto.

  reflexivity.

  apply NATf_discr in H; contradiction.

 intros ? ? (?,(?,?)).
 split; [|split]; intros.
  red; intros.
  apply H4; apply H; auto.

  symmetry in H2; apply NATf_discr in H2; contradiction.

  apply SUCC_inj in H2.
  exists x.
   red; intros.
   rewrite <- H2; apply H; auto.

   rewrite H2; reflexivity.
Qed.


Lemma NREC_choice_0 : forall f g, uchoice_pred (NREC f g ZERO).
split; [|split]; intros.
 unfold NREC in *; intros.
 rewrite <- H.
 apply H0; auto.

 exists f.
 red; auto.

 cut (ZERO==ZERO); auto with *.
 pattern ZERO at 2, x; apply H; intros.
  do 3 red; intros.
  rewrite H1; rewrite H2; reflexivity.

  revert H1; pattern ZERO at 2, x'; apply H0; intros.
   do 3 red; intros.
   rewrite H1; rewrite H2; reflexivity.

   reflexivity.

   apply NATf_discr in H2; contradiction.

  apply NATf_discr in H2; contradiction.
Qed.


Lemma NREC_choice : forall f g n,
  n \in NAT ->
  morph2 g ->
  uchoice_pred (NREC f g n).
intros f g n H gm.
split; intros.
 unfold NREC; intros.
 rewrite <- H0.
 apply H1; auto.

 split; intros.
  elim H using NAT_ind; intros.
   destruct H2.
   exists x0; red; intros.
   rewrite <- H1.
   apply H2; auto.

   exists f; red; auto.

   destruct H1.
   exists (g n0 x); red; intros.
   apply H4.
   apply H1; auto.

  revert x x' H0 H1.
  elim H using NAT_ind; intros.
   apply H2.
    red; intros; rewrite H1; apply H3; trivial.
    red; intros; rewrite H1; apply H4; trivial.

   apply NREC_inv in H0; trivial; apply NREC_inv in H1; trivial;
   destruct H0 as (_,(?,_)); destruct H1 as (_,(?,_)).
   rewrite H0; auto with *.
   rewrite H1; auto with *.

   apply NREC_inv in H2; trivial; apply NREC_inv in H3; trivial;
   destruct H2 as (_,(_,?)); destruct H3 as (_,(_,?)).
   destruct (H2 n0); auto with *.
   destruct (H3 n0); auto with *.
   rewrite H5; rewrite H7.
   apply gm; auto with *.
Qed.


Definition NATREC f g n := uchoice (NREC f g n).

Instance NATREC_morph :
  Proper (eq_set ==> (eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) NATREC.
do 4 red; intros.
unfold NATREC, NREC.
apply uchoice_morph_raw.
red; intros.
apply fa_morph; intro P.
apply fa_morph; intro Pm.
rewrite H.
apply fa_morph; intros _.
split; intros.
 rewrite <- H1; rewrite <- H2; apply H3; intros.
 setoid_replace (x0 m x3) with (y0 m x3); auto.
 apply H0; reflexivity.

 rewrite H1; rewrite H2; apply H3; intros.
 setoid_replace (y0 m x3) with (x0 m x3); auto.
 symmetry; apply H0; reflexivity.
Qed.

Lemma NATREC_def : forall f g n,
  morph2 g -> n \in NAT -> NREC f g n (NATREC f g n).
intros.
unfold NATREC; apply uchoice_def.
apply NREC_choice; trivial.
Qed.


Lemma NATREC_0 : forall f g, NATREC f g ZERO == f.
unfold NATREC; intros.
symmetry; apply uchoice_ext; trivial.
 apply NREC_choice_0.

 red; auto.
Qed.

Lemma NATREC_S : forall f g n, morph2 g -> n \in NAT ->
   NATREC f g (SUCC n) == g n (NATREC f g n).
intros.
elim H0 using NAT_ind; intros.
 rewrite <- H2; trivial.

 symmetry; apply uchoice_ext.
  apply NREC_choice; trivial.
  apply SUCC_typ; apply ZERO_typ.
 red; intros.
 apply H3.
 rewrite NATREC_0; auto.

 unfold NATREC at 1; symmetry; apply uchoice_ext; auto.
  apply NREC_choice; trivial.
  do 2 apply SUCC_typ; trivial.

  red; intros.
  apply H5.
  rewrite H2.
  apply H5.
  revert P H3 H4 H5; change (NREC f g n0 (NATREC f g n0)).
  unfold NATREC; apply uchoice_def.
  apply NREC_choice; trivial.
Qed.


Definition NatRec (f g n:trm) : trm.
left; exists (fun i => NATREC (int i f) (fun n y => app (app (int i g) n) y) (int i n))
             (fun j => Lc.App2 (tm j n) (tm j f) (tm j g)).
 do 2 red; intros.
 apply NATREC_morph.
  rewrite H; reflexivity.

  do 2 red; intros.
  rewrite H; rewrite H0; rewrite H1; reflexivity.

  rewrite H; reflexivity.

 do 2 red; intros.
 rewrite H; auto.

 red; intros; simpl.
 repeat rewrite tm_liftable; trivial.

 red; intros; simpl.
 repeat rewrite tm_substitutive; trivial.
Defined.


Lemma typ_Nrect : forall e n f g P,
  typ e n Nat ->
  typ e f (App P Zero) ->
  typ e g (Prod Nat (Prod (App (lift 1 P) (Ref 0))
              (App (lift 2 P) (App Succ (Ref 1))))) ->
  typ e (NatRec f g n) (App P n).
red; intros.
red in H; specialize H with (1:=H2).
red in H0; specialize H0 with (1:=H2).
red in H1; specialize H1 with (1:=H2).
unfold in_int in *; simpl.
destruct H as (_,H).
destruct H0 as (_,H0).
destruct H1 as (_,H1).
unfold Nat in H; simpl in H.
unfold App in H0; simpl in H0.
unfold Prod in H1; simpl in H1.
split.
 discriminate.
set (c := int i n) in *; clearbody c.
set (tc := tm j n) in *; clearbody tc; clear n.
set (f0 := int i f) in *; clearbody f0.
set (b0 := tm j f) in *; clearbody b0; clear f.
set (fS := int i g) in *; clearbody fS.
set (bS := tm j g) in *; clearbody bS; clear g.
set (fS' := fun n y :set => app (app fS n) y) in |-*.
assert (fsm : morph2 fS').
 do 3 red; intros.
 unfold fS'; rewrite H3; rewrite H4; reflexivity.
rewrite realNat_def in H.
destruct H as (H,H3).
assert (forall x tx y ty,
 (x,tx) \real mkTy NAT realNat ->
 (y,ty) \real app (int i P) x ->
 (app (app fS x) y, Lc.App2 bS tx ty) \real app (int i P) (SUCC x)).
 intros.
 refine (let H6 := prod_elim _ H1 H4 in _).
  red; intros.
  apply prod_ext.
   rewrite H7; reflexivity.

   red; intros.
   rewrite H9; rewrite H7; reflexivity.

  clear H1.
  assert ((y,ty) \real app (int (V.cons x i) (lift 1 P)) x).
   apply inSAT_val with (3:=H5); try reflexivity.
   rewrite int_cons_lift_eq; reflexivity.
  refine (let H7 := prod_elim _ H6 H1 in _).
   red; intros.
   rewrite H8; reflexivity.

   apply inSAT_val with (3:=H7); try reflexivity.
    apply ZFcoc.cc_app_morph.
     unfold lift; rewrite int_lift_rec_eq.
     apply int_morph; try reflexivity.
     red; red; intros.
     destruct a as [|[|a]]; simpl; reflexivity.

     apply beta_eq with tx; trivial.
     red; intros.
     rewrite H9; reflexivity.
clear H1; rename H4 into H1.
revert H0 H1; generalize (int i P).
clear H2 i j e P.
intros P H0 H1.
assert (forall x:num, is_cand (fun t => (NATREC f0 fS' x, t) \real app P x)).
 destruct x as (x,xnat); simpl; intros.
 intros.
 elim xnat using NAT_ind; intros.
  revert H5; apply is_cand_morph.
  red; intros.
  apply in_ext.
   split; simpl; trivial.
   apply NATREC_morph; auto with *.

   rewrite H4; reflexivity.

  apply inSAT_CR with b0.
  apply inSAT_val with (3:=H0); try reflexivity.
  rewrite NATREC_0; reflexivity.

  apply inSAT_CR with (Lc.App2 bS daimon daimon).
  apply inSAT_val with (fS' n (NATREC f0 fS' n)) (app P (SUCC n)); try reflexivity.
   rewrite NATREC_S; trivial; reflexivity.

   apply H1; trivial.
    rewrite realNat_def.
    exists H2; apply varSAT.

    apply var_in_cand with (1:=H4).

rewrite cNAT_eq in H3.
rewrite fNAT_def in H3.
pose (F:=fun x => exist _ _ (H2 x) :SAT).
assert (Fm : forall x y, eqnum x y -> eqSAT (F x) (F y)).
 intros.
 unfold F.
 red; simpl; intros.
 apply in_ext.
  split; simpl; trivial.
  apply NATREC_morph; auto with *.

  red in H4; rewrite H4; reflexivity.
apply H3 with (f:=b0) (g:=bS) (P:=mkFam F Fm); intros; simpl.
 apply inSAT_val with (3:=H0); try reflexivity.
 rewrite NATREC_0; reflexivity.

 apply inSAT_val with (fS' n (NATREC f0 fS' n)) (app P (SUCC n)); try reflexivity.
  rewrite NATREC_S; trivial.
   reflexivity.

   apply is_num.

  apply H1; trivial.
  rewrite realNat_def.
  exists (is_num n).
  destruct n; exact H4.
Qed.

Lemma red_iota_simulated_0 : forall f g j,
  clos_trans _ Lc.red1 (tm j (NatRec f g Zero)) (tm j f).
simpl; intros.
unfold ZE.
apply t_trans with (Lc.App (Lc.Abs (Lc.lift 1 (tm j f))) (tm j g)).
 apply t_step.
 apply Lc.app_red_l.
 apply Lc.beta.

 apply t_step.
 rewrite <- (Lc.lift0 (tm j f)) at 2.
 unfold Lc.lift at 2.
 rewrite <- (Lc.simpl_subst_rec (tm j g) (tm j f) 0 0 0); auto with arith.
 apply Lc.beta.
Qed.

Lemma red_iota_simulated_S : forall f g n j,
  clos_trans _ Lc.red1
    (tm j (NatRec f g (App Succ n)))
    (tm j (App (App g n) (NatRec f g n))).
simpl; intros.
unfold SU.
apply t_trans with 
 (Lc.App2 (Lc.Abs (Lc.Abs (Lc.App2 (Lc.Ref 0) (Lc.lift 2 (tm j n))
    (Lc.App2 (Lc.lift 2 (tm j n)) (Lc.Ref 1) (Lc.Ref 0)))))
    (tm j f) (tm j g)).
 apply t_step; do 2 constructor.
 apply Lc.beta.

 apply t_trans with
  (let nn := Lc.subst_rec (tm j f) (Lc.lift 2 (tm j n)) 1 in
   let ff := Lc.lift 1 (tm j f) in
   (Lc.App (Lc.Abs (Lc.App2 (Lc.Ref 0) nn (Lc.App2 nn ff (Lc.Ref 0)))) (tm j g))).
  apply t_step; repeat constructor.

  rewrite Lc.simpl_subst; auto with arith.
  replace (Lc.App (Lc.App (tm j g) (tm j n)) (Lc.App2 (tm j n) (tm j f) (tm j g)))
   with (let nn := Lc.subst_rec (tm j g) (Lc.lift 1 (tm j n)) 0 in
         let ff := Lc.subst_rec (tm j g) (Lc.lift 1 (tm j f)) 0 in
         let gg := Lc.lift 0 (tm j g) in
         Lc.App2 gg nn (Lc.App2 nn ff gg)).
   apply t_step; simpl; repeat constructor.

   repeat rewrite Lc.simpl_subst; auto with arith; repeat rewrite Lc.lift0.
   reflexivity.
Qed.