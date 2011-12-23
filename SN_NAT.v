
(* Nat *)
Set Implicit Arguments.

Require Import ZF ZFcoc ZFind_nat.
Import IZF.

Require Import basic Can Sat SATnat GenRealSN.
Module Lc:=Lambda.
Import MM.

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