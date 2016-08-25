
(** In this file, we build a strong normalization model of the
    Calculus of Constructions extended with natural numbers and
    the usual recursor.
 *)

Set Implicit Arguments.
Require Import basic Can Sat SATnat_old SN_CC_Real_old.
Require Import ZF ZFcoc ZFuniv_real ZFind_nat.
Module Lc:=Lambda.
Import SN CCSN.
Require Import TypModels.

(** * Nat and its constructors *)

Module Make <: Nat_Rules SN.

Definition Zero : term.
(*begin show*)
left; exists (fun _ => ZERO) (fun _ => ZE).
(*end show*)
 do 2 red; reflexivity.
 do 2 red; reflexivity.
 red; reflexivity.
 red; reflexivity.
Defined.

Definition Succ : term.
(*begin show*)
left; exists (fun _ => lam (mkTY NAT cNAT) SUCC) (fun _ => SU).
(*end show*)
 do 2 red; reflexivity.
 do 2 red; reflexivity.
 red; reflexivity.
 red; reflexivity.
Defined.

Definition Nat : term.
(*begin show*)
left; exists (fun _ => mkTY NAT cNAT) (fun _ => Lc.K).
(*end show*)
 do 2 red; reflexivity.
 do 2 red; reflexivity.
 red; reflexivity.
 red; reflexivity.
Defined.

Lemma ElNat_eq i : El (int Nat i) == NAT.
simpl; apply El_def.
Qed.

Lemma RealNat_eq i n :
  n ∈ NAT ->
  eqSAT (Real (int Nat i) n) (cNAT n).
intros.
simpl int.
rewrite Real_def; intros; trivial.
 reflexivity.

 apply cNAT_morph; trivial.
Qed.

  Notation "[ x , t ] \real A" := (x ∈ El A  /\ inSAT t (Real A x)) (at level 60).

Lemma realNat_def : forall i n t,
  [n,t] \real int Nat i <-> n ∈ NAT /\ inSAT t (cNAT n).
intros.
rewrite ElNat_eq.
split; destruct 1; split; trivial.
 rewrite RealNat_eq in H0; trivial.
 rewrite RealNat_eq; trivial.
Qed.

(** Typing rules of constructors *)
Lemma typ_0 : forall e, typ e Zero Nat.
intros.
apply typ_common;[exact I|intros].
apply realNat_def; split.
 apply ZERO_typ.

 apply cNAT_ZE.
Qed.

Lemma sn_SU : Lc.sn SU.
unfold SU.
constructor; intros ? h.
apply nf_norm in h;[contradiction|repeat constructor].
Qed.


Lemma typ_S : forall e, typ e Succ (Prod Nat (lift 1 Nat)).
intros.
apply typ_common;[exact I|intros i j isval].
rewrite intProd_eq.
change (int Succ i) with (lam (int Nat i) SUCC).
apply prod_intro_sn.
 red; intros.
 rewrite H0; reflexivity.

 red; intros.
 rewrite H0; reflexivity.

 apply sn_SU.

 destruct 1; split; unfold inX in *.
  rewrite int_cons_lift_eq.
  rewrite ElNat_eq in H|-*.
  apply SUCC_typ; trivial.

  rewrite int_cons_lift_eq.
  rewrite ElNat_eq in H.
  rewrite RealNat_eq in H0|-*; auto. 
   apply cNAT_SU; trivial.

   apply SUCC_typ; trivial.
Qed.

Lemma typ_N : forall e, typ e Nat kind.
red; red; simpl; intros.
split;[discriminate|].
split.
 red.
 exists List.nil.
 exists Nat.
  reflexivity.

  exists ZERO. (* NAT is not empty! *)
  simpl; intros _.
  unfold inX; rewrite El_def.
  apply ZERO_typ.

 exact Lc.sn_K.
Qed.

Require Import ZFord.


Require Import ZFrepl.

(** * The recursor *)

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
  n ∈ NAT ->
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

(** Recursor at the level of sets *)
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
  morph2 g -> n ∈ NAT -> NREC f g n (NATREC f g n).
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

Lemma NATREC_S : forall f g n, morph2 g -> n ∈ NAT ->
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

Lemma NATREC_typ P f g n :
  morph1 P ->
  morph2 g ->
  n ∈ NAT ->
  f ∈ P ZERO ->
  (forall k h, k ∈ NAT -> h ∈ P k -> g k h ∈ P (SUCC k)) ->
  NATREC f g n ∈ P n.
intros.
elim H1 using NAT_ind; intros.
 rewrite <- H5; trivial.

 rewrite NATREC_0; trivial.

 rewrite NATREC_S; auto.
Qed.

(** Recursor *)
Definition NatRec (f g n:term) : term.
(*begin show*)
left; exists (fun i => NATREC (int f i) (fun n y => app (app (int g i) n) y) (int n i))
             (fun j => Lc.App2 (tm n j) (tm f j) (tm g j)).
(*end show*)
 do 2 red; intros.
 apply NATREC_morph.
  rewrite H; reflexivity.
(**)
  do 2 red; intros.
  rewrite H; rewrite H0; rewrite H1; reflexivity.
(**)
  rewrite H; reflexivity.
(**)
 do 2 red; intros.
 rewrite H; auto.
(**)
 red; intros; simpl.
 repeat rewrite tm_liftable; trivial.
(**)
 red; intros; simpl.
 repeat rewrite tm_substitutive; trivial.
Defined.

(** Typing rule of the eliminator *)
Lemma typ_Nrect : forall e n f g P,
  typ e n Nat ->
  typ e f (App P Zero) ->
  typ e g (Prod Nat (Prod (App (lift 1 P) (Ref 0))
              (App (lift 2 P) (App Succ (Ref 1))))) ->
  typ e (NatRec f g n) (App P n).
intros.
apply typ_common; [exact I|intros].
red in H; specialize H with (1:=H2).
red in H0; specialize H0 with (1:=H2).
red in H1; specialize H1 with (1:=H2).
apply in_int_not_kind in H;[|discriminate].
apply in_int_not_kind in H0;[|discriminate].
apply in_int_not_kind in H1;[|discriminate].
rewrite intProd_eq in H1.
pose (gg := fun n y => app (app (int g i) n) y).
assert (ggm : morph2 gg).
 unfold gg; do 3 red; intros.
 rewrite H3;rewrite H4; reflexivity.
assert (NRtyp : forall n, n ∈ NAT ->
  NATREC (int f i) gg n ∈ El (app (int P i) n)).
 destruct H0 as (H0,_).
 destruct H1 as (H1,_); unfold inX, prod in H1; rewrite El_def in H1.
 intros.
 apply NATREC_typ with (P:=fun x => El (app (int P i) x)); trivial.
  do 2 red; intros.
  rewrite <- H4; reflexivity.

  intros.
  rewrite <- ElNat_eq in H4.
  apply cc_prod_elim with (2:=H4) in H1.
  rewrite intProd_eq in H1.
  unfold prod in H1; rewrite El_def in H1.
  apply cc_app_typ with (1:=H1); simpl.
   rewrite split_lift; do 2 rewrite int_cons_lift_eq.
   rewrite beta_eq; auto with *.
   red; intros.
   rewrite H7; reflexivity.

   rewrite int_cons_lift_eq; trivial.
split.
 simpl.
 destruct H as (H,_); unfold inX in H; rewrite ElNat_eq in H.
 apply NRtyp; trivial.

 simpl tm.
 destruct H as (H,rn).
 unfold inX in H; rewrite ElNat_eq in H.
 rewrite RealNat_eq in rn; trivial.
 rewrite cNAT_eq in rn.
 rewrite fNAT_def in rn.
 destruct H0 as (_,rf).
 destruct H1 as (ty,rg).
 unfold inX,prod in ty; rewrite El_def in ty.
 simpl Real.
 apply rn with (P:=fun x => Real (app (int P i) x) (NATREC (int f i) gg x)); intros.
  do 2 red; intros.
  apply Real_morph.
   rewrite H0; reflexivity.

   apply NATREC_morph; auto with *.

  rewrite NATREC_0; trivial.

  rewrite Real_prod in rg.
   apply depSAT_intro; intros.
    apply sat_sn in rg; trivial.
   rewrite NATREC_S; trivial.
   apply prodSAT_intro'; intros m satm.
   apply piSAT0_elim' in rg; red in rg.
   specialize rg with (x:=x)(u:=m).
   unfold inX in rg;rewrite ElNat_eq in rg; trivial.
   rewrite RealNat_eq in rg; trivial.
   rewrite intProd_eq in rg.
   rewrite Real_prod in rg.
    apply prodSAT_intro'; intros y saty.
    assert (rg' := rg H0 satm); clear rg.
    apply piSAT0_elim' in rg'; red in rg'.
    specialize rg' with (x0:=NATREC (int f i) gg x)(u:=y).
    simpl int in rg'.
    rewrite int_cons_lift_eq in rg'.
    assert (rg := rg' (NRtyp _ H0) saty); clear rg'.
    rewrite split_lift in rg.
    do 2 rewrite int_cons_lift_eq in rg.
    rewrite beta_eq in rg; auto with *.
     red; intros.
     rewrite H3; reflexivity.

     rewrite El_def; trivial.

    red; intros.
    rewrite <- H3; reflexivity.

    apply cc_prod_elim with (1:=ty).
    rewrite ElNat_eq; trivial.

   red; intros.
   rewrite <- H1; reflexivity.

   revert ty; apply eq_elim.
   unfold prod; rewrite El_def.
   reflexivity.
Qed.

(** beta-reduction on the realizers simulates the reduction of
    the eliminator *)

Lemma red_iota_simulated_0 : forall f g,
  red_term (NatRec f g Zero) f.
red; simpl; intros.
apply ZE_iota.
Qed.

Lemma red_iota_simulated_S : forall f g n,
  red_term (NatRec f g (App Succ n)) (App (App g n) (NatRec f g n)).
red; simpl; intros.
apply SU_iota.
Qed.


Lemma eq_typ_NatRec e f f' g g' n n' :
    eq_typ e f f' ->
    eq_typ e g g' ->
    eq_typ e n n' ->
    eq_typ e (NatRec f g n) (NatRec f' g' n').
unfold eq_typ; intros.
specialize H with (1:=H2).
specialize H0 with (1:=H2).
specialize H1 with (1:=H2).
red; simpl.
apply NATREC_morph; trivial.
do 2 red; intros.
rewrite H0,H3,H4; reflexivity.
Qed.

Lemma NatRec_eq_0 e f g :
    eq_typ e (NatRec f g Zero) f.
red; simpl; intros.
rewrite NATREC_0; reflexivity.
Qed.

Lemma NatRec_eq_S e f g n :
    typ e n Nat ->
    eq_typ e (NatRec f g (App Succ n)) (App (App g n) (NatRec f g n)).
unfold typ, eq_typ; intros.
specialize H with (1:=H0).
apply in_int_not_kind in H.
2:discriminate.
simpl.
transitivity (NATREC (int f i) (fun n y => app (app (int g i) n) y) (SUCC (int n i))).
 apply NATREC_morph; auto with *.
  do 2 red; intros.
  rewrite H1, H2; reflexivity.

  apply beta_eq.
   red; intros; apply ZFsum.inr_morph; trivial.

   apply H.

 rewrite NATREC_S.
  reflexivity.

  do 3 red; intros.
  rewrite H1, H2; reflexivity.

 destruct H.
 red in H; rewrite ElNat_eq in H; trivial.
Qed.

End Make.
