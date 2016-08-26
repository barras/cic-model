
(** In this file, we build a strong normalization model of the
    Calculus of Constructions extended with natural numbers and
    the usual recursor.
    This file supports universes.
 *)

Set Implicit Arguments.
Require Import basic Can Sat SATnat SN_CC_Real.
Require Import TypModels.
Require Import ZF ZFcoc ZFuniv_real ZFind_natbot.
Module Lc:=Lambda.

(* Building the realizability on the nats of ZFind_natbot *)
Module natARG <: SimpleNats.
  Definition N := NAT'.
  Definition Nbot := cc_bot NAT'.
  Definition N_Nbot : N ⊆ Nbot := cc_bot_intro NAT'.
  Lemma Ndec n (h:n ∈ Nbot) : n ∈ N \/ ~ n ∈ N.
    apply cc_bot_ax in h; destruct h; [right|left;trivial].
    rewrite H; intros h; apply mt_not_in_NATf' in h; auto with *.
  Qed.    

  Definition zero := ZERO.
  Definition succ := SUCC.
  Definition succ_morph := ZFsum.inr_morph.

  Definition zero_typ := ZERO_typ'.
  Definition succ_typ := SUCC_typ'.
End natARG.
Module SAT_nat := SATnat.Make(natARG).
Import SAT_nat.

(** * Nat and its constructors *)

Module Make <: Nat_Rules SN_CC_Real.SN.

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
left; exists (fun _ => lam (mkTY NAT' cNAT) SUCC) (fun _ => SU).
(*end show*)
 do 2 red; reflexivity.
 do 2 red; reflexivity.
 red; reflexivity.
 red; reflexivity.
Defined.

Definition Nat : term.
(*begin show*)
left; exists (fun _ => mkTY NAT' cNAT) (fun _ => Lc.K).
(*end show*)
 do 2 red; reflexivity.
 do 2 red; reflexivity.
 red; reflexivity.
 red; reflexivity.
Defined.

Lemma ElNat_eq i : El (int Nat i) == cc_bot NAT'.
simpl; rewrite El_def; reflexivity.
Qed.

Lemma RealNat_eq i n :
  n ∈ cc_bot NAT' ->
  eqSAT (Real (int Nat i) n) (cNAT n).
intros.
simpl int.
rewrite Real_def; intros; trivial.
 reflexivity.

 apply cNAT_morph; trivial.
Qed.

Lemma typ_N e : typ e Nat kind.
red; simpl; intros.
unfold in_int; simpl.
split; [discriminate|split; auto with *].
apply Lc.sn_K.
Qed.

(** Typing rules of constructors *)
Lemma typ_0 : forall e, typ e Zero Nat.
intros.
apply typ_common;[exact I|intros].
apply and_split; intros.
 red; rewrite ElNat_eq.
 apply cc_bot_intro; apply ZERO_typ'.

 red in H0; rewrite ElNat_eq in H0.
 rewrite RealNat_eq; trivial.
 apply cNAT_ZE.
Qed.

Lemma typ_S : forall e, typ e Succ (Prod Nat (lift 1 Nat)).
intros.
apply typ_common;[exact I|intros i j isval].
apply and_split; intros.
 red.
 rewrite El_int_prod.
 apply cc_prod_intro.
  do 2 red; intros.
  rewrite H0; reflexivity.

  do 2 red; intros.
  rewrite H0; reflexivity.

  intros.
  rewrite int_cons_lift_eq.
  rewrite ElNat_eq in H|-*.
  apply cc_bot_intro; apply SUCC_typ'; trivial.

 red in H.
 rewrite El_int_prod in H.
 rewrite Real_int_prod; trivial.
 apply piSAT0_intro'.
 2:exists empty; auto.
 intros.
 rewrite int_cons_lift_eq.
 rewrite ElNat_eq in H0.
 simpl (int Succ i); rewrite beta_eq.
  rewrite RealNat_eq in H1|-*; trivial.
   apply cNAT_SU; trivial.

   apply cc_bot_intro; simpl.
   apply SUCC_typ'; trivial.

  red; intros; apply couple_morph; auto with *.

  red; rewrite El_def; trivial.
Qed.

(** Recursor *)
Definition NatRec (f g n:term) : term.
(*begin show*)
left; exists (fun i => NAT_RECT (int f i) (fun n y => app (app (int g i) n) y) (int n i))
             (fun j => Lc.App2 (tm n j) (tm f j) (tm g j)).
(*end show*)
 do 2 red; intros.
 apply NAT_RECT_morph.
  rewrite H; reflexivity.
  do 2 red; intros; repeat apply cc_app_morph; trivial; apply int_morph; auto with *.
  rewrite H; reflexivity.
(**)
  do 2 red; intros.
  rewrite H; reflexivity.
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
destruct H as (tyn, satn).
destruct H0 as (tyf, satf).
destruct H1 as (tyg, satg).
red in tyn, tyf, tyg.
set (gg := fun n y => app (app (int g i) n) y).
assert (ggm : morph2 gg).
 unfold gg; do 3 red; intros.
 rewrite H;rewrite H0; reflexivity.
rewrite ElNat_eq in tyn.
rewrite RealNat_eq in satn; trivial.
rewrite El_int_prod in tyg.
rewrite Real_int_prod in satg; trivial.
assert (NRtyp : forall n, n ∈ cc_bot NAT' ->
  NAT_RECT (int f i) gg n ∈ El (app (int P i) n)).
 intros.
 apply NAT_RECT_typ with (P:=fun x => El (app (int P i) x)); trivial.
  do 2 red; intros.
  rewrite <- H0; reflexivity.

  revert tyg; apply eq_elim; symmetry; apply cc_prod_ext.
   rewrite ElNat_eq; reflexivity.

   red; intros.
   rewrite El_int_prod.
   apply cc_prod_ext.
    simpl.
    rewrite int_lift_eq.
    rewrite H1; reflexivity.

    red; intros.
    simpl; rewrite int_lift_eq.
    rewrite beta_eq.
     rewrite H1; reflexivity.

     red; intros; apply couple_morph; auto with *.

     red; rewrite El_def; trivial.
     rewrite <- H1; trivial.
apply and_split; intros.
 red; apply NRtyp; trivial.

 red in H.
 simpl tm.
 apply cNAT_pre in satn; trivial.
 assert (satn' := proj1 (fNAT_def _ _ _) satn); clear satn.
 apply satn' with (P:=fun k => Real (app (int P i) k) (NAT_RECT (int f i) gg k)).
  do 2 red; intros.
  rewrite H0; reflexivity.

  rewrite NAT_RECT_ZERO; trivial.

 apply depSAT_intro'.
  exists (int n i); trivial.
 intros k tyk.
 apply prodSAT_intro'.
 intros tk satk.
 apply prodSAT_intro'.
 intros v satv.
 apply piSAT0_elim' in satg.
 red in satg.
 rewrite <- (RealNat_eq i) in satk; trivial.
 rewrite <- (ElNat_eq i) in tyk.
 specialize satg with (1:=tyk) (2:=satk).
 apply cc_prod_elim with (2:=tyk) in tyg.
 rewrite El_int_prod in tyg.
 rewrite Real_int_prod in satg; trivial.
 apply piSAT0_elim' in satg.
 red in satg.
 refine (_ (satg _ _ _ _)).
  apply Real_morph.
   simpl.
   rewrite int_lift_eq.
   unfold V.shift; simpl.
   rewrite beta_eq; auto with *.
    reflexivity.

    red; intros.
    apply ZFsum.inr_morph; trivial.

   rewrite NAT_RECT_SUCC; auto.
   2:rewrite (ElNat_eq i) in tyk; trivial.
   unfold gg.
   reflexivity.

  simpl.
  rewrite int_lift_eq.
  apply NRtyp.
  rewrite (ElNat_eq i) in tyk; trivial.

  simpl.
  rewrite int_lift_eq.
  exact satv.
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

Print Assumptions typ_Nrect.

Lemma eq_typ_NatRec : forall e f f' g g' n n',
    eq_typ e f f' ->
    eq_typ e g g' ->
    eq_typ e n n' ->
    eq_typ e (NatRec f g n) (NatRec f' g' n').
unfold eq_typ; simpl; intros.
specialize H with (1:=H2).
specialize H0 with (1:=H2).
specialize H1 with (1:=H2).
apply NAT_RECT_morph; eauto with *.
do 2 red; intros.
red in H0.
rewrite H0,H3,H4; reflexivity.
Qed.

Lemma NatRec_eq_0 e f g :
    eq_typ e (NatRec f g Zero) f.
red; simpl; intros.
rewrite NAT_RECT_ZERO; reflexivity.
Qed.

Lemma NatRec_eq_S : forall e f g n,
    typ e n Nat ->
    eq_typ e (NatRec f g (App Succ n)) (App (App g n) (NatRec f g n)).
red; simpl; intros.
red in H; specialize H with (1:=H0).
apply in_int_not_kind in H.
2:discriminate.
destruct H.
red in H; rewrite ElNat_eq in H.
rewrite beta_eq.
 rewrite NAT_RECT_SUCC; trivial.
  reflexivity.

  do 3 red; intros.
  rewrite H2,H3; reflexivity. 

 red; intros; apply ZFsum.inr_morph; trivial.

 red; rewrite El_def; trivial.
Qed.

End Make.
