
(** In this file, we build a strong normalization model of the
    Calculus of Constructions extended with natural numbers and
    the usual recursor.
    This file supports universes.
 *)

Set Implicit Arguments.
Require Import basic ZF ZFcoc ZFuniv_real ZFnats.
Require Import Sat SATnat SN_CC_Real.
Module Lc:=Lambda.
Import CC_Real.

(* Building the realizability on the nats of ZFnats *)
Module natARG <: SimpleNats.
 Include ZFnats.
 Definition Nbot := N.
 Definition N_Nbot : N ⊆ N := reflexivity N.
 Definition Ndec n (h:n∈N) : n∈N \/ ~n∈N := or_introl _ h.
End natARG.
Module SAT_nat := SATnat.Make(natARG).
Export natARG SAT_nat.

(** * Nat and its constructors *)

Definition Zero : term.
(*begin show*)
left; exists (fun _ => zero);[|exact ZE].
(*end show*)
 do 2 red; reflexivity.
Defined.

Definition Succ : term.
(*begin show*)
left; exists (fun _ => lam (mkTY N cNAT) succ);[|exact SU].
(*end show*)
 do 2 red; reflexivity.
Defined.

Definition Nat : term.
(*begin show*)
left; exists (fun _ => mkTY N cNAT);[|exact Lc.K].
(*end show*)
 do 2 red; reflexivity.
Defined.


Lemma mt_in_N : cc_bot N == N.
apply eq_intro; intros.
 apply union2_elim in H; destruct H; trivial.
 apply singl_elim in H; rewrite H.
 apply zero_typ.

 apply union2_intro2; trivial.
Qed.
Definition eqNbot := mt_in_N.

Lemma ElNat_eq i : El (int Nat i) == N.
simpl; rewrite El_def.
apply mt_in_N.
Qed.

Lemma RealNat_eq i n :
  n ∈ N ->
  eqSAT (Real (int Nat i) n) (cNAT n).
intros.
simpl int.
rewrite Real_def; intros; trivial.
 reflexivity.

 apply cNAT_morph; trivial.

 rewrite mt_in_N; trivial.
Qed.

  Notation "[ x , t ] \real A" := (x ∈ El A  /\ inSAT t (Real A x)) (at level 60).

Lemma realNat_def : forall i n t,
  [n,t] \real int Nat i <-> n ∈ N /\ inSAT t (cNAT n).
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
 apply zero_typ.

 apply cNAT_ZE.
Qed.

Lemma sn_SU : Lc.sn SU.
unfold SU.
constructor; intros ? h.
apply Lc.nf_norm in h;[contradiction|repeat constructor].
Qed.


Lemma typ_S : forall e, typ e Succ (Prod Nat (lift 1 Nat)).
intros.
apply typ_common;[exact I|intros i j isval].
rewrite intProd_eq.
apply rprod_intro_sn.
 red; red; intros.
 rewrite H0; reflexivity.

 red; intros.
 rewrite H0; reflexivity.

 apply sn_SU.

 destruct 1; split; unfold inX in *.
  rewrite int_cons_lift_eq.
  rewrite ElNat_eq in H|-*.
  apply succ_typ; trivial.

  rewrite int_cons_lift_eq.
  rewrite ElNat_eq in H.
  rewrite RealNat_eq in H0|-*; trivial.
  2:apply succ_typ; trivial.
  apply cNAT_SU; trivial.
Qed.

Lemma typ_N : forall e, typ e Nat kind.
red; red; simpl; intros.
split;[discriminate|].
split; trivial.
exact Lc.sn_K.
Qed.

(** Recursor *)
Definition NatRec (f g n:term) : term.
(*begin show*)
left; exists (fun i => natrec (int f i) (fun n y => app (app (int g i) n) y) (int n i));
[|exact (Lc.App2 (tmm n) (tmm f) (tmm g))].
(*end show*)
 do 2 red; intros.
 apply natrec_morph.
  rewrite H; reflexivity.
(**)
  do 2 red; intros.
  rewrite H; rewrite H0; rewrite H1; reflexivity.
(**)
  rewrite H; reflexivity.
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
simpl.
set (gg := fun n y => app (app (int g i) n) y).
assert (ggm : morph2 gg).
 unfold gg; do 3 red; intros.
 rewrite H;rewrite H0; reflexivity.
red in tyn, tyf, tyg.
rewrite ElNat_eq in tyn.
rewrite RealNat_eq in satn; trivial.
rewrite El_int_prod in tyg.
rewrite Real_int_prod in satg; trivial.
assert (tygg :forall k h : set,
   k ∈ N -> h ∈ El (app (int P i) k) -> gg k h ∈ El (app (int P i) (succ k))).
 intros.
 rewrite <- ElNat_eq with (i:=i) in H.
 apply cc_prod_elim with (2:=H) in tyg.
 rewrite El_int_prod in tyg.
 assert (tyh : h ∈ El (app (int (lift 1 P) (V.cons k i)) k)).
  rewrite int_cons_lift_eq; trivial.
 apply cc_prod_elim with (2:=tyh) in tyg.
 simpl in tyg.
 rewrite int_lift_eq in tyg.
 rewrite beta_eq in tyg; auto with *.
 red; intros; apply succ_morph; trivial.
assert (NRtyp : forall n, n ∈ N ->
  natrec (int f i) gg n ∈ El (app (int P i) n)).
 intros.
 apply natrec_typ with (P:=fun x => El (app (int P i) x)); trivial.
 do 2 red; intros.
 rewrite <- H0; reflexivity.
apply and_split; intros.
 red; apply NRtyp; trivial.

 rewrite <- !tm_tmm.
 red in H.
 apply fNAT_def with (P:=fun k => Real (app (int P i) k) (natrec (int f i) gg k))
    (A:=cNAT).
  rewrite cNAT_eq in satn; trivial.

  do 2 red; intros.
  rewrite H0; reflexivity.

  rewrite natrec_0; trivial.

  apply depSAT_intro.
   apply sat_sn in satg; trivial.
  intros m tym.
  apply prodSAT_intro'; intros mt satm.
  apply prodSAT_intro'; intros v satv.
  rewrite natrec_S; trivial.
  apply piSAT0_elim' in satg; red in satg.
  rewrite <- RealNat_eq with (i:=i) in satm; trivial.
  rewrite <- ElNat_eq with (i:=i) in tym.
  specialize satg with (1:=tym) (2:=satm).
  rewrite Real_int_prod in satg.
   apply piSAT0_elim' in satg; red in satg.
   specialize satg with (x:=natrec (int f i) gg m) (u:=v).
   simpl in satg.
   rewrite int_cons_lift_eq in satg.
   rewrite ElNat_eq in tym.
   specialize satg with (1:=NRtyp _ tym) (2:=satv).
   rewrite int_lift_eq in satg.
   rewrite beta_eq in satg; auto with *.
    red; intros; apply succ_morph; trivial.

    red; rewrite El_def; auto.
    apply cc_prod_elim with (2:=tym) in tyg.
    rewrite El_int_prod in tyg; trivial.
Qed.

(** beta-reduction on the realizers simulates the reduction of
    the eliminator *)

Lemma red_iota_simulated_0 : forall f g,
  red_term (NatRec f g Zero) f.
red; simpl; intros.
unfold ZE.
eapply t_trans;[apply Lc.redp_app_l;apply t_step;apply Lc.red1_beta; reflexivity|].
unfold Lc.subst; simpl.
apply t_step.
apply Lc.red1_beta.
unfold Lc.subst; rewrite Lc.simpl_subst; trivial.
rewrite Lc.lift0; trivial.
Qed.

Lemma red_iota_simulated_S : forall f g n,
  red_term (NatRec f g (App Succ n)) (App (App g n) (NatRec f g n)).
red; simpl; intros.
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
Print Assumptions typ_Nrect.
