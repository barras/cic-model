
(** In this file, we build a strong normalization model of the
    Calculus of Constructions extended with natural numbers and
    the usual recursor.
 *)

Set Implicit Arguments.
Require Import basic Can Sat SATnat_nat SN_ECC_Real.
Require Import ZF ZFcoc ZFuniv_real ZFnats.
Module Lc:=Lambda.
Import SN_CC_Model SN.


(** * Nat and its constructors *)

Definition Zero : trm.
(*begin show*)
left; exists (fun _ => zero) (fun _ => ZE).
(*end show*)
 do 2 red; reflexivity.
 do 2 red; reflexivity.
 red; reflexivity.
 red; reflexivity.
Defined.

Definition Succ : trm.
(*begin show*)
left; exists (fun _ => lam (mkTY N cNAT) succ) (fun _ => SU).
(*end show*)
 do 2 red; reflexivity.
 do 2 red; reflexivity.
 red; reflexivity.
 red; reflexivity.
Defined.

Definition Nat : trm.
(*begin show*)
left; exists (fun _ => mkTY N cNAT) (fun _ => Lc.K).
(*end show*)
 do 2 red; reflexivity.
 do 2 red; reflexivity.
 red; reflexivity.
 red; reflexivity.
Defined.


Lemma mt_in_N : cc_bot N == N.
apply eq_intro; intros.
 apply union2_elim in H; destruct H; trivial.
 apply singl_elim in H; rewrite H.
 apply zero_typ.

 apply union2_intro2; trivial.
Qed.

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
apply nf_norm in h;[contradiction|repeat constructor].
Qed.


Lemma typ_S : forall e, typ e Succ (Prod Nat (lift 1 Nat)).
intros.
apply typ_common;[exact I|intros i j isval].
rewrite intProd_eq.
apply prod_intro_sn.
 red; intros.
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
split.
 red.
 exists List.nil.
 exists Nat.
  reflexivity.

  exists empty.
  simpl; intros _.
  unfold SN_CC_Model.inX; rewrite El_def.
  apply union2_intro1; apply singl_intro.

 exact Lc.sn_K.
Qed.

Require Import ZFord.
Require Import ZFrepl.

(** * The recursor *)

Definition NREC f g n y :=
  forall P,
  Proper (eq_set ==> eq_set ==> iff) P -> 
  P zero f -> (forall m x, m ∈ N -> P m x -> P (succ m) (g m x)) -> P n y.

Instance NREC_morph : Proper (eq_set ==> (eq_set==>eq_set==>eq_set) ==> eq_set ==> eq_set ==> iff) NREC.
do 5 red; intros.
apply fa_morph; intros P.
apply fa_morph; intros Pm.
rewrite H.
apply fa_morph; intros _.
apply impl_morph; intros.
 apply fa_morph; intro.
 apply fa_morph; intro.
 apply fa_morph; intro.
 apply fa_morph; intro.
 apply Pm; auto with *.
 apply H0; auto with *.

 apply Pm; auto. 
Qed.

Lemma NREC_inv : forall f g n y,
  morph2 g ->
  NREC f g n y ->
  NREC f g n y /\
  (n == zero -> y == f) /\
  (forall m, m ∈ N -> n == succ m -> exists2 z, NREC f g m z & y == g m z).
intros f g n y gm h; pattern n, y; apply h.
 do 3 red; intros.
 apply and_iff_morphism.
  apply NREC_morph; auto with *.

  apply and_iff_morphism.
   rewrite H; rewrite H0; reflexivity.

   apply fa_morph; intro m.
   apply fa_morph; intros _.
   rewrite H.
   apply fa_morph; intros _.
   apply ex2_morph.
    red; reflexivity.

    red; intros.
    rewrite H0; reflexivity.

 split; [|split]; intros.
  red; auto.

  reflexivity.

  symmetry in H0; apply discr in H0; contradiction.

 intros ? ? ? (?,(?,?)).
 split; [|split]; intros.
  red; intros.
  apply H5; trivial.
  apply H0; auto.

  apply discr in H3; contradiction.
  assert (m == m0).
   apply succ_inj in H4; trivial.
  exists x.
   red; intros.
   rewrite <- H5; apply H0; auto.

   rewrite H5; reflexivity.
Qed.


Lemma NREC_choice_0 : forall f g, uchoice_pred (NREC f g zero).
split; [|split]; intros.
 unfold NREC in *; intros.
 rewrite <- H.
 apply H0; auto.

 exists f.
 red; auto.

 cut (zero==zero); auto with *.
 pattern zero at 2, x; apply H; intros.
  do 3 red; intros.
  rewrite H1; rewrite H2; reflexivity.

  revert H1; pattern zero at 2, x'; apply H0; intros.
   do 3 red; intros.
   rewrite H1; rewrite H2; reflexivity.

   reflexivity.

   symmetry in H3; apply discr in H3; contradiction.

  symmetry in H3; apply discr in H3; contradiction.
Qed.


Lemma NREC_choice : forall f g n,
  n ∈ N ->
  morph2 g ->
  uchoice_pred (NREC f g n).
intros f g n H gm.
split; intros.
 rewrite <- H0; trivial.

 elim H using N_ind; intros.
  revert H2; apply iff_impl.
  apply and_iff_morphism.
   apply ex_morph; red; intros.
   rewrite H1; reflexivity.

   apply fa_morph; intros.
   apply fa_morph; intros.
   rewrite H1; reflexivity.

  split; intros.
   exists f; red; auto.

   apply NREC_inv in H0; trivial; apply NREC_inv in H1; trivial;
   destruct H0 as (_,(?,_)); destruct H1 as (_,(?,_)).
   rewrite H0; auto with *.
   rewrite H1; auto with *.

 destruct H1 as ((y,?),?).
 split.
  exists (g n0 y).
  red; intros.
  apply H5; trivial.
  apply H1; trivial.

  intros.
  apply NREC_inv in H3; trivial; apply NREC_inv in H4; trivial;
   destruct H3 as (_,(_,?)); destruct H4 as (_,(_,?)).
   destruct (H3 n0); auto with *.
   destruct (H4 n0); auto with *.
   rewrite H6; rewrite H8.
   apply gm; auto with *.
Qed.


(** Recursor at the level of sets *)
Definition NATREC f g n := uchoice (NREC f g n).

Instance NATREC_morph :
  Proper (eq_set ==> (eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) NATREC.
do 4 red; intros.
unfold NATREC.
apply uchoice_morph_raw.
red; intros.
apply NREC_morph; trivial.
Qed.

Lemma NATREC_def : forall f g n,
  morph2 g -> n ∈ N -> NREC f g n (NATREC f g n).
intros.
unfold NATREC; apply uchoice_def.
apply NREC_choice; trivial.
Qed.

Lemma NATREC_0 : forall f g, NATREC f g zero == f.
unfold NATREC; intros.
symmetry; apply uchoice_ext; trivial.
 apply NREC_choice_0.

 red; auto.
Qed.

Lemma NATREC_S : forall f g n, morph2 g -> n ∈ N ->
   NATREC f g (succ n) == g n (NATREC f g n).
intros.
elim H0 using N_ind; intros.
 rewrite <- H2; trivial.

 symmetry; apply uchoice_ext.
  apply NREC_choice; trivial.
  apply succ_typ; apply zero_typ.
 red; intros.
 apply H3; trivial.
  apply zero_typ.

  rewrite NATREC_0; auto.

 unfold NATREC at 1; symmetry; apply uchoice_ext; auto.
  apply NREC_choice; trivial.
  do 2 apply succ_typ; trivial.

  red; intros.
  apply H5.
   apply succ_typ; trivial.
  rewrite H2.
  apply H5; trivial.
  revert P H3 H4 H5; change (NREC f g n0 (NATREC f g n0)).
  unfold NATREC; apply uchoice_def.
  apply NREC_choice; trivial.
Qed.

Lemma NATREC_typ P f g n :
  morph1 P ->
  morph2 g ->
  n ∈ N ->
  f ∈ P zero ->
  (forall k h, k ∈ N -> h ∈ P k -> g k h ∈ P (succ k)) ->
  NATREC f g n ∈ P n.
intros.
elim H1 using N_ind; intros.
 rewrite <- H5; trivial.

 rewrite NATREC_0; trivial.

 rewrite NATREC_S; auto.
Qed.

(** Recursor *)
Definition NatRec (f g n:trm) : trm.
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
assert (NRtyp : forall n, n ∈ N ->
  NATREC (int f i) gg n ∈ El (app (int P i) n)).
 destruct H0 as (H0,_).
 destruct H1 as (H1,_); unfold inX, prod, ZFuniv_real.prod in H1; rewrite El_def in H1.
 intros.
 apply NATREC_typ with (P:=fun x => El (app (int P i) x)); trivial.
  do 2 red; intros.
  rewrite <- H4; reflexivity.

  intros.
  apply union2_elim in H1; destruct H1.
   apply singl_elim in H1; unfold gg; rewrite H1.
   rewrite cc_app_empty.
   rewrite cc_app_empty.
   auto.
  rewrite <- ElNat_eq in H4.
  apply cc_prod_elim with (2:=H4) in H1.
  rewrite intProd_eq in H1.
  unfold prod,ZFuniv_real.prod in H1; rewrite El_def in H1.
  apply union2_elim in H1; destruct H1.
   apply singl_elim in H1; unfold gg; rewrite H1.
   rewrite cc_app_empty.
   auto.
  apply cc_app_typ with (1:=H1); simpl.
   rewrite split_lift; do 2 rewrite int_cons_lift_eq.
   rewrite beta_eq; auto with *.
   red; intros; apply succ_morph; trivial.

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
 destruct H0 as (tyf,rf).
 destruct H1 as (ty,rg).
 unfold inX,prod,ZFuniv_real.prod in ty; rewrite El_def in ty.
 simpl SN_CC_addon.Real.
 apply rn with (P:=fun x => Real (app (int P i) x) (NATREC (int f i) gg x)); intros.
  do 2 red; intros; apply Real_morph.
   rewrite H0; reflexivity.

   apply NATREC_morph; auto with *.

  rewrite NATREC_0; trivial.

  apply depSAT_intro; intros.
   apply sat_sn in rg; trivial.
  apply prodSAT_intro'; intros m satm.
  apply prodSAT_intro'; intros u satu.
  rewrite NATREC_S; trivial.
  rewrite Real_prod in rg.
   apply piSAT0_elim' in rg; red in rg.
   specialize rg with (x:=x) (u:=m).
   rewrite ElNat_eq in rg; trivial.
   rewrite RealNat_eq in rg; trivial.
   specialize rg with (1:=H0)(2:=satm).
   rewrite intProd_eq in rg.
   rewrite Real_prod in rg.
    apply piSAT0_elim' in rg; red in rg.
    specialize rg with (x0:=NATREC (int f i) gg x) (u:=u).
    simpl int in rg.
    rewrite split_lift with (n:=1) in rg.
    do 3 rewrite int_cons_lift_eq in rg.
    rewrite beta_eq in rg; auto with *. 
     red; intros.
     rewrite H3; reflexivity.

     red; rewrite El_def.
     rewrite mt_in_N; trivial.

    red; intros.
    rewrite H3; reflexivity.

    apply union2_elim in ty; destruct ty.
     apply singl_elim in H1; rewrite H1.
     rewrite cc_app_empty; auto.

     apply cc_prod_elim with (1:=H1).
     rewrite ElNat_eq; trivial.

   red; intros.
   rewrite H3; reflexivity.

   unfold ZFuniv_real.prod; rewrite El_def.
   trivial.
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
