
(** In this file, we build a strong normalization model of the
    Calculus of Constructions extended with natural numbers and
    the usual recursor.
    This file supports universes.
 *)

Set Implicit Arguments.
Require Import basic Can Sat SATnat SN_CC_Real.
Require Import ZF ZFcoc ZFuniv_real ZFind_natbot.
Module Lc:=Lambda.
Import SN_CC_Model SN.


(** * Nat and its constructors *)

Definition Zero : trm.
(*begin show*)
left; exists (fun _ => ZERO) (fun _ => ZE).
(*end show*)
 do 2 red; reflexivity.
 do 2 red; reflexivity.
 red; reflexivity.
 red; reflexivity.
Defined.

Definition Succ : trm.
(*begin show*)
left; exists (fun _ => lam (mkTY NAT' cNAT) SUCC) (fun _ => SU).
(*end show*)
 do 2 red; reflexivity.
 do 2 red; reflexivity.
 red; reflexivity.
 red; reflexivity.
Defined.

Definition Nat : trm.
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

  Notation "[ x , t ] \real A" := (x ∈ El A  /\ inSAT t (Real A x)) (at level 60).

Lemma realNat_def : forall i n t,
  [n,t] \real int Nat i <-> n ∈ cc_bot NAT' /\ inSAT t (cNAT n).
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
 apply cc_bot_intro; apply ZERO_typ'.

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

 destruct 1.
 red in H; rewrite ElNat_eq in H.
 apply and_split; intros.
  red; rewrite int_cons_lift_eq.
  rewrite ElNat_eq.
  apply cc_bot_intro; apply SUCC_typ'; trivial.

  red in H1.
  rewrite int_cons_lift_eq in H1|-*.
  rewrite ElNat_eq in H1.
  rewrite RealNat_eq in H0|-*; trivial.
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

Require Import ZFord ZFfix.
Require Import ZFfixrec.

Definition NREC f g n y :=
  forall (P:set->set->Prop),
  Proper (eq_set==>eq_set==>iff) P ->
  P empty empty ->
  P ZERO f ->
  (forall m z, m ∈ cc_bot NAT' -> P m z -> P (SUCC m) (g m z)) ->
  P n y.

Lemma NREC_mt f g : NREC f g empty empty.
red; intros; trivial.
Qed.
Lemma NREC_ZERO f g : NREC f g ZERO f.
red; intros; trivial.
Qed.
Lemma NREC_SUCC f g n y:
  n ∈ cc_bot NAT' -> NREC f g n y -> NREC f g (SUCC n) (g n y).
unfold NREC; intros.
apply H4; trivial.
apply H0; trivial.
Qed.
Instance NREC_morph :
  Proper (eq_set==>(eq_set==>eq_set==>eq_set)==>eq_set==>eq_set==>iff) NREC.
apply morph_impl_iff4; auto with *.
unfold NREC; do 6 red; intros.
rewrite <- H in H6.
rewrite <- H1; rewrite <- H2; apply H3; trivial.
intros.
rewrite (H0 _ _ (reflexivity m) _ _ (reflexivity z)).
auto.
Qed.
Instance NREC_morph_eq :
  Proper (eq_set==>eq==>eq_set==>eq_set==>iff) NREC.
apply morph_impl_iff4; auto with *.
unfold NREC; do 6 red; intros.
subst x0; rewrite <- H in H6.
rewrite <- H1; rewrite <- H2; apply H3; trivial.
Qed.

Lemma NREC_inv f g n y :
  NREC f g n y ->
   NREC f g n y /\
   ((n==empty/\y==empty) \/
    (n==ZERO/\y==f) \/
    (exists2 m, n == SUCC m & exists2 z, NREC f g m z & y==g m z)).
intros H; apply H; intros.
 do 3 red; intros.
 apply and_iff_morphism.
  apply NREC_morph_eq; auto with *.

  repeat apply or_iff_morphism.
   rewrite H0; rewrite H1; reflexivity.
   rewrite H0; rewrite H1; reflexivity.
   apply ex2_morph; red; intros.
    rewrite H0; reflexivity.
   apply ex2_morph; red; intros.
    apply NREC_morph_eq; auto with *.
    rewrite H1; reflexivity.

 split; auto with *.
 apply NREC_mt.

 split; auto with *.
 apply NREC_ZERO.

 destruct H1 as (?,_).
 split.
  apply NREC_SUCC; trivial.

  right; right.
  exists m;[reflexivity|].
  exists z; auto with *.
Qed.
Lemma NREC_inv_mt f g y :
  NREC f g empty y -> y == empty.
intros; apply NREC_inv in H;
   destruct H as (_,[(_,eqy)|[(abs,_)|(n,abs,_)]]); auto.
 apply discr_mt_pair in abs; contradiction.
 apply discr_mt_pair in abs; contradiction.
Qed.
Lemma NREC_inv_ZERO f g y :
  NREC f g ZERO y -> y == f.
intros; apply NREC_inv in H;
   destruct H as (_,[(abs,_)|[(_,eqy)|(n,abs,_)]]); auto.
 symmetry in abs; apply discr_mt_pair in abs; contradiction.
 apply NATf_discr in abs; contradiction.
Qed.
Lemma NREC_inv_SUCC f g n y :
  morph2 g ->
  NREC f g (SUCC n) y -> exists2 z, NREC f g n z & y == g n z.
intros; apply NREC_inv in H0;
   destruct H0 as (_,[(abs,_)|[(abs,_)|(m,eqS,(z,defz,eqy))]]).
 symmetry in abs; apply discr_mt_pair in abs; contradiction.
 symmetry in abs; apply NATf_discr in abs; contradiction.

 apply SUCC_inj in eqS.
 rewrite <- eqS in defz, eqy; eauto.
Qed.

Require Import ZFrepl.

Lemma NAT'_ind P n :
  Proper (eq_set==>iff) P ->
  n ∈ cc_bot NAT' ->
  P empty ->
  P ZERO ->
  (forall m, m ∈ cc_bot NAT' -> P m -> P (SUCC m)) -> 
  P n.
intros.
revert n H0; unfold NAT'; apply isOrd_ind with (2:=isOrd_omega); intros.
apply cc_bot_ax in H6; destruct H6.
 rewrite H6; trivial.

 apply TI_elim in H6; auto with *.
 destruct H6 as (o',o'o,?).
 apply NATf_case with (3:=H6); intros.
  rewrite H7; trivial.

  rewrite H8; apply H3.
   revert H7; apply cc_bot_mono.
   apply NATf'_stages.
   apply isOrd_inv with y; trivial.

   apply H5 with o'; trivial. 
Qed.

Lemma NREC_uch_mt f g :
  uchoice_pred (NREC f g empty).
split;[|split]; intros.
 rewrite <- H; trivial.

 exists empty; apply NREC_mt.
 apply NREC_inv_mt in H.
 apply NREC_inv_mt in H0.
 rewrite H; rewrite H0; reflexivity.
Qed.

Lemma NREC_uch_ZERO f g :
  uchoice_pred (NREC f g ZERO).
split;[|split]; intros.
 rewrite <- H; trivial.

 exists f; apply NREC_ZERO.
 apply NREC_inv_ZERO in H.
 apply NREC_inv_ZERO in H0.
 rewrite H; rewrite H0; reflexivity.
Qed.

Lemma NREC_uch f g n :
  morph2 g ->
  n ∈ cc_bot NAT' ->
  uchoice_pred (NREC f g n).
intros gm tyn.
apply NAT'_ind with (2:=tyn).
 do 2 red; intros; apply uchoice_pred_morph.
 red; intros; apply NREC_morph_eq; auto with *.

 apply NREC_uch_mt.

 apply NREC_uch_ZERO.

 intros m tym (_,((z,?),muniq)).
 split; [|split]; intros.
  rewrite <- H0; trivial.

  exists (g m z); apply NREC_SUCC; trivial.

  apply NREC_inv_SUCC in H0; trivial.
  apply NREC_inv_SUCC in H1; trivial.
  destruct H0 as (y,?,eqx).
  destruct H1 as (y',?,eqx').
  rewrite eqx; rewrite eqx'; apply gm; eauto with *.
Qed.

Definition NAT_RECT f g n := uchoice (NREC f g n).

Instance NAT_RECT_morph :
  Proper (eq_set==>(eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) NAT_RECT.
do 4 red; intros.
apply uchoice_morph_raw.
red; intros; apply NREC_morph; trivial.
Qed.
Instance NAT_RECT_morph_eq :
  Proper (eq_set==>eq==>eq_set==>eq_set) NAT_RECT.
do 4 red; intros.
apply uchoice_morph_raw.
red; intros; apply NREC_morph_eq; trivial.
Qed.

Lemma NAT_RECT_mt f g :
  NAT_RECT f g empty == empty.
symmetry; apply uchoice_ext.
 apply NREC_uch_mt.

 apply NREC_mt.
Qed.

Lemma NAT_RECT_ZERO f g :
  NAT_RECT f g ZERO == f.
symmetry; apply uchoice_ext.
 apply NREC_uch_ZERO.

 apply NREC_ZERO.
Qed.

Lemma NAT_RECT_eq f g n y :
  morph2 g ->
  n ∈ cc_bot NAT' ->
  (NAT_RECT f g n == y <-> NREC f g n y).
intros.
assert (ch := NREC_uch f H H0).
assert (eqn := uchoice_def _ ch).
split; intros.
 rewrite <- H1; trivial.

 symmetry; apply uchoice_ext; trivial.
Qed.

Lemma NAT_RECT_SUCC f g n :
  morph2 g ->
  n ∈ cc_bot NAT' ->
  NAT_RECT f g (SUCC n) == g n (NAT_RECT f g n).
intros.
apply NAT_RECT_eq; trivial.
 apply cc_bot_intro.
 apply SUCC_typ'; trivial.

 apply NREC_SUCC; trivial.

 apply NAT_RECT_eq; trivial.
 reflexivity.
Qed.


Lemma NAT_RECT_typ f g n P :
  morph1 P ->
  n ∈ cc_bot NAT' ->
  empty ∈ P empty ->
  f ∈ P ZERO ->
  g ∈ cc_prod (cc_bot NAT') (fun m => cc_arr (P m) (P (SUCC m))) ->
  NAT_RECT f (fun m y => cc_app (cc_app g m) y) n ∈ P n.
intros.
apply NAT'_ind with (2:=H0).
 do 2 red; intros.
 apply in_set_morph; auto.  
 apply NAT_RECT_morph_eq; auto with *.

 rewrite NAT_RECT_mt; trivial.

 rewrite NAT_RECT_ZERO; trivial.

 intros.
 rewrite NAT_RECT_SUCC; trivial.
  apply cc_prod_elim with (2:=H4) in H3.
  apply cc_arr_elim with (1:=H3) (2:=H5).

  do 3 red; intros.
  rewrite H6; rewrite H7; reflexivity.
Qed.

(** Recursor *)
Definition NatRec (f g n:trm) : trm.
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
(*assert (tygg :forall k h : set,
   k ∈ cc_bot NAT' -> h ∈ El (app (int P i) k) -> gg k h ∈ El (app (int P i) (SUCC k))).
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
 red; intros; apply succ_morph; trivial.*)
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
 rewrite cNAT'_eq in satn; trivial.
 apply condSAT_smaller in satn; trivial.
 assert (satn' := proj1 (fNAT_def _ _ _) satn); clear satn.
 apply satn' with (P:=fun k => Real (app (int P i) k) (NAT_RECT (int f i) gg k)).
  do 2 red; intros.
  rewrite H0; reflexivity.

  rewrite NAT_RECT_ZERO; trivial.

Lemma interSAT_mono_subset :
  forall A (P Q:A->Prop) (F:sig P->SAT) (G:sig Q->SAT),
  (forall x, Q x -> P x) ->
  (forall x Px Qx,
   inclSAT (F (exist P x Px)) (G (exist Q x Qx))) ->
  inclSAT (interSAT F) (interSAT G).
red; intros.
split.
 apply sat_sn in H1; trivial.
intros (x,Qx).
change (inSAT t (G (exist Q x Qx))).
apply H0 with (Px:=H _ Qx).
apply interSAT_elim with (1:=H1).
Qed.

  revert satg; apply interSAT_mono_subset; simpl proj1_sig; intros.
   rewrite ElNat_eq; trivial.
  apply prodSAT_mono.
   do 2 red; intros.
   rewrite RealNat_eq; auto with *.
  apply cc_prod_elim with (2:=Px) in tyg.
  rewrite El_int_prod in tyg.
Instance inclSAT_morph : Proper (eqSAT==>eqSAT==>iff) inclSAT.
apply morph_impl_iff2; auto with *.
do 5 red; intros.
 rewrite <- H0; rewrite <- H in H2; auto. 
Qed.
  rewrite Real_int_prod; trivial.

Lemma incl_interSAT_l A (F:A->SAT) x :
  inclSAT (interSAT F) (F x).
red; intros.
apply interSAT_elim with (1:=H).
Qed.

  red; intros.
Lemma depSAT_elim' A (P:A->Prop) F t :
  inSAT t (depSAT P F) -> id (forall x, P x -> inSAT t (F x)).
red; intros.
apply depSAT_elim with (1:=H) (2:=H0).
Qed.
  apply depSAT_elim' in H0; red in H0.
  specialize H0 with (x0:=NAT_RECT (int f i) gg x).
  change (int (App (lift 1 P) (Ref 0)) (V.cons x i)) with
    (app (int (lift 1 P) (V.cons x i)) x) in H0.
  rewrite int_lift_eq in H0.
  generalize (H0 (NRtyp x Qx)).
  apply prodSAT_morph.
   reflexivity.

   simpl; rewrite int_lift_eq.
   apply Real_morph.
    rewrite beta_eq.
     reflexivity.

     red; intros; apply couple_morph; auto with *.

     red; rewrite El_def; trivial.

    rewrite NAT_RECT_SUCC; auto with *.
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

Print Assumptions typ_Nrect.
