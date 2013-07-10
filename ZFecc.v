Require Import ZF ZFpairs ZFnats ZFgrothendieck.
Require Import ZFrelations ZFcoc.

(** Statement that there exists a set containing infinitely many Grothendieck universes *)

(*Definition infinitely_many_universes :=
  { U:set | empty ∈ U /\ forall x, x ∈ U -> grot_succ x ∈ U }.*)
Definition infinitely_many_universes :=
  { U:set | empty ∈ U /\ forall x, x ∈ U -> exists V, V ∈ U /\ grot_univ V /\ x ∈ V }.
(*
Instance grot_succ_pred_mono : Proper (eq_set==>eq_set==>iff) grot_succ_pred.
do 3 red; intros.
apply and_iff_morphism.
 split; apply grot_univ_ext; auto with *.
apply and_iff_morphism.
 apply in_set_morph; trivial.
apply fa_morph; intros U.
rewrite H; rewrite H0; reflexivity.
Qed.
*)

Instance grot_succ_pred_morph : Proper (eq_set==>eq_set==>iff) grot_succ_pred.
do 3 red; intros.
apply and_iff_morphism.
 split; apply grot_univ_ext; auto with *.
apply and_iff_morphism.
 apply in_set_morph; trivial.
apply fa_morph; intros U.
rewrite H; rewrite H0; reflexivity.
Qed.

Lemma grot_succ_incl x y :
  x ∈ grot_succ y ->
  ZFrepl.uchoice_pred (grot_succ_pred x) ->
  ZFrepl.uchoice_pred (grot_succ_pred y) ->
  grot_succ x ⊆ grot_succ y.
intros.
specialize ZFrepl.uchoice_def with (1:=H0); intros (?,(?,xmin)).
specialize ZFrepl.uchoice_def with (1:=H1); intros (?,(?,_)).
apply xmin; trivial.
Qed.
Lemma grot_succ_mono x y :
  x ⊆ y ->
  ZFrepl.uchoice_pred (grot_succ_pred x) ->
  ZFrepl.uchoice_pred (grot_succ_pred y) ->
  grot_succ x ⊆ grot_succ y.
intros.
apply grot_succ_incl; trivial.
specialize ZFrepl.uchoice_def with (1:=H1); intros (?,(?,_)).
apply G_incl with y; trivial.
Qed.

(** In Tarski-Grothendieck set theory, there exists an infinite sequence of universes *)
Lemma tg_implies_ecc : grothendieck -> infinitely_many_universes.
assert (gsm : morph1 grot_succ).
 do 2 red ;intros.
 apply ZFrepl.uchoice_morph_raw.
 red; intros.
 apply grot_succ_pred_morph; trivial.
intros gr.
exists (ZFord.TI grot_succ ZFord.omega).
split; intros.
 apply ZFord.TI_intro with (ZFord.osucc zero); auto.
 eapply G_incl.
  apply (grot_succ_typ gr).

  apply (grot_succ_in gr).

  red; intros.
  apply empty_ax in H; contradiction.

 apply ZFord.TI_elim in H; auto.
 destruct H as (o,?,?).
 assert (oo: ZFord.isOrd o) by eauto using ZFord.isOrd_inv.
 exists (grot_succ (ZFord.TI grot_succ o)).
 split;[|split]; trivial.
 2:apply (grot_succ_typ gr).
 apply ZFord.TI_intro with (ZFord.osucc o); auto.
 eapply G_incl.
  apply (grot_succ_typ gr).

  apply (grot_succ_in gr).

  red; intros.
  apply ZFord.TI_intro with o; auto.
Qed.

(*
(* We are in Tarski-Grothendieck set theory: *)
Axiom gr : grothendieck.
*)

Axiom infinite_seq_of_grot_univ : infinitely_many_universes.

Let U := proj1_sig infinite_seq_of_grot_univ.

Fixpoint ecc (n:nat) : set :=
  match n with
  | 0 => grot_succ props (* grot_succ props is included in HF *)
  | S k => grot_succ (ecc k)
  end.

Lemma grot_succU y x :
  y ⊆ x -> 
  x ∈ U ->
  grot_univ (grot_succ y) /\ y ∈ grot_succ y /\ exists2 W, W ∈ U & grot_succ y ⊆ W.
intros.
destruct (proj2_sig infinite_seq_of_grot_univ) as (_,nextU); fold U in *.
destruct nextU with (1:=H0) as (V,(VU,(gV,xV))).
pose (W:=subset V (fun z =>
    forall U, grot_univ U -> y ∈ U -> z ∈ U)).
assert (grot_succ_pred y W).
 split;[|split]; intros.
  apply grot_intersection; trivial.
  apply G_incl with x; auto.

  apply subset_intro; trivial.
  apply G_incl with x; auto.

  red; intros.
  unfold W in H3; rewrite subset_ax in H3; destruct H3.
  destruct H4 as (z',eqz,min).
  rewrite eqz; auto.
assert (ZFrepl.uchoice_pred (grot_succ_pred y)).
 split;[|split]; intros.
  revert H3; apply grot_succ_pred_morph; auto with *.

  exists W; trivial.

  destruct H2 as (?,(?,?)).
  destruct H3 as (?,(?,?)).
  apply incl_eq; auto.
specialize ZFrepl.uchoice_ext with (1:=H2)(2:=H1); intro.
fold (grot_succ y) in H3.
split.
 apply grot_univ_ext with W; auto.
 apply H1.
split.
 destruct H1 as (_,(?,_)).
 rewrite <- H3; trivial.

 exists V; trivial.
 rewrite <- H3.
 red; intros.
 apply subset_elim1 in H4; trivial.
Qed.


Lemma grot_succ_hf : grot_succ empty == grot_succ props.
  apply ZFrepl.uchoice_morph_raw.
  red; intros.
  unfold grot_succ_pred.
  split; intros.
   destruct H0.
   assert (grot_univ y).
    revert H0; apply grot_univ_ext; auto.
   split; trivial.
   destruct H1; split; intros.
    apply G_power; trivial.
    apply G_singl; trivial.
    rewrite <- H; trivial.

    rewrite <- H; apply H3; trivial.
    apply G_incl with props; trivial.
    red; intros.
    apply empty_ax in H6; contradiction.

   destruct H0.
   assert (grot_univ x).
    revert H0; apply grot_univ_ext; auto with *.
   split; trivial.
   destruct H1; split; intros.
    rewrite H.
    apply G_incl with props; trivial.
    red; intros.
    apply empty_ax in H4; contradiction.

    rewrite H; apply H3; trivial.
    apply G_power; trivial.
    apply G_singl; trivial.
Qed.

Lemma ecc_U : forall n, grot_univ (ecc n) /\ exists2 W, W ∈ U & ecc n ⊆ W.
destruct (proj2_sig infinite_seq_of_grot_univ) as (mtU, nextU); fold U in *.
induction n; simpl; intros.
 destruct grot_succU with empty empty as (?,(_,?)); auto with *.
 split; intros.
  revert H; apply grot_univ_ext; auto with *.
  apply grot_succ_hf.

  destruct H0.
  exists x; trivial.
  rewrite <- grot_succ_hf; trivial.

 destruct IHn as (?,(W,?,?)).
 destruct grot_succU with (1:=H1)(2:=H0) as (?,(_,?)); auto.
Qed.

Lemma ecc_grot : forall n, grot_univ (ecc n).
intros.
apply ecc_U.
Qed.
Hint Resolve ecc_grot.

Lemma ecc_in2 : forall n, ecc n ∈ ecc (S n).
simpl; intros.
destruct ecc_U with n as (?,(W,?,?)).
destruct grot_succU with (1:=H1)(2:=H0) as (_,(?,_)); trivial.
Qed.

Lemma ecc_in1 : forall n, props ∈ ecc n.
induction n; simpl; intros.
 destruct grot_succU with empty empty as (?,(?,?)); auto with *.
  apply (proj2_sig infinite_seq_of_grot_univ).

  rewrite <- grot_succ_hf.
  apply G_power; trivial.
  apply G_singl; trivial.

 apply G_trans with (ecc n); trivial.
  apply (ecc_grot (S n)).

  apply ecc_in2.
Qed.
 

Lemma ecc_incl : forall n x, x ∈ ecc n -> x ∈ ecc (S n).
simpl; intros.
apply G_trans with (ecc n); trivial.
 apply (ecc_grot (S n)).

 apply ecc_in2.
Qed.

Lemma ecc_incl_le x m n :
  (m <= n)%nat -> x ∈ ecc m -> x ∈ ecc n.
induction 1; intros; auto with *.
apply ecc_incl; auto.
Qed.

Lemma ecc_incl_prop : forall x, x ∈ props -> x ∈ ecc 0.
simpl; intros.
apply G_trans with props; trivial.
 apply (ecc_grot 0).

 apply (ecc_in1 0).
Qed.

Lemma ecc_prod : forall n X Y,
  ext_fun X Y ->
  X ∈ ecc n ->
  (forall x, x ∈ X -> Y x ∈ ecc n) ->
  cc_prod X Y ∈ ecc n.
intros.
apply G_cc_prod; trivial.
Qed.

Lemma ecc_prod2 : forall n X Y,
  ext_fun X Y ->
  X ∈ props ->
  (forall x, x ∈ X -> Y x ∈ ecc n) ->
  cc_prod X Y ∈ ecc n.
intros.
apply G_cc_prod; trivial.
apply G_trans with props; trivial.
apply ecc_in1.
Qed.

(* *)

Lemma empty_in_ecc n : empty ∈ ecc n.
apply G_trans with ZFcoc.props; auto.
apply ecc_in1.
Qed.

Lemma one_in_ecc n : singl empty ∈ ecc n.
apply G_trans with ZFcoc.props; auto.
apply ecc_in1.
Qed.

(* ecc 0 is the set of hereditarily finite sets, so we need to skip it. *)
Lemma omega_incl_ecc n : ZFord.omega ⊆ ecc n.
red; intros.
unfold ZFord.omega, ZFord.ord_sup in H.
rewrite sup_ax in H.
 destruct H.
 rewrite ZFrepl.uchoice_ax in H0.
  destruct H0.
  destruct H0.
  rewrite <- H2 in H1.
  apply G_trans with (ZFord.nat2ordset x1); trivial.
  elim x1; intros.
   apply G_incl with ZFcoc.props; trivial.
    apply ecc_in1.
    red; intros.
    apply empty_ax in H3; contradiction.

   apply G_subset; trivial.
   apply G_power; auto.

  (* Fch *)
  split;[|split]; intros.
 revert H2; apply ex2_morph; red; intros; auto with *.
 rewrite H1; reflexivity.

 elim H using ZFnats.N_ind; intros.
  revert H3; apply ex_morph.
  red; intros.
  apply ex2_morph; red; intros; auto with *.
  rewrite H2; reflexivity.

  exists (ZFord.nat2ordset 0); exists 0; simpl; auto with *.

  destruct H2 as (y,(m,?,?)).
  exists (ZFord.nat2ordset (S m)); exists (S m); simpl; auto with *.
  apply ZFnats.succ_morph; trivial.

 destruct H1; destruct H2.
 rewrite <- H3; rewrite <- H4; rewrite H1 in H2; apply ZFnats.nat2set_inj in H2.
 rewrite H2; reflexivity.

 (* Fm *)
do 2 red; intros.
apply ZFrepl.uchoice_morph_raw.
red; intros.
apply ex2_morph.
 red; intros.
 rewrite H1; reflexivity.

 red; intros.
 rewrite H2; reflexivity.
Qed.

Lemma omega_in_ecc n : ZFord.omega ∈ ecc (S n).
apply G_incl with (ecc n); auto.
 apply ecc_in2.

 apply omega_incl_ecc.
Qed.

Lemma N_in_ecc n : ZFnats.N ∈ ecc (S n).
apply G_N; trivial.
apply omega_in_ecc.
Qed.

Hint Resolve empty_in_ecc one_in_ecc omega_in_ecc N_in_ecc.