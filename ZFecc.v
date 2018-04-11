Require Import ZF ZFpairs ZFnats ZFgrothendieck.
Require Import ZFrelations ZFcoc.

Lemma grot_succ_hf : grot_succ empty == grot_succ props.
  apply ZFrepl.uchoice_morph_raw.
  red; intros.
  unfold grot_succ_pred.
  split; intros.
   destruct H0.
   rewrite H in H0.
   split; trivial.
   destruct H1; split; intros.
    apply G_power; trivial.
    apply G_singl; trivial.
    rewrite <- H; trivial.

    rewrite <- H; apply H2; trivial.
    apply G_incl with props; trivial.
    red; intros.
    apply empty_ax in H5; contradiction.

   destruct H0.
   rewrite <- H in H0.
   split; trivial.
   destruct H1; split; intros.
    rewrite <- H in H1.
    apply G_incl with props; trivial.
    red; intros.
    apply empty_ax in H3; contradiction.

    rewrite H; apply H2; trivial.
    apply G_power; trivial.
    apply G_singl; trivial.
Qed.

(** Statement that there exists a set containing infinitely many Grothendieck universes *)

(** Actually, we should not need the existence of a set containing
    infinitely many Grothendieck universes, but only the existence of a meta-function
    ecc : nat -> set which is equivalent to introducing infinitely many symbols (one
    for each universe).
*)
Definition infinitely_many_universes := { U:set | empty ∈ U /\ forall
x, x ∈ U -> exists V, V ∈ U /\ grot_univ V /\ x ∈ V }.


(** In Tarski-Grothendieck set theory, there exists an infinite sequence of universes *)
Lemma tg_implies_ecc : grothendieck -> infinitely_many_universes.
intros gr.
exists (ZFord.TI grot_succ ZFord.omega).
split; intros.
 apply ZFord.TI_intro with (ZFord.osucc zero); auto with *.
 eapply G_incl.
  apply (grot_succ_typ gr).

  apply (grot_succ_in gr).

  red; intros.
  apply empty_ax in H; contradiction.

 apply ZFord.TI_elim in H; auto with *.
 destruct H as (o,?,?).
 assert (oo: ZFord.isOrd o) by eauto using ZFord.isOrd_inv.
 exists (grot_succ (ZFord.TI grot_succ o)).
 split;[|split]; trivial.
 2:apply (grot_succ_typ gr).
 apply ZFord.TI_intro with (ZFord.osucc o); auto with *.
 eapply G_incl.
  apply (grot_succ_typ gr).

  apply (grot_succ_in gr).

  red; intros.
  apply ZFord.TI_intro with o; auto with *.
Qed.

(*
(* We are in Tarski-Grothendieck set theory: *)
Axiom gr : grothendieck.
*)

Axiom infinite_seq_of_grot_univ : infinitely_many_universes.

Fixpoint ecc (n:nat) : set :=
  match n with
  | 0 => grot_succ props (* grot_succ props is included in HF *)
  | S k => grot_succ (ecc k)
  end.


Let prop_univ : ZFrepl.uchoice_pred (grot_succ_pred empty).
destruct (proj2_sig infinite_seq_of_grot_univ) as (mtU, nextU).
apply nextU in mtU; destruct mtU as (V,(VU,(gV,xV))).
specialize grot_succ_from_U with (1:=gV) (2:=xV); intro.
apply grot_succ_ex in H; trivial.
Qed.

Let prop_grot : grot_univ (grot_succ props).
rewrite <- grot_succ_hf.
apply grot_succ_U_typ.
apply prop_univ.
Qed.

Let prop_in : props ∈ grot_succ props.
assert (h := prop_grot).
apply G_power; trivial.
apply G_singl; trivial.
rewrite <- grot_succ_hf.
apply grot_succ_U_in.
apply prop_univ.
Qed.

Let U := proj1_sig infinite_seq_of_grot_univ.

Lemma grot_ecc_U : forall n, exists V, V ∈ U /\ grot_univ V /\ ecc n ∈ V.
destruct (proj2_sig infinite_seq_of_grot_univ) as (mtU, nextU); fold U in *.
induction n; simpl; intros.
 destruct nextU with (1:=mtU) as (V,(VU,(gV,nV))).
 destruct nextU with (1:=VU) as (V',(VU',(gV',nV'))).
 exists V'; split; trivial.
 split; trivial.
 apply G_incl with V; trivial.
 rewrite <- grot_succ_hf.
 apply grot_succ_U_lst; trivial.

 destruct IHn as (V,(VU,(gV,nV))).
 destruct nextU with (1:=VU) as (V',(VU',(gV',nV'))).
 exists V'; split; trivial.
 split; trivial.
 apply G_incl with V; trivial.
 apply grot_succ_U_lst; trivial.
Qed.

Lemma ecc_defined : forall n, ZFrepl.uchoice_pred (grot_succ_pred (ecc n)).
intros.
destruct grot_ecc_U with n as (V,(_,(gV,nV))).
specialize grot_succ_from_U with (1:=gV) (2:=nV); intro.
apply grot_succ_ex in H; trivial.
Qed.

Lemma ecc_grot : forall n, grot_univ (ecc n).
intros.
destruct n; simpl.
 apply prop_grot.

 apply grot_succ_U_typ.
 apply ecc_defined.
Qed.
Hint Resolve ecc_grot.

Lemma ecc_in2 : forall n, ecc n ∈ ecc (S n).
simpl; intros.
apply grot_succ_U_in.
apply ecc_defined.
Qed.

Lemma ecc_in1 : forall n, props ∈ ecc n.
induction n; simpl; intros.
 apply prop_in.

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