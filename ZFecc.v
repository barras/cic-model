Require Import ZF ZFpairs ZFnats ZFgrothendieck.
Require Import ZFrelations ZFcoc.


(** Statement that there exists a set containing infinitely many Grothendieck universes *)

(** Actually, we should not need the existence of a set containing
    infinitely many Grothendieck universes, but only the existence of a meta-function
    ecc : nat -> set which is equivalent to introducing infinitely many symbols (one
    for each universe).
*)
Definition infinitely_many_universes :=
   { U:set | empty ∈ U /\ forall x, x ∈ U -> exists V, V ∈ U /\ grot_univ V /\ x ∈ V }.


Section S.
Import WithUChoice.
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

   destruct H0.
   rewrite <- H in H0.
   split; trivial.
   destruct H1; split; intros.
    rewrite <- H in H1.
    apply G_incl with props; trivial.

    rewrite H; apply H2; trivial.
    apply G_power; trivial.
    apply G_singl; trivial.
Qed.

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

End S.

(*
(* We are in Tarski-Grothendieck set theory: *)
Axiom gr : grothendieck.
*)

Axiom infinite_seq_of_grot_univ : infinitely_many_universes.

Definition UU := proj1_sig infinite_seq_of_grot_univ.

Definition ecc_succ X := grot_succ_ub (union UU) X.

Lemma ecc_succ_bounded X U :
  X ⊆ U ->
  grot_univ U ->
  U ∈ UU ->
  X ∈ ecc_succ X /\
  grot_univ (ecc_succ X) /\
  exists V, grot_univ V /\ ecc_succ X ⊆ V /\ V ∈ UU.
destruct (proj2_sig infinite_seq_of_grot_univ) as (u0,uS).
intros.
destruct uS with (1:=H1) as (V & ? & ? & ?).  
destruct grot_succ_ub_sound with (union UU) X as (?&?&?).
{exists V; split;[trivial|split].
  apply G_incl with U; trivial.
  red; intros; apply union_ax; exists V; trivial. }
split;[trivial|].
split;[trivial|].
exists V; split; [trivial|split;[|trivial]].
apply H7; trivial.
apply G_incl with U; trivial.
Qed.


Lemma prop_grot : grot_univ (ecc_succ empty).
apply ecc_succ_bounded with empty; auto with *.
 apply grot_empty.
 apply (proj2_sig infinite_seq_of_grot_univ).
Qed.
Hint Resolve prop_grot : core.

Lemma prop_in : props ∈ ecc_succ empty.
assert (empty ∈ ecc_succ empty).
{apply ecc_succ_bounded with empty; auto with *.
  apply grot_empty.
  apply (proj2_sig infinite_seq_of_grot_univ). }
apply G_power; trivial.
apply G_singl; trivial.
Qed.


Fixpoint ecc n :=
  match n with
  | 0 => ecc_succ empty
  | S k => ecc_succ (ecc k)
  end.

Lemma ecc_bounded n :
  grot_univ (ecc n) /\
  exists V, grot_univ V /\ ecc n ⊆ V /\ V ∈ UU.
destruct (proj2_sig infinite_seq_of_grot_univ) as (u0,uS).
induction n; simpl.
*destruct uS with (1:=u0) as (U & ? & ? & ?).
 apply ecc_succ_bounded with (U:=empty); auto with *.
 apply grot_empty.
*destruct IHn as (?,(V&?&?&?)).
 apply ecc_succ_bounded with (U:=V); auto with *.
Qed.

Lemma ecc_grot n : grot_univ (ecc n).
apply ecc_bounded.
Qed.
Hint Resolve ecc_grot : core.

Lemma ecc_in2 : forall n, ecc n ∈ ecc (S n).
simpl; intros.
destruct (ecc_bounded n) as (_,(V&?&?&?)).
apply ecc_succ_bounded with V; trivial.
Qed.

Lemma ecc_in1 : forall n, props ∈ ecc n.
induction n; simpl; intros.
 apply prop_in.

 apply G_trans with (ecc n); trivial.
  apply (ecc_grot (S n)).

  apply ecc_in2.
Qed.

(* Derived results *)
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
apply prop_in.
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

(* ecc 0 is the set of hereditarily finite sets, so it contains all finite ordinals,
   but omega is in ecc 1 *)
Lemma omega_incl_ecc : ZFord.omega ⊆ ecc_succ empty.
red; intros.
unfold ZFord.omega, ZFord.next_limOrd, ZFord.w_iter in H.
assert (aux := ZFord.w_iter_aux_m _ ZFord.osucc_morph).
rewrite sup_ax in H; [|apply ZFord.w_iter_aux_ext;apply ZFord.osucc_morph].
destruct H as (n, tyn, tyz).
apply G_trans with (2:=tyz); trivial.
clear tyz.
elim tyn using N_ind; intros.
*rewrite <- H0; auto.
*rewrite natrec_0.
 apply (empty_in_ecc 0).
*rewrite natrec_S; trivial.
 2:do 2 red; intros; apply ZFord.osucc_morph; trivial.
 apply G_subset; auto.
 apply G_power; auto.
Qed.

Lemma omega_in_ecc n : ZFord.omega ∈ ecc (S n).
apply G_incl with (ecc 0); auto.
 apply ecc_incl_le with 1; [auto with arith|].
 apply ecc_in2.

 apply omega_incl_ecc.
Qed.

Lemma N_in_ecc n : ZFnats.N ∈ ecc (S n).
apply G_N; trivial.
apply omega_in_ecc.
Qed.

Hint Resolve empty_in_ecc one_in_ecc omega_in_ecc N_in_ecc : core.
