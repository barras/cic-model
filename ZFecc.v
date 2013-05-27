Require Import ZF ZFpairs ZFnats ZFgrothendieck.
Require Import ZFrelations ZFcoc.

(* We are in Tarski-Grothendieck set theory: *)
Axiom gr : grothendieck.

Fixpoint ecc (n:nat) : set :=
  match n with
  | 0 => grot_succ props (* grot_succ props is included in HF *)
  | S k => grot_succ (ecc k)
  end.

Lemma ecc_grot : forall n, grot_univ (ecc n).
destruct n; apply (grot_succ_typ gr).
Qed.
Hint Resolve ecc_grot.

Lemma ecc_in1 : forall n, props ∈ ecc n.
induction n; simpl; intros.
 apply (grot_succ_in gr).
 apply G_trans with (ecc n); trivial.
  apply (grot_succ_typ gr).

  apply (grot_succ_in gr).
Qed.

Lemma ecc_in2 : forall n, ecc n ∈ ecc (S n).
simpl; intros.
apply (grot_succ_in gr).
Qed.

Lemma ecc_incl : forall n x, x ∈ ecc n -> x ∈ ecc (S n).
simpl; intros.
apply G_trans with (ecc n); trivial.
 apply (grot_succ_typ gr).

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
 apply (grot_succ_typ gr).

 apply grot_succ_in.
 exact gr.
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
 apply grot_succ_in; exact gr.

 apply omega_incl_ecc.
Qed.

Lemma N_in_ecc n : ZFnats.N ∈ ecc (S n).
apply G_N; trivial.
apply omega_in_ecc.
Qed.

Hint Resolve empty_in_ecc one_in_ecc omega_in_ecc N_in_ecc.