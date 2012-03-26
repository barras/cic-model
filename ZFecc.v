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

Lemma ecc_prod : forall n X Y,
  ext_fun X Y ->
  X ∈ ecc n ->
  (forall x, x ∈ X -> Y x ∈ ecc n) ->
  cc_prod X Y ∈ ecc n.
intros.
apply G_cc_prod; trivial.
apply ecc_grot.
Qed.

Lemma ecc_prod2 : forall n X Y,
  ext_fun X Y ->
  X ∈ props ->
  (forall x, x ∈ X -> Y x ∈ ecc n) ->
  cc_prod X Y ∈ ecc n.
intros.
apply G_cc_prod; trivial.
 apply ecc_grot.

 apply G_trans with props; trivial.
  apply ecc_grot.

  apply ecc_in1.
Qed.

