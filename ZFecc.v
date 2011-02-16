Require Import ZF ZFpairs ZFnats ZFgrothendieck.
Require Import ZFcoc.
Import IZF.

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

Lemma ecc_in1 : forall n, props \in ecc n.
induction n; simpl; intros.
 apply (grot_succ_in gr).
 apply G_trans with (ecc n); trivial.
  apply (grot_succ_typ gr).

  apply (grot_succ_in gr).
Qed.

Lemma ecc_in2 : forall n, ecc n \in ecc (S n).
simpl; intros.
apply (grot_succ_in gr).
Qed.

Lemma ecc_incl : forall n x, x \in ecc n -> x \in ecc (S n).
simpl; intros.
apply G_trans with (ecc n); trivial.
 apply (grot_succ_typ gr).

 apply ecc_in2.
Qed.

Lemma cc_prod_univ : forall X Y U,
  grot_univ U ->
  ext_fun X Y ->
  X \in U ->
  (forall x, x \in X -> Y x \in U) ->
  cc_prod X Y \in U.
intros X Y U grot_U H H0 H1.
unfold cc_prod.
assert (df_clos : dep_func X Y \in U) by (apply G_dep_func; trivial).
apply G_replf; intros; trivial.
unfold cc_lam.
apply G_union; trivial.
apply G_replf; trivial; intros.
 apply cc_lam_fun2 with (y:=fun x' => app x x').
 do 2 red; intros.
 rewrite H4; reflexivity.

 assert (app x x0 \in U).
  apply G_trans with (Y x0); auto.
  apply dep_func_elim with (1:=H2); trivial.
 apply G_replf; trivial; intros.
 apply G_couple; trivial.
  apply G_trans with X; trivial.

  apply G_trans with (app x x0); trivial.
Qed.


Lemma ecc_prod : forall n X Y,
  ext_fun X Y ->
  X \in ecc n ->
  (forall x, x \in X -> Y x \in ecc n) ->
  cc_prod X Y \in ecc n.
intros.
apply cc_prod_univ; trivial.
 apply ecc_grot.
Qed.

Lemma ecc_prod2 : forall n X Y,
  ext_fun X Y ->
  X \in props ->
  (forall x, x \in X -> Y x \in ecc n) ->
  cc_prod X Y \in ecc n.
intros.
apply cc_prod_univ; trivial.
 apply ecc_grot.

 apply G_trans with props; trivial.
  apply ecc_grot.

  apply ecc_in1.
Qed.

