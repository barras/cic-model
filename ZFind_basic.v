Require Import ZF ZFnats.

(***************************************************************************)
(* Elementary inductive types: *)

Definition UNIT := succ zero.
Lemma unit_typ : zero ∈ UNIT.
unfold UNIT.
apply succ_intro1.
reflexivity.
Qed.

Lemma unit_elim : forall p, p ∈ UNIT -> p == zero.
unfold UNIT; intros.
elim le_case with (1:=H); intros; trivial.
elim empty_ax with p; trivial.
Qed.

Definition BOOL := succ (succ zero).
Definition TRUE := zero.
Definition FALSE := succ zero.

Lemma true_typ : TRUE ∈ BOOL.
unfold TRUE, BOOL.
apply succ_intro2.
apply succ_intro1.
reflexivity.
Qed.

Lemma false_typ : FALSE ∈ BOOL.
unfold FALSE, BOOL.
apply succ_intro1.
reflexivity.
Qed.

Lemma bool_elim : forall b, b ∈ BOOL -> b == TRUE \/ b == FALSE.
unfold BOOL, TRUE, FALSE; intros.
elim le_case with (1:=H); intros; auto.
elim le_case with (1:=H0); intros; auto.
elim empty_ax with (1:=H1).
Qed.

Definition EQ A x y :=
  cond_set (x ∈ A /\ x == y) (singl empty).

Instance EQ_morph : Proper (eq_set ==> eq_set ==> eq_set ==> eq_set) EQ.
do 4 red; intros.
unfold EQ.
rewrite H; rewrite H0; rewrite H1; reflexivity.
Qed.

Definition REFL := empty.

Lemma refl_typ : forall A x, x ∈ A -> REFL ∈ EQ A x x.
unfold EQ, REFL; intros.
apply subset_intro; auto with *.
apply singl_intro.
Qed.

(* Rk: this property implies K (p ∈ EQ A x x -> p == REFL) *)
Lemma EQ_elim : forall A x y p,
  p ∈ EQ A x y -> x ∈ A /\ x == y /\ p == REFL.
unfold EQ; intros.
rewrite cond_set_ax in H; destruct H.
apply singl_elim in H.
destruct H0; auto.
Qed.

Lemma EQ_ind : forall A P,
  Proper (eq_set ==> eq_set ==> iff) P ->
  forall x y p, P x REFL -> p ∈ EQ A x y -> P y p.
intros.
apply EQ_elim in H1.
revert H0; apply H.
 symmetry; apply H1.
 apply H1.
Qed.
