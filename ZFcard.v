Require Import ZF.
Import IZF.

(* Cardinal ordering *)

Definition le_card (x y:set) : Prop :=
  exists2 R : set -> set -> Prop,
    (forall x', x' \in x -> exists2 y', y' \in y & R x' y') &
    (forall x1 y1 x2 y2, x1 \in x -> x2 \in x -> y1 \in y -> y2 \in y ->
     R x1 y1 -> R x2 y2 -> y1 == y2 -> x1 == x2).

Instance le_card_morph : Proper (eq_set ==> eq_set ==> iff) le_card.
split; destruct 1.
 exists x1; intros.
  rewrite <- H in H3.
  elim H1 with x'; intros; trivial.
  exists x2; trivial.
  rewrite <- H0; trivial.

  rewrite <- H in H3,H4|-.
  rewrite <- H0 in H5,H6|-.
  eauto.

 exists x1; intros.
  rewrite H in H3.
  elim H1 with x'; intros; trivial.
  exists x2; trivial.
  rewrite H0; trivial.

  rewrite H in H3,H4|-.
  rewrite H0 in H5,H6|-.
  eauto.
Qed.

Instance le_card_refl : Reflexive le_card.
exists (fun x' y' => x' == y').
 intros.
 exists x'; trivial; reflexivity.

 intros.
 rewrite H3; rewrite H4; trivial.
Qed.

Instance le_card_trans : Transitive le_card.
red.
destruct 1 as (R,incl,inj);
destruct 1 as (R',incl',inj').
exists (fun x' z' => exists2 y', y' \in y & R x' y' /\ R' y' z'); intros.
 elim incl with x'; trivial; intros.
 elim incl' with x0; trivial; intros.
 exists x1; trivial.
 exists x0; auto.

 destruct H3 as (y1',in1,(r1,r1'));
   destruct H4 as (y2',in2,(r2,r2')).
 eauto.
Qed.

Definition lt_card x y :=
  ~ le_card y x.

Lemma incl_le_card : forall x y, x \incl y -> le_card x y.
intros.
exists (fun x y => x == y); intros.
 exists x'; auto.
 reflexivity.

 rewrite H4; rewrite H5; trivial.
Qed.

Lemma cantor_le : forall x, lt_card x (power x).
red; red; intros.
destruct H as (R,incl,Rfun).
pose (D := subset x (fun x' => forall x'' z, z \in power x ->
             x'' == x' -> R z x'' -> ~ x'' \in z)).
assert (D \in power x).
 apply power_intro; intros.
 unfold D in H.
 apply subset_elim1 with (1:=H).
elim incl with D; trivial; intros d in_d rel_d.
assert (~ d \in D).
 red; intros.
 unfold D in H0.
 elim subset_elim2 with (1:=H0); intros.
 apply H2 with d D; trivial.
apply H0.
unfold D; apply subset_intro; trivial.
intros.
rewrite H2.
assert (z == D).
 apply Rfun with x'' d; auto.
 rewrite H2; trivial.
rewrite H4; trivial.
Qed.

Lemma discr_power : forall x, ~ x == power x.
red; intros.
apply cantor_le with x.
rewrite <- H.
reflexivity.
Qed.

(* Same cardinality *)

Definition equi_card (x y:set) : Prop :=
  exists2 R : set -> set -> Prop,
    (forall x', x' \in x -> exists2 y', y' \in y & R x' y') /\
    (forall y', y' \in y -> exists2 x', x' \in x & R x' y') &
    (forall x1 y1 x2 y2, x1 \in x -> x2 \in x -> y1 \in y -> y2 \in y ->
     R x1 y1 -> R x2 y2 -> (x1 == x2 <-> y1 == y2)).

Instance equi_card_morph : Proper (eq_set ==> eq_set ==> iff) equi_card.
unfold equi_card; split; destruct 1.
 destruct H1.
 exists x1; intros.
  split; intros.
   rewrite <- H in H4.
   destruct (H1 x'); trivial.
   rewrite H0 in H5.
   exists x2; trivial.

   rewrite <- H0 in H4.
   destruct (H3 y'); trivial.
   rewrite H in H5.
   exists x2; trivial.

 rewrite <- H in H4,H5.
 rewrite <- H0 in H6,H7.
 auto.

 destruct H1.
 exists x1; intros.
  split; intros.
   rewrite H in H4.
   destruct (H1 x'); trivial.
   rewrite <- H0 in H5.
   exists x2; trivial.

   rewrite H0 in H4.
   destruct (H3 y'); trivial.
   rewrite <- H in H5.
   exists x2; trivial.

 rewrite H in H4,H5.
 rewrite H0 in H6,H7.
 auto.
Qed.

Instance equi_card_refl : Reflexive equi_card.
exists (fun x' y' => x' == y').
 split; intros.
  exists x'; trivial; reflexivity.
  exists y'; trivial; reflexivity.
 intros.
 rewrite H3; rewrite H4; reflexivity.
Qed.

Instance equi_card_sym : Symmetric equi_card.
red; destruct 1 as (R,(incl1,incl2),bij).
exists (fun x' y' => R y' x'); intros; auto.
symmetry; auto.
Qed.

Instance equi_card_trans : Transitive equi_card.
red.
destruct 1 as (R,(incl1,incl2),bij);
destruct 1 as (R',(incl1',incl2'),bij').
exists (fun x' z' => exists2 y', y' \in y & R x' y' /\ R' y' z').
 split; intros.
  elim incl1 with x'; trivial; intros.
  elim incl1' with x0; trivial; intros.
  exists x1; trivial.
  exists x0; auto.

  elim incl2' with y'; trivial; intros.
  elim incl2 with x0; trivial; intros.
  exists x1; trivial.
  exists x0; auto.

 intros.
 destruct H3 as (y1',in1,(r1,r1'));
   destruct H4 as (y2',in2,(r2,r2')).
 transitivity (y1' == y2'); auto.
Qed.

Lemma equi_card_le : forall x y, equi_card x y -> le_card x y.
destruct 1 as (R,(incl1,incl2),bij).
exists R; auto.
intros.
refine (proj2 (bij _ _ _ _ _ _ _ _ H3 H4) H5); trivial.
Qed.

Lemma cantor : forall x, ~ equi_card x (power x).
red; intros; apply (cantor_le x);
apply equi_card_le; apply equi_card_sym; trivial.
Qed.

(* Strict ordering *)

Require Import ZFnats ZFord.

Definition isCard x :=
  isOrd x /\ (forall y, lt y x -> lt_card y x).


Definition regular_card o :=
  forall x F,
  lt_card x o ->
  ext_fun x F ->
  (forall y, y \in x -> lt_card (F y) o) ->
  lt_card (sup x F) o.

Definition regular o := forall x F,
  lt_card x o ->
  ext_fun x F ->
  (forall y, y \in x -> lt (F y) o) ->
  lt (sup x F) o.


Section RegularRelational.
Import ZFrepl.

Definition regular_rel o := forall x R,
  lt_card x o ->
  repl_rel x R ->
  (forall y z, y \in x -> R y z -> lt z o) ->
  lt (union (repl x R)) o.

Lemma regular_weaker : forall o,
  regular_rel o -> regular o.
red; intros.
change (sup x F) with (union (repl x (fun x y => y == F x))).
apply H; intros; auto.
 apply repl_rel_fun; trivial.

 rewrite H4; auto.
Qed.

End RegularRelational.

(* regular' -> regular ?
   (not converse: w+w is regular but nor regular') *)
Definition regular' o := forall x F,
  lt x o ->
  ext_fun x F ->
  (forall y, y \in x -> lt (F y) o) ->
  lt (sup x F) o.

Definition stronglyInaccessibleCard o :=
  limitOrd o /\ regular o.
(* limitOrd or limit *cardinal* ? *)


(* any functional relation from a to b cannot be surjective *)
Definition lt_card2 a b :=
  forall R:set->set->Prop,
  (forall x x' y y', x \in a -> y \in b -> y' \in b ->
   R x y -> R x' y' -> x==x' -> y==y') ->
  exists2 y, y \in b & forall x, x \in a -> ~ R x y.

Lemma lt_card_weaker : forall a b,
  lt_card2 a b -> lt_card a b.
red; red; intros.
destruct H0 as (R,?,?).
destruct (H (fun x y => R y x)).
 intros.
 apply H1 with x x'; trivial.
 rewrite <- H7; trivial.

 destruct H0 with x; trivial.
 eapply H3; eauto.
Qed.  