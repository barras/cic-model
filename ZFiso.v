Require Import basic ZF ZFpairs ZFsum ZFrelations ZFcoc.
Import IZF.

Parameter iso : set -> set -> Prop.
Parameter iso_equiv : Equivalence  iso.
Existing Instance iso_equiv.
Parameter iso_morph : Proper (eq_set ==> eq_set ==> iff) iso.
Existing Instance iso_morph.

Lemma eq_iso : forall x y, x == y -> iso x y.
intros.
rewrite H; reflexivity.
Qed.

Parameter sum_iso_morph : Proper (iso ==> iso ==> iso) sum.
Parameter sum_comm_iso :
  forall X Y, iso (sum X Y) (sum Y X).
Parameter sum_assoc_iso :
  forall X Y Z, iso (sum (sum X Y) Z) (sum X (sum Y Z)).
Existing Instance sum_iso_morph.

Parameter prodcart_iso_morph : Proper (iso ==> iso ==> iso) prodcart.
Parameter prodcart_comm_iso :
  forall X Y, iso (prodcart X Y) (prodcart Y X).
Parameter prodcart_assoc_iso :
  forall X Y Z, iso (prodcart (prodcart X Y) Z) (prodcart X (prodcart Y Z)).
Existing Instance prodcart_iso_morph.


Lemma sigma_iso_morph : forall A A' B B',
  A == A' ->
  (forall x x', x \in A -> x == x' -> iso (B x) (B' x')) ->
  iso (sigma A B) (sigma A' B').
Admitted.
(*Instance sigma_iso_morph : Proper (eq_set ==> (eq_set ==> iso) ==> iso) sigma.
do 3 red; intros.
apply sigma_iso_morph'; auto with *.
Qed.
*)

Parameter cc_prod_iso_morph : Proper (eq_set ==> (eq_set ==> iso) ==> iso) cc_prod.
Existing Instance cc_prod_iso_morph.


Parameter sigma_iso_1_l : forall x F,
  iso (sigma (singl x) F) (F x).

Parameter sigma_iso_1_r : forall A B,
  (forall x, x \in A -> iso (B x) (singl empty)) ->
  iso (sigma A B) A.

Parameter cc_prod_0_l : forall F,
  iso (cc_prod empty F) (singl empty).

Parameter cc_prod_1_l : forall x F,
  iso (cc_prod (singl x) F) (F x).

Lemma iso_sum_sigma : forall A1 A2 B1 B2,
  iso (sum (sigma A1 B1) (sigma A2 B2))
    (sigma (sum A1 A2) (sum_case B1 B2)).
Admitted.
Lemma iso_prodcart_sigma : forall A1 A2 B1 B2,
  iso (prodcart (sigma A1 B1) (sigma A2 B2))
    (sigma (prodcart A1 A2)
      (fun p => prodcart (B1 (fst p)) (B2 (snd p)))).
Admitted.
Lemma iso_prodcart_cc_prod : forall A1 A2 F,
  iso (prodcart (cc_prod A1 F) (cc_prod A2 F))
    (cc_prod (sum A1 A2) F).
Admitted.

Lemma iso_sigma_sigma : forall A B C,
  iso (sigma A (fun x => sigma (B x) (fun y => C x y)))
    (sigma (sigma A B) (fun p => C (fst p) (snd p))).
Admitted.
Lemma iso_cc_prod_sigma : forall A B C,
  iso (cc_prod A (fun x => sigma (B x) (fun y => C x y)))
    (sigma (cc_prod A B) (fun f => cc_prod A (fun x => C x (cc_app f x)))). 
Admitted.

Lemma cc_prod_curry : forall A B C,
  iso (cc_prod A (fun x => cc_prod (B x) (fun y => C x y)))
    (cc_prod (sigma A B) (fun p => C (fst p) (snd p))).
Admitted.
