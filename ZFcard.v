Require Import ZF.

(* Cardinal ordering *)

Definition le_card (x y:set) : Prop :=
  exists2 R : set -> set -> Prop,
    Proper (eq_set ==> eq_set ==> iff) R &
    (forall x', x' \in x -> exists2 y', y' \in y & R x' y') /\
    (forall x1 y1 x2 y2, x1 \in x -> x2 \in x -> y1 \in y -> y2 \in y ->
     R x1 y1 -> R x2 y2 -> y1 == y2 -> x1 == x2).

Instance le_card_morph : Proper (eq_set ==> eq_set ==> iff) le_card.
split; destruct 1.
 destruct H2.
 exists x1; trivial; split; intros.
  rewrite <- H in H4.
  elim H2 with x'; intros; trivial.
  exists x2; trivial.
  rewrite <- H0; trivial.

  rewrite <- H in H4,H5|-.
  rewrite <- H0 in H6,H7|-.
  eauto.

 destruct H2.
 exists x1; trivial; split; intros.
  rewrite H in H4.
  elim H2 with x'; intros; trivial.
  exists x2; trivial.
  rewrite H0; trivial.

  rewrite H in H4,H5|-.
  rewrite H0 in H6,H7|-.
  eauto.
Qed.

Instance le_card_refl : Reflexive le_card.
exists (fun x' y' => x' == y').
 do 3 red; intros.
 rewrite H; rewrite H0; reflexivity.

 split; intros.
  exists x'; trivial; reflexivity.

  rewrite H3; rewrite H4; trivial.
Qed.

Instance le_card_trans : Transitive le_card.
red.
destruct 1 as (R,Rm,(incl,inj));
destruct 1 as (R',R'm,(incl',inj')).
exists (fun x' z' => exists2 y', y' \in y & R x' y' /\ R' y' z'); [|split;intros].
 do 3 red; intros.
 apply ex2_morph.
  red; reflexivity.

  red; intros.
  rewrite H; rewrite H0; reflexivity.

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
exists (fun x y => x == y); [|split;intros].
 do 3 red; intros.
 rewrite H0; rewrite H1; reflexivity.

 exists x'; auto.
 reflexivity.

 rewrite H4; rewrite H5; trivial.
Qed.

Lemma cantor_le : forall x, lt_card x (power x).
red; red; intros.
destruct H as (R,Rm,(incl,Rfun)).
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
    Proper (eq_set ==> eq_set ==> iff) R &
    (forall x', x' \in x -> exists2 y', y' \in y & R x' y') /\
    (forall y', y' \in y -> exists2 x', x' \in x & R x' y') /\
    (forall x1 y1 x2 y2, x1 \in x -> x2 \in x -> y1 \in y -> y2 \in y ->
     R x1 y1 -> R x2 y2 -> (x1 == x2 <-> y1 == y2)).

Instance equi_card_morph : Proper (eq_set ==> eq_set ==> iff) equi_card.
apply morph_impl_iff2; auto with *.
unfold equi_card; do 4 red; intros.
destruct H1 as (R,Rm,(incl1,(incl2,bij))).
exists R; [trivial|split;[|split]]; intros.
 rewrite <- H in H1.
 destruct (incl1 x'); trivial.
 rewrite H0 in H2.
 exists x1; trivial.

 rewrite <- H0 in H1.
 destruct (incl2 y'); trivial.
 rewrite H in H2.
 exists x1; trivial.

 rewrite <- H in H1,H2.
 rewrite <- H0 in H3,H4.
 auto.
Qed.

Instance equi_card_refl : Reflexive equi_card.
exists (fun x' y' => x' == y').
 do 3 red; intros.
 rewrite H; rewrite H0; reflexivity.

 split; [|split]; intros.
  exists x'; trivial; reflexivity.
  exists y'; trivial; reflexivity.
  rewrite H3; rewrite H4; reflexivity.
Qed.

Instance equi_card_sym : Symmetric equi_card.
red; destruct 1 as (R,Rm,(incl1,(incl2,bij))).
exists (fun x' y' => R y' x'); intros; auto.
 do 3 red; intros; apply Rm; trivial.

 split;[|split]; trivial.
 symmetry; auto.
Qed.

Instance equi_card_trans : Transitive equi_card.
red.
destruct 1 as (R,Rm,(incl1,(incl2,bij)));
destruct 1 as (R',R'm,(incl1',(incl2',bij'))).
exists (fun x' z' => exists2 y', y' \in y & R x' y' /\ R' y' z').
 do 3 red; intros.
 apply ex2_morph.
  red; reflexivity.

  red; intros.
  rewrite H; rewrite H0; reflexivity.

 split; [|split]; intros.
  elim incl1 with x'; trivial; intros.
  elim incl1' with x0; trivial; intros.
  exists x1; trivial.
  exists x0; auto.

  elim incl2' with y'; trivial; intros.
  elim incl2 with x0; trivial; intros.
  exists x1; trivial.
  exists x0; auto.

  destruct H3 as (y1',in1,(r1,r1'));
    destruct H4 as (y2',in2,(r2,r2')).
  transitivity (y1' == y2'); auto.
Qed.

Lemma equi_card_le : forall x y, equi_card x y -> le_card x y.
destruct 1 as (R,Rm,(incl1,(incl2,bij))).
exists R; [trivial|split;intros;auto].
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
destruct H0 as (R,?,(?,?)).
destruct (H (fun x y => R y x)).
 intros.
 apply H2 with x x'; trivial.
 rewrite <- H8; trivial.

 destruct H1 with x; trivial.
 eapply H4; eauto.
Qed.  


(* Hartog numbers *)

Require Import ZFrelations.

Require Import Relations.

(*

Section Inverse_Image.

  Variables (A B : Type) (R : B -> B -> Prop) (f : A -> B).

  Definition Rof (x y : A) : Prop := R (f x) (f y).

  Remark ACC_lemma :
   forall y : B, Acc R y -> forall x : A, y = f x -> Acc Rof x.
    simple induction 1; intros.
    constructor; intros.
    apply (H1 (f y0)); trivial.
    elim H2 using eq_ind_r; trivial.
    Qed.

  Lemma ACC_inverse_image : forall x : A, Acc R (f x) -> Acc Rof x.
    intros; apply (ACC_lemma (f x)); trivial.
    Qed.

  Lemma WF_inverse_image : well_founded R -> well_founded Rof.
    red in |- *; intros; apply ACC_inverse_image; auto.
    Qed.

End Inverse_Image.

Section Burali_Forti_Paradox.

  Definition morphism (A : Type) (R : A -> A -> Prop) 
    (B : Type) (S : B -> B -> Prop) (f : A -> B) :=
    forall x y : A, R x y -> S (f x) (f y).

  (* The hypothesis of the paradox:
     assumes there exists an universal system of notations, i.e:
      - A type A0
      - An injection i0 from relations on any type into A0
      - The proof that i0 is injective modulo morphism 
   *)
  Variable A0 : Type.                     (* Type_i *)
  Variable i0 : forall X : Type, (X -> X -> Prop) -> A0. (* X: Type_j *)
  Hypothesis
    inj :
      forall (X1 : Type) (R1 : X1 -> X1 -> Prop) (X2 : Type)
        (R2 : X2 -> X2 -> Prop),
      i0 X1 R1 = i0 X2 R2 -> exists f : X1 -> X2, morphism X1 R1 X2 R2 f.

  (* Embedding of x in y: x and y are images of 2 well founded relations
     R1 and R2, the ordinal of R2 being strictly greater than that of R1.
   *)
  Record emb (x y : A0) : Prop := 
    {X1 : Type;
     R1 : X1 -> X1 -> Prop;
     eqx : x = i0 X1 R1;
     X2 : Type;
     R2 : X2 -> X2 -> Prop;
     eqy : y = i0 X2 R2;
     W2 : well_founded R2;
     f : X1 -> X2;
     fmorph : morphism X1 R1 X2 R2 f;
     maj : X2;
     majf : forall z : X1, R2 (f z) maj}.


  Lemma emb_trans : forall x y z : A0, emb x y -> emb y z -> emb x z.
intros.
case H; intros.
case H0; intros.
generalize eqx0; clear eqx0.
elim eqy using eq_ind_r; intro.
case (inj _ _ _ _ eqx0); intros.
exists X1 R1 X3 R3 (fun x : X1 => f0 (x0 (f x))) maj0; trivial.
red in |- *; auto.
Defined.


  Lemma ACC_emb :
   forall (X : Type) (R : X -> X -> Prop) (x : X),
   Acc R x ->
   forall (Y : Type) (S : Y -> Y -> Prop) (f : Y -> X),
   morphism Y S X R f -> (forall y : Y, R (f y) x) -> Acc emb (i0 Y S).
simple induction 1; intros.
constructor; intros.
destruct H4.
rewrite eqx.
destruct (inj X2 R2 Y S).
 symmetry; trivial.

apply H1 with (y := f (x1 maj)) (f := fun x : X1 => f (x1 (f0 x)));
 try red in |- *; auto.
Defined.

  (* The embedding relation is well founded *)
  Lemma WF_emb : well_founded emb.
constructor; intros.
destruct H.
rewrite eqx.
apply ACC_emb with (X := X2) (R := R2) (x := maj) (f := f); trivial.
Defined.


  (* The following definition enforces Type_j >= Type_i *)
  Definition Omega : A0 := i0 A0 emb.


Section Subsets.

  Variable a : A0.

  (* We define the type of elements of A0 smaller than a w.r.t embedding.
     The Record is in Type, but it is possible to avoid such structure. *)
  Record sub : Type :=  {witness : A0; emb_wit : emb witness a}.

  (* F is its image through i0 *)
  Definition F : A0 := i0 sub (Rof _ _ emb witness).

  (* F is embedded in Omega:
     - the witness projection is a morphism
     - a is an upper bound because emb_wit proves that witness is
       smaller than a.
   *)
  Lemma F_emb_Omega : emb F Omega.
exists sub (Rof _ _ emb witness) A0 emb witness a; trivial.
exact WF_emb.

red in |- *; trivial.

exact emb_wit.
Defined.

End Subsets.


  Definition fsub (a b : A0) (H : emb a b) (x : sub a) : 
    sub b := Build_sub _ (witness _ x) (emb_trans _ _ _ (emb_wit _ x) H).

  (* F is a morphism: a < b => F(a) < F(b)
      - the morphism from F(a) to F(b) is fsub above
      - the upper bound is a, which is in F(b) since a < b
   *)
  Lemma F_morphism : morphism A0 emb A0 emb F.
red in |- *; intros.
exists
 (sub x)
   (Rof _ _ emb (witness x))
   (sub y)
   (Rof _ _ emb (witness y))
   (fsub x y H)
   (Build_sub _ x H); trivial.
apply WF_inverse_image.
exact WF_emb.

unfold morphism, Rof, fsub in |- *; simpl in |- *; intros.
trivial.

unfold Rof, fsub in |- *; simpl in |- *; intros.
apply emb_wit.
Defined.


  (* Omega is embedded in itself:
     - F is a morphism
     - Omega is an upper bound of the image of F
   *)
  Lemma Omega_refl : emb Omega Omega.
exists A0 emb A0 emb F Omega; trivial.
exact WF_emb.

exact F_morphism.

exact F_emb_Omega.
Defined.

  (* The paradox is that Omega cannot be embedded in itself, since
     the embedding relation is well founded.
   *)
  Theorem Burali_Forti : False.
assert (forall x, Acc emb x -> x <> Omega).
 induction 1.
 red; intros.
 rewrite H1 in H0.
 apply (H0 Omega); trivial.
 apply Omega_refl.
apply (H Omega); trivial.
apply WF_emb.
Defined.

End Burali_Forti_Paradox.

Section S.

  Variable X:set.

  Definition A0 : Type := { x:set | x \in X}.

  Definition  i0 : forall X : Type, (X -> X -> Prop) -> A0),
       (forall (X1 : Type) (R1 : X1 -> X1 -> Prop) 
          (X2 : Type) (R2 : X2 -> X2 -> Prop),
        i0 X1 R1 = i0 X2 R2 -> exists f : X1 -> X2, morphism X1 R1 X2 R2 f) ->
       False

*)
(******************************************************)

Section Hartog.

Variable X:set.
Set Implciit Arguments.

  Record REL A0 : Type := {
    Rel :> A0 -> A0 -> Prop;
    dom : A0 -> Prop;
    wfrel : well_founded Rel
  }.

  Definition morphism A0 (R S : REL A0) (f : A0 -> A0) :=
    (forall x y, dom _ R x -> dom _ R y -> R x y -> S (f x) (f y)) /\
    (forall x, dom _ R x -> dom _ S (f x)).

  Record emb A0 (R1 R2 : REL A0) : Prop := {
     f : A0 -> A0;
     fmorph : morphism _ R1 R2 f;
     maj : A0;
     majd : dom _ R2 maj;
     majf : forall z, dom _ R1 z -> R2 (f z) maj}.

  Parameter WF_emb : forall A0, well_founded (emb A0).

  Definition emb0 A0 i0 (x y:A0) :=
    exists2 R1, x = i0 R1 & exists2 R2, y = i0 R2 & emb A0 R1 R2.

  Parameter WF_emb0 : forall A0 i0, well_founded (emb0 A0 i0).

  Definition Emb A0 i0 (P:A0->Prop) : REL A0 :=
     Build_REL _ (emb0 A0 i0) P (WF_emb0 A0 i0).

Parameter Burali_Forti
     : forall (A0 : Type) (i0 : REL A0 -> A0),
       (forall R1 R2 : REL A0,
        i0 R1 = i0 R2 -> exists f : A0 -> A0, morphism A0 R1 R2 f) -> False.

(*
Record iso_rel R o f := {
  rel_ord : isOrd o;
  fun_ty : forall x, f x \in o;
  surj : forall y, y \in o -> exists x, f x == y;
  equiv : forall x y, rel_app R x y <-> f x \in f y
}.

Definition wo := subset (ZFrelations.rel X X)
  (fun R => exists o, exists2 f, ext_fun X f & iso_rel R o f).

Definition hartog := repl wo (fun R => uchoice (fun o => exists2 f, ext_fun X f & iso_rel R o f)).

Hypothesis inj : set -> set.
Hypothesis is_inj : forall o, o \in hartog


Require Import Plump.

Definition isWellOrder R := forall x, isWO set (rel_app R) x.

Instance isWo_morph : Proper (eq_set==>iff) isWellOrder.
Admitted.

Instance R_app_morph : forall R, Proper (eq_set ==> eq_set ==> iff) (rel_app R).
do 3 red; intros.
rewrite H; rewrite H0; reflexivity.
Qed.

Definition order_type_assign_rel R a o :=
  forall P,
  Proper (eq_set ==> eq_set ==> iff) P ->
  (forall x f,
   let x' := subset X (fun y => rel_app R y x) in
   ext_fun x' f ->
   (forall y, rel_app R y x -> P y (f y)) ->
   P x (replf x' f)) ->
  P a o.

Instance order_type_assign_ext :
  Proper (eq_set==>eq_set==>eq_set==>iff) order_type_assign_rel.
Admitted.


Lemma order_type_assign_rel_inv : forall r a x,
  order_type_assign_rel r a x ->
  exists2 f,
    forall b, rel_app r b a -> order_type_assign_rel r b (f b) &
    let a' := subset X (fun b => rel_app r b a) in
    ext_fun a' f /\ x == replf a' f.
intros.
apply H; intros.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 destruct H2.
 exists x2; intros.
  rewrite <- H0 in H4; auto.

  destruct H3; split.
   do 2 red; intros; apply H3; auto.
   apply subset_intro.
    apply subset_elim1 in H5; trivial.

    apply subset_elim2 in H5; destruct H5.
    rewrite H5; rewrite H0; trivial.

   rewrite<- H1; rewrite H4.
   apply replf_morph; trivial.
   apply subset_morph; auto with *.
   red; intros.
   rewrite H0; auto with *.

 exists f; intros.
 2:split; [trivial|reflexivity].
 red; intros.
 destruct H1 with b; trivial.
 destruct H6.
 rewrite H7.
 apply H4; intros; trivial.
 apply H5; trivial.
Qed.

Require Import ZFrepl.

Lemma order_type_assign_uchoice : forall R a,
  isWellOrder R ->
  uchoice_pred (order_type_assign_rel R a).
intros.
red in H.
apply isWO_ind with (E:=eq_set) (4:=H a); intros; auto with *.
split;[|split]; intros.
 rewrite <- H3; trivial.

 exists (replf (subset X (fun z => rel_app R z y))
            (fun z => uchoice (order_type_assign_rel R z))).
 red; intros.
 apply H4; intros.
  do 2 red; intros.
  apply uchoice_morph_raw.
  red; intros.
  rewrite H6; rewrite H7; reflexivity.

  apply (uchoice_def _ (H2 _ H5)); trivial.

 clear a H1.
 revert x' H2 H4.
 apply H3; intros.
  apply morph_impl_iff2; auto with *.
  do 4 red; intros.
  rewrite <- H2; apply H4; intros.
   apply H5.
   rewrite <- H1; trivial.

   rewrite H1; trivial.

  clear x H3.
  destruct order_type_assign_rel_inv with (1:=H5) as (f',?,(_,?)).
  rewrite H6.
  apply replf_morph.
   apply subset_morph; auto with *.

   red; intros.
   apply H2; intros; auto.
    apply subset_elim2 in H7; destruct H7.
    rewrite H7; trivial.

    apply H4.
    eapply isWO_trans with eq_set x; auto with *.
    apply subset_elim2 in H7; destruct H7.
    rewrite H7; trivial.

    rewrite H8.
    apply H3.
    rewrite <- H8.
    apply subset_elim2 in H7; destruct H7.
    rewrite H7; trivial.
Qed.

Lemma order_type_assign_ord : forall R a o,
  isWO set (rel_app R) a ->
  order_type_assign_rel R a o ->
  isOrd o.
intros.
revert o H0.
apply isWO_ind with (E:=eq_set) (4:=H); intros; auto with *.
apply isOrd_intro; intros.
apply order_type_assign_rel_inv in H3; trivial.
destruct H3 as (f,?,(?,?)).
rewrite H8 in H6|-*; clear o H8.
 apply replf_elim in H6; trivial; destruct H6.
 rewrite H8 in H5; clear b H8.
 rewrite subset_ax in H6.
 destruct H6 as (?,(x',?,?)).
 rewrite <- H8 in H9; clear x' H8.
 assert (exists2 w, I set (rel_app R) w x & a0 == f w).
  exists (subset X (fun x'
  exists (subset X (fun x' => rel_app R x' x /\ exists2 w, w \in a0 & order_type_assign_rel R x' w)).
   red; intros.
   apply isWO_plump with
   

  admit.
 destruct H8 as (w,?,?).
 assert (rel_app R w y).
  apply isWO_plump with eq_set x; auto with *.
  admit. (* w isWO *)
 apply replf_intro with w; auto.
 apply subset_intro; trivial.
 admit. (* w in X *)




  apply H3 in H11.

 exists 


 = 

red in H.
pattern a, o; apply H.
 do 3 red; intros.
 rewrite H1; reflexivity.

 intros.
 apply isOrd_intro; intros.
 apply replf_elim in H4; trivial.
 destruct H4.

 apply isOrd_supf; intros.
  do 2 red; intros.
  apply osucc_morph; apply H0; trivial.

  apply subset_elim2 in H2; destruct H2.
  rewrite <- H2 in H3; auto.
Qed. 

*)


Definition order_type_assign_rel R a o :=
  forall P,
  Proper (eq_set ==> eq_set ==> iff) P ->
  (forall x f,
   let x' := subset X (fun y => rel_app R y x) in
   ext_fun x' f ->
   (forall y, rel_app R y x -> P y (f y)) ->
   P x (osup x' (fun y => osucc (f y)))) ->
  P a o.

Instance order_type_assign_ext :
  Proper (eq_set==>eq_set==>eq_set==>iff) order_type_assign_rel.
Admitted.

Lemma order_type_assign_rel_inv : forall r a x,
  order_type_assign_rel r a x ->
  exists2 f,
    forall b, rel_app r b a -> order_type_assign_rel r b (f b) &
    let a' := subset X (fun b => rel_app r b a) in
    ext_fun a' f /\ x == osup a' (fun y => osucc (f y)).
intros.
apply H; intros.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 destruct H2.
 exists x2; intros.
  rewrite <- H0 in H4; auto.

  destruct H3; split.
   do 2 red; intros; apply H3; auto.
   apply subset_intro.
    apply subset_elim1 in H5; trivial.

    apply subset_elim2 in H5; destruct H5.
    rewrite H5; rewrite H0; trivial.

   rewrite<- H1; rewrite H4.
   apply osup_morph; auto.
    apply subset_morph; auto with *.
    red; intros.
    rewrite H0; auto with *.

    red; intros.
    apply osucc_morph.
    apply H3; trivial.

 exists f; intros.
 2:split; [trivial|reflexivity].
 red; intros.
 destruct H1 with b; trivial.
 destruct H6.
 rewrite H7.
 apply H4; intros; trivial.
 apply H5; trivial.
Qed.

Require Import ZFrepl.

Require Import Relations.

Definition isWellOrder R :=
  forall x, Acc (rel_app R) x.

Instance isWO_m : Proper (eq_set ==> iff) isWellOrder.
Admitted.

Lemma order_type_assign_uchoice : forall R a,
  isWellOrder R ->
  uchoice_pred (order_type_assign_rel R a).
intros.
elim (H a); intros.
split;[|split]; intros.
 rewrite <- H2; trivial.

 exists (osup (subset X (fun z => rel_app R z x))
            (fun z => osucc (uchoice (order_type_assign_rel R z)))).
 red; intros.
 apply H3; intros.
  do 2 red; intros.
  apply uchoice_morph_raw.
  red; intros.
  rewrite H5; rewrite H6; reflexivity.

  apply (uchoice_def _ (H1 _ H4)); trivial.

 clear a.
 revert x' H1 H3.
 apply H2; intros.
  apply morph_impl_iff2; auto with *.
  do 4 red; intros.
  rewrite <- H3; apply H4; intros.
   apply H5.
   rewrite <- H1; trivial.

   rewrite H1; trivial.

  destruct order_type_assign_rel_inv with (1:=H5) as (f',?,(_,?)).
  rewrite H7.
  apply osup_morph.
   apply subset_morph; auto with *.

   red; intros.
   apply osucc_morph.
   apply H3; intros; auto.
    apply subset_elim2 in H8; destruct H8.
    rewrite H8; trivial.

    apply H4.
    admit. (* R trans... *)
(*    eapply isWO_trans with eq_set x; auto with *.
    apply subset_elim2 in H7; destruct H7.
    rewrite H7; trivial.
*)
    rewrite H9.
    apply H6.
    rewrite <- H9.
    apply subset_elim2 in H8; destruct H8.
    rewrite H8; trivial.
Qed.

Lemma order_type_assign_rel_inv' : forall r a,
  isWellOrder r ->
  uchoice (order_type_assign_rel r a) ==
  osup (subset X (fun b => rel_app r b a))
    (fun b => osucc (uchoice (order_type_assign_rel r b))).
intros.
generalize (uchoice_def _ (order_type_assign_uchoice _ a H)); intro.
apply order_type_assign_rel_inv in H0; destruct H0.
destruct H1.
rewrite H2.
apply osup_morph; auto with *.
red; intros.
apply osucc_morph.
rewrite (H1 x0 x'); trivial.
rewrite H4 in H3; clear x0 H4.
apply subset_elim2 in H3; destruct H3.
rewrite <- H3 in H4 ;clear x0 H3.
apply H0 in H4.
apply uchoice_ext; trivial.
apply order_type_assign_uchoice; trivial.
Qed.

Lemma order_type_assign_ord : forall R a o,
  order_type_assign_rel R a o ->
  isOrd o.
intros.
red in H.
pattern a, o; apply H.
 do 3 red; intros.
 rewrite H1; reflexivity.

 intros.
 apply isOrd_osup; intros.
  do 2 red; intros.
  apply osucc_morph; apply H0; trivial.

  apply subset_elim2 in H2; destruct H2.
  rewrite <- H2 in H3; auto.
Qed. 

Definition order_type R :=
  osup X (fun a => osucc (uchoice (order_type_assign_rel R a))).

Lemma ot_ext : forall x x',
  x == x' ->
  eq_fun X
    (fun a => osucc (uchoice (order_type_assign_rel x a)))
    (fun a => osucc (uchoice (order_type_assign_rel x' a))).
red; intros.
apply osucc_morph.
apply uchoice_morph_raw.
apply order_type_assign_ext; auto with *.
Qed.

Instance order_type_ext : morph1 order_type.
unfold order_type.
do 2 red; intros.
apply osup_morph; auto with *.
apply ot_ext; trivial.
Qed.

Definition wo := subset (rel X X) isWellOrder.

Lemma wo_def2 : forall r, r \in wo -> isWellOrder r.
intros.
apply subset_elim2 in H; destruct H.
rewrite H; trivial.
Qed.
Hint Resolve wo_def2.


(*
Lemma order_type_assign_rel_inv2 : forall r a x y,
  isWellOrder r ->
  a \in X ->
  order_type_assign_rel r a x ->
  y \in x ->
  exists2 b, rel_app r b a & order_type_assign_rel r b y.
intros.
destruct order_type_assign_rel_inv with (1:=H1) as (f,fsub,(extf,eqx)).
rewrite eqx in H2.
rewrite sup_ax in H2; trivial.
destruct H2.
exists x0.
 apply subset_elim2 in H2; destruct H2.
 rewrite H2; trivial.
Admitted.
*)

Definition hartog_succ :=
  osup wo order_type.

Lemma isOrd_hartog : isOrd hartog_succ.
unfold hartog_succ.
apply isOrd_osup.
 do 2 red; intros.
 rewrite H0; reflexivity.

 intros.
 unfold order_type.
 apply isOrd_osup.
  red; apply ot_ext; reflexivity.

  intros.
  apply wo_def2 in H.
  generalize (uchoice_def _ (order_type_assign_uchoice _ x0 H)).
  intros.
  apply isOrd_succ.
  apply order_type_assign_ord with (1:=H1).
Qed.

(*
Lemma order_type_assign_rel_inv2 : forall r x,
  isWellOrder r ->
  x \in order_type r ->
  forall y, isOrd y ->
  y \incl x ->
  exists r', y == order_type r'.
intros r x wor otr.
intros.
unfold order_type in otr.
rewrite sup_ax in otr;[|admit].
destruct otr as (a,aX,aass).
set (w := uchoice (order_type_assign_rel r a)) in *.
pose (r' :=fun a b =>
  uchoice (order_type_assign_rel r a) \in
  uchoice (order_type_assign_rel r b) /\
  uchoice (order_type_assign_rel r b) \incl w).
exists (inject_rel r' X X).
unfold order_type.
apply eq_intro; intros.
 rewrite sup_ax;[|admit].
 admit.

(*
 assert (Hrec : forall x', lt x' x ->
  forall y', isOrd y' -> y' \incl x' ->
  sup X (fun a => osucc (uchoice (order_type_assign_rel (inject_rel r') X X) a)) \incl
  y' *)
 rewrite sup_ax in H1;[|admit].
 destruct H1 as (b,bX,bass).
 apply isOrd_plump with (uchoice (order_type_assign_rel (inject_rel r' X X) b)); trivial.
  admit.

  apply olts_le in bass; trivial.


  .
 apply olts_le in bass.


assert (xord : isOrd x).
 admit.
induction xord using isOrd_ind; intros.


Lemma order_type_assign_rel_inv2 : forall r a x y,
  isWellOrder r ->
  a \in X ->
  order_type_assign_rel r a x ->
  y \in x ->
  exists2 b, rel_app r b a & order_type_assign_rel r b y.
intros.
assert (rplump :
  forall x y z, x \in X -> (forall z, rel_app r z x -> rel_app r z y) ->
  rel_app r y z -> rel_app r x z).
 admit.
assert (rtrans : forall x y z, rel_app r x y -> rel_app r y z -> rel_app r x z).
 admit.
assert (rext : forall x y, (forall z, rel_app r z x <-> rel_app r z y) -> x == y).
 admit.
assert (rty : forall a b, rel_app r a b -> a \in X).
 admit.
assert (xord : isOrd x).
 apply order_type_assign_ord in H1; trivial.
revert a y H0 H1 H2.
induction xord using isOrd_ind; intros.
destruct order_type_assign_rel_inv with (1:=H3) as (f,fsub,(extf,eqx)).
rewrite eqx in H4.
rewrite sup_ax in H4; trivial.
2:admit.
destruct H4 as (b,bX,?).
assert (rel_app r b a).
 apply subset_elim2 in bX; destruct bX.
 rewrite H5; trivial.
clear bX.
pose (bs := fun b' => b' \in X /\ forall z, rel_app r z b' <-> rel_app r z b /\ f z \in y0).
assert (bs (uchoice bs)).
 apply uchoice_def.
 split;[|split];intros.
  destruct H7; split; intros; rewrite <- H6; trivial.

  admit. (* ex *)

  red in H6,H7.
  apply rext.
  intro.
  rewrite (proj2 H6).
  rewrite (proj2 H7).
  reflexivity.

destruct H6 as (inX,H6).
assert (rel_app r (uchoice bs) a).
 apply rplump with b; trivial.
 intros.
 rewrite H6 in H7; destruct H7; trivial.
exists (uchoice bs); trivial.

assert (y0 == f (uchoice bs)).
 apply eq_intro; intros.

elim H1 with (f b) b z; auto; intros.
 assert (z == f x0).
  destruct (order_type_assign_uchoice _ x0 H) as (_,(_,?)).
  apply H11; trivial.
  apply fsub.
  apply rtrans with b; trivial.
 assert (rel_app r x0 (uchoice bs)).
  rewrite H6.
  split; trivial.
  rewrite <- H11; trivial.
 specialize fsub with (1:=H7).
 apply order_type_assign_rel_inv in fsub; destruct fsub.
 destruct H14.
 rewrite H15.
 rewrite sup_ax.
 2:admit.
 exists x0.
  apply subset_intro; eauto.

  assert (z == x1 x0).
   apply H13 in H12.
   destruct (order_type_assign_uchoice _ x0 H) as (_,(_,?)).
   auto.
  rewrite H16; apply lt_osucc.
  apply H13 in H12.
  apply order_type_assign_ord in H12; trivial.

 rewrite eqx.
 rewrite sup_ax.
 2:admit.
 exists b.
  apply subset_intro; eauto.
 apply lt_osucc.
 apply fsub in H5; apply order_type_assign_ord in H5; trivial.
 eauto.

 apply olts_le in H4; apply H4 in H8; trivial.

elim H1 with (f (uchoice bs)) (uchoice bs) z; auto; intros. 
assert (z == f x0).
  destruct (order_type_assign_uchoice _ x0 H) as (_,(_,?)).
  apply H11; trivial.
  apply fsub.
  apply rtrans with (uchoice bs); trivial.
 rewrite H11.
 apply -> H6; trivial.

 rewrite eqx.
 rewrite sup_ax.
 2:admit.
 exists (uchoice bs).
  apply subset_intro; eauto.
  apply lt_osucc.
  apply fsub in H7.
  apply order_type_assign_ord in H7; trivial.

 eauto.

rewrite H8.
auto.
Qed.
*)


Lemma hartog_assign_surj : forall x,
  x \in hartog_succ ->
  exists2 R, R \in wo &
   forall y, y \in x -> exists2 b, b \in X & order_type_assign_rel R b y.
Admitted.
(*
Lemma hartog_surj : forall x,
  x \in hartog_succ ->
  exists2 R, R \in wo & order_type R == x.
intros.
destruct hartog_assign_surj with (1:=H) as (R,woR,assR).
exists R; trivial.
 

   forall y, y \in x -> exists2 b, b \in X & order_type_assign_rel R b y.


intros.
assert (xord : isOrd x).
 apply isOrd_inv with hartog_succ; trivial.
 apply isOrd_hartog.
unfold hartog_succ in H; rewrite sup_ax in H.
2:admit.
destruct H as (R,Rwo,otr).
unfold order_type in otr.
rewrite sup_ax in otr.
2:apply ot_ext; reflexivity.
destruct otr as (a,aX,xass).
apply olts_le in xass.






rewrite order_type_assign_rel_inv' in xass; auto.
assert (forall y, y \in x ->
  exists2 b, rel_app R b a & y \in osucc (uchoice (order_type_assign_rel R b))).
 intros.
 apply xass in H.
 rewrite sup_ax in H.
 2:admit.
 destruct H.
 exists x0; trivial.
 apply subset_elim2 in H; destruct H.
 rewrite H; trivial.
clear xass.
admit.
Qed.
*)

Section BuraliForti.

Variable I : set -> set -> Prop.
Hypothesis ty_I : forall x,
  x \in hartog_succ -> exists2 y, y \in X & I x y.
Hypothesis inj_I : forall x1 y1 x2 y2,
  x1 \in hartog_succ ->
  x2 \in hartog_succ ->
  y1 \in X ->
  y2 \in X ->
  I x1 y1 ->
  I x2 y2 ->
  y1 == y2 -> x1 == x2.

  Definition OT R :=
    order_type (inject_rel (fun x y => dom _ R x /\ dom _ R y /\ R x y) X X).

  Parameter OT_inj : forall (R1 R2:REL set),
    (forall x, dom _ R1 x -> x \in X) ->
    (forall x, dom _ R2 x -> x \in X) ->
    OT R1 \incl OT R2 -> exists f, morphism _ R1 R2 f.

  Lemma burali_forti : False.
generalize ty_I inj_I.
admit.
Qed.

End BuraliForti.

(*
Lemma hartog_succ_card : lt_card X hartog_succ.
do 2 red; destruct 1.
apply burali_forti with x; trivial.
Qed.

Lemma hartog_bound :
  forall F,
  ext_fun X F -> 
  (forall n, n \in X -> lt (F n) hartog_succ) ->
  lt (sup X F) hartog_succ.
Admitted.
*)
(*
Lemma inj :
  order_type R1 \incl order_type R2 ->
  exists f, morphism R1 R2 f.
*)
(*
Lemma isCard_hartog : isCard hartog_succ.
split; intros.
 apply isOrd_hartog.

 do 2 red; destruct 1 as (R,tyR,injR).  (* R : h -> y *)
 unfold hartog_succ in H; rewrite sup_ax in H.
 2:admit.
 destruct H as (r,wfr,otr).
 unfold order_type in otr; rewrite sup_ax in otr.
 2:admit.
 destruct otr as (a,aX,a_ass).
 rewrite order_type_assign_rel_inv' in a_ass.
 apply olts_le in a_ass.
 apply burali_forti with (fun o a =>
   exists2 w, R o w /\ w \in y &
   



 rewrite uchoice_ax in a_ass.
 2:apply order_type_assign_uchoice; auto.
 destruct a_ass as (z, zass, zlty).
 apply burali_forti with (fun o a => exists2 w, R o w /\ w \in y & order_type_assign_rel r a w); intros.
  elim tyR with x; trivial; intros.

destruct order_type_assign_rel_inv with (1:=zass).
destruct H3.


  assert (exists2 b, rel_app r b a & order_type_assign_rel r b x0).
   apply order_type_assign_rel_inv with z; auto.
   apply isOrd_trans with y; trivial.
   apply order_type_assign_ord with (1:=zass).
  destruct H2 as (b,bRa,b_ass).
  exists b.
   apply app_typ1 with (1:=subset_elim1 _ _ _ wfr) (2:=bRa).

   exists x0; auto.

  destruct H3 as (w1,(rw1,w1y),ass1); destruct H4 as (w2,(rw2,w2y),ass2).
  assert (w1==w2).
   assert (isWellOrder r).
    apply subset_elim2 in wfr; destruct wfr.
    rewrite H3; trivial.
   destruct (order_type_assign_uchoice _ _ H3 H1) as (_,(_,uniq)).
   rewrite <- H5 in ass2; auto.
  apply injR with w1 w2; auto.
Qed.



End Hartog.

(*
Section Burali_Forti_Paradox.

  Definition morphism A (R : A -> A -> Prop) B (S : B -> B -> Prop) f :=
    forall x y, R x y -> S (f x) (f y).

  Variable A0 : Type.                             (* Type_i *)
  Variable i0 : forall X, (X -> X -> Prop) -> A0. (* X: Type_j *)
  Hypothesis inj : forall X1 R1 X2 R2,
    i0 X1 R1 = i0 X2 R2 -> exists f, morphism X1 R1 X2 R2 f.

  Record emb x y : Prop := 
    {X1 : Type;
     R1 : X1 -> X1 -> Prop;
     eqx : x = i0 X1 R1;
     X2 : Type;
     R2 : X2 -> X2 -> Prop;
     eqy : y = i0 X2 R2;
     W2 : WF X2 R2;
     f : X1 -> X2;
     fmorph : morphism X1 R1 X2 R2 f;
     maj : X2;
     majf : forall z, R2 (f z) maj}.


  Lemma emb_trans : forall x y z, emb x y -> emb y z -> emb x z.

  Lemma ACC_emb : forall X R x,
   ACC X R x ->
   forall Y S f,
   morphism Y S X R f ->
   (forall y, R (f y) x) ->
   ACC A0 emb (i0 Y S).

  Lemma WF_emb : WF A0 emb.

  Definition Omega : A0 := i0 A0 emb.


Section Subsets.

  Variable a : A0.

  (* We define the type of elements of A0 smaller than a w.r.t embedding.
     The Record is in Type, but it is possible to avoid such structure. *)
  Record sub : Type :=  {witness : A0; emb_wit : emb witness a}.

  (* F is its image through i0 *)
  Definition F : A0 := i0 sub (Rof _ _ emb witness).

  Lemma F_emb_Omega : emb F Omega.

End Subsets.


  Definition fsub a b (H : emb a b) (x : sub a) : sub b :=
    Build_sub _ (witness _ x) (emb_trans _ _ _ (emb_wit _ x) H).

  (* F is a morphism: a < b => F(a) < F(b)
      - the morphism from F(a) to F(b) is fsub above
      - the upper bound is a, which is in F(b) since a < b
   *)
  Lemma F_morphism : morphism A0 emb A0 emb F.
red in |- *; intros.
exists
 (sub x)
   (Rof _ _ emb (witness x))
   (sub y)
   (Rof _ _ emb (witness y))
   (fsub x y H)
   (Build_sub _ x H); trivial.
Defined.

  Lemma Omega_refl : emb Omega Omega.

  (* The paradox is that Omega cannot be embedded in itself, since
     the embedding relation is well founded.
   *)
  Theorem Burali_Forti : False.
apply ACC_nonreflexive with A0 emb Omega.
apply WF_emb.

exact Omega_refl.
Defined.
*)
End Burali_Forti_Paradox.
*)
End Hartog.
