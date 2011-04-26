Require Import ZF ZFpairs ZFsum ZFrelations ZFcoc.
Import IZF.

Require Import ZFstable.

Lemma cc_prod_stable : forall dom F,
  morph2 F ->
  (forall x, stable (fun y => F y x)) ->
  stable (fun y => cc_prod dom (F y)).
Admitted. (* proved in ZFclosord *)

(* Here we define the (semantic) notion of strictly positiveness.
   We then show that it fulfills all the requirements for the existence
   of a fixpoint:
   - monotonicity
   - stability
   - isomorphism with an instance of W
 *)

(* Qu: does this notion of strict positivity is powerful enough to build a model
   of IZF? *)

(* Qu: maybe we can avoid the restriction that the first component
   of a sigma cannot be a recursive argument if we consider that we only need
   parametricity (map) up to isomorphic types. *)

Inductive positive :=
| P_Cst (A:set)
| P_Rec
| P_Sum (p1 p2:positive)
| P_ConsRec (p1 p2:positive)
| P_ConsNoRec (A:set) (p:set->positive)
| P_Param (A:set) (p:set->positive).


Fixpoint pos_oper p X :=
  match p with
  | P_Cst A => A
  | P_Rec => X
  | P_Sum p1 p2 => sum (pos_oper p1 X) (pos_oper p2 X)
  | P_ConsRec p1 p2 => prodcart (pos_oper p1 X) (pos_oper p2 X)
  | P_ConsNoRec A p => sigma A (fun x => pos_oper (p x) X)
  | P_Param A p => cc_prod A (fun x => pos_oper (p x) X)
  end.

Inductive eq_pos : positive -> positive -> Prop :=
| EP_Cst : forall A A', A == A' -> eq_pos (P_Cst A) (P_Cst A')
| EP_Rec : eq_pos P_Rec P_Rec
| EP_Sum : forall p1 p2 q1 q2,
   eq_pos p1 p2 -> eq_pos q1 q2 -> eq_pos (P_Sum p1 q1) (P_Sum p2 q2)
| EP_ConsRec : forall p1 p2 q1 q2,
   eq_pos p1 p2 -> eq_pos q1 q2 -> eq_pos (P_ConsRec p1 q1) (P_ConsRec p2 q2)
| EP_ConsNoRec : forall A A' p1 p2,
   A == A' ->
   (forall x x', (*x \in A ->*) x == x' -> eq_pos (p1 x) (p2 x')) ->
   eq_pos (P_ConsNoRec A p1) (P_ConsNoRec A' p2)
| EP_Param : forall A A' p1 p2,
   A == A' ->
   (forall x x', (*x \in A ->*) x == x' -> eq_pos (p1 x) (p2 x')) ->
   eq_pos (P_Param A p1) (P_Param A' p2).

Parameter eq_pos_sym : Symmetric eq_pos.
Existing Instance eq_pos_sym.
Parameter eq_pos_trans : Transitive eq_pos.
Existing Instance eq_pos_trans.

Lemma pos_oper_morph :
  Proper (eq_pos ==> eq_set ==> eq_set) pos_oper.
do 2 red; intros.
red.
induction H; simpl; intros; auto with *.
 apply sum_morph; auto.

 apply prodcart_morph; auto.

 apply sigma_morph; auto with *.

 apply cc_prod_ext; intros; auto.
 red; auto.
Qed.

Lemma pos_oper_mono :
  Proper (eq_pos ==> incl_set ==> incl_set) pos_oper.
do 2 red; intros.
red.
induction H; simpl; intros; auto with *.
 rewrite H; reflexivity.

 apply sum_mono; auto.

 apply prodcart_mono; auto.

 apply sigma_mono; auto with *.
  do 2 red; intros.
  apply pos_oper_morph; auto with *.
  transitivity (p2 x'); auto with *.
  symmetry.
  rewrite H4 in H3; auto with *.

  do 2 red; intros.
  apply pos_oper_morph; auto with *.
  rewrite <- H in H3.
  transitivity (p1 x0); auto with *.
  symmetry; auto with *.

  rewrite H; reflexivity.

 apply cc_prod_covariant; auto with *.
 do 2 red; intros.
 apply pos_oper_morph; auto with *.
 rewrite <- H in H3.
 transitivity (p1 x0); auto with *.
 symmetry; auto with *.
Qed.

Lemma sp_mono : forall p, eq_pos p p -> Proper (incl_set ==> incl_set) (pos_oper p).
do 2 red; intros.
apply pos_oper_mono; trivial.
Qed.

Lemma sp_morph : forall p, eq_pos p p -> morph1 (pos_oper p).
intros.
apply ZFfix.Fmono_morph.
apply sp_mono; trivial.
Qed.

Hint Resolve sp_morph.

Lemma sp_stable : forall p, eq_pos p p -> stable (pos_oper p).
induction p; simpl; intros.
 apply cst_stable.

 apply id_stable.

 inversion_clear H.
 apply sum_stable; eauto.

 inversion_clear H.
 apply prodcart_stable; eauto.

 inversion_clear H0.
 clear H1.
 apply sigma_stable; auto.
  do 2 red; reflexivity.

  do 3 red; intros.
  apply pos_oper_morph; auto.

  apply cst_stable.

  intro.
  change (stable (pos_oper (p x))); auto with *.

 inversion_clear H0.
 clear H1.
 apply cc_prod_stable; auto.
  do 3 red; intros.
  apply pos_oper_morph; auto.

  intro.
  change (stable (pos_oper (p x))); auto with *.
Qed.

Require Import ZFind_w.
Require Import ZFind_nat.
Require Import ZFiso.


(* Label part of the constructor *)
Fixpoint pos_to_w1 p :=
  match p with
  | P_Cst A => A
  | P_Rec => singl empty
  | P_Sum p1 p2 => sum (pos_to_w1 p1) (pos_to_w1 p2)
  | P_ConsRec p1 p2 => prodcart (pos_to_w1 p1) (pos_to_w1 p2)
  | P_ConsNoRec X p => sigma X (fun x => pos_to_w1 (p x))
  | P_Param X p => cc_prod X (fun x => pos_to_w1 (p x))
  end.

Instance pos_to_w1_morph : Proper (eq_pos ==> eq_set) pos_to_w1.
Admitted.

(* Subterm index part of the constructor *)
Fixpoint pos_to_w2 p :=
  match p with
  | P_Cst A => (fun _ => empty)
  | P_Rec => (fun _ => singl empty)
  | P_Sum p1 p2 => sum_case (pos_to_w2 p1) (pos_to_w2 p2)
  | P_ConsRec p1 p2 =>
      (fun c => sum (pos_to_w2 p1 (fst c)) (pos_to_w2 p2 (snd c)))
  | P_ConsNoRec X p =>
      (fun c => pos_to_w2 (p (fst c)) (snd c))
  | P_Param X p =>
      (fun f => sigma X (fun x => pos_to_w2 (p x) (cc_app f x)))
  end.

Instance pos_to_w2_morph : Proper (eq_pos ==> eq_set ==> eq_set) pos_to_w2.
Admitted.

Instance pos_to_w2_morph' :
  forall p, eq_pos p p -> morph1 (pos_to_w2 p).
intros; apply pos_to_w2_morph; trivial.
Qed.

Fixpoint trad_pos_w1 p :=
  match p with
  | P_Cst A => (fun a => a)
  | P_Rec => (fun _ => empty)
  | P_Sum p1 p2 =>
     sum_case
       (fun a1 => inl (trad_pos_w1 p1 a1))
       (fun a2 => inr (trad_pos_w1 p2 a2))
  | P_ConsRec p1 p2 =>
     (fun c => couple (trad_pos_w1 p1 (fst c)) (trad_pos_w1 p2 (snd c)))
  | P_ConsNoRec X p =>
     (fun c => couple (fst c) (trad_pos_w1 (p (fst c)) (snd c)))
  | P_Param X p =>
     (fun f => cc_lam X (fun x => trad_pos_w1 (p x) (cc_app f x)))
  end.

Instance trad_pos_w1_morph : Proper (eq_pos ==> eq_set ==> eq_set) trad_pos_w1.
Admitted.

Fixpoint trad_pos_w2 p :=
  match p with
  | P_Cst A => (fun x _ => empty) (* dummy *)
  | P_Rec => (fun x _ => x)
  | P_Sum p1 p2 =>
     (fun x c => sum_case (fun x1 => trad_pos_w2 p1 x1 c) (fun x2 => trad_pos_w2 p2 x2 c) x)
  | P_ConsRec p1 p2 =>
     (fun x c => sum_case (trad_pos_w2 p1 (fst x)) (trad_pos_w2 p2 (snd x)) c)
  | P_ConsNoRec X p =>
     (fun x c => trad_pos_w2 (p (fst x)) (snd x) c)
  | P_Param X p =>
     (fun x c => trad_pos_w2 (p (fst c)) (cc_app x (fst c)) (snd c))
  end.

Instance trad_pos_w2_morph : Proper (eq_pos ==> eq_set ==> eq_set ==> eq_set) trad_pos_w2.
Admitted.



Definition trad_pos_w p x :=
  couple (trad_pos_w1 p x) (cc_lam (pos_to_w2 p (trad_pos_w1 p x)) (trad_pos_w2 p x)).



Lemma trad_w1_typ : forall X p x,
  eq_pos p p ->
  x \in pos_oper p X ->
  trad_pos_w1 p x \in pos_to_w1 p.
induction p; simpl; intros; trivial.
 apply singl_intro.

 inversion_clear H.
 apply sum_case_ind with (6:=H0).
  do 2 red; intros.
  rewrite H; reflexivity.

  do 2 red; intros.
  apply inl_morph; apply trad_pos_w1_morph; auto with *.

  do 2 red; intros.
  apply inr_morph; apply trad_pos_w1_morph; auto with *.

  intros.
  apply inl_typ; auto.

  intros.
  apply inr_typ; auto.

 inversion_clear H.
 apply couple_intro.
  apply fst_typ in H0; auto.
  apply snd_typ in H0; auto.

 inversion_clear H0.
 clear H2.
 apply couple_intro_sigma.
  do 2 red; intros.
  specialize H3 with (1:=H2).
  rewrite H3; reflexivity.

  apply fst_typ_sigma in H1; trivial.

  apply H; auto with *.
  apply snd_typ_sigma with (2:=H1); auto with *.
  do 2 red; intros.
  specialize H3 with (1:=H2).
  apply pos_oper_morph; auto with *.

 inversion_clear H0.
 clear H2.
 apply cc_prod_intro; intros.
  do 2 red; intros.
  apply trad_pos_w1_morph; auto.
  rewrite H2; reflexivity.

  do 2 red; intros.
  apply pos_to_w1_morph; auto.

  apply H; auto with *.
  apply cc_prod_elim with (1:=H1); trivial.
Qed.

Lemma trad_w2_typ : forall X p x i,
  eq_pos p p ->
  x \in pos_oper p X ->
  i \in pos_to_w2 p (trad_pos_w1 p x) ->
  trad_pos_w2 p x i \in X.
induction p; simpl; trivial; intros.
 apply empty_ax in H1; contradiction.

 inversion_clear H.
 generalize (pos_to_w2_morph' _ H2); intro m1.
 generalize (pos_to_w2_morph' _ H3); intro m1'.
 assert (m2 : morph1 (fun a => inl (trad_pos_w1 p1 a))).
  do 2 red; intros.
  apply inl_morph; apply trad_pos_w1_morph; auto with *.
 assert (m2' : morph1 (fun a => inr (trad_pos_w1 p2 a))).
  do 2 red; intros.
  apply inr_morph; apply trad_pos_w1_morph; auto with *.
 assert (m3 : morph1 (fun x => trad_pos_w2 p1 x i)).
  do 2 red; intros.
  apply trad_pos_w2_morph; auto with *.
 assert (m3' : morph1 (fun x => trad_pos_w2 p2 x i)).
  do 2 red; intros.
  apply trad_pos_w2_morph; auto with *.
 apply sum_ind with (3:=H0); intros.
  rewrite H4 in H1|-*.
  rewrite sum_case_inl in H1|-*; auto with *.
  rewrite sum_case_inl in H1; auto.

  rewrite H4 in H1|-*.
  rewrite sum_case_inr in H1|-*; auto with *.
  rewrite sum_case_inr in H1; auto.

 inversion_clear H.
 generalize (pos_to_w2_morph' _ H2); intro m1.
 generalize (pos_to_w2_morph' _ H3); intro m1'.
 assert (m2:morph1 (trad_pos_w2 p1 (fst x))).
  do 2 red; intros.
  apply trad_pos_w2_morph; auto with *.
 assert (m2':morph1 (trad_pos_w2 p2 (snd x))).
  do 2 red; intros.
  apply trad_pos_w2_morph; auto with *.
 rewrite fst_def in H1.
 rewrite snd_def in H1.
 apply sum_ind with (3:=H1); intros.
  apply fst_typ in H0.
  rewrite H4.
  rewrite sum_case_inl; auto with *.

  apply snd_typ in H0.
  rewrite H4.
  rewrite sum_case_inr; auto with *.

 inversion_clear H0.
 clear H3.
 change (Proper (eq_set ==> eq_pos) p) in H4.
 rewrite fst_def in H2.
 rewrite snd_def in H2.
 apply H; auto with *.
 apply snd_typ_sigma with (2:=H1); auto with *.
 do 2 red; intros.
 apply pos_oper_morph; auto with *.

 inversion_clear H0.
 clear H3.
 apply H; auto with *.
  apply cc_prod_elim with (1:=H1).
  apply fst_typ_sigma in H2; trivial.

  generalize (pos_to_w2_morph _ _ (H4 _ _ (reflexivity (fst i)))); intro m2.
  rewrite (m2 (trad_pos_w1 (p (fst i)) (cc_app x (fst i)))
    (cc_app (cc_lam A (fun x1 => trad_pos_w1 (p x1) (cc_app x x1))) (fst i))).
   eapply snd_typ_sigma with (2:=H2); auto with *.
   do 2 red; intros.
   apply pos_to_w2_morph; auto with *.
   rewrite H3; reflexivity.

   rewrite cc_beta_eq; auto with *.
    do 2 red; intros.
    apply trad_pos_w1_morph; auto with *.
    rewrite H3; reflexivity.

    apply fst_typ_sigma in H2; trivial.
Qed.

(* Proving that the translation of any strictly positive operator to W is
   well-typed. *)
Lemma trad_w_typ : forall p x X,
  eq_pos p p ->
  x \in pos_oper p X ->
  trad_pos_w p x \in W_F (pos_to_w1 p) (pos_to_w2 p) X.
intros.
apply couple_intro_sigma.
 do 2 red; intros.
 apply cc_prod_ext; auto with *.
  apply pos_to_w2_morph; auto with *.
  red; reflexivity.

 apply trad_w1_typ with (2:=H0); trivial.

 apply cc_prod_intro; intros.
  do 2 red; intros.
  apply trad_pos_w2_morph; auto with *.

  do 2 red; reflexivity.

  apply trad_w2_typ with (1:=H); trivial.
Qed.

(* We now have to show that the translation is an isomorphism *)

Lemma trad_w_iso : forall p X Y,
  eq_pos p p ->
  iso X Y -> 
  iso (pos_oper p X) (W_F (pos_to_w1 p) (pos_to_w2 p) Y).
induction p; simpl; intros.
 unfold W_F.
 rewrite sigma_iso_1_r.
  reflexivity.

  intros.
  apply cc_prod_0_l.

 unfold W_F.
 rewrite sigma_iso_1_l.
 rewrite cc_prod_1_l; trivial.

 inversion_clear H.
 rewrite IHp1 with (2:=H0); trivial.
 rewrite IHp2 with (2:=H0); trivial.
 unfold W_F.
 rewrite iso_sum_sigma.
 apply sigma_iso_morph; auto with *.
 intros.
 assert (m1: morph1 (fun x0 => cc_prod (pos_to_w2 p1 x0) (fun _ => Y))).
  do 2 red; intros.
  apply cc_prod_ext.
   apply pos_to_w2_morph; auto with *.
   red; reflexivity.
 assert (m1': morph1 (fun x0 => cc_prod (pos_to_w2 p2 x0) (fun _ => Y))).
  do 2 red; intros.
  apply cc_prod_ext.
   apply pos_to_w2_morph; auto with *.
   red; reflexivity.
 assert (m2:morph1 (pos_to_w2 p1)).
  apply pos_to_w2_morph; auto with *.
 assert (m2':morph1 (pos_to_w2 p2)).
  apply pos_to_w2_morph; auto with *.
 apply sum_ind with (3:=H); intros.
  rewrite H5.
  rewrite sum_case_inl; trivial.
  apply cc_prod_iso_morph.
   rewrite <- H3; rewrite H5; rewrite sum_case_inl; auto with *.
   red; reflexivity.

  rewrite H5.
  rewrite sum_case_inr; trivial.
  apply cc_prod_iso_morph.
   rewrite <- H3; rewrite H5; rewrite sum_case_inr; auto with *.
   red; reflexivity.

 inversion_clear H.
 rewrite IHp1 with (2:=H0); trivial.
 rewrite IHp2 with (2:=H0); trivial.
 unfold W_F.
 rewrite iso_prodcart_sigma.
 apply sigma_iso_morph; auto with *.
 intros.
 rewrite iso_prodcart_cc_prod.
 apply cc_prod_iso_morph.
  apply sum_morph.
   apply pos_to_w2_morph; auto with *.
   rewrite H3; reflexivity.

   apply pos_to_w2_morph; auto with *.
   rewrite H3; reflexivity.

  red; reflexivity.
 inversion_clear H0.
 clear H2.
 transitivity (sigma A (fun x => W_F (pos_to_w1 (p x)) (pos_to_w2 (p x)) Y)).
  apply sigma_iso_morph; auto with *.
  intros.
  rewrite H with (1:=H3 _ _ (reflexivity x)) (2:=H1).
  apply sigma_iso_morph.
   apply pos_to_w1_morph; auto.

   intros.
   apply eq_iso.
   apply cc_prod_ext; intros; auto with *.
    apply pos_to_w2_morph; auto.
    red; reflexivity.

  unfold W_F.
  apply iso_sigma_sigma.

 inversion_clear H0.
 clear H2.
 transitivity (cc_prod A (fun x => W_F (pos_to_w1 (p x)) (pos_to_w2 (p x)) Y)).
  apply cc_prod_iso_morph; auto with *.
  red; intros.
  rewrite H with (1:=H3 _ _ (reflexivity x)) (2:=H1).
  apply sigma_iso_morph.
   apply pos_to_w1_morph; auto.

   intros.
   apply eq_iso.
   apply cc_prod_ext; intros; auto with *.
    apply pos_to_w2_morph; auto.

    red; reflexivity.

  unfold W_F.
  rewrite iso_cc_prod_sigma.
  apply sigma_iso_morph; auto with *.
  intros.
  rewrite cc_prod_curry.
  apply eq_iso.
  apply cc_prod_ext; intros; auto with *.
   apply sigma_morph; intros; auto with *.
   apply pos_to_w2_morph; auto with *.
   rewrite H2; rewrite H5; reflexivity.

   red; reflexivity.
Qed.


(*
Inductive strictly_pos : (set->set) -> Prop :=
(* When the argument is not recursive *)
| SP_cst : forall x, strictly_pos P_Cst (fun _ => x)
(* Recursive argument *)
| SP_id : strictly_pos P_Rec (fun X => X)
(* Alternatives *)
| SP_sum : forall p1 p2 F G,
    strictly_pos p1 F ->
    strictly_pos p2 G ->
    strictly_pos (P_Sum p1 p2) (fun X => sum (F X) (G X))
(* Concatenation of possibly recursive arguments *)
| SP_prodcart : forall p1 p2 F G,
    strictly_pos p1 F ->
    strictly_pos p2 G ->
    strictly_pos (P_ConsRec p1 p2) (fun X => prodcart (F X) (G X))
(* Consing a dependent (hence non-recursive) argument *)
| SP_sigma : forall p A F,
    (forall X, morph1 (F X)) ->
    (forall x, strictly_pos p (fun X => F X x)) ->
    strictly_pos (P_ConsNoRec p) (fun X => sigma A (F X))
(* Higher-Order recursive argument *)
| SP_prod : forall p A F,
    (forall X, morph1 (F X)) ->
    (forall x, strictly_pos p (fun X => F X x)) ->
    strictly_pos (P_Param p) (fun X => cc_prod A (F X)).


Lemma sp_mono : forall p F,
  strictly_pos p F -> Proper (incl_set ==> incl_set) F.
do 2 red.
induction 1; intros; auto with *.
 apply sum_mono; auto.

 apply prodcart_mono; auto.

 apply sigma_mono; auto with *.
 intros.
 setoid_replace (F x x0) with (F x x').
  rewrite H4 in H3; auto.

  apply H; trivial.

 apply cc_prod_covariant; auto with *.
Qed.

Lemma sp_morph : forall p F,
  strictly_pos p F -> morph1 F.
intros.
Require ZFfix.
apply ZFfix.Fmono_morph.
apply sp_mono with p; trivial.
Qed.

Hint Resolve sp_morph.

Lemma sp_stable : forall p F,
  strictly_pos p F -> stable F.
induction 1; intros.
 apply cst_stable.

 apply id_stable.

 apply sum_stable; eauto.

 apply prodcart_stable; eauto.

 apply sigma_stable; auto.
  do 2 red; reflexivity.

  do 3 red; intros.
  transitivity (F x y0).
   apply H; trivial.

   apply (sp_morph p _ (H0 y0)); trivial.

  apply cst_stable.

 apply cc_prod_stable; auto.
 do 3 red; intros.
 transitivity (F x y0).
  apply H; trivial.

  apply (sp_morph p _ (H0 y0)); trivial.
Qed.

Require Import ZFind_w.
Require Import ZFind_nat.
Require Import ZFiso.

Lemma sp_iso_w : forall p F,
  strictly_pos p F ->
  exists A, exists2 B, morph1 B & forall X, iso (F X) (W_F A B X).
*)
