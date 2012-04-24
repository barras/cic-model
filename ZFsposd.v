Require Import ZF ZFpairs ZFsum ZFrelations ZFcoc ZFord ZFfix.
Require Import ZFstable ZFiso ZFind_w ZFspos.

(** Inductive families. Indexes are modelled as a constraint over an inductive
    type defined without considering the index values.
 *)

Section InductiveFamily.

Variable Arg : set.

(** Given a function [f] that computes the index of any element of [X],
    [index(f)] shall compute the index of any element of [F(X)] it assumes
    the index information is stored within the data (not the case of non-uniform
    parameters...).
 *)
Record dpositive := mkDPositive {
  carrier :> positive;
  w3 : set -> set -> set;
  w4 : set -> set -> Prop
}.

Record isDPositive (p:dpositive) := {
  dpos_pos : isPositive p;
  w3m : morph2 (w3 p);
  w4m : Proper (eq_set==>eq_set==>iff) (w4 p);
  w3typ : forall x i, x ∈ w1 p -> i ∈ w2 p x -> w3 p x i ∈ Arg
}.

Require Import ZFind_wd.

Definition dpos_oper (p:dpositive) (X:set->set) (a:set) :=
  W_Fd (w1 p) (w2 p) (w3 p) (w4 p) X a.

(** Library of dependent positive operators *)
(*
Definition lift_pos (p:positive) : dpositive :=
  mkDPositive p (fun _ _ => empty) (fun _ _ => True)
*)

(** Constraint on the index: corresponds to the conclusion of the constructor *)
Definition dpos_inst i :=
  mkDPositive (pos_cst (singl empty)) (fun _ _ => empty) (fun _ a => i==a).

Lemma isDPos_inst i : isDPositive (dpos_inst i).
constructor; simpl; intros.
 apply isPos_cst.

 do 3 red; reflexivity.

 do 3 red; intros.
 rewrite H0; reflexivity.

 apply empty_ax in H0; contradiction.
Qed.

Definition dpos_cst A := mkDPositive (pos_cst A) (fun _ _ => empty) (fun _ _ => True).

Lemma isDPos_cst A : isDPositive (dpos_cst A).
constructor; simpl; intros.
 apply isPos_cst.

 do 3 red; reflexivity.

 do 3 red; reflexivity.

 apply empty_ax in H0; contradiction.
Qed.

Definition dpos_rec j := mkDPositive pos_rec (fun _ _ => j) (fun _ _ => True).

Lemma isDPos_rec j : j ∈ Arg -> isDPositive (dpos_rec j).
constructor; simpl; intros; trivial.
 apply isPos_rec.

 do 3 red; reflexivity.

 do 3 red; reflexivity.
Qed.

Require Import ZFsum.

Definition dpos_sum (F G:dpositive) :=
  mkDPositive (pos_sum F G)
    (fun x i => sum_case (fun x1 => w3 F x1 i) (fun x2 => w3 G x2 i) x)
    (fun x i => (forall x1, x == inl x1 -> w4 F x1 i) /\
                (forall x2, x == inr x2 -> w4 G x2 i)).

Lemma isDPos_sum F G :
  isDPositive F ->
  isDPositive G ->
  isDPositive (dpos_sum F G).
intros (Fp,F3m,F4m,Fty) (Gp,G3m,G4m,Gty).
constructor; simpl; intros.
 apply isPos_sum; trivial.

 do 3 red; intros.
 apply sum_case_morph; trivial.
  red; intros.
  apply F3m; trivial.

  red; intros.
  apply G3m; trivial.

 do 3 red; intros.
 apply and_iff_morphism.
  apply fa_morph; intros x1.
  rewrite <- H.
  apply fa_morph; intros _.
  apply F4m; auto with *.

  apply fa_morph; intros x2.
  rewrite <- H.
  apply fa_morph; intros _.
  apply G4m; auto with *.

 apply sum_case_ind0 with (2:=H); intros.
  do 2 red; intros.
  rewrite H1; reflexivity.

  rewrite H2; rewrite dest_sum_inl.
  apply Fty; trivial.
  assert (F2m := w2m _ Fp).
  rewrite sum_case_inl0 in H0; eauto.
  revert H0; apply eq_elim; symmetry; apply F2m; trivial.
  rewrite H2; rewrite dest_sum_inl; reflexivity.

  rewrite H2; rewrite dest_sum_inr.
  apply Gty; trivial.
  assert (G2m := w2m _ Gp).
  rewrite sum_case_inr0 in H0; eauto.
  revert H0; apply eq_elim; symmetry; apply G2m; trivial.
  rewrite H2; rewrite dest_sum_inr; reflexivity.
Qed.

Definition dpos_consrec (F G:dpositive) :=
  mkDPositive (pos_consrec F G)
    (fun x => sum_case (w3 F (fst x)) (w3 G (snd x)))
    (fun x i => w4 F (fst x) i /\ w4 G (snd x) i).

Lemma isDPos_consrec F G :
  isDPositive F ->
  isDPositive G ->
  isDPositive (dpos_consrec F G).
intros (Fp,F3m,F4m,Fty) (Gp,G3m,G4m,Gty).
constructor; simpl; intros.
 apply isPos_consrec; trivial.

 do 3 red; intros.
 apply sum_case_morph; trivial.
  red; intros.
  apply F3m; trivial.
  apply fst_morph; trivial.

  red; intros.
  apply G3m; trivial.
  apply snd_morph; trivial.

 do 3 red; intros.
 apply and_iff_morphism.
  apply F4m; trivial.
  apply fst_morph; trivial.

  apply G4m; trivial.
  apply snd_morph; trivial.

 apply sum_case_ind with (6:=H0); intros.
  do 2 red; intros.
  rewrite H1; reflexivity.

  apply F3m; reflexivity.

  apply G3m; reflexivity.

  apply Fty; trivial.
  apply fst_typ in H; trivial.

  apply Gty; trivial.
  apply snd_typ in H; trivial.
Qed.

Definition dpos_norec (A:set) (F:set->dpositive) :=
  mkDPositive (pos_norec A F)
    (fun x i => w3 (F (fst x)) (snd x) i)
    (fun x i => w4 (F (fst x)) (snd x) i).

Definition eqdpos (p1 p2:dpositive) :=
  eqpos p1 p2 /\
  (forall x x' i i', x==x' -> i==i' -> w3 p1 x i == w3 p2 x' i') /\
  (forall x x' i i', x==x' -> i==i' -> (w4 p1 x i <-> w4 p2 x' i')).

Lemma isDPos_norec A F :
  Proper (eq_set ==> eqdpos) F ->
  (forall x, x ∈ A -> isDPositive (F x)) ->
  isDPositive (dpos_norec A F).
constructor; simpl; intros.
 apply isPos_consnonrec.
  do 2 red; intros.
  apply H in H1.
  apply H1.

  intros.
  apply H0; trivial.

 do 3 red; intros.
 assert (ef := fst_morph _ _ H1).
 assert (es := snd_morph _ _ H1).
 apply H in ef.
 destruct ef as (?,(?,?)).
 apply H4; trivial.

 do 3 red; intros.
 assert (ef := fst_morph _ _ H1).
 assert (es := snd_morph _ _ H1).
 apply H in ef.
 destruct ef as (?,(?,?)).
 apply H5; trivial.

 assert (fty := fst_typ_sigma _ _ _ H1).
 apply snd_typ_sigma with (y:=fst x) in H1; auto with *.
  apply H0; trivial.

  do 2 red; intros.
  apply H in H4.
  apply H4.
Qed.

Definition dpos_param (A:set) (F:set->dpositive) :=
  mkDPositive (pos_param A F)
    (fun x i => w3 (F (fst i)) (cc_app x (fst i)) (snd i))
    (fun x i => forall k, k ∈ A -> w4 (F k) (cc_app x k) i).


Lemma isDPos_param A F :
  Proper (eq_set ==> eqdpos) F ->
  (forall x, x ∈ A -> isDPositive (F x)) ->
  isDPositive (dpos_param A F).
constructor; simpl; intros.
 apply isPos_param.
  do 2 red; intros.
  apply H in H1.
  apply H1.

  intros.
  apply H0; trivial.

 do 3 red; intros.
 assert (ef := fst_morph _ _ H2).
 assert (es := snd_morph _ _ H2).
 apply H in ef.
 destruct ef as (?,(?,?)).
 apply H4; trivial.
 apply cc_app_morph; trivial.
 apply fst_morph; trivial.

 do 3 red; intros.
 apply fa_morph; intros k.
 apply fa_morph; intros kty.
 apply H0; trivial.
 rewrite H1; reflexivity.

 assert (fty := fst_typ_sigma _ _ _ H2).
 apply snd_typ_sigma with (y:=fst i) in H2; auto with *.
  apply H0; trivial.
  apply cc_prod_elim with (1:=H1); trivial.

  do 2 red; intros.
  apply H; trivial.
  rewrite H4; reflexivity.
Qed.


End InductiveFamily.

(** Examples *)

Module Vectors.

Require Import ZFnats.

Definition vect A :=
  dpos_sum
    (* vect 0 *)
    (dpos_inst zero)
    (* forall n:N, A -> vect n -> vect (S n) *)
    (dpos_norec N (fun k => dpos_consrec (dpos_cst A) (dpos_consrec (dpos_rec k) (dpos_inst (succ k))))).

Lemma vect_pos A : isDPositive N (vect A).
unfold vect; intros.
apply isDPos_sum.
 apply isDPos_inst.

 apply isDPos_norec.
  do 2 red; intros.
  admit.

  intros.
  apply isDPos_consrec.
   apply isDPos_cst.
  apply isDPos_consrec.
   apply isDPos_rec; trivial.

   apply isDPos_inst.
Qed.

Definition nil := couple (inl empty) (cc_lam empty (fun _ => empty)).

Lemma nil_typ A X :
  morph1 X ->
  nil ∈ dpos_oper (vect A) X zero.
unfold dpos_oper; simpl; intros.
unfold W_Fd.
apply couple_intro_sigma.
 admit.

 apply subset_intro.
  apply inl_typ.
  apply singl_intro.

  split; intros; auto with *.
  apply discr_sum in H0; contradiction.

 apply cc_prod_intro'; intros.
  do 2 red; reflexivity.

  do 2 red; intros.
  apply H.
  apply sum_case_morph; auto with *.
   red; intros; reflexivity.

   red; intros.
   apply sum_case_morph; trivial.
    red; reflexivity.

    red; intros.
    apply sum_case_morph; auto with *.
     red; intros; apply fst_morph; trivial.
     red; reflexivity.

  rewrite sum_case_inl; auto with *.
  do 2 red; reflexivity.

 apply empty_ax in H0; contradiction.
Qed.

Definition cons k x l :=
  couple (inr (couple k (couple x (couple empty empty))))
   (cc_lam (sum empty (sum (singl empty) empty)) (fun _ => l)).

Lemma cons_typ A X k x l :
  morph1 X ->
  k ∈ N ->
  x ∈ A ->
  l ∈ X k ->
  cons k x l ∈ dpos_oper (vect A) X (succ k).
unfold dpos_oper; simpl; intros.
unfold W_Fd.
apply couple_intro_sigma.
 admit.

 apply subset_intro.
  apply inr_typ.
  apply couple_intro_sigma; trivial.
  apply couple_intro; trivial.
  apply couple_intro; apply singl_intro.

  split; intros.
   symmetry in H3; apply discr_sum in H3; contradiction.

   apply inr_inj in H3.
   rewrite <- H3; rewrite fst_def.
   auto with *.

 apply cc_prod_intro'; intros.
  auto with *.

  admit.

  rewrite sum_case_inr; auto with *.
  do 2 red; intros; reflexivity.

  rewrite sum_case_inr.
   assert (x0 == inr (inl empty)).
    apply sum_ind with (3:=H3); intros.
     apply empty_ax in H4; contradiction.

     rewrite H5; apply inr_morph.
     apply sum_ind with (3:=H4); intros.
      rewrite H7.
      apply singl_elim in H6.
      rewrite H6; reflexivity.

      apply empty_ax in H6; contradiction.
   rewrite sum_case_inr0 with (x:=x0).
   2:exists (inl empty); trivial.
   rewrite sum_case_inl0 with (x:=dest_sum x0).
    rewrite fst_def; trivial.

    exists empty.
    rewrite H4; rewrite dest_sum_inr; reflexivity.

   do 2 red; intros.
   apply sum_case_morph; auto with *.
    red; reflexivity.

    red; intros; apply sum_case_morph; auto with *.
     red; intros; apply fst_morph; trivial.
     red; reflexivity.
Qed.

End Vectors.
