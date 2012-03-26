
Require Import IntMap.
Require Import TypeECC.
Require Import Models.
Require Import Max.

(** Model construction for ECC, in the standard style:
    - syntax first
    - define the interpretation function
    - prove the soundness of the interpretation
 *)

Module MakeModel (M : ECC_Model).
Import M M.CC.

Lemma in_reg_r : forall x y y',
  x ∈ y ->
  y == y' ->
  x ∈ y'.
intros.
rewrite <- H0; trivial.
Qed.

(** * Interpretation *)

Fixpoint int (i:nat->X) (t:term) {struct t} : X :=
  match t with
    Srt (kind n) => u_card n
  | Srt prop => props
  | Ref n => i n
  | App u v => app (int i u) (int i v)
  | Abs A M => lam (int i A) (fun x => int (cons_map x i) M)
  | Prod A B => prod (int i A) (fun x => int (cons_map x i) B)
  end.

Definition In_int (i:nat->X) (M T:term) : Prop :=
  int i M ∈ int i T.

(* setoid stuff *)
Definition eq_int (i1 i2:nat->X) := forall i, i1 i == i2 i.

Instance eq_int_equiv : Equivalence eq_int.
split.
 red; red in |- *; reflexivity.
 red; red in |- *; intros; symmetry  in |- *; trivial.
 red; red in |- *; intros.
   transitivity (y i); trivial.
Qed.

Require Import Setoid.

Instance int_morph : Proper (eq_int ==> @eq _ ==> eqX) int.
do 3 red; intros.
subst y0.
revert x y H.
induction x0; simpl in |- *; intros.
 destruct s; reflexivity.
 apply (H n).
 apply lam_ext; auto.
  red in |- *; intros; apply IHx0_2.
   red in |- *; destruct i; simpl in |- *; auto.
 apply app_ext; auto.
 apply prod_ext; auto.
  red in |- *; intros; apply IHx0_2.
   red in |- *; destruct i; simpl in |- *; auto.
Qed.

(** thinning *)

Lemma int_lift :
  forall n t k i,
  int i (lift_rec n t k) == int (del_map n k i) t.
Proof.
induction t; simpl in |- *; auto.
 destruct s; reflexivity.
 intros.
   unfold del_map in |- *.
   case (le_gt_dec k n0); try reflexivity.
 intros.
   apply lam_ext; auto.
   red in |- *; intros.
   transitivity (int (del_map n (S k) (cons_map y1 i)) t2); trivial.
   apply int_morph; trivial.
   red in |- *; intros.
    rewrite del_cons_map.
   destruct i0; simpl in |- *; auto.
   reflexivity.
 intros.
   apply app_ext; auto.
 intros.
   apply prod_ext; auto.
   red in |- *; intros.
   transitivity (int (del_map n (S k) (cons_map y1 i)) t2); trivial.
   apply int_morph; trivial.
   red in |- *; intros.
    rewrite del_cons_map.
   destruct i0; simpl in |- *; auto.
   reflexivity.
Qed.

(** substitution *)

Lemma int_subst :
  forall n t k i,
  int i (subst_rec n t k) ==
  int (ins_map k (int (del_map k O i) n) i) t.
Proof.
induction t; simpl in |- *; intros.
 destruct s; reflexivity.
 unfold ins_map in |- *.
   destruct (lt_eq_lt_dec k n0) as [[_| _]| _]; try reflexivity.
   unfold lift in |- *.
   apply int_lift.
 apply lam_ext; auto.
   red in |- *; intros.
   transitivity
    (int
       (ins_map (S k) (int (del_map (S k) 0 (cons_map y1 i)) n)
          (cons_map y1 i)) t2); auto.
   apply int_morph; trivial.
   red in |- *; intros.
    rewrite ins_cons_map.
   destruct i0; simpl in |- *; auto.
   reflexivity.
 apply app_ext; auto.
 apply prod_ext; auto.
   red in |- *; intros.
   transitivity
    (int
       (ins_map (S k) (int (del_map (S k) 0 (cons_map y1 i)) n)
          (cons_map y1 i)) t2); auto.
   apply int_morph; trivial.
   red in |- *; intros.
    rewrite ins_cons_map.
   destruct i0; simpl in |- *; auto.
   reflexivity.
Qed.

Lemma int_subst0 :
  forall n t i, int i (subst n t) == int (cons_map (int i n) i) t.
Proof.
unfold subst in |- *.
intros.
transitivity (int (ins_map 0 (int (del_map 0 0 i) n) i) t).
 apply int_subst.
 apply int_morph; trivial.
   red in |- *.
   destruct i0; simpl in |- *; try reflexivity.
Qed.


(** * Semantical judgements *)

Definition int_env (e:env) (i:nat->X) : Prop :=
  forall t n, item_lift t e n -> i n ∈ int i t.

Lemma int_env_cons :
  forall e i T x,
  int_env e i ->
  x ∈ int i T ->
  int_env (cons T e) (cons_map x i).
unfold int_env in |- *; intros.
destruct n.
 simpl in |- *.
   destruct H1.
    subst t.
   apply in_reg_r with (1 := H0).
   symmetry  in |- *.
   unfold lift in |- *.
   transitivity (int (del_map 1 0 (cons_map x i)) T).
  inversion_clear H2.
    apply int_lift.
  apply int_morph; trivial.
    red in |- *; simpl in |- *.
    reflexivity.
 inversion_clear H1.
    subst t.
   inversion_clear H3.
   assert (i n ∈ int i (lift (S n) x0)).
  apply H.
    exists x0; trivial.
   rewrite simpl_lift.
    apply in_reg_r with (1 := H2).
    unfold lift in |- *.
    symmetry  in |- *.
    transitivity (int (del_map 1 0 (cons_map x i)) (lift_rec (S n) x0 0)).
   apply int_lift.
   apply int_morph; trivial.
     red in |- *; simpl in |- *; reflexivity.
Qed.

Definition judge e t T : Prop :=
   forall i, int_env e i -> In_int i t T.

Definition eq_judge e T U : Prop :=
  forall i, int_env e i -> int i T == int i U.

Lemma eq_judge_trans : forall e T U V,
  eq_judge e T U -> eq_judge e U V -> eq_judge e T V.
unfold eq_judge in |- *; intros.
transitivity (int i U); auto.
Qed.

(** * Typing rules and soundness *)

Lemma judge_prop : forall e, judge e (Srt prop) (Srt (kind 0)).
red;red;simpl;intros.
apply u_card_in1.
Qed.

Lemma judge_kind : forall e n, judge e (Srt (kind n)) (Srt (kind (S n))).
red;red;simpl;intros.
apply u_card_in2.
Qed.

Lemma judge_var : forall e n t, item_lift t e n -> judge e (Ref n) t.
red;red;intros.
red in H0.
simpl in |- *; auto.
Qed.

Lemma judge_abs : forall e T M U s1 s2,
  judge e T (Srt s1) ->
  judge (T :: e) U (Srt s2) ->
  judge (T :: e) M U ->
  judge e (Abs T M) (Prod T U).
Proof.
unfold judge in |- *; intros.
red in |- *; simpl in |- *.
apply prod_intro.
 red in |- *; intros.
   apply int_morph; trivial.
   red in |- *; destruct i0; simpl in |- *; auto; reflexivity.
 red in |- *; intros.
   apply int_morph; trivial.
   red in |- *; destruct i0; simpl in |- *; auto; reflexivity.
 intros.
   specialize int_env_cons with (1 := H2) (2 := H3); intro.
   apply H1.
   trivial.
Qed.

Lemma judge_app : forall e u v V Ur,
  judge e v V ->
  judge e u (Prod V Ur) ->
  judge e (App u v) (subst v Ur).
unfold judge in |- *; intros.
red in |- *; simpl in |- *.
apply in_reg_r with (int (cons_map (int i v) i) Ur).
 specialize H0 with (1 := H1).
   red in H0.
   simpl in H0.
   apply prod_elim with (2 := H0).
    red in |- *; intros.
    apply int_morph; trivial.
    red in |- *; destruct i0; simpl in |- *; auto; reflexivity.

    apply H; trivial.
 symmetry  in |- *.
 apply int_subst0.
Qed.

Lemma u_card_incl_le : forall n m x, le n m -> x ∈ u_card n -> x ∈ u_card m.
induction 1; intros; trivial.
apply u_card_incl; auto.
Qed.

Lemma judge_prod : forall e T U s1 s2 s3,
  judge e T (Srt s1) ->
  judge (T :: e) U (Srt s2) ->
  ecc_prod s1 s2 s3 = true ->
  judge e (Prod T U) (Srt s3).
unfold judge in |- *; intros.
red in |- *; destruct s2; simpl in |- *.
 destruct s1; destruct s3; simpl in H, H0, H1 |- *; try discriminate.
  (* Type, Type *)
  destruct (eq_nat_dec (Max.max n n0) n1); simpl in H1; intros; try discriminate.
  subst n1.
  apply u_card_prod; intros.
   red; intros.
   apply int_morph; trivial.
   red; destruct i0; simpl; trivial; reflexivity.

   red in H; simpl in H.
   apply u_card_incl_le with n0; auto.
   apply le_max_r.

   red in H0; simpl in H0.
   apply u_card_incl_le with n.
    apply le_max_l.

    apply H0.
    apply int_env_cons; auto.

  destruct (eq_nat_dec n n0); intros; try discriminate.
  subst n0.
  apply u_card_prod2; intros; auto.
   red; intros.
   apply int_morph; trivial.
   red; destruct i0; simpl; trivial; reflexivity.

   apply (H _ H2).

   red in H0; simpl in H0.
   apply H0.
   apply int_env_cons; trivial.

 simpl in H1.
 destruct s3; simpl in |- *; try  discriminate.
 apply impredicative_prod; intros.
  red in |- *; intros.
  apply int_morph; trivial.
  red in |- *; destruct i0; simpl in |- *; auto; reflexivity.

  red in H0; simpl in H0; apply H0.
  apply int_env_cons; trivial.
Qed.

Lemma judge_beta : forall e T M N U,
  judge e N T ->
  judge (T::e) M U ->
  judge e (App (Abs T M) N) (subst N U).
Proof.
red in |- *; simpl in |- *; intros.
red in |- *; simpl in |- *.
apply in_reg_r with (int (cons_map (int i N) i) U).
 apply prod_elim with (dom := int i T) (F := fun x => int (cons_map x i) U).
  red in |- *; intros.
  apply int_morph; trivial.
  red in |- *; destruct i0; simpl in |- *; auto; reflexivity.

  apply prod_intro.
   red in |- *; intros.
   apply int_morph; trivial.
   red in |- *; destruct i0; simpl in |- *; auto; reflexivity.

   red in |- *; intros.
   apply int_morph; trivial.
   red in |- *; destruct i0; simpl in |- *; auto; reflexivity.

   intros.
   red in H0; red in H0.
   apply H0.
   apply int_env_cons; trivial.
  apply (H _ H1).

 symmetry  in |- *.
 apply int_subst0.
Qed.

Lemma eq_judge_beta : forall e T M N,
  judge e N T ->
  eq_judge e (App (Abs T M) N) (subst N M).
red in |- *; simpl in |- *; intros.
transitivity (int (cons_map (int i N) i) M).
 apply beta_eq with (F := fun x => int (cons_map x i) M).
  red in |- *; intros.
    apply int_morph; trivial.
    red in |- *; destruct i0; simpl in |- *; auto.
    reflexivity.
  apply (H _ H0).
 symmetry  in |- *.
   apply int_subst0.
Qed.

Lemma judge_conv :
  forall e M T T',
  judge e M T ->
  eq_judge e T T' ->
  judge e M T'.
red in |- *; simpl in |- *; intros.
red in |- *.
apply in_reg_r with (int i T); auto.
apply (H _ H1).
Qed.

Require Import TypeJudgeECC.

Lemma int_sound : forall e M M' T,
  eq_typ e M M' T ->
  judge e M T /\ eq_judge e M M'.
induction 1; intros.
 split.
  apply judge_prop.
  red in |- *; reflexivity.
 split.
  apply judge_kind.
  red in |- *; reflexivity.
 split.
  apply judge_var; trivial.
  red in |- *; reflexivity.
 destruct IHeq_typ1.
   destruct IHeq_typ2.
   destruct IHeq_typ3.
   split.
  apply judge_abs with s1 s2; trivial.
  red in |- *; intros.
    simpl in |- *.
    apply lam_ext; auto.
    red in |- *; intros.
    red in H7.
    transitivity (int (cons_map y2 i) M).
   apply int_morph; trivial.
     red in |- *; destruct i0; simpl in |- *; auto.
     reflexivity.
   apply H8.
     apply int_env_cons; trivial.
     rewrite <- H11; trivial.
 destruct IHeq_typ1.
   destruct IHeq_typ2.
   destruct IHeq_typ3.
   destruct IHeq_typ4.
   split.
  red in |- *; intros.
    generalize i H12.
    apply judge_app with V; trivial.
  red in |- *; intros.
    simpl in |- *.
    apply app_ext.
   apply H9; trivial.
   apply H5; trivial.
 destruct IHeq_typ1.
   destruct IHeq_typ2.
   split.
  apply judge_prod with s1 s2; trivial.
  red in |- *; simpl in |- *; intros.
    apply prod_ext.
   apply H3; trivial.
   red in |- *; intros.
     transitivity (int (cons_map y1 i) U').
    apply H5.
      apply int_env_cons; trivial.
    apply int_morph; trivial.
      red in |- *; destruct i0; simpl in |- *; auto; reflexivity.
 destruct IHeq_typ1.
   destruct IHeq_typ2.
   destruct IHeq_typ3.
   destruct IHeq_typ4.
   split.
  apply judge_beta; trivial.
  apply eq_judge_trans with (subst N M).
   apply eq_judge_beta; trivial.
   red in |- *; intros.
     transitivity (int (cons_map (int i N) i) M).
    apply int_subst0.
    transitivity (int (cons_map (int i N) i) M').
     apply H9.
       apply int_env_cons; trivial.
       apply (H4 _ H12).
     transitivity (int (cons_map (int i N') i) M').
      apply int_morph; trivial.
        red in |- *; destruct i0; simpl in |- *; auto; reflexivity.
      symmetry  in |- *.
        apply int_subst0.
 destruct IHeq_typ1.
   destruct IHeq_typ2.
   split; trivial.
   apply judge_conv with T; trivial.
 destruct IHeq_typ1.
   destruct IHeq_typ2.
   split; trivial.
   apply judge_conv with T'; trivial.
   red in |- *; intros.
   symmetry  in |- *.
   apply H4; trivial.
Qed.

End MakeModel.


(** Now we show that we have a model in Tarski-Grothendieck *)

Require Import ZF ZFcoc ModelZF ZFecc.

Module ECC <: ECC_Model.

  Module CC := ModelZF.CCM.

  Definition u_card := ecc.
  
  Lemma u_card_in1 : props ∈ u_card 0.
  Proof (ecc_in1 0).

  Lemma u_card_in2 : forall n, u_card n ∈ u_card (S n).
  Proof ecc_in2.

  Lemma u_card_incl : forall n x, x ∈ u_card n -> x ∈ u_card (S n).
  Proof ecc_incl.

  Lemma u_card_prod : forall n X Y,
    CC.eq_fun X Y Y ->
    X ∈ u_card n ->
    (forall x, x ∈ X -> Y x ∈ u_card n) ->
    CC.prod X Y ∈ u_card n.
  Proof ecc_prod.

  Lemma u_card_prod2 : forall n X Y,
    CC.eq_fun X Y Y ->
    X ∈ props ->
    (forall x, x ∈ X -> Y x ∈ u_card n) ->
    CC.prod X Y ∈ u_card n.
  Proof ecc_prod2.

End ECC.

Module ECC_Sound := MakeModel ECC.

Print Assumptions ECC_Sound.int_sound.

