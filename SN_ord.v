Require Import ZF ZFnats ZFord ZFcoc.
Require Import Sat.
Require Import ZFuniv_real SN_ECC_Real.

(** Typing rules for ordinals
*)

(** * Ordinals *)

Definition Ordt (o:set) : term :=
  SN.T.cst (mkTY o (fun _ => snSAT)) Lc.K (fun _ _ => eq_refl) (fun _ _ _ => eq_refl).

Definition typ_ord_kind : forall e o, typ e (Ordt o) kind.
red; simpl; intros.
split; [|split]; simpl.
 discriminate.

 exists nil; exists (Ordt o);[reflexivity|].
 exists zero; intros; simpl.
 unfold inX; rewrite El_def; trivial.

 apply Lc.sn_K.
Qed.

Lemma El_int_ord o i :
  zero ∈ o ->
  El (int (Ordt o) i) == o.
intros; simpl.
rewrite El_def.
apply eq_intro; intros; auto.
rewrite cc_bot_ax in H0; destruct H0; trivial.
rewrite H0; trivial.
Qed.

Definition OSucc : term -> term.
(*begin show*)
intros o; left; exists (fun i => osucc (int o i)) (fun j => tm o j).
(*end show*)
 do 2 red; intros.
 rewrite H; reflexivity.
 (**)
 do 2 red; intros.
 rewrite H; reflexivity.
 (**)
 red; intros.
 apply tm_liftable.
 (**)
 red; intros.
 apply tm_substitutive.
Defined.

Definition OSucct : term -> term.
(*begin show*)
intros o; left; exists (fun i => mkTY (osucc (int o i)) (fun _ => snSAT)) (fun j => tm o j).
(*end show*)
 do 2 red; intros.
 apply mkTY_ext; auto with *.
 rewrite H; reflexivity.
 (**)
 do 2 red; intros.
 rewrite H; reflexivity.
 (**)
 red; intros.
 apply tm_liftable.
 (**)
 red; intros.
 apply tm_substitutive.
Defined.

Lemma El_int_osucc O' i :
  El (int (OSucct O') i) == osucc (int O' i).
simpl; rewrite El_def.
apply eq_intro; intros; auto.
rewrite cc_bot_ax in H; destruct H; trivial.
rewrite H.
apply ole_lts; auto.
red; intros.
apply empty_ax in H0; contradiction.
Qed.

Lemma tyord_inv : forall e i j o o',
  isOrd o' ->
  zero ∈ o' ->
  typ e o (Ordt o') ->
  val_ok e i j ->
  isOrd (int o i) /\ int o i < o' /\ Lc.sn (tm o j).
unfold typ; intros.
specialize H1 with (1:=H2).
apply in_int_not_kind in H1.
2:discriminate.
destruct H1.
red in H1; rewrite El_int_ord in H1; trivial.
split;[apply isOrd_inv with o'; trivial|].
split; trivial.
apply sat_sn in H3; trivial.
Qed.

(** * Ordinal judgment *)

Definition typ_ord (e:env) (O:term) : Prop :=
  forall i j, val_ok e i j -> isOrd (int O i) /\ Lc.sn (tm O j).

Lemma typ_ord_cst e o :
  isOrd o ->
  typ_ord e (cst o).
split; simpl; trivial.
apply Lc.sn_K.
Qed.
Hint Resolve typ_ord_cst.


Lemma OSucc_typ e O :
  typ_ord e O ->
  typ_ord e (OSucc O).
unfold typ_ord; intros.
destruct H with (1:=H0).
split; simpl; auto.
Qed.

Hint Resolve OSucc_typ.

Lemma typ_ord_varS e n T :
  typ_ord e (Ref n) ->
  typ_ord (T::e) (Ref (S n)).
unfold typ_ord; simpl; intros.
apply val_ok_shift1 in H0.
apply H with (1:=H0).
Qed.

Lemma typ_ord_var0_ord e O :
  O <> kind ->
  typ_ord e O ->
  typ_ord (OSucct O::e) (Ref 0).
red; simpl; intros.
destruct (H1 0 _ eq_refl).
apply val_ok_shift1  in  H1.
red in H0; specialize H0 with (1:=H1).
destruct H0 as (?,_).
destruct H3.
red in H3; rewrite int_lift_eq in H3.
apply sat_sn in H4; split; trivial.
apply cc_bot_ax in H3; destruct H3.
 simpl in H3; rewrite H3; auto.

 simpl in H3; rewrite Elt_def in H3.
 apply isOrd_inv with (2:=H3); auto.
Qed.

Lemma typ_ord_var0 e o :
  isOrd o ->
  typ_ord (OSucct (cst o)::e) (Ref 0).
intros.
apply typ_ord_var0_ord; auto.
discriminate.
Qed.
