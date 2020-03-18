Require Import ZF ZFnats ZFord ZFcoc.
Require Import Sat.
Require Import ZFuniv_real SN_ECC_Real.
Module Lc := Lambda.

(** Typing rules for ordinals
*)

(** * Ordinals *)

(** The type of ordinals < o (o independent of context) *)
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

(** The type of ordinals < o *)
Definition Oty (o : term) : term.
(*begin show*)
left; exists (fun i => mkTY (int o i) (fun _ => snSAT)) (fun j => tm o j).
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

Lemma El_int_oty O' i :
  El (int (Oty O') i) == cc_bot (int O' i).
simpl; rewrite El_def; reflexivity.
(*apply eq_intro; intros; auto.
rewrite cc_bot_ax in H; destruct H; trivial.
rewrite H.
apply ole_lts; auto.*)
Qed.

(** The type of ordinals <= o *)
Definition OSucct (o : term) : term.
(*begin show*)
left; exists (fun i => mkTY (osucc (int o i)) (fun _ => snSAT)) (fun j => tm o j).
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

Lemma El_int_osucct O' i :
  El (int (OSucct O') i) == osucc (int O' i).
simpl; rewrite El_def.
apply eq_intro; intros; auto.
rewrite cc_bot_ax in H; destruct H; trivial.
rewrite H.
apply ole_lts; auto.
Qed.


(** The ordinal o^+ *)
Definition OSucc (o:term) : term.
(*begin show*)
left; exists (fun i => osucc (int o i)) (fun j => tm o j).
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

(** The ordinal o1∩o2 *)
Definition OMin (O1 O2:term) : term.
(*begin show*)
left; exists (fun i => int O1 i ∩ int O2 i) (fun j => Lc.App2 Lc.K (tm O1 j) (tm O2 j)).
(*end show*)
 do 2 red; intros.
 rewrite H; reflexivity.
 (**)
 do 2 red; intros.
 rewrite H; reflexivity.
 (**)
 red; intros.
 unfold Lc.App2; simpl.
 f_equal.
 2:apply tm_liftable.
 f_equal.
 apply tm_liftable.
 (**)
 red; intros.
 unfold Lc.App2; simpl.
 f_equal.
 2:apply tm_substitutive.
 f_equal.
 apply tm_substitutive.
Defined.

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


Lemma OMin_typ e O1 O2 :
  typ_ord e O1 ->
  typ_ord e O2 ->
  typ_ord e (OMin O1 O2).
unfold typ_ord; intros.
destruct H with (1:=H1).
destruct H0 with (1:=H1).
split; simpl; auto.
apply Lc.sn_K2; trivial.
Qed.

Lemma OSucc_typ e o :
  typ_ord e o ->
  typ_ord e (OSucc o).
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
