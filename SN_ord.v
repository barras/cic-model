Require Import ZF ZFnats ZFord ZFcoc ZFuniv_real.
Require Import Sat.

Require Import SN_ECC_Real.
Import SN_CC_Real.SN_CC_Model. (* The abstract model instance *)
Import SN_CC_Real.SN.          (* The generic model construction *)

(** Typing rules for ordinals
*)

(** * Ordinals *)

Definition Ordt (o:set) : trm :=
  cst (mkTY o (fun _ => snSAT)) Lc.K (fun _ _ => eq_refl) (fun _ _ _ => eq_refl).

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

Definition OSucc : trm -> trm.
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

Definition OSucct : trm -> trm.
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
