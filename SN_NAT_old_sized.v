(** Strong normalization of the model of CC+NAT in the type-based
  termination presentation.

  This is work in progress, several lemmas of this module are admitted.
*)

Require Import List Bool Models.
Require SN_CC_Real_old.
Import ZFgrothendieck.
Import ZF ZFsum ZFnats ZFrelations ZFord ZFfix.
Require Import ZFfunext ZFfixrec ZFecc (*ZFuniv_real*) ZFind_nat SATtypes SATnat_old_real.

Import SN_CC_Real_old.
Import SN_CC_Real_old.SN.
Import SN_CC_Real_old.CCSN.
Opaque Real.
Import Sat Sat.SatSet.

Lemma Real_intro x t T :
  x ∈ El T ->
  (x ∈ El T -> inSAT t (Real T x)) ->
  [x,t] \real T.
split; auto.
Qed.

Lemma Real_ax x t T R :
  (forall x x', x ∈ T -> x==x' -> eqSAT (R x) (R x')) ->
  ([x,t] \real mkTY T R <-> x ∈ T /\ inSAT t (R x)).
intros.
unfold inX; rewrite El_def.
split; destruct 1; split; trivial; rewrite Real_def in *; auto with *.
Qed.

Lemma Real_intro2 x t T R :
  (forall x x', x ∈ T -> x==x' -> eqSAT (R x) (R x')) ->
  x ∈ T ->
  (x ∈ T -> inSAT t (R x)) ->
  [x,t] \real mkTY T R.
split.
 unfold inX; rewrite El_def; trivial.

 rewrite Real_def; auto.
Qed.


(** Subtyping *)
(*
Definition sub_typ_covariant : forall e U1 U2 V1 V2,
  U1 <> kind ->
  eq_typ e U1 U2 ->
  sub_typ (U1::e) V1 V2 ->
  sub_typ e (Prod U1 V1) (Prod U2 V2).
intros.
apply sub_typ_covariant; trivial.
intros.
unfold eqX, lam, app.
unfold inX in H2.
unfold prod in H2; rewrite El_def in H2.
apply cc_eta_eq in H2; trivial.
Qed.
*)
(** Universes *)
(*Module Lc:=Lambda.
Definition type (n:nat) : term :=
  cst (mkTY (ecc n) (fun _ => snSAT)) Lc.K (fun _ _ => eq_refl) (fun _ _ _ => eq_refl).

Lemma typ_Prop : forall e, typ e prop (type 0).
red; intros; simpl.
split;[discriminate|split].
 unfold inX; simpl.
 rewrite El_def.
 apply (grot_succ_in gr).
Qed.

Lemma typ_Type : forall e n, typ e (type n) (type (S n)).
red; intros; simpl.
apply (grot_succ_in gr).
Qed.

Lemma cumul_Type : forall e n, sub_typ e (type n) (type (S n)).
red; simpl; intros.
red; intros.
apply ecc_incl; trivial.
Qed.

Lemma cumul_Prop : forall e, sub_typ e prop (type 0).
red; simpl; intros.
red; intros.
apply G_trans with props; trivial.
 apply (grot_succ_typ gr).

 apply (grot_succ_in gr).
Qed.

Lemma typ_prod2 : forall e n T U,
  typ e T (type n) ->
  typ (T :: e) U (type n) ->
  typ e (Prod T U) (type n).
Proof.
unfold typ, Prod; simpl; red; intros e n T U ty_T ty_U i is_val.
apply G_cc_prod.
 apply ecc_grot.

 red; red; intros.
 rewrite H0; auto with *.

 apply ty_T; trivial.

 intros.
 apply ty_U.
 apply vcons_add_var; auto.
Qed.
*)


(** Ordinals *)

Definition Ord (o:set) : term :=
  cst o Lc.K (fun _ _ => eq_refl) (fun _ _ _ => eq_refl).

Definition Ordt (o:set) : term :=
  cst (mkTY o (fun _ => snSAT)) Lc.K (fun _ _ => eq_refl) (fun _ _ _ => eq_refl).

Definition typ_ord_kind : forall e o, zero ∈ o -> typ e (Ordt o) kind.
red; simpl; intros.
split; [|split]; simpl.
 discriminate.

 exists nil; exists (Ordt o);[reflexivity|].
 exists zero; intros; simpl.
 unfold inX; rewrite El_def; trivial.

 apply Lc.sn_K.
Qed.


Definition typ_ord_ord : forall e o o',
  o < o' -> typ e (Ord o) (Ordt o').
red; simpl; intros.
apply in_int_intro; try discriminate.
simpl.
rewrite Real_ax;[split|]; auto with *.
apply Lc.sn_K.
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

Lemma tyord_inv : forall e i j o o',
  isOrd o' ->
  typ e o (Ordt o') ->
  val_ok e i j ->
  isOrd (int o i) /\ int o i < o' /\ Lc.sn (tm o j).
unfold typ; intros.
specialize H0 with (1:=H1).
apply in_int_not_kind in H0.
2:discriminate.
simpl in H0.
rewrite Real_ax in H0; auto with *.
destruct H0.
eauto using isOrd_inv.
Qed.

(** Nat *)

Definition Nat : term.
(*begin show*)
left; exists (fun _ => mkTY NAT (fNATi omega)) (fun _ => Lc.K).
(*end show*)
 do 2 red; reflexivity.
 do 2 red; reflexivity.
 red; reflexivity.
 red; reflexivity.
Defined.

Definition NatI (O:term) : term.
(*begin show*)
left; exists (fun i => mkTY (NATi (int O i)) (fNATi (int O i))) (fun j => tm O j).
(*end show*)
 do 2 red; intros.
 unfold eqX.
 apply mkTY_ext.
  rewrite H; reflexivity.

  intros.
  apply fNATi_morph; auto.
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

Lemma typ_natI : forall e eps o,
  isOrd eps ->
  typ e o (Ordt eps) ->
  typ e (NatI o) kind.
red; intros; simpl.
red in H0; specialize H0 with (1:=H1).
apply in_int_not_kind in H0.
2:discriminate.
split;[|split].
 discriminate.

 exists nil; exists (NatI o);[reflexivity|].
 admit. (* not empty *)

 simpl.
 apply real_sn in H0; trivial.
Qed.

Lemma realNati_def x t i O :
 isOrd (int O i) ->
 ([x,t] \real int (NatI O) i <->
  x ∈ NATi (int O i) /\ inSAT t (fNATi (int O i) x)).
intros.
simpl.
rewrite Real_ax; auto with *.
intros.
rewrite H1; reflexivity.
Qed.

(* Zero *)

Definition Zero : term.
(* begin show *)
left; exists (fun _ => ZERO) (fun _ => ZE).
(* end show *)
 do 2 red; reflexivity.
 do 2 red; reflexivity.
 red; reflexivity.
 red; reflexivity.
Defined.

Lemma typ_Zero : forall o e O,
  isOrd o ->
  typ e O (Ordt o) ->
  typ e Zero (NatI (OSucc O)).
red; simpl; intros.
destruct tyord_inv with (2:=H0)(3:=H1) as (?,(?,_)); trivial.
apply in_int_intro; try discriminate.
rewrite realNati_def.
2:simpl; auto.
split.
 simpl.
 apply ZEROi_typ; trivial.

 simpl tm.
 apply Real_ZERO; trivial.
Qed.


(* Successor *)

Definition Succ (o:term): term.
(* begin show *)
left; exists (fun i => lam (int (NatI o) i) SUCC) (fun _ => Lc.Abs (SU (Lc.Ref 0))).
(*end show *)
 do 2 red; intros.
 apply lam_ext.
  apply mkTY_ext; auto with *.
   rewrite H; reflexivity.

   intros.
   rewrite H; rewrite H1.
   reflexivity.

  red; intros.
  rewrite H1; reflexivity.

 do 2 red; auto.

 red; reflexivity.

 red; reflexivity.
Defined.


Lemma El_prod A Ar B Br :
  ext_fun A B ->
  El (prod(mkTY A Ar) (fun x => mkTY (B x) (Br x))) ==
  cc_prod A B.
intros.
unfold prod; rewrite El_def.
apply cc_prod_ext.
 rewrite El_def; reflexivity.

 red; intros.
 rewrite El_def; apply H; trivial.
 rewrite El_def in H0; trivial.
Qed.
(*
 Lemma prodReal :
  [x,t] \real prod (mkTY A Ar) (fun x => mkTY (B x) (Br x)) <->
  x ∈ cc_prod
*)

Lemma typ_succi : forall e o i,
  isOrd o ->
  typ e i (Ordt o) ->
  typ e (Succ i) (Prod (NatI i) (NatI (OSucc (lift 1 i)))). 
red; intros.
destruct tyord_inv with (2:=H0) (3:=H1) as (?,(?,?)); trivial.
clear H0.
apply in_int_intro; try discriminate.
apply prod_intro_sn.
 red; intros.
 rewrite H5; reflexivity.

 red; intros.
 rewrite H5; reflexivity.

 simpl.
 unfold INR.
 constructor; intros.
 red in H0; apply Lc.nf_norm in H0; [contradiction|].
 repeat constructor.

 intros.
 rewrite realNati_def in H0 |- *; auto with *.
 2:simpl;rewrite int_lift_eq; simpl; auto.
 destruct H0.
 split.
  simpl; rewrite int_lift_eq; simpl.
  apply SUCCi_typ; auto.

  simpl tm.
  apply inSAT_exp.
   left; reflexivity.
  unfold Lc.subst; simpl Lc.subst_rec.
  simpl int; rewrite int_lift_eq.
  apply Real_SUCC; trivial.
Qed.

(* Case analysis *)

Definition Natcase (fZ fS n : term) : term.
(*begin show*)
left; exists (fun i => NATCASE (int fZ i) (fun k => int fS (V.cons k i)) (int n i))
       (fun j => Lc.App2 (tm n j) (Lc.Abs (Lc.lift 1 (tm fZ j))) (Lc.Abs (tm fS (Lc.ilift j)))).
(*end show*)
do 2 red; intros.
apply NATCASE_morph.
 red; intros.
 rewrite H; reflexivity.

 red; intros.
 rewrite H; rewrite H0; reflexivity.

 rewrite H; reflexivity.
(**)
do 2 red; intros.
f_equal.
 rewrite H; trivial.

 f_equal; f_equal.
 rewrite H; trivial.

 f_equal.
 rewrite H; trivial.
(**)
 red; intros; simpl.
 unfold Lc.App2.
 f_equal.
  f_equal.
   apply tm_liftable.

   rewrite <- Lc.permute_lift.
   f_equal.
   f_equal.
   apply tm_liftable.

  f_equal.
  rewrite <- tm_liftable.
  apply tm_morph; auto with *.
  apply Lc.ilift_binder_lift.

(**)
 red; intros; simpl.
 unfold Lc.App2.
 f_equal.
  f_equal.
   apply tm_substitutive.

   rewrite Lc.commut_lift_subst.
   f_equal.
   f_equal.
   apply tm_substitutive.

  f_equal.
  rewrite <- tm_substitutive.
  apply tm_morph; auto with *.
  apply Lc.ilift_binder.
Defined.

Instance Natcase_morph :
  Proper (eq_term ==> eq_term ==> eq_term ==> eq_term) Natcase.
do 4 red; intros.
split; red; simpl; intros.
 apply NATCASE_morph.
  red; intros.
  apply int_morph; trivial.

  red; intros; apply int_morph; trivial.
  apply V.cons_morph; trivial.

  apply int_morph; trivial.

 f_equal.
  apply tm_morph; trivial.
  rewrite H2; rewrite H; reflexivity.
  rewrite H2; rewrite H0; reflexivity.
Qed.

Existing Instance NATCASE_morph.

Lemma Natcase_succ : forall o O e n fZ fS,
  isOrd o ->
  typ e O (Ordt o) ->
  typ e n (NatI O) ->
  eq_typ e (Natcase fZ fS (App (Succ O) n)) (subst n fS).
red; intros.
destruct tyord_inv with (2:=H0) (3:=H2) as (?,(?,_)); trivial.
red in H1; specialize H1 with (1:=H2).
apply in_int_not_kind in H1.
2:discriminate.
destruct H1 as (H1,_).
red; simpl.
assert (m1: morph1 (fun _ => int fZ i)).
 do 2 red; intros; reflexivity.
assert (m2: morph1 (fun k => int fS (V.cons k i))).
 do 2 red; intros.
 rewrite H5; reflexivity.
rewrite beta_eq; trivial.
 rewrite NATCASE_SUCC; intros.
  rewrite int_subst_eq; reflexivity.

  rewrite H5; reflexivity.

 red; intros.
 rewrite H6; reflexivity.
Qed.
Existing Instance NATi_morph.

Lemma typ_natcase : forall o e O P fZ fS n,
  isOrd o ->
  typ e O (Ordt o) ->
  typ e fZ (App P Zero) ->
  typ (NatI O :: e) fS (App (lift 1 P) (App (Succ (lift 1 O)) (Ref 0))) ->
  typ e n (NatI (OSucc O)) ->
  typ e (Natcase fZ fS n) (App P n).
red; intros.
destruct tyord_inv with (2:=H0)(3:=H4) as (?,(?,_ )); trivial.
red in H1; specialize H1 with (1:=H4).
apply in_int_not_kind in H1;[|discriminate].
red in H3; specialize H3 with (1:=H4).
apply in_int_not_kind in H3;[|discriminate].
apply in_int_intro; try discriminate.
destruct H1.
rewrite realNati_def in H3; simpl in H3|-*; auto.
destruct H3.
apply Real_intro; intros.
 apply NATCASE_typ with (o:=int O i) (P:=fun n => El(app (int P i) n)); intros; trivial.
  do 2 red; intros.
  rewrite H9; reflexivity.

  do 2 red; intros.
  rewrite H9; reflexivity.

  assert (val_ok (NatI O :: e) (V.cons n0 i) (I.cons daimon j)).
   apply vcons_add_var; trivial.
   2:discriminate.
   rewrite realNati_def; auto with *.
   split; trivial.
   apply varSAT.
  apply H2 in H10; clear H1; simpl in H10.
  apply in_int_not_kind in H10;[|discriminate].
  destruct H10 as(H10,_ ).
  revert H10; apply eq_elim; simpl.
  rewrite int_cons_lift_eq.
  rewrite beta_eq; auto with *.
   red; intros; apply inr_morph; auto.

   rewrite El_def.
   rewrite int_cons_lift_eq; trivial.

 apply Real_NATCASE with
   (C:=fun n => Real (app (int P i) n) (NATCASE (int fZ i) (fun k => int fS (V.cons k i)) n)) (o:=int O i); auto.
  do 2 red; intros.
  apply Real_morph.
   rewrite H10; reflexivity.

   apply NATCASE_morph; auto with *.
   red; intros.
   rewrite H11; reflexivity.

  rewrite NATCASE_ZERO; trivial.

  apply piSAT0_intro.
   apply typ_abs in H2.
   3:discriminate.
   2:left.
   2:apply typ_natI with o; trivial.
   apply H2 in H4.
   apply in_int_sn in H4.
   eapply Lc.subterm_sn.
   eapply Lc.subterm_sn.
   eexact H4.
   apply Lc.sbtrm_app_l.
   apply Lc.sbtrm_app_r.

   intros.
   apply inSAT_exp; [apply sat_sn in H11; auto|].
   rewrite <- tm_subst_cons.
   rewrite NATCASE_SUCC.
   2:intros ? e'; rewrite e'; reflexivity.
   assert (val_ok (NatI O :: e) (V.cons x i) (I.cons u j)).
    apply vcons_add_var; trivial.
    2:discriminate.
    rewrite realNati_def; auto with *.
   apply H2 in H12.
   apply in_int_not_kind in H12.
   2:discriminate.
   destruct H12 as (_,H12).
   simpl in H12.
   rewrite int_lift_eq in H12.
   revert H12; apply inSAT_morph; trivial.
   apply Real_morph; auto with *.
   apply cc_app_morph; [reflexivity|].
   unfold app, lam; rewrite cc_beta_eq; auto with *.
   rewrite El_def.
   rewrite int_lift_eq; trivial.
Qed.
Print Assumptions typ_natcase.

Lemma typ_natcase' : forall o e O P fZ fS n T,
  isOrd o ->
  T <> kind ->
  typ e O (Ordt o) ->
  sub_typ e (App P n) T -> 
  typ e fZ (App P Zero) ->
  typ (NatI O :: e) fS
    (App (lift 1 P) (App (Succ (lift 1 O)) (Ref 0))) ->
  typ e n (NatI (OSucc O)) ->
  typ e (Natcase fZ fS n) T.
intros.
apply typ_subsumption with (App P n); auto.
2:discriminate.
apply typ_natcase with o O; trivial.
Qed.

(********************************************************************************)
(** Occurrences *)


  (* Non-occurrence : interp do not depend on variables in set [f] *)
  Definition noccur (f:nat->bool) (T:term) : Prop :=
    forall i i',
    (forall n, if f n then True else i n == i' n) ->
    int T i == int T i'.

  Lemma noc_var : forall f n, f n = false -> noccur f (Ref n).
red; simpl; intros.
specialize (H0 n).
rewrite H in H0; trivial.
Qed.

  Lemma noc_kind : forall f, noccur f kind.
red; simpl; reflexivity.
Qed.

  Lemma noc_prop : forall f, noccur f prop.
red; simpl; reflexivity.
Qed.

  Lemma noc_app : forall f a b,
    noccur f a -> noccur f b -> noccur f (App a b).
unfold noccur; simpl; intros.
rewrite (H _ _ H1).
rewrite (H0 _ _ H1).
reflexivity.
Qed.


(********************************************************************************)
(** Judgements with variance *)

Module Beq.
Definition t := bool.
Definition eq := @eq bool.
Definition eq_equiv : Equivalence eq := eq_equivalence.
Existing Instance eq_equiv.
End Beq.
Module B := VarMap.Make(Beq).

Module OTeq.
Definition t := option term.
Definition eq := @eq (option term).
Definition eq_equiv : Equivalence eq := eq_equivalence.
Existing Instance eq_equiv.
End OTeq.
Module OT := VarMap.Make(OTeq).

(* Environments with tags on ordinal and recursive function variables *)
Record fenv := {
  tenv : env;
  ords : B.map; (* variables denoting ordinals *)
  fixs : OT.map (* variables denoting recursive functions with their domain *)
}.

Definition tinj e :=
  Build_fenv e (B.nil false) (OT.nil None).

Definition push_var e T :=
  Build_fenv (T::tenv e) (B.cons false (ords e)) (OT.cons None (fixs e)).

Definition push_fun e dom rng :=
  Build_fenv (Prod dom rng::tenv e)
    (B.cons false (ords e)) (OT.cons (Some dom) (fixs e)).

Definition push_ord e T :=
  Build_fenv (T::tenv e) (B.cons true (ords e)) (OT.cons None (fixs e)).


(* Additional judgments for fix body *)
Definition val_mono (e:fenv) i j i' j' :=
    val_ok (tenv e) i j /\
    val_ok (tenv e) i' j' /\
    forall n,
    if ords e n then i n ⊆ i' n
    else match fixs e n with
      Some T => forall x, x ∈ El(int T (V.shift (S n) i)) -> app (i n) x == app (i' n) x
    | _ => i n == i' n
    end.

Lemma val_mono_refl : forall e i j,
  val_ok (tenv e) i j -> val_mono e i j i j.
split;[idtac|split]; simpl; auto with *.
intro n.
destruct (ords e n); auto with *.
destruct (fixs e n); auto with *.
Qed.

Lemma val_push_var : forall e i j i' j' x t x' t' T,
  val_mono e i j i' j' ->
  x == x' ->
  [x,t] \real int T i ->
  [x',t'] \real int T i' ->
  T <> kind ->
  val_mono (push_var e T) (V.cons x i) (I.cons t j) (V.cons x' i') (I.cons t' j').
destruct 1 as (?&?&?); split;[idtac|split]; trivial.
 unfold push_var; simpl.
 apply vcons_add_var; trivial.

 unfold push_var; simpl.
 apply vcons_add_var; trivial.

 destruct n as [|n]; simpl; auto.
 generalize (H1 n).
 destruct (ords e n); trivial.
Qed.

Lemma val_push_ord : forall e i j i' j' x t x' t' T,
  val_mono e i j i' j' ->
  x ⊆ x' ->
  [x,t] \real int T i ->
  [x',t'] \real int T i' ->
  T <> kind ->
  val_mono (push_ord e T) (V.cons x i) (I.cons t j) (V.cons x' i') (I.cons t' j').
destruct 1 as (?&?&?); split;[idtac|split]; trivial.
 unfold push_ord; simpl.
 apply vcons_add_var; trivial.

 unfold push_ord; simpl.
 apply vcons_add_var; trivial.

 destruct n as [|n]; simpl; auto.
 generalize (H1 n).
 destruct (ords e n); trivial.
Qed.

Lemma val_push_fun : forall e i j i' j' f tf g tg T U,
  val_mono e i j i' j' ->
  [f,tf] \real prod (int T i) (fun x => int U (V.cons x i)) ->
  [g,tg] \real prod (int T i') (fun x => int U (V.cons x i')) ->
  fcompat (El(int T i)) f g ->
  val_mono (push_fun e T U) (V.cons f i) (I.cons tf j) (V.cons g i') (I.cons tg j').
destruct 1 as (?&?&?); split;[idtac|split]; trivial.
 unfold push_fun; simpl.
 apply vcons_add_var; trivial.
 discriminate.

 unfold push_fun; simpl.
 apply vcons_add_var; trivial.
 discriminate.

 destruct n as [|n]; simpl; auto.
 generalize (H1 n).
 destruct (ords e n); trivial.
Qed.

(** Function Extension judgment *)
Definition fx_extends e dom M :=
  forall i i' j j', val_mono e i j i' j' ->
  fcompat (El(int dom i)) (int M i) (int M i').

(** Covariance judgment *)
Definition fx_sub e M :=
  forall i i' j j', val_mono e i j i' j' ->
  forall x t, [x,t] \real int M i -> [x,t] \real int M i'.

Definition fx_subval e M :=
  forall i i' j j', val_mono e i j i' j' -> int M i ⊆ int M i'.

(** Invariance *)
Definition fx_equals e M :=
  forall i i' j j', val_mono e i j i' j' -> int M i == int M i'.

Definition spec_var e n :=
  ords e n || match fixs e n with Some _ => true | _ => false end.

  Lemma fx_eq_noc : forall e t,
    noccur (spec_var e) t ->
    fx_equals e t.
unfold noccur, fx_equals, spec_var; intros.
apply H; intros.
destruct H0 as (_,(_,H0)).
generalize (H0 n).
destruct (ords e n); simpl; trivial.
destruct (fixs e n); simpl; trivial.
Qed.

  Lemma fx_eq_app : forall e u v,
    fx_equals e u ->
    fx_equals e v ->
    fx_equals e (App u v).
unfold fx_equals; intros.
specialize H with (1:=H1).
specialize H0 with (1:=H1).
simpl.
rewrite H; rewrite H0; reflexivity.
Qed.

  Lemma fx_eq_abs : forall e T M,
    T <> kind ->
    fx_equals e T ->
    fx_equals (push_var e T) M ->
    fx_equals e (Abs T M).
unfold fx_equals; intros.
simpl.
apply lam_ext; eauto.
red; intros.
apply H1 with (I.cons daimon j) (I.cons daimon j').
specialize H0 with (1:=H2).
apply val_push_var; auto.
 split; trivial.
 apply varSAT.

 split.
 2:apply varSAT.
 unfold inX; rewrite <- H4; rewrite <- H0; trivial.
Qed.

  Lemma fx_eq_rec_call : forall e n x T U,
    ords e n = false ->
    fixs e n = Some T ->
    T <> kind ->
    typ (tenv e) (Ref n) (Prod (lift (S n) T) U) ->
    fx_equals e x ->
    typ (tenv e) x (lift (S n) T) ->
    fx_equals e (App (Ref n) x).
unfold fx_equals; intros.
simpl.
specialize H3 with (1:=H5).
rewrite <- H3.
destruct H5 as (Hty,(Hty',Hrec)).
specialize Hrec with n.
rewrite H in Hrec; rewrite H0 in Hrec.
apply Hrec.
red in H4; specialize H4 with (1:=Hty); trivial.
apply in_int_not_kind in H4; trivial.
2:destruct T;[discriminate|elim H1;reflexivity].
destruct H4 as (?,_ ).
unfold inX in H4.
unfold lift in H4; rewrite int_lift_rec_eq in H4.
rewrite V.lams0 in H4; trivial.
Qed.

  (* Covariance *)

  Lemma fx_equals_subval : forall e M, fx_equals e M -> fx_subval e M.
unfold fx_subval, fx_equals; intros.
apply H in H0.
rewrite <- H0; reflexivity.
Qed.

  Lemma fx_equals_sub : forall e M, fx_equals e M -> fx_sub e M.
unfold fx_sub, fx_equals; intros.
apply H in H0.
rewrite <- H0; trivial.
Qed.

  Lemma var_sub : forall e n,
    ords e n = true ->
    fx_subval e (Ref n).
unfold fx_subval; intros.
destruct H0 as (_,(_,H0)).
generalize (H0 n); rewrite H.
simpl; trivial.
Qed.

Lemma fx_sub_prod : forall e T U,
  T <> kind ->
  fx_equals e T ->
  fx_sub (push_var e T) U ->
  fx_sub e (Prod T U).
red; intros.
rewrite intProd_eq in H3|-*.
specialize (H0 _ _ _ _ H2).
destruct H3.
unfold inX in H3.
rewrite Real_prod in H4; trivial.
 unfold prod in H3; rewrite El_def in H3.
 assert (x ∈ El(prod (int T i') (fun x0 : X => int U (V.cons x0 i')))).
  unfold prod, inX; rewrite El_def.
  revert H3; apply cc_prod_covariant.
   do 2 red; intros.
   rewrite H5; reflexivity.

   rewrite H0; reflexivity.

   intros.
   red in H1.
   assert (val_mono (push_var e T) (V.cons x0 i) (I.cons daimon j) (V.cons x0 i') (I.cons daimon j')).
    apply val_push_var; auto with *.
    split; trivial; apply varSAT.
    split.
     rewrite <- H0; trivial.
     apply varSAT.
   specialize (H1 _ _ _ _ H5).
   red; intros.
   destruct H1 with z daimon; trivial.
   split; trivial.
   apply varSAT.
 split; trivial.
 rewrite Real_prod; trivial.
  unfold piSAT.
  revert H4; apply piSAT0_mono with (fun x=>x); intros; auto with *.
   rewrite H0; trivial.

   rewrite H0; reflexivity.

   red; intros.
   rewrite <- H0 in H4.
   apply H1 with (i:=V.cons x0 i) (j:=I.cons daimon j) (j':=I.cons daimon j').
    apply val_push_var; auto with *.
     split; trivial; apply varSAT.
     split.
      rewrite <- H0; trivial.
      apply varSAT.

     split; trivial.
     unfold inX; apply cc_prod_elim with (1:=H3); trivial.

  red; intros.
  rewrite H7; reflexivity.

 red; intros.
 rewrite H6; reflexivity.
Qed.

  Lemma NATi_sub : forall e o O,
    isOrd o ->
    typ (tenv e) O (Ordt o) ->
    fx_subval e O ->
    fx_sub e (NatI O).
unfold fx_sub, fx_subval; intros.
destruct tyord_inv with (2:=H0) (3:=proj1 H2); trivial.
destruct tyord_inv with (2:=H0) (3:=proj1 (proj2 H2)); trivial.
specialize H1 with (1:=H2).
rewrite realNati_def in H3|-*; trivial.
destruct H3.
split.
 revert H3; apply TI_mono; auto.

 rewrite <- fNATi_mono with (3:=H1); auto.
Qed.



  Lemma OSucc_sub : forall e O,
    fx_subval e O ->
    fx_subval e (OSucc O).
unfold fx_subval; simpl; intros.
unfold osucc.
red; intros.
rewrite subset_ax in H1 |-*.
destruct H1; split; auto.
revert H1; apply power_mono.
eauto.
Qed.

  (* Function subtyping *)

  Lemma fx_abs : forall e U T M,
    T <> kind ->
    fx_sub e T ->
    fx_equals (push_var e T) M ->
    typ (T::tenv e) M U ->
    U <> kind ->
    fx_extends e T (Abs T M).
unfold fx_sub, fx_equals, fx_extends; intros.
specialize H0 with (1:=H4).
simpl.
red; intros.
fold app.
rewrite beta_eq; try assumption.
 rewrite beta_eq.
  apply H1 with (I.cons daimon j) (I.cons daimon j').
  apply val_push_var; auto with *.
   split; [trivial|apply varSAT].

   split; [trivial|apply varSAT].
   destruct H0 with x daimon; trivial.
   split; [trivial|apply varSAT].

  red; red; intros.
  rewrite H7; reflexivity.

  apply H0 with (x:=x) (t:=daimon); trivial.
  split; [trivial|apply varSAT].

 red; red; intros.
 rewrite H7; reflexivity.
Qed.

(*
Lemma Natcase_fx_eq : forall o e O f1 f2 c,
  isOrd o ->
  typ (tenv e) O (Ord o) ->
  fx_sub e O ->
  fx_equals e f1 ->
  fx_equals (push_var e (NatI O)) f2 ->
  typ (tenv e) c (NatI (OSucc O)) ->
  fx_equals e c ->
  fx_equals e (Natcase f1 f2 c).
red; intros o e O f1 f2 c H tyO H0 H1 H2 tyc H3 i i' H4.
simpl.
assert (ord : isOrd (int O i)).
 destruct H4 as (H4,_); apply tyO in H4.
 apply isOrd_inv with o; trivial.
assert (ord' : isOrd (int O i')).
 destruct H4 as (_,(H4,_)); apply tyO in H4.
 apply isOrd_inv with o; trivial.
assert (int c i ∈ NATi (osucc (int O i))).
 destruct H4 as (H4,_).
 apply tyc in H4; trivial.
apply NATCASE_morph_gen; intros; auto.
 apply H3; trivial.

 apply H1; trivial.

 apply H2.
 red in H0; specialize H0 with (1:=H4).
 rewrite H6 in H5.
 apply SUCCi_inv_typ in H5; auto.
 apply val_push_var; simpl; auto.
 rewrite <- H7.
 clear H6 H7 x'; revert x H5.
 apply TI_mono; auto.
Qed.

*)

(*****************************************************************************)
(** Recursor (without case analysis) *)

(* NatFix O M is a fixpoint of domain Nati O with body M *)
Definition NatFix (O M:term) : term.
(*begin show*)
left.
exists (fun i =>
         NATREC (fun o' f => int M (V.cons f (V.cons o' i))) (int O i))
       (fun j => NATFIX (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j))))).
(*end show*)
 do 2 red; intros.
 apply NATREC_morph.
  do 2 red; intros.
  apply int_morph; auto with *.
  apply V.cons_morph; trivial.
  apply V.cons_morph; trivial.

  apply int_morph; auto with *.

 (* *)
 do 2 red; intros.
 rewrite H; reflexivity.

 (* *)
 red; intros.
 replace (Lc.lift_rec 1
     (NATFIX (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j))))) k) with
   (NATFIX (Lc.lift_rec 1 (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j)))) k)).
  simpl.
  f_equal.
  f_equal.
  rewrite <- tm_liftable.
  apply tm_morph; auto with *.
  rewrite <- Lc.ilift_binder_lift.
  apply Lc.ilift_morph.
  intros [|k']; simpl; trivial.
  apply tm_liftable.

  generalize  (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j)) )); intro.
  unfold NATFIX, FIXP; simpl.
  rewrite <- Lc.permute_lift.
  reflexivity.

 (* *)
 red; intros.
 replace (Lc.subst_rec u
     (NATFIX (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j))))) k) with
   (NATFIX (Lc.subst_rec u (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j)))) k)).
  simpl.
  f_equal.
  f_equal.
  rewrite <- tm_substitutive.
  apply tm_morph; auto with *.
  rewrite <- Lc.ilift_binder.
  apply Lc.ilift_morph.
  intros [|k']; simpl; trivial.
  apply tm_substitutive.

  generalize  (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j)))); intro.
  unfold NATFIX, FIXP; simpl.
  rewrite <- Lc.commut_lift_subst.
  reflexivity.
Defined.


(** Typing rules of NatFix *)

Section NatFixRules.

  Variable infty : set.
  Hypothesis infty_ord : isOrd infty.
  Variable E : fenv.
  Let e := tenv E.
  Variable O U M : term.
  Hypothesis M_nk : ~ eq_term M kind.
  Hypothesis ty_O : typ e O (Ordt infty).
  Hypothesis ty_M : typ (Prod (NatI (Ref 0)) U::OSucct O::e)
    M (Prod (NatI (OSucc (Ref 1)))
         (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U)))).

  Hypothesis stab : fx_extends
    (push_fun (push_ord E (OSucct O)) (NatI (Ref 0)) U)
    (NatI (OSucc (Ref 1)))
    M.

  Let F i := fun o' f => int M (V.cons f (V.cons o' i)).

  Lemma morph_fix_body : forall i, morph2 (F i).
unfold F; do 3 red; intros.
rewrite H; rewrite H0; reflexivity.
Qed.

  Lemma ext_fun_ty : forall o i,
    ext_fun (NATi o) (fun x => int U (V.cons x (V.cons o i))).
do 2 red; intros.
rewrite H0;reflexivity.
Qed.

  Hypothesis fx_sub_U :
    fx_sub (push_var (push_ord E (OSucct O)) (NatI (OSucc (Ref 0)))) U.

  Lemma ty_fix_body : forall i j o f,
   val_ok e i j ->
   o < osucc (int O i) ->
   f ∈ cc_prod (NATi o) (fun x => El(int U (V.cons x (V.cons o i)))) ->
   F i o f ∈
   cc_prod (NATi (osucc o)) (fun x => El(int U (V.cons x (V.cons (osucc o) i)))).
unfold F; intros.
destruct tyord_inv with (2:=ty_O) (3:=H); trivial.
red in ty_M.
assert (val_ok (Prod (NatI(Ref 0)) U::OSucct O::e)
  (V.cons f (V.cons o i)) (I.cons daimon (I.cons daimon j))).
 apply vcons_add_var; auto.
 3:discriminate.
  apply vcons_add_var; auto.
  2:discriminate.
  split;[|apply varSAT].
  unfold inX; simpl; rewrite El_def; trivial.

  split;[|apply varSAT].
  rewrite intProd_eq.
  unfold inX, prod; rewrite El_def.
  revert H1; apply eq_elim.
  apply cc_prod_ext.
   simpl; rewrite El_def; reflexivity.

   red; intros.
   rewrite H4; reflexivity.
specialize ty_M with (1:=H4).
apply in_int_not_kind in ty_M.
2:discriminate.
destruct ty_M as (?,_).
rewrite intProd_eq in H5; unfold inX in H5.
unfold prod in H5; rewrite El_def in H5.
revert H5; apply eq_elim.
symmetry; apply cc_prod_ext.
 simpl; rewrite El_def.
 reflexivity.

 red; intros.
 rewrite int_lift_rec_eq.
 rewrite int_subst_rec_eq.
 rewrite int_lift_rec_eq.
 apply El_morph; apply int_morph; auto with *.
 do 2 red.
 intros [|[|k]].
  compute; trivial.

  unfold V.lams, V.shift; simpl.
  reflexivity.

  unfold V.lams, V.shift; simpl.
  replace (k-0) with k; auto with *.
Qed.

  Lemma fix_body_irrel : forall i j,
    val_ok e i j ->
    NAT_ord_irrel (int O i) (F i) (fun o' x => El(int U (V.cons x (V.cons o' i)))).
red; red; intros.
assert (isOrd (int O i)).
 apply ty_O in H.
 apply isOrd_inv with infty; auto.
 apply in_int_not_kind in H;[|discriminate].
 destruct H; simpl in H.
 red in H; rewrite El_def in H; trivial.
red in stab.
assert (Hstab := stab (V.cons f (V.cons o i)) (V.cons g (V.cons o' i))).
simpl in Hstab.
red in Hstab.
eapply Hstab; clear Hstab; trivial.
2:rewrite El_def; auto.
apply val_push_fun.
 apply val_push_ord; auto.
  apply val_mono_refl; exact H.

  split;[|apply varSAT].
  red; simpl.
  rewrite El_def.
  apply ole_lts; trivial.
  transitivity o'; trivial.

  split;[|apply varSAT].
  red; simpl.
  rewrite El_def.
  apply ole_lts; trivial.

  discriminate.

 split;[|apply varSAT].
 red; simpl.
 unfold prod; rewrite El_def.
 revert H4; apply eq_elim; apply cc_prod_ext.
  rewrite El_def; reflexivity.

  red; intros.
  rewrite H9; reflexivity.

 split;[|apply varSAT].
 red; simpl.
 unfold prod; rewrite El_def.
 revert H5; apply eq_elim; apply cc_prod_ext.
  rewrite El_def; reflexivity.

  red; intros.
  rewrite H9; reflexivity.

 red; intros.
 simpl in H9; rewrite El_def in H9.
 auto.
Qed.

  Lemma val_mono_2 i j y y' n n':
    val_ok e i j ->
    isOrd (int O i) ->
    isOrd y ->
    isOrd y' ->
    y ⊆ y' ->
    y' ⊆ int O i ->
    n ∈ NATi y ->
    n == n' ->
    val_mono (push_var (push_ord E (OSucct O)) (NatI (OSucc (Ref 0))))
      (V.cons n (V.cons y i)) (I.cons daimon (I.cons daimon j))
      (V.cons n' (V.cons y' i)) (I.cons daimon (I.cons daimon j)).
Proof.
intros.
apply val_push_var; auto with *.
 4:discriminate.
 apply val_push_ord; auto with *.
  4:discriminate.
  apply val_mono_refl; trivial.

  split;[|apply varSAT].
  unfold inX; simpl; rewrite El_def; apply ole_lts; auto.
  transitivity y'; trivial.

  split;[|apply varSAT].
  unfold inX; simpl; rewrite El_def; apply ole_lts; auto.

 rewrite realNati_def.
 2:simpl; auto.
 split;[|apply varSAT].
 simpl.
 revert H5; apply TI_incl; auto with *.

 rewrite realNati_def.
 2:simpl; auto.
 split;[|apply varSAT].
 simpl.
 rewrite <- H6; revert H5; apply TI_incl; auto with *.
 apply isOrd_plump with y'; auto with *.
 apply lt_osucc; trivial.
Qed.


  Lemma fix_codom_mono : forall o o' x x' i j,
   val_ok e i j ->
   isOrd o' ->
   o' ⊆ int O i ->
   isOrd o ->
   o ⊆ o' ->
   x ∈ NATi o ->
   x == x' ->
   El (int U (V.cons x (V.cons o i))) ⊆ El(int U (V.cons x' (V.cons o' i))).
Proof.
intros.
red in fx_sub_U.
assert (val_mono (push_var (push_ord E (OSucct O)) (NatI(OSucc(Ref 0))))
  (V.cons x (V.cons o i)) (I.cons daimon (I.cons daimon j))
  (V.cons x' (V.cons o' i)) (I.cons daimon (I.cons daimon j))).
 apply val_mono_2; trivial.
 apply ty_O in H.
 apply in_int_not_kind in H;[|discriminate].
 destruct H; red in H; simpl in H.
 rewrite El_def in H.
 apply isOrd_inv with infty; auto.

red; intros.
apply fx_sub_U with (x:=z)(t:=daimon) in H6.
 destruct H6; trivial.

 split; trivial.
 apply varSAT.
Qed.
  Hint Resolve morph_fix_body ext_fun_ty ty_fix_body fix_codom_mono fix_body_irrel.


Let fix_typ o i j:
  val_ok e i j ->
  isOrd o ->
  isOrd (int O i) ->
  o ⊆ int O i ->
  NATREC (F i) o
   ∈ cc_prod (NATi o) (fun n => El (int U (V.cons n (V.cons o i)))).
intros.
eapply NATREC_wt with (U:=fun o n => El (int U (V.cons n (V.cons o i)))); trivial.
 intros.
 apply fix_codom_mono with (1:=H); trivial.
 transitivity o; trivial.

 intros; apply ty_fix_body with (1:=H); trivial.
 apply isOrd_plump with (int O i); auto.
  transitivity o; trivial.

  apply lt_osucc; trivial.

 red; intros; apply fix_body_irrel with (1:=H); trivial.
 transitivity o; trivial.
Qed.


  Lemma fix_irr i j o o' x :
    val_ok e i j ->
    isOrd o ->
    isOrd o' ->
    isOrd (int O i) ->
    o ⊆ o' ->
    o' ⊆ int O i ->
    x ∈ NATi o ->
    cc_app (NATREC (F i) o) x == cc_app (NATREC (F i) o') x.
intros.
apply NATREC_ord_irrel with 
  (ord:=int O i)
  (U:=fun o x => El (int U (V.cons x (V.cons o i)))); auto.
 intros.
 apply fix_codom_mono with (1:=H); trivial.

 intros; apply ty_fix_body with (1:=H); trivial.
 apply isOrd_plump with (int O i); auto.
 apply lt_osucc; trivial.

 red; intros; apply fix_body_irrel with (1:=H); trivial.
Qed.



Lemma fix_eqn : forall i j o n,
  val_ok e i j ->
  isOrd o ->
  isOrd (int O i) ->
  o ⊆ int O i ->
  n ∈ NATi (osucc o) ->
  cc_app (NATREC (F i) (osucc o)) n ==
  cc_app (int M (V.cons (NATREC (F i) o) (V.cons o i))) n.
intros.
unfold NATREC at 1.
rewrite REC_eq; auto with *.
apply cc_app_morph; auto with *.
apply incl_eq.
 red; intros.
 rewrite sup_ax in H4; auto with *.
 destruct H4.
 assert (xo : isOrd x) by eauto using isOrd_inv.
 assert (xle : x ⊆ o) by (apply olts_le; auto).
 assert (xle' : x ⊆ int O i) by (transitivity o; trivial).
 assert (F i x (REC (F i) x) ∈ 
         cc_prod (NATi (osucc x)) (fun n => El (int U (V.cons n (V.cons (osucc x) i))))).
  apply ty_fix_body with (1:=H); trivial.
   apply ole_lts; auto.

   apply fix_typ with (1:=H); trivial.
 assert (F i o (NATREC (F i) o) ∈ 
         cc_prod (NATi (osucc o)) (fun n => El (int U (V.cons n (V.cons (osucc o) i))))).
  apply ty_fix_body with (1:=H).
   apply ole_lts; trivial.

   apply fix_typ with (1:=H); trivial.
 rewrite cc_eta_eq with (1:=H6) in H5.
 unfold F at 1 in H7; rewrite cc_eta_eq with (1:=H7).
 rewrite cc_lam_def in H5|-*.
  destruct H5.
  destruct H8.
  exists x0.
   revert H5; apply TI_mono; auto with *.
   apply osucc_mono; auto.
  exists x1; trivial.
  revert H8; apply eq_elim.
  do 2 red in stab.
  apply stab with (I.cons daimon (I.cons daimon j)) (I.cons daimon (I.cons daimon j)).
   apply val_push_fun.
    apply val_push_ord; trivial.
     apply val_mono_refl; trivial.

     split;[|apply varSAT].
     unfold inX; simpl; rewrite El_def; apply ole_lts; auto.

     split;[|apply varSAT].
     unfold inX; simpl; rewrite El_def; apply ole_lts; auto.

     discriminate.

    split;[|apply varSAT].
    unfold inX,prod; rewrite El_def.
    eapply eq_elim.
    2:eapply fix_typ with (1:=H); auto.
    apply cc_prod_ext.
     simpl; rewrite El_def; reflexivity.

     red; intros.
     rewrite H10; reflexivity.

    split;[|apply varSAT].
    unfold inX,prod; rewrite El_def.
    eapply eq_elim.
    2:eapply fix_typ with (1:=H); auto.
    apply cc_prod_ext.
     simpl; rewrite El_def; reflexivity.

     red; intros.
     rewrite H10; reflexivity.

    red; intros.
    apply fix_irr with (1:=H); auto with *.
    simpl in H8; rewrite El_def in H8; trivial.

   simpl; rewrite El_def; trivial.

  do 2 red; intros; apply cc_app_morph; auto with *.
  do 2 red; intros; apply cc_app_morph; auto with *.

 apply sup_incl with (F:=fun o'=>F i o'(REC (F i) o')); auto with *.
 apply lt_osucc; trivial.
Qed.


Lemma nat_fix_eqn : forall i j,
  val_ok e i j ->
  NATREC (F i) (int O i) ==
  cc_lam (NATi (int O i))
    (fun x => cc_app (F i (int O i) (NATREC (F i) (int O i))) x).
intros.
destruct tyord_inv with (2:=ty_O) (3:=H); trivial.
apply NATREC_eqn with
  (ord:=int O i)
  (U:=fun o x => El (int U (V.cons x (V.cons o i)))); auto.
 intros.
 apply fix_codom_mono with (1:=H); trivial.

 intros; apply ty_fix_body with (1:=H); trivial.
 apply isOrd_plump with (int O i); auto.
 apply lt_osucc; trivial.

 red; intros; apply fix_body_irrel with (1:=H); trivial.
Qed.


(*
Lemma equiv_piSAT_piNAT o B B' f:
isOrd o ->
(forall n, n ∈ NATi o -> eqSAT (Real (B n) (f n)) (B' n)) ->
eqSAT (piSAT (mkTY (NATi o) cNAT) B f)
      (piNATi (fun n => prodSAT (cNAT n) (B' n)) o).
intros.
red; intro.
unfold piSAT, piNATi.
apply interSAT_morph.
split; intros.
 destruct x as (n,xty); simpl proj1_sig.
 simpl in xty; rewrite El_def in xty.
 exists (exist (fun n=>n ∈ NATi o) n xty); simpl proj1_sig.
 apply prodSAT_morph; auto.
 rewrite Real_def; auto with *.
 intros; apply fam_mrph; trivial.
 revert H1; apply NATi_NAT; simpl; auto.

 destruct y as (n,xty); simpl proj1_sig.
 assert (nty : n ∈ El (mkTY (NATi o) cNAT)).
  rewrite El_def; trivial.
 exists (exist (fun n=>n ∈ El(mkTY (NATi o) cNAT)) n nty); simpl proj1_sig.
 apply prodSAT_morph; auto.
 rewrite Real_def; auto with *.
 intros; apply fam_mrph; trivial.
 revert H1; apply NATi_NAT; simpl; auto.
Qed.
*)
(*
Lemma indexed_relation_equiv A B (R:B->B->Prop) (P P':A->Prop) (G G':A->B) :
  (forall x:A, P x <-> P' x) -> 
  (forall x:A, P x -> R (G x) (G' x)) ->
  indexed_relation R (fun x:sig P => G (proj1_sig x)) (fun x:sig P' => G' (proj1_sig x)).
split; intros (i,?); simpl.
 pose (p' := p).
 apply H in p'.
 exists (exist _ i p').
 simpl; auto.

 apply H in p.
 exists (exist _ i p); simpl; auto.
Qed.
*)
Lemma typ_nat_fix :
  typ e (NatFix O M) (Prod (NatI O) (subst_rec O 1 U)).
red; intros.
destruct tyord_inv with (2:=ty_O)(3:=H); trivial.
apply in_int_intro.
discriminate.
discriminate.
assert (int (NatFix O M) i ∈ El(int (Prod (NatI O) (subst_rec O 1 U)) i)).
 rewrite intProd_eq.
 eapply eq_elim.
 2:simpl.
 2:apply fix_typ with (1:=H); auto with *.
 unfold prod; rewrite El_def; apply cc_prod_ext.
  simpl; rewrite El_def; auto with *.

  red; intros.
  rewrite int_subst_rec_eq.
  apply El_morph.
  apply int_morph; auto with *.
  intros [|[|k]]; try reflexivity.
  exact H3.
split; trivial.
rewrite intProd_eq.
rewrite Real_prod; trivial.
2:red; intros ? ? ? eqn; rewrite eqn; reflexivity.
simpl tm.
unfold piSAT.
cut (inSAT (NATFIX (Lc.Abs (tm M (Lc.ilift (I.cons (tm O j) j)))))
       (piSAT0 (fun n => n ∈ NATi (int O i)) (fNATi (int O i))
          (fun n =>Real (int U (V.cons n (V.cons (int O i) i)))
                    (cc_app (NATREC (F i) (int O i)) n)))).
 apply piSAT0_morph; intros; auto with *.
  red; intros; simpl; rewrite El_def; reflexivity.

  simpl; rewrite Real_def; trivial.
   reflexivity.

   intros.
   rewrite H6; reflexivity.

  apply Real_morph; [|reflexivity].
  rewrite int_subst_rec_eq.
  apply int_morph; auto with *.
  intros [|[|k]]; reflexivity.

apply NATFIX_sat with (X:=fun o n => Real (int U (V.cons n (V.cons o i)))
   (cc_app (NATREC (F i) o) n)); trivial.
 red; intros.
 red in fx_sub_U.
 apply fx_sub_U with (V.cons n (V.cons y i))
    (I.cons daimon (I.cons daimon j)) (I.cons daimon (I.cons daimon j)).
  apply val_mono_2; auto with *.
  rewrite <- fix_irr with (1:=H) (o:=y); auto.
  split; trivial.
  unfold inX.
  apply cc_prod_elim with (dom:=NATi y) (F:=fun n=>El(int U (V.cons n (V.cons y i)))); trivial.
  apply fix_typ with (1:=H); trivial.
  transitivity y'; trivial.

 (* sat body *)
 apply piSAT0_intro'.
 2:exists (int O i); auto.
 2:apply lt_osucc; auto.
 intros o' v tyo' ?.
 apply inSAT_exp;[right;apply sat_sn in H3;trivial|].
 cbv zeta.
 assert (val_ok (Prod (NatI(Ref 0)) U::OSucct O::e)
    (V.cons (NATREC (F i) o') (V.cons o' i)) (I.cons v (I.cons (tm O j) j))).
  apply vcons_add_var.
   3:discriminate.
   apply vcons_add_var; trivial.
   2:discriminate.
   split.
    unfold inX; simpl; rewrite El_def; trivial.

    simpl int; rewrite Real_def; auto with *.
    apply ty_O in H.
    apply in_int_sn in H; trivial.

   rewrite intProd_eq.
   assert (NATREC (F i) o' ∈ cc_prod (NATi o')
             (fun x => El(int U(V.cons x(V.cons o' i))))).
    apply fix_typ with (1:=H); trivial.
     eauto using isOrd_inv.
     apply olts_le in tyo'; trivial.
   split.
    unfold inX, prod; rewrite El_def.
    revert H4; apply eq_elim; apply cc_prod_ext.
     simpl; rewrite El_def; reflexivity.

     red; intros.
     rewrite H5; reflexivity.

    rewrite Real_prod.
     revert H3; apply piSAT0_morph; intros; auto with *.
      red; simpl; intros; rewrite El_def; auto.

      simpl.
      rewrite Real_def; auto with *.
      intros ? ? ? eqn; rewrite eqn; reflexivity.

     red; intros.
     rewrite H6; reflexivity.

     eapply eq_elim.
     2:apply fix_typ with (1:=H); auto with *.
     2:   eauto using isOrd_inv.
     2:   apply olts_le; trivial.
     unfold prod; rewrite El_def; apply cc_prod_ext.
      simpl; rewrite El_def; auto with *.

      red; intros.
      rewrite H6; reflexivity.

  red in ty_M; specialize ty_M with (1:=H4).
  apply in_int_not_kind in ty_M.
  2:discriminate.
  destruct ty_M.
  replace (Lc.subst v (tm M (Lc.ilift (I.cons (tm O j) j))))
     with (tm M (I.cons v (I.cons (tm O j) j))).
   rewrite intProd_eq in H6.
   rewrite Real_prod in H6; trivial.
    revert H6; apply piSAT0_morph; intros; auto with *.
     red; simpl; intros.
     rewrite El_def; reflexivity.

     simpl.
     rewrite Real_def; trivial.
      reflexivity.

      intros ? ? ? eqn; rewrite eqn; reflexivity.

     apply Real_morph.
      rewrite int_lift_rec_eq.
      rewrite int_subst_rec_eq.
      rewrite int_lift_rec_eq.
      apply int_morph; auto with *.
      intros [|[|k]]; try reflexivity.
      compute; fold minus.
      replace (k-0) with k; auto with *.

      apply fix_eqn with (1:=H); auto.
       eauto using isOrd_inv.
       apply olts_le; trivial.

    red; intros.
    rewrite H8; reflexivity.

   unfold Lc.subst; rewrite <- tm_substitutive.
   apply tm_morph; auto with *.
   intros [|[|k]].
    unfold Lc.ilift,I.cons; simpl.
    rewrite Lc.lift0; trivial.

    unfold Lc.ilift,I.cons; simpl.
    rewrite Lc.simpl_subst; trivial.
    rewrite Lc.lift0; trivial.

    unfold Lc.ilift,I.cons; simpl.
    rewrite Lc.simpl_subst; trivial.
    rewrite Lc.lift0; trivial.
Qed.


Lemma nat_fix_eq : forall N,
  typ e N (NatI O) ->
  eq_typ e (App (NatFix O M) N)
           (App (subst O (subst (lift 1 (NatFix O M)) M)) N).
red; intros.
unfold eqX.
change
 (app (NATREC (F i) (int O i)) (int N i) ==
  app (int (subst O (subst (lift 1 (NatFix O M)) M)) i) (int N i)).
do 2 rewrite <- int_subst_eq.
rewrite int_cons_lift_eq.
rewrite nat_fix_eqn with (1:=H0); trivial.
rewrite cc_beta_eq.
 reflexivity.

 do 2 red; intros.
 rewrite H2; reflexivity.

 red in H; specialize H with (1:=H0).
 apply in_int_not_kind in H.
  destruct H.
  unfold inX in H; simpl in H; rewrite El_def in H; trivial.

  discriminate.
Qed.

Lemma nat_fix_extend :
  fx_subval E O ->
  fx_extends E (NatI O) (NatFix O M).
intro subO.
do 2 red; intros.
simpl in H0; rewrite El_def in H0.
assert (isval := proj1 H).
assert (isval' := proj1 (proj2 H)).
assert (oo: isOrd (int O i)).
 destruct tyord_inv with (2:=ty_O) (3:=isval); trivial.
assert (oo': isOrd (int O i')).
 destruct tyord_inv with (2:=ty_O) (3:=isval'); trivial.
assert (inclo: int O i ⊆ int O i').
 apply subO in H; trivial.
clear subO.
change (cc_app (NATREC (F i) (int O i)) x == cc_app (NATREC (F i') (int O i')) x).
revert x H0.
elim oo using isOrd_ind; intros.
apply TI_elim in H3; auto.
destruct H3 as (o',?,?).
assert (o_o' : isOrd o') by eauto using isOrd_inv.
rewrite <- TI_mono_succ in H4; auto with *.
rewrite <- fix_irr with (1:=isval) (o:=osucc o'); auto.
 rewrite fix_eqn with (1:=isval); auto.
 rewrite <- fix_irr with (1:=isval') (o:=osucc o'); auto with *.
  rewrite fix_eqn with (1:=isval'); auto.
  do 2 red in stab.
  apply stab with (I.cons daimon (I.cons daimon j)) (I.cons daimon (I.cons daimon j')).
   apply val_push_fun.
    apply val_push_ord; auto with *.
     split;[|apply varSAT].
     unfold inX; simpl; rewrite El_def; apply ole_lts; auto.

     split;[|apply varSAT].
     unfold inX; simpl; rewrite El_def; apply ole_lts; auto.

     discriminate.

    split;[|apply varSAT].
    unfold inX,prod; rewrite El_def.
    eapply eq_elim.
    2:eapply fix_typ with (1:=isval); auto.
    apply cc_prod_ext.
     simpl; rewrite El_def; reflexivity.

     red; intros.
     rewrite H6; reflexivity.

    split;[|apply varSAT].
    unfold inX,prod; rewrite El_def.
    eapply eq_elim.
    2:eapply fix_typ with (1:=isval'); auto.
    apply cc_prod_ext.
     simpl; rewrite El_def; reflexivity.

     red; intros.
     rewrite H6; reflexivity.

    red; intros.
    simpl in H5; rewrite El_def in H5.
    rewrite fix_irr with (1:=isval') (o':=int O i'); auto with *.


   simpl; rewrite El_def; trivial.

  red; intros.
  apply inclo; apply H1.
  apply le_lt_trans with o'; trivial.

 red; intros.
 apply le_lt_trans with o'; trivial.
Qed.

Lemma nat_fix_equals :
  fx_equals E O ->
  fx_equals E (NatFix O M).
red; intros.
assert (fxs: fx_subval E O).
 apply fx_equals_subval; trivial.
apply nat_fix_extend in fxs.
red in fxs.
specialize fxs with (1:=H0).
apply fcompat_typ_eq with (3:=fxs).
 eapply cc_prod_is_cc_fun.
 assert (h := typ_nat_fix _ _ (proj1 H0)).
 apply in_int_not_kind in h.
 2:discriminate.
 destruct h.
 rewrite intProd_eq in H1.
 unfold inX, prod in H1; rewrite El_def in H1.
 eexact H1.

 setoid_replace (int (NatI O) i) with (int (NatI O) i').
  eapply cc_prod_is_cc_fun.
  assert (h := typ_nat_fix _ _ (proj1 (proj2 H0))).
  apply in_int_not_kind in h.
  2:discriminate.
  destruct h.
  rewrite intProd_eq in H1.
  unfold inX, prod in H1; rewrite El_def in H1.
  eexact H1.

  do 2 red.
  assert (h:= H _ _ _ _ H0).
  apply mkTY_ext.
   rewrite h; reflexivity.

   intros; apply fNATi_morph; trivial.
Qed.

End NatFixRules.

Print Assumptions typ_nat_fix.


Lemma typ_nat_fix' : forall infty e O U M T,
       T <> kind ->
       isOrd infty ->
       typ e O (Ordt infty) ->
       typ (Prod (NatI (Ref 0)) U :: OSucct O :: e) M
         (Prod (NatI (OSucc (Ref 1)))
           (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U)))) ->
       fx_extends (push_fun (push_ord (tinj e) (OSucct O)) (NatI (Ref 0)) U)
         (NatI (OSucc (Ref 1))) M ->
       fx_sub (push_var (push_ord (tinj e) (OSucct O)) (NatI (OSucc (Ref 0)))) U ->
       sub_typ e (Prod (NatI O) (subst_rec O 1 U)) T ->
       typ e (NatFix O M) T.
intros.
apply typ_subsumption with (Prod (NatI O) (subst_rec O 1 U)); auto.
2:discriminate.
change e with (tenv (tinj e)).
apply typ_nat_fix with (infty:=infty); trivial.
Qed.

(****************************************************************************************)
(** Compound judgements : typing + variance *)

Definition typ_ext e M A B :=
  fx_extends e A M /\ typ (tenv e) M (Prod A B).

Definition typ_mono e M :=
  fx_sub e M /\ typs (tenv e) M.

Definition typ_monoval e M T :=
  fx_subval e M /\ typ (tenv e) M T.

Definition typ_impl e M T :=
  fx_equals e M /\ typ (tenv e) M T.

Instance typ_impl_morph e : Proper (eq_term ==> eq_term ==> iff) (typ_impl e).
apply morph_impl_iff2; auto with *.
do 4 red; intros.
destruct H1; split.
 red; intros.
 rewrite <- H; eauto.

 rewrite <- H; rewrite <- H0; eauto.
Qed.

Lemma typ_var_impl : forall e n t T,
    spec_var e n = false ->
    nth_error (tenv e) n = value t ->
    t <> kind ->
    T <> kind ->
    sub_typ (tenv e) (lift (S n) t) T ->
    typ_impl e (Ref n) T.
intros.
split.
 apply fx_eq_noc; apply noc_var; trivial.

 apply typ_subsumption with (lift (S n) t); trivial.
  apply typ_var; trivial.

  destruct t as [(t,tm)|]; simpl in *; auto.
  discriminate.
Qed.

  Lemma impl_abs : forall e s1 U T T' M,
    T <> kind ->
    U <> kind ->
    s1=prop \/ s1=kind ->
    eq_typ (tenv e) T T' ->
    typ_impl e T s1 ->
    typ_impl (push_var e T) M U ->
    typ_impl e (Abs T M) (Prod T' U).
intros.
destruct H3; destruct H4.
split.
 apply fx_eq_abs; trivial.

 apply typ_conv with (Prod T U); auto.
  apply typ_abs; trivial.
  destruct H1; subst s1; red; auto.

  apply eq_typ_prod; trivial.
  reflexivity.

  discriminate.

  discriminate.
Qed.

Lemma impl_app : forall e u v V Ur T,
  T <> kind ->
  V <> kind ->
  Ur <> kind ->
  sub_typ (tenv e) (subst v Ur) T ->
  typ_impl e u (Prod V Ur) ->
  typ_impl e v V ->
  typ_impl e (App u v) T.
intros.
destruct H3.
destruct H4.
split.
 apply fx_eq_app; trivial.

 apply typ_subsumption with (subst v Ur); trivial.
  apply typ_app with V; auto.

  destruct Ur as [(Ur,Urm)|]; simpl; trivial.
  discriminate.
Qed.

  Lemma NATi_fx_sub : forall e o O,
    isOrd o ->
    typ_monoval e O (Ordt o) ->
    fx_sub e (NatI O).
destruct 2.
apply NATi_sub with (o:=o); trivial.
Qed.

  Lemma OSucc_fx_sub : forall e O o,
    isOrd o ->
    typ_monoval e O (Ordt o)->
    typ_monoval e (OSucc O) (Ordt (osucc o)).
destruct 2.
split.
 apply OSucc_sub; trivial.

 red; simpl; intros.
 apply in_int_intro; try discriminate.
 assert (osucc (int O i) ∈ El (int (Ordt (osucc o)) i)).
  simpl; rewrite El_def.
  apply lt_osucc_compat; trivial.
  destruct tyord_inv with (2:=H1)(3:=H2) as (_,(?,_)); trivial.
 split; trivial.
 unfold int at 1, Ordt, cst, iint.
 rewrite Real_def; auto with *.
  assert (h:= H1 _ _ H2).
  apply in_int_sn in h.
  simpl; trivial.

  simpl.
  apply lt_osucc_compat; trivial.
  destruct tyord_inv with (2:=H1)(3:=H2) as (_,(?,_)); trivial.
Qed.

  Lemma typ_var_mono : forall e n t T,
    ords e n = true ->
    nth_error (tenv e) n = value t ->
    T <> kind ->
    t <> kind ->
    sub_typ (tenv e) (lift (S n) t) T ->
    typ_monoval e (Ref n) T.
intros.
split.
 apply var_sub; trivial.

 apply typ_subsumption with (lift (S n) t); trivial.
  apply typ_var; trivial.

  destruct t as [(t,tm)|]; simpl in *; auto.
  discriminate.
Qed.

  Lemma ext_abs : forall e U T M,
    T <> kind ->
    U <> kind ->
    typ_mono e T ->
    typ_impl (push_var e T) M U ->
    typ_ext e (Abs T M) T U.
intros.
destruct H1; destruct H2; split.
 apply fx_abs with U; trivial.

 apply typ_abs; trivial.
Qed.

(*************)
(*
Lemma impl_natcase : forall o e O P fZ fS n T,
       isOrd o ->
       typ_mono e O (Ordt o) ->
       sub_typ (tenv e) (App P n) T -> 
       typ_impl e fZ (App P Zero) ->
       typ_impl (push_var e (NatI O)) fS
         (App (lift 1 P) (App (Succ (lift 1 O)) (Ref 0))) ->
       typ_impl e n (NatI (OSucc O)) ->
       typ_impl e (Natcase fZ fS n) T.
intros.
destruct H0.
destruct H2.
destruct H3.
simpl in H7.
destruct H4.
split.
 apply Natcase_fx_eq with o O; trivial.

 apply typ_natcase' with o O P; trivial.
Qed.
*)

  Lemma impl_call : forall e n x t u T,
    ords e n = false ->
    fixs e n = Some t ->
    T <> kind ->
    t <> kind ->
    u <> kind ->
    nth_error (tenv e) n = value (Prod t u) ->
    sub_typ (tenv e) (subst x (lift_rec (S n) 1 u)) T ->
    typ_impl e x (lift (S n) t) ->
    typ_impl e (App (Ref n) x) T.
intros.
destruct H6.
assert (typ (tenv e) (Ref n) (Prod (lift (S n) t) (lift_rec (S n) 1 u))).
 apply typ_var0; rewrite H4; split;[discriminate|].
 apply sub_refl.

 unfold lift; rewrite red_lift_prod.
 reflexivity.
split.
 apply fx_eq_rec_call with t (lift_rec (S n) 1 u); trivial.

 apply typ_subsumption with (subst x (lift_rec (S n) 1 u)); auto.
 2:destruct u as [(u,um)|]; trivial.
 2:discriminate.
 apply typ_app with (lift (S n) t); trivial.
 destruct t as [(t,tm)|]; trivial.
 discriminate.
 destruct u as [(u,um)|]; trivial.
 discriminate.
Qed.


Lemma typ_nat_fix'' : forall infty e O U M T,
       isOrd infty ->
       T <> kind ->
       sub_typ (tenv e) (Prod (NatI O) (subst_rec O 1 U)) T ->
       typ (tenv e) O (Ordt infty) ->
       typ_mono (push_var (push_ord e (OSucct O)) (NatI (OSucc (Ref 0)))) U ->
       typ_ext (push_fun (push_ord e (OSucct O)) (NatI (Ref 0)) U)
         M (NatI (OSucc (Ref 1)))
           (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
       typ (tenv e) (NatFix O M) T.
intros.
destruct H3; destruct H4.
apply typ_subsumption with (2:=H1); trivial.
2:discriminate.
apply typ_nat_fix with infty; trivial.
Qed.

  Lemma typ_ext_fix : forall eps e O U M,
    isOrd eps ->
    typ_monoval e O (Ordt eps) ->
    typ_ext (push_fun (push_ord e (OSucct O)) (NatI (Ref 0)) U) M
      (NatI (OSucc (Ref 1))) (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    fx_sub (push_var (push_ord e (OSucct O)) (NatI (OSucc (Ref 0)))) U ->
    typ_ext e (NatFix O M) (NatI O) (subst_rec O 1 U).
intros eps e O U M eps_ord tyO tyM tyU.
destruct tyO as (inclO,tyO).
destruct tyM as (extM,tyM).
assert (tyF: typ (tenv e) (NatFix O M) (Prod (NatI O) (subst_rec O 1 U))).
 apply typ_nat_fix with eps; trivial.
split; trivial.
apply nat_fix_extend with eps U; trivial.
Qed.

  Lemma typ_impl_fix : forall eps e O U M,
    isOrd eps ->
    typ_impl e O (Ordt eps) ->
    typ_ext (push_fun (push_ord e (OSucct O)) (NatI (Ref 0)) U) M
      (NatI (OSucc (Ref 1))) (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    fx_sub (push_var (push_ord e (OSucct O)) (NatI (OSucc (Ref 0)))) U ->
    typ_impl e (NatFix O M) (Prod (NatI O) (subst_rec O 1 U)).
intros eps e O U M eps_ord tyO tyM tyU.
destruct tyO as (inclO,tyO).
destruct tyM as (extM,tyM).
assert (tyF: typ (tenv e) (NatFix O M) (Prod (NatI O) (subst_rec O 1 U))).
 apply typ_nat_fix with eps; trivial.
split; trivial.
apply nat_fix_equals with eps U; trivial.
Qed.


(*
(************************************************************************)
(** Two examples of derived principles:
    - the standard recursor for Nat
    - subtraction with size information
*)
Section Example.

Definition nat_ind_typ :=
   Prod (Prod (NatI (Ord omega)) prop) (* P : nat -> Prop *)
  (Prod (App (Ref 0) Zero)
  (Prod (Prod (NatI (Ord omega)) (Prod (App (Ref 2) (Ref 0))
                        (App (Ref 3) (App (Succ (Ord omega)) (Ref 1)))))
  (Prod (NatI (Ord omega)) (App (Ref 3) (Ref 0))))).

Definition nat_ind :=
   Abs (*P*)(Prod (NatI (Ord omega)) prop) (* P : nat -> Prop *)
  (Abs (*fZ*) (App (Ref 0) Zero)
  (Abs (*fS*) (Prod (*n*)(NatI (Ord omega)) (Prod (App (Ref 2) (Ref 0))
                                   (App (Ref 3) (App (Succ (Ord omega)) (Ref 1)))))
  (NatFix (Ord omega)
    (*o,Hrec*)
    (Abs (*n*)(NatI (OSucc (Ref 1)))
      (Natcase
        (Ref 4)
        (*k*)(App (App (Ref 4) (Ref 0))
                  (App (Ref 2) (Ref 0)))
        (Ref 0)))))).



Lemma nat_ind_def :
  forall e, typ e nat_ind nat_ind_typ.
assert (eq_term Nat (NatI (Ord omega))).
 red; simpl.
 red; unfold NAT; reflexivity.
unfold nat_ind, nat_ind_typ; intros.
apply typ_abs; try discriminate.
apply typ_abs; try discriminate.
apply typ_abs; try discriminate.

set (E0 := Prod (NatI (Ord omega))
                 (Prod (App (Ref 2) (Ref 0))
                    (App (Ref 3) (App (SuccI (Ord omega)) (Ref 1))))
               :: App (Ref 0) Zero :: Prod (NatI (Ord omega)) prop :: e) in |-*.
change E0 with (tenv (tinj E0)).
apply typ_nat_fix'' with (osucc omega) (App (Ref 4) (Ref 0)); auto.
 (* sub *)
 apply sub_refl.
 apply eq_typ_prod.
  reflexivity.

  eapply eq_typ_morph;[reflexivity| |reflexivity].
  simpl; do 2 red; simpl; intros.
  unfold V.lams, V.shift; simpl.
  apply cc_app_morph; apply H0.

 (* ord *)
 red; simpl; intros.
 apply lt_osucc; trivial.

 (* codom mono *)
 split.
  apply fx_equals_sub.
  apply fx_eq_noc.
  apply noc_app.
   apply noc_var; reflexivity.
   apply noc_var; reflexivity.

  red; intros; simpl; exact I.

 (* fix body *)
 apply ext_abs; try discriminate.
  apply NATi_fx_sub with (o:=osucc (osucc omega)); auto.
  apply OSucc_fx_sub; auto.
  apply typ_var_mono with (OSucct (Ord omega)); auto; try discriminate.
  red; simpl; intros; trivial.

  apply impl_natcase with (osucc omega) (Ref 2) (Ref 5); auto.
   eapply typ_var_mono.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.

    simpl tenv; apply sub_refl.
    red; simpl; intros; reflexivity.

   simpl tenv.
   apply sub_refl.
   red; simpl; intros.
   unfold V.lams, V.shift; simpl.
   reflexivity.

   (* branch 0 *)
   eapply typ_var_impl.
    compute; reflexivity.
    simpl nth_error.
    reflexivity.
    discriminate.

    apply sub_refl; red; simpl; intros.
    unfold V.lams, V.shift; simpl.
    reflexivity.

   (* branch S *)
   apply impl_app with (App (Ref 6) (Ref 0))
     (App (Ref 7) (App (SuccI (Ref 4)) (Ref 1))); try discriminate.
    simpl tenv.
    apply sub_refl; red; intros; simpl.
    unfold V.lams, V.shift; simpl.
    reflexivity.

    apply impl_app with (NatI (Ord omega))
      (Prod (App (Ref 7) (Ref 0)) (App (Ref 8) (App (SuccI (Ord omega)) (Ref 1))));
      try discriminate.
     simpl tenv.
     unfold subst; rewrite eq_subst_prod.
     apply sub_typ_covariant.
      red; simpl; intros; reflexivity.

     apply sub_refl.
     red; intros; simpl.
     apply cc_app_morph; [reflexivity|].
     assert (i 1 ∈ NATi (i 4)).
      generalize (H0 1 _ (eq_refl _)); simpl.
      unfold V.lams, V.shift; simpl.
      trivial.
     rewrite beta_eq.
      rewrite beta_eq; auto with *.
       reflexivity.
       red; intros; apply inr_morph; trivial.

      red; intros; apply inr_morph; trivial.

      apply NATi_NAT in H1; trivial.
      generalize (H0 4 _ (eq_refl _)); simpl; intro.
      apply isOrd_inv with (osucc omega); auto.

     eapply typ_var_impl.
      compute; reflexivity.
      simpl; reflexivity.
      discriminate.

      apply sub_refl.
      red; intros; simpl.
      unfold V.lams, V.shift; simpl.
      reflexivity.

     eapply typ_var_impl.
      compute; reflexivity.
      simpl; reflexivity.
      discriminate.

      red; intros; simpl.
      simpl in H1.
      unfold V.lams, V.shift in H1; simpl in H1.
      apply NATi_NAT in H1; trivial.
      generalize (H0 3 _ (eq_refl _)); simpl; intro.
      apply isOrd_inv with (osucc omega); auto.

    eapply impl_call.
     compute; trivial.
     simpl; reflexivity.
     discriminate.
     2:simpl; reflexivity.
     discriminate.

     apply sub_refl; red; intros; simpl.
     unfold V.lams, V.shift; simpl.
     reflexivity.

     eapply typ_var_impl.
      compute; reflexivity.
      simpl; reflexivity.
      discriminate.

      apply sub_refl; red; intros; simpl.
      reflexivity.

   (* Scrutinee *)
   eapply typ_var_impl.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.

    apply sub_refl; red; intros; simpl.
    reflexivity.
Qed.


(* Subtraction *)

Definition minus O :=
  NatFix O
    (*o,Hrec*)
    (Abs (*n*) (NatI (OSucc (Ref 1)))
    (Abs (*m*) (NatI (Ord omega))
    (Natcase
       Zero
       (*n'*)
       (Natcase
         (Ref 2)
         (*m'*)
         (App (App (Ref 4) (Ref 1)) (Ref 0))
         (Ref 1))
       (Ref 1)))).

Definition minus_typ O := Prod (NatI O) (Prod (NatI (Ord omega)) (NatI (lift 2 O))).



Lemma minus_def :
  forall e infty O,
  isOrd infty ->
  typ e O (Ord infty) ->
  typ e (minus O) (minus_typ O).
intros.
unfold minus, minus_typ.
change e with (tenv (tinj e)).
apply typ_nat_fix'' with infty (Prod (NatI (Ord omega)) (NatI (Ref 2))); auto.
 (* sub *)
 apply sub_refl.
 apply eq_typ_prod.
  reflexivity.

  rewrite eq_subst_prod.
  apply eq_typ_prod.
   red; intros; simpl; reflexivity.

   red; intros; simpl.
   unfold lift; rewrite int_lift_rec_eq.
   rewrite V.lams0.
   unfold V.lams, V.shift; simpl; reflexivity.

 (* codom mono *)
 split;[|red; intros; simpl; exact I].
 apply fx_sub_prod.
  apply fx_eq_noc.
  red; simpl; reflexivity.

  apply NATi_sub with infty; trivial.
  simpl.
  apply typ_var0; split; [discriminate|].
  red; intros; simpl.
  unfold lift in H2; rewrite int_lift_rec_eq in H2.
  rewrite V.lams0 in H2.
  simpl in H2.
  apply le_lt_trans with (2:=H2); trivial.
  apply H0.
  red; intros.
  generalize (H1 (3+n) _ H3).
  destruct T as [(T,Tm)|]; simpl; trivial.

  apply var_sub.
  compute; reflexivity.

 (* fix body *)
 apply ext_abs; try discriminate.
  apply NATi_fx_sub with (o:=osucc infty); auto.
  apply OSucc_fx_sub; auto.
  eapply typ_var_mono.
   compute; reflexivity.
   simpl; reflexivity.
   discriminate.
  red; simpl; intros; trivial.
  apply weakening0 in H0; apply weakeningS with (A:=OSucct O) in H0.
  apply weakeningS with (A:=Prod(NatI(Ref 0))(Prod(NatI(Ord omega))(NatI(Ref 2)))) in H0.
  apply H0 in H1.
  simpl in H1.
  unfold lift in H1; rewrite int_lift_rec_eq in H1.
  apply le_lt_trans with (3:=H1); trivial.

 rewrite eq_lift_prod.
 rewrite eq_subst_prod.
 unfold lift1; rewrite eq_lift_prod.
 apply impl_abs.
  discriminate.

  red; intros; simpl.
  reflexivity.

  red; intros; simpl; auto with *.

 match goal with |- typ_impl ?e _ _ => set (E:=e) end.
 assert (typ_impl E (Ref 1) (NatI (OSucc (Ref 3)))).
  eapply typ_var_impl.
   compute; reflexivity.
   simpl; reflexivity.
   discriminate.
  apply sub_refl.
  red; intros; simpl; reflexivity.
 apply impl_natcase with infty (Ref 3)
    (Abs (NatI (OSucc (Ref 3))) (NatI (OSucc (Ref 4)))); auto.
  Focus 2.
  apply sub_refl.
  rewrite eq_typ_betar.
  3:discriminate.
   red; intros; simpl.
   unfold V.lams, V.shift; simpl.
   reflexivity.

   apply H1.

  (* ord *)
  eapply typ_var_mono.
   compute;reflexivity.
   simpl; reflexivity.
   discriminate.
  red; intros; simpl.
  unfold lift in H3; rewrite int_lift_rec_eq in H3.
  rewrite V.lams0 in H3.
  simpl in H3.
  apply le_lt_trans with (2:=H3); trivial.
  apply H0.
  red; intros.
  generalize (H2 (4+n) _ H4).
  destruct T as [(T,Tm)|]; simpl; auto.

  (* branch 0 *)
  split.
   red; intros; simpl; reflexivity.
  assert (tyz : typ (tenv E) Zero (NatI (OSucc (Ref 3)))).
    apply typ_Zero with infty; trivial.
    apply typ_var0; split; [discriminate|].
    red; intros; simpl.
    unfold lift in H3; rewrite int_lift_rec_eq in H3.
    rewrite V.lams0 in H3.
    simpl in H3.
    apply le_lt_trans with (2:=H3); trivial.
    apply H0.
    red; intros.
    generalize (H2 (4+n) _ H4).
    destruct T as [(T,Tm)|]; simpl; trivial.
  apply typ_conv with (NatI (OSucc (Ref 3))); trivial.
  2:discriminate.
  rewrite eq_typ_betar; trivial.
  2:discriminate.
  red; intros; simpl.
  reflexivity.

  (* branch S *)
  assert (typ_impl (push_var E (NatI (Ref 3))) (Ref 1) (NatI (Ord (osucc omega)))).
   eapply typ_var_impl.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.
   apply sub_refl.
   red; intros; simpl.
   unfold NATi at 2; rewrite TI_mono_succ; auto.
   apply NAT_eq.
  apply impl_natcase with (osucc omega) (Ord omega)
     (Abs (NatI (OSucct (Ord omega))) (NatI (OSucc (Ref 5)))); auto.
   Focus 2.
   apply sub_refl.
   rewrite eq_typ_betar.
   3:discriminate.
    unfold lift; rewrite eq_lift_abs.
    rewrite eq_typ_betar.
    3:discriminate.
     red; intros; simpl; reflexivity.
     apply typ_conv with (NatI (OSucc (lift_rec 1 0 (Ref 3)))).
     3:discriminate.
      apply typ_SuccI with (o:=infty); trivial.
      apply typ_var0; split;[discriminate|].
      red; intros; simpl.
      unfold lift in H4; rewrite int_lift_rec_eq in H4.
      rewrite V.lams0 in H4.
      simpl in H4.
      apply le_lt_trans with (2:=H4); trivial.
      apply H0.
      red; intros.
      generalize (H3 (5+n) _ H5).
      destruct T as [(T,Tm)|]; simpl; trivial.

      apply typ_var0; split;[discriminate|].
      apply sub_refl; red; intros; simpl.
      reflexivity.

     red; intros; simpl.
     reflexivity.

     apply H2.

   (* ord *)
   split.
    red; intros; simpl; reflexivity.

    red; intros; simpl.
    apply lt_osucc; trivial.

  (* branch 0 *)
  eapply typ_var_impl.
   compute; reflexivity.
   simpl; reflexivity.
   discriminate.
  apply sub_refl.
  rewrite eq_typ_betar.
  3:discriminate.
   red; intros; simpl.
   unfold V.lams, V.shift; simpl; reflexivity.

   eapply typ_Zero with (osucc omega); auto.
   red; intros; simpl.
   apply lt_osucc; trivial.

  (* branch S *)    
  apply impl_app with (NatI (Ord omega)) (NatI (OSucc (Ref 6))).
   discriminate.
   discriminate.

   unfold lift; rewrite eq_lift_abs.
   apply sub_refl.
   rewrite eq_typ_betar.
   3:discriminate.
    red; intros; simpl.
    unfold V.lams, V.shift; simpl.
    reflexivity.

    apply typ_conv with (NatI (OSucc (lift_rec 1 0 (Ord omega)))).
    3:discriminate.
     apply typ_SuccI with (o:=osucc omega); auto.
      red; intros; simpl.
      apply lt_osucc; trivial.

      apply typ_var0; split;[discriminate|].
      apply sub_refl; red; intros; simpl.
      reflexivity.

     red; intros; simpl.
     reflexivity.

   eapply impl_call.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.
    2:simpl; reflexivity.
    discriminate.

    unfold subst, lift1; rewrite eq_lift_prod.
    rewrite eq_subst_prod.
    apply sub_typ_covariant.
     red; intros; simpl; reflexivity.

     red; intros; simpl.
     rewrite int_subst_rec_eq in H4.
     simpl in H4; unfold V.lams, V.shift in H4; simpl in H4.
     assert (isOrd (i 6)).
      generalize (H3 6 _ (reflexivity _)).
      simpl; intro.
      rewrite V.lams0 in H5.
      apply isOrd_inv with (2:=H5).      
      apply isOrd_succ.
      assert (val_ok e (V.shift 7 i)).
       red; intros.
       generalize (H3 (7+n) _ H6).
       destruct T as [(T,Tm)|]; simpl; auto.
      apply H0 in H6.
      simpl in H6.
      apply isOrd_inv with infty; trivial.
     revert H4; apply TI_incl; auto.

    eapply typ_var_impl.
     compute; reflexivity.
     simpl; reflexivity.
     discriminate.

     apply sub_refl.
     red; intros; simpl.
     reflexivity.

     eapply typ_var_impl.
      compute; reflexivity.
      simpl; reflexivity.
      discriminate.

      apply sub_refl.
      red; intros; simpl.
      reflexivity.
Qed.

End Example.

Print Assumptions minus_def.
*)