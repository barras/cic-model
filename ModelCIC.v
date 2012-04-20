Require Import List Bool Models.
Require Import ZFfunext ZFecc ZFind_nat.
Import ZF ZFsum ZFnats ZFrelations ZFord ZFfix ZFgrothendieck.
Require ModelZF.

Import ModelZF.CCM.
Import ModelZF.BuildModel.
Import T R J.

(** Derived rules of the basic judgements *)

Lemma eq_typ_betar : forall e N T M,
  typ e N T ->
  T <> kind ->
  eq_typ e (App (Abs T M) N) (subst N M).
intros.
apply eq_typ_beta; trivial.
 reflexivity.
 reflexivity.
Qed.

Lemma typ_var0 : forall e n T,
  match nth_error e n with
    value T' => T' <> kind /\ sub_typ e (lift (S n) T') T
  | _ => False end ->
  typ e (Ref n) T.
intros.
case_eq (nth_error e n); intros.
 rewrite H0 in H.
 destruct H.
 apply typ_subsumption with (lift (S n) t); auto.
  apply typ_var; trivial.

  destruct t as [(t,tm)|]; simpl; try discriminate.
  elim H; trivial.

 rewrite H0 in H; contradiction.
Qed.

Lemma typ_kind_univ e t : typ e t kind.
red; simpl; auto.
Qed.

(** Subtyping *)

Definition sub_typ_covariant : forall e U1 U2 V1 V2,
  eq_typ e U1 U2 ->
  sub_typ (U1::e) V1 V2 ->
  sub_typ e (Prod U1 V1) (Prod U2 V2).
unfold sub_typ; simpl; intros.
apply cc_prod_covariant with (4:=H2).
 red; red; intros.
 rewrite H4; auto with *.

 apply H; trivial.

 red; intros.
 apply H0; trivial.
 apply vcons_add_var; trivial.
Qed.

(** Universes *)

Definition type (n:nat) := cst (ecc n).

Lemma typ_Prop : forall e, typ e prop (type 0).
red; intros; simpl.
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


(** * Ordinals *)

(** Closure ordinal *)
Definition Infty := cst omega.

(** A special judgment (class of ordinals). It is not a set but kind does not
    restrict to ordinals *)
Definition typ_ord e O := forall i, val_ok e i -> isOrd (int O i).

Lemma typ_ord_lift e n O :
  typ_ord (List.skipn n e) O ->
  typ_ord e (lift n O).
red; intros.
unfold lift; rewrite int_lift_rec_eq.
rewrite V.lams0.
apply H.
red; intros.
assert (nth_error e (n+n0) = value T).
 clear H H0; revert e H1.
 elim n; simpl; intros; trivial.
 destruct e; auto.
 destruct n0; discriminate H1.
generalize (H0 _ _ H2).
destruct T as [(T,Tm)|]; simpl; trivial.
do 2 rewrite V.lams0.
unfold V.shift.
apply in_set_morph; auto with *.
apply Tm.
do 2 red; intros.
simpl.
replace (n+(S(n0+a))) with (S (n+n0+a)); auto with *.
Qed.

  Lemma typ_Infty e : typ_ord e Infty.
red; simpl; intros; auto.
Qed.

  Lemma typ_ord_ref : forall e n T,
    nth_error e n = value T ->
    T <> kind ->
    typ_ord e (lift (S n) T) ->
    typ_ord e (Ref n).
red; simpl; intros.
generalize (H2 _ _ H); simpl.
red in H1; specialize H1 with (1:=H2); simpl in H1.
destruct T as [(T,Tm)|]; simpl in *.
 eauto using isOrd_inv.

 elim H0; trivial.
Qed.

(** Ordinal successor (also type of ordinals less or equal to the argument) *)
Definition OSucc : term -> term.
(*begin show*)
intros o; left; exists (fun i => osucc (int o i)).
(*end show*)
do 2 red; intros.
rewrite H; reflexivity.
Defined.

Lemma typ_OSucc e O :
  typ_ord e O ->
  typ_ord e (OSucc O).
red; simpl; intros.
apply H in H0.
auto.
Qed.

Lemma typ_ord_le e O O':
  typ_ord e O ->
  typ e O' (OSucc O) ->
  typ_ord e O'.
red; simpl; intros.
red in H; specialize H with (1:=H1); simpl in H.
red in H0; specialize H0 with (1:=H1); simpl in H0.
apply isOrd_inv with (2:=H0); auto.
Qed.

Lemma typ_le_inv i e O O':
  typ e O' (OSucc O) ->
  val_ok e i ->
  int O' i ⊆ int O i.
intros.
apply H in H0; simpl in H0.
apply olts_le; trivial.
Qed.

(** O ≤ O *)
Lemma typ_ord_max e O :
  typ_ord e O ->
  typ e O (OSucc O).
red; simpl; intros.
apply lt_osucc.
apply H; trivial.
Qed.

(** * Nat *)

Definition Nat := cst NAT.

Definition NatI : term -> term.
(*begin show*)
intros o.
left; exists (fun i => NATi (int o i)).
(*end show*)
do 2 red; intros.
apply NATi_morph.
rewrite H; reflexivity.
Defined.

Lemma typ_natI : forall e o,
  typ e (NatI o) kind.
red; intros; simpl; trivial.
Qed.

(* Zero *)

Definition Zero := cst ZERO.

Lemma typ_Zero : forall e O,
  typ_ord e O ->
  typ e Zero (NatI (OSucc O)).
red; simpl; intros.
apply H in H0.
apply ZEROi_typ; trivial.
Qed.

(* Successor *)

Definition SuccI : term -> term.
(*begin show*)
intros o.
apply (Abs (NatI o)).
left; exists (fun i => SUCC (i 0)).
(*end show*)
do 2 red; intros.
unfold SUCC.
unfold eqX.
apply inr_morph.
apply H.
Defined.

Lemma typ_SuccI : forall e O,
  typ_ord e O ->
  typ e (SuccI O) (Prod (NatI O) (NatI (OSucc (lift 1 O)))).
red; simpl; intros.
apply H in H0.
apply cc_prod_intro; intros; auto with *.
 do 2 red; intros.
 apply NATi_morph.
 apply osucc_morph.
 apply int_morph; auto with *.
 do 2 red; intros.
 rewrite H2; reflexivity.

 unfold lift; rewrite int_lift_rec_eq.
 rewrite V.lams0.
 apply SUCCi_typ; auto.
Qed.

Lemma typ_app_SuccI : forall e i n,
  typ_ord e i ->
  typ e n (NatI i) ->
  typ e (App (SuccI i) n) (NatI (OSucc i)). 
intros.
apply typ_conv with (subst n (NatI (OSucc (lift 1 i)))).
3:discriminate.
 apply typ_app with (NatI i); trivial.
 2:discriminate.
 apply typ_SuccI; trivial.

 red; intros; simpl.
 unfold lift; rewrite int_lift_rec_eq.
 rewrite V.lams0.
 reflexivity.
Qed.

(* Case analysis *)

Definition Natcase (fZ fS n : term) : term.
(*begin show*)
left; exists (fun i => NATCASE (int fZ i) (fun k => int fS (V.cons k i)) (int n i)).
(*end show*)
do 2 red; intros.
red.
apply NATCASE_morph.
 rewrite H; reflexivity.
(**)
 red; intros.
 rewrite H; rewrite H0; reflexivity.
(**)
 rewrite H; reflexivity.
Defined.

Instance Natcase_morph :
  Proper (eq_term ==> eq_term ==> eq_term ==> eq_term) Natcase.
do 4 red; intros.
simpl; red; intros.
apply NATCASE_morph_gen; intros.
 rewrite H1; rewrite H2; reflexivity.
 rewrite H; rewrite H2; reflexivity.
 rewrite H0; rewrite H4; rewrite H2; reflexivity.
Qed.

Lemma Natcase_succ : forall O e n fZ fS,
  typ_ord e O ->
  typ e n (NatI O) ->
  eq_typ e (Natcase fZ fS (App (SuccI O) n)) (subst n fS).
red; intros.
red in H; specialize H with (1:=H1).
red in H0; specialize H0 with (1:=H1).
simpl in *.
rewrite <- (fun e1 e2 => NATCASE_morph (int fZ i) (int fZ i) e1
  (fun k => int fS(V.cons k i)) (fun k => int fS(V.cons k i)) e2
  (SUCC (int n (fun k => i k)))); auto with *.
 rewrite NATCASE_SUCC; auto.
  rewrite int_subst_eq; reflexivity.

  intros.
  rewrite H2; reflexivity.

 red; intros.
 rewrite H2; reflexivity.

 rewrite beta_eq; auto with *.
 red; intros.
 unfold SUCC; apply inr_morph; trivial.
Qed.

Existing Instance NATi_morph.

Lemma typ_natcase : forall e O P fZ fS n,
  typ_ord e O ->
  typ e fZ (App P Zero) ->
  typ (NatI O :: e) fS (App (lift 1 P) (App (SuccI (lift 1 O)) (Ref 0))) ->
  typ e n (NatI (OSucc O)) ->
  typ e (Natcase fZ fS n) (App P n).
red; intros.
red in H; specialize H with (1:=H3).
simpl in H; red in H.
red in H0; specialize H0 with (1:=H3).
simpl in H0; red in H0.
red in H2; specialize H2 with (1:=H3).
simpl in H2; red in H2.
simpl; red.
apply NATCASE_typ with (o:=int O i) (P:=fun n => app (int P i) n); trivial.
 do 2 red; intros.
 rewrite H4; reflexivity.

 do 2 red; intros.
 rewrite H4; reflexivity.

 intros.
 assert (val_ok (NatI O :: e) (V.cons n0 i)).
  apply vcons_add_var; trivial.
 apply H1 in H5; clear H1; simpl in H5.
 change (fun k => V.cons n0 i k) with (V.cons n0 i) in H5.
 rewrite beta_eq in H5; trivial.
  rewrite simpl_int_lift1 in H5; trivial.

  red; intros.
  unfold SUCC; apply inr_morph; trivial.

  rewrite simpl_int_lift1; auto.
Qed.

Lemma typ_natcase' : forall e O P fZ fS n T,
  typ_ord e O ->
  sub_typ e (App P n) T -> 
  typ e fZ (App P Zero) ->
  typ (NatI O :: e) fS
    (App (lift 1 P) (App (SuccI (lift 1 O)) (Ref 0))) ->
  typ e n (NatI (OSucc O)) ->
  typ e (Natcase fZ fS n) T.
intros.
apply typ_subsumption with (App P n); auto.
2:discriminate.
apply typ_natcase with O; trivial.
Qed.

(********************************************************************************)
(** * Variance *)

(** Occurrences *)

Module Beq.
Definition t := bool.
Definition eq := @eq bool.
Definition eq_equiv : Equivalence eq := eq_equivalence.
Existing Instance eq_equiv.
End Beq.
Module B := VarMap.Make(Beq).


  (* Non-occurrence : interp do not depend on variables in set [f] *)
  Definition noccur (f:B.map) (T:term) : Prop :=
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

Lemma noc_abs a b f :
  noccur f a ->
  noccur (B.cons false f) b ->
  noccur f (Abs a b).
red; simpl; intros.
apply cc_lam_ext.
 apply H; trivial.

 red; intros.
 apply H0.
 destruct n; simpl; trivial.
 apply H1.
Qed.

Lemma noc_prod a b f :
  noccur f a ->
  noccur (B.cons false f) b ->
  noccur f (Prod a b).
red; simpl; intros.
apply cc_prod_ext.
 apply H; trivial.

 red; intros.
 apply H0.
 destruct n; simpl; trivial.
 apply H1.
Qed.

Ltac noc_tac :=
  lazymatch goal with 
    |- noccur _ (App _ _) => apply noc_app; noc_tac
  | |- noccur _ (Abs _ _) => apply noc_abs; noc_tac
  | |- noccur _ (Prod _ _) => apply noc_prod; noc_tac
  | |- noccur _ (Ref _) => apply noc_var; reflexivity
  | |- noccur _ _ => try (red; reflexivity) (* closed case *)
  end.


(********************************************************************************)
(** ** Judgements with variance *)


(** Mark stage-irrelevant functions (domain information have to be repeated) *)
Module OTeq.
Definition t := option term.
Definition eq := @eq (option term).
Definition eq_equiv : Equivalence eq := eq_equivalence.
Existing Instance eq_equiv.
End OTeq.
Module OT := VarMap.Make(OTeq).

(** Environments with tags on ordinal and recursive function variables *)
Record fenv := {
  tenv : env;
  ords : B.map; (* variables denoting ordinals *)
  fixs : OT.map (* variables denoting recursive functions with their domain *)
}.

Definition tinj e :=
  Build_fenv e (B.nil false) (OT.nil None).

(** Pushing an ordinary variable *)
Definition push_var e T :=
  Build_fenv (T::tenv e) (B.cons false (ords e)) (OT.cons None (fixs e)).

(** Pushing a stage-irrelevant function *)
Definition push_fun e dom rng :=
  Build_fenv (Prod dom rng::tenv e)
    (B.cons false (ords e)) (OT.cons (Some dom) (fixs e)).

(** Pushing an ordinal (stage) variable *)
Definition push_ord e T :=
  Build_fenv (T::tenv e) (B.cons true (ords e)) (OT.cons None (fixs e)).


(** Semantics of contexts for variance judgments:
    - ordinal variables follow the ordinal order
    - stage-irrelevant function have to be compatible
    - regular variables have to be the same
*)

Definition val_mono (e:fenv) i i' :=
    val_ok (tenv e) i /\
    val_ok (tenv e) i' /\
    forall n,
    if ords e n then i n ⊆ i' n
    else match fixs e n with
      Some T => fcompat (int T (V.shift (S n) i)) (i n) (i' n)
    | _ => i n == i' n
    end.

Lemma val_mono_refl : forall e i,
  val_ok (tenv e) i -> val_mono e i i.
split;[idtac|split]; simpl; auto with *.
intro n.
destruct (ords e n); auto with *.
destruct (fixs e n); auto with *.
red; auto with *.
Qed.

Lemma val_push_var : forall e i i' x x' T,
  val_mono e i i' ->
  x == x' ->
  el T i x ->
  el T i' x' ->
  val_mono (push_var e T) (V.cons x i) (V.cons x' i').
destruct 1 as (?&?&?); split;[idtac|split]; trivial.
 unfold push_var; simpl.
 apply vcons_add_var0; trivial.

 unfold push_var; simpl.
 apply vcons_add_var0; trivial.

 destruct n as [|n]; simpl; auto.
 generalize (H1 n).
 destruct (ords e n); trivial.
Qed.

Lemma val_push_ord : forall e i i' x x' T,
  val_mono e i i' ->
  x ⊆ x' ->
  el T i x ->
  el T i' x' ->
  val_mono (push_ord e T) (V.cons x i) (V.cons x' i').
destruct 1 as (?&?&?); split;[idtac|split]; trivial.
 unfold push_ord; simpl.
 apply vcons_add_var0; trivial.

 unfold push_ord; simpl.
 apply vcons_add_var0; trivial.

 destruct n as [|n]; simpl; auto.
 generalize (H1 n).
 destruct (ords e n); trivial.
Qed.

Lemma val_push_fun : forall e i i' f g T U,
  val_mono e i i' ->
  f ∈ prod (int T i) (fun x => int U (V.cons x i)) ->
  g ∈ prod (int T i') (fun x => int U (V.cons x i')) ->
  fcompat (int T i) f g ->
  val_mono (push_fun e T U) (V.cons f i) (V.cons g i').
destruct 1 as (?&?&?); split;[idtac|split]; trivial.
 unfold push_fun; simpl.
 apply vcons_add_var0; trivial.

 unfold push_fun; simpl.
 apply vcons_add_var0; trivial.

 destruct n as [|n]; simpl; auto.
 generalize (H1 n).
 destruct (ords e n); trivial.
Qed.

(** Invariance judgement *)
Definition var_equals e M :=
  forall i i', val_mono e i i' -> int M i == int M i'.

(** Function Extension judgment *)
Definition var_compat e dom M :=
  forall i i', val_mono e i i' ->
  fcompat (int dom i) (int M i) (int M i').

(** Covariance judgment *)
Definition var_mono e M :=
  forall i i', val_mono e i i' ->
  int M i ⊆ int M i'.


(** Invariance rules *)
  Definition spec_var e n :=
    ords e n || match fixs e n with Some _ => true | _ => false end.

  Lemma var_eq_noc : forall e t,
    noccur (spec_var e) t ->
    var_equals e t.
unfold noccur, var_equals, spec_var; intros.
apply H; intros.
destruct H0 as (_,(_,H0)).
generalize (H0 n).
destruct (ords e n); simpl; trivial.
destruct (fixs e n); simpl; trivial.
Qed.

  Lemma var_eq_app : forall e u v,
    var_equals e u ->
    var_equals e v ->
    var_equals e (App u v).
unfold var_equals; intros.
specialize H with (1:=H1).
specialize H0 with (1:=H1).
simpl.
rewrite H; rewrite H0; reflexivity.
Qed.

  Lemma var_eq_abs : forall e T M,
    var_equals e T ->
    var_equals (push_var e T) M ->
    var_equals e (Abs T M).
unfold var_equals; intros.
simpl.
apply lam_ext; auto.
red; intros.
apply H0.
specialize H with (1:=H1).
apply val_push_var; auto.
 change (el T i' y2).
 apply in_int_el; trivial.
 rewrite <- H3; rewrite <- H; trivial.
Qed.

  Lemma var_eq_prod : forall e T U,
    var_equals e T ->
    var_equals (push_var e T) U ->
    var_equals e (Prod T U).
red; simpl; intros.
specialize (H _ _ H1).
apply cc_prod_ext; trivial.
red; intros.
apply H0.
apply val_push_var; auto with *.
change (el T i' x').
rewrite <- H3.
apply in_int_el.
rewrite <- H; trivial.
Qed.

  Lemma var_eq_NATi : forall e O,
    typ_ord (tenv e) O ->
    var_equals e O ->
    var_equals e (NatI O).
unfold var_equals; intros.
simpl.
apply NATi_morph; apply H0; trivial.
Qed.

  Lemma var_eq_OSucc : forall e O,
    var_equals e O ->
    var_equals e (OSucc O).
unfold var_equals; simpl; intros.
apply osucc_morph; apply H; trivial.
Qed.

  Lemma var_eq_Natcase : forall e O f1 f2 c,
    typ_ord (tenv e) O ->
    var_mono e O ->
    var_equals e f1 ->
    var_equals (push_var e (NatI O)) f2 ->
    typ (tenv e) c (NatI (OSucc O)) ->
    var_equals e c ->
    var_equals e (Natcase f1 f2 c).
red; intros e O f1 f2 c tyO H0 H1 H2 tyc H3 i i' H4.
simpl.
change (fun k => i k) with i.
change (fun k => i' k) with i'.
assert (ord : isOrd (int O i)).
 apply (tyO _ (proj1 H4)).
assert (ord' : isOrd (int O i')).
 apply (tyO _ (proj1 (proj2 H4))).
assert (int c i ∈ NATi (osucc (int O i))).
 destruct H4 as (H4,_).
 apply tyc in H4; trivial.
apply NATCASE_morph_gen; intros; auto.
 apply H3; trivial.

 apply H1; trivial.

 apply H2.
 red in H0; specialize H0 with (1:=H4).
 rewrite H5 in H.
 apply SUCCi_inv_typ in H; auto.
 apply val_push_var; simpl; auto.
 rewrite <- H6.
 clear H5 H6 x'; revert x H.
 apply TI_mono; auto.
Qed.

(** Stage-irrelevance rules *)
  Lemma var_comp_ref : forall e dom n T,
    ords e n = false ->
    fixs e n = Some T ->
    T <> kind ->
    eq_typ (tenv e) (lift (S n) T) dom ->
    var_compat e dom (Ref n).
unfold var_compat; simpl; intros.
destruct H3 as (Hty,(Hty',Hrec)).
generalize (Hrec n).
rewrite H; rewrite H0.
unfold fcompat; intros.
apply H3.
revert H4.
rewrite <- (H2 _ Hty).
unfold lift; rewrite int_lift_rec_eq.
rewrite V.lams0; trivial.
Qed.
  Lemma abs_compat : forall e U T M,
    var_mono e T ->
    var_equals (push_var e T) M ->
    typ (T::tenv e) M U ->
    U <> kind ->
    var_compat e T (Abs T M).
unfold var_mono, var_equals, var_compat; intros.
specialize H with (1:=H3).
simpl.
red; intros.
fold app.
 rewrite beta_eq; try assumption.
 rewrite beta_eq.
 3:apply H; trivial.
  apply H0.
  apply val_push_var; simpl; auto with *.
  apply in_int_el; apply H; trivial.

  red; red; intros.
  rewrite H6; reflexivity.

 red; red; intros.
 rewrite H6; reflexivity.
Qed.

  Lemma succ_compat e O :
    typ_ord (tenv e) O ->
    var_mono e O ->
    var_compat e (NatI O) (SuccI O).
do 2 red; simpl; intros.
red in H, H0.
specialize H0 with (1:=H1).
rewrite cc_beta_eq; auto with *.
rewrite cc_beta_eq; auto with *.
revert H2; apply TI_mono; auto with *.
 apply H; apply H1.
 apply H; apply H1.
Qed.


  Lemma var_comp_app : forall e dom u v,
    dom <> kind ->
    var_compat e dom u ->
    typ (tenv e) v dom ->
    var_equals e v ->
    var_equals e (App u v).
unfold var_equals; intros.
simpl.
transitivity (app (int u i') (int v i)).
 do 2 red in H0.
 apply H0; trivial.
 red in H1.
 specialize H1 with (1:=proj1 H3).
 revert H1; destruct dom; trivial.
 elim H; trivial.

 rewrite <- H2 with (1:=H3).
 reflexivity.
Qed.


(** Covariance rules *)

  Lemma var_eq_sub : forall e M, var_equals e M -> var_mono e M.
unfold var_mono, var_equals; intros.
apply H in H0.
rewrite H0; reflexivity.
Qed.

  Lemma var_mono_ref : forall e n,
    ords e n = true ->
    var_mono e (Ref n).
unfold var_mono; intros.
destruct H0 as (_,(_,H0)).
generalize (H0 n); rewrite H.
simpl; trivial.
Qed.

  Lemma var_mono_prod : forall e T U,
    var_equals e T ->
    var_mono (push_var e T) U ->
    var_mono e (Prod T U).
red; simpl; intros.
specialize (H _ _ H1).
apply cc_prod_covariant; intros; auto.
 red; red; intros.
 rewrite H3; reflexivity.

 apply H0.
 apply val_push_var; auto with *.
  change (el T i' x).
  apply in_int_el.
  rewrite <- H; trivial.
Qed.

  Lemma var_mono_NATi : forall e O,
    typ_ord (tenv e) O ->
    var_mono e O ->
    var_mono e (NatI O).
unfold var_mono; intros.
simpl.
assert (oo : isOrd (int O i)).
 apply (H _ (proj1 H1)).
assert (oo' : isOrd (int O i')).
 apply (H _ (proj1 (proj2 H1))).
clear H.
apply TI_mono; auto.
Qed.

  Lemma var_mono_OSucc : forall e O,
    var_mono e O ->
    var_mono e (OSucc O).
unfold var_mono; simpl; intros.
red; intros.
unfold osucc in *.
apply subset_intro.
 apply power_intro; intros.
 apply H with (1:=H0); trivial.
 apply power_elim with z; trivial.
 apply subset_elim1 in H1; trivial.

 apply subset_elim2 in H1.
 destruct H1.
 rewrite H1; trivial.
Qed.


(*****************************************************************************)
(** ** Recursor (without case analysis) *)

(* NatFix O M is a fixpoint of domain Nati O with body M *)
Definition NatFix (O M:term) : term.
(*begin show*)
left.
exists (fun i =>
  NATREC (fun o' f => int M (V.cons f (V.cons o' i))) (int O i)).
(*end show*)
red; red; intros.
apply NATREC_morph.
 do 2 red; intros.
 rewrite H; rewrite H0; rewrite H1; reflexivity.
(**)  
 rewrite H.
 reflexivity.
Defined.


(** Typing rules of NatFix *)

Section NatFixRules.

  Variable E : fenv.
  Let e := tenv E.
  Variable O U M : term.
  Hypothesis M_nk : ~ eq_term M kind.
  Hypothesis ty_O : typ_ord e O.
  Hypothesis ty_M : typ (Prod (NatI (Ref 0)) U::OSucc O::e)
    M (Prod (NatI (OSucc (Ref 1)))
         (lift1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U)))).

  Hypothesis stab : var_compat
    (push_fun (push_ord E (OSucc O)) (NatI (Ref 0)) U)
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

  Hypothesis var_mono_U :
    var_mono (push_var (push_ord E (OSucc O)) (NatI (OSucc (Ref 0)))) U.


  Lemma ty_fix_body : forall i o f,
    val_ok e i ->
    o < osucc (int O i) ->
    f ∈ prod (NATi o) (fun x => int U (V.cons x (V.cons o i))) ->
    F i o f ∈
    prod (NATi (osucc o)) (fun x => int U (V.cons x (V.cons (osucc o) i))).
unfold F; intros.
specialize (ty_O _ H); simpl in ty_O.
assert (isOrd (int O i)).
 auto.
refine (eq_elim _ _ _ _ (ty_M (V.cons f (V.cons o i)) _)); simpl.
 apply prod_ext; auto with *.
 red; intros.
 change (fun k => V.cons f (V.cons o i) k) with (V.cons f (V.cons o i)).
 rewrite simpl_lift1; rewrite lift10.
 rewrite int_subst_rec_eq.
 rewrite <- V.cons_lams.
  rewrite V.lams0.
  rewrite int_lift_rec_eq.
  rewrite <- V.cons_lams.
   rewrite <- V.cons_lams.
    rewrite V.lams0.
    simpl.
    unfold V.shift; simpl.
    rewrite H4; reflexivity.

    red; red; intros.
    rewrite H5; reflexivity.

   red; red; intros.
   rewrite H5; reflexivity.

  red; red; intros.
  rewrite H5; reflexivity.

 apply vcons_add_var; auto.
 apply vcons_add_var; simpl; auto.
Qed.

  Lemma fix_body_irrel : forall i,
    val_ok e i ->
    NAT_ord_irrel (int O i) (F i) (fun o' x => int U (V.cons x (V.cons o' i))).
red; red; intros.
assert (isOrd (int O i)).
 auto.
red in stab.
assert (Hstab := stab (V.cons f (V.cons o i)) (V.cons g (V.cons o' i))).
simpl in Hstab.
apply Hstab; clear Hstab; trivial.
apply val_push_fun; auto.
apply ole_lts in H1; trivial.
apply val_push_ord; auto.
 apply val_mono_refl; trivial.

 simpl.
 apply isOrd_plump with o'; auto.
Qed.

  Lemma fix_codom_mono : forall o o' x x' i,
   val_ok e i ->
   isOrd o' ->
   o' ⊆ int O i ->
   isOrd o ->
   o ⊆ o' ->
   x ∈ NATi o ->
   x == x' ->
   int U (V.cons x (V.cons o i)) ⊆ int U (V.cons x' (V.cons o' i)).
intros.
apply var_mono_U.
apply val_push_var; simpl; auto.
 apply val_push_ord; simpl; auto; change (int O (fun k => i k)) with (int O i).
  apply val_mono_refl; trivial.

  apply ole_lts; auto.
  transitivity o'; trivial.

  apply ole_lts; auto.

 revert H4; apply TI_incl; auto.

 rewrite <- H5.
 revert H4; apply TI_incl; auto.
 apply ole_lts; auto.
Qed.

  Hint Resolve morph_fix_body ext_fun_ty ty_fix_body fix_codom_mono fix_body_irrel.

  Lemma nat_fix_eqn : forall i,
    val_ok e i ->
    NATREC (F i) (int O i) ==
    cc_lam (NATi (int O i))
      (fun x => cc_app (F i (int O i) (NATREC (F i) (int O i))) x).
intros.
assert (oi : isOrd (int O i)).
 auto.
apply NATREC_eqn with
  (ord:=int O i)
  (U:=fun o x => int U (V.cons x (V.cons o i))); auto.
intros.
apply ty_fix_body; trivial.
apply ole_lts; auto.
Qed.


  Lemma typ_nat_fix : typ e (NatFix O M) (Prod (NatI O) (subst_rec O 1 U)).
red; intros.
simpl.
assert (isOrd (int O i)).
 auto.
apply eq_elim with
   (prod (NATi (int O i)) (fun x => int U (V.cons x (V.cons (int O i) i)))).
 apply prod_ext.
  reflexivity.
  red; intros.
  rewrite int_subst_rec_eq.
  rewrite V.shift_cons.
  rewrite <- V.cons_lams.
   rewrite V.lams0.
   rewrite H2; reflexivity.

   do 2 red; intros.
   rewrite H3; reflexivity.
apply NATREC_wt with (F:=F i)
  (ord := int O i)
  (U:=fun o x => int U (V.cons x (V.cons o i))); intros; auto.
apply ty_fix_body; trivial.
apply ole_lts; trivial.
Qed.


  Lemma nat_fix_eq : forall N,
    typ e N (NatI O) ->
    eq_typ e (App (NatFix O M) N)
             (App (subst O (subst (lift 1 (NatFix O M)) M)) N).
red; intros.
change
 (app (NATREC (F i) (int O i)) (int N i) ==
  app (int (subst O (subst (lift 1 (NatFix O M)) M)) i) (int N i)).
do 2 rewrite int_subst_eq.
rewrite simpl_int_lift.
rewrite lift0_term.
simpl.
change (int O (fun k => i k)) with (int O i).
assert (O_lt := @ty_O _ H0).
simpl in O_lt.
rewrite nat_fix_eqn; trivial.
rewrite beta_eq.
 reflexivity.

 red; intros.
 rewrite H2; reflexivity.

 apply H; trivial.
Qed.

  Lemma var_comp_fix :
    var_mono E O ->
    var_compat E (NatI O) (NatFix O M).
intro subO.
do 2 red; intros.
assert (isval := proj1 H).
assert (isval' := proj1 (proj2 H)).
assert (oo: isOrd (int O i)).
 auto.
assert (oo': isOrd (int O i')).
 auto.
assert (inclo: int O i ⊆ int O i').
 apply subO in H; trivial.
clear subO.
assert (tyfx' :
  NATREC (F i') (int O i') ∈
  prod (NATi (int O i')) (fun x1 => int U (V.cons x1 (V.cons (int O i') i')))).
 apply NATREC_wt with
   (ord := int O i')
   (U:=fun o x => int U (V.cons x (V.cons o i'))); intros; auto.
 apply ty_fix_body; trivial.
 apply ole_lts; trivial.
assert (NATREC (F i) (int O i) ==
  cc_lam (NATi (int O i)) (cc_app (NATREC (F i') (int O i')))).
 apply NATREC_ext with  (ord := int O i)
  (U:=fun o x => int U (V.cons x (V.cons o i))); intros; auto.
  apply ty_fix_body; trivial.
  apply ole_lts; trivial.

  apply is_cc_fun_lam.
  do 2 red; intros; apply cc_app_morph; auto with *.

  red; intros.
  rewrite cc_beta_eq.
  eapply transitivity.
   apply cc_app_morph;[|reflexivity].
   apply nat_fix_eqn; trivial.
  rewrite cc_beta_eq.
   symmetry; apply stab.
   apply val_push_fun; trivial.
    apply val_push_ord; simpl; auto.
     apply isOrd_trans with (int O i); auto.

     apply lt_osucc; auto.

    apply cc_prod_intro; intros.
     do 2 red; intros; apply cc_app_morph; auto with *.

     do 2 red; intros.
     rewrite H5; reflexivity.

     rewrite cc_beta_eq; trivial.
      assert (tyfx1 : NATREC (F i) o' ∈
         prod (NATi o') (fun x1 => int U (V.cons x1 (V.cons o' i)))).
       apply NATREC_wt with
        (ord := o')
        (U:=fun o x => int U (V.cons x (V.cons o i))); intros; auto.
        apply isOrd_inv with (int O i); auto.

        apply fix_codom_mono; trivial.
        transitivity o'; trivial.
        transitivity (int O i); trivial.
        red; intros; apply isOrd_trans with o'; auto.

        reflexivity.

        apply ty_fix_body; trivial.
        apply ole_lts; trivial.
        red; intros; apply isOrd_trans with o'; auto.
        red; auto.

        red; intros.
        apply fix_body_irrel; trivial.
        transitivity o'; trivial.
        red; intros; apply isOrd_trans with o'; auto.
       rewrite H2 in tyfx1.
       specialize cc_prod_elim with (1:=tyfx1) (2:=H4); intro.
       rewrite cc_beta_eq in H5; trivial.
        rewrite cc_beta_eq in H5; trivial.
         do 2 red; intros; apply cc_app_morph; auto with *.

         revert H4; simpl; apply TI_incl; auto.

        do 2 red; intros; apply cc_app_morph; auto with *.

       do 2 red; intros; apply cc_app_morph; auto with *.

      revert H4; simpl; apply TI_incl; auto.

    red; intros.
    rewrite cc_beta_eq; auto.
     rewrite cc_beta_eq; auto with *.
      do 2 red; intros; apply cc_app_morph; auto with *.

      revert H4; simpl; apply TI_incl; auto. 

     do 2 red; intros; apply cc_app_morph; auto with *.

     simpl; trivial.

   do 2 red; intros; apply cc_app_morph; auto with *.

   revert H3; apply TI_mono; auto. 
    eauto using isOrd_inv.

    red; intros.
    apply inclo.
    apply isOrd_plump with o'; eauto using isOrd_inv, olts_le.

  do 2 red; intros; apply cc_app_morph; auto with *.

  revert H3; apply TI_mono; auto. 
   eauto using isOrd_inv.

   red; intros.
   apply isOrd_plump with o'; eauto using isOrd_inv, olts_le.
simpl in H1|-*; unfold F in H1 at 1; rewrite H1.
rewrite cc_beta_eq; auto with *.
 reflexivity.

 do 2 red; intros; apply cc_app_morph; auto with *.
Qed.

  Lemma var_eq_fix :
    var_equals E O ->
    var_equals E (NatFix O M).
red; intros.
assert (ty1 := typ_nat_fix _ (proj1 H0)); simpl in ty1.
assert (ty2 := typ_nat_fix _ (proj1 (proj2 H0))); simpl in ty2.
simpl.
rewrite cc_eta_eq with (1:=ty1).
rewrite cc_eta_eq with (1:=ty2).
apply cc_lam_ext; auto with *.
 apply NATi_morph.
 apply H; trivial.

 red; intros.
 rewrite <- H2.
 apply var_comp_fix; trivial.
 apply var_eq_sub; trivial.
Qed.

End NatFixRules.

Print Assumptions typ_nat_fix.

(****************************************************************************************)
(** ** Compound judgements : typing + variance *)

Definition typ_inv e M T :=
  var_equals e M /\ typ (tenv e) M T.

Definition typ_ext e M A B :=
  var_compat e A M /\ typ (tenv e) M (Prod A B).

Definition typ_mono e M T :=
  var_mono e M /\ typ (tenv e) M T.

Instance typ_inv_morph e : Proper (eq_term ==> eq_term ==> iff) (typ_inv e).
apply morph_impl_iff2; auto with *.
do 4 red; intros.
destruct H1; split.
 red; intros.
 rewrite <- H; auto.

 rewrite <- H; rewrite <- H0; auto.
Qed.

(** ** Inference rules *)

(** Inclusion relation between judgements *)
  Lemma typ_inv_mono : forall e M T, typ_inv e M T -> typ_mono e M T.
destruct 1; split; trivial.
apply var_eq_sub; trivial.
Qed.

  Lemma typ_inv_ext : forall e M A B, typ_inv e M (Prod A B) -> typ_ext e M A B.
destruct 1; split; trivial.
do 2 red; intros.
apply H in H1.
rewrite H1; reflexivity.
Qed.

(** Subsumption *)
  Lemma typ_inv_subsumption e M T T' :
    typ_inv e M T -> sub_typ (tenv e) T T' -> T <> kind -> typ_inv e M T'.
destruct 1; split; trivial.
apply typ_subsumption with (2:=H1); trivial.
Qed.

(** Typing the three kind of variables *)
  Lemma typ_inv_ref : forall e n T,
    spec_var e n = false ->
    nth_error (tenv e) n = value T ->
    typ_inv e (Ref n) (lift (S n) T).
intros.
split.
 apply var_eq_noc; apply noc_var; trivial.
 apply typ_var; trivial.
Qed.


(* Not really useful since (Ref n) should be an ordinal... *)
  Lemma typ_mono_ref : forall e n T,
    ords e n = true ->
    nth_error (tenv e) n = value T ->
    typ_mono e (Ref n) (lift (S n) T).
split.
 apply var_mono_ref; trivial.
 apply typ_var; trivial.
Qed.

 Lemma typ_ext_ref e n A B :
    ords e n = false ->
    fixs e n = Some A ->
    A <> kind ->
    nth_error (tenv e) n = value (Prod A B) ->
    typ_ext e (Ref n) (lift (S n) A) (lift1 (S n) B).
split.
 apply var_comp_ref with (2:=H0); trivial.
 reflexivity.

 eapply typ_conv.
  apply typ_var with (1:=H2).
  2:discriminate.

  unfold lift; rewrite eq_lift_prod; reflexivity.
Qed.

(** Abstraction *)
  Lemma typ_inv_abs : forall e U T M,
    U <> kind ->
    var_equals e T ->
    typ_inv (push_var e T) M U ->
    typ_inv e (Abs T M) (Prod T U).
destruct 3; split.
 apply var_eq_abs; trivial.

 apply typ_abs; trivial.
Qed.

  Lemma typ_ext_abs : forall e U T M,
    var_mono e T ->
    typ_inv (push_var e T) M U ->
    U <> kind ->
    typ_ext e (Abs T M) T U.
destruct 2; split.
 apply abs_compat with U; trivial.

 apply typ_abs; trivial.
Qed.

(** Application *)

  Lemma typ_ext_app : forall e u v A B,
    A <> kind ->
    typ_ext e u A B -> 
    typ_inv e v A ->
    typ_inv e (App u v) (subst v B).
intros.
destruct H0; destruct H1; split.
 apply var_comp_app with (2:=H0); trivial.

 apply typ_app with A; trivial.
Qed.

(** Natural numbers: type and constructors *)

(*
  Lemma mono_NATi : forall e O,
    typ_mono e O Ord ->
    var_mono e (NatI O).
destruct 1.
apply var_mono_NATi; auto.
Qed.
*)
(*
  Lemma mono_OSucc : forall e O o,
    isOrd o ->
    typ_mono e O O' ->
    typ_mono e (OSucc O) (OSucc O').
destruct 2.
split.
 apply var_mono_OSucc; trivial.

 red; simpl; intros.
 apply lt_osucc_compat; trivial.
 apply H1; trivial.
Qed.
*)

  Lemma typ_inv_Zero e O :
    typ_ord (tenv e) O ->
(*    var_mono e O -> *)
    typ_inv e Zero (NatI (OSucc O)).
split; simpl.
 red; reflexivity.
 apply typ_Zero; trivial.
Qed.


  Lemma typ_inv_Succ e O :
    typ_ord (tenv e) O ->
    var_equals e O ->
    typ_inv e (SuccI O) (Prod (NatI O) (NatI (OSucc (lift 1 O)))).
split; simpl.
 red; simpl; intros.
 apply cc_lam_ext.
  apply NATi_morph.
  apply H0; trivial.

  red; intros. 
  rewrite H3; reflexivity.

 apply typ_SuccI; trivial.
Qed.

  Lemma typ_ext_Succ e O :
    typ_ord (tenv e) O ->
    var_mono e O ->
    typ_ext e (SuccI O) (NatI O) (NatI (OSucc (lift 1 O))).
split; simpl.
 do 2 red; simpl; intros.
 rewrite cc_beta_eq; auto with *.
 rewrite cc_beta_eq; auto with *.
 change (x ∈ NATi (int O i')).
 revert H2; apply TI_mono; auto with *.
  apply H; apply H1.
  apply H; apply H1.

 apply typ_SuccI; trivial.
Qed.


(** Case-analysis *)
  Lemma typ_inv_natcase : forall e O P fZ fS n T,
    typ_ord (tenv e) O ->
    var_mono e O ->
    sub_typ (tenv e) (App P n) T -> 
    typ_inv e fZ (App P Zero) ->
    typ_inv (push_var e (NatI O)) fS
      (App (lift 1 P) (App (SuccI (lift 1 O)) (Ref 0))) ->
    typ_inv e n (NatI (OSucc O)) ->
    typ_inv e (Natcase fZ fS n) T.
intros.
destruct H2.
destruct H3.
simpl in H6.
destruct H4.
split.
 apply var_eq_Natcase with O; trivial.

 apply typ_natcase' with O P; trivial.
Qed.

(** Fixpoint *)

  Lemma typ_ext_fix : forall e O U M,
    typ_ord (tenv e) O ->
    var_mono e O ->
    typ_ext (push_fun (push_ord e (OSucc O)) (NatI (Ref 0)) U) M
      (NatI (OSucc (Ref 1))) (lift1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    var_mono (push_var (push_ord e (OSucc O)) (NatI (OSucc (Ref 0)))) U ->
    typ_ext e (NatFix O M) (NatI O) (subst_rec O 1 U).
intros e O U M tyO inclO (extM,tyM) tyU.
split.
 apply var_comp_fix with U; trivial.

 apply typ_nat_fix; trivial.
Qed.

  Lemma typ_inv_fix : forall e O U M,
    typ_ord (tenv e) O ->
    var_equals e O ->
    typ_ext (push_fun (push_ord e (OSucc O)) (NatI (Ref 0)) U) M
      (NatI (OSucc (Ref 1))) (lift1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    var_mono (push_var (push_ord e (OSucc O)) (NatI (OSucc (Ref 0)))) U ->
    typ_inv e (NatFix O M) (Prod (NatI O) (subst_rec O 1 U)).
intros e O U M tyO inclO (extM,tyM) tyU.
split.
 apply var_eq_fix with U; trivial.

 apply typ_nat_fix; trivial.
Qed.



(** Derived rules for practical examples (basically applies subsumption beforehand) *)

  Lemma typ_inv_ref' : forall e n t T,
    spec_var e n = false ->
    nth_error (tenv e) n = value t ->
    t <> kind ->
    sub_typ (tenv e) (lift (S n) t) T ->
    typ_inv e (Ref n) T.
intros.
split.
 apply var_eq_noc; apply noc_var; trivial.

 apply typ_subsumption with (lift (S n) t); trivial.
  apply typ_var; trivial.

  destruct t as [(t,tm)|]; simpl in *; auto.
  discriminate.
Qed.

  Lemma typ_inv_app : forall e u v V Ur T,
    V <> kind ->
    Ur <> kind ->
    sub_typ (tenv e) (subst v Ur) T ->
    typ_inv e u (Prod V Ur) ->
    typ_inv e v V ->
    typ_inv e (App u v) T.
intros.
destruct H2.
destruct H3.
split.
 apply var_eq_app; trivial.

 apply typ_subsumption with (subst v Ur); trivial.
  apply typ_app with V; auto.

  destruct Ur as [(Ur,Urm)|]; simpl; trivial.
  discriminate.
Qed.

  Lemma typ_inv_rec_call : forall e n x t u T,
    ords e n = false ->
    fixs e n = Some t ->
    t <> kind ->
    u <> kind ->
    nth_error (tenv e) n = value (Prod t u) ->
    sub_typ (tenv e) (subst x (lift1 (S n) u)) T ->
    typ_inv e x (lift (S n) t) ->
    typ_inv e (App (Ref n) x) T.
intros.
apply typ_inv_subsumption with (2:=H4).
 eapply typ_ext_app with (3:=H5).
  destruct t as [(t,tm)|]; simpl; trivial; discriminate.

  eapply typ_ext_ref with (4:=H3); trivial.

 destruct u as [(u,um)|]; simpl; trivial; discriminate.
Qed.

  Lemma typ_inv_fix' : forall e O U M T,
    sub_typ (tenv e) (Prod (NatI O) (subst_rec O 1 U)) T ->
    typ_ord (tenv e) O ->
    var_equals e O ->
    var_mono (push_var (push_ord e (OSucc O)) (NatI (OSucc (Ref 0)))) U ->
    typ_ext (push_fun (push_ord e (OSucc O)) (NatI (Ref 0)) U) M
      (NatI (OSucc (Ref 1))) (lift1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    typ_inv e (NatFix O M) T.
intros.
apply typ_inv_subsumption with (2:=H).
2:discriminate.
apply typ_inv_fix; trivial.
Qed.


(************************************************************************)
(** Two examples of derived principles:
    - the standard recursor for Nat
    - subtraction with size information
*)

Section Example.

Definition nat_ind_typ K :=
   Prod (Prod (NatI Infty) K) (* P : nat -> Prop *)
  (Prod (App (Ref 0) Zero)
  (Prod (Prod (NatI Infty) (Prod (App (Ref 2) (Ref 0))
                        (App (Ref 3) (App (SuccI Infty) (Ref 1)))))
  (Prod (NatI Infty) (App (Ref 3) (Ref 0))))).

Definition nat_ind K :=
   Abs (*P*)(Prod (NatI Infty) K) (* P : nat -> Prop *)
  (Abs (*fZ*) (App (Ref 0) Zero)
  (Abs (*fS*) (Prod (*n*)(NatI Infty) (Prod (App (Ref 2) (Ref 0))
                                   (App (Ref 3) (App (SuccI Infty) (Ref 1)))))
  (NatFix Infty
    (*o,Hrec*)
    (Abs (*n*)(NatI (OSucc (Ref 1)))
      (Natcase
        (Ref 4)
        (*k*)(App (App (Ref 4) (Ref 0))
                  (App (Ref 2) (Ref 0)))
        (Ref 0)))))).

Lemma nat_ind_def e K (cK:forall f, noccur(B.cons false f)K) :
  typ_inv e (nat_ind K) (nat_ind_typ K).
assert (eq_term Nat (NatI Infty)).
 red; simpl.
 red; unfold NAT; reflexivity.
unfold nat_ind, nat_ind_typ.
apply typ_inv_abs; try discriminate.
 apply var_eq_noc; noc_tac.
 trivial.
(* *)
apply typ_inv_abs; try discriminate.
 apply var_eq_noc; noc_tac.
(* *)
apply typ_inv_abs; try discriminate.
 apply var_eq_noc; noc_tac.
(* *)
assert (e1 : eq_term (App (Ref 3) (Ref 0)) (subst_rec Infty 1 (App (Ref 4) (Ref 0)))).
 simpl.
 red; intros.
 unfold V.lams, V.shift; simpl.
 apply cc_app_morph; apply H0.
rewrite e1.
apply typ_inv_fix; auto.
 (* infty : infty *)
 apply typ_Infty.
 red; reflexivity.

 (* codom mono *)
 Focus 2.
 apply var_eq_sub.
 apply var_eq_noc.
 noc_tac.

 (* fix body *)
 apply typ_ext_abs; try discriminate.
  apply var_mono_NATi.
   apply typ_OSucc.
   apply typ_ord_ref with (OSucc Infty); auto.
    discriminate.
    red; simpl; auto.

   apply var_mono_OSucc.
   apply var_mono_ref; reflexivity.

  apply typ_inv_natcase with (Ref 2) (Ref 5); auto.
   eapply typ_ord_ref.
    simpl; reflexivity.
    discriminate.
    red; simpl; auto.

   apply var_mono_ref; simpl; reflexivity.

   (* eqtrm *)
   simpl tenv; apply sub_refl.
   red; simpl; intros; reflexivity.

   (* branch 0 *)
   eapply typ_inv_ref'.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.

    (* eqtrm *)
    apply sub_refl; red; simpl; intros.
    unfold V.lams, V.shift; simpl; reflexivity.

   (* branch S *)
   apply typ_inv_app with (App (Ref 6) (Ref 0))
     (App (Ref 7) (App (SuccI Infty) (Ref 1))); try discriminate.
    simpl tenv.
    apply sub_refl; red; intros; simpl.
    (* conversion (succ domain) *)
    unfold V.lams, V.shift; simpl.
    assert (i 0 ∈ NATi (i 3)).
     generalize (H0 0 _ (eq_refl _)); simpl.
     unfold V.lams, V.shift; simpl; trivial.
    rewrite beta_eq.
     rewrite beta_eq; auto with *.
     red; intros; apply inr_morph; trivial.

      red; intros; apply inr_morph; trivial.

     apply NATi_NAT in H1; trivial.
     generalize (H0 3 _ (eq_refl _)); simpl; intro.
     apply isOrd_inv with (osucc omega); auto.

    (**)
    apply typ_inv_app with (NatI Infty)
      (Prod (App (Ref 7) (Ref 0)) (App (Ref 8) (App (SuccI Infty) (Ref 1))));
      try discriminate.
     (* eqtrm *)
     apply sub_refl; red; intros; simpl.
     unfold V.lams, V.shift; simpl.
     reflexivity.

     eapply typ_inv_ref'.
      compute; reflexivity.
      simpl; reflexivity.
      discriminate.

      (* eqtrm *)
      apply sub_refl; red; intros; simpl.
      unfold V.shift, V.lams, V.shift; simpl.
      reflexivity.

     eapply typ_inv_ref'.
      compute; reflexivity.
      simpl; reflexivity.
      discriminate.

      (* subtyping: nat -> infty *)
      red; simpl; intros.
      unfold V.lams, V.shift in H1; simpl in H1.
      apply NATi_NAT in H1; trivial.
      generalize (H0 3 _ (eq_refl _)); simpl; intro.
      apply isOrd_inv with (osucc omega); auto.

    (**)
    eapply typ_inv_rec_call.
     compute; trivial.
     simpl; reflexivity.
     discriminate.
     2:simpl; reflexivity.
     discriminate.

     (* eqtrm *)
     apply sub_refl; red; intros; simpl.
     unfold V.lams, V.shift; simpl.
     reflexivity.

     eapply typ_inv_ref'.
      compute; reflexivity.
      simpl; reflexivity.
      discriminate.

      (* eqtrm *)
      apply sub_refl; red; intros; simpl.
      reflexivity.

   (* Scrutinee *)
   eapply typ_inv_ref'.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.

    (* eqtrm *)
    apply sub_refl; red; intros; simpl.
    reflexivity.
Qed.

(*
Lemma int_abs_eq : forall T M i i',
  int T i == int T i' ->
  (forall x, x ∈ int T i -> int M (V.cons x i) == int M (V.cons x i')) ->
  int (Abs T M) i == int (Abs T M) i'.
intros.
simpl.
apply cc_lam_ext.
 trivial.
red; intros.
transitivity (int M (V.cons x' i)).
 apply int_morph; auto with *.
 apply V.cons_morph; trivial.
 reflexivity.

 apply H0.
 rewrite <- H2; trivial.
Qed.
*)

(** Subtraction *)

Definition minus O :=
  NatFix O
    (*o,Hrec*)
    (Abs (*n*) (NatI (OSucc (Ref(*o*)1)))
    (Abs (*m*) (NatI Infty)
    (Natcase
       Zero
       (*n'*)
       (Natcase
         (Ref 2)
         (*m'*)
         (App (App (Ref(*minus*)4) (Ref(*n'*)1)) (Ref(*m'*)0))
         (Ref(*m*)1))
       (Ref(*n*)1)))).

Definition minus_typ O := Prod (NatI O) (Prod (NatI Infty) (NatI (lift 2 O))).

Lemma minus_def e O :
  typ_ord (tenv e) O ->
  var_equals e O ->
  typ_inv e (minus O) (minus_typ O).
intros tyO eqO.
unfold minus, minus_typ.
apply typ_inv_fix' with (Prod (NatI Infty) (NatI (Ref 2))); auto.
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
 apply var_mono_prod.
  apply var_eq_noc; noc_tac.

  apply var_mono_NATi; trivial.
   eapply typ_ord_ref.
    simpl; reflexivity.
    discriminate.

    apply typ_ord_lift; simpl.
    apply typ_OSucc; trivial.

   apply var_mono_ref.
   compute; reflexivity.

 (* fix body *)
 apply typ_ext_abs; try discriminate.
  apply var_mono_NATi.
   apply typ_OSucc.
   eapply typ_ord_ref.
    simpl; reflexivity.
    discriminate.

    apply typ_ord_lift; simpl.
    apply typ_OSucc; trivial.

   apply var_mono_OSucc; auto.
   apply var_mono_ref.
   compute; reflexivity.

 (* 2nd abs *)
 rewrite eq_lift_prod.
 rewrite eq_subst_prod.
 unfold lift1; rewrite eq_lift_prod.
 eapply typ_inv_subsumption.
 apply typ_inv_abs.
 5:discriminate.
  Focus 4.
  apply sub_refl.
  apply eq_typ_prod.
   red; intros; simpl; reflexivity.

   reflexivity.

  discriminate.

  apply var_eq_noc; noc_tac.

 (**)
 apply typ_inv_natcase with (Ref 3)
    (Abs (NatI (OSucc (Ref 3))) (NatI (OSucc (Ref 4)))); auto.
  eapply typ_ord_ref.
   simpl; reflexivity.
   discriminate.

   apply typ_ord_lift; simpl.
   apply typ_OSucc; trivial.

  apply var_mono_ref.
  compute; reflexivity.

  (* conversion *)
  apply sub_refl.
  rewrite eq_typ_betar.
  3:discriminate.
   red; intros; simpl.
   unfold V.lams, V.shift; simpl.
   reflexivity.

   apply typ_var0; split; [discriminate|].
   apply sub_refl.
   red; simpl; reflexivity.

  (* branch 0 *)
  eapply typ_inv_subsumption.
   apply typ_inv_Zero.
   eapply typ_ord_ref with (n:=3).
    simpl; reflexivity.
    discriminate.
    apply typ_ord_lift; simpl.
    apply typ_OSucc; trivial.

   2:discriminate.
   apply sub_refl.
   rewrite eq_typ_betar.
   3:discriminate.
    red; simpl; reflexivity.

    apply typ_Zero.
    eapply typ_ord_ref.
     simpl; reflexivity.
     discriminate.
     apply typ_ord_lift; simpl.
     apply typ_OSucc; trivial.

  (* branch S *)
  apply typ_inv_natcase with Infty
     (Abs (NatI (OSucc Infty)) (NatI (OSucc (Ref 5)))); auto.
   apply typ_Infty.

   red; simpl; reflexivity.

   apply sub_refl.
   rewrite eq_typ_betar.
   3:discriminate.
    unfold lift; rewrite eq_lift_abs.
    rewrite eq_typ_betar.
    3:discriminate.
     red; intros; simpl; reflexivity.

     apply typ_conv with (NatI (OSucc (lift_rec 1 0 (Ref 3)))).
     3:discriminate.
      apply typ_app_SuccI; trivial.
       apply typ_ord_lift; simpl.
       eapply typ_ord_ref.
        simpl; reflexivity.
        discriminate.
        apply typ_ord_lift; simpl.
        apply typ_OSucc; trivial.

       apply typ_var0; split;[discriminate|].
       apply sub_refl; red; intros; simpl.
       reflexivity.

     red; intros; simpl.
     reflexivity.

    apply typ_var0; split;[discriminate|].
    (* subtyping infty < infty+ *)
    red; simpl; intros.
    revert H0; apply TI_incl; auto with *.

  (* branch 0 *)
  eapply typ_inv_ref'.
   compute; reflexivity.
   simpl; reflexivity.
   discriminate.

   apply sub_refl.
   rewrite eq_typ_betar.
   3:discriminate.
    red; intros; simpl.
    unfold V.lams, V.shift; simpl; reflexivity.

    eapply typ_Zero; auto.
    apply typ_Infty.

  (* branch S *)    
  apply typ_inv_app with (NatI Infty) (NatI (Ref 6)).
   discriminate.
   discriminate.

   unfold lift; rewrite eq_lift_abs.
   apply sub_trans with (NatI (OSucc (Ref 5))).
    (* sub nat(o) < nat(o+) *)
    red; simpl; intros.
    unfold V.lams, V.cons, V.shift in H; simpl in H0.
    assert (isOrd (i 5)).
     assert (h := H 5 _ (refl_equal _)); simpl in h.
     apply isOrd_inv with (2:=h).
     apply isOrd_succ.
     rewrite <- int_lift_rec_eq.
     revert H; apply typ_ord_lift; simpl; trivial.
    revert H0; apply TI_incl; auto with *.

    apply sub_refl.
    rewrite eq_typ_betar.
    3:discriminate.
     red; intros; simpl.
     unfold V.lams, V.shift; simpl.
     reflexivity.

     apply typ_conv with (NatI (OSucc (lift_rec 1 0 Infty))).
     3:discriminate.
      apply typ_app_SuccI; auto.
       apply typ_Infty.

      apply typ_var0; split;[discriminate|].
      apply sub_refl; red; intros; simpl.
      reflexivity.

     red; intros; simpl.
     reflexivity.

   eapply typ_inv_rec_call.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.
    2:simpl; reflexivity.
    discriminate.

    apply sub_refl.
    unfold subst, lift1; rewrite eq_lift_prod.
    rewrite eq_subst_prod.
    red; intros; simpl; reflexivity.

    eapply typ_inv_ref'.
     compute; reflexivity.
     simpl; reflexivity.
     discriminate.

     apply sub_refl.
     red; intros; simpl; reflexivity.

     eapply typ_inv_ref'.
      compute; reflexivity.
      simpl; reflexivity.
      discriminate.

      apply sub_refl.
      red; intros; simpl; reflexivity.

   (**)
   eapply typ_inv_ref'.
    compute; reflexivity.
    simpl; reflexivity.
    discriminate.

    (* infty < infty+ *)
    red; simpl; intros.
    revert H0; apply TI_incl; auto with *.

  (**)
  eapply typ_inv_ref'.
   compute; reflexivity.
   simpl; reflexivity.
   discriminate.

   apply sub_refl.
   red; intros; simpl; reflexivity.
Qed.

End Example.

(* begin hide *)
Print Assumptions minus_def.
(* end hide *)
