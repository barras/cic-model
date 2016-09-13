Require SN_ECC_Real.
Import ZF ZFsum ZFnats ZFrelations ZFord ZFfix.
Require Import ZFfunext ZFcoc ZFuniv_real.
Import Sat.
Import SN_ECC_Real.

(********************************************************************************)
(** Occurrences *)

Module B := VarMap.Bool.


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


(********************************************************************************)
(** Judgements with variance *)

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
  [f,tf] \real int (Prod T U) i ->
  [g,tg] \real int (Prod T U) i' ->
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


Lemma El_sub e T i j i' j':
  fx_sub e T ->
  val_mono e i j i' j' ->
  El (int T i) ⊆ El (int T i').
intros.
apply H in H0.
red; intros.
apply H0 with daimont.
split;[trivial|apply varSAT].
Qed.
Lemma El_eq e T i j i' j':
  fx_equals e T ->
  val_mono e i j i' j' ->
  El (int T i) == El (int T i').
intros.
apply H in H0.
rewrite H0; reflexivity.
Qed.

Require Import Bool.

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
apply H1 with (I.cons daimont j) (I.cons daimont j').
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
destruct H1.
split.
 red.
 rewrite <- H0; trivial.

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
red in H0; specialize H0 with (1:=H2).
destruct H3.
red in H3.
rewrite El_int_prod in H3.
rewrite Real_int_prod in H4; trivial.
apply and_split; intros.
 red; rewrite El_int_prod.
 revert H3; apply cc_prod_covariant; intros.
  do 2 red; intros.
  rewrite H5; reflexivity.

  rewrite H0; reflexivity.

  apply El_sub with (1:=H1) (j:=I.cons daimont j) (j':=I.cons daimont j').
  apply val_push_var; auto with *.
   split;[trivial|apply varSAT].
   split;[|apply varSAT].
   red; rewrite <- H0; trivial.

 red in H5; rewrite El_int_prod in H5.
 rewrite Real_int_prod; trivial.
 revert t H4; apply piSAT0_mono with (f:=fun x=>x); intros; auto with *.
  rewrite H0; trivial.

  rewrite H0; reflexivity.

  rewrite <- H0 in H4.
  red; intros.
  apply H1 with (i:=V.cons x0 i) (j:=I.cons daimont j) (j':=I.cons daimont j').
   apply val_push_var; auto with *.
   split; trivial; apply varSAT.
   split.
    red; rewrite <- H0; trivial.
    apply varSAT.

   split; trivial.
   unfold inX; apply cc_prod_elim with (1:=H3); trivial.
Qed.

  (* Function subtyping *)

  Lemma fx_abs : forall e U T M,
    T <> kind ->
    fx_sub e T ->
    fx_equals (push_var e T) M ->
    typ (T::tenv e) M U ->
    U <> kind ->
    fx_extends e T (Abs T M).
unfold fx_equals, fx_extends; intros.
specialize El_sub with (1:=H0)(2:=H4); clear H0; intro H0.
simpl.
red; intros.
rewrite beta_eq; try assumption.
 assert (H5' := H0 _ H5).
 rewrite beta_eq; trivial.
  apply H1 with (I.cons daimont j) (I.cons daimont j').
  apply val_push_var; auto with *.
   split; [trivial|apply varSAT].

   split; [trivial|apply varSAT].

  red; red; intros.
  rewrite H7; reflexivity.

 red; red; intros.
 rewrite H7; reflexivity.
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

Lemma typ_impl_inj e M T :
  typ e M T ->
  typ_impl (tinj e) M T.
split; trivial.
red; intros.
apply int_morph; auto with *.
intros k.
generalize (proj2 (proj2 H0) k); simpl.
auto.
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


(** Variance and ordinals *)
Require Import SN_ord.

Definition typ_ord_mono (e:fenv) O :=
  fx_subval e O /\ typ_ord (tenv e) O.

Definition typ_ord_impl (e:fenv) O :=
  fx_equals e O /\ typ_ord (tenv e) O.

Lemma OSucc_subval e O :
  typ_ord (tenv e) O ->
  fx_subval e O ->
  fx_subval e (OSucc O).
unfold fx_subval; intros.
specialize H0 with (1:=H1).
destruct (H _ _ (proj1 H1)) as (?,_).
destruct (H _ _ (proj1 (proj2 H1))) as (?,_).
simpl.
apply osucc_mono; trivial.
Qed.

Hint Resolve OSucc_subval.

  Lemma typ_Ordt_ord e O o :
    isOrd o ->
    typ e O (Ordt o) ->
    typ_ord e O.
red; intros.
destruct H0 with (1:=H1) as (_,(?,?)).
simpl in H2; red in H2.
rewrite El_def in H2.
simpl in H3; rewrite Real_def in H3; trivial.
2:reflexivity.
apply sat_sn in H3; split; trivial.
apply cc_bot_ax in H2; destruct H2.
 rewrite H2; trivial.

 apply isOrd_inv with o; trivial.
Qed.

  Lemma OSucc_fx_sub : forall e O o,
    isOrd o ->
    zero ∈ o ->
    typ_monoval e O (Ordt o)->
    typ_monoval e (OSucc O) (Ordt (osucc o)).
destruct 3.
split.
 apply OSucc_subval; trivial.
 apply typ_Ordt_ord with o; trivial.

 red; simpl; intros.
 apply in_int_intro; try discriminate.
 destruct tyord_inv with (3:=H2)(4:=H3) as (_,(?,_)); trivial.
 assert (osucc (int O i) ∈ El (int (Ordt (osucc o)) i)).
  rewrite El_int_ord.
  apply lt_osucc_compat; trivial.
  apply ole_lts; auto.
 split; simpl; trivial.
 rewrite <- !tm_tmm.
 rewrite Real_def; auto with *.
  assert (h:= H2 _ _ H3).
  apply in_int_sn in h.
  simpl; trivial.

  simpl.
  apply cc_bot_intro.
  apply lt_osucc_compat; trivial.
Qed.
