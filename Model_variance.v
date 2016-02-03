Require Import Bool.
Require Import ZF ZFcoc ZFfunext.
Require Import ModelZF.

Import BuildModel.
Import T J R.

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

  Lemma noc_cst : forall f x, noccur f (cst x).
red; simpl; reflexivity.
Qed.

  Lemma noc_kind : forall f, noccur f kind.
red; simpl; reflexivity.
Qed.

  Lemma noc_prop : forall f, noccur f prop.
intros; apply noc_cst.
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
Definition val_mono (e:fenv) i i' :=
    val_ok (tenv e) i /\
    val_ok (tenv e) i' /\
    forall n,
    if ords e n then i n ⊆ i' n
    else match fixs e n with
      Some T => forall x, x ∈ int T (V.shift (S n) i) -> cc_app (i n) x == cc_app (i' n) x
    | _ => i n == i' n
    end.

Lemma val_mono_refl : forall e i,
  val_ok (tenv e) i -> val_mono e i i.
split;[idtac|split]; simpl; auto with *.
intro n.
destruct (ords e n); auto with *.
destruct (fixs e n); auto with *.
Qed.

Lemma val_push_var : forall e i i' x x' T,
  val_mono e i i' ->
  x == x' ->
  x ∈ int T i ->
  x' ∈ int T i' ->
  val_mono (push_var e T) (V.cons x i) (V.cons x' i').
destruct 1 as (?&?&?); split;[idtac|split]; trivial.
 unfold push_var; simpl.
 apply vcons_add_var; trivial.

 unfold push_var; simpl.
 apply vcons_add_var; trivial.

 destruct n as [|n]; simpl; auto.
 generalize (H1 n).
 destruct (ords e n); trivial.
Qed.

Lemma val_push_ord : forall e i i' x x' T,
  val_mono e i i' ->
  x ⊆ x' ->
  x ∈ int T i ->
  x' ∈ int T i' ->
  val_mono (push_ord e T) (V.cons x i) (V.cons x' i').
destruct 1 as (?&?&?); split;[idtac|split]; trivial.
 unfold push_ord; simpl.
 apply vcons_add_var; trivial.

 unfold push_ord; simpl.
 apply vcons_add_var; trivial.

 destruct n as [|n]; simpl; auto.
 generalize (H1 n).
 destruct (ords e n); trivial.
Qed.


Lemma val_push_fun : forall e i i' f g T U,
  val_mono e i i' ->
  f ∈ int (Prod T U) i ->
  g ∈ int (Prod T U) i' ->
  fcompat (int T i) f g ->
  val_mono (push_fun e T U) (V.cons f i) (V.cons g i').
destruct 1 as (?&?&?); split;[idtac|split]; trivial.
 unfold push_fun; simpl.
 apply vcons_add_var; trivial.

 unfold push_fun; simpl.
 apply vcons_add_var; trivial.

 destruct n as [|n]; simpl; auto.
 generalize (H1 n).
 destruct (ords e n); trivial.
Qed.

(** Invariance *)
Definition var_equals e M :=
  forall i i', val_mono e i i' -> int M i == int M i'.

(** Covariance judgment *)
Definition var_mono e M :=
  forall i i', val_mono e i i' ->
  int M i ⊆ int M i'.

(** Function Extension judgment *)
Definition var_ext e dom M :=
  forall i i', val_mono e i i' ->
  fcompat (int dom i) (int M i) (int M i').

Lemma El_sub e T i i':
  var_mono e T ->
  val_mono e i i' ->
  int T i ⊆ int T i'.
intros.
apply H in H0.
red; auto.
Qed.
Lemma El_eq e T i i':
  var_equals e T ->
  val_mono e i i' ->
  int T i == int T i'.
intros.
apply H in H0.
rewrite H0; reflexivity.
Qed.


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
apply cc_lam_ext; eauto.
red; intros.
apply H0.
specialize H with (1:=H1).
apply val_push_var; auto.
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
rewrite <- H3.
rewrite <- H; trivial.
Qed.

  Lemma var_eq_rec_call : forall e n x T U,
    ords e n = false ->
    fixs e n = Some T ->
    T <> kind ->
    typ (tenv e) (Ref n) (Prod (lift (S n) T) U) ->
    var_equals e x ->
    typ (tenv e) x (lift (S n) T) ->
    var_equals e (App (Ref n) x).
unfold var_equals; intros.
simpl.
specialize H3 with (1:=H5).
rewrite <- H3.
destruct H5 as (Hty,(Hty',Hrec)).
specialize Hrec with n.
rewrite H in Hrec; rewrite H0 in Hrec.
apply Hrec.
red in H4; specialize H4 with (1:=Hty); trivial.
apply in_int_not_kind in H4; trivial.
2:destruct T as [(T,Tm)|];simpl;[discriminate|elim H1;reflexivity].
unfold lift in H4; rewrite int_lift_rec_eq in H4.
rewrite V.lams0 in H4; trivial.
Qed.

  (** Covariance rules *)

  Lemma var_eq_sub : forall e M, var_equals e M -> var_mono e M.
unfold var_mono, var_equals; intros.
apply H in H0.
rewrite <- H0; reflexivity.
Qed.

  Lemma var_mono_ref : forall e n,
    ords e n = true ->
    var_mono e (Ref n).
unfold var_mono; intros.
destruct H0 as (_,(_,H0)).
generalize (H0 n); rewrite H.
simpl; intros; trivial.
Qed.

Lemma var_mono_prod : forall e T U,
  var_equals e T ->
  var_mono (push_var e T) U ->
  var_mono e (Prod T U).
red; red; intros.
red in H; specialize H with (1:=H1).
revert H2; simpl; apply cc_prod_covariant; intros.
 do 2 red; intros.
 rewrite H3; reflexivity.

 rewrite H; reflexivity.

 apply El_sub with (1:=H0).
 apply val_push_var; auto with *.
 rewrite <- H; trivial.
Qed.

  (** Function subtyping rules *)

  Lemma var_ext_abs : forall e U T M,
    var_mono e T ->
    var_equals (push_var e T) M ->
    typ (T::tenv e) M U ->
    var_ext e T (Abs T M).
unfold var_equals, var_ext; intros.
specialize El_sub with (1:=H)(2:=H2); clear H; intro H.
simpl.
red; intros.
rewrite cc_beta_eq; try assumption.
 assert (H3' := H _ H3).
 rewrite cc_beta_eq; trivial.
  apply H0.
  apply val_push_var; auto with *.

  red; red; intros.
  rewrite H5; reflexivity.

 red; red; intros.
 rewrite H5; reflexivity.
Qed.

(****************************************************************************************)
(** Compound judgements : typing + variance *)

Definition typ_equals e M T :=
  var_equals e M /\ typ (tenv e) M T.

Definition typ_mono e M T :=
  var_mono e M /\ typ (tenv e) M T.

Definition typ_ext e M A B :=
  var_ext e A M /\ typ (tenv e) M (Prod A B).

Instance typ_equals_morph e : Proper (eq_term ==> eq_term ==> iff) (typ_equals e).
apply morph_impl_iff2; auto with *.
do 4 red; intros.
destruct H1; split.
 red; intros.
 rewrite <- H; eauto.

 rewrite <- H; rewrite <- H0; eauto.
Qed.

(** ** Inference rules *)

(** Inclusion relation between judgements *)

  Lemma typ_eq_mono : forall e M T, typ_equals e M T -> typ_mono e M T.
destruct 1; split; trivial.
apply var_eq_sub; trivial.
Qed.

  Lemma typ_eq_ext : forall e M A B, typ_equals e M (Prod A B) -> typ_ext e M A B.
destruct 1; split; trivial.
do 2 red; intros.
apply H in H1.
rewrite H1; reflexivity.
Qed.

(** Subsumption *)
  Lemma typ_eq_subsumption e M T T' :
    typ_equals e M T -> sub_typ (tenv e) T T' -> T <> kind -> typ_equals e M T'.
destruct 1; split; trivial.
apply typ_subsumption with (2:=H1); trivial.
Qed.

(** Typing the three kind of variables *)

  Lemma typ_eq_ref : forall e n T,
    spec_var e n = false ->
    nth_error (tenv e) n = value T ->
    typ_equals e (Ref n) (lift (S n) T).
intros.
split.
 apply var_eq_noc; apply noc_var; trivial.
 apply typ_var; trivial.
Qed.

  Lemma typ_mono_ref : forall e n t T,
    ords e n = true ->
    nth_error (tenv e) n = value t ->
    T <> kind ->
    t <> kind ->
    sub_typ (tenv e) (lift (S n) t) T ->
    typ_mono e (Ref n) T.
intros.
split.
 apply var_mono_ref; trivial.

 apply typ_subsumption with (lift (S n) t); trivial.
  apply typ_var; trivial.

  destruct t as [(t,tm)|]; simpl in *; auto.
  discriminate.
Qed.

  Lemma typ_eq_abs : forall e s1 U T T' M,
    U <> kind ->
    s1=prop \/ s1=kind ->
    eq_typ (tenv e) T T' ->
    typ_equals e T s1 ->
    typ_equals (push_var e T) M U ->
    typ_equals e (Abs T M) (Prod T' U).
intros.
destruct H2; destruct H3.
split.
 apply var_eq_abs; trivial.

 apply typ_conv with (Prod T U); auto.
  apply typ_abs; trivial.

  apply eq_typ_prod; trivial.
  reflexivity.

 discriminate.
Qed.

  Lemma typ_ext_abs : forall e U T M,
    U <> kind ->
    typ_mono e T kind ->
    typ_equals (push_var e T) M U ->
    typ_ext e (Abs T M) T U.
intros.
destruct H0; destruct H1; split.
 apply var_ext_abs with U; trivial.

 apply typ_abs; trivial.
Qed.

Lemma typ_eq_app e u v V Ur T :
  V <> kind ->
  Ur <> kind ->
  sub_typ (tenv e) (subst v Ur) T ->
  typ_equals e u (Prod V Ur) ->
  typ_equals e v V ->
  typ_equals e (App u v) T.
intros Vnk Unk Tsub (uty,ueq) (vty,veq).
split.
 apply var_eq_app; trivial.

 apply typ_subsumption with (subst v Ur); trivial.
  apply typ_app with V; auto.

  destruct Ur as [(Ur,Urm)|]; simpl; trivial.
  discriminate.
Qed.


  Lemma typ_ext_app : forall e n x t u T,
    ords e n = false ->
    fixs e n = Some t ->
    T <> kind ->
    t <> kind ->
    u <> kind ->
    nth_error (tenv e) n = value (Prod t u) ->
    sub_typ (tenv e) (subst x (lift_rec (S n) 1 u)) T ->
    typ_equals e x (lift (S n) t) ->
    typ_equals e (App (Ref n) x) T.
intros.
destruct H6.
assert (typ (tenv e) (Ref n) (Prod (lift (S n) t) (lift_rec (S n) 1 u))).
 apply typ_var0; rewrite H4; split;[discriminate|].
 apply sub_refl.

 unfold lift; rewrite eq_lift_prod.
 reflexivity.
split.
 apply var_eq_rec_call with t (lift_rec (S n) 1 u); trivial.

 apply typ_subsumption with (subst x (lift_rec (S n) 1 u)); auto.
 2:destruct u as [(u,um)|]; trivial.
 2:discriminate.
 apply typ_app with (lift (S n) t); trivial.
 destruct t as [(t,tm)|]; trivial.
 discriminate.
Qed.


(** Derived rules for practical examples (basically applies subsumption beforehand) *)

  Lemma typ_eq_ref' : forall e n t T,
    spec_var e n = false ->
    nth_error (tenv e) n = value t ->
    t <> kind ->
    sub_typ (tenv e) (lift (S n) t) T ->
    typ_equals e (Ref n) T.
intros.
split.
 apply var_eq_noc; apply noc_var; trivial.

 apply typ_subsumption with (lift (S n) t); trivial.
  apply typ_var; trivial.

  destruct t as [(t,tm)|]; simpl in *; auto.
  discriminate.
Qed.

(*  Lemma typ_eq_app' : forall e u v V Ur T,
    V <> kind ->
    Ur <> kind ->
    sub_typ (tenv e) (subst v Ur) T ->
    typ_equals e u (Prod V Ur) ->
    typ_equals e v V ->
    typ_equals e (App u v) T.
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
*)
(*  Lemma typ_ext_app' e n x t u T :
    ords e n = false ->
    fixs e n = Some t ->
    t <> kind ->
    u <> kind ->
    nth_error (tenv e) n = value (Prod t u) ->
    sub_typ (tenv e) (subst x (lift1 (S n) u)) T ->
    typ_equals e x (lift (S n) t) ->
    typ_equals e (App (Ref n) x) T.
intros.
apply typ_eq_subsumption with (2:=H4).
 eapply typ_ext_app with (8:=H5); trivial.
  destruct t as [(t,tm)|]; simpl; trivial; discriminate.

  eapply typ_ext_ref with (4:=H3); trivial.

 destruct u as [(u,um)|]; simpl; trivial; discriminate.
Qed.
*)
