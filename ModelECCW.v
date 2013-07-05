(** Strong normalization of the model of CC+W in the type-based
  termination presentation.
*)

Require Import List Bool Models.
Require Import ZF ZFsum ZFnats ZFrelations ZFord ZFfix ZFgrothendieck.
Require Import ZFfunext ZFind_w.
Require Import ModelZF.

Import BuildModel.
Import T J R.

(** Derived rules of the basic judgements *)

Lemma typ_var0 : forall e n T,
  match T, nth_error e n with
    Some _, value T' => T' <> kind /\ sub_typ e (lift (S n) T') T
  | _,_ => False end ->
  typ e (Ref n) T.
intros.
case_eq T; intros.
 rewrite H0 in H.
 case_eq (nth_error e n); intros.
  rewrite H1 in H.
  destruct H.
  apply typ_subsumption with (lift (S n) t); auto.
   apply typ_var; trivial.

   destruct t as [(t,tm)|]; simpl; try discriminate.
   elim H; trivial.

  rewrite H1 in H; contradiction.

 rewrite H0 in H; contradiction.
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
unfold prod, ZFuniv_real.prod in H2; rewrite El_def in H2.
apply cc_eta_eq in H2; trivial.
Qed.
*)

(** Universes *)
(*
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
*)

(** Ordinals *)

Definition Ordt (o:set) : term := cst o.

Definition typ_ord_kind : forall e o, typ e (Ordt o) kind.
red; simpl; trivial.
Qed.

(*Lemma El_int_ord o i :
  zero ∈ o ->
  El (int (Ordt o) i) == o.*)

Definition OSucc : term -> term.
(*begin show*)
intros o; left; exists (fun i => osucc (int o i)).
(*end show*)
do 2 red; intros.
rewrite H; reflexivity.
Defined.

(*Lemma El_int_osucc O' i :
  El (int (OSucct O') i) == osucc (int O' i).
*)

Lemma tyord_inv : forall e i o o',
  isOrd o' ->
  typ e o (Ordt o') ->
  val_ok e i ->
  isOrd (int o i) /\ int o i < o'.
unfold typ; simpl; intros.
unfold ZFnats.lt.
red in H0.
split; auto.
apply isOrd_inv with o'; trivial.
apply H0; trivial.
Qed.

(** W *)

Section Wtypes_typing.

Variable o : set.
Hypothesis oo : isOrd o.

Variable e:env.

Variable A B:term.
Hypothesis Ank : A <> kind.
Hypothesis Bnk : B <> kind.

Let Aw i := int A i.
Let Bw i x := int B (V.cons x i).
Let Ww i := W (Aw i) (Bw i).

Definition WF' i := W_F (Aw i) (Bw i).

Instance Aw_morph : Proper (eq_val==>eq_set) Aw.
do 2 red; intros.
apply int_morph; auto with *.
Qed.

Instance Bw_morph : Proper (eq_val==>eq_set==>eq_set) Bw.
do 3 red; intros.
unfold Bw.
rewrite H; rewrite H0; reflexivity.
Qed.

Instance WF'_morph : Proper (eq_val ==> eq_set ==> eq_set) WF'.
do 3 red; intros.
unfold WF'.
apply W_F_ext; trivial.
 apply Aw_morph; trivial.

 red; intros.
 apply Bw_morph; trivial.
Qed.

Definition WI (O:term) : term.
(*begin show*)
left; exists (fun i => TI (WF' i) (int O i)).
(*end show*)
do 3 red; intros.
apply TI_morph_gen.
 apply WF'_morph; trivial.

 rewrite H; reflexivity.
Defined.

(*Lemma El_int_W O i :
  El (int (WI O) i) == cc_bot (TI (WF' i) (int O i)).
*)

Lemma typ_WI : forall eps O,
  isOrd eps ->
  typ e O (Ordt eps) ->
  typ e (WI O) kind.
red; simpl; trivial.
Qed.

(** Constructor *)

Require Import ZFpairs.

Definition Wc (x:term) (f:term) : term.
(* begin show *)
left; exists (fun i => couple (int x i) (int f i)).
(* end show *)
do 2 red; intros; apply couple_morph; apply int_morph; auto with *.
Defined.


Lemma in_int_not_kind T i x :
  el T i x ->
  T <> kind ->
  x ∈ int T i.
destruct T as [(?,?)|]; simpl; intros; trivial.
elim H0; trivial.
Qed.

Lemma El_int_arr T U i :
  int (Prod T (lift 1 U)) i == cc_arr (int T i) (int U i).
simpl.
apply cc_prod_ext.
 reflexivity.

 red; intros.
 rewrite simpl_int_lift.
 rewrite lift0_term; reflexivity.
Qed.

Lemma typ_Wc : forall O X F,
  typ e O (Ordt o) ->
  typ e X A ->
  typ e F (Prod (subst X B) (lift 1 (WI O))) ->
  typ e (Wc X F) (WI (OSucc O)).
red; intros.
red in H0; specialize H0 with (1:=H2).
apply in_int_not_kind in H0; trivial.
red in H1; specialize H1 with (1:=H2).
apply in_int_not_kind in H1.
2:discriminate.
destruct tyord_inv with (2:=H)(3:=H2) as (?,?); trivial.
apply in_int_el.
assert (couple (int X i) (int F i) ∈ TI (WF' i) (osucc (int O i))).
 apply TI_intro with (int O i); auto.
  apply WF'_morph; reflexivity.

  unfold WF'.
  apply couple_intro_sigma.
   do 2 red; intros.
   rewrite H6; reflexivity.

   apply H0.

   rewrite El_int_arr in H1.
   rewrite int_subst_eq in H1.
   trivial.
assumption.
Qed.


(* Case analysis *)


Definition W_CASE b w :=
  sigma_case (fun x f => cc_app (cc_app b x) f) w.

Definition Wcase (b n : term) : term.
(*begin show*)
left; exists (fun i => W_CASE (int b i) (int n i)).
(*end show*)
do 3 red; intros.
apply sigma_case_morph.
 do 2 red; intros.
 rewrite H; rewrite H0; rewrite H1; reflexivity.

 rewrite H; reflexivity.
Defined.

Instance Wcase_morph :
  Proper (eq_term ==> eq_term ==> eq_term) Wcase.
do 3 red; simpl; intros.
red; intros.
 unfold sigma_case.
 apply cond_set_morph.
  rewrite H0; rewrite H1; reflexivity.
  rewrite H; rewrite H0; rewrite H1; reflexivity.
Qed.

Existing Instance Wcase_morph.

Lemma Wcase_iota : forall X F G,
  eq_typ e (Wcase G (Wc X F)) (App (App G X) F).
red; intros.
simpl.
unfold W_CASE.
rewrite sigma_case_couple with (a:=int X i) (b:=int F i).
 reflexivity.

 do 3 red; intros.
 rewrite H0; rewrite H1; reflexivity.

 reflexivity.
Qed.


Lemma typ_Wcase : forall P O G n,
  typ e O (Ordt o) ->
  typ e G (Prod A (Prod (Prod B (lift 2 (WI O))) (App (lift 2 P) (Wc (Ref 1) (Ref 0))))) ->
  typ e n (WI (OSucc O)) ->
  typ e (Wcase G n) (App P n).
red; intros.
destruct tyord_inv with (2:=H)(3:=H2) as (?,?); trivial.
red in H0; specialize H0 with (1:=H2).
apply in_int_not_kind in H0;[|discriminate].
red in H1; specialize H1 with (1:=H2).
apply in_int_not_kind in H1;[|discriminate].
apply in_int_el.
simpl int in H0.
simpl in H1.
red; simpl.
rewrite TI_mono_succ in H1; auto with *.
2:apply W_F_mono; trivial.
2:apply Bw_morph; reflexivity.
assert (fst (int n i) ∈ Aw i).
 apply fst_typ_sigma in H1; trivial.
 assert (snd (int n i) ∈ cc_arr (Bw i (fst (int n i))) (TI (WF' i) (int O i))).
  apply snd_typ_sigma with (y:=fst(int n i)) in H1; auto with *.
  do 2 red; intros.
  rewrite H7; reflexivity.
 assert (int n i == couple (fst (int n i)) (snd (int n i))).
  apply (surj_pair _ _ _ (subset_elim1 _ _ _ H1)).
 unfold W_CASE, sigma_case.
 rewrite cond_set_ok; trivial.
 specialize cc_prod_elim with (1:=H0) (2:=H5); clear H0; intro H0.
 apply eq_elim with
    (cc_app (int (lift 2 P) (V.cons (snd (int n i)) (V.cons (fst (int n i)) i)))
       (couple (fst (int n i)) (snd (int n i)))).
  apply cc_app_morph; auto with *.
  do 2 rewrite simpl_int_lift.
  rewrite lift0_term; reflexivity.

  apply cc_prod_elim with (1:=H0).
  revert H6; apply eq_elim.
  apply cc_prod_ext.
   reflexivity.

   red; intros.
   rewrite V.lams0.
   reflexivity.
Qed.
(*Print Assumptions typ_Wcase.*)

Lemma typ_Wcase' : forall P O G n T,
  T <> kind ->
  typ e O (Ordt o) ->
  sub_typ e (App P n) T -> 
  typ e G (Prod A (Prod (Prod B (lift 2 (WI O))) (App (lift 2 P) (Wc (Ref 1) (Ref 0))))) ->
  typ e n (WI (OSucc O)) ->
  typ e (Wcase G n) T.
intros.
apply typ_subsumption with (App P n); auto.
2:discriminate.
apply typ_Wcase with O; trivial.
Qed.

End Wtypes_typing.

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
  T <> kind ->
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
  T <> kind ->
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

(** Function Extension judgment *)
Definition fx_extends e dom M :=
  forall i i', val_mono e i i' ->
  fcompat (int dom i) (int M i) (int M i').

(** Covariance judgment *)
Definition fx_sub e M :=
  forall i i', val_mono e i i' ->
  forall x, x ∈ int M i -> x ∈ int M i'.

(** Invariance *)
Definition fx_equals e M :=
  forall i i', val_mono e i i' -> int M i == int M i'.


Lemma El_sub e T i i':
  fx_sub e T ->
  val_mono e i i' ->
  int T i ⊆ int T i'.
intros.
apply H in H0.
red; auto.
Qed.
Lemma El_eq e T i i':
  fx_equals e T ->
  val_mono e i i' ->
  int T i == int T i'.
intros.
apply H in H0.
rewrite H0; reflexivity.
Qed.


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
apply cc_lam_ext; eauto.
red; intros.
apply H1.
specialize H0 with (1:=H2).
apply val_push_var; auto.
rewrite <- H4; rewrite <- H0; trivial.
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
2:destruct T as [(T,Tm)|];simpl;[discriminate|elim H1;reflexivity].
unfold lift in H4; rewrite int_lift_rec_eq in H4.
rewrite V.lams0 in H4; trivial.
Qed.

  (* Covariance *)

  Lemma fx_equals_sub : forall e M, fx_equals e M -> fx_sub e M.
unfold fx_sub, fx_equals; intros.
apply H in H0.
rewrite <- H0; trivial.
Qed.

  Lemma var_sub : forall e n,
    ords e n = true ->
    fx_sub e (Ref n).
unfold fx_sub; intros.
destruct H0 as (_,(_,H0)).
generalize (H0 n); rewrite H.
simpl; intros.
apply H2; trivial.
Qed.

Lemma fx_sub_prod : forall e T U,
  T <> kind ->
  fx_equals e T ->
  fx_sub (push_var e T) U ->
  fx_sub e (Prod T U).
red; intros.
red in H0; specialize H0 with (1:=H2).
revert H3; simpl; apply cc_prod_covariant; intros.
 do 2 red; intros.
 rewrite H4; reflexivity.

 rewrite H0; reflexivity.

 apply El_sub with (1:=H1).
 apply val_push_var; auto with *.
 rewrite <- H0; trivial.
Qed.


  Lemma Wi_sub : forall e o A B O,
    isOrd o ->
    A <> kind ->
    typ (tenv e) O (Ordt o) ->
    fx_equals e A ->
    fx_equals (push_var e A) B ->
    fx_sub e O ->
    fx_sub e (WI A B O).
unfold fx_sub, fx_sub.
intros e o A B O oo Ank tyO eqA eqB subO i i' val_m x xty.
destruct tyord_inv with (2:=tyO) (3:=proj1 val_m); trivial.
destruct tyord_inv with (2:=tyO) (3:=proj1 (proj2 val_m)); trivial.
red in eqA; specialize eqA with (1:=val_m).
specialize subO with (1:=val_m).
assert (x ∈ TI (WF' A B i') (int O i)).
 revert xty; simpl; apply eq_elim.
 apply TI_morph_gen; auto with *.
  red; intros.
  apply W_F_ext; auto with *.
  red; intros.
  apply eqB.
  apply val_push_var; auto with *.
  rewrite H5 in H4.
  rewrite eqA in H4; trivial.

  reflexivity.

 revert H3; apply TI_mono; trivial.
 apply W_F_mono.
 apply Bw_morph; reflexivity.
Qed.

  Lemma OSucc_sub : forall e O,
    fx_sub e O ->
    fx_sub e (OSucc O).
unfold fx_sub; simpl; intros.
unfold osucc in H1|-*.
rewrite subset_ax in H1 |-*.
destruct H1; split; auto.
revert H1; apply power_mono.
red; intros; eauto.
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
rewrite cc_beta_eq; try assumption.
 assert (H5' := H0 _ H5).
 rewrite cc_beta_eq; trivial.
  apply H1.
  apply val_push_var; auto with *.

  red; red; intros.
  rewrite H7; reflexivity.

 red; red; intros.
 rewrite H7; reflexivity.
Qed.

(*****************************************************************************)
(** Recursor (without case analysis) *)

(* WFix O M is a fixpoint of domain WI O with body M *)
Definition WFix (O M:term) : term.
(*begin show*)
left.
exists (fun i =>
         WREC (fun o' f => int M (V.cons f (V.cons o' i))) (int O i)).
(*end show*)
do 2 red; intros.
unfold WREC.
unfold ZFfixrec.REC.
apply TR_morph.
2:rewrite H; reflexivity.
do 2 red; intros.
apply sup_morph; trivial.
red; intros.
apply int_morph; auto with *.
apply V.cons_morph.
 apply H0; trivial.
apply V.cons_morph; trivial.
Defined.


(** Typing rules of WFix *)

Section WFixRules.

  Variable infty : set.
  Hypothesis infty_ord : isOrd infty.
  Variable E : fenv.
  Let e := tenv E.
  Variable A B O U M : term.
  Hypothesis A_nk : A <> kind.
  Hypothesis Aeq : fx_equals E A.
  Hypothesis Beq : fx_equals (push_var E A) B.

  Definition WIL n := WI (lift n A) (lift_rec n 1 B).

  Hypothesis ty_O : typ e O (Ordt infty).
  Hypothesis ty_M : typ (Prod (WIL 1 (Ref 0)) U::OSucc O::e)
    M (Prod (WIL 2 (OSucc (Ref 1)))
         (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U)))).

  Hypothesis stab : fx_extends
    (push_fun (push_ord E (OSucc O)) (WIL 1 (Ref 0)) U)
    (WIL 2 (OSucc (Ref 1)))
    M.

  Lemma WF'mono i : Proper (incl_set==>incl_set) (WF' A B i).
do 2 red; intros.
unfold WF'.
apply W_F_mono; trivial.
do 2 red; intros; apply Bw_morph; auto with *.
Qed.
  Hint Resolve WF'mono.

  Let Wi i o := TI (WF' A B i) o.
  Let F i := fun o' f => int M (V.cons f (V.cons o' i)).
  Let U' i := fun o' x => int U (V.cons x (V.cons o' i)).

  Local Instance U'morph : forall i, morph2 (U' i).
do 3 red; intros; unfold U'.
rewrite H; rewrite H0; reflexivity.
Qed.
  Instance morph_fix_body : forall i, morph2 (F i).
unfold F; do 3 red; intros.
rewrite H; rewrite H0; reflexivity.
Qed.
  Lemma ext_fun_ty : forall o i,
    ext_fun (Wi i o) (U' i o).
do 2 red; intros.
rewrite H0;reflexivity.
Qed.
  Hint Resolve U'morph morph_fix_body ext_fun_ty.


  Hypothesis fx_sub_U :
    fx_sub (push_var (push_ord E (OSucc O)) (WIL 1 (OSucc (Ref 0)))) U.


Lemma El_int_W_lift O' n i :
  int (WIL n O') i == TI (WF' A B (V.shift n i)) (int O' i).
unfold WIL; simpl.
apply TI_morph_gen; auto with *.
2:reflexivity.
red; intros.
unfold WF'; apply W_F_ext; auto with *.
 unfold lift; rewrite int_lift_rec_eq; rewrite V.lams0; reflexivity.

 red; intros.
 rewrite int_lift_rec_eq.
 rewrite <- V.cons_lams.
 2:apply V.shift_morph; trivial.
 rewrite V.lams0.
 rewrite H1; reflexivity.
Qed.

  Lemma val_mono_1 i i' y y' f g:
    val_mono E i i' ->
    isOrd (int O i) ->
    isOrd (int O i') ->
    int O i ⊆ int O i' ->
    isOrd y ->
    isOrd y' ->
    y ⊆ int O i ->
    y' ⊆ int O i' ->
    y ⊆ y' ->
    f ∈ cc_prod (Wi i y) (U' i y) ->
    g ∈ cc_prod (Wi i' y') (U' i' y') ->
    fcompat (Wi i y) f g ->
    val_mono (push_fun (push_ord E (OSucc O)) (WIL 1 (Ref 0)) U)
      (V.cons f (V.cons y i)) (V.cons g (V.cons y' i')).
intros is_val Oo Oo' oo' yo y'o yO y'O yy' fty gty eqfg.
apply val_push_fun.
 apply val_push_ord; auto.
 3:discriminate.
  apply ole_lts; trivial.

  apply ole_lts; trivial.

 revert fty; apply eq_elim; apply cc_prod_ext; intros.
  rewrite El_int_W_lift; reflexivity.

  apply ext_fun_ty.

 revert gty; apply eq_elim; apply cc_prod_ext; intros.
  rewrite El_int_W_lift; reflexivity.

  apply ext_fun_ty.

 rewrite El_int_W_lift.
 trivial.
Qed.

  Lemma val_mono_2 i y y' n n':
    val_ok e i ->
    isOrd (int O i) ->
    isOrd y ->
    isOrd y' ->
    y ⊆ y' ->
    y' ⊆ int O i ->
    n ∈ Wi i y ->
    n == n' ->
    val_mono (push_var (push_ord E (OSucc O)) (WIL 1 (OSucc (Ref 0))))
      (V.cons n (V.cons y i)) (V.cons n' (V.cons y' i)).
Proof.
intros.
apply val_push_var; auto with *.
 4:discriminate.
 apply val_push_ord; auto with *.
  4:discriminate.
  apply val_mono_refl; trivial.

  apply ole_lts; auto.
  transitivity y'; trivial.

  apply ole_lts; auto.

 red; rewrite El_int_W_lift.
 revert H5; apply TI_incl; simpl; auto.

 red; rewrite El_int_W_lift.
 rewrite <- H6.
 revert H5; apply TI_incl; simpl; auto.
 apply ole_lts; trivial.
Qed.


  Lemma fix_codom_mono : forall o o' x x' i,
   val_ok e i ->
   isOrd o' ->
   o' ⊆ int O i ->
   isOrd o ->
   o ⊆ o' ->
   x ∈ Wi i o ->
   x == x' ->
   U' i o x ⊆ U' i o' x'.
Proof.
intros.
red in fx_sub_U.
assert (val_mono (push_var (push_ord E (OSucc O)) (WIL 1(OSucc(Ref 0))))
  (V.cons x (V.cons o i)) (V.cons x' (V.cons o' i))).
 apply val_mono_2; trivial.
 apply ty_O in H.
 apply in_int_not_kind in H;[|discriminate].
 apply isOrd_inv with infty; auto.
red; intros.
apply fx_sub_U with (x:=z) in H6; trivial.
Qed.

  Lemma ty_fix_body : forall i o f,
   val_ok e i ->
   o < osucc (int O i) ->
   f ∈ cc_prod (Wi i o) (U' i o) ->
   F i o f ∈ cc_prod (Wi i (osucc o)) (U' i (osucc o)).
unfold F; intros.
destruct tyord_inv with (2:=ty_O) (3:=H); trivial.
assert (val_ok (Prod (WIL 1 (Ref 0)) U::OSucc O::e) (V.cons f (V.cons o i))).
 apply vcons_add_var; auto.
  apply vcons_add_var; auto.

  red; revert H1; apply eq_elim.
  apply cc_prod_ext.
   rewrite El_int_W_lift.
   reflexivity.

   apply ext_fun_ty.
red in ty_M.
specialize ty_M with (1:=H4).
apply in_int_not_kind in ty_M.
2:discriminate.
revert ty_M; apply eq_elim.
symmetry; apply cc_prod_ext.
 rewrite El_int_W_lift.
 reflexivity.

 red; intros.
 rewrite int_lift_rec_eq.
 rewrite int_subst_rec_eq.
 rewrite int_lift_rec_eq.
 apply int_morph; auto with *.
 do 3 red.
 intros [|[|k]].
  compute; trivial.

  unfold V.lams, V.shift; simpl.
  reflexivity.

  unfold V.lams, V.shift; simpl.
  replace (k-0) with k; auto with *.
Qed.

  Lemma fix_body_irrel : forall i,
    val_ok e i ->
    Wi_ord_irrel (int A i)
      (fun x => int B (V.cons x i)) (int O i)
      (F i) (U' i).
red; intros.
assert (isOrd (int O i)).
 apply ty_O in H.
 apply isOrd_inv with infty; auto.
red in stab.
assert (Hstab := stab (V.cons f (V.cons o i)) (V.cons g (V.cons o' i))).
red in Hstab.
red; intros.
eapply Hstab; clear Hstab; trivial.
 apply val_mono_1; auto with *.
  apply val_mono_refl; exact H.

  transitivity o'; trivial.

 rewrite El_int_W_lift; auto.
Qed.

  Hint Resolve morph_fix_body ext_fun_ty ty_fix_body fix_codom_mono fix_body_irrel.


Let fix_typ o i:
  val_ok e i ->
  isOrd o ->
  isOrd (int O i) ->
  o ⊆ int O i ->
  WREC (F i) o ∈ cc_prod (Wi i o) (U' i o).
intros.
eapply WREC_wt with (U:=U' i); trivial.
 do 2 red; intros.
 apply Bw_morph; auto with *.

 intros.
 apply fix_codom_mono with (1:=H); trivial.
 transitivity o; auto.

 intros.
 apply ty_fix_body with (1:=H); trivial.
 apply ole_lts; trivial.
 transitivity o; trivial.

 red; intros; apply fix_body_irrel with (1:=H); trivial.
 transitivity o; trivial.
Qed.


  Lemma fix_irr i o o' x :
    val_ok e i ->
    isOrd o ->
    isOrd o' ->
    isOrd (int O i) ->
    o ⊆ o' ->
    o' ⊆ int O i ->
    x ∈ Wi i o ->
    cc_app (WREC (F i) o) x == cc_app (WREC (F i) o') x.
intros.
assert (WRECi := WREC_irrel).
red in WRECi.
apply WRECi with 
  (A:=int A i) (B:=fun x=>int B (V.cons x i))
  (ord:=int O i) (U:=U' i); auto with *.
 do 2 red; intros; apply Bw_morph; auto with *.

 intros.
 apply ty_fix_body with (1:=H); trivial.
 apply ole_lts; trivial.
Qed.

Lemma fix_eqn0 : forall i o,
  val_ok e i ->
  isOrd o ->
  isOrd (int O i) ->
  o ⊆ int O i ->
  WREC (F i) (osucc o) == F i o (WREC (F i) o).
intros.
unfold WREC at 1.
rewrite ZFfixrec.REC_eq; auto with *.
rewrite eq_set_ax; intros z.
rewrite sup_ax; auto with *.
split; intros.
 destruct H3 as (o',o'lt,zty).
 assert (o'o : isOrd o') by eauto using isOrd_inv.
 assert (o'le : o' ⊆ o) by (apply olts_le; auto).
 assert (o'le' : o' ⊆ int O i) by (transitivity o; trivial).
 assert (F i o' (WREC (F i) o') ∈ cc_prod (TI (WF' A B i) (osucc o')) (U' i (osucc o'))).
  apply ty_fix_body with (1:=H); trivial.
   apply ole_lts; auto.

   apply fix_typ with (1:=H); trivial.
 assert (F i o (WREC (F i) o) ∈ cc_prod (TI (WF' A B i) (osucc o)) (U' i (osucc o))).
  apply ty_fix_body with (1:=H); trivial.
   apply ole_lts; auto.

   apply fix_typ with (1:=H); trivial.
 rewrite cc_eta_eq with (1:=H3) in zty.
 rewrite cc_eta_eq with (1:=H4).
 rewrite cc_lam_def in zty|-*.
 2:intros ? ? _ eqn; rewrite eqn; reflexivity.
 2:intros ? ? _ eqn; rewrite eqn; reflexivity.
 destruct zty as (n', n'ty, (y, yty, eqz)).
 exists n'.
  revert n'ty; apply TI_mono; auto with *.
  apply osucc_mono; auto.
 exists y; trivial.
 revert yty; apply eq_elim.
 assert (firrel := fix_body_irrel).
 do 2 red in firrel.
 apply firrel with (1:=H); auto.
  apply fix_typ with (1:=H); auto.
  apply fix_typ with (1:=H); auto.

  clear firrel.
  red; intros.
  apply fix_irr with (1:=H); trivial.

 exists o;[apply lt_osucc;trivial|trivial].
Qed.

Lemma fix_eqn : forall i o n,
  val_ok e i ->
  isOrd o ->
  isOrd (int O i) ->
  o ⊆ int O i ->
  n ∈ TI (WF' A B i) (osucc o) ->
  cc_app (WREC (F i) (osucc o)) n ==
  cc_app (F i o (WREC (F i) o)) n.
intros.
rewrite fix_eqn0 with (1:=H); trivial.
unfold F.
reflexivity.
Qed.

Lemma typ_wfix :
  typ e (WFix O M) (Prod (WI A B O) (subst_rec O 1 U)).
red; intros.
destruct tyord_inv with (2:=ty_O)(3:=H); trivial.
apply in_int_el.
eapply eq_elim.
2:simpl.
2:apply fix_typ with (1:=H); auto with *.
2:reflexivity.
apply cc_prod_ext.
 reflexivity.

 red; intros.
 rewrite int_subst_rec_eq.
 rewrite <- V.cons_lams.
 2:apply V.cons_morph; reflexivity.
 rewrite V.lams0.
 rewrite H3; reflexivity.
Qed.

(** Fixpoint equation. *)
Lemma wfix_eq : forall N,
  typ e N (WI A B O) ->
  eq_typ e (App (WFix O M) N)
           (App (subst O (subst (lift 1 (WFix O M)) M)) N).
intros N tyN.
red; intros.
red.
change
 (cc_app (WREC (F i) (int O i)) (int N i) ==
  cc_app (int (subst O (subst (lift 1 (WFix O M)) M)) i) (int N i)).
do 2 rewrite int_subst_eq.
rewrite simpl_int_lift.
rewrite lift0_term.
red in tyN; specialize tyN with (1:=H).
apply in_int_not_kind in tyN.
2:discriminate.
destruct tyord_inv with (2:=ty_O)(3:=H); trivial.
simpl in tyN.
apply TI_elim in tyN; auto.
destruct tyN as (o,oly,nty).
assert (oo: isOrd o) by eauto using isOrd_inv.
rewrite <- TI_mono_succ in nty; auto with *.
rewrite <- fix_irr with (1:=H)(o:=osucc o); auto with *.
2:apply olts_le.
2:apply lt_osucc_compat; auto.
rewrite fix_eqn with (1:=H); auto with *.
eapply fix_body_irrel with (1:=H); auto with *.
 apply fix_typ with (1:=H); trivial.
 red; intros; apply isOrd_trans with o; trivial.

 simpl.
 apply fix_typ with (1:=H); auto with *.

 red; simpl; intros.
 apply fix_irr with (1:=H); auto with *.
 reflexivity.
Qed.


Lemma wfix_extend :
  fx_sub E O ->
  fx_extends E (WI A B O) (WFix O M).
intro subO.
do 2 red; intros.
assert (isval := proj1 H).
assert (isval' := proj1 (proj2 H)).
assert (oo: isOrd (int O i)).
 destruct tyord_inv with (2:=ty_O) (3:=isval); trivial.
assert (oo': isOrd (int O i')).
 destruct tyord_inv with (2:=ty_O) (3:=isval'); trivial.
assert (inclo: int O i ⊆ int O i').
 apply subO in H; trivial.
clear subO.
change (cc_app (WREC (F i) (int O i)) x == cc_app (WREC (F i') (int O i')) x).
revert x H0.
change (int (WI A B O) i) with (Wi i (int O i)).
elim oo using isOrd_ind; intros.
simpl in H3; apply TI_elim in H3; auto.
destruct H3 as (o',?,?).
assert (o_o' : isOrd o') by eauto using isOrd_inv.
assert (o'_y : osucc o' ⊆ y).
 red; intros; apply le_lt_trans with o'; auto.
rewrite <- TI_mono_succ in H4; auto.
rewrite <- fix_irr with (1:=isval) (o:=osucc o'); auto.
rewrite fix_eqn with (1:=isval); auto.
 assert (TIeq: forall o', isOrd o' -> TI (WF' A B i) o' == TI (WF' A B i') o').
  intros; apply TI_morph_gen; auto with *.
  red; intros.
  apply W_F_ext; trivial.
   apply (Aeq _ _ H).

   red; intros.
   eapply Beq.
   apply val_push_var with (1:=H); trivial.
    rewrite (Aeq _ _ H) in H7.
    rewrite H8 in H7; trivial.

assert (x ∈ TI (WF' A B i') (osucc o')).
 rewrite <- TIeq; auto.
rewrite <- fix_irr with (1:=isval') (o:=osucc o'); auto with *.
2:red; intros; apply le_lt_trans with o' ;auto.
2:apply inclo; apply H1; trivial.
rewrite fix_eqn with (1:=isval'); auto.
assert (irr := stab).
do 2 red in irr.
eapply irr.
2:rewrite El_int_W_lift; trivial.
apply val_mono_1 with (1:=H); auto with *.
do 2 red; intros.
rewrite H2; trivial.
symmetry; apply fix_irr with (1:=proj1(proj2 H)); auto with *.
revert H6; apply eq_elim.
apply TIeq; trivial.
Qed.


Lemma wfix_equals :
  fx_equals E O ->
  fx_equals E (WFix O M).
red; intros.
assert (fxs: fx_sub E O).
 apply fx_equals_sub; trivial.
apply wfix_extend in fxs.
red in fxs.
specialize fxs with (1:=H0).
apply fcompat_typ_eq with (3:=fxs).
 eapply cc_prod_is_cc_fun.
 assert (h := typ_wfix _ (proj1 H0)).
 apply in_int_not_kind in h.
 2:discriminate.
 exact h.

 setoid_replace (int (WI A B O) i) with (int (WI A B O) i').
  eapply cc_prod_is_cc_fun.
  assert (h := typ_wfix _ (proj1 (proj2 H0))).
  apply in_int_not_kind in h.
  2:discriminate.
  exact h.
 do 2 red.
 assert (h:= H _ _ H0).
 apply TI_morph_gen; auto with *.
 red; intros.
 apply W_F_ext; trivial.
  apply (Aeq _ _ H0).

  red; intros.
  apply Beq.
  apply val_push_var with (1:=H0); trivial.
   rewrite H3 in H2.
   rewrite <- (Aeq _ _ H0); trivial.
Qed.

End WFixRules.

Print Assumptions typ_wfix.


Lemma typ_wfix' : forall infty e A B O U M T,
       T <> kind ->
       isOrd infty ->
       A <> kind ->
       typ e O (Ordt infty) ->
       typ (Prod (WIL A B 1 (Ref 0)) U :: OSucc O :: e) M
         (Prod (WIL A B 2 (OSucc (Ref 1)))
         (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U)))) ->
       fx_extends (push_fun (push_ord (tinj e) (OSucc O)) (WIL A B 1 (Ref 0)) U)
         (WIL A B 2 (OSucc (Ref 1))) M ->
       fx_sub (push_var (push_ord (tinj e) (OSucc O)) (WIL A B 1 (OSucc (Ref 0)))) U ->
       sub_typ e (Prod (WI A B O) (subst_rec O 1 U)) T ->
       typ e (WFix O M) T.
intros.
apply typ_subsumption with (Prod (WI A B O) (subst_rec O 1 U)); auto.
2:discriminate.
change e with (tenv (tinj e)).
apply typ_wfix with (infty:=infty); trivial.
Qed.

(****************************************************************************************)
(** Compound judgements : typing + variance *)

Definition typ_ext e M A B :=
  fx_extends e A M /\ typ (tenv e) M (Prod A B).

Definition typ_mono e M T :=
  fx_sub e M /\ typ (tenv e) M T.

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

  apply eq_typ_prod; trivial.
  reflexivity.

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

  Lemma Wi_fx_sub : forall e o A B O,
    isOrd o ->
    A <> kind ->
    typ_impl e A kind ->
    typ_impl (push_var e A) B kind ->
    typ_mono e O (Ordt o) ->
    fx_sub e (WI A B O).
intros e o A B O oo Ank (eqA,_) (eqB,_) (subO,tyO).
apply Wi_sub with (o:=o); trivial.
Qed.

  Lemma OSucc_fx_sub : forall e O o,
    isOrd o ->
    typ_mono e O (Ordt o)->
    typ_mono e (OSucc O) (Ordt (osucc o)).
destruct 2.
split.
 apply OSucc_sub; trivial.

 red; simpl; intros.
 red.
 destruct tyord_inv with (2:=H1)(3:=H2) as (_,?); trivial.
 apply lt_osucc_compat; trivial.
Qed.

  Lemma typ_var_mono : forall e n t T,
    ords e n = true ->
    nth_error (tenv e) n = value t ->
    T <> kind ->
    t <> kind ->
    sub_typ (tenv e) (lift (S n) t) T ->
    typ_mono e (Ref n) T.
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
    typ_mono e T kind ->
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

 unfold lift; rewrite eq_lift_prod.
 reflexivity.
split.
 apply fx_eq_rec_call with t (lift_rec (S n) 1 u); trivial.

 apply typ_subsumption with (subst x (lift_rec (S n) 1 u)); auto.
 2:destruct u as [(u,um)|]; trivial.
 2:discriminate.
 apply typ_app with (lift (S n) t); trivial.
 destruct t as [(t,tm)|]; trivial.
 discriminate.
Qed.


Lemma typ_wfix'' : forall infty e A B O U M T,
       isOrd infty ->
       T <> kind ->
       sub_typ (tenv e) (Prod (WI A B O) (subst_rec O 1 U)) T ->
       typ (tenv e) O (Ordt infty) ->
       typ_mono (push_var (push_ord e (OSucc O)) (WI (lift 1 A) (lift_rec 1 1 B) (OSucc (Ref 0)))) U kind ->
       typ_ext (push_fun (push_ord e (OSucc O)) (WI (lift 1 A) (lift_rec 1 1 B) (Ref 0)) U)
         M (WI (lift 2 A) (lift_rec 2 1 B) (OSucc (Ref 1)))
           (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
       typ (tenv e) (WFix O M) T.
intros.
destruct H3; destruct H4.
apply typ_subsumption with (2:=H1); trivial.
2:discriminate.
apply typ_wfix with infty; trivial.
Qed.

  Lemma typ_ext_fix : forall eps e A B O U M,
    isOrd eps ->
    A <> kind ->
    typ_impl e A kind ->
    typ_impl (push_var e A) B kind ->
    typ_mono e O (Ordt eps) ->
    typ_ext (push_fun (push_ord e (OSucc O)) (WI (lift 1 A) (lift_rec 1 1 B) (Ref 0)) U) M
      (WI (lift 2 A) (lift_rec 2 1 B) (OSucc (Ref 1)))
      (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    fx_sub (push_var (push_ord e (OSucc O)) (WI (lift 1 A) (lift_rec 1 1 B) (OSucc (Ref 0)))) U ->
    typ_ext e (WFix O M) (WI A B O) (subst_rec O 1 U).
intros eps e A B O U M eps_ord Ank tyA tyB tyO tyM tyU.
destruct tyO as (inclO,tyO).
destruct tyM as (extM,tyM).
assert (tyF: typ (tenv e) (WFix O M) (Prod (WI A B O) (subst_rec O 1 U))).
 apply typ_wfix with eps; trivial.
split; trivial.
destruct tyB as (eqB,_).
destruct tyA as (eqA,tyA).
apply wfix_extend with eps U; trivial.
Qed.

  Lemma typ_impl_fix : forall eps e A B O U M,
    isOrd eps ->
    A <> kind ->
    typ_impl e A kind ->
    typ_impl (push_var e A) B kind ->
    typ_impl e O (Ordt eps) ->
    typ_ext (push_fun (push_ord e (OSucc O)) (WI (lift 1 A) (lift_rec 1 1 B) (Ref 0)) U) M
      (WI (lift 2 A) (lift_rec 2 1 B) (OSucc (Ref 1)))
      (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    fx_sub (push_var (push_ord e (OSucc O)) (WI (lift 1 A) (lift_rec 1 1 B) (OSucc (Ref 0)))) U ->
    typ_impl e (WFix O M) (Prod (WI A B O) (subst_rec O 1 U)).
intros eps e A B O U M eps_ord Ank (eqA,tyA) (eqB,_) (inclO,tyO) (extM,tyM) tyU.
assert (tyF: typ (tenv e) (WFix O M) (Prod (WI A B O) (subst_rec O 1 U))).
 apply typ_wfix with eps; trivial.
split; trivial.
apply wfix_equals with eps A B U; trivial.
Qed.

(** Universes *)

Require Import ZFecc.

Definition type (n:nat) := cst (ecc (S n)).

Lemma typ_Prop : forall e, typ e prop (type 0).
red; intros; simpl.
apply G_trans with (grot_succ (ZFcoc.props)); auto.
 apply (grot_succ_typ gr).

 apply (grot_succ_in gr).

 apply (grot_succ_in gr).
Qed.

Lemma typ_Type : forall e n, typ e (type n) (type (S n)).
red; intros; simpl.
apply (grot_succ_in gr).
Qed.

Lemma cumul_Type : forall e n, sub_typ e (type n) (type (S n)).
red; simpl; intros.
red; intros.
apply ecc_incl with (n:=S n); trivial.
Qed.

Lemma cumul_Prop : forall e, sub_typ e prop (type 0).
red; simpl; intros.
red; intros.
apply G_trans with ZFcoc.props; trivial.
 apply (grot_succ_typ gr).
apply G_trans with (grot_succ ZFcoc.props); trivial.
 apply (grot_succ_typ gr).

 apply (grot_succ_in gr).

 apply (grot_succ_in gr).
Qed.

Lemma typ_prod2 : forall e n T U,
  typ e T (type n) ->
  typ (T :: e) U (type n) ->
  typ e (Prod T U) (type n).
Proof.
red; intros e n T U ty_T ty_U i is_val.
apply G_cc_prod.
 apply ecc_grot.

 red; red; intros.
 rewrite H0; auto with *.

 apply ty_T; trivial.

 intros.
 red in ty_U.
 change (int (type n) i) with (int (type n) (V.cons x i)).
 apply in_int_not_kind.
 2:discriminate.
 apply ty_U.
 apply vcons_add_var; auto.
Qed.


(** * W-types and universes. *)

Lemma typ_WI_type n eps e A B O :
  isOrd eps ->
  A <> kind ->
  typ e O (Ordt eps) ->
  typ e A (type n) ->
  typ (A::e) B (type n) ->
  typ e (WI A B O) (type n).
red; intros epso Ank tyO tyA tyB i is_val.
red.
destruct tyord_inv with (2:=tyO)(3:=is_val) as (oo,_); trivial.
clear tyO.
red in tyA; specialize tyA with (1:=is_val).
apply in_int_not_kind in tyA.
2:discriminate.
assert (G_B : forall a, a ∈ int A i -> int B (V.cons a i) ∈ ecc (S n)).
 intros.
 assert (val_ok (A::e) (V.cons a i)).
  apply vcons_add_var; trivial.
 apply tyB in H0.
 apply in_int_not_kind in H0.
 2:discriminate.
 trivial.
apply G_incl with (TI (WF' A B i) (W_ord (int A i) (fun x => int B (V.cons x i)))); trivial.
 apply (grot_succ_typ gr).

 apply G_TI; trivial.
  apply (grot_succ_typ gr).

  apply WF'_morph; auto with *.

  unfold W_ord.
  apply Ffix_o_o; auto with *.
   apply Wf_mono.
   apply Bw_morph; reflexivity.

   red; intros.
   revert H0; apply Wf_typ; trivial.
   apply Bw_morph; reflexivity.

  apply G_W_ord; auto.
   apply Bw_morph; reflexivity.

   apply (grot_succ_typ gr).

   change (omega ∈ ecc (S n)); auto.

  intros.
  apply G_W_F; auto.
   apply Bw_morph; reflexivity.

   apply (grot_succ_typ gr).

 apply W_stages; trivial.
 apply Bw_morph; reflexivity.
Qed.


(*
(************************************************************************)
(** One example of derived principles:
    - the standard recursor for W
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
assert (eq_trm Nat (NatI (Ord omega))).
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
  apply Wi_fx_sub with (o:=osucc (osucc omega)); auto.
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
     assert (i 1 ∈ Wi (i 4)).
      generalize (H0 1 _ (eq_refl _)); simpl.
      unfold V.lams, V.shift; simpl.
      trivial.
     rewrite beta_eq.
      rewrite beta_eq; auto with *.
       reflexivity.
       red; intros; apply inr_morph; trivial.

      red; intros; apply inr_morph; trivial.

      apply Wi_NAT in H1; trivial.
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
      apply Wi_NAT in H1; trivial.
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
*)