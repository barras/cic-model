Require Import List Bool Models.
Require ModelZF.
Import ZFgrothendieck.
Import ZF ZFsum ZFnats ZFrelations ZFord ZFfix.
Require Import ZFfunext ZFfixrec ZFecc ZFind_nat.

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


(** Ordinals *)

Definition Ord (o:set) := cst o.

Definition typ_ord_kind : forall e o, typ e (Ord o) kind.
red; simpl; intros.
trivial.
Qed.

Definition typ_ord_ord : forall e o o',
  lt o o' -> typ e (Ord o) (Ord o').
red; simpl; intros; trivial.
Qed.


Definition OSucc : term -> term.
(*begin show*)
intros o; left; exists (fun i => osucc (int o i)).
(*end show*)
do 2 red; intros.
rewrite H; reflexivity.
Defined.



(** Nat *)

Definition Nat := cst NAT.

Definition Nati (o:set) := cst (NATi o).

Definition NatI : term -> term.
(*begin show*)
intros o.
left; exists (fun i => NATi (int o i)).
(*end show*)
do 2 red; intros.
apply NATi_morph.
rewrite H; reflexivity.
Defined.

Lemma typ_nati : forall e o,
  isOrd o -> typ e (Nati o) kind.
red; intros; simpl; trivial.
Qed.

Lemma typ_natI : forall e o,
  typ e (NatI o) kind.
red; intros; simpl; trivial.
Qed.

(* Zero *)

Definition Zero := cst ZERO.

Lemma typ_zero : forall e o,
  isOrd o -> typ e Zero (Nati (osucc o)).
red; simpl; intros.
apply ZEROi_typ; trivial.
Qed.

Lemma typ_Zero : forall o e O,
  isOrd o ->
  typ e O (Ord o) ->
  typ e Zero (NatI (OSucc O)).
red; simpl; intros.
specialize (H0 _ H1); simpl in H0.
assert (isOrd (int O i)).
 apply isOrd_inv with o; auto.
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

Lemma typ_succi : forall e o i,
  isOrd o ->
  typ e i (Ord o) ->
  typ e (SuccI i) (Prod (NatI i) (NatI (OSucc (lift 1 i)))). 
intros.
unfold SuccI.
apply typ_abs.
 2:discriminate.
red; simpl; intros.
assert (ty_arg :=H1).
red in ty_arg.
specialize (ty_arg 0 _ (refl_equal _)).
simpl in ty_arg.
assert (isOrd (int (lift 1 i) i0)).
 specialize weakening with (1:=H0) (A:=NatI i).
 unfold Ord, lift at 2; rewrite eqterm_lift_cst; intro.
 apply H2 in H1.
 simpl in H1.
 apply isOrd_inv with o; auto.
apply SUCCi_typ; trivial.
apply eq_elim with (2:=ty_arg).
fold NATi.
apply NATi_morph.
unfold lift; rewrite int_lift_rec_eq; reflexivity.
Qed.

Lemma typ_SuccI : forall e o i n,
  isOrd o ->
  typ e i (Ord o) ->
  typ e n (NatI i) ->
  typ e (App (SuccI i) n) (NatI (OSucc i)). 
intros.
apply typ_conv with (subst n (NatI (OSucc (lift 1 i)))).
3:discriminate.
 apply typ_app with (NatI i); trivial.
 2:discriminate.
 apply typ_succi with (o:=o); trivial.

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

Lemma Natcase_succ : forall o O e n fZ fS,
  isOrd o ->
  typ e O (Ord o) ->
  typ e n (NatI O) ->
  eq_typ e (Natcase fZ fS (App (SuccI O) n)) (subst n fS).
red; intros.
red in H0; specialize H0 with (1:=H2).
red in H1; specialize H1 with (1:=H2).
simpl in *.
rewrite <- (fun e1 e2 => NATCASE_morph (int fZ i) (int fZ i) e1
  (fun k => int fS(V.cons k i)) (fun k => int fS(V.cons k i)) e2
  (SUCC (int n (fun k => i k)))); auto with *.
 rewrite NATCASE_SUCC; auto.
  rewrite int_subst_eq; reflexivity.

  intros.
  rewrite H3; reflexivity.

 red; intros.
 rewrite H3; reflexivity.

 rewrite beta_eq; auto with *.
 red; intros.
 unfold SUCC; apply inr_morph; trivial.
Qed.

Existing Instance NATi_morph.

Lemma typ_natcase : forall o e O P fZ fS n,
  isOrd o ->
  typ e O (Ord o) ->
  typ e fZ (App P Zero) ->
  typ (NatI O :: e) fS (App (lift 1 P) (App (SuccI (lift 1 O)) (Ref 0))) ->
  typ e n (NatI (OSucc O)) ->
  typ e (Natcase fZ fS n) (App P n).
red; intros.
 red in H0; specialize H0 with (1:=H4).
 simpl in H0; red in H0.
 red in H1; specialize H1 with (1:=H4).
 simpl in H1; red in H1.
 red in H3; specialize H3 with (1:=H4).
 simpl in H3; red in H3.
 simpl; red.
 apply NATCASE_typ with (o:=int O i) (P:=fun n => app (int P i) n); trivial.
  do 2 red; intros.
  rewrite H5; reflexivity.

  do 2 red; intros.
  rewrite H5; reflexivity.

  apply isOrd_inv with o; trivial.

  intros.
  assert (val_ok (NatI O :: e) (V.cons n0 i)).
   apply vcons_add_var; trivial.
  apply H2 in H6; clear H1; simpl in H6.
  change (fun k => V.cons n0 i k) with (V.cons n0 i) in H6.
  rewrite beta_eq in H6; trivial.
   rewrite simpl_int_lift1 in H6; trivial.

   red; intros.
   unfold SUCC; apply inr_morph; trivial.

   rewrite simpl_int_lift1; auto.
Qed.

Lemma typ_natcase' : forall o e O P fZ fS n T,
  isOrd o ->
  typ e O (Ord o) ->
  sub_typ e (App P n) T -> 
  typ e fZ (App P Zero) ->
  typ (NatI O :: e) fS
    (App (lift 1 P) (App (SuccI (lift 1 O)) (Ref 0))) ->
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
Definition val_mono (e:fenv) i i' :=
    val_ok (tenv e) i /\
    val_ok (tenv e) i' /\
    forall n,
    if ords e n then i n \incl i' n
    else match fixs e n with
      Some T => forall x, x \in int T (V.shift (S n) i) -> app (i n) x == app (i' n) x
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
  x \incl x' ->
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
  f \in prod (int T i) (fun x => int U (V.cons x i)) ->
  g \in prod (int T i') (fun x => int U (V.cons x i')) ->
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

(** Function Extension judgment *)
Definition fx_extends e dom M :=
  forall i i', val_mono e i i' ->
  fcompat (int dom i) (int M i) (int M i').

(** Covariance judgment *)
Definition fx_sub e M :=
  forall i i', val_mono e i i' ->
  int M i \incl int M i'.

(** Invariance *)
Definition fx_equals e M :=
  forall i i', val_mono e i i' -> int M i == int M i'.

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
    fx_equals e T ->
    fx_equals (push_var e T) M ->
    fx_equals e (Abs T M).
unfold fx_equals; intros.
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
destruct T as [(T,Tm)|]; simpl in H4|-*; auto.
 rewrite V.lams0 in H4; assumption.

 elim H1; trivial.
Qed.

  (* Covariance *)

  Lemma fx_equals_sub : forall e M, fx_equals e M -> fx_sub e M.
unfold fx_sub, fx_equals; intros.
apply H in H0.
rewrite H0; reflexivity.
Qed.

  Lemma var_sub : forall e n,
    ords e n = true ->
    fx_sub e (Ref n).
unfold fx_sub; intros.
destruct H0 as (_,(_,H0)).
generalize (H0 n); rewrite H.
simpl; trivial.
Qed.

Lemma fx_sub_prod : forall e T U,
  fx_equals e T ->
  fx_sub (push_var e T) U ->
  fx_sub e (Prod T U).
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

  Lemma NATi_sub : forall e o O,
    isOrd o ->
    typ (tenv e) O (Ord o) ->
    fx_sub e O ->
    fx_sub e (NatI O).
unfold fx_sub; intros.
simpl.
apply TI_mono; auto.
 destruct H2 as (_,(H2,_)).
 apply H0 in H2.
 apply isOrd_inv with o; auto.

 destruct H2 as (H2,_).
 apply H0 in H2.
 apply isOrd_inv with o; auto.
Qed.

  Lemma OSucc_sub : forall e O,
    fx_sub e O ->
    fx_sub e (OSucc O).
unfold fx_sub; simpl; intros.
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

  (* Function subtyping *)

  Lemma fx_abs : forall e U T M,
    fx_sub e T ->
    fx_equals (push_var e T) M ->
    typ (T::tenv e) M U ->
    U <> kind ->
    fx_extends e T (Abs T M).
unfold fx_sub, fx_equals, fx_extends; intros.
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
assert (int c i \in NATi (osucc (int O i))).
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



(*****************************************************************************)
(** Recursor (without case analysis) *)

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

  Variable infty : set.
  Hypothesis infty_ord : isOrd infty.
  Variable E : fenv.
  Let e := tenv E.
  Variable O U M : term.
  Hypothesis M_nk : ~ eq_term M kind.
  Hypothesis ty_O : typ e O (Ord infty).
  Hypothesis ty_M : typ (Prod (NatI (Ref 0)) U::OSucc O::e)
    M (Prod (NatI (OSucc (Ref 1)))
         (lift1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U)))).

  Hypothesis stab : fx_extends
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

  Hypothesis fx_sub_U :
    fx_sub (push_var (push_ord E (OSucc O)) (NatI (OSucc (Ref 0)))) U.


  Lemma ty_fix_body : forall i o f,
   val_ok e i ->
   lt o (osucc (int O i)) ->
   f \in prod (NATi o) (fun x => int U (V.cons x (V.cons o i))) ->
   F i o f \in
   prod (NATi (osucc o)) (fun x => int U (V.cons x (V.cons (osucc o) i))).
unfold F; intros.
specialize (ty_O _ H); simpl in ty_O.
assert (isOrd (int O i)).
 apply isOrd_inv with infty; trivial.
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
 apply ty_O in H.
 apply isOrd_inv with infty; auto.
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
   o' \incl int O i ->
   isOrd o ->
   o \incl o' ->
   x \in NATi o ->
   x == x' ->
   int U (V.cons x (V.cons o i)) \incl int U (V.cons x' (V.cons o' i)).
intros.
apply fx_sub_U.
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
 apply ty_O in H.
 simpl in H.
 apply isOrd_inv with infty; trivial.
apply NATREC_eqn with
  (ord:=int O i)
  (U:=fun o x => int U (V.cons x (V.cons o i))); auto.
intros.
apply ty_fix_body; trivial.
apply ole_lts; auto.
Qed.


Lemma typ_nat_fix :
  typ e (NatFix O M) (Prod (NatI O) (subst_rec O 1 U)).
red; intros.
simpl.
assert (isOrd (int O i)).
 apply ty_O in H.
 simpl in H.
 apply isOrd_inv with infty; trivial.
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
assert (isOrd (int O i)).
 apply isOrd_inv with infty; trivial.
rewrite nat_fix_eqn; trivial.
rewrite beta_eq.
 reflexivity.

 red; intros.
 rewrite H3; reflexivity.

 apply H; trivial.
Qed.

Lemma nat_fix_extend :
  fx_sub E O ->
  fx_extends E (NatI O) (NatFix O M).
intro subO.
do 2 red; intros.
assert (isval := proj1 H).
assert (isval' := proj1 (proj2 H)).
assert (oo: isOrd (int O i)).
 apply isOrd_inv with infty; trivial.
 apply ty_O; trivial.
assert (oo': isOrd (int O i')).
 apply isOrd_inv with infty; trivial.
 apply ty_O; trivial.
assert (inclo: int O i \incl int O i').
 apply subO in H; trivial.
clear subO.
assert (tyfx' :
  NATREC (F i') (int O i') \in
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
      assert (tyfx1 : NATREC (F i) o' \in
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

Lemma nat_fix_equals :
  fx_equals E O ->
  fx_equals E (NatFix O M).
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
 apply nat_fix_extend; trivial.
 apply fx_equals_sub; trivial.
Qed.

End NatFixRules.

Print Assumptions typ_nat_fix.


Lemma typ_nat_fix' : forall infty e O U M T,
       isOrd infty ->
       typ e O (Ord infty) ->
       typ (Prod (NatI (Ref 0)) U :: OSucc O :: e) M
         (Prod (NatI (OSucc (Ref 1)))
           (lift1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U)))) ->
       fx_extends (push_fun (push_ord (tinj e) (OSucc O)) (NatI (Ref 0)) U)
         (NatI (OSucc (Ref 1))) M ->
       fx_sub (push_var (push_ord (tinj e) (OSucc O)) (NatI (OSucc (Ref 0)))) U ->
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

Definition typ_mono e M T :=
  fx_sub e M /\ typ (tenv e) M T.

Definition typ_impl e M T :=
  fx_equals e M /\ typ (tenv e) M T.

Instance typ_impl_morph e : Proper (eq_term ==> eq_term ==> iff) (typ_impl e).
apply morph_impl_iff2; auto with *.
do 4 red; intros.
destruct H1; split.
 red; intros.
 rewrite <- H; auto.

 rewrite <- H; rewrite <- H0; auto.
Qed.

Lemma typ_var_impl : forall e n t T,
    spec_var e n = false ->
    nth_error (tenv e) n = value t ->
    t <> kind ->
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

  Lemma impl_abs : forall e U T T' M,
    U <> kind ->
    eq_typ (tenv e) T T' ->
    fx_equals e T ->
    typ_impl (push_var e T) M U ->
    typ_impl e (Abs T M) (Prod T' U).
destruct 4; split.
 apply fx_eq_abs; trivial.

 apply typ_conv with (Prod T U); auto.
  apply typ_abs; trivial.

  apply eq_typ_prod; trivial.
  reflexivity.

  discriminate.
Qed.

Lemma impl_app : forall e u v V Ur T,
  V <> kind ->
  Ur <> kind ->
  sub_typ (tenv e) (subst v Ur) T ->
  typ_impl e u (Prod V Ur) ->
  typ_impl e v V ->
  typ_impl e (App u v) T.
intros.
destruct H2.
destruct H3.
split.
 apply fx_eq_app; trivial.

 apply typ_subsumption with (subst v Ur); trivial.
  apply typ_app with V; auto.

  destruct Ur as [(Ur,Urm)|]; simpl; trivial.
  discriminate.
Qed.

  Lemma NATi_fx_sub : forall e o O,
    isOrd o ->
    typ_mono e O (Ord o) ->
    fx_sub e (NatI O).
destruct 2.
apply NATi_sub with (o:=o); trivial.
Qed.

  Lemma OSucc_fx_sub : forall e O o,
    isOrd o ->
    typ_mono e O (Ord o)->
    typ_mono e (OSucc O) (Ord (osucc o)).
destruct 2.
split.
 apply OSucc_sub; trivial.

 red; simpl; intros.
 apply lt_osucc_compat; trivial.
 apply H1; trivial.
Qed.

  Lemma typ_var_mono : forall e n t T,
    ords e n = true ->
    nth_error (tenv e) n = value t ->
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
    fx_sub e T ->
    typ_impl (push_var e T) M U ->
    U <> kind ->
    typ_ext e (Abs T M) T U.
destruct 2; split.
 apply fx_abs with U; trivial.
 apply typ_abs; trivial.
Qed.


(*************)


Lemma impl_natcase : forall o e O P fZ fS n T,
       isOrd o ->
       typ_mono e O (Ord o) ->
       sub_typ (tenv e) (App P n) T -> 
       typ_impl e fZ (App P Zero) ->
       typ_impl (push_var e (NatI O)) fS
         (App (lift 1 P) (App (SuccI (lift 1 O)) (Ref 0))) ->
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


  Lemma impl_call : forall e n x t u T,
    ords e n = false ->
    fixs e n = Some t ->
    t <> kind ->
    u <> kind ->
    nth_error (tenv e) n = value (Prod t u) ->
    sub_typ (tenv e) (subst x (lift1 (S n) u)) T ->
    typ_impl e x (lift (S n) t) ->
    typ_impl e (App (Ref n) x) T.
intros.
destruct H5.
assert (typ (tenv e) (Ref n) (Prod (lift (S n) t) (lift1 (S n) u))).
 apply typ_var0; rewrite H3; split;[discriminate|].
 apply sub_refl.
 unfold lift; rewrite eq_lift_prod.
 reflexivity.
split.
 apply fx_eq_rec_call with t (lift1 (S n) u); trivial.

 apply typ_subsumption with (subst x (lift1 (S n) u)); auto.
 2:destruct u as [(u,um)|]; trivial.
 2:discriminate.
 apply typ_app with (lift (S n) t); trivial.
 destruct t as [(t,tm)|]; trivial.
 discriminate.
Qed.


Lemma typ_nat_fix'' : forall infty e O U M T,
       isOrd infty ->
       sub_typ (tenv e) (Prod (NatI O) (subst_rec O 1 U)) T ->
       typ (tenv e) O (Ord infty) ->
       typ_mono (push_var (push_ord e (OSucc O)) (NatI (OSucc (Ref 0)))) U kind ->
       typ_ext (push_fun (push_ord e (OSucc O)) (NatI (Ref 0)) U)
         M (NatI (OSucc (Ref 1)))
           (lift1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
       typ (tenv e) (NatFix O M) T.
intros.
destruct H2; destruct H3.
apply typ_subsumption with (2:=H0).
2:discriminate.
apply typ_nat_fix with infty; trivial.
Qed.

  Lemma typ_ext_fix : forall eps e O U M,
    isOrd eps ->
    typ_mono e O (Ord eps) ->
    typ_ext (push_fun (push_ord e (OSucc O)) (NatI (Ref 0)) U) M
      (NatI (OSucc (Ref 1))) (lift1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    fx_sub (push_var (push_ord e (OSucc O)) (NatI (OSucc (Ref 0)))) U ->
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
    typ_impl e O (Ord eps) ->
    typ_ext (push_fun (push_ord e (OSucc O)) (NatI (Ref 0)) U) M
      (NatI (OSucc (Ref 1))) (lift1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    fx_sub (push_var (push_ord e (OSucc O)) (NatI (OSucc (Ref 0)))) U ->
    typ_impl e (NatFix O M) (Prod (NatI O) (subst_rec O 1 U)).
intros eps e O U M eps_ord tyO tyM tyU.
destruct tyO as (inclO,tyO).
destruct tyM as (extM,tyM).
assert (tyF: typ (tenv e) (NatFix O M) (Prod (NatI O) (subst_rec O 1 U))).
 apply typ_nat_fix with eps; trivial.
split; trivial.
apply nat_fix_equals with eps U; trivial.
Qed.


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
                        (App (Ref 3) (App (SuccI (Ord omega)) (Ref 1)))))
  (Prod (NatI (Ord omega)) (App (Ref 3) (Ref 0))))).

Definition nat_ind :=
   Abs (*P*)(Prod (NatI (Ord omega)) prop) (* P : nat -> Prop *)
  (Abs (*fZ*) (App (Ref 0) Zero)
  (Abs (*fS*) (Prod (*n*)(NatI (Ord omega)) (Prod (App (Ref 2) (Ref 0))
                                   (App (Ref 3) (App (SuccI (Ord omega)) (Ref 1)))))
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
  apply typ_var_mono with (OSucc (Ord omega)); auto; try discriminate.
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
     assert (i 1 \in NATi (i 4)).
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
  apply weakening0 in H0; apply weakeningS with (A:=OSucc O) in H0.
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
     (Abs (NatI (OSucc (Ord omega))) (NatI (OSucc (Ref 5)))); auto.
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
