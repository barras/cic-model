Set Implicit Arguments.
Require Import List Compare_dec.
Require Import basic.
Require Import Sat.
Require Import Models.

Module Lc := Lambda.

(** * Abstract strong mormalization model (supporting strong eliminations) *)

Module Type RealSN_addon (M : CC_Model).
  Import M.

  (** Types are equipped with a saturated set *)
  Parameter Real : X -> X -> SAT.
  Parameter Real_morph: Proper (eqX ==> eqX ==> eqSAT) Real.

  Parameter Real_sort : forall P, P ∈ props -> eqSAT (Real props P) snSAT.

  Definition piSAT A F f :=
    interSAT (fun p:{x|x ∈ A} =>
      prodSAT (Real A (proj1_sig p)) (Real (F (proj1_sig p)) (f (proj1_sig p)))).

  Parameter Real_prod : forall dom f F,
    eq_fun dom F F ->
    f ∈ prod dom F ->
    eqSAT (Real (prod dom F) f) (piSAT dom F (app f)).

  Existing Instance Real_morph.

  (** Every proposition is inhabited *)
  Parameter daimon : X.
  Parameter daimon_false : daimon ∈ prod props (fun P => P).

End RealSN_addon.

(******************************************************************************)
(* The generic model construction: *)

Module MakeModel (M : CC_Model) (MM : RealSN_addon(M)).
Import M.
Import MM.

(* Derived properties of the abstract SN model *)

(** We first introduce the realizability relation, which the conjunction
   of the value and term interpretation requirements.
   [x,t] \real T reads "t is a realizer of x as a value of type T".
 *)
Notation "[ x , t ] \real A" := (x ∈ A  /\ inSAT t (Real A x)) (at level 60).

Lemma real_daimon : forall x t T,
  [x,t] \real T -> [x,SatSet.daimon] \real T.
destruct 1; split; trivial.
apply varSAT.
Qed.

Lemma real_sn : forall x A t, [x,t] \real A -> Lc.sn t.
destruct 1 as (_,?).
apply sat_sn in H; trivial.
Qed.

Lemma real_exp_K : forall x A u v,
  Lc.sn v ->
  [x,u] \real A ->
  [x,Lc.App2 Lc.K u v] \real A. 
destruct 2; split; trivial.
apply KSAT_intro; trivial.
Qed.

Lemma piSAT_intro : forall A B f t,
  Lc.sn t -> (* if A is empty *)
  (forall x u, x ∈ A -> inSAT u (Real A x) -> inSAT (Lc.App t u) (Real (B x) (f x))) ->
  inSAT t (piSAT A B f).
unfold piSAT; intros.
apply interSAT_intro' with (P:=fun x=>x ∈ A)
   (F:=fun x => prodSAT (Real A x) (Real (B x) (f x))); trivial; intros.
intros ? ?.
apply H0; trivial.
Qed.

Lemma piSAT_elim : forall A B f x t u,
  inSAT t (piSAT A B f) ->
  x ∈ A ->
  inSAT u (Real A x) ->
  inSAT (Lc.App t u) (Real (B x) (f x)).
intros.
apply interSAT_elim with (x:=exist (fun x => x ∈ A) x H0) in H; simpl proj1_sig in H.
apply H; trivial.
Qed.

(* Works even when dom is empty: *)
Lemma prod_intro_sn : forall dom f F m,
  eq_fun dom f f ->
  eq_fun dom F F ->
  Lc.sn m ->
  (forall x u, [x,u] \real dom ->
   [f x, Lc.App m u] \real F x) ->
  [lam dom f, m] \real prod dom F.
intros.
assert (lam dom f ∈ prod dom F).
 apply prod_intro; intros; trivial.
 apply H2 with SatSet.daimon.
 split; trivial.
 apply varSAT.
split; trivial.
rewrite Real_prod; trivial.
apply piSAT_intro; intros; trivial.
rewrite beta_eq; trivial.
apply H2; auto.
Qed.

Lemma prod_intro_lam : forall dom f F m,
  eq_fun dom f f ->
  eq_fun dom F F ->
  Lc.sn m ->
  (forall x u, [x,u] \real dom ->
   [f x, Lc.subst u m] \real F x) ->
  [lam dom f, Lc.Abs m] \real prod dom F.
intros.
apply prod_intro_sn; intros; trivial.
 apply Lc.sn_abs; trivial.

 destruct H2 with (1:=H3).
 split; trivial.
 apply inSAT_exp; trivial.
 destruct H3.
 apply sat_sn in H6; auto.
Qed.

Lemma prod_elim : forall dom f x F t u,
  eq_fun dom F F ->
  [f,t] \real prod dom F ->
  [x,u] \real dom ->
  [app f x, Lc.App t u] \real F x.
destruct 2; destruct 1.
split.
 apply prod_elim with (2:=H0); trivial.

 rewrite Real_prod in H1; trivial.
 apply interSAT_elim with (x:=exist (fun x => x ∈ dom) x H2) in H1; simpl proj1_sig in H1.
 apply prodSAT_elim with (1:=H1); trivial.
Qed.



(** The abstract strong normalization proof. *)
Require ObjectSN.
Include ObjectSN.MakeObject(M).


(** * Semantic typing relation. *)

(** Handles the case of kind: a type that contains all "non-empty" types
    and that is included in no type.
 *)

Definition in_int (i:val) (j:Lc.intt) (M T:trm) :=
  M <> None /\
  match T with
  (** M has type kind *)
  | None => kind_ok M /\ Lc.sn (tm j M)
  (** T is a regular type *)
  | _ => [int i M, tm j M] \real int i T
  end.

Instance in_int_morph : Proper
  (eq_val ==> pointwise_relation nat eq ==> eq_trm ==> eq_trm ==> iff)
  in_int.
unfold in_int; do 5 red; intros.
repeat rewrite eq_kind.
destruct x2; destruct y2; try contradiction.
 rewrite H; rewrite H0; rewrite H1; rewrite H2; reflexivity.
 rewrite H0; rewrite H1; reflexivity.
Qed.

Lemma in_int_not_kind : forall i j M T,
  in_int i j M T ->
  T <> kind ->
  [int i M, tm j M] \real int i T.
destruct 1 as (_,mem); intros.
destruct T; auto.
elim H; trivial.
Qed.

Lemma in_int_intro : forall i j M T,
  [int i M, tm j M] \real int i T ->
  M <> kind ->
  T <> kind ->
  in_int i j M T.
red; intros.
destruct T; auto.
elim H1; trivial.
Qed.


Lemma in_int_var0 : forall i j x t T,
  [x,t] \real int i T ->
  T <> kind ->
  in_int (V.cons x i) (I.cons t j) (Ref 0) (lift 1 T).
intros.
red; simpl.
split; try discriminate.
 revert H0; pattern T at 1 2.
 case T; simpl; intros.
  rewrite int_cons_lift_eq; trivial.

  elim H0; trivial.
Qed.

Lemma in_int_varS : forall i j x t n T,
  in_int i j (Ref n) (lift (S n) T) ->
  in_int (V.cons x i) (I.cons t j) (Ref (S n)) (lift (S (S n)) T).
intros.
destruct H as (_,mem); simpl in *.
red; simpl.
split; try discriminate.
 revert mem; pattern T at 1 4.
 case T; [intros T0|]; simpl; intros; trivial.
  rewrite split_lift.
  rewrite int_cons_lift_eq; trivial.

  destruct mem; split; trivial.
  rewrite kind_ok_lift with (k:=0) in H.
  rewrite eq_trm_lift_ref_fv in H; auto with arith.
Qed.

Lemma in_int_sn : forall i j M T,
  in_int i j M T -> Lc.sn (tm j M).
destruct 1 as (_,mem).
destruct T; simpl in mem.
 apply real_sn in mem; trivial.

 destruct mem; trivial.
Qed.

(** Environments *)
Definition env := list trm.

Definition val_ok (e:env) (i:val) (j:Lc.intt) :=
  forall n T, nth_error e n = value T ->
  in_int i j (Ref n) (lift (S n) T).

Lemma vcons_add_var : forall e T i j x t,
  val_ok e i j ->
  [x,t] \real int i T ->
  T <> kind ->
  val_ok (T::e) (V.cons x i) (I.cons t j).
unfold val_ok; simpl; intros.
destruct n; simpl in *.
 injection H2; clear H2; intro; subst; simpl in *. 
 apply in_int_var0; trivial.

 apply in_int_varS; auto.
Qed.

Lemma vcons_add_var_daimon : forall e T i j x,
  val_ok e i j ->
  x ∈ int i T ->
  T <> kind ->
  val_ok (T::e) (V.cons x i) (I.cons SatSet.daimon j).
intros.
apply vcons_add_var; trivial.
split; trivial.
apply varSAT.
Qed.

Lemma add_var_eq_fun : forall T U U' i,
  (forall x t, [x,t] \real int i T -> int (V.cons x i) U == int (V.cons x i) U') -> 
  eq_fun (int i T)
    (fun x => int (V.cons x i) U)
    (fun x => int (V.cons x i) U').
red; intros.
rewrite <- H1.
apply H with (t:=SatSet.daimon).
split; trivial.
apply varSAT.
Qed.


(** * Judgements *)

(** #<a name="MakeModel.wf"></a># *)
Definition wf (e:env) :=
  exists i, exists j, val_ok e i j.
Definition typ (e:env) (M T:trm) :=
  forall i j, val_ok e i j -> in_int i j M T.
Definition eq_typ (e:env) (M M':trm) :=
  (forall i j, val_ok e i j -> int i M == int i M').
Definition sub_typ (e:env) (M M':trm) :=
  forall i j, val_ok e i j ->
  (forall x t, [x,t] \real int i M -> [x,t] \real int i M').

Definition eq_typ' e M N := eq_typ e M N /\ conv_term M N.

Instance typ_morph : forall e, Proper (eq_trm ==> eq_trm ==> iff) (typ e).
unfold typ; split; simpl; intros.
 rewrite <- H; rewrite <- H0; auto.
 rewrite H; rewrite H0; auto.
Qed.

Instance eq_typ_morph : forall e, Proper (eq_trm ==> eq_trm ==> iff) (eq_typ e).
intro; apply morph_impl_iff2; auto with *.
do 4 red; unfold eq_typ; intros.
rewrite <- H; rewrite <- H0; eauto.
Qed.

Instance eq_typ'_morph : forall e, Proper (eq_trm ==> eq_trm ==> iff) (eq_typ' e).
do 3 red; intros.
apply and_iff_morphism.
 apply eq_typ_morph; trivial.

 rewrite H; rewrite H0; reflexivity.
Qed.

Instance sub_typ_morph : forall e, Proper (eq_trm ==> eq_trm ==> iff) (sub_typ e).
unfold sub_typ; split; simpl; intros.
 rewrite <- H in H3.
 rewrite <- H0; eauto.

 rewrite H in H3.
 rewrite H0; eauto.
Qed.


(* Auxiliary lemmas: *)
Lemma typ_common e M T :
  match M,T with Some _,Some _=> True |_,_ => False end ->
  (forall i j, val_ok e i j -> [int i M, tm j M]\real int i T) ->
  typ e M T.
red; red; intros.
destruct M; try contradiction.
split;[discriminate|].
destruct T; try contradiction.
apply H0; trivial.
Qed.

(** Well-formed types *)
Definition typs e T :=
  typ e T kind \/ typ e T prop.

Lemma typs_not_kind : forall e T, wf e -> typs e T -> T <> kind.
intros e T (i,(j,is_val)) [ty|ty]; apply ty in is_val;
  destruct is_val; assumption.
Qed.

(* Uses that all types are inhabited *)
Lemma typs_non_empty : forall e T i j,
  typs e T ->
  val_ok e i j ->
  exists x, [x,SatSet.daimon] \real int i T.
intros.
destruct H.
 apply H in H0.
 destruct H0 as (_,(mem,_)).
 destruct kind_ok_witness with (1:=mem) (i:=i) as (w,?); exists w.
 split; trivial.
 apply varSAT.

 apply H in H0.
 destruct H0 as (_,mem); simpl in *.
 exists (app daimon (int i T)).
 apply real_daimon with (Lc.App SatSet.daimon (tm j T)).
 apply prod_elim with (dom:=props) (F:=fun P => P); trivial.
  red; intros; trivial.

  split; [apply daimon_false|apply varSAT].
Qed.


(** * Strong normalization *)

Lemma typs_sn : forall e T i j, typs e T -> val_ok e i j -> Lc.sn (tm j T).
destruct 1 as [ty_T|ty_T]; intro is_val; apply ty_T in is_val;
 red in is_val; simpl in is_val.
 destruct is_val as (_,(_,sn)); trivial.
 destruct is_val as (_,mem); apply real_sn in mem; trivial.
Qed.

(** This lemma shows that the abstract model construction entails
   strong normalization.
   At this level, we do not have the actual syntax. However, red_term
   is a relation on the denotations that admits the same introduction
   rules as the syntactic reduction.
   When the syntax is introduced, it will only remain to check that
   the syntactic reduction implies the semantic one, which will be
   straightforward.
 *)
Lemma model_strong_normalization e M T :
  wf e ->
  typ e M T ->
  Acc (transp _ red_term) M.
intros (i,(j,is_val)) ty.
apply ty in is_val.
apply in_int_sn in is_val.
apply simul with (1:=is_val) (2:=eq_refl).
Qed.


(** * Inference rules *)

(** ** Context formation rules *)

Lemma wf_nil : wf List.nil.
red.
exists vnil; exists (fun _ => SatSet.daimon).
red; intros.
destruct n; discriminate.
Qed.

Lemma wf_cons : forall e T,
  wf e ->
  typs e T ->
  wf (T::e).
unfold wf; intros.
assert (T <> kind).
 apply typs_not_kind in H0; trivial.
destruct H as (i,(j,is_val)).
destruct typs_non_empty with (1:=H0) (2:=is_val) as (x,non_mt).
exists (V.cons x i); exists (I.cons SatSet.daimon j).
apply vcons_add_var; trivial.
Qed.

(** ** Extensional equality rules *)

Lemma refl : forall e M, eq_typ e M M.
red; simpl; reflexivity.
Qed.

Lemma sym : forall e M M', eq_typ e M M' -> eq_typ e M' M.
unfold eq_typ; intros; symmetry; eauto.
Qed.

Lemma trans : forall e M M' M'',
  eq_typ e M M' -> eq_typ e M' M'' -> eq_typ e M M''.
unfold eq_typ; intros.
transitivity (int i M'); eauto.
Qed.

Instance eq_typ_equiv : forall e, Equivalence (eq_typ e).
split.
 exact (@refl e).
 exact (@sym e).
 exact (@trans e).
Qed.


Lemma eq_typ_app : forall e M M' N N',
  eq_typ e M M' ->
  eq_typ e N N' ->
  eq_typ e (App M N) (App M' N').
unfold eq_typ; simpl; intros.
apply app_ext; eauto.
Qed.

Lemma eq_typ_abs : forall e T T' M M',
  eq_typ e T T' ->
  eq_typ (T::e) M M' ->
  T <> kind ->
  eq_typ e (Abs T M) (Abs T' M').
Proof.
unfold eq_typ; simpl; intros.
apply lam_ext; eauto.
red; intros.
rewrite <- H4.
apply H0 with (j:=I.cons SatSet.daimon j).
apply vcons_add_var_daimon; auto.
Qed.

Lemma eq_typ_prod : forall e T T' U U',
  eq_typ e T T' ->
  eq_typ (T::e) U U' ->
  T <> kind ->
  eq_typ e (Prod T U) (Prod T' U').
Proof.
unfold eq_typ; simpl; intros.
apply prod_ext; eauto.
red; intros.
rewrite <- H4.
apply H0 with (j:=I.cons SatSet.daimon j).
apply vcons_add_var_daimon; auto.
Qed.

Lemma eq_typ_beta : forall e T M M' N N',
  eq_typ (T::e) M M' ->
  eq_typ e N N' ->
  typ e N T -> (* Typed reduction! *)
  T <> kind ->
  eq_typ e (App (Abs T M) N) (subst N' M').
Proof.
unfold eq_typ, typ; simpl; intros.
assert (real_arg :  [int i N, tm j N]\real int i T).
 apply in_int_not_kind; auto.
rewrite beta_eq.
 rewrite <- int_subst_eq.
 rewrite <- H0 with (1:=H3).
 apply H with (j:=I.cons (tm j N) j).
 apply vcons_add_var; trivial.

 apply add_var_eq_fun with (T:=T); intros; trivial; reflexivity.

 destruct real_arg; trivial.
Qed.

(** ** Intensional equality *)

Instance eq_typ'_equiv : forall e, Equivalence (eq_typ' e).
split; red; intros.
 split; reflexivity.
 destruct H; split; symmetry; trivial.
 destruct H; destruct H0; split; transitivity y; trivial.
Qed.

Lemma eq_typ'_eq_typ e M N :
  eq_typ' e M N -> eq_typ e M N.
destruct 1; trivial.
Qed.

Lemma eq_typ'_app : forall e M M' N N',
  eq_typ' e M M' ->
  eq_typ' e N N' ->
  eq_typ' e (App M N) (App M' N').
destruct 1; destruct 1; split.
 apply eq_typ_app; trivial.

 apply conv_term_app; trivial.
Qed.

Lemma eq_typ'_abs : forall e T T' M M',
  eq_typ' e T T' ->
  eq_typ' (T::e) M M' ->
  T <> kind ->
  eq_typ' e (Abs T M) (Abs T' M').
Proof.
destruct 1; destruct 1; split.
 apply eq_typ_abs; trivial.

 apply conv_term_abs; trivial.
Qed.

Lemma eq_typ'_prod : forall e T T' U U',
  eq_typ' e T T' ->
  eq_typ' (T::e) U U' ->
  T <> kind ->
  eq_typ' e (Prod T U) (Prod T' U').
Proof.
destruct 1; destruct 1; split.
 apply eq_typ_prod; trivial.

 apply conv_term_prod; trivial.
Qed.

Lemma eq_typ'_beta : forall e T M M' N N',
  eq_typ' (T::e) M M' ->
  eq_typ' e N N' ->
  typ e N T -> (* Typed reduction! *)
  T <> kind ->
  eq_typ' e (App (Abs T M) N) (subst N' M').
Proof.
destruct 1; destruct 1; split.
 apply eq_typ_beta; trivial.

 apply conv_term_beta; trivial.
Qed.

(** ** Typing rules *)

Lemma typ_prop : forall e, typ e prop kind.
red; simpl; intros.
split; try discriminate.
split; simpl; auto.
 apply prop_kind_ok.

 apply Lc.sn_K.
Qed.

Lemma typ_var : forall e n T,
  nth_error e n = value T -> typ e (Ref n) (lift (S n) T).
red; simpl; intros.
apply H0 in H; trivial.
Qed.

Lemma typ_app : forall e u v V Ur,
  typ e v V ->
  typ e u (Prod V Ur) ->
  V <> kind ->
  Ur <> kind ->
  typ e (App u v) (subst v Ur).
intros e u v V Ur ty_v ty_u ty_V ty_Ur i j is_val.
specialize (ty_v _ _ is_val).
specialize (ty_u _ _ is_val).
apply in_int_not_kind in ty_v; trivial.
apply in_int_not_kind in ty_u; try discriminate.
simpl in *.
apply prod_elim with (x:=int i v) (u:=tm j v) in ty_u; trivial.
 apply in_int_intro; simpl; trivial; try discriminate.
  rewrite <- int_subst_eq; trivial.

  destruct Ur as [Ur|]; simpl; try discriminate; trivial.

 red; intros.
 rewrite H0; reflexivity.
Qed.

Lemma prod_intro2 : forall dom f F t m,
  eq_fun dom f f ->
  eq_fun dom F F ->
  Lc.sn t ->
  (exists x, [x,SatSet.daimon] \real dom) ->
  (forall x u, [x, u] \real dom -> [f x, Lc.subst u m] \real F x) ->
  [lam dom f, CAbs t m] \real prod dom F.
intros.
apply prod_intro_lam in H3; trivial.
unfold CAbs; apply real_exp_K; trivial.
(* *)
destruct H2.
apply H3 in H2.
apply real_sn in H2.
apply Lc.sn_subst in H2; trivial.
Qed.

Lemma typ_abs : forall e T M U,
  typs e T ->
  typ (T :: e) M U ->
  U <> kind ->
  typ e (Abs T M) (Prod T U).
Proof.
intros e T M U ty_T ty_M not_tops i j is_val.
assert (T_not_tops : T <> kind).
 destruct ty_T as [ty_T|ty_T]; apply ty_T in is_val;
   destruct is_val; trivial.
apply in_int_intro; simpl; try discriminate.
apply prod_intro2; intros.
 apply add_var_eq_fun; auto with *.

 apply add_var_eq_fun; auto with *.

 apply typs_sn with (1:=ty_T) (2:=is_val).

 apply typs_non_empty with (2:=is_val); trivial.

 apply vcons_add_var with (x:=x) (T:=T) (t:=u) in is_val; trivial.
 apply ty_M in is_val.
 apply in_int_not_kind in is_val; trivial.
 rewrite <- tm_subst_cons; trivial.
Qed.

Lemma typ_prod : forall e T U s2,
  s2 = kind \/ s2 = prop ->
  typs e T ->
  typ (T :: e) U s2 ->
  typ e (Prod T U) s2.
Proof.
intros e T U s2 is_srt ty_T ty_U i j is_val.
assert (T_not_tops : T <> kind).
 destruct ty_T as [ty_T|ty_T]; apply ty_T in is_val;
   destruct is_val; trivial.
assert (typs (T::e) U) by (destruct is_srt; subst; red; auto).
destruct (typs_non_empty ty_T is_val) as (witT,in_T).
specialize vcons_add_var with (1:=is_val) (2:=in_T) (3:=T_not_tops);
  intros in_U.
apply ty_U in in_U.
split;[discriminate|simpl].
assert (snU : Lc.sn (tm (Lc.ilift j) U)).
 apply Lc.sn_subst with SatSet.daimon.
 rewrite <- tm_subst_cons.
 destruct is_srt; subst s2; simpl in *.
  destruct in_U as (_,(_,snu)); trivial.

  destruct in_U as (_,mem); simpl in mem.
  apply real_sn in mem; trivial.
destruct is_srt; subst s2; simpl in *.
 (* s2=kind *)
 split.
  apply prod_kind_ok.
  destruct in_U as (_,(mem,_)); trivial.

  apply Lc.sn_K2.
   apply typs_sn with (1:=ty_T) (2:=is_val).

   apply Lc.sn_abs; trivial.

 (* s2=prop *)
 unfold CProd.
 apply real_exp_K.
  apply Lc.sn_abs; trivial.
 assert (prod (int i T) (fun x => int (V.cons x i) U) ∈ props).
  apply impredicative_prod; intros.   
   red; intros.
   rewrite H1; reflexivity.
   assert (val_ok (T::e) (V.cons x i) (I.cons SatSet.daimon j)).
    apply vcons_add_var; trivial.
    split; trivial.
    apply varSAT.
   apply ty_U in H1.
   destruct H1 as (_,(?,_)); trivial.
 split; simpl; trivial.
 rewrite Real_sort; trivial.
 apply typs_sn with (1:=ty_T) (2:=is_val).
Qed.

Lemma typ_conv : forall e M T T',
  typ e M T ->
  eq_typ e T T' ->
  T <> kind ->
  T' <> kind ->
  typ e M T'.
Proof.
unfold typ, eq_typ; simpl; intros.
specialize H with (1:=H3).
specialize H0 with (1:=H3).
generalize (proj1 H); intro.
apply in_int_not_kind in H; trivial.
apply in_int_intro; trivial.
rewrite <- H0; trivial.
Qed.

(** Weakening *)

Lemma weakening : forall e M T A,
  typ e M T ->
  typ (A::e) (lift 1 M) (lift 1 T).
unfold typ, in_int; intros.
assert (val_ok e (V.lams 0 (V.shift 1) i) (I.lams 0 (I.shift 1) j)).
 red; intros.
 rewrite I.lams0; rewrite V.lams0; unfold V.shift, I.shift; simpl.
 red in H0.
 apply H0 with (n:=S n) in H1.
 revert H1.
 unfold in_int; destruct T0 as [(T0,T0m)|]; simpl.
  intros (_,realV); split;[discriminate|exact realV].

  intros (_,(ne,sat)); split;[discriminate|split; trivial].

  rewrite kind_ok_lift with (k:=0).
  rewrite eq_trm_lift_ref_fv; auto with *.
destruct H with (1:=H1) as (M_nk, inT).
split.
 destruct M; try discriminate.
 elim M_nk; trivial.
 revert inT; pattern T at 1 4; case T; intros; simpl.
 unfold lift.
 do 2 rewrite int_lift_rec_eq.
 rewrite tm_lift_rec_eq; trivial.

 destruct inT; split.
  unfold lift; rewrite <- kind_ok_lift; trivial.

  unfold lift; rewrite tm_lift_rec_eq; trivial.
Qed.


(** ** Subtyping rules *)

Lemma sub_refl : forall e M M',
  eq_typ e M M' -> sub_typ e M M'.
red; intros.
apply H in H0.
clear H.
rewrite <- H0; trivial.
Qed.

Lemma sub_trans : forall e M1 M2 M3,
  sub_typ e M1 M2 -> sub_typ e M2 M3 -> sub_typ e M1 M3.
unfold sub_typ; eauto.
Qed.

Instance sub_typ_preord e : PreOrder (sub_typ e).
split; red; intros.
 apply sub_refl; reflexivity.

 apply sub_trans with y; trivial.
Qed.

(* subsumption: generalizes typ_conv *)
Lemma typ_subsumption : forall e M T T',
  typ e M T ->
  sub_typ e T T' ->
  T <> kind ->
  T' <> kind ->
  typ e M T'.
Proof.
unfold typ, sub_typ; intros.
specialize H with (1:=H3).
specialize H0 with (1:=H3).
assert (Mnk := proj1 H).
apply in_int_not_kind in H; trivial.
apply in_int_intro; auto.
Qed.

(** Covariance can be derived if we have a weak eta property:
   any function is a lambda abstraction *with the same domain*.
   This is OK with set-theoretical functions (in contrast with
   general eta which does not hold on set-theoretical functions).
   This property could be added to the abstract domain.

   Contravariance of product does not hold in set-theory.
 *)
Definition sub_typ_covariant
  (eta_eq : forall dom F f, f ∈ prod dom F -> f == lam dom (app f))
  e U1 U2 V1 V2 :
  U1 <> kind ->
  eq_typ e U1 U2 ->
  sub_typ (U1::e) V1 V2 ->
  sub_typ e (Prod U1 V1) (Prod U2 V2).
unfold sub_typ; simpl; intros U1_nk eqU subV i j is_val x t in1.
assert (eqx : x == lam (int i U2) (app x)).
 destruct in1 as (tyx,_).
 apply eta_eq in tyx.
 apply (transitivity tyx).
 apply lam_ext.
  apply eqU with (1:=is_val).

  red; intros; apply app_ext; auto with *.
rewrite eqx.
apply prod_intro_sn.
 red; intros; apply app_ext; auto with *.

 red; intros.
 rewrite H0; reflexivity.

 apply real_sn in in1; trivial.

 intros.
 apply subV with (j:=I.cons u j).
  apply vcons_add_var; trivial.
  rewrite (eqU _ _ is_val); trivial.

  apply prod_elim with (2:=in1).
   red; intros.
   rewrite H1; auto with *.

   rewrite (eqU _ _ is_val); trivial.
Qed.

End MakeModel.
