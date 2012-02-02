Set Implicit Arguments.
Require Import List Compare_dec.
Require Import basic.
Require Import Sat.
Require Import Models.

Module Lc := Lambda.

(* The abstract normalization model. *)

Module Type RealSN_addon (M : CC_Model).
  Import M.

  Parameter Red : X -> X -> SAT.
  Parameter Red_morph: Proper (eqX ==> eqX ==> eqSAT) Red.

  Parameter Red_sort : forall P, P \in props -> eqSAT (Red props P) snSAT.

  Definition piSAT A F f :=
    interSAT (fun p:{x|x \in A} =>
      prodSAT (Red A (proj1_sig p)) (Red (F (proj1_sig p)) (f (proj1_sig p)))).

  Parameter Red_prod : forall dom f F,
    eq_fun dom F F ->
    f \in prod dom F ->
    eqSAT (Red (prod dom F) f) (piSAT dom F (app f)).

  Existing Instance Red_morph.

(* No empty types (False is inhabited) *)

  Parameter daimon : X.
  Parameter daimon_false : daimon \in prod props (fun P => P).

End RealSN_addon.

(******************************************************************************)
(* The generic model construction: *)

Module MakeModel (M : CC_Model) (MM : RealSN_addon(M)).
Import M.
Import MM.

(* Derived properties of the abstract SN model *)

(* We first introduce the realizability relation, which the conjunction
   of the value and term interpretation requirements *)
Notation "[ x , t ] \real A" := (x \in A  /\ inSAT t (Red A x)) (at level 60).

Lemma piSAT_intro : forall A B f t,
  Lc.sn t -> (* if A is empty *)
  (forall x u, x \in A -> inSAT u (Red A x) -> inSAT (Lc.App t u) (Red (B x) (f x))) ->
  inSAT t (piSAT A B f).
unfold piSAT; intros.
apply interSAT_intro' with (P:=fun x=>x \in A)
   (F:=fun x => prodSAT (Red A x) (Red (B x) (f x))); trivial; intros.
intros ? ?.
apply H0; trivial.
Qed.

Lemma piSAT_elim : forall A B f x t u,
  inSAT t (piSAT A B f) ->
  x \in A ->
  inSAT u (Red A x) ->
  inSAT (Lc.App t u) (Red (B x) (f x)).
intros.
apply interSAT_elim with (x:=exist (fun x => x \in A) x H0) in H; simpl proj1_sig in H.
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
assert (lam dom f \in prod dom F).
 apply prod_intro; intros; trivial.
 apply H2 with SatSet.daimon.
 split; trivial.
 apply varSAT.
split; trivial.
rewrite Red_prod; trivial.
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
 destruct H3.
 apply prodSAT_elim with (Red dom x); trivial.
 apply prodSAT_intro; intros.
 apply H2; auto.
Qed.

Lemma prod_elim : forall dom f x F t u,
  eq_fun dom F F ->
  [f,t] \real prod dom F ->
  [x,u] \real dom ->
  [app f x, Lc.App t u] \real F x.
destruct 2; destruct 1.
split.
 apply prod_elim with (2:=H0); trivial.

 rewrite Red_prod in H1; trivial.
 apply interSAT_elim with (x:=exist (fun x => x \in dom) x H2) in H1; simpl proj1_sig in H1.
 apply prodSAT_elim with (1:=H1); trivial.
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


(* Now the abstract strong normalization proof. *)
Require ObjectSN.
Include ObjectSN.MakeObject(M).


(* Dealing with top sorts.
   We prove all types of top sorts are inhabited. *)

Fixpoint cst_fun (i:val) (e:list trm) (x:X) : X :=
  match e with
  | List.nil => x
  | T::f => lam (int i T) (fun y => cst_fun (V.cons y i) f x)
  end.

Instance cst_morph : Proper (eq_val ==> @eq _ ==> eqX ==> eqX) cst_fun.
do 4 red; intros.
subst y0.
revert x y H.
induction x0; simpl; intros; auto.
apply lam_ext; intros.
 rewrite H; reflexivity.

 red; intros.
 apply IHx0.
 rewrite H2; rewrite H; reflexivity.
Qed.

Fixpoint cst_trm (e:list trm) (x:Lc.term) : Lc.term :=
  match e with
  | List.nil => x
  | T::f => Lc.Abs (Lc.lift 1 (cst_trm f x))
  end.


Lemma cst_trm_sn : forall e t,
  Lc.sn t -> Lc.sn (cst_trm e t).
induction e; simpl; intros; auto.
apply Lc.sn_abs.
apply Lc.sn_lift; auto.
Qed.

Lemma wit_prod : forall x U t,
  (forall i, [x,t] \real int i U) ->
  forall e i,
  [cst_fun i e x, cst_trm e t] \real int i (prod_list e U).
induction e; simpl; intros; auto.
apply prod_intro_lam; intros; auto.
 red; intros.
 rewrite H1; reflexivity.

 red; intros.
 rewrite H1; reflexivity.

 apply Lc.sn_lift.
 apply cst_trm_sn.
 apply real_sn with x (int i U); auto.

 unfold Lc.subst; rewrite Lc.simpl_subst; auto with arith.
 rewrite Lc.lift0.
 trivial.
Qed.


(* We could parameterize non_empty with a val [i0], and
   quantify over i s.t. vshift (length e) i = i0.
   This would allow kind variables. *)
Definition non_empty T :=
  exists e, exists2 U, eq_trm T (prod_list e U) &
    exists x t, forall i, [x,t] \real int i U.

Instance non_empty_morph : Proper (eq_trm ==> iff) non_empty.
unfold non_empty; do 2 red; intros.
split; intros (e,(U,eq_U,inU)); exists e;
  exists U; trivial.
 rewrite <- H; trivial.
 rewrite H; trivial.
Qed.

Lemma prop_non_empty : non_empty prop.
exists List.nil; exists prop; simpl prod_list.
 reflexivity.

 exists (prod props (fun P => P)); exists Lc.K; intro i.
 assert (prod props (fun P => P) \in props).
  apply impredicative_prod; intros; auto.
  red; auto.
 split; trivial.
 simpl; rewrite Red_sort; trivial.
 apply Lc.sn_K.
Qed.

Lemma prod_non_empty : forall T U,
  non_empty U ->
  non_empty (Prod T U).
intros.
destruct H as (e,(U',eq_U,wit_U)).
exists (T::e); exists U'; simpl prod_list; trivial.
rewrite eq_U; reflexivity.
Qed.

Lemma non_empty_witness : forall i T,
  non_empty T ->
  exists x, exists u, [x,u] \real int i T.
intros.
destruct H as (e,(U,eq_U,(wit1,(wit2,in_U)))).
exists (cst_fun i e wit1); exists (cst_trm e wit2).
rewrite eq_U.
apply wit_prod; trivial.
Qed.

Lemma non_empty_lift M k :
  non_empty M <-> non_empty (lift_rec 1 k M).
unfold non_empty; split; intros.
 destruct H as (e,(U,?,(x,(t,?)))).
 destruct lift_prod_list_ex with 1 k e U as (e',?).
 exists e'.
 exists (lift_rec 1 (length e+k) U).
  rewrite H; trivial.

  exists x; exists t; intros.
  rewrite int_lift_rec_eq.
  apply H0.

 destruct H as (e,(U,?,(x,(t,?)))).
 destruct subst_prod_list_ex with (Ref 0) k e U as (e',?).
 exists e'.
 exists (subst_rec (Ref 0) (length e+k) U).
  rewrite <- H1.
  rewrite <- H.
  apply simpl_subst_lift_rec.

  exists x; exists t; intros.
  rewrite int_subst_rec_eq.
  apply H0.
Qed.

(* Semantic typing relation.
   Handles the case of kind: a type that contains all "non-empty" types
   and that is included in no type.
 *)

Definition in_int (i:val) (j:Lc.intt) (M T:trm) :=
  M <> None /\
  match T with
  (* M has type kind *)
  | None => non_empty M /\ Lc.sn (tm j M)
  (* T is a regular type *)
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
  rewrite non_empty_lift with (k:=0) in H.
  rewrite eq_trm_lift_ref_fv in H; auto with arith.
Qed.

Lemma in_int_sn : forall i j M T,
  in_int i j M T -> Lc.sn (tm j M).
destruct 1 as (_,mem).
destruct T; simpl in mem.
 apply real_sn in mem; trivial.

 destruct mem; trivial.
Qed.

(* Environments *)
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


(* Judgements *)
Definition wf (e:env) :=
  exists i, exists j, val_ok e i j.
Definition typ (e:env) (M T:trm) :=
  forall i j, val_ok e i j -> in_int i j M T.
(* Alternative equality: not intensional
Definition eq_typ (e:env) (M M':trm) :=
  forall i j, val_ok e i j -> int i M == int i M'.
*)
Definition eq_typ (e:env) (M M':trm) :=
  (forall i j, val_ok e i j -> int i M == int i M') /\
  (forall j, Lc.conv (tm j M) (tm j M')).
Definition sub_typ (e:env) (M M':trm) :=
  forall i j, val_ok e i j ->
  (forall x t, [x,t] \real int i M -> [x,t] \real int i M').

Instance typ_morph : forall e, Proper (eq_trm ==> eq_trm ==> iff) (typ e).
unfold typ; split; simpl; intros.
 rewrite <- H; rewrite <- H0; auto.
 rewrite H; rewrite H0; auto.
Qed.

Instance eq_typ_morph : forall e, Proper (eq_trm ==> eq_trm ==> iff) (eq_typ e).
unfold eq_typ; split; simpl; intros.
 destruct H1; split; intros.
  rewrite <- H; rewrite <- H0; eauto.
  rewrite <- H; rewrite <- H0; auto.

 destruct H1; split; intros.
  rewrite H; rewrite H0; eauto.
  rewrite H; rewrite H0; auto.
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
  exists x, exists u, [x,u] \real int i T.
intros.
destruct H.
 apply H in H0.
 destruct H0 as (_,(mem,_)); apply non_empty_witness; trivial.

 apply H in H0.
 destruct H0 as (_,mem); simpl in *.
 exists (app daimon (int i T)); exists (Lc.App SatSet.daimon (tm j T)).
 apply prod_elim with (dom:=props) (F:=fun P => P); trivial.
  red; intros; trivial.

  split; [apply daimon_false|apply varSAT].
Qed.


(* Strong normalization *)

Lemma typs_sn : forall e T i j, typs e T -> val_ok e i j -> Lc.sn (tm j T).
destruct 1 as [ty_T|ty_T]; intro is_val; apply ty_T in is_val;
 red in is_val; simpl in is_val.
 destruct is_val as (_,(_,sn)); trivial.
 destruct is_val as (_,mem); apply real_sn in mem; trivial.
Qed.

(* This lemma shows that the abstract model construction entails
   strong normalization.
   At this level, we do have the actual syntax. However, red_term
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

(* Context formation rules *)

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
destruct typs_non_empty with (1:=H0) (2:=is_val) as (x,(u,non_mt)).
exists (V.cons x i); exists (I.cons u j).
apply vcons_add_var; trivial.
Qed.

(* Equality rules *)

Lemma refl : forall e M, eq_typ e M M.
red; simpl; split; reflexivity.
Qed.

Lemma sym : forall e M M', eq_typ e M M' -> eq_typ e M' M.
unfold eq_typ; destruct 1; split; intros; symmetry; eauto.
Qed.

Lemma trans : forall e M M' M'',
  eq_typ e M M' -> eq_typ e M' M'' -> eq_typ e M M''.
unfold eq_typ; destruct 1; destruct 1; split; intros.
 transitivity (int i M'); eauto.

 transitivity (tm j M'); trivial.
Qed.

Instance eq_typ_setoid : forall e, Equivalence (eq_typ e).
split.
 exact (@refl e).
 exact (@sym e).
 exact (@trans e).
Qed.


Lemma eq_typ_app : forall e M M' N N',
  eq_typ e M M' ->
  eq_typ e N N' ->
  eq_typ e (App M N) (App M' N').
unfold eq_typ; destruct 1; destruct 1; split; simpl; intros.
 apply app_ext; eauto.

 apply Lc.conv_conv_app; auto.
Qed.


Lemma eq_typ_abs : forall e T T' M M',
  eq_typ e T T' ->
  eq_typ (T::e) M M' ->
  T <> kind ->
  eq_typ e (Abs T M) (Abs T' M').
Proof.
unfold eq_typ; destruct 1; destruct 1; split; simpl; intros.
 apply lam_ext; eauto.
 red; intros.
 rewrite <- H6.
 apply H1 with (j:=I.cons SatSet.daimon j).
 apply vcons_add_var; auto.
 split; trivial; apply varSAT.

 unfold CAbs, Lc.App2.
 apply Lc.conv_conv_app; auto.
 apply Lc.conv_conv_app; auto with *.
 apply Lc.conv_conv_abs; auto.
Qed.

Lemma eq_typ_prod : forall e T T' U U',
  eq_typ e T T' ->
  eq_typ (T::e) U U' ->
  T <> kind ->
  eq_typ e (Prod T U) (Prod T' U').
unfold eq_typ; simpl; intros.
split; intros.
 apply prod_ext.
  eapply H; eauto.
 red; intros.
 rewrite <- H4.
 apply H0 with (j:=I.cons SatSet.daimon j).
 apply vcons_add_var; auto.
 split; trivial; apply varSAT.

 unfold CProd, Lc.App2.
 apply Lc.conv_conv_app.
  apply Lc.conv_conv_app; auto with *.
  apply H.

  apply Lc.conv_conv_abs.
  apply H0.
Qed.

Lemma eq_typ_beta : forall e T M M' N N',
  eq_typ (T::e) M M' ->
  eq_typ e N N' ->
  typ e N T -> (* Typed reduction! *)
  T <> kind ->
  eq_typ e (App (Abs T M) N) (subst N' M').
Proof.
unfold eq_typ, typ, App, Abs; simpl; intros.
split; intros.
 assert (eq_fun (int i T)
   (fun x => int (V.cons x i) M) (fun x => int (V.cons x i) M)).
  apply add_var_eq_fun with (T:=T); intros; trivial; reflexivity.
 assert ([int i N, tm j N] \real int i T).
  apply H1 in H3.
  apply in_int_not_kind in H3; trivial.
 rewrite beta_eq; auto.
  rewrite <- int_subst_eq.
  destruct H0 as (H0,_); destruct H as (H,_).
  rewrite <- H0 with (1:=H3).
  apply H with (j:=I.cons (tm j N) j).
  apply vcons_add_var; auto.

  apply H5.

 apply Lc.trans_conv_conv with (Lc.App (CAbs (tm j T) (tm (Lc.ilift j) M')) (tm j N)).
  apply Lc.conv_conv_app; auto with *.
  unfold CAbs, Lc.App2.
  apply Lc.conv_conv_app; auto with *.
  apply Lc.conv_conv_app; auto with *.
  apply Lc.conv_conv_abs.
  apply H.
 apply Lc.trans_conv_conv with (Lc.App (CAbs (tm j T) (tm (Lc.ilift j) M')) (tm j N')).
  apply Lc.conv_conv_app; auto with *.
  apply H0.
 unfold CAbs, Lc.App2, Lc.K.
 eapply Lc.trans_conv_conv.
  apply Lc.conv_conv_app;[|apply Lc.refl_conv].
  apply Lc.conv_conv_app;[|apply Lc.refl_conv].
  apply Lc.red_conv; apply Lc.one_step_red; apply Lc.beta.
  unfold Lc.subst; simpl.
 eapply Lc.trans_conv_conv.
  apply Lc.conv_conv_app;[|apply Lc.refl_conv].
  apply Lc.red_conv; apply Lc.one_step_red; apply Lc.beta.
 unfold Lc.subst; rewrite Lc.simpl_subst; auto with arith; rewrite Lc.lift0.
 rewrite tm_subst_eq. 
 apply Lc.red_conv; apply Lc.one_step_red; apply Lc.beta.
Qed.

(* Typing rules *)

Lemma typ_prop : forall e, typ e prop kind.
red; simpl; intros.
split; try discriminate.
split; simpl; auto.
 apply prop_non_empty.

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
  (exists x, exists u, [x,u] \real dom) ->
  (forall x u, [x, u] \real dom -> [f x, Lc.subst u m] \real F x) ->
  [lam dom f, CAbs t m] \real prod dom F.
intros.
apply prod_intro_lam in H3; trivial.
unfold CAbs; apply real_exp_K; trivial.
(* *)
destruct H2.
destruct H2.
apply H3 in H2.
apply real_sn in H2.
apply Lc.sn_subst with x0; trivial.
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

Lemma typ_beta : forall e T M N U,
  typs e T ->
  typ (T::e) M U ->
  typ e N T ->
  T <> kind ->
  U <> kind ->
  typ e (App (Abs T M) N) (subst N U).
Proof.
intros.
apply typ_app with T; trivial.
apply typ_abs; trivial.
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
destruct (typs_non_empty ty_T is_val) as (witT,(witt,in_T)).
specialize vcons_add_var with (1:=is_val) (2:=in_T) (3:=T_not_tops);
  intros in_U.
apply ty_U in in_U.
split;[discriminate|simpl].
assert (snU : Lc.sn (tm (Lc.ilift j) U)).
 apply Lc.sn_subst with witt.
 rewrite <- tm_subst_cons.
 destruct is_srt; subst s2; simpl in *.
  destruct in_U as (_,(_,snu)); trivial.

  destruct in_U as (_,mem); simpl in mem.
  apply real_sn in mem; trivial.
destruct is_srt; subst s2; simpl in *.
 (* s2=kind *)
 split.
  apply prod_non_empty.
  destruct in_U as (_,(mem,_)); trivial.

  apply Lc.sn_K2.
   apply typs_sn with (1:=ty_T) (2:=is_val).

   apply Lc.sn_abs; trivial.

 (* s2=prop *)
 unfold CProd.
 apply real_exp_K.
  apply Lc.sn_abs; trivial.
 assert (prod (int i T) (fun x => int (V.cons x i) U) \in props).
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
 rewrite Red_sort; trivial.
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
destruct H0.
specialize H with (1:=H3).
specialize H0 with (1:=H3).
generalize (proj1 H); intro.
apply in_int_not_kind in H; trivial.
apply in_int_intro; trivial.
rewrite <- H0; trivial.
Qed.

(* Weakening *)


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

  rewrite non_empty_lift with (k:=0).
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
  unfold lift; rewrite <- non_empty_lift; trivial.

  unfold lift; rewrite tm_lift_rec_eq; trivial.
Qed.


(* Subtyping rules *)

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

(* subsumption: generalizes typ_conv *)
Lemma typ_subsumption : forall e M T T',
  typ e M T ->
  sub_typ e T T' ->
  T <> kind ->
  T' <> kind ->
  typ e M T'.
Proof.
unfold typ, sub_typ, in_int; simpl; intros; auto.
destruct T' as [(T',T'm)|]; simpl in *; trivial; auto.
 destruct T as [(T,Tm)|]; simpl in *.
  destruct (H _ _ H3); eauto.

  elim H1; trivial.

 elim H2; trivial.
Qed.

(* Covariance can be derived if we have a weak eta property:
   any function is a lambda abstraction *with the same domain*.
   This is OK with set-theoretical functions (in contrast with
   general eta which does not hold on set-theoretical functions).
   This property could be added to the abstract domain.

   Contravariance of product does not hold in set-theory.
 *)
Definition sub_typ_covariant
  (eta_eq : forall dom F f, f \in prod dom F -> f == lam dom (app f))
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
  apply (proj1 eqU) with (1:=is_val).

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
  rewrite (proj1 eqU _ _ is_val); trivial.

  apply prod_elim with (2:=in1).
   red; intros.
   rewrite H1; auto with *.

   rewrite (proj1 eqU _ _ is_val); trivial.
Qed.

End MakeModel.
