Set Implicit Arguments.
Require Import List Compare_dec.
Require Import Sat.
Require Import Models.
Require ObjectSN.

Module Lc := Lambda.

(** Equiping the model with saturated sets *)
Module Type SN_addon (M : CC_Model).
  Import M.

  Parameter Red : X -> SAT.
  Parameter Red_morph : Proper (eqX ==> eqSAT) Red.

  Parameter Red_sort : eqSAT (Red props) snSAT.

  Parameter Red_prod : forall A B,
    eqSAT (Red (prod A B))
     (prodSAT (Red A)
        (interSAT (fun p:{y|y\in A} => Red (B (proj1_sig p))))).

  Parameter daemon : X.
  Parameter daemon_false : daemon \in prod props (fun P => P).

  Existing Instance Red_morph.

End SN_addon.

(** Now the abstract strong normalization proof. *)

Module MakeModel(M : CC_Model) (SN : SN_addon M).
Import M.
Import SN.

(** We use the generic model construction upon the
   abstract model
 *)
Include ObjectSN.MakeObject(M).


(** Dealing with top sorts *)

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

Lemma wit_prod : forall x U,
  (forall i, x \in int i U) ->
  forall e i,
  cst_fun i e x \in int i (prod_list e U).
induction e; simpl; intros; auto.
apply prod_intro; intros; auto.
 red; intros.
 rewrite H1; reflexivity.

 red; intros.
 rewrite H1; reflexivity.
Qed.

(* We could parameterize non_empty with a val [i0], and
   quantify over i s.t. vshift (length e) i = i0.
   This would allow kind variables. *)
Definition non_empty T :=
  exists e, exists2 U, eq_trm T (prod_list e U) &
    exists x, forall i, x \in int i U.

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

 exists (prod props (fun P => P)); intros.
 apply impredicative_prod; intros; auto.
 red; auto.
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
  exists x, x \in int i T.
intros.
destruct H as (e,(U,eq_U,(wit,in_U))).
exists (cst_fun i e wit).
rewrite eq_U.
apply wit_prod; trivial.
Qed.

Lemma non_empty_lift M k :
  non_empty M <-> non_empty (lift_rec 1 k M).
unfold non_empty; split; intros.
 destruct H as (e,(U,?,(x,?))).
 destruct lift_prod_list_ex with 1 k e U as (e',?).
 exists e'.
 exists (lift_rec 1 (length e+k) U).
  rewrite H; trivial.

  exists x; intros.
  rewrite int_lift_rec_eq.
  apply H0.

 destruct H as (e,(U,?,(x,?))).
 destruct subst_prod_list_ex with (Ref 0) k e U as (e',?).
 exists e'.
 exists (subst_rec (Ref 0) (length e+k) U).
  rewrite <- H1.
  rewrite <- H.
  apply simpl_subst_lift_rec.

  exists x; intros.
  rewrite int_subst_rec_eq.
  apply H0.
Qed.


(** Semantic typing relation.
   Handles the case of kind: a type that contains all "non-empty" types
   and that is included in no type.
 *)
Definition in_int (i:val) (j:Lc.intt) (M T:trm) :=
  M <> kind /\
  match T with
  | None => non_empty M /\ Lc.sn (tm j M)
  | _ => int i M \in int i T /\ inSAT (tm j M) (Red (int i T))
  end.

Instance in_int_morph : Proper
  (eq_val ==> pointwise_relation nat (@eq Lc.term) ==> eq_trm ==> eq_trm ==> iff)
  in_int.
apply morph_impl_iff4; auto with *.
unfold in_int; do 5 red; intros.
repeat rewrite eq_kind.
destruct x2; destruct y2; try contradiction.
 rewrite H; rewrite H0; rewrite H1; rewrite H2.
 reflexivity.

 rewrite H0; rewrite H1.
 reflexivity.
Qed.

Lemma in_int_not_kind : forall i j M T,
  in_int i j M T ->
  T <> kind ->
  int i M \in int i T /\
  inSAT (tm j M) (Red (int i T)).
destruct T; intros in_T not_tops;[|elim not_tops; reflexivity].
destruct in_T as (mem,sat); trivial.
Qed.

Lemma in_int_intro : forall i j M T,
  int i M \in int i T ->
  inSAT (tm j M) (Red (int i T)) ->
  M <> kind ->
  T <> kind ->
  in_int i j M T.
red; intros.
destruct T; auto.
elim H2; trivial.
Qed.


Lemma in_int_var0 : forall i j x t T,
  x \in int i T ->
  inSAT t (Red (int i T)) ->
  T <> kind ->
  in_int (V.cons x i) (I.cons t j) (Ref 0) (lift 1 T).
intros.
red; simpl.
revert H1; pattern T at 1 2.
case T; [|destruct 1;reflexivity].
simpl; intros _ _.
split; [discriminate|].
rewrite int_cons_lift_eq; auto.
Qed.

Lemma in_int_varS : forall i j x t n T,
  in_int i j (Ref n) (lift (S n) T) ->
  in_int (V.cons x i) (I.cons t j) (Ref (S n)) (lift (S (S n)) T).
destruct 1 as (_,in_T); split; [discriminate|].
revert in_T; pattern T at 1 4; case T; simpl.
 intros _ in_T.
 rewrite split_lift.
 rewrite int_cons_lift_eq; trivial.

 destruct 1; split; trivial.
 rewrite non_empty_lift with (k:=0) in H.
 rewrite eq_trm_lift_ref_fv in H; auto with arith.
Qed.

Lemma in_int_sn : forall i j M T,
  in_int i j M T -> Lc.sn (tm j M).
intros i j M [f|] (_,(_,sat)); trivial.
apply sat_sn in sat; trivial.
Qed.

(** Environments *)
Definition env := list trm.

Definition val_ok (e:env) (i:val) (j:Lc.intt) :=
  forall n T, nth_error e n = value T ->
  in_int i j (Ref n) (lift (S n) T).

Lemma vcons_add_var : forall e T i j x t,
  val_ok e i j ->
  x \in int i T ->
  inSAT t (Red (int i T)) ->
  T <> kind ->
  val_ok (T::e) (V.cons x i) (I.cons t j).
unfold val_ok; simpl; intros.
destruct n; simpl in *.
 injection H3; clear H3; intro; subst; simpl in *. 
 apply in_int_var0; trivial.

 apply in_int_varS; auto.
Qed.

Lemma add_var_eq_fun : forall T U U' i,
  (forall x, x \in int i T -> int (V.cons x i) U == int (V.cons x i) U') -> 
  eq_fun (int i T)
    (fun x => int (V.cons x i) U)
    (fun x => int (V.cons x i) U').
red; intros.
rewrite <- H1; auto.
Qed.


Lemma vcons_add_var0 : forall e T i j x,
  val_ok e i j ->
  x \in int i T ->
  T <> kind ->
  val_ok (T::e) (V.cons x i) (I.cons daimon j).
intros.
apply vcons_add_var; trivial.
apply varSAT.
Qed.

(** Judgements *)

Definition wf (e:env) :=
  exists i, exists j, val_ok e i j.
Definition typ (e:env) (M T:trm) :=
  forall i j, val_ok e i j -> in_int i j M T.
Definition eq_typ (e:env) (M M':trm) :=
  forall i j, val_ok e i j -> int i M == int i M'.

Instance typ_morph : forall e, Proper (eq_trm ==> eq_trm ==> iff) (typ e).
unfold typ; split; simpl; intros.
 rewrite <- H; rewrite <- H0; auto.
 rewrite H; rewrite H0; auto.
Qed.

Instance eq_typ_morph : forall e, Proper (eq_trm ==> eq_trm ==> iff) (eq_typ e).
unfold eq_typ; split; simpl; intros.
 rewrite <- H; rewrite <- H0; eauto.
 rewrite H; rewrite H0; eauto.
Qed.

(** Strong normalization *)

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


(* Well-formed types: terms typed by a sort *)

Definition typs e T :=
  typ e T kind \/ typ e T prop.

Lemma typs_not_kind : forall e T, wf e -> typs e T -> T <> kind.
intros e T (i,(j,is_val)) [ty|ty]; apply ty in is_val;
  destruct is_val; assumption.
Qed.

Lemma typs_non_empty : forall e T i j,
  typs e T ->
  val_ok e i j ->
  exists x, x \in int i T.
intros.
destruct H.
 apply H in H0.
 destruct H0 as (_,(mem,_)); apply non_empty_witness; trivial.

 exists (app daemon (int i T)).
 apply H in H0.
 destruct H0 as (_,(mem,_)); simpl in *.
 apply prod_elim with (2:=daemon_false); trivial.
 red; intros; trivial.
Qed.


(** Context formation rules *)

Lemma wf_nil : wf List.nil.
red.
exists vnil; exists (fun _ => daimon).
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
exists (V.cons x i); exists (I.cons daimon j).
apply vcons_add_var0; trivial.
Qed.

(** Equality rules *)

Lemma refl : forall e M, eq_typ e M M.
red; simpl; reflexivity.
Qed.

Lemma sym : forall e M M', eq_typ e M M' -> eq_typ e M' M.
unfold eq_typ; symmetry; eauto.
Qed.

Lemma trans : forall e M M' M'', eq_typ e M M' -> eq_typ e M' M'' -> eq_typ e M M''.
unfold eq_typ; intros.
transitivity (int i M'); eauto.
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
apply H0 with (j:=I.cons daimon j).
apply vcons_add_var0; auto.
Qed.

Lemma eq_typ_prod : forall e T T' U U',
  eq_typ e T T' ->
  eq_typ (T::e) U U' ->
  T <> kind ->
  eq_typ e (Prod T U) (Prod T' U').
unfold eq_typ; simpl; intros.
apply prod_ext; eauto.
red; intros.
rewrite <- H4.
apply H0 with (j:=I.cons daimon j).
apply vcons_add_var0; auto.
Qed.

Lemma eq_typ_beta : forall e T M M' N N',
  eq_typ (T::e) M M' ->
  eq_typ e N N' ->
  typ e N T -> (* Typed reduction! *)
  T <> kind ->
  eq_typ e (App (Abs T M) N) (subst N' M').
Proof.
unfold eq_typ, typ, App, Abs; simpl; intros.
assert (eq_fun (int i T)
  (fun x => int (V.cons x i) M) (fun x => int (V.cons x i) M)).
 apply add_var_eq_fun with (T:=T); intros; trivial; reflexivity.
assert (int i N \in int i T).
 apply H1 in H3.
 apply in_int_not_kind in H3; trivial.
 destruct H3; trivial.
rewrite beta_eq; auto.
rewrite <- int_subst_eq.
rewrite <- H0; eauto.
apply H with (j:=I.cons daimon j).
apply vcons_add_var0; auto.
Qed.

(** Typing rules *)

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
destruct ty_v.
apply in_int_not_kind in ty_u; try discriminate.
destruct ty_u.
simpl in *.
rewrite Red_prod in H2.
apply prod_elim with (x:=int i v) in H1; trivial.
 apply in_int_intro; simpl; trivial; try discriminate.
  rewrite <- int_subst_eq; trivial.

  rewrite <- int_subst_eq.
  apply prodSAT_elim with (v:=tm j v) in H2; trivial.
  apply interSAT_elim with
   (x:=exist (fun z=>z\in int i V) (int i v) H) in H2; trivial.

  destruct Ur as [Ur|]; simpl; try discriminate; trivial.

 red; intros.
 rewrite H4; reflexivity.
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
 apply prod_intro; intros.
  red; intros.
  rewrite H0; reflexivity.

  red; intros.
  rewrite H0; reflexivity.

  apply vcons_add_var0 with (x:=x) (T:=T) in is_val; trivial.
  apply ty_M in is_val.
  apply in_int_not_kind in is_val; trivial.
  destruct is_val; trivial.

 rewrite Red_prod.
 destruct (typs_non_empty ty_T is_val) as (wit,in_T).
 apply KSAT_intro.
  destruct ty_T as [ty_T|ty_T]; apply ty_T in is_val;
    destruct is_val as (_,(_,satT)); simpl in satT; trivial.
  rewrite Red_sort in satT; trivial.

  apply prodSAT_intro; intros.
  apply interSAT_intro; intros.
   exists wit; trivial.

   destruct x; simpl in *.
   assert (val_ok (T::e) (V.cons x i) (I.cons v j)).
    apply vcons_add_var; auto.
   apply ty_M in H0.
   apply in_int_not_kind in H0; trivial.
   destruct H0 as (_,H0).
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
destruct (typs_non_empty ty_T is_val) as (witT,in_T).
specialize vcons_add_var0 with (1:=is_val) (2:=in_T) (3:=T_not_tops);
  intros in_U.
apply ty_U in in_U.
assert (Lc.sn (tm j T)).
 destruct ty_T as [ty_T|ty_T]; apply ty_T in is_val;
   destruct is_val as (_,(_,satT)); trivial.
 apply sat_sn in satT; trivial.
split;[discriminate|destruct is_srt; subst s2; split;simpl].
 (* s2=kind *)
 (* non_empty: *)
 apply prod_non_empty.
 destruct in_U as (_,(mem,_)); trivial.

 (* sn *)
 destruct in_U as (_,(_,satU)).
 rewrite tm_subst_cons in satU.
 apply Lc.sn_subst in satU.
 apply KSAT_intro with (A:=snSAT); auto.

 (* s2=prop *)
 (* value *)
 apply impredicative_prod; intros.   
  red; intros.
  rewrite H2; reflexivity.

  clear in_U.
  specialize vcons_add_var0 with (1:=is_val) (2:=H1) (3:=T_not_tops);
    intros in_U.
  apply ty_U in in_U.
  apply in_int_not_kind in in_U;[|discriminate].
  destruct in_U; trivial.

 (* sat *)
 destruct in_U as (_,(_,satU)).
 rewrite Red_sort in satU|-*; simpl.
 rewrite tm_subst_cons in satU.
 apply Lc.sn_subst in satU.
 apply KSAT_intro with (A:=snSAT); auto.
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
destruct H.
apply in_int_intro; trivial.
 rewrite <- H0; trivial.

 rewrite <- H0; trivial.
Qed.

End MakeModel.

