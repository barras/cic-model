Set Implicit Arguments.
Require Import List Compare_dec.
Require Import Sat.
Require Import Models SnModels TypModels.
Require ObjectSN.

Module Lc := Lambda.

(** * The abstract strong normalization proof. *)

Module MakeModel(M : SN_CC_Model) <: Syntax (* Judge *).
Import M.

(** We use the generic model construction based on the
   abstract model
 *)
Include ObjectSN.MakeObject(M).

(** * Semantic typing relation *)

(** Handles the case of kind: a type that contains all "non-empty" types
   and that is included in no type.
 *)
Definition in_int (M T:term) (i:val) (j:Lc.intt) :=
  M <> kind /\
  match T with
  | None => kind_ok M /\ Lc.sn (tm M j)
  | _ => int M i ∈ int T i /\ inSAT (tm M j) (Real (int T i))
  end.

Instance in_int_morph : Proper
  (eq_term ==> eq_term ==> eq_val ==> pointwise_relation nat (@eq Lc.term) ==> iff)
  in_int.
apply morph_impl_iff4; auto with *.
unfold in_int; do 5 red; intros.
repeat rewrite eq_kind.
destruct x0; destruct y0; try contradiction.
 rewrite H; rewrite H0; rewrite H1; rewrite H2.
 reflexivity.

 rewrite H; rewrite H2.
 reflexivity.
Qed.

Lemma in_int_not_kind : forall i j M T,
  in_int M T i j ->
  T <> kind ->
  int M i ∈ int T i /\
  inSAT (tm M j) (Real (int T i)).
destruct T; intros in_T not_tops;[|elim not_tops; reflexivity].
destruct in_T as (mem,sat); trivial.
Qed.

Lemma in_int_intro : forall i j M T,
  int M i ∈ int T i ->
  inSAT (tm M j) (Real (int T i)) ->
  M <> kind ->
  T <> kind ->
  in_int M T i j.
red; intros.
destruct T; auto.
elim H2; trivial.
Qed.

(* We do not accept kind variables yet *)
Lemma in_int_var0 : forall i j x t T,
  x ∈ int T i ->
  inSAT t (Real (int T i)) ->
  T <> kind ->
  in_int (Ref 0) (lift 1 T) (V.cons x i) (I.cons t j).
intros.
red; simpl.
revert H1; pattern T at 1 2.
case T; [|destruct 1;reflexivity].
simpl; intros _ _.
split; [discriminate|].
rewrite int_cons_lift_eq; auto.
Qed.

Lemma in_int_varS : forall i j x t n T,
  in_int (Ref n) (lift (S n) T) i j ->
  in_int (Ref (S n)) (lift (S (S n)) T) (V.cons x i) (I.cons t j).
destruct 1 as (_,in_T); split; [discriminate|].
revert in_T; pattern T at 1 4; case T; simpl.
 intros _ in_T.
 rewrite split_lift.
 rewrite int_cons_lift_eq; trivial.

 destruct 1; split; trivial.
 apply kind_ok_refS; trivial.
Qed.

Lemma in_int_sn : forall i j M T,
  in_int M T i j -> Lc.sn (tm M j).
intros i j M [f|] (_,(_,sat)); trivial.
apply sat_sn in sat; trivial.
Qed.

(** * Environments *)
Definition env := list term.

Definition val_ok (e:env) (i:val) (j:Lc.intt) :=
  forall n T, nth_error e n = value T ->
  in_int (Ref n) (lift (S n) T) i j.

Lemma vcons_add_var : forall e T i j x t,
  val_ok e i j ->
  x ∈ int T i ->
  inSAT t (Real (int T i)) ->
  T <> kind ->
  val_ok (T::e) (V.cons x i) (I.cons t j).
unfold val_ok; simpl; intros.
destruct n; simpl in *.
 injection H3; clear H3; intro; subst; simpl in *. 
 apply in_int_var0; trivial.

 apply in_int_varS; auto.
Qed.

Lemma add_var_eq_fun : forall T U U' i,
  (forall x, x ∈ int T i -> int U (V.cons x i) == int U' (V.cons x i)) ->
  eq_fun (int T i)
    (fun x => int U (V.cons x i))
    (fun x => int U' (V.cons x i)).
red; intros.
rewrite <- H1; auto.
Qed.


Lemma vcons_add_var0 : forall e T i j x,
  val_ok e i j ->
  x ∈ int T i ->
  T <> kind ->
  val_ok (T::e) (V.cons x i) (I.cons SatSet.daimon j).
intros.
apply vcons_add_var; trivial.
apply varSAT.
Qed.

(** * Judgements *)
Module J.
(** #<a name="MakeModel.wf"></a># *)
Definition wf (e:env) :=
  exists i, exists j, val_ok e i j.
Definition typ (e:env) (M T:term) :=
  forall i j, val_ok e i j -> in_int M T i j.
Definition eq_typ (e:env) (M M':term) :=
  forall i j, val_ok e i j -> int M i == int M' i.
Definition sub_typ (e:env) (M M':term) :=
  forall i j, val_ok e i j ->
  forall x t, x ∈ int M i -> inSAT t (Real (int M  i)) ->
    x ∈ int M' i /\ inSAT t (Real (int M' i)).

Definition typ_sub (e:env) (s:sub) (f:env) :=
  forall i j, val_ok e i j ->
  val_ok f (sint s i) (stm s j).

Instance typ_morph : forall e, Proper (eq_term ==> eq_term ==> iff) (typ e).
unfold typ; split; simpl; intros.
 rewrite <- H; rewrite <- H0; auto.
 rewrite H; rewrite H0; auto.
Qed.

Instance eq_typ_morph : forall e, Proper (eq_term ==> eq_term ==> iff) (eq_typ e).
unfold eq_typ; split; simpl; intros.
 rewrite <- H; rewrite <- H0; eauto.
 rewrite H; rewrite H0; eauto.
Qed.

Instance sub_typ_morph : forall e, Proper (eq_term ==> eq_term ==> iff) (sub_typ e).
unfold sub_typ; split; simpl; intros.
 rewrite <-H in H3,H4.
 rewrite <-H0.
 eauto.

 rewrite H in H3,H4.
 rewrite H0.
 eauto.
Qed.

End J.
Import J.

Lemma assume_wf e M T :
  (wf e -> typ e M T) ->
  typ e M T.
red; intros; apply H; trivial.
red; eauto.
Qed.

(** * Strong normalization *)

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

(** If there exists a proposition whose proofs are realized only by neutral
    terms, then there is no closed proof of the absurd proposition. *)
Theorem model_consistency FF :
  FF ∈ props ->
  eqSAT (Real FF) neuSAT ->
  forall M, ~ typ List.nil M (Prod prop (Ref 0)).
intros tyFF neutr M prf_of_false.
red in prf_of_false.
(* The valuation below contains only closed terms, and it interprets the
   empty context *) 
assert (valok : val_ok List.nil (V.nil props) (I.nil (Lc.Abs (Lc.Ref 0)))).
 red; intros.
 destruct n; discriminate H.
specialize prf_of_false with (1:=valok).
clear valok.
destruct prf_of_false as (_,(tym,satm)).
simpl in tym,satm.
set (prf := tm M (I.nil (Lc.Abs (Lc.Ref 0)))) in *.
assert (forall S, inSAT (Lc.App prf (Lc.Abs (Lc.Ref 0))) S).
 apply neuSAT_def.
 assert (inSAT (Lc.Abs (Lc.Ref 0)) (Real props)).
  rewrite Real_sort; trivial.
  apply snSAT_intro.
  apply Lc.sn_abs; auto with *.  
 rewrite Real_prod in satm.
 apply prodSAT_elim with (2:=H) in satm.
 apply depSAT_elim' in satm.
 rewrite <- neutr.
 apply satm; trivial.
destruct (neutral_not_closed _ H).
inversion_clear H0.
 apply tm_closed in H1.
 apply H1.
 red; intros.
 unfold I.nil in H0; simpl in H0.
 inversion_clear H0.
 inversion H2.

 inversion_clear H1.
 inversion H0.
Qed.

(** In a consistency model, we cannot have A=(A->B),
    which contradicts (definitional) propositional extensionality. *)

Theorem sn_model_A_not_A_to_B e A B :
  wf e ->
  ~ eq_typ e A (Prod A B).
intros (i,(j,vok)) H.
red in H; specialize H with (1:=vok).
apply Real_morph in H.
simpl in H.
rewrite Real_prod in H.
symmetry in H.
apply AB_is_not_A in H; trivial.
Qed.

 (* Well-formed types: terms typed by a sort *)

Definition typs e T :=
  typ e T kind \/ typ e T prop.

Lemma typs_not_kind : forall e T, wf e -> typs e T -> T <> kind.
intros e T (i,(j,is_val)) [ty|ty]; apply ty in is_val;
  destruct is_val; assumption.
Qed.

Lemma typs_kind_ok : forall e T i j,
  typs e T ->
  val_ok e i j ->
  exists x, x ∈ int T i.
intros.
destruct H.
 apply H in H0.
 destruct H0 as (_,(mem,_)); apply kind_ok_witness; trivial.

 exists (app daimon (int T i)).
 apply H in H0.
 destruct H0 as (_,(mem,_)); simpl in *.
 apply prod_elim with (2:=daimon_false); trivial.
 red; intros; trivial.
Qed.

Definition type_ok e T :=
  T <> kind /\ forall i j, val_ok e i j -> Lc.sn (tm T j) /\ exists w, w ∈ int T i.

Lemma typs_type_ok e T :
  wf e -> typs e T -> type_ok e T.
intros (i0,(j0,is_val0)) ty_T.
split; intros.
 destruct ty_T as [ty_T|ty_T]; apply ty_T in is_val0; destruct is_val0; trivial.

 split.
  destruct ty_T as [ty_T|ty_T]; apply ty_T in H; apply in_int_sn in H; trivial.

  apply typs_kind_ok with (1:=ty_T) (2:=H).
Qed.

Lemma typs_is_non_empty e i j T :
  typs e T ->
  val_ok e i j -> 
  T <> kind /\ Lc.sn (tm T j) /\ exists w, w ∈ int T i.
split.
 apply typs_not_kind with (2:=H).
 exists i; exists j; trivial.
split.
 destruct H; apply H in H0; apply in_int_sn in H0; trivial.

 apply typs_kind_ok with (1:=H) (2:=H0).
Qed.

(** #<a name="MakeModel.TypingRules"></a># *)

(** * Inference rules *)

(** ** Context formation rules *)

Lemma wf_nil : wf List.nil.
red.
exists vnil; exists (fun _ => SatSet.daimon).
red; intros.
destruct n; discriminate.
Qed.

Lemma wf_cons_ok : forall e T,
  wf e ->
  type_ok e T ->
  wf (T::e).
unfold wf; intros e T (i,(j,is_val)) (T_nk,inh_T).
destruct inh_T with (1:=is_val) as (_,(x,non_mt)).
exists (V.cons x i); exists (I.cons SatSet.daimon j).
apply vcons_add_var0; trivial.
Qed.

Lemma wf_cons : forall e T,
  wf e ->
  typs e T ->
  wf (T::e).
unfold wf; intros.
assert (T <> kind).
 apply typs_not_kind in H0; trivial.
destruct H as (i,(j,is_val)).
destruct typs_kind_ok with (1:=H0) (2:=is_val) as (x,non_mt).
exists (V.cons x i); exists (I.cons SatSet.daimon j).
apply vcons_add_var0; trivial.
Qed.

(** ** Equality rules *)

Lemma refl : forall e M, eq_typ e M M.
red; simpl; reflexivity.
Qed.

Lemma sym : forall e M M', eq_typ e M M' -> eq_typ e M' M.
unfold eq_typ; symmetry; eauto.
Qed.

Lemma trans : forall e M M' M'', eq_typ e M M' -> eq_typ e M' M'' -> eq_typ e M M''.
unfold eq_typ; intros.
transitivity (int M' i); eauto.
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
apply H0 with (j:=I.cons SatSet.daimon j).
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
apply H0 with (j:=I.cons SatSet.daimon j).
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
assert (eq_fun (int T i)
  (fun x => int M (V.cons x i)) (fun x => int M (V.cons x i))).
 apply add_var_eq_fun with (T:=T); intros; trivial; reflexivity.
assert (int N i ∈ int T i).
 apply H1 in H3.
 apply in_int_not_kind in H3; trivial.
 destruct H3; trivial.
rewrite beta_eq; auto.
rewrite <- int_subst_eq.
rewrite <- H0; eauto.
apply H with (j:=I.cons SatSet.daimon j).
apply vcons_add_var0; auto.
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
destruct ty_v.
apply in_int_not_kind in ty_u; try discriminate.
destruct ty_u.
simpl in *.
rewrite Real_prod in H2.
apply prod_elim with (x:=int v i) in H1; trivial.
 apply in_int_intro; simpl; trivial; try discriminate.
  rewrite <- int_subst_eq; trivial.

  rewrite <- int_subst_eq.
  apply prodSAT_elim with (v:=tm v j) in H2; trivial.
  apply (depSAT_elim _ H2); trivial.

  destruct Ur as [Ur|]; simpl; try discriminate; trivial.

 red; intros.
 rewrite H4; reflexivity.
Qed.

Lemma typ_abs_ok : forall e T M U,
  type_ok e T ->
  typ (T :: e) M U ->
  U <> kind ->
  typ e (Abs T M) (Prod T U).
Proof.
intros e T M U (T_not_tops,inh_T) ty_M not_tops i j is_val.
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

 rewrite Real_prod.
 specialize inh_T with (1:=is_val).
 destruct inh_T as (snT, (wit, in_T)).
 apply KSAT_intro; trivial.
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

Lemma typ_abs : forall e T M U,
  typs e T ->
  typ (T :: e) M U ->
  U <> kind ->
  typ e (Abs T M) (Prod T U).
Proof.
intros e T M U ty_T ty_M not_tops.
apply assume_wf; intro wfe.
apply typ_abs_ok; trivial.
apply typs_type_ok; trivial.
Qed.

Lemma typ_beta_ok : forall e T M N U,
  type_ok e T ->
  typ (T::e) M U ->
  typ e N T ->
  T <> kind ->
  U <> kind ->
  typ e (App (Abs T M) N) (subst N U).
Proof.
intros.
apply typ_app with T; trivial.
apply typ_abs_ok; trivial.
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

Lemma typ_prod_prop : forall e T U,
  type_ok e T ->
  typ (T :: e) U prop ->
  typ e (Prod T U) prop.
Proof.
intros e T U (T_not_tops, inh_T) ty_U i j is_val.
specialize inh_T with (1:=is_val).
destruct inh_T as (snT,(witT, in_T)).
specialize vcons_add_var0 with (1:=is_val) (2:=in_T) (3:=T_not_tops);
  intros in_U.
apply ty_U in in_U.
split;[discriminate|split;simpl].
 (* value *)
 apply impredicative_prod; intros.   
  red; intros.
  rewrite H0; reflexivity.

  clear in_U.
  specialize vcons_add_var0 with (1:=is_val) (2:=H) (3:=T_not_tops);
    intros in_U.
  apply ty_U in in_U.
  apply in_int_not_kind in in_U;[|discriminate].
  destruct in_U; trivial.

 (* sat *)
 destruct in_U as (_,(_,satU)).
 rewrite Real_sort in satU|-*; simpl.
 rewrite tm_subst_cons in satU.
 apply sat_sn in satU.
 apply Lc.sn_subst in satU.
 apply KSAT_intro with (A:=snSAT); auto.
Qed.

Lemma typ_prod : forall e T U s2,
  s2 = kind \/ s2 = prop ->
  typs e T ->
  typ (T :: e) U s2 ->
  typ e (Prod T U) s2.
Proof.
intros e T U s2 is_srt ty_T ty_U.
destruct is_srt; subst s2.
 (* s2=kind *)
 intros i j is_val.
 assert (T_not_tops : T <> kind).
  destruct ty_T as [ty_T|ty_T]; apply ty_T in is_val;
    destruct is_val; trivial.
 destruct (typs_kind_ok ty_T is_val) as (witT,in_T).
 specialize vcons_add_var0 with (1:=is_val) (2:=in_T) (3:=T_not_tops);
   intros in_U.
 apply ty_U in in_U.
 assert (Lc.sn (tm T j)).
  destruct ty_T as [ty_T|ty_T]; apply ty_T in is_val;
    destruct is_val as (_,(_,satT)); trivial.
  apply sat_sn in satT; trivial.
 split;[discriminate|split;simpl].
  (* kind_ok: *)
  apply prod_kind_ok.
  destruct in_U as (_,(mem,_)); trivial.

  (* sn *)
  destruct in_U as (_,(_,satU)).
  rewrite tm_subst_cons in satU.
  apply Lc.sn_subst in satU.
  apply sat_sn with snSAT.
  apply KSAT_intro with (A:=snSAT); auto.

 (* s2=prop *)
 apply assume_wf; intros (i0,(j0,is_val0)).
 destruct typs_is_non_empty with (1:=ty_T) (2:=is_val0) as (T_nk,_).
 apply typ_prod_prop; trivial.
 split; trivial.
 intros.
 destruct typs_is_non_empty with (1:=ty_T) (2:=H); trivial.
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

