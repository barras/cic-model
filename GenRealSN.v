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

(* Valuations *)
Module Xeq.
  Definition t := X.
  Definition eq := eqX.
  Definition eq_equiv : Equivalence eq := eqX_equiv.
  Existing Instance eq_equiv.
End Xeq.
Require Import VarMap.
Module V := VarMap.Make(Xeq).

Notation val := V.map.
Notation eq_val := V.eq_map.

Definition vnil : val := V.nil props.

Import V.
Existing Instance cons_morph.
Existing Instance cons_morph'.
Existing Instance shift_morph.
Existing Instance lams_morph.

(* Term valuations *)
Module I := Lambda.I.

(* Terms *)

Record inftrm := {
  iint : val -> X;
  iint_morph : Proper (eq_val ==> eqX) iint;
  itm : Lc.intt -> Lc.term;
  itm_morph : Proper (Lc.eq_intt ==> eq) itm;
  itm_lift : Lc.liftable itm;
  itm_subst : Lc.substitutive itm
}.
Existing Instance iint_morph.
Existing Instance itm_morph.

Definition trm := option inftrm.

Definition eq_trm (x y:trm) :=
  match x, y with
  | Some f, Some g =>
     (eq_val ==> eqX)%signature (iint f) (iint g) /\
     (Lc.eq_intt ==> eq)%signature (itm f) (itm g)
  | None, None => True
  | _, _ => False
  end.

Instance eq_trm_refl : Reflexive eq_trm.
red; intros.
destruct x as [(f,mf,g,mg,sg)|]; simpl; auto.
Qed.

Instance eq_trm_sym : Symmetric eq_trm.
red; intros.
destruct x as [(fx,mfx,gx,mgx,sgx)|];
destruct y as [(fy,mfy,gy,mgy,sgy)|]; simpl in *; auto.
destruct H; split; symmetry; trivial.
Qed.

Instance eq_trm_trans : Transitive eq_trm.
red; intros.
destruct x as [(fx,mfx,gx,mgx,sgx)|];
destruct y as [(fy,mfy,gy,mgy,sgy)|];
destruct z as [(fz,mfz,gz,mgz,sgz)|];
 try contradiction; simpl in *; auto.
destruct H; destruct H0; split.
 transitivity fy; trivial.
 transitivity gy; trivial.
Qed.

Instance eq_trm_equiv : Equivalence eq_trm.
constructor; auto with *.
Qed.

Lemma eq_kind : forall (M:trm), M = None <-> eq_trm M None.
destruct M; simpl; split; contradiction||discriminate||trivial.
Qed.

Definition dummy_trm : Lc.term.
exact Lc.K.
Defined.
(* The only fact needed is that dummy_trm is a closed term *)

Definition tm (j:Lc.intt) (M:trm) :=
  match M with
  | Some f => itm f j
  | None => dummy_trm
  end.

Definition dummy_int : X.
Proof props.

Definition int (i:val) (M:trm) :=
  match M with
  | Some f => iint f i
  | None => dummy_int
  end.

Lemma eq_trm_intro : forall T T',
  (forall i, int i T == int i T') ->
  (forall j, tm j T = tm j T') ->
  match T, T' with Some _,Some _=>True|None,None=>True|_,_=>False end ->
  eq_trm T T'.
destruct T as [T|]; destruct T' as [T'|]; simpl; intros; trivial.
split; red; intros.
 rewrite H2; auto.
 rewrite H2; auto.
Qed.

Instance tm_morph : Proper (Lc.eq_intt ==> eq_trm ==> @eq Lc.term) tm.
unfold tm; do 3 red; intros.
destruct x0; destruct y0; simpl in *; (contradiction||reflexivity||auto).
destruct H0; simpl in *.
apply H1; trivial.
Qed.

Lemma tm_substitutive : forall u t j k,
  tm (fun n => Lc.subst_rec u (j n) k) t =
  Lc.subst_rec u (tm j t) k.
destruct t; simpl; intros; trivial.
apply itm_subst.
Qed.

Lemma tm_liftable : forall j t k,
  tm (fun n => Lc.lift_rec 1 (j n) k) t = Lc.lift_rec 1 (tm j t) k.
destruct t; simpl; intros; trivial.
apply itm_lift.
Qed.

Lemma tm_subst_cons : forall x j t,
  tm (I.cons x j) t = Lc.subst x (tm (Lc.ilift j) t).
unfold Lc.subst; intros.
rewrite <- tm_substitutive.
apply tm_morph; [red; intros|reflexivity].
red.
destruct a; simpl.
 rewrite Lc.lift0; trivial.
 rewrite Lc.simpl_subst; trivial; rewrite Lc.lift0; trivial.
Qed.

Instance int_morph : Proper (eq_val ==> eq_trm ==> eqX) int.
unfold int; do 3 red; intros.
destruct x0; destruct y0; simpl in *; (contradiction||reflexivity||auto).
destruct H0; simpl in *.
apply H0; trivial.
Qed.

Definition cst (x:X) (t:Lc.term)
  (H0 : Lc.liftable (fun _ => t)) (H1 : Lc.substitutive (fun _ => t)) : trm.
left; exists (fun _ => x) (fun _ => t); trivial.
 do 2 red; reflexivity.
 do 2 red; reflexivity.
Defined.

Definition kind : trm := None.

Definition prop : trm := @cst props (Lc.K) (fun _ _ => eq_refl _) (fun _ _ _ => eq_refl _).

Definition Ref (n:nat) : trm.
left; exists (fun i => i n) (fun j => j n).
 do 2 red; simpl; auto.
 do 2 red; simpl; auto.
 red; reflexivity.
 red; reflexivity.
Defined.

Definition App (u v:trm) : trm.
left; exists (fun i => app (int i u) (int i v))
             (fun j => Lc.App (tm j u) (tm j v)). 
 do 2 red; simpl; intros.
 rewrite H; reflexivity.

 do 2 red; simpl; intros.
 rewrite H; reflexivity.

 red; simpl; intros.
 do 2 rewrite <- tm_liftable; trivial.

 red; simpl; intros.
 do 2 rewrite <- tm_substitutive; trivial.
Defined.

(* Church-style abstraction: *)
Definition CAbs t m :=
  Lc.App2 Lc.K (Lc.Abs m) t.

Definition Abs (A M:trm) : trm.
left; exists (fun i => lam (int i A) (fun x => int (V.cons x i) M))
             (fun j => CAbs (tm j A) (tm (Lc.ilift j) M)).
 do 2 red; simpl; intros.
 apply lam_ext.
  rewrite H; reflexivity.

  red; intros.
  rewrite H; rewrite H1; reflexivity.

 do 2 red; intros.
 rewrite H; trivial.

 red; simpl; intros.
 rewrite Lc.ilift_binder_lift; trivial.
 do 2 rewrite <- tm_liftable; trivial.

 red; simpl; intros.
 rewrite Lc.ilift_binder; trivial.
 do 2 rewrite <- tm_substitutive; trivial.
Defined.

(* Encoding product *)
Definition CProd a b :=
  Lc.App2 Lc.K a (Lc.Abs b).

Definition Prod (A B:trm) : trm.
left;
  exists (fun i => prod (int i A) (fun x => int (V.cons x i) B))
         (fun j => CProd (tm j A) (tm (Lc.ilift j) B)).
do 2 red; simpl; intros.
 apply prod_ext.
  rewrite H; reflexivity.

  red; intros.
  rewrite H; rewrite H1; reflexivity.

 do 2 red; intros.
 rewrite H; trivial.

 red; simpl; intros.
 do 2 rewrite <- tm_liftable; trivial.
 rewrite Lc.ilift_binder_lift; trivial.

 red; simpl; intros.
 do 2 rewrite <- tm_substitutive; trivial.
 rewrite Lc.ilift_binder; trivial.
Defined.

Lemma intProd_eq i A B :
  int i (Prod A B) = prod (int i A) (fun x => int (V.cons x i) B).
reflexivity.
Qed.

Definition lift_rec (n m:nat) (t:trm) : trm.
destruct t as [t|]; [left|exact kind].
exists (fun i => iint t (V.lams m (V.shift n) i))
       (fun j => itm t (I.lams m (I.shift n) j)).
 do 2 red; intros.
 rewrite H; reflexivity.

 do 2 red; intros.
 rewrite H; reflexivity.

 red; intros.
 rewrite <- itm_lift.
 apply itm_morph; do 2 red; intros.
 unfold I.lams.
 destruct (le_gt_dec m a); trivial.

 red; intros.
 rewrite <- itm_subst.
 apply itm_morph; do 2 red; intros.
 unfold I.lams.
 destruct (le_gt_dec m a); trivial.
Defined.

Lemma int_lift_rec_eq : forall n k T i,
  int i (lift_rec n k T) == int (V.lams k (V.shift n) i) T.
intros; destruct T as [T|]; simpl; reflexivity.
Qed.

Definition lift n := lift_rec n 0.

Instance lift_morph : forall k, Proper (eq_trm ==> eq_trm) (lift k).
do 2 red; simpl; intros.
destruct x as [x|]; destruct y as [y|];
  simpl in *; (contradiction||trivial).
destruct H; split.
 red; intros.
 apply H; rewrite H1; reflexivity.

 red; intros.
 apply H0; rewrite H1; reflexivity.
Qed.

Lemma int_lift_eq : forall i T,
  int i (lift 1 T) == int (V.shift 1 i) T.
unfold int; intros;
  destruct T as [T|]; simpl; auto. (* BUG: intros needed before destruct *)
2:reflexivity.
rewrite V.lams0.
reflexivity.
Qed.

Lemma int_cons_lift_eq : forall i T x,
  int (V.cons x i) (lift 1 T) == int i T.
intros.
rewrite int_lift_eq.
rewrite V.shift_cons; reflexivity.
Qed.

Lemma tm_lift_rec_eq : forall n k T j,
  tm j (lift_rec n k T) = tm (I.lams k (I.shift n) j) T.
intros; destruct T; simpl; reflexivity.
Qed.

Lemma split_lift : forall n T,
  eq_trm (lift (S n) T) (lift 1 (lift n T)).
destruct T as [T|]; simpl; auto.
split; red; intros.
 do 2 rewrite V.lams0.
 change (V.shift n (fun k => V.lams 0 (V.shift 1) y k)) with
   (V.shift n (V.lams 0 (V.shift 1) y)).
 rewrite V.lams0.
 rewrite V.shift_split.
 change (eq_val (fun k => x k) (fun k => y k)) in H.
 rewrite H; reflexivity.

 do 2 rewrite I.lams0.
 change (I.shift n (fun k => I.lams 0 (I.shift 1) y k)) with
   (I.shift n (I.lams 0 (I.shift 1) y)).
 rewrite I.lams0.
 rewrite I.shift_split.
 change (Lc.eq_intt (fun k => x k) (fun k => y k)) in H.
 rewrite H; reflexivity.
Qed.

Definition subst_rec (arg:trm) (m:nat) (t:trm) : trm.
destruct t as [body|]; [left|right].
exists (fun i => iint body (V.lams m (V.cons (int (V.shift m i) arg)) i))
       (fun j => itm body (I.lams m (I.cons (tm (I.shift m j) arg)) j)).
 do 2 red; intros.
 rewrite H; reflexivity.

 do 2 red; intros.
 rewrite H; reflexivity.

 red; intros.
 rewrite <- itm_lift.
 apply itm_morph; do 2 red; intros.
 unfold I.lams.
 destruct (le_gt_dec m a); trivial.
 destruct (a-m); simpl; auto.
 rewrite <- tm_liftable.
 reflexivity.

 red; intros.
 rewrite <- itm_subst.
 apply itm_morph; do 2 red; intros.
 unfold I.lams.
 destruct (le_gt_dec m a); trivial.
 destruct (a-m); simpl; auto.
 rewrite <- tm_substitutive.
 reflexivity.
Defined.

Lemma int_subst_rec_eq : forall arg k T i,
  int i (subst_rec arg k T) == int (V.lams k (V.cons (int (V.shift k i) arg)) i) T.
intros; destruct T as [T|]; simpl; reflexivity.
Qed.

Definition subst arg := subst_rec arg 0.

Lemma int_subst_eq : forall N M i,
 int (V.cons (int i N) i) M == int i (subst N M).
destruct M as [M|]; simpl; intros.
2:reflexivity.
rewrite V.lams0.
rewrite V.shift0.
reflexivity.
Qed.

Lemma tm_subst_rec_eq : forall arg k T j,
  tm j (subst_rec arg k T) = tm (I.lams k (I.cons (tm (I.shift k j) arg)) j) T.
intros; destruct T; simpl; reflexivity.
Qed.

Lemma tm_subst_eq : forall u v j,
  tm j (subst u v) = Lc.subst (tm j u) (tm (Lc.ilift j) v).
intros.
unfold Lc.subst; rewrite <- tm_substitutive.
destruct v as [v|]; simpl; trivial.
rewrite I.lams0.
rewrite I.shift0.
apply itm_morph.
apply I.cons_ext; simpl.
 rewrite Lc.lift0; trivial.

 do 2 red; unfold I.shift; simpl; intros.
 rewrite Lc.simpl_subst; trivial; rewrite Lc.lift0; trivial.
Qed.

Instance App_morph : Proper (eq_trm ==> eq_trm ==> eq_trm) App.
unfold App; do 3 red; simpl; split; intros.
 red; intros.
 rewrite H; rewrite H0; rewrite H1; reflexivity.

 red; intros.
 rewrite H; rewrite H0; rewrite H1; reflexivity.
Qed.

Instance Abs_morph : Proper (eq_trm ==> eq_trm ==> eq_trm) Abs.
unfold Abs; do 4 red; simpl; split; red; intros.
 apply lam_ext.
  apply int_morph; auto.

  red; intros.
  rewrite H0; rewrite H1; rewrite H3; reflexivity.

 rewrite H0; rewrite H1; rewrite H; reflexivity.
Qed.


Instance Prod_morph : Proper (eq_trm ==> eq_trm ==> eq_trm) Prod.
unfold Prod; do 4 red; simpl; split; red; intros.
 apply prod_ext.
  rewrite H; rewrite H1; reflexivity.

  red; intros.
  rewrite H0; rewrite H1; rewrite H3; reflexivity.

 rewrite H0; rewrite H1; rewrite H; reflexivity.
Qed.


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

Fixpoint prod_list (e:list trm) (U:trm) :=
  match e with
  | List.nil => U
  | T::f => Prod T (prod_list f U)
  end.

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

Lemma discr_ref_prod : forall n A B,
  ~ eq_trm (Ref n) (Prod A B).
red; intros.
simpl in H.
destruct H as (_,H).
red in H.
specialize H with Lc.Ref Lc.Ref.
discriminate H.
reflexivity.
Qed.

Lemma lift1var : forall n, eq_trm (lift 1 (Ref n)) (Ref (S n)).
simpl; split; red; intros.
 revert n.
 change (eq_val (V.lams 0 (V.shift 1) x) (V.shift 1 y)).
 rewrite V.lams0; rewrite <- H.
 reflexivity.

 revert n.
 change (Lc.eq_intt (I.lams 0 (I.shift 1) x) (I.shift 1 y)).
 rewrite I.lams0; rewrite <- H.
 reflexivity.
Qed.

Lemma non_empty_var_lift : forall n,
  non_empty (Ref n) -> non_empty (Ref (S n)).
intros n (e,(U,eq_U,(x,(t,in_U)))).
destruct e; simpl prod_list in eq_U.
 exists List.nil; exists (lift 1 U).
  simpl prod_list.
  rewrite <- lift1var.
  apply lift_morph; trivial.

  exists x; exists t; intros.
  rewrite int_lift_eq; auto.

 elim (discr_ref_prod eq_U).
Qed.


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
  apply non_empty_var_lift; trivial.
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

Lemma typ_sn : forall e M T,
  wf e -> typ e M T -> exists j, Lc.sn (tm j M).
intros e M T (i,(j,is_val)) ty.
exists j.
apply ty in is_val.
apply in_int_sn in is_val; trivial.
Qed.

(* Context formation *)

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

Lemma trans : forall e M M' M'', eq_typ e M M' -> eq_typ e M' M'' -> eq_typ e M M''.
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
 assert (prod (int i T) (fun x => int (cons x i) U) \in props).
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

(*
Lemma weakening : forall e M T A,
  typ e M T ->
  typ (A::e) (lift 1 M) (lift 1 T).
unfold typ, in_int; intros.
destruct T as [(T,Tm)|]; simpl in *; trivial.
red; simpl.
unfold lift.
rewrite int_lift_rec_eq.
apply H.
unfold val_ok in *.
intros.
specialize (H0 (S n) _ H1).
destruct T0 as [(T0,T0m)|]; simpl in *; trivial.
unfold V.lams at 1, V.shift at 1 2; simpl.
replace (n-0) with n; auto with arith.
Qed.
*)


(* Subtyping *)

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

(* "Untyped" reduction: tools for proving simulation and strong normalization *)

Require Import Relations.

Definition red_term M N :=
  forall j, Lc.redp (tm j M) (tm j N).

Instance red_term_morph : Proper (eq_trm ==> eq_trm ==> iff) red_term.
apply morph_impl_iff2; auto with *.
do 4 red; intros.
red; intros.
rewrite <- H; rewrite <- H0; auto.
Qed.

Lemma red_term_trans M1 M2 M3 :
  red_term M1 M2 -> red_term M2 M3 -> red_term M1 M3.
unfold red_term; intros.
specialize H with j.
specialize H0 with j.
apply t_trans with (tm j M2); trivial.
Qed.

Lemma red_term_app_l M M' N :
  red_term M M' ->
  red_term (App M N) (App M' N).
unfold red_term; intros.
specialize H with j.
apply Lc.redp_app_l; trivial.
Qed.

Lemma red_term_app_r M N N' :
  red_term N N' ->
  red_term (App M N) (App M N').
unfold red_term; intros.
specialize H with j.
apply Lc.redp_app_r; trivial.
Qed.

Lemma red_term_abs_l M M' N :
  red_term M M' ->
  red_term (Abs M N) (Abs M' N).
unfold red_term; intros.
specialize H with j.
simpl.
apply Lc.redp_app_r; trivial.
Qed.

Lemma red_term_abs_r M N N' :
  red_term N N' ->
  red_term (Abs M N) (Abs M N').
unfold red_term; intros.
specialize H with (Lc.ilift j).
simpl.
apply Lc.redp_app_l; trivial.
apply Lc.redp_app_r; trivial.
apply Lc.redp_abs; trivial.
Qed.

Lemma red_term_prod_l M M' N :
  red_term M M' ->
  red_term (Prod M N) (Prod M' N).
unfold red_term; intros.
specialize H with j.
simpl.
apply Lc.redp_app_l; trivial.
apply Lc.redp_app_r; trivial.
Qed.

Lemma red_term_prod_r M N N' :
  red_term N N' ->
  red_term (Prod M N) (Prod M N').
unfold red_term; intros.
specialize H with (Lc.ilift j).
simpl.
apply Lc.redp_app_r; trivial.
apply Lc.redp_abs; trivial.
Qed.

Lemma red_term_beta T M N :
  red_term (App (Abs T M) N) (subst N M).
red; simpl; intros.
eapply t_trans.
 eapply Lc.redp_app_l.
 eapply Lc.redp_K.

 apply t_step.
 apply Lc.red1_beta.
 unfold Lc.subst; rewrite <- tm_substitutive.
 destruct M; simpl; trivial.
 rewrite I.lams0.
 unfold I.shift; simpl.
 apply itm_morph.
 do 2 red; intros.
 destruct a; simpl.
  rewrite Lc.lift0; trivial.

  rewrite Lc.simpl_subst; auto.
  rewrite Lc.lift0; trivial.
Qed.

Lemma red_lift_app n A B k :
  eq_trm (lift_rec n k (App A B)) (App (lift_rec n k A) (lift_rec n k B)).
red; simpl; intros.
split.
 red; intros.
 apply app_ext.
  rewrite int_lift_rec_eq.
  rewrite H; reflexivity.

  rewrite int_lift_rec_eq.
  rewrite H; reflexivity.

 red; intros.
 do 2 rewrite tm_lift_rec_eq.
 rewrite H; trivial.
Qed.

Lemma red_lift_abs n A B k :
  eq_trm (lift_rec n k (Abs A B)) (Abs (lift_rec n k A) (lift_rec n (S k) B)).
red; simpl; intros.
split.
 red; intros.
 apply lam_ext.
  rewrite int_lift_rec_eq.
  rewrite H; reflexivity.

  red; intros.
  rewrite int_lift_rec_eq.
  rewrite <- V.cons_lams.
   rewrite H1.
   rewrite H.
   reflexivity.

   do 2 red; intros.
   rewrite H2; reflexivity.

 red; intros.
 apply f_equal2.
  rewrite tm_lift_rec_eq.
  rewrite H; auto.

  rewrite tm_lift_rec_eq.
  apply tm_morph; auto with *.
  rewrite H.
  apply Lc.cross_binder_shift.
Qed.

Lemma red_lift_prod n A B k :
  eq_trm (lift_rec n k (Prod A B)) (Prod (lift_rec n k A) (lift_rec n (S k) B)).
red; simpl; intros.
split.
 red; intros.
 apply prod_ext.
  rewrite int_lift_rec_eq.
  rewrite H; reflexivity.

  red; intros.
  rewrite int_lift_rec_eq.
  rewrite <- V.cons_lams.
   rewrite H1.
   rewrite H.
   reflexivity.

   do 2 red; intros.
   rewrite H2; reflexivity.

 red; intros.
 apply f_equal2.
  rewrite tm_lift_rec_eq.
  rewrite H; auto.

  rewrite tm_lift_rec_eq.
  apply tm_morph; auto with *.
  rewrite H.
  apply Lc.cross_binder_shift.
Qed.

Lemma red_sigma_app N A B k :
  eq_trm (subst_rec N k (App A B)) (App (subst_rec N k A) (subst_rec N k B)).
red; simpl; intros.
split.
 red; intros.
 apply app_ext.
  rewrite int_subst_rec_eq.
  rewrite H; reflexivity.

  rewrite int_subst_rec_eq.
  rewrite H; reflexivity.

 red; intros.
 do 2 rewrite tm_subst_rec_eq.
 rewrite H; trivial.
Qed.

Lemma red_sigma_abs N A B k :
  eq_trm (subst_rec N k (Abs A B)) (Abs (subst_rec N k A) (subst_rec N (S k) B)).
red; simpl; intros.
split.
 red; intros.
 apply lam_ext.
  rewrite int_subst_rec_eq.
  rewrite H; reflexivity.

  red; intros.
  rewrite int_subst_rec_eq.
  rewrite <- V.cons_lams.
   rewrite H1.
   rewrite H.
   reflexivity.

   do 2 red; intros.
   rewrite H2; reflexivity.

 red; intros.
 apply f_equal2.
  rewrite tm_subst_rec_eq.
  rewrite H; auto.

  rewrite tm_subst_rec_eq.
  apply tm_morph; auto with *.
  rewrite H.
  apply Lc.cross_binder_cons.
  unfold I.shift, Lc.ilift; simpl.
  unfold Lc.lift; rewrite <- tm_liftable; trivial.
Qed.

Lemma red_sigma_prod N A B k :
  eq_trm (subst_rec N k (Prod A B)) (Prod (subst_rec N k A) (subst_rec N (S k) B)).
red; simpl; intros.
split.
 red; intros.
 apply prod_ext.
  rewrite int_subst_rec_eq.
  rewrite H; reflexivity.

  red; intros.
  rewrite int_subst_rec_eq.
  rewrite <- V.cons_lams.
   rewrite H1.
   rewrite H.
   reflexivity.

   do 2 red; intros.
   rewrite H2; reflexivity.

 red; intros.
 apply f_equal2.
  rewrite tm_subst_rec_eq.
  rewrite H; auto.

  rewrite tm_subst_rec_eq.
  apply tm_morph; auto with *.
  rewrite H.
  apply Lc.cross_binder_cons.
  unfold I.shift, Lc.ilift; simpl.
  unfold Lc.lift; rewrite <- tm_liftable; trivial.
Qed.

Lemma red_sigma_var_eq N k :
  N <> kind ->
  eq_trm (subst_rec N k (Ref k)) (lift k N).
unfold subst_rec; simpl.
destruct N; simpl.
2:destruct 1; trivial.
intros _.
split; red; intros.
 unfold V.lams, V.shift; simpl.
 destruct (le_gt_dec k k).
 2:omega.
 replace (k-k) with 0; auto with *.
 simpl V.cons.
 apply iint_morph.
 do 2 red; intros.
 replace (a-0) with a; auto with *.

 unfold I.lams; simpl.
 destruct (le_gt_dec k k).
 2:omega.
 replace (k-k) with 0; auto with *.
 simpl I.cons.
 apply itm_morph.
 do 2 red; intros.
 unfold I.shift; simpl.
 replace (a-0) with a; auto with *.
Qed.

Lemma red_sigma_var_lt N k n :
  n < k ->
  eq_trm (subst_rec N k (Ref n)) (Ref n).
unfold subst_rec; simpl; intros.
split; red; intros.
 unfold V.lams, V.shift; simpl.
 destruct (le_gt_dec k n); auto.
 omega.

 unfold I.lams, I.shift; simpl.
 destruct (le_gt_dec k n); auto.
 omega.
Qed.

Lemma red_sigma_var_gt N k n :
  k <= n ->
  eq_trm (subst_rec N k (Ref (S n))) (Ref n).
unfold subst_rec; simpl; intros.
split; red; intros.
 unfold V.lams; simpl.
 destruct (le_gt_dec k (S n)); simpl.
  unfold V.cons, V.shift; simpl.
  destruct k; simpl; auto.
  replace (n-k) with (S (n-S k)).
   replace (S (k+(n- S k))) with n; auto.
   omega.
  omega.
 omega.

 unfold I.lams, I.shift, I.cons; simpl.
 destruct (le_gt_dec k (S n)); simpl.
  destruct k; simpl; auto.
  replace (n-k) with (S (n-S k)).
   replace (S (k+(n- S k))) with n; auto.
   omega.
  omega.
 omega.
Qed.

Require Import Transitive_Closure.

Lemma simul M :
  Lc.sn M ->
  forall j M', M = tm j M' ->
  Acc (transp _ red_term) M'.
intros snM.
elim (Acc_clos_trans _ _ _ snM); clear snM; intros.
constructor; intros.
red in H2.
assert (redM' := H2 j).
assert (clos_trans _ (transp _ Lc.red1) (tm j y) x).
 rewrite H1.
 clear H1 H2.
 elim redM'; intros.
  apply t_step; trivial.

  apply t_trans with y0; trivial.
apply H0 with (tm j y) j; trivial.
Qed.

Lemma model_strong_normalization e M T :
  wf e ->
  typ e M T ->
  Acc (transp _ red_term) M.
intros.
destruct typ_sn with (1:=H) (2:=H0) as (j,?).
apply simul with (1:=H1) (2:=eq_refl).
Qed.

End MakeModel.
