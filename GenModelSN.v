Set Implicit Arguments.
Require Import List Compare_dec.
Require Import Sat.
Require Import Models.

Module Lc := Lambda.

(* Equiping the model with saturated sets *)
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

(* Now the abstract strong normalization proof. *)

Module MakeModel(M : CC_Model) (SN : SN_addon M).
Import M.
Import SN.

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

(**)
Module LCeq.
  Definition t := Lc.term.
  Definition eq := @Logic.eq Lc.term.
  Definition eq_equiv : Equivalence eq := eq_equivalence.
  Existing Instance eq_equiv.
End LCeq.
Module I := VarMap.Make(LCeq).

Notation intt := I.map.
Notation eq_intt := I.eq_map.

Import I.
Existing Instance cons_morph.
Existing Instance cons_morph'.
Existing Instance shift_morph.
Existing Instance lams_morph.

Definition ilift (j:intt) : intt :=
  fun k => match k with
  | 0 => Lc.Ref 0
  | S n => Lc.lift 1 (j n)
  end.

Instance ilift_morph : Proper (eq_intt ==> eq_intt) ilift.
do 4 red; intros.
unfold ilift.
destruct a; simpl; auto.
rewrite H; trivial.
Qed.

Lemma ilift_lams : forall k f j,
  (forall j j', (forall a, Lc.lift 1 (j a) = j' a) ->
   forall a, Lc.lift 1 (f j a) = f j' a) ->
  eq_intt (ilift (I.lams k f j)) (I.lams (S k) f (ilift j)).
intros.
do 2 red; intros.
destruct a; simpl.
 reflexivity.

 unfold I.lams; simpl.
 destruct (le_gt_dec k a); simpl; trivial.
 apply H.
 unfold I.shift, ilift; simpl; intros; trivial.
Qed.

Lemma ilift_binder : forall u j k,
  eq_intt
    (ilift (fun n => Lc.subst_rec u (j n) k))
    (fun n => Lc.subst_rec u (ilift j n) (S k)).
red; red; intros.
destruct a; simpl; trivial.
rewrite Lc.commut_lift_subst; trivial.
Qed.

Lemma ilift_binder_lift : forall j k,
  eq_intt
    (ilift (fun n => Lc.lift_rec 1 (j n) k))
    (fun n => Lc.lift_rec 1 (ilift j n) (S k)).
red; red; intros.
destruct a; simpl; trivial.
rewrite Lc.permute_lift; trivial.
Qed.

(* Terms *)

Definition substitutive (t:intt->Lc.term) :=
  forall u j k,
  t (fun n => Lc.subst_rec u (j n) k) = Lc.subst_rec u (t j) k.
Definition liftable (t:intt->Lc.term) :=
  forall j k,
  t (fun n => Lc.lift_rec 1 (j n) k) = Lc.lift_rec 1 (t j) k.

Record inftrm := {
  iint : val -> X;
  iint_morph : Proper (eq_val ==> eqX) iint;
  itm : intt -> Lc.term;
  itm_morph : Proper (eq_intt ==> @eq Lc.term) itm;
  itm_lift : liftable itm;
  itm_subst : substitutive itm
}.
Existing Instance iint_morph.
Existing Instance itm_morph.

Definition trm := option inftrm.

Definition eq_trm (x y:trm) :=
  match x, y with
  | Some f, Some g =>
     (eq_val ==> eqX)%signature (iint f) (iint g) /\
     (eq_intt ==> @eq Lc.term)%signature (itm f) (itm g)
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

Lemma eq_kind : forall (M:trm), M = None <-> eq_trm M None.
destruct M; simpl; split; contradiction||discriminate||trivial.
Qed.

Definition tm (j:intt) (M:trm) :=
  match M with
  | Some f => itm f j
  | None => Lc.K (* kind is interpreted by any SN term *)
  end.

Definition int (i:val) (M:trm) :=
  match M with
  | Some f => iint f i
  | None => props
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

Instance tm_morph : Proper (eq_intt ==> eq_trm ==> @eq Lc.term) tm.
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
  tm (I.cons x j) t = Lc.subst x (tm (ilift j) t).
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

Definition kind : trm := None.

Definition prop : trm.
left; exists (fun _ => props) (fun _=> Lc.K).
 do 2 red; reflexivity.
 do 2 red; reflexivity.
 red; reflexivity.
 red; reflexivity.
Defined.

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

Definition Abs (A M:trm) : trm.
left; exists (fun i => lam (int i A) (fun x => int (V.cons x i) M))
             (fun j => Lc.App2 Lc.K (Lc.Abs (tm (ilift j) M)) (tm j A)).
 do 2 red; simpl; intros.
 apply lam_ext.
  rewrite H; reflexivity.

  red; intros.
  rewrite H; rewrite H1; reflexivity.

 do 2 red; intros.
 rewrite H; trivial.

 red; simpl; intros.
 rewrite ilift_binder_lift; trivial.
 do 2 rewrite <- tm_liftable; trivial.

 red; simpl; intros.
 rewrite ilift_binder; trivial.
 do 2 rewrite <- tm_substitutive; trivial.
Defined.

Definition Prod (A B:trm) : trm.
left;
  exists (fun i => prod (int i A) (fun x => int (V.cons x i) B))
         (fun j => Lc.App2 Lc.K (tm j A) (Lc.Abs (tm (ilift j) B))).
do 2 red; simpl; intros.
 apply prod_ext.
  rewrite H; reflexivity.

  red; intros.
  rewrite H; rewrite H1; reflexivity.

 do 2 red; intros.
 rewrite H; trivial.

 red; simpl; intros.
 do 2 rewrite <- tm_liftable; trivial.
 rewrite ilift_binder_lift; trivial.

 red; simpl; intros.
 do 2 rewrite <- tm_substitutive; trivial.
 rewrite ilift_binder; trivial.
Defined.

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
 change (shift n (fun k => lams 0 (shift 1) y k)) with
   (shift n (lams 0 (shift 1) y)).
 rewrite I.lams0.
 rewrite I.shift_split.
 change (eq_intt (fun k => x k) (fun k => y k)) in H.
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
  tm j (subst u v) = Lc.subst (tm j u) (tm (ilift j) v).
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


(* Dealing with top sorts *)

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
 change (eq_intt (I.lams 0 (I.shift 1) x) (I.shift 1 y)).
 rewrite I.lams0; rewrite <- H.
 reflexivity.
Qed.

Lemma non_empty_var_lift : forall n,
  non_empty (Ref n) -> non_empty (Ref (S n)).
intros n (e,(U,eq_U,(x,in_U))).
destruct e; simpl prod_list in eq_U.
 exists List.nil; exists (lift 1 U).
  simpl prod_list.
  rewrite <- lift1var.
  apply lift_morph; trivial.

  exists x; intros.
  setoid_replace i with (V.cons (i 0) (V.shift 1 i)).
   rewrite int_lift_eq; trivial.

   red; intros.
   destruct a; reflexivity.

 elim (discr_ref_prod eq_U).
Qed.


Definition in_int (i:val) (j:intt) (M T:trm) :=
  M <> None /\
  match T with
  | None => non_empty M
  | _ => int i M \in int i T
  end /\
  inSAT (tm j M) (Red (int i T)).

Instance in_int_morph : Proper
  (eq_val ==> pointwise_relation nat (@eq Lc.term) ==> eq_trm ==> eq_trm ==> iff)
  in_int.
apply morph_impl_iff4; auto with *.
unfold in_int; do 5 red; intros.
repeat rewrite eq_kind.
destruct x2; destruct y2; try contradiction.
 rewrite H; rewrite H0; rewrite H1; rewrite H2.
 reflexivity.

 rewrite H; rewrite H0; rewrite H1.
 reflexivity.
Qed.

Lemma in_int_not_kind : forall i j M T,
  in_int i j M T ->
  T <> kind ->
  int i M \in int i T /\
  inSAT (tm j M) (Red (int i T)).
destruct 1 as (_,(mem,sat)); intros.
destruct T; auto.
elim H; trivial.
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
split; try discriminate.
split.
 revert H1; pattern T at 1 2.
 case T; simpl; intros.
  rewrite int_cons_lift_eq; trivial.

  elim H1; trivial.

 rewrite int_cons_lift_eq; trivial.
Qed.

Lemma in_int_varS : forall i j x t n T,
  in_int i j (Ref n) (lift (S n) T) ->
  in_int (V.cons x i) (I.cons t j) (Ref (S n)) (lift (S (S n)) T).
intros.
destruct H as (_,(mem,subs)); simpl in *.
red; simpl.
split; try discriminate.
split.
 revert mem; pattern T at 1 3.
 case T; [intros T0|]; simpl; intros; trivial.
  rewrite split_lift.
  rewrite int_cons_lift_eq; trivial.

  apply non_empty_var_lift; trivial.

 rewrite split_lift.
 rewrite int_cons_lift_eq; trivial.
Qed.

Lemma in_int_sn : forall i j M T,
  in_int i j M T -> Lc.sn (tm j M).
destruct 1 as (_,(_,sat)).
apply sat_sn in sat; trivial.
Qed.

(* Environments *)
Definition env := list trm.

Definition val_ok (e:env) (i:val) (j:intt) :=
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

(* Judgements *)
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


(* Strong normalization *)

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

(* Equality rules *)

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


Lemma typ_prop : forall e, typ e prop kind.
red; simpl; intros.
split; try discriminate.
split; simpl; auto.
 apply prop_non_empty.

 rewrite Red_sort.
 apply snSAT_intro.
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
    destruct is_val as (_,(_,satT)); simpl in satT;
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
split;[discriminate|split;simpl].
 destruct is_srt; subst s2; simpl in *.
  apply prod_non_empty.
  destruct in_U as (_,(mem,_)); trivial.

  apply impredicative_prod; intros.   
   red; intros.
   rewrite H1; reflexivity.

   clear in_U.
   specialize vcons_add_var0 with (1:=is_val) (2:=H0) (3:=T_not_tops);
     intros in_U.
   apply ty_U in in_U.
   apply in_int_not_kind in in_U.
    destruct in_U; trivial.
    discriminate.

 destruct in_U as (_,(_,satU)).
 rewrite tm_subst_cons in satU.
 apply KSAT_intro.
  apply Lc.sn_abs.
  apply sat_sn in satU.
  apply Lc.sn_subst in satU; trivial.

  assert (Lc.sn (tm j T)).
   destruct ty_T as [ty_T|ty_T]; apply ty_T in is_val;
     destruct is_val as (_,(_,satT));
     apply sat_sn in satT; trivial.
  destruct is_srt; subst s2; simpl; rewrite Red_sort;
    apply snSAT_intro; trivial.
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

