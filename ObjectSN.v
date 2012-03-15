Require Export basic.
Require Import Models.
Require Import VarMap.
Require Lambda.
Module Lc := Lambda.

Module MakeObject (M: CC_Model).
Import M.

(** Valuations *)
Module Xeq.
  Definition t := X.
  Definition eq := eqX.
  Definition eq_equiv : Equivalence eq := eqX_equiv.
  Existing Instance eq_equiv.
End Xeq.
Module V := VarMap.Make(Xeq).

Notation val := V.map.
Notation eq_val := V.eq_map.

Definition vnil : val := V.nil props.

Existing Instance V.cons_morph.
Existing Instance V.cons_morph'.
Existing Instance V.shift_morph.
Existing Instance V.lams_morph.

(* Term valuations *)
Module I := Lambda.I.

(** Terms *)

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
(* begin show *)
left; exists (fun _ => x) (fun _ => t); trivial.
(* end show *)
 do 2 red; reflexivity.
 do 2 red; reflexivity.
Defined.

Definition kind : trm := None.

Definition prop : trm :=
  @cst props (Lc.K) (fun _ _ => eq_refl _) (fun _ _ _ => eq_refl _).

Definition Ref (n:nat) : trm.
(* begin show*)
left; exists (fun i => i n) (fun j => j n).
(*end show*)
 do 2 red; simpl; auto.
 do 2 red; simpl; auto.
 red; reflexivity.
 red; reflexivity.
Defined.

Definition App (u v:trm) : trm.
(*begin show*)
left; exists (fun i => app (int i u) (int i v))
             (fun j => Lc.App (tm j u) (tm j v)). 
(*end show*)
 do 2 red; simpl; intros.
 rewrite H; reflexivity.
(**)
 do 2 red; simpl; intros.
 rewrite H; reflexivity.
(**)
 red; simpl; intros.
 do 2 rewrite <- tm_liftable; trivial.
(**)
 red; simpl; intros.
 do 2 rewrite <- tm_substitutive; trivial.
Defined.

(* Church-style abstraction: *)
Definition CAbs t m :=
  Lc.App2 Lc.K (Lc.Abs m) t.

Definition Abs (A M:trm) : trm.
(*begin show*)
left; exists (fun i => lam (int i A) (fun x => int (V.cons x i) M))
             (fun j => CAbs (tm j A) (tm (Lc.ilift j) M)).
(*end show *)
 do 2 red; simpl; intros.
 apply lam_ext.
  rewrite H; reflexivity.
(**)
  red; intros.
  rewrite H; rewrite H1; reflexivity.
(**)
 do 2 red; intros.
 rewrite H; trivial.
(**)
 red; simpl; intros.
 rewrite Lc.ilift_binder_lift; trivial.
 do 2 rewrite <- tm_liftable; trivial.
(**)
 red; simpl; intros.
 rewrite Lc.ilift_binder; trivial.
 do 2 rewrite <- tm_substitutive; trivial.
Defined.

(* Encoding product *)
Definition CProd a b :=
  Lc.App2 Lc.K a (Lc.Abs b).

Definition Prod (A B:trm) : trm.
(*begin show*)
left; exists (fun i => prod (int i A) (fun x => int (V.cons x i) B))
             (fun j => CProd (tm j A) (tm (Lc.ilift j) B)).
(*end show*)
do 2 red; simpl; intros.
 apply prod_ext.
  rewrite H; reflexivity.
(**)
  red; intros.
  rewrite H; rewrite H1; reflexivity.
(**)
 do 2 red; intros.
 rewrite H; trivial.
(**)
 red; simpl; intros.
 do 2 rewrite <- tm_liftable; trivial.
 rewrite Lc.ilift_binder_lift; trivial.
(**)
 red; simpl; intros.
 do 2 rewrite <- tm_substitutive; trivial.
 rewrite Lc.ilift_binder; trivial.
Defined.

Lemma intProd_eq i A B :
  int i (Prod A B) = prod (int i A) (fun x => int (V.cons x i) B).
reflexivity.
Qed.

Definition lift_rec (n m:nat) (t:trm) : trm.
(*begin show*)
destruct t as [t|]; [left|exact kind].
exists (fun i => iint t (V.lams m (V.shift n) i))
       (fun j => itm t (I.lams m (I.shift n) j)).
(*end show*)
 do 2 red; intros.
 rewrite H; reflexivity.
(**)
 do 2 red; intros.
 rewrite H; reflexivity.
(**)
 red; intros.
 rewrite <- itm_lift.
 apply itm_morph; do 2 red; intros.
 unfold I.lams.
 destruct (le_gt_dec m a); trivial.
(**)
 red; intros.
 rewrite <- itm_subst.
 apply itm_morph; do 2 red; intros.
 unfold I.lams.
 destruct (le_gt_dec m a); trivial.
Defined.

Instance lift_rec_morph n k :
  Proper (eq_trm ==> eq_trm) (lift_rec n k).
 do 2 red; intros.
 destruct x; destruct y; try contradiction; try exact I.
 red; simpl.
 destruct H.
 split; red; intros.
  apply H.
  rewrite H1; reflexivity.

  apply H0.
  rewrite H1; reflexivity.
Qed.

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
(*begin show*)
destruct t as [body|]; [left|right].
exists (fun i => iint body (V.lams m (V.cons (int (V.shift m i) arg)) i))
       (fun j => itm body (I.lams m (I.cons (tm (I.shift m j) arg)) j)).
(*end show*)
 do 2 red; intros.
 rewrite H; reflexivity.
(**)
 do 2 red; intros.
 rewrite H; reflexivity.
(**)
 red; intros.
 rewrite <- itm_lift.
 apply itm_morph; do 2 red; intros.
 unfold I.lams.
 destruct (le_gt_dec m a); trivial.
 destruct (a-m); simpl; auto.
 rewrite <- tm_liftable.
 reflexivity.
(**)
 red; intros.
 rewrite <- itm_subst.
 apply itm_morph; do 2 red; intros.
 unfold I.lams.
 destruct (le_gt_dec m a); trivial.
 destruct (a-m); simpl; auto.
 rewrite <- tm_substitutive.
 reflexivity.
Defined.

Instance subst_rec_morph :
  Proper (eq_trm ==> eq ==> eq_trm ==> eq_trm) subst_rec.
do 4 red; intros.
subst y0; rename x0 into k.
destruct x1; destruct y1; try contradiction; try exact I.
red; simpl.
destruct H1.
split; red; intros.
 apply H0.
 rewrite H; rewrite H2; reflexivity.

 apply H1.
 rewrite H; rewrite H2; reflexivity.
Qed.

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

Lemma eq_trm_lift_ref_fv n k i :
  k <= i ->
  eq_trm (lift_rec n k (Ref i)) (Ref (n+i)).
split; simpl; red; intros.
 unfold V.lams.
 destruct (le_gt_dec k i).
  unfold V.shift; simpl.
  replace (n+i) with (k+(n+(i-k))); auto with *.

  omega.

 unfold I.lams.
 destruct (le_gt_dec k i).
  unfold I.shift; simpl.
  replace (n+i) with (k+(n+(i-k))); auto with *.

  omega.
Qed.

(*
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
*)

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

Lemma simpl_subst_lift_rec A M k :
  eq_trm M (subst_rec A k (lift_rec 1 k M)).
destruct M;[|exact I].
simpl; split; red; intros.
 apply iint_morph; do 2 red; intros.
 unfold V.lams, V.shift, V.cons; simpl.
 destruct (le_gt_dec k a); auto.
 destruct le_gt_dec.
 2:omega.
 case_eq (k+S(a-k)-k); intros. 
  omega.

  replace a with (k+n); auto.
  omega.

 apply itm_morph; do 2 red; intros.
 unfold I.lams, I.shift, I.cons; simpl.
 destruct (le_gt_dec k a); auto.
 destruct le_gt_dec.
 2:omega.
 case_eq (k+S(a-k)-k); intros. 
  omega.

  replace a with (k+n); auto.
  omega.
Qed.



(** "Untyped" reduction: tools for proving simulation and strong normalization *)

Definition red_term M N :=
  forall j, Lc.redp (tm j M) (tm j N).

Instance red_term_morph : Proper (eq_trm ==> eq_trm ==> iff) red_term.
apply morph_impl_iff2; auto with *.
do 4 red; intros.
red; intros.
rewrite <- H; rewrite <- H0; auto.
Qed.

Instance red_term_trans : Transitive red_term.
unfold red_term; red; intros.
specialize H with j.
specialize H0 with j.
apply t_trans with (tm j y); trivial.
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

(** "Untyped" conversion: can be used to make equality more
   intensional: assume we have plus and plus' that perform the
   addition, but with different algorithms. Then we won't
   have conv_term plus plus', while eq_typ e plus plus' will
   hold. *)
Definition conv_term M N :=
  forall j, Lc.conv (tm j M) (tm j N).

Instance conv_term_morph : Proper (eq_trm ==> eq_trm ==> iff) conv_term.
apply morph_impl_iff2; auto with *.
do 4 red; intros.
red; intros.
rewrite <- H; rewrite <- H0; auto.
Qed.

Instance conv_term_equiv : Equivalence conv_term.
split; red; red; intros.
 apply Lc.conv_refl.
 symmetry; trivial.
 transitivity (tm j y); trivial. 
Qed.

Lemma red_conv_term M N :
  red_term M N -> conv_term M N. 
unfold red_term, conv_term; intros.
induction (H j).
 apply Lc.red_conv; apply Lc.one_step_red; trivial.
 transitivity y; trivial.
Qed.

Instance conv_term_app : Proper (conv_term==>conv_term==>conv_term) App.
unfold conv_term; do 3 red; simpl; intros.
rewrite H; rewrite H0; reflexivity.
Qed.

Instance conv_term_abs : Proper (conv_term==>conv_term==>conv_term) Abs.
unfold conv_term; do 3 red; simpl; intros.
unfold CAbs, Lc.App2.
rewrite H; rewrite H0; reflexivity.
Qed.

Instance conv_term_prod : Proper (conv_term==>conv_term==>conv_term) Prod.
unfold conv_term; do 3 red; simpl; intros.
unfold CProd, Lc.App2.
rewrite H; rewrite H0; reflexivity.
Qed.

Lemma conv_term_beta T M M' N N' :
  conv_term M M' ->
  conv_term N N' ->
  conv_term (App (Abs T M) N) (subst N' M').
intros.
rewrite H; rewrite H0.
apply red_conv_term.
apply red_term_beta.
Qed.

(* This lemma shows that the strong normalization of any
   term interpretation entails the strong normalization
   of the original "term" (w.r.t. red_trans).
 *)
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


(** Iterated products *)

Fixpoint prod_list (e:list trm) (U:trm) :=
  match e with
  | List.nil => U
  | T::f => Prod T (prod_list f U)
  end.

Lemma lift_prod_list_ex n k e T :
  exists e',
  eq_trm (lift_rec n k (prod_list e T))
    (prod_list e' (lift_rec n (length e+k) T)).
revert k; induction e; intros.
 exists nil; reflexivity.

 destruct (IHe (S k)) as (e',?).
 exists (cons (lift_rec n k a) e').
 simpl prod_list.
 rewrite red_lift_prod.
 rewrite H.
 replace (length e + S k) with (S (length e +k)); auto with *.
Qed.
Lemma subst_prod_list_ex M k e T :
  exists e',
  eq_trm (subst_rec M k (prod_list e T))
    (prod_list e' (subst_rec M (length e+k) T)).
revert k; induction e; intros.
 exists nil; reflexivity.

 destruct (IHe (S k)) as (e',?).
 exists (cons (subst_rec M k a) e').
 simpl prod_list.
 rewrite red_sigma_prod.
 rewrite H.
 replace (length e + S k) with (S (length e +k)); auto with *.
Qed.


End MakeObject.
