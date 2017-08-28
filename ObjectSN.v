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


(** Pseudo-terms *)
Module T.

Record infterm := {
  iint : val -> X;
  iint_morph : Proper (eq_val ==> eqX) iint;
  itm : Lc.intt -> Lc.term;
  itm_morph : Proper (Lc.eq_intt ==> eq) itm;
  itm_lift : Lc.liftable itm;
  itm_subst : Lc.substitutive itm
}.
Existing Instance iint_morph.
Existing Instance itm_morph.

Definition term := option infterm.

Definition eq_term (x y:term) :=
  match x, y with
  | Some f, Some g =>
     (eq_val ==> eqX)%signature (iint f) (iint g) /\
     (Lc.eq_intt ==> eq)%signature (itm f) (itm g)
  | None, None => True
  | _, _ => False
  end.

Instance eq_term_refl : Reflexive eq_term.
red; intros.
destruct x as [(f,mf,g,mg,lg,sg)|]; simpl; auto.
Qed.

Instance eq_term_sym : Symmetric eq_term.
red; intros.
destruct x as [(fx,mfx,gx,mgx,lgx,sgx)|];
destruct y as [(fy,mfy,gy,mgy,lgy,sgy)|]; simpl in *; auto.
destruct H; split; symmetry; trivial.
Qed.

Instance eq_term_trans : Transitive eq_term.
red; intros.
destruct x as [(fx,mfx,gx,mgx,lgx,sgx)|];
destruct y as [(fy,mfy,gy,mgy,lgy,sgy)|];
destruct z as [(fz,mfz,gz,mgz,lgz,sgz)|];
 try contradiction; simpl in *; auto.
destruct H; destruct H0; split.
 transitivity fy; trivial.
 transitivity gy; trivial.
Qed.

Instance eq_term_equiv : Equivalence eq_term.
constructor; auto with *.
Qed.

Lemma eq_kind : forall (M:term), M = None <-> eq_term M None.
destruct M; simpl; split; contradiction||discriminate||trivial.
Qed.

Definition dummy_term : Lc.term.
exact Lc.K.
Defined.
(* The only fact needed is that dummy_term is a closed term *)

Definition tm (M:term) (j:Lc.intt) :=
  match M with
  | Some f => itm f j
  | None => dummy_term
  end.

Instance tm_morph : Proper (eq_term ==> Lc.eq_intt ==> @eq Lc.term) tm.
unfold tm; do 3 red; intros.
destruct x; destruct y; simpl in *; (contradiction||reflexivity||auto).
destruct H; simpl in *.
apply H1; trivial.
Qed.

Lemma tm_substitutive : forall u t j k,
  tm t (fun n => Lc.subst_rec u (j n) k) =
  Lc.subst_rec u (tm t j) k.
destruct t; simpl; intros; trivial.
apply itm_subst.
Qed.

Lemma tm_liftable : forall j t k,
  tm t (fun n => Lc.lift_rec 1 (j n) k) = Lc.lift_rec 1 (tm t j) k.
destruct t; simpl; intros; trivial.
apply itm_lift.
Qed.

Lemma tm_subst_cons : forall x j t,
  tm t (I.cons x j) = Lc.subst x (tm t (Lc.ilift j)).
unfold Lc.subst; intros.
rewrite <- tm_substitutive.
apply tm_morph; [reflexivity|red; intros].
red.
destruct a; simpl.
 rewrite Lc.lift0; trivial.
 rewrite Lc.simpl_subst; trivial; rewrite Lc.lift0; trivial.
Qed.

Definition dummy_int : X.
Proof props.

Definition int (M:term) (i:val) :=
  match M with
  | Some f => iint f i
  | None => dummy_int
  end.

Instance int_morph : Proper (eq_term ==> eq_val ==> eqX) int.
unfold int; do 3 red; intros.
destruct x; destruct y; simpl in *; (contradiction||reflexivity||auto).
destruct H; simpl in *.
apply H; trivial.
Qed.


Lemma eq_term_intro : forall T T',
  (forall i, int T i == int T' i) ->
  (forall j, tm T j = tm T' j) ->
  match T, T' with Some _,Some _=>True|None,None=>True|_,_=>False end ->
  eq_term T T'.
destruct T as [T|]; destruct T' as [T'|]; simpl; intros; trivial.
split; red; intros.
 rewrite H2; auto.
 rewrite H2; auto.
Qed.

(** Substitutions *)

Record sub_ := {
  sint : val -> val;
  sint_morph : Proper (eq_val ==> eq_val) sint;
  stm : Lc.intt -> Lc.intt;
  stm_morph : Proper (Lc.eq_intt ==> Lc.eq_intt) stm;
  stm_lift : forall n, Lc.liftable (fun j => stm j n);
  stm_subst : forall n, Lc.substitutive (fun j => stm j n)
}.
Definition sub := sub_.
Definition eq_sub (s1 s2:sub) :=
     (eq_val ==> eq_val)%signature (sint s1) (sint s2) /\
     (Lc.eq_intt ==> Lc.eq_intt)%signature (stm s1) (stm s2).

Global Instance eq_sub_equiv : Equivalence eq_sub.
split; red; intros.
 red; split;red; intros; auto with *.
  apply sint_morph; trivial.
  apply stm_morph; trivial.

 destruct H.
 red; split;red; intros; auto with *.
  symmetry; apply H; symmetry; trivial.
  symmetry; apply H0; symmetry; trivial.

 destruct H; destruct H0.
 red; split; red; intros.
  transitivity (sint y x0); auto.
  apply H; reflexivity.

  transitivity (stm y x0); auto.
  apply H1; reflexivity.
Qed.

Definition sub_comp (s1 s2 : sub) : sub.
(*begin show*)
exists (fun i => sint s1 (sint s2 i))
       (fun j => stm s1 (stm s2 j)).
(*end show*)
do 2 red; intros.
do 2 apply sint_morph; trivial.

do 2 red; intros.
do 2 apply stm_morph; trivial.

red; intros.
eapply transitivity.
2:apply (stm_lift s1).
assert (s1m := stm_morph s1).
apply s1m.
intros i.
apply (stm_lift s2).

red; intros.
eapply transitivity.
2:apply (stm_subst s1).
assert (s1m := stm_morph s1).
apply s1m.
intros i.
apply (stm_subst s2).
Defined.

Definition sub_id : sub.
(*begin show*)
exists (fun i => i) (fun j => j).
(*end show*)
do 2 red; intros; trivial.
do 2 red; intros; trivial.
red; intros; reflexivity.
red; intros; reflexivity.
Defined.

Definition sub_cons (t:term) (s:sub) : sub.
(*begin show*)
exists (fun i => V.cons (int t i) (sint s i))
       (fun j => I.cons (tm t j) (stm s j)).
(*end show*)
do 2 red; intros.
apply V.cons_morph.
 rewrite H; reflexivity.

 apply sint_morph; trivial.
 
do 2 red; intros.
apply I.cons_morph.
 rewrite H; reflexivity.

 apply stm_morph; trivial.

destruct n; red; intros.
 apply tm_liftable.
 apply (stm_lift s).

destruct n; red; intros.
 apply tm_substitutive.
 apply (stm_subst s).
Defined.

Definition sub_lift (k:nat) (s:sub) : sub.
(*begin show*)
exists (V.lams k (sint s)) (I.lams k (stm s)).
(*end show*)
do 2 red; intros.
apply V.lams_morph; auto with *.
apply sint_morph.

do 2 red; intros.
apply I.lams_morph; auto with *.
apply stm_morph.

red; intros.
unfold I.lams.
destruct (le_gt_dec k n); trivial.
unfold I.shift.
apply (stm_lift s).

red; intros.
unfold I.lams.
destruct (le_gt_dec k n); trivial.
unfold I.shift.
apply (stm_subst s).
Defined.

Definition sub_shift (n:nat) : sub.
(*begin show*)
exists (V.shift n) (I.shift n).
(*end show*)
do 2 red; intros.
apply V.shift_morph; trivial.

do 2 red; intros.
apply I.shift_morph; trivial.

red; intros; reflexivity.

red; intros; reflexivity.
Defined.

Definition Sub (t:term) (s:sub) : term.
(*begin show*)
destruct t as [t|]; [left|exact None].
exists (fun i => iint t (sint s i))
       (fun j => itm t (stm s j)).
(*end show*)
do 2 red; intros.
apply iint_morph; apply sint_morph; trivial.

do 2 red; intros.
apply itm_morph; apply stm_morph; trivial.

red; intros.
eapply transitivity.
2:apply (itm_lift t).
apply (itm_morph t).
intros i.
apply (stm_lift s).

red; intros.
eapply transitivity.
2:apply (itm_subst t).
apply (itm_morph t).
intros i.
apply (stm_subst s).
Defined.

Lemma int_Sub_eq t s i :
  int (Sub t s) i == int t (sint s i).
destruct t as [t|]; simpl;reflexivity.
Qed.

Lemma tm_Sub_eq t s j :
  tm (Sub t s) j = tm t (stm s j).
destruct t as [t|]; simpl; reflexivity.
Qed.

Lemma eq_Sub_comp t s1 s2 :
  eq_term (Sub (Sub t s1) s2) (Sub t (sub_comp s1 s2)).
apply eq_term_intro; intros.
 rewrite !int_Sub_eq.
 unfold sub_comp; simpl; reflexivity.

 rewrite !tm_Sub_eq.
 unfold sub_comp; simpl; reflexivity.

 destruct t as [t|]; simpl; trivial.
Qed.

(** Property of substitutivity: whenever a term-denotation contains
   a free var, then it comes from the term-valuation (but we can't tell which
   var, short of using Markov rule, hence the double negation.
   *)
Lemma tm_closed : forall k j M,
  Lc.occur k (tm M j) -> ~ forall n, ~ Lc.occur k (j n).
red; intros.
rewrite Lc.occur_subst in H.
rewrite <- tm_substitutive in H.
rewrite <- tm_liftable in H.
apply H; clear H.
apply tm_morph; auto with *.
red; red; intros.
generalize (H0 a).
rewrite Lc.occur_subst; intro.
destruct (Lc.eqterm (Lc.lift_rec 1 (Lc.subst_rec (Lc.Abs (Lc.Ref 0)) (j a) k) k) (j a)); auto.
contradiction.
Qed.

(** Lift and substitution *)

Definition lift_rec (n m:nat) (t:term) : term.
(*begin show*)
destruct t as [t|]; [left|exact None].
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
  Proper (eq_term ==> eq_term) (lift_rec n k).
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
  int (lift_rec n k T) i == int T (V.lams k (V.shift n) i).
intros; destruct T as [T|]; simpl; reflexivity.
Qed.

Definition lift n := lift_rec n 0.
Definition lift1 n := lift_rec n 1.

Instance lift_morph : forall k, Proper (eq_term ==> eq_term) (lift k).
do 2 red; simpl; intros.
destruct x as [x|]; destruct y as [y|];
  simpl in *; (contradiction||trivial).
destruct H; split.
 red; intros.
 apply H; rewrite H1; reflexivity.

 red; intros.
 apply H0; rewrite H1; reflexivity.
Qed.

Lemma int_lift_eq : forall n T i,
  int (lift n T) i == int T (V.shift n i).
unfold int; intros;
  destruct T as [T|]; simpl; auto. (* BUG: intros needed before destruct *)
2:reflexivity.
rewrite V.lams0.
reflexivity.
Qed.

Lemma int_cons_lift_eq : forall i T x,
  int (lift 1 T) (V.cons x i) == int T i.
intros.
rewrite int_lift_eq.
rewrite V.shift_cons; reflexivity.
Qed.

Lemma tm_lift_rec_eq : forall n k T j,
  tm (lift_rec n k T) j = tm T (I.lams k (I.shift n) j).
intros; destruct T; simpl; reflexivity.
Qed.

Lemma lift0 : forall A, eq_term (lift 0 A) A.
intros; apply eq_term_intro; intros; [| |destruct A; simpl; trivial].
 unfold lift; rewrite int_lift_rec_eq; rewrite V.lams0; reflexivity.

 unfold lift; rewrite tm_lift_rec_eq; rewrite I.lams0; reflexivity.
Qed.

Lemma split_lift : forall n T,
  eq_term (lift (S n) T) (lift 1 (lift n T)).
destruct T as [T|]; simpl; auto.
split; red; intros.
 do 2 rewrite V.lams0.
 change (V.shift n (fun k => V.lams 0 (V.shift 1) y k)) with
   (V.shift n (V.lams 0 (V.shift 1) y)).
 rewrite V.lams0.
 rewrite V.shiftS_split.
 change (eq_val (fun k => x k) (fun k => y k)) in H.
 rewrite H; reflexivity.

 do 2 rewrite I.lams0.
 change (I.shift n (fun k => I.lams 0 (I.shift 1) y k)) with
   (I.shift n (I.lams 0 (I.shift 1) y)).
 rewrite I.lams0.
 rewrite I.shiftS_split.
 change (Lc.eq_intt (fun k => x k) (fun k => y k)) in H.
 rewrite H; reflexivity.
Qed.

Definition subst_rec (arg:term) (m:nat) (t:term) : term.
(*begin show*)
destruct t as [body|]; [left|right].
exists (fun i => iint body (V.lams m (V.cons (int arg (V.shift m i))) i))
       (fun j => itm body (I.lams m (I.cons (tm arg (I.shift m j))) j)).
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
  Proper (eq_term ==> eq ==> eq_term ==> eq_term) subst_rec.
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
  int (subst_rec arg k T) i == int T (V.lams k (V.cons (int arg (V.shift k i))) i).
intros; destruct T as [T|]; simpl; reflexivity.
Qed.

Definition subst arg := subst_rec arg 0.

Lemma int_subst_eq : forall N M i,
 int M (V.cons (int N i) i) == int (subst N M) i.
destruct M as [M|]; simpl; intros.
2:reflexivity.
rewrite V.lams0.
rewrite V.shift0.
reflexivity.
Qed.

Lemma tm_subst_rec_eq : forall arg k T j,
  tm (subst_rec arg k T) j = tm T (I.lams k (I.cons (tm arg (I.shift k j))) j).
intros; destruct T; simpl; reflexivity.
Qed.

Lemma tm_subst_eq : forall u v j,
  tm (subst u v) j = Lc.subst (tm u j) (tm v (Lc.ilift j)).
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

(** Pseudo-term constructors *)

Definition cst (x:X) (t:Lc.term)
  (H0 : Lc.liftable (fun _ => t)) (H1 : Lc.substitutive (fun _ => t)) : term.
(* begin show *)
left; exists (fun _ => x) (fun _ => t); trivial.
(* end show *)
 do 2 red; reflexivity.
 do 2 red; reflexivity.
Defined.

Definition kind : term := None.

Lemma kind_dec (T:term) : {T=kind}+{T<>kind}.
destruct T;[right;discriminate|left;reflexivity].
Qed.

Definition prop : term :=
  @cst props (Lc.K) (fun _ _ => eq_refl _) (fun _ _ _ => eq_refl _).

Definition Ref (n:nat) : term.
(* begin show*)
left; exists (fun i => i n) (fun j => j n).
(*end show*)
 do 2 red; simpl; auto.
 do 2 red; simpl; auto.
 red; reflexivity.
 red; reflexivity.
Defined.

Definition App (u v:term) : term.
(*begin show*)
left; exists (fun i => app (int u i) (int v i))
             (fun j => Lc.App (tm u j) (tm v j)). 
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

Definition Abs (A M:term) : term.
(*begin show*)
left; exists (fun i => lam (int A i) (fun x => int M (V.cons x i)))
             (fun j => CAbs (tm A j) (tm M (Lc.ilift j))).
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

Definition Prod (A B:term) : term.
(*begin show*)
left; exists (fun i => prod (int A i) (fun x => int B (V.cons x i)))
             (fun j => CProd (tm A j) (tm B (Lc.ilift j))).
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
  int (Prod A B) i = prod (int A i) (fun x => int B (V.cons x i)).
reflexivity.
Qed.

Instance App_morph : Proper (eq_term ==> eq_term ==> eq_term) App.
unfold App; do 3 red; simpl; split; intros.
 red; intros.
 rewrite H; rewrite H0; rewrite H1; reflexivity.

 red; intros.
 rewrite H; rewrite H0; rewrite H1; reflexivity.
Qed.

Instance Abs_morph : Proper (eq_term ==> eq_term ==> eq_term) Abs.
unfold Abs; do 4 red; simpl; split; red; intros.
 apply lam_ext.
  apply int_morph; auto.

  red; intros.
  rewrite H0; rewrite H1; rewrite H3; reflexivity.

 rewrite H0; rewrite H1; rewrite H; reflexivity.
Qed.


Instance Prod_morph : Proper (eq_term ==> eq_term ==> eq_term) Prod.
unfold Prod; do 4 red; simpl; split; red; intros.
 apply prod_ext.
  rewrite H; rewrite H1; reflexivity.

  red; intros.
  rewrite H0; rewrite H1; rewrite H3; reflexivity.

 rewrite H0; rewrite H1; rewrite H; reflexivity.
Qed.


Lemma discr_ref_prod : forall n A B,
  ~ eq_term (Ref n) (Prod A B).
red; intros.
simpl in H.
destruct H as (_,H).
red in H.
specialize H with Lc.Ref Lc.Ref.
discriminate H.
reflexivity.
Qed.

Lemma eq_term_lift_ref_fv n k i :
  k <= i ->
  eq_term (lift_rec n k (Ref i)) (Ref (n+i)).
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
Lemma red_lift_ref_bound n k i :
  (i < k)%nat ->
  eq_term (lift_rec n k (Ref i)) (Ref i).
intros; simpl.
unfold V.lams, V.shift, I.lams, I.shift.
destruct (le_gt_dec  k i).
 exfalso; omega.
split; red; intros; auto.
Qed.
Lemma red_lift_ref n k i :
  eq_term (lift_rec n k (Ref i)) (Ref (if le_gt_dec k i then n+i else i)).
destruct (le_gt_dec k i).
apply eq_term_lift_ref_fv; trivial.
apply red_lift_ref_bound; trivial.
Qed.

(*
Lemma lift1var : forall n, eq_term (lift 1 (Ref n)) (Ref (S n)).
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
  eq_term (lift_rec n k (App A B)) (App (lift_rec n k A) (lift_rec n k B)).
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
  eq_term (lift_rec n k (Abs A B)) (Abs (lift_rec n k A) (lift_rec n (S k) B)).
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
  eq_term (lift_rec n k (Prod A B)) (Prod (lift_rec n k A) (lift_rec n (S k) B)).
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
  eq_term (subst_rec N k (App A B)) (App (subst_rec N k A) (subst_rec N k B)).
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
  eq_term (subst_rec N k (Abs A B)) (Abs (subst_rec N k A) (subst_rec N (S k) B)).
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
  eq_term (subst_rec N k (Prod A B)) (Prod (subst_rec N k A) (subst_rec N (S k) B)).
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
  eq_term (subst_rec N k (Ref k)) (lift k N).
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
  eq_term (subst_rec N k (Ref n)) (Ref n).
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
  eq_term (subst_rec N k (Ref (S n))) (Ref n).
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
Lemma red_sigma_ref N k i :
  N <> kind ->
  eq_term (subst_rec N k (Ref i))
    match lt_eq_lt_dec k i with
    | inleft (left _) => Ref (Peano.pred i)
    | inleft (right _) => lift k N
    | inright _ => Ref i
    end.
intros.
destruct (lt_eq_lt_dec k i) as [[?|?]|?].
 destruct i; simpl Peano.pred.
  inversion l.
 apply red_sigma_var_gt; auto with arith.

 subst i; apply red_sigma_var_eq; trivial.

 apply red_sigma_var_lt; auto with arith.
Qed.

Lemma simpl_subst_lift_rec A M k :
  eq_term M (subst_rec A k (lift_rec 1 k M)).
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
  forall j, Lc.redp (tm M j) (tm N j).

Instance red_term_morph : Proper (eq_term ==> eq_term ==> iff) red_term.
apply morph_impl_iff2; auto with *.
do 4 red; intros.
red; intros.
rewrite <- H; rewrite <- H0; auto.
Qed.

Instance red_term_trans : Transitive red_term.
unfold red_term; red; intros.
specialize H with j.
specialize H0 with j.
apply t_trans with (tm y j); trivial.
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
  forall j, Lc.conv (tm M j) (tm N j).

Instance conv_term_morph : Proper (eq_term ==> eq_term ==> iff) conv_term.
apply morph_impl_iff2; auto with *.
do 4 red; intros.
red; intros.
rewrite <- H; rewrite <- H0; auto.
Qed.

Instance conv_term_equiv : Equivalence conv_term.
split; red; red; intros.
 apply Lc.conv_refl.
 symmetry; trivial.
 transitivity (tm y j); trivial. 
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
  forall j M', M = tm M' j ->
  Acc (transp _ red_term) M'.
intros snM.
elim (Acc_clos_trans _ _ _ snM); clear snM; intros.
constructor; intros.
red in H2.
assert (redM' := H2 j).
assert (clos_trans _ (transp _ Lc.red1) (tm y j) x).
 rewrite H1.
 clear H1 H2.
 elim redM'; intros.
  apply t_step; trivial.

  apply t_trans with y0; trivial.
apply H0 with (tm y j) j; trivial.
Qed.


(** Iterated products *)

Fixpoint prod_list (e:list term) (U:term) :=
  match e with
  | List.nil => U
  | T::f => Prod T (prod_list f U)
  end.

Lemma lift_prod_list_ex n k e T :
  exists e',
  eq_term (lift_rec n k (prod_list e T))
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
  eq_term (subst_rec M k (prod_list e T))
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

(** Dealing with kind (top sorts) *)

Fixpoint cst_fun (i:val) (e:list term) (x:X) : X :=
  match e with
  | List.nil => x
  | T::f => lam (int T i) (fun y => cst_fun (V.cons y i) f x)
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
  (forall i, x ∈ int U i) ->
  forall e i,
  cst_fun i e x ∈ int (prod_list e U) i.
induction e; simpl; intros; auto.
apply prod_intro; intros; auto.
 red; intros.
 rewrite H1; reflexivity.

 red; intros.
 rewrite H1; reflexivity.
Qed.

(* We could parameterize kind_ok with a val [i0], and
   quantify over i s.t. vshift (length e) i = i0.
   This would allow kind variables. *)

Definition kind_ok T :=
  exists e, exists2 U, eq_term T (prod_list e U) &
    exists x, forall i, x ∈ int U i.

Instance kind_ok_morph : Proper (eq_term ==> iff) kind_ok.
unfold kind_ok; do 2 red; intros.
split; intros (e,(U,eq_U,inU)); exists e;
  exists U; trivial.
 rewrite <- H; trivial.
 rewrite H; trivial.
Qed.

Lemma prop_kind_ok : kind_ok prop.
exists List.nil; exists prop; simpl prod_list.
 reflexivity.

 exists (prod props (fun P => P)); intros.
 apply impredicative_prod; intros; auto.
 red; auto.
Qed.

Lemma prod_kind_ok : forall T U,
  kind_ok U ->
  kind_ok (Prod T U).
intros.
destruct H as (e,(U',eq_U,wit_U)).
exists (T::e); exists U'; simpl prod_list; trivial.
rewrite eq_U; reflexivity.
Qed.

Lemma kind_ok_witness : forall i T,
  kind_ok T ->
  exists x, x ∈ int T i.
intros.
destruct H as (e,(U,eq_U,(wit,in_U))).
exists (cst_fun i e wit).
rewrite eq_U.
apply wit_prod; trivial.
Qed.

Lemma kind_ok_lift M k :
  kind_ok M <-> kind_ok (lift_rec 1 k M).
unfold kind_ok; split; intros.
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

Lemma kind_ok_refS n :
  kind_ok (Ref n) -> kind_ok (Ref (S n)).
intros.
apply kind_ok_lift with (k:=0) in H.
rewrite eq_term_lift_ref_fv in H; auto with arith.
Qed.

End T.
Export T.

End MakeObject.
