
Require Import basic.
Require Import Models List.

(** A general model construction of a model of CC given an
    abstract model. *)

Module MakeModel(M : CC_Model).
Import M.

Lemma eq_fun_sym : forall x f1 f2, eq_fun x f1 f2 -> eq_fun x f2 f1.
Proof.
unfold eq_fun in |- *; intros.
symmetry  in |- *.
apply H.
 rewrite <- H1; trivial.
 symmetry  in |- *; trivial.
Qed.

Lemma eq_fun_trans : forall x f1 f2 f3,
   eq_fun x f1 f2 -> eq_fun x f2 f3 -> eq_fun x f1 f3.
Proof.
unfold eq_fun in |- *; intros.
transitivity (f2 y1); auto.
apply H; trivial.
reflexivity.
Qed.

(** Valuations *)
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
Hint Unfold eq_val.


(** * Pseudo-Terms *)

Module T.

Definition term :=
  option {f:val -> X|Proper (eq_val ==> eqX) f}.

Definition eq_term (x y:term) :=
  match x, y with
  | Some f, Some g => (eq_val ==> eqX)%signature (proj1_sig f) (proj1_sig g)
  | None, None => True
  | _, _ => False
  end.

Global Instance eq_term_refl : Reflexive eq_term.
red; intros.
destruct x; simpl; trivial.
destruct s; trivial.
Qed.

Global Instance eq_term_sym : Symmetric eq_term.
red; intros.
destruct x; destruct y; simpl in *; auto.
symmetry; trivial.
Qed.

Global Instance eq_term_trans : Transitive eq_term.
red; intros.
destruct x; destruct y; try contradiction; destruct z; simpl in *; auto.
transitivity (proj1_sig s0); trivial.
Qed.

(** Denotation as value *)
Definition int (t:term) (i:val) : X :=
  match t with
  | Some f => proj1_sig f (fun k => i k)
  | None => props
  end.

Global Instance int_morph : Proper (eq_term ==> eq_val ==> eqX) int.
unfold int; do 3 red; intros.
destruct x; destruct y; simpl in *; (contradiction||reflexivity||auto).
Qed.

(** Denotation as type *)
Definition el (t:term) (i:val) (x:X) :=
  match t with
  | Some _ => x ∈ int t i
  | None => True
  end.

Global Instance el_morph : Proper (eq_term ==> eq_val ==> eqX ==> iff) el.
apply morph_impl_iff3; auto with *.
unfold el; do 5 red; intros.
 destruct y; trivial; destruct x; (contradiction||simpl in *).
 rewrite <- H1.
 rewrite <- (H (fun k => x0 k) (fun k => y0 k)); auto.
Qed.

Lemma in_int_el : forall i x T,
  x ∈ int T i -> el T i x.
destruct T as [(T,Tm)|]; simpl; trivial.
Qed.

Lemma in_int_not_kind T i x :
  el T i x ->
  T <> None ->
  x ∈ int T i.
destruct T as [(T,Tm)|]; simpl; intros; trivial.
elim H0; trivial.
Qed.

(** Injecting sets into the model *)
Definition cst (x:X) : term.
(*begin show*)
left; exists (fun _ => x).
(*end show*)
do 2 red; reflexivity.
Defined.


(** General substitutions *)
Record sub := mkSub {
  sub_f :> val -> val;
  sub_m : Proper (eq_val ==> eq_val) sub_f
}.
Existing Instance sub_m.

Definition eq_sub (s1 s2:sub) :=
  (eq_val==>eq_val)%signature s1 s2.
  
Definition Sub (t:term) (s:sub) : term.
(* begin show *)
destruct t as [(t,tm)|];
 [left; exists (fun i => t (s i))|right].
(* end show *)
do 2 red; intros; auto.
apply tm; apply sub_m; trivial.
Defined.

Definition sub_id : sub.
exists (fun x => x).
do 2 red; auto.
Defined.

Definition sub_comp (s1 s2:sub) : sub.
exists (fun i => s2 (s1 i)).
do 2 red; intros.
apply sub_m.
apply sub_m.
trivial.
Defined.

Definition sub_lift (m:nat) (s:sub) : sub.
exists (V.lams m s).
do 2 red; intros.
apply V.lams_morph; trivial.
apply sub_m.
Defined.

Definition sub_shift (n:nat) : sub.
exists (V.shift n); auto with *.
apply V.shift_morph; trivial.
Defined.

Definition sub_cons (t:term) (s:sub) : sub.
exists (fun i => V.cons (int t i) (s i)).
do 2 red; intros.
apply V.cons_morph.
 apply int_morph; auto with *.
 apply sub_m; trivial.
Defined.

(** Relocations *)
Section Lift.

Definition lift_rec (n m:nat) (t:term) : term.
(*begin show*)
destruct t as [(t,tm)|]; [left|exact None].
exists (fun i => t (V.lams m (V.shift n) i)).
(*end show*)
 do 2 red; intros.
 rewrite H; reflexivity.
Defined.

Global Instance lift_rec_morph n k : Proper (eq_term ==> eq_term) (lift_rec n k).
do 3 red; intros.
destruct x as [(x,xm)|]; destruct y as [(y,ym)|]; simpl in H|-*; try contradiction; trivial.
red; intros.
apply H.
rewrite H0; reflexivity.
Qed.

Lemma lift_rec_equiv n k t :
  eq_term (lift_rec n k t) (Sub t (sub_lift k (sub_shift n))).
destruct t as [(t,tm)|]; simpl; trivial.
red; intros.
rewrite H.
reflexivity.
Qed.

Definition lift1 n := lift_rec n 1.

Lemma lift10: forall T, eq_term (lift1 0 T) T.
unfold lift1.
destruct T as [(T,Tm)|]; simpl; trivial.
red; intros.
apply Tm; do 2 red; intros.
unfold V.lams, V.shift; destruct a; simpl.
 apply H.

 replace (a-0) with a; auto with arith.
Qed.

Lemma int_lift_rec_eq : forall n k T i,
  int (lift_rec n k T) i == int T (V.lams k (V.shift n) i).
intros; destruct T as [(T,Tm)|]; simpl; reflexivity.
Qed.

Definition lift n := lift_rec n 0.

Global Instance lift_morph : forall k, Proper (eq_term ==> eq_term) (lift k).
do 3 red; simpl; intros.
destruct x as [(x,xm)|]; destruct y as [(y,ym)|];
  simpl in *; (contradiction||trivial).
red; intros.
apply H.
rewrite H0; reflexivity.
Qed.

Lemma lift0_term : forall T, eq_term (lift 0 T) T.
destruct T as [(T,Tm)|]; simpl; trivial.
red; intros.
apply Tm.
rewrite V.lams0.
rewrite V.shift0.
do 2 red; apply H.
Qed.

Lemma simpl_int_lift : forall i n x T,
  int (lift (S n) T) (V.cons x i) == int (lift n T) i.
intros.
destruct T as [(T,Tm)|]; simpl; auto with *.
apply Tm.
red; red; intros; reflexivity.
Qed.

Lemma simpl_int_lift1 : forall i x T,
  int (lift 1 T) (V.cons x i) == int T i.
intros.
rewrite simpl_int_lift; rewrite lift0_term; reflexivity.
Qed.

Lemma simpl_lift1 : forall i n x y T,
  int (lift1 (S n) T) (V.cons x (V.cons y i)) == int (lift1 n T) (V.cons x i).
unfold lift1; simpl; intros.
do 2 rewrite int_lift_rec_eq.
repeat rewrite <- V.cons_lams.
 reflexivity.

 do 2 red; intros; rewrite H; reflexivity.

 do 2 red; intros; rewrite H; reflexivity.
Qed.

Lemma eqterm_lift_cst : forall n k c,
  eq_term (lift_rec n k (cst c)) (cst c).
red; simpl; intros.
red; reflexivity.
Qed.

End Lift.

(** Substitution *)
Section Substitution.

Definition subst_rec (arg:term) (m:nat) (t:term) : term.
(*begin show*)
destruct t as [(body,bm)|]; [left|right].
exists (fun i => body (V.lams m (V.cons (int arg (V.shift m i))) i)).
(*end show*)
 do 2 red; intros.
 rewrite H; reflexivity.
Defined.

Global Instance subst_rec_morph : Proper (eq_term ==> eq ==> eq_term ==> eq_term) subst_rec.
do 4 red; intros.
destruct x1 as [(x1,x1m)|]; destruct y1 as [(y1,y1m)|]; simpl in H1|-*; try contradiction; trivial.
red; intros.
apply H1.
rewrite H; rewrite H0; rewrite H2; reflexivity.
Qed.

Lemma subst_rec_equiv a k t :
  eq_term (subst_rec a k t) (Sub t (sub_lift k (sub_cons a sub_id))).
destruct t as [(t,tm)|]; simpl; trivial.
red; intros.
apply tm.
unfold V.lams; do 2 red; intros.
destruct (le_gt_dec k a0); auto with *.
rewrite H; reflexivity.
Qed.


Lemma int_subst_rec_eq : forall arg k T i,
  int (subst_rec arg k T) i == int T (V.lams k (V.cons (int arg (V.shift k i))) i).
intros; destruct T as [(T,Tm)|]; simpl; reflexivity.
Qed.

Definition subst arg := subst_rec arg 0.

Global Instance subst_morph : Proper (eq_term ==> eq_term ==> eq_term) subst.
do 3 red; simpl; intros.
destruct x0 as [(x0,xm0)|]; destruct y0 as [(y0,ym0)|];
  simpl in *; (contradiction||trivial).
red; intros.
apply H0.
rewrite H; rewrite H1; reflexivity.
Qed.

Lemma int_subst_eq : forall N M i,
  int (subst N M) i == int M (V.cons (int N i) i).
destruct M as [(M,Mm)|]; simpl; intros.
2:reflexivity.
rewrite V.lams0.
rewrite V.shift0.
reflexivity.
Qed.

Lemma el_subst_eq : forall N M i x,
  el (subst N M) i x <-> el M (V.cons (int N i) i) x.
destruct M as [(M,Mm)|]; simpl; intros.
2:reflexivity.
rewrite V.lams0.
rewrite V.shift0.
reflexivity.
Qed.

End Substitution.



(** Syntax of the Calculus of Constructions *)
Definition prop := cst props.

Definition kind : term := None.

Definition Ref (n:nat) : term.
(*begin show*)
left; exists (fun i => i n).
(*end show*)
do 2 red; simpl; auto.
Defined.

Definition App (u v:term) : term.
(*begin show*)
left; exists (fun i => app (int u i) (int v i)).
(*end show*)
do 2 red; simpl; intros.
rewrite H; reflexivity.
Defined.

Global Instance App_morph : Proper (eq_term ==> eq_term ==> eq_term) App.
unfold App; do 3 red; simpl; intros.
red; intros.
rewrite H; rewrite H0; rewrite H1; reflexivity.
Qed.

Lemma eqterm_subst_App : forall N u v,
  eq_term (subst N (App u v)) (App (subst N u) (subst N v)).
red; simpl; intros.
red; intros.
unfold subst.
do 2 rewrite int_subst_rec_eq.
rewrite H.
reflexivity.
Qed.

Definition Abs (A M:term) : term.
(*begin show*)
left; exists (fun i => lam (int A i) (fun x => int M (V.cons x i))).
(*end show*)
do 2 red; simpl; intros.
apply lam_ext.
 rewrite H; reflexivity.
(**)
 red; intros.
 rewrite H; rewrite H1; reflexivity.
Defined.

Global Instance Abs_morph : Proper (eq_term ==> eq_term ==> eq_term) Abs.
unfold Abs; do 5 red; simpl; intros.
apply lam_ext.
 apply int_morph; auto.

 red; intros.
 rewrite H0; rewrite H1; rewrite H3; reflexivity.
Qed.

Lemma eq_lift_abs : forall n A B k,
  eq_term (lift_rec n k (Abs A B))
    (Abs (lift_rec n k A) (lift_rec n (S k) B)).
do 5 red; simpl; intros.
apply lam_ext; intros.
 rewrite int_lift_rec_eq.
 rewrite H; reflexivity.

 red; intros.
 rewrite int_lift_rec_eq.
 rewrite <- V.cons_lams; auto with *.
  rewrite H1; rewrite H; reflexivity.

  do 2 red; intros.
  rewrite H2; reflexivity.
Qed.

Definition Prod (A B:term) : term.
(*begin show*)
left; exists (fun i => prod (int A i) (fun x => int B (V.cons x i))).
(*end show*)
do 2 red; simpl; intros.
apply prod_ext.
 rewrite H; reflexivity.
(**)
 red; intros.
 rewrite H; rewrite H1; reflexivity.
Defined.

Global Instance Prod_morph : Proper (eq_term ==> eq_term ==> eq_term) Prod.
unfold Prod; do 5 red; simpl; intros.
apply prod_ext.
 apply int_morph; auto.

 red; intros.
 rewrite H0; rewrite H1; rewrite H3; reflexivity.
Qed.

Lemma eq_lift_prod : forall n A B k,
  eq_term (lift_rec n k (Prod A B))
    (Prod (lift_rec n k A) (lift_rec n (S k) B)).
do 5 red; simpl; intros.
apply prod_ext; intros.
 rewrite int_lift_rec_eq.
 rewrite H; reflexivity.

 red; intros.
 rewrite int_lift_rec_eq.
 rewrite <- V.cons_lams; auto with *.
  rewrite H1; rewrite H; reflexivity.

  do 2 red; intros.
  rewrite H2; reflexivity.
Qed.

Lemma eq_subst_prod : forall u A B k,
  eq_term (subst_rec u k (Prod A B))
    (Prod (subst_rec u k A) (subst_rec u (S k) B)).
do 5 red; simpl; intros.
apply prod_ext; intros.
 rewrite int_subst_rec_eq.
 rewrite H; reflexivity.

 red; intros.
 rewrite int_subst_rec_eq.
 rewrite <- V.cons_lams; auto with *.
  rewrite H1; rewrite H; reflexivity.

  do 2 red; intros.
  rewrite H2; reflexivity.
Qed.

End T.
Import T.

(** * Environments *)
Definition env := list term.

Definition val_ok (e:env) (i:val) :=
  forall n T, nth_error e n = value T -> el (lift (S n) T) i (i n).

Lemma vcons_add_var0 : forall e T i x,
  val_ok e i -> el T i x -> val_ok (T::e) (V.cons x i).
unfold val_ok; simpl; intros.
destruct n; simpl in *.
 injection H1; clear H1; intro; subst; simpl in *.
 destruct T0 as [(T0,Tm)|]; simpl in *; trivial.
 rewrite V.lams0; assumption.

 apply H in H1; simpl in H1; trivial.
 destruct T0 as [(T0,Tm)|]; simpl in *; trivial.
Qed.

Lemma vcons_add_var : forall e T i x,
  val_ok e i -> x ∈ int T i -> val_ok (T::e) (V.cons x i).
intros.
apply vcons_add_var0; trivial.
destruct T as[(T,Tm)|]; simpl in *; trivial.
Qed.


Lemma add_var_eq_fun : forall T U U' i,
  (forall x, el T i x -> int U (V.cons x i) == int U' (V.cons x i)) -> 
  eq_fun (int T i)
    (fun x => int U (V.cons x i))
    (fun x => int U' (V.cons x i)).
red; intros.
rewrite <- H1.
apply H.
destruct T as [(T,Tm)|]; simpl in *; trivial.
Qed.


(** * Judgements *)

Module J.

(** Typing *)
Definition typ (e:env) (M T:term) :=
  forall i, val_ok e i -> el T i (int M i).
(** Equality *)
Definition eq_typ (e:env) (M M':term) :=
  forall i, val_ok e i -> int M i == int M' i.
(** Subtyping *)
Definition sub_typ (e:env) (M M':term) :=
  forall i x, val_ok e i -> x ∈ int M i -> x ∈ int M' i.
(** Alternative equality (with kind=kind) *)
Definition eq_typ' e M M' :=
  eq_typ e M M' /\ match M,M' with None,None => True|Some _,Some _=>True|_,_=>False end.
(** Subtyping as inclusion of values *)
Definition sub_typ' (e:env) (M M':term) :=
  forall i x, val_ok e i -> el M i x -> el M' i x.


Definition typ_sub (e:env) (s:sub) (f:env) :=
  forall i, val_ok e i -> val_ok f (s i).

Global Instance typ_morph : forall e, Proper (eq_term ==> eq_term ==> iff) (typ e).
intros.
apply morph_impl_iff2; auto with *.
unfold typ; do 4 red; intros.
rewrite <- H; rewrite <- H0; auto.
Qed.

Global Instance eq_typ_morph : forall e, Proper (eq_term ==> eq_term ==> iff) (eq_typ e).
intros.
apply morph_impl_iff2; auto with *.
unfold eq_typ; do 4 red; intros.
rewrite <- H; rewrite <- H0; auto.
Qed.

(*
Instance eq_typ'_morph : forall e, Proper (eq_term ==> eq_term ==> iff) (eq_typ' e).
unfold eq_typ'; split; simpl; intros.
 destruct x; destruct y; try contradiction.

 rewrite <- H; rewrite <- H0; auto.
 rewrite H; rewrite H0; auto.
Qed.
*)
Global Instance sub_typ_morph : forall e, Proper (eq_term ==> eq_term ==> iff) (sub_typ e).
intros.
apply morph_impl_iff2; auto with *.
unfold sub_typ; do 4 red; intros.
rewrite <- H in H3; rewrite <- H0; auto.
Qed.

Global Instance sub_typ'_morph : forall e, Proper (eq_term ==> eq_term ==> iff) (sub_typ' e).
intros.
apply morph_impl_iff2; auto with *.
unfold sub_typ'; do 4 red; intros.
rewrite <- H in H3; rewrite <- H0; auto.
Qed.

End J.
Import J.

(** * Inference rules *)

Module R.

(** Equality rules *)

Lemma refl : forall e M, eq_typ e M M.
red; simpl; reflexivity.
Qed.

Lemma sym : forall e M M', eq_typ e M M' -> eq_typ e M' M.
unfold eq_typ; symmetry; auto.
Qed.

Lemma trans : forall e M M' M'', eq_typ e M M' -> eq_typ e M' M'' -> eq_typ e M M''.
unfold eq_typ; intros.
transitivity (int M' i); auto.
Qed.

Global Instance eq_typ_equiv : forall e, Equivalence (eq_typ e).
split.
 exact (refl e).
 exact (sym e).
 exact (trans e).
Qed.


Lemma eq_typ_app : forall e M M' N N',
  eq_typ e M M' ->
  eq_typ e N N' ->
  eq_typ e (App M N) (App M' N').
unfold eq_typ; simpl; intros.
apply app_ext; auto.
Qed.

Lemma eq_typ_abs : forall e T T' M M',
  eq_typ e T T' ->
  eq_typ (T::e) M M' ->
  eq_typ e (Abs T M) (Abs T' M').
Proof.
unfold eq_typ; simpl; intros.
apply lam_ext; auto.
apply add_var_eq_fun; trivial.
intros.
apply H0.
apply vcons_add_var0; trivial.
Qed.

Lemma eq_typ_prod : forall e T T' U U',
  eq_typ e T T' ->
  eq_typ (T::e) U U' ->
  eq_typ e (Prod T U) (Prod T' U').
unfold eq_typ; simpl; intros.
apply prod_ext; auto.
apply add_var_eq_fun; trivial.
intros.
apply H0.
apply vcons_add_var0; trivial.
Qed.

Lemma eq_typ_beta : forall e T M M' N N',
  eq_typ (T::e) M M' ->
  eq_typ e N N' ->
  typ e N T -> (* Typed reduction! *)
  T <> kind ->
  eq_typ e (App (Abs T M) N) (subst N' M').
Proof.
unfold eq_typ, typ, App, Abs; simpl; intros.
rewrite int_subst_eq.
assert (eq_fun (int T i) (fun x => int M (V.cons x i)) (fun x => int M (V.cons x i))).
 apply add_var_eq_fun with (T:=T); intros; trivial; reflexivity.
assert (int N i ∈ int T i).
 destruct T as [(T,Tm)|]; [clear H2;simpl in *;auto|elim H2;reflexivity]. 
rewrite beta_eq; auto.
rewrite <- H0; auto.
apply H.
apply vcons_add_var0; simpl; auto.
Qed.

(** Typing rules *)

Lemma typ_Sub e f s m u :
  typ f m u ->
  typ_sub e s f ->
  typ e (Sub m s) (Sub u s).
unfold typ, typ_sub; intros.
destruct u as [(u,um)|]; simpl in *; trivial.
 simpl.
 destruct m as [(m,mm)|]; simpl in *; auto.
Qed.

Lemma typ_prop : forall e, typ e prop kind.
red; simpl; trivial.
Qed.

Lemma typ_var : forall e n T,
  nth_error e n = value T -> typ e (Ref n) (lift (S n) T).
unfold lift; red; simpl; intros.
apply H0 in H.
destruct T; simpl in *; trivial.
Qed.

Lemma typ_app : forall e u v V Ur,
  typ e v V ->
  typ e u (Prod V Ur) ->
  V <> kind ->
  typ e (App u v) (subst v Ur).
unfold typ, App, Prod; simpl;
intros e u v V Ur ty_v ty_u not_tops i is_val.
specialize (ty_v _ is_val).
specialize (ty_u _ is_val).
destruct V as [(V,Vm)|]; [clear not_tops;simpl in *|elim not_tops;reflexivity].
apply in_int_el.
rewrite int_subst_eq.
apply prod_elim with (dom := V (fun k => i k)) (F:=fun x => int Ur (V.cons x i)); trivial.
red; intros.
rewrite H0; reflexivity.
Qed.

Lemma typ_abs : forall e T M U,
  typ (T :: e) M U ->
  U <> kind ->
  typ e (Abs T M) (Prod T U).
Proof.
unfold typ, Abs, Prod; simpl; intros e T M U ty_M not_tops i is_val.
apply prod_intro.
 apply add_var_eq_fun; trivial; intros; reflexivity.

 apply add_var_eq_fun; trivial; intros; reflexivity.

 intros.
 destruct U as[U|]; [clear not_tops; simpl in *|elim not_tops; reflexivity].
 apply ty_M.
 apply vcons_add_var; trivial.
Qed.

Lemma typ_beta : forall e T M N U,
  typ e N T ->
  typ (T::e) M U ->
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
  typ (T :: e) U s2 ->
  typ e (Prod T U) s2.
Proof.
unfold typ, Prod; simpl; red; intros e T U s2 is_srt ty_U i is_val.
destruct s2 as [(s2,sm)|]; trivial; simpl in *.
destruct is_srt as [is_srt|is_srt];
  [discriminate|injection is_srt;clear is_srt; intro; subst s2].
apply impredicative_prod.
 red; intros.
 rewrite H0; reflexivity.

 intros.
 apply ty_U.
 apply vcons_add_var; trivial.
Qed.

Lemma typ_conv : forall e M T T',
  typ e M T ->
  eq_typ e T T' ->
  T <> kind ->
  typ e M T'.
Proof.
unfold typ, eq_typ; simpl; intros.
destruct T as [(T,Tm)|]; [simpl in *; clear H1|elim H1; reflexivity].
destruct T' as [(T',T'm)|]; simpl in *; trivial.
rewrite <- H0; auto.
Qed.

(** Weakening *)

Lemma weakening : forall e M T A,
  typ e M T ->
  typ (A::e) (lift 1 M) (lift 1 T).
unfold typ; intros.
destruct T as [(T,Tm)|]; simpl in *; trivial.
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

Lemma weakening0 : forall e M T,
  typ e M T ->
  typ e (lift 0 M) (lift 0 T).
red; intros.
destruct T as [(T,Tm)|]; simpl; trivial.
rewrite V.lams0.
unfold V.shift; simpl.
rewrite lift0_term.
apply H; trivial.
Qed.

(* TODO: use split lift! *)
Lemma weakeningS : forall e k M T A,
  typ e (lift k M) (lift k T) ->
  typ (A::e) (lift (S k) M) (lift (S k) T).
red; intros.
assert (val_ok e (V.shift 1 i)).
 red; intros.
 specialize (H0 (S n) _ H1).
 destruct T0 as [(T0,T0m)|]; simpl in *; auto.
specialize (H _ H1).
destruct T as [(T,Tm)|]; simpl in *; auto.
unfold lift in H|-*.
rewrite int_lift_rec_eq in H|-*.
rewrite V.lams0 in H|-*.
assumption.
Qed.


(** Subtyping *)
Lemma sub_refl : forall e M M',
  eq_typ e M M' -> sub_typ e M M'.
red; intros.
apply H in H0.
clear H.
rewrite <- H0; trivial.
Qed.

Lemma sub_trans : forall e M1 M2 M3,
  sub_typ e M1 M2 -> sub_typ e M2 M3 -> sub_typ e M1 M3.
unfold sub_typ; auto.
Qed.

(* subsumption: generalizes typ_conv *)
Lemma typ_subsumption : forall e M T T',
  typ e M T ->
  sub_typ e T T' ->
  T <> kind ->
  typ e M T'.
Proof.
unfold typ, sub_typ; simpl; intros; auto.
destruct T' as [(T',T'm)|]; simpl in *; trivial; auto.
destruct T as [(T,Tm)|]; simpl in *; auto.
elim H1; trivial.
Qed.

Lemma sub_refl' : forall e M M',
  eq_typ' e M M' -> sub_typ' e M M'.
red; intros.
destruct H.
apply H in H0.
destruct M; destruct M'; try contradiction; trivial.
unfold el in *.
rewrite <- H0; trivial.
Qed.

Lemma sub_trans' : forall e M1 M2 M3,
  sub_typ' e M1 M2 -> sub_typ' e M2 M3 -> sub_typ' e M1 M3.
unfold sub_typ'; auto.
Qed.

Lemma typ_subsumption' : forall e M T T',
  typ e M T ->
  sub_typ' e T T' ->
  typ e M T'.
Proof.
unfold typ, sub_typ'; simpl; intros; auto.
Qed.

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

End R.

Hint Resolve in_int_el.

(** Consistency *)

Lemma abstract_consistency M FF :
  FF ∈ props ->
  (forall x, ~ x ∈ FF) ->
  ~ typ List.nil M (Prod prop (Ref 0)).
unfold typ; red; intros.
assert (val_ok List.nil (V.nil props)).
 red; simpl; intros.
 destruct n; discriminate H2.
specialize H1 with (1:=H2); simpl in H1.
apply H0 with (app (int M (V.nil props)) FF).
apply prod_elim with (2:=H1) (3:=H).
red; auto.
Qed.

End MakeModel.

