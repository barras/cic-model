Require Import ZFskol.
Require Import Sublogic.

Definition transport {A} (P:A->Type) {x y} (e:x=y) (h:P x) : P y :=
  eq_rect _ P h _ e.

Lemma f_app A (B:A->Type) (f g:forall x, B x) x :
   f = g -> f x = g x.
destruct 1; reflexivity.
Qed.

Definition eqD {A} (P:A->Type) {x y} (e:x=y) (h1:P x) (h2:P y) : Prop :=
  transport P e h1 = h2.

Definition sig_proj1 {A B} {p q:@sig A B} (e:p=q) : proj1_sig p = proj1_sig q :=
  f_equal _ e.
Definition sig_proj2 {A B} {p q:@sig A B} (e:p=q) :
    eqD B (sig_proj1 e) (proj2_sig p) (proj2_sig q) :=
  match e with eq_refl => eq_refl end.

(** In this file, we give an attempt to build a model of IZF
   in Coq + definite description + prop-truncation
 *)
Definition isProp X := forall x y:X, x=y.

Lemma isProp_True : isProp True.
red; intros [ ] [ ]; reflexivity.
Qed.

Lemma isProp_False : isProp False.
red; intros; contradiction.
Qed.

Lemma isProp_conj (A B:Prop) :
  isProp A -> isProp B -> isProp (A/\B).
red; intros.
destruct x; destruct y.  
f_equal.
 apply H.
 apply H0.
Qed.

Lemma isProp_forall A P :
  (forall x, isProp (P x)) -> isProp (forall x:A, P x).
Admitted.  

Lemma isProp_iff {A B:Prop} : isProp A -> isProp B -> isProp (A<->B).
intros.
apply isProp_conj; apply isProp_forall; trivial.
Qed.

Lemma is_prop_uip A (x y:A) :
  isProp A -> isProp (x=y).
red; intros.
assert (K : forall (r : x = y), r = eq_trans (H x x) (eq_sym (H y x))).
 intro r; destruct r.
 destruct (H x x); reflexivity.
eapply eq_trans;[|symmetry];apply K.
Qed.

Lemma isProp_isProp A : isProp (isProp A).
red; intros.
apply isProp_forall; intros a.
apply isProp_forall; intros a'.
apply is_prop_uip; trivial.
Qed.

Lemma sig_intro {A P} (p q:@sig A P) :
  (forall a, isProp (P a)) ->
  proj1_sig p = proj1_sig q ->
  p = q.
destruct p as (p,p'); destruct q as (q,q'); simpl; intros.
subst q.
f_equal.
apply H.
Defined.

Lemma sig_intro_proj1 {A P} (p q:@sig A P) Pp e :
 sig_proj1 (sig_intro p q Pp e) = e.
unfold sig_intro; simpl.
destruct p; destruct q; simpl in *.
revert p0; destruct e; simpl; intros.
destruct (Pp x p p0).
reflexivity.
Qed.
Lemma sig_proj1_intro {A} {P:A->Prop} Pp
      {p q:@sig A P} (e:p=q) :
  e = sig_intro p q Pp (sig_proj1 e).
destruct e.
simpl.
unfold sig_intro.
destruct p as (p,t); simpl.
replace (Pp p t t) with (eq_refl t); trivial.
apply is_prop_uip; trivial.
Qed.

Lemma isProp_sig :
  forall {A} {P:A->Prop}, (forall a, isProp (P a)) ->
  (forall a a', P a -> P a' -> a=a') ->
  isProp {x:A | P x}.
red; intros.
apply sig_intro; auto.
apply H0; apply proj2_sig.
Qed.

Definition isSet X :=
  forall (x y:X) (p q:x=y), p=q.

Lemma isSet_prop A :
  isProp A -> isSet A.
red; intros.
apply is_prop_uip; trivial.
Qed.

Lemma isSet_sig X (R:X->Prop) :
   isSet X -> (forall x, isProp (R x)) -> isSet (@sig X R).
red; intros.
assert (forall e:x=y, e = sig_intro x y H0 (sig_proj1 e)).
 destruct e.
 simpl.
 unfold sig_intro.
 destruct x; simpl.
 replace (H0 x r r) with (eq_refl r); trivial.
 apply is_prop_uip; trivial.
rewrite (H1 p), (H1 q).
f_equal.
apply H. 
Qed.

(** Prop-truncation *)
Definition tr X := forall P:Prop, isProp P -> (X->P) -> P.
Lemma tr_prop X : isProp (tr X).
apply isProp_forall; intros P.
apply isProp_forall; intros Pp.
apply isProp_forall; trivial.
Qed.
Definition tr_i {X} (x:X) : tr X := fun _ _ f => f x.
(*Definition tr_ind_nodep {X P} (Pp:isProp P) (h:X->P) (t:tr X) : P :=
  t P Pp h.*)

(*Parameter tr : Type -> Prop.
Parameter tr_prop : forall X, isProp (tr X).
Parameter tr_i : forall {X}, X -> tr X.*)
Parameter tr_ind_nodep : forall {X P},
  isProp P -> (X->P) -> tr X -> P.

Lemma tr_elim : forall {P},
  isProp P -> tr P -> P.
intros.
apply @tr_ind_nodep with (X:=P); trivial.
Qed.

Lemma tr_ind {X} (P : tr X -> Type) :
    (forall x, isProp (P x)) ->
    (forall x, P (tr_i x)) ->
    forall x:tr X, P x.
intros Pp h t.
elim t using tr_ind_nodep; trivial.
intros x.
replace t with (tr_i x); trivial.
apply tr_prop.
Qed.

Lemma tr_ind_eq {X} (P:tr X->Type) Pp h x :
  tr_ind P Pp h (tr_i x) = h x.
intros.
apply Pp.
Qed.

Definition tr_ind_tr {X} (P : Type)
           (h:forall x, tr P) (x:tr X) : tr P :=
  tr_ind (fun x => tr P) (fun x => tr_prop _) h x.

           
Module trSub <: ConsistentSublogic.
  Definition Tr := fun P:Prop => tr P.
  Definition TrI (P:Prop) (p:P) : Tr P := tr_i p.
  Definition TrP (P:Prop) (p:Tr (Tr P)) : Tr P :=
    tr_ind_tr P (fun x:Tr P=>x) p.
  Definition TrMono (P Q:Prop) (f:P->Q) (p:Tr P) : Tr Q :=
    tr_ind_tr Q (fun x => tr_i (f x)) p.
  Notation "# T" := (Tr T).
  Definition TrCons : ~ Tr False :=
    fun p => tr_ind (fun _ => False) (fun _ => isProp_False) (fun x=>x) p.
End trSub.
Module TrSubThms <: SublogicTheory := BuildConsistentSublogic trSub.
Import trSub TrSubThms.
Lemma isL_tr : forall P, isL (tr P).
red; intros.
apply tr_ind_tr with (2:=H); trivial.
Qed.
Hint Resolve isL_tr.

Lemma descr :
  forall {A} {P:A->Prop}, (forall a, isProp (P a)) ->
  (forall a a', P a -> P a' -> a=a') ->
  (tr {a:A | P a}) -> {a:A | P a}.
intros.
elim H1 using tr_ind; trivial.
intros.
apply isProp_sig; trivial.
Qed.

Lemma descr_eq A (P:A->Prop) (Pp:forall a, isProp(P a))
      (uniq : forall a a', P a -> P a' -> a=a')
      (w:tr{a|P a}) (x:A) (px : P x) :
  proj1_sig (descr Pp uniq w) = x.
apply uniq; trivial.
exact (proj2_sig (descr Pp uniq w)).
Qed.


(** Predicate extensionality: consequence of univalence *)
Parameter pred_ext :
  forall {A} {P Q:A->Prop},
  (forall a, isProp (P a)) ->
  (forall a, isProp (Q a)) ->
  (forall a, P a <-> Q a) ->
  P = Q.
(*
Lemma isProp_forall' A (P:A->Prop) :
  (forall x, isProp (P x)) -> isProp (forall x:A, P x).
red; intros.
assert (P = fun _ => True).
 apply pred_ext; auto.
 red; intros.
 destruct x0; destruct y0; reflexivity.
 split; trivial.
 generalize x y.
rewrite H0. 
intros.
*)

Definition pred_eqv {A} {P Q:A->Prop} (e:P=Q) a : P a <-> Q a.
Proof conj (fun x => match e in _=X return X a with eq_refl => x end)
           (fun x => match eq_sym e in _=X return X a with eq_refl => x end).

(* Version of pred_ext that returns the reflexivity when
   given the identity equivalence, so it is the inverse of pred_eqv *)
Definition pred_ext' {A} {P Q:A->Prop}
  (Pp : forall a, isProp (P a)) (Qp : forall a, isProp (Q a))
  (e:forall a, P a <-> Q a) : P=Q :=
  eq_trans (eq_sym (pred_ext Pp Pp (pred_eqv eq_refl)))
           (pred_ext Pp Qp e).

Definition pred_eqv_ext {A} {P Q:A->Prop}
           (Pp : forall a, isProp (P a)) (Qp : forall a, isProp (Q a))
           (w:P=Q) :
  pred_ext' Pp Qp (pred_eqv w) = w.
revert Qp; destruct w.
simpl; intros.  
unfold pred_ext'.
replace Qp with Pp.
2:apply isProp_forall; intros; apply isProp_isProp.
destruct (pred_ext Pp Pp (pred_eqv eq_refl)); reflexivity.
Qed.

Lemma isProp_pred_eq {A} {P Q:A->Prop} :
  (forall a, isProp (P a)) ->
  (forall a, isProp (Q a)) ->
  isProp (P=Q).
intros Pp Qp e1 e2.  
rewrite <-(pred_eqv_ext Pp Qp e1), <-(pred_eqv_ext Pp Qp e2).
apply f_equal with (f:=pred_ext' Pp Qp).
apply isProp_forall; intros a.
apply isProp_iff; trivial.
Qed.

(** Quotient *)

Require Import Setoid.

Class isClass {X} (R:X->X->Prop) (P:X->Prop) := mkCl {
  cl_prop : forall x, isProp (P x);
  wit : X;
  wit_ok : P wit;
  uniq :  forall y, P y <-> R wit y
}.
 
Class isRel {X} (R:X->X->Prop) := {
  isP : forall x y, isProp (R x y);
  isR :> Equivalence R
  }.


Instance isClass_eq {X} {R:X->X->Prop} (Rr:isRel R) x :
  isClass R (fun y => R x y).
exists x; intros; auto with *.
 apply isP.
Qed.

                                         
Definition quo (X:Type) (R:X->X->Prop) :=
  { P : X->Prop | tr (isClass R P) }.

Lemma isProp_quo_proj1 {X R} (x:quo X R) (z:X) :
  isProp (proj1_sig x z).
destruct x as (x,clx); simpl.
elim clx using tr_ind; intros.  
 apply isProp_isProp.

 apply x0.
Qed.

Lemma quo_proj1_wit {X R} (q:quo X R) :
  tr {x | proj1_sig q x}.
destruct q as (x,clx); simpl.
elim clx using tr_ind; intros.  
 apply tr_prop.

 apply tr_i.
 exists wit.
 apply x0.
Qed.

Lemma quo_ext X R (Rr:isRel  R) (q1 q2:quo X R) :
  (forall x, proj1_sig q1 x <-> proj1_sig q2 x) ->
  q1 = q2.
intros.
apply sig_intro.
 intros.
 apply tr_prop.

 apply pred_ext; trivial.
  apply isProp_quo_proj1.
  apply isProp_quo_proj1.
Qed.

Lemma isSet_quo X (R:X->X->Prop) (Rr:isRel R) : isSet (quo X R).
red; intros.
rewrite (sig_proj1_intro (fun _ => tr_prop _) p).
rewrite (sig_proj1_intro (fun _ => tr_prop _) q).
f_equal.
apply isProp_pred_eq; apply isProp_quo_proj1.
Qed.


Definition quo_i {X} {R:X->X->Prop} (Rr:isRel R) (x:X) : quo X R :=
  exist (fun P => tr(isClass R P))
    (fun y => R x y)
    (tr_i (isClass_eq Rr x)).

Lemma quo_i_eq {X R} (Rr:isRel  R) {x y:X} :
  quo_i _ x = quo_i _ y <-> R x y.
split.
 intros.
 apply sig_proj1 in H; simpl in H.
 apply f_app with (x:=y) in H.
 rewrite H; reflexivity.

 intros; apply quo_ext; simpl; intros; trivial.
 rewrite H; reflexivity.
Qed.

Lemma class_quo_proj1 X R (Rr:isRel R) (q:quo X R) w :
  proj1_sig q w <-> q = quo_i _ w.
split; intros.
 apply quo_ext; trivial.
 intros; simpl.
 assert (Pp := isProp_quo_proj1 q).
 destruct q as (P,Pc); simpl in *.
 elim Pc using tr_ind; intros.
  apply isProp_iff; auto.
  apply Rr.
 destruct x0 as (_,w',_,eqvP).
 rewrite eqvP in H|-*.
 rewrite H; reflexivity.

 subst q; simpl.
 reflexivity.
Qed.

Lemma quo_ind {X} {R:X->X->Prop} (Rr:isRel R) (P:quo X R->Type):
  (forall x, isProp (P x)) ->
  (forall (x:X), P (quo_i Rr x)) ->
  forall x:quo X R, P x.
intros Pp h x.
assert (w := quo_proj1_wit x).
elim w using tr_ind; auto.
clear w; intros (w,wdef).
rewrite class_quo_proj1 with (Rr:=Rr) in wdef.
rewrite wdef; trivial.
Qed.

Lemma quo_ind_eq {X} {R:X->X->Prop} {Rr:isRel R} {P:quo X R->Type} Pp h (x:X) :
  quo_ind _ P Pp h (quo_i _ x) = h x.
apply Pp.
Qed.

Section QuotientSetInduction.
  Variable X : Type.
  Variable R : X->X->Prop.
  Variable Rr : isRel R.
  Variable P : quo X R -> Type.
  Variable Ps : forall x, isSet (P x).
  Variable h : forall (x:X), P (quo_i _ x).
  Variable hcomp :
    forall x y (r:R x y), eqD P (proj2 (quo_i_eq _) r) (h x) (h y).

  Let img x p := {x':X & { e: quo_i _ x' = x | eqD P e (h x') p}}.

  Lemma img_ex q : img (quo_i Rr q) (h q).
exists q.
exists (eq_refl (quo_i _ q)).    
reflexivity.
Defined.

  Lemma img_uniq q (p p':P q) : img q p -> img q p' -> p = p'.
intros (x0,(eqx0,imgx0)) (x1,(eqx1,imgx1)).
rewrite <- imgx0, <- imgx1.
clear imgx0 imgx1.
revert eqx0; destruct eqx1.
simpl; intros.
assert (R x0 x1).
 apply quo_i_eq in eqx0; trivial.
replace eqx0 with (proj2 (quo_i_eq _) H).
 apply hcomp.

 apply isSet_quo; trivial.
Qed.

  Lemma img_uniq_tr q (p p':P q) : tr (img q p) -> tr (img q p') -> p=p'.
intros.
elim H using tr_ind; intros.
 red; intros; apply Ps.
elim H0 using tr_ind; intros.
 red; intros; apply Ps.
apply img_uniq; trivial.
Qed.

  Let imgP x := tr { p:P x | tr (img x p) }.

  Lemma quo_imgP (q:quo X R) : imgP q.
elim q using (quo_ind Rr).
 intros; apply tr_prop.
intros.
apply tr_i; exists (h x).
apply tr_i; apply img_ex.
Qed.
 
 Lemma quo_ind_set (q:quo X R) : P q.
assert (p' := quo_imgP q).
apply descr in p'.
 exact (proj1_sig p'). 

 intros; apply tr_prop.

 apply img_uniq_tr.
Defined.

 Lemma quo_ind_set_eq (x:X) :
  quo_ind_set (quo_i _ x) = h x.
unfold quo_ind_set.
apply descr_eq.
apply tr_i; apply img_ex.
Qed.

End QuotientSetInduction.

 Lemma quo_ind_set_nodep {X} {R:X->X->Prop} (Rr:isRel R) {P:Type}:
  isSet P ->
  forall h:X->P,
  (forall x y (r:R x y), h x = h y) ->
  quo X R -> P.
intros.
apply quo_ind_set with (Rr:=Rr) (P:=fun _ => P) (h:=h); trivial.
intros.
destruct (proj2 (quo_i_eq _) r); simpl; auto.
apply H0; trivial.
Defined.

Hint Resolve tr_prop isProp_forall isProp_conj isProp_iff.

Lemma tr_ex_sig {A} {P:A->Prop} :
  (#exists x, P x) <-> tr{x|P x}.
split; intros h; elim h using tr_ind; intros; auto.
 destruct x; apply tr_i; eauto.
 destruct x; apply tr_i; eauto.
Qed.

(* Set-truncation form Prop-truncation + quotients *)

Definition tr0 X := quo X (fun x y => tr(x=y)). 

Instance isRel_treq {X} : isRel (fun x y:X => tr(x=y)).
split; auto.
split ;red; intros.
 apply tr_i; reflexivity.

 elim H using tr_ind; intros; auto.
 apply tr_i; symmetry; trivial.

 elim H using tr_ind; intros; auto.
 elim H0 using tr_ind; intros; auto.
 apply tr_i; transitivity y; trivial.
Qed.

Definition tr0_i {X} (x:X) : tr0 X := quo_i _ x.

Definition tr0_ind_set {X} (P:tr0 X->Type) :
  (forall x, isSet (P x)) ->
  (forall x:X, P (tr0_i x)) ->
  forall x', P x'.
intros.
apply (quo_ind_set _ _ _) with (h:=X0); trivial.
red.
intros.
elim r using tr_ind.
 red; intros; apply H.

 clear r; intros e.
 destruct e.
 assert (proj2 (quo_i_eq _) (tr_i (eq_refl x)) = eq_refl (quo_i _ x)).
  apply isSet_quo; auto with *.
 rewrite H0; reflexivity.
Defined.

Lemma tr0_ind_set_eq {X} (P:tr0 X->Type)
  (Pp:forall x, isSet (P x))
  (h:forall x:X, P (tr0_i x)) (x:X) :
  tr0_ind_set P Pp h (tr0_i x) = h x.
unfold tr0_ind_set.
apply quo_ind_set_eq.
Qed.

(** * The type of sets *)
Module S.

(* The level of indexes *)
Definition Ti := Type.

Inductive set : Type :=
  sup (X:Ti) (f:X->set).


Definition idx (x:set) := let (X,_) := x in X.
Definition elts (x:set) : idx x -> set :=
  match x return idx x -> set with
  | sup X f => f
  end.

Fixpoint eq_set (x y:set) {struct x} :=
  (forall i, #exists j, eq_set (elts x i) (elts y j)) /\
  (forall j, #exists i, eq_set (elts x i) (elts y j)).

Lemma isProp_eq_set x y : isProp (eq_set x y).
destruct x; simpl; intros.
apply isProp_conj.
 apply isProp_forall; intros i; apply tr_prop.
 apply isProp_forall; intros i; apply tr_prop.
Qed.

Lemma eq_set_refl : forall x, eq_set x x.
induction x; simpl.
split; intros; apply tr_i.
 exists i; trivial.
 exists j; trivial.
Qed.

Lemma eq_set_sym : forall x y, eq_set x y -> eq_set y x.
induction x; destruct y; simpl; intros.
destruct H0.
split; intros.
 elim (H1 i) using tr_ind_tr; intros (?,?).
 apply tr_i.
 exists x; auto.

 elim (H0 j) using tr_ind_tr; intros (?,?).
 apply tr_i; exists x; auto.
Qed.

Lemma eq_set_trans : forall x y z,
  eq_set x y -> eq_set y z -> eq_set x z.
induction x; destruct y; destruct z; simpl; intros.
destruct H0.
destruct H1.
split; intros.
 elim (H0 i) using tr_ind_tr; intros (?,?).
 elim (H1 x) using tr_ind_tr; intros (?,?).
 apply tr_i; exists x0; eauto.

 elim (H3 j) using tr_ind_tr; intros (?,?).
 elim (H2 x) using tr_ind_tr; intros (?,?).
 apply tr_i; exists x0; eauto.
Qed.


Lemma eq_set_def : forall x y,
  (forall i, #exists j, eq_set (elts x i) (elts y j)) ->
  (forall j, #exists i, eq_set (elts x i) (elts y j)) ->
  eq_set x y.
destruct x; simpl; auto.
Qed.

Definition in_set x y :=
  #exists j, eq_set x (elts y j).


Lemma in_set_ind P x y :
  isProp P ->
  (forall j, eq_set x (elts y j) -> P) ->
  in_set x y -> P.
intros.
apply (proj1 tr_ex_sig) in H0.
elim H0 using tr_ind; auto.  
destruct 1; intros; eauto.
Qed.

Lemma isProp_in_set x y : isProp (in_set x y).
apply tr_prop.
Qed.

  Definition incl_set x y := forall z, in_set z x -> in_set z y.

Lemma isProp_incl_set x y : isProp (incl_set x y).
apply isProp_forall; intros.
apply isProp_forall; intros.
auto.
apply tr_prop.
Qed.
Hint Resolve isProp_eq_set isProp_incl_set isProp_in_set tr_prop.


Lemma eq_elim0 x y i :
  eq_set x y ->
  in_set (elts x i) y.
destruct x; simpl; intros.
destruct H.
red; auto.
Qed.

Lemma eq_set_ax : forall x y,
  eq_set x y <-> (forall z, in_set z x <-> in_set z y).
unfold in_set; split; intros.
 split; intros h; Tdestruct h.
  elim (eq_elim0 x y x0) using in_set_ind; intros; auto.
  Texists j; apply eq_set_trans with (elts x x0); trivial.

  apply eq_set_sym in H.
  elim (eq_elim0 y x x0) using in_set_ind; intros; auto.
  Texists j; apply eq_set_trans with (elts y x0); trivial.

  apply eq_set_def; intros.
   apply H.
   Texists i; apply eq_set_refl.

   destruct (H (elts y j)).
   elim H1 using in_set_ind; intros; auto.
    Texists j0; apply eq_set_sym; trivial.

    Texists j; apply eq_set_refl.
Qed.

Definition elts' (x:set) (i:idx x) : {y|in_set y x}.
exists (elts x i).
abstract (apply tr_i; exists i; apply eq_set_refl).
Defined.

Lemma in_reg : forall x x' y,
  eq_set x x' -> in_set x y -> in_set x' y.
intros.
elim H0 using in_set_ind; intros; auto.
apply tr_i; exists j.
apply eq_set_trans with x; trivial.
apply eq_set_sym; trivial.
Qed.

Lemma eq_intro : forall x y,
  (forall z, in_set z x -> in_set z y) ->
  (forall z, in_set z y -> in_set z x) ->
  eq_set x y.
intros.
rewrite eq_set_ax.
split; intros; eauto.
Qed.

Lemma eq_elim : forall x y y',
  in_set x y ->
  eq_set y y' ->
  in_set x y'.
intros.
rewrite eq_set_ax in H0.
destruct (H0 x); auto.
Qed.


  Lemma wf_ax :
  forall (P:set->Prop),
  (forall x, isProp (P x)) ->
  (forall x, (forall y, in_set y x -> P y) -> P x) -> forall x, P x.
intros P Pp H x.
cut (forall x', eq_set x x' -> P x');[auto using eq_set_refl|].
induction x; intros.
apply H; intros.
assert (in_set y (sup X f)).
 apply eq_elim with x'; trivial.
 apply eq_set_sym; trivial.
clear H1 H2.
elim H3 using in_set_ind; intros; auto.
apply eq_set_sym in H1; eauto.
Qed.


Definition empty :=
  sup False (fun x => match x with end).

Lemma empty_ax : forall x, ~ in_set x empty.
red; intros.
elim H using in_set_ind; intros.
 apply isProp_False.
contradiction.
Qed.

Definition singl x := sup unit (fun _ => x).

Definition pair_spec (a b:set->Prop) (x:set) : Prop :=
  forall z, in_set z x <-> #(a z \/ b z).

Definition pair x y :=
  sup bool (fun b => if b then x else y).

Lemma pair_spec_intro a b :
  pair_spec (fun a' => eq_set a' a) (fun b' => eq_set b' b) (pair a b).
intros z.
unfold pair; simpl.
split; intros.
 elim H using in_set_ind; intros; auto.
 apply tr_i.
 destruct j; auto.

 elim H using tr_ind; intros; auto.
 destruct x.
  apply tr_i; exists true; trivial.
  apply tr_i; exists false; trivial.
Qed.

Lemma pair_ax : forall a b z,
  in_set z (pair a b) <-> #(eq_set z a \/ eq_set z b).
Proof pair_spec_intro.


Lemma pair_morph :
  forall a a', eq_set a a' -> forall b b', eq_set b b' ->
  eq_set (pair a b) (pair a' b').
unfold pair.
simpl; intros.
split; intros.
 apply tr_i; exists i; destruct i; trivial.
 apply tr_i; exists j; destruct j; trivial.
Qed.

Definition subset_spec (x:set) (P:set->Prop) (y:set) :=
  forall z,
  in_set z y <->
  in_set z x /\ # (exists2 z', eq_set z z' & P z').

Definition subset (x:set) (P:set->Prop) :=
  sup {a|exists2 x', eq_set (elts x a) x' & P x'}
    (fun y => elts x (proj1_sig y)).

Lemma subset_ax : forall x P, subset_spec x P (subset x P).
red.
unfold subset; simpl.
split; intros.
 elim H using in_set_ind; simpl; intros; auto.
 clear H; destruct j as (j,?); simpl in H0.
 split.
  apply tr_i; exists j; trivial.

  destruct e.
  apply tr_i; exists x0; trivial.
  apply eq_set_trans with (elts x j); trivial.

 destruct H.
 elim H using in_set_ind; auto.
 clear H; intros.
 elim H0 using tr_ind; intros; auto.
 destruct x0.
 assert (exists2 x', eq_set (elts x j) x' & P x').
  exists x0; trivial.
  apply eq_set_trans with z; trivial.
  apply eq_set_sym; trivial.
 apply tr_i; exists
  (@exist _ (fun a=>exists2 x',eq_set (elts x a) x' & P x')
    j H3); simpl; trivial.
Qed.

Definition power (x:set) :=
  sup (idx x->Prop)
   (fun P => subset x (fun y => exists2 i, eq_set y (elts x i) & P i)).

Lemma power_ax : forall x z,
  in_set z (power x) <->
  (forall y, in_set y z -> in_set y x).
unfold power; simpl; intros.
split; intros.
 elim H using in_set_ind; intros; auto.
 simpl in *.
 specialize eq_elim with (1:=H0)(2:=H1); intro.
 apply (proj1 (proj1 (subset_ax _ _ _) H2)).

 apply tr_i; exists (fun i => in_set (elts x i) z); simpl.
 apply eq_intro; intros.
  apply (fun x P z => proj2 (subset_ax x P z)).
  split; auto.
  elim H with z0 using in_set_ind; trivial; intros.
  Texists z0.
   apply eq_set_refl.

   exists j; trivial.
   apply in_reg with z0; trivial.

  elim (proj2 (proj1 (subset_ax _ _ _) H0)) using tr_ind; intros; auto.
  destruct x0 as (z', ?, (i,?,?)).
  apply in_reg with (elts x i); trivial.
  apply eq_set_sym; apply eq_set_trans with z'; trivial.
Qed.

Lemma power_morph : forall x y,
  eq_set x y -> eq_set (power x) (power y).
intros.
apply eq_intro; intros.
 rewrite power_ax in H0|-*; intros.
 apply eq_elim with x; auto.

 apply eq_set_sym in H.
 rewrite power_ax in H0|-*; intros.
 apply eq_elim with y; auto.
Qed.

  
 Definition union (x:set) :=
  sup {i:idx x & idx (elts x i)}
    (fun p => elts (elts x (projS1 p)) (projS2 p)).

Lemma union_ax : forall a z,
  in_set z (union a) <-> #exists2 b, in_set z b & in_set b a.
unfold in_set at 1, union; simpl; intros.
split; intros.
 Tdestruct H.
 Texists (elts a (projT1 x)).
  Texists (projT2 x); trivial.
  Texists (projT1 x); apply eq_set_refl.

 Tdestruct H.
 Tdestruct H0.
 assert (in_set z (elts a x0)).
  apply eq_elim with x; trivial.
 Tdestruct H1.
 Texists (existT (fun i=>idx(elts a i)) x0 x1); simpl.
 trivial.
Qed.

Lemma union_morph :
  forall a a', eq_set a a' -> eq_set (union a) (union a').
intros.
apply eq_set_ax; intros z.
rewrite union_ax.
rewrite union_ax.
split; intros h; Tdestruct h as (b,?,?); Texists b; trivial.
 apply eq_elim with a; trivial.
 apply eq_elim with a'; trivial.
 apply eq_set_sym; trivial.
Qed.


Fixpoint num (n:nat) : set :=
  match n with
  | 0 => empty
  | S k => union (pair (num k) (pair (num k) (num k)))
  end.

Definition infinity := sup _ num.

Lemma infty_ax1 : in_set empty infinity.
 Texists 0.
 unfold elts, infinity, num.
 apply eq_set_refl.
Qed.

Lemma infty_ax2 : forall x, in_set x infinity ->
  in_set (union (pair x (pair x x))) infinity.
intros.
elim H using in_set_ind; intros; auto.
Texists (S j).
simpl elts.
apply union_morph.
apply pair_morph; trivial.
apply pair_morph; trivial.
Qed.

Definition replf (x:set) (F:set->set) :=
  sup _ (fun i => F (elts x i)).

Lemma replf_ax : forall x F z,
  (forall z z', in_set z x ->
   eq_set z z' -> eq_set (F z) (F z')) ->
  (in_set z (replf x F) <->
   #exists2 y, in_set y x & eq_set z (F y)).
unfold replf; simpl; intros.
split; intros.
 elim H0 using in_set_ind; intros; auto.
 simpl in *.
 Texists (elts x j); trivial.
 Texists j; apply eq_set_refl.

 elim H0 using tr_ind; intros; auto.
 destruct x0 as (x',?,?).
 elim H1 using in_set_ind; intros; auto.
 Texists j; simpl.
 apply eq_set_trans with (F x'); trivial.
 apply eq_set_sym.
 apply H.
  Texists j; apply eq_set_refl.
  apply eq_set_sym; trivial.
Qed.

End S.


Hint Resolve S.isProp_eq_set S.isProp_incl_set S.isProp_in_set.

Instance Tr_morph : Proper (iff ==> iff) Tr. 
do 2 red; intros.
split; apply TrMono; apply H.
Qed.


Module IZF_R <: IZF_R_sig TrSubThms.
(*Module IZF_R <: IZF_R_Ex_sig CoqSublogicThms.*)

Definition set := quo S.set S.eq_set.
Definition eq_set := @eq set.

Instance isRel_eqset : isRel S.eq_set.
split; intros; auto.
split; red; intros.
 apply S.eq_set_refl.

 apply S.eq_set_sym; trivial.  

 apply S.eq_set_trans with y; trivial.  
Qed.

Lemma isSet_set : isSet set.
apply isSet_quo; auto with *.
Qed.

Lemma isProp_eq x y : isProp (eq_set x y).
red; intros; apply isSet_set.
Qed.
Global Hint Resolve isProp_eq.

Definition qset_set (q:set) (x:S.set) : Prop :=
  q = quo_i _ x.

Lemma qset_set_eq (x:S.set) :
  qset_set (quo_i _ x) = S.eq_set x.
unfold qset_set.
apply pred_ext; intros; auto.
apply quo_i_eq.
Qed.

(*
Definition is_set (P:set->Prop) := tr (isClass eq_set P).
Definition mk_qset (P:set->Prop) (Ps:is_set P) : qset :=
  exist is_set P Ps.
*)

Definition in_set (x y:set) :=
  tr { x' | x = quo_i _ x' /\ tr{ y' | y = quo_i _ y' /\ S.in_set x' y'}}.

Lemma isProp_in x y : isProp (in_set x y).
apply tr_prop.
Qed.
Global Hint Resolve isProp_in.

Lemma in_set_ind P x y :
  isProp P ->
  (forall x' y', x = quo_i _ x' -> y = quo_i _ y' -> S.in_set x' y' -> P) ->
  in_set x y -> P.
intros.
elim H0 using tr_ind; auto.
clear H0.
destruct 1 as (x', (?,?)).
elim H1 using tr_ind; auto.
clear H1.
destruct 1 as (y',(?,?)).
eauto.
Qed.

Lemma in_set_eqv x y :
  in_set (quo_i _ x) (quo_i _ y) <-> S.in_set x y.
split; intros.
 elim H using in_set_ind; intros; auto.
 apply quo_i_eq in H0.
 apply quo_i_eq in H1.
 apply S.eq_elim with y'; trivial.
  apply S.in_reg with x'; trivial.
  apply S.eq_set_sym; trivial.
  apply S.eq_set_sym; trivial.

 apply tr_i; exists x; split; trivial.
 apply tr_i; exists y; split; trivial.
Qed.


Lemma eq_set_ax : forall x y,
  eq_set x y <-> (forall z, in_set z x <-> in_set z y).
unfold eq_set.
split; intros.
 subst y; auto with *.

 revert H.
 elim x using (quo_ind _); auto.
 clear x; intros x.
 elim y using (quo_ind _); auto.
 clear y; intros y.
 intros.
 apply quo_i_eq.
 apply S.eq_set_ax; intros.
 do 2 rewrite <- in_set_eqv.
 apply H.
Qed.

Lemma in_reg : forall x x' y,
  eq_set x x' -> in_set x y -> in_set x' y.
unfold eq_set; intros; subst; trivial.
Qed.

(* Set induction *)
(*
Lemma isProp_Acc X (R:X->X->Prop) x : isProp (Acc R x).
red; revert x; fix 2.
intros x a a'.
destruct a; destruct a'.
assert (Hrec := fun y r => isProp_Acc y (a y r)).
clear isProp_Acc.
f_equal.
apply isProp_forall; intros y.
apply isProp_forall; intros r.
red; intros.
 transitivity (a y r); auto.
Qed.
  
Lemma Acc_in_set : forall x, Acc in_set x.
cut (forall x y, eq_set x y -> Acc in_set y).
 intros.
 apply H with x; apply eq_set_refl.
induction x; intros.
constructor; intros.
specialize eq_elim with (1:=H1)(2:=eq_set_sym _ _ H0); intro.
clear y H0 H1.
elim H2 using tr_ind; intros.
 apply isProp_Acc.
destruct x; simpl in *.
apply H with x.
apply eq_set_sym; trivial.
Qed.


Lemma wf_rec :
  forall P : set -> Type,
  (forall x, (forall y, in_set y x -> P y) -> P x) -> forall x, P x.
intros.
elim (Acc_in_set x); intros.
apply X; apply X0.
Defined.
*)


  Lemma wf_ax0 :
  forall (P:set->Prop),
  (forall x, isProp (P x)) ->
  (forall x, (forall y, in_set y x -> P y) -> P x) -> forall x, P x.
intros P Pp H x.
elim x using (quo_ind _); auto.
clear x; intros x.
elim x using S.wf_ax; auto.
intros y Hy.
apply H.
intros z.
elim z using (quo_ind _); auto.
clear z; intros z ?.
apply in_set_eqv in H0.
auto.
Qed.

  Lemma wf_ax :
  forall (P:set->Prop),
  (forall x, (forall y, in_set y x -> #(P y)) -> #(P x)) -> forall x, #(P x).
intros.
apply wf_ax0 with (P:=fun x => #P x); auto.
Qed.

(*  Lemma wf_ax :
  forall (P:set->Prop),
  (forall x, isL (P x)) -> (* ! *)
  (forall x, (forall y, in_set y x -> P y) -> P x) -> forall x, P x.
Admitted.
*)
(* *)

Definition empty := quo_i _ S.empty.

Lemma empty_ax0 : forall x, ~ in_set x empty.
red; intros.
elim H using in_set_ind; auto.
 apply isProp_False.
intros x' y' _ mtdef inmt.
apply quo_i_eq in mtdef.
apply S.eq_elim with (2:=S.eq_set_sym _ _ mtdef) in inmt.
apply S.empty_ax in inmt; trivial.
Qed.

Lemma empty_ax : forall x, in_set x empty -> #False.
intros.
apply tr_i; apply empty_ax0 in H; trivial.
Qed.

Definition pair (a b:set) : set.
pose (h := fun a b => quo_i _ (S.pair a b)).
assert (forall a x y, S.eq_set x y -> h a x = h a y).
 intros.
 unfold h.
 apply quo_i_eq.
 apply S.pair_morph; trivial.
 reflexivity.
pose (qh := fun a => quo_ind_set_nodep _ isSet_set (h a) (H a) b).
apply quo_ind_set_nodep with (1:=_) (h0:=qh) (4:=a).
 exact isSet_set.
intros.
unfold qh.
elim b using (quo_ind _).
 red; intros.
 apply isSet_set.
intros.
unfold quo_ind_set_nodep.
rewrite quo_ind_set_eq.
rewrite quo_ind_set_eq.
unfold h.
apply quo_i_eq.
apply S.pair_morph; trivial.
apply S.eq_set_refl.
Defined.

Lemma pair_eq a b:
  pair (quo_i _ a) (quo_i _ b) = quo_i _ (S.pair a b).
unfold pair.
unfold quo_ind_set_nodep.
eapply transitivity.
match goal with
    |- context[quo_ind_set ?X ?R ?Rr ?P ?Ps ?h ?hcomp (quo_i ?Rr ?x)] =>
  apply (quo_ind_set_eq X R Rr P Ps h hcomp x)
end.
match goal with
    |- context[quo_ind_set ?X ?R ?Rr ?P ?Ps ?h ?hcomp (quo_i ?Rr ?x)] =>
  apply (quo_ind_set_eq X R Rr P Ps h hcomp x)
end.
Qed.

Lemma pair_ax : forall a b z,
  in_set z (pair a b) <-> #(z=a \/ z=b).
intros.
elim a using (quo_ind _); auto.
clear a; intros a.
elim b using (quo_ind _); auto.
clear b; intros b.
elim z using (quo_ind _); auto.
clear z; intros z.
rewrite pair_eq.
rewrite in_set_eqv.
rewrite S.pair_ax.
split; apply TrMono; (destruct 1;[left|right]); try apply quo_i_eq; trivial.
 apply quo_i_eq in H; trivial.
 apply quo_i_eq in H; trivial.
Qed.
Print Assumptions pair_ax.

Definition union (a:set) : set.
pose (h := fun a => quo_i _ (S.union a)).
apply quo_ind_set_nodep with (1:=_) (h0:=h) (4:=a).
 exact isSet_set.
unfold h; intros.
apply quo_i_eq.
apply S.union_morph; trivial.
Defined.

Lemma union_eq a:
  union (quo_i _ a) = quo_i _ (S.union a).
unfold union.
unfold quo_ind_set_nodep.
rewrite quo_ind_set_eq.
reflexivity.
Qed.

Lemma union_ax : forall a z,
  in_set z (union a) <-> #exists2 b, in_set z b & in_set b a.
intros.
elim a using (quo_ind _); auto.
clear a; intros a.
elim z using (quo_ind _); auto.
clear z; intros z.
rewrite union_eq.
rewrite in_set_eqv.
rewrite S.union_ax.
split.
 apply TrMono.
 destruct 1 as (b,?,?); exists (quo_i _ b).
  apply in_set_eqv; trivial.
  apply in_set_eqv; trivial.

 intros h.
 Tdestruct h as (b,?,?).
 revert H H0.
 elim b using (quo_ind _); auto.
 clear b; intros b ? ?.
 Texists b.
  apply in_set_eqv; trivial.
  apply in_set_eqv; trivial.
Qed.

Definition subset (a:set) (P:set->Prop) : set.
pose (P' z := P (quo_i _ z)).
pose (h := fun a => quo_i _ (S.subset a P')).
apply quo_ind_set_nodep with (1:=_) (h0:=h) (4:=a).
 exact isSet_set.
intros.
unfold h.
apply quo_i_eq.
assert (aux := S.subset_ax).
red in aux.
apply S.eq_set_ax; intros z.
do 2 rewrite aux.
apply and_iff_morphism; auto with *.
split; intros.
 apply S.eq_elim with x; trivial.
 apply S.eq_elim with y; trivial.
 apply S.eq_set_sym; trivial.
Defined.

Lemma subset_eq a P:
  subset (quo_i _ a) P = quo_i _ (S.subset a (fun z => P (quo_i _ z))).
unfold subset.
unfold quo_ind_set_nodep.
rewrite quo_ind_set_eq.
reflexivity.
Qed.

Lemma subset_ax x P z :
  in_set z (subset x P) <->
  in_set z x /\ # (exists2 z', eq_set z z' & P z').
elim x using (quo_ind _); auto.
clear x; intros x.
elim z using (quo_ind _); auto.
clear z; intros z.
rewrite subset_eq.
rewrite in_set_eqv.
assert (aux := S.subset_ax).
red in aux.
rewrite aux.
rewrite in_set_eqv.
apply and_iff_morphism; auto with *.
split.
 apply TrMono.
 destruct 1 as (b,?,?); exists (quo_i _ b); trivial.
 apply quo_i_eq; trivial.

 intros h.
 Tdestruct h as (b,?,?).
 revert H H0.
 elim b using (quo_ind _); auto.
 clear b; intros b ? ?.
 apply quo_i_eq in H.
 Texists b; trivial.
Qed.

Definition infinite := quo_i _ S.infinity.

Lemma infinity_ax1 : in_set empty infinite.
apply in_set_eqv.
apply S.infty_ax1.
Qed.

Lemma infinity_ax2 : forall x, in_set x infinite ->
  in_set (union (pair x (pair x x))) infinite.
intros x.
elim x using (quo_ind _); auto.
clear x; intros x tyx.
apply in_set_eqv in tyx.
rewrite !pair_eq, union_eq.
apply in_set_eqv.
apply S.infty_ax2; trivial.
Qed.

Definition power (a:set) : set.
pose (h := fun a => quo_i _ (S.power a)).
apply quo_ind_set_nodep with (1:=_) (h0:=h) (4:=a).
 exact isSet_set.
unfold h; intros.
apply quo_i_eq.
apply S.power_morph; trivial.
Defined.

Lemma power_eq a:
  power (quo_i _ a) = quo_i _ (S.power a).
unfold power.
unfold quo_ind_set_nodep.
rewrite quo_ind_set_eq.
reflexivity.
Qed.

Lemma power_ax : forall x z,
  in_set z (power x) <->
  (forall y, in_set y z -> in_set y x).
intros.
elim x using (quo_ind _); auto.
clear x; intros x.
elim z using (quo_ind _); auto.
clear z; intros z.
rewrite power_eq.
rewrite in_set_eqv.
rewrite S.power_ax.
split.
 intros h y.
 elim y using (quo_ind _); auto.
 intros.
 apply in_set_eqv.
 apply in_set_eqv in H.
 auto.

 intros h y ?.
 apply in_set_eqv.
 apply in_set_eqv in H.
 auto.
Qed.
(*
Definition replf (x:set) (F:set->set) : set.
assert (tr (S.set->S.set)).

  sup _ (fun i => F (elts x i)).

Lemma replf_ax : forall x F z,
  (forall z z', in_set z x ->
   eq_set z z' -> eq_set (F z) (F z')) ->
  (in_set z (replf x F) <->
   #exists2 y, in_set y x & eq_set z (F y)).
unfold replf; simpl; intros.
split; intros.
 elim H0 using in_set_ind; intros; auto.
 simpl in *.
 Texists (elts x j); trivial.
 Texists j; apply eq_set_refl.

 elim H0 using tr_ind; intros; auto.
 destruct x0 as (x',?,?).
 elim H1 using in_set_ind; intros; auto.
 Texists j; simpl.
 apply eq_set_trans with (F x'); trivial.
 apply eq_set_sym.
 apply H.
  Texists j; apply eq_set_refl.
  apply eq_set_sym; trivial.
Qed.

*)

Parameter repl : set -> (set -> set -> Prop) -> set.

Lemma repl_ax:
    forall a (R:set->set->Prop),
    (forall x x' y y', in_set x a ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x y y', in_set x a -> R x y -> R x y' -> eq_set y y') ->
    forall z, in_set z (repl a R) <->
     #(exists2 y, in_set y a & R y z).
Admitted.

Lemma repl_mono a a' :
 (forall z, in_set z a -> in_set z a') ->
 forall R R' : set -> set -> Prop,
 (forall x x', eq_set x x' ->
  forall y y', eq_set y y' -> (R x y <-> R' x' y')) ->
 forall z,
 in_set z (repl a R) ->
 in_set z (repl a' R').
Admitted.

End IZF_R.
Import IZF_R.

(*

 Lemma pair_spec_is_set (a b:qset) :
  is_set (pair_spec (qset_set a) (qset_set b)).
elim a using (quo_ind isRel_eqset).
 intros.
 apply tr_prop.
clear a; intros a.
elim b using (quo_ind isRel_eqset).
 intros.
 apply tr_prop.
clear b; intros b.
apply tr_i.
exists (pair a b).
 intros; apply isProp_forall; intros z.
 apply isProp_conj; apply isProp_forall; intros _; auto.

 red; intros.
 rewrite pair_ax.
 do 2 rewrite qset_set_eq.
 split; apply TrMono; (destruct 1;[left|right]); apply eq_set_sym; trivial.

 split; intros.
  apply eq_set_ax; intros z.
  rewrite pair_ax.
  red in H.
  rewrite H.  
  do 2 rewrite qset_set_eq.
  split; apply TrMono; (destruct 1;[left|right]); apply eq_set_sym; trivial.

  red; intros.
  transitivity (in_set z (pair a b)).
   split; intros.
    apply eq_elim with y; trivial.
    apply eq_set_sym; trivial.

    apply eq_elim with (pair a b); trivial.

    rewrite pair_ax.
  do 2 rewrite qset_set_eq.
  split; apply TrMono; (destruct 1;[left|right]); apply eq_set_sym; trivial.
Qed.


Definition qpair (a b:qset) : qset :=


  mk_qset (pair_spec (qset_set a) (qset_set b)) (pair_spec_is_set a b).

Lemma qpair_ax : forall a b z,
  in_qset z (qpair a b) <-> tr (z=a \/ z=b).
split; intros.
 elim H using in_qset_ind; intros; auto.
 apply sig_proj1 in H1.
 simpl in H1.


 apply f_app with (x:=y') in H1.
 unfold pair_spec in H1.
 assert (h:=eq_set_refl y').
 rewrite <- H1 in h.
 rewrite h in H2.
 revert H2; apply TrMono.
 admit.

 elim H using tr_ind; intros.
  apply tr_prop.
 clear H.
 destruct x; subst z.
  apply tr_i; exists  
 auto.
 red in H1.
 
 elim H2 using in_set_ind; intros; auto.

 intros (z', eqz, (x, eqx, inx)).
 admit.

 intros.
 destruct H; subst z.
  unfold qpair.
  elim a using quo_ind with (Rr:=isRel_eqset).
   admit.  
  clear a; intros a.
  Lemma quo_ind_eq : forall X (R:X->X->Prop) (Rr:isRel R) P Ps h x,
   quo_ind Rr P Ps h (quo_i Rr x) = h x. 
Admitted.
rewrite quo_ind_eq.    
  elim b using quo_ind with (Rr:=isRel_eqset).
   admit.  
  clear b; intros b.
rewrite quo_ind_eq.    
 exists a; trivial.
 exists (pair a b); trivial.
 apply pair_ax.
 left; apply eq_set_refl.

  unfold qpair.
  elim a using quo_ind with (Rr:=isRel_eqset).
   admit.  
  clear a; intros a.
rewrite quo_ind_eq.    
  elim b using quo_ind with (Rr:=isRel_eqset).
   admit.  
  clear b; intros b.
rewrite quo_ind_eq.    
 exists b; trivial.
 exists (pair a b); trivial.
 apply pair_ax.
 right; apply eq_set_refl.
Qed.
 *)

Lemma uchoice :
  forall (P:set->Prop),
  (forall q, isProp (P q)) ->
  (#exists x, P x) ->
  (forall y y', P y -> P y' -> y = y') ->
  set.
intros P Pp Pex Puniq.
apply (proj1 (@tr_ex_sig _ P)) in Pex; trivial.
exact (proj1_sig (descr Pp Puniq Pex)).  
Defined.

Lemma uchoice_ext : forall (P:set->Prop) x
  (Pp : forall q, isProp (P q))
  (w:#exists x, P x )
  (uniq:forall y y', P y -> P y' -> y = y'),
  P x -> uchoice P Pp w uniq = x.
intros.
unfold uchoice.
apply descr_eq; trivial.
Qed.
Print Assumptions uchoice_ext.

(*
  Lemma qrepl_ax:
    forall a (R:qset->qset->Prop),
    (forall x y y', in_qset x a -> R x y -> R x y' -> y = y') ->
    exists b, forall x, in_qset x b <->
     (exists2 y, in_qset y a & R y x).
  intros.
  


(* Fixpoint *)
Fixpoint wfrec (F:(set->set)->set->set) (x:set) : set :=
  F (fun y => union (sup {i:idx x|eq_set (elts x i) y}
               (fun i => wfrec F (elts x (proj1_sig i))))) x.
Section FixRec.
Hypothesis F : (set->set)->set->set.
Hypothesis Fext : forall x x' f f',
  (forall y y', in_set y x -> eq_set y y' -> eq_set (f y) (f' y')) ->
  eq_set x x' ->
  eq_set (F f x) (F f' x').

Instance wfrecm : Proper (eq_set==>eq_set) (wfrec F).
do 2 red.
induction x; destruct y; intros.
simpl wfrec.
apply Fext; trivial.
simpl in H0; destruct H0.
intros.
apply union_morph.
simpl.
split; intros.
 clear H2; destruct i as (i,?); simpl.
 destruct (H0 i) as (j,?).
 assert (eq_set (f0 j) y').
  apply eq_set_trans with y; trivial.
  apply eq_set_trans with (f i); trivial.
  apply eq_set_sym; trivial.
 exists (exist _ j H4); simpl.
 apply H; trivial.

 destruct H2 as (i,?H2); simpl in i,H2.
 destruct j as (j,?).
 exists (exist _ i (eq_set_sym _ _ H2)); simpl.
 apply H.
 apply eq_set_sym.
 apply eq_set_trans with y; trivial. 
 apply eq_set_trans with y'; trivial.
 apply eq_set_sym; trivial.
Qed.

Lemma wfrec_eqn x :
  eq_set (wfrec F x) (F (wfrec F) x).
destruct x; simpl.
apply Fext.
2:apply eq_set_refl.
intros.
rewrite eq_set_ax.
intros z.
rewrite union_ax.
split; intros.
 destruct H1 as (b,?,?).
 destruct H2 as ((j,e),?).
 simpl in H2.
 apply eq_elim with b; trivial.
 apply eq_set_trans with (1:=H2).
 apply wfrecm.
 apply eq_set_trans with y; trivial.

 destruct H as (i,H).
 simpl in i,H.
 apply eq_set_sym in H0.
 exists (wfrec F (f i)).
  apply eq_elim with (1:=H1).
  apply wfrecm.
  apply eq_set_trans with y; trivial.

  apply eq_set_sym in H.
  exists (exist _ i H).
  simpl.
  apply eq_set_refl.
Qed.
End FixRec.



(* We only use the following instance of unique choice for
   replacement: *)
Definition ttrepl :=
  forall a:set, unique_choice {x|in_set x a} set eq_set.

(* We show it is a consequence of [choice]. *)
Lemma ttrepl_axiom : ttrepl.
red; red; intros; apply choice_axiom; trivial.
Qed.

Lemma repl_ax:
    forall a (R:set->set->Prop),
    (forall x x' y y', in_set x a ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x y y', in_set x a -> R x y -> R x y' -> eq_set y y') ->
    exists b, forall x, in_set x b <->
     (exists2 y, in_set y a & R y x).
intros.
elim (ttrepl_axiom (subset a (fun x=>exists y, R x y))
        (fun p y => R (proj1_sig p) y)); intros.
pose (a' := {x|in_set x (subset a (fun x => exists y, R x y))}).
fold a' in x,H1.
exists (repl1 _ x).
intros.
elim (repl1_ax _ x x0); intros.
 fold a' in H2,H3|-.
 split; intros.
  elim H2; trivial; intros.
  exists (proj1_sig x1).
   apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig x1))).

   apply H with (4:=H1 x1).
    apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig x1))).
    apply eq_set_refl.
    apply eq_set_sym; trivial.

  apply H3.
  destruct H4.
  assert (in_set x1 (subset a (fun x => exists y, R x y))).
   apply (proj2 (subset_ax a (fun x => exists y, R x y) x1)).
   split; trivial.
   exists x1.
    apply eq_set_refl.
    exists x0; trivial.
  pose (x' := exist _ x1 H6 : a').
  exists x'.
  apply H0 with x1; trivial.
  apply (H1 x').

 apply H0 with (proj1_sig z); trivial.
  apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig z))).
  apply H with (proj1_sig z') (x z'); trivial.
   apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig z'))).
   apply eq_set_sym; trivial.
   apply eq_set_refl.

(* side conditions *)
 elim (proj2 (proj1 (subset_ax _ _ _) (proj2_sig x))); intros. 
 destruct H2.
 exists x1; apply H with (4:=H2).
  apply in_reg with (proj1_sig x); trivial.
  apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig x))).

  apply eq_set_sym; trivial.

  apply eq_set_refl.

 assert (in_set (proj1_sig x) a).
  apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig x))).
 split; intros.
  apply H0 with (proj1_sig x); trivial.

  revert H1; apply H; trivial.
  apply eq_set_refl.
Qed.

(* Attempt to prove that choice is necessary for replacement, by deriving
   choice from replacement. Works only for relations that are morphisms for
   set equality... *)
Lemma ttrepl_needed_for_repl :
  forall a:set,
  let A := {x|in_set x a} in
  let eqA (x y:A) := eq_set (proj1_sig x) (proj1_sig y) in
  let B := set in
  let eqB := eq_set in
  forall (R:A->B->Prop),
  Proper (eqA==>eqB==>iff) R ->
  (forall x:A, exists y:B, R x y) ->
  (forall x y y', R x y -> R x y' -> eqB y y') ->
  exists f:A->B, forall x:A, R x (f x).
intros a A eqA B eqB R Rext Rex Runiq.
destruct repl_ax with
  (a:=a) (R:=fun x y => exists h:in_set x a, R (exist _ x h) y).
 intros.
 destruct H2.
 exists (in_reg _ _ _ H0 x0).
 revert H2; apply Rext; apply eq_set_sym; assumption.

 intros x y y' _ (h,Rxy) (h',Rxy').
 apply Runiq with (1:=Rxy).
 revert Rxy'; apply Rext.
  apply eq_set_refl.
  apply eq_set_refl.

 exists (fun y => union (subset x (fun z => R y z))).
 intro.
 destruct Rex with x0.
 apply Rext with (3:=H0);[apply eq_set_refl|].
 apply eq_set_sym.
 apply eq_set_ax; split; intros.
  rewrite union_ax; exists x1; trivial.
  rewrite subset_ax.
  split.
   apply H.
   exists (proj1_sig x0); [apply proj2_sig|].
   exists (proj2_sig x0).
   destruct x0; trivial.

   exists x1; trivial; apply eq_set_refl.

  rewrite union_ax in H1; destruct H1.
  rewrite subset_ax in H2; destruct H2.
  destruct H3.
  apply eq_elim with x2; trivial.
  apply eq_set_trans with (1:=H3).
  apply Runiq with (1:=H4); trivial.
Qed.
 *)

Notation "x ∈ y" := (in_set x y).
Notation "x == y" := (eq_set x y).

(* Deriving the existentially quantified sets *)

Lemma empty_ex: #exists empty, forall x, x ∈ empty -> #False.
apply tr_i.
exists empty.
exact empty_ax.
Qed.

Lemma pair_ex: forall a b, #exists c, forall x, x ∈ c <-> #(x == a \/ x == b).
intros.
apply tr_i.
exists (pair a b).
apply pair_ax.
Qed.

Lemma union_ex: forall a, #exists b,
    forall x, x ∈ b <-> #(exists2 y, x ∈ y & y ∈ a).
intros.
apply tr_i.
exists (union a).
apply union_ax.
Qed.

Lemma subset_ex : forall x P, #exists b,
  forall z, z ∈ b <->
  (z ∈ x /\ #exists2 z', z == z' & P z').
intros.
apply tr_i.
exists (subset x P).
apply subset_ax.
Qed.

Lemma power_ex: forall a, #exists b,
     forall x, x ∈ b <-> (forall y, y ∈ x -> y ∈ a).
intros.
apply tr_i.
exists (power a).
apply power_ax.
Qed.

Lemma repl_ex: forall a (R:set->set->Prop),
    (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x ∈ a -> R x y -> R x y' -> y == y') ->
    #exists b, forall x, x ∈ b <-> #(exists2 y, y ∈ a & R y x).
intros.
apply tr_i.
exists (repl a R).
apply repl_ax; trivial.
Qed.

(* Collection *)
(*Section Collection.

Section FromTTColl.

(* TTColl is a consequence of choice *)
Lemma ttcoll :
  forall (A:Ti) (R:A->set->Prop),
  (forall x:A, exists y:set, R x y) ->
  exists X:Ti, exists f : X->set,
    forall x:A, exists i:X, R x (f i).
intros.
destruct (choice_axiom A set R) as (f,Hf); trivial.
(* X is A because choice "chooses" just one y for each x *)
exists A; exists f; eauto.
Qed.

Lemma ttcoll' :
  forall (A:Ti) R,
  (forall x:A, exists y:set, R x y) ->
  exists B, forall x:A, exists2 y, y ∈ B & R x y.
intros.
destruct ttcoll with (1:=H) as (X,(f,Hf)).
exists (sup X f).
intro.
destruct Hf with x.
exists (f x0); trivial.
exists x0; apply eq_set_refl.
Qed.

Lemma coll_ax_ttcoll : forall A (R:set->set->Prop), 
    (forall x x' y y', in_set x A ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x, in_set x A -> exists y, R x y) ->
    exists B, forall x, in_set x A -> exists2 y, in_set y B & R x y.
intros.
destruct (ttcoll (idx A) (fun i y => R (elts A i) y)) as (X,(f,Hf)).
 intro i.
 apply H0.
 exists i; apply eq_set_refl.

 exists (sup X f); intros.
 destruct H1 as (i,?).
 destruct (Hf i) as (j,?).
 exists (f j).
  exists j; apply eq_set_refl.

  revert H2; apply H.
   exists i; apply eq_set_refl.
   apply eq_set_sym; assumption.
   apply eq_set_refl.
Qed.

(* Proving collection requires the specialized version of ttcoll *)
Lemma ttcoll'' : forall A (R:set->set->Prop),
  (forall x x' y y', in_set x A ->
   eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
  (forall x, x ∈ A -> exists y:set, R x y) ->
  exists f : {x|x∈ A} -> {X:Ti & X->set},
    forall x, exists i:projT1 (f x), R (proj1_sig x) (projT2 (f x) i).
intros.
destruct (coll_ax_ttcoll A R H H0) as (B,HB).
exists (fun _ => let (X,f) := B in existT (fun X => X->set) X f).
destruct B; simpl.
destruct x; simpl; intros.
destruct HB with x; trivial.
destruct H1.
exists x1.
apply H with (4:=H2); auto with *.
apply eq_set_refl.
Qed.

End FromTTColl.

Section FromChoice.

Lemma coll_ax_choice : forall A (R:set->set->Prop), 
    (forall x x' y y', in_set x A ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x, in_set x A -> exists y, R x y) ->
    exists B, forall x, in_set x A -> exists y, in_set y B /\ R x y.
intros.
elim (choice_axiom {x|x ∈ A} set (fun p y => R (proj1_sig p) y)); trivial; intros.
 exists (repl1 A x).
 intros.
 destruct H2.
 exists (x (elts' _ x1)); split.
  exists x1; apply eq_set_refl.

  apply H with (proj1_sig (elts' _ x1)) (x (elts' _ x1)); trivial.
   apply (proj2_sig (elts' _ x1)).
   apply eq_set_sym; trivial.
   apply eq_set_refl.

 apply H0.
 apply (proj2_sig x).
Qed.

End FromChoice.

End Collection.
*)

(* Infinity *)

Lemma infinity_ex: #exists2 infinite,
    #(exists2 empty, (forall x, x ∈ empty -> #False) & empty ∈ infinite) &
    (forall x, x ∈ infinite ->
     #exists2 y, (forall z, z ∈ y <-> #(z == x \/ z ∈ x)) &
       y ∈ infinite).
Texists infinite.
 Texists empty.
  exact empty_ax.
  exact infinity_ax1.

 intros.
 Texists (union (pair x (pair x x))); intros.
  rewrite union_ax.
  split; intros.
   Tdestruct H0.
   rewrite pair_ax in H1; Tdestruct H1.
    subst x; Tright; trivial.

    subst x0.
    rewrite pair_ax in H0; Tdestruct H0; apply tr_i; auto.

   Tdestruct H0.
    red in H0; subst z.
    Texists (pair x x).
     rewrite pair_ax; apply tr_i; auto.
     rewrite pair_ax; apply tr_i; auto.

    Texists x; trivial.
    rewrite pair_ax; Tleft; trivial.

  apply infinity_ax2; trivial.
Qed.

