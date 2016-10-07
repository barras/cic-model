Require Import ZFskol.
Require Import Sublogic.

Lemma f_app A (B:A->Type) (f g:forall x, B x) x :
   f = g -> f x = g x.
destruct 1; reflexivity.
Qed.

Definition sig_proj1 {A B} {p q:@sig A B} (e:p=q) : proj1_sig p = proj1_sig q :=
  f_equal _ e.

(** In this file, we give an attempt to build a model of IZF
   in Coq + definite description + prop-truncation
 *)
Definition isProp X := forall x y:X, x=y.

Definition isSet X :=
  forall (x y:X) (p q:x=y), p=q.

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

Lemma isProp_sig :
  forall {A} {P:A->Prop}, (forall a, isProp (P a)) ->
  (forall a a', P a -> P a' -> a=a') ->
  isProp {x:A | P x}.
red; intros.
apply sig_intro; auto.
apply H0; apply proj2_sig.
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

(** Predicate extensionality: consequence of univalence *)
Parameter pred_ext :
  forall {A} {P Q:A->Prop},
  (forall a, isProp (P a)) ->
  (forall a, isProp (Q a)) ->
  (forall a, P a <-> Q a) ->
  P = Q.

Parameter isProp_pred_eq :
  forall {A} {P Q:A->Prop},
  (forall a, isProp (P a)) ->
  (forall a, isProp (Q a)) ->
  isProp (P=Q).
(*
Lemma isSet_pred X : isSet {Q:X->Prop | forall x, isProp (Q x)}.
red; intros.
assert (forall p, p = sig_intro x y (fun x => isProp_forall _ _ (fun x => isProp_isProp _)) (sig_proj1 p)).
clear.
intros.
destruct p.
unfold sig_intro; simpl.
destruct x; simpl.
replace  (isProp_forall X (fun x0 : X => isProp (x x0))
           (fun x0 : X => isProp_isProp (x x0)) i i) with (eq_refl i).
 reflexivity.
assert (isProp (forall z, isProp (x z))).
 apply isProp_forall.
 intros; apply isProp_isProp.
apply (is_prop_uip _ i i) in H.
apply H.

rewrite (H p), (H q).
destruct (pred_ext' (proj2_sig x) (proj2_sig y) (sig_proj1 p) (sig_proj1 q)).
reflexivity.
Qed.
 *)

(** Prop-truncation *)
Parameter tr : Type -> Prop.
Parameter tr_prop : forall X, isProp (tr X).
Parameter tr_i : forall {X}, X -> tr X.
Parameter tr_ind_nodep : forall {X P},
  isProp P -> (X->P) -> tr X -> P.

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
Import trSub.

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

Definition quo_i {X} {R:X->X->Prop} (Rr:isRel R) (x:X) : quo X R :=
  existT (fun P => tr(isClass R P))
    (fun y => R x y)
    (tr_i (isClass_eq Rr x)).

Lemma quo_i_eq {X R} (Rr:isRel  R) {x y:X} :
  quo_i _ x = quo_i _ y <-> R x y.
split.
 intros.
 apply sig_proj1 in H; simpl in H.
 apply f_app with (x:=y) in H.
 rewrite H; reflexivity.

 intros.
 apply sig_intro.
  intros.
  apply tr_prop.

  simpl; apply pred_ext.
   intros; apply Rr.
   intros; apply Rr.

   intros; rewrite H.
   reflexivity.  
Qed.

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

Lemma class_quo_proj1 X R (Rr:isRel R) (q:quo X R) w :
  proj1_sig q w <-> q = quo_i _ w.
split; intros.
 apply quo_ext; trivial.
 intros; simpl.
 assert (Pp := isProp_quo_proj1 q).
 destruct q as (P,Pc); simpl in *.
 elim Pc using tr_ind; intros.
  apply isProp_conj; apply isProp_forall; intros; auto.
  apply Rr.
 destruct x0 as (_,w',_,eqvP).
 rewrite eqvP in H|-*.
 rewrite H; reflexivity.

 subst q; simpl.
 reflexivity.
Qed.


Lemma quo_isSet X (R:X->X->Prop) (Rr:isRel R) : isSet (quo X R).
red; intros.
assert (forall e:x=y, e = sig_intro x y (fun _ => tr_prop _) (sig_proj1 e)).
 destruct e.
 simpl.
 unfold sig_intro.
 destruct x; simpl.
 replace (tr_prop (isClass R x) t t) with (eq_refl t); trivial.
 apply is_prop_uip; trivial.
 apply tr_prop.
rewrite (H p), (H q).
f_equal.
apply isProp_pred_eq; apply isProp_quo_proj1.
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
Defined.

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
    forall x y (r:R x y), eq_rect _ P (h x) _ (proj2 (quo_i_eq _) r) = h y.

  Let imgP x :=
    tr { p:P x | tr {x':X & { e: quo_i _ x' = x | eq_rect _ P (h x') _ e = p}}}.

  Lemma quo_imgP (q:quo X R) : imgP q.
elim q using (quo_ind Rr).
 intros; apply tr_prop.
intros.
apply tr_i.
exists (h x).
apply tr_i.
exists x; auto.
exists eq_refl; trivial.
Qed.
 
Lemma imgP_uniq q (p p':P q) :
  {x:X & { e: quo_i _ x = q | eq_rect _ P (h x) _ e = p}} ->
  {x:X & { e: quo_i _ x = q | eq_rect _ P (h x) _ e = p'}} ->
  p=p'.
intros (x0,(eqx0,imgx0)) (x1,(eqx1,imgx1)).
rewrite <- imgx0, <- imgx1.
clear imgx0 imgx1.
revert eqx0; destruct eqx1.
simpl; intros.
assert (R x0 x1).
 apply quo_i_eq in eqx0; trivial.
replace eqx0 with (proj2 (quo_i_eq _) H).
 apply hcomp.

 apply quo_isSet; trivial.
Qed.

Lemma imgP_uniq_tr q (p p':P q) :
  tr {x:X & { e: quo_i _ x = q | eq_rect _ P (h x) _ e = p}} ->
  tr {x:X & { e: quo_i _ x = q | eq_rect _ P (h x) _ e = p'}} ->
  p=p'.
intros.
elim H using tr_ind; intros.
 red; intros; apply Ps.
elim H0 using tr_ind; intros.
 red; intros; apply Ps.
apply imgP_uniq; trivial.
Qed.

 Lemma quo_ind_set (q:quo X R) : P q.
assert (p' := quo_imgP q).
apply descr in p'.
 exact (proj1_sig p'). 

 intros; apply tr_prop.

 apply imgP_uniq_tr.
Defined.

 Lemma quo_ind_set_eq (x:X) :
  quo_ind_set (quo_i _ x) = h x.
unfold quo_ind_set.
apply descr_eq.
apply tr_i.
exists x.
exists (eq_refl (quo_i _ x)).
reflexivity.
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
Defined.



Module IZF_R <: IZF_R_Ex_sig CoqSublogicThms.

(* The level of indexes *)
Definition Ti := Type.

Inductive set_ : Type :=
  sup (X:Ti) (f:X->set_).
Definition set := set_.

Definition idx (x:set) := let (X,_) := x in X.
Definition elts (x:set) : idx x -> set :=
  match x return idx x -> set with
  | sup X f => f
  end.

Fixpoint eq_set (x y:set) {struct x} :=
  (forall i, tr { j | eq_set (elts x i) (elts y j)}) /\
  (forall j, tr { i | eq_set (elts x i) (elts y j)}).

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
  (forall i, tr { j | eq_set (elts x i) (elts y j)}) ->
  (forall j, tr { i | eq_set (elts x i) (elts y j)}) ->
  eq_set x y.
destruct x; simpl; auto.
Qed.

Definition in_set x y :=
  tr { j | eq_set x (elts y j)}.

Lemma in_set_ind P x y :
  isProp P ->
  (forall j, eq_set x (elts y j) -> P) ->
  in_set x y -> P.
intros.
elim H0 using tr_ind; auto.  
destruct 1; eauto.
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

(*Lemma eq_elim0 : forall x y i,
  eq_set x y ->
  tr { j | eq_set (elts x i) (elts y j)}.
destruct x; simpl; intros.
destruct H.
auto.
Qed.*)
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
 split; intros; elim H0 using tr_ind_tr; destruct 1.
  elim (eq_elim0 x y x0) using in_set_ind; intros; auto.
  apply tr_i; exists j; apply eq_set_trans with (elts x x0); trivial.

  apply eq_set_sym in H.
  elim (eq_elim0 y x x0) using in_set_ind; intros; auto.
  apply tr_i; exists j; apply eq_set_trans with (elts y x0); trivial.

  apply eq_set_def; intros.
   apply H.
   apply tr_i; exists i; apply eq_set_refl.

   destruct (H (elts y j)).
   elim H1 using in_set_ind; intros; auto.
    apply tr_i; exists j0; apply eq_set_sym; trivial.

    apply tr_i; exists j; apply eq_set_refl.
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


Definition qset := quo set eq_set.

Instance isRel_eqset : isRel eq_set.
split; intros; auto.
split; red; intros.
 apply eq_set_refl.

 apply eq_set_sym; trivial.  

 apply eq_set_trans with y; trivial.  
Qed.

Lemma isSet_qset : isSet qset.
apply quo_isSet; auto with *.
Qed.


Definition qset_set (q:qset) (x:set) : Prop :=
  q = quo_i _ x.

Lemma qset_set_eq (x:set) :
  qset_set (quo_i _ x) = eq_set x.
unfold qset_set.
apply pred_ext; intros; auto.
 red; intros.
 apply quo_isSet; auto with *.

 apply quo_i_eq.
Qed.


Definition is_set (P:set->Prop) := tr (isClass eq_set P).
Definition mk_qset (P:set->Prop) (Ps:is_set P) : qset :=
  exist is_set P Ps.


Definition in_qset (x y:qset) :=
  tr { x' | x = quo_i _ x' /\ tr{ y' | y = quo_i _ y' /\ in_set x' y'}}.

Lemma in_qset_ind P x y :
  isProp P ->
  (forall x' y', x = quo_i _ x' -> y = quo_i _ y' -> in_set x' y' -> P) ->
  in_qset x y -> P.
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
  in_qset (quo_i _ x) (quo_i _ y) <-> in_set x y.
split; intros.
 elim H using in_qset_ind; intros; auto.
 apply quo_i_eq in H0.
 apply quo_i_eq in H1.
 apply eq_elim with y'; trivial.
  apply in_reg with x'; trivial.
  apply eq_set_sym; trivial.
  apply eq_set_sym; trivial.

 apply tr_i; exists x; split; trivial.
 apply tr_i; exists y; split; trivial.
Qed.


(* Set induction *)

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

(* *)

Definition empty :=
  sup False (fun x => match x with end).

Lemma empty_ax : forall x, ~ in_set x empty.
red; intros.
elim H using in_set_ind; intros.
 apply isProp_False.
contradiction.
Qed.


Definition qempty := quo_i _ empty.
Lemma qempty_ax : forall x, ~ in_qset x qempty.
red; intros.
elim H using in_qset_ind.
 apply isProp_False.

 intros x' y' _ mtdef inmt.
 apply quo_i_eq in mtdef.
 apply eq_elim with (2:=eq_set_sym _ _ mtdef) in inmt.
 apply empty_ax in inmt; trivial.
Qed.

Definition singl x := sup unit (fun _ => x).

Definition pair_spec (a b:set->Prop) (x:set) : Prop :=
  forall z, in_set z x <-> tr (a z \/ b z).

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
  in_set z (pair a b) <-> tr (eq_set z a \/ eq_set z b).
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

Definition qpair (a b:qset) : qset.
pose (h := fun a b => quo_i _ (pair a b)).
assert (forall a x y, eq_set x y -> h a x = h a y).
 intros.
 unfold h.
 apply quo_i_eq.
 apply pair_morph; trivial.
 reflexivity.
pose (qh := fun a => quo_ind_set_nodep _ isSet_qset (h a) (H a) b).
apply quo_ind_set_nodep with (1:=_) (h0:=qh) (4:=a).
 exact isSet_qset.
 intros.
unfold qh.
elim b using (quo_ind _).
 red; intros.
 apply isSet_qset.
intros.
unfold quo_ind_set_nodep.
rewrite quo_ind_set_eq.
rewrite quo_ind_set_eq.
unfold h.
apply quo_i_eq.
apply pair_morph; trivial.
apply eq_set_refl.
Defined.

Lemma qpair_eq a b:
  qpair (quo_i _ a) (quo_i _ b) = quo_i _ (pair a b).
unfold qpair.
unfold quo_ind_set_nodep.
eapply transitivity.
match goal with
    |- context[quo_ind_set ?X ?R ?Rr ?P ?Ps ?h ?hcomp (quo_i ?Rr ?x)] =>
    pose (thm := quo_ind_set_eq X R Rr P Ps h hcomp x)
end.
apply thm.
match goal with
    |- context[quo_ind_set ?X ?R ?Rr ?P ?Ps ?h ?hcomp (quo_i ?Rr ?x)] =>
    pose (thm' := quo_ind_set_eq X R Rr P Ps h hcomp x)
end.
apply thm'.
Qed.


Lemma qpair_ax : forall a b z,
  in_qset z (qpair a b) <-> tr (z=a \/ z=b).
intros.
assert (forall a b z, isProp (in_qset z (qpair a b) <-> tr (z=a\/z=b))).  
 intros.
 apply isProp_conj;apply isProp_forall; intros; auto.
 apply tr_prop.
elim a using (quo_ind _); auto.
clear a; intros a.
elim b using (quo_ind _); auto.
clear b; intros b.
elim z using (quo_ind _); auto.
clear z; intros z.
rewrite qpair_eq.
rewrite in_set_eqv.
rewrite pair_ax.
split; apply TrMono; (destruct 1;[left|right]); try apply quo_i_eq; trivial.
 apply quo_i_eq in H0; trivial.
 apply quo_i_eq in H0; trivial.
Qed.
Print Assumptions qpair_ax.
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

Lemma quchoice :
  forall (R:qset->Prop),
  (forall q, isProp (R q)) ->
  tr { x | R x } ->
  (forall y y', R y -> R y' -> y = y') ->
  qset.
intros.
exact (proj1_sig (descr H H1 H0)).  
Defined.

Lemma quchoice_ext : forall (P:qset->Prop) x
  (Pp : forall q, isProp (P q))
  (w:tr { x | P x })
  (uniq:forall y y', P y -> P y' -> y = y'),
  P x -> quchoice P Pp w uniq = x.
intros.
unfold quchoice.
apply descr_eq; trivial.
Qed.
Print Assumptions quchoice_ext.


                          
Definition uchoice (P : set -> Prop) : set :=
  union (repl (singl empty) (fun _ => P)).

  {q:qset | R q }.
intros.
apply descr; trivial.
Defined.



  Lemma quchoice_ax:
    forall (R:qset->Prop),
    (forall q, isProp (R q)) ->
    tr { x | R x } ->
    (forall y y', R y -> R y' -> y = y') ->
    exists b, forall x, in_qset x b <-> R x.
    intros.
exists (quchoice R H H0).    
intros.
(exists2 y, in_qset y a & R y x).


  Lemma qrepl_ax:
    forall a (R:qset->qset->Prop),
    (forall x y y', in_qset x a -> R x y -> R x y' -> y = y') ->
    exists b, forall x, in_qset x b <->
     (exists2 y, in_qset y a & R y x).
  intros.
  

  
 Definition union (x:set) :=
  sup {i:idx x & idx (elts x i)}
    (fun p => elts (elts x (projS1 p)) (projS2 p)).

Lemma union_ax : forall a z,
  in_set z (union a) <-> exists2 b, in_set z b & in_set b a.
unfold in_set at 1, union; simpl; intros.
split; intros.
 destruct H.
 exists (elts a (projT1 x)).
  exists (projT2 x); trivial.
  exists (projT1 x); apply eq_set_refl.

 destruct H.
 destruct H0.
 assert (in_set z (elts a x0)).
  apply eq_elim with x; trivial.
 destruct H1.
 exists (existT (fun i=>idx(elts a i)) x0 x1); simpl.
 trivial.
Qed.

Lemma union_morph :
  forall a a', eq_set a a' -> eq_set (union a) (union a').
unfold union.
simpl; intros.
split; intros.
 destruct i; simpl.
 assert (in_set (elts a x) a').
  apply eq_elim with a; trivial.
  exists x; apply eq_set_refl.
 destruct H0.
 assert (in_set (elts (elts a x) i) (elts a' x0)).
  apply eq_elim with (elts a x); trivial.
  exists i; apply eq_set_refl. 
 destruct H1.
 exists (existT (fun i=>idx (elts a' i)) x0 x1); simpl.
 trivial.

 destruct j; simpl.
 generalize (eq_set_sym _ _ H); clear H; intro.
 assert (in_set (elts a' x) a).
  apply eq_elim with a'; trivial.
  exists x; apply eq_set_refl.
 destruct H0.
 assert (in_set (elts (elts a' x) i) (elts a x0)).
  apply eq_elim with (elts a' x); trivial.
  exists i; apply eq_set_refl. 
 destruct H1.
 exists (existT (fun i=>idx (elts a i)) x0 x1); simpl.
 apply eq_set_sym; trivial.
Qed.

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

Definition subset (x:set) (P:set->Prop) :=
  sup {a|exists2 x', eq_set (elts x a) x' & P x'}
    (fun y => elts x (proj1_sig y)).

Lemma subset_ax : forall x P z,
  in_set z (subset x P) <->
  in_set z x /\ exists2 z', eq_set z z' & P z'.
unfold in_set at 1, subset; simpl.
split; intros.
 destruct H.
 destruct x0; simpl in H.
 split.
  exists x0; trivial.
  destruct e.
  exists x1; trivial.

  apply eq_set_trans with (elts x x0); trivial.

 destruct H.
 destruct H.
 destruct H0.
 assert (exists2 x', eq_set (elts x x0) x' & P x').
  exists x1; trivial.
  apply eq_set_trans with z; trivial.
  apply eq_set_sym; trivial.
 exists
  (@exist _ (fun a=>exists2 x',eq_set (elts x a) x' & P x')
    x0 H2); simpl; trivial.
Qed.

Definition power (x:set) :=
  sup (idx x->Prop)
   (fun P => subset x (fun y => exists2 i, eq_set y (elts x i) & P i)).

Lemma power_ax : forall x z,
  in_set z (power x) <->
  (forall y, in_set y z -> in_set y x).
unfold in_set at 1, power; simpl; intros.
split; intros.
 destruct H.
 specialize eq_elim with (1:=H0)(2:=H); intro.
 apply (proj1 (proj1 (subset_ax _ _ _) H1)).

 exists (fun i => in_set (elts x i) z).
 apply eq_intro; intros.
  apply (fun x P z => proj2 (subset_ax x P z)).
  split; auto.
  exists z0.
   apply eq_set_refl.

   elim H with z0; trivial; intros.
   exists x0; trivial.
   apply in_reg with z0; trivial.

  elim (proj2 (proj1 (subset_ax _ _ _) H0)); intros.
  destruct H2.
  apply in_reg with (elts x x1); trivial.
  apply eq_set_sym;
    apply eq_set_trans with x0; trivial.
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

Fixpoint num (n:nat) : set :=
  match n with
  | 0 => empty
  | S k => union (pair (num k) (pair (num k) (num k)))
  end.

Definition infinity := sup _ num.

Lemma infty_ax1 : in_set empty infinity.
 exists 0.
 unfold elts, infinity, num.
 apply eq_set_refl.
Qed.

Lemma infty_ax2 : forall x, in_set x infinity ->
  in_set (union (pair x (pair x x))) infinity.
intros.
destruct H.
exists (S x0).
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
   exists2 y, in_set y x & eq_set z (F y)).
unfold in_set at 2, replf; simpl; intros.
split; intros.
 destruct H0.
 exists (elts x x0); trivial.
 exists x0; apply eq_set_refl.

 destruct H0.
 destruct H0.
 exists x1.
 apply eq_set_trans with (F x0); trivial.
 apply eq_set_sym.
 apply H.
  exists x1; apply eq_set_refl.
  apply eq_set_sym; trivial.
Qed.


Definition repl1 (x:set) (F:{y|in_set y x}->set) :=
  sup _ (fun i => F (elts' x i)).

Lemma repl1_ax : forall x F z,
  (forall z z', eq_set (proj1_sig z) (proj1_sig z') ->
   eq_set (F z) (F z')) ->
  (in_set z (repl1 x F) <->
   exists y, eq_set z (F y)).
unfold in_set at 6, repl1; simpl; intros.
split; intros.
 destruct H0.
 exists (elts' x x0); trivial.

 destruct H0.
 destruct x0.
 elim i; intros.
 exists x1.
 apply eq_set_trans with (1:=H0).
 apply H; simpl; trivial.
Qed.

Lemma repl1_morph : forall x y F G,
  eq_set x y ->
  (forall x' y', eq_set (proj1_sig x') (proj1_sig y') ->
   eq_set (F x') (G y')) ->
  eq_set (repl1 x F) (repl1 y G).
intros.
assert (forall z z', eq_set (proj1_sig z) (proj1_sig z') ->
        eq_set (F z) (F z')).
 intros.
 assert (in_set (proj1_sig z') y).
  apply eq_elim with x; trivial.
  apply (proj2_sig z').
 apply eq_set_trans with (G (exist _ (proj1_sig z') H2)).
  apply H0; simpl; trivial.

  apply eq_set_sym; apply H0; simpl; apply eq_set_refl.
assert (forall z z', eq_set (proj1_sig z) (proj1_sig z') ->
        eq_set (G z) (G z')).
 intros.
 apply eq_set_sym in H.
 assert (in_set (proj1_sig z') x).
  apply eq_elim with y; trivial.
  apply (proj2_sig z').
 apply eq_set_trans with (F (exist _ (proj1_sig z') H3)).
  apply eq_set_sym; apply H0; simpl; apply eq_set_sym; trivial.

  apply H0; simpl; apply eq_set_refl.
apply eq_intro; intros.
 rewrite repl1_ax in H3|-*; trivial.
 destruct H3.
 assert (in_set (proj1_sig x0) y).
  apply eq_elim with x; trivial.
  apply (proj2_sig x0).
 exists (exist (fun y' => in_set y' y) (proj1_sig x0) H4). (* regression of unification *)
(* exists (exist _ (proj1_sig x0) H4).*)
 apply eq_set_trans with (1:=H3).
 apply H0; simpl; apply eq_set_refl.

 rewrite repl1_ax in H3|-*; trivial.
 destruct H3.
 assert (in_set (proj1_sig x0) x).
  apply eq_set_sym in H.
  apply eq_elim with y; trivial.
  apply (proj2_sig x0).
 exists (exist (fun y0 => in_set y0 _) (proj1_sig x0) H4). (* unif regression *)
 apply eq_set_trans with (1:=H3).
 apply eq_set_sym; apply H0; simpl; apply eq_set_refl.
Qed.

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

Notation "x ∈ y" := (in_set x y).
Notation "x == y" := (eq_set x y).

(* Deriving the existentially quantified sets *)

Lemma empty_ex: exists empty, forall x, ~ x ∈ empty.
exists empty.
exact empty_ax.
Qed.

Lemma pair_ex: forall a b, exists c, forall x, x ∈ c <-> (x == a \/ x == b).
intros.
exists (pair a b).
apply pair_ax.
Qed.

Lemma union_ex: forall a, exists b,
    forall x, x ∈ b <-> (exists2 y, x ∈ y & y ∈ a).
intros.
exists (union a).
apply union_ax.
Qed.

Lemma subset_ex : forall x P, exists b,
  forall z, z ∈ b <->
  (z ∈ x /\ exists2 z', z == z' & P z').
intros.
exists (subset x P).
apply subset_ax.
Qed.

Lemma power_ex: forall a, exists b,
     forall x, x ∈ b <-> (forall y, y ∈ x -> y ∈ a).
intros.
exists (power a).
apply power_ax.
Qed.

Lemma repl_ex: forall a (R:set->set->Prop),
    (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x ∈ a -> R x y -> R x y' -> y == y') ->
    exists b, forall x, x ∈ b <-> (exists2 y, y ∈ a & R y x).
Proof repl_ax.

(* Collection *)
Section Collection.

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

Section FromReplClassic.

Hypothesis EM : forall A:Prop, A \/ ~A.

(* von Neumann cumulative hierarchy (applied to any set) *)
Fixpoint V (x:set) := union (replf x (fun x' => power (V x'))).

Lemma V_morph : forall x x', eq_set x x' -> eq_set (V x) (V x').
induction x; destruct x'; intros.
simpl V; unfold replf; simpl sup.
apply union_morph.
simpl in H0.
destruct H0.
apply eq_intro; intros.
 destruct H2.
 destruct (H0 x).
 exists x0.
 apply eq_set_trans with (1:=H2).
 simpl elts.
 apply power_morph.
 auto.

 destruct H2.
 destruct (H1 x).
 exists x0.
 apply eq_set_trans with (1:=H2).
 simpl elts.
 apply power_morph.
 apply eq_set_sym; auto.
Qed.

Lemma V_def : forall x z,
  in_set z (V x) <-> exists y, in_set y x /\ incl_set z (V y).
destruct x; simpl; intros.
rewrite union_ax.
unfold replf; simpl.
split; intros.
 destruct H.
 destruct H0; simpl in *.
 exists (f x0); split.
  exists x0; apply eq_set_refl.

  red; rewrite <- power_ax.
  apply eq_elim with x; trivial.

 destruct H.
 destruct H.
 exists (power (V x)).
  rewrite power_ax; trivial.

  destruct H; simpl in *.
  exists x0.
  apply power_morph.
  apply V_morph; trivial.
Qed.

Lemma V_trans : forall x y z,
  z ∈ y -> y ∈ V x -> z ∈ V x.
intros x.
pattern x; apply wf_ax; trivial; clear x; intros.
rewrite V_def in H1|-*.
destruct H1.
destruct H1.
exists x0; split; trivial.
red; intros; eauto.
Qed.

Lemma V_pow : forall x, power (V x) == V (singl x).
intros.
apply eq_intro; intros.
 rewrite power_ax in H.
 rewrite V_def.
 exists x; split; trivial.
 exists tt; apply eq_set_refl.

 rewrite power_ax; intros.
 rewrite V_def in H; destruct H; destruct H.
 destruct H; simpl in *.
 apply eq_elim with (V x0); auto.
 apply V_morph; trivial.
Qed.

Lemma V_mono : forall x x',
  in_set x x' -> in_set (V x) (V x').
intros.
rewrite (V_def x').
exists x; split; trivial.
red; trivial.
Qed.

Lemma V_sub : forall x y y',
  in_set y (V x) -> incl_set y' y -> in_set y' (V x).
intros x.
pattern x; apply wf_ax; trivial; clear x; intros.
rewrite V_def in H0|-*.
destruct H0; destruct H0.
exists x0; split; trivial.
red; auto.
Qed.


Lemma V_compl : forall x z, in_set z (V x) -> in_set (V z) (V x). 
intros x.
pattern x; apply wf_ax; trivial; clear x; intros.
rewrite V_def in *.
destruct H0; destruct H0.
exists x0; split; trivial.
red; intros.
rewrite V_def in H2; destruct H2; destruct H2.
apply H1 in H2.
apply V_sub with (V x1); eauto.
Qed.

Lemma V_intro : forall x, incl_set x (V x).
intros x.
pattern x; apply wf_ax; trivial; clear x; intros.
red; intros.
rewrite V_def.
exists z; split; auto.
Qed.

Lemma V_idem : forall x, V (V x) == V x.
intros.
apply eq_intro; intros.
 rewrite V_def in H; destruct H; destruct H.
 apply V_sub with (V x0); trivial.
 apply V_compl; trivial.

 apply V_sub with (V z).
  apply V_mono; trivial.
  apply V_intro.
Qed.

Lemma rk_induc :
  forall P:set->Prop,
  (forall x, (forall y, y ∈ V x -> P y) -> P x) ->
  forall x, P x.
intros.
cut (forall y, incl_set (V y) (V x) -> P y).
 intros.
 apply H0.
 red; trivial.
induction x using wf_ax; trivial; intros.
apply H; intros.
apply H1 in H2.
rewrite V_def in H2; destruct H2; destruct H2.
apply H0 with x0; trivial.
red; intros.
rewrite V_def in H4; destruct H4; destruct H4.
apply H3 in H4.
apply V_sub with (V x1); trivial.
apply V_compl; trivial.
Qed.

(* classical *)
Lemma V_total : forall x y, in_set (V x) (V y) \/ incl_set (V y) (V x).
intros x y.
revert x.
pattern y; apply wf_ax; trivial; clear y.
intros y Hy x.
destruct (EM (exists y', y' ∈ V y /\ incl_set (V x) y')).
left.
destruct H; destruct H.
apply V_sub with x0; trivial.

right; red; intros.
rewrite V_def in H0; destruct H0; destruct H0.
assert (exists w, w ∈ V x /\ ~ w ∈ V x0).
 destruct (EM (exists w, w ∈ V x /\ ~ w ∈ V x0)); trivial.
 assert (~ incl_set (V x) (V x0)).
  red; intros; apply H.
  exists (V x0); split; trivial.
  apply V_mono; trivial.
 elim H3; red; intros.
 destruct (EM (z0 ∈ V x0)); trivial.
 elim H2.
 exists z0; split; trivial.
destruct H2; destruct H2.
destruct (Hy _ H0 x1).
 elim H3.
 apply V_sub with (V x1); trivial.
 apply V_intro.

 apply V_sub with (V x1).
  apply V_compl; trivial.

  red; auto.
Qed.

Definition lst_rk (P:set->Prop) (y:set) :=
  P y /\
  (exists w, y == V w) /\
  (forall x, (exists w, x == V w) -> P x -> incl_set y (V x)).

Lemma lst_rk_morph :
  forall (P P':set->Prop), (forall x x', x == x' -> (P x <-> P' x')) ->
  forall y y', y == y' -> lst_rk P y -> lst_rk P' y'.
intros.
destruct H1.
destruct H2.
split; [|split].
 revert H1; apply H; trivial.

 destruct H2.
 exists x.
 apply eq_set_trans with y; trivial.
 apply eq_set_sym; trivial.

 red; intros.
 apply (H3 x); trivial.
 revert H5; apply H; apply eq_set_refl.

 apply eq_elim with y'; trivial.
 apply eq_set_sym; trivial.
Qed.

Lemma lst_incl : forall P y, lst_rk P y -> P y. 
destruct 1.
trivial.
Qed.

Lemma lst_fun : forall P y y', lst_rk P y -> lst_rk P y' -> y == y'.
destruct 1; destruct 1.
destruct H0; destruct H2.
apply H3 in H1; trivial; apply H4 in H; trivial.
clear H3 H4.
apply eq_intro; intros.
 apply H1 in H3.
 destruct H2.
 apply eq_elim with (V x).
 2:apply eq_set_sym; trivial.
 apply eq_elim with (V (V x)).
 2:apply V_idem.
 apply eq_elim with (V y'); trivial.
 apply V_morph; trivial.

 apply H in H3.
 destruct H0.
 apply eq_elim with (V y); trivial.
 apply eq_set_trans with (V (V x)).
  apply V_morph; trivial.
 apply eq_set_trans with (V x).
  apply V_idem.
 apply eq_set_sym; trivial.
Qed.

Lemma lst_ex : forall (P:set->Prop), (forall x x', eq_set x x' -> P x -> P x') ->
  (exists x, P (V x)) -> exists y, lst_rk P y.
intros P Pm.
destruct 1.
revert H.
pattern x; apply rk_induc; clear x; intros.
destruct (EM (exists z, z ∈ V x /\ P (V z))).
 destruct H1; destruct H1; eauto.

 exists (V x).
 split; [|split]; trivial.
  exists x; apply eq_set_refl.

  red; intros.
  destruct (V_total x0 x); auto.
  elim H1.
  destruct H2.
  exists x0; split.
   apply V_sub with (V x0); trivial.
   apply V_intro.

   apply Pm with x0; trivial.
   apply eq_set_trans with (V x1); trivial.
   apply eq_set_trans with (V (V x1)).
    apply eq_set_sym; apply V_idem.
   apply eq_set_sym; apply V_morph; trivial.
Qed.


Lemma coll_ax : forall A (R:set->set->Prop), 
    (forall x x' y y', in_set x A ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x, in_set x A -> exists y, R x y) ->
    exists B, forall x, in_set x A -> exists y, in_set y B /\ R x y.
intros.
pose (P := fun x y => x ∈ A /\ exists z, z ∈ y /\ R x z).
assert (Pm : forall x x', x ∈ A -> x == x' -> forall y y', y == y' -> P x y -> P x' y').
 intros.
 destruct H4.
 destruct H5; destruct H5.
 split; [|exists x0;split].
  apply in_reg with x; trivial.

  apply eq_elim with y; trivial.

  apply H with x x0; trivial.
  apply eq_set_refl.
assert (Pwit : forall x, x ∈ A -> exists y, P x (V y)). 
 intros.
 destruct (H0 x); trivial.
 exists (singl x0); split; trivial.
 exists x0; split; trivial.
 apply V_sub with (V x0).
  apply V_mono; exists tt; apply eq_set_refl.
  apply V_intro.
destruct (@repl_ax A (fun x y => lst_rk (P x) y)); eauto using lst_fun, lst_ex.
 intros.
 apply lst_rk_morph with (P x) y; trivial.
 intros.
 split; intros; eauto.
  apply Pm with x' x'0; trivial.
   apply in_reg with x; trivial.
   apply eq_set_sym; trivial.
   apply eq_set_sym; trivial.

 exists (union x); intros.
 destruct lst_ex with (P x0); auto.
  apply Pm; trivial; apply eq_set_refl.

  specialize lst_incl with (1:=H3).
  destruct 1 as (_,(?,(?,?))).
  exists x2; split; trivial.
  rewrite union_ax.
  exists x1; trivial.
  rewrite H1.
  exists x0; auto.
Qed.

Lemma coll2_ax : forall A (R:set->set->Prop) x,
    (forall x x' y y', in_set x A ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (exists y, R x y) ->
    in_set x A ->
    exists B, exists y, in_set y B /\ R x y.
intros.
assert (forall z, z ∈ singl x -> z ∈ A).
 intros.
 destruct H2; simpl in *.
 apply in_reg with x; trivial.
 apply eq_set_sym; trivial.
destruct (coll_ax (singl x) R); intros; eauto.
 destruct H0.
 exists x1.
 apply H with x x1; trivial.
  destruct H3; simpl in *.
  apply eq_set_sym; trivial.

  apply eq_set_refl.

 exists x0.
 apply H3.
 exists tt; apply eq_set_refl.
Qed.
 
End FromReplClassic.

End Collection.


(* Infinity *)

Lemma infinity_ex: exists2 infinite,
    (exists2 empty, (forall x, ~ x ∈ empty) & empty ∈ infinite) &
    (forall x, x ∈ infinite ->
     exists2 y, (forall z, z ∈ y <-> (z == x \/ z ∈ x)) &
       y ∈ infinite).
exists infinity.
 exists empty.
  exact empty_ax.
  exact infty_ax1.

 intros.
 exists (union (pair x (pair x x))); intros.
  rewrite union_ax.
  split; intros.
   destruct H0.
   rewrite pair_ax in H1; destruct H1.
    right.
    unfold in_set.
    apply eq_elim with x0; trivial.

    left.
    specialize eq_elim with (1:=H0) (2:=H1); intro.
    rewrite pair_ax in H2; destruct H2; trivial.

   destruct H0.
    exists (pair x x).
     rewrite pair_ax; auto.

     rewrite pair_ax; right; apply eq_set_refl.

    exists x; trivial.
    rewrite pair_ax; left; apply eq_set_refl.

  apply infty_ax2; trivial.
Qed.


(* Rk: decision of membership implies excluded-middle *)
Lemma set_dec_EM :
  (forall x y, in_set x y \/ ~ in_set x y) ->
  (forall P, P \/ ~ P).
intros.
destruct (H empty (subset (power empty) (fun _ => P))).
 left.
 rewrite subset_ax in H0; destruct H0.
 destruct H1; trivial.
 right; red; intros; apply H0.
 rewrite subset_ax.
 split.
  rewrite power_ax; intros.
  elim empty_ax with y; trivial.

  exists empty; trivial.
  apply eq_set_refl.
Qed.

(* Failed attempt to build (set-theoretical) choice axiom. *)

Section Choice.

Hypothesis C : forall X:Type, X + (X->False).

Lemma impl_choice_ax : forall A B, choice A B.
red; intros.
exists (fun x =>
  match C ({y:B|R x y}) with
  | inl y => proj1_sig y
  | inr h =>
    False_rect B (let (y,r) := H x in h (exist _ y r))
  end).
intros.
destruct (C {y:B|R x y}).
 destruct s; trivial.

 destruct (H x).
 destruct (f (exist (fun y => R x y) x0 r)).
Qed.

Definition choose (x:set) :=
  match C (idx x) with
  | inl i => elts x i
  | _ => empty
  end.

Lemma choose_ax : forall a, (exists x, x ∈ a) -> choose a ∈ a.
intros.
unfold choose.
destruct (C (idx a)).
 exists i; apply eq_set_refl.

 destruct H.
 destruct H.
 elim (f x0).
Qed.

(* ... but choose is not a morphism! *)
Lemma choose_not_morph : ~ forall x x', x == x' -> choose x == choose x'.
unfold choose; red; intros.
generalize (H (sup bool (fun b => if b then empty else singl empty))
              (sup bool (fun b => if b then singl empty else empty))).
simpl; intros.
assert (singl empty == empty).
 refine (let H1 := H0 _ in _).
  split; intros.
   exists (negb i).
   destruct i; apply eq_set_refl.

   exists (negb j).
   destruct j; apply eq_set_refl.

  clear H0.
  destruct (C bool).
   destruct b; auto with *.
   apply eq_set_sym; trivial.

   destruct (f true).
elim empty_ax with empty.
apply eq_elim with (singl empty); trivial.
exists tt; apply eq_set_refl.
Qed.

End Choice.

(* Regularity is classical *)

Section Regularity.

Definition regularity :=
  forall a a0, a0 ∈ a ->
  exists2 b, b ∈ a & ~(exists2 c, c ∈ a & c ∈ b).

Lemma regularity_ax (EM:forall P,P\/~P): regularity.
red.
induction a0; intros.
destruct (EM (exists i:X, f i ∈ a)).
 destruct H1; eauto.

 exists (sup X f); trivial.
 red; intros; apply H1.
 destruct H2.
 destruct H3; simpl in *.
 exists x0.
 apply in_reg with x; trivial.
Qed.

Lemma regularity_is_classical (reg : regularity) : forall P, P \/ ~P.
intros.
destruct (reg (subset (pair empty (power empty))
           (fun x => x == power empty \/ x == empty /\ P)) (power empty)).
 rewrite subset_ax.
 split.
  rewrite pair_ax; right ;apply eq_set_refl.
  exists (power empty).
   apply eq_set_refl.
   left; apply eq_set_refl.

 rewrite subset_ax in H; destruct H.
 destruct H1.
 destruct H2.
  right ;red; intros.
  apply H0.
  exists empty.
   rewrite subset_ax.
   split.
    rewrite pair_ax; left; apply eq_set_refl.
    exists empty.
     apply eq_set_refl.
     right; split; trivial.
     apply eq_set_refl.

    apply eq_elim with x0.
    2:apply eq_set_sym; trivial.
    apply eq_elim with (power empty).
    2:apply eq_set_sym; trivial.
    rewrite power_ax; trivial.

  destruct H2; auto.
Qed.

End Regularity.

End IZF_R.
