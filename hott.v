Require Import Sublogic.
Require Import paths.


Lemma eq_trans_cancel_l {A} {x y z:A} (e:x=y) (e1 e2:y=z) :
  e * e1 = e * e2 -> e1 = e2.
destruct e; rewrite !eq_trans_idl; trivial.
Qed.
Lemma eq_trans_cancel_r {A} {x y z:A} (e1 e2:x=y) (e:y=z) :
  e1 * e = e2 * e -> e1 = e2.
destruct e; trivial.
Qed.

(*

Lemma transport_eql A (x y z:A) (e1:y=x)(e2:y=z):
  transport (fun x => x=z) e1 e2 = eq_sym e1 * e2.
destruct e1; simpl.
destruct e2; reflexivity.  
Qed.
Lemma transport_eqr A (x y z:A) (e1:y=z)(e2:x=y):
  transport (fun z => x=z) e1 e2 = e2 * e1.
destruct e1; simpl.
reflexivity.  
Qed.
*)
(*
Lemma f_app_trans {A B} {f g h:forall x:A,B x} (e1:f=g)(e2:g=h) x :
  f_app (e1*e2) x = f_app e1 x * f_app e2 x.
destruct e2; trivial.
Defined.
Lemma f_app_sym {A B} {f g:forall x:A,B x} (e:f=g) x :
  f_app (eq_sym e) x = eq_sym (f_app e x).
destruct e; trivial.
Defined.
 *)

Definition to_singl {A}{a b:A} (e:a=b) :
    existT (fun y => a = y) a eq_refl = existT(fun y=>a=y) b e :=
  match e in _=y return existT(fun c=>a=c) a eq_refl=existT(fun c=>a=c) y e
  with eq_refl => eq_refl end.



Class type_fun_ext : Prop :=
  Type_fun_ext :
    forall {A:Type}{B:A->Type}{f g:forall x:A,B x},
      (forall x, f x = g x) -> f = g.


(** h-levels *)

Definition isContr X := {x:X & forall y, y=x}.
Definition isProp X := forall x y:X, x=y.


Class prop_fun_ext : Prop :=
  Prop_fun_ext :
    forall {A:Type}{B:A->Prop}, (forall x, isProp (B x)) ->
    forall {f g:forall x:A,B x},
      (forall x, f x = g x) -> f = g.

Global Instance type_to_prop_fun_ext : type_fun_ext -> prop_fun_ext.
exact (fun ext A B Bs => ext A B).
Defined.

Lemma isContr_singl {A} (c:A) : isContr {x:A & x=c}.
exists (existT (fun x=>x=c) c eq_refl).
intros (y,e).
destruct e; reflexivity.
Defined.
Lemma isContr_singl_sym {A} (c:A) : isContr {x:A & c=x}.
exists (existT (fun x=>c=x) c eq_refl).
intros (y,e).
destruct e; reflexivity.
Defined.
  
Lemma isContr_intro {X} (c:X) (h:forall x, x=c) : isContr X.
exists c; trivial.
Defined.

Lemma isContr_True : isContr True.
apply isContr_intro with I.
destruct x; reflexivity.
Qed.

Lemma isContr_eqv A B : isContr A -> isContr B -> eqv A B.
intros (a,ea) (b,eb).
exists (fun _ => b) (fun _ =>a); auto.
Defined.


Lemma isContr_intro_prop {X} (x:X) (Xp:isProp X) : isContr X.
exists x.
intros; apply Xp.
Defined.

Lemma isContr_isProp {X} : isContr X -> isProp X.
red; intros.
transitivity (projT1 X0).
 apply (projT2 X0).

 symmetry; apply (projT2 X0).
Defined.

Lemma isProp_True : isProp True.
apply isContr_isProp.
apply isContr_True.  
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

Lemma is_prop_uip A (x y:A) :
  isProp A -> isProp (x=y).
red; intros.
assert (K : forall (r : x = y), r = H x x * eq_sym (H y x)).
 intro r; destruct r.
 destruct (H x x); reflexivity.
eapply eq_trans;[|symmetry];apply K.
Qed.

Lemma isProp_by_retr {A B} : isProp A -> retr B A -> isProp B.
intros Ap E x y.
rewrite <-(rgf _ _ E x).
rewrite <-(rgf _ _ E y).
apply f_equal with (f:=rg _ _ E).
apply Ap.
Qed.


Section isPropTheoryWithFunExt.

  Context {fun_ext : prop_fun_ext}.
(*
Axiom prop_fun_ext : forall A (P:A->Prop) (f g:forall x,P x),
  (forall x, f x = g x) -> f = g.
*)
Lemma isProp_forall : forall A (P:A->Prop),
  (forall x, isProp (P x)) -> isProp (forall x:A, P x).
red; intros.
apply Prop_fun_ext.
 intros a.
 apply H.

 intros a.
 apply H.
Qed.

Lemma isContr_forall_prop : forall A (B:A->Prop), (forall x:A, isContr (B x)) -> isContr(forall x,B x).
intros.
apply isContr_intro_prop.
 exact (fun x => projT1 (X x)).

 apply isProp_forall.
 intros.
 apply isContr_isProp; trivial.
Qed.

(* We need P to be a *set*...
Lemma prop_fun_ext' : forall A (P:A->Prop) (f g:forall x,P x),
  (forall x, f x = g x) -> f = g.
intros.
generalize (fun h => isProp_forall A (fun a=>{p:P a|p=f a}) h (fun a=>exist _ (f a) (eq_refl (f a))) (fun a => exist _ (g a) (eq_sym (H a)))).
intros.
generalize (fun h => f_equal (fun f a => proj1_sig (f a)) (H0 h)).
simpl.
intros.
apply H1.
red; intros x (p,e) (q,e').
apply sig_eq with (eq_trans e (eq_sym e')).
simpl.
 *)

Lemma isProp_iff {A B:Prop} : isProp A -> isProp B -> isProp (A<->B).
intros.
apply isProp_conj; apply isProp_forall; trivial.
Qed.


Lemma isProp_isContr X : isProp (isContr X).
red; intros (x1,e1) (x2,e2).
apply sigT_eq_intro with (e:=e2 x1); simpl.
unfold eqD.
rewrite transport_rng.
apply fun_ext; intros.
 apply is_prop_uip.
 apply isContr_isProp.
 exists x1; exact e1.
assert (h := f_eqD e2 (eq_sym (e1 x))).
red in h.
elim h.
clear h.
rewrite !transport_eq, !f_equal_cst, !f_equal_id; simpl.
rewrite eq_trans_idl, eq_sym_sym; trivial.
Qed.

Lemma isProp_isProp A : isProp (isProp A).
red; intros.
apply isProp_forall; intros a.
apply isProp_forall; intros a'.
apply is_prop_uip; trivial.
Qed.

End isPropTheoryWithFunExt.

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



Lemma retr_paths {A B} (R:retr A B) {x y} : retr (x=y) (rf _ _ R x = rf _ _ R y).
exists (fun e => f_equal (rf _ _ R) e)
       (fun e => eq_sym (rgf _ _ R x) * (f_equal (rg _ _ R) e * rgf _ _ R y)).
intros e.
rewrite f_equal_compose.
rewrite (f_equal_qid _ (rgf _ _ R) e).
rewrite <- !eq_trans_assoc.
rewrite eq_sym_invl, eq_trans_idl.
rewrite eq_trans_assoc.
rewrite eq_sym_invl; trivial.
Qed.

  Lemma isSet_by_retr {A B} : isSet A -> retr B A -> isSet B.
intros As R x y.
eapply isProp_by_retr with (2:=retr_paths R).
red; intros; apply As.
Qed.


Lemma isSet_by_eqv {A B} : isSet A -> eqv B A -> isSet B.
intros As E.
apply isSet_by_retr with (1:=As).
apply eqv2retr; trivial.
Qed.

(** Set equivalences (isomorphisms) *)

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


Lemma isSet_sigma X (R:X->Type) :
   isSet X -> (forall x, isSet (R x)) -> isSet (@sigT X R).
intros Xs Rs.
red; intros.
rewrite (sigT_proj1_intro p), (sigT_proj1_intro q).
pose (f:=fun c:{e1:projT1 x=projT1 y & eqD R e1 (projT2 x) (projT2 y)} => sigT_eq_intro x y (projT1 c) (projT2 c)).
change (f (existT _ (sigT_proj1 p) (sigT_proj2 p)) = 
        f (existT _ (sigT_proj1 q) (sigT_proj2 q))).
apply f_equal with (f:=f).
eapply sigT_eq_intro with (e:=Xs _ _ _ _); simpl.
apply Rs.
Qed.

Section isSetTheoryWithFunExt.

  Context {fun_ext : type_fun_ext}.

  Lemma isContr_forall A B:
    (forall x:A, isContr (B x)) -> isContr(forall x,B x).
intros.
apply isContr_intro_prop.
 exact (fun x => projT1 (X x)).

 intros f g.
 apply fun_ext; intros x.
 apply isContr_isProp with (1:=X x).
Defined.

Definition fun_ext_singl_raw {A B}{f g:forall x:A,B x}(e:forall x, f x =g x) :
    (fun x => existT (fun y => f x = y) (f x) eq_refl) =
    (fun x => existT (fun y => f x = y) (g x) (e x)).
Proof Type_fun_ext (fun x=> to_singl (e x)).


Definition fun_ext_singl {A B}{f g:forall x:A,B x}(e:forall x, f x =g x) : f=g :=
  f_equal (fun (h : forall x, {u:_ & f x = u}) x => projT1 (h x))
          (fun_ext_singl_raw e).

Definition fun_ext_eqv {A B} {f g:forall x:A,B x} (w:f=g) :
  fun_ext_singl (f_app w) = w.
destruct w; simpl.
unfold fun_ext_singl.
replace (fun_ext_singl_raw (f:=f)(g:=f)(f_app eq_refl)) with
   (eq_refl (fun x => existT (fun y => f x = y) (f x) eq_refl)).
 reflexivity.

 apply is_prop_uip.
 apply isContr_isProp.
 apply isContr_forall.
 intros.
 apply isContr_singl_sym.
Qed.

Definition fun_ext_eqv2 {A B} {f g:forall x:A,B x} (w:forall x,f x=g x) :
  f_app (fun_ext_singl w) = w.
apply fun_ext; intros x.
unfold fun_ext_singl, f_app.
eapply eq_trans.
 apply f_equal_compose with
  (f0:=fun f0=>f0 x) (g0:= (fun (h:forall x,{u:_& f x = u}) x => projT1 (h x)))
  (e:=fun_ext_singl_raw w).
eapply eq_trans.
 symmetry; apply f_equal_compose with
  (f0:=fun x=>projT1 x) (g0:= fun h:forall x,{u:B x&f x=u} => h x)
  (e:=fun_ext_singl_raw w).
replace  (f_equal (fun h : forall x,{u:_&f x = u} => h x)
                  (fun_ext_singl_raw w))
  with (to_singl (w x)).
 unfold to_singl.
 destruct (w x); reflexivity.

 apply is_prop_uip.
 apply isContr_isProp.
 apply isContr_singl_sym.
Qed.

  Lemma isProp_forallT : forall {A B},
    (forall x:A, isProp (B x)) -> isProp (forall x, B x).
red; intros.
apply fun_ext; intros a.
apply H.
Qed.

  Lemma isProp_prod : forall {A B}, isProp A -> isProp B -> isProp (prod A B).
intros A B Ap Bp (x1,y1) (x2,y2).
f_equal; auto.
Qed.
    

(* fun_ext *)
  Lemma isProp_fun_eq {A B} {f g:forall x:A,B x} (Bp : forall x, isSet (B x)) : isProp (f=g).
intros e1 e2.  
rewrite <-(fun_ext_eqv e1), <-(fun_ext_eqv e2).
apply f_equal with (f:=fun_ext_singl).
unfold f_app.
apply fun_ext.
intros.
apply Bp.
Qed.

Lemma isSet_forall : forall {A B},
  (forall x:A, isSet (B x)) -> isSet (forall x, B x).
red; intros; apply isProp_fun_eq; trivial.
Qed.


Lemma prop_eqv A B (As:isSet A)(e1 e2:eqv A B) :
  (forall a, ef e1 a = ef e2 a) ->
  e1 = e2.
assert (Bs := isSet_by_eqv As (eqv_sym e1)).
destruct e1 as (f,g,gf,fg); destruct e2 as (f',g',gf',fg'); simpl; intros.
assert (forall b, g b = g' b).
 intros.
 transitivity (g (f (g b))).
  symmetry; trivial.
 transitivity (g' (f' (g b))).
  rewrite gf,gf'; trivial.
  rewrite <-H,fg; trivial.
apply fun_ext in H.  
apply fun_ext in H0.
revert gf' fg'.
destruct H; destruct H0.
intros.
apply f_equal2 with (f:=mkE f g).
 apply (isProp_forall _).
 red; intros; apply As.

 apply (isProp_forall _); intros.
 red; intros; apply Bs.
Qed.

(* Converse *)
  
  Hypothesis fext : forall A B, (forall x:A, isContr (B x)) -> isContr(forall x,B x).

  Lemma fun_ext_from_contr_forall : type_fun_ext.
red; intros.
pose (C x := {b:B x & b = f x}).
specialize fext with (1:=fun x=> isContr_singl (f x)).
apply isContr_isProp in fext.
red in fext.
specialize fext with
 (x:=fun x => existT (fun c=>c=f x) (f x) eq_refl)
 (y:=fun x => existT (fun c=>c=f x) (g x) (eq_sym (H x))).
simpl in fext.
pose (f1 :=fun (h:forall x:A, C x) x => projT1 (h x)).
apply f_equal with (f:=f1) in fext.
exact fext.
Qed.


End isSetTheoryWithFunExt.

(** Prop-truncation (with resizing since tr X : Prop !) *)


  Definition tr (X:Type) : Prop := forall P:Prop, isProp P -> (X->P) -> P.

  Definition tr_i {X} (x:X) : tr X := fun _ _ f => f x.
(*Definition tr_ind_nodep {X P} (Pp:isProp P) (h:X->P) (t:tr X) : P :=
  t P Pp h.*)

(*Parameter tr : Type -> Prop.
Parameter tr_prop : forall X, isProp (tr X).
Parameter tr_i : forall {X}, X -> tr X.*)
(*Axiom tr_ind_nodep : forall {X P:Type},
  isProp P -> (X->P) -> tr X -> P.*)

  Axiom tr_elim : forall {P:Type}, isProp P -> tr P -> P.


  Lemma tr_elim_eq : forall P (Pp:isProp P) x, tr_elim Pp (tr_i x) = x.
intros.
apply Pp.
Qed.
  
  Lemma tr_elim_prop {P:Prop} :
    isProp P -> tr P -> P.
intros Pp t; apply t; trivial.
Defined.

  Lemma tr_map {X Y} (f:X->Y) (t:tr X) : tr Y.
intros P Pp yp.
apply t.
 exact Pp.

 auto.
Qed.

Lemma tr_ind_nodep : forall {X P},
  isProp P -> (X->P) -> tr X -> P.
intros.
apply tr_map in X0; trivial.
apply tr_elim in X0; trivial.
Qed.

Lemma tr_ind_nodep_eq {X P} (Pp:isProp P) (f:X->P) x :
  tr_ind_nodep Pp f (tr_i x) = f x.
apply Pp.
Qed.

(*
Lemma tr_elim : forall {P:Type},
  isProp P -> tr P -> P.
intros P Pp t.
assert (iPp : isProp (itr P)).
 apply @isProp_by_retr with (A:=P); trivial.

apply tr_map with (1:=itr_i _) in t.
 apply tr_elim_prop in t.
apply @coe with (A:=itr P).
2:appl
apply (coe (prop_univ  
*)
(*Lemma tr_elim : forall {P:Type},
  isProp P -> tr P -> P.
intros.
apply @tr_ind_nodep with (X:=P); trivial.
Qed.
*)

Definition tr_f {P:Type} (tt:tr(tr P)) : tr P :=
  fun Q Qp (f:P->Q) => tt Q Qp (fun t => t Q Qp f).




Module trSub <: ConsistentSublogic.
  Definition Tr := fun P:Prop => tr P.
  Definition TrI (P:Prop) (p:P) : Tr P := tr_i p.
  Definition TrP (P:Prop) (p:Tr (Tr P)) : Tr P := tr_f p.
  Definition TrMono (P Q:Prop) (f:P->Q) (p:Tr P) : Tr Q := tr_map f p.
  Notation "# T" := (Tr T).
  Definition TrCons : ~ Tr False := tr_elim_prop isProp_False.
End trSub.
Module TrSubThms <: SublogicTheory := BuildConsistentSublogic trSub.
Import trSub TrSubThms.
Lemma isL_tr : forall P, isL (tr P).
red; intros.
apply tr_f; trivial.
Qed.
Hint Resolve isL_tr.

Instance Tr_morph : Proper (iff ==> iff) Tr. 
do 2 red; intros.
split; apply TrMono; apply H.
Qed.



Definition tr_ind_tr {X} (P : Type)
           (h:X -> tr P) (x:tr X) : tr P :=
  tr_f (tr_map h x).

Lemma descr :
  forall {A} {P:A->Prop}, (forall a, isProp (P a)) ->
  (forall a a', P a -> P a' -> a=a') ->
  (tr {a:A | P a}) -> {a:A | P a}.
intros.
elim H1 using tr_ind_nodep; trivial.
apply isProp_sig; trivial.
Qed.

Lemma descr_eq A (P:A->Prop) (Pp:forall a, isProp(P a))
      (uniq : forall a a', P a -> P a' -> a=a')
      (w:tr{a|P a}) (x:A) (px : P x) :
  proj1_sig (descr Pp uniq w) = x.
apply uniq; trivial.
exact (proj2_sig (descr Pp uniq w)).
Qed.


Lemma tr_ex_sig {A} {P:A->Prop} :
  (tr (exists x, P x)) <-> tr{x|P x}.
split; intros h; elim h using tr_ind_tr; intros; auto.
 destruct H; apply tr_i; eauto.
 destruct X; apply tr_i; eauto.
Qed.

Lemma tr_neg X : tr (X->False) -> X -> False.
intros.
elim H using tr_ind_nodep; intros.
 apply isProp_False.
auto.
Qed.

Section Truncation.

Context {fun_ext : prop_fun_ext}.

Lemma tr_prop X : isProp (tr X).
apply (isProp_forall _); intros P.
apply (isProp_forall _); intros Pp.
apply (isProp_forall _); trivial.
Qed.

Inductive itr (A:Type) : Prop := itr_i (_:A).
Lemma itr_prop {A} : isProp A -> isProp (itr A).
intros As.
apply @isProp_by_retr with (A:=A); trivial.
exists (fun i:itr A => tr_elim As (let (i) := i in tr_i i)) (fun i => itr_i _ i).
intros; destruct a.
replace (tr_elim As (tr_i a)) with a; trivial.
Qed.

Lemma tr_ind {X} (P : tr X -> Type) :
    (forall t, isProp (P t)) ->
    (forall x, P (tr_i x)) ->
    forall t:tr X, P t.
intros Pp h t.
elim t using tr_ind_nodep; trivial.
intros x.
replace t with (tr_i x); trivial.
apply tr_prop.
Qed.

Lemma tr_ind_eq {X} (P:tr X->Type) Pp h x :
  tr_ind P Pp h (tr_i x) = h x.
apply Pp.
Qed.

Section TruncationSetInduction.
  Context
    {X : Type}
    (P : tr X -> Type)
    (Ps : forall x, isSet (P x))
    (h : forall (x:X), P (tr_i x))
    (hcomp :
       forall x y, eqD P (tr_prop X (tr_i x) (tr_i y)) (h x) (h y)).

  Let P' (x:tr X) := {p:P x | tr{x':X|eqD P (tr_prop X (tr_i x') x) (h x') p}}.

  Let P'_prop x : isProp (P' x).
apply isProp_sig.
 intros; apply tr_prop.

 intros p1 p2 i1 i2.
 elim i1 using tr_ind; clear i1.
  red; intros; apply Ps.
 intros (x1,e1).
 elim i2 using tr_ind; clear i2.
  red; intros; apply Ps.
 intros (x2,e2).
  red in e1,e2.
  rewrite <-e1,<-e2.
  rewrite <- (hcomp x1 x2).
  transitivity (transport P (tr_prop _ (tr_i x1) (tr_i x2) * tr_prop _ (tr_i x2) x) (h x1)).
   f_equal.
   apply is_prop_uip; apply tr_prop.

   rewrite transport_trans; trivial.
Qed.

 Lemma tr_ind_set (q:tr X) : P q.
assert (p:P' q).
 apply tr_ind.
  intros; apply P'_prop.

  intros x ; exists (h x).
  apply tr_i; exists x.
  replace (tr_prop _ (tr_i x) (tr_i x)) with (eq_refl (tr_i x)).
   reflexivity.

   apply is_prop_uip; apply tr_prop.
exact (projT1 p).
Defined.

 Lemma tr_ind_set_eq (x:X) :
  tr_ind_set (tr_i x) = h x.
unfold tr_ind_set.
rewrite tr_ind_eq; simpl.
reflexivity.
Qed.


End TruncationSetInduction.

Lemma tr_ind_set_nodep X P (Ps:isSet P) (h:X->P) (hcomp : forall x y, h x = h y) (q:tr X) : P.
apply tr_ind_set with (P0:=fun _ =>P) (h0:=h); trivial.
intros.
destruct (tr_prop X (tr_i x) (tr_i y)); apply hcomp.
Defined.

Lemma tr_ind_set_nodep_ind X P Ps h hcomp Q (Qs:forall p, isProp(Q p)) q :
  (forall x, Q (h x)) ->
  Q (tr_ind_set_nodep X P Ps h hcomp q) .
intros.
unfold tr_ind_set_nodep.
unfold tr_ind_set. 
elim q using tr_ind.
 intros; apply Qs.

 intros x; rewrite tr_ind_eq; simpl.
 apply X0.
Qed.

Hint Resolve tr_prop isProp_forall isProp_conj isProp_iff.

(*
Lemma prop_fun_ext_type {A B} (Bp:forall x:A, isProp (B x)) {f g:forall x:A,B x} :
  (forall x, f x = g x) -> f = g.
intros eqfg.
pose (f' := fun x => itr_i _ (f x)).
pose (g' := fun x => itr_i _ (g x)).
assert (f' = g').
 apply fun_ext;[intros; apply itr_prop; apply Bp|].
 intros x.
 apply f_equal with (f:=itr_i _). 
 apply eqfg.
assert (f = fun x => tr_elim (Bp x) (f' x)).
red in fun_ext.


pose (f' := fun x => tr_i (f x)).
pose (g' := fun x => tr_i (g x)).
assert (f' = g').
 apply fun_ext;[intros; apply tr_prop|].
 intros x.
 apply f_equal with (f:=tr_i). 
 apply eqfg.
assert (f = fun x => tr_elim (Bp x) (f' x)).
red in fun_ext.

unfold tr_elim.
_ *)
 
End Truncation.
Global Hint Resolve tr_prop isProp_forall isProp_conj isProp_iff.
Arguments tr_ind {_} X P _ _ t.
Arguments tr_prop {_} X x y.
Arguments isProp_isProp {_} A _ _.
Arguments isProp_forall {_} A P _ x y.

(** Predicate extensionality: consequence of univalence *)
Definition iffT A B := prod (A->B) (B->A).

Lemma iffT_trans {A B C}: iffT A B -> iffT B C -> iffT A C.
intros (?,?) (?,?); split; auto.
Defined.

Class type_predicate_ext :=
  Type_pred_ext :
    forall {A} {P Q:A->Type},
      (forall a, isProp (P a)) ->
      (forall a, isProp (Q a)) ->
      (forall a, iffT (P a) (Q a)) ->
      P = Q.

Section PredExt.

  Context
    {fun_ext : type_fun_ext}
    {pred_ext :type_predicate_ext}.
 
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

Definition pred_eqv {A} {P Q:A->Type} (e:P=Q) a : iffT (P a) (Q a).
Proof ((fun x => match e in _=X return X a with eq_refl => x end),
       (fun x => match eq_sym e in _=X return X a with eq_refl => x end)).

(* Version of pred_ext that returns the reflexivity when
   given the identity equivalence, so it is the inverse of pred_eqv *)
Definition pred_ext' {A} {P Q:A->Type}
  (Pp : forall a, isProp (P a)) (Qp : forall a, isProp (Q a))
  (e:forall a, iffT (P a) (Q a)) : P=Q :=
  eq_sym (Type_pred_ext Pp Pp (pred_eqv eq_refl)) *
  Type_pred_ext Pp Qp e.

Definition pred_ext_eqv {A} {P Q:A->Type}
           (Pp : forall a, isProp (P a)) (Qp : forall a, isProp (Q a))
           (w:P=Q) :
  pred_ext' Pp Qp (pred_eqv w) = w.
revert Qp; destruct w.
simpl; intros.  
unfold pred_ext'.
replace Qp with Pp.
2:apply isProp_forall; intros; apply isProp_isProp.
destruct (Type_pred_ext Pp Pp (pred_eqv eq_refl)); reflexivity.
Qed.

Lemma isProp_pred_eq {A} {P Q:A->Type} :
  (forall a, isProp (P a)) ->
  (forall a, isProp (Q a)) ->
  isProp (P=Q).
intros Pp Qp e1 e2.  
rewrite <-(pred_ext_eqv Pp Qp e1), <-(pred_ext_eqv Pp Qp e2).
apply f_equal with (f:=pred_ext' Pp Qp).
apply isProp_forallT; intros a.
apply isProp_prod.
 apply isProp_forallT; intros _; trivial.
 apply isProp_forallT; intros _; trivial.
Qed.

Lemma prop_ext (P Q:Type) (Pp:isProp P) (Qp:isProp Q) :
  iffT P Q -> P=Q.
intros.
apply (@f_app _ _ (fun _ => P) (fun _ =>Q)) with (2:=tt).
apply pred_ext; auto.
Qed.

End PredExt.

(** Quotient *)

Require Import Setoid.

Module Quo.

Section Quo.
Context
  {fun_ext : type_fun_ext}
  {pred_ext : type_predicate_ext}.
  
Class isClass {X} (R:X->X->Prop) (P:X->Type) := mkCl {
  cl_prop : forall x, isProp (P x);
  wit : X;
  wit_ok : P wit;
  uniq :  forall y, iffT (P y) (R wit y)
}.
 
Class isRel {X} (R:X->X->Prop) := {
  isP : forall x y, isProp (R x y);
  isR :> Equivalence R
  }.


Instance isClass_eq {X} {R:X->X->Prop} (Rr:isRel R) x :
  isClass R (fun y => R x y).
exists x; intros; auto with *.
 apply isP.
split; trivial.
Qed.

                                         
Definition quo (X:Type) (R:X->X->Prop) :=
  { P : X->Type | tr (isClass R P) }.

Lemma isProp_quo_proj1 {X R} (x:quo X R) (z:X) :
  isProp (proj1_sig x z).
destruct x as (x,clx); simpl.
elim clx using tr_ind_nodep; intros.  
 apply (isProp_isProp _).

 apply X0.
Qed.

Lemma quo_proj1_wit {X R} (q:quo X R) :
  tr {x:_ & proj1_sig q x}.
destruct q as (x,clx); simpl.
elim clx using tr_ind_nodep; intros.  
 apply (tr_prop _).

 apply tr_i.
 exists wit.
 apply X0.
Qed.

Lemma quo_ext X R (Rr:isRel  R) (q1 q2:quo X R) :
  (forall x, iffT (proj1_sig q1 x) (proj1_sig q2 x)) ->
  q1 = q2.
intros.
apply sig_intro.
 intros.
 apply tr_prop.

 apply Type_pred_ext; trivial.
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
 apply (coe (eq_sym (f_app H y))).
 reflexivity.

 intros; apply quo_ext; simpl; intros; trivial.
 split; intros.
  transitivity x; auto with *.
  transitivity y; auto with *.
Qed.

Lemma class_quo_proj1 X R (Rr:isRel R) (q:quo X R) w :
  iffT (proj1_sig q w) (q = quo_i _ w).
split; intros.
 apply quo_ext; trivial.
 intros; simpl.
 assert (Pp := isProp_quo_proj1 q).
 destruct q as (P,Pc); simpl in *.
 elim Pc using tr_ind_nodep; intros.
  apply isProp_prod; apply isProp_forallT; auto.
  intros; apply Rr.
 destruct X1 as (_,w',_,eqvP).
 destruct eqvP with w.
 destruct eqvP with x.
 split; intros.
  transitivity w'; auto.
  symmetry; auto.

  apply p0.
  transitivity w; auto.

 subst q; simpl.
 reflexivity.
Qed.

Lemma quo_ind {X} {R:X->X->Prop} (Rr:isRel R) (P:quo X R->Type):
  (forall x, isProp (P x)) ->
  (forall (x:X), P (quo_i Rr x)) ->
  forall x:quo X R, P x.
intros Pp h x.
assert (w := quo_proj1_wit x).
elim w using tr_ind_nodep; auto.
clear w; intros (w,wdef).
apply class_quo_proj1 with (Rr:=Rr) in wdef.
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
elim H using tr_ind_nodep; intros.
 red; intros; apply Ps.
elim H0 using tr_ind_nodep; intros.
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

End Quo.
End Quo.
Export Quo.

Module Quo1.

Section Quo.
Context
  {fun_ext : type_fun_ext}
  {pred_ext : type_predicate_ext}.
  
Class isClass {X} (R:X->X->Prop) (P:X->Type) := mkCl {
  cl_prop : forall x, isProp (P x);
  wit : X;
  wit_ok : P wit;
  uniq :  forall y, iffT (P y) (R wit y)
}.
 
Class isRel {X} (R:X->X->Prop) := {
  isP : forall x y, isProp (R x y);
  isR :> Equivalence R
  }.


Instance isClass_eq {X} {R:X->X->Prop} (Rr:isRel R) x :
  isClass R (fun y => R x y).
exists x; intros; auto with *.
 apply isP.
split; trivial.
Qed.

                                         
Definition quo (X:Type) (R:X->X->Prop) :=
  { P : X->Type | tr (isClass R P) }.

Lemma isProp_quo_proj1 {X R} (x:quo X R) (z:X) :
  isProp (proj1_sig x z).
destruct x as (x,clx); simpl.
elim clx using tr_ind_nodep; intros.  
 apply (isProp_isProp _).

 apply X0.
Qed.

Lemma quo_proj1_wit {X R} (q:quo X R) :
  tr {x:_ & proj1_sig q x}.
destruct q as (x,clx); simpl.
elim clx using tr_ind_nodep; intros.  
 apply (tr_prop _).

 apply tr_i.
 exists wit.
 apply X0.
Qed.

Lemma quo_ext X R (Rr:isRel  R) (q1 q2:quo X R) :
  (forall x, iffT (proj1_sig q1 x) (proj1_sig q2 x)) ->
  q1 = q2.
intros.
apply sig_intro.
 intros.
 apply tr_prop.

 apply Type_pred_ext; trivial.
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
 apply (coe (eq_sym (f_app H y))).
 reflexivity.

 intros; apply quo_ext; simpl; intros; trivial.
 split; intros.
  transitivity x; auto with *.
  transitivity y; auto with *.
Qed.

Lemma class_quo_proj1 X R (Rr:isRel R) (q:quo X R) w :
  iffT (proj1_sig q w) (q = quo_i _ w).
split; intros.
 apply quo_ext; trivial.
 intros; simpl.
 assert (Pp := isProp_quo_proj1 q).
 destruct q as (P,Pc); simpl in *.
 elim Pc using tr_ind_nodep; intros.
  apply isProp_prod; apply isProp_forallT; auto.
  intros; apply Rr.
 destruct X1 as (_,w',_,eqvP).
 destruct eqvP with w.
 destruct eqvP with x.
 split; intros.
  transitivity w'; auto.
  symmetry; auto.

  apply p0.
  transitivity w; auto.

 subst q; simpl.
 reflexivity.
Qed.

Lemma quo_ind {X} {R:X->X->Prop} (Rr:isRel R) (P:quo X R->Type):
  (forall x, isProp (P x)) ->
  (forall (x:X), P (quo_i Rr x)) ->
  forall x:quo X R, P x.
intros Pp h x.
assert (w := quo_proj1_wit x).
elim w using tr_ind_nodep; auto.
clear w; intros (w,wdef).
apply class_quo_proj1 with (Rr:=Rr) in wdef.
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
elim H using tr_ind_nodep; intros.
 red; intros; apply Ps.
elim H0 using tr_ind_nodep; intros.
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

End Quo.
End Quo1.


(** Predicate extensionality: consequence of univalence *)
Class predicate_ext :=
  Pred_ext :
    forall {A} {P Q:A->Prop},
      (forall a, isProp (P a)) ->
      (forall a, isProp (Q a)) ->
      (forall a, P a <-> Q a) ->
      P = Q.

(* Set-truncation form Prop-truncation + quotients *)

Section SetTrunc.
Context
  {fun_ext : type_fun_ext}
  {pred_ext : type_predicate_ext}.

Definition tr0 X := quo X (fun x y => tr(x=y)). 

Instance isRel_treq {X} : isRel (fun x y:X => tr(x=y)).
split; auto with *.
split ;red; intros.
 apply tr_i; reflexivity.

 elim H using tr_ind_tr; intros; auto.
 apply tr_i; symmetry; trivial.

 elim H using tr_ind_tr; intros.
 elim H0 using tr_ind_tr; intros; auto.
 apply tr_i; transitivity y; trivial.
Qed.

Definition tr0_i {X} (x:X) : tr0 X := quo_i _ x.

Definition tr0_ind_set {X} (P:tr0 X->Type) :
  (forall x, isSet (P x)) ->
  (forall x:X, P (tr0_i x)) ->
  forall x', P x'.
intros.
apply (quo_ind_set _ _) with (h:=X0); trivial.
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

End SetTrunc.

Section PropUnivalence.

  Definition prop_univ :=
    forall (A B:Prop), isProp A -> isProp B -> (A<->B) -> A=B.

  Hypothesis univ : prop_univ.
  Hypothesis fun_ext : type_fun_ext.

  Lemma pred_ext_from_prop_fun_ext :
    forall A (P Q : A -> Prop),
       (forall a, isProp (P a)) ->
       (forall a, isProp (Q a)) -> (forall a : A, P a <-> Q a) -> P = Q.
intros A P Q Pp Qp e.
apply fun_ext; intros a.
apply univ; trivial.
Qed.
  
End PropUnivalence.

(** Univalence for sets *)

Section SetUnivalence.

  Definition set_univ :=
    forall {A B:Type}{f:A->B}{g:B->A},
      isSet A ->
      (forall a, g (f a) = a) /\ (forall b, f (g b) = b) ->
      A=B.
  Definition set_univ_comp (ax:set_univ) :=
    forall {A B:Type}{f:A->B}{g:B->A}{As:isSet A}
      (e:(forall a, g (f a) = a) /\ (forall b, f (g b) = b)),
    transport (fun X=>X) (ax _ _ _ _ As e) = f.

  Definition uni (ax:set_univ) {A B} As (e:eqv A B) : A=B :=
    ax A B _ _ As (conj (egf e) (efg e)).
 
  Lemma univ_inv {A B:Type} : A=B -> eqv A B.
intros e.
exists (transport (fun X=>X) e) (transport (fun X=>X) (eq_sym e)).    
destruct e; reflexivity.
destruct e; reflexivity.
Defined.


  Hypothesis univ : set_univ.
  Hypothesis univ_comp : set_univ_comp univ.

  Definition univ' {A B} (As:isSet A) (e:eqv A B) :=
    eq_sym (uni univ As (univ_inv eq_refl)) * uni univ As e.


Lemma univ_inv_eq A B As (e:A=B) :
  univ' As (univ_inv e) = e.
destruct e.
unfold univ'.
apply eq_sym_invl.
Qed.


Lemma univ_inv_comp_f A B C (e1:A=B)(e2:B=C):
  ef (univ_inv (e1 * e2)) =
  (fun a => ef (univ_inv e2) (ef (univ_inv e1) a)).
unfold univ_inv; simpl.
destruct e2; simpl; trivial.
Qed.
Lemma univ_inv_comp_g A B C (e1:A=B)(e2:B=C):
  eg (univ_inv (e1 * e2)) =
  (fun c => eg (univ_inv e1) (eg (univ_inv e2) c)).
unfold univ_inv; simpl.
destruct e2; simpl; trivial.
Qed.
Lemma univ_inv_inv_f A B (e:A=B):
  ef (univ_inv (eq_sym e)) =
  eg (univ_inv e).
  reflexivity.
Qed.
Lemma univ_inv_inv_g A B (e:A=B):
  eg (univ_inv (eq_sym e)) =
  ef (univ_inv e).
unfold univ_inv; simpl.
destruct e; reflexivity.
Qed.
Lemma univ_inv_inv_f' A B (e:A=B):
  ef (univ_inv (eq_sym e)) =
  fun b => transport (fun X=>X) (eq_sym e)
              (ef (univ_inv e) (transport (fun X=>X) (eq_sym e) b)).
simpl.
destruct e; reflexivity.
Qed.

(*Hypothesis fun_ext : forall {A B} {f g:A->B}, (forall x, f x=g x) -> f=g.*)


(*

Lemma transp_univ A B As Bs (e:eqv A B) a :
    transport (fun X=>X) (univ' As Bs e) a = ef _ _ e a.
unfold univ'.    
transitivity (ef _ _ (univ_inv As Bs (univ' As Bs e)) a); auto.
apply f_equal with (f:=fun e => ef A B e a).

apply prop_eqv; trivial.
simpl.
intros.
unfold univapply  2:rewrite fg; trivial.
 transitivity (
 unfold univ_inv0 at 2; simpl.
reflexivity.
replace iso with (univ_inv As As eq_refl).

transitivity (id f a); auto.
generalize (id f).
 *)

Lemma prop_ext_from_univ (P Q:Prop) (Pp:isProp P) (Qp:isProp Q) :
  (P<->Q) -> P=Q :>Type.
intros (f,g).
red in univ.
apply univ with f g.
 red; intros; apply is_prop_uip; trivial.
 split; intros; auto.
Qed.

End SetUnivalence.

Section Univalence.

  Lemma eq_weqv {X Y:Type} (e:X=Y) : weqv X Y.
refine (exist _ (univ_inv e) _).
destruct e; simpl; reflexivity.
Defined.
          
  Definition type_univ := forall X:Type, isContr {Y:Type & weqv X Y}.

  Hypothesis univ : type_univ.

  Lemma weqv_eq {X Y} : weqv X Y -> X=Y.
intros.
specialize isContr_isProp with (1:=univ X); intros wp.
red in wp.
specialize wp with (x:=existT _ X (eq_weqv eq_refl)) (y:=existT _ Y X0).
apply f_equal with (f:=projT1 (P:=_)) in wp; trivial.
Defined.

  Lemma univ_comp {A B:Type}(e:weqv A B) :
    transport (fun X=>X) (weqv_eq e) = ef (proj1_sig e).
unfold weqv_eq.
set (aux := isContr_isProp (univ A) (existT (weqv A) A (eq_weqv eq_refl)) (existT (weqv A) B e)).
change ((fun (w:{Y:Type&weqv A Y}) (e:existT (weqv A) A (eq_weqv eq_refl) = w) =>
           transport (fun X=>X) (f_equal (projT1 (P:=_)) e) =
           ef (proj1_sig (projT2 w))) (existT (weqv A) B e) aux).
case aux; simpl.
reflexivity.
Qed.

  Lemma univ_comp_sym {A B:Type}(e:weqv A B) :
    transport (fun X=>X) (eq_sym (weqv_eq e)) = eg (proj1_sig e).
unfold weqv_eq.
set (aux := isContr_isProp (univ A) (existT (weqv A) A (eq_weqv eq_refl)) (existT (weqv A) B e)).
change ((fun (w:{Y:Type&weqv A Y}) (e:existT (weqv A) A (eq_weqv eq_refl) = w) =>
           transport (fun X=>X) (eq_sym (f_equal (projT1 (P:=_)) e)) =
           eg (proj1_sig (projT2 w))) (existT (weqv A) B e) aux).
case aux; simpl.
reflexivity.
Qed.
  
End Univalence.
