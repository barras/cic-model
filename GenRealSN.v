Set Implicit Arguments.
Require Import List Compare_dec.
Require Import basic.
Require Import Sat.
Require Import Models.
Import Can.

Import Relation_Operators.

Definition prod_eq A B R1 R2 (p1 p2:A*B) :=
  R1 (fst p1) (fst p2) /\ R2 (snd p1) (snd p2).

Module Lc := Lambda.

(* The abstract normalization model. *)

Module Type Model.

Parameter X : Type.
Parameter inX : X * Lc.term -> X -> Prop.
Parameter eqX : X -> X -> Prop.
Parameter eqX_equiv : Equivalence eqX.
Notation "x \real y" := (inX x y) (at level 60).
Notation "x == y" := (eqX x y) (at level 70).

Definition Pi dom F f :=
  Inter _ (fun x:X =>
    Arr (fun u => (x,u) \real dom) (fun u => (f x, u) \real F x)).

Parameter in_ext: Proper (prod_eq eqX (@eq _) ==> eqX ==> iff) inX.

Parameter props : X.
Parameter app : X -> X -> X.
Parameter lam : X -> (X -> X) -> X.
Parameter prod : X -> (X -> X) -> X.

Definition eq_fun (x:X) (f1 f2:X->X) :=
  forall y1 y2 t, (y1,t) \real x -> y1 == y2 -> f1 y1 == f2 y2.

Parameter lam_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  lam x1 f1 == lam x2 f2.

Parameter app_ext: Proper (eqX ==> eqX ==> eqX) app.

Parameter prod_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  prod x1 f1 == prod x2 f2.

Parameter prod_intro : forall dom f F t,
  eq_fun dom f f ->
  eq_fun dom F F ->
  Pi dom F f t ->
  (lam dom f, t) \real prod dom F.

Parameter prod_elim : forall dom f x F t u,
  eq_fun dom F F ->
  (f,t) \real prod dom F ->
  (x,u) \real dom ->
  (app f x, Lc.App t u) \real F x.

Parameter impredicative_prod : forall dom F T U,
  eq_fun dom F F ->
  Lc.sn T ->
  Pi dom (fun _ => props) F U ->
  (prod dom F, Lc.App2 Lc.K T U) \real props.

Parameter beta_eq:
  forall dom F x u,
  eq_fun dom F F ->
  (x,u) \real dom ->
  app (lam dom F) x == F x.

Existing Instance eqX_equiv.
Existing Instance in_ext.
Existing Instance app_ext.

(* No empty types (False is inhabited) *)

  Parameter daemon : X.
  Parameter daemont : Lc.term.
  Parameter daemon_false : (daemon,daemont) \real prod props (fun P => P).

(* Equiping the model with saturated sets *)

Parameter inSAT_CR : forall x t A,
  (x,t) \real A -> is_cand (fun u => (x,u) \real A).

End Model.

(* We can instantiate the abstract model in ZF: *)

Module MM <: Model.

Require Import ZF ZFpairs ZFcoc ZFlambda.
Import IZF. 

Definition X : Type := set.

Definition eqX : X -> X -> Prop := eq_set.
Lemma eqX_equiv : Equivalence eqX.
auto with *.
Qed.

Notation "x == y" := (eqX x y) (at level 70).


Definition inTyp (p:X*Lc.term) (x:X) :=
  couple (Datatypes.fst p) (iLAM (Datatypes.snd p)) \in x.

Definition inX (p:X*Lc.term) (x:X) :=
  inTyp p x /\ is_cand (fun t => inTyp (Datatypes.fst p, t) x).

Notation "x \real y" := (inX x y) (at level 60).

Lemma in_ext: Proper (prod_eq eqX (@eq _) ==> eqX ==> iff) inX.
do 3 red; intros.
destruct x; destruct y; destruct H; simpl in H,H1.
unfold inX; simpl.
apply and_iff_morphism.
 unfold inTyp; simpl.
 rewrite H; rewrite H1; rewrite H0; reflexivity.

 unfold inTyp; simpl.
 subst t0.
 apply is_cand_morph; red; intros.
 rewrite H; rewrite H0; reflexivity.
Qed.

Definition Pi dom F f :=
  Inter _ (fun x:X =>
    Arr (fun u => (x,u) \real dom) (fun u => (f x, u) \real F x)).


Lemma inSAT_CR0 : forall x t A,
  (x,t) \real A -> is_cand (fun u => inTyp (x,u) A).
destruct 1; trivial.
Qed.

Lemma inSAT_CR : forall x t A,
  (x,t) \real A -> is_cand (fun u => (x,u) \real A).
intros.
specialize inSAT_CR0 with (1:=H); intro isCR; generalize isCR.
apply iff_impl.
apply is_cand_morph.
red; intros.
split; intros.
 split; trivial.

 destruct H0; trivial.
Qed.

Lemma inSAT_red : forall x A t u,
  (x,t) \real A -> Lc.red t u -> (x,u) \real A.
intros.
destruct (inSAT_CR H); eauto.
Qed.

Lemma inSAT_sn : forall x A t, (x,t) \real A -> Lc.sn t.
intros.
destruct (inSAT_CR H); eauto.
Qed.

Lemma inSAT_exp : forall x A t u,
  (x,t) \real A ->
  neutral u ->
  (forall v, Lc.red1 u v -> (x,v) \real A) ->
  (x,u) \real A. 
intros.
destruct (inSAT_CR H); eauto.
Qed.

Lemma inSAT_val : forall x x' A A' t,
  x == x' -> A == A' -> (x,t) \real A -> (x',t) \real A'.
intros.
revert H1; apply iff_impl.
apply in_ext; auto.
red; auto.
Qed.

Definition El (T:set) : set :=
  repl T
   (fun p x => (exists t, p == couple x (iLAM t)) /\
               is_cand (fun t => inTyp(x, t) T)).

Lemma repl1 : forall T,
  ZFrepl.repl_rel T
   (fun p x => (exists t, p == couple x (iLAM t)) /\
               is_cand (fun t => inTyp(x, t) T)).
split; intros.
 destruct H2 as ((t,eqx),iscan); split.
  exists t.
  rewrite <- H0; rewrite <- H1; trivial.

  revert iscan; apply iff_impl.
  apply is_cand_morph; red; intros.
  unfold inTyp; simpl.
  rewrite H1; reflexivity.

 destruct H0 as ((t1,eq1),_); destruct H1 as ((t2,eq2),_).
 rewrite eq1 in eq2.
 apply couple_injection in eq2; destruct eq2; trivial.
Qed.
Hint Resolve repl1.

Instance El_morph : morph1 El.
do 2 red; intros.
unfold El.
apply ZFrepl.repl_morph_raw; trivial.
do 2 red; intros.
apply and_iff_morphism.
 apply ex_morph; red; intros t.
 rewrite H0; rewrite H1; reflexivity.

 apply is_cand_morph; red; intros.
 unfold inTyp; simpl.
 rewrite H; rewrite H1; reflexivity.
Qed.

Lemma El_def : forall x T,
  x \in El T <-> (exists t, (x,t) \real T).
split; intros.
 unfold El in H.
 apply ZFrepl.repl_elim in H; auto.
 destruct H.
 destruct H0.
 destruct H0.
 rewrite H0 in H.
 exists x1.
 split; trivial.

 destruct H.
 destruct H.
 unfold El.
 apply ZFrepl.repl_intro with (couple x (iLAM x0)); trivial.
 split; trivial.
 exists x0; reflexivity.
Qed.


Definition mkTy (A:set) (R: set -> Lc.term -> Prop) : set :=
  subset (prodcart A CCLam) (fun p =>
    exists2 t, snd p == iLAM t & R (fst p) t).

Lemma mkTy_morph : forall A A' R R',
  A == A' ->
  (forall x t, x \in A -> (R x t <-> R' x t)) ->
  mkTy A R == mkTy A' R'.
intros.
unfold mkTy.
apply subset_morph.
 rewrite H; reflexivity.

 red; intros.
 apply ex2_morph.
  reflexivity.

  red; intros.
  apply H0.
  apply fst_typ in H1; trivial.
Qed.


Lemma mkTy_def : forall x t A R,
  Proper (eq_set ==> eq ==> iff) R ->
  (couple x (iLAM t) \in mkTy A R <-> x \in A /\ R x t).
intros.
unfold mkTy.
split; intros.
 split.
  apply subset_elim1 in H0.
  apply fst_typ in H0.
  rewrite fst_def in H0; trivial.

  apply subset_elim2 in H0.
  destruct H0.
  destruct H1.
  rewrite <- H0 in H1,H2; clear x0 H0.
  rewrite fst_def in H2; rewrite snd_def in H1.
  apply iLAM_inj in H1; subst; trivial.

 apply subset_intro.
  destruct H0.
  apply couple_intro; trivial.
  apply iLAM_typ.

  destruct H0.
  exists t.
   apply snd_def.

   rewrite fst_def; trivial.
Qed.

Lemma mkTy_def0 : forall x t A R,
  Proper (eq_set ==> eq ==> iff) R ->
  (x \in A -> R x t -> is_cand (fun t => R x t)) ->
  ((x,t) \real mkTy A R <-> x \in A /\ R x t).
intros.
unfold inX, inTyp; rewrite mkTy_def; trivial; simpl.
split; intros.
 destruct H1 as (H1,_); trivial.

 split; trivial.
 destruct H1.
 generalize (H0 H1 H2); apply is_cand_morph; red; intros; simpl.
 rewrite mkTy_def; trivial.
 split; intros; auto.
 destruct H3; trivial.
Qed.

Lemma mkTy_def' : forall x t A R,
  Proper (eq_set ==> eq ==> iff) R ->
  x \in A ->
  is_cand (fun t => R x t) ->
  ((x,t) \real mkTy A R <-> R x t).
intros.
unfold inX, inTyp; rewrite mkTy_def; trivial; simpl.
split; intros.
 destruct H2 as ((_,H2),_); trivial.

 split; auto.
 revert H1; apply is_cand_morph; red; intros; simpl.
 rewrite mkTy_def; trivial.
 split; intros; auto.
 destruct H1; trivial.
Qed.

Definition mkProp S :=
  mkTy (power empty) (fun x t => inSAT t S).

Lemma prop3 : forall S, Proper (eq_set ==> eq ==> iff) (fun _ t => inSAT t S).
do 3 red; intros.
subst y0; reflexivity.
Qed.

Lemma mkProp_def : forall x t S,
  (x,t) \real mkProp S <-> x == empty /\ inSAT t S.
intros.
unfold mkProp.
rewrite mkTy_def0.
2:apply prop3.
 setoid_replace (x \in power empty) with (x == empty);
   auto with *.
 rewrite power_ax.
 split; intros.
  apply empty_ext; red; intros.
  generalize (H _ H0); apply empty_ax.

  rewrite <- H; trivial.

 intros _ _.
 generalize (proj2_sig S); apply iff_impl.
 apply is_cand_morph; red; intros.
 reflexivity.
Qed.

Lemma El_mkProp : forall S, El (mkProp S) == power empty.
intros.
apply power_ext; intros.
 rewrite El_def.
 exists (Lc.Ref 0).
 rewrite mkProp_def; split.
  apply empty_ext; red; intros.
  apply H in H0; elim empty_ax with x0; trivial.

  apply varSAT.

 rewrite El_def in H.
 destruct H.
 rewrite mkProp_def in H; destruct H.
 rewrite H in H0; trivial.
Qed.


Definition props :=
  mkTy (power (prodcart (power empty) CCLam))
    (fun P t => Lc.sn t /\ exists S, P == mkProp S).

Lemma prop2 :
  Proper (eq_set ==> eq ==> iff)
    (fun P t => Lc.sn t /\ (exists S : SAT, P == mkProp S)).
do 3 red; intros.
subst y0.
apply and_iff_morphism; auto with *.
apply ex_morph; red; intros.
rewrite H; reflexivity.
Qed.

Lemma props_def : forall x t,
  (x,t) \real props <-> (exists S, x == mkProp S) /\ Lc.sn t.
intros.
unfold props.
rewrite mkTy_def0.
2:apply prop2.
 split; intros.
  destruct H as (_,(snt,isprop)); auto.

  destruct H as (isprop,snt); split; auto.
  destruct isprop as (S,isprop); rewrite isprop.
  apply power_intro; intros.
  apply subset_elim1 in H; trivial.

 intros _ (_,?).
 generalize cand_sn; apply is_cand_morph; red; intros.
 split; intros; auto.
 destruct H0; trivial.
Qed.

(***)

Definition app : X -> X -> X := cc_app.
Definition lam (dom : X) (f: X -> X) : X :=
  cc_lam (El dom) f.

Definition prod (A : X) (B : X -> X) : X :=
  mkTy (cc_prod (El A) (fun x => El (B x))) (fun f t => Pi A B (fun x => app f x) t).

Lemma prop1 : forall dom F,
  Proper (eq_set ==> eq ==> iff) (fun f t => Pi dom F (fun x => app f x) t).
do 3 red; intros.
subst y0.
apply and_iff_morphism; auto with *.
apply fa_morph; intro x1.
apply fa_morph; intro u.
apply fa_morph; intros _.
apply in_ext;[split|]; simpl; auto with *.
rewrite H; reflexivity.
Qed.

Definition eq_fun (x:X) (f1 f2:X->X) :=
  forall y1 y2 t, (y1,t) \real x -> y1 == y2 -> f1 y1 == f2 y2.

Lemma eq_fun_ext : forall dom f g,
  eq_fun dom f g -> ZF.eq_fun (El dom) f g.
red; intros.
rewrite El_def in H0; destruct H0.
apply H with x0; auto.
Qed.
Hint Resolve eq_fun_ext.
Hint Unfold ext_fun.

Lemma lam_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  lam x1 f1 == lam x2 f2.
intros.
unfold lam; apply cc_lam_ext; auto.
rewrite H; reflexivity.
Qed.

Lemma app_ext: Proper (eqX ==> eqX ==> eqX) app.
Proof cc_app_morph.

Lemma prod_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  prod x1 f1 == prod x2 f2.
intros.
unfold prod.
apply mkTy_morph.
 apply cc_prod_ext.
  apply El_morph; trivial.

  red; intros.
  apply El_morph.
  rewrite El_def in H1; destruct H1.
  apply H0 with x0; trivial.

 intros.
 apply and_iff_morphism; auto with *.
 apply fa_morph; intros x0.
 apply fa_morph; intros u.
 assert ((x0,u) \real x1 <-> (x0,u) \real x2).
  split; intros.
   apply inSAT_val with x0 x1; auto with *.
   apply inSAT_val with x0 x2; auto with *.
 assert ((x0,u) \real x1 -> f1 x0 == f2 x0).
  intros.
  apply H0 with u; auto with *.
 split; intros.
  rewrite <- H2 in H5.
  apply inSAT_val with (3:=H4 H5); auto with *.

  rewrite <- H2 in H4.
  apply inSAT_val with (3:=H4 H5); auto with *.
  symmetry; auto.
Qed.

Lemma beta_eq : forall dom F x u,
  eq_fun dom F F ->
  (x,u) \real dom ->
  app (lam dom F) x == F x.
intros.
unfold app, lam.
apply cc_beta_eq; auto.
rewrite El_def; exists u; trivial.
Qed.


Lemma is_cand_pi : forall dom f F,
  (exists t, Pi dom F f t) -> is_cand (Pi dom F f).
unfold Pi, Inter, Arr; intros.
split; intros.
 apply H0.

 destruct H0 as (snt,pi).
 split; intros.
  apply Lc.sn_red_sn with t; auto with coc.

  apply pi in H0.
  apply inSAT_red with (1:=H0); auto with coc.

 split; intros.
  constructor; intros.
  apply H1 in H2; apply H2.

  assert (snu : Lc.sn u).
   apply inSAT_sn in H2; trivial.
  assert (forall t', Lc.red1 t t' -> (f x, Lc.App t' u) \real F x).
   intros.
   apply H1; trivial.
  destruct H as (t0,(_,pi_t0)).
  specialize pi_t0 with (1:=H2).
  clear H1 H2.
  revert t H0 H3. 
  elim snu; intros.
  unfold transp in *.
  apply inSAT_exp with (1:=pi_t0).
   exact I.

   intros.
   revert H1; inversion_clear H2; intro; auto.
    destruct H1.

    apply H0; intros; auto.
    apply inSAT_red with (Lc.App t' x0); auto with coc.
Qed.


Lemma is_cand_pi0 : forall dom f F,
  (exists t, forall x u, (x, u) \real dom -> (f x, Lc.App t u) \real F x) ->
  is_cand
    (fun t => Lc.sn t /\ forall x u, (x, u) \real dom -> (f x, Lc.App t u) \real F x).
intros.
split; intros.
 apply H0.

 destruct H0 as (snt,pi).
 split; intros.
  apply Lc.sn_red_sn with t; auto with coc.

  apply pi in H0.
  apply inSAT_red with (1:=H0); auto with coc.

 split; intros.
  constructor; intros.
  apply H1 in H2; apply H2.

  assert (snu : Lc.sn u).
   apply inSAT_sn in H2; trivial.
  assert (forall t', Lc.red1 t t' -> (f x, Lc.App t' u) \real F x).
   intros.
   apply H1; trivial.
  destruct H as (t0,pi_t0).
  specialize pi_t0 with (1:=H2).
  clear H1 H2.
  revert t H0 H3. 
  elim snu; intros.
  unfold transp in *.
  apply inSAT_exp with (1:=pi_t0).
   exact I.

   intros.
   revert H1; inversion_clear H2; intro; auto.
    destruct H1.

    apply H0; intros; auto.
    apply inSAT_red with (Lc.App t' x0); auto with coc.
Qed.

Lemma prod_def : forall f t dom F,
  (f,t) \real prod dom F <->
  f \in cc_prod (El dom) (fun x => El (F x)) /\
  Pi dom F (fun x => app f x) t.
intros.
unfold prod.
rewrite mkTy_def0.
2:apply prop1.
 reflexivity.

 intros.
 apply is_cand_pi.
 exists t; trivial.
Qed.

(*
Lemma prod_def : forall f t dom F,
  (f,t) \real prod dom F <->
  f \in cc_prod (El dom) (fun x => El (F x)) /\
  Lc.sn t /\
  forall x u, (x,u) \real dom -> (app f x, Lc.App t u) \real F x.
intros.
unfold inX at 1, inTyp, prod; rewrite mkTy_def; simpl.
2:apply prop1.
split; intros.
 decompose [and] H; auto.

 decompose [and] H; clear H.
 split; [split|]; repeat red; auto.
 refine (let iscan := @is_cand_pi dom (fun x => app f x) F _ in _).
  exists t; split; trivial.
 revert iscan; apply iff_impl.
 apply is_cand_morph; red; intros.
 rewrite mkTy_def.
 2:apply prop1.
 split; intros.
  decompose [and] H; auto.
  decompose [and] H; auto.
Qed.
*)

Lemma is_cand_pi' : forall dom f F,
  (forall x, x \in El dom -> f x \in El (F x)) ->
  is_cand (Pi dom F f).
intros.
apply is_cand_pi.
exists (Lc.Ref 0).
split.
 apply Lc.sn_var.
red; intros.
assert (x \in El dom).
 rewrite El_def; exists u; trivial.
apply H in H1.
rewrite El_def in H1; destruct H1.
apply (@SAT_daimon1 (exist _ _ (inSAT_CR H1) : SAT)).
apply inSAT_sn in H0; trivial.
Qed.

Lemma prod_intro : forall dom f F t,
  eq_fun dom f f ->
  eq_fun dom F F ->
  Pi dom F f t ->
  (lam dom f, t) \real prod dom F.
intros dom f F t H H0 H1.
assert (exF : ext_fun (El dom) (fun x => El (F x))).
 apply eq_fun_ext.
 red; intros.
 apply El_morph.
 eapply H0; eauto.
rewrite prod_def.
destruct H1.
red in H2.
split; [|split]; trivial.
 apply cc_prod_intro; intros; auto.
 rewrite El_def in *.
 destruct H3.
 exists (Lc.App t x0); auto.

 red; intros.
 apply inSAT_val with (f x) (F x); auto with *.
 unfold app,lam; rewrite cc_beta_eq; auto with *.
 rewrite El_def; exists u; trivial.
Qed.

Lemma prod_elim : forall dom f x F t u,
  eq_fun dom F F ->
  (f,t) \real prod dom F ->
  (x,u) \real dom ->
  (app f x, Lc.App t u) \real F x.
intros.
rewrite prod_def in H0; destruct H0 as (_,(_,pi)); auto.
apply pi; trivial.
Qed.

Lemma impredicative_prod : forall dom F T U,
  eq_fun dom F F ->
  Lc.sn T ->
  Pi dom (fun _ => props) F U ->
  (prod dom F, Lc.App2 Lc.K T U) \real props.
intros.
rewrite props_def.
split; [|destruct H1; apply Lc.sn_K2; trivial].
assert (alltrue : forall x, x \in El dom -> El (F x) == power empty).
 intros.
 rewrite El_def in H2; destruct H2.
 apply H1 in H2.
 rewrite props_def in H2; destruct H2 as ((S,isprop),_).
 rewrite isprop; apply El_mkProp.
assert (isunit : cc_prod (El dom) (fun x => El (F x)) == power empty).
 assert (ZFcoc.cc_lam (El dom) (fun _ => empty) == empty).
  apply ZFcoc.cc_impredicative_lam; auto with *.
 apply power_ext; intros.
  setoid_replace x with empty.
   rewrite <- H2.
   apply ZFcoc.cc_prod_intro; auto.
    do 2 red; intros.
    apply El_morph.
    rewrite El_def in H4; destruct H4.
    apply H with x1; trivial.

    intros.
    rewrite alltrue; trivial.
    apply power_intro; auto.

   apply empty_ext.
   red; intros.
   apply H3 in H4.
   elim empty_ax with x0; trivial.

  assert (x == empty).
   specialize cc_eta_eq with (1:=H3); intro.
   rewrite <- H2; trivial; rewrite H5.
   apply cc_lam_ext; auto with *.
   red; intros.
   apply empty_ext; red; intros.
   specialize cc_prod_elim with (1:=H3) (2:=H6); intro.
   rewrite alltrue in H9; trivial.
   specialize power_elim with (1:=H9) (2:=H8).
   apply empty_ax.
  rewrite H5 in H4; trivial.
refine (let iscan := @is_cand_pi' dom (fun _ => empty) F _ in _).
 intros.
 rewrite alltrue; trivial.
 apply power_intro; auto.
exists (exist _ _ iscan : SAT).
unfold prod, mkProp.
apply mkTy_morph; intros; auto.
simpl.
apply and_iff_morphism; try reflexivity.
apply fa_morph; intro x0.
apply fa_morph; intro u.
apply fa_morph; intro.
apply in_ext; [split|]; simpl; auto with *.
assert (x0 \in El dom).
 rewrite El_def; exists u; trivial.
specialize cc_prod_elim with (1:=H2) (2:=H3); intro.
rewrite alltrue in H4; trivial.
apply empty_ext; red; intros.
specialize power_elim with (1:=H4) (2:=H5).
apply empty_ax.
Qed.

Existing Instance eqX_equiv.
Existing Instance in_ext.
Existing Instance app_ext.

(* No empty types (False is inhabited) *)

  Definition daemon := empty.
  Definition daemont := Lc.Ref 0.

  Lemma daemon_false : (daemon,daemont) \real prod props (fun P => P).
apply inSAT_val with (lam props (fun _ => empty)) (prod props (fun P => P)); auto with *.
 apply cc_impredicative_lam; auto with *.
apply prod_intro; intros.
 red; red; reflexivity.

 red; red; auto.

 constructor; intros.
  apply Lc.sn_var.

  red; intros.
  rewrite props_def in H; destruct H as ((S,isprop),snu).
  apply inSAT_val with empty (mkProp S); auto with *.
  rewrite mkProp_def; split; auto with *.
  apply SAT_daimon1; trivial.
Qed.

End MM.
(*Declare Module MM : Model.*)
Import MM.

Lemma inSAT_val : forall x x' A A' t,
  x == x' -> A == A' -> (x,t) \real A -> (x',t) \real A'.
intros.
revert H1; apply iff_impl.
apply in_ext; auto.
red; auto.
Qed.

Lemma inSAT_red : forall x A t u,
  (x,t) \real A -> Lc.red t u -> (x,u) \real A.
intros.
destruct (inSAT_CR H); eauto.
Qed.

Lemma inSAT_sn : forall x A t, (x,t) \real A -> Lc.sn t.
intros.
destruct (inSAT_CR H); eauto.
Qed.

Lemma inSAT_exp : forall x A t u,
  (x,t) \real A ->
  neutral u ->
  (forall v, Lc.red1 u v -> (x,v) \real A) ->
  (x,u) \real A. 
intros.
destruct (inSAT_CR H); eauto.
Qed.

Lemma inSAT_exp_sat : forall x A m u,
  Lc.sn u ->
  (x,Lc.subst u m) \real A ->
  (x,Lc.App (Lc.Abs m) u) \real A. 
intros.
assert (Lc.sn m).
 apply Lc.sn_subst with u.
 apply inSAT_sn in H0; trivial.
revert m H1 H0.
induction H.
rename x0 into u.
unfold transp in *.
assert (snu : Lc.sn u).
 apply Acc_intro; trivial.
clear H.
induction 1.
rename x0 into m.
unfold transp in *.
assert (snm : Lc.sn m).
 apply Acc_intro; trivial.
clear H.
intros.
apply inSAT_exp with (1:=H2); intros.
 exact I.
inversion_clear H; trivial.
 inversion_clear H3.
 apply H1; auto.
 apply inSAT_red with (1:=H2).
 unfold Lc.subst; auto with coc.

 apply H0; auto.
 apply inSAT_red with (1:=H2).
 unfold Lc.subst; auto with coc.
Qed.

Lemma inSAT_exp_sat1 : forall x A m u u1,
  Lc.sn u ->
  (x,Lc.App (Lc.subst u m) u1) \real A ->
  (x,Lc.App (Lc.App (Lc.Abs m) u) u1) \real A. 
intros x A m u u1 snu inA.
revert m u1 inA.
induction snu; intros.
clear H; rename x0 into u.
assert (snm: Lc.sn m).
 apply Lc.sn_subst with u.
 apply inSAT_sn in inA; trivial.
 apply Lc.subterm_sn with (1:=inA); auto with coc.
revert u1 inA.
induction snm; intros.
clear H; rename x0 into m.
assert (snu1: Lc.sn u1).
 apply inSAT_sn in inA; trivial.
 apply Lc.subterm_sn with (1:=inA); auto with coc.
revert inA.
induction snu1.
clear H; rename x0 into u1.
intros.
unfold transp in *.
apply inSAT_exp with (1:=inA); intros.
 exact I.
inversion_clear H.
 inversion_clear H3; auto.
  inversion_clear H.
  apply H1; trivial.
  apply inSAT_red with (1:=inA); trivial.
  unfold Lc.subst; auto with coc.

  apply H0; trivial.
  apply inSAT_red with (1:=inA); trivial.
  unfold Lc.subst; auto with coc.

 apply H2; trivial.
 apply inSAT_red with (1:=inA); auto with coc.
Qed.


Lemma inSAT_exp_sat2 : forall x A m u u1 u2,
  Lc.sn u ->
  (x,Lc.App (Lc.App (Lc.subst u m) u1) u2) \real A ->
  (x,Lc.App (Lc.App (Lc.App (Lc.Abs m) u) u1) u2) \real A. 
intros x A m u u1 u2 snu inA.
revert m u1 u2 inA.
induction snu; intros.
clear H; rename x0 into u.
assert (snm: Lc.sn m).
 apply Lc.sn_subst with u.
 apply inSAT_sn in inA; trivial.
 apply Lc.subterm_sn with (Lc.App (Lc.subst u m) u1); auto with coc.
 apply Lc.subterm_sn with (1:=inA); auto with coc.
revert u1 u2 inA.
induction snm; intros.
clear H; rename x0 into m.
assert (snu1: Lc.sn u1).
 apply inSAT_sn in inA; trivial.
 apply Lc.subterm_sn with (Lc.App (Lc.subst u m) u1); auto with coc.
 apply Lc.subterm_sn with (1:=inA); auto with coc.
revert u2 inA.
induction snu1; intros.
clear H; rename x0 into u1.
assert (snu2: Lc.sn u2).
 apply inSAT_sn in inA; trivial.
 apply Lc.subterm_sn with (1:=inA); auto with coc.
revert inA.
induction snu2; intros.
clear H; rename x0 into u2.
unfold transp in *.
apply inSAT_exp with (1:=inA); intros.
 exact I.
inversion_clear H.
 inversion_clear H4.
  inversion_clear H; auto.
   inversion_clear H4.
   apply H1; trivial.
   apply inSAT_red with (1:=inA); trivial.
   unfold Lc.subst; auto with coc.

   apply H0; trivial.
   apply inSAT_red with (1:=inA); trivial.
   unfold Lc.subst; auto with coc.

  apply H2; trivial.
  apply inSAT_red with (1:=inA); auto with coc.

 apply H3; trivial.
 apply inSAT_red with (1:=inA); auto with coc.
Qed.

Lemma prod_intro' : forall dom f F m,
  eq_fun dom f f ->
  eq_fun dom F F ->
  Lc.sn m ->
  (forall x u, (x,u) \real dom ->
   (f x, Lc.subst u m) \real F x) ->
  (lam dom f, Lc.Abs m) \real prod dom F.
intros.
apply prod_intro; trivial; intros.
split; intros.
 apply Lc.sn_abs; trivial.

 red; intros.
 apply inSAT_exp_sat; auto.
 apply inSAT_sn in H3; trivial.
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

Admitted.

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

Definition tm (j:intt) (M:trm) :=
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

Definition cst (x:X) (t:Lc.term)
  (H0 : liftable (fun _ => t)) (H1 : substitutive (fun _ => t)) : trm.
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
             (fun j => CAbs (tm j A) (tm (ilift j) M)).
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

(* Encoding product *)
Definition CProd a b :=
  Lc.App2 Lc.K a (Lc.Abs b).

Definition Prod (A B:trm) : trm.
left;
  exists (fun i => prod (int i A) (fun x => int (V.cons x i) B))
         (fun j => CProd (tm j A) (tm (ilift j) B)).
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
  (forall i, (x,t) \real int i U) ->
  forall e i,
  (cst_fun i e x, cst_trm e t) \real int i (prod_list e U).
induction e; simpl; intros; auto.
apply prod_intro'; intros; auto.
 red; intros.
 rewrite H1; reflexivity.

 red; intros.
 rewrite H1; reflexivity.

 apply sn_lift.
 apply cst_trm_sn.
 apply inSAT_sn with x (int i U); auto.

 unfold Lc.subst; rewrite Lc.simpl_subst; auto with arith.
 rewrite Lc.lift0.
 trivial.
Qed.


(* We could parameterize non_empty with a val [i0], and
   quantify over i s.t. vshift (length e) i = i0.
   This would allow kind variables. *)
Definition non_empty T :=
  exists e, exists2 U, eq_trm T (prod_list e U) &
    exists x, forall i, x \real int i U.

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

 exists (prod props (fun P => P), Lc.App2 Lc.K Lc.K (Lc.Abs (Lc.Ref 0))); intros.
 apply impredicative_prod; intros; auto.
  red; auto.

  apply Lc.sn_K.

  split.
   apply Lc.sn_abs; apply Lc.sn_var. 

   red; intros.
   apply inSAT_exp_sat.
    apply inSAT_sn in H; trivial.

    unfold Lc.subst; simpl; rewrite Lc.lift0; trivial.
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
  exists x, exists u, (x,u) \real int i T.
intros.
destruct H as (e,(U,eq_U,(wit,in_U))).
exists (cst_fun i e (fst wit)); exists (cst_trm e (snd wit)).
apply inSAT_val with (cst_fun i e (fst wit)) (int i (prod_list e U)); auto with *.
 rewrite eq_U; reflexivity.

 apply wit_prod; destruct wit; trivial.
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
intros n (e,(U,eq_U,((x,t),in_U))).
destruct e; simpl prod_list in eq_U.
 exists List.nil; exists (lift 1 U).
  simpl prod_list.
  rewrite <- lift1var.
  apply lift_morph; trivial.

  exists (x,t); intros.
  apply inSAT_val with x (int (V.shift 1 i) U); auto with *.
  setoid_replace i with (V.cons (i 0) (V.shift 1 i)).
   rewrite int_lift_eq; reflexivity.

   red; red; intros.
   destruct a; reflexivity.

 elim (discr_ref_prod eq_U).
Qed.


Definition in_int (i:val) (j:intt) (M T:trm) :=
  M <> None /\
  match T with
  (* M has type kind *)
  | None => non_empty M /\ Lc.sn (tm j M)
  (* T is a regular type *)
  | _ => (int i M, tm j M) \real int i T
  end.

Instance in_int_morph : Proper
  (eq_val ==> pointwise_relation nat (@eq Lc.term) ==> eq_trm ==> eq_trm ==> iff)
  in_int.
unfold in_int; do 5 red; intros.
repeat rewrite eq_kind.
destruct x2; destruct y2; try contradiction.
 replace (tm x0 x1) with (tm y0 y1).
 2:rewrite H0; rewrite H1; reflexivity.
 setoid_replace (eq_trm x1 None) with (eq_trm y1 None).
 (*2:rewrite H1; reflexivity. 
 split; destruct 1; split; trivial.
  apply inSAT_val with (3:=H4); trivial.
   rewrite H; rewrite H1; reflexivity.
   rewrite H; rewrite H2; reflexivity.
  apply inSAT_val with (3:=H4); trivial.
   rewrite H; rewrite H1; reflexivity.
   rewrite H; rewrite H2; reflexivity.

 rewrite H0; rewrite H1; reflexivity.
Qed.*)Admitted.

Lemma in_int_not_kind : forall i j M T,
  in_int i j M T ->
  T <> kind ->
  (int i M, tm j M) \real int i T.
destruct 1 as (_,mem); intros.
destruct T; auto.
elim H; trivial.
Qed.

Lemma in_int_intro : forall i j M T,
  (int i M, tm j M) \real int i T ->
  M <> kind ->
  T <> kind ->
  in_int i j M T.
red; intros.
destruct T; auto.
elim H1; trivial.
Qed.


Lemma in_int_var0 : forall i j x t T,
  (x,t) \real int i T ->
  T <> kind ->
  in_int (V.cons x i) (I.cons t j) (Ref 0) (lift 1 T).
intros.
red; simpl.
split; try discriminate.
 revert H0; pattern T at 1 2.
 case T; simpl; intros.
  apply inSAT_val with x (int i T); auto with *.
  symmetry; apply int_cons_lift_eq; trivial.

  elim H0; trivial.
Qed.

Lemma in_int_varS : forall i j x t n T,
  in_int i j (Ref n) (lift (S n) T) ->
  in_int (V.cons x i) (I.cons t j) (Ref (S n)) (lift (S (S n)) T).
intros.
destruct H as (_,mem); simpl in *.
red; simpl.
split; try discriminate.
 revert mem; pattern T at 1 3.
 case T; [intros T0|]; simpl; intros; trivial.
  apply inSAT_val with (i n) (int i (lift (S n) T)); auto with *.
  symmetry; rewrite split_lift.
  apply int_cons_lift_eq.

  destruct mem; split; trivial.
  apply non_empty_var_lift; trivial.
Qed.

Lemma in_int_sn : forall i j M T,
  in_int i j M T -> Lc.sn (tm j M).
destruct 1 as (_,mem).
destruct T; simpl in mem.
 apply inSAT_sn in mem; trivial.

 destruct mem; trivial.
Qed.

(* Environments *)
Definition env := list trm.

Definition val_ok (e:env) (i:val) (j:intt) :=
  forall n T, nth_error e n = value T ->
  in_int i j (Ref n) (lift (S n) T).

Lemma vcons_add_var : forall e T i j x t,
  val_ok e i j ->
  (x,t) \real int i T ->
  T <> kind ->
  val_ok (T::e) (V.cons x i) (I.cons t j).
unfold val_ok; simpl; intros.
destruct n; simpl in *.
 injection H2; clear H2; intro; subst; simpl in *. 
 apply in_int_var0; trivial.

 apply in_int_varS; auto.
Qed.

Lemma add_var_eq_fun : forall T U U' i,
  (forall x t, (x,t) \real int i T -> int (V.cons x i) U == int (V.cons x i) U') -> 
  eq_fun (int i T)
    (fun x => int (V.cons x i) U)
    (fun x => int (V.cons x i) U').
red; intros.
rewrite <- H1; eauto.
Qed.


(* Judgements *)
Definition wf (e:env) :=
  exists i, exists j, val_ok e i j.
Definition typ (e:env) (M T:trm) :=
  forall i j, val_ok e i j -> in_int i j M T.
Definition eq_typ (e:env) (M M':trm) :=
  (forall i j, val_ok e i j -> int i M == int i M') /\
  (forall j, conv (tm j M) (tm j M')).
Definition sub_typ (e:env) (M M':trm) :=
  forall i j, val_ok e i j ->
  (forall x t, (x,t) \real int i M -> (x,t) \real int i M').

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
 apply inSAT_val with x1 (int i x0); auto with *.
  rewrite H0; reflexivity.
 apply H1 with (1:=H2).
 apply inSAT_val with x1 (int i y); auto with *.
 rewrite H; reflexivity.

 apply inSAT_val with x1 (int i y0); auto with *.
  rewrite H0; reflexivity.
 apply H1 with (1:=H2).
 apply inSAT_val with x1 (int i x); auto with *.
 rewrite H; reflexivity.
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
  exists x, exists u, (x,u) \real int i T.
intros.
destruct H.
 apply H in H0.
 destruct H0 as (_,(mem,_)); apply non_empty_witness; trivial.

 apply H in H0.
 destruct H0 as (_,mem); simpl in *.
 exists (app daemon (int i T)); exists (Lc.App daemont (tm j T)).
 apply prod_elim with (2:=daemon_false); trivial.
 red; intros; trivial.
Qed.


(* Strong normalization *)

Lemma typs_sn : forall e T i j, typs e T -> val_ok e i j -> Lc.sn (tm j T).
destruct 1 as [ty_T|ty_T]; intro is_val; apply ty_T in is_val;
 red in is_val; simpl in is_val.
 destruct is_val as (_,(_,sn)); trivial.
 destruct is_val as (_,mem); apply inSAT_sn in mem; trivial.
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

 apply conv_conv_app; auto.
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
 apply H1 with (j:=I.cons t j).
 apply vcons_add_var; auto.

 unfold CAbs, Lc.App2.
 apply conv_conv_app; auto.
 apply conv_conv_app; auto with *.
 apply conv_conv_abs; auto.
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
 apply H0 with (j:=I.cons t j).
 apply vcons_add_var; auto.

 unfold CProd, Lc.App2.
 apply conv_conv_app.
  apply conv_conv_app; auto with *.
  apply H.

  apply conv_conv_abs.
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
 assert ((int i N, tm j N) \real int i T).
  apply H1 in H3.
  apply in_int_not_kind in H3; trivial.
 rewrite (beta_eq (u:=tm j N) H4); auto.
 rewrite <- int_subst_eq.
 destruct H0.
 rewrite <- H0; eauto.
 apply H with (j:=I.cons (tm j N) j).
 apply vcons_add_var; auto.

 apply trans_conv_conv with (Lc.App (CAbs (tm j T) (tm (ilift j) M')) (tm j N)).
  apply conv_conv_app; auto with *.
  unfold CAbs, Lc.App2.
  apply conv_conv_app; auto with *.
  apply conv_conv_app; auto with *.
  apply conv_conv_abs.
  apply H.
 apply trans_conv_conv with (Lc.App (CAbs (tm j T) (tm (ilift j) M')) (tm j N')).
  apply conv_conv_app; auto with *.
  apply H0.
 unfold CAbs, Lc.App2, Lc.K.
 eapply trans_conv_conv.
  apply conv_conv_app;[|apply refl_conv].
  apply conv_conv_app;[|apply refl_conv].
  apply Lc.red_conv; apply Lc.one_step_red; apply beta.
  unfold Lc.subst; simpl.
 eapply trans_conv_conv.
  apply conv_conv_app;[|apply refl_conv].
  apply Lc.red_conv; apply Lc.one_step_red; apply beta.
 unfold Lc.subst; rewrite Lc.simpl_subst; auto with arith; rewrite Lc.lift0.
 rewrite tm_subst_eq. 
 apply Lc.red_conv; apply Lc.one_step_red; apply beta.
Qed.

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
  apply inSAT_val with (3:=ty_u); auto with *.
  apply int_subst_eq.

  destruct Ur as [Ur|]; simpl; try discriminate; trivial.

 red; intros.
 rewrite H0; reflexivity.
Qed.

Lemma red_abs_sat : forall x A t m,
  Lc.sn t ->
  (x, Lc.Abs m) \real A ->
  (x, CAbs t m) \real A.
intros.
unfold CAbs, Lc.App2, Lc.K.
apply inSAT_exp_sat1; trivial.
 apply inSAT_sn in H0; trivial.

 unfold Lc.subst, Lc.lift; simpl.
 apply inSAT_exp_sat; trivial.
 unfold Lc.subst; rewrite Lc.simpl_subst; auto with arith.
 rewrite Lc.lift0.
 trivial.
Qed.

Lemma prod_intro2 : forall dom f F t m,
  eq_fun dom f f ->
  eq_fun dom F F ->
  Lc.sn t ->
  (exists x, exists u, (x,u) \real dom) ->
  (forall x u, (x, u) \real dom -> (f x, Lc.subst u m) \real F x) ->
  (lam dom f, CAbs t m) \real prod dom F.
intros.
apply prod_intro' in H3; trivial.
apply red_abs_sat; trivial.
(* *)
destruct H2.
destruct H2.
apply H3 in H2.
apply inSAT_sn in H2.
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
assert (snU : Lc.sn (tm (ilift j) U)).
 apply Lc.sn_subst with witt.
 rewrite <- tm_subst_cons.
 destruct is_srt; subst s2; simpl in *.
  destruct in_U as (_,(_,snu)); trivial.

  destruct in_U as (_,mem); simpl in mem.
  apply inSAT_sn in mem; trivial.
destruct is_srt; subst s2; simpl in *.
 split.
  apply prod_non_empty.
  destruct in_U as (_,(mem,_)); trivial.

  apply Lc.sn_K2.
   apply typs_sn with (1:=ty_T) (2:=is_val).

   apply Lc.sn_abs; trivial.

 apply impredicative_prod; intros.   
   red; intros.
   rewrite H1; reflexivity.

   apply typs_sn with (1:=ty_T) (2:=is_val).

   split.
    apply Lc.sn_abs; trivial.

    red; intros.
    clear in_U.
    specialize vcons_add_var with (1:=is_val) (2:=H0) (3:=T_not_tops);
      intros in_U.
    apply ty_U in in_U.
    apply in_int_not_kind in in_U.
    2:discriminate.
    apply inSAT_exp_sat.
     apply inSAT_sn in H0; trivial.

     rewrite <- tm_subst_cons.
     trivial.
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
apply inSAT_val with (3:=H); auto with *.
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
apply inSAT_val with x (int i M); auto with *.
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


(* Consistency out of the strong normalization model *)

Lemma occur_subst : forall k t,
  Lc.occur k t <->
  Lc.lift_rec 1 (Lc.subst_rec (Lc.Abs (Lc.Ref 0)) t k) k <> t.
split; intros.
 induction H; simpl; intros.
  destruct (lt_eq_lt_dec n n) as [[?|_]|?].
   elim (Lt.lt_irrefl n); trivial.

   discriminate.

   elim (Lt.lt_irrefl n); trivial.

  red; intros.
  injection H0; clear H0; intros; auto.

  red; intros. 
  injection H0; clear H0; intros; auto.

  red; intros.
  injection H0; clear H0; intros; auto.

 revert k H; induction t; simpl; intros.
  destruct (lt_eq_lt_dec k n) as [[?|?]|?]; simpl in H.
   destruct (le_gt_dec k (Peano.pred n)); simpl in *.
    elim H.
    destruct n; simpl; trivial.
    inversion l.

    apply NPeano.Nat.lt_pred_le in g.
    elim (Lt.lt_irrefl n).
    apply Lt.le_lt_trans with k; trivial.

   subst k; auto.

   destruct (le_gt_dec k n).
    elim (Lt.lt_irrefl n).
    apply Lt.lt_le_trans with k; trivial.

    elim H; trivial.

  constructor; apply IHt.
  red; intros; apply H.
  rewrite H0; trivial.

  destruct (eqterm (Lc.lift_rec 1 (Lc.subst_rec (Lc.Abs (Lc.Ref 0)) t1 k) k) t1).
   apply Lc.occ_app_r.
   apply IHt2.
   red; intros; apply H.
   rewrite e; rewrite H0; trivial.

   apply Lc.occ_app_l; auto.
Qed.

Lemma tm_closed : forall k j M,
  Lc.occur k (tm j M) -> ~ forall n, ~ Lc.occur k (j n).
red; intros.
rewrite occur_subst in H.
rewrite <- tm_substitutive in H.
rewrite <- tm_liftable in H.
apply H; clear H.
apply tm_morph; auto with *.
red; red; intros.
generalize (H0 a).
rewrite occur_subst; intro.
destruct (eqterm (Lc.lift_rec 1 (Lc.subst_rec (Lc.Abs (Lc.Ref 0)) (j a) k) k) (j a)); auto.
elim H; trivial.
Qed.

(*
Fixpoint nf t :=
  match t with
  | Lc.App u v => neutral u /\ nf u /\ nf v
  | Lc.Abs t => nf t
  | _ => True
  end.
*)
Inductive nf : term -> Prop :=
| Nf_var : forall n, nf (Lc.Ref n)
| Nf_app : forall u v, neutral u -> nf u -> nf v -> nf (Lc.App u v)
| Nf_abs : forall t, nf t -> nf (Lc.Abs t).

Hint Constructors nf.

Lemma nf_norm : forall t, nf t -> forall u, ~ red1 t u.
(*
red; intros.
revert H.
induction H0; simpl; auto.
 destruct 1; auto.

 destruct 1 as (_,(?,_)); auto.

 destruct 1 as (_,(_,?)); auto.
*)
red; intros.
revert H.
induction H0; simpl; intros; auto.
 inversion_clear H.
 elim H0.

 inversion_clear H; auto.

 inversion_clear H; auto.

 inversion_clear H; auto.
Qed.

Lemma red1_dec : forall t, {u|red1 t u}+{nf t}.
induction t; intros.
 right; simpl; trivial.

 destruct IHt.
  destruct s.
  left; exists (Lc.Abs x); auto with coc.

  right; simpl; auto.

 destruct IHt1.
  destruct s.
  left; exists (Lc.App x t2); auto with coc.

  destruct IHt2.
   destruct s.
   left; exists (Lc.App t1 x); auto with coc.

   destruct t1;[right;simpl;auto|left|right;simpl;auto].
repeat constructor; trivial.
   exists (Lc.subst t2 t1); auto with coc.
constructor; trivial.
simpl; trivial.
Qed.

Lemma norm : forall t, sn t -> { u | red t u /\ nf u}.
induction 1; intros.
destruct (red1_dec x).
 destruct s.
 destruct (H0 x0); trivial.
 destruct a.
 exists x1; split; trivial.
 transitivity x0; auto with coc.

 exists x; auto with coc.
Qed.

Definition Neu : CR := fun t =>
  Lc.sn t /\ exists2 u, Lc.red t u & nf u /\ neutral u.

Lemma neutral_is_cand : is_cand Neu.
split; intros.
 destruct H; trivial.

 destruct H.
 destruct H1.
 split.
  apply Lc.sn_red_sn with t; auto with coc.

  exists x; trivial.
  destruct H2.
  elim confluence with (1:=H1) (2:=H0); intros.
  replace x with x0; trivial.
  revert H2; elim H4; trivial; intros.
  rewrite H6 in H7; trivial.
  elim nf_norm with (2:=H7); trivial.

 assert (Lc.sn t).
  constructor; intros.
  destruct (H0 y); auto.
 split; trivial.
 destruct (red1_dec t).
  destruct s.
  specialize H0 with (1:=r).
  destruct H0.
  destruct H2.
  exists x0; trivial.
  transitivity x; auto with coc.

  exists t; auto with *.
Qed.

Lemma nf_neutral_open : forall t,
  nf t ->
  neutral t ->
  exists k, Lc.occur k t.
induction 1; intros.
 exists n; auto with coc.

 destruct (IHnf1 H).
 exists x; apply Lc.occ_app_l; trivial.

 destruct H0.
Qed.


Lemma lift_closed : forall m M n k,
  k <= n ->
  Lc.occur n (Lc.lift_rec m M k) ->
  m+k <= n /\ Lc.occur (n-m) M.
induction M; simpl; intros.
 destruct (le_gt_dec k n).
  inversion_clear H0.
  split; auto with arith.
  replace (m+n-m) with n; auto with arith.

  inversion H0; subst n0.
  elim (Lt.lt_irrefl n); apply Lt.lt_le_trans with k; trivial.

 inversion_clear H0.
 apply IHM in H1; auto with arith.
 destruct H1.
 rewrite <- plus_n_Sm in H0.
 split; auto with arith.
 constructor.
 rewrite <- NPeano.Nat.sub_succ_l; trivial.
 apply Le.le_trans with (m+k); auto with arith.

 inversion_clear H0.
  apply IHM1 in H1; destruct H1; auto with *.
  apply IHM2 in H1; destruct H1; auto with *.
Qed.

Lemma subst_closed : forall N M n k,
  k <= n ->
  Lc.occur n (Lc.subst_rec N M k) ->
  Lc.occur (n-k) N \/ Lc.occur (S n) M.
induction M; simpl; intros.
 destruct (lt_eq_lt_dec k n) as [[?|?]|?].
  inversion H0; subst n0.
  right.
  destruct n; simpl; auto with *.
  inversion l.

  left.
  apply lift_closed with (k:=0); auto with arith.

  inversion H0; subst n0.
  elim (Lt.lt_irrefl n); apply Lt.lt_le_trans with k; trivial.

 inversion_clear H0.
 apply IHM in H1.
 destruct H1; auto with *.
 apply Le.le_n_S; trivial.

 inversion_clear H0.
  apply IHM1 in H1; trivial.
  destruct H1; auto.

  apply IHM2 in H1; trivial.
  destruct H1; auto.
Qed.


Lemma red_closed : forall t t',
  Lc.red t t' ->
  forall k,
  Lc.occur k t' ->
  Lc.occur k t.
induction 1; intros; auto.
apply IHred.
revert k H1; clear H IHred t.
induction H0.
 intros.
 destruct subst_closed with (2:=H1); auto with arith.
 replace (k-0) with k in H; auto with *.

 intros.
 inversion_clear H1; apply Lc.occ_abs; auto.

 intros.
 inversion_clear H1.
  apply Lc.occ_app_l; auto.
  apply Lc.occ_app_r; trivial.

 intros.
 inversion_clear H1.
  apply Lc.occ_app_l; trivial.
  apply Lc.occ_app_r; auto.
Qed.


Lemma neutral_not_closed :
  forall t, (forall S, inSAT t S) -> exists k, Lc.occur k t.
intros.
assert (neu := H (exist _ _ neutral_is_cand : SAT)).
simpl in neu.
destruct neu.
destruct H1.
destruct H2.
destruct nf_neutral_open with (1:=H2) (2:=H3).
exists x0.
apply red_closed with x; auto.
Qed.


Lemma consistency : forall M, ~ typ List.nil M (Prod prop (Ref 0)).
red; intros.
red in H.
assert (val_ok List.nil (V.nil props) (I.nil (Lc.Abs (Lc.Ref 0)))).
 red; intros.
 destruct n; discriminate H0.
apply H in H0.
clear H.
red in H0; simpl in H0.
destruct H0 as (_,H0).
set (prf := tm (I.nil (Lc.Abs (Lc.Ref 0))) M) in H0.
assert (forall S, inSAT (Lc.App prf (Lc.Abs (Lc.Ref 0))) S).
 intros.
 assert ((mkProp S, Lc.Abs (Lc.Ref 0)) \real props). 
  rewrite props_def.
  split; auto with coc.
  exists S; reflexivity.
 specialize prod_elim with (2:=H0)(3:=H); intros.
 rewrite mkProp_def in H1.
 destruct H1; trivial.
 red; intros; trivial.
destruct (neutral_not_closed _ H).
inversion_clear H1.
 apply tm_closed in H2.
 apply H2.
 red; intros.
 unfold I.nil in H1; simpl in H1.
 inversion_clear H1.
 inversion H3.

 inversion_clear H2.
 inversion H1.
Qed.

Admitted.

Admitted.

 