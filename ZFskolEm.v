
(** In this file, we show the equivalence between the Skolemized
   and existentially quantified presentations of ZF.
 *)

Require Import basic.
Require Export ZFdef.
Require Import EnsEm Sublogic.

Module Skolem (L:SublogicTheory). (*<: IZF_R_sig L *)

(** We assume we have a model of set theory with existential axioms in
    sublogic L. We could do the same with the abstract signature... *)
Module Z := Ensembles L.
Import L.

Instance Zsetoid: Equivalence Z.eq_set.
Proof.
split; red; intros; rewrite Z.eq_set_ax in *; intros.
 reflexivity.
 symmetry; trivial.
 transitivity (Z.in_set z0 y); trivial.
Qed.

Instance Zin_morph : Proper (Z.eq_set ==> Z.eq_set ==> iff) Z.in_set.
Proof.
do 3 red; intros.
rewrite Z.eq_set_ax in H0.
split; intros.
 rewrite <- H0.
 apply Z.in_reg with x; trivial.

 rewrite H0.
 symmetry in H.
 apply Z.in_reg with y; trivial.
Qed. 

(** * Existential sets and their relation with regular sets *)

(** The type of existential sets *)
Definition set :=
  { f : Z.set -> Prop |
    (#exists u, f u) /\
    (forall a a', f a -> f a' -> Z.eq_set a a') }.

Lemma set_intro : forall (f:Z.set->Prop) (P:set->Prop),
  (#exists u, f u) ->
  (forall a a', f a -> f a' -> Z.eq_set a a') ->
  (forall Hex Huniq, P (exist _ f (conj Hex Huniq))) ->
  sig P.
intros.
exists (exist _ f (conj H H0)); trivial.
Qed.

(** Membership. (Uses an inductive to avoid unwanted unfolding...) *)
Inductive in_set_ (x y:set) : Prop :=
 InSet
  (_:#exists2 x', proj1_sig x x' &
      exists2 y', proj1_sig y y' & Z.in_set x' y').

Definition in_set := in_set_.

Lemma inset_isL x y : isL (in_set x y).
red.
constructor.
Telim H; intro.
destruct H; trivial.
Qed.
Global Hint Resolve inset_isL.

Lemma in_set_elim : forall x y, in_set x y <->
  #exists2 x', proj1_sig x x' &
   exists2 y', proj1_sig y y' & Z.in_set x' y'.
split; intros.
 destruct H; trivial.
 constructor; trivial.
Qed.

Notation "x ∈ y" := (in_set x y).

(** Equality *)
Definition eq_set a b := forall x, x ∈ a <-> x ∈ b.

Notation "x == y" := (eq_set x y).

Lemma eqset_isL x y : isL (x == y).
red; red; intros.
Telim H; auto.
Qed.
Global Hint Resolve eqset_isL.

Lemma eq_set_ax : forall a b, a == b <-> (forall x, x ∈ a <-> x ∈ b).
reflexivity.
Qed.

Instance eq_setoid: Equivalence eq_set.
Proof.
split; do 2 red; intros.
 reflexivity.
 symmetry; trivial.
 transitivity (x0 ∈ y); trivial.
Qed.

Lemma In_intro: forall x y: set,
  (forall x' y', proj1_sig x x' -> proj1_sig y y' -> Z.in_set x' y') ->
  x ∈ y.
intros.
destruct (proj2_sig x).
Tdestruct H0.
destruct (proj2_sig y).
Tdestruct H2.
constructor.
Texists x0; trivial.
exists x1; auto.
Qed.

Lemma In_elim (P:Prop) (x y:set):
  isL P ->
  (forall x' y', proj1_sig x x' -> proj1_sig y y' -> Z.in_set x' y' -> P) ->
  x ∈ y -> P.
intros.
rewrite in_set_elim in H1.
Tdestruct H1.
destruct H2.
eauto.
Qed.

(** Lifting sets to existential sets *)
Definition Z2set (x:Z.set) : set.
exists (fun a => Z.eq_set a x).
split.
 Texists x; reflexivity.

 intros; transitivity x; trivial.
 symmetry; trivial.
Defined.

Lemma Eq_proj : forall (x:set) x', proj1_sig x x' -> x == Z2set x'.
intros.
destruct (proj2_sig x).
clear H0.
split; intros.
 rewrite in_set_elim in H0.
 Tdestruct H0.
 destruct H2.
 constructor.
 Texists x1; simpl; trivial.
 exists x2; auto.

 rewrite in_set_elim in H0.
 Tdestruct H0; simpl in *.
 destruct H2.
 constructor.
 Texists x1; simpl; trivial.
 exists x'; trivial.
 rewrite <- H2; trivial.
Qed.

(** Perservation of equality and membership by lifting *)
Lemma inZ_in : forall a b, Z.in_set a b -> Z2set a ∈ Z2set b.
unfold Z2set, in_set; simpl.
intros.
constructor; simpl.
Texists a; try reflexivity.
exists b; try reflexivity; trivial.
Qed.

Lemma in_inZ : forall a b, Z2set a ∈ Z2set b -> Z.in_set a b.
intros.
rewrite in_set_elim in H.
Tdestruct H.
destruct H0.
unfold Z2set in *; simpl in *.
apply Z.in_reg with x; trivial.
rewrite <- H0; auto.
Qed.

Lemma in_equiv a b : in_set (Z2set a) (Z2set b) <-> Z.in_set a b.
split; intros.
 apply in_inZ; trivial.
 apply inZ_in; trivial.
Qed.

Lemma eq_Zeq : forall x y, Z2set x == Z2set y -> Z.eq_set x y.
intros.
rewrite Z.eq_set_ax; split; intros.
 apply in_inZ.
 apply (proj1 (H (Z2set z))).
 apply inZ_in; trivial.

 apply in_inZ.
 apply (proj2 (H (Z2set z))).
 apply inZ_in; trivial.
Qed.

Lemma Zeq_eq : forall x y, Z.eq_set x y -> Z2set x == Z2set y.
intros.
split; intros.
 rewrite in_set_elim in H0.
 Tdestruct H0.
 destruct H1.
 simpl in H1.
 constructor.
 Texists x1; trivial.
 exists x2; trivial.
 simpl.
 transitivity x; trivial.

 rewrite in_set_elim in H0.
 Tdestruct H0.
 destruct H1.
 simpl in H1.
 constructor.
 Texists x1; trivial.
 exists x2; trivial.
 simpl.
 transitivity y; trivial.
 symmetry; trivial.
Qed.

Lemma eq_equiv x y : Z2set x == Z2set y <-> Z.eq_set x y.
split; intros.
 apply eq_Zeq; trivial.
 apply Zeq_eq; trivial.
Qed.

Instance Z2set_morph : Proper (Z.eq_set ==> eq_set) Z2set.
exact Zeq_eq.
Qed.

(** Compatibility axiom *)
Lemma in_reg : forall a a' b, a == a' -> a ∈ b -> a' ∈ b.
intros.
rewrite in_set_elim in H0.
Tdestruct H0 as (a0,eq_a,(b0,eq_b,in_ab)).
destruct (proj2_sig a') as (h,_).
Tdestruct h as (a'0, eq_a').
constructor.
Texists a'0; trivial.
exists b0; trivial.
apply Z.in_reg with a0; trivial.
apply eq_Zeq.
rewrite <- (Eq_proj _ _ eq_a).
rewrite <- (Eq_proj _ _ eq_a').
trivial.
Qed.

Instance in_morph : Proper (eq_set ==> eq_set ==> iff) in_set.
Proof.
unfold eq_set in |- *; split; intros.
 apply in_reg with x; auto.
 elim (H0 x); auto.

 apply in_reg with y; auto.
  symmetry  in |- *; auto.
  elim (H0 y); auto.
Qed.

(** Surjectivity of lifting *)
Lemma Z2set_surj : forall x, #exists y, x == Z2set y.
intros.
destruct (proj2_sig x).
Tdestruct H.
Texists x0.
split; intros.
 rewrite in_set_elim in H1.
 Tdestruct H1.
 destruct H2.
 constructor.
 Texists x2; trivial.
 exists x3; trivial.
 simpl; auto.

 rewrite in_set_elim in H1.
 Tdestruct H1.
 destruct H2.
 constructor.
 Texists x2; trivial.
 simpl in H2.
 exists x0; trivial.
 rewrite <- H2; trivial.
Qed.

(**)

Lemma ex2_equiv (P Q:_->Prop) (P' Q':_->Prop) :
  (forall x x', x == Z2set x' -> (P x <-> P' x')) ->
  (forall x x', x == Z2set x' -> (Q x <-> Q' x')) ->
  ((#ex2 P Q) <-> (#ex2 P' Q')).
split; intros.
 Tdestruct H1.
 Tdestruct (Z2set_surj x) as (x',?).
 Texists x'.
  revert H1; apply -> H; trivial.
  revert H2; apply -> H0; trivial.

 Tdestruct H1.
 Texists (Z2set x).
  revert H1; apply <- H; reflexivity.
  revert H2; apply <- H0; reflexivity.
Qed.

Lemma set_intro' (P:set->Prop) (P':set->Prop) :
  (forall x, isL (P x)) ->
  Proper (eq_set ==> iff) P ->
  (forall z, (forall x, x ∈ z <-> P x) -> P' z) ->
  (#exists z, forall x, Z.in_set x z <-> P (Z2set x)) ->
  sig P'.
intros.
apply set_intro with (fun z => forall x, Z.in_set x z <-> P (Z2set x)); trivial.
 intros.
 apply Z.eq_set_ax; intros.
 rewrite H3; rewrite H4; reflexivity.

 intros. 
 apply H1.
 split; intros.
  apply In_elim with (3:=H3); simpl; intros; auto.
  apply Eq_proj in H4.
  rewrite H4; rewrite <- H5; trivial.

  apply In_intro; simpl; intros.
  apply Eq_proj in H4.
  rewrite H5.
  rewrite <- H4; trivial.
Qed.

(** * Skolemizing Zermelo axioms *)

(** empty set *)

Lemma empty_sig : { empty | forall x, x ∈ empty -> #False }.
apply set_intro' with (P:=fun _ => #False); intros; auto.
 do 2 red; reflexivity.

 rewrite H in H0; trivial.

 Tdestruct Z.empty_ex; intros.
 Texists x; split; intros; eauto.
 Tabsurd; trivial.
Qed.

Definition empty := proj1_sig empty_sig.
Lemma empty_ax: forall x, x ∈ empty -> #False.
Proof proj2_sig empty_sig.

(** pair *)

Let pair_spec a b x := #(x == a \/ x == b).

Let pair_spec_morph a b :
  Proper (eq_set ==> iff) (pair_spec a b).
unfold pair_spec; intros.
do 2 red; intros.
rewrite H; reflexivity.
Qed.

Lemma pair_sig : forall a b,
  { pair | forall x, x ∈ pair <-> pair_spec a b x }.
intros a b.
apply set_intro' with (P:=pair_spec a b); unfold pair_spec; intros; auto.
 apply pair_spec_morph; trivial.

 Tdestruct (Z2set_surj a) as (a',?).
 Tdestruct (Z2set_surj b) as (b',?).
 Tdestruct (Z.pair_ex a' b') as (w,?).
 Texists w; intros.
 rewrite H1.
 rewrite H; rewrite H0.
 apply Tr_morph.
 apply or_iff_morphism.
  symmetry; apply eq_equiv.

  symmetry; apply eq_equiv.
Qed.

Definition pair a b := proj1_sig (pair_sig a b).
Lemma pair_ax: forall a b x, x ∈ pair a b <-> #(x == a \/ x == b).
Proof fun a b => proj2_sig (pair_sig a b).

(** union *)

Let union_spec a x := #exists2 y, x ∈ y & y ∈ a.

Let union_spec_morph a :
  Proper (eq_set==>iff) (union_spec a).
do 2 red; intros.
apply Tr_morph; apply ex2_morph; red; intros; auto with *.
rewrite H; reflexivity.
Qed.


Lemma union_sig: forall a,
  { union | forall x, x ∈ union <-> union_spec a x }.
intro a.
apply set_intro' with (P:=union_spec a); unfold union_spec; intros; auto.
 apply union_spec_morph; trivial.

 Tdestruct (Z2set_surj a) as (a',?).
 Tdestruct (Z.union_ex a') as (z,spec).
 Texists z; intros.
 rewrite spec.
 symmetry; apply ex2_equiv; intros.
  rewrite H0; apply in_equiv.

  rewrite H0; rewrite H; apply in_equiv.
Qed.

Definition union a := proj1_sig (union_sig a).
Lemma union_ax: forall a x,
  x ∈ union a <-> #exists2 y, x ∈ y & y ∈ a.
Proof fun a => proj2_sig (union_sig a).

(** subset *)

Let subset_spec a P x := x ∈ a /\ #exists2 x', x == x' & P x'.

Let subset_spec_morph a P :
  Proper (eq_set ==> iff) (subset_spec a P).
do 2 red; intros.
apply and_iff_morphism.
 rewrite H; reflexivity.

 apply Tr_morph; apply ex2_morph; red; intros; auto with *.
 rewrite H; reflexivity.
Qed.

Lemma subset_sig: forall a P,
  { subset | forall x, x ∈ subset <->
             (x ∈ a /\ #exists2 x', x==x' & P x') }.
intros a P.
apply set_intro' with (P:=subset_spec a P); unfold subset_spec; intros; auto.
 apply subset_spec_morph; trivial.

 Tdestruct (Z2set_surj a) as (a',?).
 Tdestruct (Z.subset_ex a' (fun z => #exists2 z', z' == Z2set z & P z')) as (w,?).
 Texists w; intros.
 rewrite H0.
 apply and_iff_morphism.
  rewrite H; symmetry; apply in_equiv.

  split; intros.
   Tdestruct H1.
   Tdestruct H2.
   Texists x1; trivial.
   rewrite H2; apply eq_equiv; trivial.

   Tdestruct H1.
   Texists x; auto with *.
   Texists x0; auto with *.
Qed.

Definition subset a P := proj1_sig (subset_sig a P).
Lemma subset_ax : forall a P x,
    x ∈ subset a P <-> (x ∈ a /\ #exists2 x', x==x' & P x').
Proof fun a P => proj2_sig (subset_sig a P).

(** power set *)

Let power_spec a x := forall y, y ∈ x -> y ∈ a.

Let power_spec_morph a :
  Proper (eq_set ==> iff) (power_spec a).
do 2 red; intros.
apply fa_morph; intro.
rewrite H; reflexivity.
Qed.

Lemma power_sig: forall a,
  { power | forall x, x ∈ power <-> (forall y, y ∈ x -> y ∈ a) }.
intro a.
apply set_intro' with (P:=power_spec a); unfold power_spec; intros; auto.
 apply power_spec_morph; trivial.

 Tdestruct (Z2set_surj a) as (a',?).
 Tdestruct (Z.power_ex a') as (z,spec).
 Texists z; intros.
 rewrite spec.
 split; intros.
  Tdestruct (Z2set_surj y).
  rewrite H; rewrite H2; apply in_equiv; apply H0; apply in_equiv.
  rewrite <- H2; trivial.

  apply in_equiv; rewrite <- H; apply H0; apply in_equiv; trivial.
Qed.

Definition power a := proj1_sig (power_sig a).
Lemma power_ax:
  forall a x, x ∈ power a <-> (forall y, y ∈ x -> y ∈ a).
Proof fun a => proj2_sig (power_sig a).

(** uchoice holds, but we need to give the proof that P is a specification to
    the Skolem symbol. *)

Definition uchoice_pred (P:set->Prop) :=
  (forall x x', x == x' -> P x -> P x') /\
  (#exists x, P x) /\
  (forall x x', P x -> P x' -> x == x').

Definition uchoice (P : set -> Prop) (Hp : uchoice_pred P) : set.
exists (fun z => P (Z2set z)).
destruct Hp.
destruct H0.
split; intros.
 Tdestruct H0.
 Tdestruct (Z2set_surj x).
 Texists x0; apply H with x; trivial.

 apply eq_Zeq.
 auto.
Defined.

Lemma uchoice_ax : forall P h x,
  (x ∈ uchoice P h <-> #exists2 z, P z & x ∈ z).
split; intros.
 destruct H.
 Tdestruct H.
 destruct H0.
 simpl in H0.
 Texists (Z2set x1); trivial.
 apply In_intro; intros.
 simpl in H3.
 rewrite H3.
 destruct (proj2_sig x).
 rewrite (H5 x' x0); trivial.

 Tdestruct H.
 destruct H0.
 Tdestruct H0.
 destruct H1.
 constructor.
 Texists x1; trivial.
 simpl.
 exists x2; trivial.
 apply (proj1 h x0); trivial.
 apply Eq_proj; trivial.
Qed.

Lemma uchoice_morph_raw : forall (P1 P2:set->Prop) h1 h2,
  (forall x x', x == x' -> (P1 x <-> P2 x')) ->
  uchoice P1 h1 == uchoice P2 h2.
intros.
apply eq_set_ax; intros.
rewrite uchoice_ax.
rewrite uchoice_ax.
apply Tr_morph; apply ex2_morph; red; intros.
 apply H; reflexivity.

 reflexivity.
Qed.


Instance uchoice_pred_morph : Proper ((eq_set ==> iff) ==> iff) uchoice_pred.
apply morph_impl_iff1; auto with *.
do 3 red; intros.
destruct H0 as (?,(?,?)); split;[|split]; intros.
 assert (x x0).
  revert H4; apply H; auto with *.
 revert H5; apply H; trivial.

 Tdestruct H1; Texists x0.
 revert H1; apply H; auto with *.

 apply H2; [revert H3|revert H4]; apply H; auto with *.
Qed.


Lemma uchoice_ext : forall (P:set->Prop) h x, (#P x) -> x == uchoice P h.
intros.
apply eq_set_ax;intros.
rewrite uchoice_ax.
Telim H; intro.
split; intros.
 Texists x; trivial.

 Tdestruct H0.
 destruct h.
 destruct H3.
 rewrite (H4 x x1); auto.
Qed.

Lemma uchoice_def : forall P h, #P (uchoice P h).
intros.
destruct h.
destruct a.
Tdestruct t.
Tin; apply p with x; trivial.
apply uchoice_ext; trivial.
Tin; trivial.
Qed.

(** infinite set (natural numbers) *)

Definition Nat x :=
  forall (P:set),
  empty ∈ P ->
  (forall x, x ∈ P -> union (pair x (pair x x)) ∈ P) ->
  x ∈ P.

Instance Nat_morph : Proper (eq_set ==> iff) Nat.
unfold Nat; split; intros.
 rewrite <- H; apply H0; trivial.
 rewrite H; apply H0; trivial.
Qed.

Lemma Nat_S : forall x,
  Nat x -> Nat (union (pair x (pair x x))).
unfold Nat; intros; auto.
Qed.

Definition infinite_sig :
  { infty | empty ∈ infty /\
      forall x, x ∈ infty -> union (pair x (pair x x)) ∈ infty }.
apply set_intro' with (P:=Nat).
 unfold Nat; auto.

 apply Nat_morph.

 intros.
 split; intros.
  rewrite H; red; auto.

  rewrite H in H0|-*.
  apply Nat_S; trivial.

 Tdestruct Z.infinity_ex as (infty,?,?).
 Tdestruct (Z.subset_ex infty (fun x => Nat(Z2set x))) as (z,spec).
 Texists z.
 split; intros.
  rewrite spec in H1.
  destruct H1.
  red; Tdestruct H2.
  revert H3; apply Nat_morph.
  apply eq_equiv; trivial.

  rewrite spec.
  split.
  2:Texists x; auto with *.
  apply in_equiv; apply H1; intros.
   Tdestruct H.
   assert (empty == Z2set x0).
    apply eq_set_ax; split; intros.
     Tabsurd; apply empty_ax with (1:=H3).

     Tdestruct (Z2set_surj x1).
     Tabsurd; apply H with x2.
     apply in_equiv; rewrite<- H4; trivial.
   rewrite H3; apply in_equiv; trivial.

   Tdestruct (Z2set_surj x0).
   rewrite H3 in H2; apply in_equiv in H2.
apply H0 in H2; clear H0.
Tdestruct H2.
apply in_equiv in H2; revert H2; apply in_reg.
rewrite eq_set_ax.
intros.
rewrite union_ax.
Tdestruct (Z2set_surj x3).
rewrite H2; rewrite in_equiv.
rewrite H0.
split; intros.
 Tdestruct H4.
  Texists (pair x0 x0).
   rewrite pair_ax; Tleft.
   rewrite H2; rewrite H3; apply eq_equiv; trivial.

   rewrite pair_ax; Tright; reflexivity. 

  Texists x0.
   rewrite H2; rewrite H3; apply in_equiv; trivial.

   rewrite pair_ax; Tleft; reflexivity.

 Tdestruct H4.
 rewrite <- eq_equiv.
 rewrite <- in_equiv.
 rewrite <- H3.
 rewrite <- H2.
 rewrite pair_ax in H5; Tdestruct H5.
  Tright; rewrite <- H5; trivial.

  rewrite H5 in H4.
  Tleft.
  rewrite pair_ax in H4; Tdestruct H4; trivial.
Qed.
Definition infinite := proj1_sig infinite_sig.
Lemma infinity_ax1: empty ∈ infinite.
Proof proj1 (proj2_sig infinite_sig).

Lemma infinity_ax2: forall x,
  x ∈ infinite -> union (pair x (pair x x)) ∈ infinite.
Proof proj2 (proj2_sig infinite_sig).

(** well-founded induction *)

Lemma wf_ax0 (P:set->Prop):
  (forall x, isL (P x)) ->
  (forall x, (forall y, y ∈ x -> P y) -> P x) ->
  forall x, P x.
intros.
cut (forall xs (x:set), x == Z2set xs -> P x).
 intros.
 Tdestruct (Z2set_surj x).
 eauto.
clear x.
intros xs; elim xs using Z.wf_ax0; intros; auto.
apply H0; intros.
Tdestruct (Z2set_surj y).
rewrite H2,H4 in H3.
apply in_inZ in H3; eauto.
Qed.

Lemma wf_ax :
  forall (P:set->Prop),
  (forall x, (forall y, y ∈ x -> #P y) -> #P x) ->
  forall x, #P x.
intros; apply wf_ax0 with (P:=fun x => #P x); auto.
Qed.

(** * Skolemizing Replacement *)

Definition funDom (R:set -> set -> Prop) x :=
  forall x' y y', R x y -> R x' y' -> x == x' -> y == y'.
Definition downR (R:set -> set -> Prop) x' y' :=
  exists2 x, x == Z2set x' /\ funDom R x & exists2 y, y == Z2set y' & R x y.

Lemma downR_morph : Proper
  ((eq_set ==> eq_set ==> iff) ==> Z.eq_set ==> Z.eq_set ==> iff) downR.
do 4 red; intros.
unfold downR.
apply Zeq_eq in H0.
apply Zeq_eq in H1.
apply ex2_morph; red; intros.
 apply and_iff_morphism.
  rewrite H0; reflexivity.

  unfold funDom.
  split; intros.
   rewrite <- (fun e1 => H a a e1 y2 y2) in H3; auto with *.
   rewrite <- (fun e1 => H x' x' e1 y' y') in H4; eauto with *.

   rewrite (fun e1 => H a a e1 y2 y2) in H3; auto with *.
   rewrite (fun e1 => H x' x' e1 y' y') in H4; eauto with *.

 apply ex2_morph; red; intros.
  rewrite H1; reflexivity.
  apply H; reflexivity.
Qed.

Lemma downRm : forall R x x' y y',
  Z.eq_set x x' ->
  Z.eq_set y y' ->
  downR R x y ->
  downR R x' y'.
intros.
destruct H1 as (xx,(eqx,fdomx), (yy,eqy,rel)).
exists xx.
 split; trivial.
 rewrite eqx.
 rewrite eq_equiv; trivial.
exists yy; trivial.
rewrite eqy.
rewrite eq_equiv; trivial.
Qed.

Lemma downR_fun : forall R x y y',
  downR R x y ->
  downR R x y' ->
  Z.eq_set y y'.
intros.
destruct H as (xx,(eqx,fdomx), (yy,eqy,rel)).
destruct H0 as (xx',(eqx',_), (yy',eqy',rel')).
apply eq_Zeq.
rewrite <- eqy; rewrite <- eqy'.
red in fdomx.
apply fdomx with xx'; trivial.
rewrite eqx; rewrite eqx'.
reflexivity.
Qed.

Module Type ExReplacement.
Parameter repl_ex : forall a (R:Z.set->Z.set->Prop),
  (forall x x' y y', Z.in_set x a -> Z.eq_set x x' -> Z.eq_set y y' -> R x y -> R x' y') ->
  (forall x y y', Z.in_set x a -> R x y -> R x y' -> Z.eq_set y y') ->
  #exists b, forall x, Z.in_set x b <-> #exists2 y, Z.in_set y a & R y x.
End ExReplacement.

Module SkolemReplacement (Repl : ExReplacement).

Lemma repl0 : forall (a:set) (R:set->set->Prop), set.
intros a R.
exists
 (fun a' => forall x,
  Z.in_set x a' <-> #exists2 y, Z2set y ∈ a & downR R y x).
split; intros.
 Tdestruct (Z2set_surj a).
 assert (R'm := fun x0 x' y y' (_:Z.in_set x0 x) => downRm R x0 x' y y').
 assert (R'fun := fun x0 y y' (_:Z.in_set x0 x) => downR_fun R x0 y y').
 Tdestruct (Repl.repl_ex x (downR R) R'm R'fun); intros.
 Texists x0; intros.
 rewrite H0.
 apply Tr_morph; apply ex2_morph; red; intros.
 2:reflexivity.
 split; intros.
  rewrite H.
  apply inZ_in; trivial.

  apply in_inZ.
  rewrite <- H; trivial.

 rewrite Z.eq_set_ax; intros.
 rewrite H.
 rewrite H0.
 reflexivity.
Defined.

Definition incl_set x y := forall z, z ∈ x -> z ∈ y.

Lemma repl0_mono :
  Proper (incl_set ==> (eq_set ==> eq_set ==> iff) ==> incl_set) repl0.
do 4 red; simpl; intros.
rewrite in_set_elim in *.
Tdestruct H1.
destruct H2.
simpl in *; intros.
Tdestruct (Z2set_surj y).
assert (R'm := fun x x' y y' (_:Z.in_set x x3) => downRm y0 x x' y y').
assert (R'fun := fun x y y' (_:Z.in_set x x3) => downR_fun y0 x y y').
Tdestruct (Repl.repl_ex x3 (downR y0) R'm R'fun).
Texists x1; trivial.
exists x4; trivial.
 intro; rewrite H5.
 apply Tr_morph; apply ex2_morph; red; intros; auto with *.
 rewrite H4.
 symmetry; apply in_equiv.

 rewrite H5.
 rewrite H2 in H3.
 clear x2 H1 H2 x4 H5.
 Tdestruct H3.
 Texists x2.
  apply H in H1.
  rewrite H4 in H1; rewrite in_equiv in H1; trivial.

  revert H2; apply iff_impl; apply downR_morph; auto with *.
Qed. 

Lemma repl_sig :
  { repl |
    Proper (incl_set ==> (eq_set ==> eq_set ==> iff) ==> incl_set) repl /\
    forall a (R:set->set->Prop),
    (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x ∈ a -> R x y -> R x y' -> y == y') ->
    forall x, x ∈ repl a R <-> #exists2 y, y ∈ a & R y x }.
exists repl0; split.
 exact repl0_mono.
split; intros.
 rewrite in_set_elim in H1.
 Tdestruct H1.
 destruct H2; simpl in *.
 rewrite H2 in H3.
 Tdestruct H3.
 destruct H4.
 destruct H5.
 destruct H4.
 Texists x3.
  rewrite H4; trivial.
 revert H6; apply H; auto with *.
  rewrite H4; trivial.

  apply Eq_proj in H1.
  rewrite H1; trivial.

 Tdestruct H1.
 apply In_intro; simpl; intros.
 rewrite H4; clear H4.
 Tdestruct (Z2set_surj x0).
 Texists x1.
  rewrite <- H4; trivial.
 exists x0.
  split; intros; eauto.
  red; intros.
  apply H0 with x0; trivial.
  revert H6; apply H; auto with *.
  rewrite <- H7; trivial.

  exists x; trivial.
  apply Eq_proj; trivial.
Defined.

Definition repl := proj1_sig repl_sig.
Lemma repl_mono : 
  Proper (incl_set ==> (eq_set ==> eq_set ==> iff) ==> incl_set) repl.
Proof (proj1 (proj2_sig repl_sig)).
Lemma repl_ax:
    forall a (R:set->set->Prop),
    (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x ∈ a -> R x y -> R x y' -> y == y') ->
    forall x, x ∈ repl a R <-> #exists2 y, y ∈ a & R y x.
Proof proj2 (proj2_sig repl_sig).

End SkolemReplacement.

(*
(** Replacement can be skolemized in the general case only using TTColl *)
Module TTCollRepl : ExReplacement.
Definition repl_ex := Z.repl_ex.
End TTCollRepl.
Include SkolemReplacement TTCollRepl.
*)

(** * Collection *)

(** ** Keeping existential version of collection in intutionistic logic. *)

Definition downR' (R:set -> set -> Prop) x' y' :=
  exists2 x, x == Z2set x' & exists2 y, y == Z2set y' & R x y.

Lemma downR'_morph : Proper
  ((eq_set ==> eq_set ==> iff) ==> Z.eq_set ==> Z.eq_set ==> iff) downR'.
do 4 red; intros.
unfold downR'.
apply Zeq_eq in H0.
apply Zeq_eq in H1.
apply ex2_morph; red; intros.
 rewrite H0; reflexivity.

 apply ex2_morph; red; intros.
  rewrite H1; reflexivity.
  apply H; reflexivity.
Qed.

Lemma coll_ex : forall A (R:set->set->Prop), 
    Proper (eq_set ==> eq_set ==> iff) R ->
    #exists B, forall x, x ∈ A ->
         (#exists y, R x y) -> #exists2 y, y ∈ B & R x y.
intros.
Tdestruct (Z2set_surj A) as (A',?).
Tdestruct (Z.coll_ex A' _ (downR'_morph R R H)) as (B,HB).
Texists (Z2set B).
intros.
rewrite H0 in H1.
Tdestruct (Z2set_surj x) as (x',?).
rewrite H3 in H1; rewrite in_equiv in H1.
assert (#exists y, downR' R x' y).
 Tdestruct H2 as (y,?).
 Tdestruct (Z2set_surj y) as (y',?).
 Texists y'; red; eauto.
Tdestruct (HB _ H1 H4) as (y,?,(x'',?,(y',?,?))).
Texists y'.
 rewrite H7; rewrite in_equiv; trivial.

 rewrite H3; rewrite <- H6; trivial.
Qed.

(** ** Skolemizing Collection in classical logic *)

Module ClassicCollection.

(** Proving that collection can be skolemized in classical ZF:
    we need excluded-middle to prove coll_ax_uniq (see EnsEm)
 *)

Section Classic.

Hypothesis EM : forall P, #(P \/ (P -> #False)).

(** We need to provide a spec that is more specific than what appears here
    (it is not uniquely satifiable). Instead, we specify coll as the
    smallest Veblen universe that satisfies collection. This is why we need
    excluded-middle. *)
Lemma coll_sig : forall A (R:set->set->Prop), 
  {coll| Proper (eq_set==>eq_set==>iff) R ->
     forall x, x ∈ A ->
     (#exists y, R x y) ->
     (#exists2 y, y ∈ coll & R x y) }.
intros A R.
pose (R' x y := exists2 x', Z2set x == x' & exists2 y', Z2set y == y' & R x' y').
assert (R'm : Proper (Z.eq_set==>Z.eq_set==>iff) R').
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 destruct H1 as (x'',?,(y'',?,?)).
 exists x'';[|exists y'';trivial].
  transitivity (Z2set x); trivial.
  apply Zeq_eq.
  symmetry; trivial.

  transitivity (Z2set x0); trivial.
  apply Zeq_eq.
  symmetry; trivial.
apply set_intro with
  (Z.lst_rk(fun B => exists2 A', Z2set A' == A & forall x, Z.in_set x A' ->
      (#exists y, R' x y) ->
      (#exists2 y, Z.in_set y B & R' x y))); intros.
 Tdestruct (Z2set_surj A) as (A',e).
 Tdestruct (Z.coll_ax_uniq EM A' R' R'm) as (B,HB); eauto.
 Texists B.
 revert HB; apply Z.lst_rk_morph; auto with *.
 intros.
 split; intros.
  exists A'; intros; auto with *.
  Tdestruct (H0 x0 H1 H2) as (y,?,?); trivial.
  Texists y; trivial.
  revert H3; apply Zin_morph; auto with *.

  destruct H0 as (A'',e',?).
  rewrite e in e'.
  apply eq_Zeq in e'.
  rewrite <- e' in H1.
  Tdestruct (H0 x0 H1 H2) as (y,?,?); trivial.
  Texists y; trivial.
  revert H3; apply Zin_morph; auto with *.

 apply Z.lst_fun with (1:=H) (2:=H0).

 Tdestruct Hex as (B,HB).
 assert (Bok := Z.lst_incl _ _ HB).
 destruct Bok as (A',eA,Bok).
 Tdestruct (Z2set_surj x) as (x',ex).
 rewrite ex in H0; rewrite <- eA in H0; apply in_inZ in H0.
 assert (#exists y, R' x' y).
  Tdestruct H1 as (y,Rxy).
  Tdestruct (Z2set_surj y) as (y',ey).
  Texists y'; exists x; [|exists y]; auto with *.
 Tdestruct (Bok x' H0 H2)  as (y,?,?).
 destruct H4 as (x'',?,(y',?,?)).
 Texists (Z2set y).
  apply In_intro; simpl; intros.
  specialize Huniq with (1:=HB) (2:=H8).
  rewrite <- Huniq.
  rewrite H7; trivial.

  revert H6; apply H; trivial.
  rewrite ex; trivial.
Qed.

Definition coll A R := proj1_sig (coll_sig A R).
Lemma coll_ax : forall A (R:set->set->Prop), 
  Proper (eq_set==>eq_set==>iff) R ->
  forall x, x ∈ A -> (#exists y, R x y) ->
  #exists2 y, y ∈ coll A R & R x y.
Proof (fun A R => proj2_sig (coll_sig A R)).

End Classic.
End ClassicCollection.

End Skolem.

(** * Instance *)


(** Several useful instances *)

(** Model of IZF_R *)

Module IZF_R <: IZF_R_sig CoqSublogicThms.
  Import CoqSublogic.
  Include Skolem CoqSublogicThms.
  Definition intuit : forall P:Prop, Tr P -> P := fun P h => h.
  Module Re <: ExReplacement.
    Definition repl_ex := Z.intuit_repl_ax intuit.
  End Re.
  Include SkolemReplacement Re.
End IZF_R.

Let IZFRpack := (IZF_R.repl_mono,IZF_R.repl_ax,IZF_R.wf_ax).
Print Assumptions IZFRpack. (* TTrepl *)

(** Model of IZF_C *)

Module IZF_C <: IZF_C_sig CoqSublogicThms := Skolem CoqSublogicThms.
Let IZFCpack := (IZF_C.coll_ex,IZF_C.wf_ax).
Print Assumptions IZFCpack. (* TTcoll (with intuitionistic equality on sets) *)

(** A model of ZF, based only on TTColl (no ecluded-middle in the
    metatheory).
 *)
Module ZF <: ZF_sig ClassicSublogicThms.
 Include Skolem ClassicSublogicThms.
 Import ClassicSublogicThms.
 Lemma EM : forall P, #(P \/ (P -> #False)).
cbv beta; intros P nem.
apply nem.
right; intros p _.
apply nem.
left; exact p.
Qed.
 Definition coll := (ClassicCollection.coll EM).
 Lemma coll_ax : forall A R, 
    Proper (eq_set==>eq_set==>iff) R ->
    forall x, x ∈ A ->
      (#exists y, R x y) -> (#exists2 y, y ∈ coll A R & R x y).
 Proof ClassicCollection.coll_ax EM.
End ZF.

Let ZFpack := ZF.coll_ax.
Print Assumptions ZFpack. (* TTColl (with classical equality on sets) *)
(* Eval cbv beta delta - [ ZF.Z.eq_set Proper respectful iff ] iota in ZF.Z.ttcoll.
 *)
