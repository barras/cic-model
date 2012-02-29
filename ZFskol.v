
(* In this file, we show the equivalence between the Skolemized
   and existentially quantified presentations of ZF.
 *)

Require Import basic.
Require Export ZFdef.
Require Import Sublogic.

Module Skolem (Z : IZF_R_Ex_sig CoqSublogicThms) <: IZF_R_sig CoqSublogicThms.

Instance Zsetoid: Equivalence Z.eq_set.
Proof.
split; red; intros; rewrite Z.eq_set_ax in *; intros.
 reflexivity.
 symmetry; trivial.
 transitivity (Z.in_set x0 y); trivial.
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

Definition set :=
  { f : Z.set -> Prop |
    (exists u, f u) /\
    (forall a a', f a -> f a' -> Z.eq_set a a') }.

Lemma set_intro : forall (f:Z.set->Prop) (P:set->Prop),
  (exists u, f u) ->
  (forall a a', f a -> f a' -> Z.eq_set a a') ->
  (forall Hex Huniq, P (exist _ f (conj Hex Huniq))) ->
  sig P.
intros.
exists (exist (fun _ => _ /\ _) f (conj H H0)); trivial. (* regression of unification *)
(*exists (exist _ f (conj H H0)); trivial.*)
Qed.

Inductive in_set_ (x y:set) : Prop :=
 InSet
  (_:exists2 x', proj1_sig x x' &
     exists2 y', proj1_sig y y' & Z.in_set x' y').

Definition in_set := in_set_.

Lemma in_set_elim : forall x y, in_set x y <->
  exists2 x', proj1_sig x x' &
  exists2 y', proj1_sig y y' & Z.in_set x' y'.
split; intros.
 destruct H; trivial.
 constructor; trivial.
Qed.

Notation "x \in y" := (in_set x y).

Definition eq_set a b := forall x, x \in a <-> x \in b.

Notation "x == y" := (eq_set x y).

Lemma eq_set_ax : forall a b, a == b <-> (forall x, x \in a <-> x \in b).
reflexivity.
Qed.

Instance eq_setoid: Equivalence eq_set.
Proof.
split; do 2 red; intros.
 reflexivity.
 symmetry; trivial.
 transitivity (x0 \in y); trivial.
Qed.

Lemma In_intro: forall x y: set,
  (forall x' y', proj1_sig x x' -> proj1_sig y y' -> Z.in_set x' y') ->
  x \in y.
intros.
destruct (proj2_sig x).
destruct H0.
destruct (proj2_sig y).
destruct H2.
constructor.
exists x0; trivial.
exists x1; auto.
Qed.


Definition Z2set (x:Z.set) : set.
exists (fun a => Z.eq_set a x).
split.
 exists x; reflexivity.
 intros; transitivity x; trivial.
 symmetry; trivial.
Defined.

Lemma Z2set_surj : forall x, exists y, x == Z2set y.
intros.
destruct (proj2_sig x).
destruct H.
exists x0.
split; intros.
 rewrite in_set_elim in H1.
 destruct H1.
 destruct H2.
 constructor.
 exists x2; trivial.
 exists x3; trivial.
 simpl; auto.

 rewrite in_set_elim in H1.
 destruct H1.
 destruct H2.
 constructor.
 exists x2; trivial.
 simpl in H2.
 exists x0; trivial.
 rewrite <- H2; trivial.
Qed.

Lemma Eq_proj : forall (x:set) x', proj1_sig x x' -> x == Z2set x'.
intros.
destruct (proj2_sig x).
clear H0.
split; intros.
 rewrite in_set_elim in H0.
 destruct H0.
 destruct H2.
 constructor.
 exists x1; simpl; trivial.
 exists x2; auto.

 rewrite in_set_elim in H0.
 destruct H0; simpl in *.
 destruct H2.
 constructor.
 exists x1; simpl; trivial.
 exists x'; trivial.
 rewrite <- H2; trivial.
Qed.

Lemma inZ_in : forall a b, Z.in_set a b -> Z2set a \in Z2set b.
unfold Z2set, in_set; simpl.
intros.
constructor; simpl.
exists a; try reflexivity.
exists b; try reflexivity; trivial.
Qed.

Lemma in_inZ : forall a b, Z2set a \in Z2set b -> Z.in_set a b.
intros.
rewrite in_set_elim in H.
destruct H.
destruct H0.
unfold Z2set in *; simpl in *.
apply Z.in_reg with x; trivial.
rewrite <- H0; auto.
Qed.

Lemma eq_Zeq : forall x y, Z2set x == Z2set y -> Z.eq_set x y.
intros.
rewrite Z.eq_set_ax; split; intros.
 apply in_inZ.
 apply (proj1 (H (Z2set x0))).
 apply inZ_in; trivial.

 apply in_inZ.
 apply (proj2 (H (Z2set x0))).
 apply inZ_in; trivial.
Qed.

Lemma Zeq_eq : forall x y, Z.eq_set x y -> Z2set x == Z2set y.
intros.
split; intros.
 rewrite in_set_elim in H0.
 destruct H0.
 destruct H1.
 simpl in H1.
 constructor.
 exists x1; trivial.
 exists x2; trivial.
 simpl.
 transitivity x; trivial.

 rewrite in_set_elim in H0.
 destruct H0.
 destruct H1.
 simpl in H1.
 constructor.
 exists x1; trivial.
 exists x2; trivial.
 simpl.
 transitivity y; trivial.
 symmetry; trivial.
Qed.

Instance Z2set_morph : Proper (Z.eq_set ==> eq_set) Z2set.
exact Zeq_eq.
Qed.

Lemma in_reg : forall a a' b, a == a' -> a \in b -> a' \in b.
intros.
rewrite in_set_elim in H0.
destruct H0 as (a0,eq_a,(b0,eq_b,in_ab)).
destruct (proj2_sig a') as ((a'0, eq_a'),_).
constructor.
exists a'0; trivial.
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

(* empty set *)

Lemma empty_sig : { empty | forall x, ~ x \in empty }.
apply set_intro with (fun x:Z.set => forall y, ~ Z.in_set y x); intros.
 apply Z.empty_ex.

 rewrite Z.eq_set_ax; split; intros.
  elim H with x; trivial.
  elim H0 with x; trivial.

 red; intros.
 rewrite in_set_elim in H.
 destruct H; simpl in *.
 destruct H0.
 elim H0 with x0; trivial.
Qed.

Definition empty := proj1_sig empty_sig.
Lemma empty_ax: forall x, ~ x \in empty.
Proof proj2_sig empty_sig.

(* pair *)

Lemma pair_sig : forall a b,
  { pair | forall x, x \in pair <-> (x == a \/ x == b) }.
intros a b.
apply set_intro with
  (fun x => forall y, y \in Z2set x <-> y == a \/ y == b); intros.
 elim (Z2set_surj a); intros.
 elim (Z2set_surj b); intros.
 elim Z.pair_ex with x x0; intros.
 exists x1; intros.
 elim (Z2set_surj y); intros.
 rewrite H2.
 transitivity (Z.in_set x2 x1).
  split; intros; first [apply inZ_in|apply in_inZ]; trivial. 
  apply iff_trans with (1:=H1 x2).
  rewrite H.
  rewrite H0.
  setoid_replace (Z.eq_set x2 x) with (Z2set x2 == Z2set x).
  setoid_replace (Z.eq_set x2 x0) with (Z2set x2 == Z2set x0).
  reflexivity.
  split; intros; first [apply Zeq_eq|apply eq_Zeq]; trivial. 
  split; intros; first [apply Zeq_eq|apply eq_Zeq]; trivial. 

 intros; rewrite Z.eq_set_ax; intros.
 transitivity (Z2set x \in Z2set a0).
  split; intros; first [apply inZ_in|apply in_inZ]; trivial. 
  transitivity (Z2set x == a \/ Z2set x == b); auto.
  symmetry.
  transitivity (Z2set x \in Z2set a'); trivial.
  split; intros; first [apply inZ_in|apply in_inZ]; trivial.

 split; intros.
  rewrite in_set_elim in H.
  destruct H; simpl in *.
  destruct H0.
  apply (proj1 (H0 x)).
  constructor.
  exists x0; trivial; simpl.
  exists x1; trivial; reflexivity.

  apply In_intro; simpl; intros.
  apply in_inZ.
  rewrite <- (Eq_proj _ _ H0). 
  apply (proj2 (H1 x)); trivial.
Qed.

Definition pair a b := proj1_sig (pair_sig a b).
Lemma pair_ax: forall a b x, x \in pair a b <-> (x == a \/ x == b).
Proof fun a b => proj2_sig (pair_sig a b).

(* union *)

Lemma union_sig: forall a,
  { union | forall x, x \in union <-> (exists2 y, x \in y & y \in a) }.
intro a.
apply set_intro with
 (fun x => forall z,
  Z.in_set z x <-> exists2 y, Z.in_set z y & Z2set y \in a); intros.
 elim (Z2set_surj a); intros.
 elim (Z.union_ex x); intros.
 exists x0.
 intros.
 apply iff_trans with (1:=H0 z).
 split; intros.
  destruct H1.
  exists x1; trivial.
  rewrite H; apply inZ_in; trivial.

  destruct H1.
  exists x1; trivial.
  apply in_inZ; rewrite <- H; trivial.

 rewrite Z.eq_set_ax; intros.
 apply iff_trans with (1:=H x).
 symmetry; trivial.

split; intros.
 rewrite in_set_elim in H.
 destruct H; simpl in *.
 destruct H0.
 elim (proj1 (H0 _) H1); intros.
 exists (Z2set x2); trivial.
 rewrite (Eq_proj  _ _ H).
 apply inZ_in; trivial.

 destruct H.
 apply In_intro; simpl; intros.
 apply (proj2 (H2 x')).
 elim (Z2set_surj x0); intros.
 exists x1.
  apply in_inZ.
  rewrite <- H3; rewrite <- (Eq_proj _ _ H1); trivial.

  rewrite <- H3; trivial.
Qed.

Definition union a := proj1_sig (union_sig a).
Lemma union_ax: forall a x,
  x \in union a <-> (exists2 y, x \in y & y \in a).
Proof fun a => proj2_sig (union_sig a).

(* subset *)

Lemma subset_sig: forall a P,
  { subset | forall x, x \in subset <->
             (x \in a /\ exists2 x', x==x' & P x') }.
intros a P.
apply set_intro with
  (fun x => forall y, y \in Z2set x <->
    (y \in a /\ exists2 y', y==y' & P y')); intros.
 elim (Z2set_surj a); intros.
 elim Z.subset_ex with
   x (fun z => exists2 z', z' == Z2set z & P z'); intros.
 exists x0; intros.
 elim (Z2set_surj y); intros.
 rewrite H1.
 transitivity (Z.in_set x1 x0).
  split; intros; first [apply inZ_in|apply in_inZ]; trivial. 
  apply iff_trans with (1:=H0 x1).
  rewrite H.
  apply and_iff_morphism.
   split; intros; first [apply inZ_in|apply in_inZ]; trivial. 

   split; destruct 1.
    destruct H3.
    exists x3; trivial.
    rewrite H1; rewrite H3; apply Zeq_eq; trivial.

    exists x1;[reflexivity|].
    exists x2; trivial.
    rewrite <- H1; symmetry; trivial.

 apply eq_Zeq.
 rewrite eq_set_ax; intros.
 rewrite H.
 rewrite H0.
 reflexivity.

 split; intros.
  rewrite in_set_elim in H.
  destruct H; simpl in *.
  destruct H0.
  apply (proj1 (H0 x)).
  constructor.
  exists x0; trivial; simpl.
  exists x1; trivial; reflexivity.

  apply In_intro; simpl; intros.
  apply in_inZ.
  rewrite <- (Eq_proj _ _ H0). 
  apply (proj2 (H1 x)); trivial.
Qed.

Definition subset a P := proj1_sig (subset_sig a P).
Lemma subset_ax : forall a P x,
    x \in subset a P <-> (x \in a /\ exists2 x', x==x' & P x').
Proof fun a P => proj2_sig (subset_sig a P).

(* power set *)

Lemma power_sig: forall a,
  { power | forall x, x \in power <-> (forall y, y \in x -> y \in a) }.
intro a.
apply set_intro with
 (fun x => forall z,
  Z.in_set z x <-> (forall y, Z.in_set y z -> Z2set y \in a)); intros.
 elim (Z2set_surj a); intros.
 elim (Z.power_ex x); intros.
 exists x0; intros.
 apply iff_trans with (1:= H0 z).
 split; intros.
  rewrite H; apply inZ_in; auto.
  apply in_inZ; rewrite <- H; auto.

 rewrite Z.eq_set_ax; intros.
 apply iff_trans with (1:=H x).
 symmetry; trivial.

split; intros.
 rewrite in_set_elim in H.
 destruct H; simpl in *.
 destruct H1.
 elim (Z2set_surj y); intros.
 rewrite H3.
 apply (proj1 (H1 _) H2).
 apply in_inZ; rewrite <- H3; rewrite <- (Eq_proj _ _ H); trivial.

 apply In_intro; simpl; intros.
 apply (proj2 (H1 x')).
 intros.
 apply H.
 rewrite (Eq_proj _ _ H0); apply inZ_in; trivial.
Qed.

Definition power a := proj1_sig (power_sig a).
Lemma power_ax:
  forall a x, x \in power a <-> (forall y, y \in x -> y \in a).
Proof fun a => proj2_sig (power_sig a).

(* uchoice *)

Definition uchoice_pred (P:set->Prop) :=
  (forall x x', x == x' -> P x -> P x') /\
  (exists x, P x) /\
  (forall x x', P x -> P x' -> x == x').

Definition uchoice (P : set -> Prop) (Hp : uchoice_pred P) : set.
exists (fun z => P (Z2set z)).
destruct Hp.
destruct H0.
split; intros.
 destruct H0.
 destruct (Z2set_surj x).
 exists x0; apply H with x; trivial.

 apply eq_Zeq.
 auto.
Defined.

Lemma uchoice_ax : forall P h x,
  (x \in uchoice P h <-> exists2 z, P z & x \in z).
split; intros.
 destruct H.
 destruct H.
 destruct H0.
 simpl in H0.
 exists (Z2set x1); trivial.
 apply In_intro; intros.
 simpl in H3.
 rewrite H3.
 destruct (proj2_sig x).
 rewrite (H5 x' x0); trivial.

 destruct H.
 destruct H0.
 destruct H0.
 destruct H1.
 constructor.
 exists x1; trivial.
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
apply ex2_morph; red; intros.
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

 destruct H1; exists x0.
 revert H1; apply H; auto with *.

 apply H2; [revert H3|revert H4]; apply H; auto with *.
Qed.


Lemma uchoice_ext : forall (P:set->Prop) h x, P x -> x == uchoice P h.
intros.
apply eq_set_ax;intros.
rewrite uchoice_ax.
split; intros.
 exists x; trivial.

 destruct H0.
 destruct h.
 destruct H3.
 rewrite (H4 x x1); auto.
Qed.

Lemma uchoice_def : forall P h, P (uchoice P h).
intros.
destruct h.
destruct a.
destruct e.
apply p with x; trivial.
apply uchoice_ext; trivial.
Qed.

(* replacement *)

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

Lemma downR_fun : forall R x x' y y',
  downR R x y ->
  downR R x' y' ->
  Z.eq_set x x' ->
  Z.eq_set y y'.
intros.
destruct H as (xx,(eqx,fdomx),(yy,eqy,rel)).
destruct H0 as (xx',(eqx',_),(yy',eqy',rel')).
apply eq_Zeq.
rewrite <- eqy; rewrite <- eqy'.
red in fdomx.
apply fdomx with xx'; trivial.
rewrite eqx; rewrite eqx'.
apply Zeq_eq; trivial.
Qed.

Lemma repl0 : forall (a:set) (R:set->set->Prop), set.
intros a R.
exists
 (fun a' => forall x,
  Z.in_set x a' <-> exists2 y, Z2set y \in a & exists2 x', Z.eq_set x x' & downR R y x').
split; intros.
 elim (Z2set_surj a); intros.
 elim Z.repl_ex with x (downR R); intros.
  exists x0; intros.
  rewrite H0.
  split; intros.
   destruct H1.
   exists x2; trivial.
   rewrite H.
   apply inZ_in; trivial.

   destruct H1.
   exists x2; trivial.
   apply in_inZ.
   rewrite <- H; trivial.

  apply downR_fun with (1:=H1)(2:=H2); trivial.

 rewrite Z.eq_set_ax; intros.
 rewrite H.
 rewrite H0.
 reflexivity.
Defined.

Definition incl_set x y := forall z, z \in x -> z \in y.

Lemma repl0_mono :
  Proper (incl_set ==> (eq_set ==> eq_set ==> iff) ==> incl_set) repl0.
do 4 red; simpl; intros.
rewrite in_set_elim in *.
destruct H1.
exists x1; trivial.
clear z H1.
destruct H2.
simpl in *; intros.
elim (Z2set_surj y); intros.
destruct (Z.repl_ex x3 (downR y0)).
 intros.
 apply downR_fun with (1:=H5) (2:=H6); trivial.

exists x4; trivial.
 intro; rewrite H4.
 apply ex2_morph; red; intros; auto with *.
 rewrite H3.
 split; intros.
  apply inZ_in; trivial.
  apply in_inZ; trivial.

 rewrite H4.
 rewrite H1 in H2.
 clear x2 H1 x4 H4.
 destruct H2.
 destruct H2.
 exists x2.
  apply in_inZ.
  rewrite <- H3; apply H; trivial.

  exists x4; trivial.
  rewrite <- (fun e1 => downR_morph _ _ H0 x2 x2 e1 x4 x4); auto with *.
Qed. 

Lemma repl_sig :
  { repl |
    Proper (incl_set ==> (eq_set ==> eq_set ==> iff) ==> incl_set) repl /\
    forall a (R:set->set->Prop),
    (forall x x' y y', x \in a -> R x y -> R x' y' -> x == x' -> y == y') ->
    forall x, x \in repl a R <-> (exists2 y, y \in a & exists2 x', x == x' & R y x') }.
exists repl0; split.
 exact repl0_mono.
split; intros.
 rewrite in_set_elim in H0.
 destruct H0.
 destruct H1; simpl in *.
 elim (proj1 (H1 x0) H2); intros.
 destruct H4.
 destruct H5.
 destruct H5.
 destruct H6.
 rewrite <- H5 in H3; clear x2 H5.
 apply Zeq_eq in H4.
 rewrite <- H4 in H6; clear x3 H4.
 exists x4; trivial.
 exists x5; trivial.
 rewrite H6.
 apply Eq_proj; trivial.

 destruct H0.
 destruct H1.
 apply In_intro; simpl; intros.
 apply (proj2 (H4 x')); clear H4.
 elim (Z2set_surj x0); intros.
 exists x2.
  rewrite <- H4; trivial.
 exists x'.
  reflexivity.
 exists x0.
  split; intros; eauto.
  red; eauto.
 exists x1; auto.
 rewrite <- H1.
 apply Eq_proj; trivial.
Defined.

Definition repl := proj1_sig repl_sig.
Lemma repl_mono : 
  Proper (incl_set ==> (eq_set ==> eq_set ==> iff) ==> incl_set) repl.
Proof (proj1 (proj2_sig repl_sig)).
Lemma repl_ax:
    forall a (R:set->set->Prop),
    (forall x x' y y', x \in a -> R x y -> R x' y' -> x == x' -> y == y') ->
    forall x, x \in repl a R <-> (exists2 y, y \in a & exists2 x', x == x' & R y x').
Proof proj2 (proj2_sig repl_sig).

(* infinite set (natural numbers) *)

Definition Nat x :=
  forall (P:set),
  empty \in P ->
  (forall x, x \in P -> union (pair x (pair x x)) \in P) ->
  x \in P.

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
  { infty | empty \in infty /\
      forall x, x \in infty -> union (pair x (pair x x)) \in infty }.
apply set_intro with
  (fun x => forall y, Z.in_set y x <-> Nat (Z2set y)); intros.
 elim Z.infinity_ex; intros.
 elim Z.repl_ex with x (fun x' y' => Z.eq_set x' y' /\ Nat (Z2set y')); intros.
  exists x0; intros.
  rewrite H1.
  split; intros.
   destruct H2.
   destruct H3.
   destruct H4.
   rewrite H3; trivial.

   exists y.
    red in H2.
    apply in_inZ.
    apply H2; intros.
     destruct H.
     apply inZ_in in H3.
     apply in_reg with (Z2set x1); trivial.
     split; intros.
      destruct (Z2set_surj x2).
      rewrite H5 in H4; apply in_inZ in H4.
      elim H with x3; trivial.

      elim empty_ax with x2; trivial.

     destruct (Z2set_surj x1).
     rewrite H4 in H3; apply in_inZ in H3.
     apply H0 in H3.
     destruct H3.
     apply in_reg with (Z2set x3).
     2:apply inZ_in; trivial.
     split; simpl; intros.
      rewrite union_ax.
      destruct (Z2set_surj x4).
      rewrite H7 in H6; apply in_inZ in H6; rewrite H3 in H6.
      destruct H6.
       exists (pair x1 x1).
        rewrite pair_ax; left.
        rewrite H7; rewrite H4; apply Zeq_eq; trivial.

        rewrite pair_ax; right; reflexivity.

       exists x1.
        rewrite H7; rewrite H4; apply inZ_in; trivial.

        rewrite pair_ax; left; reflexivity.

      destruct (Z2set_surj x4).
      rewrite H7; apply inZ_in.
      rewrite H3.
      rewrite H7 in H6; clear x4 H7.
      rewrite union_ax in H6.
      destruct H6.
      rewrite pair_ax in H7; destruct H7.
       right; apply in_inZ.
       rewrite <- H4; rewrite <- H7; trivial.

       rewrite H7 in H6; clear x4 H7.
       left; apply eq_Zeq.
       rewrite <- H4.
       rewrite pair_ax in H6; destruct H6; trivial.

    exists y; trivial.
    reflexivity.

   split; trivial; reflexivity.

  destruct H2.
  destruct H3.
  transitivity x0; trivial.
   symmetry; trivial.
  transitivity x'; trivial.

 rewrite Z.eq_set_ax; split; intros.
  rewrite H0; rewrite H in H1; trivial.

  rewrite H; rewrite H0 in H1; trivial.

split; intros.
 apply In_intro; simpl; unfold Nat; intros.
 apply (proj2 (H0 x')); intros.
 apply in_reg with empty; trivial.
 split; intros.
  elim empty_ax with x; trivial.

  elim (Z2set_surj x); intros.
 apply Eq_proj in H.
 rewrite <- H in H3.
 elim empty_ax with (1:=H3).

 rewrite in_set_elim in H.
 destruct H; simpl in *.
 destruct H0.
 apply In_intro; simpl; intros.
 apply (proj2 (H3 x')).
 setoid_replace (Z2set x') with (union (pair x (pair x x))).
  apply Nat_S.
  rewrite (Eq_proj _ _ H).
  apply (proj1 (H0 x0)); trivial.

  split; intros.
   elim (Z2set_surj x2); intros.
   rewrite H5 in H4 |- *; clear H5 x2.
   apply Eq_proj in H2.
   rewrite <- H2 in H4; trivial. 

   elim (Z2set_surj x2); intros.
   rewrite H5 in H4 |- *; clear H5 x2.
   apply Eq_proj in H2.
   rewrite <- H2; trivial.
Qed.
Definition infinite := proj1_sig infinite_sig.
Lemma infinity_ax1: empty \in infinite.
Proof proj1 (proj2_sig infinite_sig).

Lemma infinity_ax2: forall x,
  x \in infinite -> union (pair x (pair x x)) \in infinite.
Proof proj2 (proj2_sig infinite_sig).

(* well-founded induction *)

Lemma wf_ax : forall (P:set->Prop),
  (forall x, P x -> P x) ->
  (forall x, (forall y, y \in x -> P y) -> P x) ->
  forall x, P x.
intros P _ H x.
cut (forall xs (x:set), x == Z2set xs -> P x).
 intros.
 destruct (Z2set_surj x).
 eauto.
clear x.
intros xs; elim xs using Z.wf_ax; intros; trivial.
apply H; intros.
elim (Z2set_surj y); intros.
rewrite H1,H3 in H2.
apply in_inZ in H2; eauto.
Qed.

(* Proving that collection can be skolemized in classical ZF:
   we need excluded-middle to prove coll_ax_uniq (see EnsEm)
 *)

Section Collection.

(* A predicate transformer that is true for the least element of
   the Veblen hierarchy that satisfies the input predicate. If there
   is no unique solution, the returned predicate is empty. No
   excluded-middle needed here.
 *)
Hypothesis lst_rk : (Z.set->Prop) -> Z.set -> Prop.
Hypothesis lst_rk_morph : forall (P P':Z.set->Prop),
  (forall x x', Z.eq_set x x' -> (P x <-> P' x')) ->
  forall y y', Z.eq_set y y' -> lst_rk P y -> lst_rk P' y'.
Hypothesis lst_incl : forall P y, lst_rk P y -> P y.
Hypothesis lst_fun : forall P y y', lst_rk P y -> lst_rk P y' -> Z.eq_set y y'.

(* The modification of the collection axiom that return the least Veblen universe
   that collects all the images of A. This can exist only when the Veblen hierarchy
   is totally ordered, which requires excluded-middle. See EnsEm for the
   construction.
 *)
Hypothesis coll_ax_uniq : forall A (R:Z.set->Z.set->Prop), 
    (forall x x' y y', Z.in_set x A -> Z.eq_set x x' -> Z.eq_set y y' ->
     R x y -> R x' y') ->
    exists B, lst_rk(fun B =>
      forall x, Z.in_set x A ->
      (exists y, R x y) ->
      exists2 y, Z.in_set y B & R x y) B.
(* We could also try to prove that B grows when A and R do. *)

Lemma coll_sig : forall A (R:set->set->Prop), 
  {coll| Proper (eq_set==>eq_set==>iff) R ->
     forall x, x \in A -> (exists y, R x y) ->
     exists2 y, y \in coll & R x y }.
intros A R.
pose (R' x y := exists2 x', Z2set x == x' & exists2 y', Z2set y == y' & R x' y').
assert (R'm : forall x x' y y', Z.eq_set x x' -> Z.eq_set y y' ->
     R' x y -> R' x' y').
 destruct 3 as (x'',?,(y'',?,?)).
 exists x'';[|exists y'';trivial].
  transitivity (Z2set x); trivial.
  apply Zeq_eq.
  symmetry; trivial.

  transitivity (Z2set y); trivial.
  apply Zeq_eq.
  symmetry; trivial.
apply set_intro with
  (lst_rk(fun B => exists2 A', Z2set A' == A & forall x, Z.in_set x A' ->
      (exists y, R' x y) ->
      exists2 y, Z.in_set y B & R' x y)); intros.
 destruct (Z2set_surj A) as (A',e).
 destruct coll_ax_uniq with A' R' as (B,HB); eauto.
 exists B.
 revert HB; apply lst_rk_morph; auto with *.
 intros.
 split; intros.
  exists A'; intros; auto with *.
  destruct H0 with x0 as (y,?,?); trivial.
  exists y; trivial.
  revert H3; apply Zin_morph; auto with *.

  destruct H0 as (A'',e',?).
  rewrite e in e'.
  apply eq_Zeq in e'.
  rewrite <- e' in H1.
  destruct H0 with x0 as (y,?,?); trivial.
  exists y; trivial.
  revert H3; apply Zin_morph; auto with *.

 apply lst_fun with (1:=H) (2:=H0).

 destruct Hex as (B,HB).
 assert (Bok := lst_incl _ _ HB).
 destruct Bok as (A',eA,Bok).
 destruct (Z2set_surj x) as (x',ex).
 destruct Bok with x' as (y,?,?).
  apply in_inZ.
  rewrite eA; rewrite <- ex; trivial.

  destruct H1 as (y,Rxy).
  destruct (Z2set_surj y) as (y',ey).
  exists y'; exists x; [|exists y]; auto with *.

  exists (Z2set y).
   apply In_intro; simpl; intros.
   specialize Huniq with (1:=HB) (2:=H5).
   rewrite <- Huniq.
   rewrite H4; trivial.

   destruct H3 as (x'',?,(y',?,?)).
   revert H5; apply H; trivial.
   rewrite ex; rewrite <- H3; auto with *.
Qed.

Definition coll A R := proj1_sig (coll_sig A R).
Lemma coll_ax : forall A (R:set->set->Prop), 
  Proper (eq_set==>eq_set==>iff) R ->
  forall x, x \in A -> (exists y, R x y) ->
  exists2 y, y \in coll A R & R x y.
Proof (fun A R => proj2_sig (coll_sig A R)).

End Collection.

End Skolem.
