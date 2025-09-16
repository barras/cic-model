Require Export basic.
Require Import Sublogic.
Require Export ZFdef.

(** Basic definitions in Zermelo set theory, abstracted over the underlying logic. *)

Module ZermeloSetTheory (L:SublogicTheory) (Z:Zermelo_sig L).
  Import L.
  Import Z.
Hint Resolve TrI : core.
  
Notation morph1 := (Proper (eq_set ==> eq_set)).
Notation morph2 := (Proper (eq_set ==> eq_set ==> eq_set)).

Instance eq_set_equiv: Equivalence eq_set.
Proof.
split; red; intros; rewrite eq_set_ax in *; intros.
 reflexivity.
 symmetry; trivial.
 transitivity (x0 ∈ y); trivial.
Qed.

Lemma eq_set_morph : Proper (eq_set ==> eq_set ==> iff) eq_set.
auto with *.
Qed.

Lemma forall_eq_intro x (P:set->Prop) Q :
  (forall x', x'==x -> P x' <-> Q) ->
  (forall x', x'==x -> P x') <-> Q .
split; intros.
+apply (H x); [reflexivity|].
 apply H0; reflexivity.
+apply (H x'); trivial.
Qed.

Lemma exists_eq_intro x (P:set->Prop) Q :
  (forall x', x==x' -> P x' <-> Q) ->
  (exists2 x', x==x' & P x') <-> Q .
split; intros.
+destruct H0.
 apply (H x0); trivial.
+exists x; [reflexivity|].
 rewrite H; [trivial|reflexivity].
Qed.

Lemma eq_intro : forall x y,
  (forall z, z ∈ x -> z ∈ y) ->
  (forall z, z ∈ y -> z ∈ x) ->
  eq_set x y.
intros.
rewrite eq_set_ax; split; auto.
Qed.

Lemma eq_elim : forall x y y',
  y == y' ->
  x ∈ y ->
  x ∈ y'.
intros.
rewrite eq_set_ax in H.
destruct (H x); auto.
Qed.

Instance in_set_morph : Proper (eq_set ==> eq_set ==> iff) in_set.
apply morph_impl_iff2; auto with *.
do 4 red; intros.
apply in_reg with x; trivial.
apply eq_elim with x0; trivial.
Qed.

Lemma in_set_def a x :
  a ∈ x <-> exists y, y ∈ x /\ y==a.
split; [exists a; split; auto with *|destruct 1 as (y,(?,?))].
rewrite <- H0; trivial.
Qed.

Lemma fa_eq_var_iff y P :
    Proper (eq_set==>iff) P ->
    (forall x, x == y -> P x) <-> P y.
split; intros; auto with *.
rewrite H1; trivial.
Qed.

Lemma ex_eq_var_iff y P :
    Proper (eq_set==>iff) P ->
    (exists x, x == y /\ P x) <-> P y.
split; intros; eauto with *.
*destruct H0 as (x,(?,?)).
 rewrite <- H0; trivial.
*exists y; auto with *.
Qed.


Definition incl_set x y := forall z, z ∈ x -> z ∈ y.

Notation "x ⊆ y" := (incl_set x y).

Instance incl_set_pre : PreOrder incl_set.
split; do 2 red; intros; eauto.
Qed.

Instance incl_set_morph : Proper (eq_set ==> eq_set ==> iff) incl_set.
apply morph_impl_iff2; auto with *.
unfold incl_set; do 4 red; intros.
rewrite <- H0; rewrite <- H in H2; auto.
Qed.

Lemma incl_eq x y : x ⊆ y -> y ⊆ x -> x == y.
intros.
apply eq_intro; auto.
Qed.

Lemma eq_incl x y : x == y -> x ⊆ y.
intro h; rewrite h; reflexivity.
Qed.

Instance Fmono_morph F : Proper (incl_set==>incl_set) F -> morph1 F.
do 2 red; intros.
apply incl_eq; apply H; rewrite H0; reflexivity.
Qed.
Hint Resolve Fmono_morph : core.

(** Extensional equivalences *)

Definition eq_fun dom F G :=
  forall x x', x ∈ dom -> x == x' -> F x == G x'.

Instance eq_fun_sym : forall dom, Symmetric (eq_fun dom).
do 2 red; intros.
rewrite H1 in H0.
symmetry in H1.
symmetry; apply H; auto.
Qed.

Instance eq_fun_trans : forall dom, Transitive (eq_fun dom).
do 2 red; intros.
transitivity (y x'); auto.
apply H0.
 rewrite <- H2; trivial.
 reflexivity.
Qed.

Definition ext_fun dom f := eq_fun dom f f.

Definition ext_fun2 A B f :=
  forall x x' y y', x ∈ A -> x == x' -> y ∈ B x -> y == y' -> f x y == f x' y'.

Lemma eq_fun_ext : forall dom F G, eq_fun dom F G -> ext_fun dom F.
red; intros.
transitivity G; trivial.
symmetry; trivial.
Qed.

Lemma morph_is_ext : forall F X, morph1 F -> ext_fun X F.
red; red; intros.
apply H; trivial.
Qed.
Hint Resolve morph_is_ext : core.

Lemma cst_is_ext : forall X o, ext_fun o (fun _ => X).
do 2 red; reflexivity.
Qed.
Hint Resolve cst_is_ext : core.

Definition eq_pred dom (P Q : set -> Prop) :=
  forall x, x ∈ dom -> (P x <-> Q x).

Instance eq_pred_set : forall dom, Equivalence (eq_pred dom).
firstorder.
Qed.

Definition ext_rel dom (R:set->set->Prop) :=
  forall x x' y y', x ∈ dom -> x == x' -> y == y' -> (R x y <-> R x' y').

Definition eq_index x F y G :=
  (forall a, a ∈ x -> exists2 b, b ∈ y & F a == G b) /\
  (forall b, b ∈ y -> exists2 a, a ∈ x & F a == G b).

Lemma eq_index_sym : forall x F y G, eq_index x F y G -> eq_index y G x F.
destruct 1; split; intros.
 apply H0 in H1; destruct H1.
 symmetry in H2.
 exists x0; trivial.

 apply H in H1; destruct H1.
 symmetry in H2.
 exists x0; trivial.
Qed.

Lemma eq_index_eq : forall x F y G,
  x == y ->
  eq_fun x F G ->
  eq_index x F y G.
red; intros.
split; intros.
 exists a.
  rewrite H in H1; trivial.
  apply H0; auto with *.
 rewrite <- H in H1; trivial.
 exists b; trivial.
 apply H0; auto with *.
Qed.

Definition typ_fun f A B := forall x, x ∈ A -> f x ∈ B.

Instance typ_fun_morph0 : Proper (eq ==> eq_set ==> eq_set ==> iff) typ_fun.
apply morph_impl_iff3; auto with *.
do 6 red; intros.
subst y.
rewrite <- H1; rewrite <- H0 in H3; auto.
Qed.

(** Rephrasing axioms *)

Lemma empty_ext : forall e, (forall x, #¬x ∈ e) -> e == empty.
Proof.
intros.
apply eq_intro; intros.
*Tdestruct (H _ H0).
*apply empty_ax in H0.
 Tdestruct H0.
Qed.

Lemma fa_empty_iff P : (forall x, x ∈ empty -> #P x) <-> True.
split;[trivial|intros].
Tabsurd; apply empty_ax in H0; trivial.
Qed.

Lemma ex_empty_iff P : #(exists x, x ∈ empty /\ P x) <-> #False.
split;[intros|intros; Tabsurd; trivial].
Tdestruct H as (x,(?,_)).
apply empty_ax in H; trivial.
Qed.

Lemma pair_intro1 : forall x y, x ∈ pair x y.
Proof.
intros.
elim (pair_ax x y x); intros; auto.
apply H0; Tleft; reflexivity.
Qed.

Lemma pair_intro2 : forall x y, y ∈ pair x y.
Proof.
intros.
elim (pair_ax x y y); intros; auto.
apply H0; Tright; reflexivity.
Qed.

Hint Resolve pair_intro1 pair_intro2 : core.

Lemma pair_elim : forall x a b, x ∈ pair a b -> #(x == a \/ x == b).
Proof.
intros.
elim (pair_ax a b x); auto.
Qed.

Lemma pair_ext : forall p a b,
  a ∈ p -> b ∈ p -> (forall x, x ∈ p -> #(x == a \/ x == b)) ->
  p == pair a b.
Proof.
intros; apply eq_intro; intros.
*apply H1 in H2.
 Telim H2; intros [x_eq|x_eq];  rewrite x_eq; trivial.
*apply pair_elim in H2.
 Telim H2; intros[x_eq|x_eq]; rewrite x_eq; trivial.
Qed.

Instance pair_morph : morph2 pair.
do 3 red; intros.
apply pair_ext; intros.
 rewrite <- H; apply pair_intro1.
 rewrite <- H0; apply pair_intro2.

 rewrite <- H; rewrite <- H0.
 apply pair_elim in H1; auto.
Qed.

Lemma fa_pair_iff a b P :
    Proper (eq_set==>iff) P ->
    (forall x, x ∈ pair a b -> #P x) <-> #P a /\ #P b.
intros Pm.
split; intros; auto.
destruct H.
rewrite pair_ax in H0; Tdestruct H0; rewrite H0; trivial.
Qed.

Lemma ex_pair_iff a b P :
    Proper (eq_set==>iff) P ->
    #(exists x, x ∈ pair a b /\ #P x) <-> #(P a \/ P b).
intros Pm.
split; intros.
*Tdestruct H as (x,(?,?)).
 apply pair_ax in H.
 Telim H0; intros H0.
 Tdestruct H; rewrite H in H0; auto.
*Tdestruct H; [Texists a|Texists b]; split; auto.
Qed.

Lemma union_intro : forall x y z, x ∈ y -> y ∈ z -> x ∈ union z.
Proof.
intros.
elim (union_ax z x); intros.
apply H2.
Texists y; trivial.
Qed.

Lemma union_elim : forall x z, x ∈ union z -> #exists2 y, x ∈ y & y ∈ z.
Proof.
intros.
elim (union_ax z x); auto.
Qed.

Lemma union_ext :
  forall u z,
  (forall x y, x ∈ y -> y ∈ z -> x ∈ u) ->
  (forall x, x ∈ u -> #exists2 y, x ∈ y & y ∈ z) ->
  u == union z.
Proof.
intros; apply eq_intro; intros.
*apply H0 in H1.
 Telim H1; intros (y,?,?).
apply union_intro with y; trivial.
*apply union_elim in H1.
 Telim H1; intros (y,?,?); eauto.
Qed.

Instance union_morph : morph1 union.
do 2 red; intros.
apply union_ext; intros.
*eapply union_intro;  eauto.
 rewrite H; trivial.
*apply union_elim in H0.
 Telim H0; intros (z,?,?); Texists z; trivial.
 rewrite <- H; trivial.
Qed.

Lemma fa_union_iff a P :
    (forall x, x ∈ union a -> #P x) <->
    (forall y, y ∈ a -> forall x, x ∈ y -> #P x).
split; intros.
*apply H; apply union_ax; eauto.
*apply union_ax in H0; Tdestruct H0; eauto.
Qed.

Lemma ex_union_iff a P :
    #(exists x, x ∈ union a /\ P x) <->
    #(exists y, y ∈ a /\ exists x, x ∈ y /\ P x).
split; intros.
*Tdestruct H as (x,(?,?)).
 apply union_ax in H; Tdestruct H; Tin; eauto.
*Tdestruct H as (y,(?,(x,(?,?)))); Texists x; split;[|trivial].
 apply union_ax; eauto.
Qed.

Instance union_mono : Proper (incl_set ==> incl_set) union.
do 3 red; intros.
apply union_elim in H0.
Tdestruct H0.
apply union_intro with x0; auto.
Qed.

Lemma union_empty_eq : union empty == empty.
Proof.
symmetry  in |- *.
apply union_ext; intros.
*apply empty_ax in H0; Tdestruct H0.
*apply empty_ax in H; Tdestruct H.
Qed.

Lemma power_intro :
  forall x y, (forall z, z ∈ x -> z ∈ y) -> x ∈ power y.
Proof.
intros.
elim (power_ax y x); intros; auto.
Qed.

Lemma power_elim : forall x y z, x ∈ power y -> z ∈ x -> z ∈ y.
Proof.
intros.
elim (power_ax y x); intros; auto.
Qed.

Lemma power_mono : Proper (incl_set ==> incl_set) power.
do 3 red; intros.
apply power_intro; intros.
apply H.
apply power_elim with z; trivial.
Qed.

Lemma power_ext :
  forall p a,
  (forall x, (forall y, y ∈ x -> y ∈ a) -> x ∈ p) ->
  (forall x y, x ∈ p -> y ∈ x -> y ∈ a) ->
  p == power a.
Proof.
intros; apply eq_intro; intros.
 apply power_intro; eauto.
 apply H; intros;  eapply power_elim;  eauto.
Qed.

Instance power_morph : morph1 power.
do 2 red; intros.
apply power_ext; intros.
 apply power_intro; intros.
    rewrite H; auto.
  rewrite <- H.
    eapply power_elim;  eauto.
Qed.

Lemma empty_incl_all a : empty ⊆ a.
red; intros; apply empty_ax in H; Tdestruct H.
Qed.  

Lemma empty_in_power : forall x, empty ∈ power x.
Proof.
intros.
apply power_intro; intros.
apply empty_ax in H; Tdestruct H.
Qed.

Hint Resolve empty_incl_all empty_in_power : core.

Lemma union_in_power :
    forall x X, x ⊆ power X -> union x ∈ power X.
intros.
apply power_intro; intros.
apply union_elim in H0; Tdestruct H0.
apply power_elim with x0; auto.
Qed.


Lemma subset_ax' x P z :
  Proper (eq_set==>iff) P ->
  (z ∈ subset x P <-> z ∈ x /\ #P z).
intros.
rewrite subset_ax.
apply and_iff_morphism; auto with *.
split; intros.
 Tdestruct H0.
 rewrite H0; auto.

 Telim H0; intros.
 Texists z; auto with *.
Qed.

Lemma subset_intro : forall a (P:set->Prop) x,
  x ∈ a -> #P x -> x ∈ subset a P.
Proof.
intros.
Telim H0; intros.
elim (subset_ax a P x); intros.
apply H2; split; trivial.
Texists x; trivial; reflexivity.
Qed.

Lemma subset_elim1 : forall a (P:set->Prop) x, x ∈ subset a P -> x ∈ a.
Proof.
intros.
elim (subset_ax a P x); intros.
elim H0; trivial.
Qed.

Lemma subset_elim2 : forall a (P:set->Prop) x, x ∈ subset a P ->
  #exists2 x', x==x' & P x'.
Proof.
intros.
elim (subset_ax a P x); intros.
elim H0; trivial.
Qed.

Lemma subset_ext :
  forall s a (P:set->Prop),
  (forall x, x ∈ a -> P x -> x ∈ s) ->
  (forall x, x ∈ s -> x ∈ a) ->
  (forall x, x ∈ s -> #exists2 x', x==x' & P x') ->
  s == subset a P.
Proof.
intros; apply eq_intro; intros.
*specialize H0 with (1:=H2).
 specialize H1 with (1:=H2).
 Tdestruct H1.
 rewrite H1.
 apply subset_intro; auto.
 rewrite <- H1; auto.
*apply subset_ax in H2.
 destruct H2.
 Tdestruct H3.
 rewrite H3 in H2|-*; auto.
Qed.

Lemma subset_morph :
  forall x x', x == x' ->
  forall (P P':set->Prop), eq_pred x P P' ->
  subset x P == subset x' P'.
intros.
apply subset_ext; intros.
 rewrite <- H in H1.
 apply subset_intro; auto.
 red in H0.
 rewrite H0; auto.

 rewrite <- H.
 apply subset_elim1 in H1; trivial.

 specialize subset_elim2 with (1:=H1); intro.
 Tdestruct H2.
 apply subset_elim1 in H1.
 Texists x1; trivial.
 red in H0.
 rewrite <- H0; trivial.
 rewrite <- H2; trivial.
Qed.

Lemma fa_subset_iff a P Q :
    Proper (eq_set==>iff) P ->
    (forall x, x ∈ subset a P -> #Q x) <->
    (forall x, x ∈ a -> P x -> #Q x).
intros Pm.
split; intros.
*apply H; apply subset_intro; auto.
*apply subset_ax in H0; destruct H0 as (?,H0); Tdestruct H0 as (x',?,?).
 rewrite <- H0 in H2; auto.
Qed.

Lemma ex_subset_iff a P Q :
    Proper (eq_set==>iff) P ->
    #(exists x, x ∈ subset a P /\ Q x) <->
    #(exists x, x ∈ a /\ (P x /\ Q x)).
intros Pm.
split; intros.
*Tdestruct H as (x,(?,?)).
 apply subset_ax in H; destruct H as (?,H); Tdestruct H as (x',?,?).
 rewrite <- H in H2; Tin; eauto.
*Tdestruct H as (x,(?&?&?)).
 Texists x; split; trivial.
 apply subset_intro; auto.
Qed.

Lemma union_subset_singl : forall x (P:set->Prop) y y',
  y ∈ x ->
  y == y' ->
  #P y' ->
  (forall y y', y ∈ x -> y' ∈ x -> #P y -> #P y' -> y == y') ->
  union (subset x P) == y.
intros.
symmetry; apply union_ext; intros.
 setoid_replace y with y0; trivial.
 apply subset_ax in H4; destruct H4.
 Tdestruct H5.
 rewrite H5.
 rewrite H0.
 apply H2; auto.
 rewrite <- H0; trivial.
 rewrite <- H5; trivial.

 Texists y; trivial.
 rewrite H0.
 apply subset_intro; trivial.
 rewrite <- H0; trivial.
Qed.

(** Conditional set *)

  Definition cond_set P x := subset x (fun _ => P). 

  Instance cond_set_morph : Proper (iff ==> eq_set ==> eq_set) cond_set.
do 3 red; intros.
apply subset_morph; trivial.
red; auto.
Qed.

  Lemma cond_set_ax P x z :
    z ∈ cond_set P x <-> (z ∈ x /\ #P).
unfold cond_set.
rewrite subset_ax.
split; destruct 1; split; trivial.
*Tdestruct H0; auto.
*Telim H0; intros.
 Texists z; auto with *.
Qed.

 (* A more precise morphism lemma *)
 Lemma cond_set_morph2 : forall P Q x y,
    (P <-> Q) ->
    (P -> x == y) ->
    cond_set P x == cond_set Q y.
intros.
apply subset_ext; intros.
 rewrite <- H in H2.
 apply subset_intro; auto.
 rewrite H0; trivial.

 rewrite cond_set_ax in H1; destruct H1.
 Telim H2; intros.
 rewrite <- H0; trivial.

 rewrite cond_set_ax in H1; destruct H1.
 Telim H2; intros.
 Texists x0; auto with *.
 rewrite <- H; trivial.
Qed.

  Lemma cond_set_ok (P:Prop) x : #P -> cond_set P x == x.
intro p.
apply eq_intro; intros.
 apply subset_elim1 in H; trivial.

 apply subset_intro; trivial.
Qed.

  Lemma cond_set_mt P x : (#¬P) -> cond_set P x == empty.
intros.
apply empty_ext; red; intros.
rewrite cond_set_ax in H0.
destruct H0.
Telim H1; auto.
Qed.
  
(** other properties of axioms *)

Lemma pair_commut : forall x y, pair x y == pair y x.
Proof.
intros.
apply pair_ext; intros; auto.
apply pair_elim in H.
Tdestruct H; auto.
Qed.

Lemma pair_inv : forall x y x' y',
  pair x y == pair x' y' -> #((x==x' /\ y==y') \/ (x==y' /\ y==x')).
Proof.
intros.
assert (x ∈ pair x' y').
{rewrite <- H; auto. }
assert (y ∈ pair x' y').
{rewrite <- H; auto. }
apply pair_elim in H0; Tdestruct H0; apply pair_elim in H1; Tdestruct H1; auto.
*Tleft; split; auto.
 assert (y' ∈ pair x y).
 {rewrite H; auto. }
 rewrite H0,<-H1 in H2.
 symmetry  in |- *.
 apply pair_elim in H2; Tdestruct H2; auto.
*Tright; split; trivial.
 assert (x' ∈ pair x y).
 {rewrite H; auto. }
 rewrite H0,<-H1 in H2.
 symmetry.
 apply pair_elim in H2; Tdestruct H2; auto.
Qed.

Lemma discr_mt_pair : forall a b, #¬empty == pair a b.
red; intros.
apply (empty_ax a).
rewrite H.
apply pair_intro1.
Qed.

(** macros *)
Definition singl x := pair x x.

Lemma singl_intro : forall x, x ∈ singl x.
Proof.
unfold singl in |- *; auto.
Qed.

Lemma singl_intro_eq : forall x y, x == y -> x ∈ singl y.
Proof.
intros.
 rewrite H; apply singl_intro.
Qed.

Lemma singl_elim : forall x y, x ∈ singl y -> x == y.
Proof.
unfold singl; intros.
apply pair_elim in H; Tdestruct H; auto.
Qed.

Lemma singl_ext :
  forall y x,
  x ∈ y ->
  (forall z, z ∈ y -> z == x) ->
  y == singl x.
Proof.
intros; apply eq_intro; intros.
 apply singl_intro_eq; auto.
  rewrite (singl_elim _ _ H1); trivial.
Qed.

Instance singl_morph : morph1 singl.
unfold singl; do 2 red; intros.
rewrite H; reflexivity.
Qed.

Lemma union_singl_eq : forall x, union (singl x) == x.
Proof.
intros; apply eq_intro; intros.
*apply union_elim in H.
 Tdestruct H.
 rewrite <- (singl_elim _ _ H0); trivial.
*apply union_intro with (1 := H).
 apply singl_intro.
Qed.

Lemma singl_inj : forall x y, singl x == singl y -> x == y.
Proof.
intros.
rewrite <- (union_singl_eq x); rewrite <- (union_singl_eq y).
apply union_morph;trivial.
Qed.

(** Union of 2 sets *)
Definition union2 x y := union (pair x y).

Infix "∪" := union2.

Lemma union2_intro1: forall x y z, z ∈ x -> z ∈ union2 x y.
Proof.
unfold union2 in |- *; intros.
apply union_intro with x; trivial.
Qed.

Lemma union2_intro2: forall x y z, z ∈ y -> z ∈ union2 x y.
Proof.
unfold union2 in |- *; intros.
apply union_intro with y; trivial.
Qed.

Lemma union2_elim : forall x y z, z ∈ x ∪ y -> #(z ∈ x \/ z ∈ y).
Proof.
unfold union2; intros.
apply union_elim in H.
Tdestruct H.
apply pair_elim in H0; Telim H0; intros [x0_eq|x0_eq]; rewrite <- x0_eq; auto.
Qed.

Lemma union2_ax x y z : z ∈ x ∪ y <-> #(z ∈ x \/ z ∈ y).
split; intros.
 apply union2_elim in H; trivial.

 Tdestruct H; [apply union2_intro1|apply union2_intro2]; auto.
Qed.

Lemma union2_mono : forall A A' B B',
  A ⊆ A' -> B ⊆ B' -> A ∪ B ⊆ A' ∪ B'.
red; intros.
red in H,H0|-.
apply union2_elim in H1; Tdestruct H1.
 apply union2_intro1; auto.
 apply union2_intro2; auto.
Qed.

Instance union2_morph : morph2 union2.
unfold union2; do 3 red; intros.
rewrite H; rewrite H0; reflexivity.
Qed.

Lemma union2_commut : forall x y, x ∪ y == y ∪ x.
Proof.
intros.
unfold union2; rewrite pair_commut; reflexivity.
Qed.

Lemma union2_mt_l x : empty ∪ x == x.
apply eq_set_ax; intros z; rewrite union2_ax. 
split; intros; auto.
Tdestruct H; trivial.
apply empty_ax in H; Tdestruct H.
Qed.

Lemma union2_mt_r x : x ∪ empty == x.
apply eq_set_ax; intros z; rewrite union2_ax. 
split; intros; auto.
Tdestruct H; trivial.
apply empty_ax in H; Tdestruct H.
Qed.


(** subtraction *)
Definition minus2 x y := subset x (fun x' => ~ (x' ∈ y)).

(** Conditional set *)

Definition if_prop P x y :=
  cond_set P x ∪ cond_set (#¬P) y.
  
Instance if_prop_morph : Proper (iff ==> eq_set ==> eq_set ==> eq_set) if_prop.
do 4 red; intros.
unfold if_prop.
apply union2_morph.
 apply cond_set_morph; auto.
 apply cond_set_morph; auto.
 rewrite H; reflexivity.
Qed.

Lemma if_left (P:Prop) x y : #P -> if_prop P x y == x.
unfold if_prop; intros.
apply eq_intro; intros.
*apply union2_elim in H0; Tdestruct H0.
  rewrite cond_set_ax in H0.
  destruct H0; trivial.

  rewrite cond_set_ax in H0; destruct H0.
  Telim H; Telim H1; intros.
  Tdestruct (H H1).
  
*apply union2_intro1; rewrite cond_set_ax; auto.
Qed.

Lemma if_right (P:Prop) x y : #¬P -> if_prop P x y == y.
unfold if_prop; intros.
apply eq_intro; intros.
*apply union2_elim in H0; Tdestruct H0.
  rewrite cond_set_ax in H0; destruct H0.
  Telim H1; intros.
  Tdestruct (H H1).

  rewrite cond_set_ax in H0.
  destruct H0; trivial.
*apply union2_intro2; rewrite cond_set_ax; split; auto.
Qed.


(** Russel's paradox *)

Section Russell.

Variable U : set.
Variable universal : forall x, x ∈ U.

Definition russell_omega := subset U (fun x => #¬ x ∈ x).

Lemma omega_not_in_omega : #¬russell_omega ∈ russell_omega.
Proof.
unfold russell_omega at 2 in |- *.
red; intro.
specialize subset_elim2 with (1:=H); intros.
Tdestruct H0.
rewrite <- H0 in H1.
exact (H1 H).
Qed.

Lemma omega_in_omega : russell_omega ∈ russell_omega.
Proof.
unfold russell_omega at 2 in |- *.
apply subset_intro; trivial.
Tin; exact omega_not_in_omega.
Qed.

Lemma no_universal_set : #False.
exact (omega_not_in_omega omega_in_omega).
Qed.

End Russell.

(** intersection *)

Definition inter x := subset (union x) (fun y => forall z, z ∈ x -> y ∈ z).

Lemma inter_empty_eq : inter empty == empty.
Proof.
unfold inter in |- *.
apply empty_ext; red; intros.
specialize subset_elim1 with (1 := H).
 rewrite union_empty_eq.
apply empty_ax.
Qed.

Lemma inter_intro :
  forall x a,
  (forall y, y ∈ a -> x ∈ y) ->
  #(exists w, w ∈ a) -> (* non empty intersection *)
  x ∈ inter a.
Proof.
unfold inter in |- *; intros.
apply subset_intro; auto.
Tdestruct H0 as (w,?).
apply union_intro with w; auto.
Qed.

Lemma inter_elim : forall x a y, x ∈ inter a -> y ∈ a -> x ∈ y.
Proof.
unfold inter in |- *; intros.
apply subset_elim2 in H.
Tdestruct H.
rewrite H; auto.
Qed.

Lemma inter_non_empty :
  forall x y, y ∈ inter x -> #exists2 w, w ∈ x & y ∈ w.
intros.
apply subset_elim1 in H.
rewrite union_ax in H; Tdestruct H; eauto.
Qed.

Lemma inter_ax a z :
  z ∈ inter a <-> (#exists w, w ∈ a) /\ (forall y, y ∈ a -> z ∈ y).
split; intros.
*split.
 +apply inter_non_empty in H; Tdestruct H as (w,?,_); eauto.
 +intros.
  apply inter_elim with (1:=H); trivial.
*destruct H as (wit,inall).
 apply inter_intro; trivial.
Qed.


Lemma inter_ext :
  forall i a,
  (forall y, y ∈ a -> i ⊆ y) ->
  (forall x, (forall y, y ∈ a -> x ∈ y) -> x ∈ i) ->
  #(exists w, w ∈ a) ->
  i == inter a.
Proof.
unfold incl_set in |- *.
intros; apply eq_intro; intros.
 apply inter_intro; auto.

 apply H0; intros.
 apply inter_elim with (1 := H2); trivial.
Qed.

Instance inter_morph : morph1 inter.
unfold inter in |- *; do 2 red; intros.
apply subset_morph; intros;  eauto.
 apply union_morph; trivial.

 red in |- *; intros.
 split; intros.
 rewrite <- H in H2; auto.
 rewrite H in H2; auto.
Qed.

(** Binary intersection *)

Definition inter2 x y := inter (pair x y).

Infix "∩" := inter2.

Instance inter2_morph: morph2 inter2.
do 3 red; intros; apply inter_morph; apply pair_morph; trivial.
Qed.

Lemma inter2_def : forall x y z,
  z ∈ x ∩ y <-> z ∈ x /\ z ∈ y.
unfold inter2.
split; intros.
 split; apply inter_elim with (1:=H);
   [apply pair_intro1|apply pair_intro2].

 destruct H.
 apply inter_intro; [intros|Texists x; apply pair_intro1].
 apply pair_elim in H1; Tdestruct H1; rewrite H1; trivial.
Qed.

Instance inter2_mono : Proper (incl_set==>incl_set==>incl_set) inter2.
do 4 red; intros.
apply inter2_def in H1; destruct H1.
apply inter2_def; split; auto.
Qed.

Lemma inter2_incl1 : forall x y, x ∩ y ⊆ x.
red; intros.
rewrite inter2_def in H; destruct H; trivial.
Qed.

Lemma inter2_incl2 : forall x y, x ∩ y ⊆ y.
red; intros.
rewrite inter2_def in H; destruct H; trivial.
Qed.

Lemma inter2_incl a x y : a ⊆ x -> a ⊆ y -> a ⊆ x ∩ y.
red; intros; rewrite inter2_def; split; auto.
Qed.

Lemma incl_inter2 x y: x ⊆ y -> x ∩ y == x.
intros; apply eq_intro; intro z; rewrite inter2_def; auto.
destruct 1; trivial.
Qed.

Lemma inter2_comm x y :
  x ∩ y == y ∩ x.
apply eq_intro; intro z; do 2 rewrite inter2_def; destruct 1; auto.
Qed.

End ZermeloSetTheory.
