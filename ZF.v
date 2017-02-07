
Require Export basic.
Require Import Sublogic.
Require Export ZFdef.

(** We assume the existence of a model of IZF: *)
Require ZFskolEm.
Module IZF : IZF_R_sig CoqSublogicThms := ZFskolEm.IZF_R.
(*Import IZF.*)
Include IZF.

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
Hint Resolve Fmono_morph.

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
Hint Resolve morph_is_ext.

Lemma cst_is_ext : forall X o, ext_fun o (fun _ => X).
do 2 red; reflexivity.
Qed.
Hint Resolve cst_is_ext.

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

Lemma empty_ext : forall e, (forall x, ~x ∈ e) -> e == empty.
Proof.
intros.
apply eq_intro; intros.
 elim H with (1 := H0).
 elim empty_ax with (1 := H0).
Qed.

Lemma pair_intro1 : forall x y, x ∈ pair x y.
Proof.
intros.
elim (pair_ax x y x); intros; auto.
apply H0; left; reflexivity.
Qed.

Lemma pair_intro2 : forall x y, y ∈ pair x y.
Proof.
intros.
elim (pair_ax x y y); intros; auto.
apply H0; right; reflexivity.
Qed.

Hint Resolve pair_intro1 pair_intro2.

Lemma pair_elim : forall x a b, x ∈ pair a b -> x == a \/ x == b.
Proof.
intros.
elim (pair_ax a b x); auto.
Qed.

Lemma pair_ext : forall p a b,
  a ∈ p -> b ∈ p -> (forall x, x ∈ p -> x == a \/ x == b) ->
  p == pair a b.
Proof.
intros; apply eq_intro; intros.
 elim H1 with (1 := H2); intro x_eq;  rewrite x_eq; trivial.
 elim pair_elim with (1 := H2); intro x_eq;  rewrite x_eq; trivial.
Qed.

Instance pair_morph : morph2 pair.
do 3 red; intros.
apply pair_ext; intros.
 rewrite <- H; apply pair_intro1.
 rewrite <- H0; apply pair_intro2.

 rewrite <- H; rewrite <- H0.
 apply pair_elim in H1; auto.
Qed.

Lemma union_intro : forall x y z, x ∈ y -> y ∈ z -> x ∈ union z.
Proof.
intros.
elim (union_ax z x); intros.
apply H2.
exists y; trivial.
Qed.

Lemma union_elim : forall x z, x ∈ union z -> exists2 y, x ∈ y & y ∈ z.
Proof.
intros.
elim (union_ax z x); auto.
Qed.

Lemma union_ext :
  forall u z,
  (forall x y, x ∈ y -> y ∈ z -> x ∈ u) ->
  (forall x, x ∈ u -> exists2 y, x ∈ y & y ∈ z) ->
  u == union z.
Proof.
intros; apply eq_intro; intros.
 elim H0 with (1 := H1); intros.
   apply union_intro with x; trivial.
 elim union_elim with (1 := H1); intros; eauto.
Qed.

Instance union_morph : morph1 union.
do 2 red; intros.
apply union_ext; intros.
  eapply union_intro;  eauto.
  rewrite H; trivial.
 elim union_elim with (1 := H0); intros.
 exists x1; trivial.
 rewrite <- H; trivial.
Qed.

Instance union_mono : Proper (incl_set ==> incl_set) union.
do 3 red; intros.
apply union_elim in H0.
destruct H0.
apply union_intro with x0; auto.
Qed.

Lemma union_empty_eq : union empty == empty.
Proof.
symmetry  in |- *.
apply union_ext; intros.
 elim empty_ax with (1 := H0).
 elim empty_ax with (1 := H).
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

Lemma empty_in_power : forall x, empty ∈ power x.
Proof.
intros.
apply power_intro; intros.
elim empty_ax with (1:=H).
Qed.

Lemma union_in_power :
    forall x X, x ⊆ power X -> union x ∈ power X.
intros.
apply power_intro; intros.
elim union_elim with (1:=H0); clear H0; intros.
apply power_elim with x0; auto.
Qed.


Lemma subset_intro : forall a (P:set->Prop) x,
  x ∈ a -> P x -> x ∈ subset a P.
Proof.
intros.
elim (subset_ax a P x); intros.
apply H2; split; trivial.
exists x; trivial; reflexivity.
Qed.

Lemma subset_elim1 : forall a (P:set->Prop) x, x ∈ subset a P -> x ∈ a.
Proof.
intros.
elim (subset_ax a P x); intros.
elim H0; trivial.
Qed.

Lemma subset_elim2 : forall a (P:set->Prop) x, x ∈ subset a P ->
  exists2 x', x==x' & P x'.
Proof.
intros.
elim (subset_ax a P x); intros.
elim H0; trivial.
Qed.

Lemma subset_ext :
  forall s a (P:set->Prop),
  (forall x, x ∈ a -> P x -> x ∈ s) ->
  (forall x, x ∈ s -> x ∈ a) ->
  (forall x, x ∈ s -> exists2 x', x==x' & P x') ->
  s == subset a P.
Proof.
intros; apply eq_intro; intros.
 elim H1 with (1:=H2); intros.
 rewrite H3.
 apply subset_intro; auto.
 rewrite <- H3; auto.
 elim subset_elim2 with (1:=H2); intros.
 rewrite H3.
 apply H; trivial.
 rewrite <- H3.
 apply subset_elim1 with P; auto.
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
 rewrite H0; trivial.

 rewrite <- H.
 apply subset_elim1 in H1; trivial.

 specialize subset_elim2 with (1:=H1); intro.
 destruct H2.
 apply subset_elim1 in H1.
 exists x1; trivial.
 red in H0.
 rewrite <- H0; trivial.
 rewrite <- H2; trivial.
Qed.

Lemma union_subset_singl : forall x (P:set->Prop) y y',
  y ∈ x ->
  y == y' ->
  P y' ->
  (forall y y', y ∈ x -> y' ∈ x -> P y -> P y' -> y == y') ->
  union (subset x P) == y.
intros.
symmetry; apply union_ext; intros.
 setoid_replace y with y0; trivial.
 elim subset_elim2 with (1:=H4); intros.
 rewrite H5.
 rewrite H0.
 apply H2; trivial.
 rewrite <- H0; trivial.
 rewrite <- H5.
 apply subset_elim1 with (1:=H4).

 exists y; trivial.
 rewrite H0.
 apply subset_intro; trivial.
 rewrite <- H0; trivial.
Qed.

(*Parameter replf : set -> (set->set) -> set.*)
Definition replf a (F:set->set) :=
  repl a (fun x y => y == F x).


Instance replf_mono_raw :
  Proper (incl_set ==> (eq_set ==> eq_set) ==> incl_set) replf.
unfold replf.
do 4 red; intros.
assert (xm : morph1 x0).
 do 2 red; intros.
 transitivity (y0 y1); auto.
 symmetry; apply H0; reflexivity.
assert (ym : morph1 y0).
 do 2 red; intros.
 transitivity (x0 x1); auto.
 symmetry; apply H0; reflexivity.
rewrite repl_ax in H1.
 rewrite repl_ax.
  destruct H1.
  exists x1; auto.
  rewrite H2; apply H0; reflexivity.

  intros.
  rewrite <- H4; rewrite H5; auto.

  intros.
  rewrite H3; rewrite H4; reflexivity.

 intros.
 rewrite <- H4; rewrite H5; auto.

 intros.
 rewrite H3; rewrite H4; reflexivity.
Qed.

Instance replf_morph_raw :
  Proper (eq_set ==> (eq_set ==> eq_set) ==> eq_set) replf.
do 3 red; intros.
apply eq_intro.
 apply replf_mono_raw; auto.
 rewrite H; reflexivity.

 symmetry in H0.
 apply replf_mono_raw; auto.
 rewrite H; reflexivity.
Qed.

Lemma replf_ax : forall a F z,
  ext_fun a F ->
  (z ∈ replf a F <-> exists2 x, x ∈ a & z == F x).
unfold replf; intros.
rewrite repl_ax; intros.
 split; intros.
  destruct H0.
  exists x; trivial.

  destruct H0.
  exists x; trivial.

 rewrite <- H2; rewrite H3; auto.

 rewrite H2; trivial.
Qed.

Lemma replf_intro : forall a F y x,
  ext_fun a F -> x ∈ a -> y == F x -> y ∈ replf a F.
Proof.
intros a F y x Fext H1 H2.
rewrite replf_ax; trivial.
exists x; trivial.
Qed.

Lemma replf_elim : forall a F y,
  ext_fun a F -> y ∈ replf a F -> exists2 x, x ∈ a & y == F x.
Proof.
intros a F y Fext H1.
rewrite replf_ax in H1; trivial.
Qed.

Lemma replf_ext : forall p a F,
  ext_fun a F ->
  (forall x, x ∈ a -> F x ∈ p) ->
  (forall y, y ∈ p -> exists2 x, x ∈ a & y == F x) ->
  p == replf a F.
intros.
apply eq_intro; intros.
 apply H1 in H2; destruct H2.
 apply replf_intro with x; auto.

 apply replf_elim in H2; trivial; destruct H2.
 rewrite H3; auto.
Qed.

Lemma replf_mono2 : forall x y F,
  ext_fun y F ->
  x ⊆ y ->
  replf x F ⊆ replf y F.
red; intros.
assert (ext_fun x F).
 do 2 red; auto.
apply replf_elim in H1; trivial.
destruct H1.
apply replf_intro with x0; auto.
Qed.

Lemma replf_morph_gen : forall x1 x2 F1 F2, 
  ext_fun x1 F1 ->
  ext_fun x2 F2 ->
  eq_index x1 F1 x2 F2 ->
  replf x1 F1 == replf x2 F2.
Proof.
destruct 3.
apply replf_ext; intros; trivial.
 apply H2 in H3; destruct H3.
 apply replf_intro with x0; trivial.
 symmetry; trivial.

 apply replf_elim in H3; trivial; destruct H3.
 apply H1 in H3; destruct H3.
 rewrite H5 in H4.
 exists x0; auto.
Qed.

Lemma replf_morph : forall x1 x2 F1 F2, 
  x1 == x2 ->
  eq_fun x1 F1 F2 ->
  replf x1 F1 == replf x2 F2.
intros.
apply replf_morph_gen; intros.
 apply eq_fun_ext in H0; trivial.
 
 do 2 red; intros.
 rewrite <- H in H1.
 transitivity (F1 x); auto.
 symmetry; apply H0; trivial; reflexivity.

 apply eq_index_eq; trivial.
Qed.

Lemma replf_empty : forall F, replf empty F == empty.
Proof.
intros.
apply empty_ext.
red; intros.
apply replf_elim in H.
 destruct H.
 elim empty_ax with (1:=H).

 do 2 red; intros.
 elim empty_ax with (1:=H0).
Qed.

Lemma compose_replf : forall A F G,
  ext_fun A F ->
  ext_fun (replf A F) G ->
  replf (replf A F) G == replf A (fun x => G (F x)).
intros.
assert (eGF : ext_fun A (fun x => G (F x))).
 red; red; intros.
 apply H0; auto.
 rewrite replf_ax; trivial.
 exists x; auto with *.
apply eq_intro; intros.
 rewrite replf_ax in H1; trivial.
 destruct H1.
 rewrite replf_ax in H1; trivial.
 destruct H1.
 rewrite replf_ax; trivial.
 exists x0; trivial.
 rewrite H2; apply H0; trivial.
 rewrite replf_ax; trivial.
 exists x0; trivial.

 rewrite replf_ax in H1; trivial.
 destruct H1.
 rewrite replf_ax; trivial.
 exists (F x); trivial.
 rewrite replf_ax; trivial.
 exists x; auto with *.
Qed.

(** Conditional set *)

  Definition cond_set P x := subset x (fun _ => P). 

  Instance cond_set_morph : Proper (iff ==> eq_set ==> eq_set) cond_set.
do 3 red; intros.
apply subset_morph; trivial.
red; auto.
Qed.

  Lemma cond_set_ax P x z :
    z ∈ cond_set P x <-> (z ∈ x /\ P).
unfold cond_set.
rewrite subset_ax.
split; destruct 1; split; trivial.
 destruct H0; trivial.
 exists z; auto with *.
Qed.

 (* A more precise morphism lemma *)
 Lemma cond_set_morph2 : forall P Q x y,
    (P <-> Q) ->
    (P -> x == y) ->
    cond_set P x == cond_set Q y.
intros.
apply subset_ext; intros.
 rewrite <- H in H2.
 apply subset_intro; trivial.
 rewrite H0; trivial.

 rewrite cond_set_ax in H1; destruct H1.
 rewrite <- H0; trivial.

 rewrite cond_set_ax in H1; destruct H1.
 exists x0; auto with *.
 rewrite <- H; trivial.
Qed.

  Lemma cond_set_ok (P:Prop) x : P -> cond_set P x == x.
intro p.
apply eq_intro; intros.
 apply subset_elim1 in H; trivial.

 apply subset_intro; trivial.
Qed.

  Lemma cond_set_mt P x : ~P -> cond_set P x == empty.
intros.
apply empty_ext; red; intros.
rewrite cond_set_ax in H0.
destruct H0; auto.
Qed.
  
(** other properties of axioms *)

Lemma pair_commut : forall x y, pair x y == pair y x.
Proof.
intros.
apply pair_ext; intros; auto.
elim pair_elim with (1:=H); auto.
Qed.

Lemma pair_inv : forall x y x' y',
  pair x y == pair x' y' -> (x==x' /\ y==y') \/ (x==y' /\ y==x').
Proof.
intros.
assert (x ∈ pair x' y').
 rewrite <- H; auto.
 assert (y ∈ pair x' y').
  rewrite <- H; auto.
  elim pair_elim with (1 := H0); intros; elim pair_elim with (1 := H1);
   intros; auto.
   left; split; trivial.
     assert (y' ∈ pair x y).
    rewrite H; auto.
     rewrite H2 in H4.
       rewrite H3 in H4.
       rewrite H3.
      symmetry  in |- *.
      elim pair_elim with (1:=H4); trivial.
   right; split; trivial.
     assert (x' ∈ pair x y).
    rewrite H; auto.
     rewrite H2 in H4.
       rewrite H3 in H4.
       rewrite H3.
      symmetry  in |- *.
      elim pair_elim with (1:=H4); trivial.
Qed.

Lemma discr_mt_pair : forall a b, ~ empty == pair a b.
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
elim pair_elim with (1:=H); auto.
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
 elim union_elim with (1 := H); intros.
    rewrite <- (singl_elim _ _ H1); trivial.
 apply union_intro with (1 := H).
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

Lemma union2_elim : forall x y z, z ∈ x ∪ y -> z ∈ x \/ z ∈ y.
Proof.
unfold union2; intros.
elim union_elim with (1:=H); intros.
elim pair_elim with (1:=H1); intro x0_eq; rewrite <- x0_eq; auto.
Qed.

Lemma union2_ax x y z : z ∈ x ∪ y <-> z ∈ x \/ z ∈ y.
split; intros.
 apply union2_elim in H; trivial.

 destruct H; [apply union2_intro1|apply union2_intro2]; auto.
Qed.

Lemma union2_mono : forall A A' B B',
  A ⊆ A' -> B ⊆ B' -> A ∪ B ⊆ A' ∪ B'.
red; intros.
red in H,H0|-.
elim union2_elim with (1:=H1); intros.
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
split; auto.
destruct 1; trivial.
elim empty_ax with (1:=H).
Qed.

Lemma union2_mt_r x : x ∪ empty == x.
apply eq_set_ax; intros z; rewrite union2_ax. 
split; auto.
destruct 1; trivial.
elim empty_ax with (1:=H).
Qed.


(** subtraction *)
Definition minus2 x y := subset x (fun x' => ~ (x' ∈ y)).


(** Upper bound of a family of sets *)

Definition sup x F := union (replf x F).

Lemma sup_ax : forall x F z,
  ext_fun x F ->
  (z ∈ sup x F <-> exists2 y, y ∈ x & z ∈ F y).
intros.
unfold sup.
rewrite union_ax.
split; destruct 1; intros.
 apply replf_elim in H1; auto; destruct H1.
 rewrite H2 in H0; clear H2.
 exists x1; trivial.

 exists (F x0); trivial.
 apply replf_intro with x0; trivial.
 reflexivity.
Qed.

Lemma sup_ext : forall y a F,
  ext_fun a F ->
  (forall x, x ∈ a -> F x ⊆ y) ->
  (forall z, z ∈ y -> exists2 x, x ∈ a & z ∈ F x) ->
  y == sup a F.
intros.
apply eq_intro; intros.
 rewrite sup_ax; auto.

 rewrite sup_ax in H2; trivial; destruct H2.
 apply H0 in H3; trivial.
Qed.

Lemma sup_morph_gen : forall a F b G,
  ext_fun a F ->
  ext_fun b G ->
  eq_index a F b G ->
  sup a F == sup b G.
unfold sup; intros.
apply union_morph; apply replf_morph_gen; trivial.
Qed.

Lemma sup_morph : forall a F b G,
  a == b ->
  eq_fun a F G ->
  sup a F == sup b G.
intros.
apply sup_morph_gen; intros.
 apply eq_fun_ext in H0; trivial.

 do 2 red; intros.
 rewrite <- H in H1.
 transitivity (F x); auto.
 symmetry; apply H0; trivial; reflexivity.

 apply eq_index_eq; trivial.
Qed.

Lemma sup_incl : forall a F x,
  ext_fun a F -> x ∈ a -> F x ⊆ sup a F.
intros.
red; intros.
rewrite sup_ax; trivial.
exists x; trivial.
Qed.
Hint Resolve sup_incl.


Lemma replf_is_sup A F :
  ext_fun A F ->
  replf A F == sup A (fun x => singl (F x)).
intros.
assert (fm : ext_fun A (fun x => singl (F x))).
 do 2 red; intros; apply singl_morph; apply H; trivial.
apply eq_intro; intros.
 rewrite sup_ax; trivial.
 rewrite replf_ax in H0; trivial.
 revert H0; apply ex2_morph; red; intros; auto with *.
 split; intros.
  apply singl_elim in H0; trivial.
  rewrite H0; apply singl_intro.

 rewrite replf_ax; trivial.
 rewrite sup_ax in H0; trivial.
 revert H0; apply ex2_morph; red; intros; auto with *.
 split; intros.
  rewrite H0; apply singl_intro.
  apply singl_elim in H0; trivial.
Qed.

Lemma union_is_sup a :
  union a == sup a (fun x => x).
apply eq_intro; intros.
 rewrite sup_ax;[|do 2 red; auto].
 apply union_elim in H; destruct H.
 eauto.

 rewrite sup_ax in H;[|do 2 red; auto].
 destruct H; eauto using union_intro.
Qed.

(** Conditional set *)

Definition if_prop P x y :=
  cond_set P x ∪ cond_set (~P) y.

Instance if_prop_morph : Proper (iff ==> eq_set ==> eq_set ==> eq_set) if_prop.
do 4 red; intros.
unfold if_prop.
apply union2_morph.
 apply cond_set_morph; auto.
 apply cond_set_morph; auto.
 rewrite H; reflexivity.
Qed.

Lemma if_left (P:Prop) x y : P -> if_prop P x y == x.
unfold if_prop; intros.
apply eq_intro; intros.
 apply union2_elim in H0; destruct H0.
  rewrite cond_set_ax in H0.
  destruct H0; trivial.

  rewrite cond_set_ax in H0; destruct H0; contradiction.

 apply union2_intro1; rewrite cond_set_ax; auto.
Qed.

Lemma if_right (P:Prop) x y : ~P -> if_prop P x y == y.
unfold if_prop; intros.
apply eq_intro; intros.
 apply union2_elim in H0; destruct H0.
  rewrite cond_set_ax in H0; destruct H0; contradiction.

  rewrite cond_set_ax in H0.
  destruct H0; trivial.

 apply union2_intro2; rewrite cond_set_ax; auto.
Qed.


(** Russel's paradox *)

Section Russell.

Variable U : set.
Variable universal : forall x, x ∈ U.

Definition russell_omega := subset U (fun x => ~ x ∈ x).

Lemma omega_not_in_omega : ~ russell_omega ∈ russell_omega.
Proof.
unfold russell_omega at 2 in |- *.
red in |- *; intro.
elim subset_elim2 with (1 := H); intros.
rewrite <- H0 in H1.
exact (H1 H).
Qed.

Lemma omega_in_omega : russell_omega ∈ russell_omega.
Proof.
unfold russell_omega at 2 in |- *.
apply subset_intro; trivial.
exact omega_not_in_omega.
Qed.

Lemma no_universal_set : False.
Proof (omega_not_in_omega omega_in_omega).

End Russell.

(** intersection *)

Definition inter x := subset (union x) (fun y => forall z, z ∈ x -> y ∈ z).

Lemma inter_empty_eq : inter empty == empty.
Proof.
unfold inter in |- *.
apply empty_ext; red in |- *; intros.
specialize subset_elim1 with (1 := H).
 rewrite union_empty_eq.
apply empty_ax.
Qed.

Lemma inter_intro :
  forall x a,
  (forall y, y ∈ a -> x ∈ y) ->
  (exists w, w ∈ a) -> (* non empty intersection *)
  x ∈ inter a.
Proof.
unfold inter in |- *; intros.
apply subset_intro; auto.
destruct H0 as (w,?).
apply union_intro with w; auto.
Qed.

Lemma inter_elim : forall x a y, x ∈ inter a -> y ∈ a -> x ∈ y.
Proof.
unfold inter in |- *; intros.
elim subset_elim2 with (1 := H); intros.
rewrite H1; auto.
Qed.

Lemma inter_non_empty :
  forall x y, y ∈ inter x -> exists2 w, w ∈ x & y ∈ w.
intros.
apply subset_elim1 in H.
rewrite union_ax in H; destruct H; eauto.
Qed.

Lemma inter_wit : forall X F, morph1 F -> 
 forall x, x ∈ inter (replf X F) ->
 exists y, y ∈ X.
intros.
destruct inter_non_empty with (1:=H0).
rewrite replf_ax in H1.
2:red;red;intros; apply H; trivial.
destruct H1; eauto.
Qed.

Lemma inter_ext :
  forall i a,
  (forall y, y ∈ a -> i ⊆ y) ->
  (forall x, (forall y, y ∈ a -> x ∈ y) -> x ∈ i) ->
  (exists w, w ∈ a) ->
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
 apply inter_intro; [intros|exists x; apply pair_intro1].
 apply pair_elim in H1; destruct H1; rewrite H1; trivial.
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
