
Require Export basic.
Require Export ZFdef.

(* We assume the existence of a model of IZF: *)
Require Ens ZFskol.
Module IZF : IZF_sig := ZFskol.Skolem Ens.IZF.
Import IZF.

Notation morph1 := (Proper (eq_set ==> eq_set)).
Notation morph2 := (Proper (eq_set ==> eq_set ==> eq_set)).

Instance eq_set_equiv: Equivalence eq_set.
Proof.
split; red; intros; rewrite eq_set_ax in *; intros.
 reflexivity.
 symmetry; trivial.
 transitivity (x0 \in y); trivial.
Qed.

Lemma eq_intro : forall x y,
  (forall z, z \in x -> z \in y) ->
  (forall z, z \in y -> z \in x) ->
  eq_set x y.
intros.
rewrite eq_set_ax; split; auto.
Qed.

Lemma eq_elim : forall x y y',
  y == y' ->
  x \in y ->
  x \in y'.
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

Definition incl_set x y := forall z, z \in x -> z \in y.

Notation "x \incl y" := (incl_set x y) (at level 70).

Instance incl_set_pre : PreOrder incl_set.
split; do 2 red; intros; eauto.
Qed.


Instance incl_set_morph : Proper (eq_set ==> eq_set ==> iff) incl_set.
apply morph_impl_iff2; auto with *.
unfold incl_set; do 4 red; intros.
rewrite <- H0; rewrite <- H in H2; auto.
Qed.

Lemma incl_eq : forall x y, x \incl y -> y \incl x -> x == y.
intros.
apply eq_intro; auto.
Qed.


(* Extentional equivalences *)

Definition eq_fun dom F G :=
  forall x x', x \in dom -> x == x' -> F x == G x'.

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

Lemma eq_fun_ext : forall dom F G, eq_fun dom F G -> ext_fun dom F.
red; intros.
transitivity G; trivial.
symmetry; trivial.
Qed.

Definition eq_pred dom (P Q : set -> Prop) :=
  forall x, x \in dom -> (P x <-> Q x).

Instance eq_pred_set : forall dom, Equivalence (eq_pred dom).
firstorder.
Qed.

Definition ext_rel dom (R:set->set->Prop) :=
  forall x x' y y', x \in dom -> x == x' -> y == y' -> (R x y <-> R x' y').

Definition eq_index x F y G :=
  (forall a, a \in x -> exists2 b, b \in y & F a == G b) /\
  (forall b, b \in y -> exists2 a, a \in x & F a == G b).

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


(* Derived axioms *)

Definition subset a (P:set->Prop) := repl a (fun x y => x==y /\ P x).

Lemma subset_ax: forall a (P:set->Prop),
    forall x, x \in subset a P <-> (x \in a /\ exists2 x', x==x' & P x').
intros.
unfold subset.
rewrite repl_ax.
 split; intros.
  destruct H.
  destruct H0.
  destruct H1.
  rewrite <- H1 in H0.
  split.
   rewrite H0; trivial.

   exists x0; trivial.

  destruct H.
  destruct H0.
  exists x0.
   rewrite <- H0; trivial.

   exists x0; auto with *.

 intros.
 destruct H0.
 destruct H1.
 rewrite <- H0; rewrite H2; trivial.
Qed. 

(* rephrasing axioms *)

Lemma empty_ext : forall e, (forall x, ~x \in e) -> e == empty.
Proof.
intros.
apply eq_intro; intros.
 elim H with (1 := H0).
 elim empty_ax with (1 := H0).
Qed.

Lemma pair_intro1 : forall x y, x \in pair x y.
Proof.
intros.
elim (pair_ax x y x); intros; auto.
apply H0; left; reflexivity.
Qed.

Lemma pair_intro2 : forall x y, y \in pair x y.
Proof.
intros.
elim (pair_ax x y y); intros; auto.
apply H0; right; reflexivity.
Qed.

Hint Resolve pair_intro1 pair_intro2.

Lemma pair_elim : forall x a b, x \in pair a b -> x == a \/ x == b.
Proof.
intros.
elim (pair_ax a b x); auto.
Qed.

Lemma pair_ext : forall p a b,
  a \in p -> b \in p -> (forall x, x \in p -> x == a \/ x == b) ->
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

Lemma union_intro : forall x y z, x \in y -> y \in z -> x \in union z.
Proof.
intros.
elim (union_ax z x); intros.
apply H2.
exists y; trivial.
Qed.

Lemma union_elim : forall x z, x \in union z -> exists2 y, x \in y & y \in z.
Proof.
intros.
elim (union_ax z x); auto.
Qed.

Lemma union_ext :
  forall u z,
  (forall x y, x \in y -> y \in z -> x \in u) ->
  (forall x, x \in u -> exists2 y, x \in y & y \in z) ->
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
  forall x y, (forall z, z \in x -> z \in y) -> x \in power y.
Proof.
intros.
elim (power_ax y x); intros; auto.
Qed.

Lemma power_elim : forall x y z, x \in power y -> z \in x -> z \in y.
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
  (forall x, (forall y, y \in x -> y \in a) -> x \in p) ->
  (forall x y, x \in p -> y \in x -> y \in a) ->
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

Lemma empty_in_power : forall x, empty \in power x.
Proof.
intros.
apply power_intro; intros.
elim empty_ax with (1:=H).
Qed.

Lemma union_in_power :
    forall x X, x \incl power X -> union x \in power X.
intros.
apply power_intro; intros.
elim union_elim with (1:=H0); clear H0; intros.
apply power_elim with x0; auto.
Qed.


Lemma subset_intro : forall a (P:set->Prop) x,
  x \in a -> P x -> x \in subset a P.
Proof.
intros.
elim (subset_ax a P x); intros.
apply H2; split; trivial.
exists x; trivial; reflexivity.
Qed.

Lemma subset_elim1 : forall a (P:set->Prop) x, x \in subset a P -> x \in a.
Proof.
intros.
elim (subset_ax a P x); intros.
elim H0; trivial.
Qed.

Lemma subset_elim2 : forall a (P:set->Prop) x, x \in subset a P ->
  exists2 x', x==x' & P x'.
Proof.
intros.
elim (subset_ax a P x); intros.
elim H0; trivial.
Qed.

Lemma subset_ext :
  forall s a (P:set->Prop),
  (forall x, x \in a -> P x -> x \in s) ->
  (forall x, x \in s -> x \in a) ->
  (forall x, x \in s -> exists2 x', x==x' & P x') ->
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
  y \in x ->
  y == y' ->
  P y' ->
  (forall y y', y \in x -> y' \in x -> P y -> P y' -> y == y') ->
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

Definition replf a (F:set->set) :=
  repl a (fun x y => y == F x).

Instance replf_mono_raw :
  Proper (incl_set ==> (eq_set ==> eq_set) ==> incl_set) replf.
unfold replf.
do 4 red; intros.
rewrite repl_ax in H1.
 rewrite repl_ax.
  destruct H1.
  destruct H2.
  exists x1; auto.
  exists x2; trivial.
  rewrite H3; apply H0; reflexivity.

  intros.
  rewrite H3; rewrite H4; transitivity (x0 x1).
   symmetry; apply H0; reflexivity.

   apply H0; trivial.

 intros.
 rewrite H3; rewrite H4; transitivity (y0 x'); auto.
 symmetry; auto with *.
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
  (z \in replf a F <-> exists2 x, x \in a & z == F x).
unfold replf; intros.
rewrite repl_ax; intros.
 split; intros.
  destruct H0.
  destruct H1.
  exists x; trivial.
  rewrite H1; trivial.

  destruct H0.
  exists x; trivial.
  exists z; trivial; reflexivity.

 rewrite H1; rewrite H2; auto.
Qed.

Lemma replf_intro : forall a F y x,
  ext_fun a F -> x \in a -> y == F x -> y \in replf a F.
Proof.
intros a F y x Fext H1 H2.
rewrite replf_ax; trivial.
exists x; trivial.
Qed.

Lemma replf_elim : forall a F y,
  ext_fun a F -> y \in replf a F -> exists2 x, x \in a & y == F x.
Proof.
intros a F y Fext H1.
rewrite replf_ax in H1; trivial.
Qed.

Lemma replf_ext : forall p a F,
  ext_fun a F ->
  (forall x, x \in a -> F x \in p) ->
  (forall y, y \in p -> exists2 x, x \in a & y == F x) ->
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
  x \incl y ->
  replf x F \incl replf y F.
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

(* other properties of axioms *)

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
assert (x \in pair x' y').
 rewrite <- H; auto.
 assert (y \in pair x' y').
  rewrite <- H; auto.
  elim pair_elim with (1 := H0); intros; elim pair_elim with (1 := H1);
   intros; auto.
   left; split; trivial.
     assert (y' \in pair x y).
    rewrite H; auto.
     rewrite H2 in H4.
       rewrite H3 in H4.
       rewrite H3.
      symmetry  in |- *.
      elim pair_elim with (1:=H4); trivial.
   right; split; trivial.
     assert (x' \in pair x y).
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

(* macros *)
Definition singl x := pair x x.

Lemma singl_intro : forall x, x \in singl x.
Proof.
unfold singl in |- *; auto.
Qed.

Lemma singl_intro_eq : forall x y, x == y -> x \in singl y.
Proof.
intros.
 rewrite H; apply singl_intro.
Qed.

Lemma singl_elim : forall x y, x \in singl y -> x == y.
Proof.
unfold singl; intros.
elim pair_elim with (1:=H); auto.
Qed.

Lemma singl_ext :
  forall y x,
  x \in y ->
  (forall z, z \in y -> z == x) ->
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

(* union of 2 sets *)
Definition union2 x y := union (pair x y).

Lemma union2_intro1: forall x y z, z \in x -> z \in union2 x y.
Proof.
unfold union2 in |- *; intros.
apply union_intro with x; trivial.
Qed.

Lemma union2_intro2: forall x y z, z \in y -> z \in union2 x y.
Proof.
unfold union2 in |- *; intros.
apply union_intro with y; trivial.
Qed.

Lemma union2_elim : forall x y z, z \in union2 x y -> z \in x \/ z \in y.
Proof.
unfold union2; intros.
elim union_elim with (1:=H); intros.
elim pair_elim with (1:=H1); intro x0_eq; rewrite <- x0_eq; auto.
Qed.

Lemma union2_mono : forall A A' B B',
  A \incl A' -> B \incl B' -> union2 A B \incl union2 A' B'.
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

Lemma union2_commut : forall x y, union2 x y == union2 y x.
Proof.
intros.
unfold union2; rewrite pair_commut; reflexivity.
Qed.


(* subtraction *)
Definition minus2 x y := subset x (fun x' => ~ (x' \in y)).


(* Upper bound of a family of sets *)

Definition sup x F := union (replf x F).

Lemma sup_ax : forall x F z,
  ext_fun x F ->
  (z \in sup x F <-> exists2 y, y \in x & z \in F y).
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
  (forall x, x \in a -> F x \incl y) ->
  (forall z, z \in y -> exists2 x, x \in a & z \in F x) ->
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
  ext_fun a F -> x \in a -> F x \incl sup a F.
intros.
red; intros.
rewrite sup_ax; trivial.
exists x; trivial.
Qed.
Hint Resolve sup_incl.


(* Russel's paradox *)

Section Russel.

Variable U : set.
Variable universal : forall x, x \in U.

Definition omega := subset U (fun x => ~ x \in x).

Lemma omega_not_in_omega : ~ omega \in omega.
Proof.
unfold omega at 2 in |- *.
red in |- *; intro.
elim subset_elim2 with (1 := H); intros.
rewrite <- H0 in H1.
exact (H1 H).
Qed.

Lemma omega_in_omega : omega \in omega.
Proof.
unfold omega at 2 in |- *.
apply subset_intro; trivial.
exact omega_not_in_omega.
Qed.

Lemma no_universal_set : False.
Proof (omega_not_in_omega omega_in_omega).

End Russel.

(* intersection *)

Definition inter x := subset (union x) (fun y => forall z, z \in x -> y \in z).

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
  (forall y, y \in a -> x \in y) ->
  (exists w, w \in a) -> (* non empty intersection *)
  x \in inter a.
Proof.
unfold inter in |- *; intros.
apply subset_intro; auto.
destruct H0 as (w,?).
apply union_intro with w; auto.
Qed.

Lemma inter_elim : forall x a y, x \in inter a -> y \in a -> x \in y.
Proof.
unfold inter in |- *; intros.
elim subset_elim2 with (1 := H); intros.
rewrite H1; auto.
Qed.

Lemma inter_non_empty :
  forall x y, y \in inter x -> exists2 w, w \in x & y \in w.
intros.
apply subset_elim1 in H.
rewrite union_ax in H; destruct H; eauto.
Qed.

Lemma inter_wit : forall X F, morph1 F -> 
 forall x, x \in inter (replf X F) ->
 exists y, y \in X.
intros.
destruct inter_non_empty with (1:=H0).
rewrite replf_ax in H1.
2:red;red;intros; apply H; trivial.
destruct H1; eauto.
Qed.

Lemma inter_ext :
  forall i a,
  (forall y, y \in a -> i \incl y) ->
  (forall x, (forall y, y \in a -> x \in y) -> x \in i) ->
  (exists w, w \in a) ->
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

(* Binary intersection *)

Definition inter2 x y := inter (pair x y).

Lemma inter2_def : forall x y z,
  z \in inter2 x y <-> z \in x /\ z \in y.
unfold inter2.
split; intros.
 split; apply inter_elim with (1:=H);
   [apply pair_intro1|apply pair_intro2].

 destruct H.
 apply inter_intro; [intros|exists x; apply pair_intro1].
 apply pair_elim in H1; destruct H1; rewrite H1; trivial.
Qed.

Lemma inter2_incl1 : forall x y, inter2 x y \incl x.
red; intros.
rewrite inter2_def in H; destruct H; trivial.
Qed.
Lemma inter2_incl2 : forall x y, inter2 x y \incl y.
red; intros.
rewrite inter2_def in H; destruct H; trivial.
Qed.

