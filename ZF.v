
Require Export basic.
Require Import Sublogic.
Require Export ZFdef.
Require Z.
Export CoqSublogicThms.
#[global]Hint Unfold Tnot : core.

Module Structure.
  Record izfr : Type :=
    BuildIZFR {
        set : Type;
        eq_set : set -> set -> Prop;
        in_set : set -> set -> Prop;
        eq_set_ax :
          forall a b : set, eq_set a b <-> (forall x : set, in_set x a <-> in_set x b);
        in_reg : forall a a' b : set, eq_set a a' -> in_set a b -> in_set a' b;
        wf_ax :
          forall P : set -> Prop,
            (forall x : set, (forall y : set, in_set y x -> P y) -> P x) ->
            forall x : set, P x;
        empty : set;
        pair : set -> set -> set;
        union : set -> set;
        subset : set -> (set -> Prop) -> set;
        infinite : set;
        power : set -> set;
        empty_ax : forall x : set, ~ in_set x empty;
        pair_ax :
          forall a b x : set, in_set x (pair a b) <-> eq_set x a \/ eq_set x b;
        union_ax :
          forall a x : set, in_set x (union a) <-> exists2 y : set, in_set x y & in_set y a;
        subset_ax :
          forall (a : set) (P : set -> Prop) (x : set),
          in_set x (subset a P) <-> in_set x a /\ exists2 x' : set, eq_set x x' & P x';
        infinity_ax1 : in_set empty infinite;
        infinity_ax2 :
          forall x : set, in_set x infinite -> in_set (union (pair x (pair x x))) infinite;
        power_ax :
          forall a x : set, in_set x (power a) <-> (forall y : set, in_set y x -> in_set y a);
        repl : set -> (set -> set -> Prop) -> set;
        repl_mono :
          forall a a' : set,
            (forall z : set, in_set z a -> in_set z a') ->
            forall R R' : set -> set -> Prop,
              (forall x x' : set, eq_set x x' -> forall y y' : set,
                    eq_set y y' -> R x y <-> R' x' y') ->
              forall z : set, in_set z (repl a R) -> in_set z (repl a' R');
        repl_ax :
          forall (a : set) (R : set -> set -> Prop),
          (forall x x' y y' : set, in_set x a -> eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
          (forall x y y' : set, in_set x a -> R x y -> R x y' -> eq_set y y') ->
          forall x : set, in_set x (repl a R) <-> exists2 y : set, in_set y a & R y x }.
End Structure.
  
(** We assume the existence of a model of IZF (that is actually
    constructed modulo one axiom (ttrepl): *)
Require ZFskolEm.
(** We will only use this construction of sets through the abstract
    module signature IZF_R_Sig. *)
(*Module IZF_Axioms : IZF_R_sig CoqSublogicThms := ZFskolEm.IZF_R.*)

Section BuildStructure.
  Import Structure ZFskolEm.IZF_R.
  
  Lemma izfr_struct : izfr.
 exact (BuildIZFR set
        eq_set
        in_set
        eq_set_ax
        in_reg
        wf_ax
        empty
        pair
        union
        subset
        infinite
        power
        empty_ax
        pair_ax
        union_ax
        subset_ax
        infinity_ax1
        infinity_ax2
        power_ax
        repl
        repl_mono
        repl_ax).
  Qed.
End BuildStructure.

Module IZF_Axioms.
Definition set : Type :=
  Structure.set izfr_struct.
Definition eq_set : set -> set -> Prop :=
  Structure.eq_set izfr_struct.
Definition in_set : set -> set -> Prop :=
  Structure.in_set izfr_struct.
Definition eq_set_isL (x y:set) : eq_set x y->eq_set x y := fun h=>h.
Definition in_set_isL (x y:set) : in_set x y->in_set x y := fun h=>h.
Lemma eq_set_ax :
  forall a b : set, eq_set a b <-> (forall x : set, in_set x a <-> in_set x b).
exact (Structure.eq_set_ax izfr_struct).
Qed.
Lemma in_reg : forall a a' b : set, eq_set a a' -> in_set a b -> in_set a' b.
exact (Structure.in_reg izfr_struct).
Qed.
Lemma wf_ax :
  forall P : set -> Prop,
    (forall x : set, (forall y : set, in_set y x -> P y) -> P x) ->
    forall x : set, P x.
exact (Structure.wf_ax izfr_struct).
Qed.
Definition empty : set :=
  Structure.empty izfr_struct.
Definition pair : set -> set -> set :=
  Structure.pair izfr_struct.
Definition union : set -> set :=
  Structure.union izfr_struct.
Definition subset : set -> (set -> Prop) -> set :=
  Structure.subset izfr_struct.
Definition infinite : set :=
  Structure.infinite izfr_struct.
Definition power : set -> set :=
  Structure.power izfr_struct.
Lemma empty_ax : forall x : set, ~ in_set x empty.
exact (Structure.empty_ax izfr_struct).
Qed.
Lemma pair_ax :
  forall a b x : set, in_set x (pair a b) <-> eq_set x a \/ eq_set x b.
exact (Structure.pair_ax izfr_struct).
Qed.
Lemma union_ax :
  forall a x : set, in_set x (union a) <-> exists2 y : set, in_set x y & in_set y a.
exact (Structure.union_ax izfr_struct).
Qed.
Lemma subset_ax :
  forall (a : set) (P : set -> Prop) (x : set),
    in_set x (subset a P) <-> in_set x a /\ exists2 x' : set, eq_set x x' & P x'.
exact (Structure.subset_ax izfr_struct).
Qed.
Lemma infinity_ax1 : in_set empty infinite.
exact (Structure.infinity_ax1 izfr_struct).
Qed.
Lemma infinity_ax2 :
  forall x : set, in_set x infinite -> in_set (union (pair x (pair x x))) infinite.
exact (Structure.infinity_ax2 izfr_struct).
Qed.
Lemma power_ax :
  forall a x : set, in_set x (power a) <-> (forall y : set, in_set y x -> in_set y a).
exact (Structure.power_ax izfr_struct).
Qed.
Definition repl : set -> (set -> set -> Prop) -> set :=
  Structure.repl izfr_struct.
Lemma repl_mono :
  forall a a' : set,
    (forall z : set, in_set z a -> in_set z a') ->
    forall R R' : set -> set -> Prop,
      (forall x x' : set, eq_set x x' -> forall y y' : set,
            eq_set y y' -> R x y <-> R' x' y') ->
      forall z : set, in_set z (repl a R) -> in_set z (repl a' R').
exact (Structure.repl_mono izfr_struct).
Qed.
Lemma repl_ax :
  forall (a : set) (R : set -> set -> Prop),
    (forall x x' y y' : set, in_set x a -> eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x y y' : set, in_set x a -> R x y -> R x y' -> eq_set y y') ->
    forall x : set, in_set x (repl a R) <-> exists2 y : set, in_set y a & R y x.
exact (Structure.repl_ax izfr_struct).
Qed.
End IZF_Axioms.
(* We get all the derived facts of Zermelo Set Theory *)
Module IZ_Lemmas := Z.ZermeloSetTheory CoqSublogicThms IZF_Axioms.

Export IZF_Axioms.
Export IZ_Lemmas.
#[global]Opaque set eq_set in_set empty pair union subset power infinite repl.
Notation "x == y" := (eq_set x y).
Notation "x ∈ y" := (in_set x y).

(*Include IZF_Axioms.*) (*Print Assumptions repl_ax.*)
(** And we import all the basic derived notions belonging to
    Zermelo set theory *)

(**********************************************************************)
(* Basic derived notions involving (functional) replacement *)

(*Parameter replf : set -> (set->set) -> set.*)
Definition replf (a:set) (F:set->set) : set :=
  repl a (fun x y => forall x', x==x' -> y == F x').
(*Definition replf (a:set) (F:set->set) : set :=
  repl a (fun x y => y == F x). *)

Lemma replf_ax_raw : forall a F z,
  (z ∈ replf a F <-> exists2 x, x ∈ a & forall x', x==x' -> z == F x').
intros.
unfold replf.
apply repl_ax.
*intros.
 rewrite <-H1.
 apply H2.
 rewrite H0; trivial.
*intros.
 rewrite H0 with (x':=x); [|reflexivity].
 rewrite H1 with (x':=x); [|reflexivity].
 reflexivity.
Qed.

#[global] Opaque replf.

Instance replf_mono_raw :
  Proper (incl_set ==> (eq_set ==> eq_set) ==> incl_set) replf.
do 4 red; intros.
rewrite replf_ax_raw in *.
destruct H1 as (a,?,?).
exists a; [auto|intros].
rewrite H2 with (x':=x'); trivial.
apply H0; reflexivity.
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
intros.
rewrite replf_ax_raw.
apply ex2_morph'; [reflexivity|intros].
split; intros; auto with *.
rewrite H1; auto.
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

Lemma replf_id x : replf x (fun y => y) == x.
apply eq_set_ax; intros z.
rewrite replf_ax;[|auto with *].
split; intros.
*destruct H as (z',?,e).
 rewrite e; trivial.
*exists z; [trivial|reflexivity].
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

  Lemma fa_replf_iff a F P :
    Proper (eq_set==>iff) P ->
    ext_fun a F ->
    (forall x, x ∈ replf a F -> P x) <-> (forall z, z ∈ a -> P (F z)).
intros Pm Fext.
split; intros.
*apply H.
 rewrite replf_ax; eauto with *.
*rewrite replf_ax in H0; trivial.
 destruct H0 as (z,?,?).
 rewrite H1; auto.
Qed.


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

  Lemma ex_sup_iff a b P :
    ext_fun a b ->
    (exists x, x ∈ sup a b /\ P x) <->
    (exists y, y ∈ a /\ exists x, x ∈ b y /\ P x).
split; intros.
*destruct H0 as (x,(?,?)).
 rewrite sup_ax in H0; [|trivial].
 destruct H0; eauto.
*destruct H0 as (y,(?,(x,(?,?)))); exists x; split;[|trivial].
 rewrite sup_ax; eauto.
Qed.

Lemma sup_incl : forall a F x,
  ext_fun a F -> x ∈ a -> F x ⊆ sup a F.
intros.
red; intros.
rewrite sup_ax; trivial.
exists x; trivial.
Qed.
Hint Resolve sup_incl : core.

Lemma sup_lub x f A :
  ext_fun x f ->
  (forall y, y ∈ x -> f y ⊆ A) ->
  sup x f ⊆ A.
red; intros.
apply sup_ax in H1; trivial.
destruct H1 as (y,?,?).
apply H0 with (y:=y); trivial.
Qed.


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

Lemma inter_wit : forall X F, morph1 F -> 
 forall x, x ∈ inter (replf X F) ->
 exists y, y ∈ X.
intros.
destruct inter_non_empty with (1:=H0).
rewrite replf_ax in H1.
2:red;red;intros; apply H; trivial.
destruct H1; eauto.
Qed.
