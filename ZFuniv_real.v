Require Import Sat.
Require Import ZF ZFcoc ZFord ZFgrothendieck.
Require Import ZFlambda.
Require Import Models SnModels.

Set Implicit Arguments.

(** * Encoding of types *)

(** Types are coded by a carrier set X and a realizability relation R
   assigning a reducibility candidate to each element of the
   domain.
   This means that even non-computable functions have "realizers",
   but no closed ones (it is the set of neutral terms).
 *)
Definition mkTY X R := couple X (cc_lam (cc_bot X) (fun x => iSAT (R x))).

Lemma mkTY_ext : forall X Y R R',
  X == Y ->
  (forall x x', x ∈ cc_bot X -> x == x' -> eqSAT (R x) (R' x')) ->
  mkTY X R == mkTY Y R'.
unfold mkTY; intros.
apply couple_morph; trivial.
apply cc_lam_ext; auto.
 apply cc_bot_morph; trivial.
red; intros.
apply iSAT_morph.
auto.
Qed.

(* Accessing the set of values of a type.
   The official membership relation of the model (see inX below) will be
   x ∈ El T, which reads "x is a value of type T"
 *)
Definition Elt T := fst T. (* total elements *)
Definition El T := cc_bot (Elt T). (* partial elements *)

Instance Elt_morph : morph1 Elt.
Proof fst_morph.

Instance El_morph : morph1 El.
do 2 red; intros; apply cc_bot_morph; auto with *.
apply fst_morph; trivial.
Qed.

Lemma Elt_empty : Elt empty == empty.
apply fst_mt.
Qed.

Lemma Elt_def : forall X R, Elt (mkTY X R) == X.
unfold El,mkTY; intros.
apply fst_def.
Qed.

Lemma El_def : forall X R, El (mkTY X R) == cc_bot X.
unfold El,Elt,mkTY; intros.
rewrite fst_def; reflexivity.
Qed.

Lemma Elt_El x y : x ∈ Elt y -> x ∈ El y.
intros; apply cc_bot_intro; trivial.
Qed.
Lemma empty_El y : empty ∈ El y.
unfold El; auto.
Qed.
Hint Resolve Elt_El empty_El.


(** * Universes *)

(** Given K a set of set of values, builds a type of types (a sort), such that:
    - types are neutral term (hence the Real field of the sort is SN)
    - for each set of values and each realizability relation, there is a type
      built from this data.
 *)
Definition sn_sort K :=
   mkTY (sup K (fun P => replf (cc_arr (cc_bot P) SATset) (fun R => couple P R)))
     (fun _ => snSAT).

Lemma sn_sort_ax T K:
  T ∈ El (sn_sort K) <->
  T == empty \/
  exists2 P, P ∈ K & exists2 R,
    (forall x x', x ∈ cc_bot P -> x==x' -> eqSAT (R x) (R x')) &
    T == mkTY P R.
unfold sn_sort; rewrite El_def.
rewrite cc_bot_ax.
apply or_iff_morphism; [reflexivity|].
rewrite sup_ax.
 apply ex2_morph; auto with *.
 intros P.
 rewrite replf_ax.
  split; intros.
   destruct H as (R,tyR,eqT).
   exists (fun x => sSAT (cc_app R x)).
    intros.
    apply sSAT_morph.
    apply cc_app_morph; auto with *.

    rewrite eqT; apply couple_morph; auto with *.
    rewrite cc_eta_eq with (1:=tyR).
    apply cc_lam_ext; auto with *.
    red; intros.
    symmetry.
    rewrite <- H0.
    apply cc_arr_elim  with (2:=H) in tyR.
    apply subset_elim2 in tyR.
    destruct tyR as (S,eqS,is_sat).
    rewrite eqS; trivial.

   destruct H as (R,?,?).
   assert (ext_fun (cc_bot P) (fun x : set => iSAT (R x))).
    do 2 red; intros; apply iSAT_morph; auto.
   exists (cc_lam (cc_bot P) (fun x => iSAT (R x))); trivial.
   apply cc_prod_intro; intros; auto.
   apply subset_intro.
    apply power_intro; intros.
    apply subset_elim1 in H3; trivial.

    rewrite iSAT_id; reflexivity.

 do 2 red; intros.
 rewrite H0; reflexivity.

 do 2 red; intros.
 apply replf_morph.
  rewrite H0; reflexivity.

  red; intros.
  apply couple_morph; trivial.
Qed.


Lemma sn_sort_intro K T A :
  (forall x x', x ∈ cc_bot T -> x == x' -> eqSAT (A x) (A x')) ->
  T ∈ K -> mkTY T A ∈ El (sn_sort K).
intros.
apply sn_sort_ax; right.
exists T; trivial.
exists A; auto with *.
Qed.

Lemma sn_sort_elim_raw K T :
  T ∈ El (sn_sort K) ->
  T == empty \/
  exists U A, T == mkTY U A /\ U ∈ K /\ forall x x', x∈cc_bot U->x==x'->eqSAT(A x)(A x').
intro.
apply sn_sort_ax in H.
destruct H as [?|(P,?,(R,Rext,eqT))]; auto.
right.
exists P; exists R; auto.
Qed.

Lemma sn_sort_elim K T : T ∈ El (sn_sort K) -> T == empty \/ Elt T ∈ K.
intros.
apply sn_sort_elim_raw in H; destruct H as [?|(U,(A,(?,(?,?))))]; auto.
right; rewrite H.
unfold Elt, mkTY; rewrite fst_def; trivial.
Qed.

Lemma sort_incl K1 K2 :
  K1 ⊆ K2 ->
  El (sn_sort K1) ⊆ El (sn_sort K2).
red; intros.
apply sn_sort_elim_raw in H0; destruct H0 as [?|(U,(A,(?,(?,?))))].
 rewrite H0; auto.

 rewrite H0; apply sn_sort_intro; auto.
Qed.

Lemma sn_sort_in_type K1 K2 :
  grot_univ K2 ->
  omega ∈ K2 ->
  K1 ∈ K2 ->
  sn_sort K1 ∈ El (sn_sort K2).
intros.
apply sn_sort_intro.
 reflexivity.
apply G_sup; intros; auto.
 do 2 red; intros.
 apply replf_morph.
  rewrite H3; reflexivity.

  red; intros.
  apply couple_morph; auto.
assert (cc_arr (cc_bot x) SATset ∈ K2).
 apply G_cc_prod; intros; auto.
  apply G_union2; auto.
   apply G_singl; trivial; apply G_inf_nontriv; trivial.
   apply G_trans with K1; trivial.
   
  apply G_subset; auto.
  apply G_power; auto.
apply G_replf; auto with *.
 do 2 red; intros.  
 apply couple_morph; auto with *.

 intros.
 apply G_couple; trivial.
  apply G_trans with K1; trivial.

  apply G_trans with (2:=H4); trivial.
Qed.

Lemma El_in_grot K T :
  grot_univ K -> 
  empty ∈ K ->
  T ∈ El (sn_sort K) ->
  El T ∈ K.
intros K_grot K_ne T_in_K.
assert (Kse : singl empty ∈ K).
 auto using G_singl.
apply sn_sort_elim in T_in_K; destruct T_in_K.
 apply G_union2; trivial.
 rewrite H.
 rewrite Elt_empty; trivial.

 apply G_union2; auto.
Qed.

(** Universe of propositions *)

Notation sn_props := (sn_sort props).

Lemma El_in_props P :
  P ∈ El sn_props ->
  El P ∈ props.
intros.
apply cc_bot_prop.
apply sn_sort_elim in H; destruct H; trivial.
rewrite H.
rewrite Elt_empty.
apply power_intro; intros.
apply empty_ax in H0; contradiction.
Qed.

Definition mkProp S := mkTY (singl empty) (fun _ => S).

Lemma El_mkProp : forall S, El (mkProp S) == singl empty.
intros.
apply singl_ext;  auto.
intros.
unfold mkProp in H; rewrite El_def in H.
apply cc_bot_ax in H; destruct H; trivial.
apply singl_elim in H; trivial.
Qed.

Lemma mkProp_intro S : mkProp S ∈ El sn_props.
apply sn_sort_intro.
 reflexivity.

 apply power_intro.
 intros.
 apply singl_elim in H.
 rewrite  H; apply singl_intro.
Qed.

Lemma El_props_true P :
  P ∈ El sn_props -> El P == singl empty.
intros.
apply sn_sort_elim in H.
apply singl_ext; auto.
intros.
apply cc_bot_ax in H0; destruct H0; trivial.
destruct H.
 rewrite H in H0.
 rewrite Elt_empty in H0.
 apply empty_ax in H0; contradiction.

 apply props_proof_irrelevance with (1:=H); trivial.
Qed.



(** * Now we build an instance of the abstract SN model *)

Module CC_Real <: SN_Univ_Model.

Definition X := set.
Definition inX x y := x ∈ El y.
Definition eqX := eq_set.
Definition eqX_equiv := eq_set_equiv.
Definition in_ext : Proper (eq_set ==> eq_set ==> iff) inX.
apply morph_impl_iff2; auto with *.
unfold inX; do 4 red; intros.
rewrite H,H0 in H1; trivial.
Qed.
Definition inclX x y := forall z, inX z x -> inX z y.

(* Accessing the realizability relation.
   inSAT t (Real T x), means that t is a realizer of x in type T. It
   implicitely requires x ∈ El T. 
 *)
Definition Real T x := sSAT (cc_app (snd T) x) .

Instance Real_morph : Proper (eq_set==>eq_set==>eqSAT) Real.
do 3 red; intros.
unfold Real.
apply sSAT_morph.
rewrite H; rewrite H0; reflexivity.
Qed.

Lemma Real_def : forall x X R,
  (forall x x', x ∈ cc_bot X -> x == x' -> eqSAT (R x) (R x')) ->
  x ∈ cc_bot X ->
  eqSAT (Real (mkTY X R) x) (R x).
intros.
unfold Real, mkTY.
rewrite snd_def.
rewrite cc_beta_eq; auto.
 apply iSAT_id.

 do 2 red; intros.
 apply iSAT_morph; auto.
Qed.

(** Sorts *)

Lemma Real_sort_sn T K : T ∈ El (sn_sort K) -> eqSAT (Real (sn_sort K) T) snSAT.
intros.
unfold sn_sort.
apply Real_def.
 reflexivity.

 unfold sn_sort in H; rewrite El_def in H; trivial.
Qed.

Lemma Real_mkProp S x : x == empty -> eqSAT (Real (mkProp S) x) S.
intros.
unfold mkProp; rewrite Real_def; auto with *.
rewrite H; auto.
Qed.

(** Dependent product *)

(** The realizability relation of a dependent product of domain type A
   and co-domain family of types F for a  function f:
   it is the intersection of all reducibility candidates {x}A -> {f(x)}F(x)
   when x ranges A.
   Note: {x}A -> {f(x)}F(x) is the set of that map any realizer of x (in A) to a
   realizer of f(x) (in F(x)). So the intersection of these sets when x ranges El(A)
   is the set of terms that realize f (in forall x:A. F(x)).
 *)
Definition piSAT A (F:set->set) (f:set->set) :=
  piSAT0 (fun x => x ∈ El A) (Real A) (fun x => Real (F x) (f x)).

Lemma piSAT_morph : forall A B F F' f f',
  A == B ->
  eq_fun (El A) F F' ->
  eq_fun (El A) f f' -> 
  eqSAT (piSAT A F f) (piSAT B F' f').
unfold piSAT; intros.
apply piSAT0_morph; intros.
 red; intros.
 rewrite H; reflexivity.

 rewrite H; reflexivity.

 apply Real_morph; auto with *.
Qed.

Definition prod A F :=
  mkTY (cc_prod (El A) (fun x => El (F x))) (fun f => piSAT A F (cc_app f)).

Lemma El_prod dom F :
  ext_fun (El dom) F ->
  El (prod dom F) == cc_prod (El dom) (fun x => El (F x)).
intros.
unfold prod; rewrite El_def.
rewrite cc_prod_mt; intros; auto with *.
do 2 red; intros; apply El_morph; auto.
Qed.

Lemma Real_prod dom f F :
  ext_fun (El dom) F ->
  f ∈ El (prod dom F) ->
  eqSAT (Real (prod dom F) f) (piSAT dom F (cc_app f)).
intros.
rewrite El_prod in H0; trivial.
unfold prod; rewrite Real_def; auto.
 reflexivity.

 intros; apply piSAT_morph; auto with *.
 red; intros; apply cc_app_morph; trivial.
Qed.

Definition lam A F := cc_lam (El A) F.

Definition app := cc_app.

Lemma prod_intro : forall dom f F,
  ext_fun (El dom) f ->
  ext_fun (El dom) F ->
  (forall x, x ∈ El dom -> f x ∈ El (F x)) ->
  lam dom f ∈ El (prod dom F).
intros.
unfold lam.
rewrite El_prod; trivial.
apply cc_prod_intro; intros; auto.
do 2 red; intros; apply El_morph; auto.
Qed.

Lemma prod_elim : forall dom f x F,
  eq_fun (El dom) F F ->
  f ∈ El (prod dom F) ->
  x ∈ El dom ->
  cc_app f x ∈ El (F x).
intros dom f x F Fm H H0.
rewrite El_prod in H; trivial.
apply cc_prod_elim with (dom:=El dom) (F:=fun x => El(F x)); trivial.
Qed.


(** * Dependent product and universes *)

Lemma predicative_prod : forall K dom F,
  grot_univ K ->
  empty ∈ K ->
  ext_fun (El dom) F ->
  dom ∈ El (sn_sort K) ->
  (forall x, x ∈ El dom -> F x ∈ El (sn_sort K)) ->
  prod dom F ∈ El (sn_sort K).
intros K dom F K_grot K_ne ext_F dom_ty F_ty.
apply sn_sort_intro.
 intros.
 apply piSAT_morph; auto with *.
 red; intros.
 apply cc_app_morph; trivial.

 apply G_cc_prod; trivial.
  do 2 red; intros; apply El_morph; auto.

  apply El_in_grot; trivial.

  intros.
  specialize F_ty with (1:=H).
  apply El_in_grot; trivial.
Qed.

Lemma impredicative_prod : forall dom F,
  ext_fun (El dom) F ->
  (forall x, x ∈ El dom -> F x ∈ El sn_props) ->
  prod dom F ∈ El sn_props.
intros.
apply sn_sort_intro.
 intros.
 apply piSAT_morph; auto with *.
 red; intros.
 apply cc_app_morph; trivial.

 apply cc_impredicative_prod; intros.
 specialize H0 with (1:=H1).
 apply El_in_props; trivial.
Qed.


Definition eq_fun dom f g := (* ZF.eq_fun (El dom) f g. *)
  forall x x', x ∈ El dom -> x == x' -> f x == g x'.

Definition props := sn_props.

Lemma lam_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  lam x1 f1 == lam x2 f2.
intros.
apply cc_lam_ext; trivial.
apply El_morph; trivial.
Qed.

Definition app_ext := cc_app_morph.

Lemma prod_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  prod x1 f1 == prod x2 f2.
unfold prod, eqX, mkTY; intros.
apply couple_morph.
 apply cc_prod_ext; intros.
  apply El_morph; trivial.
  red; intros.
  apply El_morph; auto.

 apply cc_lam_ext.
  apply cc_bot_morph.
  apply cc_prod_ext; intros.
   apply El_morph; trivial.
   red; intros.
   apply El_morph; auto.

  red; intros.
  apply iSAT_morph.
  unfold piSAT.
  apply piSAT0_morph; auto with *.
   red; intros; rewrite H; reflexivity.

   intros; rewrite H; reflexivity.

   intros; apply Real_morph; auto with *.
   rewrite H2; reflexivity.
Qed.

Lemma beta_eq:
  forall dom F x,
  eq_fun dom F F ->
  inX x dom ->
  app (lam dom F) x == F x.
unfold app, lam, inX, eqX, El; intros.
apply cc_beta_eq; trivial.
Qed.

  Lemma Real_sort P : inX P props -> eqSAT (Real props P) snSAT.
intros.
apply Real_sort_sn; trivial.
Qed.

  Definition daimon := empty.
  Lemma daimon_in_all_types A : inX daimon A.
red; auto.
Qed.
  Lemma daimon_false : inX daimon (prod props (fun P => P)).
red; auto.
Qed.

End CC_Real.
Export CC_Real.
