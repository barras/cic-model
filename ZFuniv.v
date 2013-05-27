Require Import Sat.
Require Import ZF ZFcoc ZFord ZFgrothendieck.
Require Import ZFlambda.

Set Implicit Arguments.

(** * Auxiliary lemmas: *)

Lemma G_CCLam U :
  grot_univ U ->
  omega ∈ U ->
  CCLam ∈ U.
intros.
assert (U_singl := G_singl _ H).
assert (U_N : ZFnats.N ∈ U).
 apply G_N; trivial.
assert (U_0 : ZFnats.zero ∈ U).
 apply G_inf_nontriv; trivial.
assert (U_succ : forall n, n ∈ U -> ZFnats.succ n ∈ U).
 intros.
 apply G_union2; auto.
unfold CCLam.
unfold Lam.Lambda.
apply G_TI; trivial.
 do 2 red; intros.
 unfold Lam.LAMf.
 rewrite H1; reflexivity.

 intros.
 unfold Lam.LAMf.
 auto 20 using G_union2, G_prodcart.
Qed.
Hint Resolve G_CCLam.

(** * Encoding of types *)

Definition mkTY x S := couple x (iSAT S).
Definition Elt T := fst T. (* total elements *)
Definition El T := union2 (singl empty) (Elt T). (* partial elements *)
Definition Real T := sSAT (snd T) .

Instance El_morph : morph1 El.
do 2 red; intros; apply union2_morph; auto with *.
apply fst_morph; trivial.
Qed.

Lemma El_mkTY T A : El (mkTY T A) == singl empty ∪ T.
unfold El, Elt, mkTY; rewrite fst_def; reflexivity.
Qed.
Lemma Real_mkTY T A : eqSAT (Real (mkTY T A)) A.
unfold Real, mkTY; rewrite snd_def; apply iSAT_id.
Qed.

Lemma Elt_El x y : x ∈ Elt y -> x ∈ El y.
intros; apply union2_intro2; trivial.
Qed.
Lemma empty_El y : empty ∈ El y.
apply union2_intro1; apply singl_intro.
Qed.
Hint Resolve Elt_El empty_El.

(** * Universes *)

(** Given K a set of set of values, builds a type of types (a sort), such that:
    - types are neutral term (hence the Real field of the sort is SN)
    - for each set of values and each saturated, there is a type built from
      this data.
 *)
Definition sn_sort K := mkTY (sup K (fun P => replSAT (fun A => mkTY P A))) snSAT.

Lemma sort_repl_morph :
  Proper (eq_set ==> eqSAT ==> eq_set) (fun P A => mkTY P A).
do 3 red; intros.
apply couple_morph; trivial.
apply iSAT_morph; trivial.
Qed.
Lemma sort_repl_morph2 :
  Proper (eq_set ==> eq_set) (fun P => replSAT(fun A => mkTY P A)).
do 2 red; intros.
apply ZFrepl.repl_morph_raw; auto with *.
do 2 red; intros.
rewrite H1.
unfold mkTY; rewrite H.
rewrite (iSAT_morph _ _ (sSAT_morph _ _ H0)).
reflexivity.
Qed.
Hint Resolve sort_repl_morph sort_repl_morph2.

Lemma sn_sort_intro K T A :
  T ∈ K -> mkTY T A ∈ El (sn_sort K).
intros.
unfold sn_sort; rewrite El_mkTY; apply union2_intro2.
rewrite sup_ax; auto.
exists T; trivial.
rewrite replSAT_ax; auto.
2:apply sort_repl_morph; reflexivity.
exists A; reflexivity.
Qed.

Lemma sn_sort_elim_raw K T :
  T ∈ El (sn_sort K) -> T == empty \/ exists U A, T == mkTY U A /\ U ∈ K.
unfold sn_sort; rewrite El_mkTY.
intro.
apply union2_elim in H; destruct H.
 apply singl_elim in H; auto.

 rewrite sup_ax in H; auto.
 destruct H as (U,?,?).
 rewrite replSAT_ax in H0.
 2:apply sort_repl_morph; reflexivity.
 destruct H0 as (A,?).
 eauto.
Qed.

Lemma sn_sort_elim K T : T ∈ El (sn_sort K) -> T == empty \/ Elt T ∈ K.
intros.
apply sn_sort_elim_raw in H; destruct H as [?|(U,(A,(?,?)))]; auto.
right; rewrite H.
unfold Elt, mkTY; rewrite fst_def; trivial.
Qed.

Lemma sort_incl K1 K2 :
  K1 ⊆ K2 ->
  El (sn_sort K1) ⊆ El (sn_sort K2).
red; intros.
apply sn_sort_elim_raw in H0; destruct H0 as [?|(U,(A,(?,?)))].
 rewrite H0; auto.

 rewrite H0; apply sn_sort_intro; auto.
Qed.

Lemma Real_sort_sn K : eqSAT (Real (sn_sort K)) snSAT.
apply Real_mkTY.
Qed.

Lemma sn_sort_in_type K1 K2 :
  grot_univ K2 ->
  omega ∈ K2 ->
  K1 ∈ K2 ->
  sn_sort K1 ∈ El (sn_sort K2).
intros.
apply sn_sort_intro.
apply G_sup; intros; auto.
apply G_replf; auto.
 do 2 red; intros; apply couple_morph; auto with *.
 apply iSAT_morph; apply sSAT_morph; trivial.

 apply G_power; auto.

 intros.
 apply G_couple; trivial.
  apply G_trans with K1; trivial.

 apply G_subset; auto.
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
 apply G_union; trivial.
 apply G_subset; trivial.
 apply G_union; trivial.

 apply G_union2; auto.
Qed.

Definition sn_props := sn_sort props.

Lemma El_in_props P :
  P ∈ El sn_props ->
  El P ∈ props.
intros.
apply cc_dec_prop.
apply sn_sort_elim in H; destruct H; trivial.
rewrite H.
apply power_intro; intros.
apply union_elim in H0; destruct H0.
apply subset_elim1 in H1.
apply union_elim in H1; destruct H1.
apply empty_ax in H2; contradiction.
Qed.


(** * Dependent product *)

Definition piSAT A (F:set->SAT) :=
  prodSAT (Real A) (interSAT (fun p:{y|y ∈ El A} => F (proj1_sig p))).

Definition sn_prod A F :=
  mkTY (cc_prod (El A) (fun x => El (F x)))
       (piSAT A (fun x => Real (F x))).

Definition sn_lam A F := cc_lam (El A) F.

Lemma sn_prod_intro : forall dom f F,
  ext_fun (El dom) f ->
  ext_fun (El dom) F ->
  (forall x, x ∈ El dom -> f x ∈ El (F x)) ->
  sn_lam dom f ∈ El (sn_prod dom F).
intros.
unfold sn_lam, sn_prod; rewrite El_mkTY.
apply union2_intro2.
apply cc_prod_intro; intros; auto.
do 2 red; intros.
apply El_morph; auto.
Qed.

Lemma sn_prod_elim : forall dom f x F,
  f ∈ El (sn_prod dom F) ->
  x ∈ El dom ->
  cc_app f x ∈ El (F x).
intros.
unfold sn_prod in H; rewrite El_mkTY in H.
apply union2_elim in H; destruct H.
 apply singl_elim in H.
 rewrite H.
 rewrite cc_app_empty; auto.

 apply cc_prod_elim with (dom:=El dom) (F:=fun x => El(F x)); trivial.
Qed.

(** * Dependent product and universes *)

Lemma sn_predicative_prod : forall K dom F,
  grot_univ K ->
  empty ∈ K ->
  ext_fun (El dom) F ->
  dom ∈ El (sn_sort K) ->
  (forall x, x ∈ El dom -> F x ∈ El (sn_sort K)) ->
  sn_prod dom F ∈ El (sn_sort K).
intros K dom F K_grot K_ne ext_F dom_ty F_ty.
apply sn_sort_intro.
apply G_cc_prod; trivial.
 do 2 red; intros.
 apply union2_morph; auto with *.
 apply fst_morph.
 apply ext_F; auto.

 apply El_in_grot; trivial.

 intros.
 specialize F_ty with (1:=H).
 apply El_in_grot; trivial.
Qed.

Lemma sn_impredicative_prod : forall dom F,
  ext_fun (El dom) F ->
  (forall x, x ∈ El dom -> F x ∈ El sn_props) ->
  sn_prod dom F ∈ El sn_props.
intros.
apply sn_sort_intro.
apply cc_impredicative_prod; intros.
specialize H0 with (1:=H1).
apply El_in_props; trivial.
Qed.
