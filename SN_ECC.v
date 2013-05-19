Require Export Relations Wellfounded Compare_dec.
Require Import Sat.
Require Import ZF ZFcoc ZFecc.
Require Import ZFlambda.

(** Strong normalization proof of the Extended Calculus of Constructions.
    It is based on GenModelSN, so it does not support strong eliminations.
    Inhabitation of all types is obtained by adding the empty set in every
    type. The product is interpreted by the set of *partial* functions.
 *)

Set Implicit Arguments.

(***********************************************************************)
(** * Proving the SN requirements *)

Module CCSN.

Definition mkTY x S := couple x (iSAT S).
Definition Elt T := fst T. (* total elements *)
Definition El T := union2 (singl empty) (Elt T). (* partial elements *)
Definition Real T := sSAT (snd T) .

Lemma Elt_El x y : x ∈ Elt y -> x ∈ El y.
intros; apply union2_intro2; trivial.
Qed.
Lemma empty_El y : empty ∈ El y.
apply union2_intro1; apply singl_intro.
Qed.
Hint Resolve Elt_El empty_El.

Definition piSAT A (F:set->SAT) :=
  prodSAT (Real A) (interSAT (fun p:{y|y ∈ El A} => F (proj1_sig p))).

Definition sn_prod A F :=
  mkTY (cc_prod (El A) (fun x => El (F x)))
       (piSAT A (fun x => Real (F x))).

Definition sn_lam A F := cc_lam (El A) F.

Lemma sn_prod_intro0 : forall dom f F,
  ext_fun (El dom) f ->
  ext_fun (El dom) F ->
  (forall x, x ∈ El dom -> f x ∈ El (F x)) ->
  sn_lam dom f ∈ Elt (sn_prod dom F).
unfold sn_lam, sn_prod, mkTY, El, Elt.
intros.
rewrite fst_def.
apply cc_prod_intro; intros; auto.
do 2 red; intros.
apply union2_morph; auto with *.
apply fst_morph; auto.
Qed.
Lemma sn_prod_intro : forall dom f F,
  ext_fun (El dom) f ->
  ext_fun (El dom) F ->
  (forall x, x ∈ El dom -> f x ∈ El (F x)) ->
  sn_lam dom f ∈ El (sn_prod dom F).
intros.
apply Elt_El.
apply sn_prod_intro0; auto.
Qed.

Lemma sn_prod_elim : forall dom f x F,
  f ∈ El (sn_prod dom F) ->
  x ∈ El dom ->
  cc_app f x ∈ El (F x).
intros.
unfold sn_prod, mkTY, El in H.
apply union2_elim in H; destruct H.
 apply singl_elim in H.
 rewrite H.
 rewrite cc_app_empty; auto.

 unfold Elt at 1 in H; rewrite fst_def in H.
 apply cc_prod_elim with (dom:=El dom) (F:=fun x => El(F x)); trivial.
(*
 apply union2_elim in H0; destruct H0.
  apply singl_elim in H0.
  assert (x ∈ Elt dom \/ ~ x ∈ Elt dom). admit.
  destruct H1.
   apply cc_prod_elim with (dom:=Elt dom) (F:=fun x => El(F x)); trivial.

   assert (cc_app f x == empty).
    apply empty_ext.
    red; intros y ?.
    rewrite <- couple_in_app in H2.
    apply H1.
    apply cc_prod_is_cc_fun in H.
    red in H.
    apply H in H2.
    destruct H2 as (_,?).
    rewrite fst_def in H2; trivial.
   rewrite H2; auto.

  apply cc_prod_elim with (dom:=Elt dom) (F:=fun x => El(F x)); trivial.*)
Qed.

Lemma cc_impredicative_prod_non_empty : forall dom F,
  ext_fun dom F ->
  (forall x, x ∈ dom -> F x == singl prf_trm) ->
  cc_prod dom F == singl prf_trm.
Proof.
intros.
apply singl_ext; intros.
 rewrite <- (cc_impredicative_lam dom (fun x => prf_trm)); intros.
 2:do 2 red; reflexivity.
  apply cc_prod_intro; intros; auto.
  apply H0 in H1; rewrite H1.
  apply singl_intro.

  reflexivity.

 unfold cc_prod in H1.
 rewrite replf_ax in H1; intros.
  destruct H1 as (f,f_fun,z_lam).
  rewrite z_lam; clear z z_lam.
  apply cc_impredicative_lam; intros.
   do 2 red; intros.
   rewrite H2; reflexivity.

   apply singl_elim.
   fold prf_trm.
   rewrite <- (H0 _ H1).
   apply dep_func_elim with (1:=f_fun); trivial.

  do 2 red; intros.
  apply cc_lam_ext; try reflexivity.
  red; intros.
  apply app_morph; trivial.
Qed.


Definition sn_props :=
  mkTY (replSAT(fun A => mkTY (singl prf_trm) A)) snSAT.

Lemma prop_repl_morph :
  Proper (eqSAT ==> eq_set) (fun A => mkTY (singl prf_trm) A).
do 2 red; intros.
apply couple_morph; try reflexivity.
apply iSAT_morph; trivial.
Qed.
Hint Resolve prop_repl_morph.

Lemma sn_impredicative_prod : forall dom F,
  ext_fun (El dom) F ->
  (forall x, x ∈ El dom -> F x ∈ El sn_props) ->
  sn_prod dom F ∈ El sn_props.
intros.
apply Elt_El.
unfold sn_props, mkTY, El, Elt in *.
rewrite fst_def.
assert (singl prf_trm ∈ props).
 apply power_intro; auto.
rewrite replSAT_ax; trivial.
exists (piSAT dom (fun x : set => Real (F x))).
unfold sn_prod, mkTY.
apply couple_morph; auto with *.
apply cc_impredicative_prod_non_empty.
 do 2 red; intros; unfold El, Elt.
 apply union2_morph; auto with *.
 apply fst_morph.
 apply H; trivial.
(* apply union2_intro2; trivial.*)

 intros.
 specialize H0 with (1:=H2).
 rewrite fst_def in H0.
 apply union2_elim in H0; destruct H0.
  apply singl_elim in H0.
  unfold El; rewrite H0.
  apply eq_intro; intros.
   apply union2_elim in H3; destruct H3; trivial.
   unfold Elt, fst in H3.
   apply union_elim in H3; destruct H3.
   apply subset_elim1 in H4.
   rewrite union_empty_eq in H4.
   apply empty_ax in H4; contradiction.

   apply union2_intro1; trivial.

  rewrite replSAT_ax in H0; trivial.
  destruct H0.
  unfold El; rewrite H0; rewrite fst_def.
  apply eq_intro; intros.
   apply union2_elim in H3; destruct H3; trivial.
   apply union2_intro1; trivial.
Qed.

(*

Definition sn_props :=
  mkTY (sup props (fun P => replSAT(fun A => mkTY P A))) snSAT.

Lemma prop_repl_morph :
  Proper (eq_set ==> eqSAT ==> eq_set) (fun P A => mkTY P A).
do 3 red; intros.
apply couple_morph; trivial.
apply iSAT_morph; trivial.
Qed.
Lemma prop_repl_morph2 :
  Proper (eq_set ==> eq_set) (fun P => replSAT(fun A => mkTY P A)).
do 2 red; intros.
apply ZFrepl.repl_morph_raw; auto with *.
do 2 red; intros.
rewrite H1.
unfold mkTY; rewrite H.
rewrite (iSAT_morph _ _ (sSAT_morph _ _ H0)).
reflexivity.
Qed.
Hint Resolve prop_repl_morph prop_repl_morph2.

Lemma sn_impredicative_prod : forall dom F,
  ext_fun (El dom) F ->
  (forall x, x ∈ El dom -> F x ∈ El sn_props) ->
  sn_prod dom F ∈ El sn_props.
intros.
apply Elt_El.
unfold sn_props, mkTY, El, Elt in *.
rewrite fst_def.
pose (P := cc_prod (Elt dom) (fun x => El(F x))).
assert (P ∈ props).
 apply cc_impredicative_prod; intros.
 specialize H0 with (1:=Elt_El H1).
 rewrite fst_def in H0.
 apply power_intro; intros.
 apply union2_elim in H2; destruct H2; trivial.
 apply union2_elim in H0; destruct H0.
  apply singl_elim in H0.
  rewrite H0 in H2.
  unfold Elt, fst in H2.
  apply union_elim in H2; destruct H2.
  apply subset_elim1 in H3.
  rewrite union_empty_eq in H3.
  apply empty_ax in H3; contradiction.

  rewrite sup_ax in H0.
  2:do 2 red; intros; apply prop_repl_morph2; auto.
  destruct H0.
  rewrite replSAT_ax in H3.
  2:apply prop_repl_morph; reflexivity.
  destruct H3.
  rewrite H3 in H2.
  unfold Elt in H2; rewrite fst_def in H2.
  apply power_elim with x0; auto.
rewrite sup_ax.
2:do 2 red; intros; apply prop_repl_morph2; auto.
exists P; auto with *.
rewrite replSAT_ax; trivial.
2:apply prop_repl_morph; reflexivity.
exists (piSAT dom (fun x : set => Real (F x))).
reflexivity.
Qed.
*)

  Lemma sn_proof_of_false : prf_trm ∈ El (sn_prod sn_props (fun P => P)).
auto.
(*
setoid_replace prf_trm with (cc_lam (El sn_props) (fun _ => prf_trm)).
 unfold sn_prod, mkTY, El; rewrite fst_def.
 apply cc_prod_intro; intros.
  do 2 red; reflexivity.

  do 2 red; intros; apply fst_morph; trivial.
  unfold sn_props, mkTY in H.
  rewrite fst_def in H.
  rewrite replSAT_ax in H; trivial.
  destruct H as (A, eq_x).
  rewrite eq_x.
  rewrite fst_def.
  apply singl_intro.

 symmetry.
 apply cc_impredicative_lam; intros.
  do 2 red; intros; reflexivity.
  reflexivity.*)
Qed.

End CCSN.
Import CCSN.

(** * Building the CC abstract SN model *)


Require Import Models.
Module SN_CC_Model <: CC_Model.

Definition X := set.
Definition inX x y := x ∈ El y.
Definition eqX := eq_set.
Lemma eqX_equiv : Equivalence eqX.
Proof eq_set_equiv.

Lemma in_ext: Proper (eqX ==> eqX ==> iff) inX.
do 3 red; intros.
unfold inX, El, eqX in *.
rewrite H; rewrite H0; reflexivity.
Qed.

Definition props := sn_props.
Definition app := cc_app.
Definition lam := sn_lam.
Definition prod := sn_prod.
(*
Notation "x ∈ y" := (inX x y).
Notation "x == y" := (eqX x y).
*)
Definition eq_fun (x:X) (f1 f2:X->X) :=
  forall y1 y2, inX y1 x -> y1 == y2 -> f1 y1 == f2 y2.

Lemma eq_fun_El x f1 f2 : eq_fun x f1 f2 -> ZF.eq_fun (El x) f1 f2.
do 2 red; intros.
apply H; auto.
Qed.
Hint Resolve eq_fun_El.

Lemma lam_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  lam x1 f1 == lam x2 f2.
unfold lam, sn_lam, eqX; intros.
apply cc_lam_ext; auto.
unfold El; rewrite H; reflexivity.
Qed.

Lemma app_ext: Proper (eqX ==> eqX ==> eqX) app.
Proof cc_app_morph.

Lemma prod_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  prod x1 f1 == prod x2 f2.
unfold prod, sn_prod, eqX, mkTY, El; intros.
apply couple_morph.
 apply cc_prod_ext; intros.
  rewrite H; reflexivity.

  red; intros.
  apply union2_morph; auto with *.
  apply fst_morph; apply H0; auto.
  red; auto.

 apply iSAT_morph.
 unfold piSAT, Real.
 apply prodSAT_morph.
  apply sSAT_morph; apply snd_morph; trivial.

  apply interSAT_morph_subset; simpl; intros.
   unfold El; rewrite H; reflexivity.

   apply sSAT_morph; apply snd_morph; apply H0; auto; reflexivity.
Qed.

Lemma prod_intro : forall dom f F,
  eq_fun dom f f ->
  eq_fun dom F F ->
  (forall x, inX x dom -> inX (f x) (F x)) ->
  inX (lam dom f) (prod dom F).
Proof sn_prod_intro.

Lemma prod_elim : forall dom f x F,
  eq_fun dom F F ->
  inX f (prod dom F) ->
  inX x dom ->
  inX (app f x) (F x).
intros.
eapply sn_prod_elim; eauto.
Qed.

Lemma impredicative_prod : forall dom F,
  eq_fun dom F F ->
  (forall x, inX x dom -> inX (F x) props) ->
  inX (prod dom F) props.
Proof sn_impredicative_prod.

Lemma beta_eq:
  forall dom F x,
  eq_fun dom F F ->
  inX x dom ->
  app (lam dom F) x == F x.
unfold app, lam, inX, eqX; intros.
apply cc_beta_eq; auto.
Qed.

End SN_CC_Model.

Import SN_CC_Model.

(***********************************************************************)
(** Building the SN addon *)

Module SN_CC_addon.

  Definition Real : X -> SAT := Real.

  Lemma Real_morph : Proper (eqX ==> eqSAT) Real.
do 2 red; intros.
apply sSAT_morph.
apply snd_morph; trivial.
Qed.

  Lemma Real_sort : eqSAT (Real props) snSAT.
unfold Real, CCSN.Real, props, sn_props, mkTY.
rewrite snd_def.
rewrite iSAT_id.
reflexivity.
Qed.

  Lemma Real_prod : forall A B,
    eqSAT (Real (prod A B))
     (prodSAT (Real A)
        (interSAT (fun p:{y|inX y A} => Real (B (proj1_sig p))))).
unfold Real, CCSN.Real, prod, sn_prod, piSAT, mkTY; intros.
rewrite snd_def.
rewrite iSAT_id.
reflexivity.
Qed.

  Definition daimon := empty.

  Lemma daimon_false : inX daimon (prod props (fun P => P)).
Proof sn_proof_of_false.

End SN_CC_addon.


(** * Universes *)

Definition sort K :=
  sup K (fun P => replSAT (fun A => mkTY P A)).

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


Definition sn_type n := mkTY (sort (ecc n)) snSAT.

Import ZFgrothendieck.
Hint Resolve ecc_grot.


Lemma omega_ecc0 : ZFord.omega ⊆ ecc 0.
red; intros.
unfold ZFord.omega, ZFord.ord_sup in H.
rewrite sup_ax in H.
 destruct H.
 rewrite ZFrepl.uchoice_ax in H0.
  destruct H0.
  destruct H0.
  rewrite <- H2 in H1.
  apply G_trans with (ZFord.nat2ordset x1); trivial.
  elim x1; intros.
   apply G_incl with ZFcoc.props; trivial.
    apply ecc_in1.
    red; intros.
    apply empty_ax in H3; contradiction.

   apply G_subset; trivial.
   apply G_power; auto.

  (* Fch *)
  split;[|split]; intros.
 revert H2; apply ex2_morph; red; intros; auto with *.
 rewrite H1; reflexivity.

 elim H using ZFnats.N_ind; intros.
  revert H3; apply ex_morph.
  red; intros.
  apply ex2_morph; red; intros; auto with *.
  rewrite H2; reflexivity.

  exists (ZFord.nat2ordset 0); exists 0; simpl; auto with *.

  destruct H2 as (y,(m,?,?)).
  exists (ZFord.nat2ordset (S m)); exists (S m); simpl; auto with *.
  apply ZFnats.succ_morph; trivial.

 destruct H1; destruct H2.
 rewrite <- H3; rewrite <- H4; rewrite H1 in H2; apply ZFnats.nat2set_inj in H2.
 rewrite H2; reflexivity.

 (* Fm *)
do 2 red; intros.
apply ZFrepl.uchoice_morph_raw.
red; intros.
apply ex2_morph.
 red; intros.
 rewrite H1; reflexivity.

 red; intros.
 rewrite H2; reflexivity.
Qed.

Lemma omega_in_ecc1 : ZFord.omega ∈ ecc 1.
apply G_incl with (ecc 0); auto.
 apply grot_succ_in; exact gr.

 apply omega_ecc0.
Qed.

(* ecc 0 is countable so we need to skip it.
   ecc 1 is not countable...*)
Lemma CCLam_ecc0 : CCLam ∈ ecc 1.
unfold CCLam.
unfold Lam.Lambda.
apply G_TI; auto.
 do 2 red; intros.
 unfold Lam.LAMf.
 rewrite H; reflexivity.

 apply omega_in_ecc1.

 intros.
 unfold Lam.LAMf.
 apply G_union2; trivial.
  apply G_union2; trivial.
   apply G_prodcart; trivial.
    apply G_singl; trivial.
    apply G_trans with ZFnats.N; auto.
    apply ZFnats.zero_typ.
    apply G_N; trivial.
    apply omega_in_ecc1.

    apply G_N; trivial.
    apply omega_in_ecc1.

   apply G_prodcart; trivial.
    apply G_singl; trivial.
    apply G_trans with ZFnats.N; auto.
    apply ZFnats.succ_typ.
    apply ZFnats.zero_typ.
    apply G_N; trivial.
    apply omega_in_ecc1.

    apply G_trans with ZFnats.N; auto.
    apply ZFnats.zero_typ.
    apply G_N; trivial.
    apply omega_in_ecc1.

  apply G_union2; trivial.
   apply G_prodcart; trivial.
    apply G_singl; trivial.
    apply G_trans with ZFnats.N; auto.
    apply ZFnats.succ_typ.
    apply ZFnats.succ_typ.
    apply ZFnats.zero_typ.
    apply G_N; trivial.
    apply omega_in_ecc1.

    apply G_prodcart; trivial.

   apply G_prodcart; trivial.
    apply G_singl; trivial.
    apply G_trans with ZFnats.N; auto.
    apply ZFnats.succ_typ.
    apply ZFnats.succ_typ.
    apply ZFnats.succ_typ.
    apply ZFnats.zero_typ.
    apply G_N; trivial.
    apply omega_in_ecc1.
Qed.
Hint Resolve CCLam_ecc0.

Lemma ecc_incl_le x m n :
  le m n -> x ∈ ecc m -> x ∈ ecc n.
induction 1; intros; auto with *.
apply ecc_incl; auto.
Qed.
(*
Lemma G_props n : ZFcoc.props.gl empty ∈ ecc n.
apply G_singl; trivial.
apply G_incl with ZFcoc.props; trivial.
 apply ecc_in1.
cl_le with (m:=0); auto with *.
 apply ecc_in.
*)

Lemma G_TY T A n :
  T ∈ ecc (S n) ->
  mkTY T A ∈ ecc (S n).
intros.
unfold mkTY.
apply G_couple; trivial.
apply G_subset; auto.
apply ecc_incl_le with 1; auto with *.
Qed.

Lemma sort_intro K T A :
  T ∈ K -> mkTY T A ∈ sort K.
intros.
unfold sort.
rewrite sup_ax; auto.
exists T; trivial.
rewrite replSAT_ax; auto.
2:apply sort_repl_morph; reflexivity.
exists A; reflexivity.
Qed.

Lemma sort_elim_raw K T : T ∈ sort K -> exists U A, T == mkTY U A /\ U ∈ K.
unfold sort; rewrite sup_ax; auto.
intros (U,?,?).
rewrite replSAT_ax in H0.
2:apply sort_repl_morph; reflexivity.
destruct H0 as (A,?).
eauto.
Qed.

Lemma sort_elim K T : T ∈ sort K -> Elt T ∈ K.
intros.
apply sort_elim_raw in H; destruct H as (U,(A,(?,?))).
rewrite H.
unfold Elt, mkTY; rewrite fst_def; trivial.
Qed.

Lemma sn_prop_type0 :
  inX sn_props (sn_type 1).
apply Elt_El.
unfold Elt, sn_type, mkTY; rewrite fst_def.
apply sort_intro.
apply G_replf; auto.
 do 2 red; intros; apply couple_morph; auto with *.
 apply iSAT_morph; apply sSAT_morph; trivial.

 apply G_power; trivial.

 intros.
 unfold mkTY.
 apply G_couple; trivial.
  apply G_trans with ZFcoc.props; auto.
   apply power_intro; auto.
   apply ecc_in1.

  apply G_subset; auto.
Qed.

Lemma sn_type_type n :
  inX (sn_type n) (sn_type (S n)).
apply Elt_El.
unfold Elt, sn_type, mkTY; rewrite fst_def.
apply sort_intro.
apply G_sup; auto.
 apply ecc_in2.

 intros.
 apply G_replf; auto.
  do 2 red; intros; apply couple_morph; auto with *.
  apply iSAT_morph; apply sSAT_morph; trivial.

  apply G_power; trivial.
  apply ecc_incl_le with 1; auto with *.

  intros.
  unfold mkTY.
  apply G_couple; trivial.
   apply ecc_incl; trivial.

   apply G_subset; auto.
   apply ecc_incl_le with 1; auto with *.
Qed.

Lemma El_type n T :
  T ∈ singl empty ∪ sort (ecc n) ->
  El T ∈ ecc n.
intros.
apply union2_elim in H; destruct H.
 apply G_union2; trivial.
  apply G_trans with ZFcoc.props; auto.
   apply power_intro; auto.
   apply ecc_in1.

   apply singl_elim in H.
   rewrite H.
   apply G_union; trivial.
   apply G_subset; trivial.
   apply G_union; trivial.
   apply G_incl with ZFcoc.props; auto.
    apply ecc_in1.
    red; intros.
    apply empty_ax in H0; contradiction.

  apply sort_elim in H.
  apply G_union2; auto.
  apply G_trans with ZFcoc.props; auto.
   apply power_intro; auto.
   apply ecc_in1.
Qed.

Lemma sn_predicative_prod : forall n dom F,
  ext_fun (El dom) F ->
  dom ∈ El (sn_type n) ->
  (forall x, x ∈ El dom -> F x ∈ El (sn_type n)) ->
  sn_prod dom F ∈ El (sn_type n).
intros.
apply Elt_El.
unfold sn_type, mkTY, El, Elt in *.
rewrite fst_def in H0|-*.
apply sort_intro.
apply ecc_prod; intros.
 do 2 red; intros.
 apply union2_morph; auto with *.
 apply fst_morph.
 apply H; auto.

 apply El_type; trivial.

 specialize H1 with (1:=H2).
 rewrite fst_def in H1.
 apply El_type; trivial.
Qed.


(***********************************************************************)
(*
----
*)

Require GenModelSN.
Module SN := GenModelSN.MakeModel SN_CC_Model SN_CC_addon.

(** ** Extendability *)
Definition cst (x:set) : SN.trm.
left; exists (fun _ =>x) (fun _ =>Lambda.K).
 do 2 red; reflexivity.
 do 2 red; reflexivity.
 red; reflexivity.
 red; reflexivity.
Defined.

Definition mkSET (x:set) := cst (mkTY x snSAT).

Lemma mkSET_kind e x :
(*  (exists w, in_set w x) ->*)
  SN.typ e (mkSET x) SN.kind.
red; intros.
split;[discriminate|].
split;[|apply Lambda.sn_K].
exists nil; exists (mkSET x).
 reflexivity.

 exists empty; simpl; intros _.
 apply union2_intro1.
 apply singl_intro.
Qed.

Lemma cst_typ e x y :
  in_set x y ->
  SN.typ e (cst x) (mkSET y).
red; intros.
apply SN.in_int_intro; try discriminate.
 simpl.
 apply Elt_El.
 unfold mkTY, Elt.
 rewrite fst_def; trivial. 

 unfold SN_CC_addon.Real, Real, SN.tm, SN.int, mkSET, cst, SN.iint, SN.itm.
 unfold mkTY; rewrite snd_def.
 rewrite iSAT_id.
 apply Lambda.sn_K.
Qed.
(*
Lemma cst_typ_inv x y :
  SN.typ nil (cst x) (mkSET y) ->
  in_set x y.
intros.
assert (SN.val_ok nil (SN.V.nil empty) (SN.I.nil Lambda.K)).
 red; intros.
 destruct n; inversion H0.
apply H in H0.
apply SN.in_int_not_kind in H0.
2:discriminate.
destruct H0 as (H0,_ ); simpl in H0.
unfold SN_CC_Model.inX, mkTY, El in H0.
rewrite fst_def in H0; trivial.
Qed.
*)
Lemma cst_eq_typ e x y :
  x == y ->
  SN.eq_typ e (cst x) (cst y).
red; simpl; intros; trivial.
Qed.

Lemma cst_eq_typ_inv x y :
  SN.eq_typ nil (cst x) (cst y) ->
  x == y.
intros.
assert (SN.val_ok nil (SN.V.nil empty) (SN.I.nil Lambda.K)).
 red; intros.
 destruct n; inversion H0.
apply H in H0.
simpl in H0; trivial.
Qed.

Lemma mkSET_eq_typ e x y :
  x == y ->
  SN.eq_typ e (mkSET x) (mkSET y).
red; simpl; intros; trivial.
unfold mkTY; rewrite H; reflexivity.
Qed.

Lemma mkSET_eq_typ_inv x y :
  SN.eq_typ nil (mkSET x) (mkSET y) ->
  x == y.
intros.
assert (SN.val_ok nil (SN.V.nil empty) (SN.I.nil Lambda.K)).
 red; intros.
 destruct n; inversion H0.
apply H in H0.
simpl in H0; trivial.
apply couple_injection in H0; destruct H0; trivial.
Qed.

(** * Predicative universes: inference rules *)

Definition type (n:nat) : SN.trm := cst (sn_type (S n)).

Lemma typ_prop_type0 e :
  SN.typ e SN.prop (type 0).
red; intros.
apply SN.in_int_intro.
 apply sn_prop_type0.

 simpl SN.int; simpl SN.tm.
 simpl SN_CC_addon.Real.
 unfold SN_CC_addon.Real, sn_type.
 unfold Real, mkTY.
 generalize (snSAT_intro Lambda.sn_K).
 apply inSAT_morph; auto.
 rewrite snd_def.
 rewrite iSAT_id; reflexivity.

 discriminate.
 discriminate.
Qed.

Lemma typ_type_type e n :
  SN.typ e (type n) (type (S n)).
red; intros.
apply SN.in_int_intro.
 apply sn_type_type.

 simpl SN.int; simpl SN.tm.
 simpl SN_CC_addon.Real.
 unfold SN_CC_addon.Real, sn_type.
 unfold Real, mkTY.
 generalize (snSAT_intro Lambda.sn_K).
 apply inSAT_morph; auto.
 rewrite snd_def.
 rewrite iSAT_id; reflexivity.

 discriminate.
 discriminate.
Qed.

Lemma typ_prop_cumul e T :
  SN.typ e T SN.prop ->
  SN.typ e T (type 0).
red; intros.
apply H in H0.
destruct H0.
split; trivial.
destruct H1.
split.
 revert H1; apply union2_mono; auto with *.
Opaque ecc.
 simpl; unfold props, sn_props, sn_type; simpl.
 unfold Elt, mkTY; rewrite fst_def; rewrite fst_def.
 red; intros.
 rewrite replSAT_ax in H1.
 2:apply prop_repl_morph.
 destruct H1.
 rewrite H1.
 apply sort_intro.
 apply ecc_incl.
 apply ecc_incl_prop.
 apply power_intro; auto.

 revert H2; apply inSAT_morph; trivial.
 apply sSAT_morph.
 simpl; unfold props, sn_props, sn_type, mkTY.
 rewrite snd_def; rewrite snd_def; reflexivity.
Qed.

Lemma typ_type_cumul e T n :
  SN.typ e T (type n) ->
  SN.typ e T (type (S n)).
red; intros.
apply H in H0.
destruct H0.
split; trivial.
destruct H1.
split.
 revert H1; apply union2_mono; auto with *.
 unfold Elt, type, sn_type, mkTY; simpl.
 rewrite fst_def; rewrite fst_def.
 red; intros.
 apply sort_elim_raw in H1.
 destruct H1 as (U,(A,(?,?))).
 rewrite H1; apply sort_intro.
 revert H3; apply (ecc_incl (S n)).

 revert H2; apply inSAT_morph; trivial.
 apply sSAT_morph.
 simpl; unfold sn_type, mkTY.
 rewrite snd_def; rewrite snd_def; reflexivity.
Qed.
Lemma typ_type_cumul_le e T m n :
  le m n ->
  SN.typ e T (type m) ->
  SN.typ e T (type n).
induction 1; intros; auto.
apply typ_type_cumul; auto.
Qed.

Lemma typ_predicative_prod e T U n :
  SN.typ e T (type n) ->
  SN.typ (T::e) U (type n) ->
  SN.typ e (SN.Prod T U) (type n).
unfold SN.typ; intros.
specialize H with (1:=H1).
destruct H as (?,(?,?)); trivial.
split;[discriminate|].
split.
 apply sn_predicative_prod; trivial.
  red; red; intros.
  rewrite H5; reflexivity.

  intros.
  specialize SN.vcons_add_var0 with (1:=H1) (2:=H4) (3:=H);
    intros in_U.
  apply H0 in in_U.
  apply SN.in_int_not_kind in in_U;[|discriminate].
  destruct in_U; trivial.

  assert (forall i, eqSAT (SN_CC_addon.Real (SN.int i (type n))) snSAT).
   simpl; intros _.
   unfold SN_CC_addon.Real, sn_type, Real, mkTY.
   rewrite snd_def.
   rewrite iSAT_id; reflexivity.
  specialize SN.vcons_add_var0 with (1:=H1) (2:=empty_El _) (3:=H);
    intros in_U.
  apply H0 in in_U.
  destruct in_U  as (_,(_,satU)).
  rewrite H4 in H3,satU|-*.
  simpl in satU|-*.
  rewrite SN.tm_subst_cons in satU.
  apply Lambda.sn_subst in satU.
  apply KSAT_intro with (A:=snSAT); auto.
Qed.

(** * Mapping from syntactic entities to their semantic counterparts. *)

(** syntax of ECC *)
Require TypeJudgeECC.
Module Ty := TypeJudgeECC.
Module Tm := TermECC.
Module Lc := Lambda.


(** Terms *)
Fixpoint int_trm t :=
  match t with
  | Tm.Srt Tm.prop => SN.prop
  | Tm.Srt (Tm.kind n) => type n
  | Tm.Ref n => SN.Ref n
  | Tm.App u v => SN.App (int_trm u) (int_trm v)
  | Tm.Abs T M => SN.Abs (int_trm T) (int_trm M)
  | Tm.Prod T U => SN.Prod (int_trm T) (int_trm U)
  end.
Definition interp t := int_trm t.
Definition int_env := List.map interp.

Section LiftAndSubstEquiv.
(* Proof that lift and subst at both levels (SN and Tm) are equivalent. *)

(* Locally Import this module *)
Import SN.

Lemma int_lift_rec : forall n t k,
  eq_trm (lift_rec n k (int_trm t)) (int_trm (Tm.lift_rec n t k)).
induction t; simpl int_trm; intros.
 destruct s; simpl; trivial.
 split; red; intros; reflexivity.

 split; red; intros; reflexivity.

 simpl; unfold V.lams, I.lams, V.shift, I.shift.
 destruct (le_gt_dec k n0); simpl.
  replace (k+(n+(n0-k))) with (n+n0) by omega.
  split; red; auto.

  split; red; auto.

 rewrite red_lift_abs; rewrite IHt1; rewrite IHt2; reflexivity.
 rewrite red_lift_app; rewrite IHt1; rewrite IHt2; reflexivity.
 rewrite red_lift_prod; rewrite IHt1; rewrite IHt2; reflexivity.
Qed.

Lemma int_lift : forall n t,
  eq_trm (int_trm (Tm.lift n t)) (lift n (int_trm t)).
intros.
symmetry.
unfold Tm.lift, lift.
apply int_lift_rec.
Qed.

Lemma int_subst_rec : forall arg,
  int_trm arg <> kind ->
  forall t k,
  eq_trm (subst_rec (int_trm arg) k (int_trm t)) (int_trm (Tm.subst_rec arg t k)).
intros arg not_knd.
induction t; simpl int_trm; intros.
 destruct s; simpl; trivial.
 split; red; intros; reflexivity.

 split; red; intros; reflexivity.

 simpl Tm.subst_rec.
 destruct (lt_eq_lt_dec k n) as [[fv|eqv]|bv]; simpl int_trm.
  simpl int_trm.
  destruct n; [inversion fv|].
  rewrite SN.red_sigma_var_gt; auto with arith.
  reflexivity.

  subst k; rewrite SN.red_sigma_var_eq; trivial.
  symmetry; apply int_lift.

  rewrite SN.red_sigma_var_lt; trivial.
  reflexivity.

 rewrite SN.red_sigma_abs.
 rewrite IHt1; rewrite IHt2; reflexivity.

 rewrite SN.red_sigma_app.
 rewrite IHt1; rewrite IHt2; reflexivity.

 rewrite SN.red_sigma_prod.
 rewrite IHt1; rewrite IHt2; reflexivity.
Qed.


Lemma int_subst : forall u t,
  int_trm u <> kind ->
  eq_trm (int_trm (Tm.subst u t)) (subst (int_trm u) (int_trm t)).
unfold Tm.subst; symmetry; apply int_subst_rec; trivial.
Qed.

End LiftAndSubstEquiv.
(* Proof that beta-reduction at the Lc level simulates beta-reduction
   at the Tm level. One beta at the Tm level may require several
   (but not zero) steps at the Lc level, because of the encoding
   of type-carrying lambda abstractions.
 *)
Lemma red1_sound : forall x y,
  Tm.red1 x y ->
  SN.red_term (int_trm x) (int_trm y).
induction 1; simpl; intros.
 rewrite int_subst.
  apply SN.red_term_beta.

  destruct N; try discriminate.
  destruct s; try discriminate.

 apply SN.red_term_abs_l; auto 10.
 apply SN.red_term_abs_r; auto 10.
 apply SN.red_term_app_l; auto 10.
 apply SN.red_term_app_r; auto 10.
 apply SN.red_term_prod_l; auto 10.
 apply SN.red_term_prod_r; auto 10.
Qed.

Lemma sn_sound : forall M,
  Acc (transp _ SN.red_term) (interp M) ->
  Tm.sn M.
intros M accM.
apply Acc_inverse_image with (f:=int_trm) in accM.
induction accM; intros.
constructor; intros.
apply H0; trivial.
 apply red1_sound; trivial.
Qed.


(** Soundness of the typing rules *)

Lemma interp_nk : forall T, interp T <> SN.kind.
induction T; simpl; intros; try discriminate.
destruct s; discriminate.
Qed.
Hint Resolve interp_nk.

Lemma typ_sort_type_ok e T s : 
  T <> SN.kind ->
  SN.typ e T (interp (TermECC.Srt s)) ->
  SN.type_ok e T.
split; trivial.
split.
 apply H0 in H1.
 apply SN.in_int_sn in H1; trivial.

 exists empty; red; auto. 
Qed.

Lemma int_sound : forall e M M' T,
  Ty.eq_typ e M M' T ->
  SN.typ (int_env e) (interp M) (interp T) /\
  SN.eq_typ (int_env e) (interp M) (interp M').
induction 1; simpl; intros.
 (* Srt *)
 split.
  apply typ_prop_type0.
  apply SN.refl.
 split.
  apply typ_type_type.
  apply SN.refl.
 (* Ref *)
 split.
  destruct H0.
  subst t.
  unfold Tm.lift, interp.
  fold (Tm.lift (S v) x); rewrite int_lift.
  simpl.
  apply SN.typ_var.
  elim H1; simpl; auto.

  apply SN.refl.
 (* Abs *)
 destruct IHeq_typ1.
 clear IHeq_typ2.
 destruct IHeq_typ3.
 unfold interp; simpl; fold (interp T) (interp M) (interp U).
 split.
  apply SN.typ_abs_ok; eauto.
  apply typ_sort_type_ok in H3; auto.

  apply SN.eq_typ_abs; eauto.
 (* App *)
 destruct IHeq_typ1.
 destruct IHeq_typ3.
 clear IHeq_typ2 IHeq_typ4.
 unfold interp; simpl; fold (interp u) (interp v) (interp Ur).
 split.
  rewrite int_subst; fold (interp v); eauto.
  fold (interp Ur).
  apply SN.typ_app with (interp V); eauto.

  apply SN.eq_typ_app; trivial.
 (* Prod *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 unfold interp; simpl; fold (interp T) (interp U) (interp T') (interp U').
 split.
  destruct s2; simpl in H1.
   destruct s1.
    destruct s3; try discriminate.
    destruct (eq_nat_dec (max n n0) n1); try discriminate.
    subst n1.
    apply typ_predicative_prod.
     apply typ_type_cumul_le with n0; auto with *.
     apply typ_type_cumul_le with n; auto with *.

    destruct s3; try discriminate.
    destruct (eq_nat_dec n n0); try discriminate.
    subst n0.
    apply typ_predicative_prod; trivial.
    apply typ_type_cumul_le with 0; auto with *.
    apply typ_prop_cumul; trivial.

  destruct s3; try discriminate.
  apply SN.typ_prod_prop; auto.
  apply typ_sort_type_ok in H2; auto.

  apply SN.eq_typ_prod; eauto.
 (* Beta *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 destruct IHeq_typ3.
 clear IHeq_typ4.
 unfold interp; simpl; fold (interp T) (interp M) (interp U) (interp N).
 split.
  rewrite int_subst; fold (interp N); eauto.
  fold (interp U).
  apply SN.typ_beta_ok; auto.
  apply typ_sort_type_ok in H6; auto.

  rewrite int_subst; fold (interp N').
  2:assert (h := Ty.typ_refl2 _ _ _ _ H); eauto.
  apply SN.eq_typ_beta; eauto.
 (* Red *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 split; trivial.
 apply SN.typ_conv with (interp T); eauto.
 (* Exp *)
 destruct IHeq_typ1.
 destruct IHeq_typ2.
 split; trivial.
 apply SN.typ_conv with (int_trm T'); eauto.
 apply SN.sym; trivial.
Qed.

  Lemma interp_wf : forall e, Ty.wf e -> SN.wf (int_env e).
induction e; simpl; intros.
 apply SN.wf_nil.

 inversion_clear H.
 assert (wfe := Ty.typ_wf _ _ _ _ H0).
 apply int_sound in H0.
 destruct H0 as (H0,_).
 apply SN.wf_cons_ok; auto.
 apply typ_sort_type_ok in H0; auto.
Qed.

Lemma interp_sound : forall e M M' T,
  Ty.eq_typ e M M' T ->
  SN.wf (int_env e) /\ SN.typ (int_env e) (interp M) (interp T).
intros.
assert (wfe := Ty.typ_wf _ _ _ _ H).
apply interp_wf in wfe.
apply int_sound in H; destruct H; auto.
Qed.

(***********)
(*
----
*)

(** The main theorem: strong normalization of CC *)

Lemma strong_normalization : forall e M M' T,
  Ty.eq_typ e M M' T ->
  Tm.sn M.
Proof.
intros.
apply interp_sound in H.
destruct H as (wfe,ty).
apply SN.model_strong_normalization in ty; trivial.
apply sn_sound; trivial.
Qed.

(* Print the assumptions made to derive strong normalization of ECC:
   the axioms of ZF, and the existence of Grothendieck universes.
   In fact we don't need full replacement, only the functional version,
   so we have the SN theorem with only the axiom about Grothendieck universes.
 *)
Print Assumptions strong_normalization.
