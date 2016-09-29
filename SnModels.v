Require Export basic.
Require Import Models.
Require Import Sat.

(** * Inhabitability condition of SN models*)

(** For CC, we may just requires all props to be inhabited,
    which implies that any typable kind is also inhabited.
    However this does not scale to universes. *)
Module Type AllPropsInhabited (M : CC_Model).
  Import M.
  (** Proposition "false" is inhabited *)
  Parameter daimon : X.
  Parameter daimon_false : daimon ∈ prod props (fun P => P).
End AllPropsInhabited.

(** To deal with universes, we need all types to be inhabited.
    Note that the condition below implies (daimon ∈ daimon),
    so "∈" cannot be the plain set membership. *)
Module Type AllTypesInhabited (M : CC_Model).
  Import M.
  (** Every type is inhabited *)
  Parameter daimon : X.
  Parameter daimon_in_all_types : forall A, daimon ∈ A.
End AllTypesInhabited.

Module InhabitPropsFromTypes
       (M : CC_Model) (H : AllTypesInhabited M) <: AllPropsInhabited M.
  Definition daimon := H.daimon.
  Definition daimon_false := H.daimon_in_all_types (M.prod M.props (fun P=>P)).
End InhabitPropsFromTypes.
  
(** * Abstract strong mormalization model ( *not* supporting strong eliminations) *)

Module Type SAT_weak_addon (M : CC_Model).
  Import M.

  (** Types are equipped with a saturated set *)
  Parameter Real : X -> SAT.
  Parameter Real_morph : Proper (eqX ==> eqSAT) Real.

  Parameter Real_sort : eqSAT (Real props) snSAT.

  Parameter Real_prod : forall A B,
    eqSAT (Real (prod A B))
     (prodSAT (Real A) (depSAT (fun x=>x∈A) (fun x => Real (B x)))).

  Existing Instance Real_morph.

End SAT_weak_addon.

Module Type SN_CC_Model :=
  CC_Model <+ SAT_weak_addon <+ AllPropsInhabited.
Module Type SN_CC_addon (M : CC_Model) :=
  SAT_weak_addon M  <+ AllPropsInhabited M.

Module Type SN_univ_addon (M : CC_Model) :=
  SAT_weak_addon M  <+ AllTypesInhabited M.

(** * Abstract strong mormalization model (supporting strong eliminations) *)

Module Type SAT_strong_addon (M : CC_Model).
  Import M.

  (** Types are equipped with a saturated set for eachh value *)
  Parameter Real : X -> X -> SAT.
  Parameter Real_morph: Proper (eqX ==> eqX ==> eqSAT) Real.

  Parameter Real_sort : forall P, P ∈ props -> eqSAT (Real props P) snSAT.

  Parameter Real_prod : forall dom f F,
    eq_fun dom F F ->
    f ∈ prod dom F ->
    eqSAT (Real (prod dom F) f)
      (piSAT0 (fun x => x ∈ dom) (Real dom)
          (fun x => Real (F x) (app f x))).

  Existing Instance Real_morph.

End SAT_strong_addon.

Module Type SN_NoUniv_Model :=
  CC_Model <+ SAT_strong_addon <+ AllPropsInhabited.

Module Type SN_Univ_Model :=
  CC_Model <+ SAT_strong_addon <+ AllTypesInhabited.
