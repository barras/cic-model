Require Export basic.
Require Import Models.
Require Import Sat.


(** * Abstract strong mormalization model ( *not* supporting strong eliminations) *)

Module Type SN_addon (M : CC_Model).
  Import M.

  (** Types are equipped with a saturated set *)
  Parameter Real : X -> SAT.
  Parameter Real_morph : Proper (eqX ==> eqSAT) Real.

  Parameter Real_sort : eqSAT (Real props) snSAT.

  Parameter Real_prod : forall A B,
    eqSAT (Real (prod A B))
     (prodSAT (Real A) (depSAT (fun x=>x∈A) (fun x => Real (B x)))).

  (** Every proposition is inhabited *)
  Parameter daimon : X.
  Parameter daimon_false : daimon ∈ prod props (fun P => P).

  Existing Instance Real_morph.

End SN_addon.

(** * Abstract strong mormalization model (supporting strong eliminations) *)

Module Type RealSN_addon (M : CC_Model).
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

  (** Every proposition is inhabited *)
  Parameter daimon : X.
  Parameter daimon_false : daimon ∈ prod props (fun P => P).

End RealSN_addon.

Module Type CC_SN_Model := CC_Model <+ RealSN_addon.
