Set Implicit Arguments.

(** In this file, we build a consistency model of the
    Calculus of Constructions extended with natural numbers and
    the usual recursor (CC+NAT). It is a follow-up of file
    ModelZF. 
 *)

Require Import basic.
Require Import Models.
Require Import ModelZF ZFnats.

(** We give an instance of the abstract model of CC + nats *)
Module CCN <: CCNat_Model := ModelZF.CCM <+ ZFnats.

(** We derive the syntax and the typing rules *)
Require Import GenModelNat.
Module M : CCNat_Rules := MakeNatModel(CCN).

