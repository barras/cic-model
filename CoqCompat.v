Require Export Coq85.
Require Export AdmitAxiom.

Require Coq.omega.Omega.
Ltac omega := Coq.omega.Omega.omega.
Global Set Asymmetric Patterns.

Require Import Morphisms.
Existing Instance respectful_per.

Notation value := Some.
