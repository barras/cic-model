(****************************************************************************)
(****************************************************************************)
(*This file proves SN after embedding Presburger*)
(****************************************************************************)
(****************************************************************************)

Require Import PIntp.
Require Import AbsSNT.

Import PSem PSyn.

Module SNP := Abs_SN_Theory PresburgerTheory PresburgerSem IntpPresburger.

Import SNP.
Import Esub SN_CC_Real.
Import SN CCSN.
Import PresburgerTheory PresburgerSem IntpPresburger.

Lemma SN_P : forall e x y,
  (exists hyp a b i j, 
    x = app_esub i j (intp_fotrm a) /\
    y = app_esub i j (intp_fotrm b) /\
    wf_clsd_env (intp_hyp hyp) /\
    typ_esub e i j (intp_hyp hyp) /\
    deriv hyp (eq_fotrm a b)) ->
  eq_typ e x y.
Proof. apply SN_T. Qed.