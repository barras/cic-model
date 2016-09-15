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
Import SN_CC_Real.
Import SN.
Import PresburgerTheory PresburgerSem IntpPresburger.

Lemma SN_P : forall e x y,
  (exists hyp a b s, 
    x = Sub (intp_foterm a) s /\
    y = Sub (intp_foterm b) s /\
    wf_clsd_env (intp_hyp hyp) /\
    typ_sub e s (intp_hyp hyp) /\
    deriv hyp (eq_foterm a b)) ->
  eq_typ e x y.
Proof. apply SN_T. Qed.
