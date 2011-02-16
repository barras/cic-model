Require Import ZFnats ZFord ZFord_equiv ZFcard.
Import IZF.

Lemma lt_card_non_zero :
  forall x o, isOrd o -> lt_card x o -> lt zero o.
intros.
destruct (ZFordcl.ClassicOrdinal.ord_total o zero); auto.
elim H0.
setoid_replace o with empty.
 exists (fun _ _ => True); intros.
  elim empty_ax with (1:=H2).
  elim empty_ax with (1:=H2).

 red in H1.
 unfold succ in H1.
 apply union2_elim in H1; destruct H1.
  elim empty_ax with (1:=H1).

  apply singl_elim in H1; trivial.
Qed.
