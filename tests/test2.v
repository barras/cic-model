(* Acc and well-founded recursion... *)
Require Import ZFwf ZFord.

Import WellFoundedRecursion2.

Definition AR x y :=
  (isOrd x /\ y = singl (singl empty)) \/
  (isOrd y /\ x ∈ y).
Lemma ssmt_not_ord :
  ~ isOrd (singl (singl empty)).
intro.
assert (empty ∈ singl (singl empty)).
 apply isOrd_trans with (singl empty); trivial.
 apply singl_intro.
 apply singl_intro.
apply singl_elim in H0.
apply empty_ax with empty.
apply eq_elim with (singl empty); auto with *.
apply singl_intro.
Qed.
Lemma wfARo o : isOrd o -> Acc AR o.
induction 1 using isOrd_ind.
constructor; intros.
destruct H2.
destruct H2.
rewrite H3 in H.
apply ssmt_not_ord in H; contradiction.
destruct H2.
auto.
Qed.
Lemma wfAR x : Acc AR x.
constructor; intros.
destruct H.
 destruct H.
 apply wfARo; trivial.
 destruct H.
 apply wfARo; trivial.
 apply isOrd_inv with x; trivial.
Qed.

Lemma not_an_ord :
  ~ exists2 f: set->set,
        (forall x, isOrd (f x)) &
        (forall x y, AR x y -> f x ∈ f y).
intros (f,fo,felt).
assert (forall o, isOrd o -> o ⊆ f o).
 intros.
 elim H using isOrd_ind; intros.
 red; intros.
 apply isOrd_plump with (f z); auto.
  apply isOrd_inv with y; trivial. 

  apply felt.
  right; auto.
pose (w := singl (singl empty)).
assert (forall o, isOrd o -> o ∈ f w).
 intros.
 apply isOrd_plump with (f o); auto.
 apply felt.
 left; auto.
apply (lt_antirefl (f w)); auto.
apply H0; auto.
Qed.

(* But hopefully we cannot use WFR to build such a function...
  

Definition f x := WFR AR (fun F y => osup y (fun z => osucc (F z))) x .

Lemma fo x : isOrd (f x).
elim (wfAR x); intros.
unfold f.
rewrite WFR_eqn.
 apply isOrd_osup.
  admit.

  intros.
  apply isOrd_succ.  
  apply H0.

 *)
