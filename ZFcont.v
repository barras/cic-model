Require Export basic.
Require Import ZF ZFsum ZFfix ZFnats ZFord ZFstable ZFrank ZFrelations.
Import IZF ZFrepl.

(* Continuity *)

Definition continuous o F :=
  forall X, ext_fun o X -> F (sup o X) == sup o (fun z => F (X z)).

Lemma cst_cont : forall X o, (exists y, lt y o) -> X == sup o (fun _ => X).
intros.
apply eq_intro; intros.
 rewrite sup_ax; trivial.
 destruct H as (y,?); exists y; trivial.

 rewrite sup_ax in H0; trivial.
 destruct H0; trivial.
Qed. 

Lemma sum_cont : forall o F G,
  ext_fun o F ->
  ext_fun o G ->
  sum (sup o F) (sup o G) == sup o (fun y => sum (F y) (G y)).
intros.
apply eq_intro; intros.
 rewrite sup_ax; auto.
 elim H1 using sum_ind; clear H1; intros.
  rewrite sup_ax in H1; auto.
  destruct H1.
  exists x0; trivial.
  rewrite H2; apply inl_typ; trivial.

  rewrite sup_ax in H1; auto.
  destruct H1.
  exists x; trivial.
  rewrite H2; apply inr_typ; trivial.

 rewrite sup_ax in H1; auto.
 destruct H1.
 apply sum_mono with (F x) (G x); auto.
Qed.

Section ProductContinuity.

  Hypothesis mu : set.
  Hypothesis mu_ord : isOrd mu.

  Variable X : set.
  Hypothesis X_small : bound_ord X mu. 
(*forall F,
    ext_fun X F ->
    (forall x, x \in X -> lt (F x) mu) ->
    lt (sup X F) mu.*)

  Lemma func_cont_gen : forall F,
    stable_ord F ->
    increasing F ->
    func X (sup mu F) \incl sup mu (fun A => func X (F A)).
intros F Fstb Fincr.
assert (Fm : forall o, isOrd o -> ext_fun o F) by auto.
red; intros.
pose (G := fun n => inter (subset mu (fun y => app z n \in F y))).
assert (Gm : ext_fun X G).
 red; red; intros.
 apply inter_morph.
 apply subset_morph; auto with *.
 red; intros.
 rewrite H1; reflexivity.
assert (Fprop : forall x, x \in X -> app z x \in F (G x) /\ lt (G x) mu).
  intros.
  apply app_typ with (x:=x) in H; trivial.
  rewrite sup_ax in H; auto.
  destruct H.
  split.
   apply Fstb; intros.
    apply subset_elim1 in H2; eauto using isOrd_inv.
   apply inter_intro.
    intros.
    rewrite replf_ax in H2.
     destruct H2.
     rewrite H3.
     rewrite subset_ax in H2; destruct H2.
     destruct H4.
     setoid_replace (F x1) with (F x2); trivial.
     apply Fm with mu; auto.

     red; red; intros.
     apply Fm with mu; auto.
     apply subset_elim1 in H3; trivial.

    exists (F x0).
    rewrite replf_ax.
     exists x0; auto with *.
     apply subset_intro; trivial.

     red; red; intros.
     apply Fm with mu; auto.
     apply subset_elim1 in H2; trivial.

   apply isOrd_plump with x0; auto.
    apply isOrd_inter; intros.
    apply subset_elim1 in H2; eauto using isOrd_inv.

    red; intros.
    apply inter_elim with (1:=H2).
    apply subset_intro; trivial.
assert (Fmu := fun x h => proj2 (Fprop x h)).
assert (Fspec := fun x h => proj1 (Fprop x h)).
clear Fprop.
assert (Ford : forall x, x \in X -> isOrd (G x)).
 intros.
 apply isOrd_inv with mu; auto.
rewrite sup_ax; auto.
assert (lt (osup X G) mu) by (apply X_small; trivial).
exists (osup X G); trivial.
apply func_narrow with (1:=H); intros.
apply Fincr with (G x); auto.
 apply isOrd_osup; auto.

 apply osup_intro; trivial.
Qed.


  Hypothesis mu_bound : lt (osup (func X mu) (fun f => osup X (app f))) mu.


  Lemma func_bound : bound_ord X mu.
red; intros.
apply isOrd_plump with (4:=mu_bound); auto.
 apply isOrd_osup; auto.
 intros.
 apply isOrd_inv with mu; auto.

 red; intros.
 apply osup_intro with (x:=lam X F).
  do 2 red; intros.
  apply osup_morph; auto with *.
  red; intros.
  apply app_morph; trivial.

  apply lam_is_func; auto.

  apply eq_elim with (2:=H1).
  apply osup_morph; auto with *.
  red; intros.
  rewrite beta_eq; auto.
  rewrite <- H3; trivial.
Qed.
(*
Goal lt_cardf X mu.
red ;intros.
assert (exG : exists2 G,
  ext_fun X G &
  (forall x, x \in X -> lt (G x) mu) /\
  forall x, x \in X -> lt (F x) mu -> F x == G x).
 exists (fun x => subset (F x) (fun _ => lt (F x) mu)).
  admit.

  split; intros.
  assert (lt (F x) mu \/ ~ lt (F x) mu).
   admit. (*EM*)
  destruct H1.
   setoid_replace (subset (F x) (fun _ => lt (F x) mu)) with (F x); auto.
   apply eq_intro; intros.
    apply subset_elim1 in H2; trivial.

    apply subset_intro; trivial.

   setoid_replace (subset (F x) (fun _ => lt (F x) mu)) with empty.
    admit. (* mu at least one *)

    apply empty_ext.
    red; intros.
    apply subset_elim2 in H2; destruct H2.
    auto.

   apply eq_intro; intros.
    apply subset_intro; trivial.

    apply subset_elim1 in H2; trivial.
destruct exG as (G, eG, (bG, eFG)).
pose (l := sup X G).
assert (isOrd l).
 apply isOrd_supf; trivial.
 intros.
 apply isOrd_inv with mu; auto.
assert (ll : osucc l \in mu).
 assert (l \in mu).
  apply X_small; trivial.
 admit. (* mu limit *)
exists (osucc l); trivial.
red; intros.
assert (F x \incl l).
 red; intros.
 unfold l; rewrite sup_ax; trivial.
 exists x; trivial.
 rewrite <- eFG; trivial.
 rewrite <- H2; trivial.
apply (lt_antirefl l); trivial.
apply oles_lt; trivial.
rewrite H2; trivial.
Qed.
*)

End ProductContinuity.

(* Case when mu is a regular ordinal *)

Lemma func_cont : forall mu X F,
  isOrd mu ->
  VN_regular mu ->
  stable_ord F ->
  increasing F ->
  X \in VN mu ->
  func X (sup mu F) == sup mu (fun x => func X (F x)).
intros mu X F mu_ord mu_reg Fstb Fincr Fsmall.
apply eq_intro; intros.
 apply func_cont_gen; trivial.
 red; intros; apply VN_reg_ord; auto.

 rewrite sup_ax in H; auto.
 destruct H.
 apply func_mono with X (F x); auto.
 reflexivity.
Qed.
