
Require Import ZFnats ZFord ZFrank ZFgrothendieck.

(* An inaccesible cardinal yields a Grothendieck universe *)
Section VN_Inaccessible.

Variable mu : set.
Hypothesis mu_inacc : VN_inaccessible_rel mu.

Let mu_ord : isOrd mu.
destruct mu_inacc as ((?,_),_); trivial.
Qed.

Let mu_lim : forall x, lt x mu -> lt (osucc x) mu.
destruct mu_inacc as ((_,?),_); trivial.
Qed.

Let mu_reg : VN_regular_rel mu.
destruct mu_inacc as ((_,_),?); trivial.
Qed.

Lemma VN_grot : grot_univ (VN mu).
split; intros.
 apply VN_trans with x; trivial.

 apply VN_clos_pair; auto.

 apply VNlim_power; trivial.
 split; trivial.

 apply mu_reg; trivial.
Qed.

End VN_Inaccessible.

(* Conversely, the set of ordinals of a Grothendieck universe form
   an inaccessible cardinal *)

Section Grothendieck_Universe.

  Variable U : set.
  Hypothesis Ug : grot_univ U.
  Hypothesis Uinf : omega ∈ U.

  Definition grot_ord := subset U isOrd.

  Lemma grot_ord_intro : forall x, lt x grot_ord -> x ∈ U.
intros.
apply subset_elim1 in H; trivial.
Qed.

  Lemma isOrd_grot : forall x, lt x grot_ord -> isOrd x.
intros.
apply subset_elim2 in H; destruct H.
rewrite H; trivial.
Qed.
Hint Resolve isOrd_grot.

  Lemma grot_ord_inv : forall x, isOrd x -> x ∈ U -> lt x grot_ord.
intros.
apply subset_intro; trivial.
Qed.

  Lemma isOrd_grot_ord : isOrd grot_ord.
apply isOrd_intro; intros.
 apply subset_intro; trivial.
 apply G_incl with b; trivial.
 apply grot_ord_intro; trivial.

 red; intros.
 assert (isOrd x) by eauto using isOrd_grot.
 assert (isOrd y) by eauto using isOrd_grot.
 assert (x ∈ U) by (apply grot_ord_intro; trivial).
 assert (y ∈ U) by (apply grot_ord_intro; trivial).
 exists (x ⊔ y). 
  apply subset_intro.
   apply G_osup2; auto.

   apply isOrd_osup2; trivial.

  split; [apply osup2_incl1|apply osup2_incl2]; auto.

 apply isOrd_grot; trivial.
Qed.
Hint Resolve isOrd_grot_ord.

 Lemma G_limit : forall x, lt x grot_ord -> lt (osucc x) grot_ord.
intros.
apply grot_ord_inv; auto.
apply G_subset; trivial.
apply G_power; trivial.
apply grot_ord_intro; trivial.
Qed.

(* *)

  Lemma VN_in_grot :
    forall o, lt o grot_ord -> VN o ∈ U.
unfold VN; intros.
apply G_TI; auto with *.
 apply grot_ord_intro; trivial.

 intros.
 apply G_power; trivial.
Qed.


  Lemma VN_incl_grot : VN grot_ord ⊆ U.
red; intros.
rewrite VN_def in H; auto.
destruct H.
apply G_trans with (power (VN x)); trivial.
 rewrite power_ax; trivial.

 apply G_power; trivial.
 apply VN_in_grot; trivial.
Qed.


  Lemma G_ord_sup : forall x F,
  ext_fun x F ->
  x ∈ U ->
  (forall y, y ∈ x -> lt (F y) grot_ord) ->
  lt (osup x F) grot_ord.
intros.
assert (osup x F ∈ U).
 apply G_osup; intros; auto.
 apply grot_ord_intro; auto.
assert (isOrd (osup x F)).
 apply isOrd_osup; trivial.
 intros.
 apply isOrd_inv with grot_ord; auto.
apply grot_ord_inv; trivial.
Qed.

  Lemma G_regular : VN_regular_rel grot_ord.
red; intros.
rewrite VN_def; trivial.
pose (A := subset x (fun x' => exists y, R x' y)).
pose (F := fun x' => inter
       (subset grot_ord (fun z => exists2 y, R x' y & y ⊆ VN z))).
assert (oF : forall y, y ∈ A -> isOrd (F y)).
 intros.
 apply isOrd_inter; intros.
 apply subset_elim1 in H3; apply isOrd_inv with grot_ord; trivial.
assert (eF : ext_fun A F).
 red; red; intros.
 apply inter_morph.
 apply subset_morph; auto with *.
 red; intros.
 apply ex2_morph.
  red; intros.
  split; intros.
   apply (proj1 H) with x0 a; auto with *.
   apply subset_elim1 in H2; trivial.

   apply (proj1 H) with x' a; auto with *.
   rewrite <- H3.
   apply subset_elim1 in H2; trivial.

  red; intros.
  reflexivity.
exists (osup A F).
 apply grot_ord_inv.
  apply isOrd_osup; trivial.

  apply grot_ord_intro.  
  apply G_ord_sup; trivial.
   apply G_subset; trivial.
   apply VN_incl_grot; trivial.

   intros.
   assert (exists2 z, R y z & z ∈ VN grot_ord).
    unfold A in H2; rewrite subset_ax in H2; destruct H2.
    destruct H3.
    destruct H4.
    exists x1.
     apply (proj1 H) with x0 x1; auto with *.
     rewrite <- H3; trivial.

     apply H1 with x0; trivial.
     rewrite <- H3; trivial.
   destruct H3 as (z0, r0, ?).
   rewrite VN_def in H3; trivial; destruct H3.
   apply isOrd_plump with x0; auto.
   red; intros.
   apply inter_elim with (1:=H5).
   apply subset_intro; trivial.
   exists z0; trivial.

red; intros.
rewrite union_ax in H2; destruct H2.
apply ZFrepl.repl_elim in H3; trivial.
destruct H3.
assert (x0 ⊆ VN (F x1)).
 red; intros.
 apply VN_stable.
  intros.
  apply subset_elim1 in H6; eauto using isOrd_inv.

  generalize (H1 _ _ H3 H4); intros.
  rewrite VN_def in H6; eauto using isOrd_inv.
  destruct H6.
  apply inter_intro.
   clear x2 H6 H7.
   intros.
   rewrite replf_ax in H6.
   2:red;red;intros;apply VN_morph; trivial.
   destruct H6.
   rewrite H7; clear H7 y.
   apply subset_elim2 in H6.
   destruct H6.
   destruct H7.
   rewrite H6.
   assert (x0 == x4).
    apply (proj2 H) with x1; trivial.
   rewrite H9 in H5; auto.

   exists (VN x2).
   rewrite replf_ax.
   2:red;red;intros;apply VN_morph; trivial.
   exists x2; auto with *.
   apply subset_intro; trivial.
   exists x0; trivial.
apply H5 in H2.
rewrite VN_def in H2.
2:apply oF; apply subset_intro; eauto.
destruct H2.
rewrite VN_def.
2:apply isOrd_osup; auto.
exists x2; trivial.
revert H2; apply osup_intro; trivial.
apply subset_intro; trivial.
exists x0; trivial.
Qed.

  Lemma G_inaccessible : VN_inaccessible_rel grot_ord.
split;[split|]; auto.
 exact G_limit.

 exact G_regular.
Qed.

  Lemma G_VN_is_grot : grot_univ (VN grot_ord).
apply VN_grot; trivial.
exact G_inaccessible.
Qed.

End Grothendieck_Universe.

Hint Resolve grot_ord_intro isOrd_grot_ord isOrd_grot.
Hint Resolve G_VN_is_grot.