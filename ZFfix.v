Require Import ZF ZFrelations ZFnats ZFord.
Import IZF.

Section IterMonotone.

  Variable F : set -> set.
  Variable Fmono : Proper (incl_set ==> incl_set) F.

  Instance Fmono_morph: Proper (eq_set ==> eq_set) F.
do 2 red; intros.
apply eq_intro; intros.
 apply Fmono with x; trivial.
 red; intros.
 rewrite <- H; trivial.

 apply Fmono with y; trivial.
 red; intros.
 rewrite H; trivial.
Qed.
Hint Resolve Fmono_morph.

  Lemma TI_mono : increasing (TI F).
do 2 red; intros.
apply TI_elim in H2; intros; auto with *.
destruct H2.
apply TI_intro with x0; auto with *.
apply H1 in H2; trivial.
Qed.

  Lemma TI_incl : forall o, isOrd o ->
    forall o', lt o' o ->
    TI F o' \incl TI F o.
intros.
apply TI_mono; trivial; auto.
 apply isOrd_inv with o; trivial.
 red; intros; apply isOrd_trans with o'; trivial.
Qed.

  Lemma TI_mono_succ : forall o,
    isOrd o ->
    TI F (osucc o) == F (TI F o).
intros.
assert (Fext : ext_fun (osucc o) (fun o' => F (TI F o'))).
 generalize (isOrd_succ _ H); auto.
rewrite TI_eq; auto.
 apply eq_intro; intros.
  rewrite sup_ax in H0; trivial.
  destruct H0.
  apply Fmono with (TI F x); trivial.
  apply TI_mono; trivial.
   apply isOrd_inv with (osucc o); auto.
   apply olts_le; trivial.

 rewrite sup_ax; trivial.
 exists o; trivial.
 apply lt_osucc; trivial.
Qed.

  Lemma TI_mono_eq : forall o,
    isOrd o ->
    TI F o == sup o (fun o' => TI F (osucc o')).
intros.
rewrite TI_eq; auto.
apply sup_morph; auto with *.
red; intros.
rewrite <- TI_mono_succ.
 apply TI_morph.
 rewrite H1; reflexivity.

 apply isOrd_inv with o; trivial.
Qed.

  Lemma TI_pre_fix : forall fx o,
     isOrd o ->
     F fx \incl fx ->
     TI F o \incl fx.
intros.
induction H using isOrd_ind; intros.
red; intros.
apply H0.
elim TI_elim with (3:=H3); intros; auto with *.
apply Fmono with (TI F x); auto.
Qed.


Section BoundedOperator.

Variable A : set.
Hypothesis Ftyp : forall X, X \incl A -> F X \incl A.

Definition Ffix := subset A (fun a => exists2 o, isOrd o & a \in TI F o).

Lemma Ffix_inA : Ffix \incl A.
red; intros.
apply subset_elim1 in H; trivial.
Qed.

Lemma TI_Ffix : forall o, isOrd o -> TI F o \incl Ffix.
intros.
apply isOrd_ind with (2:=H); intros.
red; intros.
apply TI_elim in H3; auto with *.
destruct H3.
unfold Ffix.
apply subset_intro.
 revert z H4; apply Ftyp.
 transitivity Ffix; auto.
 apply Ffix_inA.
exists (osucc x); auto.
 apply isOrd_succ; apply isOrd_inv with y; trivial.

 rewrite TI_mono_succ; auto.
 apply isOrd_inv with y; trivial.
Qed.

Lemma Ffix_def : forall a, a \in Ffix <-> exists2 o, isOrd o & a \in TI F o.
unfold Ffix; intros.
rewrite subset_ax.
split; intros.
 destruct H.
 destruct H0.
 destruct H1.
 exists x0; trivial.
 rewrite H0; trivial.

 destruct H.
 split.
  apply Ffix_inA.
  revert a H0; apply TI_Ffix; trivial.

  exists a; auto with *.
  exists x; trivial.
Qed.

Definition Fsub x y :=
  forall o, isOrd o ->
  y \in TI F o -> exists2 o', lt o' o & x \in TI F o'.

Definition Ffix_rel a y :=
  forall R:set->set->Prop,
  Proper (eq_set ==> eq_set ==> iff) R ->
  (forall x g,
   let x' := subset A (fun a => Fsub a x) in
   ext_fun x' g ->
   (forall y, Fsub y x -> R y (g y)) ->
   R x (sup x' (fun y => osucc (g y)))) ->
  R a y.

  Instance Ffix_rel_morph :
    Proper (eq_set ==> eq_set ==> iff) Ffix_rel.
Admitted.
                                                                             
  Lemma Ffix_rel_intro : forall x g,
    let x' := subset A (fun a => Fsub a x) in
    ext_fun x' g ->
    (forall y, Fsub y x -> Ffix_rel y (g y)) ->
    Ffix_rel x (sup x' (fun y => osucc (g y))).
red; intros.
apply H2; trivial; intros.
apply H0; trivial.
Qed.                                                                         
                                                                             
  Lemma Ffix_rel_inv : forall x o,
    Ffix_rel x o ->
    let x' := subset A (fun a => Fsub a x) in
    exists2 g,
      ext_fun x' g /\
      (forall y, Fsub y x -> Ffix_rel y (g y)) &                 
      o == sup x' (fun y => osucc (g y)).
intros x o Fr.
apply (@proj2 (Ffix_rel x o)).
apply Fr; intros.
 admit. (* mrph *)

 split.
  apply Ffix_rel_intro; auto.
  intros.
  apply H0; trivial.

  exists g.
   split; intros; trivial.
   apply H0; trivial.

  apply sup_morph.
   reflexivity.

   red; intros; apply osucc_morph; apply H; trivial.
Qed.

  Lemma Ffix_rel_fun :
    forall x y, Ffix_rel x y -> forall y', Ffix_rel x y' -> y == y'.
intros x y H.
apply H; intros.
 admit. (* mrph *)
apply Ffix_rel_inv in H2; trivial.
destruct H2 as (g',(eg',Hg),eqy').
rewrite eqy'; clear y' eqy'.
apply sup_morph.
 reflexivity.

 red; intros.
 assert (Fsub x1 x0).
  apply subset_elim2 in H2; destruct H2.
  admit. (* uses Fsub morph *)
 apply osucc_morph; apply H1; trivial.
 rewrite <- (eg' _ _ H2 H3); auto.
Qed.

Require Import ZFrepl.

  Lemma Ffix_rel_def : forall o a, isOrd o -> a \in TI F o -> exists y, Ffix_rel a y.
intros o a oo; revert a; apply isOrd_ind with (2:=oo); intros.
clear o oo H0.
apply TI_elim in H2; trivial.
destruct H2.
assert (xo : isOrd x).
 apply isOrd_inv with y; trivial.
assert (forall z, Fsub z a -> uchoice_pred (fun o => Ffix_rel z o)).
 intros.
 destruct H1 with x z; trivial.
  rewrite <- TI_mono_succ in H2; auto.
  apply H3 in H2; auto.
  destruct H2.
  apply TI_mono with x0; auto. 
   apply isOrd_inv with (osucc x); auto.

   apply olts_le; auto.

  split; intros.
   rewrite <- H5; trivial.
  split; intros.
   exists x0; trivial.
  apply Ffix_rel_fun with z; trivial.
exists (sup (subset A (fun b => Fsub b a))
         (fun b => osucc (uchoice (fun o => Ffix_rel b o)))).
apply Ffix_rel_intro; trivial.
 admit. (*ext*)
intros.
apply uchoice_def; auto.
Qed.

  Lemma Ffix_rel_choice_pred : forall o a, isOrd o -> a \in TI F o ->
    uchoice_pred (fun o => Ffix_rel a o).
split; intros.
 rewrite <- H1; trivial.
split; intros.
 apply Ffix_rel_def with o; trivial.
apply Ffix_rel_fun with a; trivial.
Qed.

  Definition F_assign a := uchoice (fun o => Ffix_rel a o).

  Lemma F_a_eqn : forall a o,
    isOrd o ->
    a \in TI F o ->
    F_assign a ==
    sup (subset A (fun b => Fsub b a)) (fun b => osucc (F_assign b)).
intros.
unfold F_assign.
generalize (uchoice_def _ (Ffix_rel_choice_pred _ _ H H0)); intro.
apply Ffix_rel_inv in H1; auto.
destruct H1.
destruct H1.
rewrite H2.
apply sup_morph; auto with *.
red; intros.
apply osucc_morph.
assert (Fsub x' a).
 apply subset_elim2 in H4; destruct H4.
 admit. (* Fsub mrph... *)
assert (x' \in TI F o).
 apply H6 in H0; auto.
 destruct H0.
 apply TI_incl with x1; auto.
generalize (uchoice_def _ (Ffix_rel_choice_pred _ _ H H7)); intro.
specialize H3 with (1:=H6).
rewrite <- Ffix_rel_fun with (1:=H3) (2:=H8).
apply H1; trivial.
Qed.

  Lemma F_a_ord : forall a, a \in Ffix -> isOrd (F_assign a).
intros.
rewrite Ffix_def in H; destruct H.
revert a H0; apply isOrd_ind with (2:=H); intros.
rewrite F_a_eqn with (o:=y); auto.
apply isOrd_supf.
 admit. (*ext *)

 intros.
 apply isOrd_succ.
 apply subset_elim2 in H4; destruct H4.
 apply H5 in H3; trivial.
 destruct H3.
 rewrite <- H4 in H6; eauto.
Qed.

Hint Resolve F_a_ord.

  Hypothesis F_intro : forall w,
    isOrd w ->
    forall a, a \in TI F w ->
    forall o, isOrd o ->
    (forall y, Fsub y a -> y \in TI F o) ->
    a \in F (TI F o).
(*
intros w ow.
apply isOrd_ind with (2:=ow); intros.

unfold Fsub in H0.

rewrite <- TI_mono_succ; auto.
rewrite TI_eq; auto.
unfold TI.
*)

  Lemma F_a_tot : forall a,
   a \in Ffix ->
   a \in TI F (osucc (F_assign a)).
intros.
rewrite Ffix_def in H; destruct H.
revert a H0; apply isOrd_ind with (2:=H); intros.
assert (forall y, Fsub y a -> y \in TI F (F_assign a)).
 intros.
 red in H4.
 destruct H4 with (1:=H0)(2:=H3).
 assert (xo : isOrd x0).
  apply isOrd_inv with y; trivial.
 assert (y0 \in TI F (osucc (F_assign y0))).
  apply H2 with x0; trivial.
 revert H7; apply TI_mono; auto.
  apply F_a_ord; rewrite Ffix_def; exists y; auto.

  apply isOrd_succ; apply F_a_ord; rewrite Ffix_def; exists x0; trivial.

  red; intros.
  rewrite F_a_eqn with (o:=y); auto.
  rewrite sup_ax.
  2:admit.
  exists y0; auto.
  apply subset_intro; trivial.
   admit.
rewrite TI_mono_succ; auto.
2:apply F_a_ord; rewrite Ffix_def; exists y; trivial.
apply F_intro with y; trivial.
apply F_a_ord; rewrite Ffix_def; exists y; trivial.
Qed.

  Definition Ffix_ord :=
    sup Ffix (fun a => osucc (F_assign a)).

  Lemma Ffix_o_o : isOrd Ffix_ord.
apply isOrd_supf; auto.
admit. (* ext *)
Qed.
Hint Resolve Ffix_o_o.

  Lemma Ffix_post : forall a,
   a \in Ffix ->
   a \in TI F Ffix_ord.
intros.
apply TI_intro with (F_assign a); auto.
 unfold Ffix_ord; rewrite sup_ax.
 2:admit. (* ext*)
 exists a; trivial.
 apply lt_osucc; auto.

 rewrite <- TI_mono_succ; auto.
 apply F_a_tot; trivial.
Qed.

  Lemma Ffix_eqn : Ffix == F Ffix.
apply eq_intro; intros.
rewrite Ffix_def in H; destruct H.
apply Fmono with (TI F x).
 apply TI_Ffix; trivial.

 rewrite <- TI_mono_succ; auto.
 revert H0; apply TI_incl; auto.

 assert (z \in TI F (osucc Ffix_ord)).
  rewrite TI_mono_succ; auto.
  revert H; apply Fmono.
  red; intros; apply Ffix_post; trivial.
 rewrite Ffix_def; exists (osucc Ffix_ord); auto.
Qed.




(* Pb with limit ordinals... *)
(*
Definition Fsub x y :=
  forall o, isOrd o ->
  y \in F (TI F o) -> x \in TI F o.

Definition Ffix_rel a y :=
  forall R:set->set->Prop,
  Proper (eq_set ==> eq_set ==> iff) R ->
  (forall x g,
   let x' := subset A (fun a => Fsub a x) in
   ext_fun x' g ->
   (forall y, Fsub y x -> R y (g y)) ->
   R x (sup x' (fun y => osucc (g y)))) ->
  R a y.

  Instance Ffix_rel_morph :
    Proper (eq_set ==> eq_set ==> iff) Ffix_rel.
Admitted.
                                                                             
  Lemma Ffix_rel_intro : forall x g,
    let x' := subset A (fun a => Fsub a x) in
    ext_fun x' g ->
    (forall y, Fsub y x -> Ffix_rel y (g y)) ->
    Ffix_rel x (sup x' (fun y => osucc (g y))).
red; intros.
apply H2; trivial; intros.
apply H0; trivial.
Qed.                                                                         
                                                                             
  Lemma Ffix_rel_inv : forall x o,
    Ffix_rel x o ->
    let x' := subset A (fun a => Fsub a x) in
    exists2 g,
      ext_fun x' g /\
      (forall y, Fsub y x -> Ffix_rel y (g y)) &                 
      o == sup x' (fun y => osucc (g y)).
intros x o Fr.
apply (@proj2 (Ffix_rel x o)).
apply Fr; intros.
 admit. (* mrph *)

 split.
  apply Ffix_rel_intro; auto.
  intros.
  apply H0; trivial.

  exists g.
   split; intros; trivial.
   apply H0; trivial.

  apply sup_morph.
   reflexivity.

   red; intros; apply osucc_morph; apply H; trivial.
Qed.

  Lemma Ffix_rel_fun :
    forall x y, Ffix_rel x y -> forall y', Ffix_rel x y' -> y == y'.
intros x y H.
apply H; intros.
 admit. (* mrph *)
apply Ffix_rel_inv in H2; trivial.
destruct H2 as (g',(eg',Hg),eqy').
rewrite eqy'; clear y' eqy'.
apply sup_morph.
 reflexivity.

 red; intros.
 assert (Fsub x1 x0).
  apply subset_elim2 in H2; destruct H2.
  admit. (* uses Fsub morph *)
 apply osucc_morph; apply H1; trivial.
 rewrite <- (eg' _ _ H2 H3); auto.
Qed.

Require Import ZFrepl.

  Lemma Ffix_rel_def : forall o a, isOrd o -> a \in TI F o -> exists y, Ffix_rel a y.
intros o a oo; revert a; apply isOrd_ind with (2:=oo); intros.
clear o oo H0.
apply TI_elim in H2; trivial.
destruct H2.
assert (forall z, Fsub z a -> uchoice_pred (fun o => Ffix_rel z o)).
 intros.
 assert (H3' := H3 _ (isOrd_inv _ _ H H0) H2).
 destruct H1 with x z; trivial.
 split; intros.
  rewrite <- H5; trivial.
 split; intros.
  exists x0; trivial.
 apply Ffix_rel_fun with z; trivial.
exists (sup (subset A (fun b => Fsub b a))
         (fun b => osucc (uchoice (fun o => Ffix_rel b o)))).
apply Ffix_rel_intro; trivial.
 admit. (*ext*)
intros.
apply uchoice_def; auto.
Qed.

  Lemma Ffix_rel_choice_pred : forall o a, isOrd o -> a \in TI F o ->
    uchoice_pred (fun o => Ffix_rel a o).
split; intros.
 rewrite <- H1; trivial.
split; intros.
 apply Ffix_rel_def with o; trivial.
apply Ffix_rel_fun with a; trivial.
Qed.

  Definition F_assign a := uchoice (fun o => Ffix_rel a o).

  Lemma F_a_eqn : forall a o,
    isOrd o ->
    a \in TI F o ->
    F_assign a ==
    sup (subset A (fun b => Fsub b a)) (fun b => osucc (F_assign b)).
intros.
unfold F_assign.
generalize (uchoice_def _ (Ffix_rel_choice_pred _ _ H H0)); intro.
apply Ffix_rel_inv in H1; auto.
destruct H1.
destruct H1.
rewrite H2.
apply sup_morph; auto with *.
red; intros.
apply osucc_morph.
assert (Fsub x' a).
 apply subset_elim2 in H4; destruct H4.
 admit. (* Fsub mrph... *)
assert (x' \in TI F o).
 apply H6; trivial.
 rewrite <- TI_mono_succ; auto.
 revert H0; apply TI_incl; auto.
generalize (uchoice_def _ (Ffix_rel_choice_pred _ _ H H7)); intro.
specialize H3 with (1:=H6).
rewrite <- Ffix_rel_fun with (1:=H3) (2:=H8).
apply H1; trivial.
Qed.

  Lemma F_a_ord : forall a, a \in Ffix -> isOrd (F_assign a).
intros.
rewrite Ffix_def in H; destruct H.
revert a H0; apply isOrd_ind with (2:=H); intros.
rewrite F_a_eqn with (o:=y); auto.
apply isOrd_supf.
 admit. (*ext *)

 intros.
 apply TI_elim in H3; trivial.
 destruct H3.
 apply isOrd_succ.
 apply H2 with x1; trivial.
 apply subset_elim2 in H4; destruct H4.
 rewrite H4; apply H6; trivial.
 apply isOrd_inv with y; trivial.
Qed.

Hint Resolve F_a_ord.

  Lemma F_intro : forall o a,
    isOrd o ->
    (forall y, Fsub y a -> y \in TI F o) ->
    a \in F (TI F o).
intros.
unfold Fsub in H0.

rewrite <- TI_mono_succ; auto.
rewrite TI_eq; auto.
unfold TI.

  Lemma F_a_tot : forall a,
   a \in Ffix ->
   a \in TI F (osucc (F_assign a)).
intros.
rewrite Ffix_def in H; destruct H.
revert a H0; apply isOrd_ind with (2:=H); intros.
(*setoid_replace (TI F (osucc (F_assign a))) with
(TI F (osucc (sup (subset A (fun b => Fsub b a)) (fun b => osucc (F_assign b))))).
2:apply TI_morph.
2:apply osucc_morph.
2:apply F_a_eqn with y; trivial.*)
assert (forall y, Fsub y a -> y \in TI F (F_assign a)).
 intros.
 apply TI_elim in H3; trivial.
 destruct H3.
 assert (xo : isOrd x0).
  apply isOrd_inv with y; trivial.
 rewrite <- TI_mono_succ in H5; auto.
 assert (y0 \in TI F (osucc (F_assign y0))).
  apply H2 with x0; trivial.
  apply H4; trivial.
  rewrite <- TI_mono_succ; auto.
 revert H6; apply TI_mono; auto.
  apply F_a_ord; rewrite Ffix_def; exists (osucc x0); auto.

  apply isOrd_succ; apply F_a_ord; rewrite Ffix_def; exists x0; trivial.
  apply H4; auto.
  rewrite <- TI_mono_succ; auto.

  red; intros.
  rewrite F_a_eqn with (o:=osucc x0); auto.
  rewrite sup_ax.
  2:admit.
  exists y0; auto.
  apply subset_intro; trivial.
  admit.
intros.
rewrite TI_mono_succ; auto.
apply stp; auto.
 apply F_a_ord; rewrite Ffix_def; exists y; trivial.
 apply F_a_ord; rewrite Ffix_def; exists y; trivial.

apply TI_intro with (F_assign a); auto.
 apply isOrd_succ; apply F_a_ord.
 rewrite Ffix_def; exists y; trivial.

 apply lt_osucc.



assert (forall y, Fsub y a ->
y \in TI F (osucc (osucc (F_assign y)))).
 intros.
apply TI_elim in H3; trivial.
destruct H3.
rewrite <- TI_mono_succ in H5; auto.
2:apply isOrd_inv with y; trivial.
assert (y0 \in TI F (osucc (F_assign y0))).
 apply H2 with x0; trivial.
 rewrite TI_mono_succ in H5; auto.
 2:apply isOrd_inv with y; trivial.
 apply H4; trivial.
 apply isOrd_inv with y; trivial.
admit.
rewrite TI_eq; trivial.
rewrite sup_ax.

2:apply F_a_ord; rewrite Ffix_def; eauto.
apply TI_elim in H3; trivial.
destruct H3.

assert (a \in F (sup (subset A (fun b => Fsub b a)) (fun b => TI F (osucc (F_assign b))))).
 admit.
revert H5; apply Fmono.
red; intros.
rewrite sup_ax in H5.
2:admit.
destruct H5.
rewrite TI_mono_succ in H6; auto.
2:admit.
assert (Fsub x1 a).
 apply subset_elim2 in H5; destruct H5.
 admit.
red in H7.
apply H7 in H6.


 rewrite sup_ax.

revert H4; apply Fmono; red; intros.

apply W_ind with (3:=H); intros.
 admit. (* mrph *)
rewrite TI_mono_succ; trivial.
 2:apply W_a_ord; apply (TI_Ffix (osucc o')); auto.
 2:apply Wsup_typ; trivial.
 apply Wf_intro; trivial.
 rewrite cc_eta_eq with (1:=H2).
 apply cc_prod_intro.
  admit. (*ext*)
  auto.

  intros.
  apply TI_intro with (W_assign (cc_app f x0)).
   apply Fmono_morph; trivial.

   apply W_a_ord.
   apply (TI_Ffix (osucc o')); auto.
   apply Wsup_typ; trivial.

   unfold W_assign at 2.
   rewrite W_eqn2 with (o:=o'); trivial.
    rewrite sup_ax.
    2:admit. (* ext*)
    exists x0; trivial.
    apply lt_osucc.
    apply W_a_ord.
    rewrite Ffix_def.
    exists o'; auto.
    apply cc_prod_elim with (1:=H2); trivial.

    admit. (* ext *)

   rewrite <- TI_mono_succ; auto.
   apply W_a_ord.
   rewrite Ffix_def; exists o'; trivial.
   apply cc_prod_elim with (1:=H2); trivial.
Qed.

  Definition W_ord :=
    sup W (fun a => osucc (W_assign a)).

  Lemma W_o_o : isOrd W_ord.
apply isOrd_supf; auto.
admit. (* ext *)
Qed.
Hint Resolve W_o_o.
Hint Resolve Fmono_morph.

  Lemma W_post : forall a,
   a \in W ->
   a \in TI Wf W_ord.
intros.
apply TI_intro with (W_assign a); auto.
 unfold W_ord; rewrite sup_ax.
 2:admit. (* ext*)
 exists a; trivial.
 apply lt_osucc; auto.

 rewrite <- TI_mono_succ; auto.
 apply W_ord_tot; trivial.
Qed.

  Lemma W_eqn : W == Wf W.
apply eq_intro; intros.
rewrite Ffix_def in H; destruct H.
apply Wf_mono with (TI Wf x).
 apply TI_Ffix; trivial.

 rewrite <- TI_mono_succ; auto.
 revert H0; apply TI_incl; auto.

 assert (z \in TI Wf (osucc W_ord)).
  rewrite TI_mono_succ; auto.
  revert H; apply Wf_mono.
  red; intros; apply W_post; trivial.
 rewrite Ffix_def; exists (osucc W_ord); auto.
Qed.

End WithoutKnaster.
*)


End BoundedOperator.


End IterMonotone.


Section KnasterTarski.

Variable A : set.
Variable F : set -> set.

Record fp_props : Prop :=
 { typ : forall x, x \incl A -> F x \incl A;
(*   morph : morph1 F;*)
   mono : forall x x',
     x' \incl A -> x \incl x' -> F x \incl F x'}.

Hypothesis Ffix : fp_props.

Lemma fx_mrph : forall x x', x \incl A -> x == x' -> F x == F x'.
intros.
apply eq_intro; intros.
 revert z H1; apply mono; trivial.
 rewrite <- H0; trivial.
 rewrite H0; auto with *.

 revert z H1; apply mono; trivial.
 rewrite H0; auto with *.
Qed.

Let Ftyp := Ffix.(typ).
Let Fmono := Ffix.(mono).

Definition is_lfp x :=
  F x == x /\ forall y, y \incl A -> F y \incl y -> x \incl y.

Definition pre_fix x := x \incl F x.
Definition post_fix x := F x \incl x.

Lemma post_fix_A : post_fix A.
red; intros.
apply Ftyp; auto with *.
Qed.

Definition M' := subset (power A) post_fix.

Lemma member_A : A \in M'.
unfold M'.
apply subset_intro.
 apply power_intro; auto.

 apply post_fix_A.
Qed.

Lemma post_fix1 : forall x, x \in M' -> F x \incl x.
unfold M'; intros.
elim subset_elim2 with (1:=H); intros.
red; intros.
red in H1. red in H1.
rewrite H0.
apply subset_elim1 in H.
apply H1.
apply Fmono with x; trivial.
 rewrite <- H0; red; intros.
 apply power_elim with x; trivial.

 rewrite H0; auto with *.
Qed.

Definition least_fp := inter M'.

Lemma lfp_typ : least_fp \incl A.
unfold least_fp, M'.
red; intros.
apply inter_elim with (1:=H).
apply subset_intro.
 apply power_intro; auto.

 apply post_fix_A.
Qed.

Lemma lower_bound : forall x, x \in M' -> least_fp \incl x.
unfold least_fp, M'; red; intros.
apply inter_elim with (1:=H0); auto.
Qed.

Lemma post_fix2 : forall x, x \in M' -> F least_fp \incl F x.
intros.
apply Fmono.
 apply subset_elim1 in H.
 red; intros.
 apply power_elim with x; trivial.

 apply lower_bound; trivial.
Qed.


Lemma post_fix_lfp : post_fix least_fp.
red; red; intros.
unfold least_fp.
apply inter_intro.
2:exists A; apply member_A.
intros.
apply post_fix1 with (1:=H0).
apply post_fix2 with (1:=H0).
trivial.
Qed.

Lemma incl_f_lfp : F least_fp \in M'.
unfold M'; intros.
apply subset_intro.
 apply power_intro.
 apply Ftyp.
 apply lfp_typ.

 red; intros.
 apply Fmono.
  apply lfp_typ.

  apply post_fix_lfp; trivial.
Qed.

Lemma knaster_tarski : is_lfp least_fp.
split.
 apply eq_intro; intros.
  apply (post_fix_lfp z H); trivial.

  apply (lower_bound (F least_fp)); trivial.
  apply incl_f_lfp; trivial.

 intros.
 apply lower_bound.
 unfold M'.
 apply subset_intro; trivial.
 apply power_intro; trivial.
Qed.
(*
  Lemma TI_incl_lstfix : forall o,
     isOrd o ->
     TI F o \incl least_fp.
intros.
induction H using isOrd_ind; intros.
red; intros.
apply TI_elim in H2; auto.
2:admit.
destruct H2.
apply post_fix_lfp.
revert z H3.
apply Fmono; auto.
apply lfp_typ.
Qed.

  Definition lstfx' :=
    subset A (fun x => exists2 o, isOrd o & x \in TI F o).

  Lemma pofx' : post_fix lstfx'.
red; red; intros.

unfodl lstfx' in *.
*)

End KnasterTarski.

