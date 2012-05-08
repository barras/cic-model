Require Import ZF ZFrelations ZFnats ZFord.

(** Transfinite iteration of a monotonic operator
 *)

(** * Elementary properties *)
Section IterMonotone.

  Variable F : set -> set.
  Variable Fmono : Proper (incl_set ==> incl_set) F.

  Let Fm := Fmono_morph _ Fmono.

  Lemma TI_mono : increasing (TI F).
do 2 red; intros.
apply TI_elim in H2; intros; auto with *.
destruct H2.
apply TI_intro with x0; auto with *.
apply H1 in H2; trivial.
Qed.

  Lemma TI_incl : forall o, isOrd o ->
    forall o', o' < o ->
    TI F o' ⊆ TI F o.
intros.
apply TI_mono; trivial; auto.
apply isOrd_inv with o; trivial.
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
 apply TI_morph; auto.
 rewrite H1; reflexivity.

 apply isOrd_inv with o; trivial.
Qed.

  Lemma TI_pre_fix : forall fx o,
     isOrd o ->
     F fx ⊆ fx ->
     TI F o ⊆ fx.
intros.
induction H using isOrd_ind; intros.
red; intros.
apply H0.
elim TI_elim with (3:=H3); intros; auto with *.
apply Fmono with (TI F x); auto.
Qed.


(** * Case of a bounded monotonic operator 
 *)
Section BoundedOperator.

Variable A : set.
Hypothesis Ftyp : forall X, X ⊆ A -> F X ⊆ A.

(** The union of all stages. We will show it is a fixpoint. *)

Definition Ffix := subset A (fun a => exists2 o, isOrd o & a ∈ TI F o).

Lemma Ffix_inA : Ffix ⊆ A.
red; intros.
apply subset_elim1 in H; trivial.
Qed.

Lemma TI_Ffix : forall o, isOrd o -> TI F o ⊆ Ffix.
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

Lemma Ffix_def : forall a, a ∈ Ffix <-> exists2 o, isOrd o & a ∈ TI F o.
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

(***)
(*
Definition frules a :=
  subset (power Ffix)
   (fun X => a ∈ F X /\ forall Y, Y ⊆ X -> a ∈ F Y -> X ⊆ Y).

Instance frules_morph : morph1 frules.
Admitted.

(*
Lemma fsub_elim : forall x y o,
  isOrd o ->
  y ∈ TI F o ->
  x ∈ frules y ->
  exists2 o', lt o' o & x ⊆ TI F o'.
intros.
unfold frules in H1; rewrite subset_ax in H1.
destruct H1 as (?,(x',?,?)).
apply TI_elim in H0; trivial.
destruct H0.
exists x0; trivial.
destruct H3.
rewrite H2 in H1|-*;clear x H2; rename x' into x.
transitivity (inter2 x (TI F x0)).
2:apply inter2_incl2.
apply H5.
 apply inter2_incl1.

 

rewrite H2; apply H5; trivial.
red; intros.


rewrite H2; apply H3; trivial.
apply TI_Ffix.
apply isOrd_inv with o; trivial.
Qed.
*)

Section Iter.

Variable G : (set -> set) -> set -> set.
Hypothesis Gm : forall x x' g g',
  x ∈ Ffix ->
  eq_fun (frules x) g g' ->
  x == x' -> G g x == G g' x'.

Definition Ffix_rel a y :=
  forall R:set->set->Prop,
  Proper (eq_set ==> eq_set ==> iff) R ->
  (forall x g,
   ext_fun (frules x) g ->
   (forall y, y ∈ frules x -> R y (g y)) ->
   R x (G g x)) ->
  R a y.

  Instance Ffix_rel_morph :
    Proper (eq_set ==> eq_set ==> iff) Ffix_rel.
apply morph_impl_iff2; auto with *.
do 5 red; intros.
rewrite <- H; rewrite <- H0; apply H1; trivial.
Qed.


  Lemma Ffix_rel_intro : forall x g,
    ext_fun (frules x) g ->
    (forall y, y ∈ frules x -> Ffix_rel y (g y)) ->
    Ffix_rel x (G g x).
red; intros.
apply H2; trivial; intros.
apply H0; trivial.
Qed.

  Lemma Ffix_rel_inv : forall x o,
    x ∈ Ffix ->
    Ffix_rel x o ->
    exists2 g,
      ext_fun (frules x) g /\
      (forall y, y ∈ frules x -> Ffix_rel y (g y)) &
      o == G g x.
intros x o xA Fr.
apply (@proj2 (Ffix_rel x o)).
revert xA.
apply Fr; intros.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 rewrite <- H in xA.
 destruct (H1 xA) as (?,(g,(?,?),?)); clear H1.
 split;[|exists g].
  rewrite <- H; rewrite <- H0; trivial.

  split; intros.
   red; red; intros; apply H3; trivial.
   rewrite H; trivial.

   rewrite <- H in H1; auto.

  rewrite <- H0; rewrite H5.
  apply Gm; auto with *.

 split.
  apply Ffix_rel_intro; auto.
  intros.
  apply H0; trivial.
  apply Ffix_fsub_inv with x0; trivial.

  exists g.
   split; intros; trivial.
   apply H0; trivial.
   apply Ffix_fsub_inv with x0; trivial.

  apply Gm; auto with *.
Qed.

  Lemma Ffix_rel_fun :
    forall x y, Ffix_rel x y ->
    forall y', Ffix_rel x y' -> x ∈ Ffix -> y == y'.
intros x y H.
apply H; intros.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 rewrite <- H1; rewrite <- H0 in H3,H4; auto.
apply Ffix_rel_inv in H2; trivial.
destruct H2 as (g',(eg',Hg),eqy').
rewrite eqy'; clear y' eqy'.
apply Gm; auto with *.
red; intros.
rewrite <- (eg' _ _ H2 H4); auto.
apply H1; auto.
apply Ffix_fsub_inv with x0; trivial.
Qed.

Require Import ZFrepl.

  Lemma Ffix_rel_def : forall o a, isOrd o -> a ∈ TI F o -> exists y, Ffix_rel a y.
intros o a oo; revert a; apply isOrd_ind with (2:=oo); intros.
clear o oo H0.
apply TI_elim in H2; trivial.
destruct H2.
assert (xo : isOrd x).
 apply isOrd_inv with y; trivial.
assert (forall z, z ∈ fsub a -> uchoice_pred (fun o => Ffix_rel z o)).
 intros.
 destruct H1 with x z; auto.
  apply subset_elim2 in H3; destruct H3.
  rewrite H3; apply H4; trivial.
  apply TI_Ffix; trivial.

  split; intros.
   rewrite <- H5; trivial.
  split; intros.
   exists x0; trivial.
  apply Ffix_rel_fun with z; trivial.
  apply Ffix_fsub_inv with a; trivial.
  apply TI_Ffix with (o:=y); trivial.
  apply TI_intro with x; trivial.
exists (G (fun b => uchoice (fun o => Ffix_rel b o)) a).
apply Ffix_rel_intro; trivial.
 red; red; intros.
 apply uchoice_morph_raw.
 apply Ffix_rel_morph; trivial.
intros.
apply uchoice_def; auto.
Qed.

  Lemma Ffix_rel_choice_pred : forall o a, isOrd o -> a ∈ TI F o ->
    uchoice_pred (fun o => Ffix_rel a o).
split; intros.
 rewrite <- H1; trivial.
split; intros.
 apply Ffix_rel_def with o; trivial.
apply Ffix_rel_fun with a; trivial.
revert H0; apply TI_Ffix; trivial.
Qed.

  Definition Fix_rec a := uchoice (fun o => Ffix_rel a o).
*)

(***)

(** Subterms of [a] *)
Definition fsub a :=
  subset Ffix (fun b => forall X, X ⊆ Ffix -> a ∈ F X -> b ∈ X).

Instance fsub_morph : morph1 fsub.
unfold fsub; do 2 red; intros.
apply subset_morph; auto with *.
red; intros.
apply fa_morph; intro X.
rewrite H; reflexivity.
Qed.

Lemma fsub_elim : forall x y o,
  isOrd o ->
  y ∈ TI F o ->
  x ∈ fsub y ->
  exists2 o', lt o' o & x ∈ TI F o'.
intros.
unfold fsub in H1; rewrite subset_ax in H1.
destruct H1 as (?,(x',?,?)).
apply TI_elim in H0; auto.
destruct H0.
exists x0; trivial.
rewrite H2; apply H3; trivial.
apply TI_Ffix.
apply isOrd_inv with o; trivial.
Qed.

Lemma Ffix_fsub_inv : forall x y,
  x ∈ Ffix ->
  y ∈ fsub x ->
  y ∈ Ffix.
intros.
apply subset_elim1 in H0; trivial.
Qed.

(** Functions defined by recursion on subterms *)
Section Iter.

Variable G : (set -> set) -> set -> set.
Hypothesis Gm : forall x x' g g',
  x ∈ Ffix ->
  eq_fun (fsub x) g g' ->
  x == x' -> G g x == G g' x'.

Definition Ffix_rel a y :=
  forall R:set->set->Prop,
  Proper (eq_set ==> eq_set ==> iff) R ->
  (forall x g,
   ext_fun (fsub x) g ->
   (forall y, y ∈ fsub x -> R y (g y)) ->
   R x (G g x)) ->
  R a y.

  Instance Ffix_rel_morph :
    Proper (eq_set ==> eq_set ==> iff) Ffix_rel.
apply morph_impl_iff2; auto with *.
do 5 red; intros.
rewrite <- H; rewrite <- H0; apply H1; trivial.
Qed.


  Lemma Ffix_rel_intro : forall x g,
    ext_fun (fsub x) g ->
    (forall y, y ∈ fsub x -> Ffix_rel y (g y)) ->
    Ffix_rel x (G g x).
red; intros.
apply H2; trivial; intros.
apply H0; trivial.
Qed.

  Lemma Ffix_rel_inv : forall x o,
    x ∈ Ffix ->
    Ffix_rel x o ->
    exists2 g,
      ext_fun (fsub x) g /\
      (forall y, y ∈ fsub x -> Ffix_rel y (g y)) &
      o == G g x.
intros x o xA Fr.
apply (@proj2 (Ffix_rel x o)).
revert xA.
apply Fr; intros.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 rewrite <- H in xA.
 destruct (H1 xA) as (?,(g,(?,?),?)); clear H1.
 split;[|exists g].
  rewrite <- H; rewrite <- H0; trivial.

  split; intros.
   red; red; intros; apply H3; trivial.
   rewrite H; trivial.

   rewrite <- H in H1; auto.

  rewrite <- H0; rewrite H5.
  apply Gm; auto with *.

 split.
  apply Ffix_rel_intro; auto.
  intros.
  apply H0; trivial.
  apply subset_elim1 in H1; trivial.

  exists g.
   split; intros; trivial.
   apply H0; trivial.
   apply subset_elim1 in H1; trivial.

  apply Gm; auto with *.
Qed.

  Lemma Ffix_rel_fun :
    forall x y, Ffix_rel x y ->
    forall y', Ffix_rel x y' -> x ∈ Ffix -> y == y'.
intros x y H.
apply H; intros.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 rewrite <- H1; rewrite <- H0 in H3,H4; auto.
apply Ffix_rel_inv in H2; trivial.
destruct H2 as (g',(eg',Hg),eqy').
rewrite eqy'; clear y' eqy'.
apply Gm; auto with *.
red; intros.
rewrite <- (eg' _ _ H2 H4); auto.
apply H1; auto.
apply subset_elim1 in H2; trivial.
Qed.

Require Import ZFrepl.

  Lemma Ffix_rel_def : forall o a, isOrd o -> a ∈ TI F o -> exists y, Ffix_rel a y.
intros o a oo; revert a; apply isOrd_ind with (2:=oo); intros.
clear o oo H0.
apply TI_elim in H2; auto.
destruct H2.
assert (xo : isOrd x).
 apply isOrd_inv with y; trivial.
assert (forall z, z ∈ fsub a -> uchoice_pred (fun o => Ffix_rel z o)).
 intros.
 destruct H1 with x z; auto.
  apply subset_elim2 in H3; destruct H3.
  rewrite H3; apply H4; trivial.
  apply TI_Ffix; trivial.

  split; intros.
   rewrite <- H5; trivial.
  split; intros.
   exists x0; trivial.
  apply Ffix_rel_fun with z; trivial.
  apply subset_elim1 in H3; trivial.
exists (G (fun b => uchoice (fun o => Ffix_rel b o)) a).
apply Ffix_rel_intro; trivial.
 red; red; intros.
 apply uchoice_morph_raw.
 apply Ffix_rel_morph; trivial.
intros.
apply uchoice_def; auto.
Qed.

  Lemma Ffix_rel_choice_pred : forall o a, isOrd o -> a ∈ TI F o ->
    uchoice_pred (fun o => Ffix_rel a o).
split; intros.
 rewrite <- H1; trivial.
split; intros.
 apply Ffix_rel_def with o; trivial.
apply Ffix_rel_fun with a; trivial.
revert H0; apply TI_Ffix; trivial.
Qed.

(** The recursion operator *)
  Definition Fix_rec a := uchoice (fun o => Ffix_rel a o).

  Lemma Fr_eqn : forall a o,
    isOrd o ->
    a ∈ TI F o ->
    Fix_rec a == G Fix_rec a.
intros.
unfold Fix_rec.
generalize (uchoice_def _ (Ffix_rel_choice_pred _ _ H H0)); intro.
apply Ffix_rel_inv in H1; auto.
 2:revert H0; apply TI_Ffix; trivial.
destruct H1.
destruct H1.
rewrite H2.
apply Gm; auto with *.
 revert H0; apply TI_Ffix; trivial.
red; intros.
rewrite H5 in H4.
assert (x' ∈ TI F o).
 destruct fsub_elim with (2:=H0) (3:=H4); trivial.
 apply TI_incl with x1; auto.
generalize (uchoice_def _ (Ffix_rel_choice_pred _ _ H H6)); intro.
specialize H3 with (1:=H4).
rewrite <- Ffix_rel_fun with (1:=H3) (2:=H7).
2:apply subset_elim1 in H4; trivial.
rewrite <- H5 in H4.
apply H1; trivial.
Qed.
(*
  Lemma Fix_rec_typ U1 U2 a :
    Ffix ⊆ U1 ->
    (forall x g, ext_fun (fsub x) g -> x ∈ U1 -> (forall y, y ∈ fsub x -> g y ∈ U2) -> G g x ∈ U2) ->
    a ∈ Ffix ->
    Fix_rec a ∈ U2.
intros.
rewrite Ffix_def in H1; destruct H1.
revert a H2.
induction H1 using isOrd_ind; intros.
rewrite Fr_eqn with (2:=H4); trivial.
apply H0.
 do 2 red; intros; apply uchoice_morph_raw.
 red; intros.
 apply Ffix_rel_morph; trivial.

 apply H.
 rewrite Ffix_def; eauto.

 intros.
 apply fsub_elim with (o:=y) in H5; trivial.
 destruct H5.
 apply H3 with x0; trivial.
Qed.
*)
  Lemma Fix_rec_typ U2 a :
    (forall x g, ext_fun (fsub x) g -> x ∈ Ffix -> (forall y, y ∈ fsub x -> g y ∈ U2) -> G g x ∈ U2) ->
    a ∈ Ffix ->
    Fix_rec a ∈ U2.
intros.
rewrite Ffix_def in H0; destruct H0.
revert a H1.
induction H0 using isOrd_ind; intros.
rewrite Fr_eqn with (2:=H3); trivial.
apply H.
 do 2 red; intros; apply uchoice_morph_raw.
 red; intros.
 apply Ffix_rel_morph; trivial.

 apply TI_Ffix with y; trivial.

 intros.
 apply fsub_elim with (o:=y) in H4; trivial.
 destruct H4.
 apply H2 with x0; trivial.
Qed.

End Iter.

  Definition F_a g x := osup (fsub x) (fun a => osucc (g a)).

  Lemma F_a_morph : forall x x' g g',
    eq_fun (fsub x) g g' ->
    x == x' -> F_a g x == F_a g' x'.
unfold F_a; intros.
apply osup_morph.
 rewrite H0; reflexivity.

 red; intros.
 apply osucc_morph; apply H; trivial.
Qed.
Hint Resolve F_a_morph.


  Lemma Fe1 : forall X, ext_fun X (fun b => osucc (Fix_rec F_a b)).
red; red; intros.
apply osucc_morph.
apply uchoice_morph_raw.
apply Ffix_rel_morph; trivial.
Qed.
Hint Resolve Fe1.

  Lemma F_a_ord : forall a, a ∈ Ffix -> isOrd (Fix_rec F_a a).
intros.
rewrite Ffix_def in H; destruct H.
revert a H0; apply isOrd_ind with (2:=H); intros.
rewrite Fr_eqn with (o:=y); auto.
apply isOrd_osup; trivial.
intros.
apply isOrd_succ.
destruct fsub_elim with (2:=H3) (3:=H4); trivial.
eauto.
Qed.

Hint Resolve F_a_ord.

(** We need stability to prove that Ffix is a fixpoint *)
  Hypothesis Fstab : forall X,
    X ⊆ power A ->
    inter (replf X F) ⊆ F (inter X).

  Lemma F_intro : forall w,
    isOrd w ->
    forall a, a ∈ TI F w ->
    a ∈ F (fsub a).
intros.
assert (fx_ok : Ffix ∈ subset (power Ffix) (fun X => a ∈ F X)).
 apply subset_intro.
  apply power_intro; trivial.

  apply TI_elim in H0; auto.
  destruct H0.
  revert H1; apply Fmono.
  apply TI_Ffix; trivial.
  apply isOrd_inv with w; trivial.
assert (inter (replf (subset (power Ffix) (fun X => a ∈ F X)) (fun X => X)) ⊆ fsub a).
 red; intros.
 apply subset_intro.
  apply inter_elim with (1:=H1).
  rewrite replf_ax.
  2:red;red;auto.
  exists Ffix; auto with *.

  intros.
  apply inter_elim with (1:=H1).
  rewrite replf_ax.
  2:red;red;auto.
  exists X; auto with *.
  apply subset_intro; trivial.
  apply power_intro; trivial.

apply Fmono in H1.
apply H1.
apply Fstab.
 red; intros.
 rewrite replf_ax in H2.
 2:do 2 red; trivial.
 destruct H2.
 apply subset_elim1 in H2.
 rewrite H3; revert H2; apply power_mono.
 apply Ffix_inA.

 apply TI_elim in H0; auto.
 destruct H0.
 apply inter_intro.
  intros.
  rewrite replf_ax in H3; auto.
  destruct H3 as (x',?,?).
  rewrite replf_ax in H3.
  2:do 2 red; trivial.
  destruct H3 as (x'',?,?).
  rewrite H4; rewrite H5.
  apply subset_elim2 in H3; destruct H3.
  rewrite H3; trivial.

  exists (F Ffix).
  rewrite replf_ax.
  2:red;red;auto.
  exists Ffix; auto with *.
  rewrite replf_ax.
  2:red;red;trivial.
  exists Ffix; auto with *.
Qed.

  Lemma F_a_tot : forall a,
   a ∈ Ffix ->
   a ∈ TI F (osucc (Fix_rec F_a a)).
intros.
rewrite Ffix_def in H; destruct H.
revert a H0; apply isOrd_ind with (2:=H); intros.
assert (ao : isOrd (Fix_rec F_a a)).
 apply F_a_ord; rewrite Ffix_def; exists y; trivial.
rewrite TI_mono_succ; auto.
assert (fsub a ⊆ TI F (Fix_rec F_a a)).
 red; intros.
 destruct fsub_elim with (2:=H3) (3:=H4); trivial.
 assert (xo : isOrd x0).
  apply isOrd_inv with y; trivial.
 assert (z ∈ TI F (osucc (Fix_rec F_a z))).
  apply H2 with x0; trivial.
 revert H7; apply TI_mono; auto.
  apply isOrd_succ; apply F_a_ord; rewrite Ffix_def; exists x0; trivial.

  red; intros.
  rewrite Fr_eqn with (o:=y); auto.
  unfold F_a.
  apply osup_intro with (x:=z); trivial.
apply Fmono in H4.
apply H4.
apply F_intro with y; trivial.
Qed.

(** The closure ordinal *)
  Definition Ffix_ord :=
    osup Ffix (fun a => osucc (Fix_rec F_a a)).

  Lemma Ffix_o_o : isOrd Ffix_ord.
apply isOrd_osup; auto.
Qed.
Hint Resolve Ffix_o_o.

  Lemma Ffix_post : forall a,
   a ∈ Ffix ->
   a ∈ TI F Ffix_ord.
intros.
apply TI_intro with (Fix_rec F_a a); auto.
 apply osup_intro with (x:=a); trivial.
 apply lt_osucc; auto.

 rewrite <- TI_mono_succ; auto.
 apply F_a_tot; trivial.
Qed.

  Lemma Ffix_closure : Ffix == TI F Ffix_ord.
apply incl_eq.
 red; intros; apply Ffix_post; trivial.

 apply TI_Ffix; trivial.
Qed.

(** We prove it is a fixpoint *)
  Lemma Ffix_eqn : Ffix == F Ffix.
apply eq_intro; intros.
rewrite Ffix_def in H; destruct H.
apply Fmono with (TI F x).
 apply TI_Ffix; trivial.

 rewrite <- TI_mono_succ; auto.
 revert H0; apply TI_incl; auto.

 assert (z ∈ TI F (osucc Ffix_ord)).
  rewrite TI_mono_succ; auto.
  revert H; apply Fmono.
  red; intros; apply Ffix_post; trivial.
 rewrite Ffix_def; exists (osucc Ffix_ord); auto.
Qed.


End BoundedOperator.

Section BoundIndep.

Variable A : set.
Hypothesis Ftyp : forall X, X ⊆ A -> F X ⊆ A.
Variable A' : set.
Hypothesis Ftyp' : forall X, X ⊆ A' -> F X ⊆ A'.

Lemma Ffix_indep : Ffix A == Ffix A'.
apply eq_intro; intros.
 rewrite Ffix_def in H|-*; trivial.
 rewrite Ffix_def in H|-*; trivial.
Qed.

Lemma Ffix_ord_indep :
  Ffix_ord A == Ffix_ord A'.
unfold Ffix_ord.
apply osup_morph.
 apply Ffix_indep.

 red; intros.
 apply osucc_morph.
 unfold Fix_rec.
 apply uchoice_morph_raw; red; intros.
 unfold Ffix_rel.
 apply fa_morph; intro R.
 apply fa_morph; intro.
 apply impl_morph; intros.
  apply fa_morph; intro x2.
  apply fa_morph; intro g.
assert (fsub A x2 ==  fsub A' x2).
 unfold fsub.
 apply subset_morph.
  apply Ffix_indep.

  red; intros.
  apply fa_morph; intro X.
  rewrite Ffix_indep; reflexivity.
apply impl_morph.
 unfold ext_fun, eq_fun.
 apply fa_morph; intro x3.
 apply fa_morph; intro x4.
 rewrite H2; reflexivity.

 intros.
 apply impl_morph; intros.
  apply fa_morph; intro y0.
  rewrite H2; reflexivity.

  apply x1; auto with *.
  unfold F_a.
  apply osup_morph; auto.
  red; intros.
  apply osucc_morph.
  apply H3; trivial.

 apply x1; trivial.
Qed.

End BoundIndep.

End IterMonotone.

(** * Construction of the fixpoint "from above" *)

Section KnasterTarski.

Variable A : set.
Variable F : set -> set.

Hypothesis Fmono : Proper (incl_set==>incl_set) F.
Hypothesis Ftyp : forall x, x ⊆ A -> F x ⊆ A.

(*
Lemma fx_mrph : forall x x', x ⊆ A -> x == x' -> F x == F x'.
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
*)

Definition is_lfp x :=
  F x == x /\ forall y, (*y ⊆ A ->*) F y ⊆ y -> x ⊆ y.

Definition pre_fix x := x ⊆ F x.
Definition post_fix x := F x ⊆ x.

Lemma post_fix_A : post_fix A.
red; intros.
apply Ftyp; auto with *.
Qed.

Definition M' := subset (power A) post_fix.

Lemma member_A : A ∈ M'.
unfold M'.
apply subset_intro.
 apply power_intro; auto.

 apply post_fix_A.
Qed.

Lemma post_fix1 : forall x, x ∈ M' -> F x ⊆ x.
unfold M'; intros.
elim subset_elim2 with (1:=H); intros.
red; intros.
red in H1. red in H1.
rewrite H0.
apply subset_elim1 in H.
apply H1.
revert H2; apply Fmono.
rewrite H0; reflexivity.
Qed.

Definition FIX := inter M'.

Lemma lfp_typ : FIX ⊆ A.
unfold FIX, M'.
red; intros.
apply inter_elim with (1:=H).
apply subset_intro.
 apply power_intro; auto.

 apply post_fix_A.
Qed.

Lemma lower_bound : forall x, x ∈ M' -> FIX ⊆ x.
unfold FIX, M'; red; intros.
apply inter_elim with (1:=H0); auto.
Qed.

Lemma post_fix2 : forall x, x ∈ M' -> F FIX ⊆ F x.
intros.
apply Fmono.
apply lower_bound; trivial.
Qed.


Lemma post_fix_lfp : post_fix FIX.
red; red; intros.
unfold FIX.
apply inter_intro.
2:exists A; apply member_A.
intros.
apply post_fix1 with (1:=H0).
apply post_fix2 with (1:=H0).
trivial.
Qed.

Lemma incl_f_lfp : F FIX ∈ M'.
unfold M'; intros.
apply subset_intro.
 apply power_intro.
 apply Ftyp.
 apply lfp_typ.

 red; intros.
 apply Fmono.
 apply post_fix_lfp; trivial.
Qed.

Lemma FIX_eqn : F FIX == FIX.
apply incl_eq.
 apply post_fix_lfp.

 apply lower_bound.
 apply incl_f_lfp.
Qed.

Lemma knaster_tarski : is_lfp FIX.
split.
 apply FIX_eqn.

 intros.
 transitivity (y ∩ A). 
 2:apply inter2_incl1.
 apply lower_bound.
 unfold M'.
 apply subset_intro; trivial.
  apply power_intro.
  apply inter2_incl2.

  red.
  apply inter2_incl.
   transitivity (F y); trivial.
   apply Fmono.
   apply inter2_incl1.

   apply Ftyp.
   apply inter2_incl2.
Qed.

Lemma TI_FIX : forall o, isOrd o -> TI F o ⊆ FIX.
induction 1 using isOrd_ind.
red; intros.
apply TI_elim in H2; auto.
destruct H2.
specialize H1 with (1:=H2).
apply Fmono in H1.
apply H1 in H3.
revert H3; apply post_fix_lfp.
Qed.

End KnasterTarski.

