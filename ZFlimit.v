Require Import ZF ZFpairs ZFnats ZFord.
Require ZFfix. (* limited dependency... *)

Section Limit.

(** Building the limit of a sequence of sets *)
Variable o : set.
Variable F : set -> set.
Hypothesis oord : isOrd o.
Hypothesis Fm : ext_fun o F.

Definition lim :=
  subset (sup o F) (fun z => exists2 o', o' ∈ o & forall w, o' ⊆ w -> w ∈ o -> z ∈ F w).

Lemma lim_def z :
  z ∈ lim <-> exists2 o', o' ∈ o &forall w, o' ⊆ w -> w ∈ o -> z ∈ F w.
intros.
unfold lim.
rewrite subset_ax.
rewrite sup_ax; auto with *.
split; intro.
 destruct H as (_,(z',eqz,(o',o'lt,zin))).
 exists o'; intros; trivial.
 rewrite eqz; auto.

 destruct H as (o',o'lt,zin).
 split; eauto with *.
 exists z; eauto with *.
Qed.

(** If the sequence is stationary, it has a limit *)
Lemma lim_cst o' :
  o' ∈ o ->
  (forall w, o' ⊆ w -> w ∈ o -> F w == F o') ->
  lim == F o'.
intros o'lt fcst.
apply eq_set_ax; intros z.
assert (os := fun y => isOrd_inv o y oord).
rewrite lim_def; trivial.
split; intros.
 destruct H as (w,w'o,zin).
 rewrite <- (fcst (o' ⊔ w)).
  apply zin.
   apply osup2_incl2; auto.
   apply osup2_lt; auto.

  apply osup2_incl1; auto.
  apply osup2_lt; auto.

 exists o'; intros; trivial.
 rewrite fcst; auto.
Qed.

End Limit.

(** Limits at a successor ordinal is just the last value *)
Lemma lim_oucc o F :
  isOrd o ->
  ext_fun (osucc o) F ->
  lim (osucc o) F == F o.
intros.
apply lim_cst; auto with *; intros.
 apply lt_osucc; trivial.

 apply H0; auto.
 apply olts_le in H2; trivial.
 apply incl_eq; trivial.
Qed.

Lemma lim_ext :
  forall o o', isOrd o -> o == o' -> forall f f', eq_fun o f f' -> lim o f == lim o' f'.
intros; unfold lim.
apply subset_morph.
 apply sup_morph; auto with *.

 red; intros.
 split; destruct 1 as (w',?,?); exists w'; intros.
  rewrite <- H0; trivial.

  rewrite <- H0 in H6.
  rewrite <- (H1 _ _ H6 (reflexivity w)); auto.

  rewrite H0; trivial.

  rewrite (H1 _ _ H6 (reflexivity w)); auto.
  rewrite H0 in H6; auto.
Qed.

Instance lim_morph : Proper (eq_set==>(eq_set==>eq_set)==>eq_set) lim.
do 3 red; intros; unfold lim.
apply subset_morph.
 apply sup_morph; auto with *.
 red; intros; apply H0; trivial.

 red; intros.
 apply ex2_morph; red; intros.
  rewrite H; reflexivity.

  apply fa_morph; intro w.
  rewrite H; rewrite (H0 _ _ (reflexivity w)); reflexivity.
Qed.

(** Limits of a monotonic operator *)
Section LimitMono.

Variable F:set->set.
Variable o : set.
Hypothesis oord : isOrd o.
Hypothesis Fmono : increasing F.

Let os := fun y => isOrd_inv _ y oord.

Let Fext : ext_fun o F.
do 2 red; intros.
apply incl_eq; apply Fmono; auto.
 rewrite <- H0; auto.
 rewrite H0; reflexivity.
 rewrite <- H0; auto.
 rewrite H0; reflexivity.
Qed.

(** This is the same as the union *)
Lemma lim_def_mono : lim o F == sup o F.
apply eq_set_ax; intros z.
rewrite lim_def; auto with *.
rewrite sup_ax; trivial.
split; destruct 1.
 exists x; auto with *.

 exists x; intros; trivial.
 revert H0; apply Fmono; auto.
Qed.

Lemma lim_mono z :
  z ∈ lim o F <-> exists2 o', o' ∈ o & z ∈ F o'.
rewrite lim_def_mono; rewrite sup_ax; auto with *.
Qed.

End LimitMono.

(** Limit of the transfinite iteration *)
Section LimitTI.

Variable F : set->set.
Hypothesis Fm : Proper (incl_set==>incl_set) F.

Lemma TIlim o :
  isOrd o ->
  TI F o == lim o (fun o' => F(TI F o')).
intros oo.
rewrite TI_eq; auto.
rewrite lim_def_mono; auto with *.
red; intros.
apply Fm; apply ZFfix.TI_mono; trivial.
Qed.

End LimitTI.

Section TRF.

Hypothesis F:(set->set->set)->set->set->set.
Hypothesis Fext : forall o o' f f' x x',
  isOrd o ->
  (forall o' o'' x x', o' ∈ o -> o'==o'' -> x==x' -> f o' x == f' o'' x') ->
  o == o' ->
  x == x' ->
  F f o x == F f' o' x'.


Fixpoint TR_acc (o:set) (H:Acc in_set o) (H':isOrd o) (x:set) : set :=
  F (fun o' x' => ZFrepl.uchoice (fun y' => exists h:o' ∈ o, y' == TR_acc o' (Acc_inv H h) (isOrd_inv _ _ H' h) x')) o x.

Lemma TR_acc_morph o o' h h' oo oo' x x' :
  o == o' ->
  x == x' ->
  TR_acc o h oo x == TR_acc o' h' oo' x'.
revert o' h' oo' x x'; induction h using Acc_indd; destruct h'; simpl; intros.
apply Fext; intros; trivial.
apply ZFrepl.uchoice_morph_raw; red; intros.
split; destruct 1; intros.
 rewrite H5 in H6; clear x2 H5.
 assert (o'' ∈ o').
  rewrite <- H0; rewrite <- H3; trivial.
 exists H5.
 rewrite H6; clear y H6.
 apply H; trivial.

 rewrite <- H5 in H6; clear y H5.
 exists H2.
 rewrite H6; clear x2 H6.
 symmetry; apply H; trivial.
Qed.

Lemma isOrd_acc o : isOrd o -> Acc in_set o.
intros.
rewrite <- ZFwf.isWf_acc; auto.
apply H.
Qed.

Definition TR o x := ZFrepl.uchoice (fun y => exists h:isOrd o, y == TR_acc o (isOrd_acc _ h) h x).

Lemma TR_acc_eqn o h h' x :
  TR_acc o h h' x == F TR o x.
revert h' x; induction h using Acc_indd; simpl; intros.
apply Fext; intros; auto with *.
symmetry; apply ZFrepl.uchoice_ext; intros.
 split;[|split]; intros.
  destruct H4.
  rewrite H3 in H4.
  exists x3; trivial.

  exists (TR_acc o' (a o' H0) (isOrd_inv x o' h' H0) x1); exists H0; reflexivity.

  destruct H3; destruct H4.
  rewrite H3; rewrite H4; apply TR_acc_morph; auto with *.

 exists H0.
 unfold TR.
 symmetry; apply ZFrepl.uchoice_ext.
  split;[|split]; intros.
   destruct H4.
   rewrite H3 in H4.
   exists x3; trivial.

   assert (isOrd o'').
    rewrite <- H1; apply isOrd_inv with x; trivial.
   exists (TR_acc o'' (isOrd_acc _ H3) H3 x'); exists H3; reflexivity.

   destruct H3; destruct H4.
   rewrite H3; rewrite H4; apply TR_acc_morph; auto with *.

  assert (h'' := H0); rewrite H1 in h''.
  exists (isOrd_inv _ _ h' h'').
  apply TR_acc_morph; trivial.
Qed.

Lemma TR_eqn o x :
  isOrd o ->
  TR o x == F TR o x.
intros.
rewrite <- TR_acc_eqn with (h:=isOrd_acc _ H) (h':=H).
unfold TR.
symmetry; apply ZFrepl.uchoice_ext.
 split;[|split];intros.
  destruct H1; rewrite H0 in H1.
  exists x1; trivial.

  econstructor; exists H; reflexivity.

  destruct H0; destruct H1; rewrite H0; rewrite H1; apply TR_acc_morph; reflexivity.

 exists H; reflexivity.
Qed.

Global Instance TR_morph : morph2 TR.
do 3 red; intros.
unfold TR.
apply ZFrepl.uchoice_morph_raw; red; intros.
split; destruct 1.
 assert (isOrd y) by (rewrite <- H; trivial).
 exists H3.
 rewrite <- H1; rewrite H2; apply TR_acc_morph; trivial.

 assert (isOrd x) by (rewrite H; trivial).
 exists H3.
 rewrite H1; rewrite H2; symmetry; apply TR_acc_morph; trivial.
Qed.

End TRF.


Section TR_irrel.

Variable F : (set->set->set)->set->set->set.

Variable T : set -> set.
Variable Tcont : forall o z, isOrd o ->
  (z ∈ T o <-> exists2 o', o' ∈ o & z ∈ T (osucc o')).

Hypothesis Fext : forall o o' f f' x x',
  isOrd o ->
  (forall o' o'' x x', o' ∈ o -> o'==o'' -> x==x' -> f o' x == f' o'' x') ->
  o == o' ->
  x == x' ->
  F f o x == F f' o' x'.

Hypothesis Firr : forall o o' f f' x x',
  morph2 f ->
  morph2 f' ->
  isOrd o ->
  isOrd o' ->
  (forall o1 o1' x x',
   o1 ∈ o -> o1' ∈ o' -> o1 ⊆ o1' -> x ∈ T o1 -> x==x' ->
   f o1 x == f' o1' x') ->
  o ⊆ o' ->
  x ∈ T o ->
  x == x' ->
  F f o x == F f' o' x'.

Lemma TR_irrel : forall o o' x,
  isOrd o ->
  isOrd o' ->
  o' ⊆ o ->
  x ∈ T o' ->
  TR F o x == TR F o' x.
intros.
revert o H H1 x H2; elim H0 using isOrd_ind; intros.
rewrite Tcont in H5; trivial; destruct H5. 
rewrite TR_eqn; auto with *.
rewrite TR_eqn; auto with *.
symmetry; apply Firr; intros; auto with *.
 symmetry.
assert (h:=TR_morph F Fext).
 rewrite <- H11.
 eauto using isOrd_inv.

 rewrite Tcont; eauto.
Qed.

End TR_irrel.

Section TRirr.

Variable F : (set->set)->set->set.
Hypothesis Fm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) F.
Variable T : set -> set.
Variable Tcont : forall o z, isOrd o ->
  (z ∈ T o <-> exists2 o', o' ∈ o & z ∈ T (osucc o')).
Hypothesis Fext : forall o f f',
  isOrd o ->
  eq_fun (T o) f f' ->
  eq_fun (T (osucc o)) (F f) (F f').

Lemma Tmono o o': isOrd o -> isOrd o' -> o ⊆ o' -> T o ⊆ T o'.
red; intros.
rewrite Tcont in H2; auto.
destruct H2.
rewrite Tcont; trivial.
exists x; auto.
Qed.


Let G f o x := F (fun x => lim o (fun o' => f o' x)) x.
Definition TRF := TR G.

Let Gext : forall o o' f f' x x',
  isOrd o ->
  (forall o' o'' x x', o' ∈ o -> o'==o'' -> x==x' -> f o' x == f' o'' x') ->
  o == o' ->
  x == x' ->
  G f o x == G f' o' x'.
unfold G; intros.
apply Fm; trivial.
red; intros.
apply lim_ext; trivial.
red; intros; auto.
Qed.

Let Girr : forall o o' f f' x x',
  morph2 f ->
  morph2 f' ->
  isOrd o ->
  isOrd o' ->
  (forall o1 o1' x x',
   o1 ∈ o -> o1' ∈ o' -> o1 ⊆ o1' -> x ∈ T o1 -> x==x' ->
   f o1 x == f' o1' x') ->
  o ⊆ o' ->
  x ∈ T o ->
  x == x' ->
  G f o x == G f' o' x'.
unfold G; intros.
assert (os := fun y => isOrd_inv _ y H1).
rewrite Tcont in H5; trivial.
destruct H5 as (w,?,?).
apply Fext with w; auto.
red; intros.
rewrite lim_cst with (o':=w); auto.
 rewrite lim_cst with (o':=w); auto.
  apply H3; auto with *.

  do 2 red; intros.
  apply H0; auto with *.

  intros.
  transitivity (f w x0).
   symmetry; apply H3; auto with *.

   apply H3; auto with *.

 do 2 red; intros.
 apply H; auto with *.

 intros.
 transitivity (f' w0 x'0).
  apply H3; auto with *.
  revert H8; apply Tmono; auto.

  symmetry; apply H3; auto with *.
Qed.

Instance TRF_morph : morph2 TRF.
unfold TRF; apply TR_morph; trivial.
Qed.


Lemma TRF_indep : forall o o' x,
  isOrd o ->
  o' ∈ o ->
  x ∈ T (osucc o') ->
  TRF o x == F (TRF o') x.
intros.
assert (os := fun y => isOrd_inv _ y H).
unfold TRF. 
rewrite TR_eqn; auto with *.
unfold G at 1.
apply (Fext o'); auto with *.
red; intros.
assert (h:=TR_morph G Gext).
rewrite <- H3.
rewrite lim_cst with (o':=o'); auto with *.
 do 2 red; intros.
 apply TR_morph; auto with *.

 intros.
 apply TR_irrel with (T:=T); auto with *.
Qed.

End TRirr.
