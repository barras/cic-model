Require Import ZF ZFrelations ZFnats ZFord ZFcoc.
Import IZF.

Definition incl_fam A X Y :=
  forall a a', a \in A -> a == a' -> X a \incl Y a'.

Instance incl_fam_trans : forall A, Transitive (incl_fam A).
red; red; intros.
transitivity (y a); auto with *.
Qed.

Definition mono_fam A F :=
  forall X Y, morph1 X -> morph1 Y -> incl_fam A X Y -> incl_fam A (F X) (F Y).

Section IterMonotone.

  Variable A : set.
  Variable F : (set -> set) -> set -> set.
  Variable Fmono : mono_fam A F.

  Lemma FFmono_ext: forall X Y, morph1 X -> morph1 Y -> eq_fun A X Y -> eq_fun A (F X) (F Y).
red; intros.
apply incl_eq.
 apply Fmono; trivial.
 red; red; intros.
 revert H6; apply eq_elim; auto.

 rewrite H3 in H2; symmetry in H3.
 apply Fmono; trivial.
 red; red; intros.
 revert H6; apply eq_elim; symmetry; apply H1; auto with *.
 rewrite <- H5; trivial.
Qed.
Hint Resolve FFmono_ext.

  Definition TIF o :=
    cc_app (TR (fun f o => cc_lam A (fun a => sup o (fun o' => F (cc_app (f o')) a))) o).

  Let m1 : forall o o' f f', isOrd o -> o == o' -> eq_fun o f f' ->
    cc_lam A (fun a => sup o (fun o' => F (cc_app (f o')) a)) ==
    cc_lam A (fun a => sup o' (fun o' => F (cc_app (f' o')) a)).
intros.
apply cc_lam_ext; intros; auto with *.
red; intros.
apply sup_morph; trivial.
red; intros.
apply FFmono_ext; trivial.
 apply cc_app_morph.
 transitivity (f' x0); auto with *.
 symmetry; auto with *.

 apply cc_app_morph.
 rewrite H5 in H4.
 transitivity (f x'0); auto with *.
 symmetry; auto with *.

 red; intros.
 apply cc_app_morph; auto with *.
Qed.

  Instance TIF_morph : morph2 TIF.
unfold TIF; do 3 red; intros.
apply cc_app_morph; trivial.
apply TR_morph; auto with *.
Qed.

  Let m2: forall a a' o o', a \in A -> a == a' -> isOrd o -> o == o' ->
    F (TIF o) a == F (TIF o') a'.
intros.
apply FFmono_ext; auto with *.
 apply TIF_morph; auto with *.
 apply TIF_morph; auto with *.

 red; intros; apply TIF_morph; auto.
Qed.

  Lemma TIF_eq : forall o a,
    isOrd o ->
    a \in A ->
    TIF o a == sup o (fun o' => F (TIF o') a).
intros.
unfold TIF.
rewrite TR_eqn; intros; auto.
 rewrite cc_beta_eq; auto with *.
 do 2 red; intros.
 apply sup_morph; auto with *.
 red; intros.
 apply m2; trivial.
 apply isOrd_inv with o; trivial.

 apply cc_lam_ext; auto with *.
 red; intros.
 apply sup_morph; trivial.
 red; intros.
 apply FFmono_ext; trivial.
  apply cc_app_morph; reflexivity.
  apply cc_app_morph; reflexivity.
  red; intros; apply cc_app_morph; auto.
Qed.

  Lemma TIF_intro : forall o o' a x,
    isOrd o ->
    lt o' o ->
    a \in A ->
    x \in F (TIF o') a ->
    x \in TIF o a.
intros.
rewrite TIF_eq; trivial.
rewrite sup_ax; auto.
 exists o'; trivial.

 do 2 red; intros; apply m2; auto with *.
 apply isOrd_inv with o; trivial.
Qed.

  Lemma TIF_elim : forall o x a,
    isOrd o ->
    a \in A ->
    x \in TIF o a ->
    exists2 o', lt o' o & x \in F (TIF o') a.
intros.
rewrite TIF_eq in H1; trivial.
rewrite sup_ax in H1; auto.
do 2 red; intros; apply m2; auto with *.
apply isOrd_inv with o; trivial.
Qed.

  Lemma TIF_mono : forall a, a \in A -> increasing (fun o => TIF o a).
do 2 red; intros.
apply TIF_elim in H3; intros; auto with *.
destruct H3.
apply TIF_intro with x0; auto with *.
apply H2 in H3; trivial.
Qed.

  Lemma TI_incl : forall o, isOrd o ->
    forall o', lt o' o ->
    forall a, a \in A -> 
    TIF o' a \incl TIF o a.
intros.
apply TIF_mono; trivial; auto.
 apply isOrd_inv with o; trivial.
 red; intros; apply isOrd_trans with o'; trivial.
Qed.

  Lemma TIF_mono_succ : forall o a,
    isOrd o ->
    a \in A ->
    TIF (osucc o) a == F (TIF o) a.
intros.
assert (Fext : ext_fun (osucc o) (fun o' => F (TIF o') a)).
 do 2 red; intros; apply m2; auto with *.
 apply isOrd_inv with (osucc o); auto.
rewrite TIF_eq; auto.
 apply eq_intro; intros.
  rewrite sup_ax in H1; trivial.
  destruct H1.
  revert H2; apply Fmono; auto with *.
   apply TIF_morph; auto with *.
   apply TIF_morph; auto with *.
  red; intros.
  rewrite <- H3.
  apply TIF_mono; trivial.
   apply isOrd_inv with (osucc o); auto.
   apply olts_le; trivial.

 rewrite sup_ax; trivial.
 exists o; trivial.
 apply lt_osucc; trivial.
Qed.

  Lemma TIF_mono_eq : forall o a,
    isOrd o ->
    a \in A ->
    TIF o a == sup o (fun o' => TIF (osucc o') a).
intros.
rewrite TIF_eq; auto.
apply sup_morph; auto with *.
red; intros.
rewrite <- TIF_mono_succ; trivial.
 apply TIF_morph; auto with *.
 rewrite H2; reflexivity.

 apply isOrd_inv with o; trivial.
Qed.

  Lemma TIF_pre_fix : forall fx o,
     morph1 fx ->
     isOrd o ->
     incl_fam A (F fx) fx ->
     incl_fam A (TIF o) fx.
intros.
induction H0 using isOrd_ind; intros.
red; intros.
transitivity (F fx a').
2:rewrite H5 in H4; auto with *.
red; intros.
elim TIF_elim with (3:=H6); intros; auto with *.
revert H8; apply Fmono; auto with *.
apply TIF_morph; auto with *.
Qed.


Section BoundedOperator.

Variable B : set.
Hypothesis Ftyp : forall X, morph1 X ->
  (forall a, a \in A -> X a \incl B) ->
  forall a, a \in A -> F X a \incl B.

Definition fsub a' x :=
  subset B (fun b => forall a X, morph1 X -> (forall a, a \in A -> X a \incl B) ->
                     x \in F X a -> b \in X a').

Instance fsub_morph : morph2 fsub.
unfold fsub; do 3 red; intros.
apply subset_morph; auto with *.
red; intros.
apply fa_morph; intro a.
apply fa_morph; intro X.
apply fa_morph; intro.
apply fa_morph; intro a'.
rewrite H; rewrite H0; reflexivity.
Qed.

Definition Ffix a := subset B (fun b => exists2 o, isOrd o & b \in TIF o a).

Lemma Ffix_in_dom : forall a, a \in A -> Ffix a \incl B.
red; intros.
apply subset_elim1 in H0; trivial.
Qed.

Lemma TIF_Ffix : forall o a, isOrd o -> a \in A -> TIF o a \incl Ffix a.
intros.
revert a H0.
apply isOrd_ind with (2:=H); intros.
red; intros.
apply TIF_elim in H4; auto with *.
destruct H4.
unfold Ffix.
apply subset_intro.
 revert z H5; apply Ftyp; trivial.
  apply TIF_morph; auto with *.
 intros.
 transitivity (Ffix a0); auto.
 apply Ffix_in_dom; trivial.
exists (osucc x); auto.
 apply isOrd_succ; apply isOrd_inv with y; trivial.

 rewrite TIF_mono_succ; auto.
 apply isOrd_inv with y; trivial.
Qed.

Lemma Ffix_def : forall a b, a \in A ->
  (b \in Ffix a <-> exists2 o, isOrd o & b \in TIF o a).
unfold Ffix; intros.
rewrite subset_ax.
split; intros.
 destruct H0.
 destruct H1.
 destruct H2.
 exists x0; trivial.
 rewrite H1; trivial.

 destruct H0.
 split.
  apply (Ffix_in_dom a); trivial.
  revert b H1; apply TIF_Ffix; trivial.

  exists b; auto with *.
  exists x; trivial.
Qed.

Lemma fsub_elim : forall x y o a a',
  a \in A ->
  a' \in A ->
  isOrd o ->
  y \in TIF o a ->
  x \in fsub a' y ->
  exists2 o', lt o' o & x \in TIF o' a'.
intros.
unfold fsub in H3; rewrite subset_ax in H3.
destruct H3 as (?,(x',?,?)).
apply TIF_elim in H2; trivial.
destruct H2.
exists x0; trivial.
rewrite H4; apply H5 with a; trivial.
 apply TIF_morph; auto with *.

 intros.
 transitivity (Ffix a0);[apply TIF_Ffix|apply Ffix_in_dom]; trivial.
 apply isOrd_inv with o; trivial.
Qed.

Lemma Ffix_fsub_inv : forall x y a a',
  a \in A ->
  a' \in A ->
  x \in Ffix a ->
  y \in fsub a' x ->
  y \in Ffix a'.
intros.
rewrite Ffix_def in H1|-*; trivial.
destruct H1.
apply fsub_elim with (4:=H3) in H2; trivial.
destruct H2.
exists x1; eauto using isOrd_inv.
Qed.


Section Iter.

Variable G : (set -> set -> set) -> set -> set -> set.
Hypothesis Gm : forall a x x' g g',
  a \in A ->
  x \in Ffix a ->
  (forall a', a' \in A -> eq_fun (fsub a' x) (g a') (g' a')) ->
  x == x' -> G g a x == G g' a x'.

Definition Ffix_rel a b y :=
  forall R:set->set->set->Prop,
  Proper (eq_set ==> eq_set ==> eq_set ==> iff) R ->
  (forall a x g,
   a \in A ->
   (forall a', a' \in A -> ext_fun (fsub a' x) (g a')) ->
   (forall a' y, a' \in A -> y \in fsub a' x -> R a' y (g a' y)) ->
   R a x (G g a x)) ->
  R a b y.

(*
  Instance Ffix_rel_morph :
    Proper (eq_set ==> eq_set ==> iff) Ffix_rel.
apply morph_impl_iff2; auto with *.
do 5 red; intros.
rewrite <- H; rewrite <- H0; apply H1; trivial.
Qed.


  Lemma Ffix_rel_intro : forall x g,
    ext_fun (fsub x) g ->
    (forall y, y \in fsub x -> Ffix_rel y (g y)) ->
    Ffix_rel x (G g x).
red; intros.
apply H2; trivial; intros.
apply H0; trivial.
Qed.

  Lemma Ffix_rel_inv : forall x o,
    x \in Ffix ->
    Ffix_rel x o ->
    exists2 g,
      ext_fun (fsub x) g /\
      (forall y, y \in fsub x -> Ffix_rel y (g y)) &
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
    forall y', Ffix_rel x y' -> x \in Ffix -> y == y'.
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

  Lemma Ffix_rel_def : forall o a, isOrd o -> a \in TI F o -> exists y, Ffix_rel a y.
intros o a oo; revert a; apply isOrd_ind with (2:=oo); intros.
clear o oo H0.
apply TI_elim in H2; trivial.
destruct H2.
assert (xo : isOrd x).
 apply isOrd_inv with y; trivial.
assert (forall z, z \in fsub a -> uchoice_pred (fun o => Ffix_rel z o)).
 intros.
 destruct H1 with x z; auto.
  apply subset_elim2 in H3; destruct H3.
  rewrite H3; apply H4; trivial.
  transitivity Ffix; [apply TIF_Ffix; trivial|apply Ffix_in_dom].

  split; intros.
   rewrite <- H5; trivial.
  split; intros.
   exists x0; trivial.
  apply Ffix_rel_fun with z; trivial.
  apply Ffix_fsub_inv with a; trivial.
  apply TIF_Ffix with (o:=y); trivial.
  apply TI_intro with x; trivial.
exists (G (fun b => uchoice (fun o => Ffix_rel b o)) a).
apply Ffix_rel_intro; trivial.
 red; red; intros.
 apply uchoice_morph_raw.
 apply Ffix_rel_morph; trivial.
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
revert H0; apply TIF_Ffix; trivial.
Qed.

  Definition Fix_rec a := uchoice (fun o => Ffix_rel a o).

  Lemma Fr_eqn : forall a o,
    isOrd o ->
    a \in TI F o ->
    Fix_rec a == G Fix_rec a.
intros.
unfold Fix_rec.
generalize (uchoice_def _ (Ffix_rel_choice_pred _ _ H H0)); intro.
apply Ffix_rel_inv in H1; auto.
 2:revert H0; apply TIF_Ffix; trivial.
destruct H1.
destruct H1.
rewrite H2.
apply Gm; auto with *.
 revert H0; apply TIF_Ffix; trivial.
red; intros.
rewrite H5 in H4.
assert (x' \in TI F o).
 destruct fsub_elim with (2:=H0) (3:=H4); trivial.
 apply TI_incl with x1; auto.
generalize (uchoice_def _ (Ffix_rel_choice_pred _ _ H H6)); intro.
specialize H3 with (1:=H4).
rewrite <- Ffix_rel_fun with (1:=H3) (2:=H7).
2:apply Ffix_fsub_inv with a; trivial.
2:revert H0; apply TIF_Ffix; trivial.
rewrite <- H5 in H4.
apply H1; trivial.
Qed.
*)

End Iter.

(*
  Definition F_a g x := sup (fsub x) (fun a => osucc (g a)).

  Lemma F_a_morph : forall x x' g g',
    eq_fun (fsub x) g g' ->
    x == x' -> F_a g x == F_a g' x'.
unfold F_a; intros.
apply sup_morph.
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

  Lemma F_a_ord : forall a, a \in Ffix -> isOrd (Fix_rec F_a a).
intros.
rewrite Ffix_def in H; destruct H.
revert a H0; apply isOrd_ind with (2:=H); intros.
rewrite Fr_eqn with (o:=y); auto.
apply isOrd_supf; trivial.
intros.
apply isOrd_succ.
destruct fsub_elim with (2:=H3) (3:=H4); trivial.
eauto.
Qed.

Hint Resolve F_a_ord.

  Hypothesis Fstab : forall X,
    X \incl power A ->
    inter (replf X F) \incl F (inter X).

  Lemma F_intro : forall w,
    isOrd w ->
    forall a, a \in TI F w ->
    forall o, isOrd o ->
    (forall y, y \in fsub a -> y \in TI F o) ->
    a \in F (TI F o).
intros.
assert (inter (replf (subset (power A) (fun X => a \in F X)) (fun X => X))
        \incl TI F o).
 red; intros.
 apply H2.
 apply subset_intro.
  apply inter_elim with (1:=H3).
  rewrite replf_ax.
  2:red;red;auto.
  exists A; auto with *.
  apply subset_intro; auto with *.
   apply power_intro; auto.

   apply TI_elim in H0; auto.
   destruct H0.
   revert H4; apply Fmono.
   transitivity Ffix; [apply TIF_Ffix; trivial|apply Ffix_in_dom].
   apply isOrd_inv with w; trivial.

  intros.
  apply inter_elim with (1:=H3).
  rewrite replf_ax.
  2:red;red;auto.
  exists X; auto with *.
  apply subset_intro; trivial.
  apply power_intro; auto.
apply (Fmono _ _ H3).
apply Fstab.
 red; intros.
 rewrite replf_ax in H4.
 2:red;red;auto.
 destruct H4.
 rewrite H5; apply subset_elim1 in H4; trivial.
apply inter_intro; intros.
 rewrite replf_ax in H4.
 2:red;red;auto.
 destruct H4.
 rewrite H5; clear y H5.
 rewrite replf_ax in H4.
 2:red;red;trivial.
 destruct H4.
 rewrite <- H5 in H4; clear x0 H5.
 apply subset_elim2 in H4.
 destruct H4.
 rewrite H4; trivial.

 apply TI_elim in H0; auto.
 destruct H0.
 exists (F (TI F x)).
 rewrite replf_ax.
 2:red;red;auto.
 exists (TI F x); auto with *.
 rewrite replf_ax.
 2:red;red;trivial.
 exists (TI F x); auto with *.
 apply subset_intro; trivial.
 apply power_intro; intros; apply Ffix_in_dom.
 revert H5; apply TIF_Ffix.
 apply isOrd_inv with w; trivial.
Qed.

  Lemma F_a_tot : forall a,
   a \in Ffix ->
   a \in TI F (osucc (Fix_rec F_a a)).
intros.
rewrite Ffix_def in H; destruct H.
revert a H0; apply isOrd_ind with (2:=H); intros.
assert (fsub a \incl TI F (Fix_rec F_a a)).
 red; intros.
 destruct fsub_elim with (2:=H3) (3:=H4); trivial.
 assert (xo : isOrd x0).
  apply isOrd_inv with y; trivial.
 assert (z \in TI F (osucc (Fix_rec F_a z))).
  apply H2 with x0; trivial.
 revert H7; apply TI_mono; auto.
  apply F_a_ord; rewrite Ffix_def; exists y; auto.

  apply isOrd_succ; apply F_a_ord; rewrite Ffix_def; exists x0; trivial.

  red; intros.
  rewrite Fr_eqn with (o:=y); auto.
  unfold F_a; rewrite sup_ax; trivial.
  exists z; auto.
rewrite TI_mono_succ; auto.
2:apply F_a_ord; rewrite Ffix_def; exists y; trivial.
apply F_intro with y; trivial.
apply F_a_ord; rewrite Ffix_def; exists y; trivial.
Qed.

  Definition Ffix_ord :=
    sup Ffix (fun a => osucc (Fix_rec F_a a)).

  Lemma Ffix_o_o : isOrd Ffix_ord.
apply isOrd_supf; auto.
Qed.
Hint Resolve Ffix_o_o.

  Lemma Ffix_post : forall a,
   a \in Ffix ->
   a \in TI F Ffix_ord.
intros.
apply TI_intro with (Fix_rec F_a a); auto.
 unfold Ffix_ord; rewrite sup_ax; trivial.
 exists a; trivial.
 apply lt_osucc; auto.

 rewrite <- TI_mono_succ; auto.
 apply F_a_tot; trivial.
Qed.

  Lemma Ffix_eqn : Ffix == F Ffix.
apply eq_intro; intros.
rewrite Ffix_def in H; destruct H.
apply Fmono with (TI F x).
 apply TIF_Ffix; trivial.

 rewrite <- TI_mono_succ; auto.
 revert H0; apply TI_incl; auto.

 assert (z \in TI F (osucc Ffix_ord)).
  rewrite TI_mono_succ; auto.
  revert H; apply Fmono.
  red; intros; apply Ffix_post; trivial.
 rewrite Ffix_def; exists (osucc Ffix_ord); auto.
Qed.
*)

End BoundedOperator.


End IterMonotone.

