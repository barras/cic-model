(** Construction of a function (a.k.a a family of sets) over a fixed domain by
    transfinite iteration. No fixpoint theorem here.
 *)

Require Import ZF ZFrelations ZFnats ZFord.
    
(** Order on families *)
Definition incl_fam A X Y :=
  forall a, a ∈ A -> X a ⊆ Y a.

Instance incl_fam_trans : forall A, Transitive (incl_fam A).
red; red; intros.
transitivity (y a); auto with *.
Qed.

(** Monotonicity *)
Definition mono_fam A F :=
  forall X Y, morph1 X -> morph1 Y -> incl_fam A X Y -> incl_fam A (F X) (F Y).

Section IterMonotone.

  Variable A : set.
  Variable F : (set -> set) -> set -> set.
  Variable Fm : Proper ((eq_set==>eq_set) ==> eq_set ==> eq_set) F.
  Variable Fmono : mono_fam A F.

  Lemma FFmono_ext: forall X Y, morph1 X -> morph1 Y -> eq_fun A X Y -> eq_fun A (F X) (F Y).
red; intros.
rewrite <- H3; clear x' H3.
apply incl_eq.
 apply Fmono; trivial.
 red; red; intros.
 revert H4; apply eq_elim; auto with *.

 apply Fmono; trivial.
 red; red; intros.
 revert H4; apply eq_elim; symmetry; apply H1; auto with *.
Qed.
Hint Resolve FFmono_ext.

(** Definition of the TIF iterator *)
  Let F' f o := cc_lam A (fun a => sup o (fun o' => F (cc_app (f o')) a)).

  Let F'm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) F'.
do 3 red; intros.
unfold F'.
apply cc_lam_ext; intros; auto with *.
red; intros.
apply sup_morph; trivial.
red; intros.
apply FFmono_ext; trivial.
 apply cc_app_morph; reflexivity.
(**)
 apply cc_app_morph; reflexivity.
(**)
 red; intros.
 apply cc_app_morph; auto with *.
Qed.

  Let F'ext : forall o f f', isOrd o -> eq_fun o f f' -> F' f o == F' f' o.
intros.
unfold F'.
apply cc_lam_ext; intros; auto with *.
red; intros.
apply sup_morph; auto with *.
red; intros.
apply FFmono_ext; trivial.
 apply cc_app_morph; reflexivity.
(**)
 apply cc_app_morph; reflexivity.
(**)
 red; intros.
 apply cc_app_morph; auto with *.
Qed.

  Definition TIF o := cc_app (TR F' o).

  Instance TIF_morph : morph2 TIF.
unfold TIF; do 3 red; intros.
apply cc_app_morph; trivial.
apply TR_morph0; auto with *.
Qed.

  Let m2: forall a a' o o', a ∈ A -> a == a' -> isOrd o -> o == o' ->
    F (TIF o) a == F (TIF o') a'.
intros.
apply FFmono_ext; auto with *.
 apply TIF_morph; auto with *.
 apply TIF_morph; auto with *.
(**)
 red; intros; apply TIF_morph; auto.
Qed.

  Lemma TIF_eq : forall o a,
    isOrd o ->
    a ∈ A ->
    TIF o a == sup o (fun o' => F (TIF o') a).
intros.
unfold TIF.
rewrite TR_eqn; intros; auto.
unfold F' at 1; rewrite cc_beta_eq; auto with *.
do 2 red; intros.
apply sup_morph; auto with *.
red; intros.
apply m2; trivial.
apply isOrd_inv with o; trivial.
Qed.

  Lemma TIF_intro : forall o o' a x,
    isOrd o ->
    lt o' o ->
    a ∈ A ->
    x ∈ F (TIF o') a ->
    x ∈ TIF o a.
intros.
rewrite TIF_eq; trivial.
rewrite sup_ax; auto.
 exists o'; trivial.

 do 2 red; intros; apply m2; auto with *.
 apply isOrd_inv with o; trivial.
Qed.

  Lemma TIF_elim : forall o x a,
    isOrd o ->
    a ∈ A ->
    x ∈ TIF o a ->
    exists2 o', lt o' o & x ∈ F (TIF o') a.
intros.
rewrite TIF_eq in H1; trivial.
rewrite sup_ax in H1; auto.
do 2 red; intros; apply m2; auto with *.
apply isOrd_inv with o; trivial.
Qed.

  (** Monotonicity of TIF *)
  Lemma TIF_mono : forall a, a ∈ A -> increasing (fun o => TIF o a).
do 2 red; intros.
apply TIF_elim in H3; intros; auto with *.
destruct H3.
apply TIF_intro with x0; auto with *.
apply H2 in H3; trivial.
Qed.

  Lemma TIF_incl : forall o, isOrd o ->
    forall o', lt o' o ->
    forall a, a ∈ A -> 
    TIF o' a ⊆ TIF o a.
intros.
apply TIF_mono; trivial; auto.
apply isOrd_inv with o; trivial.
Qed.

  Lemma TIF_mono_succ : forall o a,
    isOrd o ->
    a ∈ A ->
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
 apply TIF_mono; trivial.
  apply isOrd_inv with (osucc o); auto.
  apply olts_le; trivial.

 rewrite sup_ax; trivial.
 exists o; trivial.
 apply lt_osucc; trivial.
Qed.

  Lemma TIF_mono_eq : forall o a,
    isOrd o ->
    a ∈ A ->
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

  (** Property related to fixpoints: any post-fixpoint [fx] contains all stages *)
  Lemma TIF_pre_fix : forall fx o,
     morph1 fx ->
     isOrd o ->
     incl_fam A (F fx) fx ->
     incl_fam A (TIF o) fx.
intros.
induction H0 using isOrd_ind; intros.
red; intros.
transitivity (F fx a); auto with *.
red; intros.
elim TIF_elim with (3:=H5); intros; auto with *.
revert H7; apply Fmono; auto with *.
apply TIF_morph; auto with *.
Qed.

(*
Section BoundedOperator.

Variable B : set -> set.
Hypothesis Bm : morph1 B.
Hypothesis Ftyp : forall X, morph1 X -> incl_fam A X B -> incl_fam A (F X) B.

Definition fsub a a' x :=
  subset (B a') (fun b => forall X, morph1 X -> incl_fam A X B -> x ∈ F X a -> b ∈ X a').

Instance fsub_morph : Proper (eq_set==>eq_set==>eq_set==>eq_set) fsub.
unfold fsub; do 4 red; intros.
apply subset_morph; auto with *.
red; intros.
apply fa_morph; intro X.
apply fa_morph; intro Xm.
rewrite H; rewrite H0; rewrite H1; reflexivity.
Qed.

Definition Ffix a := subset (B a) (fun b => exists2 o, isOrd o & b ∈ TIF o a).

Lemma Ffix_in_dom : incl_fam A Ffix B.
do 2 red; intros.
apply subset_elim1 in H0; trivial.
Qed.

Lemma TIF_Ffix : forall o, isOrd o -> incl_fam A (TIF o) Ffix.
intros.
apply isOrd_ind with (2:=H); intros.
do 2 red; intros.
apply TIF_elim in H4; auto with *.
destruct H4.
unfold Ffix.
apply subset_intro.
 revert z H5; apply Ftyp; trivial.
  apply TIF_morph; auto with *.
 transitivity Ffix; auto.
 apply Ffix_in_dom; trivial.
exists (osucc x); auto.
 apply isOrd_succ; apply isOrd_inv with y; trivial.

 rewrite TIF_mono_succ; auto.
 apply isOrd_inv with y; trivial.
Qed.

Lemma Ffix_def : forall a b, a ∈ A ->
  (b ∈ Ffix a <-> exists2 o, isOrd o & b ∈ TIF o a).
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
  a ∈ A ->
  a' ∈ A ->
  isOrd o ->
  y ∈ TIF o a ->
  x ∈ fsub a a' y ->
  exists2 o', lt o' o & x ∈ TIF o' a'.
intros.
unfold fsub in H3; rewrite subset_ax in H3.
destruct H3 as (?,(x',?,?)).
apply TIF_elim in H2; trivial.
destruct H2.
exists x0; trivial.
rewrite H4; apply H5; trivial.
 apply TIF_morph; auto with *.

 transitivity Ffix; [apply TIF_Ffix|apply Ffix_in_dom]; trivial.
 apply isOrd_inv with o; trivial.
Qed.

Lemma Ffix_fsub_inv : forall x y a a',
  a ∈ A ->
  a' ∈ A ->
  x ∈ Ffix a ->
  y ∈ fsub a a' x ->
  y ∈ Ffix a'.
intros.
rewrite Ffix_def in H1|-*; trivial.
destruct H1.
apply fsub_elim with (4:=H3) in H2; trivial.
destruct H2.
exists x1; eauto using isOrd_inv.
Qed.

Section IterDep.

Variable G : (set -> set -> set) -> set -> set -> set.
Hypothesis Gm : forall a x x' g g',
  a ∈ A ->
  x ∈ Ffix a ->
  (forall a' a'', a' ∈ A -> a' == a'' -> eq_fun (fsub a a' x) (g a') (g' a'')) ->
  x == x' -> G g a x == G g' a x'.

Definition Ffixd_rel a x y :=
  forall R:set->set->set->Prop,
  Proper (eq_set ==> eq_set ==> eq_set ==> iff) R ->
  (forall a x g,
   a ∈ A ->
   morph2 g ->
   (forall a', a' ∈ A -> ext_fun (fsub a a' x) (g a')) ->
   (forall a' y, a' ∈ A -> y ∈ fsub a a' x -> R a' y (g a' y)) ->
   R a x (G g a x)) ->
  R a x y.

  Instance Ffixd_rel_morph :
    Proper (eq_set ==> eq_set ==> eq_set ==> iff) Ffixd_rel.
apply morph_impl_iff3; auto with *.
do 6 red; intros.
rewrite <- H; rewrite <- H0; rewrite <- H1; apply H2; trivial.
Qed.

  Lemma Ffixd_rel_intro : forall a x g,
    a ∈ A ->
    morph2 g -> 
    (forall a', a' ∈ A -> ext_fun (fsub a a' x) (g a')) ->
    (forall a' y, a' ∈ A -> y ∈ fsub a a' x -> Ffixd_rel a' y (g a' y)) ->
    Ffixd_rel a x (G g a x).
red; intros.
apply H4; trivial; intros.
apply H2; trivial.
Qed.

  Lemma Ffixd_rel_inv : forall a x o,
    a ∈ A ->
    x ∈ Ffix a ->
    Ffixd_rel a x o ->
    exists2 g,
      morph2 g /\
      (forall a', a' ∈ A -> ext_fun (fsub a a' x) (g a')) /\
      (forall a' y, a' ∈ A -> y ∈ fsub a a' x -> Ffixd_rel a' y (g a' y)) &
      o == G g a x.
intros a x o tya xFx Fr.
apply (@proj2 (Ffixd_rel a x o)).
revert xFx.
apply Fr; intros.
 admit. (*
 apply morph_impl_iff3; auto with *.
 do 5 red; intros.
 rewrite <- H0 in xFx.
 destruct (H1 xA) as (?,(g,(?,?),?)); clear H1.
 split;[|exists g].
  rewrite <- H; rewrite <- H0; trivial.

  split; intros.
   red; red; intros; apply H3; trivial.
   rewrite H; trivial.

   rewrite <- H in H1; auto.

  rewrite <- H0; rewrite H5.
  apply Gm; auto with *.
*)

 split.
  apply Ffixd_rel_intro; auto.
  intros.
  apply H2; trivial.
  apply Ffix_fsub_inv with x0 a0; trivial.

  exists g.
   split; [|split]; intros; auto.
   apply H2; trivial.
   apply Ffix_fsub_inv with x0 a0; trivial.

  apply Gm; auto with *.
  red; intros.
  rewrite <- H4.
  apply H1; trivial.
Qed.

  Lemma Ffixd_rel_fun :
    forall a x y, Ffixd_rel a x y ->
    forall y', Ffixd_rel a x y' -> x ∈ Ffix a -> y == y'.
intros a x y H.
apply H; intros.
 apply morph_impl_iff3; auto with *.
 do 5 red; intros.
 admit. (*
 rewrite <- H2; rewrite <- H0 in H4,H5; rewrite <- H1 in H4,H5; auto. *)
apply Ffixd_rel_inv in H4; trivial.
destruct H4 as (g',(mg',(eg',Hg)),eqy').
rewrite eqy'; clear y' eqy'.
apply Gm; auto with *.
red; intros.
apply H3; trivial.
 rewrite <- (mg' _ _ H6 _ _ H8); auto.

 apply Ffix_fsub_inv with x0 a0; trivial.
Qed.

Require Import ZFrepl.

  Lemma Ffixd_rel_def : forall o x a, isOrd o -> a ∈ A -> x ∈ TIF o a ->
    exists y, Ffixd_rel a x y.
intros o x a oo; revert x a; apply isOrd_ind with (2:=oo); intros.
clear o oo H0.
assert (forall a' z, a' ∈ A -> z ∈ fsub a a' x -> uchoice_pred (fun o => Ffixd_rel a' z o)).
 intros.
 destruct fsub_elim with (4:=H3) (5:=H4) as (y',lty',tyz); trivial.
 split; intros.
  rewrite <- H5; trivial.
 split; intros; eauto.
 apply Ffixd_rel_fun with a' z; trivial.
 apply Ffix_fsub_inv with x a; trivial.
 apply TIF_Ffix with (o:=y); trivial.
exists (G (fun a' b => uchoice (fun o => Ffixd_rel a' b o)) a x).
apply Ffixd_rel_intro; trivial.
 do 3 red; intros.
 apply uchoice_morph_raw.
 red; intros.
 apply Ffixd_rel_morph; trivial.

 do 2 red; intros.
 apply uchoice_morph_raw.
 apply Ffixd_rel_morph; auto with *.
intros.
apply uchoice_def; auto.
Qed.

  Lemma Ffixd_rel_choice_pred : forall o x a, isOrd o -> a ∈ A -> x ∈ TIF o a ->
    uchoice_pred (fun o => Ffixd_rel a x o).
split; intros.
 rewrite <- H2; trivial.
split; intros.
 apply Ffixd_rel_def with o; trivial.
apply Ffixd_rel_fun with a x; trivial.
revert H1; apply TIF_Ffix; trivial.
Qed.

  Definition Fixd_rec a x := uchoice (fun o => Ffixd_rel a x o).

  Lemma Frd_eqn : forall a x o,
    isOrd o ->
    a ∈ A -> 
    x ∈ TIF o a ->
    Fixd_rec a x == G Fixd_rec a x.
intros.
unfold Fixd_rec.
generalize (uchoice_def _ (Ffixd_rel_choice_pred _ _ _ H H0 H1)); intro.
apply Ffixd_rel_inv in H2; auto.
 2:revert H1; apply TIF_Ffix; trivial.
destruct H2 as (g,(gm,(gext,Hg)),eqg).
rewrite eqg.
apply Gm; auto with *.
 revert H1; apply TIF_Ffix; trivial.
red; intros.
rewrite H5 in H4|-*; clear x0 H5.
rewrite H3 in H2, H4|-*; clear a' H3.
assert (x' ∈ TIF o a'').
 destruct fsub_elim with (4:=H1) (5:=H4); trivial.
 apply TIF_incl with x0; auto.
generalize (uchoice_def _ (Ffixd_rel_choice_pred _ _ _ H H2 H3)); intro.
specialize Hg with (1:=H2) (2:=H4).
apply Ffixd_rel_fun with (1:=Hg) (2:=H5).
apply Ffix_fsub_inv with x a; trivial.
revert H1; apply TIF_Ffix; trivial.
Qed.

End IterDep.
*)
(*
Section Iter.

Variable G : (set -> set) -> set -> set.
Hypothesis Gm : forall a x x' g g',
  a ∈ A ->
  x ∈ Ffix a ->
  (forall a', a' ∈ A -> eq_fun (fsub a a' x) g g') ->
  x == x' -> G g x == G g' x'.

Definition Ffix_rel x y :=
  forall R:set->set->Prop,
  Proper (eq_set ==> eq_set ==> iff) R ->
  (forall a x g,
   a ∈ A ->
   x ∈ Ffix a ->
   (forall a', a' ∈ A -> ext_fun (fsub a a' x) g) ->
   (forall a' y, a' ∈ A -> y ∈ fsub a a' x -> R y (g y)) ->
   R x (G g x)) ->
  R x y.

  Instance Ffix_rel_morph :
    Proper (eq_set ==> eq_set ==> iff) Ffix_rel.
apply morph_impl_iff2; auto with *.
do 5 red; intros.
rewrite <- H; rewrite <- H0; apply H1; trivial.
Qed.

  Lemma Ffix_rel_intro : forall a x g,
    a ∈ A ->
    x ∈ Ffix a ->
    (forall a', a' ∈ A -> ext_fun (fsub a a' x) g) ->
    (forall a' y, a' ∈ A -> y ∈ fsub a a' x -> Ffix_rel y (g y)) ->
    Ffix_rel x (G g x).
red; intros.
apply H4 with a; trivial; intros.
apply H2 with a'; trivial.
Qed.

  Lemma Ffix_rel_inv : forall a x o,
    a ∈ A ->
    x ∈ Ffix a ->
    Ffix_rel x o ->
    exists2 g,
      (forall a', a' ∈ A -> ext_fun (fsub a a' x) g) /\
      (forall a' y, a' ∈ A -> y ∈ fsub a a' x -> Ffix_rel y (g y)) &
      o == G g x.
intros a x o tya xFx Fr.
apply (@proj2 (Ffix_rel x o)).
revert a tya xFx.
apply Fr; intros.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 rewrite <- H in xFx.
 destruct (H1 _ tya xFx) as (?,(g,(?,?),?)); clear H1.
 split;[|exists g].
  rewrite <- H; rewrite <- H0; trivial.

  split; intros.
   red; red; intros; apply (H3 a'); trivial.
   rewrite H; trivial.

   rewrite <- H in H6; eauto.

  rewrite <- H0; rewrite H5.
  apply Gm with a; auto with *.

 split.
  apply Ffix_rel_intro with a0; auto.
  intros.
  apply H2 with a'; trivial.
  apply Ffix_fsub_inv with x0 a0; trivial.

  exists g.
   split; intros; auto.
   apply H2 with a' a'; trivial.
   apply Ffix_fsub_inv with x0 a0; trivial.

  apply Gm with a0; auto with *.
Qed.

  Lemma Ffix_rel_fun :
    forall x y, Ffix_rel x y ->
    forall a y', Ffix_rel x y' -> a ∈ A -> x ∈ Ffix a -> y == y'.
intros x y H.
apply H; intros.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 rewrite <- H1; rewrite <- H0 in H3,H5; eauto.
apply Ffix_rel_inv with (a:=a0) in H4; trivial.
destruct H4 as (g',(eg',Hg),eqy').
rewrite eqy'; clear y' eqy'.
apply Gm with a0; auto with *.
red; intros.
apply H3 with a' a'; trivial.
 rewrite H8 in H7|-*; eauto.

 apply Ffix_fsub_inv with x0 a0; trivial.
Qed.

Require Import ZFrepl.

  Lemma Ffix_rel_def : forall o x a, isOrd o -> a ∈ A -> x ∈ TIF o a ->
    exists y, Ffix_rel x y.
intros o x a oo; revert x a; apply isOrd_ind with (2:=oo); intros.
clear o oo H0.
assert (forall a z, a ∈ A -> z ∈ fsub a x -> uchoice_pred (fun o => Ffix_rel z o)).
 intros.
 destruct fsub_elim with (4:=H3) (5:=H4) as (y',lty',tyz); trivial.
 split; intros.
  rewrite <- H5; trivial.
 split; intros; eauto.
 apply Ffix_rel_fun with z a0; trivial.
 apply Ffix_fsub_inv with x a; trivial.
 apply TIF_Ffix with (o:=y); trivial.
exists (G (fun b => uchoice (fun o => Ffix_rel b o)) x).
apply Ffix_rel_intro with a; trivial.
 apply TIF_Ffix with (o:=y); trivial.

 do 2 red; intros.
 apply uchoice_morph_raw.
 red; intros.
 apply Ffix_rel_morph; trivial.
intros.
apply uchoice_def; eauto.
Qed.

  Lemma Ffix_rel_choice_pred : forall o x a, isOrd o -> a ∈ A -> x ∈ TIF o a ->
    uchoice_pred (fun o => Ffix_rel x o).
split; intros.
 rewrite <- H2; trivial.
split; intros.
 apply Ffix_rel_def with o a; trivial.
apply Ffix_rel_fun with x a; trivial.
revert H1; apply TIF_Ffix; trivial.
Qed.

  Definition Fix_rec x := uchoice (fun o => Ffix_rel x o).

  Lemma Fr_eqn : forall a x o,
    isOrd o ->
    a ∈ A -> 
    x ∈ TIF o a ->
    Fix_rec x == G Fix_rec x.
intros.
unfold Fix_rec.
generalize (uchoice_def _ (Ffix_rel_choice_pred _ _ _ H H0 H1)); intro.
destruct Ffix_rel_inv with (1:=H0) (3:=H2) as (g,(gext,Hg),eqg); auto.
 revert H1; apply TIF_Ffix; trivial.
rewrite eqg.
apply Gm with a; auto with *.
 revert H1; apply TIF_Ffix; trivial.
red; intros.
rewrite (gext _ H3 _ _ H4 H5).
rewrite H5 in H4; clear x0 H5.
assert (x' ∈ TIF o a').
 destruct fsub_elim with (4:=H1) (5:=H4); trivial.
 apply TIF_incl with x0; auto.
generalize (uchoice_def _ (Ffix_rel_choice_pred _ _ _ H H3 H5)); intro.
specialize Hg with (1:=H3) (2:=H4).
apply Ffix_rel_fun with x' a'; trivial.
revert H5; apply TIF_Ffix; trivial.
Qed.

End Iter.

  Definition F_a g x := osup (sup A (fun a => fsub a x)) (fun y => osucc (g y)).

  Lemma F_a_morph : forall x x' g g',
    (forall a', a' ∈ A -> eq_fun (fsub a' x) g g') ->
    x == x' -> F_a g x == F_a g' x'.
unfold F_a; intros.
apply osup_morph.
 apply sup_morph; auto with *.
 red; intros.
 rewrite H0; rewrite H2; reflexivity.

 red; intros.
 rewrite sup_ax in H1.
 2:do 2 red; intros; apply fsub_morph; auto with *.
 destruct H1.
 apply osucc_morph; apply (H x1); trivial.
Qed.
Hint Resolve F_a_morph.


  Lemma Fe1 : forall X, ext_fun X (fun b => osucc (Fix_rec F_a b)).
red; red; intros.
apply osucc_morph.
apply uchoice_morph_raw.
apply Ffix_rel_morph; trivial.
Qed.
Hint Resolve Fe1.

  Lemma F_a_ord : forall a x, a ∈ A -> x ∈ Ffix a -> isOrd (Fix_rec F_a x).
intros.
rewrite Ffix_def in H0; trivial.
destruct H0.
revert a x H H1; apply isOrd_ind with (2:=H0); intros.
rewrite Fr_eqn with (o:=y) (a:=a); auto.
apply isOrd_osup; trivial.
intros.
rewrite sup_ax in H5.
2:do 2 red; intros; apply fsub_morph; auto with *.
destruct H5.
apply isOrd_succ.
destruct fsub_elim with (4:=H4) (5:=H6); trivial.
eauto.
Qed.

Hint Resolve F_a_ord.

(*
  Hypothesis Fstab : forall X,
    X ⊆ power A ->
    inter (replf X F) ⊆ F (inter X).
*)
  Lemma F_intro : forall w,
    isOrd w ->
    forall a x, a ∈ A -> x ∈ TIF w a ->
    forall o, isOrd o ->
    (forall a' y, a' ∈ A -> y ∈ fsub a' x -> y ∈ TIF o a') ->
    x ∈ F (TIF o) a.
Admitted.
(*intros.
assert (True).
 auto.
(*assert (inter (replf (subset (power A) (fun X => x ∈ F X a)) (fun X => X))
        ⊆ TIF o a).
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
  apply power_intro; auto.*)
eapply (Fmono _ _ _ _ _ _ H0 _ H1).
apply (Fmono _ _ (fun y y' e => H3 _ y H0)).
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
*)
  Lemma F_a_tot : forall a x,
   a ∈ A ->
   x ∈ Ffix a ->
   x ∈ TIF (osucc (Fix_rec F_a x)) a.
intros.
rewrite Ffix_def in H0; trivial.
destruct H0.
revert a x H H1; apply isOrd_ind with (2:=H0); intros.
assert (incl_fam A (fun a => fsub a x) (TIF (Fix_rec F_a x))).
 do 2 red; intros.
 destruct fsub_elim with (4:=H4) (5:=H6); trivial.
 assert (xo : isOrd x1).
  apply isOrd_inv with y; trivial.
 assert (z ∈ TIF (osucc (Fix_rec F_a z)) a0).
  apply H2 with x1; trivial.
 revert H9; apply TIF_mono; auto.
  apply F_a_ord with a; trivial.
  rewrite Ffix_def; eauto.

  apply isOrd_succ; apply F_a_ord with a0; trivial.
  rewrite Ffix_def; eauto.

  red; intros.
  rewrite Fr_eqn with (o:=y) (a:=a); auto.
  unfold F_a at 1.
  apply osup_intro with (x:=z); trivial.
  rewrite sup_ax; eauto.
  do 2 red; intros; apply fsub_morph; auto with *.
rewrite TIF_mono_succ; auto.
2:apply F_a_ord with a; trivial; rewrite Ffix_def; eauto.
apply F_intro with y; trivial.
 apply F_a_ord with a; trivial; rewrite Ffix_def; eauto.

 do 2 red in H5; eauto.
Qed.

  Definition Ffix_ord a :=
    osup (Ffix a) (fun x => osucc (Fix_rec F_a x)).

  Lemma Ffix_o_o : forall a, a ∈ A -> isOrd (Ffix_ord a).
intros.
apply isOrd_osup; eauto.
Qed.
Hint Resolve Ffix_o_o.

  Lemma Ffix_post : incl_fam A Ffix (fun a => TIF (Ffix_ord a) a).
do 2 red; intros.
apply TIF_intro with (Fix_rec F_a z); auto.
 unfold Ffix_ord; apply osup_intro with (x:=z); trivial.
 apply lt_osucc; eauto.

 rewrite <- TIF_mono_succ; eauto.
 apply F_a_tot; trivial.
Qed.

(*
  Lemma Ffix_post : forall a x,
   a ∈ A ->
   x ∈ Ffix a ->
   x ∈ TIF (Ffix_ord a) a.
intros.
apply TIF_intro with (Fix_rec F_a x); auto.
 unfold Ffix_ord; apply osup_intro with (x:=x); trivial.
 apply lt_osucc; eauto.

 rewrite <- TIF_mono_succ; eauto.
 apply F_a_tot; trivial.
Qed.
*)

  Lemma Ffix_eqn : forall a, a ∈ A -> Ffix a == F Ffix a.
intros.
apply eq_intro; intros.
 rewrite Ffix_def in H0; trivial.
 destruct H0.
 apply (Fmono (TIF x)); trivial.
  apply TIF_morph; auto with *.

  admit.

  apply TIF_Ffix; trivial.

  rewrite <- TIF_mono_succ; auto.
  revert H1; apply TIF_incl; auto.

 assert (z ∈ TIF (osucc (Ffix_ord a)) a).
  rewrite TIF_mono_succ; auto.
  revert H0; apply Fmono; trivial.
   admit.

   apply TIF_morph; auto with *.

   do 2 red; intros.
   admit.
 rewrite Ffix_def; trivial.
 exists (osucc (Ffix_ord a)); auto.
Qed.
*)
(*
End BoundedOperator.
*)

End IterMonotone.

