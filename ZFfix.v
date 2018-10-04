Require Import ZF ZFrelations ZFwfr ZFnats ZFord ZFstable.

(** Transfinite iteration of a monotonic operator
 *)

(** * Elementary properties *)
Section IterMonotone.

  Variable F : set -> set.
  Variable Fmono : Proper (incl_set ==> incl_set) F.

  Let Fm := Fmono_morph _ Fmono.

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

Lemma TI_inv o x :
  isOrd o ->
  x ∈ TI F o ->
  exists2 o', o' ∈ o & x ∈ TI F (osucc o').
intros.
apply TI_elim in H0; trivial.
destruct H0 as (o',?,?).
exists o'; trivial.
rewrite TI_mono_succ; auto with *.
apply isOrd_inv with o; trivial.
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
(** Stability of ordinal-indexed families *)

Definition stable_ord := stable_class isOrd.

Lemma TI_stable K :
  Proper (eq_set ==> iff) K ->
  stable_class K F ->
  (forall o, isOrd o -> K (TI F o)) ->
  stable_ord (TI F).
intros Km Fs KTI.
cut (forall o, isOrd o ->
  forall X, o == inter X ->
  (forall x, x ∈ X -> isOrd x) ->
  inter (replf X (TI F)) ⊆ TI F (inter X)).
 do 2 red; intros.
 apply H with (inter X); auto with *.
 apply isOrd_inter; auto.
induction 1 using isOrd_ind; red; intros.
assert (eX : ext_fun X (TI F)).
 red; red; intros; apply TI_morph; trivial.
assert (eN : forall X, ext_fun X F).
 red; red; intros; apply Fm; trivial.
pose (Y := subset (union X) (fun y => z ∈ F (TI F y))).
assert (oY : forall y, y ∈ Y -> isOrd y).
 unfold Y; intros.
 apply subset_elim1 in H5.
 apply union_elim in H5; destruct H5.
 eauto using isOrd_inv.
assert (eY : ext_fun Y (TI F)).
 red; red; intros.
 apply TI_morph; trivial.
assert (wX : exists w, w ∈ X).
 destruct inter_non_empty with (1:=H4).
 rewrite replf_ax in H5; trivial.
 destruct H5.
 exists x0; trivial.
destruct wX as (wx,wX).
assert (wY : exists w, w ∈ Y).
 assert (z ∈ TI F wx).
  apply inter_elim with (1:=H4).
  rewrite replf_ax; trivial.
  exists wx; auto with *.
 apply TI_elim in H5; auto.
 destruct H5.
 exists x.
 apply subset_intro; trivial.
 apply union_intro with wx; trivial.
destruct wY as (wy,wY).
assert (ltY : lt (inter Y) (inter X)).
 apply inter_intro; eauto.
 intros.
 assert (z ∈ TI F y0).
  apply inter_elim with (1:=H4).
  rewrite replf_ax; trivial.
  exists y0; auto with *.
 apply TI_elim in H6; auto.
 destruct H6.
 apply isOrd_plump with x; auto.
  apply isOrd_inter; auto.

  red; intros.
  apply inter_elim with (1:=H8).
  apply subset_intro; trivial.
  apply union_intro with y0; trivial.
assert (inter (replf Y (TI F)) ⊆ TI F (inter Y)).
 apply H1 with (inter Y); auto with *.
 rewrite H2; trivial.
apply TI_intro with (inter Y); auto.
 apply isOrd_inter; auto.
apply Fmono with (1:=H5).
apply Fs.
 intros.
 rewrite replf_ax in H6; auto with *.
 destruct H6.
 rewrite H7; auto.
apply inter_intro.
 intros.
 rewrite replf_ax in H6; trivial.
 destruct H6.
 rewrite replf_ax in H6; trivial.
 destruct H6.
 apply subset_elim2 in H6; destruct H6.
 setoid_replace y0 with (F (TI F x1)); trivial.
 rewrite H7; apply Fm.
 rewrite H8; apply TI_morph; trivial.

 exists (F (TI F wy)).
 rewrite replf_ax; trivial.
 exists (TI F wy); auto with *.
 rewrite replf_ax; trivial.
 exists wy; auto with *.
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

Lemma TI_inA o : isOrd o -> TI F o ⊆ A.
induction 1 using isOrd_ind; intros.
rewrite TI_eq; auto.
apply sup_lub; auto with *.
Qed.

Lemma TI_Ffix : forall o, isOrd o -> TI F o ⊆ Ffix.
intros.
red; intros.
apply subset_intro.
 apply TI_inA in H0; auto.

 exists o; trivial.
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
  apply TI_inA in H0; trivial.

  exists a; auto with *.
  exists x; trivial.
Qed.

(** Showing Ffix is a fixpoint if collection holds *)

Section FixColl.

Hypothesis coll_ax :
  forall A (R:set->set->Prop), 
  Proper (eq_set ==> eq_set ==> iff) R ->
  exists B, forall x, x ∈ A ->
         (exists y, R x y) -> exists2 y, y ∈ B & R x y.


Lemma Ffix_fix_coll_stage : exists2 o, isOrd o & Ffix ⊆ TI F o.
pose (R := fun x o => isOrd o /\ x ∈ TI F o).
destruct coll_ax with (A:=Ffix) (R:=R) as (B,?).
 do 3 red; intros.
 unfold R; rewrite H; rewrite H0; reflexivity.
pose (o:=osup (subset B isOrd) (fun x => x)).
assert (oo : isOrd o).
 apply isOrd_osup.
  do 2 red; trivial.
  intros.
  apply subset_elim2 in H0; destruct H0.
  rewrite H0; trivial.
exists o; trivial.
red; intros.
destruct H with (1:=H0).
 rewrite Ffix_def in H0.
 destruct H0 as (o',?,?); exists o'; split; auto.

 destruct H2.
 revert H3; apply TI_mono; auto.
apply osup_intro with (f:=fun x=>x)(x:=x).
 do 2 red; trivial.

 apply subset_intro; trivial.
Qed.

Lemma Ffix_fix_coll : Ffix == F Ffix.
apply eq_intro; intros.
 rewrite Ffix_def in H.
 destruct H.
 apply TI_elim in H0; trivial.
 destruct H0 as (o,?,?).
 revert H1; apply Fmono.
 apply TI_Ffix.
 apply isOrd_inv with x; trivial.

 destruct Ffix_fix_coll_stage as (o,?,?).
 apply Fmono in H1.
 apply H1 in H.
 rewrite <- TI_mono_succ in H; trivial.
 revert H; apply TI_Ffix; auto.
Qed.

End FixColl.

(*(* The same, but with universe size *)
Section FixCollUniv.

Hypothesis coll_ax :
  forall A (R:set->set->Prop), 
  Proper (eq_set ==> eq_set ==> iff) R ->
  exists B, forall x, x ∈ A ->
         (exists y, R x y) -> exists2 y, y ∈ B & R x y.

Hypothesis K : set -> Prop.
Hypothesis Km : Proper (eq_set==>iff) K.
Hypothesis Kord : forall o, K o -> isOrd o.
Hypothesis Kord_sup : forall I f,
  morph1 f ->
  I ⊆ A ->
  (forall x, x ∈ I -> K (f x)) ->
  K (osup I f).

Definition Ffix' := subset A (fun a => exists o, K o /\ a ∈ TI F o).
(*
Lemma Ffix_inA' : Ffix' ⊆ A.
red; intros.
apply subset_elim1 in H; trivial.
Qed.
*)
Lemma Ffix_def' : forall a, a ∈ Ffix' <-> exists2 o, K o & a ∈ TI F o.
unfold Ffix'; intros.
rewrite subset_ax.
split; intros.
 destruct H.
 destruct H0.
 destruct H1.
 destruct H1.
 exists x0; trivial.
 rewrite H0; trivial.

 destruct H.
 split.
  apply Ffix_inA.
  revert a H0; apply TI_Ffix; auto.

  exists a; auto with *.
  exists x; auto.
Qed.

Lemma Ffix_fix_coll_stage' : exists2 o, K o & Ffix' ⊆ TI F o.
pose (R := fun x o => K o /\ x ∈ TI F o).
destruct coll_ax with (A:=Ffix') (R:=R) as (B,?).
 do 3 red; intros.
 unfold R; rewrite H; rewrite H0; reflexivity.
pose (o:=osup (subset B K) (fun x => x)).
assert (oo : K o).
 apply Kord_sup.
  do 2 red; trivial.

  red; intros.
  apply subset_elim2 in H0; destruct H0.
  intros.
  apply subset_elim2 in H0; destruct H0.
  rewrite H0; auto.
trivial.
exists o; trivial.
red; intros.
destruct H with (1:=H0).
 rewrite Ffix_def in H0.
 destruct H0 as (o',?,?); exists o'; split; auto.

 destruct H2.
 revert H3; apply TI_mono; auto.
apply osup_intro with (f:=fun x=>x)(x:=x).
 do 2 red; trivial.

 apply subset_intro; trivial.
Qed.

Lemma Ffix_fix_coll : Ffix == F Ffix.
apply eq_intro; intros.
 rewrite Ffix_def in H.
 destruct H.
 apply TI_elim in H0; trivial.
 destruct H0 as (o,?,?).
 revert H1; apply Fmono.
 apply TI_Ffix.
 apply isOrd_inv with x; trivial.

 destruct Ffix_fix_coll_stage as (o,?,?).
 apply Fmono in H1.
 apply H1 in H.
 rewrite <- TI_mono_succ in H; trivial.
 revert H; apply TI_Ffix; auto.
Qed.

End FixColl.
*)

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

Definition G' F a :=
  cond_set (a ∈ Ffix) (G F a).

Lemma G'm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) G'.
do 3 red; intros.
apply cond_set_morph2.
 rewrite H0; reflexivity.

 intros.
 apply Gm; trivial.
 red; intros. 
 apply H; trivial.
Qed.

Lemma G'ext : forall x x' g g',
  x ∈ Ffix ->
  eq_fun (fsub x) g g' ->
  x == x' -> G' g x == G' g' x'.
intros.
apply cond_set_morph.
 rewrite H1; reflexivity.

 apply Gm; trivial.
Qed.


Definition Fix_rec := WFR (fun b a => b ∈ fsub a) G'.

Instance Fix_rec_morph0 : morph1 Fix_rec.
do 2 red; intros.
apply WFR_morph0; auto with *.
Qed.

(*
Lemma fsub_acc o x:
  isOrd o ->
  x ∈ TI F o ->
  Acc (fun b a => b ∈ fsub a) x.
 apply Ffix_def in H1; destruct H1 as (o',oo',tyx).
intros oo; revert x; elim oo using isOrd_ind; intros.
constructor; intros.
destruct fsub_elim with (2:=H2) (3:=H3) as (z,lty,tyy0); trivial.
eauto.
Qed.
*)

Lemma Fr_eqn : forall a o,
    isOrd o ->
    a ∈ TI F o ->
    Fix_rec a == G Fix_rec a.
intros.
transitivity (G' Fix_rec a).
 unfold Fix_rec.
 apply WFR_eqn_gen; intros.
  clear; do 3 red; intros; rewrite H,H0; reflexivity. 

  apply G'm.

  apply G'ext; auto with *.
  apply Ffix_def.
  exists o; trivial.  

  revert a H0; elim H using isOrd_ind; intros.
  constructor; intros. 
  destruct fsub_elim with (2:=H3) (3:=H4) as (z,ltx,tyy0); eauto.

 unfold G'; apply cond_set_ok.
 apply TI_Ffix in H0; trivial.  
Qed.

  Lemma Fix_rec_typ U2 a :
    (forall x g, ext_fun (fsub x) g -> x ∈ Ffix ->
        (forall y, y ∈ fsub x -> g y ∈ U2) -> G g x ∈ U2) ->
    a ∈ Ffix ->
    Fix_rec a ∈ U2.
intros.
rewrite Ffix_def in H0; destruct H0.
revert a H1.
induction H0 using isOrd_ind; intros.
rewrite (Fr_eqn _ _) with (2:=H3); trivial. (*!*)
apply H.
 do 2 red; intros.
 apply Fix_rec_morph0; trivial.

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
rewrite H0; reflexivity.
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
  Hypothesis Fstab : stable_class (fun X => X ⊆ Ffix) F.

  Lemma F_intro : forall w,
    isOrd w ->
    forall a, a ∈ TI F w ->
    a ∈ F (fsub a).
intros.
pose (F1a := subset (power Ffix) (fun X => a ∈ F X)).
assert (fx_ok : Ffix ∈ F1a).
 apply subset_intro.
  apply power_intro; trivial.

  apply TI_elim in H0; auto.
  destruct H0.
  revert H1; apply Fmono.
  apply TI_Ffix; trivial.
  apply isOrd_inv with w; trivial.
assert (inter (replf F1a (fun X => X)) ⊆ fsub a).
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
 intros.
 rewrite replf_ax in H2.
 2:do 2 red; trivial.
 destruct H2.
 apply subset_elim1 in H2.
 rewrite H3; red; intros.
 apply power_elim with (1:=H2); trivial.

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

  Lemma TI_clos_stages o : isOrd o -> TI F o ⊆ TI F Ffix_ord.
intros.
transitivity Ffix.
 apply TI_Ffix; trivial.

 red; intros; apply Ffix_post; trivial.
Qed.

  Lemma TI_clos_fix_eqn : TI F Ffix_ord == F (TI F Ffix_ord).
apply eq_set_ax; intros z.
rewrite <- TI_mono_succ; trivial.
split; intros.
 revert H; apply TI_incl; auto.

 apply TI_clos_stages in H; auto.
Qed.
 

  Lemma Ffix_closure : Ffix == TI F Ffix_ord.
apply incl_eq.
 red; intros; apply Ffix_post; trivial.

 apply TI_Ffix; trivial.
Qed.

(** We prove Ffix is a fixpoint *)
  Lemma Ffix_eqn : Ffix == F Ffix.
rewrite Ffix_closure.
apply TI_clos_fix_eqn.
Qed.

(*BEGIN alt*)
(** Functions defined by recursion on subterms *)
Section Iter2.

Variable G : (set -> set) -> set -> set.
Hypothesis Gm : forall x x' g g',
  x ∈ Ffix ->
  eq_fun (fsub x) g g' ->
  x == x' -> G g x == G g' x'.

Definition G'' F a :=
  cond_set (a ∈ Ffix) (G F a).

Lemma G''m : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) G''.
do 3 red; intros.
apply cond_set_morph2.
 rewrite H0; reflexivity.

 intros.
 apply Gm; trivial.
 red; intros. 
 apply H; trivial.
Qed.

Lemma G''ext : forall x x' g g',
  (x ∈ Ffix -> eq_fun (fsub x) g g') ->
  x == x' -> G'' g x == G'' g' x'.
intros.
apply cond_set_morph2.
 rewrite H0; reflexivity.

 intros.
 apply Gm; auto.
Qed.
(*
Lemma G''ext : forall x x' g g',
  x ∈ Ffix ->
  eq_fun (fsub x) g g' ->
  x == x' -> G'' g x == G'' g' x'.
intros.
apply cond_set_morph.
 rewrite H1; reflexivity.

 apply Gm; trivial.
Qed.
*)

Definition Fix_rec' :=
  WFR (fun b a => b ∈ Ffix /\ b ∈ fsub a) G''.

Instance Fix_rec_morph0' : morph1 Fix_rec'.
do 2 red; intros.
apply WFR_morph; auto with *.
 do 2 red; intros.
 rewrite H0,H1; reflexivity.

 apply G''m.
Qed.

(*
Lemma fsub_acc o x:
  isOrd o ->
  x ∈ TI F o ->
  Acc (fun b a => b ∈ fsub a) x.
 apply Ffix_def in H1; destruct H1 as (o',oo',tyx).
intros oo; revert x; elim oo using isOrd_ind; intros.
constructor; intros.
destruct fsub_elim with (2:=H2) (3:=H3) as (z,lty,tyy0); trivial.
eauto.
Qed.
*)

Lemma Fr_eqn' : forall a o,
    isOrd o ->
    a ∈ TI F o ->
    Fix_rec' a == G Fix_rec' a.
intros.
transitivity (G'' Fix_rec' a).
 unfold Fix_rec'.
 apply WFR_eqn; intros.
  do 3 red; intros.
  rewrite H1,H2; reflexivity. 
  apply G''m.

  apply G''ext; auto with *.
  clear H1; red; intros.
  apply H2; auto.  
  split; trivial.
  apply Ffix_fsub_inv with x; trivial.

  revert a H0.
  elim H using isOrd_ind; intros.  
  constructor.
  destruct 1; trivial.
  destruct fsub_elim with (2:=H3) (3:=H5) as (z,ltx,tyy0); eauto.

 unfold G''; apply cond_set_ok.
 apply TI_Ffix in H0; trivial.  
Qed.

  Lemma Fix_rec_typ' U2 a :
    (forall x g, ext_fun (fsub x) g -> x ∈ Ffix ->
        (forall y, y ∈ fsub x -> g y ∈ U2) -> G g x ∈ U2) ->
    a ∈ Ffix ->
    Fix_rec' a ∈ U2.
intros.
rewrite Ffix_def in H0; destruct H0.
revert a H1.
induction H0 using isOrd_ind; intros.
rewrite (Fr_eqn' _ _) with (2:=H3); trivial. (*!*)
apply H.
 do 2 red; intros.
 apply Fix_rec_morph0'; trivial.

 apply TI_Ffix with y; trivial.

 intros.
 apply fsub_elim with (o:=y) in H4; trivial.
 destruct H4.
 apply H2 with x0; trivial.
Qed.

End Iter2.

  Lemma Fe1' : forall X, ext_fun X (fun b => osucc (Fix_rec' F_a b)).
red; red; intros.
rewrite H0; reflexivity.
Qed.
Hint Resolve Fe1'.

  Lemma F_a_ord' : forall a, a ∈ Ffix -> isOrd (Fix_rec' F_a a).
intros.
rewrite Ffix_def in H; destruct H.
revert a H0; apply isOrd_ind with (2:=H); intros.
rewrite Fr_eqn' with (o:=y); auto.
apply isOrd_osup; trivial.
intros.
apply isOrd_succ.
destruct fsub_elim with (2:=H3) (3:=H4); trivial.
eauto.
Qed.

Hint Resolve F_a_ord'.

  Lemma F_a_tot' : forall a,
   a ∈ Ffix ->
   a ∈ TI F (osucc (Fix_rec' F_a a)).
intros.
rewrite Ffix_def in H; destruct H.
revert a H0; apply isOrd_ind with (2:=H); intros.
assert (ao : isOrd (Fix_rec' F_a a)).
 apply F_a_ord'; rewrite Ffix_def; exists y; trivial.
rewrite TI_mono_succ; auto.
assert (fsub a ⊆ TI F (Fix_rec' F_a a)).
 red; intros.
 destruct fsub_elim with (2:=H3) (3:=H4); trivial.
 assert (xo : isOrd x0).
  apply isOrd_inv with y; trivial.
 assert (z ∈ TI F (osucc (Fix_rec' F_a z))).
  apply H2 with x0; trivial.
 revert H7; apply TI_mono; auto.
  apply isOrd_succ; apply F_a_ord'; rewrite Ffix_def; exists x0; trivial.

  red; intros.
  rewrite Fr_eqn' with (o:=y); auto.
  unfold F_a.
  apply osup_intro with (x:=z); trivial.
apply Fmono in H4.
apply H4.
apply F_intro with y; trivial.
Qed.
(** The closure ordinal *)
  Definition Ffix_ord' :=
    osup Ffix (fun a => osucc (Fix_rec' F_a a)).

  Lemma Ffix_o_o' : isOrd Ffix_ord'.
apply isOrd_osup; auto.
Qed.
Hint Resolve Ffix_o_o'.

  Lemma Ffix_post' : forall a,
   a ∈ Ffix ->
   a ∈ TI F Ffix_ord'.
intros.
apply TI_intro with (Fix_rec' F_a a); auto.
 apply osup_intro with (x:=a); trivial.
 apply lt_osucc; auto.

 rewrite <- TI_mono_succ; auto.
 apply F_a_tot'; trivial.
Qed.

  Lemma TI_clos_stages' o : isOrd o -> TI F o ⊆ TI F Ffix_ord'.
intros.
transitivity Ffix.
 apply TI_Ffix; trivial.

 red; intros; apply Ffix_post'; trivial.
Qed.

  Lemma TI_clos_fix_eqn' : TI F Ffix_ord' == F (TI F Ffix_ord').
apply eq_set_ax; intros z.
rewrite <- TI_mono_succ; trivial.
split; intros.
 revert H; apply TI_incl; auto.

 apply TI_clos_stages' in H; auto.
Qed.
 

  Lemma Ffix_closure' : Ffix == TI F Ffix_ord'.
apply incl_eq.
 red; intros; apply Ffix_post'; trivial.

 apply TI_Ffix; trivial.
Qed.

(** We prove Ffix is a fixpoint *)
  Lemma Ffix_eqn' : Ffix == F Ffix.
rewrite Ffix_closure'.
apply TI_clos_fix_eqn'.
Qed.

(*END*)  
End BoundedOperator.


End IterMonotone.

Lemma TI_mono_gen G G' o o' :
  morph1 G ->
  morph1 G' ->
  (incl_set==>incl_set)%signature G G' ->
  isOrd o ->
  isOrd o' ->
  o ⊆ o' ->
  TI G o ⊆ TI G' o'.
intros.
revert o' H3 H4.
elim H2 using isOrd_ind; intros.
red; intros.
apply TI_elim in H8; trivial.
destruct H8 as (y',y'o,?).
apply TI_intro with y'; auto.
 apply H7; trivial.

 revert H8; apply H1.
 apply H5; auto with *.
 apply isOrd_inv with y; trivial.
Qed.

Instance Ffix_morph : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) Ffix. 
do 3 red; intros.
unfold Ffix.
apply subset_morph; trivial.
red; intros.
apply ex2_morph'; intros.
reflexivity.
apply in_set_morph.
reflexivity.
apply TI_morph_gen; trivial.
reflexivity.
Qed.

Instance fsub_morph_gen :
  Proper ((eq_set==>eq_set)==>eq_set==>eq_set==>eq_set) fsub.
do 4 red; intros.
unfold fsub.
apply subset_morph.
 apply Ffix_morph; trivial.
 red; intros.
 apply fa_morph; intros X.
 apply impl_morph.
  apply incl_set_morph.
  reflexivity.
  apply Ffix_morph; trivial.

  intros.
  rewrite (H _ _ (reflexivity X)), H1.  
  reflexivity.
Qed.
Local Notation E := eq_set (only parsing).

Instance Fix_rec_morph :
  Proper ((E==>E)==>E==>((E==>E)==>E==>E)==>E==>E) Fix_rec. 
do 5 red; intros.
unfold Fix_rec.
apply WFR_morph; trivial.
 do 2 red; intros.
 apply in_set_morph; trivial.
 apply fsub_morph_gen; trivial.

 do 2 red; intros.
 apply cond_set_morph.
  apply in_set_morph; trivial.
  apply Ffix_morph; trivial.

  apply H1; trivial.
Qed.

Instance F_a_morph_gen :
  Proper ((eq_set==>eq_set)==>eq_set==>(eq_set==>eq_set)==>eq_set==>eq_set) F_a.
do 5 red; intros.
unfold F_a.
apply osup_morph.
apply fsub_morph_gen; trivial.
red; intros.
apply osucc_morph.
apply H1; trivial.
Qed.
  
Instance Ffix_ord_morph : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) Ffix_ord. 
do 3 red; intros.
unfold Ffix_ord.
apply osup_morph.
 apply Ffix_morph; trivial.

 red; intros.
 apply osucc_morph.
 apply Fix_rec_morph; trivial.
 do 2 red; intros.
 apply F_a_morph_gen; trivial.
Qed.

  Lemma TI_op_mono o o' f f' :
    morph1 f ->
    morph1 f' -> 
    (incl_set ==> incl_set)%signature f f' ->
    isOrd o ->
    o == o' ->
    TI f o ⊆ TI f' o'.
intros.
rewrite <- H3.
clear o' H3.
elim H2 using isOrd_ind; intros.
red; intros.
apply TI_elim in H6; trivial.
destruct H6.
apply TI_intro with x; trivial.
revert H7; apply H1; auto.
Qed.


Section BoundIndep.

Variable F : set -> set.
Hypothesis Fmono : Proper (incl_set ==> incl_set) F.
Let Fm : morph1 F := Fmono_morph F Fmono.
Variable A : set.
Hypothesis Ftyp : forall X, X ⊆ A -> F X ⊆ A.
Variable A' : set.
Hypothesis Ftyp' : forall X, X ⊆ A' -> F X ⊆ A'.

Lemma Ffix_indep : Ffix F A == Ffix F A'.
apply eq_intro; intros.
 rewrite Ffix_def in H|-*; trivial.
 rewrite Ffix_def in H|-*; trivial.
Qed.

Lemma fsub_indep x :
  fsub F A x == fsub F A' x.
apply subset_morph.
 apply Ffix_indep.

 red; intros.
 apply fa_morph; intros X.
 apply impl_morph; auto with *.
 rewrite Ffix_indep; reflexivity.
Qed.

Lemma Ffix_ord_indep :
  Ffix_ord F A == Ffix_ord F A'.
unfold Ffix_ord.
apply osup_morph.
 apply Ffix_indep.

 red; intros.
 apply osucc_morph.
 apply WFR_morph; trivial.
  do 2 red; intros.
  rewrite <- H2.
  apply in_set_morph; auto with *.
  apply fsub_indep.

  do 3 red; intros.
  unfold F_a.
  apply cond_set_morph.
   apply in_set_morph; trivial.
   apply Ffix_indep.

   apply osup_morph.
    rewrite H2; apply fsub_indep.

    red; intros.
    apply osucc_morph; apply H1; trivial.
Qed.

End BoundIndep.

(** * Construction of the fixpoint "from above" *)

Section KnasterTarski.

Variable A : set.
Variable F : set -> set.

Hypothesis Fmono : Proper (incl_set==>incl_set) F.
Hypothesis Ftyp : forall x, x ⊆ A -> F x ⊆ A.


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

