Require Export basic ZF.
Require Import ZFnats.

(* This file is the same as ZFord, but defines regular plump
   ordinals (whereas ZFord defines directed plump ordinals).
   This is just for the record. Directed ordinals have better
   properties w.r.t. limits (upper bounds).
 *)

Fixpoint plump ub (p:Acc in_set ub) x : Prop :=
  (forall y (q: y ∈ ub), y ∈ x -> plump y (Acc_inv p _ q) y) /\
  (forall z y (q: y ∈ ub), plump y (Acc_inv p _ q) z ->
   z ⊆ y -> y ∈ x -> z ∈ x).

Lemma plump_morph : forall x x' p p' y y',
  x == x' -> y == y' -> (plump x p y <-> plump x' p' y').
intros x x' p; revert x'.
induction p using Acc_indd; simpl; intros.
destruct p'; simpl.
split; destruct 1; split; intros.
 assert (q' := q).
 rewrite <- H0 in q'.
 rewrite <- H1 in H4.
 rewrite <- (H y0 q' _ _ y0 y0); auto with *.

 assert (q' := q).
 rewrite <- H0 in q'.
 rewrite <- H1 in H6|-*.
 rewrite <- (H y0 q' _ _ z z) in H4; eauto with *.

 assert (q' := q).
 rewrite H0 in q'.
 rewrite H1 in H4.
 rewrite (H _ _ y0 (a0 _ q') _ y0); auto with *.

 assert (q' := q).
 rewrite H0 in q'.
 rewrite H1 in H6|-*.
 rewrite (H _ _ y0 (a0 _ q') _ z) in H4; eauto with *.
Qed.

Lemma plump_bound : forall ub1 ub2 p1 p2 x,
 x ⊆ ub1 ->
 plump ub1 p1 x -> plump ub2 p2 x.
destruct p1; destruct p2; simpl; intros.
destruct H0.
split; intros.
 assert (y ∈ ub1).
  apply H; trivial.
 rewrite (plump_morph _ y _ (a _ H3) _ y); auto with *.

 assert (y ∈ ub1).
  apply H; trivial.
 rewrite (plump_morph _ y _ (a _ H5) _ z) in H2; auto with *.
 apply H1 with y H5; auto.
Qed.

Lemma plump_Acc : forall ub p x,
  plump ub p x -> x ⊆ ub -> Acc in_set x.
induction p using Acc_indd; simpl; intros.
destruct H0.
constructor; intros.
apply H with y (H1 _ H3); auto with *.
Qed.


Definition isOrd x :=
  { p:Acc in_set x | plump x p x }.

Lemma isOrd_ext : forall x y, x == y -> isOrd x -> isOrd y.
destruct 2.
generalize x0; rewrite H; intro.
exists H0.
rewrite <- (plump_morph x y x0 H0 x y); trivial.
Qed.

Instance isOrd_morph : Proper (eq_set ==> iff) isOrd.
do 2 red; split; intros.
 apply isOrd_ext with x; trivial.

 symmetry in H.
 apply isOrd_ext with y; trivial.
Qed.

Lemma isOrd_inv : forall x y,
  isOrd x -> lt y x -> isOrd y.
intros.
destruct H.
exists (Acc_inv x0 _ H0).
destruct x0; simpl in *.
destruct p; auto.
Qed.


Lemma isOrd_plump : forall z, isOrd z ->
 forall x y, isOrd x -> x ⊆ y -> y ∈ z -> x ∈ z.
destruct 1; intros.
revert p.
destruct x;simpl; intros.
destruct p.
apply H3 with y H1; trivial.
destruct H.
apply plump_bound with (2:=p); reflexivity.
Qed.


Lemma isOrd_intro : forall x,
  (forall a b, isOrd a -> a ⊆ b -> b ∈ x -> a ∈ x) ->
  (forall y, y ∈ x -> isOrd y) ->
  isOrd x.
intros.
exists (Acc_intro _ (fun y h => proj1_sig (H0 y h))); simpl.
split; intros.
 destruct (H0 y H1).
 rewrite <- (plump_morph y y x0 _ y y); auto with *.

 apply H with y; trivial.
 exists (plump_Acc _ _ _ H1 H2).
 apply plump_bound with (2:=H1); trivial.
Qed.


Lemma isOrd_trans : forall x y z,
  isOrd x -> lt z y -> lt y x -> lt z x.
unfold lt.
destruct 1.
revert y z p.
induction x0 using Acc_indd; simpl; intros.
assert (isOrd x).
 exists (Acc_intro _ a); simpl; trivial.
destruct p.
apply isOrd_plump with y; trivial.
 apply isOrd_inv with y; trivial.
 apply isOrd_inv with x; trivial.

 red; intros.
 apply H with H1 z; auto.
Qed.

Lemma isOrd_ind : forall x (P:set->Prop),
  (forall y, isOrd y ->
   y ⊆ x ->
   (forall z, lt z y -> P z) -> P y) ->
  isOrd x -> P x.
intros.
destruct H0.
cut (forall x', x' == x -> P x'); auto with *.
revert p H .
induction x0 using Acc_indd; simpl; intros.
destruct p.
assert (isOrd x).
 exists (Acc_intro _ a); simpl; split; trivial.
apply H0; intros; auto with *.
 rewrite H1; trivial.

 red; intros.
 rewrite <- H1; trivial.

rewrite H1 in H5.
clear x' H1.
apply H with (r:=H5); intros; auto with *.
apply H0; intros; auto.
red; intros.
apply isOrd_trans with z; auto.
apply H6; trivial.
Qed.

Lemma lt_antirefl : forall x, isOrd x -> ~ lt x x.
induction 1 using isOrd_ind; intros.
red; intros; apply H1 with y; trivial.
Qed.


Lemma isOrd_zero : isOrd zero.
apply isOrd_intro; intros.
 elim empty_ax with b; trivial.
 elim empty_ax with y; trivial.
Qed.


Definition osucc x := subset (power x) isOrd.

Instance osucc_morph : morph1 osucc.
unfold osucc; do 2 red; intros.
apply subset_morph.
 rewrite H; reflexivity.

 red; auto with *.
Qed.

Lemma lt_osucc : forall x, isOrd x -> lt x (osucc x).
unfold osucc, lt; intros.
apply subset_intro; trivial.
apply power_intro; auto.
Qed.

Hint Resolve isOrd_zero lt_osucc.

Lemma olts_le : forall x y, lt x (osucc y) -> x ⊆ y.
red; intros.
apply subset_elim1 in H.
apply power_elim with (1:=H); trivial.
Qed.

Lemma ole_lts : forall x y, isOrd x -> x ⊆ y -> lt x (osucc y).
intros.
apply subset_intro; trivial.
apply power_intro; trivial.
Qed.

Lemma oles_lt : forall x y,
  isOrd x ->
  osucc x ⊆ y ->
  lt x y.
intros.
apply H0.
apply lt_osucc; trivial.
Qed.

Lemma le_lt_trans : forall x y z, isOrd z -> lt x (osucc y) -> lt y z -> lt x z.
intros.
apply isOrd_plump with y; trivial.
 apply subset_elim2 in H0; destruct H0.
 rewrite H0; trivial.

 apply olts_le; trivial.
Qed.

Lemma isOrd_succ : forall n, isOrd n -> isOrd (osucc n).
unfold osucc.
intros.
apply isOrd_intro; intros.
 apply subset_intro; trivial.
 apply subset_elim1 in H2.
 apply power_intro; intros.
 apply H1 in H3.
 apply power_elim with (1:=H2); trivial.

 apply subset_elim2 in H0.
 destruct H0.
 rewrite H0; trivial.
Qed.
Hint Resolve isOrd_succ.

Lemma lt_osucc_compat : forall n m, isOrd m -> lt n m -> lt (osucc n) (osucc m).
intros.
apply ole_lts; auto.
 apply isOrd_succ.
 apply isOrd_inv with m; trivial.

 red; intros.
 apply le_lt_trans with n; trivial.
Qed.

  Lemma lt_osucc_inv : forall o o',
    isOrd o ->
    lt (osucc o) (osucc o') ->
    lt o o'.
unfold osucc; intros.
rewrite subset_ax in H0; destruct H0.
destruct H1.
rewrite power_ax in H0.
apply H0.
apply subset_intro; trivial.
apply power_intro; auto.
Qed.

Lemma isOrd_eq : forall o, isOrd o -> o == sup o osucc.
intros.
apply eq_intro; intros.
 rewrite sup_ax.
 2:do 2 red; intros; apply osucc_morph; trivial.
 exists z; auto.
 apply lt_osucc.
 apply isOrd_inv with o; trivial.

 rewrite sup_ax in H0.
 2:do 2 red; intros; apply osucc_morph; trivial.
 destruct H0.
 apply le_lt_trans with x; trivial.
Qed.

Module Examples.

Definition ord_0 := empty.
Definition ord_1 := osucc ord_0.
Definition ord_2 := osucc ord_1.

(* 1 = {0} *)
Lemma ord1 : forall x, x ∈ osucc zero <-> x == zero.
intros.
unfold osucc.
rewrite subset_ax.
split; intros.
 destruct H.
 rewrite power_ax in H.
 apply empty_ext.
 red; intros.
 apply H in H1.
 apply empty_ax with (1:=H1).

 split.
  apply power_intro; intros.
  rewrite H in H0; trivial.

  exists zero; auto.
Qed.

Definition ord_rk_1 P := subset ord_1 (fun _ => P).

Lemma rk1_order : forall P Q, ord_rk_1 P ⊆ ord_rk_1 Q <-> (P->Q).
split; intros.
 assert (zero ∈ ord_rk_1 P).
  apply subset_intro; trivial.
  unfold ord_1; apply lt_osucc; auto.
 apply H in H1.
 apply subset_elim2 in H1.
 destruct H1; trivial.

 red; intros.
 apply subset_intro.
  apply subset_elim1 in H0; trivial.

  apply subset_elim2 in H0.
  destruct H0; auto.
Qed.

Lemma isOrd_rk_1 : forall P, isOrd (ord_rk_1 P).
intros.
apply isOrd_intro; intros.
 unfold ord_rk_1 in H1; rewrite subset_ax in H1; destruct H1.
 destruct H2.
 clear x H2.
 apply subset_intro; auto.
 apply isOrd_plump with b; auto.
 unfold ord_1; auto.

 apply subset_elim1 in H.
 apply isOrd_inv with (osucc zero); auto.
Qed.

Definition isOrd2 x := exists P:Prop, x == ord_rk_1 P.

(* 2 = {o| 0<=o<=1 } isomorphic to Prop *)
Lemma ord2 : forall x, x ∈ ord_2 <-> exists P, x == ord_rk_1 P.
intros.
unfold ord_2, osucc at 1.
rewrite subset_ax.
rewrite power_ax.
split; intros.
 destruct H.
 destruct H0.
 rewrite <- H0 in H1; clear H0 x0.
 exists (zero ∈ x).
 apply subset_ext; intros; auto.
  apply ord1 in H0.
  rewrite H0; trivial.

  exists x0; auto with *.
  specialize H with (1:=H0).
  apply ord1 in H.
  rewrite H in H0; trivial.

 destruct H.
 split; intros.
  rewrite H in H0; clear H x.
  apply subset_elim1 with (1:=H0).

  exists x; auto with *.
  rewrite H.
  apply isOrd_rk_1.
Qed.


Definition ord_rk_2 (P2:Prop->Prop) :=
  subset ord_2 (fun x => exists2 P, x == ord_rk_1 P & P2 P).

Definition decr_2 (P2:Prop->Prop) := forall P Q:Prop, (P -> Q) -> (P2 Q -> P2 P).

Lemma isOrd_rk_2 : forall P2, decr_2 P2 -> isOrd (ord_rk_2 P2).
intros.
apply isOrd_intro; intros.
 assert (a ∈ ord_2).
  apply isOrd_plump with b; auto.
  unfold ord_2, ord_1; auto.
  apply subset_elim1 in H2; trivial.
 apply subset_intro; auto.
 rewrite ord2 in H3.
 destruct H3.
 exists x; trivial.
 unfold ord_rk_2 in H2; rewrite subset_ax in H2; destruct H2.
 destruct H4.
 destruct H5.
 apply (H x x1); trivial.
 rewrite H4 in H1; rewrite H5 in H1; rewrite H3 in H1.
 rewrite <- rk1_order; trivial.

 apply subset_elim1 in H0.
 apply isOrd_inv with (osucc (osucc zero)); auto.
Qed.

(* 3 is isomorphic to decreasing functions of type Prop->Prop *)
Lemma ord3 : forall x,
  x ∈ osucc ord_2 <-> exists2 P2, decr_2 P2 & x == ord_rk_2 P2.
intros.
unfold osucc.
rewrite subset_ax.
rewrite power_ax.
split; intros.
 destruct H.
 destruct H0.
 rewrite <- H0 in H1; clear H0 x0.
 exists (fun P => ord_rk_1 P ∈ x).
  red; intros.
  apply isOrd_plump with (ord_rk_1 Q); trivial.
   assert (ord_rk_1 P ∈ ord_2).
    rewrite ord2.
    exists P; auto with *.
   apply isOrd_inv with ord_2; auto.
   unfold ord_2, ord_1; auto.

   rewrite rk1_order; trivial.

  apply subset_ext; intros; auto.
   apply ord2 in H0.
   destruct H2.
   rewrite H2; trivial.
   exists x0; auto with *.
   specialize H with (1:=H0).
   apply ord2 in H.
   destruct H.
   exists x1; trivial.
   rewrite H in H0; trivial.

 destruct H.
 split; intros.
  rewrite H0 in H1; clear H0 x.
  apply subset_elim1 with (1:=H1).

  exists x; auto with *.
  rewrite H0.
  apply isOrd_rk_2; trivial.
Qed.


End Examples.


(* Increasing *)

Definition increasing F :=
  forall x y, isOrd x -> isOrd y -> y ⊆ x -> F y ⊆ F x.
(*
Definition directed o F :=
  forall o', isOrd o -> lt o' o -> F o' ⊆ F o.
*)
Definition increasing_bounded o F :=
  forall x x', lt x' o -> lt x x' -> F x ⊆ F x'.

Definition succOrd o := exists2 o', isOrd o' & o == osucc o'.

(* Limit ordinals *)

Definition limitOrd o := isOrd o /\ (forall x, lt x o -> lt (osucc x) o).

Lemma limit_is_ord : forall o, limitOrd o -> isOrd o.
destruct 1; trivial.
Qed.
Hint Resolve limit_is_ord.

Lemma limit_union : forall o, limitOrd o -> union o == o.
destruct 1.
apply eq_intro; intros.
 apply union_elim in H1; destruct H1.
 apply isOrd_trans with x; trivial.

 apply union_intro with (osucc z).
  apply lt_osucc.
  apply isOrd_inv with o; trivial.

  apply H0; trivial.
Qed.

Lemma limit_union_intro : forall o, isOrd o -> union o == o -> limitOrd o.
split; trivial.
unfold lt; intros.
assert (isOrd x).
 apply isOrd_inv with o; trivial.
rewrite <- H0 in H1.
apply union_elim in H1; destruct H1.
apply isOrd_plump with x0; auto.
red; intros.
apply le_lt_trans with x; trivial.
apply isOrd_inv with o; trivial.
Qed.

Lemma discr_lim_succ : forall o, limitOrd o -> succOrd o -> False.
destruct 1; destruct 1.
assert (lt (osucc x) o).
 apply H0.
 rewrite H2; auto.
rewrite <- H2 in H3.
elim lt_antirefl with o; trivial.
Qed.


Lemma isOrd_union2 : forall x y,
  isOrd x ->
  isOrd y ->
  isOrd (x ∪ y).
intros.
apply isOrd_intro; intros.
 apply union2_elim in H3; destruct H3.
  apply union2_intro1.
  apply isOrd_plump with b; trivial.

  apply union2_intro2.
  apply isOrd_plump with b; trivial.

 apply union2_elim in H1; destruct H1.
  apply isOrd_inv with x; trivial.
  apply isOrd_inv with y; trivial.
Qed.

Lemma isOrd_inter2 : forall x y,
  isOrd x -> isOrd y -> isOrd (x ∩ y).
intros.
apply isOrd_intro; intros.
 rewrite inter2_def in H3|-*; destruct H3; split.
  apply isOrd_plump with b; trivial.
  apply isOrd_plump with b; trivial.

 apply inter2_incl1 in H1.
 apply isOrd_inv with x; trivial.
Qed.

Lemma inter2_succ : forall x y,
  isOrd x -> isOrd y ->
  osucc x ∩ osucc y == osucc (x ∩ y).
intros.
apply eq_intro; intros.
 rewrite inter2_def in H1.
 destruct H1.
 apply ole_lts; eauto using isOrd_inv.
 apply olts_le in H1; apply olts_le in H2.
 red; intros; rewrite inter2_def; auto.

 assert (isOrd z).
  apply isOrd_inv with (osucc (x ∩ y)); trivial.
  apply isOrd_succ; apply isOrd_inter2; trivial.
 rewrite inter2_def; split.
  apply ole_lts; eauto using isOrd_inv.
  apply olts_le in H1.
  transitivity (x ∩ y); trivial.
  apply inter2_incl1.

  apply ole_lts; eauto using isOrd_inv.
  apply olts_le in H1.
  transitivity (x ∩ y); trivial.
  apply inter2_incl2.
Qed.


Module NotDirected.
Import Examples.
Section S.

 Variable P Q:Prop.

 Definition a := ord_rk_2 (fun A => (A->P) \/ (A->Q)).

 Lemma P_in_a : ord_rk_1 P ∈ a.
unfold a, ord_rk_2.
apply subset_intro.
 rewrite ord2.
 exists P; auto with *.

 exists P; auto with *.
Qed.

 Lemma PQ_in_a : ord_rk_1 (P\/Q) ∈ a -> (P->Q) \/ (Q->P).
unfold a, ord_rk_2; intros.
apply subset_elim2 in H; destruct H.
destruct H0.
rewrite H0 in H.
assert (P\/Q->x0).
 rewrite <- rk1_order.
 rewrite H; reflexivity.
tauto.
Qed.

End S.
End NotDirected.


Section OrdinalUpperBound.

  Variable I : set.
  Variable f : set -> set.
  Hypothesis f_ext : ext_fun I f.
  Hypothesis f_ord : forall x, x ∈ I -> isOrd (f x).

  Lemma isOrd_supf_intro : forall n, n ∈ I -> f n ⊆ sup I f.
red; intros.
rewrite sup_ax; trivial.
exists n; trivial.
Qed.

  Lemma isOrd_supf_elim : forall x, lt x (sup I f) -> exists2 n, n ∈ I & lt x (f n).
intros.
rewrite sup_ax in H; trivial.
Qed.

  Lemma isOrd_supf : isOrd (sup I f).
apply isOrd_intro; intros.
 elim isOrd_supf_elim with (1:=H1); intros.
 apply isOrd_supf_intro with x; trivial.
 apply isOrd_plump with b; auto.

 elim isOrd_supf_elim with (1:=H); intros.
 apply isOrd_inv with (f x); auto.
Qed.

End OrdinalUpperBound.

(* Projection toward ordinals *)

Definition toOrd (x : set) :=
  sup (subset x isOrd) osucc.

Instance toOrd_morph : morph1 toOrd.
do 2 red; intros.
unfold toOrd.
apply sup_morph.
 apply subset_morph; auto with *.

 red; intros; rewrite H1; reflexivity.
Qed.

Lemma toOrd_isOrd : forall x, isOrd (toOrd x).
intros.
unfold toOrd.
apply isOrd_supf; intros.
 red; red; intros.
 rewrite H0; reflexivity.

 apply isOrd_succ.
 destruct subset_elim2 with (1:=H).
 rewrite H0; trivial.
Qed.

Lemma toOrd_ord : forall o, isOrd o -> toOrd o == o.
intros.
unfold toOrd.
apply eq_intro; intros.
 rewrite sup_ax in H0.
 2:red; red; intros; rewrite H2; reflexivity.
 destruct H0.
 apply le_lt_trans with x; auto.
 apply subset_elim1 with (1:=H0).

 rewrite sup_ax.
 2:red; red; intros; rewrite H2; reflexivity.
 exists z.
  apply subset_intro; trivial.
  apply isOrd_inv with o; trivial.

  apply lt_osucc.
  apply isOrd_inv with o; trivial.
Qed.



Section TransfiniteRecursion.

  Variable F : (set -> set) -> set -> set.

  Variable ord : set.
  Hypothesis Fmorph : forall o o' f f', isOrd o -> o ⊆ ord ->
    o == o' -> eq_fun o f f' -> F f o == F f' o'.

  Definition TR_rel o y := (isOrd o/\o⊆ ord) /\
    forall (P:set->set->Prop),
    (forall o o' x x', isOrd o -> o ⊆ ord -> o == o' -> x == x' -> P o x -> P o' x') ->
    (forall o' f, isOrd o' -> o' ⊆ ord -> ext_fun o' f ->
     (forall n, lt n o' -> P n (f n)) ->
     P o' (F f o')) ->
    P o y.

  Instance TR_rel_morph : Proper (eq_set ==> eq_set ==> iff) TR_rel.
apply morph_impl_iff2; auto with *.
do 4 red; unfold TR_rel; intros.
destruct H1 as ((xo, xle),Hrec); split; intros.
 rewrite <- H; auto.

 apply (H1 x y x0 y0); auto.
 apply Hrec; auto.
Qed.

  Lemma TR_rel_intro : forall x f,
    isOrd x ->
    x ⊆ ord ->
    ext_fun x f ->
    (forall y, y ∈ x -> TR_rel y (f y)) ->
    TR_rel x (F f x).
red; intros.
split; intros; auto.
apply H4; trivial; intros.
apply H2; trivial.
Qed.

  Lemma TR_rel_inv : forall x y,
    TR_rel x y ->
    exists2 f,
      ext_fun x f /\ (forall y, y ∈ x -> TR_rel y (f y)) &
      y == F f x.
intros.
apply (@proj2 (TR_rel x y)).
destruct H as ((H,Hle),H0).
apply H0; intros.
 destruct H5; split.
  rewrite <- H3; rewrite <- H4; trivial.

  destruct H6 as (f,(fm,eqf),eqF); exists f; trivial.
   split; intros.
    do 2 red; intros.
    rewrite <- H3 in H6; auto.
    rewrite <- H3 in H6; auto.

    rewrite <- H4; rewrite eqF; auto.
assert (TR_relsub := fun n h => proj1 (H4 n h)); clear H4.
split.
 apply TR_rel_intro; trivial.

 exists f; auto with *.
Qed.


  Lemma TR_rel_fun :
    forall x y, TR_rel x y -> forall y', TR_rel x y' -> y == y'.
intros x y (xo,H).
apply H; intros.
 rewrite <- H3; rewrite <- H2 in H5; auto.
apply TR_rel_inv in H4; destruct H4.
destruct H4.
rewrite H5; clear y' H5.
apply Fmorph; intros; auto with *.
red; intros.
apply H3; trivial.
rewrite H7 in H5|-*; auto.
Qed.

Require Import ZFrepl.

  Lemma TR_rel_repl_rel :
    forall x, repl_rel x TR_rel.
split; intros.
 rewrite <- H0; rewrite <- H1; trivial.

 apply TR_rel_fun with x0; trivial.
Qed.

  Lemma TR_rel_def : forall o, isOrd o -> o ⊆ ord -> exists y, TR_rel o y.
induction 1 using isOrd_ind; intros.
assert (forall z, lt z y -> uchoice_pred (fun y => TR_rel z y)).
 intros.
 destruct H1 with z; trivial.
  red; intros; apply H2; apply isOrd_trans with z; trivial.
 split; intros.
  rewrite <- H5; trivial.
 split; intros.
  exists x; trivial.
 apply TR_rel_fun with z; trivial.
exists (F (fun z => uchoice (fun y => TR_rel z y)) y).
apply TR_rel_intro; intros; trivial.
 do 2 red; intros.
 apply uchoice_morph; intros; auto.
 rewrite H5; reflexivity.
apply uchoice_def; auto.
Qed.

  Lemma TR_rel_choice_pred : forall o, isOrd o -> o ⊆ ord ->
    uchoice_pred (fun y => TR_rel o y).
split; intros.
 rewrite <- H1; trivial.
split; intros.
 apply TR_rel_def; trivial.
apply TR_rel_fun with o; trivial.
Qed.

  Definition TR := uchoice (fun y => TR_rel ord y).

(*
  Lemma TR_morph : forall x x', isOrd x -> x == x' -> TR x == TR x'.
intros.
unfold TR.
unfold uchoice.
apply union_morph.
apply eq_intro; intros.
 rewrite repl_ax in H1; intros.
  rewrite repl_ax; intros.
   destruct H1.
   destruct H2.
   exists x0; trivial.
   exists x1; trivial.
   revert H3; apply basic.iff_impl.
   apply TR_rel_morph; auto with *.

   apply TR_rel_fun with x'; trivial.

  apply TR_rel_fun with x; trivial.

 rewrite repl_ax in H1; intros.
  rewrite repl_ax; intros.
   destruct H1.
   destruct H2.
   exists x0; trivial.
   exists x1; trivial.
   revert H3; apply basic.iff_impl.
   apply TR_rel_morph; auto with *.

   apply TR_rel_fun with x; trivial.

  apply TR_rel_fun with x'; trivial.
Qed.
*)

  Lemma TR_eqn0 : forall o, isOrd o -> o ⊆ ord ->
     uchoice (fun y => TR_rel o y) == F (fun o => uchoice (fun y => TR_rel o y)) o.
intros.
specialize TR_rel_choice_pred with (1:=H) (2:=H0); intro.
apply uchoice_def in H1.
apply TR_rel_inv in H1.
destruct H1.
destruct H1.
rewrite H2.
apply Fmorph; intros; auto with *.
red; intros.
apply TR_rel_fun with x'.
 rewrite <- H5; auto.

 apply uchoice_def.
 apply TR_rel_choice_pred.
 rewrite <- H5; apply isOrd_inv with o; trivial.
 red; intros; apply H0; apply isOrd_trans with x'; trivial.
 rewrite <- H5; trivial.
Qed.

End TransfiniteRecursion.

  Lemma TR_rel_irrel : forall F b1 b2 o y,
    o ⊆ b2 ->
    TR_rel F b1 o y -> TR_rel F b2 o y.
intros.
revert H; apply H0; intros.
 rewrite <- H2 in H5.
 generalize (H4 H5).
 apply TR_rel_morph; auto with *.

 apply TR_rel_intro; trivial; intros.
 apply H3; trivial.
 transitivity o'; trivial.
 red; intros; apply isOrd_trans with y0; trivial.
Qed.

  Instance TR_morph : forall F, morph1 (TR F).
do 2 red; intros.
unfold TR.
apply uchoice_morph_raw.
red; intros.
transitivity (TR_rel F x y y0).
 apply TR_rel_morph; trivial. 

 split; apply TR_rel_irrel; auto with *.
 rewrite H; reflexivity.
Qed.

  Lemma TR_morph_gen : forall o o' F F',
    isOrd o ->
    (forall x x' f f', isOrd x -> x ⊆ o -> x == x' -> eq_fun x f f' -> F f x == F' f' x') ->
    o == o' -> TR F o == TR F' o'.
unfold TR; intros.
apply uchoice_morph_raw.
red; intros.
split; intros.
 red; intros.
 destruct H3; split.
  rewrite <- H1; trivial.

  intros.
  destruct H3.
  apply H5 with o x; trivial.
   rewrite H1; reflexivity.

   apply H4; intros.
    rewrite H1 in H9; eauto.

    rewrite H1 in H9.
    apply H5 with o'0 (F' f o'0); auto with *.
    symmetry; apply H0; auto with *.
    rewrite H1; trivial.

 red; intros.
 destruct H3; split.
  rewrite H1; trivial.

  intros.
  destruct H3.
  apply H5 with o' y; auto with *.
   rewrite H1; reflexivity.

   apply H4; intros.
    rewrite <- H1 in H9; eauto.

    rewrite <- H1 in H9.
    apply H5 with o'0 (F f o'0); auto with *.
Qed.

  Lemma TR_eqn : forall F o,
    isOrd o ->
    (forall x x' f f', isOrd x -> x ⊆ o -> x == x' -> eq_fun x f f' -> F f x == F f' x') ->
    TR F o == F (TR F) o.
intros.
unfold TR; rewrite TR_eqn0; eauto with *.
apply H0; auto with *.
red; intros.
apply uchoice_morph_raw.
red; intros.
transitivity (TR_rel F o x' y).
 apply TR_rel_morph; trivial.
rewrite H2 in H1.
split; apply TR_rel_irrel; auto with *.
red; intros; apply isOrd_trans with x'; trivial.
Qed.

  Lemma TR_ind : forall F o (P:set->set->Prop),
    (forall x x' f f', isOrd x -> x ⊆ o -> x == x' -> eq_fun x f f' -> F f x == F f' x') ->
    (forall x, isOrd x -> x ⊆ o ->
     forall y y', y == y' -> P x y -> P x y') ->
    isOrd o ->
    (forall y, isOrd y -> y ⊆ o ->
     (forall x, lt x y -> P x (TR F x)) ->
     P y (F (TR F) y)) ->
    P o (TR F o).
induction 3 using isOrd_ind; intros.
apply H0 with (F (TR F) y); auto with *.
 symmetry; apply TR_eqn; trivial; intros.
 apply H; auto.
 transitivity y; trivial.
apply H4; trivial; intros.
 reflexivity.
apply H3; trivial; intros.
apply H4; trivial.
red; intros; apply isOrd_trans with x; auto.
apply H7; trivial.
Qed.

  Lemma TR_typ : forall F o X,
    isOrd o ->
    (forall x x' f f', isOrd x -> x ⊆ o -> x == x' -> eq_fun x f f' -> F f x == F f' x') ->
    morph1 X ->
    (forall y f, isOrd y -> y ⊆ o ->
     (forall z, lt z y -> f z ∈ X z) -> F f y ∈ X y) ->
    TR F o ∈ X o.
intros F o X oo Fm Xm Hrec.
apply TR_ind; intros; auto.
rewrite <- H1; trivial.
Qed.

(* Specialized version where the case of limit ordinals is union *)
Section TransfiniteIteration.

  Variable F : set -> set.
  Hypothesis Fmorph : Proper (eq_set ==> eq_set) F.

Let G f o := sup o (fun o' => F (f o')).

Lemma Gmorph : forall o o' f f',
    o == o' -> eq_fun o f f' -> G f o == G f' o'.
unfold G; intros.
apply sup_morph; trivial.
red; auto.
Qed.
Hint Resolve Gmorph.

  Definition TI := TR G.

(*
  Lemma TI_morph : forall x x', isOrd x -> x == x' -> TI x == TI x'.
unfold TI; intros.
apply TR_morph; auto with *.
Qed.
*)
  Instance TI_morph : morph1 TI.
unfold TI; do 2 red; intros.
apply TR_morph; auto with *.
Qed.

  Lemma TI_fun_ext : forall x, ext_fun x (fun y => F (TI y)).
do 2 red; intros.
apply Fmorph.
apply TI_morph; trivial.
(*apply isOrd_inv with x; trivial.*)
Qed.
(*
  Lemma TI_fun_ext : forall x, isOrd x -> ext_fun x (fun y => F (TI y)).
do 2 red; intros.
apply Fmorph.
apply TI_morph; trivial.
apply isOrd_inv with x; trivial.
Qed.
*)
Hint Resolve TI_fun_ext.

  Lemma TI_eq : forall o,
    isOrd o ->
    TI o == sup o (fun o' => F (TI o')).
intros.
unfold TI.
apply TR_eqn; auto.
Qed.

  Lemma TI_intro : forall o o' x,
    isOrd o ->
    lt o' o ->
    x ∈ F (TI o') ->
    x ∈ TI o.
intros.
rewrite TI_eq; trivial.
rewrite sup_ax; auto.
exists o'; trivial.
Qed.

  Lemma TI_elim : forall o x,
    isOrd o ->
    x ∈ TI o ->
    exists2 o', lt o' o & x ∈ F (TI o').
intros.
rewrite TI_eq in H0; trivial.
rewrite sup_ax in H0; auto.
Qed.

  Lemma TI_initial : TI zero == empty.
apply empty_ext; red; intros.
apply TI_elim in H.
 destruct H.
 elim empty_ax with (1:=H).

 apply isOrd_zero.
Qed.

  Lemma TI_typ : forall n X,
    (forall a, a ∈ X -> F a ∈ X) ->
    isOrd n ->
    (forall m G, isOrd m -> m ⊆ n ->
     ext_fun m G ->
     (forall x, lt x m -> G x ∈ X) -> sup m G ∈ X) ->
    TI n ∈ X.
induction 2 using isOrd_ind; intros.
rewrite TI_eq; trivial.
apply H3 with (G:=fun o => F (TI o)); intros; auto with *.
apply H.
apply H2; trivial; intros.
apply H3; auto.
red; intros.
apply H6 in H9.
apply isOrd_trans with x; trivial.
Qed.

End TransfiniteIteration.
Hint Resolve TI_fun_ext.


(********************************************************************)

Require Import ZFrepl.

Section LimOrd.

  Variable f : nat -> set.
  Variable ford : forall n, isOrd (f n).

  Definition ord_sup :=
    union (repl N (fun x y => exists2 n, x == nat2set n & f n == y)).

  Lemma repl_sup : 
    repl_rel N (fun x y => exists2 n, x == nat2set n & f n == y).
split; intros.
 destruct H2.
 exists x0.
  rewrite <- H0; trivial.
  rewrite <- H1; trivial.

 destruct H0.
 destruct H1.
 rewrite <- H2; rewrite <- H3.
 replace x1 with x0; try reflexivity.
 apply nat2set_inj.
 rewrite <- H0; trivial.
Qed.

  Lemma isOrd_sup_intro : forall n, f n ⊆ ord_sup.
unfold ord_sup.
red; intros.
apply union_intro with (f n); trivial.
apply repl_intro with (nat2set n).
 exact repl_sup.

 apply nat2set_typ.

 exists n; reflexivity.
Qed.

  Lemma isOrd_sup_elim : forall x, lt x ord_sup -> exists n, lt x (f n).
unfold ord_sup; intros.
elim union_elim with (1:=H); clear H; intros.
elim repl_elim with (1:=repl_sup) (2:=H0); intros.
destruct H2.
exists x2.
rewrite H3; trivial.
Qed.

  Lemma isOrd_sup : isOrd ord_sup.
apply isOrd_intro; intros.
 elim isOrd_sup_elim with (1:=H1); intros.
 apply isOrd_sup_intro with x.
 apply isOrd_plump with b; auto.

 elim isOrd_sup_elim with (1:=H); intros.
 apply isOrd_inv with (f x); trivial.
Qed.

End LimOrd.


Lemma isOrd_union : forall x,
  (forall y, y ∈ x -> isOrd y) -> isOrd (union x).
intros.
apply isOrd_intro; intros.
 rewrite union_ax in H2|-*; destruct H2.
 exists x0; trivial.
 apply isOrd_plump with b; auto.

 rewrite union_ax in H0; destruct H0. 
 apply isOrd_inv with x0; auto.
Qed.

Lemma isOrd_inter : forall x,
  (forall y, y ∈ x -> isOrd y) -> isOrd (inter x).
intros.
apply isOrd_intro; intros.
 apply inter_intro; trivial.
  intros.
  apply isOrd_plump with b; auto.
  apply inter_elim with (1:=H2); trivial.

  destruct inter_non_empty with (1:=H2); eauto.

 destruct inter_non_empty with (1:=H0).
 eauto using isOrd_inv.
Qed.

Fixpoint nat2ordset n :=
  match n with
  | 0 => zero
  | S k => osucc (nat2ordset k)
  end.

Lemma nat2ordset_typ : forall n, isOrd (nat2ordset n).
induction n; simpl; intros.
 apply isOrd_zero.
 apply isOrd_succ; trivial.
Qed.
Hint Resolve nat2ordset_typ.

(* Ordinal omega *)

Definition omega := ord_sup nat2ordset.

Lemma isOrd_omega : isOrd omega.
apply isOrd_sup; trivial.
Qed.
Hint Resolve isOrd_omega.

Lemma zero_omega : lt zero omega.
apply isOrd_sup_intro with 1; simpl.
apply lt_osucc; trivial.
Qed.
Hint Resolve zero_omega.

Lemma osucc_omega : forall n, lt n omega -> lt (osucc n) omega.
intros.
apply isOrd_sup_elim in H; destruct H.
apply isOrd_sup_intro with (S x); simpl.
apply lt_osucc_compat; auto.
Qed.
Hint Resolve osucc_omega.

Lemma omega_limit_ord : limitOrd omega.
split; auto.
Qed.
Hint Resolve omega_limit_ord.


Definition isDir o := forall x y,
    lt x o -> lt y o -> exists2 z, lt z o & x ⊆ z /\ y ⊆ z.

  Lemma isDir_omega : isDir omega.
red; intros.
apply isOrd_sup_elim in H.
destruct H.
apply isOrd_sup_elim in H0.
destruct H0.
exists (nat2ordset (Peano.max x0 x1)).
 apply isOrd_sup_intro with (f:=nat2ordset) (n:=S(Peano.max x0 x1)).
  simpl.
  apply lt_osucc.
  apply nat2ordset_typ.

 split; red; intros.
  destruct (le_gt_dec x0 x1).
   rewrite Peano.max_r; auto with arith.
   apply isOrd_trans with x; trivial.
   clear H1; revert x H.
   elim l; simpl; intros; auto.
   apply isOrd_trans with (nat2ordset m); auto.

   rewrite Peano.max_l; auto with arith.
   apply isOrd_trans with x; trivial.

  destruct (le_gt_dec x0 x1).
   rewrite Peano.max_r; auto with arith.
   apply isOrd_trans with y; trivial.

   rewrite Peano.max_l; auto with arith.
   apply isOrd_trans with y; trivial.
   clear H1; revert y H0.
   elimtype (x1 <= x0)%nat; simpl; intros; auto with arith.
   apply isOrd_trans with (nat2ordset m); auto.
Qed.

Hint Resolve isDir_omega.

(* Higher ordinals *)

Inductive ord : Set := OO | OS (o:ord) | OL (f:nat->ord).

Fixpoint ord2set (o:ord) : set :=
  match o with
  | OO => zero
  | OS k => osucc (ord2set k)
  | OL f => ord_sup (fun k => ord2set (f k)) 
  end.

Lemma ord2set_typ : forall o, isOrd (ord2set o).
induction o; simpl; intros.
 apply isOrd_zero.
 apply isOrd_succ; trivial.
 apply isOrd_sup; trivial.
Qed.
Hint Resolve ord2set_typ.

(* f^w(o) *)
Definition iter_w (f:set->set) o :=
  ord_sup(nat_rect(fun _=>set) o (fun _ => f)).

Lemma isOrd_iter_w : forall f o,
  (forall x, isOrd x -> isOrd (f x)) ->
  isOrd o ->
  isOrd (iter_w f o).
intros.
unfold iter_w.
apply isOrd_sup.
induction n; simpl; intros; auto.
Qed.

Definition plus_w := iter_w osucc.
