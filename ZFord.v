Require Import Arith.
Require Import ZFnats ZFwf ZFwfr.
Require Export ZF.

(** This file defines and develop the basic theory of ordinals in
    intuitionistic set theory. We use directed plump ordinals.
 *)

(** * Definition and elementary properties *)

Definition trans (K : set -> Prop) := forall x y, K x -> y ∈ x -> K y.
Definition plump (K : set -> Prop) := forall x y, K x -> y ⊆ x -> K y.

Instance trans_morph : Proper (pointwise_relation set iff ==> iff) trans.
do 2 red; intros.
unfold trans.
apply fa_morph; intros x0.
apply fa_morph; intros y0.
apply impl_morph; [trivial|intros].
apply fa_morph; intros; auto.
Qed.


Instance plump_morph : Proper (pointwise_relation set iff ==> iff) plump.
do 2 red; intros.
unfold plump.
apply fa_morph; intros x0.
apply fa_morph; intros y0.
apply impl_morph; [trivial|intros].
apply fa_morph; intros; auto.
Qed.

(** Directed set (finite union) *)
Definition isDir o := forall x y,
  x < o -> y < o -> exists2 z, z < o & x ⊆ z /\ y ⊆ z.

#[global]Instance isDir_morph : Proper (eq_set==>iff) isDir.
do 2 red; intros; unfold isDir.
apply fa_morph; intros x0.
apply fa_morph; intros y0.
rewrite H.
apply fa_morph; intros _.
apply fa_morph; intros _.
apply ex2_morph; red; intros; auto with *.
rewrite H; reflexivity.
Qed.

(** Directed plump ordinals.

   Plumpness is the property that
   forall ordinal x s.t. z ⊆ y ∈ x, we have z ∈ x

   Since the plumpness property is not monotonic (if we have more
   ordinals, the plumpness requirement becomes tighter), we could
   not separate the directedness property from the plumpness one.

   Even if plumpness is not monotonic, it can be defined by recursion
   over the rank (since the rank of z is smaller than that of x). So
   we go by first defining well-founded sets (cf ZFwf.v), then
   well-founded, and finally define plumpness.
 *)

(** Any property could replace directedness *)
Local Notation Q:=isDir.
Local Notation Qm:=isDir_morph.

(** Not resorting to higher-order: *)

Section FirstOrder.

(** The set of plump ordinals included in ub, given [f] the sets of plump ordinals
    of smaller rank. *)
Let plump_set f ub :=
   subset (power ub)
    (fun x =>
      isWf x /\             
      (forall y, y ∈ ub -> y ∈ x -> y ∈ f y) /\
      (forall z y, y ∈ ub -> z ∈ f y -> z ⊆ y -> y ∈ x -> z ∈ x) /\
      Q x).
(*
Let R x y := isWf x /\ x ∈ y.

Local Instance Rmorph : Proper (eq_set==>eq_set==>iff) R.
unfold R; do 3 red; intros.
rewrite H,H0; reflexivity.
Qed.
*)
Definition plumps := WFR (fun x=>x) plump_set.

Let plumps_m :
  Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) plump_set.
do 3 red; intros; unfold plump_set.
apply subset_morph.
 apply power_morph; trivial.

 red; intros.
 apply and_iff_morphism; auto with *.
 apply and_iff_morphism.
  apply fa_morph; intros yy.
  rewrite <- H0.
  rewrite (H _ _ (reflexivity _)); reflexivity.

  apply and_iff_morphism; auto with *.
  apply fa_morph; intros zz.
  apply fa_morph; intros yy.
  rewrite H0; rewrite (H _ _ (reflexivity _)); reflexivity.
Qed.

Let isWf_accR x : isWf x -> Acc in_set x.
intros.
apply isWf_ind with (2:=H); intros.
constructor; auto.
Qed.

Let plump_eqn ub x :
  isWf ub ->
  (x ∈ plumps ub <->
   x ⊆ ub /\
   (forall y, y ∈ ub -> y ∈ x -> y ∈ plumps y) /\
   (forall z y, y ∈ ub -> z ∈ plumps y -> z ⊆ y -> y ∈ x -> z ∈ x) /\
   Q x).
intro.
revert x; induction H using isWf_ind; intros.
unfold plumps at 1; rewrite WFR_eqn; fold plumps; trivial with *.
*unfold plump_set; rewrite subset_ax.
 rewrite power_ax.
 apply and_iff_morphisml; auto with *.
  intros _ xincla.
  split; intros.
   destruct H1 as (x',?,(?&?&?&?)).
   split; [|split]; intros; try rewrite H1 in *; eauto.

   exists x; auto with *.
   split; auto.
   apply isWf_incl with a; trivial.

*auto with *.   

*intros.
 apply subset_morph; [rewrite H3; reflexivity|].
 red; intros.
 apply and_iff_morphisml; auto with *.
 intros _ wfx1.
 apply and_iff_morphism.
  apply fa_morph; intros y.
  rewrite <- H3.
  apply fa_morph; intros h0.
  apply fa_morph; intros h1.
  rewrite (H2 y y); auto with *.
 apply and_iff_morphism; auto with *.
 apply fa_morph; intros z.
 apply fa_morph; intros y.
 rewrite <- H3.
 apply fa_morph; intros h.
 split; intros.
  apply H5; trivial.
  rewrite (H2 y y); auto with *.

  apply H5; trivial.
  rewrite <- (H2 y y); auto with *.

*apply isWf_accR; trivial.
Qed.

Instance plumps_morph : morph1 plumps.
do 2 red; intros; unfold plumps.
apply WFR_morph; trivial.
red; trivial.
Qed.

Lemma plump_bound : forall ub1 ub2 x,
 isWf ub1 ->
 isWf ub2 ->
 x ⊆ ub2 ->
 x ∈ plumps ub1 -> x ∈ plumps ub2.
intros.
rewrite plump_eqn in H2|-*; trivial.
destruct H2 as (?,(?,(?,?))).
eauto 10.
Qed.

(** The class of directed plump ordinals *)
Definition isOrd x := isWf x /\ x ∈ plumps x.

Lemma isOrd_wf o : isOrd o -> isWf o.
destruct 1; trivial.
Qed.
Hint Resolve isOrd_wf : core.

Lemma isOrd_ext : forall x y, x == y -> isOrd x -> isOrd y.
destruct 2.
unfold isOrd; rewrite H in H0,H1; auto.
Qed.

#[global]Instance isOrd_morph : Proper (eq_set ==> iff) isOrd.
do 2 red; split; intros.
 apply isOrd_ext with x; trivial.

 symmetry in H.
 apply isOrd_ext with y; trivial.
Qed.

Lemma isOrd_inv : forall x y,
  isOrd x -> y < x -> isOrd y.
intros.
destruct H.
split.
 apply isWf_inv with x; trivial.

 rewrite plump_eqn in H1; trivial.
 destruct H1 as (_,(?,_)); auto.
Qed.

Lemma isOrd_plump : forall z, isOrd z ->
 forall x y, isOrd x -> x ⊆ y -> y ∈ z -> x ∈ z.
destruct 1; intros.
rewrite plump_eqn in H0; trivial.
destruct H0 as (_,(_,(?,_))).
apply H0 with y; auto with *.
destruct H1.
apply plump_bound with x; auto with *.
apply isWf_inv with z; trivial.
Qed.

Lemma isOrd_dir : forall z, isOrd z -> Q z.
destruct 1; intros.
rewrite plump_eqn in H0; trivial.
destruct H0 as (_,(_,(_,?))); trivial.
Qed.

Lemma isOrd_intro : forall x,
  (forall a b, isOrd a -> a ⊆ b -> b ∈ x -> a ∈ x) ->
  Q x ->
  (forall y, y ∈ x -> isOrd y) ->
  isOrd x.
intros.
assert (wfx : isWf x).
 apply isWf_intro; intros; apply isOrd_wf; apply H1; trivial.
split; trivial.
rewrite plump_eqn; trivial.
split; [|split;[|split]]; intros; auto with *.
 apply H1; trivial.

 apply H with y; trivial.
 assert (wfy : isWf y).
  apply isWf_inv with x; trivial.
 assert (wfz : isWf z).
  apply isWf_intro; intros; apply isWf_inv with y; auto.
 split; trivial.
 apply plump_bound with y; auto with *.
Qed.

Lemma isOrd_trans : forall x y z,
  isOrd x -> z < y -> y < x -> z < x.
unfold lt.
intros.
assert (isWf x) by auto.
revert H y z H0 H1.
induction H2 using isWf_ind; intros.
apply isOrd_plump with y; auto.
 apply isOrd_inv with y; trivial.
 apply isOrd_inv with a; trivial.

 red; intros.
 apply H with z; trivial.
 apply isOrd_inv with a; trivial.
Qed.

Lemma isOrd_ind : forall x (P:set->Prop),
  (forall y, isOrd y ->
   y ⊆ x ->
   (forall z, z < y -> P z) -> P y) ->
  isOrd x -> P x.
intros.
assert (isWf x).
 destruct H0; trivial.
cut (forall x', x' == x -> P x'); auto with *.
revert H0 H .
induction H1 using isWf_ind; simpl; intros.
apply H2; intros; auto with *.
 rewrite H3; trivial.

 rewrite H3; reflexivity.

 rewrite H3 in H4; clear x' H3.
 apply H with z; auto with *.
  apply isOrd_inv with a; trivial.

  intros; apply H2; trivial.
  red; intros; apply isOrd_trans with z; auto.
Qed.
End FirstOrder.

(** Alternative definition of ordinals, slightly shorter by using Coq's accessibility
   predicate, and the plump property below by well-founded induction.
 *)
Module HigherOrder.

Fixpoint plump ub (p:Acc in_set ub) x : Prop :=
  (forall y (q: y ∈ ub), y ∈ x -> plump y (Acc_inv p _ q) y) /\
  (forall z y (q: y ∈ ub), plump y (Acc_inv p _ q) z ->
   z ⊆ y -> y ∈ x -> z ∈ x) /\
  isDir x.

Lemma plump_morph : forall x x' p p' y y',
  x == x' -> y == y' -> (plump x p y <-> plump x' p' y').
intros x x' p; revert x'.
induction p using Acc_indd; simpl; intros.
destruct p'; simpl.
split; destruct 1 as (?,(?,?)); (split; [|split]); intros.
 assert (q' := q).
 rewrite <- H0 in q'.
 rewrite <- H1 in H5.
 rewrite <- (H y0 q' _ _ y0 y0); auto with *.

 assert (q' := q).
 rewrite <- H0 in q'.
 rewrite <- H1 in H7|-*.
 rewrite <- (H y0 q' _ _ z z) in H5; eauto with *.

 red; intros.
 destruct H4 with x0 y0.
  rewrite H1; trivial.
  rewrite H1; trivial.
  exists x1; trivial.
  rewrite <- H1; trivial.

 assert (q' := q).
 rewrite H0 in q'.
 rewrite H1 in H5.
 rewrite (H _ _ y0 (a0 _ q') _ y0); auto with *.

 assert (q' := q).
 rewrite H0 in q'.
 rewrite H1 in H7|-*.
 rewrite (H _ _ y0 (a0 _ q') _ z) in H5; eauto with *.

 red; intros.
 destruct H4 with x0 y0.
  rewrite <- H1; trivial.
  rewrite <- H1; trivial.
  exists x1; trivial.
  rewrite H1; trivial.
Qed.

Lemma plump_bound : forall ub1 ub2 p1 p2 x,
 x ⊆ ub1 ->
 plump ub1 p1 x -> plump ub2 p2 x.
destruct p1; destruct p2; simpl; intros.
destruct H0 as (?,(?,?)).
split; [|split]; intros; trivial.
 assert (y ∈ ub1).
  apply H; trivial.
 rewrite (plump_morph _ y _ (a _ H4) _ y); auto with *.

 assert (y ∈ ub1).
  apply H; trivial.
 rewrite (plump_morph _ y _ (a _ H6) _ z) in H3; auto with *.
 apply H1 with y H6; auto.
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
exists x1.
rewrite <- (plump_morph x y x0 x1 x y); trivial.
Qed.

Instance isOrd_morph : Proper (eq_set ==> iff) isOrd.
do 2 red; split; intros.
 apply isOrd_ext with x; trivial.

 symmetry in H.
 apply isOrd_ext with y; trivial.
Qed.

Lemma isOrd_inv : forall x y,
  isOrd x -> y < x -> isOrd y.
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
destruct p as (_,(?,_)).
apply H2 with y H1; trivial.
destruct H.
apply plump_bound with (2:=p); reflexivity.
Qed.

Lemma isOrd_dir : forall z, isOrd z -> isDir z.
destruct 1; intros.
revert p.
destruct x;simpl; intros.
destruct p as (_,(_,?)); trivial.
Qed.


Lemma isOrd_intro : forall x,
  (forall a b, isOrd a -> a ⊆ b -> b ∈ x -> a ∈ x) ->
  isDir x ->
  (forall y, y ∈ x -> isOrd y) ->
  isOrd x.
intros.
exists (Acc_intro _ (fun y h => proj1_sig (H1 y h))); simpl.
split; [|split]; intros; trivial.
 destruct (H1 y H2).
 rewrite <- (plump_morph y y x0 _ y y); auto with *.

 apply H with y; trivial.
 exists (plump_Acc _ _ _ H2 H3).
 apply plump_bound with (2:=H2); trivial.
Qed.


Lemma isOrd_trans : forall x y z,
  isOrd x -> z < y -> y < x -> z < x.
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
   (forall z, z < y -> P z) -> P y) ->
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
Qed.
End HigherOrder.

(** * Simple theory of ordinals *)

Lemma lt_antirefl : forall x, isOrd x -> ~ x < x.
induction 1 using isOrd_ind; intros.
red; intros; apply H1 with y; trivial.
Qed.

Lemma isOrd_zero : isOrd zero.
apply isOrd_intro; intros.
 elim empty_ax with b; trivial.

 red; intros.
 elim empty_ax with x; trivial.

 elim empty_ax with y; trivial.
Qed.

(** Successor *)
Definition osucc x := subset (power x) isOrd.

Instance osucc_morph : morph1 osucc.
unfold osucc; do 2 red; intros.
apply subset_morph.
 rewrite H; reflexivity.

 red; auto with *.
Qed.

Lemma lt_osucc : forall x, isOrd x -> x < osucc x.
unfold osucc, lt; intros.
apply subset_intro; trivial.
apply power_intro; auto.
Qed.

#[global]Hint Resolve isOrd_zero lt_osucc : core.

Lemma olts_le : forall x y, x < osucc y -> x ⊆ y.
red; intros.
apply subset_elim1 in H.
apply power_elim with (1:=H); trivial.
Qed.

Lemma ole_lts : forall x y, isOrd x -> x ⊆ y -> x < osucc y.
intros.
apply subset_intro; trivial.
apply power_intro; trivial.
Qed.

Lemma oles_lt : forall x y,
  isOrd x ->
  osucc x ⊆ y ->
  x < y.
intros.
apply H0.
apply lt_osucc; trivial.
Qed.

Lemma ord_le_lt_trans : forall x y z, isOrd z -> x < osucc y -> y < z -> x < z.
intros.
apply isOrd_plump with y; trivial.
 apply subset_elim2 in H0; destruct H0.
 rewrite H0; trivial.

 apply olts_le; trivial.
Qed.

Lemma ord_lt_le : forall o o', isOrd o -> o' ∈ o -> o' ⊆ o.
red; intros; apply isOrd_trans with o'; trivial.
Qed.
#[global]Hint Resolve ord_lt_le : core.

Lemma isOrd_succ : forall n, isOrd n -> isOrd (osucc n).
unfold osucc.
intros.
apply isOrd_intro; intros.
 apply subset_intro; trivial.
 apply subset_elim1 in H2.
 apply power_intro; intros.
 apply H1 in H3.
 apply power_elim with (1:=H2); trivial.

 red; intros.
 exists n.
  apply subset_intro; trivial.
  apply power_intro; auto.

  split.
   red; intros.
   apply power_elim with x; trivial.
   apply subset_elim1 in H0; trivial.

   red; intros.
   apply power_elim with y; trivial.
   apply subset_elim1 in H1; trivial.

 apply subset_elim2 in H0.
 destruct H0.
 rewrite H0; trivial.
Qed.
#[global]Hint Resolve isOrd_succ : core.

Lemma lt_osucc_compat : forall n m, isOrd m -> n < m -> osucc n < osucc m.
intros.
apply ole_lts; auto.
 apply isOrd_succ.
 apply isOrd_inv with m; trivial.

 red; intros.
 apply ord_le_lt_trans with n; trivial.
Qed.

Lemma osucc_mono : forall n m, isOrd n -> isOrd m -> n ⊆ m -> osucc n ⊆ osucc m.
red; intros.
apply ole_lts.
 apply isOrd_inv with (osucc n); auto.

 apply olts_le in H2.
 transitivity n; trivial.
Qed.

  Lemma lt_osucc_inv : forall o o',
    isOrd o ->
    osucc o < osucc o' ->
    o < o'.
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
 apply ord_le_lt_trans with x; trivial.
Qed.

(** Examples: ordinals of rank less than 2 *)
Module Examples.

Definition ord_0 := empty.
Definition ord_1 := osucc ord_0.
Definition ord_2 := osucc ord_1.

(** 1 = {0} *)
Lemma ord1 : forall x, x ∈ ord_1 <-> x == zero.
intros.
unfold ord_1, osucc.
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

 red; intros.
 assert P.
  apply subset_elim2 in H; destruct H; trivial.
 apply subset_elim1 in H.
 apply subset_elim1 in H0.
 apply ord1 in H.
 apply ord1 in H0.
 exists empty.
  apply subset_intro; trivial.
  apply ord1; reflexivity.

  rewrite H; rewrite H0; split; reflexivity.

 apply subset_elim1 in H.
 apply isOrd_inv with (osucc zero); auto.
Qed.

Definition isOrd2 x := exists P:Prop, x == ord_rk_1 P.

(** 2 = {o| 0<=o<=1 } is isomorphic to Prop *)
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

Definition decr_2 (P2:Prop->Prop) :=
   (forall P Q:Prop, (P -> Q) -> (P2 Q -> P2 P)) /\
   (forall P Q:Prop, P2 P -> P2 Q -> P2 (P\/Q)).

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
 apply (proj1 H x x1); trivial.
 rewrite H4 in H1; rewrite H5 in H1; rewrite H3 in H1.
 rewrite <- rk1_order; trivial.

 red; intros.
  unfold ord_rk_2 in H0,H1.
  rewrite subset_ax in H0; destruct H0.
  destruct H2.
  destruct H3 as (P,?,?).
  rewrite <- H2 in H3; clear x0 H2.
  rewrite subset_ax in H1; destruct H1.
  destruct H2.
  destruct H5 as (Q,?,?).
  rewrite <- H2 in H5; clear x0 H2.
  exists (ord_rk_1 (P\/Q)).
   apply subset_intro.
    apply ord2.
    exists (P\/Q); auto with *.

    exists (P\/Q); auto with *.
    apply (proj2 H); trivial.

   split.
    rewrite H3; apply rk1_order; auto.
    rewrite H5; apply rk1_order; auto.

 apply subset_elim1 in H0.
 apply isOrd_inv with (osucc (osucc zero)); auto.
Qed.

(** 3 is isomorphic to decreasing functions of type Prop->Prop
    (and closed by union to ensure directedness) *)
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
  split; intros.
   apply isOrd_plump with (ord_rk_1 Q); trivial.
    assert (ord_rk_1 P ∈ ord_2).
     rewrite ord2.
     exists P; auto with *.
    apply isOrd_inv with ord_2; auto.
    unfold ord_2, ord_1; auto.

    rewrite rk1_order; trivial.

   destruct (isOrd_dir _ H1 _ _ H0 H2).
   destruct H4.
   apply isOrd_plump with x0; trivial.
    apply isOrd_rk_1.

    assert (h := H _ H3).
    apply ord2 in h.
    destruct h as (R,h).
    rewrite h in H4,H5|-*.
    apply rk1_order; destruct 1.
     apply (proj1 (rk1_order P R)); trivial.
     apply (proj1 (rk1_order Q R)); trivial.

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


(** Increasing sequences *)

Definition increasing_bounded o F :=
  forall x x', x < o -> x' < o -> x ⊆ x' -> F x ⊆ F x'.

Lemma increasing_bounded_is_ext F o :
  isOrd o ->
  increasing_bounded o F ->
  ext_fun o F.
intros oo Fincr.
red; red; intros.
apply eq_intro.
*apply Fincr; trivial.
 rewrite <- H0; trivial.
 rewrite H0; reflexivity.
*apply Fincr; trivial.
 rewrite <- H0; trivial.
 rewrite H0; reflexivity.
Qed.
#[global]Hint Resolve increasing_bounded_is_ext : core.

Definition increasing F :=
  forall x y, isOrd x -> isOrd y -> y ⊆ x -> F y ⊆ F x.

(*Lemma increasing_is_ext : forall F,
  increasing F ->
  forall o, isOrd o ->
  ext_fun o F.
Hint Resolve increasing_is_ext : core. *)

Lemma increasing_bounded_weaker F :
  increasing F -> forall o, isOrd o -> increasing_bounded o F.
red; intros.
apply H; eauto using isOrd_inv.
Qed.
#[global]Hint Resolve increasing_bounded_weaker : core.

(** Successor ordinals *)

Definition succOrd o := exists2 o', isOrd o' & o == osucc o'.

(** Limit ordinals *)

Definition limitOrd o := isOrd o /\ (forall x, x < o -> lt (osucc x) o).

#[global]Instance limitOrd_morph : Proper (eq_set ==> iff) limitOrd.
do 2 red; intros.
apply and_iff_morphism; [rewrite H; reflexivity|].
apply fa_morph; intros x'.
rewrite H; reflexivity.
Qed.

Lemma limit_is_ord : forall o, limitOrd o -> isOrd o.
destruct 1; trivial.
Qed.
Hint Resolve limit_is_ord : core.

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
apply ord_le_lt_trans with x; trivial.
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

Lemma isOrd_inter2 : forall x y,
  isOrd x -> isOrd y -> isOrd (x ∩ y).
intros.
revert y H0; apply isOrd_ind with (2:=H); intros.
clear x H H1; rename y into x; rename y0 into y.
apply isOrd_intro; intros.
 rewrite inter2_def in H4|-*; destruct H4; split.
  apply isOrd_plump with b; trivial.
  apply isOrd_plump with b; trivial.

 red; intros.
 rewrite inter2_def in H; destruct H.
 rewrite inter2_def in H1; destruct H1.
 destruct (isOrd_dir _ H0 _ _ H H1).
 destruct H7.
 destruct (isOrd_dir _ H3 _ _ H4 H5).
 destruct H10.
 exists (x1 ∩ x2).
  rewrite inter2_def; split.
   apply isOrd_plump with x1; trivial.
    apply H2; trivial.
    apply isOrd_inv with y; trivial.

    apply inter2_incl1.

   apply isOrd_plump with x2; trivial.
    apply H2; trivial.
    apply isOrd_inv with y; trivial.

    apply inter2_incl2.

  split; red; intros; rewrite inter2_def; split; auto.

 rewrite inter2_def in H; destruct H.
 apply isOrd_inv with x; trivial.
Qed.
#[global]Hint Resolve isOrd_inter2 : core.

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

(** * Transfinite recursion *)

Section TransfiniteRecursion.

  Variable F : (set -> set) -> set -> set.
  Hypothesis Fm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) F.

  Definition TR := WFR (fun x => x) F.

#[global]Instance TR_morph0 : morph1 TR.
clear Fm; do 2 red; intros.
unfold TR.
apply WFR_morph0; auto with *.
Qed.

  Lemma WFRle_ord_incl o o' :
    ZFrepl.WFRle (fun x=>x) o' o ->
    isOrd o ->
    isOrd o' /\ o' ⊆ o.
induction 1; intros.
*destruct H; [rewrite H; auto with *|].
 split; [eauto using isOrd_inv|].
 red; intros; apply isOrd_trans with x; trivial.
*destruct IHclos_trans2; trivial.
 destruct IHclos_trans1; trivial.
 split; [trivial|transitivity y; trivial].
Qed.
 
  Lemma TR_eqn o :
    isOrd o ->
    (forall x x' f f', isOrd x -> x ⊆ o -> x==x' -> eq_fun x f f' -> F f x == F f' x') ->
    TR o == F TR o.
intros oo Fext.
unfold TR.
apply WFR_eqn; auto with *.
*intros.
 apply WFRle_ord_incl in H; trivial.
 destruct H.
 apply Fext; auto.
*elim oo using isOrd_ind; intros; constructor; intros; auto.
Qed. 

  Lemma TR_ind : forall o (P:set->set->Prop),
    Proper (eq_set ==> eq_set ==> iff) P ->
    isOrd o ->
    (forall x x' f f', isOrd x -> x ⊆ o -> x==x' -> eq_fun x f f' -> F f x == F f' x') ->
    (forall y, isOrd y -> y ⊆ o ->
     (forall x, x < y -> P x (TR x)) ->
     P y (F TR y)) ->
    P o (TR o).
intros o P Pm oo Fmorph.
revert Fmorph; induction oo using isOrd_ind; intros.
rewrite TR_eqn; trivial.
apply H1; auto with *; intros.
apply H0; intros; trivial.
  assert (x0 ⊆ y).
   transitivity x; auto.
 auto.
apply H1; trivial.
transitivity x; auto.
Qed.

  Lemma TR_typ : forall o X,
    isOrd o ->
    (forall x x' f f', isOrd x -> x ⊆ o -> x==x' -> eq_fun x f f' -> F f x == F f' x') ->
    morph1 X ->
    (forall y f, morph1 f -> isOrd y -> y ⊆ o ->
     (forall z, z < y -> f z ∈ X z) -> F f y ∈ X y) ->
    TR o ∈ X o.
intros o X oo Fmorph Xm Hrec.
apply TR_ind with (o:=o); intros; trivial.
 do 3 red; intros.
 rewrite H; rewrite H0; reflexivity.

 apply Fmorph; trivial.

 apply Hrec; trivial; intros.
 apply TR_morph0.
Qed.

  
End TransfiniteRecursion.


#[global]Instance TR_morph :
    Proper (((eq_set ==> eq_set) ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) TR.
do 3 red; intros.
apply WFR_morph; trivial.
red; trivial.
Qed.

(** Specialized version where the case of limit ordinals is union *)
Section TransfiniteIteration.

  Variable F : set -> set.
  Hypothesis Fmorph : Proper (eq_set ==> eq_set) F.

Let G f o := sup o (fun o' => F (f o')).

Let Gm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) G.
do 3 red; intros.
unfold G.
apply sup_morph; trivial.
red; intros.
apply Fmorph.
apply H; trivial.
Qed.

Let Gmorph : forall o o' f f', o==o' -> eq_fun o f f' -> G f o == G f' o'.
unfold G; intros.
apply sup_morph; auto with *.
red; auto.
Qed.

  Definition TI := TR G.

  Instance TI_morph : morph1 TI.
unfold TI; do 2 red; intros.
apply TR_morph0; auto with *.
Qed.

  Lemma TI_fun_ext : forall x, ext_fun x (fun y => F (TI y)).
do 2 red; intros.
apply Fmorph.
apply TI_morph; trivial.
Qed.
Hint Resolve TI_fun_ext : core.

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
    exists2 o', o' < o & x ∈ F (TI o').
intros.
rewrite TI_eq in H0; trivial.
rewrite sup_ax in H0; auto.
Qed.

  Lemma TI_mono : increasing TI.
do 2 red; intros.
apply TI_elim in H2; intros; auto with *.
destruct H2.
apply TI_intro with x0; auto with *.
Qed.

  Lemma TI_incl : forall o, isOrd o ->
    forall o', o' < o ->
    TI o' ⊆ TI o.
intros.
apply TI_mono; trivial; auto.
apply isOrd_inv with o; trivial.
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
     (forall x, x < m -> G x ∈ X) -> sup m G ∈ X) ->
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
#[global]Hint Resolve TI_fun_ext : core.

#[global]Instance TI_morph_gen :
  Proper ((eq_set==>eq_set)==>eq_set==>eq_set) TI.
do 3 red; intros.
unfold TI.
apply TR_morph; trivial.
do 2 red; intros.
apply sup_morph; trivial.
red; intros.
apply H; apply H1; trivial.
Qed.

(** * Supremum of directed ordinals *)

(** ** Binary supremum *)
Require Import ZFpairs.

Section BinarySup.

  (* epsilon-recursion on the first component *and* second component *)
  Let Rsub xy := prodcart (fst xy) (snd xy).
  Let R x y := x ∈ Rsub y.

  Let Rdef x y : R x y <-> isCouple x /\ fst x ∈ fst y /\ snd x ∈ snd y.
split; intros.
*split.
 apply surj_pair in H; trivial.
 split;[apply fst_typ in H|apply snd_typ in H]; trivial.    
*destruct H as (isc&?&?).
 red in isc|-*; rewrite isc.
 apply couple_intro; trivial.
Qed.
 
  Local Instance Rsubm : morph1 Rsub.
do 2 red; intros.
unfold Rsub; rewrite H; reflexivity.
Qed.

  Local Instance Rm : Proper (eq_set==>eq_set==>iff) R.
unfold R; do 3 red; intros.
rewrite H,H0.
reflexivity.
Qed.

Hint Resolve Rsubm : core.

  Let F f xy :=
    let x := fst xy in
    let y := snd xy in
    x ∪ y ∪ sup x (fun x' => replf y (fun y' => f (couple x' y'))).
  Let Fm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) F.       
unfold F; do 3 red; intros.
apply union2_morph.
 rewrite H0; reflexivity.
apply sup_morph;[rewrite H0;reflexivity|].
red; intros.
apply replf_morph;[rewrite H0;reflexivity|].
red; intros.
apply H; rewrite H2,H4; reflexivity.
Qed.

  Definition osup2 x y := WFR Rsub F (couple x y).

Infix "⊔" := osup2 (at level 50). (* input method: \sqcup *)
(* ⋓ = \Cup would be nicer, but poor html rendering... *)

Instance osup2_morph : morph2 osup2.
unfold osup2; do 3 red; intros.
apply WFR_morph; auto with *.
 apply Rsubm.
 apply couple_morph; trivial.
Qed.

  Lemma osup2_def : forall x y, isOrd x ->
    x ⊔ y == x ∪ y ∪ sup x (fun x' => replf y (fun y' => x' ⊔ y')).
intros.
unfold osup2 at 1.
rewrite WFR_eqn; auto.
*unfold F.
 apply union2_morph.
  rewrite fst_def,snd_def; reflexivity.
 apply sup_morph.
  apply fst_def.
 red; intros.
 apply replf_morph.
  apply snd_def.
 red; intros.
 apply osup2_morph; trivial.

*intros.
 apply union2_morph; [rewrite H2; reflexivity|].
 apply sup_morph; [rewrite H2; reflexivity|].
 red; intros.
 apply replf_morph; [rewrite H2; reflexivity|].
 red; intros.
 apply H1; [apply couple_intro; trivial|].
 rewrite H4,H6; reflexivity.

*revert y; elim H using isOrd_ind; intros.
 constructor; intros.
 apply Rdef in H3; destruct H3 as (?&?&_).
 rewrite fst_def in H4.
 eapply wf_morph with  (3:=Rm)(4:=H3) ; auto with *.
Qed.

Lemma osup2_ax : forall x y z,
  isOrd x ->
  (z ∈ x ⊔ y <->
   z ∈ x \/ z ∈ y \/
   exists2 x', x' ∈ x & exists2 y', y' ∈ y & z == x' ⊔ y').
intros x y z wfx.
rewrite osup2_def; trivial.
split; intros.
 apply union2_elim in H; destruct H.
  apply union2_elim in H; destruct H; auto.

  rewrite sup_ax in H.
   destruct H.
   rewrite replf_ax in H0.
    destruct H0; eauto.

    red; red; intros.
    apply osup2_morph; auto with *.

   red; red; intros.
   apply replf_morph; auto with *.
   red; intros.
   apply osup2_morph; trivial.

 destruct H as [?|[?|?]].
  apply union2_intro1; apply union2_intro1; trivial.

  apply union2_intro1; apply union2_intro2; trivial.

  apply union2_intro2.
  destruct H.
  destruct H0.
  rewrite sup_ax.
   exists x0; trivial.
   rewrite replf_ax.
    exists x1; trivial.

    red; red; intros.
    apply osup2_morph; auto with *.

   red; red; intros.
   apply replf_morph; auto with *.
   red; intros.
   apply osup2_morph; trivial.
Qed.

Lemma osup2_incl1 : forall x y, isOrd x -> x ⊆ x ⊔ y.
red; intros.
rewrite osup2_ax; auto.
Qed.

Lemma osup2_incl2 : forall x y, isOrd x -> y ⊆ x ⊔ y.
red; intros.
rewrite osup2_ax; auto.
Qed.

Lemma osup2_mono x x' y y' :
  isOrd x' ->
  isOrd x ->
  x ⊆ x' -> y ⊆ y' ->
  x ⊔ y ⊆ x' ⊔ y'.
red; intros.
rewrite osup2_ax in H3|-*; trivial.
destruct H3 as [?|[?|(a,?,(b,?,?))]]; auto.
right; right.
exists a; auto.
exists b; auto with *.
Qed.

Lemma isDir_osup2 : forall x y, isOrd x -> isDir x -> isDir y -> isDir (x ⊔ y).
red; unfold lt; intros x y wfx H H0; intros.
assert (wfi := isOrd_inv).
rewrite osup2_ax in H1,H2; trivial.
destruct H1 as [?|[?|(x1,?,(x2,?,?))]];
  destruct H2 as [?|[?|(y1,?,(y2,?,?))]].
 (* case 1. *)
 destruct (H x0 y0); trivial.
 exists x1; trivial.
 apply osup2_incl1; trivial.
 (* case 2. *)
 exists (x0 ⊔ y0).
  rewrite osup2_ax; trivial; right; right; eauto with *.

  split.
   apply osup2_incl1; eauto.
   apply osup2_incl2; eauto.
 (* case 3. *)
 destruct (H x0 y1); trivial.
 destruct H6.
 exists (x1 ⊔ y2).
  rewrite osup2_ax; trivial; right; right; eauto with *.

  split.
   transitivity x1; trivial.
   apply osup2_incl1; eauto.

   rewrite H4; apply osup2_mono; eauto with *.
 (* case 4. *)
 exists (y0 ⊔ x0).
  rewrite osup2_ax; trivial; right; right; eauto with *.

  split.
   apply osup2_incl2; eauto.
   apply osup2_incl1; eauto.
 (* case 5. *)
 destruct (H0 x0 y0); trivial.
 exists x1; trivial.
 apply osup2_incl2; trivial.
 (* case 6. *)
 destruct (H0 x0 y2); trivial.
 destruct H6.
 exists (y1 ⊔ x1).
  rewrite osup2_ax; trivial; right; right; eauto with *.

  split.
   transitivity x1; trivial.
   apply osup2_incl2; eauto.

   rewrite H4; apply osup2_mono; eauto with *.
 (* case 7. *)
 destruct (H x1 y0); trivial.
 destruct H6.
 exists (x3 ⊔ x2).
  rewrite osup2_ax; trivial; right; right; eauto with *.

  split.
   rewrite H4; apply osup2_mono; eauto with *.

   transitivity x3; trivial; apply osup2_incl1; eauto.
 (* case 8. *)
 destruct (H0 x2 y0); trivial.
 destruct H6.
 exists (x1 ⊔ x3).
  rewrite osup2_ax; trivial; right; right; eauto with *.

  split.
   rewrite H4; apply osup2_mono; eauto with *.

   transitivity x3; trivial; apply osup2_incl2; eauto.
 (* case 9. *)
 destruct (H x1 y1); trivial.
 destruct H8.
 destruct (H0 x2 y2); trivial.
 destruct H11.
 exists (x3 ⊔ x4).
  rewrite osup2_ax; trivial; right; right; eauto with *.

  split.
   rewrite H4; apply osup2_mono; eauto with *.

   rewrite H6; apply osup2_mono; eauto with *.
Qed.

Lemma osup2_proof : forall x, isOrd x -> forall y, isOrd y ->
  isOrd (x ⊔ y) /\
  (forall z, isOrd z -> z ∩ (x ⊔ y) == z ∩ x ⊔ z ∩ y).
induction 1 using isOrd_ind.
clear H0 x; rename y into x; rename H1 into Hrecx.
intros y yo.
rename H into xo.
split.
 (* isOrd *)
 apply isOrd_intro; intros.
  (* plump *)
  rewrite osup2_ax in H1|-*; auto.
  destruct H1 as [?|[?|(x',?,(y',?,?))]].
   left; apply isOrd_plump with b; trivial.

   right; left; apply isOrd_plump with b; trivial.

   right; right.
   exists (a ∩ x').
    apply isOrd_plump with x'; trivial.
     apply isOrd_inter2; eauto using isOrd_inv.
     apply inter2_incl2.

    exists (a ∩ y').
     apply isOrd_plump with y'; trivial.
      apply isOrd_inter2; eauto using isOrd_inv.
      apply inter2_incl2.

     destruct Hrecx with x' y' as (_,?); eauto using isOrd_inv.
     rewrite <- H4; trivial.
     apply eq_intro; intros.
      rewrite inter2_def; split; trivial.
      rewrite <- H3; auto.

      apply inter2_def in H5; destruct H5; trivial.

  (* dir *)
  apply isDir_osup2; auto.

  apply isOrd_dir; trivial.
   apply isOrd_dir; trivial.

  (* trans *)
  apply osup2_ax in H; auto.
  destruct H as [?|[?|(x',?,(y',?,?))]]; eauto using isOrd_inv.
  rewrite H1; apply Hrecx; eauto using isOrd_inv.

 (* inter distrib *)
 intros.
 assert (wfizx : isOrd (z ∩ x)).
  apply isOrd_inter2; auto.
 assert (wfizy : isOrd (z ∩ y)).
  apply isOrd_inter2; auto.
 assert (Hrec: forall x' y' z, x' ∈ x -> y' ∈ y -> isOrd z ->
                 z ∩ (x' ⊔ y') == z ∩ x' ⊔ z ∩ y').
  intros; apply Hrecx; eauto using isOrd_inv.
 apply eq_intro; intros.
  rewrite inter2_def in H0; trivial; destruct H0.
  rewrite osup2_ax in H1; auto.
  destruct H1 as [?|[?|(x',?,(y',?,?))]].
   apply osup2_incl1; trivial.
   rewrite inter2_def; auto.

   apply osup2_incl2; trivial.
   rewrite inter2_def; auto.

   rewrite osup2_ax; trivial; right; right.
   exists (z0 ∩ x').
    rewrite inter2_def; split.
     apply isOrd_plump with z0; auto.
      apply isOrd_inter2; eauto using isOrd_inv.
      apply inter2_incl1.
     apply isOrd_plump with x'; auto.
      apply isOrd_inter2; eauto using isOrd_inv.
      apply inter2_incl2.
   exists (z0 ∩ y').
    rewrite inter2_def; split.
     apply isOrd_plump with z0; auto.
      apply isOrd_inter2; eauto using isOrd_inv.
      apply inter2_incl1.
     apply isOrd_plump with y'; auto.
      apply isOrd_inter2; eauto using isOrd_inv.
      apply inter2_incl2.
   rewrite <- Hrec; eauto using isOrd_inv.
   rewrite incl_inter2; auto with *. 
   rewrite H3; reflexivity.

  rewrite osup2_ax in H0; trivial.
  destruct H0 as [?|[?|(x',?,(y',?,?))]].
   rewrite inter2_def in H0; destruct H0; rewrite inter2_def; split; trivial.
   apply osup2_incl1; auto.

   rewrite inter2_def in H0; destruct H0; rewrite inter2_def; split; trivial.
   apply osup2_incl2; auto.

   rewrite inter2_def in H0; destruct H0.
   rewrite inter2_def in H1; destruct H1.
   rewrite H2; clear z0 H2.
   destruct (isOrd_dir _ H x' y'); trivial.
   destruct H5.
   rewrite inter2_def; split.
    apply isOrd_plump with x0; trivial.
     apply Hrecx; eauto using isOrd_inv.
     rewrite <- (incl_inter2 _ _) with (1:=H5). (*!*)
     rewrite <- (incl_inter2 _ _) with (1:=H6). (*!*)
     rewrite (inter2_comm x' x0); rewrite (inter2_comm y' x0).
     rewrite <- Hrec; eauto using isOrd_inv.
     apply inter2_incl1.

    rewrite (osup2_ax x y); auto; right; right; eauto with *.
Qed.

Lemma isOrd_osup2 : forall x y,
  isOrd x ->
  isOrd y ->
  isOrd (x ⊔ y).
intros.
apply osup2_proof; trivial.
Qed.

Lemma osup2_lub : forall x y z,
  isOrd x -> isOrd y -> isOrd z ->
  x ⊆ z -> y ⊆ z -> x ⊔ y ⊆ z.
intros.
rewrite <- (incl_inter2 _ _) with (1:=H2). (*!*)
rewrite <- (incl_inter2 _ _) with (1:=H3). (*!*)
rewrite (inter2_comm x z); rewrite (inter2_comm y z).
destruct osup2_proof with (1:=H)(2:=H0) as (_,dint); rewrite <- dint; trivial.
apply inter2_incl1.
Qed.

Lemma osup2_refl x : isOrd x -> x ⊔ x == x.
intros.
apply eq_intro; intros.
 revert H0; apply osup2_lub; auto with *.

 apply osup2_incl1; auto.
Qed.

Lemma osup2_lt x y z : isOrd z -> x ∈ z -> y ∈ z -> x ⊔ y ∈ z.
intros.
destruct (isOrd_dir _ H x y); trivial.
destruct H3.
apply isOrd_plump with x0; trivial.
 apply isOrd_osup2; eauto using isOrd_inv.

 apply osup2_lub; eauto using isOrd_inv.
Qed.

Lemma isDir_succ : forall o,
  isOrd o -> isDir (osucc o).
red; intros.
assert (xo : isWf x) by (apply isOrd_inv with (osucc o); auto).
exists (x ⊔ y).
 apply osup2_lt; auto.

 split.
  apply osup2_incl1; eauto using isOrd_inv.
  apply osup2_incl2; eauto using isOrd_inv.
Qed.


Lemma osup2_sym : forall x y, isOrd x -> isOrd y -> x ⊔ y == y ⊔ x.
intros x y wfx wfy.
revert y wfy ; apply isOrd_ind with (2:=wfx); intros.
apply eq_intro; intros.
 rewrite osup2_ax in H2|-*; trivial.
 destruct H2 as [?|[?|(x',?,(y',?,?))]];[right;left|left|right;right]; trivial.
 exists y'; trivial.
 exists x'; trivial.
 rewrite H4; apply H1; eauto using isOrd_inv.

 rewrite osup2_ax in H2|-*; trivial.
 destruct H2 as [?|[?|(x',?,(y',?,?))]];[right;left|left|right;right]; trivial.
 exists y'; trivial.
 exists x'; trivial.
 rewrite H4; symmetry; apply H1; eauto using isOrd_inv.
Qed.

Lemma osup2_assoc : forall x y z, isOrd x -> isOrd y -> isOrd z ->
  x ⊔ (y ⊔ z) == x ⊔ y ⊔ z.
intros x y z wfx; revert y z; apply isOrd_ind with (2:=wfx); intros.
apply eq_intro; intros.
 rewrite osup2_ax in H4|-*; auto.
 2:apply isOrd_osup2; trivial.
 rewrite osup2_ax; auto.
 destruct H4 as [?|[?|(x',?,(w',?,?))]]; auto.
  rewrite osup2_ax in H4; auto.
  destruct H4 as [?|[?|(y',?,(z',?,?))]]; auto.
  right; right.
  exists y';[|exists z']; trivial.
  apply osup2_incl2; auto.

  rewrite osup2_ax in H5; auto.
  destruct H5 as [?|[?|(y'',?,(z',?,?))]]; auto.
   left; right; right; exists x'; [trivial|exists w';trivial].

   right; right; exists x'; [|exists w';trivial].
   apply osup2_incl1; auto.

   right; right; exists (x' ⊔ y'');[|exists z']; trivial.
    rewrite osup2_ax; [right; right; exists x'; [trivial|exists y'']; auto with *|auto].

    rewrite <- H1; eauto using isOrd_inv.
    rewrite <- H8; trivial.

 rewrite osup2_ax in H4|-*; auto.
 2:apply isOrd_osup2; trivial.
 rewrite osup2_ax; auto.
 destruct H4 as [?|[?|(w',?,(z',?,?))]]; auto.
  rewrite osup2_ax in H4; auto.
  destruct H4 as [?|[?|(y',?,(z',?,?))]]; auto.
  right; right.
  exists y';[|exists z']; trivial.
  apply osup2_incl1; auto.

  rewrite osup2_ax in H4; auto.
  destruct H4 as [?|[?|(x',?,(y',?,?))]]; auto.
   right; right; exists w'; [trivial|exists z';trivial].
   apply osup2_incl2; auto.

   right; left; right; right; exists w'; [trivial|exists z';trivial].

   right; right; exists x';[|exists (y' ⊔ z')]; trivial.
    rewrite osup2_ax; [right; right; exists y'; [trivial|exists z']; auto with *|auto].

    rewrite H1; eauto using isOrd_inv.
    rewrite <- H8; trivial.
Qed.

End BinarySup.
Infix "⊔" := osup2 (at level 50). (* input method: \sqcup *)

(** ** Indexed supremum of monotonic family *)

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

  Lemma isOrd_supf_elim : forall x, x < sup I f -> exists2 n, n ∈ I & x < f n.
intros.
rewrite sup_ax in H; trivial.
Qed.

  (* Directed union: *)
  Hypothesis supf_dir : forall x y, x ∈ I -> y ∈ I ->
    exists2 z, z ∈ I & f x ⊆ f z /\ f y ⊆ f z.

  Lemma isDir_ord_sup : isDir (sup I f).
red; intros.
rewrite sup_ax in H; trivial; destruct H.
rewrite sup_ax in H0; trivial; destruct H0.
assert (xo : isOrd x).
 apply isOrd_inv with (f x0); auto.
destruct supf_dir with x0 x1; trivial.
destruct H4.
exists (x ⊔ y).
 rewrite sup_ax; trivial.
 exists x2; trivial.
 apply osup2_lt; auto.

 split.
  apply osup2_incl1; trivial.
  apply osup2_incl2; trivial.
Qed.

  Lemma isOrd_supf : isOrd (sup I f).
apply isOrd_intro; intros.
 elim isOrd_supf_elim with (1:=H1); intros.
 apply isOrd_supf_intro with x; trivial.
 apply isOrd_plump with b; auto.

 apply isDir_ord_sup.

 elim isOrd_supf_elim with (1:=H); intros.
 apply isOrd_inv with (f x); auto.
Qed.

End OrdinalUpperBound.


(********************************************************************)

Section LimOrd.

  Variable f : set -> set.
  Hypothesis fm : ext_fun N f.
  Hypothesis ford : forall n, n ∈ N -> isOrd (f n).
  Hypothesis fmono : forall m n, m ∈ N -> n ∈ N -> le m n -> f m ⊆ f n.

  Definition ord_sup := sup N f.

  Lemma isOrd_sup_intro : forall n, n ∈ N -> f n ⊆ ord_sup.
unfold ord_sup.
red; intros.
rewrite sup_ax; trivial.
exists n; trivial.
Qed.

  Lemma isOrd_sup_elim : forall x, x < ord_sup -> exists2 n, n ∈ N & x < f n.
unfold ord_sup; intros.
rewrite sup_ax in H; trivial.
Qed.

  Lemma isOrd_sup : isOrd ord_sup.
apply isOrd_intro; intros.
*elim isOrd_sup_elim with (1:=H1); intros.
 apply isOrd_sup_intro with x; trivial.
 apply isOrd_plump with b; auto.

*red; intros.
 apply isOrd_sup_elim in H; destruct H.
 apply isOrd_sup_elim in H0; destruct H0.
 assert (xo : isOrd x).
 {apply isOrd_inv with (f x0); auto. }
 exists (x ⊔ y).
 +destruct (isOrd_dir _ (ford (max x0 x1) (max_typ _ _ H H0)) x y).
   apply (fmono x0); auto with arith.
   apply (fmono x1); auto with *.

   destruct H4.
   apply (isOrd_sup_intro (max x0 x1));[auto|].
   apply isOrd_plump with x2; auto.
    apply isOrd_osup2; eauto using isOrd_inv.

    apply osup2_lub; eauto using isOrd_inv.

 +split.
   apply osup2_incl1; trivial.
   apply osup2_incl2; trivial.

*elim isOrd_sup_elim with (1:=H); intros.
 apply isOrd_inv with (f x); auto.
Qed.


  Lemma ord_sup_typ X :
    (forall n, n ∈ N -> f n ∈ X) ->
    (forall g, ext_fun N g -> (forall n, n ∈ N -> g n ∈ X) -> sup N g ∈ X) ->
    ord_sup ∈ X.
unfold ord_sup.
intros.
apply H0; trivial; intros.
Qed.

End LimOrd.

Lemma isOrd_union : forall x,
  (forall y, y ∈ x -> isOrd y) ->
  (forall a a', a ∈ x -> a' ∈ x -> exists2 b, b ∈ x & a ⊆ b /\ a' ⊆ b) ->
 isOrd (union x).
intros.
rewrite union_is_sup.
apply isOrd_supf; auto.
do 2 red; trivial.
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

 red; intros.
 destruct inter_non_empty with (1:=H0) as (w,?,?).
 assert (x0o : isOrd x0).
  apply isOrd_inv with w; auto.
 exists (x0 ⊔ y).
  apply inter_intro; intros; eauto.
  apply osup2_lt; auto.
   apply inter_elim with (1:=H0); trivial.
   apply inter_elim with (1:=H1); trivial.

  split.
   apply osup2_incl1; trivial.
   apply osup2_incl2; trivial.

 destruct inter_non_empty with (1:=H0).
 eauto using isOrd_inv.
Qed.

(* ω-iteration : f^w(o) *)

Definition w_iter f z := sup N (natrec z (fun _ o => f o)).

Instance w_iter_morph_gen : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) w_iter.
do 3 red; intros.
apply sup_morph; [reflexivity|].
red; intros.
apply natrec_morph; auto with *.
do 2 red; intros; auto.
Qed.


Section W_Iteration.

  Variable f : set -> set.
  Hypothesis fm : morph1 f.
  Variable z : set.
  
  #[global]Instance w_iter_morph : morph1 (w_iter f).
  apply w_iter_morph_gen; trivial.
  Qed.
  
Lemma w_iter_aux_m :
  morph1 (natrec z (fun _ o => f o)).
do 2 red; intros.
apply natrec_morph; auto with *.
do 2 red; intros; auto.
Qed.

Lemma w_iter_aux_ext :
  ext_fun N (natrec z (fun _ o => f o)).
do 2 red; intros; apply w_iter_aux_m; trivial.
Qed.

Hint Resolve w_iter_aux_m w_iter_aux_ext : core.

  Section W_Ord_Iteration.

    Hypothesis zo : isOrd z.
    Hypothesis fo : forall o, isOrd o -> isOrd (f o).
    
    Lemma w_iter_aux_ord n :
      n ∈ N -> isOrd (natrec z (fun _ o => f o) n).
intros H.
elim H using N_ind; intros.
+revert H2; apply isOrd_morph.
 apply w_iter_aux_m; auto with *.
+rewrite natrec_0; auto.
+rewrite natrec_S; auto.
 intros ????? h; rewrite h; reflexivity.
Qed.

    Hint Resolve zero_typ succ_typ : core.
    Hint Resolve w_iter_aux_ord : core.

    Section Mono.

      Hypothesis fext : forall o, isOrd o -> o ⊆ f o.

      Lemma isOrd_mono_w_iter : isOrd (w_iter f z).
apply isOrd_sup; auto.
intros.
elim H1 using Nle_ind; trivial.
+do 2 red; intros.
 apply incl_set_morph; apply w_iter_aux_m; auto with *.
+reflexivity.
+clear n H0 H1; intros.
 rewrite natrec_S; trivial.
 2:intros ????? h; rewrite h; reflexivity.
 rewrite H1.
 red; intros.
 apply fext; auto.
Qed.

      Lemma w_iter_limitOrd :
        (forall o z, isOrd o -> z ∈ f o -> osucc z ∈ f o) ->
        limitOrd (w_iter f z).
split; [apply isOrd_mono_w_iter|unfold w_iter;intros].
rewrite sup_ax in H0|-*; trivial.
destruct H0 as (n,?,?).
exists (succ n); [auto|].
rewrite natrec_S;[|intros ????? h; rewrite h; reflexivity|auto].
apply H;[auto|].
apply fext; auto.
Qed.

    End Mono.

    Section StrictMono.
      
      Hypothesis f_z : z < f z.
      Hypothesis f_incr : forall o o', isOrd o -> o' < o -> f o' < f o.

(*    Hypothesis f_incr : forall o, isOrd o -> o < f o.*)

    Let f_ext : forall o, isOrd o -> o ⊆ f o.
induction 1 using isOrd_ind.
red; intros.
assert (isOrd z0) by eauto using isOrd_inv.
apply isOrd_plump with (f z0); auto.
apply f_incr; trivial.
Qed.
    
    Lemma w_iter_intro1 : z ∈ w_iter f z.
intros; apply sup_ax; trivial.
exists (succ zero); [auto|].
rewrite natrec_S;[|intros ????? h; rewrite h; reflexivity|auto].
rewrite natrec_0; trivial.
Qed.

    Lemma w_iter_intro2 o : o ∈ w_iter f z -> f o ∈ w_iter f z.
unfold w_iter; intros.
rewrite sup_ax in H|-*; auto.
destruct H as (n,?,?).
exists (succ n);[apply succ_typ; trivial|].
rewrite natrec_S; trivial.
2:intros ????? h; rewrite h; reflexivity.
apply f_incr; auto.
Qed.

    Lemma limitOrd_w_iter : limitOrd (w_iter f z).
assert (isOrd (w_iter f z)) by (apply isOrd_mono_w_iter;trivial).
split; [trivial|intros].
assert (isOrd x) by eauto using isOrd_inv.
unfold w_iter in H0|-*; rewrite sup_ax in H0|-*; auto.
destruct H0 as (n,?,?).
exists (succ n);[auto|].
rewrite natrec_S; auto.
2:intros ????? h; rewrite h; reflexivity.
apply lt_osucc_compat in H2;[|auto].
apply isOrd_plump with (natrec z (fun _ o => f o) n); auto.
 apply olts_le; trivial.
clear H2 H1.
elim H0 using N_ind; intros.
*assert (Proper (eq_set==>iff) (fun z => z ∈ f z)).
 {intros ?? h; rewrite h; reflexivity. }
 revert H3; apply H4.
 apply natrec_morph; auto with *.
 intros ??????; auto.
*rewrite natrec_0; trivial.
*rewrite natrec_S; auto.
 2:intros ??????; auto.
 apply f_incr; auto.
Qed.

    End StrictMono.
  End W_Ord_Iteration.
End W_Iteration.    

(** Building limit ordinals *)

Definition next_limOrd := w_iter osucc.

Instance next_limOrd_morph : morph1 next_limOrd.
apply w_iter_morph; auto with *.
Qed.

Lemma limOrd_next_limOrd z : isOrd z -> limitOrd (next_limOrd z).
intros; apply limitOrd_w_iter; auto with *.
intros; apply lt_osucc_compat; trivial.
Qed.

Lemma next_limOrd_intro1 z : isOrd z -> z ∈ next_limOrd z.
intros; apply w_iter_intro1; auto with *.
Qed.

Lemma next_limOrd_intro2 z o : isOrd z -> o ∈ next_limOrd z -> osucc o ∈ next_limOrd z.
intros; apply w_iter_intro2; auto with *.
intros; apply lt_osucc_compat; trivial.
Qed.

Lemma next_limOrd_lub z o :
  isOrd z ->
  limitOrd o ->
  z ∈ o ->
  next_limOrd z ⊆ o.
intros oz loo zty w wty.
apply sup_ax in wty; auto.
destruct wty as (n,?,?).
assert (natrec z (fun _ o => osucc o) n ∈ o).
{elim H using N_ind; intros.
 *revert H3; apply in_reg; apply natrec_morph; auto with *.
  do 2 red; intros.
  rewrite H4; reflexivity.
 *rewrite natrec_0; trivial.
 *rewrite natrec_S; auto.
  2:intros ????? h; rewrite h; reflexivity.
  apply loo; trivial. }
apply isOrd_trans with (2:=H0); auto.
apply w_iter_aux_ext; auto with *.
Qed.

Lemma next_limOrd_mono o o' :
  isOrd o -> isOrd o' -> o ⊆ o' -> next_limOrd o ⊆ next_limOrd o'.
intros.
apply next_limOrd_lub; [trivial|apply limOrd_next_limOrd; trivial|].
apply isOrd_plump with o'; trivial;[apply limOrd_next_limOrd; trivial|].
apply next_limOrd_intro1; trivial.
Qed.

(** Ordinal omega *)

Definition omega := next_limOrd zero.

Lemma isOrd_omega : isOrd omega.
apply limOrd_next_limOrd; trivial.
Qed.

Lemma omega_limit_ord : limitOrd omega.
apply limOrd_next_limOrd; trivial.
Qed.

Lemma zero_omega : zero ∈ omega.
apply next_limOrd_intro1; trivial.
Qed.

Lemma osucc_omega n : n ∈ omega -> osucc n ∈ omega.
apply next_limOrd_intro2; trivial.
Qed.

#[global]Hint Resolve isOrd_omega zero_omega osucc_omega omega_limit_ord : core.

(** ** Indexed supremum of arbitrary family *)

Section DirOrdinalSup.

  Variable I : set.
  Variable f : set -> set.
  Hypothesis f_ext : ext_fun I f.
  Hypothesis f_ord : forall x, x ∈ I -> isOrd (f x).

  (** Taking the supremum pairwise *)
  Definition osupf X := sup X (fun x => replf X (fun y => x ⊔ y)).
  Definition osupfn n := natrec (sup I f) (fun _ => osupf) n.
  (** Iterating ω times, we get a fixpoint *)
  Definition osup := ord_sup osupfn.


  Lemma osupf_def X z : z ∈ osupf X <-> exists2 x, x ∈ X & exists2 y, y ∈ X & z == x ⊔ y.
unfold osupf; rewrite sup_ax.
 apply ex2_morph.
  red; reflexivity.

  red; intros.
  rewrite replf_ax.
   reflexivity.

   do 2 red; intros; apply osup2_morph; auto with *.

 do 2 red; intros; apply replf_morph; auto with *.
 red; intros; apply osup2_morph; trivial.
Qed.
  
  Lemma osupf_mono X Y :
    X ⊆ Y ->
    osupf X ⊆ osupf Y.
red; intros.
rewrite osupf_def in H0|-*.
destruct H0 as (x,?,(y,?,?)); exists x; auto.
exists y; auto.
Qed.

  Instance osupfn_morph : morph1 osupfn.
do 2 red; intros.
apply natrec_morph; auto with *.
do 2 red; intros.
apply Fmono_morph; trivial.
do 2 red; intros; apply osupf_mono; trivial.
Qed.


  Let osupfn_ext : ext_fun N osupfn.
do 2 red; intros; apply osupfn_morph; trivial.
Qed.
  
  Lemma osup0 : osupfn zero == sup I f.
apply natrec_0.
Qed.

  Lemma osupS n : n ∈ N -> osupfn (succ n) == osupf (osupfn n).
intros.
apply natrec_S; trivial.
do 2 red; intros.
apply Fmono_morph.
do 2 red; intros.
apply osupf_mono; trivial.
Qed.

  Lemma isOrd_osupfn : forall n x, n ∈ N -> x ∈ osupfn n -> isOrd x.
intros n x tyn; revert x; elim tyn using N_ind; intros.
*apply H1.
 revert H2; apply in_set_morph;[reflexivity|].
 apply osupfn_ext; trivial.
*rewrite osup0 in H.
 rewrite sup_ax in H; auto.
 destruct H; eauto using isOrd_inv.
*rewrite osupS in H1; auto.
 rewrite osupf_def in H1.
 destruct H1 as (y,?,(y',?,?)).
 rewrite H3; apply isOrd_osup2; eauto using isOrd_inv.
Qed.
  
  Lemma osupfn_mono m n : m ∈ N -> n ∈ N -> le m n -> osupfn m ⊆ osupfn n.
intros tym tyn Hle.
elim Hle using Nle_ind; trivial.
*do 2 red; intros.
 apply incl_set_morph; apply osupfn_morph; auto with *.
*reflexivity.
*clear n tyn Hle; intros.
 rewrite H0.
 rewrite osupS; trivial.
 red; intros.
 rewrite osupf_def.
 exists z; trivial.
 exists z; trivial.
 symmetry; apply osup2_refl.
 apply isOrd_osupfn with n; trivial.
Qed.

  Lemma osup_intro : forall x, x ∈ I -> f x ⊆ osup.
red; intros.
unfold osup.
apply isOrd_sup_intro with (n:=zero); simpl; auto with *.
*apply zero_typ.
*rewrite osup0.
 rewrite sup_ax; eauto.
Qed.


  Lemma isOrd_osup : isOrd osup.
unfold osup.
apply isOrd_intro; intros.
*apply isOrd_sup_elim in H1; trivial.
 destruct H1 as (n,tyn,?).
 apply isOrd_sup_intro with n; trivial.
 revert a b H H0 H1.
 elim tyn using N_ind; intros.
 +rewrite <- H0 in H4|-*; eauto.
 +rewrite osup0 in H1|-*.
  rewrite sup_ax in H1|-*; trivial.
  destruct H1.
  exists x; trivial.
  apply isOrd_plump with b; auto.
 +rewrite osupS in H3|-*; auto.
  rewrite osupf_def in H3|-*.
  destruct H3 as (x,?,(y,?,?)).
  assert (xo : isOrd x).
   apply isOrd_osupfn in H3; trivial.
  assert (yo : isOrd y).
   apply isOrd_osupfn in H4; trivial.
  exists (a ∩ x).
   apply H0 with x; trivial.
    apply isOrd_inter2; trivial.

    apply inter2_incl2.

  exists (a ∩ y).
   apply H0 with y; trivial.
    apply isOrd_inter2; trivial.

    apply inter2_incl2.

   destruct osup2_proof with x y as (_,?); trivial.
   rewrite <- H6; trivial.
   apply eq_intro; intros.
    rewrite inter2_def; split; trivial.
    rewrite <- H5; auto.

    rewrite inter2_def in H7; destruct H7; trivial.

*red; intros.
 apply isOrd_sup_elim in H; [destruct H as (n,tyn,?)|trivial].
 apply isOrd_sup_elim in H0; [destruct H0 as (m,tym,?)|trivial].
 assert (xo : isOrd x).
  apply isOrd_osupfn in H; trivial.
 assert (yo : isOrd y).
   apply isOrd_osupfn in H0; trivial.
 exists (x ⊔ y).
  apply isOrd_sup_intro with (succ(max n m)); simpl; trivial.
   apply succ_typ.
   apply max_typ; trivial.
  rewrite osupS; auto.
  rewrite osupf_def; exists x.
   revert H; apply osupfn_mono; auto with arith.
  exists y; auto with *.
   revert H0; apply osupfn_mono; auto with arith.

  split.
   apply osup2_incl1; apply xo.
   apply osup2_incl2; apply xo.

*apply isOrd_sup_elim in H; [destruct H as (n,tyn,?)|trivial].
 apply isOrd_osupfn in H; trivial.
Qed.

  Lemma osup_lub z :
    isOrd z ->
    (forall x, x ∈ I -> f x ⊆ z) ->
    osup ⊆ z.
red; intros.
apply isOrd_sup_elim in H1; [destruct H1 as (n,tyn,?)|trivial].
revert z0 H1; elim tyn using N_ind; simpl; intros.
*rewrite <- H2 in H4; auto.
*rewrite osup0 in H1.
 rewrite sup_ax in H1; trivial.
 destruct H1.
 revert H2; apply H0; trivial.
*rewrite osupS in H3; trivial.
  rewrite osupf_def in H3; destruct H3 as (x,?,(y,?,?)).
 rewrite H5; apply osup2_lt; auto.
Qed.

  Lemma osup_univ U :
    (forall X F, ext_fun X F -> X ∈ U -> (forall x, x ∈ X -> F x ∈ U) -> 
     sup X F ∈ U) ->
    (forall X x y, X ∈ U -> isOrd x -> x ∈ X -> y ∈ X -> singl (x ⊔ y) ∈ U) ->
    N ∈ U ->
    I ∈ U ->
    (forall x, x ∈ I -> f x ∈ U) ->
    osup ∈ U.
intros.
unfold osup.
apply ord_sup_typ; intros; auto.
elim H4 using N_ind; intros.
*rewrite <- H6; auto.
*rewrite osup0.
 apply H; auto.
*rewrite osupS; trivial.
 unfold osupf.
 apply H; intros; trivial.
  do 2 red; intros; apply replf_morph; auto with *.
  red; intros; apply osup2_morph; auto.

  intros.
  rewrite replf_is_sup.
  2:do 2 red; intros; apply osup2_morph; auto with *.
  apply H; eauto.
   do 2 red; intros; apply singl_morph; apply osup2_morph; auto with *.

   intros.
   apply H0 with (1:=H6); trivial.
   apply isOrd_osupfn in H7; auto.
Qed.

End DirOrdinalSup.

Lemma isOrd_eq_osup : forall o, isOrd o -> o == osup o osucc.
intros.
apply incl_eq.
 red; intros.
 apply osup_intro with (x:=z); trivial.
  do 2 red; intros; apply osucc_morph; trivial.

  apply lt_osucc; eauto using isOrd_inv.

 apply osup_lub; trivial.
  do 2 red; intros; apply osucc_morph; trivial.

  red; intros.
  apply ord_le_lt_trans with x; trivial.
Qed.

  Lemma osup_morph : forall x x' f f',
    x == x' -> eq_fun x f f' -> osup x f == osup x' f'.
unfold osup, ord_sup; intros.
apply sup_morph; auto with *.
red; intros.
unfold osupfn.
apply natrec_morph; trivial.
 apply sup_morph; trivial.
 do 2 red; intros; auto with *.
 unfold osupf.
 apply sup_morph; trivial.
 red; intros.
 apply replf_morph; trivial.
 red; intros. 
 apply osup2_morph; trivial.
Qed.

(** * Projection toward ordinals *)

Definition toOrd (x : set) :=
  osup (subset x isOrd) osucc.

Instance toOrd_morph : morph1 toOrd.
do 2 red; intros.
unfold toOrd.
apply osup_morph.
 apply subset_morph; auto with *.

 red; intros; rewrite H1; reflexivity.
Qed.

Lemma toOrd_isOrd : forall x, isOrd (toOrd x).
intros.
unfold toOrd.
apply isOrd_osup; intros.
 red; red; intros.
 rewrite H0; reflexivity.

 apply isOrd_succ.
 destruct subset_elim2 with (1:=H).
 rewrite H0; trivial.
Qed.

Lemma toOrd_ord : forall o, isOrd o -> toOrd o == o.
intros.
unfold toOrd.
apply incl_eq.
 apply osup_lub; trivial.
  do 2 red; intros; apply osucc_morph; trivial.

  intros.
  red; intros.
  assert (isOrd x).
   apply subset_elim2 in H0; destruct H0.
   rewrite H0; trivial.
  apply subset_elim1 in H0.
  apply isOrd_plump with x; eauto using isOrd_inv.
  apply olts_le in H1; trivial.

 red; intros.
 assert (z ∈ osucc z).
  apply lt_osucc.
  apply isOrd_inv with o; trivial.
 revert H1; apply osup_intro.
  do 2 red; intros; apply osucc_morph; auto.

  apply subset_intro; trivial.
  apply isOrd_inv with o; trivial.
Qed.

Hint Resolve isOrd_wf : core.
