Require Import basic.
Require Import ZF.

(** Theory about well-founded sets *)

(** Definition of well-founded sets. Could be Acc in_set... *)
(** Note: uses higher-order logic, although it could be done in first-order *)
Definition isWf x :=
  forall P : set -> Prop,
  (forall a,(forall b, b ∈ a -> P b)-> P a) -> P x.

Lemma isWf_intro : forall x,
  (forall a, a ∈ x -> isWf a) -> isWf x.
red; intros.
apply H0; intros.
red in H.
apply H; trivial.
Qed.

Lemma isWf_inv : forall a b,
  isWf a -> b ∈ a -> isWf b.
intros a b H; revert b.
red in H; apply H; intros.
apply isWf_intro; eauto.
Qed.

Lemma isWf_ext : forall x x', x == x' -> isWf x -> isWf x'.
intros.
apply isWf_intro; intros.
rewrite <- H in H1.
apply isWf_inv with x; trivial.
Qed.

Global Instance isWf_morph : Proper (eq_set ==> iff) isWf.
apply morph_impl_iff1; auto with *.
do 4 red; intros.
apply isWf_ext with x; auto.
Qed.

Lemma isWf_acc x : isWf x <-> Acc in_set x.
split; intros.
 apply H; intros; constructor; auto.

 elim H; intros; apply isWf_intro; auto.
Qed.

Lemma isWf_ind :
  forall P : set -> Prop,
  (forall a, isWf a -> (forall b, b ∈ a -> P b)-> P a) ->
  forall x, isWf x ->  P x.
intros.
cut (isWf x /\ P x).
 destruct 1; trivial.
apply H0; intros.
assert (isWf a).
 apply isWf_intro; intros; apply H1; trivial.
split; trivial.
apply H; intros; trivial.
apply H1; trivial.
Qed.

(** The class of well-founded sets form a model of IZF+foundation axiom *)

Lemma isWf_zero: isWf empty.
apply isWf_intro; intros.
apply empty_ax in H; contradiction.
Qed.

Lemma isWf_pair : forall x y,
  isWf x -> isWf y -> isWf (pair x y).
intros.
apply isWf_intro; intros.
elim pair_elim with (1:=H1); intros.
 rewrite H2; trivial.
 rewrite H2; trivial.
Qed.

Lemma isWf_power : forall x, isWf x -> isWf (power x).
intros.
apply isWf_intro; intros.
apply isWf_intro; intros.
apply isWf_inv with x; trivial.
apply power_elim with a; trivial.
Qed.

Lemma isWf_union : forall x, isWf x -> isWf (union x).
intros.
apply isWf_intro; intros.
elim union_elim with (1:=H0); intros.
apply isWf_inv with x0; trivial.
apply isWf_inv with x; trivial.
Qed.

Lemma isWf_incl x y : isWf x -> y ⊆ x -> isWf y.
intros.
apply isWf_intro; intros.
apply isWf_inv with x; auto.
Qed.

Lemma isWf_subset : forall x P, isWf x -> isWf (subset x P).
intros.
apply isWf_incl with x; trivial.
red; intros.
apply subset_elim1 in H0; trivial.
Qed.

Lemma isWf_replf : forall x F,
    ext_fun x F ->
    (forall a, a ∈ x -> isWf (F a)) ->
    isWf (replf x F).
intros.
apply isWf_intro; intros.
rewrite replf_ax in H1;[|trivial].
destruct H1 as (b,?,?).
rewrite H2; auto.
Qed.
Lemma isWf_sup : forall x F,
    ext_fun x F ->
    (forall a, a ∈ x -> isWf (F a)) ->
    isWf (sup x F).
intros.
apply isWf_union.
apply isWf_replf; trivial.
Qed.

Require ZFrepl.

Lemma isWf_repl : forall x R,
  ZFrepl.repl_rel x R ->
  (forall a b, a ∈ x -> R a b -> isWf b) ->
  isWf (repl x R).
intros.
apply isWf_intro; intros.
elim ZFrepl.repl_elim with (1:=H) (2:=H1); intros; eauto.
Qed.

Lemma isWf_inter2 : forall x y, isWf x -> isWf y -> isWf (x ∩ y).
unfold inter2; intros.
unfold inter.
apply isWf_subset.
apply isWf_union.
apply isWf_pair; trivial.
Qed.

(** A well-founded set does not belong to itself. *)
Lemma isWf_antirefl : forall x, isWf x -> ~ x ∈ x.
intros.
elim H using isWf_ind; clear x H; intros.
red; intros.
apply H0 with a; trivial.
Qed.

(** * Defining well-founded sets without resorting to higher-order *)

Module FirstOrder.

(** Transitive closure *)

Definition tr x p :=
  x ∈ p /\
  (forall a b, a ∈ b -> b ∈ p -> a ∈ p).

Instance tr_morph : Proper (eq_set ==> eq_set ==> iff) tr.
unfold tr.
apply morph_impl_iff2; auto with *.
do 4 red; intros.
destruct H1; split; intros.
 rewrite <- H; rewrite <- H0; trivial.

 rewrite <- H0 in H4|-*; eauto.
Qed.

Definition isTransClos x y :=
  tr x y /\ (forall p, tr x p -> y ⊆ p).

Instance isTransClos_morph : Proper (eq_set ==> eq_set ==> iff) isTransClos.
apply morph_impl_iff2; auto with *.
do 5 red; intros.
destruct H1.
split; intros.
 rewrite <- H; rewrite <- H0; trivial.
 rewrite <- H in H3; rewrite <- H0; auto.
Qed.

Lemma isTransClos_fun x y y' :
  isTransClos x y ->
  isTransClos x y' -> y == y'.
unfold isTransClos; intros.
destruct H; destruct H0.
apply incl_eq; auto.
Qed.

Lemma isTransClos_intro a f :
  morph1 f ->
  (forall b, b ∈ a -> isTransClos b (f b)) ->
  isTransClos a (singl a ∪ sup a f).
split; intros.
 split; intros.
  apply union2_intro1.
  apply singl_intro.

  apply union2_intro2.
  rewrite sup_ax; auto with *.
  apply union2_elim in H2; destruct H2.
   apply singl_elim in H2.
   rewrite H2 in H1.
   exists a0; trivial.
   apply H0; trivial.

   rewrite sup_ax in H2; auto with *.
   destruct H2.
   exists x; trivial.
   destruct H0 with (1:=H2).
   destruct H4; eauto.

 red; intros.
 destruct H1.
 apply union2_elim in H2; destruct H2.
  apply singl_elim in H2.
  rewrite H2; trivial.

  rewrite sup_ax in H2; auto with *.
  destruct H2.
  destruct H0 with (1:=H2).
  apply H6; auto.
  split; eauto.
Qed.


(** Alternative definition, only using first-order quantification *)
Definition isWf' x :=
  exists2 c:set, isTransClos x c &
  forall p:set, 
    (forall a:set, a ⊆ c -> a ⊆ p -> a ∈ p) -> x ∈ p.

Definition trClos x :=
  ZFrepl.WFR eq (fun y=>y)
    (fun f y (_:unit) => singl y ∪ sup y (fun z => f z tt)) x tt.

Global Instance trClos_morph : morph1 trClos.
do 2 red; intros; unfold trClos.
apply ZFrepl.WFR_morph0; auto with *.
Qed.

Lemma trClos_eqn x :
  Acc in_set x ->
  trClos x == singl x ∪ sup x trClos.
intros.
unfold trClos; rewrite ZFrepl.WFR_eqn; auto with *.
intros.
apply union2_morph; [rewrite H2;reflexivity|].  
 apply sup_morph; [rewrite H2; reflexivity|].
 red; intros; auto.
Qed.

Lemma trClos_def x :
  Acc in_set x ->
  isTransClos x (trClos x).
induction 1.  
apply Acc_intro in H.
rewrite trClos_eqn; trivial.
apply isTransClos_intro; auto with *.
Qed.

Lemma trClos_intro1 x : Acc in_set x -> x ∈ trClos x.
intro.
destruct trClos_def with (1:=H).
destruct H0; trivial.
Qed.

Lemma trClos_intro2 x y z : Acc in_set x -> y ∈ trClos x -> z ∈ y -> z ∈ trClos x.
intros.
destruct trClos_def with (1:=H).
destruct H2; eauto.
Qed.

Lemma trClos_ind x (P:set->Prop) :
  isWf x ->
  (forall x', x==x' -> P x') ->
  (forall y z, y ∈ trClos x -> P y -> z ∈ y -> P z) ->
  forall y,
  y ∈ trClos x ->
  P y.
intros.
rewrite isWf_acc in H.
destruct trClos_def with (1:=H).
assert (y ∈ subset (trClos x) (fun z => forall z', z==z' -> P z')).
 apply H4; trivial.
 split; intros.
  apply subset_intro; trivial.
  apply trClos_intro1; trivial.

  rewrite subset_ax in H6; destruct H6.
  destruct H7.
  rewrite H7 in H5,H6.
  apply subset_intro.
   apply trClos_intro2 with x0; auto.

   intros; apply H1 with x0; auto with *.
   rewrite <- H9; trivial.
rewrite subset_ax in H5; destruct H5.
destruct H6.
eauto with *.
Qed.


Lemma isWf_trClos x : isWf x -> isWf (trClos x).
intros.
apply isWf_intro; intros.
elim H0 using trClos_ind; intros; trivial.
 rewrite <- H1; trivial.

 apply isWf_inv with y; trivial.
Qed.

Lemma trClos_trans x y z : isWf x -> y ∈ trClos x -> z ∈ trClos y -> z ∈ trClos x.
intros.
revert z H1; elim H0 using trClos_ind; intros; trivial.
 rewrite H1; trivial.

 apply H2.
 assert (isWf y0).
  apply isWf_inv with (trClos x); auto.
  apply isWf_trClos; trivial.
 elim H4 using trClos_ind; intros; trivial.
  apply isWf_inv with y0; trivial.

  rewrite isWf_acc in H5.
  rewrite <- H6; apply trClos_intro2 with y0; trivial.
  apply trClos_intro1; trivial.

  rewrite isWf_acc in H5.
  apply trClos_intro2 with y1; trivial.
Qed.

(** The equivalence result *)
Lemma isWf_equiv x :
  isWf x <-> isWf' x.
split; intros.
*rewrite isWf_acc in H.
 induction H.
 assert (tcx : isTransClos x (trClos x)) by (apply trClos_def;constructor;trivial).
 exists (trClos x);[trivial|].
 intros.
 destruct tcx.
 destruct H2.
 apply H1.
 +red; intros.
  apply H4 with (1:=H5); trivial.
 +red; intros.
  destruct H0 with (1:=H5).
  assert (x0 == trClos z).
  {apply isTransClos_fun with (1:=H6).
   apply trClos_def; auto. }
  apply H7; intros.
  rewrite H8 in H9.
  apply H1; trivial.
  rewrite H9.
  rewrite (trClos_eqn x); [|constructor;auto].
  red; intros.
  apply union2_intro2.
  apply sup_ax.
  do 2 red; intros; apply ZFrepl.WFR_morph0; auto with *.
  exists z; trivial.
*destruct H as (c,?,?).
 destruct H.
 red; intros.
 cut (x ∈ subset (power c) (fun x' => forall x'', x' == x'' -> P x'')).
 {rewrite subset_ax; destruct 1 as (?,(x',?,?)).
  auto with *. }
 apply H0; intros.
 apply subset_intro; intros.
  apply power_intro; auto.

  apply H2; intros.
  rewrite <- H5 in H6; clear x'' H5.
  generalize (H4 _ H6); rewrite subset_ax; intros (_,(b',?,?)); auto with *.
Qed.

Hint Resolve isWf_trClos trClos_intro1 trClos_intro2 : core.


Lemma isWf_ind2 x (P : set -> Prop) :
  (forall a, a ∈ trClos x -> (forall b, b ∈ a -> P b)-> P a) ->
  isWf x ->  P x.
intros.
assert (H0' := H0).
rewrite isWf_acc in H0'.
generalize (trClos_intro1 _ H0').
pattern x at 1 3; elim H0 using isWf_ind; intros; eauto.
Qed.

End FirstOrder.

Hint Resolve isWf_morph : core.
