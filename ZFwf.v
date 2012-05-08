Require Export basic.
Require Import ZF.

(** Theory about well-founded sets *)

Section WellFoundedSets.

(** Definition of well-founded sets. Could be Acc in_set... *)
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

Require Import ZFrepl.

Lemma isWf_repl : forall x R,
  repl_rel x R ->
  (forall a b, a ∈ x -> R a b -> isWf b) ->
  isWf (repl x R).
intros.
apply isWf_intro; intros.
elim repl_elim with (1:=H) (2:=H1); intros; eauto.
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

(** The equivalence result *)
Lemma isWf_equiv x :
  isWf x <-> isWf' x.
split; intros.
 apply H; intros.
 assert (Hm : ext_fun a (fun b => uchoice (isTransClos b))).
  do 2 red; intros.
  apply uchoice_morph_raw; red; intros.
  apply isTransClos_morph; trivial.
 assert (Hch : forall b, b ∈ a -> uchoice_pred (isTransClos b)).
  split; [|split; intros]; auto.
   intros.
   rewrite <- H2; trivial.

   destruct H0 with (1:=H1).
   exists x0; trivial.

   apply isTransClos_fun with b; trivial.
 exists (singl a ∪ sup a (fun b => uchoice (isTransClos b))).
  apply isTransClos_intro.
   do 2 red; intros.
   apply uchoice_morph_raw; red; intros.
   apply isTransClos_morph; trivial.

   intros.
   apply uchoice_def; auto.

  intros.
  apply H1; intros; trivial.
   red; intros; apply union2_intro2.
   rewrite sup_ax; trivial.
   exists z; trivial.
   assert (isTransClos z (uchoice (isTransClos z))).
    apply uchoice_def; auto.
   destruct H3.
   destruct H3; trivial.

   red; intros.
   destruct H0 with (1:=H2).
   apply H4; intros.
   apply H1; trivial.
   red; intros; apply union2_intro2.
   rewrite sup_ax; trivial.
   exists z; trivial.
   rewrite <- uchoice_ext with (x:=x0); auto.

 red; intros.
 destruct H as (c,?,?).
 destruct H.
 cut (x ∈ subset (power c) (fun x' => forall x'', x' == x'' -> P x'')).
  rewrite subset_ax; destruct 1 as (?,(x',?,?)).
  auto with *.
 apply H1; intros.
 apply subset_intro; intros.
  apply power_intro; auto.

  apply H0; intros.
  rewrite <- H5 in H6; clear x'' H5.
  generalize (H4 _ H6); rewrite subset_ax; intros (_,(b',?,?)); auto with *.
Qed.

Lemma isWf_clos_ex x : isWf x -> uchoice_pred (isTransClos x).
split;[|split]; intros.
 rewrite <- H0; trivial.

 rewrite isWf_equiv in H; destruct H; eauto.

 apply isTransClos_fun with x; trivial.
Qed.

Definition trClos x := uchoice (isTransClos x).

Global Instance trClos_morph : morph1 trClos.
do 2 red; intros; unfold trClos.
apply uchoice_morph_raw; red; intros.
apply isTransClos_morph; trivial.
Qed.

Lemma trClos_intro1 x : isWf x -> x ∈ trClos x.
intro.
specialize isWf_clos_ex with (1:=H); intro.
apply uchoice_def in H0.
destruct H0 as ((?,_),_); trivial.
Qed.

Lemma trClos_intro2 x y z : isWf x -> y ∈ trClos x -> z ∈ y -> z ∈ trClos x.
intros.
specialize isWf_clos_ex with (1:=H); intro.
apply uchoice_def in H2.
destruct H2 as ((_,?),_); eauto.
Qed.

Lemma trClos_ind x (P:set->Prop) :
  isWf x ->
  (forall x', x==x' -> P x') ->
  (forall y z, y ∈ trClos x -> P y -> z ∈ y -> P z) ->
  forall y,
  y ∈ trClos x ->
  P y.
intros.
specialize isWf_clos_ex with (1:=H); intro.
apply uchoice_def in H3.
destruct H3 as (?,?).
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

  rewrite <- H6; apply trClos_intro2 with y0; trivial.
  apply trClos_intro1; trivial.

  apply trClos_intro2 with y1; trivial.
Qed.

Hint Resolve isWf_trClos trClos_intro1 trClos_intro2.


Lemma isWf_ind2 x (P : set -> Prop) :
  (forall a, a ∈ trClos x -> (forall b, b ∈ a -> P b)-> P a) ->
  isWf x ->  P x.
intros.
generalize (trClos_intro1 _ H0).
pattern x at 1 3; elim H0 using isWf_ind; intros; eauto.
Qed.

(** Transfinite iteration on a well-founded set (not using higher-order) *)
(** #<a name="WithoutHigherOrder"></a># *)

Section TransfiniteRecursion.

  Variable F : (set -> set) -> set -> set.
  Hypothesis Fm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) F.
  Hypothesis Fext : forall x f f', eq_fun x f f' -> F f x == F f' x.

Require Import ZFpairs ZFrelations.

(*
Attempt to prove directly that the relation characterizing the result of the
transfinite iteration is functional and defined on well-founded sets.
*)

(*
Let R x y :=
  forall r:set,
  (forall x' f, x' ∈ trClos x ->
   (forall z, z ∈ x' -> couple z (cc_app f z) ∈ r) ->
   couple x' (F (cc_app f) x') ∈ r) ->
  couple x y ∈ r.

Lemma R_inv x : isWf x -> forall y, R x y ->
  exists2 f,
    (forall z, z ∈ x -> R z (cc_app f z)) &
    y == F (cc_app f) x.
induction 1 using isWf_ind; intros.

intros.
red in H.


Lemma R_intro :
  forall 

  R x (F (cc_app f) x)


Lemma R_ex x :
  isWf x -> uchoice_pred (R x).
intro.
cut (forall z, z ∈ trClos x -> uchoice_pred (R z)); eauto.
elim H using isWf_ind2; intros.
split; [|split]; intros.
 admit.

 exists (F (cc_app (cc_lam z (fun z' => uchoice (R z')))) z).
 red; intros.
 assert (wfz : isWf z).
  apply isWf_inv with (trClos x); auto.
  apply trClos_trans with a; trivial.
 apply H3; intros; auto.
 rewrite cc_beta_eq; trivial. 2:admit.
 assert (uchoice_pred (R z0)).
  admit.
 apply uchoice_def in H5.
 apply H5.
 intros; apply H3; trivial.
 apply trClos_trans with z0; eauto.

 assert (wfz : isWf z).
  apply isWf_inv with (trClos x); auto.
  apply trClos_trans with a; trivial.
 pose (f:=sup z (fun b => replf (trClos b) (fun b' => couple b' (uchoice (R b'))))).
 pose (r :=union2 (singl (couple z (F (cc_app (cc_lam z (fun z' => uchoice (R z')))) z))) f).
 assert (discr : forall b, z ∈ trClos b -> b ∈ z -> False).
admit.
(*  elim wfz using isWf_ind; intros.
  assert (wfb : isWf b).
   apply isWf_inv with a0; trivial.
  revert H8; elim H7 using trClos_ind; intros; trivial.
   rewrite <- H8 in H9; apply isWf_antirefl in H9; trivial.
*)
 assert (h := fun h => conj (H3 r h) (H4 r h)).
 destruct h.
  intros.
assert (x'0 == z \/ exists2 z', z' ∈ z & x'0 ∈ trClos z') by admit.
  destruct H7.
   rewrite H7; unfold r; apply union2_intro1.
   apply singl_intro_eq.
   apply couple_morph; auto with *.
   apply Fext; intros.
   red; intros.
   rewrite <- H9.
   rewrite cc_beta_eq; auto. 2:admit.
   rewrite <- H7 in H8; specialize H6 with (1:=H8).
   unfold r in H6; rewrite union2_ax in H6; destruct H6.
    apply singl_elim in H6.
    apply couple_injection in H6; destruct H6 as (H6,_).
    rewrite H6 in H8; rewrite H7 in H8; apply isWf_antirefl in H8; trivial; contradiction.

    unfold f in H6.
    rewrite sup_ax in H6. 2:admit.
    destruct H6.
    rewrite replf_ax in H10. 2:admit.
    destruct H10.
    apply couple_injection in H11; destruct H11.
    rewrite H12; apply uchoice_morph_raw; red; intros.
    admit. (*R_morph *)

   destruct H7 as (z',?,?).
   clear H5.
   unfold r; apply union2_intro2.
   unfold f.
   rewrite sup_ax. 2:admit.
   exists z'; trivial.
   rewrite replf_ax. 2:admit.
   exists x'0; trivial.
   apply couple_morph; auto with *.   
   apply uchoice_ext.
    assert (exists2 b, b ∈ a & z' ∈ trClos b).
     admit.
    destruct H5.
    apply H1 with x1; trivial.
    apply trClos_trans with z'; trivial.
    apply isWf_inv with (trClos x); eauto.

    red; intros.
    apply H5; auto.
     apply trClos_intro1.
     apply isWf_inv with (trClos z); eauto.
     apply trClos_trans with z'; trivial.
     apply trClos_intro2 with z; auto.

     intros; apply H6.

*)

  Definition isTR_rel F P :=
    forall o y,
    couple o y ∈ P ->
    exists2 f, (forall n, n ∈ o -> couple n (cc_app f n) ∈ P) &
      y == F (cc_app f) o.

  Lemma isTR_rel_fun P P' o y y':
    isWf o ->
    isTR_rel F P ->
    isTR_rel F P' -> 
    couple o y ∈ P ->
    couple o y' ∈ P' ->
    y == y'.
intros wfo istr istr' inP inP'; revert y y' inP inP'; elim wfo using isWf_ind; intros.
destruct istr with (1:=inP) as (f,?,?).
destruct istr' with (1:=inP') as (f',?,?).
rewrite H2; rewrite H4; apply Fext; auto.
red; intros.
rewrite <- H6; clear x' H6.
apply H0 with x; auto.
Qed.

  Instance isTR_rel_morph_gen :
    Proper (((eq_set ==> eq_set) ==> eq_set ==> eq_set) ==> eq_set ==> iff) isTR_rel.
do 3 red; intros.
unfold isTR_rel.
apply fa_morph; intro o.
apply fa_morph; intro y'.
rewrite H0.
apply fa_morph; intros ?.
apply ex2_morph; red; intros; auto with *.
 apply fa_morph; intros n.
 rewrite H0; reflexivity.

 split; intros h;rewrite h;[|symmetry]; (apply H; [apply cc_app_morph|];auto with *).
Qed.

  Instance isTR_rel_morph : Proper (eq_set==>iff) (isTR_rel F).
do 2 red; intros.
apply fa_morph; intro o.
apply fa_morph; intro y'.
rewrite H.
apply fa_morph; intros ?.
apply ex2_morph; red; intros; auto with *.
apply fa_morph; intros n.
rewrite H; reflexivity.
Qed.

  Definition TRP_rel F o P :=
    isTR_rel F P /\
    (exists y, couple o y ∈ P) /\
    forall P' y, isTR_rel F P' -> couple o y ∈ P' -> P ⊆ P'.

  Instance TRP_rel_morph_gen :
    Proper (((eq_set ==> eq_set) ==> eq_set ==> eq_set) ==> eq_set ==> eq_set ==> iff) TRP_rel.
do 4 red; intros.
unfold TRP_rel.
apply and_iff_morphism.
 apply isTR_rel_morph_gen; trivial.
apply and_iff_morphism.
 apply ex_morph; red; intros; rewrite H0; rewrite H1; reflexivity.

 apply fa_morph; intros P'.
 apply fa_morph; intros w.
 apply impl_morph.
  apply isTR_rel_morph_gen; auto with *.

  intros; rewrite H0; rewrite H1; reflexivity.
Qed.

  Instance TRP_rel_morph : Proper (eq_set==>eq_set==>iff) (TRP_rel F).
do 3 red; intros.
unfold TRP_rel.
apply and_iff_morphism.
 rewrite H0; reflexivity.
apply and_iff_morphism.
 apply ex_morph; red; intros; rewrite H; rewrite H0; reflexivity.

 apply fa_morph; intros P'.
 apply fa_morph; intros w.
 rewrite H; rewrite H0; reflexivity.
Qed.

  Lemma TR_img_ex x P : isWf x ->
    TRP_rel F x P ->
    uchoice_pred (fun y => couple x y ∈ P).
intros.
split;[|split]; intros.
 rewrite <- H1; trivial.

 destruct H0 as (_,(?,_)); trivial.

 destruct H0 as (?,(?,?)).
 apply isTR_rel_fun with (2:=H0)(3:=H0)(4:=H1)(5:=H2); trivial.
Qed.


  Lemma TR_rel_ex o :
    isWf o -> uchoice_pred (TRP_rel F o).
intro wfo; elim wfo using isWf_ind; clear o wfo; intros.
split;[|split]; intros.
 revert H2; apply TRP_rel_morph; auto with *.

 pose (P:=singl(couple a (F (fun b=> uchoice(fun y => couple b y ∈ uchoice(TRP_rel F b))) a)) ∪
          sup a (fun b => uchoice(TRP_rel F b))).
 assert (Pax:forall z, z ∈ P <->
     z == couple a (F (fun b=> uchoice(fun y => couple b y ∈ uchoice(TRP_rel F b))) a) \/
     exists2 b, b ∈ a & z ∈ uchoice(TRP_rel F b)).
  intros; unfold P; rewrite union2_ax; apply or_iff_morphism.
   split; intros.
    apply singl_elim in H1; trivial.
    rewrite H1; apply singl_intro.

   rewrite sup_ax.
    reflexivity.

    do 2 red; intros; apply uchoice_morph_raw.
    apply TRP_rel_morph; trivial.
 assert (ychm : morph1 (fun b =>
      uchoice (fun y0 => couple b y0 ∈ uchoice (TRP_rel F b)))).
  do 2 red; intros.
  apply uchoice_morph_raw.
  red; intros.
  rewrite H1; rewrite H2; reflexivity.
 exists P.
 split;[|split]; intros.
  red; intros.
  rewrite Pax in H1; destruct H1 as [?|(b,?,?)].
   apply couple_injection in H1; destruct H1.
   exists (cc_lam o (fun b=> uchoice
            (fun y : set => couple b y ∈ uchoice(TRP_rel F b)))); intros.
    rewrite cc_beta_eq; trivial.
     rewrite Pax; right.
     rewrite H1 in H3; exists n; trivial.
     apply uchoice_def.
     apply TR_img_ex.
      apply isWf_inv with a; trivial.

      apply uchoice_def; auto.

     do 2 red; intros; apply uchoice_morph_raw; red; intros.
     rewrite H5; rewrite H6; reflexivity.
     
    rewrite H1; rewrite H2; apply Fext.
    red; intros.
    rewrite <- H4.
    rewrite cc_beta_eq; auto with *.

   destruct (uchoice_def _ (H0 _ H1)) as (?,trp').
   destruct H3 with (1:=H2) as (f,?,?).
   exists f; trivial; intros.
   rewrite Pax; right.
   exists b; auto.

  exists (F (fun b => uchoice (fun y => couple b y ∈ uchoice (TRP_rel F b))) a).
  rewrite Pax; left; reflexivity.

  red; intros.
  rewrite Pax in H3; destruct H3 as [?|(y',?,?)].
   destruct H1 with (1:=H2) as (f,?,?).
   rewrite H5 in H2; rewrite H3; revert H2; apply in_reg.
   apply couple_morph; auto with *.
   apply Fext; red; intros.
   apply uchoice_ext; auto.
    rewrite H6 in H2; auto.
    apply TR_img_ex.
     apply isWf_inv with a; trivial.

     apply uchoice_def; auto.

    rewrite <- H6; clear x' H6.
    specialize H0 with (1:=H2).
    apply uchoice_def in H0.
    destruct H0 as (?,((yx,?),_)).
    specialize H4 with (1:=H2).
    rewrite isTR_rel_fun with (2:=H1) (3:=H0) (4:=H4) (5:=H6); trivial.
    apply isWf_inv with a; trivial.

  specialize H0 with (1:=H3).
  apply uchoice_def in H0; destruct H0 as (?,((w,?),?)).
  assert (z == couple (fst z) (snd z)).
   assert (z ∈ subset (uchoice(TRP_rel F y')) (fun z => z == couple (fst z) (snd z))).
    apply H6 with w; trivial.
     red; intros.
     apply subset_elim1 in H7.
     destruct H0 with (1:=H7) as (f',?,?).
     exists f'; intros; trivial.
     apply subset_intro; auto.
     rewrite fst_def; rewrite snd_def; reflexivity.

     apply subset_intro; trivial.
     rewrite fst_def; rewrite snd_def; reflexivity.
   apply subset_elim2 in H7; destruct H7.
   rewrite H7; trivial.
  rewrite H7 in H4|-*.
  destruct H1 with (1:=H2) as (f0,?,_).
  specialize H8 with (1:=H3).
  apply H6 with (cc_app f0 y'); trivial.

 destruct H1 as (?,((y,?),?)).
 destruct H2 as (?,((y',?),?)).
 apply incl_eq; eauto.
Qed.

  Definition WFR x := uchoice (fun y => couple x y ∈ uchoice(TRP_rel F x)).

  Lemma WFR_eqn x : isWf x -> WFR x == F WFR x.
unfold WFR; intros.
specialize TR_rel_ex with (1:=H); intro.
apply uchoice_def in H0.
generalize H0; intros (?,_).
apply TR_img_ex in H0; trivial.
apply uchoice_def in H0.
destruct H1 with (1:=H0) as (f,?,?).
rewrite H3; apply Fext; red; intros.
rewrite H5 in H4|-*; clear x0 H5.
assert (isWf x') by eauto using isWf_inv.
specialize H2 with (1:=H4).
specialize TR_rel_ex with (1:=H5); intro.
apply uchoice_def in H6.
generalize H6; intros (?,_).
apply TR_img_ex in H6; trivial.
apply uchoice_def in H6.
apply isTR_rel_fun with (4:=H2) (5:=H6); trivial.
Qed.

  Lemma WFR_ind : forall x (P:set->set->Prop),
    Proper (eq_set ==> eq_set ==> iff) P ->
    isWf x ->
    (forall y, isWf y ->
     (forall x, x ∈ y -> P x (WFR x)) ->
     P y (F WFR y)) ->
    P x (WFR x).
intros x P Pm wfx Hrec.
induction wfx using isWf_ind; intros.
rewrite WFR_eqn; trivial.
apply Hrec; auto with *; intros.
Qed.

  Global Instance WFR_morph0 : morph1 WFR.
do 2 red; intros.
unfold WFR.
apply uchoice_morph_raw.
red; intros.
rewrite H; rewrite H0; reflexivity.
Qed.

End TransfiniteRecursion.

  Global Instance WFR_morph :
    Proper (((eq_set ==> eq_set) ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) WFR.
do 3 red; intros.
unfold WFR.
apply uchoice_morph_raw; red; intros.
rewrite (couple_morph _ _ H0 _ _ H1).
split; apply eq_elim; [|symmetry]; apply uchoice_morph_raw; red; intros.
 apply TRP_rel_morph_gen; trivial.
 apply TRP_rel_morph_gen; trivial.
Qed.

End WellFoundedSets.

Hint Resolve isWf_morph.

(*
(** Transfinite iteration on well-founded sets (higher-order version) *)
Module F.
Section WFR.
Variable A : Type.
Variable eqA : A -> A -> Prop.
Hypothesis symA : Symmetric eqA.
Hypothesis transA : Transitive eqA.
Existing Instance symA.
Existing Instance transA.
Variable uch : forall P:Prop, (P-> A) -> A.
Hypothesis uch_eq : forall P f h, eqA (uch P f) (f h).

Hypothesis F:(set->A)->set->A.
Hypothesis Fext : forall o o' f f',
  isWf o ->
  (forall o' o'', o' ∈ o -> o'==o'' -> eqA (f o') (f' o'')) ->
  o == o' ->
  eqA (F f o) (F f' o').

Fixpoint TR_acc (o:set) (H:Acc in_set o) : A :=
  F (fun o' => uch _ (fun (h:o' ∈ o) => TR_acc o' (Acc_inv H h))) o.


Hypothesis proj1 : set -> A.
Hypothesis proj1m : Proper (eq_set ==> eqA) proj1.
Hypothesis proj1inj : forall x x', eqA (proj1 x) (proj1 x') -> x == x'.
Hypothesis F_typ' : forall f x, 
  x ∈ c ->
  (forall y, y ∈ x -> exists y', eqA (f y) (proj1 y')) ->
  exists y', eqA (F f x) (proj1 y').

(*
Hypothesis proj : A -> set.
Hypothesis retA : forall x, proj (proj1 x) == x.
Hypothesis projm : Proper (eqA ==> eq_set) proj.
*)

Let proj' a := uchoice (fun x => eqA (proj1 x) a). 
Let proj'm : Proper (eqA ==> eq_set) proj'.
Admitted.
Existing Instance proj'm.
Let retA' x : proj' (proj1 x) == x.
unfold proj'.
symmetry; apply uchoice_ext.
 split;[|split]; intros.
  rewrite H in H0; trivial.
  exists x; apply proj1m; reflexivity.
  apply proj1inj.
  rewrite H0; trivial.

 apply proj1m; reflexivity.
Qed.


Variable ord : set.
Variable c : set.
Hypothesis trcl : tr ord c.
Hypothesis cwf : forall z, z ∈ c -> isWf z.

  Let G f o :=
    cond_set (o ∈ c) (proj' (F (fun x => proj1 (f x)) o)).

  Let Fext : forall o f f', eq_fun o f f' -> G f o == G f' o.
unfold G; intros.
apply cond_set_morph2; auto with *.
intros.
apply proj'm.
apply Fext; auto with *.
Qed.


Lemma equiv o h :
  o ∈ c ->
  eqA (TR_acc o h) (proj1 (WFR G o)).
induction h using Acc_indd; simpl; intros.
rewrite WFR_eqn.
 2:admit.
 2:apply Fext.
 2:rewrite isWf_acc; constructor; trivial.
unfold G at 1.
rewrite cond_set_ok; trivial.
destruct F_typ' with (f:=fun x => proj1 (WFR G x)) (x:=x); trivial.
 intros.
 exists (WFR G y).
 apply proj1m; reflexivity.

 rewrite H1.
 rewrite retA'.
 rewrite <- H1.
 apply Fext; intros; auto with *.
 rewrite uch_eq with (P:=o' ∈ x) (h:=H2).
 rewrite <- H3.
 apply H.
 destruct trcl; eauto.




destruct F_typ' with (f:=fun o' => uch (o' ∈ x) (fun h => TR_acc o' (a o' h))) (x:=x); trivial.
 intros.
 exists (WFR G y).
 rewrite uch_eq with (P:=y ∈ x) (h:=H1).
 apply H.
 destruct trcl; eauto.



apply transitivity with (1:=H1).
apply proj1m.
unfold proj'


 with (f:=fu
  eqA (F f x) (proj1 (

  (forall y, y ∈ x -> eqA (f y) (proj1 (proj' (f y)))) ->
  eqA (F f x) (proj1 (proj' (F f x))).
rewrite F_typ.
 2:trivial.

 apply proj1m.
 apply proj'm.
 apply Fext.
  auto.
  2:reflexivity.
 intros.
 rewrite uch_eq with (P:=o' ∈ x) (h:=H1).
 rewrite <- H2.
 apply H.
 destruct trcl.
 apply H4 with x; trivial.

 intros.
assert (eqA (uch (y ∈ x) (fun h => TR_acc y (a y h))) (proj1 (WFR G y))).
 rewrite uch_eq with (P:=y ∈ x) (h:=H1).
 apply H.
 destruct trcl; eauto.
apply transitivity with (1:=H2).
apply proj1m.
rewrite H2.
symmetry; apply retA'.
Qed.




(* OK: *)
Hypothesis proj : A -> set.
Hypothesis proj1 : set -> A.
Hypothesis retA : forall x, proj (proj1 x) == x.
Hypothesis projm : Proper (eqA ==> eq_set) proj.
Hypothesis proj1m : Proper (eq_set ==> eqA) proj1.

  Let G f o :=
    cond_set (isWf o) (proj (F (fun x => proj1 (f x)) o)).

  Let Fext : forall o f f', eq_fun o f f' -> G f o == G f' o.
unfold G; intros.
apply cond_set_morph2; auto with *.
Qed.

Lemma equiv o h :
  eqA (TR_acc o h) (proj1 (WFR G o)).
induction h using Acc_indd; simpl; intros.
rewrite WFR_eqn.
unfold G at 1.
rewrite cond_set_ok.
Axiom F_typ : forall f x, 
  (forall y, y ∈ x -> eqA (f y) (proj1 (proj (f y)))) ->
  eqA (F f x) (proj1 (proj (F f x))).
rewrite F_typ.
apply proj1m.
apply projm.
apply Fext.
 admit.

 intros.
 rewrite uch_eq with (P:=o' ∈ x) (h:=H0).
 rewrite <- H1.
 apply H.

 reflexivity.

rewrite 

  Variable F : (set -> set) -> set -> set.
  Hypothesis Fm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) F.
  Hypothesis Fext : forall x f f', eq_fun x f f' -> F f x == F f' x.





Lemma TR_acc_morph o o' h h' :
  o == o' ->
  eqA (TR_acc o h) (TR_acc o' h').
revert o' h'; induction h using Acc_indd; destruct h'; simpl; intros.
apply Fext; intros; trivial.
 rewrite isWf_acc; constructor; trivial.
rewrite uch_eq with (P:=o'0 ∈ x) (h:=H1).
assert (h:=H1); rewrite H0 in h; rewrite H2 in h.
rewrite uch_eq with (P:=o'' ∈ o') (h:=h).
auto.
Qed.

Definition TR o := uch _ (TR_acc o).

Lemma TR_acc_eqn o h :
  eqA (TR_acc o h) (F TR o).
case h; simpl; intros.
apply Fext; intros; auto with *.
 rewrite isWf_acc; constructor; trivial.
unfold TR.
rewrite (uch_eq (o' ∈ o) _ H).
assert (h' := H); rewrite H0 in h'.
rewrite (uch_eq (Acc in_set o'') _ (a _ h')).
apply TR_acc_morph; trivial.
Qed.

Lemma TR_eqn o :
  isWf o ->
  eqA (TR o) (F TR o).
intros.
rewrite isWf_acc in H.
rewrite <- TR_acc_eqn with (h:=H).
unfold TR.
apply uch_eq with (P:=Acc in_set o) (h:=H).
Qed.

Global Instance TR_morph : morph2 TR.
do 3 red; intros.
unfold TR.
apply ZFrepl.uchoice_morph_raw; red; intros.
split; destruct 1.
 assert (Acc in_set y) by (rewrite <- H; trivial).
 exists H3.
 rewrite <- H1; rewrite H2; apply TR_acc_morph; trivial.

 assert (Acc in_set x) by (rewrite H; trivial).
 exists H3.
 rewrite H1; rewrite H2; symmetry; apply TR_acc_morph; trivial.
Qed.











(* OK: *)

Hypothesis F:(set->set->set)->set->set->set.
Hypothesis Fext : forall o o' f f' x x',
  isWf o ->
  (forall o' o'' x x', o' ∈ o -> o'==o'' -> x==x' -> f o' x == f' o'' x') ->
  o == o' ->
  x == x' ->
  F f o x == F f' o' x'.


Fixpoint TR_acc (o:set) (H:Acc in_set o) (x:set) : set :=
  F (fun o' x' => ZFrepl.uchoice (fun y' => exists h:o' ∈ o, y' == TR_acc o' (Acc_inv H h) x')) o x.

Lemma TR_acc_morph o o' h h' x x' :
  o == o' ->
  x == x' ->
  TR_acc o h x == TR_acc o' h' x'.
revert o' h' x x'; induction h using Acc_indd; destruct h'; simpl; intros.
apply Fext; intros; trivial.
 rewrite isWf_acc; constructor; trivial.
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

Definition TR o x := ZFrepl.uchoice (fun y => exists h:Acc in_set o, y == TR_acc o h x).

Lemma TR_acc_eqn o h x :
  TR_acc o h x == F TR o x.
revert x; induction h using Acc_indd; simpl; intros.
apply Fext; intros; auto with *.
 rewrite isWf_acc; constructor; trivial.
symmetry; apply ZFrepl.uchoice_ext; intros.
 split;[|split]; intros.
  destruct H4.
  rewrite H3 in H4.
  exists x3; trivial.

  exists (TR_acc o' (a o' H0) x1); exists H0; reflexivity.

  destruct H3; destruct H4.
  rewrite H3; rewrite H4; apply TR_acc_morph; auto with *.

 exists H0.
 unfold TR.
 symmetry; apply ZFrepl.uchoice_ext.
  split;[|split]; intros.
   destruct H4.
   rewrite H3 in H4.
   exists x3; trivial.

   assert (Acc in_set o'').
    rewrite <- H1; auto.
   exists (TR_acc o'' H3 x'); exists H3; reflexivity.

   destruct H3; destruct H4.
   rewrite H3; rewrite H4; apply TR_acc_morph; auto with *.

  assert (h'' := H0); rewrite H1 in h''.
  exists (a _ h'').
  apply TR_acc_morph; trivial.
Qed.

Lemma TR_eqn o x :
  isWf o ->
  TR o x == F TR o x.
intros.
rewrite isWf_acc in H.
rewrite <- TR_acc_eqn with (h:=H).
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
 assert (Acc in_set y) by (rewrite <- H; trivial).
 exists H3.
 rewrite <- H1; rewrite H2; apply TR_acc_morph; trivial.

 assert (Acc in_set x) by (rewrite H; trivial).
 exists H3.
 rewrite H1; rewrite H2; symmetry; apply TR_acc_morph; trivial.
Qed.




End TRF.
End F.
*)
