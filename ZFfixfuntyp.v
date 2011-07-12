Require Import ZF.
Require Import ZFrelations.
Import IZF.

Require Import ZFord.
Require Import ZFnats.

(* Specialized version where the case of limit ordinals is union
   and the stage ordinal is fed to the step function.  *)
Section TransfiniteIteration.

  (* (F o x) produces value for stage o+1 given x the value for stage o *)
  Variable F : set -> set -> set.
  Hypothesis Fmorph : forall o o' x x',
    o == o' -> x == x' -> F o x == F o' x'.
(*  Hypothesis Fmorph : Proper (eq_set ==> eq_set ==> eq_set) F.*)

Let G f o := sup o (fun o' => F o' (f o')).

Lemma Gmorph : forall o o' f f',
    o == o' -> eq_fun o f f' -> G f o == G f' o'.
unfold G; intros.
apply sup_morph; trivial.
red; intros.
apply Fmorph; auto.
Qed.
Hint Resolve Gmorph.

  Definition TIO := TR G.

  Instance TIO_morph : morph1 TIO.
unfold TIO; do 2 red; intros.
apply TR_morph; auto with *.
Qed.

  Lemma TIO_fun_ext : forall x, isOrd x -> ext_fun x (fun y => F y (TIO y)).
do 2 red; intros.
apply Fmorph; trivial.
apply TIO_morph; trivial.
Qed.
Hint Resolve TIO_fun_ext.

  Lemma TIO_eq : forall o,
    isOrd o ->
    TIO o == sup o (fun o' => F o' (TIO o')).
intros.
unfold TIO.
apply TR_eqn; auto.
Qed.

  Lemma TIO_intro : forall o o' x,
    isOrd o ->
    lt o' o ->
    x \in F o' (TIO o') ->
    x \in TIO o.
intros.
rewrite TIO_eq; trivial.
rewrite sup_ax; auto.
exists o'; trivial.
Qed.

  Lemma TIO_elim : forall o x,
    isOrd o ->
    x \in TIO o ->
    exists2 o', lt o' o & x \in F o' (TIO o').
intros.
rewrite TIO_eq in H0; trivial.
rewrite sup_ax in H0; auto.
Qed.

  Lemma TIO_initial : TIO zero == empty.
apply empty_ext; red; intros.
apply TIO_elim in H.
 destruct H.
 elim empty_ax with (1:=H).

 apply isOrd_zero.
Qed.

  Lemma TIO_typ : forall n X,
    isOrd n ->
    (forall o a, lt o n -> a \in X o -> F o a \in X (osucc o)) ->
    (forall m G, isOrd m -> m \incl n ->
     ext_fun m G ->
     (forall x, lt x m -> G x \in X (osucc x)) -> sup m G \in X m) ->
    TIO n \in X n.
induction 1 using isOrd_ind; intros.
rewrite TIO_eq; trivial.
apply H3 with (G:=fun o => F o (TIO o)); intros; auto with *.
apply H2; trivial.
apply H1; intros; trivial.
 apply H2; trivial.
 apply isOrd_trans with x; trivial.

 apply H3; trivial.
 rewrite H6.
 red; intros.
 apply isOrd_trans with x; trivial.
Qed.

End TransfiniteIteration.
Hint Resolve TIO_fun_ext.

Section IterMonotone.

  Variable F : set -> set -> set.
  Hypothesis Fmorph : forall o o' x x',
    o == o' -> x == x' -> F o x == F o' x'.
(*  Variable Fmorph : morph2 F.*)
  Variable Fmono : forall o o', isOrd o -> isOrd o' -> o \incl o' ->
    TIO F o \incl TIO F o' -> F o (TIO F o) \incl F o' (TIO F o').

  Lemma TIO_mono : increasing (TIO F).
do 2 red; intros.
apply TIO_elim in H2; intros; auto with *.
destruct H2.
apply TIO_intro with x0; auto with *.
apply H1 in H2; trivial.
Qed.

  Lemma TIO_incl : forall o, isOrd o ->
    forall o', lt o' o ->
    TIO F o' \incl TIO F o.
intros.
apply TIO_mono; trivial; auto.
 apply isOrd_inv with o; trivial.
 red; intros; apply isOrd_trans with o'; trivial.
Qed.


  Lemma TIO_mono_succ : forall o,
    isOrd o ->
    TIO F (osucc o) == F o (TIO F o).
intros.
apply eq_intro; intros.
 apply TIO_elim in H0; auto.
 destruct H0.
 assert (isOrd x).
  apply isOrd_inv with (osucc o); auto.
 revert H1; apply Fmono; auto.
  apply olts_le; auto.

  apply TIO_mono; auto.
  apply olts_le; auto.

 apply TIO_intro with o; auto.
Qed.

  Lemma TIO_mono_eq : forall o,
    isOrd o -> 
    TIO F o == sup o (fun x => TIO F (osucc x)).
intros.
rewrite TIO_eq; auto.
apply sup_morph; auto with *.
red; intros.
rewrite <- TIO_mono_succ.
 apply TIO_morph; auto.
 rewrite H1; reflexivity.

 apply isOrd_inv with o; trivial.
Qed.


(*
  Lemma TIO_pre_fix : forall fx o,
     isOrd o ->
     F o fx \incl fx ->
     TIO F o \incl fx.
*)

End IterMonotone.

Existing Instance TIO_morph.
