Require Import ZF ZFrepl.

(** Building well-founded recursor using uchoice *)

Section WellFoundedRecursion.

  Variable R : set -> set -> Prop.
  Hypothesis Rm : Proper (eq_set ==> eq_set ==> iff) R.
  
  Variable F : (set -> set) -> set -> set.
  Hypothesis Fm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) F.

  Let F' f x := F (fun y => cond_set (R y x) (f y)) x.

  Local Instance Fm' : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) F'.
do 4 red; intros.   
unfold F'.
apply Fm; trivial.
red; intros.
apply cond_set_morph; auto.
apply Rm; trivial.
Qed.

  Let Fext' x f f' :
    (forall y y', R y x -> y==y' -> f y == f' y') -> F' f x == F' f' x.
unfold F'; intros.
apply Fm; auto with *.
red; intros.
apply cond_set_morph2; auto with *.
apply Rm; auto with *.
Qed.


  Definition WFR_rel o y :=
    forall (P:set->set->Prop),
    Proper (eq_set ==> eq_set ==> iff) P ->
    (forall o' f, morph1 f -> (forall n, R n o' -> P n (f n)) ->
     P o' (F' f o')) ->
    P o y.

  Instance WFR_rel_morph : Proper (eq_set ==> eq_set ==> iff) WFR_rel.
apply morph_impl_iff2; auto with *.
do 4 red; unfold WFR_rel; intros.
rewrite <- H, <-H0; auto.
apply H1; auto.
Qed.

  Lemma WFR_rel_intro x f :
    morph1 f ->
    (forall y, R y x -> WFR_rel y (f y)) ->
    WFR_rel x (F' f x).
red; intros.
apply H2; trivial.
intros.
apply H0; trivial.
Qed.

  Lemma WFR_rel_inv x y :
    WFR_rel x y ->
    exists2 f, morph1 f &
      (forall y, R y x -> WFR_rel y (f y)) /\
      y == F' f x.
intros.
apply (@proj2 (WFR_rel x y)).
apply H; intros.
 do 3 red; intros.
 apply and_iff_morphism.
  apply WFR_rel_morph; auto with *.

  apply ex2_morph'; intros; auto with *.
  apply and_iff_morphism.
   apply fa_morph; intros y2.
   rewrite H0; reflexivity.

   rewrite H0,H1; reflexivity.
assert (WFR_relsub := fun n h => proj1 (H1 n h)); clear H1.
split.
 apply WFR_rel_intro; trivial.

 exists f; auto with *.
Qed.

  (** Particular case of bottom values *)
  Lemma WFR_rel_inv_norec x y f0 :
    WFR_rel x y ->
    (forall f' x', x==x' -> F f0 x == F f' x') ->
    y == F f0 x.
intros r Fext.
generalize (@reflexivity _ eq_set _ x).
pattern x at 1, y.
apply r; intros.
 do 3 red; intros.
 intros; rewrite H,H0; reflexivity.
symmetry; apply Fext; auto with *.
Qed.
(*
  Lemma WFR_rel_inv_bot' x y f0 :
    morph1 f0 ->
    WFR_rel x y ->
    (forall y, ~ R y x) ->
    y == F' f0 x.
intros f0m r bot.
apply WFR_rel_inv_norec with (1:=r).
intros.
assert (
apply Fext'.

generalize (@reflexivity _ eq_set _ x).
pattern x at 1 3, y.
apply r; intros.
 do 3 red; intros.
 intros; rewrite H,H0; reflexivity.
apply Fext'; trivial.
intros.
rewrite H1 in H2.
elim bot with y0; trivial.
Qed.

  Lemma WFR_rel_inv_bot x y :
    WFR_rel x y ->
    (forall y, ~ R y x) ->
    y == F (fun x => empty) x.
intros (*Fm*) r bot.
transitivity (F' (fun _=>empty) x).
 apply WFR_rel_inv_bot'; trivial.
 do 2 red; reflexivity.
unfold F'.
 apply Fm; auto with *.
red; intros.
apply cond_set_mt; trivial.
Qed.
*)
  Lemma WFR_rel_fun :
    forall x y, WFR_rel x y -> forall y', WFR_rel x y' -> y == y'.
intros x y H.
apply H; intros.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 rewrite <- H1; rewrite <- H0 in H3; auto.
apply WFR_rel_inv in H2; destruct H2 as (f',?,(?,?)).
rewrite H4; clear y' H4.
apply Fext'; intros; auto with *.
apply H1; trivial.
rewrite H5 in H4|-*; auto.
Qed.

  Lemma WFR_rel_repl_rel :
    forall x, repl_rel x WFR_rel.
split; intros.
 rewrite <- H0; rewrite <- H1; trivial.

 apply WFR_rel_fun with x0; trivial.
Qed.

  Lemma WFR_rel_def : forall o, Acc R o -> exists y, WFR_rel o y.
intros o ko; generalize ko.
induction ko; intros.
assert (forall z, R z x -> uchoice_pred (fun y => WFR_rel z y)).
 intros.
 destruct H0 with z; eauto.
 split; intros.
  rewrite <- H3; trivial.
 split; intros.
  exists x0; trivial.
 apply WFR_rel_fun with z; trivial.
exists (F' (fun z => uchoice (fun y => WFR_rel z y)) x).
apply WFR_rel_intro; intros; trivial.
 do 2 red; intros.
 apply uchoice_morph_raw; red; intros.
 apply WFR_rel_morph; trivial.
apply uchoice_def; auto.
Qed.

  Lemma WFR_rel_choice_pred : forall o, Acc R o ->
    uchoice_pred (fun y => WFR_rel o y).
split; intros.
 rewrite <- H0; trivial.
split; intros.
apply WFR_rel_def; trivial.
apply WFR_rel_fun with o; trivial.
Qed.

  Definition WFR x := uchoice (fun y => WFR_rel x y).

  Global Instance WFR_morph0 : morph1 WFR.
do 2 red; intros.
unfold WFR.
apply uchoice_morph_raw.
red; intros.
rewrite H; rewrite H0; reflexivity.
Qed.

  (** Particular case of bottom values: needs less assumptions... *)
  Lemma WFR_eqn_norec x :
    (forall y, ~ R y x) ->
    (forall f' x', x==x' -> F (fun _ => empty) x == F f' x') ->
    WFR x == F (fun x => empty) x.
clear Fm.
intros bot Fext.
assert (WFR_rel x (F (fun x => empty) x)).
 red; intros.
 setoid_replace (F (fun _ => empty) x) with (F' (fun x => x) x).
  apply H0; trivial.
   do 2 red; trivial.

   intros.
   elim bot with (1:=H1).
 apply Fext; reflexivity.
assert (u: forall y y', WFR_rel x y -> WFR_rel x y' -> y==y').
 intros.
 transitivity (F (fun x => empty) x).
  apply WFR_rel_inv_norec with (1:=H0); trivial.
  symmetry; apply WFR_rel_inv_norec with (1:=H1); trivial.
symmetry; apply ZFrepl.uchoice_ext; trivial.
split;[|split];trivial; intros.
 revert H1; apply WFR_rel_morph; auto with *.
 econstructor; apply H.
Qed.
(*
  Lemma WFR_eqn_bot o :
    (forall o', ~ R o' o) ->
    WFR o == F (fun x => empty) o.
clear Rm.
intros bot.
assert (WFR_rel o (F (fun x => empty) o)).
 red; intros.
 setoid_replace (F (fun _ => empty) o) with (F' (fun x => x) o).
  apply H0; trivial.
   do 2 red; trivial.

   intros.
   elim bot with (1:=H1).
 apply Fm; auto with *.
 red; intros.
 symmetry; apply cond_set_mt; trivial.
assert (u: forall x x', WFR_rel o x -> WFR_rel o x' -> x==x').
 intros.
 transitivity (F (fun x => empty) o).
  apply WFR_rel_inv_bot with (1:=H0); trivial.
  symmetry; apply WFR_rel_inv_bot with (1:=H1); trivial.
symmetry; apply ZFrepl.uchoice_ext.
 apply WFR_rel_choice_pred; trivial.
 constructor; intros.
 elim bot with y; trivial. 
 trivial.
Qed.
*)
  Lemma WFR_eqn0 o : Acc R o -> WFR o == F' WFR o.
intros.
specialize WFR_rel_choice_pred with (1:=H); intro.
apply uchoice_def in H0.
apply WFR_rel_inv in H0.
destruct H0 as (f,fm,(?,?)).
unfold WFR at 1; rewrite H1.
apply Fext'; intros; auto with *.
apply WFR_rel_fun with y; auto.
rewrite H3.
unfold WFR.
apply uchoice_def.
apply WFR_rel_choice_pred.
apply Acc_inv with o; trivial.
rewrite <- H3; trivial.
Qed.

  Hypothesis Fext : forall x f f', Acc R x ->
    (forall y y', R y x -> y==y' -> f y == f' y') ->
    F f x == F f' x.

  Lemma WFR_eqn o : Acc R o -> WFR o == F WFR o.
intros.
rewrite WFR_eqn0; trivial.
unfold F'; apply Fext; trivial.
intros.
rewrite cond_set_ok; trivial.
apply WFR_morph0; trivial.
Qed.
  
  Lemma WFR_ind : forall x (P:set->set->Prop),
    Proper (eq_set ==> eq_set ==> iff) P ->
    Acc R x ->
    (forall y, Acc R y ->
     (forall x, R x y -> P x (WFR x)) ->
     P y (F WFR y)) ->
    P x (WFR x).
intros x P Pm wfx Hrec.
generalize wfx.
induction wfx; intros.
(*apply Acc_intro in H.*)
rewrite WFR_eqn; trivial.
apply Hrec; auto with *; intros.
Qed.

End WellFoundedRecursion.

Global Instance WFR_morph :
    Proper ((eq_set==>eq_set==>iff)==>((eq_set ==> eq_set) ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) WFR.
do 4 red; intros.
assert (H2 : (eq_set ==> iff)%signature (Acc x) (Acc y)).
 red; intros.
 apply wf_morph with (eqA:=eq_set); auto with *.
apply uchoice_morph_raw.
red; intros.
unfold WFR_rel.
apply fa_morph; intros P.
apply fa_morph; intros Pm.
apply impl_morph.
2:intros; apply Pm; trivial.
apply fa_morph; intros o'.
apply fa_morph; intros f.
apply fa_morph; intros fm.
apply impl_morph.
 apply fa_morph; intros n.
 apply impl_morph; auto with *.
 apply H; auto with *.
intros _.
apply Pm; auto with *.
apply H0; auto with *.
red; intros.
apply cond_set_morph; auto with *.
apply H; auto with *.
Qed.

Global Instance WFR_morph_gen2 R : Proper
  (pointwise_relation _ (pointwise_relation _ eq_set) ==> eq_set ==> eq_set) (WFR R).
intros F F' eqF x y e.
apply uchoice_morph_raw.
red; intros.
unfold WFR_rel. 
apply fa_morph; intros P.
apply fa_morph; intros Pm.
apply impl_morph; auto with *.
2:intros; apply Pm; trivial.
apply fa_morph; intros o'.
apply fa_morph; intros f.
apply fa_morph; intros _.
apply fa_morph; intros _.
apply Pm; auto with *.
apply eqF. 
Qed.


Section WFRK.

  Variable K : set -> Prop.
  Hypothesis Km : Proper (eq_set==>iff) K.
  
  Variable R : set -> set -> Prop.
  Hypothesis Rm : Proper (eq_set ==> eq_set ==> iff) R.

  Hypothesis Kacc : forall x, K x -> Acc R x.
  Hypothesis Ksub : forall x y, R x y -> K y -> K x.
  
  Variable F : (set -> set) -> set -> set.
  Hypothesis Fm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) F.
  Hypothesis Fext : forall x f f', K x ->
    (forall y y', R y x -> y==y' -> f y == f' y') -> F f x == F f' x.


  Definition WFRK := WFR R (fun f x => cond_set (K x) (F f x)).
(*  
  Lemma WFR_eqn_bot o :
    K o ->
    (forall f f' x', o==x' -> F f o == F f' x') ->
    (forall o', ~ R o' o) ->
    WFR o == F (fun x => x) o.
clear Rm Fm Fext Kacc Ksub.
intros Ko Fm bot.
assert (WFR_rel o (F (fun x => x) o)).
 red; intros.
 apply H0; trivial.
  do 2 red; trivial.

  intros.
  elim bot with (1:=H1).
assert (u: forall x x', WFR_rel o x -> WFR_rel o x' -> x==x').
 intros.
 transitivity (F (fun x => x) o).
  apply WFR_rel_inv_bot with (2:=H0); trivial.
  symmetry; apply WFR_rel_inv_bot with (2:=H1); trivial.
symmetry; apply ZFrepl.uchoice_ext.
 split; intros.
  revert H1; apply iff_impl; apply WFR_rel_morph; auto with *.
 split; intros.
  exists (F (fun x => x) o); trivial.
 apply u; trivial.

 trivial.
Qed.
  *)
  Lemma WFRK_eqn : forall o, K o ->
     WFRK o == F WFRK o.
intros.
transitivity (cond_set (K o) (F WFRK o)).
2:apply cond_set_ok; trivial.
unfold WFRK.
apply WFR_eqn; auto.
 do 3 red; intros; apply cond_set_morph; auto with *.
 apply Fm; trivial.
intros.
apply cond_set_morph2; auto with *.
Qed.


  Lemma WFRK_ind : forall x (P:set->set->Prop),
    Proper (eq_set ==> eq_set ==> iff) P ->
    K x ->
    (forall y, K y ->
     (forall x, R x y -> P x (WFRK x)) ->
     P y (F WFRK y)) ->
    P x (WFRK x).
intros x P Pm wfx Hrec.
generalize wfx.
apply Kacc in wfx.
induction wfx; intros.
rewrite WFRK_eqn; trivial.
apply Hrec; auto with *; intros.
apply H0; eauto.
Qed.

End WFRK.

Local Notation E:=eq_set.
Instance WFRK_morph : Proper ((E==>iff)==>(E==>E==>iff)==>((E==>E)==>E==>E)==>E==>E) WFRK.
do 5 red; intros.
apply WFR_morph; trivial.
do 2 red; intros.
apply cond_set_morph; auto.
apply H1; trivial.
Qed.

Lemma WFRK_ext (K K':set->Prop) R R' F F' x x' :
  pointwise_relation _ iff K K' ->
  (eq_set ==> pointwise_relation _ iff)%signature R R' ->
  (forall f f' y y',
   (forall z z', R z y -> z==z' -> f z == f' z') ->
   K y ->
   y == y' ->
   F f y == F' f' y') ->
  K x ->
  K' x' ->
  x == x' ->
  WFRK K R F x == WFRK K' R' F' x'.
intros eqK eqR eqF kx kx' eqx.
apply ZFrepl.uchoice_morph_raw.
red; intros x1 x1' eqx1.
unfold WFR_rel.
apply fa_morph; intro P.
apply fa_morph; intro Pm.
apply impl_morph; intros.
2:apply Pm; auto with *.
apply fa_morph; intro y.
apply fa_morph; intro f.
apply fa_morph; intro fm.
apply impl_morph.
 apply fa_morph; intros z.
 apply impl_morph; auto with *.
 apply eqR; auto with *.
intros.
apply Pm; auto with *.
apply cond_set_morph2.
 apply eqK; auto with *.
intros.
apply eqF; auto with *.
intros.
apply cond_set_morph2; auto.
apply eqR; auto with *.
Qed.
