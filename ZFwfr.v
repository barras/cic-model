Require Import ZF ZFrepl.


  Definition star_rel R :=
    clos_trans _ (fun x y => x==y \/ R x y).
  
  Lemma star_refl R0 x y : x==y -> star_rel R0 x y.
unfold star_rel; auto.
Qed.
  Lemma star_step (R0:set->set->Prop) x y : R0 x y -> star_rel R0 x y.
unfold star_rel; auto.
Qed.
    Lemma star_trans R0 x y z : star_rel R0 x y -> star_rel R0 y z -> star_rel R0 x z.
intros; apply t_trans with y; trivial.
Qed.      
Hint Resolve star_refl star_step.


  Lemma star_rel_gen_mono :
    Proper (pointwise_relation _ (pointwise_relation _ impl)==>eq_set==>eq_set==>impl) star_rel.
do 5 red; intros.
apply star_trans with x0; auto with *.
apply star_trans with x1; auto with *.
elim H2; intros.
 destruct H3; auto with *.
 apply star_step; apply H; trivial.

 apply star_trans with y2; trivial.
Qed.

  Lemma star_rel_gen_morph :
    Proper (pointwise_relation _ (pointwise_relation _ iff)==>eq_set==>eq_set==>iff) star_rel.
apply morph_impl_iff3; auto with *.
do 2 red; intros.
apply star_rel_gen_mono; trivial.
intros x' y' xry.
apply H; trivial.
Qed.

  Lemma star_rel_morph : Proper ((eq_set==>eq_set==>iff)==>eq_set==>eq_set==>iff) star_rel.
do 2 red; intros; apply star_rel_gen_morph.
intros x' y'.
apply H; reflexivity.
Qed.

  Instance star_rel_morph0 R :
    Proper (eq_set==>eq_set==>iff) (star_rel R). 
apply star_rel_gen_morph.
reflexivity.
Qed.

  Lemma star_Acc R x y : Proper (eq_set==>eq_set==>iff) R -> star_rel R x y -> Acc R y -> Acc R x.
intros Rm; induction 1; auto.  
destruct H; auto.
 rewrite H; trivial.

 intros; apply Acc_inv with y; trivial.
Qed.

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


  Definition WFR_rel x y :=
    forall (P:set->set->Prop),
    Proper (eq_set ==> eq_set ==> iff) P ->
    (forall x' f, morph1 f -> star_rel R x' x ->
     (forall z, R z x' -> P z (f z)) ->
     P x' (F' f x')) ->
    P x y.

  Instance WFR_rel_morph : Proper (eq_set ==> eq_set ==> iff) WFR_rel.
apply morph_impl_iff2; auto with *.
do 4 red; unfold WFR_rel; intros.
rewrite <- H, <-H0; auto.
apply H1; auto.
intros; apply H3; trivial.
rewrite <- H; trivial.
Qed.

  Lemma WFR_rel_intro x f :
    morph1 f ->
    (forall y, R y x -> WFR_rel y (f y)) ->
    WFR_rel x (F' f x).
red; intros.
apply H2; auto with *.
intros.
apply H0; trivial.
intros; apply H2; trivial.
apply star_trans with z; auto.
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
assert (WFR_relsub := fun n h => proj1 (H2 n h)); clear H1.
split.
 apply WFR_rel_intro; trivial.

 exists f; auto with *.
Qed.

  (** Particular case of bottom values (do not rely on Fm) *)
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
apply WFR_rel_inv in H3; destruct H3 as (f',fm',(?,?)).
rewrite H4; clear y' H4.
apply Fext'; intros; auto with *.
apply H2; trivial.
rewrite H5 in H4|-*; auto.
Qed.

  Lemma WFR_rel_repl_rel :
    forall x, repl_rel x WFR_rel.
split; intros.
 rewrite <- H0; rewrite <- H1; trivial.

 apply WFR_rel_fun with x0; trivial.
Qed.

  Lemma WFR_rel_def x: Acc R x -> exists y, WFR_rel x y.
intros kx; generalize kx.
induction kx; intros.
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
clear Rm Fm.
intros bot Fext.
assert (WFR_rel x (F (fun x => empty) x)).
 red; intros.
 setoid_replace (F (fun _ => empty) x) with (F' (fun x => x) x).
  apply H0; auto with *.
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
  Lemma WFR_eqn0 x : Acc R x -> WFR x == F' WFR x.
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
apply Acc_inv with x; trivial.
rewrite <- H3; trivial.
Qed.

  Lemma WFR_eqn_gen x :
    (forall f f',
     (forall y y', R y x -> y==y' -> f y == f' y') ->
     F f x == F f' x) ->
    Acc R x -> WFR x == F WFR x.
intros Fext wfx.
rewrite WFR_eqn0; trivial.
unfold F'; apply Fext; trivial.
intros.
rewrite cond_set_ok; trivial.
apply WFR_morph0; trivial.
Qed.



  Lemma WFR_ind_gen : forall x (P:set->set->Prop),
    (forall y f f', star_rel R y x ->
     (forall z z', R z y -> z==z' -> f z == f' z') ->
     F f y == F f' y) ->
    Proper (eq_set ==> eq_set ==> iff) P ->
    Acc R x ->
    (forall y, star_rel R y x ->
     (forall x, R x y -> P x (WFR x)) ->
     P y (F WFR y)) ->
    P x (WFR x).
intros x P Fextx Pm wfx Hrec.
generalize wfx.
induction wfx; intros.
rewrite WFR_eqn_gen; trivial.
 apply Hrec; auto with *; intros.
 apply H0; auto with *.
  intros.
  apply Fextx; trivial.
  apply star_trans with x0; auto with *.

  intros.
  apply Hrec; auto.
  apply star_trans with x0; auto with *.

 intros.
 apply Fextx; auto with *.
Qed.

  Hypothesis Fext : forall x f f', Acc R x ->
    (forall y y', R y x -> y==y' -> f y == f' y') ->
    F f x == F f' x.
  
  Lemma WFR_eqn x :
    Acc R x -> WFR x == F WFR x.
intros wfx.
rewrite WFR_eqn0; trivial.
unfold F'; apply Fext; trivial.
intros.
rewrite cond_set_ok; trivial.
apply WFR_morph0; trivial.
Qed.
  
  Lemma WFR_ind : forall x (P:set->set->Prop),
    Proper (eq_set ==> eq_set ==> iff) P ->
    Acc R x ->
    (forall y, star_rel R y x ->
     (forall x, R x y -> P x (WFR x)) ->
     P y (F WFR y)) ->
    P x (WFR x).
intros x P Pm wfx.
apply WFR_ind_gen; auto.
intros.
apply Fext; trivial.
apply star_Acc with x; trivial.
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
apply fa_morph; intros x'.
apply fa_morph; intros f.
apply fa_morph; intros fm.
apply impl_morph.
 apply star_rel_morph; auto with *.
intros _.
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
apply fa_morph; intros x'.
apply fa_morph; intros f.
apply fa_morph; intros _.
apply impl_morph; intros.
 rewrite e; reflexivity.
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

  Lemma Kstar_rel x y : star_rel R x y -> K y -> K x.
induction 1; auto.  
destruct H; eauto.
rewrite H; trivial.
Qed.

Notation WFRK := WFR.
(*  Definition WFRK0 x0 := WFR R (fun f x => cond_set (star_rel R x x0) (F f x)).

    Lemma WFRK0_eqn x0 x :
     (forall y f f',
     star_rel R y x0 ->
     (forall z z', R z y -> z==z' -> f z == f' z') -> F f y == F f' y) ->
      Acc R x ->
      WFRK0 x0 x == cond_set (star_rel R x x0) (F (WFRK0 x0) x).
intros Fext'.
apply WFR_eqn; auto.
 do 3 red; intros.
 apply cond_set_morph; auto.
  rewrite H0; reflexivity.
 apply Fm; auto with *.

 intros.
 apply cond_set_morph2; auto with *.
Qed.

Lemma WFRK0_irrel x0 x1 x:
  (forall y f f',
     star_rel R y x0 \/ star_rel R y x1 ->
     (forall z z', R z y -> z==z' -> f z == f' z') -> F f y == F f' y) ->
  Acc R x ->
  star_rel R x x0 ->
  star_rel R x x1 ->
  WFRK0 x0 x == WFRK0 x1 x.
intros Fext'.
induction 1; intros.
rewrite WFRK0_eqn; auto. 2:constructor; trivial.
rewrite WFRK0_eqn; auto. 2:constructor; trivial.
rewrite cond_set_ok; auto.
rewrite cond_set_ok; auto.
apply Fext'; auto.
intros.
transitivity (WFRK0 x1 z).
2:apply WFR_morph0; trivial.
apply H0; trivial.
 apply star_trans with x; auto.
 apply star_trans with x; auto.
Qed.
    
    Definition WFRK x := WFRK0 x x.

    Lemma WFRK_eqn x :
  K x ->
  WFRK x == F WFRK x.
intros ko.
unfold WFRK.
rewrite WFRK0_eqn; auto.
rewrite cond_set_ok; auto.
apply Fext; trivial.
intros.
transitivity (WFRK0 y' y).
2:apply WFR_morph0; trivial.
apply WFRK0_irrel; auto.
 intros.
 apply Fext; auto.
 apply Kstar_rel with x; trivial.
 destruct H1; trivial.
 apply star_trans with y'; trivial.
 rewrite <- H0; auto.

 apply Acc_inv with x; auto.

 auto with *.

 intros.
 apply Fext; auto.
 apply Kstar_rel with x; auto.
Qed.

End WFRK.


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
(*  Lemma WFRK_eqn : forall o, K o ->
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
*)
*)
  Lemma WFRK_ind : forall x (P:set->set->Prop),
    Proper (eq_set ==> eq_set ==> iff) P ->
    K x ->
    (forall y, K y ->
     (forall x, R x y -> P x (WFR R F x)) ->
     P y (F (WFR R F) y)) ->
    P x (WFR R F x).
intros x P Pm kx Hrec.
generalize kx.
apply WFR_ind_gen with (x:=x); auto with *.
 intros.
 apply Fext; trivial.
 apply Kstar_rel with x; trivial.

 do 3 red; intros.
 rewrite H,H0; reflexivity.

 intros.
 apply Hrec; trivial.
 intros.
 apply H0; trivial.
 apply Ksub with y; trivial.
Qed.

End WFRK.

Local Notation E:=eq_set (only parsing).
(*Instance WFRK_morph : Proper ((E==>iff)==>(E==>E==>iff)==>((E==>E)==>E==>E)==>E==>E) WFRK.
do 5 red; intros.
apply WFR_morph; trivial.
do 2 red; intros.
apply cond_set_morph; auto.
apply H1; trivial.
Qed.

Global Instance WFRK_morph_gen2 K R : Proper
  (pointwise_relation _ (pointwise_relation _ E) ==> E ==> E) (WFRK K R).
intros F F' eqF x y e.
apply WFR_morph_gen2; trivial.
red; red; intros.
apply cond_set_morph; auto with *.
apply eqF.
Qed.
*)

  Lemma WFR_ext R R' F F' x x' :
  (eq_set==>pointwise_relation _ iff)%signature R R' ->
  (forall f f' y,
   morph1 f ->
   morph1 f' ->
   (forall z, R z y -> f z == f' z) -> star_rel R y x ->
   F f y == F' f' y) ->
  x == x' ->
  WFR R F x == WFR R' F' x'.
intros eqR eqF eqx.
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
apply impl_morph; intros.
 apply star_rel_gen_morph; auto with *.
 intros a b; apply eqR; reflexivity.
apply impl_morph; intros.
 apply fa_morph; intros z.
 apply impl_morph; auto with *.
 apply eqR; auto with *.
apply Pm; auto with *.
apply eqF; auto with *.
 do 2 red; intros.
 apply cond_set_morph; auto.
 transitivity (R' x0 y);[|symmetry]; apply eqR; auto with *.

 do 2 red; intros.
 apply cond_set_morph; auto.
 transitivity (R x0 y);[symmetry|]; apply eqR; auto with *.
intros.
apply cond_set_morph2; auto.
 apply eqR; reflexivity.
 reflexivity.
Qed.
(*  
    Lemma WFRK_ext (K:set->Prop) R R' F F' x x' :
  (pointwise_relation _ (pointwise_relation _ iff))%signature R R' ->
  (forall f f' y,
   (forall z, R z y -> f z == f' z) ->
   K y ->
   F f y == F' f' y) ->
  K x ->
  x == x' ->
  WFR R F x == WFR R' F' x'.
intros eqR eqF kx eqx.
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
apply impl_morph; intros.
 apply star_rel_gen_morph; auto with *.
apply impl_morph; intros.
 apply fa_morph; intros z.
 apply impl_morph; auto with *.
 apply eqR; auto with *.
apply Pm; auto with *.
apply eqF; auto with *.
intros.
apply cond_set_morph2; auto.
apply eqR; auto with *.
Qed.
*)
