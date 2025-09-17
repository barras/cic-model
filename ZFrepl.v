
Require Import ZF.

Section GeneralizedRepl.

  (* We show that repl_ax allows to derive a new replacement Repl that
     is fully specified (i.e. not assuming properties on the relation),
     and that staisfies both repl_ax and repl_mono.
  *)
  
  Definition Repl a R :=
    repl (subset a (fun x => (forall x' y y', x==x' -> y==y' -> R x y <-> R x' y') /\
                             (forall y y', R x y -> R x y' -> y==y'))) R.

  Lemma Repl_ax a (R:set->set->Prop) z :
    z ∈ Repl a R <-> exists2 y, y ∈ a &
                                forall y' z', y==y' -> (R y' z' <-> z==z').
unfold Repl; rewrite repl_ax.
*split; intros.
 +destruct H as (y,tyy,?).
  rewrite subset_ax in tyy.
  destruct tyy as (?,(y',?,(?,?))).  
  exists y; trivial.
  intros.
  split; intros.
  ++apply H3.
     rewrite H2 with (x':=y) (y':=z); auto with *.
     rewrite H2 with (x':=y'0) (y':=z'); auto with *.
     rewrite <-H1; trivial.
  ++rewrite <- H2 with (y:=z');[|rewrite <-H1; trivial|reflexivity].
    rewrite H2 with (x':=y)(y':=z); auto with *.
 +destruct H as (y,?,?); exists y.
  ++apply subset_intro; trivial.
    split; intros.
    rewrite H0; auto with *.
    rewrite H0; auto with *.
    rewrite H2; reflexivity.
    rewrite H0 in H1; auto with *.
    rewrite H0 in H2; auto with *.
    rewrite <-H1; trivial.
  ++apply H0; reflexivity.
*intros.
 rewrite subset_ax in H.
 destruct H as (?,(x'',?,(?,?))).  
 rewrite <- H4 with (y:=y); auto with *.
 2:rewrite <- H3; trivial.
 rewrite H4 with (x':=x)(y':=y); auto with *.
*intros.
 rewrite subset_ax in H.
 destruct H as (?,(x',?,(?,?))).  
 apply H4.
  rewrite H3 with (x':=x)(y':=y); auto with *.
  rewrite H3 with (x':=x)(y':=y'); auto with *.
Qed.

  Opaque Repl.  

    Lemma Repl_repl_ax a (R : set -> set -> Prop) :
    (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x ∈ a -> R x y -> R x y' -> y == y') ->
    forall x, x ∈ Repl a R <-> (exists2 y, y ∈ a & R y x).
intros.
rewrite Repl_ax.
apply ex2_morph'; [reflexivity|].
intros z tyz.
split; intros.
*rewrite H1; reflexivity.
*split; intros.
 +apply H0 with z; trivial.
  apply H with y' z'; auto with *.
  rewrite <- H2; trivial.
 +apply H with z x; trivial.
Qed.

  Lemma Repl_repl_mono a a' (R R' : set -> set -> Prop) :
    (forall z, z ∈ a -> z ∈ a') ->
    (forall x x', x == x' -> forall y y', y == y' -> R x y <-> R' x' y') ->
    forall z, z ∈ Repl a R -> z ∈ Repl a' R'.
intros.
rewrite Repl_ax in *.
destruct H1 as (y,?,?); exists y; auto.
intros.
rewrite <- H0 with (x:=y')(y:=z'); auto with *.
Qed.

  
End GeneralizedRepl.
  
Instance repl_mono_raw :
  Proper (incl_set ==> (eq_set ==> eq_set ==> iff) ==> incl_set) repl.
Proof repl_mono.

Instance repl_morph_raw :
  Proper (eq_set ==> (eq_set ==> eq_set ==> iff) ==> eq_set) repl.
do 3 red; intros.
apply eq_intro.
 apply repl_mono; auto; intros.
 rewrite <- H; trivial.

 symmetry in H0.
 apply repl_mono; auto; intros.
 rewrite H; trivial.
Qed.

Definition repl_rel a (R:set->set->Prop) :=
  (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') /\
  (forall x y y', x ∈ a -> R x y -> R x y' -> y == y').

Lemma repl_intro : forall a R y x,
  repl_rel a R -> y ∈ a -> R y x -> x ∈ repl a R.
Proof.
intros a R y x (Rm,Rfun) H1 H2.
elim repl_ax with (1:=Rm) (2:=Rfun) (a := a) (x := x); intros.
apply H0.
exists y; trivial.
Qed.

Lemma repl_elim : forall a R x,
  repl_rel a R -> x ∈ repl a R -> exists2 y, y ∈ a & R y x.
Proof.
intros a R x (Rm,Rfun) H1.
elim repl_ax with (1:=Rm) (2:=Rfun) (a:=a) (x:=x); intros.
apply H in H1; clear H H0.
destruct H1.
exists x0; trivial.
Qed.

Lemma repl_ext : forall p a R,
  repl_rel a R ->
  (forall x y, x ∈ a -> R x y -> y ∈ p) ->
  (forall y, y ∈ p -> exists2 x, x ∈ a & R x y) ->
  p == repl a R.
Proof.
intros; apply eq_intro; intros.
 elim H1 with (1:=H2); intros.
 apply repl_intro with x; trivial.

 elim repl_elim with (1:=H) (2:=H2); intros; eauto.
Qed.

Lemma repl_mono2 : forall x y R,
  repl_rel y R ->
  x ⊆ y ->
  repl x R ⊆ repl y R.
red; intros.
assert (repl_rel x R).
 destruct H; split; intros; eauto.
apply repl_elim in H1; trivial.
destruct H1.
apply repl_intro with x0; auto.
Qed.


Lemma repl_empty : forall R, repl empty R == empty.
Proof.
intros.
apply empty_ext.
red; intros.
elim repl_elim with (2:=H); intros.
 elim empty_ax with x0; trivial.

 split; intros.
  elim empty_ax with x0; trivial.
  elim empty_ax with x0; trivial.
Qed.

(* Relation between replf and repl *)
Lemma repl_rel_fun : forall x f,
  ext_fun x f -> repl_rel x (fun a b => b == f a).
split; intros.
 rewrite <- H2; rewrite H3; auto.
 rewrite H1; rewrite H2; reflexivity.
Qed.

Lemma replf_def a F :
  ext_fun a F ->
  replf a F == repl a (fun x y => y == F x).
intros Fext.
apply eq_set_ax; intros z.
rewrite replf_ax; trivial.
rewrite repl_ax.
*reflexivity.
*apply repl_rel_fun; trivial.
*apply repl_rel_fun; trivial.
Qed.

Lemma repl_rel_fun_raw : forall x f,
  repl_rel x (fun a b => forall a', a==a' -> b == f a').
split; intros.
*rewrite <- H0 in H3.
 rewrite <- H1; auto.
*rewrite H0 with (a':=x0); [|reflexivity].
 rewrite H1 with (a':=x0); [|reflexivity].
 reflexivity.
Qed.

Lemma replf_def_raw a F :
  replf a F == repl a (fun x y => forall x', x==x' -> y == F x').
apply eq_set_ax; intros z.
rewrite replf_ax_raw.
rewrite repl_ax.
*reflexivity.
*apply repl_rel_fun_raw; trivial.
*apply repl_rel_fun_raw; trivial.
Qed.

(* unique choice *)
Definition uchoice (P : set -> Prop) : set :=
  union (repl (singl empty) (fun _ => P)).

Instance uchoice_morph_raw : Proper ((eq_set ==> iff) ==> eq_set) uchoice.
do 2 red; intros.
unfold uchoice.
apply union_morph.
apply repl_morph_raw; auto with *.
red; auto.
Qed.

Definition uchoice_pred (P:set->Prop) :=
  (forall x x', x == x' -> P x -> P x') /\
  (exists x, P x) /\
  (forall x x', P x -> P x' -> x == x').

Instance uchoice_pred_morph : Proper ((eq_set ==> iff) ==> iff) uchoice_pred.
apply morph_impl_iff1; auto with *.
do 3 red; intros.
destruct H0 as (?,(?,?)); split;[|split]; intros.
 assert (x x0).
  revert H4; apply H; auto with *.
 revert H5; apply H; trivial.

 destruct H1; exists x0.
 revert H1; apply H; auto with *.

 apply H2; [revert H3|revert H4]; apply H; auto with *.
Qed.


Lemma uchoice_ext : forall P x, uchoice_pred P -> P x -> x == uchoice P.
intros.
assert (repl_rel (singl empty) (fun _ => P)).
 destruct H.
 destruct H1.
 split; eauto.
unfold uchoice.
apply union_ext; intros.
 elim repl_elim with (2:=H3); clear H3; trivial; intros.
 rewrite (proj2 (proj2 H) _ _ H0 H4); trivial.

 exists x; trivial.
 apply repl_intro with empty; trivial.
 apply singl_intro.
Qed.

Lemma uchoice_def : forall P, uchoice_pred P -> P (uchoice P).
intros.
elim (proj1 (proj2 H)); intros.
apply (proj1 H x); trivial.
apply uchoice_ext; trivial.
Qed.

Lemma uchoice_morph : forall P P',
  uchoice_pred P ->
  (forall x, P x <-> P' x) ->
  uchoice P == uchoice P'.
intros.
elim (proj1 (proj2 H)); intros.
assert (P' x).
 elim (H0 x); auto.
assert (uchoice_pred P').
 destruct H.
 split; intros.
  apply (proj1 (H0 x')).
  apply H with x0; trivial.
  apply (proj2 (H0 x0)); auto.

  destruct H3.
  split; intros.
   destruct H3.
   exists x; trivial.

   apply H4.
    apply (proj2 (H0 x0)); trivial.
    apply (proj2 (H0 x')); trivial.
rewrite <- (uchoice_ext _ _ H H1).
apply uchoice_ext; trivial.
Qed.

Lemma uchoice_ax : forall P x,
  uchoice_pred P ->
  (x ∈ uchoice P <-> exists2 z, P z & x ∈ z).
intros.
specialize (uchoice_def _ H); intro.
split; intros.
 exists (uchoice P); trivial.

 destruct H1.
 destruct H.
 destruct H3.
 rewrite (H4 _ _ H0 H1); trivial.
Qed.


(* Relations between repl and uchoice *)
(*Lemma repl_rel_uchoice_pred A R :
  (forall x, x ∈ A -> uchoice_pred (R x)) ->
  repl_rel A R.
split; intros.
 destruct (H _ H0) as (?,_); eauto with *.

 destruct H as (?,?).
 split; [|split]; intros.
  destruct H; eauto with *.

  exists 
*)

(*
Lemma repl_is_choice A R :
  repl_rel A R ->
  repl A R == replf A (fun x => uchoice (R x)).
intros.
assert (ext_fun A (fun x => uchoice (R x))).
 destruct H as (?,_).
 do 2 red; intros.
 apply uchoice_morph_raw.
 red; intros.
 split; intros.
  apply H with x x0; auto with *.
  
  apply H with x' y; auto with *.
  rewrite <- H1; trivial.
apply eq_intro; intros.
 apply repl_elim in H1; trivial; destruct H1.
 rewrite replf_ax; trivial.
 exists x; trivial.
 apply uchoice_ext; trivial.
 destruct H as (?,?).
 split; [|split]; intros; eauto.
 apply H with x x0; auto with *.

 rewrite replf_ax in H1; trivial.
 destruct H1.
 rewrite H2; clear z H2.
 apply repl_intro with x; trivial.
 apply uchoice_def.
*)

(** Building well-founded recursor using uchoice *)
Section PolymorphicWellFoundedRecursion.
  Context {A : Type} (Aeq : relation A) {Aeqv : Equivalence Aeq}.

Section WellFoundedRecursion.

  Variable Rsub : set -> set.
  Hypothesis Rsubm : Proper (eq_set==>eq_set) Rsub.
  Let R x y := x ∈ Rsub y.

  Local Instance Rm : Proper (eq_set==>eq_set==>iff) R.
do 3 red; intros.
unfold R; rewrite H,H0; reflexivity.
Qed.

  Definition WFRle := clos_trans _ (fun x y => x==y \/ R x y).

  Instance WFRle_refl : Reflexive WFRle.
red; intros; apply t_step; auto with *.
Qed.
  
  Local Instance WFRlem : Proper (eq_set==>eq_set==>iff) WFRle.
apply morph_impl_iff2; auto with *.
do 4 red; intros.
revert y y0 H H0; induction H1; intros.
*apply t_step.
 unfold R; rewrite <-H0, <-H1; trivial.
*apply t_trans with y.
 apply IHclos_trans1; auto with *.
 apply IHclos_trans2; auto with *.
Qed.

  Variable F : (set -> A -> set) -> set -> A -> set.

  Variable xx : set.
  
  Hypothesis Fext : forall x x' a a' f f',
    WFRle x xx ->
    (forall y y' a a', R y x -> y==y' -> Aeq a a' -> f y a == f' y' a') ->
    x==x' ->
    Aeq a a' ->
    F f x a == F f' x' a'.

  Definition F' f x a := F (fun y a => cond_set (R y x) (f y a)) x a.

  Lemma Fext' x x' a a' f f' :
    WFRle x xx ->
    (forall y y' a a', R y x -> y==y' -> Aeq a a' -> f y a == f' y' a') ->
    x==x' ->
    Aeq a a' ->
    F' f x a == F' f' x' a'.
unfold F'; intros.
apply Fext; trivial.
intros.
apply cond_set_morph2; intros; auto.
apply Rm; auto with *.
Qed.

  Definition WFR_rel x a y :=
    forall (P:set->A->set->Prop),
    Proper (eq_set ==> Aeq ==> eq_set ==> iff) P ->
    (forall x' a' f, Proper (eq_set==>Aeq==>eq_set) f ->
     (forall x'' a'', R x'' x' -> P x'' a'' (f x'' a'')) ->
     P x' a' (F' f x' a')) ->
    P x a y.

  Instance WFR_rel_morph :
      Proper (eq_set ==> Aeq ==> eq_set ==> iff) WFR_rel.
do 4 red; intros.
unfold WFR_rel.
apply fa_morph; intros P.
apply fa_morph; intros Pm.
apply fa_morph; intros _.
apply Pm; trivial.
Qed.

  Lemma WFR_rel_intro x a f :
    Proper (eq_set==>Aeq==>eq_set) f ->
    (forall y a, R y x -> WFR_rel y a (f y a)) ->
    WFR_rel x a (F' f x a).
red; intros fm Hsub P Pm Hrec.
apply Hrec; auto with *.
intros.
apply Hsub; trivial.
Qed.

  Lemma WFR_rel_inv x a y (r:WFRle x xx):
    WFR_rel x a y ->
    exists2 f, Proper (eq_set==>Aeq==>eq_set) f &
      (forall y a, R y x -> WFR_rel y a (f y a)) /\
      y == F' f x a.
intros.
apply (@proj2 (WFR_rel x a y)).
revert r.
apply H; intros.
*do 4 red; intros.
 apply impl_morph; [rewrite H0; reflexivity|intros lex].
 apply and_iff_morphisml; [apply WFR_rel_morph; auto with *|].
 intros w _.
 apply ex2_morph'; intros f; [auto with *|intros fm].
 apply and_iff_morphism.
  apply fa_morph; intros y3.
  apply fa_morph; intros a'.
  rewrite H0; reflexivity.

  apply eq_set_morph; trivial.
  apply Fext'; [trivial| |trivial|trivial].
  intros; apply fm; trivial.
*assert (WFR_relsub := fun x a h =>
                         proj1 (H1 x a h (t_trans _ _ _ _ _ (t_step _ _ _ _ (or_intror _ h)) r))); clear H1.
 split.
  apply WFR_rel_intro; intros; auto.
  exists f; auto with *.
Qed.
  
  Lemma WFR_rel_fun x a y (r:WFRle x xx) : WFR_rel x a y -> forall y', WFR_rel x a y' -> y == y'.
intros H.
revert r; apply H; intros.
 do 4 red; intros.
 apply impl_morph; [rewrite H0;reflexivity|intros].
 apply fa_morph; intros y'.
 rewrite H0,H1,H2; reflexivity.
apply WFR_rel_inv in H2; [destruct H2 as (f',fm',(?,?))|trivial].
rewrite H3; clear y' H3.
apply Fext'; intros; auto with *.
apply H1; trivial.
 apply t_trans with x'; auto with *.
rewrite H4 in H3|-*; rewrite H5; auto with *.
Qed.

  Lemma WFR_rel_def x a (r:WFRle x xx): Acc R x -> exists y, WFR_rel x a y.
intros kx; revert r a; generalize kx.
induction kx; intros.
assert (forall x' a', R x' x -> uchoice_pred (fun y => WFR_rel x' a' y)).
{intros.
 destruct H0 with x' a';[ trivial|eauto using Acc_inv|apply t_trans with x; auto|].
 split; intros.
  rewrite <- H3; trivial.
 split; intros.
  exists x0; trivial.
  apply WFR_rel_fun with x' a'; trivial.
  apply t_trans with x; auto. }
exists (F' (fun x' a' => uchoice (fun y => WFR_rel x' a' y)) x a).
apply WFR_rel_intro; intros; trivial.
 do 3 red; intros.
 apply uchoice_morph_raw; red; intros.
 apply WFR_rel_morph; trivial.
apply uchoice_def; auto.
Qed.

  Lemma WFR_rel_choice_pred x a (r:WFRle x xx) : Acc R x ->
    uchoice_pred (fun y => WFR_rel x a y).
split; intros.
 rewrite <- H0; trivial.
split; intros.
apply WFR_rel_def; trivial.
apply WFR_rel_fun with x a; trivial.
Qed.

  Definition WFR x a :=
    cond_set (Acc R x) (uchoice (fun y => WFR_rel x a y)).

  (* TODO avoid relying on this: *)
  Global Instance WFR_morph0 : Proper (eq_set ==> Aeq ==> eq_set) WFR.
do 3 red; intros.
unfold WFR.
apply cond_set_morph.
*split; destruct 1; constructor; intros.
 rewrite <- H in H2; auto.
 rewrite H in H2; auto.
*apply uchoice_morph_raw.
 red; intros.
 apply WFR_rel_morph; trivial.
Qed.

  Lemma WFR_eqn' x a (r:WFRle x xx) :
    Acc R x -> WFR x a == F' WFR x a.
intros.
specialize WFR_rel_choice_pred with (1:=r)(2:=H)(a:=a); intro.
apply uchoice_def in H0.
apply WFR_rel_inv in H0; trivial.
destruct H0 as (f,fm,(?,ch)).
unfold WFR at 1; rewrite cond_set_ok, ch; [|trivial].
apply Fext'; intros; auto with *.
eapply WFR_rel_fun with y a0; auto.
 apply t_trans with x; auto.
rewrite H2.
unfold WFR.
rewrite cond_set_ok;
  [|rewrite H2 in H1; apply Acc_inv with x; trivial].
rewrite H3.
apply uchoice_def.
apply WFR_rel_choice_pred.
 rewrite <-H2; apply t_trans with x; auto.
apply Acc_inv with x; trivial.
rewrite <- H2; trivial.
Qed.

  Lemma WFR_ext xx' a a' : Acc R xx -> xx == xx' -> Aeq a a' -> WFR xx a == WFR xx' a'.
Proof using Aeqv Rsubm Fext.
intros.
unfold WFR.
apply cond_set_morph.
*split; destruct 1; constructor; intros.
 rewrite <- H0 in H3; auto.
 rewrite H0 in H3; auto.
*apply uchoice_morph_raw.
 red; intros.
 apply WFR_rel_morph; trivial.
Qed.


  Lemma WFR_eqn0 x a (r:WFRle x xx): Acc R x -> WFR x a == F WFR x a.
intros wfx.
rewrite WFR_eqn'; [|trivial|trivial].
unfold F'; apply Fext; auto with *.
intros.
rewrite cond_set_ok; [|trivial].
apply WFR_morph0; trivial.
Qed.

  Lemma WFR_non_mt x a z : z ∈ WFR x a -> Acc R x.
unfold WFR; rewrite cond_set_ax; intros (_,?); trivial.
Qed.
  
End WellFoundedRecursion.


Definition WFR_eqn Rsub Rsubm F x Fext a :=
  WFR_eqn0 Rsub Rsubm F x Fext x a (WFRle_refl _ x).
(*
WFR_eqn
     : forall Rsub : set -> set,
       morph1 Rsub ->
       forall (F : (set -> A -> set) -> set -> A -> set) (x : set),
       (forall (x0 x' : set) (a a' : A) (f f' : set -> A -> set),
        WFRle Rsub x0 x ->
        (forall (y y' : set) (a0 a'0 : A), y ∈ Rsub x0 -> y == y' -> Aeq a0 a'0 -> f y a0 == f' y' a'0) ->
        x0 == x' -> Aeq a a' -> F f x0 a == F f' x' a') ->
       forall a : A, Acc (fun x0 y : set => x0 ∈ Rsub y) x -> WFR Rsub F x a == F (WFR Rsub F) x a
*)

Local Notation E:=eq_set (only parsing).

Global Instance WFR_morph :
    Proper ((E==>E)==>((E==>Aeq==>E)==>E==>Aeq==>E)==>E==>Aeq==>E) WFR.
do 5 red; intros.
apply cond_set_morph.
*revert x y H x1 y1 H1; clear x2 y2 H2.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 revert y1 H1; induction H2; constructor; intros.
 apply H2 with y2; [|reflexivity].
 revert H4; apply in_set_morph; [reflexivity|auto].
*apply uchoice_morph_raw.
red; intros.
unfold WFR_rel.
apply fa_morph; intros P.
apply fa_morph; intros Pm.
apply impl_morph.
2:intros; apply Pm; trivial.
apply fa_morph; intros x'.
apply fa_morph; intros a'.
apply fa_morph; intros f.
apply fa_morph; intros fm.
apply impl_morph.
 apply fa_morph; intros x''.
 apply fa_morph; intros a''.
 apply impl_morph; auto with *.
 apply in_set_morph; [reflexivity|].
 apply H; auto with *.
intros _.
apply Pm; auto with *.
apply H0; auto with *.
do 2 red; intros.
apply cond_set_morph; [|apply fm; trivial].
apply in_set_morph; [trivial|].
 apply H; auto with *.
Qed.
(*  unused:
Global Instance WFR_morph_gen2 R : Proper
  (pointwise_relation _ (pointwise_relation set (pointwise_relation A eq_set)) ==> E==>pointwise_relation A E) (WFR R).
intros F F' eqF x y e a.
apply uchoice_morph_raw.
red; intros.
unfold WFR_rel. 
apply fa_morph; intros P.
apply fa_morph; intros Pm.
apply impl_morph; auto with *.
2:intros; apply Pm; auto with *.
apply fa_morph; intros x'.
apply fa_morph; intros a'.
apply fa_morph; intros f.
apply fa_morph; intros _.
apply fa_morph; intros _.
apply Pm; auto with *.
apply eqF. 
Qed.

  Lemma WFR_ext (R R':set->set) F F' x x' a a':
  pointwise_relation _ E R R' ->
  (forall f f' y a,
   Proper (eq_set==>Aeq==>eq_set) f ->
   Proper (eq_set==>Aeq==>eq_set) f' ->
   (forall z a, z ∈ R y -> f z a == f' z a) ->
   F f y a == F' f' y a) ->
  x == x' ->
  Aeq a a' ->
  WFR R F x a == WFR R' F' x' a'.
intros eqR eqF eqx eqa.
apply ZFrepl.uchoice_morph_raw.
red; intros x1 x1' eqx1.
unfold WFR_rel.
apply fa_morph; intro P.
apply fa_morph; intro Pm.
apply impl_morph; intros.
2:apply Pm; auto with *.
clear a a' eqa.
apply fa_morph; intro x'0.
apply fa_morph; intro a'.
apply fa_morph; intro f.
apply fa_morph; intro fm.
apply impl_morph; intros.
 apply fa_morph; intros x''.
 apply fa_morph; intros a''.
 apply impl_morph; auto with *.
 apply in_set_morph; [reflexivity|].
 apply eqR; auto with *.
apply Pm; auto with *.
apply eqF; auto with *.
*do 3 red; intros.
 apply cond_set_morph; auto.
  rewrite H0; reflexivity.
  apply fm; trivial.
*do 3 red; intros.
 apply cond_set_morph; auto.
  rewrite H0; reflexivity.
  apply fm; trivial.
*intros.
 apply cond_set_morph2; auto with *.
apply in_set_morph; [reflexivity|].
 apply eqR; reflexivity.
Qed.
*)
  
End PolymorphicWellFoundedRecursion.

#[global]Opaque WFR.
