
Require Import ZF.

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

Lemma repl_rel_fun : forall x f,
  ext_fun x f -> repl_rel x (fun a b => b == f a).
split; intros.
 rewrite <- H2; rewrite H3; auto.
 rewrite H1; rewrite H2; reflexivity.
Qed.

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


