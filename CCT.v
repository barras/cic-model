Require Import Models.
Require Import GenModel.
Require Import ModelZF.
Require Import ZFcoc.
Require Import ZF.
Import IZF.

Module BuildModel := GenModel.MakeModel(CCM).
Import BuildModel.
Import T.
Import J.
Import CCM.



Definition Zero : term.
left; exists (fun _ => empty); do 2 red; reflexivity.
Defined.

Definition Succ : term.
left; exists (fun _ => lam (singl empty) (fun x => x)); do 2 red; reflexivity.
Defined.

Definition NatRec (f g n:term) : term.
left; exists (fun i => int f i);
do 2 red; intros; rewrite H; reflexivity.
Defined.

Definition T : term.
left; exists (fun _ => singl empty); do 2 red; reflexivity.
Defined.

Lemma typ_0 : forall e, typ e Zero T.
do 2 red; simpl; intros e i H; apply singl_intro.
Qed.

Lemma typ_S : forall e, typ e Succ (Prod T (lift 1 T)).
do 2 red; simpl; intros e i H. apply prod_intro.
  red. intros y1 y2 H0 H1; exact H1.
  red; reflexivity.
  intros x H0; exact H0.
Qed.

Lemma typ_Nrect : forall e n f g P,
  typ e n T ->
  typ e P (Prod T prop) -> 
  typ e f (App P Zero) ->
  typ e g (Prod T (Prod (App (lift 1 P) (Ref 0))
              (App (lift 2 P) (App Succ (Ref 1))))) ->
  typ e (NatRec f g n) (App P n).
do 2 red; simpl; intros.
red in H. simpl in H.
  assert (int n i == empty). apply H in H3. apply (singl_elim _ _ H3).
  rewrite H4. apply H1. apply H3.
Qed. 


Lemma all_conv_allowed : forall e M M',
  typ e M T ->
  typ e M' T ->
  eq_typ e M M'.
do 2 red; intros.
  assert (int M i == empty). red in H; simpl in H. 
    apply singl_elim. apply H. apply H1.
  assert (int M' i == empty). red in H0; simpl in H0; 
    apply singl_elim; apply H0; apply H1.
  rewrite H2; rewrite H3; reflexivity.
Qed.













