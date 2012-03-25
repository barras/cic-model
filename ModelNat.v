Set Implicit Arguments.

(** In this file, we build a consistency model of the
    Calculus of Constructions extended with natural numbers and
    the usual recursor (CC+NAT). It is a follow-up of file
    ModelZF. 
 *)

Require Import ZF ZFnats ZFrelations.
Require Import basic ModelZF.
Import CCM BuildModel.
Import T J R.

(** * Nat and its constructors *)

Definition Zero : term.
(*begin show*)
left; exists (fun _ => zero).
(*end show*)
 do 2 red; reflexivity.
Defined.

Definition Succ : term.
(*begin show*)
left; exists (fun _ => lam N succ).
(*end show*)
 do 2 red; reflexivity.
Defined.

Definition Nat : term.
(*begin show*)
left; exists (fun _ => N).
(*end show*)
 do 2 red; reflexivity.
Defined.

(** Typing rules of constructors *)
Lemma typ_0 : forall e, typ e Zero Nat.
red; simpl; intros.
apply zero_typ.
Qed.

Lemma typ_S : forall e, typ e Succ (Prod Nat (lift 1 Nat)).
red; simpl; intros.
apply cc_prod_intro; intros; auto with *.
apply succ_typ; trivial.
Qed.

Lemma typ_N : forall e, typ e Nat kind.
red; simpl; trivial.
Qed.

(** * The recursor *)

(** Recursor *)
Definition NatRec (f g n:term) : term.
(*begin show*)
left; exists (fun i => natrec (int f i) (fun n y => app (app (int g i) n) y) (int n i)).
(*end show*)
 do 2 red; intros.
 apply natrec_morph.
  rewrite H; reflexivity.
(**)
  do 2 red; intros.
  rewrite H; rewrite H0; rewrite H1; reflexivity.
(**)
  rewrite H; reflexivity.
Defined.


(** Typing rule of the eliminator *)
Lemma typ_Nrect : forall e n f g P,
  typ e n Nat ->
  typ e f (App P Zero) ->
  typ e g (Prod Nat (Prod (App (lift 1 P) (Ref 0))
              (App (lift 2 P) (App Succ (Ref 1))))) ->
  typ e (NatRec f g n) (App P n).
red; simpl; intros.
apply natrec_typ with (P:=fun x => app (int P i) x); trivial.
 apply cc_app_morph; reflexivity.

 do 3 red; intros.
 apply cc_app_morph; trivial.
 apply cc_app_morph; trivial.
 reflexivity.

 apply H; trivial.

 apply H0; trivial.

 intros.
 red in H1; specialize H1 with (1:=H2).
 simpl in H1.
 apply cc_prod_elim with (2:=H3) in H1.
 eapply eq_elim.
 2:eapply cc_prod_elim with (1:=H1).
  rewrite simpl_int_lift.
  rewrite simpl_int_lift1.
  rewrite cc_beta_eq; auto with *.
  reflexivity.

  rewrite simpl_int_lift1; trivial.
Qed.


Lemma eq_typ_NatRec e f f' g g' n n' :
  eq_typ e f f' ->
  eq_typ e g g' ->
  eq_typ e n n' ->
  eq_typ e (NatRec f g n) (NatRec f' g' n').
unfold eq_typ; intros.
specialize H with (1:=H2).
specialize H0 with (1:=H2).
specialize H1 with (1:=H2).
simpl.
apply natrec_morph; trivial.
do 2 red; intros.
rewrite H0; rewrite H3; rewrite H4; reflexivity.
Qed.

(** iota-reduction *)

Lemma NatRec_eq_0 e f g :
  eq_typ e (NatRec f g Zero) f.
red; simpl; intros.
rewrite natrec_0; reflexivity.
Qed.

Lemma NatRec_eq_S e f g n :
  typ e n Nat ->
  eq_typ e (NatRec f g (App Succ n)) (App (App g n) (NatRec f g n)).
red; simpl; intros.
red in H; specialize H with (1:=H0); simpl in H.
rewrite cc_beta_eq; auto with *.
rewrite natrec_S; auto.
 reflexivity.

 do 2 red; intros; apply cc_app_morph; auto with *.
 apply cc_app_morph; auto with *.
Qed.
