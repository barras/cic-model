Set Implicit Arguments.

(** A generic model construction of the natural numbers equipped with
    the standard elimination principle. It builds on GenModel that
    performs the construction for CC.
 *)

Require Import Models TypModels.
Require Import GenModel.

(*
Require Import ZFnats ModelZF.
Module NN <: Nat_Model CCM := ZFnats.
*)

Module Type CCNat_Rules := Judge <+ Nat_Rules.

Module MakeNatModel (Import M : CCNat_Model) <: CCNat_Rules.

  Module MM := MakeModel(M).
  Include MM.

Let succ_m : eq_fun N succ succ.
red; intros; apply succ_morph; trivial.
Qed.
Hint Resolve succ_m.

(** * Nat and its constructors *)
Import T.

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

Import J.
(** Typing rules of constructors *)
Lemma typ_0 : forall e, typ e Zero Nat.
red; simpl; intros.
apply zero_typ.
Qed.

Lemma typ_S : forall e, typ e Succ (Prod Nat (lift 1 Nat)).
red; simpl; intros.
apply prod_intro; intros; auto with *.
 red; intros; reflexivity.
 
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
 apply app_ext; reflexivity.

 do 3 red; intros.
 apply app_ext; trivial.
 apply app_ext; trivial.
 reflexivity.

 apply H; trivial.

 apply H0; trivial.

 intros.
 red in H1; specialize H1 with (1:=H2).
 simpl in H1.
 apply prod_elim with (3:=H3) in H1.
  eapply in_ext; [reflexivity| |apply prod_elim with (2:=H1)].
   rewrite simpl_int_lift.
   rewrite simpl_int_lift1.
   rewrite beta_eq; auto with *.
   reflexivity.

   red; intros.
   apply app_ext; [|reflexivity].
   apply int_morph; auto with *.
   intros x.
   rewrite H6; reflexivity.

   rewrite simpl_int_lift1; trivial.

  red; intros.
  apply prod_ext.
   apply app_ext; [|trivial].
   rewrite !simpl_int_lift1; reflexivity.
  red; intros.
  rewrite !simpl_int_lift.
  rewrite H6; reflexivity.
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
rewrite natrec_0; auto with *; try reflexivity.
Qed.

Lemma NatRec_eq_S e f g n :
  typ e n Nat ->
  eq_typ e (NatRec f g (App Succ n)) (App (App g n) (NatRec f g n)).
red; simpl; intros.
red in H; specialize H with (1:=H0); simpl in H.
transitivity (natrec (int f i) (fun n y => app (app (int g i) n) y) (succ (int n i))).
 apply natrec_morph; [reflexivity| |apply beta_eq; auto].
 do 2 red; intros.
 rewrite H1,H2; reflexivity.
rewrite natrec_S; [reflexivity| |trivial].
do 3 red; intros.
rewrite H1,H2; reflexivity.
Qed.

End MakeNatModel.
