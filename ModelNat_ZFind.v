
(* Nat *)
Set Implicit Arguments.

(** In this file, we build a consistency model of the
    Calculus of Constructions extended with natural numbers and
    the usual recursor (CC+NAT). It is a follow-up of file
    ModelZF. 
 *)

Require Import ZF ZFcoc ZFind_nat.
Require Import basic ModelZF.
Import CCM BuildModel.

(** * Nat and its constructors *)
Import T J R.

Definition Zero : term.
(*begin show*)
left; exists (fun _ => ZERO).
(*end show*)
 do 2 red; reflexivity.
Defined.

Definition Succ : term.
(*begin show*)
left; exists (fun _ => lam NAT SUCC).
(*end show*)
 do 2 red; reflexivity.
Defined.

Definition Nat : term.
(*begin show*)
left; exists (fun _ => NAT).
(*end show*)
 do 2 red; reflexivity.
Defined.

(** Typing rules of constructors *)
Lemma typ_0 : forall e, typ e Zero Nat.
red; simpl; intros.
apply ZERO_typ.
Qed.

Lemma typ_S : forall e, typ e Succ (Prod Nat (lift 1 Nat)).
red; simpl; intros.
apply cc_prod_intro; intros; auto with *.
apply SUCC_typ; trivial.
Qed.

Lemma typ_N : forall e, typ e Nat kind.
red; simpl; trivial.
Qed.

(** * The recursor *)


Definition NREC f g n y :=
  forall P,
  Proper (eq_set ==> eq_set ==> iff) P -> 
  P ZERO f -> (forall m x, P m x -> P (SUCC m) (g m x)) -> P n y.

Lemma NREC_inv : forall f g n y,
  morph2 g ->
  NREC f g n y ->
  NREC f g n y /\
  (n == ZERO -> y == f) /\
  (forall m, n == SUCC m -> exists2 z, NREC f g m z & y == g m z).
intros f g n y gm h; pattern n, y; apply h.
 do 3 red; intros.
 apply and_iff_morphism.
  split; red; intros.
   rewrite <- H; rewrite <- H0; apply H1; trivial. 
   rewrite H; rewrite H0; apply H1; trivial. 
  apply and_iff_morphism.
   rewrite H; rewrite H0; reflexivity.

   apply fa_morph; intro m.
   rewrite H.
   apply fa_morph; intros _.
   apply ex2_morph.
    red; reflexivity.

    red; intros.
    rewrite H0; reflexivity.

 split; [|split]; intros.
  red; auto.

  reflexivity.

  apply NATf_discr in H; contradiction.

 intros ? ? (?,(?,?)).
 split; [|split]; intros.
  red; intros.
  apply H4; apply H; auto.

  symmetry in H2; apply NATf_discr in H2; contradiction.

  apply SUCC_inj in H2.
  exists x.
   red; intros.
   rewrite <- H2; apply H; auto.

   rewrite H2; reflexivity.
Qed.

Require Import ZFrepl.

Lemma NREC_choice_0 : forall f g, uchoice_pred (NREC f g ZERO).
split; [|split]; intros.
 unfold NREC in *; intros.
 rewrite <- H.
 apply H0; auto.

 exists f.
 red; auto.

 cut (ZERO==ZERO); auto with *.
 pattern ZERO at 2, x; apply H; intros.
  do 3 red; intros.
  rewrite H1; rewrite H2; reflexivity.

  revert H1; pattern ZERO at 2, x'; apply H0; intros.
   do 3 red; intros.
   rewrite H1; rewrite H2; reflexivity.

   reflexivity.

   apply NATf_discr in H2; contradiction.

  apply NATf_discr in H2; contradiction.
Qed.


Lemma NREC_choice : forall f g n,
  n ∈ NAT ->
  morph2 g ->
  uchoice_pred (NREC f g n).
intros f g n H gm.
split; intros.
 unfold NREC; intros.
 rewrite <- H0.
 apply H1; auto.

 split; intros.
  elim H using NAT_ind; intros.
   destruct H2.
   exists x0; red; intros.
   rewrite <- H1.
   apply H2; auto.

   exists f; red; auto.

   destruct H1.
   exists (g n0 x); red; intros.
   apply H4.
   apply H1; auto.

  revert x x' H0 H1.
  elim H using NAT_ind; intros.
   apply H2.
    red; intros; rewrite H1; apply H3; trivial.
    red; intros; rewrite H1; apply H4; trivial.

   apply NREC_inv in H0; trivial; apply NREC_inv in H1; trivial;
   destruct H0 as (_,(?,_)); destruct H1 as (_,(?,_)).
   rewrite H0; auto with *.
   rewrite H1; auto with *.

   apply NREC_inv in H2; trivial; apply NREC_inv in H3; trivial;
   destruct H2 as (_,(_,?)); destruct H3 as (_,(_,?)).
   destruct (H2 n0); auto with *.
   destruct (H3 n0); auto with *.
   rewrite H5; rewrite H7.
   apply gm; auto with *.
Qed.

(** Recursor at the level of sets *)
Definition NATREC f g n := uchoice (NREC f g n).

Instance NATREC_morph :
  Proper (eq_set ==> (eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) NATREC.
do 4 red; intros.
unfold NATREC, NREC.
apply uchoice_morph_raw.
red; intros.
apply fa_morph; intro P.
apply fa_morph; intro Pm.
rewrite H.
apply fa_morph; intros _.
split; intros.
 rewrite <- H1; rewrite <- H2; apply H3; intros.
 setoid_replace (x0 m x3) with (y0 m x3); auto.
 apply H0; reflexivity.

 rewrite H1; rewrite H2; apply H3; intros.
 setoid_replace (y0 m x3) with (x0 m x3); auto.
 symmetry; apply H0; reflexivity.
Qed.

Lemma NATREC_def : forall f g n,
  morph2 g -> n ∈ NAT -> NREC f g n (NATREC f g n).
intros.
unfold NATREC; apply uchoice_def.
apply NREC_choice; trivial.
Qed.


Lemma NATREC_0 : forall f g, NATREC f g ZERO == f.
unfold NATREC; intros.
symmetry; apply uchoice_ext; trivial.
 apply NREC_choice_0.

 red; auto.
Qed.

Lemma NATREC_S : forall f g n, morph2 g -> n ∈ NAT ->
   NATREC f g (SUCC n) == g n (NATREC f g n).
intros.
elim H0 using NAT_ind; intros.
 rewrite <- H2; trivial.

 symmetry; apply uchoice_ext.
  apply NREC_choice; trivial.
  apply SUCC_typ; apply ZERO_typ.
 red; intros.
 apply H3.
 rewrite NATREC_0; auto.

 unfold NATREC at 1; symmetry; apply uchoice_ext; auto.
  apply NREC_choice; trivial.
  do 2 apply SUCC_typ; trivial.

  red; intros.
  apply H5.
  rewrite H2.
  apply H5.
  revert P H3 H4 H5; change (NREC f g n0 (NATREC f g n0)).
  unfold NATREC; apply uchoice_def.
  apply NREC_choice; trivial.
Qed.

Lemma NATREC_typ P f g n :
  morph1 P ->
  morph2 g ->
  n ∈ NAT ->
  f ∈ P ZERO ->
  (forall k h, k ∈ NAT -> h ∈ P k -> g k h ∈ P (SUCC k)) ->
  NATREC f g n ∈ P n.
intros.
elim H1 using NAT_ind; intros.
 rewrite <- H5; trivial.

 rewrite NATREC_0; trivial.

 rewrite NATREC_S; auto.
Qed.

(** Recursor *)
Definition NatRec (f g n:term) : term.
(*begin show*)
left; exists (fun i => NATREC (int f i) (fun n y => app (app (int g i) n) y) (int n i)).
(*end show*)
 do 2 red; intros.
 apply NATREC_morph.
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
apply NATREC_typ with (P:=fun x => app (int P i) x); trivial.
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
apply NATREC_morph; trivial.
do 2 red; intros.
rewrite H0; rewrite H3; rewrite H4; reflexivity.
Qed.

(** iota-reduction *)

Lemma NatRec_eq_0 e f g :
  eq_typ e (NatRec f g Zero) f.
red; simpl; intros.
rewrite NATREC_0; reflexivity.
Qed.

Lemma NatRec_eq_S e f g n :
  typ e n Nat ->
  eq_typ e (NatRec f g (App Succ n)) (App (App g n) (NatRec f g n)).
red; simpl; intros.
Instance NATREC_morph' :
  Proper (eq ==> eq ==> eq_set ==> eq_set) NATREC.
do 4 red; intros.
subst y y0.
unfold NATREC.
apply uchoice_morph_raw.
red; intros.
unfold NREC.
apply fa_morph; intros P.
apply fa_morph; intros Pm.
rewrite H1; rewrite H; reflexivity.
Qed.

red in H; specialize H with (1:=H0); simpl in H.
rewrite cc_beta_eq; auto with *.
rewrite NATREC_S; auto.
 reflexivity.

 do 2 red; intros; apply cc_app_morph; auto with *.
 apply cc_app_morph; auto with *.
Qed.
