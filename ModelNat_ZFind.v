
(* Nat *)
Set Implicit Arguments.

(** In this file, we build a consistency model of the
    Calculus of Constructions extended with natural numbers and
    the usual recursor (CC+NAT). It is a follow-up of file
    ModelZF. 
 *)

Require Import ZF ZFwfr ZFcoc ZFind_nat.
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

(*Import ZFwf ZFord.*)
Definition NAT_REC f g n :=
  WFRK (fun x => x ∈ NAT) (fun n m => n ∈ NAT /\ m == SUCC n)
       (fun F n => NATCASE f (fun m => g m (F m)) n) n.

Instance NATREC_morph :
  Proper (eq_set ==> (eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) NAT_REC.
do 4 red; intros.
unfold NAT_REC.
apply WFRK_morph; trivial.
 red; intros.
 rewrite H2; reflexivity.

 do 2 red; intros.
 rewrite H2,H3; reflexivity.

 do 2 red; intros.
 apply NATCASE_morph; trivial.
 red; intros.
 apply H0; auto.
Qed.

Section NatrecProperties.

  Let Rm : Proper (eq_set ==> eq_set ==> iff) (fun n m : set => n ∈ NAT /\ m == SUCC n).
do 3 red; intros.
rewrite H,H0; reflexivity.
Qed.

  Let AccN x : x ∈ NAT -> Acc (fun n m : set => n ∈ NAT /\ m == SUCC n) x.
intros.
apply NAT_ind with (4:=H). 
 intros.
 revert H2; apply iff_impl; eapply wf_morph with (eqA:=eq_set); auto with *.

 constructor; intros.
 destruct H0.
 apply NATf_discr in H1; contradiction.

 intros.
 constructor; intros.
 destruct H2.
 apply SUCC_inj in H3.
 revert H1; apply iff_impl; apply wf_morph with (eqA:=eq_set); auto with *.
Qed.

  Let invN x y : x ∈ NAT /\ y == SUCC x -> y ∈ NAT -> x ∈ NAT.
destruct 1; trivial.
Qed.

  Let casem f' g' : morph2 g' -> Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set)
                (fun F n => NATCASE f' (fun m => g' m (F m)) n).
do 3 red; intros.
apply NATCASE_morph; auto with *.
red; intros.
apply H; auto.
Qed.

  Let caseext f g :
    morph2 g ->
    forall x F F', x ∈ NAT ->
    (forall y y' : set, y ∈ NAT /\ x == SUCC y -> y == y' -> F y == F' y') ->
    NATCASE f (fun m : set => g m (F m)) x ==
    NATCASE f (fun m : set => g m (F' m)) x.
intros.
apply NATCASE_morph_gen; intros; auto with *.
apply H; trivial; apply H1; trivial; split; trivial.
rewrite NAT_eq in H0.
apply SUCC_inv_typ_gen.
rewrite <- H2; trivial.
Qed.

  Lemma NATREC_0 f g : NAT_REC f g ZERO == f.
unfold NAT_REC; intros.
unfold WFRK; rewrite WFR_eqn_norec; auto.
 rewrite cond_set_ok. 2:apply ZERO_typ.
 apply NATCASE_ZERO.

 red; destruct 1.
 apply NATf_discr in H0; trivial.

 intros.
 rewrite cond_set_ok. 2:apply ZERO_typ.
 rewrite cond_set_ok. 2:rewrite <-H; apply ZERO_typ.
 rewrite NATCASE_ZERO.
 unfold NATCASE.
  rewrite cond_set_ok; auto with *.
  rewrite cond_set_mt.
  symmetry; apply union2_mt_r.

  red; destruct 1.
  rewrite <- H in H0.
  apply NATf_discr in H0; trivial.
Qed.

Lemma NATREC_S : forall f g n, morph2 g -> n ∈ NAT ->
   NAT_REC f g (SUCC n) == g n (NAT_REC f g n).
unfold NAT_REC; intros.
rewrite WFRK_eqn; auto.
 rewrite NATCASE_SUCC.
  reflexivity.

  intros; apply H; trivial.
  apply WFR_morph_gen2; trivial.
  reflexivity.  

 clear; do 2 red; intros; rewrite H; reflexivity.

 apply caseext; trivial.

 apply SUCC_typ; trivial.
Qed.
End NatrecProperties.

Lemma NATREC_typ P f g n :
  morph1 P ->
  morph2 g ->
  n ∈ NAT ->
  f ∈ P ZERO ->
  (forall k h, k ∈ NAT -> h ∈ P k -> g k h ∈ P (SUCC k)) ->
  NAT_REC f g n ∈ P n.
intros.
elim H1 using NAT_ind; intros.
 rewrite <- H5; trivial.

 rewrite NATREC_0; trivial.

 rewrite NATREC_S; auto.
Qed.

(** Recursor *)
Definition NatRec (f g n:term) : term.
(*begin show*)
left; exists (fun i => NAT_REC (int f i) (fun n y => app (app (int g i) n) y) (int n i)).
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
rewrite NATREC_0.
reflexivity.
Qed.

Lemma NatRec_eq_S e f g n :
  typ e n Nat ->
  eq_typ e (NatRec f g (App Succ n)) (App (App g n) (NatRec f g n)).
red; simpl; intros.
eapply transitivity.
 apply NATREC_morph.
  reflexivity.

  do 2 red; intros.
  apply cc_app_morph;[|exact H2].
  apply cc_app_morph;[|exact H1].
  reflexivity.
  
  apply beta_eq.
   red; intros; apply ZFsum.inr_morph; trivial.

   apply H in H0; trivial.
rewrite NATREC_S; auto.
 reflexivity.

 do 2 red; intros; apply cc_app_morph; auto with *.
 apply cc_app_morph; auto with *.

 apply H; trivial.
Qed.
