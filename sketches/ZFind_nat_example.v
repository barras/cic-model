Require Import ZF ZFsum ZFcoc ZFfix ZFnats ZFord.
Require Import ZFind_basic.
Require Import ZFind_nat.

(*******************************************************************************)
(** ** Applications *)

Module Example.
(** Abel's counter-example:
    Fix F (x:nat^i) : (nat->nat^i+) -> nat :=
      fun f => match f 0 with
               | 0   => 0
               | S n => match n with
                        | 0   => 0
|                       | S m => F m (shift f) 
 := F (
 *)

Definition U o := cc_arr (cc_arr NAT (NATi (osucc o))) NAT.

(* shift f n = pred (f (S n)) *)
Definition shift f := cc_lam NAT (fun n =>
  NATCASE ZERO (fun m => m) (cc_app f (SUCC n))).

Lemma shift_typ : forall o f,
  isOrd o ->
  f ∈ cc_arr NAT (NATi (osucc (osucc o))) ->
  shift f ∈ cc_arr NAT (NATi (osucc o)).
intros.
unfold shift.
apply cc_arr_intro; intros.
 do 2 red; intros.
 apply NATCASE_morph; auto with *.
 red; auto with *. 
 rewrite H2; auto with *.
apply NATCASE_typ with (o:=osucc o)(P:=fun _=> NATi (osucc o)); auto with *.
 do 2 red; intros; reflexivity.

 unfold NATi; rewrite TI_mono_succ; auto.
 apply ZERO_typ_gen.

 apply cc_arr_elim with (1:=H0).
 apply SUCC_typ; trivial.
Qed.

Lemma shift_identity f :
  (forall x, x ∈ NAT -> cc_app f x == x) ->
  (forall x, x ∈ NAT -> cc_app (shift f) x == x).
intros.    
unfold shift.
rewrite cc_beta_eq; trivial.
+transitivity (NATCASE ZERO (fun m=>m) (SUCC x)).
  apply NATCASE_morph; auto with *. 
   red; auto with *.  
   apply H; apply SUCC_typ; trivial.
   apply NATCASE_SUCC; trivial.
+do 2 red; intros.
  apply NATCASE_morph; auto with *. 
   red; auto with *.  
   rewrite H2; reflexivity.
Qed.

Definition loopF o loop :=
  cc_lam (NATi (osucc o)) (fun _ =>
  cc_lam (cc_arr NAT (NATi (osucc (osucc o)))) (fun f =>
  NATCASE
    ZERO
    (fun n =>
     NATCASE
       ZERO
       (fun m => cc_app (cc_app loop m) (shift f))
       n)
    (cc_app f ZERO))).

Lemma loopF_typ : forall o lp,
  isOrd o ->
  lp ∈ cc_arr (NATi o) (U o) ->
  loopF o lp ∈ cc_arr (NATi (osucc o)) (U (osucc o)).
unfold loopF, U; intros.
apply cc_arr_intro;[| intros y ?].
 do 2 red; reflexivity.
apply cc_arr_intro;[|intros f ?].
 admit.
apply NATCASE_typ with (o:=osucc o) (P:=fun _ => NAT); auto.
 do 2 red; reflexivity.
 admit.

 apply ZERO_typ.

 intros.
 apply NATCASE_typ with (o:=o) (P:=fun _=>NAT); auto.
  do 2 red; reflexivity.
  admit.

  apply ZERO_typ.

  intros.
  apply cc_arr_elim with (cc_arr NAT (NATi (osucc o))).
   apply cc_arr_elim with (NATi o); trivial.

   apply shift_typ; trivial.

 apply cc_arr_elim with NAT; trivial.
 apply ZERO_typ.
Admitted.

 (* loopF satisfies the stability criterion, but the fixpoint cannot be accepted *)

 Lemma sfp : forall o, isOrd o ->
   NAT_ord_irrel o loopF (fun o' x => U o').
intros eps oeps o o' f f' o'o o'eps oo ole tyf tyf' eqf x tyx.
unfold loopF.
rewrite cc_beta_eq; auto.
rewrite cc_beta_eq; auto.
 apply cc_lam_ext.
  admit. (* not provable (we're assuming we can have with multiple recursive arguments) *) 

  red; intros.
  apply NATCASE_morph_gen; intros; auto with *.
   rewrite H0; auto with *.
  apply NATCASE_morph_gen; intros; auto with *.
  apply cc_app_morph.
   rewrite <- H4.
   apply eqf.
   apply SUCCi_inv_typ; trivial.
   rewrite <- H3.
   apply SUCCi_inv_typ; auto.
   rewrite <- H1.
   apply cc_arr_elim with (1:=H).
   apply ZERO_typ.

   unfold shift.
   apply cc_lam_ext; auto with *.
   red; intros.
   apply NATCASE_morph; auto with *.
    red; intros; auto.

    rewrite H0; rewrite H6; reflexivity.

 revert tyx; apply TI_mono; auto with *.
 red; intros; apply ord_le_lt_trans with o; auto.
 apply ole_lts; auto.
Admitted.

End Example.
