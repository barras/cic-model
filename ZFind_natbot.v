Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFord ZFfix ZFstable.
Require Import ZFgrothendieck.
Require Import ZFlist ZFcoc.
Import ZFrepl.
Require Export ZFind_nat.

(** In this file we develop an alternative model of nat contain the empty set.
    In contrast with the standard model, we have extra values:
    ⊥, S ⊥, S S ⊥, etc.
    Interpreting the natural numbers just as N+{∅} would force to have
    S ⊥ = ⊥, and then (match S ⊥ with S k => g(k) end) would be ⊥ instead
    of g(⊥)... 
 *)

(** * Definition and properties of the new operator *)

Definition NATf' X := NATf (cc_bot X).

 Instance NATf'_mono : Proper (incl_set==>incl_set) NATf'.
do 2 red; intros.
unfold NATf'; apply NATf_mono; trivial.
apply cc_bot_mono; auto with *.
Qed.

  Lemma mt_not_in_NATf' o x :
    isOrd o ->
    x ∈ TI NATf' o ->
    ~ x == empty.
red; intros.
apply TI_elim in H0; auto with *.
destruct H0 as (o',?,?).
unfold NATf' in H2.
rewrite H1 in H2.
apply NATf_case with (3:=H2); intros.
 apply discr_mt_pair in H3; trivial.
 apply discr_mt_pair in H4; trivial.
Qed.
(*
  Lemma ZEROi_typ' o :
    isOrd o ->
    ZERO ∈ TI NATf' (osucc o).
intros.
rewrite TI_mono_succ; auto with *.
apply ZERO_typ_gen.
Qed.

  Lemma SUCCi_typ' o n :
    isOrd o ->
    n ∈ cc_bot (TI NATf' o) ->
    SUCC n ∈ TI NATf' (osucc o).
intros.
rewrite TI_mono_succ; auto with *.
apply SUCC_typ_gen; auto.
Qed.
*)

Definition NAT' := TI NATf' omega.

Require Import ZFcont.

  Lemma cc_bot_cont o F :
    ext_fun o F ->
    (exists w, w ∈ o) ->
    cc_bot (sup o F) == sup o (fun y => cc_bot (F y)).
intros.
apply eq_set_ax; intros z.
rewrite cc_bot_ax.
rewrite sup_ax; auto with *.
rewrite sup_ax.
 split; intros.
  destruct H1 as [?|(w,?,?)]; eauto.
  destruct H0 as (w,?).
  exists w; trivial.
  rewrite H1; auto.

  destruct H1 as (w,?,?).
  rewrite cc_bot_ax in H2; destruct H2; eauto.

 do 2 red; intros; apply cc_bot_morph; auto.
Qed.

  Lemma NAT'_continuous : forall F,
    ext_fun omega F ->
    NATf' (sup omega F) == sup omega (fun n => NATf' (F n)).
intros.
unfold NATf', NATf.
rewrite <- sum_cont; auto.
 rewrite <- cst_cont.
 2:exists zero; apply zero_omega.
 rewrite cc_bot_cont; auto with *.
 exists zero; apply zero_omega.

 do 2 red; intros; apply cc_bot_morph; auto.
Qed.


  Lemma NAT'_eq : NAT' == NATf' NAT'.
unfold NAT' at 1, NAT, NATi.
assert (ext_fun omega (TI NATf')).
 do 2 red; intros; apply TI_morph; auto with *.
rewrite TI_eq; auto with *.
rewrite <- NAT'_continuous; trivial.
apply (Fmono_morph _ NATf'_mono).
unfold NAT'.
apply eq_set_ax; intros z.
rewrite sup_ax; auto.
split; intros.
 destruct H0 as (o,?,?).
 assert (isOrd o) by eauto using isOrd_inv.
 apply TI_intro with o; auto with *.
 rewrite <- TI_mono_succ; auto with *.
 revert H1; apply TI_incl; auto with *.

 apply TI_elim in H0; auto with *.
 destruct H0 as (o,?,?).
 exists (osucc o); auto.
  apply osucc_omega; trivial.

  rewrite TI_mono_succ; auto with *.
  apply isOrd_inv with omega; auto.
Qed.

  Lemma NATf'_stages o :
    isOrd o ->
    TI NATf' o ⊆ NAT'.
induction 1 using isOrd_ind; intros.
red; intros.
apply TI_elim in H2; auto with *.
destruct H2 as (o',?,?).
rewrite NAT'_eq.
revert H3; apply NATf'_mono; auto.
Qed.

  Lemma ZERO_typ' :
    ZERO ∈ NAT'.
rewrite NAT'_eq.
apply ZERO_typ_gen.
Qed.

  Lemma SUCC_typ' n :
    n ∈ cc_bot NAT' ->
    SUCC n ∈ NAT'.
intros.
rewrite NAT'_eq.
apply SUCC_typ_gen; auto.
Qed.

(** Recursor on NAT' *)

Require Import ZFfunext ZFfixrec.

Section Recursor.

  Variable ord : set.
  Hypothesis oord : isOrd ord.

  Variable F : set -> set -> set.
  Hypothesis Fm : morph2 F.

  Variable U' : set -> set -> set.
  Hypothesis U'mono : forall o o' x x',
    isOrd o' -> o' ⊆ ord -> isOrd o -> o ⊆ o' ->
    x ∈ TI NATf' o -> x == x' ->
    U' o x ⊆ U' o' x'.

  Let Ty' o := cc_prod (TI NATf' o) (U' o).
  Let Q' o f := forall x, x ∈ TI NATf' o -> cc_app f x ∈ U' o x.

  Hypothesis Ftyp' : forall o f, isOrd o -> o ⊆ ord ->
    f ∈ Ty' o -> F o f ∈ Ty' (osucc o).

  Definition NAT_ord_irrel' :=
    forall o o' f g,
    isOrd o' -> o' ⊆ ord -> isOrd o -> o ⊆ o' ->
    f ∈ Ty' o -> g ∈ Ty' o' ->
    fcompat (TI NATf' o) f g ->
    fcompat (TI NATf' (osucc o)) (F o f) (F o' g).

  Hypothesis Firrel' : NAT_ord_irrel'.

Lemma U'morph : forall o o', isOrd o' -> o' ⊆ ord -> o == o' ->
    forall x x', x ∈ TI NATf' o -> x == x' -> U' o x == U' o' x'. 
intros.
apply incl_eq.
 apply U'mono; auto.
  rewrite H1; trivial.
  rewrite H1; reflexivity.

 apply U'mono; auto.
  rewrite H1; trivial.
  rewrite H1; trivial.
  rewrite H1; reflexivity.
  rewrite <- H3; rewrite <- H1; trivial.
  symmetry; trivial.
Qed.

Lemma U'ext : forall o, isOrd o -> o ⊆ ord -> ext_fun (TI NATf' o) (U' o).
red; red; intros.
apply U'morph; auto with *.
Qed.


  Lemma NATREC_typing' : forall o f, isOrd o -> o ⊆ ord -> 
    is_cc_fun (TI NATf' o) f -> Q' o f -> f ∈ Ty' o.
intros.
rewrite cc_eta_eq' with (1:=H1).
apply cc_prod_intro; intros; auto.
 do 2 red; intros.
 rewrite H4; reflexivity.

 apply U'ext; trivial.
Qed.

Let Q'm :
   forall o o',
   isOrd o ->
   o ⊆ ord ->
   o == o' -> forall f f', fcompat (TI NATf' o) f f' -> Q' o f -> Q' o' f'.
intros.
unfold Q' in H3|-*; intros.
rewrite <- H1 in H4.
specialize H3 with (1:=H4).
red in H2; rewrite <- H2; trivial.
revert H3; apply U'mono; auto with *.
 rewrite <- H1; trivial.
 rewrite <- H1; trivial.
 rewrite <- H1; reflexivity.
Qed.


Let Q'cont : forall o f : set,
 isOrd o ->
 o ⊆ ord ->
 is_cc_fun (TI NATf' o) f ->
 (forall o' : set, o' ∈ o -> Q' (osucc o') f) -> Q' o f.
intros.
red; intros.
apply TI_elim in H3; auto with *.
destruct H3.
rewrite <- TI_mono_succ in H4; eauto using isOrd_inv.
2:apply NATf'_mono.
generalize (H2 _ H3 _ H4).
apply U'mono; eauto using isOrd_inv with *.
red; intros.
apply isOrd_plump with x0; eauto using isOrd_inv.
apply olts_le in H5; trivial.
Qed.

Let Q'typ : forall o f,
 isOrd o ->
 o ⊆ ord ->
 is_cc_fun (TI NATf' o) f ->
 Q' o f -> is_cc_fun (TI NATf' (osucc o)) (F o f) /\ Q' (osucc o) (F o f).
intros.
assert (F o f ∈ Ty' (osucc o)).
 apply Ftyp'; trivial.
 apply NATREC_typing'; trivial.
split.
 apply cc_prod_is_cc_fun in H3; trivial.

 red; intros.
 apply cc_prod_elim with (1:=H3); trivial.
Qed.

  Lemma NATREC_recursor' : recursor ord (TI NATf') Q' F.
split; auto.
 apply TI_morph.

 intros.
 apply TI_mono_eq; auto with *.

 red; red; intros.
 destruct H1 as (oo,(ofun,oty)); destruct H2 as (o'o,(o'fun,o'ty)).
 apply Firrel'; trivial.
  apply NATREC_typing'; trivial. 
  transitivity o'; trivial.

  apply NATREC_typing'; trivial. 
Qed.

  Lemma NATREC_wt' : NATREC F ord ∈ Ty' ord.
intros.
destruct REC_wt with (1:=oord) (2:=NATREC_recursor').
apply NATREC_typing'; auto with *.
Qed.

  Lemma NATREC_ind' : forall P x,
    Proper (eq_set==>eq_set==>eq_set==>iff) P ->
    (forall o x, isOrd o -> lt o ord ->
     x ∈ NATf' (TI NATf' o) ->
     (forall y, y ∈ TI NATf' o -> P o y (cc_app (NATREC F ord) y)) ->
     forall w, isOrd w -> w ⊆ ord -> lt o w ->
     P w x (cc_app (F ord (NATREC F ord)) x)) ->
    x ∈ TI NATf' ord ->
    P ord x (cc_app (NATREC F ord) x).
intros.
unfold NATREC.
apply REC_ind with (2:=NATREC_recursor'); auto.
intros.
apply TI_elim in H4; auto with *.
destruct H4 as (o',?,?).
apply H0 with o'; eauto using isOrd_inv.
red; auto.
Qed.

  Lemma NATREC_expand' : forall n,
    n ∈ TI NATf' ord -> cc_app (NATREC F ord) n == cc_app (F ord (NATREC F ord)) n.
intros.
apply REC_expand with (2:=NATREC_recursor') (Q:=Q'); auto.
Qed.

  Lemma NATREC_irrel' o o' :
    isOrd o ->
    isOrd o' ->
    o ⊆ o' ->
    o' ⊆ ord ->
    eq_fun (TI NATf' o) (cc_app (NATREC F o)) (cc_app (NATREC F o')).
red; intros.
rewrite <- H4.
apply REC_ord_irrel with (2:=NATREC_recursor'); auto with *.
Qed.


End Recursor.

(** * Universe facts: NAT' belongs to any Grothendieck universes that
      is contains omega.
 *)

Section NAT'_Univ.

(* Universe facts *)
  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : omega ∈ U.  

  Lemma G_NATf' X : X ∈ U -> NATf' X ∈ U.
intros.
unfold NATf'.
assert (empty ∈ U).
 apply G_trans with omega; auto. 
 apply zero_omega.
apply G_sum; trivial.
 unfold ZFind_basic.UNIT.
 apply G_union2; trivial.
 apply G_singl; trivial.

 apply G_union2; trivial.
 apply G_singl; auto.
Qed.

  Lemma G_NAT' : NAT' ∈ U.
apply G_TI; auto with *.
apply G_NATf'.
Qed.

End NAT'_Univ.
