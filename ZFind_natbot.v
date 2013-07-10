Set Implicit Arguments.
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

Lemma NAT'_ind P n :
  Proper (eq_set==>iff) P ->
  n ∈ cc_bot NAT' ->
  P empty ->
  P ZERO ->
  (forall m, m ∈ cc_bot NAT' -> P m -> P (SUCC m)) -> 
  P n.
intros.
revert n H0; unfold NAT'; apply isOrd_ind with (2:=isOrd_omega); intros.
apply cc_bot_ax in H6; destruct H6.
 rewrite H6; trivial.

 apply TI_elim in H6; auto with *.
 destruct H6 as (o',o'o,?).
 apply NATf_case with (3:=H6); intros.
  rewrite H7; trivial.

  rewrite H8; apply H3.
   revert H7; apply cc_bot_mono.
   apply NATf'_stages.
   apply isOrd_inv with y; trivial.

   apply H5 with o'; trivial. 
Qed.

(** The usual recursor on NAT, extended to NAT' *)

Definition NREC f g n y :=
  forall (P:set->set->Prop),
  Proper (eq_set==>eq_set==>iff) P ->
  P empty empty ->
  P ZERO f ->
  (forall m z, m ∈ cc_bot NAT' -> P m z -> P (SUCC m) (g m z)) ->
  P n y.

Lemma NREC_mt f g : NREC f g empty empty.
red; intros; trivial.
Qed.
Lemma NREC_ZERO f g : NREC f g ZERO f.
red; intros; trivial.
Qed.
Lemma NREC_SUCC f g n y:
  n ∈ cc_bot NAT' -> NREC f g n y -> NREC f g (SUCC n) (g n y).
unfold NREC; intros.
apply H4; trivial.
apply H0; trivial.
Qed.
Instance NREC_morph :
  Proper (eq_set==>(eq_set==>eq_set==>eq_set)==>eq_set==>eq_set==>iff) NREC.
apply morph_impl_iff4; auto with *.
unfold NREC; do 6 red; intros.
rewrite <- H in H6.
rewrite <- H1; rewrite <- H2; apply H3; trivial.
intros.
rewrite (H0 _ _ (reflexivity m) _ _ (reflexivity z)).
auto.
Qed.
Instance NREC_morph_eq :
  Proper (eq_set==>eq==>eq_set==>eq_set==>iff) NREC.
apply morph_impl_iff4; auto with *.
unfold NREC; do 6 red; intros.
subst x0; rewrite <- H in H6.
rewrite <- H1; rewrite <- H2; apply H3; trivial.
Qed.

Lemma NREC_inv f g n y :
  NREC f g n y ->
   NREC f g n y /\
   ((n==empty/\y==empty) \/
    (n==ZERO/\y==f) \/
    (exists2 m, n == SUCC m & exists2 z, NREC f g m z & y==g m z)).
intros H; apply H; intros.
 do 3 red; intros.
 apply and_iff_morphism.
  apply NREC_morph_eq; auto with *.

  repeat apply or_iff_morphism.
   rewrite H0; rewrite H1; reflexivity.
   rewrite H0; rewrite H1; reflexivity.
   apply ex2_morph; red; intros.
    rewrite H0; reflexivity.
   apply ex2_morph; red; intros.
    apply NREC_morph_eq; auto with *.
    rewrite H1; reflexivity.

 split; auto with *.
 apply NREC_mt.

 split; auto with *.
 apply NREC_ZERO.

 destruct H1 as (?,_).
 split.
  apply NREC_SUCC; trivial.

  right; right.
  exists m;[reflexivity|].
  exists z; auto with *.
Qed.
Lemma NREC_inv_mt f g y :
  NREC f g empty y -> y == empty.
intros; apply NREC_inv in H;
   destruct H as (_,[(_,eqy)|[(abs,_)|(n,abs,_)]]); auto.
 apply discr_mt_pair in abs; contradiction.
 apply discr_mt_pair in abs; contradiction.
Qed.
Lemma NREC_inv_ZERO f g y :
  NREC f g ZERO y -> y == f.
intros; apply NREC_inv in H;
   destruct H as (_,[(abs,_)|[(_,eqy)|(n,abs,_)]]); auto.
 symmetry in abs; apply discr_mt_pair in abs; contradiction.
 apply NATf_discr in abs; contradiction.
Qed.
Lemma NREC_inv_SUCC f g n y :
  morph2 g ->
  NREC f g (SUCC n) y -> exists2 z, NREC f g n z & y == g n z.
intros; apply NREC_inv in H0;
   destruct H0 as (_,[(abs,_)|[(abs,_)|(m,eqS,(z,defz,eqy))]]).
 symmetry in abs; apply discr_mt_pair in abs; contradiction.
 symmetry in abs; apply NATf_discr in abs; contradiction.

 apply SUCC_inj in eqS.
 rewrite <- eqS in defz, eqy; eauto.
Qed.

Lemma NREC_uch_mt f g :
  uchoice_pred (NREC f g empty).
split;[|split]; intros.
 rewrite <- H; trivial.

 exists empty; apply NREC_mt.
 apply NREC_inv_mt in H.
 apply NREC_inv_mt in H0.
 rewrite H; rewrite H0; reflexivity.
Qed.

Lemma NREC_uch_ZERO f g :
  uchoice_pred (NREC f g ZERO).
split;[|split]; intros.
 rewrite <- H; trivial.

 exists f; apply NREC_ZERO.
 apply NREC_inv_ZERO in H.
 apply NREC_inv_ZERO in H0.
 rewrite H; rewrite H0; reflexivity.
Qed.

Lemma NREC_uch f g n :
  morph2 g ->
  n ∈ cc_bot NAT' ->
  uchoice_pred (NREC f g n).
intros gm tyn.
apply NAT'_ind with (2:=tyn).
 do 2 red; intros; apply uchoice_pred_morph.
 red; intros; apply NREC_morph_eq; auto with *.

 apply NREC_uch_mt.

 apply NREC_uch_ZERO.

 intros m tym (_,((z,?),muniq)).
 split; [|split]; intros.
  rewrite <- H0; trivial.

  exists (g m z); apply NREC_SUCC; trivial.

  apply NREC_inv_SUCC in H0; trivial.
  apply NREC_inv_SUCC in H1; trivial.
  destruct H0 as (y,?,eqx).
  destruct H1 as (y',?,eqx').
  rewrite eqx; rewrite eqx'; apply gm; eauto with *.
Qed.

Definition NAT_RECT f g n := uchoice (NREC f g n).

Instance NAT_RECT_morph :
  Proper (eq_set==>(eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) NAT_RECT.
do 4 red; intros.
apply uchoice_morph_raw.
red; intros; apply NREC_morph; trivial.
Qed.
Instance NAT_RECT_morph_eq :
  Proper (eq_set==>eq==>eq_set==>eq_set) NAT_RECT.
do 4 red; intros.
apply uchoice_morph_raw.
red; intros; apply NREC_morph_eq; trivial.
Qed.

Lemma NAT_RECT_mt f g :
  NAT_RECT f g empty == empty.
symmetry; apply uchoice_ext.
 apply NREC_uch_mt.

 apply NREC_mt.
Qed.

Lemma NAT_RECT_ZERO f g :
  NAT_RECT f g ZERO == f.
symmetry; apply uchoice_ext.
 apply NREC_uch_ZERO.

 apply NREC_ZERO.
Qed.

Lemma NAT_RECT_eq f g n y :
  morph2 g ->
  n ∈ cc_bot NAT' ->
  (NAT_RECT f g n == y <-> NREC f g n y).
intros.
assert (ch := NREC_uch f H H0).
assert (eqn := uchoice_def _ ch).
split; intros.
 rewrite <- H1; trivial.

 symmetry; apply uchoice_ext; trivial.
Qed.

Lemma NAT_RECT_SUCC f g n :
  morph2 g ->
  n ∈ cc_bot NAT' ->
  NAT_RECT f g (SUCC n) == g n (NAT_RECT f g n).
intros.
apply NAT_RECT_eq; trivial.
 apply cc_bot_intro.
 apply SUCC_typ'; trivial.

 apply NREC_SUCC; trivial.

 apply NAT_RECT_eq; trivial.
 reflexivity.
Qed.


Lemma NAT_RECT_typ f g n P :
  morph1 P ->
  n ∈ cc_bot NAT' ->
  empty ∈ P empty ->
  f ∈ P ZERO ->
  g ∈ cc_prod (cc_bot NAT') (fun m => cc_arr (P m) (P (SUCC m))) ->
  NAT_RECT f (fun m y => cc_app (cc_app g m) y) n ∈ P n.
intros.
apply NAT'_ind with (2:=H0).
 do 2 red; intros.
 apply in_set_morph; auto.  
 apply NAT_RECT_morph_eq; auto with *.

 rewrite NAT_RECT_mt; trivial.

 rewrite NAT_RECT_ZERO; trivial.

 intros.
 rewrite NAT_RECT_SUCC; trivial.
  apply cc_prod_elim with (2:=H4) in H3.
  apply cc_arr_elim with (1:=H3) (2:=H5).

  do 3 red; intros.
  rewrite H6; rewrite H7; reflexivity.
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
