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

Instance NATf'_morph : morph1 NATf'.
do 2 red; intros.
apply NATf_morph.
apply cc_bot_morph; trivial.
Qed.

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
 apply discr_mt_couple in H3; trivial.
 apply discr_mt_couple in H4; trivial.
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

Lemma NAT_NAT' : NAT ⊆ NAT'.
intros z tyz.
apply NAT_ind with (4:=tyz); intros.
 rewrite <- H0; trivial.

 apply ZERO_typ'.

 apply SUCC_typ'; auto.
Qed.


(** The usual recursor on NAT, extended to NAT' *)

Section Nat_rect.

Let NAT_RECT_body f g (F:set->set) :=
  NATCASE f (fun k => g k (F k)).

Local Instance NAT_RECT_body_morph :
  Proper (eq_set==>(eq_set==>eq_set==>eq_set)==>
                (eq_set==>eq_set)==>eq_set==>eq_set) NAT_RECT_body.
do 5 red; intros.
apply NATCASE_morph; trivial.
red; intros.
apply H0; auto.
Qed.
(*Instance NAT_RECT_body_morph_eq :
  Proper (eq_set==>eq==>eq==>eq_set==>eq_set) NAT_RECT_body.
do 5 red; intros.
subst y0 y1.
unfold NAT_RECT_body, NATCASE.
apply union2_morph.
 rewrite H,H2; reflexivity.

 apply cond_set_morph; auto with *.
  Qed.
*)
Lemma NAT_RECT_body_ext f g x F F' :
   morph2 g ->
   (forall y y', x == SUCC y -> y == y' -> F y == F' y') ->
   NAT_RECT_body f g F x == NAT_RECT_body f g F' x.
intros gm Feq.
apply NATCASE_morph_gen; auto with *.
intros.
apply gm; auto.
Qed.

Lemma NATCASE_ZERO' f g n : n==ZERO -> NATCASE f g n == f.
intros; unfold NATCASE.
rewrite cond_set_ok; trivial.
rewrite cond_set_mt.
 apply union2_mt_r.

 red; destruct 1.
 rewrite H in H0.
 apply NATf_discr in H0; trivial.
Qed.
Lemma NATCASE_mt' f g n : n==empty -> NATCASE f g n == empty.
intros; unfold NATCASE.
repeat rewrite cond_set_mt.
 apply union2_mt_r.

 red; destruct 1.
 rewrite H0 in H.
 apply couple_mt_discr in H; trivial.

 intro.
 rewrite H0 in H.
 apply couple_mt_discr in H; trivial.
Qed.
Lemma NAT_RECT_body0 f g F n :
  n==ZERO -> NAT_RECT_body f g F n == f.
unfold NAT_RECT_body.
intros; apply NATCASE_ZERO'; trivial.
Qed.
Lemma NAT_RECT_body_mt f g F n :
  n==empty -> NAT_RECT_body f g F n == empty.
unfold NAT_RECT_body.
intros; apply NATCASE_mt'; trivial.
Qed.

Let R m n := n == SUCC m.
Local Instance Rmorph : Proper (eq_set==>eq_set==>iff) R.
unfold R; do 3 red; intros.
rewrite H,H0; reflexivity.
Qed.

Definition NAT_RECT (f:set) (g:set->set->set) : set->set :=
  WFR R (NAT_RECT_body f g).

Global Instance NAT_RECT_morph :
  Proper (eq_set ==> (eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) NAT_RECT.
do 4 red; intros.
apply WFR_morph; auto with *.
 apply Rmorph.

 do 2 red; intros.
 apply NAT_RECT_body_morph; trivial.
Qed.

Global Instance NAT_RECT_morph_gen2 f g : morph1 (NAT_RECT f g).
apply WFR_morph0.
Qed.

Instance NAT_RECT_morph_eq :
  Proper (eq_set==>eq==>eq_set==>eq_set) NAT_RECT.
do 4 red; intros.
subst y0.
unfold NAT_RECT.
apply WFR_morph_gen2; trivial.
red; red; intros.
unfold NAT_RECT_body, NATCASE.
apply union2_morph.
 rewrite H; reflexivity.

 apply cond_set_morph; auto with *.
Qed.

Instance NAT_RECT_m1 f g : morph1 (NAT_RECT f g).
apply NAT_RECT_morph_eq; auto with *.
Qed.

Lemma NAT_RECT_mt f g :
  NAT_RECT f g empty == empty.
unfold NAT_RECT.
rewrite WFR_eqn_norec; intros.
 apply NATCASE_mt.

 unfold R; red; intros.

 symmetry in H.
 apply couple_mt_discr in H; trivial.

 rewrite NAT_RECT_body_mt; auto with *.
 rewrite NAT_RECT_body_mt; auto with *.
Qed.

Lemma NAT_RECT_ZERO f g :
  NAT_RECT f g ZERO == f.
unfold NAT_RECT.
rewrite WFR_eqn_norec; intros.
 apply NATCASE_ZERO.

 unfold R; red; intros.
 apply NATf_discr in H; trivial.

 rewrite NAT_RECT_body0; auto with *.
 rewrite NAT_RECT_body0; auto with *.
Qed.

Lemma NATi_acc n o :
  isOrd o ->
  n ∈ cc_bot (TI NATf' o) ->
  Acc R n.
intros oo.
revert n; elim oo using isOrd_ind; intros.
apply cc_bot_ax in H2; destruct H2.
 constructor; intros.
 rewrite H2 in H3.
 red in H3; symmetry in H3; apply couple_mt_discr in H3; contradiction.

 apply TI_elim in H2; auto with *.
 destruct H2 as (z,?,?).
 constructor; intros.
 red in H4; rewrite H4 in H3.
 apply SUCC_inv_typ_gen in H3.
 apply H1 with z; auto.
Qed.

Lemma NAT_RECT_SUCC f g n :
  morph2 g ->
  n ∈ cc_bot NAT' ->
  NAT_RECT f g (SUCC n) == g n (NAT_RECT f g n).
intros.
unfold NAT_RECT at 1.
rewrite WFR_eqn; auto with *.
 fold (NAT_RECT f g).
 unfold NAT_RECT_body; rewrite NATCASE_SUCC; auto with *.
 intros; apply H; auto with *.
 apply NAT_RECT_m1; trivial.
 
 apply NAT_RECT_body_morph; auto with *.

 intros; apply NAT_RECT_body_ext; trivial.

 apply SUCC_typ' in H0.
 apply cc_bot_intro in H0.
 apply NATi_acc in H0; trivial.
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

End Nat_rect.

(** Recursor on NAT' *)

Lemma NATREC_dom_ext : morph1 (TI NATf').
apply TI_morph; auto.
Qed.

Lemma NATREC_dom_cont o : isOrd o -> TI NATf' o == ZF.sup o (fun o' => TI NATf' (osucc o')).
intros.
apply TI_mono_eq; auto with *.
Qed.

Hint Resolve NATREC_dom_ext NATREC_dom_cont.

Require Import ZFrecbot.

Lemma NATREC'_rec o M U :
    typed_bot_recursor_hyps (TI NATf') U M o -> typed_bot_recursor_spec (TI NATf') U M (REC' M) o.
intros ok.
apply REC'_typed_bot_recursor_spec; auto with *.
Qed.

(** * Universe facts: NAT' belongs to any Grothendieck universes that
      is contains omega.
 *)

Section NAT'_Univ.

(* Universe facts *)
  Variable U : set.
  Hypothesis Ugrot : grot_univ U.

  Lemma G_NATf' X : X ∈ U -> NATf' X ∈ U.
intros.
assert (empty ∈ U).
 apply G_incl with X; trivial.
unfold NATf'.
apply G_sum; trivial.
 unfold ZFind_basic.UNIT.
 apply G_union2; trivial.
 apply G_singl; trivial.

 apply G_union2; trivial.
 apply G_singl; auto.
Qed.

  Lemma G_NAT' : omega ∈ U -> NAT' ∈ U.
intros.
apply G_TI; auto with *.
apply G_NATf'.
Qed.

End NAT'_Univ.
