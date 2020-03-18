Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFord ZFfix ZFstable.
Require Import ZFgrothendieck.
Require Import ZFlist ZFcoc.
Import ZFrepl.
Require Export ZFind_w.

(** In this file we develop an alternative model of W-types where all stages are non-empty
 *)

Section W_theory.

(** * Definition and properties of the W-type operator *)

Variable A : set.
Variable B : set -> set.
Hypothesis Bm : morph1 B.

Local Notation WF := (W_F A B).
Local Notation Wd := (Wdom A B).

(** The type operator on the construction domain
    (extended with bottom value) *)

  Lemma Wdom_cc_bot X :
    X ⊆ Wd -> cc_bot X ⊆ Wd.
red; intros.
apply cc_bot_ax in H0; destruct H0; auto.
rewrite H0; apply power_intro; intros.
apply empty_ax in H1; contradiction.
Qed.

  Definition W_F' X := W_F A B (cc_bot X).

  Instance W_F'_mono : Proper (incl_set==>incl_set) W_F'.
do 2 red; intros.
unfold W_F'; apply W_F_mono; trivial.
apply cc_bot_mono; auto with *.
Qed.

Lemma Wsup_ext' : forall X, ext_fun (W_F' X) (Wsup B).
intros; unfold W_F'; apply Wsup_ext; trivial.
Qed.
Hint Resolve Wsup_ext'.

Definition Wf' X := Wf A B (cc_bot X).

Instance Wf_mono' : Proper (incl_set ==> incl_set) Wf'.
do 2 red; intros.
unfold Wf'; apply Wf_mono; trivial.
apply cc_bot_mono; trivial.
Qed.

Instance Wf_morph' : morph1 Wf'.
apply Fmono_morph; auto with *.
Qed.
Hint Resolve Wf_mono' Wf_morph'.

Lemma Wsup_inj' : forall X Y x x',
  X ⊆ Wd ->
  Y ⊆ Wd ->
  x ∈ W_F' X ->
  x' ∈ W_F' Y ->
  Wsup B x == Wsup B x' -> x == x'.
intros X Y x x' tyf tyf' H H0 H1.
apply Wsup_inj with (4:=H) (5:=H0) (6:=H1); trivial.
 apply Wdom_cc_bot; trivial.
 apply Wdom_cc_bot; trivial.
Qed.

Lemma Wsup_typ_gen' : forall X x,
  X ⊆ Wd ->
  x ∈ W_F' X ->
  Wsup B x ∈ Wd.
intros.
apply Wsup_typ_gen with (3:=H0); trivial.
apply Wdom_cc_bot; trivial.
Qed.

Lemma Wf_typ' : forall X,
  X ⊆ Wd -> Wf' X ⊆ Wd.
intros.
unfold Wf'; apply Wf_typ; trivial.
apply Wdom_cc_bot; trivial.
Qed.
Hint Resolve Wf_typ'.

Lemma W_F_Wf_iso'' X :
  X ⊆ Wd ->
  iso_fun (W_F' X) (Wf' X) (Wsup B).
split; intros.
 apply Wsup_morph; trivial.

 red; intros.
 apply Wf_intro; trivial.

 apply Wsup_inj' with X X; auto.

 unfold Wf' in H0; apply Wf_elim in H0; trivial.
 destruct H0; eauto with *.
Qed.

Lemma TI_Wf_typ' o :
  isOrd o ->
  TI Wf' o ⊆ Wd.
induction 1 using isOrd_ind; intros.
red; intros.
apply TI_elim in H2; auto.
destruct H2.
revert H3; apply Wf_typ'; auto.
Qed.


  Lemma mt_not_in_W_F' o x :
    isOrd o ->
    x ∈ TI W_F' o ->
    ~ x == empty.
red; intros.
apply TI_elim in H0; auto with *.
destruct H0 as (o',?,?).
unfold W_F' in H2.
apply W_F_elim in H2; trivial.
destruct H2 as (_,(_,?)).
rewrite H2 in H1.
symmetry in H1; apply discr_mt_couple in H1; trivial.
Qed.

  Lemma mt_not_in_Wf' o x :
    isOrd o ->
    x ∈ TI Wf' o ->
    ~ x == empty.
red; intros.
apply TI_elim in H0; auto with *.
destruct H0 as (o',?,?).
unfold Wf' in H2; apply Wf_elim in H2; trivial.
destruct H2 as (w,_,?).
rewrite H2 in H1; apply empty_ax with (couple Nil (fst w)).
rewrite <- H1.
apply union2_intro1.
apply singl_intro.
Qed.

Lemma cc_bot_stable :
  stable_class (fun X => X ⊆ Ffix Wf' Wd) cc_bot.
unfold cc_bot; apply union2_stable_disjoint.
 do 2 red; reflexivity.

 do 2 red; trivial.

 apply cst_stable_class.

 apply id_stable_class.

 intros.
 apply singl_elim in H1.
 rewrite H1 in H2; apply H0 in H2.
 rewrite Ffix_def in H2; auto.
 destruct H2.
 apply mt_not_in_Wf' in H3; auto with *.
Qed.

Lemma W_F_stable' : stable_class (fun X => X ⊆ Ffix Wf' Wd) W_F'.
apply compose_stable_class with (F:=WF) (K1:=fun _ => True); trivial.
 do 2 red; reflexivity.

 apply W_F_mono; trivial.

 apply cc_bot_morph.

 apply W_F_stable; trivial.

 apply cc_bot_stable.
Qed.

Lemma Wf_stable' : stable_class (fun X => X ⊆ Ffix Wf' Wd) Wf'.
apply compose_stable_class with (F:=Wf A B) (K1:=fun X => X ⊆ cc_bot (Ffix Wf' Wd)); trivial.
 do 2 red; intros.
 rewrite H; reflexivity.

 apply Wf_mono; trivial.

 apply cc_bot_morph.

 apply Wf_stable0; intros; trivial.
 rewrite H.
 apply Wdom_cc_bot.
 apply Ffix_inA.

 apply cc_bot_stable.

 intros; apply cc_bot_mono; trivial.
Qed.

  Definition W_ord' := Ffix_ord Wf' Wd.

Lemma W_F_Wf_iso''' o f :
  isOrd o ->
  iso_fun (TI W_F' o) (TI Wf' o) f ->
  iso_fun (W_F' (TI W_F' o)) (Wf' (TI Wf' o)) (wiso B (fbot f)).
intros.
apply iso_fun_trans with (W_F' (TI Wf' o)).
 unfold W_F' at 1 3; apply WFmap_iso; trivial.
 apply iso_cc_bot; trivial.
  intro h; apply mt_not_in_W_F' in h; auto with *.
  intro h; apply mt_not_in_Wf' in h; auto with *.

 apply W_F_Wf_iso''.
 apply TI_Wf_typ'; trivial.
Qed.

Lemma wisobot_ext : forall X f f',
  ~ empty ∈ X ->
  eq_fun X f f' -> eq_fun (W_F' X) (wiso B (fbot f)) (wiso B (fbot f')).
red; intros.
unfold wiso,comp_iso.
assert (eqbot : eq_fun (cc_bot X) (fbot f) (fbot f')).
 apply eqf_fbot; trivial.
apply Wsup_morph; trivial.
apply WFmap_ext with (A:=A); intros; trivial.
 apply W_F_elim with (2:=H1); trivial.

 rewrite H2; reflexivity.

 apply eqbot.
 apply W_F_elim with (2:=H1); trivial.

 rewrite H2; rewrite H4; reflexivity.
Qed.

Let wisobotm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) (fun f => wiso B (fbot f)).
do 3 red; intros.
apply wisom; trivial.
unfold fbot; red; intros.
apply cond_set_morph; auto.
rewrite H1; reflexivity.
Qed.

Lemma TI_W_F_Wf_iso' o :
  isOrd o ->
  iso_fun (TI W_F' o) (TI Wf' o) (TI_iso W_F' (fun f => wiso B (fbot f)) o).
intros.
apply TI_iso_fun; intros; auto.
 unfold W_F'; do 2 red; intros; apply W_F_mono; trivial.
 apply cc_bot_mono; trivial.

 apply wisobot_ext; trivial.
 intros h; apply mt_not_in_W_F' in h; auto with *.

 apply W_F_Wf_iso'''; trivial.
Qed.

  Lemma W_fix' :
    TI W_F' W_ord' == W_F' (TI W_F' W_ord').
rewrite TI_iso_fixpoint with (2:=Wf_mono') (g:=fun f => wiso B (fbot f)); trivial.
 apply TI_clos_fix_eqn; auto.
 apply Wf_stable'.

 apply W_F'_mono.

 intros.
 apply wisobot_ext; trivial.
 intros h; apply mt_not_in_W_F' in h; auto with *.

 apply W_F_Wf_iso'''.

 apply Ffix_o_o; trivial.
 apply Wf_typ'.
Qed.

  Lemma W_stages' o :
    isOrd o ->
    TI W_F' o ⊆ TI W_F' W_ord'.
induction 1 using isOrd_ind; intros.
red; intros.
apply TI_elim in H2; auto with *.
destruct H2 as (o',?,?).
rewrite W_fix'.
revert H3; apply W_F'_mono; auto.
Qed.


(** * Universe facts: when A and B belong to a given (infinite) universe, then so does W(A,B). *)

Section W_Univ.

(* Universe facts *)
  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : omega ∈ U.  

  Hypothesis aU : A ∈ U.
  Hypothesis bU : forall a, a ∈ A -> B a ∈ U.

  Lemma G_W_F' X : X ∈ U -> W_F' X ∈ U.
intros.
unfold W_F'.
apply G_W_F; trivial.
apply G_union2; trivial.
apply G_singl; trivial.
apply G_incl with X; trivial.
Qed.

  Lemma G_W_ord' : W_ord' ∈ U.
unfold W_ord'.
apply G_Ffix_ord; auto.
apply G_Wdom; trivial.
Qed.

End W_Univ.

End W_theory.
