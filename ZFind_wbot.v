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
symmetry in H1; apply discr_mt_pair in H1; trivial.
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

(** Recursor on W *)

Require Import ZFfunext ZFfixrec.

Section Recursor.

  Variable ord : set.
  Hypothesis oord : isOrd ord.

  Variable F : set -> set -> set.
  Hypothesis Fm : morph2 F.

  Variable U' : set -> set -> set.
  Hypothesis U'mono : forall o o' x x',
    isOrd o' -> o' ⊆ ord -> isOrd o -> o ⊆ o' ->
    x ∈ TI W_F' o -> x == x' ->
    U' o x ⊆ U' o' x'.

  Let Ty' o := cc_prod (TI W_F' o) (U' o).
  Let Q' o f := forall x, x ∈ TI W_F' o -> cc_app f x ∈ U' o x.

  Hypothesis Ftyp' : forall o f, isOrd o -> o ⊆ ord ->
    f ∈ Ty' o -> F o f ∈ Ty' (osucc o).

  Definition Wi_ord_irrel' :=
    forall o o' f g,
    isOrd o' -> o' ⊆ ord -> isOrd o -> o ⊆ o' ->
    f ∈ Ty' o -> g ∈ Ty' o' ->
    fcompat (TI W_F' o) f g ->
    fcompat (TI W_F' (osucc o)) (F o f) (F o' g).

  Hypothesis Firrel' : Wi_ord_irrel'.

Lemma U'morph : forall o o', isOrd o' -> o' ⊆ ord -> o == o' ->
    forall x x', x ∈ TI W_F' o -> x == x' -> U' o x == U' o' x'. 
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

Lemma U'ext : forall o, isOrd o -> o ⊆ ord -> ext_fun (TI W_F' o) (U' o).
red; red; intros.
apply U'morph; auto with *.
Qed.


  Lemma WREC_typing' : forall o f, isOrd o -> o ⊆ ord -> 
    is_cc_fun (TI W_F' o) f -> Q' o f -> f ∈ Ty' o.
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
   o == o' -> forall f f', fcompat (TI W_F' o) f f' -> Q' o f -> Q' o' f'.
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
 is_cc_fun (TI W_F' o) f ->
 (forall o' : set, o' ∈ o -> Q' (osucc o') f) -> Q' o f.
intros.
red; intros.
apply TI_elim in H3; auto with *.
destruct H3.
rewrite <- TI_mono_succ in H4; eauto using isOrd_inv.
2:apply W_F'_mono.
generalize (H2 _ H3 _ H4).
apply U'mono; eauto using isOrd_inv with *.
red; intros.
apply isOrd_plump with x0; eauto using isOrd_inv.
apply olts_le in H5; trivial.
Qed.

Let Q'typ : forall o f,
 isOrd o ->
 o ⊆ ord ->
 is_cc_fun (TI W_F' o) f ->
 Q' o f -> is_cc_fun (TI W_F' (osucc o)) (F o f) /\ Q' (osucc o) (F o f).
intros.
assert (F o f ∈ Ty' (osucc o)).
 apply Ftyp'; trivial.
 apply WREC_typing'; trivial.
split.
 apply cc_prod_is_cc_fun in H3; trivial.

 red; intros.
 apply cc_prod_elim with (1:=H3); trivial.
Qed.

  Lemma WREC_recursor' : recursor ord (TI W_F') Q' F.
split; auto.
 apply TI_morph.

 intros.
 apply TI_mono_eq; auto with *.

 red; red; intros.
 destruct H1 as (oo,(ofun,oty)); destruct H2 as (o'o,(o'fun,o'ty)).
 apply Firrel'; trivial.
  apply WREC_typing'; trivial. 
  transitivity o'; trivial.

  apply WREC_typing'; trivial. 
Qed.

  Lemma WREC_wt' : WREC F ord ∈ Ty' ord.
intros.
destruct REC_wt with (1:=oord) (2:=WREC_recursor').
apply WREC_typing'; auto with *.
Qed.

  Lemma WREC_ind' : forall P x,
    Proper (eq_set==>eq_set==>eq_set==>iff) P ->
    (forall o x, isOrd o -> lt o ord ->
     x ∈ W_F' (TI W_F' o) ->
     (forall y, y ∈ TI W_F' o -> P o y (cc_app (WREC F ord) y)) ->
     forall w, isOrd w -> w ⊆ ord -> lt o w ->
     P w x (cc_app (F ord (WREC F ord)) x)) ->
    x ∈ TI W_F' ord ->
    P ord x (cc_app (WREC F ord) x).
intros.
unfold WREC.
apply REC_ind with (2:=WREC_recursor'); auto.
intros.
apply TI_elim in H4; auto with *.
destruct H4 as (o',?,?).
apply H0 with o'; eauto using isOrd_inv.
red; auto.
Qed.

  Lemma WREC_expand' : forall n,
    n ∈ TI W_F' ord -> cc_app (WREC F ord) n == cc_app (F ord (WREC F ord)) n.
intros.
apply REC_expand with (2:=WREC_recursor') (Q:=Q'); auto.
Qed.

  Lemma WREC_irrel' o o' :
    isOrd o ->
    isOrd o' ->
    o ⊆ o' ->
    o' ⊆ ord ->
    eq_fun (TI W_F' o) (cc_app (WREC F o)) (cc_app (WREC F o')).
red; intros.
rewrite <- H4.
apply REC_ord_irrel with (2:=WREC_recursor'); auto with *.
Qed.


End Recursor.

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
red; intros z ?; elim empty_ax with z; trivial.
Qed.

  Lemma G_W_ord' : W_ord' ∈ U.
unfold W_ord'.
apply G_Ffix_ord; auto.
apply G_Wdom; trivial.
Qed.

End W_Univ.

End W_theory.
