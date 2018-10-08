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

(** Recursor on W *)

Require Import ZFfunext ZFfixrec.

Definition WREC' M :=
  WREC (fun o' f => squash (M o' f)).

Section Recursor.

  Hypothesis O : set.
  Hypothesis Oo : isOrd O.
  Variable M : set->set->set.
  Hypothesis Mm : morph2 M.
  Variable U : set->set->set.
  Hypothesis Um : morph2 U.
  Hypothesis Ubot : forall o x, empty ∈ U o x.

  Let Wi o := cc_bot (TI W_F' o).
  Let F := fun o' f => squash (M o' f).
  Let Q o f := forall x, x ∈ TI W_F' o -> cc_app f x ∈ U o x.

  Hypothesis ty_M :
    forall o', o' ∈ osucc O -> forall f, f ∈ cc_prod (Wi o') (U o') ->
    M o' f ∈ cc_prod (Wi (osucc o')) (U (osucc o')).

  Hypothesis stab : forall o' o'' f g,
    isOrd o' -> o' ⊆ o'' -> o'' ∈ osucc O ->
    f ∈ cc_prod (Wi o') (U o') ->
    g ∈ cc_prod (Wi o'') (U o'') ->
    fcompat (Wi o') f g ->
    fcompat (Wi (osucc o')) (M o' f) (M o'' g).

  Instance morph_fix_body : morph2 F.
unfold F; do 3 red; intros.
apply squash_morph.
apply Mm; trivial.
Qed.
  Lemma ext_fun_ty : forall o,
    ext_fun (Wi o) (U o).
do 2 red; intros.
apply Um; auto with *.
Qed.

  Hypothesis fx_sub_U : forall o' o'' x,
    isOrd o' -> o' ⊆ o'' -> o'' ∈ osucc O ->
    x ∈ Wi o' ->
    U o' x ⊆ U o'' x.

Lemma wnot_mt o :
  isOrd o ->
  ~ empty ∈ TI W_F' o.
intros oo h; apply mt_not_in_W_F' in h; auto with *.
Qed.

Lemma wprod_ext_mt o f :
  isOrd o ->
  f ∈ cc_prod (TI W_F' o) (U o) ->
  f ∈ cc_prod (Wi o) (U o).
intros oo fty.
apply cc_prod_ext_mt in fty; trivial.
 apply ext_fun_ty.

 apply wnot_mt; trivial.
Qed.

  Lemma ty_fix_body : forall o f,
   o < osucc O ->
   f ∈ cc_prod (TI W_F' o) (U o) ->
   F o f ∈ cc_prod (TI W_F' (osucc o)) (U (osucc o)).
unfold F; intros.
apply squash_typ.
 apply ext_fun_ty.

 apply wnot_mt.
 eauto using isOrd_inv.

 apply ty_M with (1:=H); trivial.
 apply wprod_ext_mt in H0; trivial.
 simpl; eauto using isOrd_inv. 
Qed.

  Lemma fix_body_irrel : forall o o' f g,
    isOrd o' -> o' ⊆ O -> isOrd o -> o ⊆ o' ->
    f ∈ cc_prod (TI W_F' o) (U o) ->
    g ∈ cc_prod (TI W_F' o') (U o') ->
    fcompat (TI W_F' o) f g ->
    fcompat (TI W_F' (osucc o)) (F o f) (F o' g).
red; intros.
assert (o'typ : o' ∈ osucc O).
 apply ole_lts; trivial.
assert (o0typ : o ∈ osucc O).
 apply le_lt_trans with o'; auto.
 apply ole_lts; trivial.
unfold F.
rewrite squash_eq.
3:apply ty_M; trivial.
2:apply wnot_mt; auto.
2:apply wprod_ext_mt; trivial.
rewrite squash_eq.
3:apply ty_M; trivial.
2:apply wnot_mt; auto.
2:apply wprod_ext_mt; trivial.
assert (fext : forall A f, ext_fun A (cc_app f)).
 do 2 red; intros; apply cc_app_morph; auto with *.
rewrite cc_beta_eq; trivial.
rewrite cc_beta_eq; trivial.
 apply stab; trivial.
  apply wprod_ext_mt; trivial.
  apply wprod_ext_mt; trivial.

  red; intros.
  unfold Wi in H7; rewrite cc_bot_ax in H7.
  destruct H7; auto.
  rewrite H7.
  rewrite cc_app_outside_domain.
   rewrite cc_app_outside_domain; auto with *.
    rewrite cc_eta_eq with (1:=H4).
    apply is_cc_fun_lam; trivial.

    apply wnot_mt; trivial.

   rewrite cc_eta_eq with (1:=H3).
   apply is_cc_fun_lam; trivial.

   apply wnot_mt; trivial.

  apply cc_bot_intro; trivial.

  revert H6; apply TI_mono; auto with *.
  apply osucc_mono; trivial.
Qed.

  Let Qty o f :
    isOrd o ->
    (is_cc_fun (TI W_F' o) f /\ Q o f <-> f ∈ cc_prod (TI W_F' o) (U o)).
split; intros.
 destruct H0.
 rewrite cc_eta_eq' with (1:=H0).
 apply cc_prod_intro; auto.
  do 2 red; intros; apply cc_app_morph; auto with *.

  do 2 red; intros; apply Um; auto with *.

 split.
  rewrite cc_eta_eq with (1:=H0).
  apply is_cc_fun_lam.
  do 2 red; intros; apply cc_app_morph; auto with *.

  red; intros.
  apply cc_prod_elim with (1:=H0); trivial.
Qed.

  Hint Resolve morph_fix_body ext_fun_ty.

  Lemma WREC'_recursor o :
    isOrd o -> o ⊆ O -> recursor o (TI W_F') Q F.
split; intros; trivial.
 apply TI_morph; auto.

 rewrite TI_eq; auto with *.
 apply sup_morph;[reflexivity|red; intros].
 symmetry; rewrite <- H3; apply TI_mono_succ; auto with *.
 eauto using isOrd_inv.

 (* Q ext *)
 red; intros.
 rewrite <- H3.
 rewrite <- H3 in H6.
 red in H4.
 rewrite <- H4; auto.

 (* Q cont *)
 red; intros.
 apply TI_inv in H5; auto with *.
 destruct H5 as (o',?,?).
 red in H4; specialize H4 with (1:=H5) (2:=H6).
 revert H4; apply fx_sub_U; eauto using isOrd_inv with *.
  red; intros; apply le_lt_trans with o'; auto.

  apply ole_lts; trivial.
  transitivity o; trivial.

  unfold Wi; auto.

 (* F typing *)
 apply Qty; auto.
 apply ty_fix_body.
  apply ole_lts; auto.
  transitivity o; trivial.

  apply Qty; auto.

 (* F irr *)
 red; intros.
 destruct H3 as (?,fty).
 destruct H4 as (?,gty).
 apply Qty in fty; trivial.
 apply Qty in gty; trivial.
 apply fix_body_irrel; auto with *.
 transitivity o; trivial.
Qed.


Let fix_typ0 o :
  isOrd o ->
  o ⊆ O ->
  WREC' M o ∈ cc_prod (TI W_F' o) (U o).
intros.
destruct REC_wt with (1:=H) (2:=WREC'_recursor _ H H0).
apply Qty; auto.
Qed.

  Lemma WREC'_typ o:
    isOrd o ->
    o ⊆ O ->
    WREC' M o ∈ cc_prod (Wi o) (U o).
intros.
apply wprod_ext_mt; trivial.
apply fix_typ0 with (1:=H); trivial.
Qed.
Hint Resolve WREC'_typ.


  Lemma WREC'_strict o :
    isOrd o ->
    o ⊆ O ->
    cc_app (WREC' M o) empty == empty.
intros.
eapply cc_app_outside_domain.
 rewrite cc_eta_eq with (f:=WREC' M o).
  eapply is_cc_fun_lam.
  do 2 red; intros; apply cc_app_morph; auto with *.

  apply fix_typ0; trivial.

 apply wnot_mt; trivial.
Qed.

  Lemma WREC'_irr o o' x :
    isOrd o ->
    isOrd o' ->
    o ⊆ o' ->
    o' ⊆ O ->
    x ∈ Wi o ->
    cc_app (WREC' M o) x == cc_app (WREC' M o') x.
intros.
apply cc_bot_ax in H3; destruct H3.
 rewrite H3.
 rewrite WREC'_strict; trivial.
 2:transitivity o'; trivial.
 rewrite WREC'_strict; auto with *.

 apply REC_ord_irrel with (1:=H0) (2:=WREC'_recursor _ H0 H2); auto with *.
Qed.

Lemma fix_eqn0 : forall o,
  isOrd o ->
  o ⊆ O ->
  WREC' M (osucc o) == F o (WREC' M o).
intros.
unfold WREC', WREC at 1; fold F.
rewrite REC_eq; auto with *.
rewrite eq_set_ax; intros z.
rewrite sup_ax; auto with *.
split; intros.
 destruct H1 as (o',o'lt,zty).
 change (z ∈ F o (WREC' M o)).
 change (z ∈ F o' (WREC' M o')) in zty.
 assert (o'o : isOrd o') by eauto using isOrd_inv.
 assert (o'le : o' ⊆ o) by (apply olts_le; auto).
 assert (o'le' : o' ⊆ O) by (transitivity o; trivial).
 assert (F o' (WREC' M o') ∈ cc_prod (TI W_F' (osucc o')) (U (osucc o'))).
  apply ty_fix_body; auto.
  apply ole_lts; auto.
 assert (F o (WREC' M o) ∈ cc_prod (TI W_F' (osucc o)) (U (osucc o))).
  apply ty_fix_body; auto.
  apply ole_lts; auto.
 rewrite cc_eta_eq with (1:=H1) in zty.
 rewrite cc_eta_eq with (1:=H2).
 rewrite cc_lam_def in zty|-*.
 2:intros ? ? _ eqn; rewrite eqn; reflexivity.
 2:intros ? ? _ eqn; rewrite eqn; reflexivity.
 destruct zty as (n', n'ty, (y, yty, eqz)).
 exists n'.
  revert n'ty; apply TI_mono; auto with *.
  apply osucc_mono; auto.
 exists y; trivial.
 revert yty; apply eq_elim.
 apply fix_body_irrel; auto with *.
 red; intros.
 apply WREC'_irr; auto.
 apply cc_bot_intro; trivial.

 exists o;[apply lt_osucc;trivial|trivial].
Qed.


Lemma WREC'_unfold : forall o n,
  isOrd o ->
  o ⊆ O ->
  n ∈ TI W_F' (osucc o) ->
  cc_app (WREC' M (osucc o)) n ==
  cc_app (M o (WREC' M o)) n.
intros.
rewrite fix_eqn0 with (1:=H); trivial.
unfold F.
rewrite squash_beta with (3:=H1).
 reflexivity.

 apply wnot_mt; auto.

 apply ty_M; auto.
 apply ole_lts; trivial.
Qed.



Lemma WREC'_typ_app o n:
  isOrd o ->
  o ⊆ O ->
  n ∈ Wi o ->
  cc_app (WREC' M o) n ∈ U o n.
intros.
apply cc_prod_elim with (dom:=Wi o); trivial.
apply WREC'_typ; trivial.
Qed.

Lemma WREC'_eqn : forall o n,
  isOrd o ->
  o ⊆ O ->
  n ∈ TI W_F' o ->
  cc_app (WREC' M o) n ==
  cc_app (M o (WREC' M o)) n.
intros.
apply TI_inv in H1; auto with *.
destruct H1 as (o',?,?).
assert (o'o: isOrd o') by eauto using isOrd_inv.
rewrite <- WREC'_irr with (o:=osucc o'); auto.
 rewrite WREC'_unfold; auto.
 eapply stab; auto.
  apply ole_lts; auto.

  red; intros.
  apply WREC'_irr; auto.

  apply cc_bot_intro; trivial.

 red; intros; apply le_lt_trans with o'; trivial.

 apply cc_bot_intro; trivial.
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
Qed.

  Lemma G_W_ord' : W_ord' ∈ U.
unfold W_ord'.
apply G_Ffix_ord; auto.
apply G_Wdom; trivial.
Qed.

End W_Univ.

End W_theory.
