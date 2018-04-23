Require Export basic.
Require Import ZF ZFpairs ZFsum ZFfix ZFnats ZFord ZFstable ZFrank ZFrelations.
Import ZFrepl.

(** Geeralized continuity *)

Definition continuous o F :=
  forall X, ext_fun o X -> F (sup o X) == sup o (fun z => F (X z)).

Section Convergence.

Variable o :set.
Hypothesis oo : limitOrd o.
Hypothesis F : set->set.
Hypothesis Fm : morph1 F.
Hypothesis Fcont : continuous o F.

Lemma Fcont_mono :
  (exists x, x ∈ o) -> Proper (incl_set==>incl_set) F.
do 2 red; intros.
destruct H as (w,?).
assert (wo : isOrd w).
 apply isOrd_inv with o; auto.
assert (d : ~ w == osucc w).
 intro.
 apply (lt_antirefl w); trivial.
 apply eq_elim with (osucc w); auto with *.
 apply lt_osucc; trivial.
pose (X:=fun o' => cond_set (o'==w) x ∪ cond_set (o'==osucc w) y).
assert (Xm : morph1 X).
 do 2 red; intros.
 unfold X.
 rewrite H1; reflexivity.
red; intros.
setoid_replace y with (sup o X).
 rewrite (Fcont X); auto with *.
 rewrite sup_ax.
 2:do 2 red; intros; apply Fm; auto with *.
 exists w; trivial.
 revert H1; apply eq_elim; apply Fm.
 unfold X; apply eq_set_ax; intros z'.
 rewrite union2_ax.
 rewrite cond_set_ax.
 rewrite cond_set_ax.
 split; auto with *.
 destruct 1 as [(?,?)|(?,?)]; trivial.
 contradiction.

 apply eq_set_ax; intros z'.
 rewrite sup_ax; auto with *.
 split; intros.
  exists (osucc w).
   apply oo; auto.
  revert H2; apply eq_elim.
  unfold X; apply eq_set_ax; intros z''.
  rewrite union2_ax.
  rewrite cond_set_ax.
  rewrite cond_set_ax.
  split; auto with *.
  destruct 1 as [(?,?)|(?,?)]; trivial.
  symmetry in H3; contradiction.

  destruct H2.
  apply union2_elim in H3; destruct H3; rewrite cond_set_ax in H3; destruct H3; auto. 
Qed.

Lemma cont_least_fix : F (TI F o) == TI F o.
rewrite TI_eq; auto.
red in Fcont.
rewrite Fcont; auto.
apply eq_set_ax; intros z.
rewrite sup_ax; auto.
2:do 2 red; intros; apply Fm; apply Fm; apply TI_morph; trivial.
rewrite sup_ax; auto.
split; destruct 1.
 exists (osucc x).
  apply oo; trivial.
  rewrite TI_mono_succ; trivial.
   apply Fcont_mono; eauto.
   apply isOrd_inv with o; auto.

 assert (isOrd x) by eauto using isOrd_inv.
 assert (Fmono : Proper (incl_set==>incl_set) F).
  apply Fcont_mono; eauto.
 exists x; trivial.
 rewrite <- TI_mono_succ; auto.
 revert H0; apply Fmono.
 apply TI_incl; auto.
Qed.

End Convergence.
(*
Section ConvergenceOmega.

Variable F :set -> set.
Hypothesis Fm : morph1 F.
Hypothesis Fcont : continuous N F.


Let Fmono : Proper (incl_set ==> incl_set) F.
do 2 red; intros.
pose (X:=natrec x (fun _ _ => y)).
assert (Xm : morph1 X).
 do 2 red; intros.
 unfold X.
 apply natrec_morph; auto with *.
 do 2 red; reflexivity.
red; intros.
setoid_replace y with (sup N X).
 rewrite (Fcont X); auto with *.
 rewrite sup_ax.
 2:do 2 red; intros; apply Fm; auto with *.
 exists zero; [apply zero_typ|].
 revert H0; apply eq_elim; apply Fm.
 unfold X; rewrite natrec_0; reflexivity.

 apply eq_set_ax; intros z'.
 rewrite sup_ax; auto with *.
 split; intros.
  exists (succ zero).
   apply succ_typ; apply zero_typ.
  revert H1; apply eq_elim.
  unfold X; rewrite natrec_S; auto with *.
   do 3 red; reflexivity.
   apply zero_typ.
  destruct H1.
  revert H2; apply N_ind with (4:=H1); intros.
   rewrite <- H3 in H5; auto.

   unfold X in H2; rewrite natrec_0 in H2; auto.

   unfold X in H4; rewrite natrec_S in H4; auto.
   do 3 red; reflexivity.
Qed.

  Let Data n := TI F (natrec zero (fun _=>osucc) n).

  Lemma Data_eq : TI F omega == sup N Data.
apply incl_eq.
 red; intros.
 apply TI_elim in H; auto.
 destruct H.
 rewrite sup_ax.
  exists (TI succ x).
apply isOrd_ind with (x:=x); intros.
2:apply isOrd_inv with omega; trivial.


 elim isOrd_omega using isOrd_ind; intros.
 red; intros.
 apply TI_elim in H2; auto with *.
 destruct H2.

; red; intros.
 revert 


elim isOrd_oemga 


  Let G n := TI F (nat2ordset n).

  Lemma G_incl_succ : forall k, G k ⊆ G (S k).
unfold G; simpl; intros.
apply TI_incl; auto with *.
Qed.

  Lemma G_eq : forall k, G (S k) == F (G k).
unfold G; simpl; intros.
apply TI_mono_succ; auto with *.
Qed.

  Lemma G_incl : forall k k', (k <= k')%nat -> G k ⊆ G k'.
induction 1; intros.
 red; auto.
 red; intros.
 apply (G_incl_succ m z); auto.
Qed.

  Lemma G_intro : forall k, G k ⊆ TI F omega.
unfold G; intros.
apply TI_incl; auto with *.
apply isOrd_sup_intro with (S k); simpl; auto.
apply lt_osucc; auto.
Qed.

  Lemma G_elim : forall x,
    x ∈ TI F omega -> exists k, x ∈ G k.
unfold G; intros.
apply TI_elim in H; auto with *.
destruct H.
apply isOrd_sup_elim in H; destruct H.
exists x1.
apply TI_intro with x0; auto with *.
Qed.

  Lemma G_fix : forall (P:set->Prop),
    (forall k,
     (forall k' x, (k' < k)%nat -> x ∈ G k' -> P x) ->
     (forall x, x ∈ G k -> P x)) ->
    forall x, x ∈ TI F omega -> P x.
intros.
apply G_elim in H0; destruct H0.
revert x H0.
Require Import Wf_nat.
elim (lt_wf x0); intros.
eauto.
Qed.

  Lemma List_eqn : TI F omega == F (TI F omega).
apply eq_intro; intros.
 apply G_elim in H; destruct H.
 apply G_incl_succ in H.
 rewrite G_eq in H.
 eapply Fmono with (G x); trivial.
 apply G_intro.

 elim H using LISTf_ind; intros.
  do 2 red; intros.
  rewrite H0; reflexivity.

  apply List_intro with 1; rewrite Lstn_eq.
  apply Nil_typ0; trivial.

  apply List_elim in H1; destruct H1 as (k,H1).
  apply List_intro with (S k); rewrite Lstn_eq.
  apply Cons_typ0; auto.
Qed.



Lemma cont_least_fix_omega : F (TI F omega) == TI F omega.
rewrite TI_eq; auto.
red in Fcont.
rewrite Fcont; auto.
apply eq_set_ax; intros z.
rewrite sup_ax; auto.
2:do 2 red; intros; apply Fm; apply Fm; apply TI_morph; trivial.
rewrite sup_ax; auto.
split; destruct 1.
 exists (osucc x).
  apply oo; trivial.
  rewrite TI_mono_succ; trivial.
   apply Fcont_mono; eauto.
   apply isOrd_inv with o; auto.

 assert (isOrd x) by eauto using isOrd_inv.
 assert (Fmono : Proper (incl_set==>incl_set) F).
  apply Fcont_mono; eauto.
 exists x; trivial.
 rewrite <- TI_mono_succ; auto.
 revert H0; apply Fmono.
 apply TI_incl; auto.
Qed.



End ConvergenceOmega.
*)
(** A small libary of continuous functions *)

Lemma cst_cont : forall X o, (exists y, lt y o) -> X == sup o (fun _ => X).
intros.
apply eq_intro; intros.
 rewrite sup_ax; trivial.
 destruct H as (y,?); exists y; trivial.

 rewrite sup_ax in H0; trivial.
 destruct H0; trivial.
Qed. 

Lemma sum_cont : forall o F G,
  ext_fun o F ->
  ext_fun o G ->
  sum (sup o F) (sup o G) == sup o (fun y => sum (F y) (G y)).
intros.
apply eq_intro; intros.
 rewrite sup_ax; auto.
 elim H1 using sum_ind; clear H1; intros.
  rewrite sup_ax in H1; auto.
  destruct H1.
  exists x0; trivial.
  rewrite H2; apply inl_typ; trivial.

  rewrite sup_ax in H1; auto.
  destruct H1.
  exists x; trivial.
  rewrite H2; apply inr_typ; trivial.

 rewrite sup_ax in H1; auto.
 destruct H1.
 apply sum_mono with (F x) (G x); auto.
Qed.

  Lemma sup_cont : forall o F G,
    ext_fun o F ->
    ext_fun o G ->
    sup o F ∪ sup o G == sup o (fun y => F y ∪ G y).
intros.
apply eq_set_ax; intros z.
rewrite union2_ax.
repeat rewrite sup_ax; auto with *.
 split; intros.
  destruct H1 as [(o',?,?)|(o',?,?)]; exists o'; trivial.
   apply union2_intro1; trivial.
   apply union2_intro2; trivial.

  destruct H1 as (o',?,?).
  apply union2_elim in H2; destruct H2;[left|right]; exists o'; trivial.

 do 2 red; intros; apply union2_morph; auto.
Qed.

  Lemma sigma_cont dom A f :
    morph2 f ->
    sigma A (fun x => sup dom (f x)) == sup dom (fun i => sigma A (fun x => f x i)).
intros.
assert (Hm : ext_fun dom (fun i => sigma A (fun x => f x i))).
 do 2 red; intros.
 apply sigma_morph; auto with *.
 red; intros; apply H; trivial.
apply eq_intro; intros.
 rewrite sup_ax; trivial.
 assert (snd z ∈ sup dom (f (fst z))).
  apply snd_typ_sigma with (2:=H0); auto with *.
  do 2 red; intros.
  apply sup_morph; auto with *.
  red; intros; apply H; trivial.
 rewrite sup_ax in H1.
 2:do 2 red; intros; apply H;auto with *.
 destruct H1.
 exists x; trivial.
 rewrite surj_pair with (1:=subset_elim1 _ _ _ H0).
 apply couple_intro_sigma; trivial.
  do 2 red; intros; apply H; auto with *.
 apply fst_typ_sigma in H0; trivial.

 rewrite sup_ax in H0; trivial.
 destruct H0.
 rewrite surj_pair with (1:=subset_elim1 _ _ _ H1).
 apply couple_intro_sigma; trivial.
  do 2 red; intros.
  apply sup_morph; auto with *.
  red; intros; apply H; trivial.

  apply fst_typ_sigma in H1; trivial.

  rewrite sup_ax.
  2:do 2 red; intros; apply H; auto with *.
  exists x; trivial.
  apply snd_typ_sigma with (2:=H1); auto with *.
  do 2 red; intros; apply H; auto with *.
Qed.

Section ProductContinuity.

  Hypothesis mu : set.
  Hypothesis mu_ord : isOrd mu.

  Variable X : set.
  Hypothesis X_small : bound_ord X mu. 
(*forall F,
    ext_fun X F ->
    (forall x, x ∈ X -> lt (F x) mu) ->
    lt (sup X F) mu.*)

  Lemma func_cont_gen : forall F,
    stable_ord F ->
    increasing F ->
    func X (sup mu F) ⊆ sup mu (fun A => func X (F A)).
intros F Fstb Fincr.
assert (Fm : forall o, isOrd o -> ext_fun o F) by auto.
red; intros.
pose (G := fun n => inter (subset mu (fun y => app z n ∈ F y))).
assert (Gm : ext_fun X G).
 red; red; intros.
 apply inter_morph.
 apply subset_morph; auto with *.
 red; intros.
 rewrite H1; reflexivity.
assert (Fprop : forall x, x ∈ X -> app z x ∈ F (G x) /\ lt (G x) mu).
  intros.
  apply app_typ with (x:=x) in H; trivial.
  rewrite sup_ax in H; auto.
  destruct H.
  split.
   apply Fstb; intros.
    apply subset_elim1 in H2; eauto using isOrd_inv.
   apply inter_intro.
    intros.
    rewrite replf_ax in H2.
     destruct H2.
     rewrite H3.
     rewrite subset_ax in H2; destruct H2.
     destruct H4.
     setoid_replace (F x1) with (F x2); trivial.
     apply Fm with mu; auto.

     red; red; intros.
     apply Fm with mu; auto.
     apply subset_elim1 in H3; trivial.

    exists (F x0).
    rewrite replf_ax.
     exists x0; auto with *.
     apply subset_intro; trivial.

     red; red; intros.
     apply Fm with mu; auto.
     apply subset_elim1 in H2; trivial.

   apply isOrd_plump with x0; auto.
    apply isOrd_inter; intros.
    apply subset_elim1 in H2; eauto using isOrd_inv.

    red; intros.
    apply inter_elim with (1:=H2).
    apply subset_intro; trivial.
assert (Fmu := fun x h => proj2 (Fprop x h)).
assert (Fspec := fun x h => proj1 (Fprop x h)).
clear Fprop.
assert (Ford : forall x, x ∈ X -> isOrd (G x)).
 intros.
 apply isOrd_inv with mu; auto.
rewrite sup_ax; auto.
assert (lt (osup X G) mu) by (apply X_small; trivial).
exists (osup X G); trivial.
apply func_narrow with (1:=H); intros.
apply Fincr with (G x); auto.
 apply isOrd_osup; auto.

 apply osup_intro; trivial.
Qed.


  Hypothesis mu_bound : lt (osup (func X mu) (fun f => osup X (app f))) mu.


  Lemma func_bound : bound_ord X mu.
red; intros.
apply isOrd_plump with (4:=mu_bound); auto.
 apply isOrd_osup; auto.
 intros.
 apply isOrd_inv with mu; auto.

 red; intros.
 apply osup_intro with (x:=lam X F).
  do 2 red; intros.
  apply osup_morph; auto with *.
  red; intros.
  apply app_morph; trivial.

  apply lam_is_func; auto.

  apply eq_elim with (2:=H1).
  apply osup_morph; auto with *.
  red; intros.
  rewrite beta_eq; auto.
  rewrite <- H3; trivial.
Qed.
(*
Goal lt_cardf X mu.
red ;intros.
assert (exG : exists2 G,
  ext_fun X G &
  (forall x, x ∈ X -> lt (G x) mu) /\
  forall x, x ∈ X -> lt (F x) mu -> F x == G x).
 exists (fun x => subset (F x) (fun _ => lt (F x) mu)).
  admit.

  split; intros.
  assert (lt (F x) mu \/ ~ lt (F x) mu).
   admit. (*EM*)
  destruct H1.
   setoid_replace (subset (F x) (fun _ => lt (F x) mu)) with (F x); auto.
   apply eq_intro; intros.
    apply subset_elim1 in H2; trivial.

    apply subset_intro; trivial.

   setoid_replace (subset (F x) (fun _ => lt (F x) mu)) with empty.
    admit. (* mu at least one *)

    apply empty_ext.
    red; intros.
    apply subset_elim2 in H2; destruct H2.
    auto.

   apply eq_intro; intros.
    apply subset_intro; trivial.

    apply subset_elim1 in H2; trivial.
destruct exG as (G, eG, (bG, eFG)).
pose (l := sup X G).
assert (isOrd l).
 apply isOrd_supf; trivial.
 intros.
 apply isOrd_inv with mu; auto.
assert (ll : osucc l ∈ mu).
 assert (l ∈ mu).
  apply X_small; trivial.
 admit. (* mu limit *)
exists (osucc l); trivial.
red; intros.
assert (F x ⊆ l).
 red; intros.
 unfold l; rewrite sup_ax; trivial.
 exists x; trivial.
 rewrite <- eFG; trivial.
 rewrite <- H2; trivial.
apply (lt_antirefl l); trivial.
apply oles_lt; trivial.
rewrite H2; trivial.
Qed.
*)

End ProductContinuity.

(* Case when mu is a regular ordinal *)
(*
Lemma func_cont : forall mu X F,
  isOrd mu ->
  VN_regular mu ->
  omega ∈ mu ->
  stable_ord F ->
  increasing F ->
  X ∈ VN mu ->
  func X (sup mu F) == sup mu (fun x => func X (F x)).
intros mu X F mu_ord mu_reg mu_inf Fstb Fincr Fsmall.
apply eq_intro; intros.
 apply func_cont_gen; trivial.
 red; intros; apply VN_reg_ord; auto.

 rewrite sup_ax in H; auto.
 destruct H.
 apply func_mono with X (F x); auto.
 reflexivity.
Qed.
*)