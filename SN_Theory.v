Require Import InstInterp.
Require Import Esub.

Import InstSyn InstSem ModelTheory.
Import SN_CC_Real.
Import List.
Import GenLemmas.
Import ZF SN CCSN.

(*SN for the theory*)
Module SN_Theory (M1 : TheorySyn) (M2 : TheorySem) (M3 : InterpTheory M1 M2).

Import M1 M2 M3.

Fixpoint const_hyp n : list (option foformula) :=
  match n with
    |0 => nil
    |S m => None :: (const_hyp m)
  end.

Lemma intp_hyp_env_const : forall n,
  intp_hyp (const_hyp n) = const_env n.
induction n; simpl.
 rewrite intp_nil; rewrite const_env0; trivial.

 rewrite intp_hyp_cons_sort. rewrite const_envS.
 rewrite IHn; reflexivity.
Qed.

Lemma hyp_ok_eq_trm : forall x y hyp,
  hyp_ok_fml hyp (eq_fotrm x y) ->
  hyp_ok_trm hyp x /\ hyp_ok_trm hyp y.
unfold hyp_ok_fml, hyp_ok_trm.
split; intros; apply H; rewrite fv_fml_eq_trm; 
  rewrite in_app_iff; [left|right]; trivial.
Qed.

Lemma intp_sound : forall hyp P, deriv hyp P -> 
  exists p, typ ((intp_hyp hyp)) p (intp_fofml P).
induction 1; simpl.
(*hyp*)
 exists (Ref n); red; simpl; intros. unfold val_ok in H1.
 rewrite <- lift_intp_lift_fml. apply H1. apply intp_hyp_nth_fml; trivial.

(*ax_intro*)
 apply intp_ax; trivial.

(*true_intro*)
 rewrite intp_TF. apply True_symb_intro.
 
(*false_elim*)
 destruct IHderiv. exists (App x (intp_fofml f)).
 apply False_symb_elim; [rewrite intp_BF in H1|apply intp_fofml_prop]; trivial.

(*neg_intro*)
 destruct IHderiv as (p, IH). exists p.
 rewrite intp_neg. rewrite intp_implf in IH. rewrite intp_BF in IH.
 apply Neg_intro; trivial.

(*neg_elim*)
 destruct IHderiv. exists x. 
 rewrite intp_neg in H0. rewrite intp_implf. rewrite intp_BF.
 apply Neg_elim; trivial.

(*conj_intro*)
 destruct IHderiv1 as (x, IH1). 
 destruct IHderiv2 as (x', IH2).
 rewrite intp_conj.
 apply Conj_intro with (u:=x) (v:=x'); [apply intp_fofml_prop; apply deriv_well_typed
   |apply intp_fofml_prop; apply deriv_well_typed|split]; trivial.

(*conj_elim1*)
 destruct IHderiv as (t, IH). rewrite intp_conj in IH.
 apply deriv_well_typed in H.
 apply Conj_elim1 with (B:=(intp_fofml f2)) (t:=t); 
   [apply intp_fofml_prop|apply intp_fofml_prop|trivial];
   red in H |- *; intros; apply H; rewrite fv_fml_conj; rewrite in_app_iff;
     [left|right]; trivial.
 
(*conj_elim2*)
 destruct IHderiv as (t, IH). rewrite intp_conj in IH.
 apply deriv_well_typed in H.
 apply Conj_elim2 with (A:=(intp_fofml f1)) (t:=t); 
   [apply intp_fofml_prop|apply intp_fofml_prop|trivial];
   red in H |- *; intros; apply H; rewrite fv_fml_conj; rewrite in_app_iff;
     [left|right]; trivial.
 
(*disj_intro1*)
 destruct IHderiv. rewrite intp_disj.
 apply Disj_intro1 with (t:=x); [apply intp_fofml_prop; apply deriv_well_typed
   |apply intp_fofml_prop|]; trivial.
 
(*disj_intro2*)
 destruct IHderiv. rewrite intp_disj.
 apply Disj_intro2 with (t:=x); [apply intp_fofml_prop
   |apply intp_fofml_prop; apply deriv_well_typed|]; trivial.

(*disj_elim*)
 destruct IHderiv1, IHderiv2, IHderiv3.
 rewrite intp_disj in H2. rewrite intp_hyp_cons_fml in H3, H4.
 apply deriv_well_typed in H. apply deriv_well_typed in H0.
 apply hyp_ok_weakening in H0.
 apply Disj_elim with (t:=x) (t1:=x0) (t2:=x1) (A:=intp_fofml f1) (B:=intp_fofml f2);
   [apply intp_fofml_prop|apply intp_fofml_prop|apply intp_fofml_prop
     | |rewrite lift_intp_lift_fml|rewrite lift_intp_lift_fml]; trivial;
   red in H |- *; intros; apply H; rewrite fv_fml_disj;
     rewrite in_app_iff; [left|right]; trivial.

(*impl_intro*)
 destruct IHderiv as (p, IH). rewrite intp_implf.
 rewrite intp_hyp_cons_fml in IH.
 rewrite <- lift_intp_lift_fml in IH.
 exists (Abs (intp_fofml f1) p).
 apply Impl_intro; [apply intp_fofml_prop|apply intp_fofml_not_kind|]; trivial.

(*impl_elim*)
 destruct IHderiv1, IHderiv2. exists (App x x0).
 rewrite intp_implf in H1.
 apply Impl_elim with (A:=intp_fofml f1);
   [apply intp_fofml_not_kind|apply intp_fofml_not_kind| |]; trivial.
 
(*fall_intro*)
 destruct IHderiv. rewrite intp_hyp_cons_sort in H0. exists ((Abs sort x)). 
 rewrite intp_fall. apply Fall_intro; trivial.
  rewrite <- intp_hyp_cons_sort. apply intp_fofml_prop.
  apply deriv_well_typed; trivial.

(*fall_elim*)
 destruct IHderiv. exists (App x (intp_fotrm u)).
 rewrite <- subst_intp_subst_fml. rewrite intp_fall in H1.
 apply Fall_elim; [| |apply intp_fotrm_sort]; trivial.
  rewrite <- intp_hyp_cons_sort. apply intp_fofml_prop.
  apply deriv_well_typed in H0. red in H0 |- *; intros.
  rewrite fv_fml_fall in H0. destruct n; simpl; trivial.
   apply H0. apply in_S_fv_fml; trivial.
   
(*exst_intro*)
 destruct IHderiv. rewrite intp_exst. 
 apply intp_fotrm_sort in H.
 rewrite <- subst_intp_subst_fml in H1.
 apply Exst_intro with (a:=(intp_fotrm N)) (p:=x); trivial.
  rewrite <- intp_hyp_cons_sort. apply intp_fofml_prop.
  apply deriv_well_typed in H0; red in H0 |- *; intros.
  destruct n; simpl; trivial.
   apply H0. unfold fv_fml, subst_fml in H2 |- *. 
   apply (in_fv_fml_subst _ n N 0 0); trivial.

(*exst_elim*)
 destruct IHderiv1, IHderiv2. rewrite intp_exst in H1.
 rewrite <- lift_intp_lift_fml in H2.
 rewrite intp_hyp_cons_fml in H2.
 rewrite intp_hyp_cons_sort in H2.
 unfold lift_fml in H0; rewrite lift_fml_split in H0.
 fold (lift_fml f1 1) in H0. fold (lift_fml (lift_fml f1 1) 1) in H0.
 apply deriv_well_typed in H0.
 do 2 apply hyp_ok_weakening in H0.
 apply Exst_elim with (t1:=x) (t2:=x0) (A:=intp_fofml f); trivial;
   [rewrite <- intp_hyp_cons_sort|]; apply intp_fofml_prop; trivial.
  apply deriv_well_typed in H. red in H |- *; intros.
  destruct n; simpl; trivial.
   apply H; rewrite fv_fml_exst; apply in_S_fv_fml; trivial.
Qed.

Lemma Equation_embed : forall n x y t,
  typ (const_env n) x sort ->
  typ (const_env n) y sort ->
  typ (const_env n) t (EQ_trm x y) ->
  eq_typ (const_env n) x y.
intros. apply EQ_trm_eq_typ with (t:=t); trivial.
Qed.

Lemma eq_typ_env : forall env1 env2 s s' x y,
  x <> kind ->
  y <> kind ->
  typ_esub env1 s s' env2 ->
  eq_typ env2 x y ->
  eq_typ env1 (app_esub s s' x) (app_esub s s' y).
apply explicit_sub_eq_typ.
Qed.

Definition env_incl env1 env2 := forall n t,
  (nth_error env2 n = Some t /\ t <> kind) ->
  (exists m, nth_error env1 m = Some t).

Definition env_incl_cons : forall env1 env2 a,
  env_incl env1 (a::env2) ->
  env_incl env1 env2.
unfold env_incl; intros.
apply H with (n:=(S n)); simpl; trivial.
Qed.

Lemma esub_exst : forall env1 n,
  env_incl env1 (const_env n) ->
  exists esi esj, typ_esub env1 esi esj (const_env n).
induction n; simpl; intros.
 exists id_sub_i, id_sub_j. 
 rewrite const_env0; apply esub_typ_id.

 rewrite const_envS in H |- *.
 specialize env_incl_cons with (1:=H); intro H'.
 apply IHn in H'; clear IHn.
 unfold env_incl in H. 
 destruct H with (n0:=0) (t:=sort); [split; [simpl; trivial|apply sort_not_kind]|clear H].
 destruct H' as (esi, (esj, H)).
 exists (sub_cons_i (Ref x) esi), (sub_cons_j (Ref x) esj).
 red; simpl; intros. apply H1 in H0. apply H in H1.
 apply in_int_not_kind in H0; 
   [|case_eq sort; [discriminate|intro HF; apply sort_not_kind in HF; contradiction]].
 apply vcons_add_var; [trivial| |apply sort_not_kind].
  unfold lift in H0; rewrite int_lift_rec_eq in H0.
  revert H0; apply real_morph; [|apply sort_closed|]; reflexivity.
Qed.

Lemma SN_T : forall e x y,
  (exists n, deriv (const_hyp n) (eq_fotrm x y) /\ 
    env_incl e (intp_hyp (const_hyp n))) ->
  (exists esi esj, 
    eq_typ e (app_esub esi esj (intp_fotrm x)) (app_esub esi esj (intp_fotrm y))).
intros e x y Hderiv.
destruct Hderiv as (n, (Hderiv, Hincl)).
specialize intp_sound with (1:=Hderiv); intro H.
destruct H as (p, H).
rewrite intp_eq_fml in H.
rewrite intp_hyp_env_const in H, Hincl.
specialize esub_exst with (1:=Hincl); intros H'.
destruct H' as (esi, (esj, H')). exists esi, esj. 
apply eq_typ_env with (3:=H'); 
  [apply intp_fotrm_not_kind|apply intp_fotrm_not_kind|].
apply deriv_well_typed in Hderiv.
apply hyp_ok_eq_trm in Hderiv.
destruct Hderiv as (Hokx, Hoky).
apply Equation_embed with (3:=H); rewrite <- intp_hyp_env_const in H |- *;
  [apply intp_fotrm_sort|apply intp_fotrm_sort]; trivial.
Qed.

End SN_Theory.

Module SNT := SN_Theory PresburgerSyn PresburgerSem InterpPresburger.
Import SNT PresburgerSyn PresburgerSem InterpPresburger.

Lemma SN_Presburger : forall e x y,
  (exists n, deriv (const_hyp n) (eq_fotrm x y) /\ 
    env_incl e (intp_hyp (const_hyp n))) ->
  (exists esi esj, 
    eq_typ e (app_esub esi esj (intp_fotrm x)) (app_esub esi esj (intp_fotrm y))).
apply SN_T.
Qed.
