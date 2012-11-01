(*****************************************************************************************)
(*****************************************************************************************)
(*This file gives the SN proof after embedding the theory*)
(*There are two main steps to prove SN :*)
(*1. Soundness of the first order theory*)
(*2. New proof of the conversion rule*)
(*To prove 2, just need to prove eq_fotrm can be embedded in eq_typ*)
(*****************************************************************************************)
(*****************************************************************************************)

Require Import AbsTheoryIntp.

Import AbsTheorySyn AbsTheorySem.
Import Esub GenLemmas.
Import SN_CC_Real.
Import ZF SN CCSN.

(*SN for the abstract theory*)
Module Abs_SN_Theory (Msyn : TheorySyn) (Msem : TheorySem) (Mintp : TheoryIntp Msyn Msem).

Import Msyn Msem Mintp.
Import MAI MSI.

Lemma intp_sound : forall hyp P, deriv hyp P -> 
  exists p, typ ((intp_hyp hyp)) p (intp_fofml P).
induction 1; simpl.
(*hyp*)
 exists (Ref n); red; simpl; intros. unfold val_ok in H1.
 rewrite <- lift_intp_lift_fml. apply H1. apply intp_hyp_nth_fml; trivial.

(*ax_intro*)
 apply intp_ax; trivial.

(*true_intro*)
 apply True_symb_intro.
 
(*false_elim*)
 destruct IHderiv. exists (App x (intp_fofml f)).
 apply False_symb_elim; [|apply intp_fofml_prop]; trivial.

(*neg_intro*)
 destruct IHderiv as (p, IH). exists p.
 apply Neg_intro; trivial.

(*neg_elim*)
 destruct IHderiv. exists x. 
 apply Neg_elim; trivial.

(*conj_intro*)
 destruct IHderiv1 as (x, IH1). 
 destruct IHderiv2 as (x', IH2).
 apply Conj_intro with (u:=x) (v:=x'); [apply intp_fofml_prop; apply deriv_well_typed
   |apply intp_fofml_prop; apply deriv_well_typed|split]; trivial.

(*conj_elim1*)
 destruct IHderiv as (t, IH). apply deriv_well_typed in H. simpl in IH.
 apply Conj_elim1 with (B:=(intp_fofml f2)) (t:=t);
   [apply intp_fofml_prop|apply intp_fofml_prop|trivial];
   unfold wf_fml, fv_fml in H |- *; simpl in H |- *; intros; apply H;
     rewrite in_app_iff; [left|right]; trivial.
   
(*conj_elim2*)
 destruct IHderiv as (t, IH). apply deriv_well_typed in H.
 apply Conj_elim2 with (A:=(intp_fofml f1)) (t:=t); 
   [apply intp_fofml_prop|apply intp_fofml_prop|trivial];
   unfold wf_fml, fv_fml in H |- *; simpl in H; intros; apply H; 
     rewrite in_app_iff; [left|right]; trivial.
 
(*disj_intro1*)
 destruct IHderiv.
 apply Disj_intro1 with (t:=x); [apply intp_fofml_prop; apply deriv_well_typed
   |apply intp_fofml_prop|]; trivial.
 
(*disj_intro2*)
 destruct IHderiv.
 apply Disj_intro2 with (t:=x); [apply intp_fofml_prop
   |apply intp_fofml_prop; apply deriv_well_typed|]; trivial.

(*disj_elim*)
 destruct IHderiv1, IHderiv2, IHderiv3. simpl in H3, H4.
 apply deriv_well_typed in H. apply deriv_well_typed in H0.
 apply wf_weakening in H0.
 apply Disj_elim with (t:=x) (t1:=x0) (t2:=x1) (A:=intp_fofml f1) (B:=intp_fofml f2);
   [apply intp_fofml_prop|apply intp_fofml_prop|apply intp_fofml_prop
     | |rewrite lift_intp_lift_fml|rewrite lift_intp_lift_fml]; trivial;
   unfold wf_fml, fv_fml in H |- *; intros; apply H; simpl;
     rewrite in_app_iff; [left|right]; trivial.

(*impl_intro*)
 destruct IHderiv as (p, IH). simpl in IH.
 rewrite <- lift_intp_lift_fml in IH.
 exists (Abs (intp_fofml f1) p).
 apply Impl_intro; [apply intp_fofml_prop|destruct f2; simpl; discriminate|]; trivial.

(*impl_elim*)
 destruct IHderiv1, IHderiv2. exists (App x x0).
 apply Impl_elim with (A:=intp_fofml f1); trivial; [destruct f1 | destruct f2];
   simpl; discriminate.
 
(*fall_intro*)
 destruct IHderiv. simpl in H0. exists ((Abs sort x)). 
 apply Fall_intro; trivial. 
  replace (sort :: intp_hyp hyp) with (intp_hyp (None :: hyp)); trivial.
  apply intp_fofml_prop. apply deriv_well_typed; trivial.

(*fall_elim*)
 destruct IHderiv. exists (App x (intp_fotrm u)).
 rewrite <- subst_intp_subst_fml.
 apply Fall_elim; [| |apply intp_fotrm_sort]; trivial.
  replace (sort :: intp_hyp hyp) with (intp_hyp (None :: hyp)); trivial.
  apply intp_fofml_prop. apply deriv_well_typed in H0. 
  unfold wf_fml, fv_fml in H0 |- *; intros.
  destruct n; simpl; trivial.
   apply H0. apply in_S_fv_fml; trivial.
   
(*exst_intro*)
 destruct IHderiv. apply intp_fotrm_sort in H.
 rewrite <- subst_intp_subst_fml in H1.
 apply Exst_intro with (a:=(intp_fotrm N)) (p:=x); trivial.
  replace (sort :: intp_hyp hyp) with (intp_hyp (None :: hyp)); trivial.
  apply intp_fofml_prop. apply deriv_well_typed in H0. 
  unfold wf_fml, fv_fml in H0 |- *; intros.
  destruct n; simpl; trivial.
   apply H0. unfold fv_fml, subst_fml in H2 |- *. 
   apply (in_fv_fml_subst _ n N 0 0); trivial.

(*exst_elim*)
 destruct IHderiv1, IHderiv2.
 rewrite <- lift_intp_lift_fml in H2. simpl in H2.
 unfold lift_fml in H0; rewrite lift_fml_split in H0.
 fold (lift_fml f1 1) in H0. fold (lift_fml (lift_fml f1 1) 1) in H0.
 apply deriv_well_typed in H0.
 do 2 apply wf_weakening in H0.
 apply Exst_elim with (t1:=x) (t2:=x0) (A:=intp_fofml f); trivial;
   [replace (sort :: intp_hyp hyp) with (intp_hyp (None :: hyp)) by trivial|]; 
   apply intp_fofml_prop; trivial.
  apply deriv_well_typed in H. unfold wf_fml, fv_fml in H |- *; intros.
  destruct n; simpl; trivial.
   apply H; apply in_S_fv_fml; trivial.
Qed.

Lemma SN_T : forall e x y,
  (exists hyp a b i j, 
    x = app_esub i j (intp_fotrm a) /\
    y = app_esub i j (intp_fotrm b) /\
    wf_clsd_env (intp_hyp hyp) /\
    typ_esub e i j (intp_hyp hyp) /\
    deriv hyp (eq_fotrm a b)) ->
  eq_typ e x y.
intros e x y Hyp.
destruct Hyp as (hyp, (a, (b, (i, (j, (Hx, (Hy, (Hclsd, (He, Hderiv))))))))).
(*a and b are well typed in theory syntax*)
specialize deriv_well_typed with (1:=Hderiv); intro Hwf.
assert (wf_trm hyp a /\ wf_trm hyp b) as Hwfab.
 unfold wf_fml, fv_fml in Hwf; simpl in Hwf.
 unfold wf_trm; split; intros; apply Hwf; rewrite in_app_iff; [left|right]; trivial.

destruct Hwfab as (Hwfa, Hwfb); clear Hwf.
(*Therefore they have type sort in semantic*)
apply intp_fotrm_sort in Hwfa.
apply intp_fotrm_sort in Hwfb.

(*EQ_trm (intp_trm a) (intp_trm b) can be proved*)
specialize intp_sound with (1:=Hderiv); clear Hderiv; intro HEQ.
destruct HEQ as (p, HEQ); simpl in HEQ.

(*EQ_trm can be embedded in eq_typ*)
apply EQ_trm_elim in HEQ; [|exact Hclsd|exact Hwfa|exact Hwfb].

(*eq_typ relation maintains after variable recocation*)
subst x y. 
apply explicit_sub_eq_typ with (3:=He); 
  [apply intp_fotrm_not_kind|apply intp_fotrm_not_kind|exact HEQ].
Qed.

End Abs_SN_Theory.
