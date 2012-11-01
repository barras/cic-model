Require Import PSyn.
Require Import PSem.
Require Import AbsTheoryIntp.

Import SN_NAT.
Import GenLemmas.
Import SN_CC_Real.
Import ZF SN CCSN.
Import List.

(*******************************************************************)
(*Interpret Presburger signature*)
(*******************************************************************)

Module IntpPSig <: SigIntp PresburgerTheory.

Import PresburgerTheory.
Import PresburgerSem.

Fixpoint intp_fotrm t : trm :=
  match t with
  | Var i => Ref i
  | Cst_0 => Zero
  | Cst_1 => App Succ Zero
  | Df_Add u v => App (App Add (intp_fotrm u)) (intp_fotrm v)
  end.

Lemma intp_fotrm_not_kind : forall t, intp_fotrm t <> None.
destruct t; simpl; red; intros; discriminate.
Qed.

Lemma lift_intp_lift_trm_rec : forall t n k, 
  eq_trm (lift_rec n k (intp_fotrm t)) 
          (intp_fotrm (lift_trm_rec t n k)).
induction t; intros.
 simpl; case_eq (le_gt_dec k n); simpl; intros.
  split; red; simpl; intros.
   unfold V.lams, V.shift.
   rewrite H. replace (k+(n0+(n-k))) with (n+n0) by omega. apply H0.

   unfold I.lams, I.shift.
   rewrite H. replace (k+(n0+(n-k))) with (n+n0) by omega. apply H0.

  split; red; simpl; intros.
   rewrite V.lams_bv; trivial.

   rewrite I.lams_bv; trivial.

 simpl; split; red; reflexivity.

 simpl; split; red; reflexivity.

 simpl intp_fotrm. do 2 rewrite red_lift_app.
 apply App_morph; trivial.
  apply App_morph; trivial.
   simpl; split; red; reflexivity.
Qed.

Lemma lift_intp_lift_trm : forall t n,
  eq_trm (lift n (intp_fotrm t)) (intp_fotrm (lift_trm t n)).
unfold lift, lift_trm. intros. apply lift_intp_lift_trm_rec.
Qed.

Lemma subst_intp_subst_trm_rec : forall t N k, 
  eq_trm (subst_rec (intp_fotrm N) k (intp_fotrm t)) 
         (intp_fotrm (subst_trm_rec t N k)).
induction t; intros; simpl intp_fotrm.
 simpl; destruct (lt_eq_lt_dec k n) as [[lt|eq]|bt]; simpl.
  split; red; intros.
   unfold V.lams, V.shift; simpl. 
   destruct (le_gt_dec k n) as [le|gt]; [|omega].
    replace (n-k) with (S (Peano.pred n-k)) by omega; simpl.
    replace (k+(Peano.pred n-k)) with (Peano.pred n) by omega; apply H.

   unfold I.lams, I.shift; simpl.
   destruct (le_gt_dec k n) as [le|gt]; [|omega].
    replace (n-k) with (S (Peano.pred n-k)) by omega; simpl.
    replace (k+(Peano.pred n-k)) with (Peano.pred n) by omega; apply H.

  case_eq (intp_fotrm (lift_trm N k)); intros; 
    [|apply intp_fotrm_not_kind in H; trivial].
   split; red; intros; subst k.
    unfold V.lams; simpl.
    destruct (le_gt_dec n n) as [le|gt]; [|omega].
     replace (n-n) with 0 by omega; simpl. rewrite H0.
     setoid_replace (V.shift n y) with (V.lams 0 (V.shift n) y); [
       |rewrite V.lams0; reflexivity].
      rewrite <- int_lift_rec_eq. fold (lift n (intp_fotrm N)).
      rewrite lift_intp_lift_trm. rewrite H; simpl; reflexivity.

    unfold I.lams; simpl.
    destruct (le_gt_dec n n) as [le|gt]; [|omega].
     replace (n-n) with 0 by omega; simpl. rewrite H0.
     setoid_replace (I.shift n y) with (I.lams 0 (I.shift n) y) 
       using relation Lc.eq_intt; [|rewrite I.lams0; reflexivity].
      rewrite <- tm_lift_rec_eq. fold (lift n (intp_fotrm N)).
      rewrite lift_intp_lift_trm. rewrite H; simpl; reflexivity.

  simpl; split; red; intros; [rewrite V.lams_bv|rewrite I.lams_bv]; trivial.

 simpl; split; red; reflexivity.
 
 simpl; split; red; reflexivity.

 do 2 rewrite red_sigma_app. apply App_morph; trivial.
  apply App_morph; [simpl; split; red; reflexivity|trivial].
Qed.

Lemma subst_intp_subst_trm : forall t N, 
  eq_trm (subst (intp_fotrm N) (intp_fotrm t)) 
         (intp_fotrm (subst_trm t N)).
unfold subst. intros. apply subst_intp_subst_trm_rec with (k:=0).
Qed.

End IntpPSig.


(*******************************************************************)
(*Interpret Presburger Axiom*)
(*******************************************************************)
Module IntpAx : AxIntp PresburgerTheory PresburgerSem IntpPSig.

Include LangHypIntp PresburgerTheory PresburgerSem IntpPSig.
Import PresburgerTheory PresburgerSem IntpPSig.

Lemma intp_fotrm_sort : forall hyp t,
  wf_trm hyp t ->
  typ (intp_hyp hyp) (intp_fotrm t) Nat.
induction t; simpl intp_fotrm; intros.
 unfold wf_trm in H. simpl in H.
 apply typ_common; [exact I|intros].
 replace (n-0) with n in H by omega.
 assert (n=n \/ False) by auto.
 specialize H with (1:=H1); clear H1.
 assert (forall hyp n, nth_error hyp n = Some None ->
   nth_error (intp_hyp hyp) n = Some sort).
  induction hyp0; intros; destruct n0; simpl in H1 |- *; 
    [discriminate|discriminate
      |injection H1; intros; subst a; trivial
      |destruct a; apply IHhyp0; trivial].

 apply H1 in H; clear H1.
 apply H0 in H; clear H0.
 apply in_int_not_kind in H; [|discriminate].
 revert H; apply real_morph; [|simpl|]; reflexivity.

 apply typ_0.

 apply typ_S1; apply typ_0.

 apply typ_Add2; [apply IHt1|apply IHt2];
   unfold wf_trm, fv_trm in H |- *; simpl in H |- *; 
     intros; apply H; rewrite in_app_iff; [left|right]; trivial.
Qed.

Lemma intp_fofml_prop : forall f hyp,
  wf_fml hyp f ->
  typ (intp_hyp hyp) (intp_fofml f) prop.
 induction f; simpl; intros.
 apply EQ_trm_typ; apply intp_fotrm_sort; red in H |- *; simpl in H |- *; intros; 
   apply H; apply in_or_app; [left|right]; trivial.

 apply True_symb_typ.

 apply False_symb_typ.

 apply Neg_typ; apply IHf.
 red in H |- *; intros; apply H; simpl; trivial.

 apply Conj_typ; [apply IHf1|apply IHf2]; red in H |- *; simpl in H |- *; intros; 
   apply H; apply in_or_app; [left|right]; trivial.

 apply Disj_typ; [apply IHf1|apply IHf2]; red in H |- *; simpl in H |- *; intros; 
   apply H; apply in_or_app; [left|right]; trivial.

 apply Impl_typ; [apply IHf1|apply IHf2]; red in H |- *; simpl in H |- *; intros; 
   apply H; apply in_or_app; [left|right]; trivial.

 apply Fall_typ. replace (sort::intp_hyp hyp) with (intp_hyp (None::hyp)) by (simpl; trivial).
 apply IHf. red in H |- *. intros. simpl in H.
 destruct n; simpl; [|apply H; apply in_S_fv_fml]; trivial.

 apply Exst_typ. replace (sort::intp_hyp hyp) with (intp_hyp (None::hyp)) by (simpl; trivial).
 apply IHf. red in H |- *. intros; simpl in H.
 destruct n; simpl; [|apply H; apply in_S_fv_fml]; trivial.
Qed.


Lemma intp_ax : forall hyp f, 
  ax_syn hyp f -> 
  exists t, typ (intp_hyp hyp) t (intp_fofml f).
intros.

(*ax1*)
destruct H. rewrite H. generalize P_ax_intro1; intros Hax1.
unfold ax1 in Hax1. specialize Hax1 with (e:=(intp_hyp hyp)).
destruct Hax1 as (t, Hax1). exists t; simpl intp_fofml; trivial.

(*ax2*)
destruct H. rewrite H. generalize P_ax_intro2; intros Hax2.
unfold ax2 in Hax2. specialize Hax2 with (e:=(intp_hyp hyp)).
destruct Hax2 as (t, Hax2). exists t; simpl intp_fofml; trivial.

(*ax3*)
destruct H. rewrite H. generalize P_ax_intro3; intros Hax3.
unfold ax3 in Hax3. specialize Hax3 with (e:=(intp_hyp hyp)).
destruct Hax3 as (t, Hax3). exists t; simpl intp_fofml; trivial.

(*ax4*)
destruct H. rewrite H. generalize P_ax_intro4; intros Hax4.
unfold ax4 in Hax4. specialize Hax4 with (e:=(intp_hyp hyp)).
destruct Hax4 as (t, Hax4). exists t; simpl intp_fofml; trivial.

(*ax5*)
generalize P_ax_intro5; intros Hax5. unfold ax5 in Hax5.
destruct H as (g, (Hp, H)).
apply intp_fofml_prop in Hp. simpl in Hp.
setoid_replace prop with (lift 1 prop) using relation eq_trm in Hp; [|
  split; red; simpl; reflexivity].
apply Hax5 in Hp. rewrite H. clear f H Hax5.
simpl intp_fofml. destruct Hp as (t, Hp). exists t.
revert Hp; apply typ_morph; [reflexivity|].
unfold Impl, Fall. repeat rewrite <- subst_intp_subst_fml. simpl intp_fotrm.
apply Prod_morph; [reflexivity|apply lift_morph].
 apply Prod_morph; [|reflexivity].
  apply Prod_morph; [reflexivity|].
   apply Prod_morph; [reflexivity|apply lift_morph].
    unfold subst; apply subst_rec_morph;
      [|trivial|rewrite lift_intp_lift_fml_rec]; reflexivity.
Qed.

End IntpAx.


(**************************************************************************************)
(*Interpret Presburger*)
(**************************************************************************************)
Module IntpPresburger <: TheoryIntp PresburgerTheory PresburgerSem.

Module MSI := IntpPSig.
Export MSI.

Module MAI := IntpAx.
Export MAI.

End IntpPresburger.