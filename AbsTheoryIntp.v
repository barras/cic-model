(************************************************************************************)
(************************************************************************************)
(*This file describes the interpretation from syntax to semantic*)
(************************************************************************************)
(************************************************************************************)

Require Import AbsTheorySyn.
Require Import AbsTheorySem.

Import Compare_dec.
Import List.
Import GenLemmas.
Import SN_CC_Real.
Import SN CCSN.

(************************************************************************************)
(*Abstract interpretation of signature*)
(************************************************************************************)

Module Type SigIntp (Msyn : TheorySyn).

Import Msyn.

(*Interpretation first-order term*)
Parameter intp_fotrm : foterm -> trm.

(*Interpretation is not kind*)
Axiom intp_fotrm_not_kind : forall t, intp_fotrm t <> kind.

(*Properties about lift and interpretation term*)
Axiom lift_intp_lift_trm_rec : forall t n k, 
  eq_trm (lift_rec n k (intp_fotrm t)) 
         (intp_fotrm (lift_trm_rec t n k)).
Axiom lift_intp_lift_trm : forall t n,
  eq_trm (lift n (intp_fotrm t)) 
         (intp_fotrm (lift_trm t n)).

(*Properties about substitution and interpretation term*)
Axiom subst_intp_subst_trm_rec : forall t N k, 
  eq_trm (subst_rec (intp_fotrm N) k (intp_fotrm t)) 
         (intp_fotrm (subst_trm_rec t N k)).
Axiom subst_intp_subst_trm : forall t N, 
  eq_trm (subst (intp_fotrm N) (intp_fotrm t)) 
         (intp_fotrm (subst_trm t N)).

End SigIntp.


(************************************************************************************)
(*Interpret first-order language and hypothesis*)
(************************************************************************************)
Module LangHypIntp (Msyn : TheorySyn) (Msem : TheorySem) (MSI : SigIntp Msyn).

Import Msyn Msem MSI.

(*Interpretation of foformula*)
Fixpoint intp_fofml f:=
  match f with
  | eq_fotrm x y => EQ_trm (intp_fotrm x) (intp_fotrm y)
  | TF => True_symb
  | BF => False_symb
  | neg f => Neg (intp_fofml f)
  | conj f1 f2 => Conj (intp_fofml f1) (intp_fofml f2)
  | disj f1 f2 => Disj (intp_fofml f1) (intp_fofml f2)
  | implf f1 f2 => Impl (intp_fofml f1) (intp_fofml f2)
  | fall f => Fall (intp_fofml f)
  | exst f => Exst (intp_fofml f)
  end.

(*Properties about lift and interpretation formula*)
Lemma lift_intp_lift_fml_rec : forall f n k,
  eq_trm (lift_rec n k (intp_fofml f)) 
         (intp_fofml (lift_fml_rec f n k)).
induction f; simpl intp_fofml; intros.
 unfold EQ_trm; unfold lift. repeat rewrite red_lift_prod. repeat rewrite red_lift_app.
 apply Prod_morph; [apply Prod_morph; [generalize sort_clsd; intro H; destruct H as (H, _); apply H 
   |simpl; split; red; reflexivity]|]; repeat rewrite eq_trm_lift_ref_bd by omega; 
 repeat rewrite <- lift_intp_lift_trm_rec; repeat rewrite lift_rec_comm with (q:=k) by omega; reflexivity.

 simpl; split; red; reflexivity.

 simpl; split; red; reflexivity.

 unfold Neg, Impl. rewrite red_lift_prod.
 apply Prod_morph; trivial.
  simpl; split; red; reflexivity.

 unfold Conj, lift. do 4 rewrite red_lift_prod.
 apply Prod_morph; [simpl; split; red; reflexivity|].
  repeat rewrite eq_trm_lift_ref_bd by omega.
  rewrite <- IHf1, <- IHf2.
  repeat rewrite lift_rec_comm with (q:=k) by omega; reflexivity.
      
 unfold Disj, lift. do 5 rewrite red_lift_prod.
  apply Prod_morph; [simpl; split; red; reflexivity|].
   repeat rewrite eq_trm_lift_ref_bd by omega.
   rewrite <- IHf1, <- IHf2.
   repeat rewrite lift_rec_comm with (q:=k) by omega; reflexivity.
     
 unfold Impl, lift. rewrite red_lift_prod. apply Prod_morph; trivial.
  rewrite <- IHf2. rewrite lift_rec_comm with (q:=k) by omega; reflexivity.

 unfold Fall; rewrite red_lift_prod.
 apply Prod_morph; [generalize sort_clsd; intro H; destruct H as (H, _); apply H|trivial].
 
 unfold Exst. do 4 rewrite red_lift_prod. 
 apply Prod_morph; [simpl; split; red; reflexivity|].
  do 2 rewrite subst0_lift. do 2 rewrite eq_trm_lift_ref_bd by omega.
  rewrite <- IHf. rewrite lift_rec_comm with (q:=S k) by omega.
  generalize sort_clsd; intro H; destruct H as (H, _).
  apply Prod_morph; [apply Prod_morph; [unfold lift; do 2 rewrite H|]|]; reflexivity.
Qed.
      
Lemma lift_intp_lift_fml : forall f n,
  eq_trm (lift n (intp_fofml f)) (intp_fofml (lift_fml f n)).
unfold lift, lift_fml; intros. apply lift_intp_lift_fml_rec.
Qed.


(*Properties about substitution and interpretation foformula*)
Lemma subst_intp_subst_fml_rec : forall f N k,
  eq_trm (subst_rec (intp_fotrm N) k (intp_fofml f)) 
         (intp_fofml (subst_fml_rec f N k)).
induction f; simpl intp_fofml; intros.
 unfold EQ_trm. do 3 rewrite red_sigma_prod. 
 apply Prod_morph; [apply Prod_morph; [
   generalize sort_clsd; intro H; destruct H as (_, H); apply H|simpl; split; red; reflexivity]|].
  repeat rewrite red_sigma_app. repeat rewrite red_sigma_var_lt by omega.
  do 2 rewrite <- subst_intp_subst_trm_rec.
  unfold lift. repeat rewrite subst_lift_ge by omega. 
  fold (lift 0 (intp_fotrm f)). fold (lift 0 (intp_fotrm f0)).
  repeat rewrite lift0. rewrite lift_rec_acc; [reflexivity|omega].

 simpl; split; red; reflexivity.

 simpl; split; red; reflexivity.

 unfold Neg, Impl. rewrite red_sigma_prod. 
 apply Prod_morph; [trivial|simpl; split; red; reflexivity].

 unfold Conj. do 4 rewrite red_sigma_prod. 
 apply Prod_morph; [simpl; split; red; reflexivity|].
  unfold lift. repeat rewrite subst_lift_ge by omega.
  fold (lift 0 (intp_fofml f1)). fold (lift 0 (intp_fofml f2)).
  do 2 rewrite lift0. rewrite lift_rec_acc by omega.
  do 2 rewrite red_sigma_var_lt by omega.
  rewrite IHf1, IHf2; reflexivity.

 unfold Disj. do 5 rewrite red_sigma_prod. 
 apply Prod_morph; [simpl; split; red; reflexivity|].
  unfold lift. repeat rewrite subst_lift_ge by omega.
  fold (lift 0 (intp_fofml f1)). fold (lift 0 (intp_fofml f2)).
  do 2 rewrite lift0. rewrite lift_rec_acc by omega.
  do 2 rewrite red_sigma_var_lt by omega.
  rewrite IHf1, IHf2; reflexivity.

 unfold Impl. rewrite red_sigma_prod. apply Prod_morph; trivial.
  rewrite <- IHf2. unfold lift.
  rewrite subst_lift_ge by omega. 
  fold (lift 0 (intp_fofml f2)); rewrite lift0; reflexivity.
  
 unfold Fall; rewrite red_sigma_prod. 
 apply Prod_morph; [generalize sort_clsd; intro H; destruct H as (_, H); apply H|trivial].

 unfold Exst. do 4 rewrite red_sigma_prod. 
 apply Prod_morph; [simpl; split; red; reflexivity|].
  repeat rewrite subst0_lift. do 2 rewrite red_sigma_var_lt by omega.
  unfold lift; repeat rewrite subst_lift_ge by omega. rewrite <- IHf. fold (lift 0 sort). rewrite lift0. 
  apply Prod_morph; [apply Prod_morph; 
    [generalize sort_clsd; intro H; destruct H as (_, H); rewrite H; reflexivity|]|reflexivity].
   apply Prod_morph; [|reflexivity].
    apply lift_rec_morph. apply subst_rec_morph; [reflexivity|reflexivity|].
     apply eq_trm_intro; [| |destruct (intp_fofml f); simpl; trivial]; intros.
      rewrite int_lift_rec_eq. unfold V.lams, V.shift.
       apply int_morph; [do 2 red; intros|reflexivity].
        destruct (le_gt_dec 1 a); [|reflexivity].
         replace (1+(0+(a-1))) with a; [reflexivity|omega].

      rewrite tm_lift_rec_eq. unfold I.lams, I.shift.
       apply tm_morph; [do 2 red; intros|reflexivity].
        destruct (le_gt_dec 1 a); [|reflexivity].
         replace (1+(0+(a-1))) with a; [reflexivity|omega].
Qed.

Lemma subst_intp_subst_fml : forall f N,
  eq_trm (subst (intp_fotrm N) (intp_fofml f)) 
          (intp_fofml (subst_fml  f N)).
unfold subst; intros; apply subst_intp_subst_fml_rec with (k:=0).
Qed.

(*Interpretation of the context*)
Fixpoint intp_hyp (hyp : HYP) := 
  match hyp with
  | nil => nil
  | h::hyp' => 
    match h with
    | Some f => (intp_fofml f)::(intp_hyp hyp')
    | None => sort :: (intp_hyp hyp')
    end
  end.

Lemma intp_hyp_nth_fml : forall hyp f n, nth_error hyp n = Some (Some f) ->
  nth_error (intp_hyp hyp) n = Some (intp_fofml f).
induction hyp; destruct n; simpl; intros; [discriminate | discriminate | 
 injection H; intro Hinj; rewrite Hinj |]; trivial.
 destruct a; simpl; apply IHhyp; trivial.
Qed.

End LangHypIntp.

(***********************************************************************************)
(*Interpret axioms*)
(***********************************************************************************)
Module Type AxIntp (Msyn : TheorySyn) (Msem : TheorySem) (MSI : SigIntp Msyn).

Include LangHypIntp Msyn Msem MSI.
Import Msyn Msem MSI.

Axiom intp_fotrm_sort : forall hyp t,
  wf_trm hyp t ->
  typ (intp_hyp hyp) (intp_fotrm t) sort.

(*The interpretation of the foformula is prop*)
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

(*Axioms in first-order theory is provable in the associated module*)
Parameter intp_ax : forall (hyp : HYP) f, 
  ax_syn hyp f -> 
  exists t, typ (intp_hyp hyp) t (intp_fofml f).

End AxIntp.


(***********************************************************************************)
(*Interpret Theory*)
(***********************************************************************************)
Module Type TheoryIntp (Msyn : TheorySyn) (Msem : TheorySem).

Declare Module MSI : SigIntp Msyn.

Declare Module MAI : AxIntp Msyn Msem MSI.

End TheoryIntp.