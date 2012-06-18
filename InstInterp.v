Require Import InstSyn.
Require Import InstSem.

Import ModelTheory.
Import GenLemmas.
Import SN_CC_Real.
Import ZF SN CCSN.
Import List.


Module InterpPresburger <: InterpTheory PresburgerSyn PresburgerSem.

Import PresburgerSyn PresburgerSem.
Import SN_NAT.

Fixpoint intp_fotrm t:=
  match t with
  | Var i => Ref i
  | Cst_0 => Zero
  | Cst_1 => App Succ Zero
  | Df_Add u v => App (App Add (intp_fotrm u)) (intp_fotrm v)
  end.

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

Lemma intp_eq_fml : forall x y, 
  intp_fofml (eq_fotrm x y) = EQ_trm (intp_fotrm x) (intp_fotrm y).
simpl; reflexivity.
Qed.

Lemma intp_TF : intp_fofml TF = True_symb.
simpl; reflexivity.
Qed.

Lemma intp_BF : intp_fofml BF = False_symb.
simpl; reflexivity.
Qed.

Lemma intp_neg : forall f,
  intp_fofml (neg f) = Neg (intp_fofml f).
simpl; reflexivity.
Qed.

Lemma intp_conj : forall x y,
  intp_fofml (conj x y) = Conj (intp_fofml x) (intp_fofml y).
simpl; reflexivity.
Qed.

Lemma intp_disj : forall x y,
  intp_fofml (disj x y) = Disj (intp_fofml x) (intp_fofml y).
simpl; reflexivity.
Qed.

Lemma intp_implf : forall x y,
  intp_fofml (implf x y) = Impl (intp_fofml x) (intp_fofml y).
simpl; reflexivity.
Qed.

Lemma intp_fall : forall f,
  intp_fofml (fall f) = Fall (intp_fofml f).
simpl; reflexivity.
Qed.

Lemma intp_exst : forall f,
  intp_fofml (exst f) = Exst (intp_fofml f).
simpl; reflexivity.
Qed.

Fixpoint intp_hyp_rec hyp:= 
  match hyp with
  | nil => nil
  | h::hyp' => 
    match h with
    | Some f => (intp_fofml f)::(intp_hyp_rec hyp')
    | None => Nat :: (intp_hyp_rec hyp')
    end
  end.

Definition intp_hyp hyp:= (intp_hyp_rec hyp).

Lemma intp_nil : intp_hyp nil = nil.
simpl; trivial.
Qed.

Lemma intp_fotrm_not_kind : forall t, intp_fotrm t <> None.
destruct t; simpl; red; intros; discriminate.
Qed.

Lemma intp_fofml_not_kind : forall f, intp_fofml f <> None.
destruct f; simpl; red; intros; discriminate.
Qed.

Lemma intp_hyp_nth_fml : forall hyp f n, nth_error hyp n = Some (Some f) ->
  nth_error (intp_hyp hyp) n = Some (intp_fofml f).
induction hyp; destruct n; simpl; intros; [discriminate | discriminate | 
 injection H; intro Hinj; rewrite Hinj |]; trivial.
 destruct a; simpl; apply IHhyp; trivial.
Qed.

Lemma intp_hyp_nth_trm : forall hyp n, 
  nth_error hyp n = value None ->
  nth_error (intp_hyp hyp) n = value Nat.
induction hyp; destruct n; simpl; intros; try discriminate.
 destruct a; [discriminate | trivial].

 destruct a; apply IHhyp; trivial.
Qed.

Lemma intp_hyp_cons_fml : forall x e,
  intp_hyp (Some x :: e) = intp_fofml x :: intp_hyp e.
simpl; reflexivity.
Qed.

Lemma intp_hyp_cons_sort : forall e,
  intp_hyp (None :: e) = sort :: intp_hyp e.
simpl; reflexivity.
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

Lemma lift_intp_lift_fml_rec : forall f n k,
  eq_trm (lift_rec n k (intp_fofml f)) 
         (intp_fofml (lift_fml_rec f n k)).
induction f; simpl intp_fofml; intros.
 unfold EQ_trm; unfold lift. repeat rewrite red_lift_prod. repeat rewrite red_lift_app.
 apply Prod_morph; [apply Prod_morph; simpl; split; red; reflexivity|];
  repeat rewrite eq_trm_lift_ref_bd by omega; repeat rewrite <- lift_intp_lift_trm_rec;
   repeat rewrite lift_rec_comm with (q:=k) by omega; reflexivity.

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
 apply Prod_morph; [simpl; split; red; reflexivity|trivial].
 
 unfold Exst. do 4 rewrite red_lift_prod. 
 apply Prod_morph; [simpl; split; red; reflexivity|].
  do 2 rewrite subst0_lift. do 2 rewrite eq_trm_lift_ref_bd by omega.
  rewrite <- IHf. rewrite lift_rec_comm with (q:=S k) by omega.
  apply Prod_morph; [apply Prod_morph; [simpl; split; red|]|]; reflexivity.
Qed.
      
Lemma lift_intp_lift_fml : forall f n,
  eq_trm (lift n (intp_fofml f)) (intp_fofml (lift_fml f n)).
unfold lift, lift_fml; intros. apply lift_intp_lift_fml_rec.
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
 
Lemma subst_intp_subst_fml_rec : forall f N k,
  eq_trm (subst_rec (intp_fotrm N) k (intp_fofml f)) 
         (intp_fofml (subst_fml_rec f N k)).
induction f; simpl intp_fofml; intros.
 unfold EQ_trm. do 3 rewrite red_sigma_prod. 
 apply Prod_morph; [apply Prod_morph; simpl; split; red; reflexivity|].
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
 apply Prod_morph; [simpl; split; red; reflexivity|trivial].

 unfold Exst. do 4 rewrite red_sigma_prod. 
 apply Prod_morph; [simpl; split; red; reflexivity|].
  repeat rewrite subst0_lift. do 2 rewrite red_sigma_var_lt by omega.
  repeat rewrite subst_lift_ge by omega. rewrite <- IHf.
  apply Prod_morph; [apply Prod_morph; [simpl; split; red; reflexivity|]|reflexivity].
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

Lemma hyp_ok_add : forall t1 t2 hyp,
  hyp_ok_trm hyp t1 /\ hyp_ok_trm hyp t2 <-> hyp_ok_trm hyp (Df_Add t1 t2).
split; intros.
 destruct H as (H1, H2). 
 red in H1, H2 |- *. simpl in H1, H2 |- *; intros.
 unfold fv_trm in H; simpl in H; apply in_app_or in H.
 destruct H as [Hl|Hr]; [apply H1 in Hl|apply H2 in Hr]; trivial.

 split; red in H |- *; intros; simpl in H, H0.
  assert (In n (fv_trm_rec t1 0 ++ fv_trm_rec t2 0)).
   apply in_or_app; left; trivial.
   
  apply H in H1; trivial.

  assert (In n (fv_trm_rec t1 0 ++ fv_trm_rec t2 0)).
   apply in_or_app; right; trivial.
   
  apply H in H1; trivial.
Qed.

Lemma intp_fotrm_sort : forall hyp t,
  hyp_ok_trm hyp t ->
  typ (intp_hyp hyp) (intp_fotrm t) Nat.
induction t; simpl intp_fotrm; intros.
 red in H; simpl in H.
 apply typ_common; [exact I|intros].
 replace (n-0) with n in H by omega.
 assert (n=n \/ False) by auto.
 specialize H with (1:=H1); clear H1.
 apply intp_hyp_nth_trm in H. apply H0 in H; clear H0.
 apply in_int_not_kind in H; [|discriminate].
 revert H; apply real_morph; [|simpl|]; reflexivity.

 apply typ_0.

 apply typ_S1; apply typ_0.
 
 rewrite <- hyp_ok_add in H. destruct H as (H1, H2).
 apply typ_Add2; [apply IHt1|apply IHt2]; trivial.
Qed.

Lemma intp_fofml_prop : forall f hyp,
  hyp_ok_fml hyp f ->
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

 apply Fall_typ. replace (Nat::intp_hyp hyp) with (intp_hyp (None::hyp)) by (simpl; trivial).
 apply IHf. red in H |- *. intros. simpl in H.
 destruct n; simpl; [|apply H; apply in_S_fv_fml]; trivial.

 apply Exst_typ. replace (Nat::intp_hyp hyp) with (intp_hyp (None::hyp)) by (simpl; trivial).
 apply IHf. red in H |- *. intros; simpl in H.
 destruct n; simpl; [|apply H; apply in_S_fv_fml]; trivial.
Qed.

Lemma intp_ax : forall hyp f, 
  PresburgerSyn.ax hyp f -> 
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

End InterpPresburger.