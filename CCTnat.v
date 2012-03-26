Require Import Explicit_sub.
Require Import FOTheory.
Require Import basic Omega.

Import BuildModel.
Import T J R.
Import CCM.
Import ZFind_basic.
Import ZFnats.

Fixpoint int_fotrm t:=
  match t with
  | Var i => Ref i
  | Cst_0 => Zero
  | Cst_1 => Succ Zero
  | Df_Add u v => Add (int_fotrm u) (int_fotrm v)
  end.

Fixpoint int_fofml f:=
  match f with
  | eq_fotrm x y => EQ_trm (int_fotrm x) (int_fotrm y)
  | TF => True_symb
  | BF => False_symb
  | neg f => Neg (int_fofml f)
  | conj f1 f2 => Conj (int_fofml f1) (int_fofml f2)
  | disj f1 f2 => Disj (int_fofml f1) (int_fofml f2)
  | implf f1 f2 => Impl (int_fofml f1) (int_fofml f2)
  | fall f => Fall (int_fofml f)
  | exst f => Exst (int_fofml f)
  end.

Fixpoint int_hyp_rec hyp:= 
  match hyp with
  | nil => nil
  | h::hyp' => 
    match h with
    | Some f => (int_fofml f)::(int_hyp_rec hyp')
    | None => T :: (int_hyp_rec hyp')
    end
  end.

Definition int_hyp hyp:= (int_hyp_rec hyp).

Lemma fotrm_Some : forall t, int_fotrm t <> None.
destruct t; simpl; red; intros; discriminate.
Qed.

Lemma fofml_Some : forall f, int_fofml f <> None.
destruct f; simpl; red; intros; discriminate.
Qed.

Lemma int_hyp_nth_fml : forall hyp f n, nth_error hyp n = Some (Some f) ->
  nth_error (int_hyp hyp) n = Some (int_fofml f).
induction hyp; destruct n; simpl; intros; [discriminate | discriminate | 
 injection H; intro Hinj; rewrite Hinj |]; trivial.

 destruct a; simpl; apply IHhyp; trivial.
Qed.

Lemma int_hyp_nth_trm : forall hyp n, 
  nth_error hyp n = value None ->
  nth_error (int_hyp hyp) n = value T.
induction hyp; destruct n; simpl; intros; try discriminate.
 destruct a; [discriminate | trivial].
 destruct a; apply IHhyp; trivial.
Qed.

Lemma int_trm_N : forall hyp t i, hyp_ok hyp t -> 
  val_ok (int_hyp hyp) i ->
  int (int_fotrm t) i ∈ N.
unfold hyp_ok; unfold val_ok; induction t; simpl in *; intros.
 assert (n=n\/False). left; trivial.
 specialize H with (n0:=n) (1:=H1).
 generalize (int_hyp_nth_trm _ _ H); intros.
 specialize H0 with (1:=H2). simpl in H0; trivial.

 apply zero_typ.
 
 apply succ_typ. apply zero_typ.

 replace (fun k : nat => i k) with i; trivial.
 assert (int (int_fotrm t2) i ∈ N).
  apply IHt2; trivial; intros.
   apply H. apply in_or_app. right; trivial.
 elim H1 using N_ind; intros.
  revert H4; apply in_set_morph; try reflexivity.
   apply NATREC_morph; try reflexivity.
    do 2 red; intros. rewrite H5; reflexivity.

    symmetry; trivial.

  rewrite NATREC_0. apply IHt1; trivial; intros.
   apply H. apply in_or_app; left; trivial.

  rewrite NATREC_Succ;trivial. 
   apply succ_typ; trivial.

   do 3 red; intros. rewrite H5; reflexivity.
Qed.

   
Lemma lift_int_lift_trm_rec : forall t n k, 
  eq_term (lift_rec n k (int_fotrm t)) 
          (int_fotrm (lift_trm_rec t n k)).
induction t; simpl; intros.
 unfold V.lams. unfold V.shift.
 destruct (Compare_dec.le_gt_dec k n); simpl; intros.
  replace (k+(n0+(n-k))) with (n+n0) by omega.
  red; auto.

  red; auto.

 red; reflexivity.

 red; intros. apply succ_morph. reflexivity.

 red; intros. apply NATREC_morph; try rewrite H.
  rewrite <- IHt1. rewrite int_lift_rec_eq. reflexivity.

  do 2 red. intros x0 y0 H' x1 y1 HE; rewrite HE; reflexivity.

  rewrite <- IHt2. rewrite int_lift_rec_eq. reflexivity.
Qed.

Lemma lift_int_lift_trm : forall t n,
  eq_term (lift n (int_fotrm t)) (int_fotrm (lift_trm t n)).
unfold lift, lift_trm. intros. apply lift_int_lift_trm_rec.
Qed.


Lemma lift_int_lift_fml_rec : forall f n k,
  eq_term (lift_rec n k (int_fofml f)) 
          (int_fofml (lift_fml_rec f n k)).
induction f; red; simpl; red; intros; try reflexivity.
 apply subset_morph; try reflexivity.
  red; intros. do 2 rewrite <- lift_int_lift_trm_rec.
  do 2 rewrite <- int_lift_rec_eq. rewrite H; reflexivity.

 apply prod_ext.
  rewrite <- IHf. symmetry. rewrite H. apply int_lift_rec_eq.

  red. reflexivity.

 apply subset_morph; try red; intros; 
   rewrite <- IHf1; rewrite <- IHf2; rewrite H.
  apply union_morph. 
  apply pair_morph; symmetry; apply int_lift_rec_eq.

  do 2 rewrite int_lift_rec_eq. reflexivity.

 apply union2_morph; rewrite H; 
   [rewrite <- IHf1 | rewrite <- IHf2]; symmetry;
     apply int_lift_rec_eq.

 apply prod_ext; try red; intros; 
   [rewrite <- IHf1 | rewrite <- IHf2]; rewrite H;
     symmetry; apply int_lift_rec_eq.

 apply prod_ext; try reflexivity.
  red; intros. rewrite <- IHf. rewrite V.cons_lams.
   rewrite int_lift_rec_eq. rewrite H1. rewrite H. reflexivity.

   do 2 red. intros. rewrite H2. reflexivity.

 apply union_morph. apply replf_morph; try reflexivity.
  red. intros. rewrite <- IHf. rewrite int_lift_rec_eq.
  rewrite V.cons_lams.
   rewrite H; rewrite H1; reflexivity.

   do 2 red; intros. rewrite H2. reflexivity.
Qed.

Lemma lift_int_lift_fml : forall f n,
  eq_term (lift n (int_fofml f)) (int_fofml (lift_fml f n)).
unfold lift, lift_fml; intros. apply lift_int_lift_fml_rec.
Qed. 


Lemma subst_int_subst_trm_rec : forall t N k, 
  eq_term (subst_rec (int_fotrm N) k (int_fotrm t)) 
  (int_fotrm (subst_trm_rec t N k)).
induction t; intros.
 
 do 2 red; simpl.
 destruct (Compare_dec.lt_eq_lt_dec k n) as [[fv|eqv]|bv]; simpl.
  unfold V.lams, V.shift; destruct (Compare_dec.le_gt_dec k n);
  try (apply False_ind; omega; fail).
  replace (n-k) with (S(Peano.pred n-k)) by omega; simpl.
  replace (k+(Peano.pred n-k)) with (Peano.pred n) by omega; 
    red; auto.

  case_eq (int_fotrm (lift_trm N k)); intros.
   red; intros. subst k. unfold V.lams; simpl.
   destruct (Compare_dec.le_gt_dec n n).
    replace (n-n) with 0 by omega; simpl. rewrite H0.
    setoid_replace (V.shift n y) with (V.lams 0 (V.shift n) y).
     rewrite <- int_lift_rec_eq. fold (lift n (int_fotrm N)).
     rewrite lift_int_lift_trm. rewrite H. simpl. reflexivity.

     rewrite V.lams0; reflexivity.

    apply False_ind; omega.
   
   elim fotrm_Some with (1:=H).

  do 2 red; intros. rewrite V.lams_bv; trivial. apply H.

 do 2 red. simpl. do 2 red. reflexivity.
 
 do 2 red; simpl; intros. do 2 red. intros. 
 apply succ_morph. reflexivity.

 do 2 red; simpl; intros. do 2 red; intros. apply NATREC_morph.
  rewrite <- IHt1. rewrite H. 
  rewrite int_subst_rec_eq; reflexivity.

  do 2 red; intros. rewrite H1; reflexivity.
   
  rewrite <- IHt2. rewrite H. 
  rewrite int_subst_rec_eq; reflexivity.
Qed.

Lemma subst_int_subst_trm : forall t N, 
  eq_term (subst (int_fotrm N) (int_fotrm t)) 
          (int_fotrm (subst_trm t N)).
unfold subst. intros. apply subst_int_subst_trm_rec with (k:=0).
Qed.

     
Lemma subst_int_subst_fml_rec : forall f N k,
  eq_term (subst_rec (int_fotrm N) k (int_fofml f)) 
          (int_fofml (subst_fml f N k)).
induction f; do 2 red; simpl; intros.
 do 2 red; intros. apply subset_morph; try reflexivity.
  red; intros. do 2 rewrite <- subst_int_subst_trm_rec.
  do 2 rewrite int_subst_rec_eq. rewrite H; reflexivity.

 do 2 red; reflexivity.

 do 2 red; reflexivity.

 do 2 red; intros. apply prod_ext.
  rewrite <- IHf. rewrite int_subst_rec_eq. rewrite H; reflexivity.

  red; reflexivity.

 do 2 red; intros. apply subset_morph.
  apply union2_morph; [rewrite <- IHf1 | rewrite <- IHf2];
  rewrite int_subst_rec_eq; rewrite H; reflexivity.
    
  red; intros. rewrite <- IHf1; rewrite <- IHf2.
  do 2 rewrite <- int_subst_rec_eq. rewrite H. reflexivity.

 do 2 red; intros. 
 apply union2_morph; [rewrite <- IHf1 | rewrite <- IHf2];
   rewrite int_subst_rec_eq; rewrite H; reflexivity.
 
 red; intros. apply prod_ext.
  rewrite H. rewrite <- IHf1. 
  rewrite int_subst_rec_eq; reflexivity.

  red; intros. rewrite <- IHf2. 
  rewrite <- int_subst_rec_eq. rewrite H; reflexivity.

 red; intros. rewrite prod_ext; try reflexivity.
  red; intros. rewrite <- IHf. rewrite V.cons_lams.
   rewrite int_subst_rec_eq. rewrite H. rewrite V.shift_split.
   rewrite V.shift_cons. rewrite H1. reflexivity.

   do 4 red; intros. rewrite H2; reflexivity.

 do 2 red; intros. apply union_morph. 
 apply replf_morph; try reflexivity.
  red; intros. rewrite <- IHf. rewrite int_subst_rec_eq.
   rewrite V.cons_lams. rewrite V.shift_split. 
   rewrite V.shift_cons. rewrite H1; rewrite H. reflexivity.

   do 4 red; intros. rewrite H2; reflexivity.
Qed.

Lemma subst_int_subst_fml : forall f N,
  eq_term (subst (int_fotrm N) (int_fofml f)) 
          (int_fofml (subst_fml0 f N)).
unfold subst; intros; apply subst_int_subst_fml_rec.
Qed.

Lemma fofml_in_props : forall f e, 
  typ e (int_fofml f) prop.
induction f; do 2 red; simpl; intros; unfold props; 
unfold ZFcoc.props; rewrite power_ax; intros; trivial.
 unfold EQ in H0. unfold cond_set in H0.
 rewrite subset_ax in H0. destruct H0; trivial.
 
 apply empty_ax in H0; contradiction. 

 revert y H0. rewrite <- power_ax. apply impredicative_prod.
  do 2 red; reflexivity.

  unfold props; unfold ZFcoc.props; intros.
  rewrite power_ax; intros.
  apply empty_ax in H1; contradiction.

 do 2 red in IHf1; simpl in IHf1.
 rewrite subset_ax in H0. destruct H0. destruct H1. destruct H2.
 rewrite H1. clear H1 H3. revert x H2. rewrite <- power_ax.
 fold ZFcoc.props. fold props. apply IHf1 with (e:=e); trivial.
 

 apply union2_elim in H0. destruct H0; revert y H0; 
 rewrite <- power_ax; fold ZFcoc.props; fold props; 
     [do 2 red in IHf1; simpl in IHf1; apply IHf1 with (e:=e) 
       | do 2 red in IHf1; simpl in IHf1; apply IHf2 with (e:=e)]; 
     trivial.

 revert y H0. rewrite <- power_ax. apply impredicative_prod.
  do 2 red; reflexivity.

  intros. do 2 red in IHf2; simpl in IHf2; 
  apply IHf2 with (e:=e); trivial.

 revert y H0. rewrite <- power_ax. apply impredicative_prod.
  do 2 red. intros y1 y2 Hy1N H0; rewrite H0; reflexivity.

  intros. do 2 red in IHf; simpl in IHf; 
  apply IHf with (e:=(T::e)).
  apply vcons_add_var; simpl; trivial.

 apply union_elim in H0. destruct H0. 
 apply replf_elim in H1.
  destruct H1. revert y H0. rewrite <- power_ax. rewrite H2. 
  do 2 red in IHf; simpl in IHf; apply IHf with (e:=(T::e)).
   apply vcons_add_var; simpl; trivial.

  do 2 red. intros. rewrite H3; reflexivity.
Qed.

Lemma P_ax_intro5_ex : forall P, eq_term 
  (Impl (int_fofml (subst_fml0 P Cst_0)) (Impl (Fall (Impl (int_fofml P)
    (int_fofml (subst_fml0 (lift_fml_rec P 1 1) (Df_Add (Var 0) Cst_1)))))
  (Fall (int_fofml P))))
  (Impl (subst Zero (int_fofml P))
    (Impl (Fall (Impl (int_fofml P)
      (subst (Add (Ref 0) (Succ Zero)) (lift_rec 1 1 (int_fofml P)))))
    (Fall (int_fofml P)))).
red; simpl; red; intros.
apply prod_ext.
 rewrite <- subst_int_subst_fml; simpl. rewrite H; reflexivity.

 red; intros. apply prod_ext.
  apply prod_ext; try reflexivity.
   red; intros. apply prod_ext.
    apply int_morph; try reflexivity.
     replace (fun k : nat => V.cons y0 (fun k0 : nat => x k0) k)
       with (V.cons y0 x); trivial.
     rewrite H3, H. reflexivity.

     red; intros. rewrite <- subst_int_subst_fml. simpl.
     do 2 rewrite int_subst_eq. rewrite <- lift_int_lift_fml_rec.
     replace (fun k : nat => V.cons y0 (fun k0 : nat => x k0) k) with
       (V.cons y0 x); trivial.
     replace (fun k : nat => V.cons y3 (fun k0 : nat => y k0) k) with
       (V.cons y3 y); trivial.
     rewrite H. rewrite H3. reflexivity.
   
   red; intros. apply prod_ext; try reflexivity.
    red; intros. rewrite H5.
    replace (fun k : nat => x k) with x; trivial.
    replace (fun k : nat => y k) with y; trivial.
    rewrite H; reflexivity.
Qed.

Lemma int_correct : forall hyp P, deriv hyp P -> 
  exists p, typ ((int_hyp hyp)) p (int_fofml P).
induction 1; simpl.
(*hyp*)
 exists (Ref n); red; simpl; intros. unfold val_ok in H0.
 rewrite <- lift_int_lift_fml. apply H0. apply int_hyp_nth_fml; trivial.

(*ax_intro*)
destruct H. 
 rewrite H; simpl. apply P_ax_intro1.
 
 destruct H.
  rewrite H; simpl. apply P_ax_intro2.

  destruct H.
   rewrite H; simpl. apply P_ax_intro3.
   
   destruct H.
    rewrite H; simpl. apply P_ax_intro4.

    destruct H; rewrite H. generalize P_ax_intro5; intros.
     specialize H0 with (e:=(int_hyp hyp)) (1:=(fofml_Some x)).
     destruct H0. exists x0. simpl. rewrite P_ax_intro5_ex; trivial.

(*true_intro*)
 apply True_symb_intro.
 
(*false_elim*)
 apply False_symb_elim. simpl in IHderiv. trivial.

(*neg_intro*)
 destruct IHderiv as (p, IH). exists p.
 apply Neg_intro. trivial.

(*neg_elim*)
 destruct IHderiv. exists x. apply Neg_elim. trivial.

(*conj_intro*)
 destruct IHderiv1 as (x, IH1). 
 destruct IHderiv2 as (x', IH2). 
 exists x.
 apply Conj_intro; try apply fofml_Some. split; trivial.
  do 2 red; intros. case_eq (int_fofml f2); intros; trivial. 
   assert (int x i == int x' i).
    generalize (proof_irr _ _ _  (fofml_Some f1) IH1 
    (fofml_in_props f1 (int_hyp hyp))); intros. specialize H3 with (1:=H1).
    generalize (proof_irr _ _ _  (fofml_Some f2) IH2 
    (fofml_in_props f2 (int_hyp hyp))); intros. specialize H4 with (1:=H1).
    rewrite H3, H4; reflexivity.
   rewrite H3. do 2 red in IH2. rewrite H2 in IH2. 
   apply IH2; trivial.

(*conj_elim1*)
destruct IHderiv. exists x. simpl in H0. apply Conj_elim in H0.
 destruct H0; trivial.

 apply fofml_Some.

 apply fofml_Some.

(*conj_elim2*)
destruct IHderiv. exists x. simpl in H0. apply Conj_elim in H0.
 destruct H0; trivial.

 apply fofml_Some.

 apply fofml_Some.

(*disj_intro1*)
 destruct IHderiv. exists x. 
 apply Disj_intro; try apply fofml_Some.
 left; trivial.
 
(*disj_intro2*)
 destruct IHderiv. exists x. 
 apply Disj_intro; try apply fofml_Some.
 right; trivial.

(*disj_elim*)
 destruct IHderiv1, IHderiv2, IHderiv3.
 exists prf_term. simpl in H2, H3, H4. 
 apply Disj_elim with (t:=x) (t1:=x0) (t2:=x1) 
   (A:=int_fofml f1) (B:=int_fofml f2); try rewrite lift_int_lift_fml; trivial.
  apply fofml_Some.

  apply fofml_in_props.

(*impl_intro*)
 destruct IHderiv. simpl in H0.
 exists (Abs (int_fofml f1) x).
 apply Impl_intro; try apply fofml_Some.
 rewrite lift_int_lift_fml; trivial.

(*impl_elim*)
 destruct IHderiv1, IHderiv2. exists (App x x0).
 apply Impl_elim with (A:=int_fofml f1); try apply fofml_Some; trivial.
 

(*fall_intro*)
 destruct IHderiv. simpl in H0.
 exists ((Abs T x)). apply Fall_intro; try apply fofml_Some; trivial.

(*fall_elim*)
 destruct IHderiv. exists (App x (int_fotrm u)).
 rewrite <- subst_int_subst_fml. 
 apply Fall_elim; try apply fofml_Some; trivial.
  do 2 red; simpl; intros. apply int_trm_N with (hyp:=hyp); trivial.

(*exst_intro*)
 destruct IHderiv; simpl in H0.
 exists x. apply Exst_intro with (a:=(int_fotrm N)); try apply fofml_Some.
  do 2 red; simpl; intros. apply int_trm_N with (hyp:=hyp); trivial.

  do 2 red; intros. do 2 red in H1; specialize H1 with (1:=H2).
  case_eq (subst (int_fotrm N) (int_fofml f)); intros.
   rewrite <- H3. case_eq (int_fofml (subst_fml0 f N)); intros.
    rewrite H4 in H1; rewrite <- H4 in H1.
    rewrite subst_int_subst_fml; trivial.

    elim fofml_Some with (f:=(subst_fml0 f N)); trivial.

  elim subst_Some with (t:=(int_fofml f)) (a:=(int_fotrm N));
  [apply fofml_Some |  trivial ].

(*exst_elim*)
destruct IHderiv1, IHderiv2. simpl in H1, H2.
exists prf_term. apply Exst_elim with (t1:=x) (t2:=x0) (A:=int_fofml f); trivial.
 apply fofml_Some.

 apply fofml_in_props.

 rewrite lift_int_lift_fml; trivial.
Qed.



Fixpoint const_env n := 
  match n with
    | 0 => T :: nil
    | S m => T :: (const_env m)
  end.

Lemma const_env_spec : forall m n t, 
  nth_error (const_env n) m = value t ->
  (m <= n)%nat /\ t = T.
induction m; destruct n; simpl; intros.
 injection H; intros; split; [|subst t]; trivial.

 injection H; intros; split; [omega |subst t]; trivial.

 destruct m; simpl in H; discriminate.

 specialize IHm with (1:=H). destruct IHm.
 split; [omega | trivial].
Qed.

Lemma eq_ext : forall e t1 t2 s s',
  eq_typ (const_env (Peano.max (max_var t1) (max_var t2)))
  (int_fotrm t1) (int_fotrm t2) ->
  eq_fosub (S (Peano.max (max_var t1) (max_var t2))) e s s' ->
  eq_typ e (app_esub s (int_fotrm t1)) (app_esub s' (int_fotrm t2)).
do 2 red; simpl; intros.
do 2 red in H; simpl.
unfold eq_fosub in H0.
assert (val_ok (const_env (Peano.max (max_var t1) (max_var t2))) (esub_conv s i)).
 unfold val_ok. do 2 red; intros. apply const_env_spec in H2.
 destruct H2; subst T; simpl.
 assert (n < S (Peano.max (max_var t1) (max_var t2)))%nat by omega.
 specialize H0 with (1:=H3); destruct H0 as (Heqtyp, (Htyps, Htyps')).
 do 2 red in Htyps; simpl in Htyps; specialize Htyps with (1:=H1). apply Htyps.

specialize H with (1:=H2). rewrite H.
replace (fun k : nat => i k) with i; trivial. clear H H2.

induction t2; simpl; try reflexivity.
 specialize H0 with (n0:=n). destruct H0.
  rewrite succ_max_distr. apply max_split2. unfold max_var; simpl; omega.
  do 2 red in H; simpl in H; apply H; trivial.

 apply NATREC_morph.
  apply IHt2_1. intros. apply H0.
  rewrite succ_max_distr. rewrite succ_max_distr in H. 
  apply max_comb in H. destruct H.
   apply max_split1; trivial.

   apply max_split2. unfold max_var; simpl.
   rewrite succ_max_distr. apply max_split1. trivial.

  do 2 red; intros. rewrite H2; reflexivity.

  apply IHt2_2. intros. apply H0.
  rewrite succ_max_distr. rewrite succ_max_distr in H. 
  apply max_comb in H. destruct H.
   apply max_split1; trivial.

   apply max_split2. unfold max_var; simpl.
   rewrite succ_max_distr. apply max_split2. trivial.
Qed.
