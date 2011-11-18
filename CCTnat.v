Require Import TheoryInTerm.
Require Import GenModel.

Import IZF.

Import BuildModel.
Import T J.
Import CCM.

Fixpoint int_fotrm t:=
  match t with
  | Val i => Ref i
  | Cst_0 => Zero
  | Cst_S u => Succ (int_fotrm u)
  | Df_Add u v => Add (int_fotrm u) (int_fotrm v)
  end.

Fixpoint int_fofml f:=
  match f with
  | atom P l => predicate P l
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

Lemma subst_Some : forall f t, f <> None -> t <> None -> 
  subst t f <> None.
destruct f; simpl; red; intros. 
 destruct s; discriminate.

 elim H; trivial.
Qed.

Lemma nth_hyp_inthyp : forall hyp n, nth_error hyp n = value None ->
  nth_error (int_hyp hyp) n = value T.
induction hyp; destruct n; simpl; intros; try discriminate.
 destruct a; [discriminate | trivial].
 destruct a; apply IHhyp; trivial.
Qed.

Lemma int_trm_N : forall hyp t i, hyp_ok hyp t -> 
  val_ok (int_hyp hyp) i ->
  int (int_fotrm t) i \in N.
unfold hyp_ok; unfold val_ok; induction t; simpl in *; intros.
 assert (n=n\/False). left; trivial.
 specialize H with (n0:=n) (1:=H1).
 generalize (nth_hyp_inthyp _ _ H); intros.
 specialize H0 with (1:=H2). simpl in H0; trivial.

 apply zero_typ.
 
 apply succ_typ. apply IHt; trivial.

 replace (fun k : nat => i k) with i; trivial.
 assert (int (int_fotrm t2) i \in N).
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
  eq_term (lift_rec n k (int_fotrm t)) (int_fotrm (lift_trm_rec t n k)).
induction t; simpl; intros.
 unfold V.lams. unfold V.shift.
 destruct (Compare_dec.le_gt_dec k n); simpl; intros.
  replace (k+(n0+(n-k))) with (n+n0) by omega.
  red; auto.

  red; auto.

 red; reflexivity.

 red; intros. apply succ_morph. rewrite <- IHt.
 rewrite int_lift_rec_eq. rewrite H; reflexivity.

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
  eq_term (lift_rec n k (int_fofml f)) (int_fofml (lift_fml_rec f n k)).
induction f; red; simpl; red; intros; try reflexivity.
 apply subset_morph; try reflexivity.
  red; intros. split; trivial; intro HP; destruct HP as (Hl, Hs);
  unfold predicate_stable in Hs; destruct (Hs l n k Cst_0) as (Hlift, Hsubst); 
  fold (predicate_stable P) in Hs; split;
  [rewrite <- Hlift | trivial | rewrite Hlift | trivial]; trivial.

 apply prod_ext.
  rewrite <- IHf. symmetry. rewrite H. apply int_lift_rec_eq.

  red. reflexivity.

 apply subset_morph; try red; intros; rewrite <- IHf1; rewrite <- IHf2; rewrite H.
  apply union_morph. apply pair_morph; symmetry; apply int_lift_rec_eq.

  do 2 rewrite int_lift_rec_eq. reflexivity.

 apply union2_morph; rewrite H; [rewrite <- IHf1 | rewrite <- IHf2]; symmetry;
 apply int_lift_rec_eq.

 apply prod_ext; try red; intros; [rewrite <- IHf1 | rewrite <- IHf2]; rewrite H;
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
  eq_term (subst_rec (int_fotrm N) k (int_fotrm t)) (int_fotrm (subst_trm t N k)).
induction t; intros.
 
 do 2 red; simpl.
 destruct (Compare_dec.lt_eq_lt_dec k n) as [[fv|eqv]|bv]; simpl.
  unfold V.lams, V.shift; destruct (Compare_dec.le_gt_dec k n);
  try (apply False_ind; omega; fail).
  replace (n-k) with (S(Peano.pred n-k)) by omega; simpl.
  replace (k+(Peano.pred n-k)) with (Peano.pred n) by omega; red; auto.

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
 
 do 2 red; simpl; intros. do 2 red. intros. apply succ_morph.
 rewrite <- IHt. rewrite H. rewrite int_subst_rec_eq; reflexivity.

 do 2 red; simpl; intros. do 2 red; intros. apply NATREC_morph.
  rewrite <- IHt1. rewrite H. rewrite int_subst_rec_eq; reflexivity.

  do 2 red; intros. rewrite H1; reflexivity.
   
  rewrite <- IHt2. rewrite H. rewrite int_subst_rec_eq; reflexivity.
Qed.

Lemma subst_int_subst_trm : forall t N, 
  eq_term (subst (int_fotrm N) (int_fotrm t)) (int_fotrm (subst_trm t N 0)).
unfold subst. intros. apply subst_int_subst_trm_rec with (k:=0).
Qed.

     
Lemma subst_int_subst_fml_rec : forall f N k,
  eq_term (subst_rec (int_fotrm N) k (int_fofml f)) (int_fofml (subst_fml f N k)).
induction f; do 2 red; simpl; intros.
 do 2 red; intros. apply subset_morph; try reflexivity.
  red; intros. split; intro HP; destruct HP as (Hl, Hs);
  unfold predicate_stable in Hs; destruct (Hs l 0 k N) as (Hlift, Hsubst); 
  fold (predicate_stable P) in Hs; split;
  [rewrite <- Hsubst | trivial | rewrite Hsubst | trivial]; trivial.

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

 do 2 red; intros. apply union2_morph; [rewrite <- IHf1 | rewrite <- IHf2];
  rewrite int_subst_rec_eq; rewrite H; reflexivity.

 red; intros. apply prod_ext.
  rewrite H. rewrite <- IHf1. rewrite int_subst_rec_eq; reflexivity.

  red; intros. rewrite <- IHf2. rewrite <- int_subst_rec_eq. rewrite H; reflexivity.

 red; intros. rewrite prod_ext; try reflexivity.
  red; intros. rewrite <- IHf. rewrite V.cons_lams.
   rewrite int_subst_rec_eq. rewrite H. rewrite V.shift_split.
   rewrite V.shift_cons. rewrite H1. reflexivity.

   do 4 red; intros. rewrite H2; reflexivity.

 do 2 red; intros. apply union_morph. apply replf_morph; try reflexivity.
  red; intros. rewrite <- IHf. rewrite int_subst_rec_eq.
   rewrite V.cons_lams. rewrite V.shift_split. rewrite V.shift_cons.
   rewrite H1; rewrite H. reflexivity.

   do 4 red; intros. rewrite H2; reflexivity.
Qed.

Lemma subst_int_subst_fml : forall f N,
  eq_term (subst (int_fotrm N) (int_fofml f)) (int_fofml (subst_fml0 f N)).
unfold subst; intros; apply subst_int_subst_fml_rec.
Qed.

Lemma fofml_in_props : forall f e, 
  typ e (int_fofml f) prop.
induction f; do 2 red; simpl; intros; unfold props; 
unfold ZFcoc.props; rewrite power_ax; intros; trivial.
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
 | do 2 red in IHf1; simpl in IHf1; apply IHf2 with (e:=e)]; trivial.

 revert y H0. rewrite <- power_ax. apply impredicative_prod.
  do 2 red; reflexivity.

  intros. do 2 red in IHf2; simpl in IHf2; apply IHf2 with (e:=e); trivial.

 revert y H0. rewrite <- power_ax. apply impredicative_prod.
  do 2 red. intros y1 y2 Hy1N H0; rewrite H0; reflexivity.

  intros. do 2 red in IHf; simpl in IHf; apply IHf with (e:=(T::e)).
  apply vcons_add_var; simpl; trivial.

 apply union_elim in H0. destruct H0. 
 apply replf_elim in H1.
  destruct H1. revert y H0. rewrite <- power_ax. rewrite H2. 
  do 2 red in IHf; simpl in IHf; apply IHf with (e:=(T::e)).
   apply vcons_add_var; simpl; trivial.

  do 2 red. intros. rewrite H3; reflexivity.
Qed.

Lemma int_correct : forall hyp P, deriv hyp P -> 
  exists p, typ ((int_hyp hyp)) p (int_fofml P).
induction 1; simpl.
(*weak*)
 exists (Ref 0). red; simpl; intros.
 unfold val_ok in H.
 assert (nth_error (int_fofml f :: int_hyp hyp) 0 = value (int_fofml f)); trivial.
 specialize H with (1:=H0). rewrite <- lift_int_lift_fml. trivial. 

(*atom*)
 exists False_symb. apply predicate_intro; trivial.

(*neg*)
 destruct IHderiv as (p, IH). exists p.
 apply Neg_intro. trivial.

(*conj*)
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

(*disj1*)
 destruct IHderiv. exists x. 
 apply Disj_intro; try apply fofml_Some.
 left; trivial.
 
(*disj2*)
 destruct IHderiv. exists x. 
 apply Disj_intro; try apply fofml_Some.
 right; trivial.

(*impl*)
 destruct IHderiv. simpl in H0.
 exists (Abs (int_fofml f1) x).
 apply Impl_intro; try apply fofml_Some.
 rewrite lift_int_lift_fml; trivial.

(*fall*)
 destruct IHderiv. simpl in H0.
 exists ((Abs T x)). apply Fall_intro; try apply fofml_Some; trivial.

(*exst*)
 destruct IHderiv; simpl in H0.
 exists x. apply Exst_intro with (a:=(int_fotrm N)); try apply fofml_Some.
  do 2 red; simpl; intros. apply int_trm_N with (hyp:=hyp); trivial.

  do 2 red; intros. do 2 red in H1; specialize H1 with (1:=H2).
  case_eq (subst (int_fotrm N) (int_fofml f)); intros.
   rewrite <- H3. case_eq (int_fofml (subst_fml0 f N)); intros.
    rewrite H4 in H1; rewrite <- H4 in H1.
    rewrite subst_int_subst_fml; trivial.

    elim fofml_Some with (f:=(subst_fml0 f N)); trivial.

  elim subst_Some with (f:=(int_fofml f)) (t:=(int_fotrm N));
  [apply fofml_Some | apply fotrm_Some | trivial ].
Qed.

 
 


      
















