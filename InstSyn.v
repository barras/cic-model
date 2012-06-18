Require Import ModelTheory.
Import Compare_dec List.

(*Instantiate the syntax of First Order Theory with Presburger*)
Module PresburgerSyn <: TheorySyn.

Inductive foterm' :=
| Var' : nat -> foterm'
| Cst_0' : foterm'
| Cst_1' : foterm'
| Df_Add' : foterm' -> foterm' -> foterm'.

Definition foterm := foterm'.
Definition Var := Var'.
Definition Cst_0 := Cst_0'.
Definition Cst_1 := Cst_1'.
Definition Df_Add := Df_Add'.

Fixpoint lift_trm_rec t n k:=
  match t with
    | Var i => 
      match le_gt_dec k i with
        | left _ => Var (i+n)
        | right _ => Var i
      end
    | Cst_0 => Cst_0
    | Cst_1 => Cst_1
    | Df_Add u v => Df_Add (lift_trm_rec u n k) (lift_trm_rec v n k)
  end.

Definition lift_trm t n := lift_trm_rec t n 0.

Fixpoint subst_trm_rec M N n:= 
  match M with
    | Var i =>
      match lt_eq_lt_dec n i with
        | inleft (left _) => Var (pred i)
        | inleft (right _) => lift_trm N n
        | inright _ => Var i
      end
    | Cst_0 => Cst_0
    | Cst_1 => Cst_1
    | Df_Add M1 M2 => Df_Add (subst_trm_rec M1 N n) (subst_trm_rec M2 N n)
  end.

Definition subst_trm M N := subst_trm_rec M N 0.

Fixpoint fv_trm_rec t k : list nat :=
  match t with
    | Var n => 
      match le_gt_dec k n with
        | left _ => (n-k)::nil
        | right _ => nil
      end
    | Cst_0 => nil
    | Cst_1 => nil
    | Df_Add M N => (fv_trm_rec M k) ++ (fv_trm_rec N k)
  end.

Definition fv_trm t := fv_trm_rec t 0.

Inductive foformula' :=
| eq_fotrm' : foterm -> foterm -> foformula'
| TF'   : foformula'
| BF'   : foformula'
| neg' : foformula' -> foformula'
| conj' : foformula' -> foformula' -> foformula'
| disj' : foformula' -> foformula' -> foformula'
| implf' : foformula' -> foformula' -> foformula'
| fall' : foformula' -> foformula'
| exst' : foformula' -> foformula'.

Definition foformula := foformula'.
Definition eq_fotrm := eq_fotrm'.
Definition TF := TF'.
Definition BF := BF'.
Definition neg := neg'.
Definition conj := conj'.
Definition disj := disj'.
Definition implf := implf'. 
Definition fall := fall'.
Definition exst := exst'.

Fixpoint lift_fml_rec f n k:=
  match f with
    | eq_fotrm x y => eq_fotrm (lift_trm_rec x n k) (lift_trm_rec y n k)
    | TF => TF
    | BF => BF
    | neg f' => neg (lift_fml_rec f' n k)
    | conj A B => conj (lift_fml_rec A n k) (lift_fml_rec B n k)
    | disj A B => disj (lift_fml_rec A n k) (lift_fml_rec B n k)
    | implf A B => implf (lift_fml_rec A n k) (lift_fml_rec B n k)
    | fall A => fall (lift_fml_rec A n (S k))
    | exst A => exst (lift_fml_rec A n (S k))
  end.

Definition lift_fml t n := lift_fml_rec t n 0.

Fixpoint subst_fml_rec f N n :=
  match f with
    | eq_fotrm x y => eq_fotrm (subst_trm_rec x N n) (subst_trm_rec y N n)
    | TF => TF
    | BF => BF
    | neg f => neg (subst_fml_rec f N n)
    | conj f1 f2 => conj (subst_fml_rec f1 N n) (subst_fml_rec f2 N n)
    | disj f1 f2 => disj (subst_fml_rec f1 N n) (subst_fml_rec f2 N n)
    | implf f1 f2 => implf (subst_fml_rec f1 N n) (subst_fml_rec f2 N n)
    | fall f => fall (subst_fml_rec f N (S n))
    | exst f => exst (subst_fml_rec f N (S n))
  end.

Definition subst_fml f N := subst_fml_rec f N 0.

Fixpoint fv_fml_rec f k : list nat :=
  match f with
    | eq_fotrm t1 t2 => (fv_trm_rec t1 k) ++ (fv_trm_rec t2 k)
    | TF => nil
    | BF => nil
    | neg f0 => fv_fml_rec f0 k
    | conj f1 f2 => (fv_fml_rec f1 k) ++ (fv_fml_rec f2 k)
    | disj f1 f2 => (fv_fml_rec f1 k) ++ (fv_fml_rec f2 k)
    | implf f1 f2 => (fv_fml_rec f1 k) ++ (fv_fml_rec f2 k)
    | fall f0 => (fv_fml_rec f0 (S k))
    | exst f0 => (fv_fml_rec f0 (S k))
  end.

Definition fv_fml f := fv_fml_rec f 0.

Lemma fv_fml_eq_trm : forall x y,
  fv_fml (eq_fotrm x y) = (fv_trm x) ++ (fv_trm y).
unfold fv_fml, fv_trm; simpl; trivial.
Qed.

Lemma fv_fml_neg : forall f,
  fv_fml (neg f) = fv_fml f.
unfold fv_fml; simpl; trivial.
Qed.

Lemma fv_fml_conj : forall x y,
  fv_fml (conj x y) = (fv_fml x) ++ (fv_fml y).
unfold fv_fml; simpl; trivial.
Qed.

Lemma fv_fml_disj : forall x y,
  fv_fml (disj x y) = (fv_fml x) ++ (fv_fml y).
unfold fv_fml; simpl; trivial.
Qed.

Lemma fv_fml_implf : forall x y,
  fv_fml (implf x y) = (fv_fml x) ++ (fv_fml y).
unfold fv_fml; simpl; trivial.
Qed.

Lemma fv_fml_fall : forall f,
  fv_fml (fall f) = (fv_fml_rec f 1).
unfold fv_fml; simpl; trivial.
Qed.

Lemma fv_fml_exst : forall f,
  fv_fml (exst f) = (fv_fml_rec f 1).
unfold fv_fml; simpl; trivial.
Qed.

Definition hyp_ok_trm (hyp:list (option foformula)) t := 
  forall n, In n (fv_trm t) -> nth_error hyp n = Some None.

Definition hyp_ok_fml (hyp:list (option foformula)) f := 
  forall n, In n (fv_fml f) -> nth_error hyp n = Some None.

Definition ax hyp f :=
  f = (fall (neg (eq_fotrm Cst_0 (Df_Add (Var 0) Cst_1))))      \/
  f = (fall (fall (implf (eq_fotrm (Df_Add (Var 0) Cst_1) 
    (Df_Add (Var 1) Cst_1)) (eq_fotrm (Var 0) (Var 1)))))       \/
  f = (fall (eq_fotrm (Var 0) (Df_Add (Var 0) Cst_0)))          \/
  f = (fall(fall (eq_fotrm (Df_Add (Df_Add (Var 0) (Var 1)) Cst_1) 
                   (Df_Add (Var 0) (Df_Add (Var 1) (Cst_1)))))) \/
  exists g, (hyp_ok_fml (None::hyp) g) /\ f = (implf (subst_fml g Cst_0) 
    (implf (fall (implf g 
      (subst_fml (lift_fml_rec g 1 1) (Df_Add (Var 0) Cst_1)))) 
    (fall g))).

Inductive deriv : list (option foformula) -> foformula -> Prop :=
| hyp_judge : forall f hyp n, 
  nth_error hyp n = Some (Some f) ->
  hyp_ok_fml hyp (lift_fml f (S n)) ->
  deriv hyp (lift_fml f (S n))
| ax_intro : forall f hyp, ax hyp f -> deriv hyp f
| true_intro : forall hyp, deriv hyp TF
| false_elim : forall hyp f, deriv hyp BF -> hyp_ok_fml hyp f -> deriv hyp f
| neg_intro : forall hyp f, deriv hyp (implf f BF) -> deriv hyp (neg f)
| neg_elim : forall hyp f, deriv hyp (neg f) -> deriv hyp (implf f BF)
| conj_intro : forall hyp f1 f2, 
  deriv hyp f1 -> deriv hyp f2 -> deriv hyp (conj f1 f2)
| conj_elim1 : forall hyp f1 f2,
  deriv hyp (conj f1 f2) -> deriv hyp f1
| conj_elim2 : forall hyp f1 f2,
  deriv hyp (conj f1 f2) -> deriv hyp f2
| disj_intro1 : forall hyp f1 f2, 
  deriv hyp f1 -> hyp_ok_fml hyp f2 -> deriv hyp (disj f1 f2)
| disj_intro2 : forall hyp f1 f2, 
  hyp_ok_fml hyp f1 ->
  deriv hyp f2 -> deriv hyp (disj f1 f2)
| disj_elim : forall hyp f1 f2 f3,
  deriv hyp (disj f1 f2) -> deriv (Some f1::hyp) (lift_fml f3 1) -> 
  deriv (Some f2::hyp) (lift_fml f3 1) -> deriv hyp f3
| impl_intro : forall hyp f1 f2,
  hyp_ok_fml hyp f1 ->
  deriv ((Some f1)::hyp) (lift_fml f2 1) -> deriv hyp (implf f1 f2)
| impl_elim : forall hyp f1 f2,
  deriv hyp (implf f1 f2) -> deriv hyp f1 -> deriv hyp f2
| fall_intro : forall hyp f,
  deriv (None::hyp) f -> deriv hyp (fall f)
| fall_elim : forall hyp f u, 
  hyp_ok_trm hyp u -> deriv hyp (fall f) -> deriv hyp (subst_fml f u)
| exst_intro : forall hyp f N, hyp_ok_trm hyp N -> 
  deriv hyp (subst_fml f N) -> deriv hyp (exst f)
| exst_elim : forall hyp f f1, 
  deriv hyp (exst f) -> 
  deriv (Some f::None::hyp) (lift_fml f1 2) -> deriv hyp f1.

Lemma in_S_fv_trm : forall t n k,
  In (S n) (fv_trm_rec t k) <->
  In n (fv_trm_rec t (S k)).
induction t; split; [| |contradiction|contradiction|contradiction|contradiction| |]; intros.
 simpl in H. destruct (le_gt_dec k n); [|contradiction].
  simpl in H. destruct H; [|contradiction].
   assert (n = (S k + n0)) by omega.
   subst n. unfold fv_trm_rec.
   case_eq (le_gt_dec (S k) (S k + n0)); intros; [simpl; left|]; omega.

 unfold fv_trm_rec in H.
 case_eq (le_gt_dec (S k) n); intros; rewrite H0 in H; [|contradiction].
  simpl in H. destruct H; [|contradiction].
   assert (n = k + S n0) by omega.
   subst n; unfold fv_trm_rec.
   destruct (le_gt_dec k (k + S n0)); [simpl; left|]; omega.

 simpl in H |- *. rewrite in_app_iff in H |- *. 
 destruct H as [Hl|Hr]; [left; apply IHt1|right; apply IHt2]; trivial. 

 simpl in H |- *. rewrite in_app_iff in H |- *.
 destruct H as [Hl|Hr]; [left; apply IHt1|right; apply IHt2]; trivial. 
Qed.
 
Lemma in_S_fv_fml : forall f n k, 
  In (S n) (fv_fml_rec f k) <-> In n (fv_fml_rec f (S k)).
induction f; simpl; try reflexivity; trivial; intros; do 2 rewrite in_app_iff.
 do 2 rewrite in_S_fv_trm; reflexivity.

 rewrite IHf1, IHf2; reflexivity.

 rewrite IHf1, IHf2; reflexivity.

 rewrite IHf1, IHf2; reflexivity.
Qed.

Lemma lift_trm0 : forall t, lift_trm t 0 = t.
induction t; intros; unfold lift_trm; simpl; trivial.
 apply f_equal; omega.

 unfold lift_trm in IHt1, IHt2; rewrite IHt1, IHt2; trivial.
Qed.

Lemma in_fv_trm_lift : forall t n k k' k'',
  In n (fv_trm_rec (lift_trm_rec t k' k'') (k+k'+k'')) <->
  In n (fv_trm_rec t (k+k'')).
induction t; simpl; intros; try reflexivity.
 destruct (le_gt_dec k'' n) as [le|gt]; simpl.
  destruct (le_gt_dec (k+k'+k'') (n+k')) as [le'|gt]; [simpl|].
   destruct (le_gt_dec (k+k'') n) as [le''|gt]; [simpl|omega].
    replace (n+k'-(k+k'+k'')) with (n-(k+k'')) by omega; reflexivity.
   
   destruct (le_gt_dec (k+k'') n) as [le'|gt']; [omega|reflexivity].

  destruct (le_gt_dec (k+k'+k'') n) as [le|gt']; [omega|].
   destruct (le_gt_dec (k+k'') n) as [le|gt'']; [omega|reflexivity].

 do 2 rewrite in_app_iff. rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma in_fv_fml_lift : forall f n k k' k'',
  In n (fv_fml_rec (lift_fml_rec f k' k'') (k+k'+k'')) <->
  In n (fv_fml_rec f (k+k'')).
induction f; simpl; intros; try reflexivity; trivial.
 do 2 rewrite in_app_iff. do 2 rewrite in_fv_trm_lift; reflexivity.

 do 2 rewrite in_app_iff. rewrite IHf1, IHf2; reflexivity.

 do 2 rewrite in_app_iff. rewrite IHf1, IHf2; reflexivity.

 do 2 rewrite in_app_iff. rewrite IHf1, IHf2; reflexivity.

 replace (S (k + k'+ k'')) with (k + k' + S k'') by omega.
 replace (S (k + k'')) with (k + S k'') by omega. apply IHf; trivial.

 replace (S (k + k'+ k'')) with (k + k' + S k'') by omega.
 replace (S (k + k'')) with (k + S k'') by omega. apply IHf; trivial.
Qed.

Lemma in_fv_trm_subst_split : forall t n N k k',
  In n (fv_trm_rec (subst_trm_rec t N k') (k+k')) ->
  In n (fv_trm_rec N k) \/ In (S n) (fv_trm_rec t (k+k')).
induction t; intros.
 unfold subst_trm_rec in H |- *. simpl fv_trm_rec at 2.
 destruct (lt_eq_lt_dec k' n) as [[lt|eq]|gt].
  unfold fv_trm_rec in H; simpl in H.
  destruct (le_gt_dec (k+k') (pred n)) as [le|gt]; [|contradiction].
   simpl in H. destruct H; [right|contradiction].
   destruct (le_gt_dec (k+k') n) as [le'|gt]; [simpl; left|]; omega.

  subst n; left. unfold lift_trm in H. 
  replace (k+k') with (k+k'+0) in H by omega.
  apply (in_fv_trm_lift _ _ k k' 0) in H.
  replace (k+0) with k in H by omega; trivial.
  
  simpl in H. destruct (le_gt_dec (k+k') n) as [le|gt']; [omega|contradiction].

 simpl in H; contradiction.

 simpl in H; contradiction.

 simpl in H |- *. rewrite in_app_iff in H |- *. destruct H.
  apply IHt1 in H. destruct H; [left|right; left]; trivial.

  apply IHt2 in H. destruct H; [left|right; right]; trivial.
Qed.

Lemma in_fv_fml_subst_split : forall g n N k k',
  In n (fv_fml_rec (subst_fml_rec g N k') (k+k')) -> 
  In n (fv_trm_rec N k) \/ In (S n) (fv_fml_rec g (k+k')).
induction g; simpl; intros; try contradiction; trivial.
 rewrite in_app_iff in H |- *.
 destruct H as [H|H]; apply in_fv_trm_subst_split in H.
  destruct H; [left|right; left]; trivial.
  
  destruct H; [left|right; right]; trivial.

 apply IHg in H; trivial.
 
 rewrite in_app_iff in H |- *. destruct H as [H|H]; [apply IHg1 in H|apply IHg2 in H].
  destruct H; [left|right; left]; trivial.

  destruct H; [left|right; right]; trivial.

 rewrite in_app_iff in H |- *. destruct H as [H|H]; [apply IHg1 in H|apply IHg2 in H].
  destruct H; [left|right; left]; trivial.

  destruct H; [left|right; right]; trivial.

 rewrite in_app_iff in H |- *. destruct H as [H|H]; [apply IHg1 in H|apply IHg2 in H].
  destruct H; [left|right; left]; trivial.

  destruct H; [left|right; right]; trivial.

 replace (S (k + k')) with (k + S k') in H |- * by omega. apply IHg in H; trivial.

 replace (S (k + k')) with (k + S k') in H |- * by omega. apply IHg in H; trivial.
Qed.

Lemma in_fv_trm_subst : forall t n N k k',
  In (S n) (fv_trm_rec t (k+k')) ->
  In n (fv_trm_rec (subst_trm_rec t N k') (k+k')).
induction t; simpl; intros; trivial.
 destruct (le_gt_dec (k + k') n) as [le|gt]; [|contradiction].
  simpl in H. destruct H; [|contradiction].
   assert (n=S (k+k'+n0)) by omega.
   subst n. destruct (lt_eq_lt_dec k' (S (k+k'+n0))) as [[lt|eq]|lt]; [simpl|omega|omega].
    destruct (le_gt_dec (k + k') (k + k' + n0)) as [le'|gt]; [simpl; left|]; omega.

 rewrite in_app_iff in H |- *. destruct H; [left; apply IHt1|right; apply IHt2]; trivial.
Qed.

Lemma in_fv_fml_subst : forall f n N k k',
  In (S n) (fv_fml_rec f (k+k')) ->
  In n (fv_fml_rec (subst_fml_rec f N k') (k+k')).
induction f; simpl; intros; trivial.
 rewrite in_app_iff in H |- *.
 destruct H; [left|right]; apply in_fv_trm_subst; trivial.

 apply IHf; trivial.

 rewrite in_app_iff in H |- *.
 destruct H; [left; apply IHf1|right; apply IHf2]; trivial.

 rewrite in_app_iff in H |- *.
 destruct H; [left; apply IHf1|right; apply IHf2]; trivial.

 rewrite in_app_iff in H |- *.
 destruct H; [left; apply IHf1|right; apply IHf2]; trivial.

 replace (S (k + k')) with (k + S k') in H |- * by omega. apply IHf; trivial.

 replace (S (k + k')) with (k + S k') in H |- * by omega. apply IHf; trivial.
Qed.

Lemma lift_trm_split : forall t n k, 
  lift_trm_rec t (S n) k = lift_trm_rec (lift_trm_rec t n k) 1 k.
induction t; trivial; unfold lift_trm in *; simpl; intros.
 destruct (le_gt_dec k n) as [le|gt]; simpl.
  destruct (le_gt_dec k (n+n0)) as [le'|gt]; simpl; [apply f_equal|]; omega.

  destruct (le_gt_dec k n) as [le|gt']; simpl; [omega|trivial].

 rewrite IHt1, IHt2; trivial.
Qed.

Lemma lift_fml_split : forall f n k, 
  lift_fml_rec f (S n) k = lift_fml_rec (lift_fml_rec f n k) 1 k.
induction f; trivial; unfold lift_fml in *; simpl; intros.
 rewrite lift_trm_split with (t:=f).
 rewrite lift_trm_split with (t:=f0); trivial.

 rewrite IHf; trivial.

 rewrite IHf1, IHf2; trivial.
 
 rewrite IHf1, IHf2; trivial.

 rewrite IHf1, IHf2; trivial.

 rewrite IHf; trivial.

 rewrite IHf; trivial.
Qed.

Lemma hyp_ok_weakening : forall hyp t f',
  hyp_ok_fml (t :: hyp) (lift_fml f' 1) ->
  hyp_ok_fml hyp f'.
intros; red in H |- *; intros. specialize H with (n:= S n).
unfold fv_fml in H, H0. rewrite in_S_fv_fml in H.
unfold lift_fml in H. replace 1 with (0+1+0) in H by omega.
rewrite in_fv_fml_lift in H. simpl in H. apply H in H0; trivial.
Qed.

Lemma deriv_well_typed : forall hyp f, deriv hyp f -> hyp_ok_fml hyp f.
induction 1; trivial.
 destruct H as [H|[H|[H|[H|(g, (H', H))]]]]; subst f; 
   try (red; intros; simpl in H; contradiction).
 red in H' |- *; intros. unfold fv_fml in H; simpl in H.
 apply in_app_or in H. destruct H.
  unfold subst_fml in H. apply (in_fv_fml_subst_split _ _ _ 0 0) in H. 
  simpl in H. destruct H; [contradiction|apply H' in H; simpl in H; trivial].

  apply in_app_or in H. destruct H.
   apply in_app_or in H. destruct H.
    apply in_S_fv_fml in H. apply H' in H. simpl in H; trivial.

    unfold subst_fml in H. apply (in_fv_fml_subst_split _ _ _ 1 0) in H.
    simpl in H. destruct H; [contradiction|].
    rewrite in_S_fv_fml in H. replace 2 with (0+1+1) in H by omega.
    apply in_fv_fml_lift in H. simpl in H. rewrite <- in_S_fv_fml in H.
    apply H' in H; simpl in H; trivial.

   rewrite <- in_S_fv_fml in H. apply H' in H; simpl in H; trivial.

 red; simpl; intros; contradiction.

 red in IHderiv |- *. unfold fv_fml in IHderiv |- *. simpl in IHderiv |- *.
 intros; apply IHderiv. rewrite app_nil_r; trivial.

 red in IHderiv |- *. unfold fv_fml in IHderiv |- *. simpl in IHderiv |- *.
 intros; apply IHderiv. rewrite app_nil_r in H0; trivial.

 red in IHderiv1, IHderiv2 |- *. unfold fv_fml in IHderiv1, IHderiv2 |- *.
 simpl; intros. apply in_app_iff in H1. 
 destruct H1; [apply IHderiv1|apply IHderiv2]; trivial.

 red in IHderiv |- *. unfold fv_fml in IHderiv |- *. simpl in IHderiv.
 intros; apply IHderiv. rewrite in_app_iff; left; trivial.

 red in IHderiv |- *. unfold fv_fml in IHderiv |- *. simpl in IHderiv.
 intros; apply IHderiv. rewrite in_app_iff; right; trivial.

 red in IHderiv, H0 |- *. unfold fv_fml in IHderiv, H0 |- *.
 simpl; intros. apply in_app_iff in H1. 
 destruct H1; [apply IHderiv|apply H0]; trivial.

 red in IHderiv, H |- *. unfold fv_fml in IHderiv, H |- *.
 simpl; intros. apply in_app_iff in H1. 
 destruct H1; [apply H|apply IHderiv]; trivial.

 apply hyp_ok_weakening in IHderiv2; trivial.

 apply hyp_ok_weakening in IHderiv.
 red in IHderiv, H |- *. unfold fv_fml in IHderiv, H |- *. simpl; intros.
 rewrite in_app_iff in H1. destruct H1; [apply H in H1|apply IHderiv in H1]; trivial.

 red in IHderiv1 |- *. unfold fv_fml in IHderiv1 |- *. intros; apply IHderiv1.
 simpl; rewrite in_app_iff; right; trivial.

 red in IHderiv |- *. unfold fv_fml in IHderiv |- *. simpl; intros.
 rewrite <- in_S_fv_fml in H0. apply IHderiv in H0. simpl in H0; trivial.

 red in IHderiv |- *. unfold fv_fml in IHderiv |- *. simpl; intros.
 simpl in IHderiv. unfold subst_fml in H1.
 replace 0 with (0+0) in H1 by omega. apply in_fv_fml_subst_split in H1.
 destruct H1; [apply H in H1
   |rewrite in_S_fv_fml in H1; simpl in H1; apply IHderiv in H1]; trivial.

 red in IHderiv |- *. unfold fv_fml in IHderiv |- *. simpl in IHderiv |- *.
 intros; apply IHderiv. rewrite <- in_S_fv_fml in H1.
 unfold subst_fml. replace 0 with (0+0) in H1 |- * by omega.
 apply in_fv_fml_subst; trivial.
  
 unfold lift_fml in IHderiv2. rewrite lift_fml_split in IHderiv2.
 fold (lift_fml f1 1) in IHderiv2. fold (lift_fml (lift_fml f1 1) 1) in IHderiv2.
 apply hyp_ok_weakening in IHderiv2. apply hyp_ok_weakening in IHderiv2; trivial.
Qed. 

End PresburgerSyn.