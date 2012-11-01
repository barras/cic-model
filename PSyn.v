Require Import AbsTheorySyn.
Import Compare_dec List.

(*Instantiate Module sig*)
Module PresburgerSig <: TheorySig.

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

Lemma lift_trm0 : forall t, lift_trm t 0 = t.
induction t; intros; unfold lift_trm; simpl; trivial.
 apply f_equal; omega.

 unfold lift_trm in IHt1, IHt2; rewrite IHt1, IHt2; trivial.
Qed.

Lemma lift_trm_split : forall t n k, 
  lift_trm_rec t (S n) k = lift_trm_rec (lift_trm_rec t n k) 1 k.
induction t; trivial; unfold lift_trm in *; simpl; intros.
 destruct (le_gt_dec k n) as [le|gt]; simpl.
  destruct (le_gt_dec k (n+n0)) as [le'|gt]; simpl; [apply f_equal|]; omega.

  destruct (le_gt_dec k n) as [le|gt']; simpl; [omega|trivial].

 rewrite IHt1, IHt2; trivial.
Qed.

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

End PresburgerSig.


(*Instantiate Module ax*)
Module PresburgerAx <: TheoryAx PresburgerSig.

Include FoLang PresburgerSig.

Definition ax_syn hyp f :=
  f = (fall (neg (eq_fotrm Cst_0 (Df_Add (Var 0) Cst_1))))      \/
  f = (fall (fall (implf (eq_fotrm (Df_Add (Var 0) Cst_1) 
    (Df_Add (Var 1) Cst_1)) (eq_fotrm (Var 0) (Var 1)))))       \/
  f = (fall (eq_fotrm (Var 0) (Df_Add (Var 0) Cst_0)))          \/
  f = (fall(fall (eq_fotrm (Df_Add (Df_Add (Var 0) (Var 1)) Cst_1) 
                   (Df_Add (Var 0) (Df_Add (Var 1) (Cst_1)))))) \/
  exists g, (wf_fml (None::hyp) g) /\ f = (implf (subst_fml g Cst_0) 
    (implf (fall (implf g 
      (subst_fml (lift_fml_rec g 1 1) (Df_Add (Var 0) Cst_1)))) 
    (fall g))).

Lemma ax_wf : forall (hyp : HYP) (f : foformula), ax_syn hyp f -> wf_fml hyp f.
intros hyp f Hax. 
destruct Hax as [Hax|[Hax|[Hax|[Hax|(g, (H', Hax))]]]]; subst f;
  try (unfold wf_fml, fv_fml, fv_trm; simpl; intros; contradiction).
 unfold wf_fml, fv_fml in H' |- *; simpl; intros.
 apply in_app_or in H; destruct H.
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
Qed.

End PresburgerAx.


Module PresburgerTheory <: TheorySyn.

Module sig <: TheorySig := PresburgerSig.
Export sig.

Module ax <: TheoryAx sig := PresburgerAx.
Export ax.

Include FoDeriv sig ax.

End PresburgerTheory.



