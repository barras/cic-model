Require Export Arith.
Require Export Omega.
Require Export List.

Inductive foterm :=
| Var : nat -> foterm
| Cst_0 : foterm
| Cst_1 : foterm
| Df_Add : foterm -> foterm -> foterm.

Fixpoint free_var_fotrm t k : list nat :=
  match t with
    | Var n => 
      match le_gt_dec k n with
        | left _ => n::nil
        | right _ => nil
      end
    | Cst_0 => nil
    | Cst_1 => nil
    | Df_Add M N => (free_var_fotrm M k) ++ (free_var_fotrm N k)
  end.

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

Lemma subst_bound_trm : forall t m, 
  subst_trm_rec (lift_trm_rec t 1 (S m)) (Var 0) m = t.
induction t; intros; trivial.
 unfold lift_trm_rec. destruct (Compare_dec.le_gt_dec (S m) n).
  simpl. destruct (Compare_dec.lt_eq_lt_dec m (n + 1)).
   destruct s. 
    rewrite Plus.plus_comm; simpl; trivial.

    rewrite e in l. apply Le.le_Sn_le in l. 
    rewrite Plus.plus_comm in l. apply Le.le_Sn_n in l. contradiction.

    assert (m < n); trivial.
    assert (n < n + 1) by omega.
    generalize (Lt.lt_trans _ _ _ H0 l0); intros.
    generalize (Lt.lt_trans _ _ _ H1 H); intros.
    apply Lt.lt_irrefl in H2; contradiction.

  simpl. destruct (Compare_dec.lt_eq_lt_dec m n); trivial.
   destruct s.
    assert (S m <= n) by omega.
    assert (n < S m) by omega.
    generalize (Lt.le_lt_trans _ _ _ H H0); intros.
    apply Lt.lt_irrefl in H1; contradiction.

    subst m. unfold lift_trm; simpl; trivial.

 simpl. rewrite IHt1, IHt2; trivial.
Qed.

Fixpoint max_var_rec (t:foterm) max_v :=
  match t with
    | Var n => max max_v n
    | Cst_0 => max_v
    | Cst_1 => max_v
    | Df_Add m n => max (max_var_rec m max_v) (max_var_rec n max_v) 
  end.

Definition max_var t := max_var_rec t 0.

Inductive foformula :=
| eq_fotrm : foterm -> foterm -> foformula
| TF   : foformula
| BF   : foformula
| neg : foformula -> foformula
| conj : foformula -> foformula -> foformula
| disj : foformula -> foformula -> foformula
| implf : foformula -> foformula -> foformula
| fall : foformula -> foformula
| exst : foformula -> foformula.

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

Fixpoint subst_fml f N n :=
  match f with
    | eq_fotrm x y => eq_fotrm (subst_trm_rec x N n) (subst_trm_rec y N n)
    | TF => TF
    | BF => BF
    | neg f => neg (subst_fml f N n)
    | conj f1 f2 => conj (subst_fml f1 N n) (subst_fml f2 N n)
    | disj f1 f2 => disj (subst_fml f1 N n) (subst_fml f2 N n)
    | implf f1 f2 => implf (subst_fml f1 N n) (subst_fml f2 N n)
    | fall f => fall (subst_fml f N (S n))
    | exst f => exst (subst_fml f N (S n))
  end.

Definition subst_fml0 f N := subst_fml f N 0.

Lemma subst_bound_fml : forall P m,
  P = subst_fml (lift_fml_rec P 1 (S m)) (Var 0) m.
induction P; simpl; intros; trivial.
 do 2 rewrite subst_bound_trm; trivial.
 
 rewrite <- IHP; trivial.

 rewrite <- IHP1, <-IHP2; trivial.

 rewrite <- IHP1, <-IHP2; trivial.

 rewrite <- IHP1, <-IHP2; trivial.

 rewrite <- IHP with (m:= S m); trivial.

 rewrite <- IHP with (m:= S m); trivial.
Qed.

Definition P_ax f :=
  f = (fall (neg (eq_fotrm Cst_0 (Df_Add (Var 0) Cst_1))))      \/
  f = (fall (fall (implf (eq_fotrm (Df_Add (Var 0) Cst_1) 
    (Df_Add (Var 1) Cst_1)) (eq_fotrm (Var 0) (Var 1)))))       \/
  f = (fall (eq_fotrm (Var 0) (Df_Add (Var 0) Cst_0)))          \/
  f = (fall(fall (eq_fotrm (Df_Add (Df_Add (Var 0) (Var 1)) Cst_1) 
                   (Df_Add (Var 0) (Df_Add (Var 1) (Cst_1)))))) \/
  exists g, f = (implf (subst_fml0 g Cst_0) 
    (implf (fall (implf g 
      (subst_fml0 (lift_fml_rec g 1 1) (Df_Add (Var 0) Cst_1)))) 
    (fall g))).


Definition hyp_ok (hyp:list (option foformula)) t := 
  forall n, In n (free_var_fotrm t 0) -> nth_error hyp n = Some None.

Inductive deriv : list (option foformula) -> foformula -> Prop :=
| hyp_judge : forall f hyp n, nth_error hyp n = Some (Some f) ->
  deriv hyp (lift_fml f (S n))
| ax_intro : forall f hyp, P_ax f -> deriv hyp f
| true_intro : forall hyp, deriv hyp TF
| false_elim : forall hyp f, deriv hyp BF -> deriv hyp f
| neg_intro : forall hyp f, deriv hyp (implf f BF) -> deriv hyp (neg f)
| neg_elim : forall hyp f, deriv hyp (neg f) -> deriv hyp (implf f BF)
| conj_intro : forall hyp f1 f2 , 
  deriv hyp f1 -> deriv hyp f2 -> deriv hyp (conj f1 f2)
| conj_elim1 : forall hyp f1 f2,
  deriv hyp (conj f1 f2) -> deriv hyp f1
| conj_elim2 : forall hyp f1 f2,
  deriv hyp (conj f1 f2) -> deriv hyp f2
| disj_intro1 : forall hyp f1 f2, 
  deriv hyp f1 -> deriv hyp (disj f1 f2)
| disj_intro2 : forall hyp f1 f2, 
  deriv hyp f2 -> deriv hyp (disj f1 f2)
| disj_elim : forall hyp f1 f2 f3,
  deriv hyp (disj f1 f2) -> deriv (Some f1::hyp) (lift_fml f3 1) -> 
  deriv (Some f2::hyp) (lift_fml f3 1) -> deriv hyp f3
| impl_intro : forall hyp f1 f2,
  deriv ((Some f1)::hyp) (lift_fml f2 1) -> deriv hyp (implf f1 f2)
| impl_elim : forall hyp f1 f2,
  deriv hyp (implf f1 f2) -> deriv hyp f1 -> deriv hyp f2
| fall_intro : forall hyp f,
  deriv (None::hyp) f -> deriv hyp (fall f)
| fall_elim : forall hyp f u, hyp_ok hyp u ->
  deriv hyp (fall f) -> deriv hyp (subst_fml0 f u)
| exst_intro : forall hyp f N, hyp_ok hyp N -> 
  deriv hyp (subst_fml0 f N) -> deriv hyp (exst f)
| exst_elim : forall hyp f f1, deriv hyp (exst f) -> 
  deriv (Some f::None::hyp) (lift_fml f1 2) -> deriv hyp f1.







 