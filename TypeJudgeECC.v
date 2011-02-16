
Require Import TypeECC.

Section Typage.

  Inductive eq_typ : env -> term -> term -> term -> Prop :=
    | type_prop : forall e,
        wf e ->
        eq_typ e (Srt prop) (Srt prop) (Srt (kind 0))
    | type_kind : forall e n,
        wf e ->
        eq_typ e (Srt (kind n)) (Srt (kind n)) (Srt (kind(S n)))
    | type_var :
        forall e v t,
        wf e ->
        item_lift t e v ->
        eq_typ e (Ref v) (Ref v) t
    | type_abs :
        forall e T T' M M' U U' s1 s2 s3,
        eq_typ e T T' (Srt s1) ->
        eq_typ (T :: e) U U' (Srt s2) ->
        eq_typ (T :: e) M M' U ->
        ecc_prod s1 s2 s3 = true ->
        eq_typ e (Abs T M) (Abs T' M') (Prod T U)
    | type_app :
        forall e u u' v v' V V' Ur Ur' s1 s2 s3,
        eq_typ e v v' V ->
        eq_typ e V V' (Srt s1) ->
        eq_typ e u u' (Prod V Ur) ->
        eq_typ (V::e) Ur Ur' (Srt s2) ->
        ecc_prod s1 s2 s3 = true ->
        eq_typ e (App u v) (App u' v') (subst v Ur)
    | type_prod :
        forall e T T' U U' s1 s2 s3,
        eq_typ e T T' (Srt s1) ->
        eq_typ (T :: e) U U' (Srt s2) ->
        ecc_prod s1 s2 s3 = true ->
        eq_typ e (Prod T U) (Prod T' U') (Srt s3)
    | type_beta : forall e T T' M M' N N' U U' s1 s2 s3,
        eq_typ e N N' T ->
        eq_typ e T T' (Srt s1) ->
        eq_typ (T::e) M M' U ->
        eq_typ (T::e) U U' (Srt s2) ->
        ecc_prod s1 s2 s3 = true ->
        eq_typ e (App (Abs T M) N) (subst N' M') (subst N U)
    | type_red : forall e M M' T T' s,
        eq_typ e M M' T ->
        eq_typ e T T' (Srt s) ->
        eq_typ e M M' T'
    | type_exp : forall e M M' T T' s,
        eq_typ e M M' T' ->
        eq_typ e T T' (Srt s) ->
        eq_typ e M M' T
  with wf : env -> Prop :=
      wf_nil : wf nil
    | wf_var : forall e T T' s,
        eq_typ e T T' (Srt s) ->
        wf (T::e).

Scheme eq_typ_mind := Minimality for eq_typ Sort Prop
  with wf_mind := Minimality for wf Sort Prop.

  Lemma typ_wf : forall e t t' T, eq_typ e t t' T -> wf e.
Proof.
induction 1; trivial.
Qed.

  Lemma typ_refl : forall e t t' T, eq_typ e t t' T -> eq_typ e t t T.
Proof.
induction 1; intros.
 apply type_prop; trivial.
 apply type_kind; trivial.
 apply type_var; trivial.
 apply type_abs with U s1 s2 s3; trivial.
 apply type_app with V V' Ur' s1 s2 s3; trivial.
 apply type_prod with s1 s2; trivial.
 apply type_app with T T' U' s1 s2 s3; trivial.
   apply type_abs with U s1 s2 s3; trivial.
 apply type_red with T s; trivial.
 apply type_exp with T' s; trivial.
Qed.


  Lemma typ_thin :
   forall g A e t t' T,
   wf (A::g) ->
   eq_typ e t t' T ->
   forall n f,
   ins_in_env A n e f ->
   trunc n e g ->
   eq_typ f (lift_rec 1 t n) (lift_rec 1 t' n) (lift_rec 1 T n).
intros g A e t t' T H H0.
elim H0 using eq_typ_mind with (P0:=fun e => forall n f, ins_in_env A n e f ->
  trunc n e g -> wf f); simpl; intros.
 constructor; eauto.
 constructor; eauto.
 destruct (le_gt_dec n v); intros.
  constructor; eauto.
   apply ins_item_lift_ge with (1 := H4); trivial.
  constructor;  eauto.
    apply ins_item_lift_lt with (1 := H4); trivial.
 apply type_abs with (lift_rec 1 U' (S n)) s1 s2 s3;  eauto with coc.
 rewrite distr_lift_subst.
   apply type_app
     with (lift_rec 1 V n) (lift_rec 1 V' n) (lift_rec 1 Ur' (S n)) s1 s2 s3;
     eauto with coc.
 apply type_prod with s1 s2;  eauto with coc.
 repeat rewrite distr_lift_subst.
   apply type_beta with (lift_rec 1 T' n) (lift_rec 1 U' (S n)) s1 s2 s3;
   auto with coc.
 apply type_red with (lift_rec 1 T0 n) s; auto with coc.
 apply type_exp with (lift_rec 1 T' n) s; auto with coc.
 inversion_clear H1; inversion H2;  subst g; trivial.
 inversion H3;  subst n; inversion H4;  subst g.
  trivial.
  apply wf_var with (lift_rec 1 T' n0) s; auto.
Qed.

  Lemma typ_thinning :
   forall A e t t' T,
   wf (A::e) ->
   eq_typ e t t' T ->
   eq_typ (A::e) (lift 1 t) (lift 1 t') (lift 1 T).
intros.
unfold lift in |- *.
apply typ_thin with (1 := H) (2 := H0); auto with coc.
Qed.

  Lemma typ_thinning_n :
   forall f t t' T n e,
   wf e ->
   eq_typ f t t' T ->
   trunc n e f ->
   eq_typ e (lift n t) (lift n t') (lift n T).
induction n; simpl in |- *; intros.
 repeat  rewrite lift0; inversion_clear H1; trivial.
  rewrite simpl_lift.
   pattern (lift (S n) t') in |- *.
    rewrite simpl_lift.
   pattern (lift (S n) T) in |- *.
    rewrite simpl_lift.
   inversion H1.
    subst e.
   apply typ_thinning; trivial.
   apply IHn; auto.
   inversion_clear H.
   apply typ_wf with (1 := H4).
Qed.


  Lemma typ_sub :
   forall g d t e u u' U,
   eq_typ e u u' U ->
   forall d' n f,
   eq_typ g d d' t ->
   sub_in_env d t n e f ->
   trunc n f g ->
   wf f ->
   eq_typ f (subst_rec d u n) (subst_rec d' u' n) (subst_rec d U n).
induction 1; simpl in *; intros.
 constructor;  eauto.
 constructor;  eauto.
 destruct (lt_eq_lt_dec n v) as [[fvar| eq_var]| bvar].
  constructor;  eauto.
    apply sub_item_lift_sup with (1 := H2); trivial.
   subst v;  rewrite sub_item_lift_eq with (1 := H2) (2 := H0).
    apply typ_thinning_n with g;  eauto.
  constructor;  eauto.
    apply nth_sub_inf with (1 := H2); trivial.
 assert (wf (subst_rec d T n :: f)).
  apply wf_var with (subst_rec d' T' n) s1;  eauto.
  apply type_abs with (subst_rec d' U' (S n)) s1 s2 s3;  eauto with coc.
  rewrite distr_subst.
   assert (wf (subst_rec d V n :: f)).
  apply wf_var with (subst_rec d' V' n) s1;  eauto.
  apply
   type_app with
     (subst_rec d V n) (subst_rec d' V' n) (subst_rec d' Ur' (S n)) s1 s2 s3;
    eauto with coc.
 assert (wf (subst_rec d T n :: f)).
  apply wf_var with (subst_rec d' T' n) s1;  eauto.
  apply type_prod with s1 s2;  eauto with coc.
 repeat  rewrite distr_subst.
   assert (wf (subst_rec d T n :: f)).
  apply wf_var with (subst_rec d' T' n) s1;  eauto.
  apply type_beta with (subst_rec d' T' n) (subst_rec d' U' (S n)) s1 s2 s3;
   auto with coc.
 apply type_red with (subst_rec d T n) s;  eauto with coc.
   apply IHeq_typ2;  eauto.
   apply typ_refl with (1 := H1).
 apply type_exp with (subst_rec d T' n) s;  eauto with coc.
   apply IHeq_typ2;  eauto.
   apply typ_refl with (1 := H1).
Qed.

  Theorem substitution :
   forall e t u u' U d d',
   eq_typ (t :: (e:env)) u u' U ->
   eq_typ e d d' t ->
   eq_typ e (subst d u) (subst d' u') (subst d U).
Proof.
intros.
unfold subst in |- *.
apply typ_sub with (1 := H) (2 := H0); auto with coc.
apply typ_wf with (1 := H0).
Qed.


  Inductive red1_in_env : env -> env -> Prop :=
    | red1_env_hd : forall e t u s, eq_typ e t u (Srt s) ->
        red1_in_env (t :: e) (u :: e)
    | red1_env_tl :
        forall e f t, red1_in_env e f -> red1_in_env (t :: e) (t :: f).

  Hint Constructors red1_in_env: coc.

  Lemma red_item :
   forall n t e f,
   item_lift t e n ->
   red1_in_env e f ->
   wf f ->
   item_lift t f n \/
   (forall g, trunc (S n) e g -> trunc (S n) f g) /\
   (exists2 u, exists s, eq_typ f t u (Srt s) & item_lift u f n).
simple induction n.
 do 4 intro.
   elim H.
   do 3 intro.
    rewrite H0.
   inversion_clear H1.
   intro.
   inversion_clear H1; intros.
  right.
    split; intros.
   inversion_clear H3; auto with coc.
   exists (lift 1 u).
    exists s.
      change (Srt s) with (lift 1 (Srt s)) in |- *.
      unfold lift in |- *; apply typ_thin with l u l; auto with coc.
    exists u; auto with coc.
  left.
    exists x; auto with coc.
 do 6 intro.
   elim H0.
   do 3 intro.
    rewrite H1.
   inversion_clear H2.
   intro.
   inversion_clear H2; intros.
  left.
    exists x; auto with coc.
  elim H with (lift (S n0) x) l f0; auto with coc; intros.
   left.
     elim H5; intros.
     exists x0; auto with coc.
      rewrite simpl_lift.
     pattern (lift (S (S n0)) x0) in |- *.
      rewrite simpl_lift.
     elim H6; auto with coc.
   right.
     elim H5.
     simple induction 2; intros.
     split; intros.
    inversion_clear H10; auto with coc.
    elim H9; intros.
      exists (lift (S (S n0)) x1).
      rewrite simpl_lift.
       pattern (lift (S (S n0)) x1) in |- *.
        rewrite simpl_lift.
       destruct H8.
       exists x2.
       change (Srt x2) with (lift_rec 1 (Srt x2) 0) in |- *.
       elim H1; unfold lift at 1 3 in |- *; apply typ_thin with f0 y f0;
        auto with coc.
        subst x0; trivial.
     exists x1; auto with coc.
   exists x; auto with coc.
   inversion_clear H2.
     apply typ_wf with (1 := H5).
Qed.

  Lemma typ_red_env :
   forall e t t' T, eq_typ e t t' T -> forall f, red1_in_env e f -> wf f ->
   eq_typ f t t' T.
induction 1; intros.
 apply type_prop; trivial.
 apply type_kind; trivial.
 elim red_item with (1 := H0) (2 := H1); auto with coc; intros.
  apply type_var; auto.
  destruct H3.
    destruct H4.
    destruct H4.
    apply type_exp with (2 := H4).
    apply type_var; trivial.
 assert (wf (T :: f)).
  apply wf_var with T' s1; auto.
  apply type_abs with U' s1 s2 s3; auto with coc.
 assert (wf (V :: f)).
  apply wf_var with V' s1; auto.
 apply type_app with V V' Ur' s1 s2 s3; auto with coc.
 assert (wf (T :: f)).
  apply wf_var with T' s1; auto.
  apply type_prod with s1 s2; auto with coc.
 assert (wf (T :: f)).
  apply wf_var with T' s1; auto.
  apply type_beta with T' U' s1 s2 s3; auto with coc.
 apply type_red with T s; auto with coc.
 apply type_exp with T' s; auto with coc.
Qed.


  Lemma typ_refl2 : forall e M M' T, eq_typ e M M' T -> eq_typ e M' M' T.
induction 1; intros.
 apply type_prop; trivial.
 apply type_kind; trivial.
 apply type_var; trivial.
 assert (wf (T' :: e)).
  apply wf_var with T' s1; trivial.
  assert (red1_in_env (T :: e) (T' :: e)).
   constructor 1 with s1; trivial.
   apply type_exp with (Prod T' U) s3; auto.
    apply type_abs with U' s1 s2 s3; auto.
     apply typ_red_env with (T :: e); auto.
     apply typ_red_env with (T :: e); auto.
    apply type_prod with s1 s2; auto.
      apply typ_refl with U'; trivial.
 assert (wf (V' :: e)).
  apply wf_var with V' s1; trivial.
  assert (red1_in_env (V :: e) (V' :: e)).
   constructor 1 with s1; trivial.
   apply type_exp with (subst v' Ur) s2.
    apply type_app with V V Ur s1 s2 s3; auto.
     apply typ_refl with V'; trivial.
     apply typ_refl with (1 := H2).
    change (Srt s2) with (subst v (Srt s2)) in |- *.
      apply substitution with V; trivial.
      apply typ_refl with (1 := H2).
 assert (wf (T' :: e)).
  apply wf_var with T' s1; trivial.
  assert (red1_in_env (T :: e) (T' :: e)).
   constructor 1 with s1; trivial.
   apply type_prod with s1 s2; auto.
     apply typ_red_env with (T :: e); auto.
 assert (wf (T' :: e)).
  apply wf_var with T' s1; trivial.
  assert (red1_in_env (T :: e) (T' :: e)).
   constructor 1 with s1; trivial.
   apply type_exp with (subst N' U) s2.
    apply substitution with T; auto.
    change (Srt s2) with (subst N (Srt s2)) in |- *.
      apply substitution with T; auto.
      apply typ_refl with (1 := H2).
 apply type_red with T s; auto.
 apply type_exp with T' s; auto.
Qed.


  Lemma wf_sort_lift :
   forall n e t, wf e -> item_lift t e n ->
   exists s, eq_typ e t t (Srt s).
simple induction n.
simple destruct e; intros.
elim H0; intros.
inversion_clear H2.

elim H0; intros.
rewrite H1.
inversion_clear H2.
inversion_clear H.
exists s.
change (Srt s) with (lift 1 (Srt s)).
apply typ_thinning; auto with coc.
apply wf_var with T' s; auto with coc.
apply typ_refl with (1:=H2).

intros.
elim H1; intros.
rewrite H2.
generalize H0.
inversion_clear H3; intros.
rewrite simpl_lift; auto with coc.
cut (wf l); intros.
elim H with l (lift (S n0) x); intros; auto with coc.
inversion_clear H3.
exists x0.
change (Srt x0) with (lift 1 (Srt x0)).
apply typ_thinning; auto with coc.
apply wf_var with T' s; auto with coc.

exists x; auto with coc.

inversion_clear H3.
apply typ_wf with (1:=H5).
Qed.



  Theorem type_case :
   forall e t t' T, eq_typ e t t' T ->
   exists s, eq_typ e T T (Srt s).
simple induction 1; intros; auto with coc.
 exists (kind 1); constructor; trivial.
 exists (kind (S (S n))); constructor; trivial.
 apply wf_sort_lift with (2 := H1); trivial.
 exists s3.
   apply typ_refl with (Prod T' U').
   apply type_prod with s1 s2; auto with coc.
 exists s2.
   apply typ_refl with (subst v' Ur').
   change (Srt s2) with (subst v (Srt s2)) in |- *.
   apply substitution with V; trivial.
 destruct s3.
   exists (kind(S n)); constructor.
   apply typ_wf with (1 := H0).
   exists (kind 0); constructor.
   apply typ_wf with (1 := H0).
 exists s2.
   apply typ_refl with (subst N' U').
   change (Srt s2) with (subst N (Srt s2)) in |- *.
   apply substitution with T0; trivial.
 exists s.
   apply typ_refl2 with (1 := H2).
 exists s.
   apply typ_refl with (1 := H2).
Qed.


Require Import Relation_Operators.

  Definition eq_typ_eq e :=
    clos_refl_sym_trans _ (fun x y => exists s, eq_typ e x y (Srt s)).
  Hint Unfold eq_typ_eq : coc.

  Lemma eq_typ_eq_red : forall e T T' s,
    eq_typ e T T' (Srt s) -> eq_typ_eq e T T'.
Proof.
red in |- *; intros; apply rst_step.
exists s; trivial.
Qed.

  Lemma eq_typ_eq_exp : forall e T T' s,
    eq_typ e T T' (Srt s) -> eq_typ_eq e T' T.
Proof.
red in |- *; intros; apply rst_sym; apply rst_step.
exists s; trivial.
Qed.

  Lemma type_conv_gen : forall e M M' T T',
    eq_typ_eq e T T' -> 
    (eq_typ e M M' T -> eq_typ e M M' T') /\
    (eq_typ e M M' T' -> eq_typ e M M' T).
induction 1; intros.
 destruct H.
   split; intros.
  apply type_red with (2 := H); trivial.
  apply type_exp with (2 := H); trivial.
 auto.
 destruct IHclos_refl_sym_trans; auto.
 destruct IHclos_refl_sym_trans1.
   destruct IHclos_refl_sym_trans2.
   auto 10.
Qed.
  Lemma type_conv : forall e M M' T T',
    eq_typ e M M' T -> eq_typ_eq e T T' -> eq_typ e M M' T'.
intros.
elim type_conv_gen with (M := M) (M' := M') (1 := H0); intros; auto.
Qed.


  Definition inv_type (P : Prop) e t t' T :=
    match t with
    | Srt prop => eq_typ_eq e (Srt (kind 0)) T -> t' = Srt prop -> P
    | Srt (kind n) => eq_typ_eq e (Srt (kind (S n))) T -> t' = Srt (kind n) -> P
    | Ref n =>
        forall x, item_lift x e n -> eq_typ_eq e x T -> t' = Ref n -> P
    | Abs A M =>
        forall s1 s2 s3 A' M' U U',
        eq_typ e A A' (Srt s1) ->
        eq_typ (A :: e) M M' U ->
        eq_typ (A :: e) U U' (Srt s2) ->
        ecc_prod s1 s2 s3 = true ->
        eq_typ_eq e (Prod A U) T -> t' = Abs A' M' -> P
    | App u v =>
        forall u' v' Ur Ur' V V' s1 s2 s3,
        eq_typ e v v' V ->
        eq_typ e V V' (Srt s1) ->
        eq_typ e u u' (Prod V Ur) ->
        eq_typ (V::e) Ur Ur' (Srt s2) ->
        ecc_prod s1 s2 s3 = true ->
        t' = App u' v' \/
        (exists2 M, u=Abs V M &
         exists2 M', eq_typ (V::e) M M' Ur & t' = subst v' M') ->
        eq_typ_eq e (subst v Ur) T -> P
    | Prod A B =>
        forall A' B' s1 s2 s3,
        eq_typ e A A' (Srt s1) ->
        eq_typ (A :: e) B B' (Srt s2) ->
        ecc_prod s1 s2 s3 = true ->
        eq_typ_eq e (Srt s3) T -> t' = Prod A' B' -> P
    end.

  Lemma inv_type_conv :
   forall P e t t' U V, eq_typ_eq e U V ->
   inv_type P e t t' V -> inv_type P e t t' U.
do 7 intro.
cut (forall x : term, eq_typ_eq e x U -> eq_typ_eq e x V).
 intro.
   case t; simpl in |- *;  eauto.
   destruct s; simpl in |- *;  eauto.
 unfold eq_typ_eq in *; intros.
   apply rst_trans with U; auto.
Qed.

  Theorem typ_inversion :
    forall P e t t' T, eq_typ e t t' T -> inv_type P e t t' T -> P.
simple induction 1; simpl in |- *; intros;  eauto with coc sets.
 apply H9 with (Abs T' M') N' U U' T0 T' s1 s2 s3; auto with coc sets.
  apply type_abs with U' s1 s2 s3; trivial.
  right.
    exists M; trivial.
    exists M'; trivial.
 apply H1.
   apply inv_type_conv with T'; trivial.
   apply eq_typ_eq_red with s; trivial.
 apply H1.
   apply inv_type_conv with T0; trivial.
   apply eq_typ_eq_exp with s; trivial.
Qed.

(*
Lemma typ_change : forall e M N T,
  eq_typ e M N T ->
  forall N' T',
  eq_typ e M N' T' ->
  eq_typ e M N' T.
induction 1; intros.
 apply typ_inversion with (1 := H0); red in |- *; intros.
    subst N'; constructor; trivial.
 apply typ_inversion with (1 := H1); red in |- *; intros.
    subst N'; constructor; trivial.
 apply typ_inversion with (1 := H2); red in |- *; intros.
    subst N'.
   apply type_abs with U s1 s2.
  <Your Tactic Text here>
  <Your Tactic Text here>
  <Your Tactic Text here>
 apply typ_inversion with (1 := H3); red in |- *; intros.
   destruct H8.
   subst N'.
    apply type_app with V V' Ur' s1 s2;  eauto.
  <Your Tactic Text here>
 apply typ_inversion with (1 := H1); red in |- *; intros.
    subst N'.
   apply type_prod with s1;  eauto.
 <Your Tactic Text here>
 apply type_red with T s;  eauto.
 apply type_exp with T' s;  eauto.



apply typ_inversion with (1 := H3); red in |- *; intros.
destruct H8.
  subst N'.
   apply type_app with V V' Ur' s1 s2;  eauto.
 destruct H8 as (M, eq_u, (M', eq_MM', eq_N')).
    subst u N'.
   apply type_beta with V'0 Ur' s0 s2; trivial.
  specialize IHeq_typ3 with (1 := H6); intro.
    apply typ_inversion with (1 := H8); red in |- *; intros.





Lemma typ_change : forall e M N T,
  eq_typ e M N T ->
  forall N' T',
  eq_typ e M N' T' ->
  eq_typ e M N T'.
induction 1; intros; eauto.
 apply typ_inversion with (1 := H0); red in |- *; intros.
    subst N'; trivial.
 apply typ_inversion with (1 := H1); red in |- *; intros.
    subst N'; trivial.
 apply typ_inversion with (1 := H2); red in |- *; intros.
   apply type_conv with (2 := H6).
   apply type_abs with U'0 s0 s3; eauto.
 apply typ_inversion with (1 := H3); red in |- *; intros.
   apply type_conv with (2 := H9).
   apply type_app with V0 V'0 Ur'0 s0 s3;  eauto.
 apply typ_inversion with (1 := H1); red in |- *; intros.
   apply type_conv with (2 := H4).
   apply type_prod with s0;  eauto.
 apply typ_inversion with (1 := H3); red in |- *; intros.
   apply type_conv with (2 := H9).
   clear T'0 H3 H9 N'0 H8.
   apply typ_inversion with (1 := H6); red in |- *; intros.
   apply type_beta with T' U0 s4 s5;  eauto.
  apply type_conv with U0;  eauto.
(* Pb: eq_typ (T::e) Ur U0 (Srt s5) *)

apply type_beta with T' Ur' s0 s3;eauto.
apply type_beta with T' U0 s0 s3;eauto.

   apply type_beta with T' U0 s4 s5;  eauto.



(*
Lemma str_confl: forall e A B T,
  eq_typ e A B T ->
  forall B' T',
  eq_typ e A B' T' ->
  eq_typ_eq e T T' ->
  exists2 C, eq_typ e B C T & eq_typ e B' C T.
induction 1; intros.
 apply typ_inversion with (1 := H0); red in |- *; intros.
    subst B'.
   exists (Srt prop); constructor; trivial.
*)

Lemma str_confl : forall e A B T,
   eq_typ e A B T ->
   forall B' T',
   eq_typ e A B' T' ->
   exists2 C, eq_typ e B C T' & eq_typ e B' C T.
induction 1; intros.
 apply typ_inversion with (1 := H0); red in |- *; intros.
    subst B'.
   exists (Srt prop); trivial.
   constructor; trivial.
 apply typ_inversion with (1 := H1); red in |- *; intros.
    subst B'.
   exists (Ref v); trivial.
   constructor; trivial.
 apply typ_inversion with (1 := H2); red in |- *; intros.
   elim IHeq_typ1 with (1 := H3); intros.
   elim IHeq_typ3 with (1 := H4); intros.
   exists (Abs x x0).
  apply type_conv with (2 := H6).
    apply type_exp with (Prod T' U0) s3.
   apply type_abs with U'0 s0 s3;  eauto.
    apply typ_red_env with (T :: e); trivial.
     constructor 1 with s1; trivial.
     apply wf_var with T' s1.
       apply typ_refl2 with T; trivial.
    apply typ_red_env with (T :: e); trivial.
     constructor 1 with s1; trivial.
     apply wf_var with T' s1.
       apply typ_refl2 with T; trivial.
   apply type_prod with s1; trivial.
     apply typ_refl with U'0; trivial.
   subst B'.
    apply type_exp with (Prod A' U) s2.
   apply type_abs with U' s1 s2; trivial.
    apply typ_red_env with (T :: e); trivial.
     constructor 1 with s0; trivial.
     apply wf_var with x s1; trivial.
    apply typ_red_env with (T :: e); trivial.
     constructor 1 with s0; trivial.
     apply wf_var with x s1; trivial.
   apply type_prod with s0; trivial.
     apply typ_refl with U'; trivial.
 apply typ_inversion with (1 := H3); red in |- *; intros.
   destruct H8.
   subst B'.
    elim IHeq_typ1 with (1 := H4); intros.
    elim IHeq_typ3 with (1 := H6); intros.
    exists (App x0 x).
   apply type_conv with (2 := H9).
     apply type_exp with (subst v' Ur0) s3.
    apply type_app with V0 V'0 Ur'0 s0 s3; trivial.
    change (Srt s3) with (subst v (Srt s3)) in |- *.
      apply substitution with V0.
     apply typ_refl with Ur'0; trivial.





 apply typ_inversion with (1 := H3); red in |- *; intros.
   destruct H8.
   subst B'.
    <Your Tactic Text here>
  <Your Tactic Text here>
 <Your Tactic Text here>
 <Your Tactic Text here>
 elim IHeq_typ1 with B'; intros.
  exists x.
   apply type_red with T s; trivial.
   apply type_red with T s; trivial.
  apply type_exp with T' s; trivial.
 elim IHeq_typ1 with B'; intros.
  exists x.
   apply type_exp with T' s; trivial.
   apply type_exp with T' s; trivial.
  apply type_red with T s; trivial.




Lemma str_confl : forall e A B T,
   eq_typ e A B T ->
   forall B',
   eq_typ e A B' T ->
   exists2 C, eq_typ e B C T & eq_typ e B' C T
induction 1; intros.
 apply typ_inversion with (1 := H0); red in |- *; intros.
    subst B'.
   exists (Srt prop); constructor; trivial.
 apply typ_inversion with (1 := H1); red in |- *; intros.
    subst B'.
   exists (Ref v); constructor; trivial.
 apply typ_inversion with (1 := H2); red in |- *; intros.
 <Your Tactic Text here>
 apply typ_inversion' with (1 := H3); red in |- *; intros.
   destruct H8.
   subst B'.
    <Your Tactic Text here>
  <Your Tactic Text here>
 <Your Tactic Text here>
 <Your Tactic Text here>
 elim IHeq_typ1 with B'; intros.
  exists x.
   apply type_red with T s; trivial.
   apply type_red with T s; trivial.
  apply type_exp with T' s; trivial.
 elim IHeq_typ1 with B'; intros.
  exists x.
   apply type_exp with T' s; trivial.
   apply type_exp with T' s; trivial.
  apply type_red with T s; trivial.


  Lemma wf_trunc : forall n e f, trunc n e f -> wf e -> wf f.
induction 1; intros; auto.
inversion_clear H0.
specialize typ_wf with (1 := H1); auto.
Qed.



  Lemma subj_red : forall t u, red1 t u -> forall e T, typ e t T -> typ e u T.
simple induction 1; intros.
apply typ_inversion with (1:=H0); red; intros.
apply typ_inversion with (1:=H2); red; intros.






inversion_clear H1.

inversion_clear H2.

inversion_clear H6.
cut (wf (M' :: e0)); intros.
apply type_conv with (Prod M' U) s2; auto with coc.
apply type_abs with s1 s2; auto with coc.
apply typ_red_env with (T0 :: e0); auto with coc.

apply typ_red_env with (T0 :: e0); auto with coc.

apply type_prod with s1; auto with coc.

apply wf_var with s1; auto with coc.

apply type_abs with s1 s2; auto with coc.

elim type_case with (1 := H2); intros.
inversion_clear H5.
apply inv_typ_prod with (1 := H6); intros.
generalize H2 H3; clear H2 H3.
inversion_clear H4; intros.
apply inv_typ_abs with (1 := H2); intros.
apply type_conv with (subst v T1) s2; auto with coc.
apply substitution with T0; auto with coc.
apply type_conv with V s0; auto with coc.
apply sym_conv.
apply inv_conv_prod_l with (1 := H11).

unfold subst in |- *.
apply conv_conv_subst; auto with coc.
apply inv_conv_prod_r with (1 := H11); auto with coc.

replace (Srt s2) with (subst v (Srt s2)); auto with coc.
apply substitution with V; auto with coc.

apply type_app with V; auto with coc.

apply type_conv with (subst N2 Ur) s2; auto with coc.
apply type_app with V; auto with coc.

unfold subst in |- *.
apply conv_conv_subst; auto with coc.

replace (Srt s2) with (subst v (Srt s2)); auto with coc.
apply substitution with V; auto with coc.

discriminate H5.

inversion_clear H4.
apply type_prod with s1; auto with coc.
apply typ_red_env with (T0 :: e0); auto with coc.
apply wf_var with s1; auto with coc.

apply type_prod with s1; auto with coc.

apply type_conv with U s; auto with coc.
Qed.
*)
End Typage.
