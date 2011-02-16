
Require Import Types.

Section Typage.

  Inductive eq_typ : env -> term -> term -> term -> Prop :=
    | type_prop : forall e,
        wf e ->
        eq_typ e (Srt prop) (Srt prop) (Srt kind)
    | type_var :
        forall e v t,
        wf e ->
        item_lift t e v ->
        eq_typ e (Ref v) (Ref v) t
    | type_abs :
        forall e T T' M M' U U' s1 s2,
        eq_typ e T T' (Srt s1) ->
        eq_typ (T :: e) U U' (Srt s2) ->
        eq_typ (T :: e) M M' U ->
        eq_typ e (Abs T M) (Abs T' M') (Prod T U)
    | type_app :
        forall e u u' v v' V V' Ur Ur' s1 s2,
        eq_typ e v v' V ->
        eq_typ e V V' (Srt s1) ->
        eq_typ e u u' (Prod V Ur) ->
        eq_typ (V::e) Ur Ur' (Srt s2) ->
        eq_typ e (App (Prod u Ur) v) (App (Prod u' Ur') v') (subst v Ur)
    | type_prod :
        forall e T T' U U' s1 s2,
        eq_typ e T T' (Srt s1) ->
        eq_typ (T :: e) U U' (Srt s2) ->
        eq_typ e (Prod T U) (Prod T' U') (Srt s2)
    | type_beta : forall e T T' M M' N N' U U' s1 s2,
        eq_typ e N N' T ->
        eq_typ e T T' (Srt s1) ->
        eq_typ (T::e) M M' U ->
        eq_typ (T::e) U U' (Srt s2) ->
        eq_typ e (App (Prod (Abs T M) U) N) (subst N' M') (subst N U)
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

  Definition eq_red e M M' T:=
    clos_refl_trans _ (fun x y => eq_typ e x y T) M M'.
  Definition eq_conv e M M' T:=
    clos_refl_sym_trans _ (fun x y => eq_typ e x y T) M M'.

  Lemma eq_conv_refl : forall e t T, eq_conv e t t T.
red; auto with sets.
Qed.
  Hint Resolve eq_conv_refl : coc.

  Lemma eq_conv_sym :
    forall e t u T, eq_conv e t u T -> eq_conv e u t T.
red; intros; apply rst_sym; trivial.
Qed.

  Lemma eq_conv_trans : forall e M M' M'' T,
    eq_conv e M M' T ->
    eq_conv e M' M'' T ->
    eq_conv e M M'' T.
intros.
constructor 4 with M'; trivial.
Qed.


  Lemma eq_red_conv : forall e M M' T, eq_red e M M' T -> eq_conv e M M' T.
unfold eq_red, eq_conv; intros; apply clos_rt_clos_rst; trivial.
Qed.

  Lemma eq_conv_red : forall e T T' U,
    eq_typ e T T' U -> eq_conv e T T' U.
Proof.
red; auto with sets.
Qed.

  Lemma eq_conv_exp : forall e T T' U,
    eq_typ e T T' U -> eq_conv e T' T U.
Proof.
red; intros; apply rst_sym; auto with sets.
Qed.
  Hint Resolve eq_conv_red eq_conv_exp : coc.

  Lemma type_eq_conv_gen : forall e M M' T T' s,
    eq_conv e T T' (Srt s) -> 
    (eq_typ e M M' T -> eq_typ e M M' T') /\
    (eq_typ e M M' T' -> eq_typ e M M' T).
induction 1; intros.
 split; intros.
  apply type_red with (2 := H); trivial.
  apply type_exp with (2 := H); trivial.

 auto.

 destruct IHclos_refl_sym_trans; auto.

 destruct IHclos_refl_sym_trans1.
 destruct IHclos_refl_sym_trans2.
 auto 10.
Qed.
  Lemma type_eq_conv : forall e M M' T T' s,
    eq_typ e M M' T -> eq_conv e T T' (Srt s) -> eq_typ e M M' T'.
intros.
elim type_eq_conv_gen with (M := M) (M' := M') (1 := H0); intros; auto.
Qed.

  Lemma eq_conv_conv : forall (e : env) (M M' T T' : term) s,
    eq_conv e M M' T -> eq_conv e T T' (Srt s) -> eq_conv e M M' T'.
induction 1; intros.
 constructor 1.
 apply type_eq_conv with T s; trivial.

 red; apply rst_refl.

 red; apply rst_sym.
 apply IHclos_refl_sym_trans.
 trivial.

 red; apply rst_trans with y; auto.
  apply IHclos_refl_sym_trans1; trivial.
  apply IHclos_refl_sym_trans2; trivial.
Qed.


(* Basic metatheory: thinning, substitution *)

  Lemma typ_wf : forall e t t' T, eq_typ e t t' T -> wf e.
Proof.
induction 1; trivial.
Qed.

  Lemma typ_refl : forall e t t' T, eq_typ e t t' T -> eq_typ e t t T.
Proof.
induction 1; intros.
 apply type_prop; trivial.
 apply type_var; trivial.
 apply type_abs with U s1 s2; trivial.
 apply type_app with V V' s1 s2; trivial.
 apply type_prod with s1; trivial.
 apply type_app with T T s1 s2; trivial.
   apply type_abs with U s1 s2; trivial.
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

 destruct (le_gt_dec n v); intros.
  constructor; eauto.
  apply ins_item_lift_ge with (1 := H4); trivial.

  constructor;  eauto.
  apply ins_item_lift_lt with (1 := H4); trivial.

 apply type_abs with (lift_rec 1 U' (S n)) s1 s2;  eauto with coc.

 rewrite distr_lift_subst.
 apply type_app with (lift_rec 1 V n) (lift_rec 1 V' n) s1 s2;
   eauto with coc.

 apply type_prod with s1;  eauto with coc.

 repeat rewrite distr_lift_subst.
 apply type_beta with (lift_rec 1 T' n) (lift_rec 1 U' (S n)) s1 s2;
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
unfold lift.
apply typ_thin with (1 := H) (2 := H0); auto with coc.
Qed.

  Lemma typ_thinning_n :
   forall f t t' T n e,
   wf e ->
   eq_typ f t t' T ->
   trunc n e f ->
   eq_typ e (lift n t) (lift n t') (lift n T).
induction n; simpl; intros.
 repeat  rewrite lift0; inversion_clear H1; trivial.

 rewrite simpl_lift.
 pattern (lift (S n) t').
 rewrite simpl_lift.
 pattern (lift (S n) T).
 rewrite simpl_lift.
 inversion H1.
 subst e.
 apply typ_thinning; trivial.
 apply IHn; auto.
 inversion_clear H.
 apply typ_wf with (1 := H4).
Qed.

  Lemma eq_conv_lift : forall e T U A x,
    eq_conv e T U A ->
    wf (x::e) ->
    eq_conv (x::e) (lift 1 T) (lift 1 U) (lift 1 A).
red; induction 1; intros; auto with sets.
 apply eq_conv_red.
 apply typ_thinning; trivial.

 apply rst_sym; auto.

 apply rst_trans with (lift 1 y).
  apply IHclos_refl_sym_trans1; trivial.
  apply IHclos_refl_sym_trans2; trivial.
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

 destruct (lt_eq_lt_dec n v) as [[fvar| eq_var]| bvar].
  constructor;  eauto.
  apply sub_item_lift_sup with (1 := H2); trivial.

  subst v;  rewrite sub_item_lift_eq with (1 := H2) (2 := H0).
  apply typ_thinning_n with g;  eauto.

  constructor;  eauto.
  apply nth_sub_inf with (1 := H2); trivial.

 assert (wf (subst_rec d T n :: f)).
  apply wf_var with (subst_rec d' T' n) s1;  eauto.
 apply type_abs with (subst_rec d' U' (S n)) s1 s2;  eauto with coc.

 rewrite distr_subst.
 assert (wf (subst_rec d V n :: f)).
  apply wf_var with (subst_rec d' V' n) s1;  eauto.
 apply type_app with (subst_rec d V n) (subst_rec d' V' n) s1 s2;
   eauto with coc.

 assert (wf (subst_rec d T n :: f)).
  apply wf_var with (subst_rec d' T' n) s1;  eauto.
 apply type_prod with s1;  eauto with coc.

 repeat  rewrite distr_subst.
 assert (wf (subst_rec d T n :: f)).
  apply wf_var with (subst_rec d' T' n) s1;  eauto.
 apply type_beta with (subst_rec d' T' n) (subst_rec d' U' (S n)) s1 s2;
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
unfold subst.
apply typ_sub with (1 := H) (2 := H0); auto with coc.
apply typ_wf with (1 := H0).
Qed.


Lemma eq_conv_subst_ty_l : forall e M M' T U s,
  eq_conv e M M' T ->
  eq_typ (T::e) U U (Srt s) ->
  eq_conv e (subst M U) (subst M' U) (Srt s).
red; induction 1; intros; auto with sets.
 apply rst_step.
 change (Srt s) with (subst x (Srt s)).
 apply substitution with T; trivial.

 apply rst_sym.
 auto.

 apply rst_trans with (subst y U); auto.
Qed.

Lemma eq_conv_subst_r : forall e M T U U' A,
  eq_typ e M M T ->
  eq_conv (T::e) U U' A ->
  eq_conv e (subst M U) (subst M U') (subst M A).
red; induction 2; intros; auto with sets.
 apply rst_step.
 apply substitution with T; trivial.

 apply rst_trans with (subst M y); auto.
Qed.

  Inductive red1_in_env : env -> env -> Prop :=
    | red1_env_hd : forall e t u s, eq_conv e t u (Srt s) ->
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
   (exists2 u, exists s, eq_conv f t u (Srt s) & item_lift u f n).
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
    change (Srt s) with (lift 1 (Srt s)).
    apply eq_conv_lift; trivial.

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
   pattern (lift (S (S n0)) x0).
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
     pattern (lift (S (S n0)) x1).
     rewrite simpl_lift.
     destruct H8 as (s, H8).
     exists s.
     change (Srt s) with (lift 1 (Srt s)).
     apply eq_conv_lift; trivial.
     subst x0; trivial.

     exists x1; auto with coc.

   exists x; auto with coc.

   inversion_clear H2.
   apply typ_wf with (1 := H5).
Qed.

  Lemma typ_red_env_raw :
   forall e t t' T, eq_typ e t t' T -> forall f, red1_in_env e f -> wf f ->
   eq_typ f t t' T.
induction 1; intros.
 apply type_prop; trivial.

 elim red_item with (1 := H0) (2 := H1); auto with coc; intros.
  apply type_var; auto.

  destruct H3.
  destruct H4; destruct H4 as (s,H4).
  apply type_eq_conv with x s.
   apply type_var; trivial.
   red; apply rst_sym; trivial.

 assert (wf (T :: f)).
  apply wf_var with T' s1; auto.
 apply type_abs with U' s1 s2; auto with coc.

 assert (wf (V :: f)).
  apply wf_var with V' s1; auto.
 apply type_app with V V' s1 s2; auto with coc.

 assert (wf (T :: f)).
  apply wf_var with T' s1; auto.
 apply type_prod with s1; auto with coc.

 assert (wf (T :: f)).
  apply wf_var with T' s1; auto.
 apply type_beta with T' U' s1 s2; auto with coc.

 apply type_red with T s; auto with coc.

 apply type_exp with T' s; auto with coc.
Qed.


  Lemma typ_refl2 : forall e M M' T, eq_typ e M M' T -> eq_typ e M' M' T.
induction 1; intros.
 apply type_prop; trivial.

 apply type_var; trivial.

 assert (wf (T' :: e)).
  apply wf_var with T' s1; trivial.
 assert (red1_in_env (T :: e) (T' :: e)).
  constructor 1 with s1; auto with coc.
 apply type_exp with (Prod T' U) s2; auto.
  apply type_abs with U' s1 s2; auto.
   apply typ_red_env_raw with (T :: e); auto.

   apply typ_red_env_raw with (T :: e); auto.

  apply type_prod with s1; auto.
  apply typ_refl with U'; trivial.

 assert (wf (V' :: e)).
  apply wf_var with V' s1; trivial.
 assert (red1_in_env (V :: e) (V' :: e)).
  constructor 1 with s1; auto with coc.
 apply type_exp with (subst v' Ur') s2.
  apply type_app with V V s1 s2; auto.
   apply typ_refl with V'; trivial.

   apply type_red with (Prod V Ur) s2; trivial.
   apply type_prod with s1; trivial.
   apply typ_refl with V'; trivial.

  change (Srt s2) with (subst v (Srt s2)).
  apply substitution with V; trivial.

 assert (wf (T' :: e)).
  apply wf_var with T' s1; trivial.
 assert (red1_in_env (T :: e) (T' :: e)).
  constructor 1 with s1; auto with coc.
 apply type_prod with s1; auto.
 apply typ_red_env_raw with (T :: e); auto.

 assert (wf (T' :: e)).
  apply wf_var with T' s1; trivial.
 assert (red1_in_env (T :: e) (T' :: e)).
  constructor 1 with s1; auto with coc.
 apply type_exp with (subst N' U) s2.
  apply substitution with T; auto.

  change (Srt s2) with (subst N (Srt s2)).
  apply substitution with T; auto.
  apply typ_refl with U'; trivial.

 apply type_red with T s; auto.

 apply type_exp with T' s; auto.
Qed.

  Lemma eq_conv_inv : forall e T T' U,
    eq_conv e T T' U ->
    T = T' \/ eq_typ e T T U /\ eq_typ e T' T' U.
induction 1; intros; try firstorder subst; auto.
 right.
 split.
  apply typ_refl with y; trivial.
  apply typ_refl2 with x; trivial.
Qed.

  Lemma eq_conv_inv2 : forall e T T' U,
    eq_conv e T T' U ->
    eq_typ e T T U -> eq_typ e T' T' U.
intros.
elim eq_conv_inv with (1 := H);  firstorder.
 subst; trivial.
Qed.

  Lemma eq_red_inv : forall e T T' U,
    eq_red e T T' U ->
    T = T' \/ eq_typ e T T U /\ eq_typ e T' T' U.
intros; apply eq_conv_inv; apply eq_red_conv; trivial.
Qed.

  Lemma eq_red_inv2 : forall e T T' U,
    eq_red e T T' U ->
    eq_typ e T T U -> eq_typ e T' T' U.
intros; apply eq_conv_inv2 with T; trivial; apply eq_red_conv; trivial.
Qed.

  Lemma wf_red_env_trans :
    forall e f,
    clos_refl_trans _ red1_in_env e f ->
    wf e ->
    wf f.
induction 1; auto.
induction H; intros.
 elim eq_conv_inv with (1 := H); intros.
  subst u; trivial.

  destruct H1.
  apply wf_var with u s; trivial.

 inversion_clear H0.
 apply wf_var with T' s.
 apply typ_red_env_raw with e; trivial.
 apply IHred1_in_env.
 eapply typ_wf; eauto.
Qed.

  Lemma typ_red_env :
    forall e f M M' T,
    red1_in_env e f ->
    eq_typ e M M' T ->
    eq_typ f M M' T.
intros.
apply typ_red_env_raw with e; trivial.
apply wf_red_env_trans with e; auto with sets.
 eapply typ_wf;  eauto.
Qed.

  Lemma typ_red_env_trans :
    forall e f M M' T,
    clos_refl_trans _ red1_in_env e f ->
    eq_typ e M M' T ->
    eq_typ f M M' T.
induction 1; intros;  eauto.
apply typ_red_env with x; trivial.
Qed.

  Lemma eq_conv_red_env : forall e f x y T,
    red1_in_env e f ->
    eq_conv e x y T ->
    eq_conv f x y T.
intros.
elim H0; intros.
 red; apply rst_step.
   apply typ_red_env with e; trivial.
 red; apply rst_refl.
 red; apply rst_sym; trivial.
 red; apply rst_trans with y0; trivial.
Qed.

(* Admissible rules for conversion *)

  Lemma eq_conv_prod_r : forall e T U U' s1 s2,
    eq_typ e T T (Srt s1) ->
    eq_conv (T::e) U U' (Srt s2) ->
    eq_conv e (Prod T U) (Prod T U') (Srt s2).
red; induction 2; intros;  eauto with sets.
 apply eq_conv_red.
 apply type_prod with s1; trivial.

 apply rst_trans with (Prod T y); auto.
Qed.

  Lemma eq_conv_prod_l : forall e T T' U s1 s2,
    eq_conv e T T' (Srt s1) ->
    eq_typ (T::e) U U (Srt s2) ->
    eq_conv e (Prod T U) (Prod T' U) (Srt s2).
red; induction 1; intros; auto with sets.
 apply eq_conv_red.
 apply type_prod with s1; trivial.

 apply eq_conv_sym.
 apply IHclos_refl_sym_trans.
 apply typ_red_env with (y :: e); trivial.
 constructor 1 with s1; apply eq_conv_sym; trivial.

 apply eq_conv_trans with (Prod y U); red; auto.
 apply IHclos_refl_sym_trans2.
 apply typ_red_env with (x :: e); trivial.
 constructor 1 with s1; trivial.
Qed.

Lemma eq_conv_prod : forall e T T' U U' s1 s2,
  eq_typ e T T (Srt s1) ->
  eq_typ (T::e) U U (Srt s2) ->
  eq_conv e T T' (Srt s1) ->
  eq_conv (T :: e) U U' (Srt s2) ->
  eq_conv e (Prod T U) (Prod T' U') (Srt s2).
intros.
red; apply rst_trans with (Prod T U').
 apply eq_conv_prod_r with s1; trivial.

 apply eq_conv_prod_l with s1; trivial.
 elim eq_conv_inv with (1 := H2); intros.
  subst U'; trivial.
  destruct H3; trivial.
Qed.

  Lemma eq_conv_abs_r : forall e T M M' U s1 s2,
    eq_typ e T T (Srt s1) ->
    eq_typ (T::e) U U (Srt s2) ->
    eq_conv (T::e) M M' U ->
    eq_conv e (Abs T M) (Abs T M') (Prod T U).
red; induction 3; intros;  eauto with sets.
 apply rst_step.
 apply type_abs with U s1 s2; trivial.

 apply rst_trans with (Abs T y); trivial.
Qed.

  Lemma eq_conv_abs_l : forall e T T' M U s1 s2,
    eq_conv e T T' (Srt s1) ->
    eq_typ (T::e) U U (Srt s2) ->
    eq_typ (T::e) M M U ->
    eq_conv e (Abs T M) (Abs T' M) (Prod T U).
red; induction 1; intros; auto with sets.
 apply rst_step.
 apply type_abs with U s1 s2; trivial.

 apply rst_sym.
 apply eq_conv_conv with (Prod x U) s2.
  apply IHclos_refl_sym_trans.
   apply typ_red_env with (y :: e); trivial.
   constructor 1 with s1; apply eq_conv_sym; trivial.

   apply typ_red_env with (y :: e); trivial.
   constructor 1 with s1; apply eq_conv_sym; trivial.

  apply eq_conv_prod_l with s1; trivial.
  apply typ_red_env with (y :: e); trivial.
  constructor 1 with s1; apply eq_conv_sym; trivial.

 apply rst_trans with (Abs y M); auto.
 apply eq_conv_conv with (Prod y U) s2.
  apply IHclos_refl_sym_trans2.
   apply typ_red_env with (x :: e); trivial.
   constructor 1 with s1; trivial.

   apply typ_red_env with (x :: e); trivial.
   constructor 1 with s1; trivial.

  apply eq_conv_sym; trivial.
  apply eq_conv_prod_l with s1; trivial.
Qed.

  Lemma eq_conv_abs : forall e T T' M M' U s1 s2,
    eq_typ e T T (Srt s1) ->
    eq_typ (T::e) U U (Srt s2) ->
    eq_typ (T::e) M M U ->
    eq_conv e T T' (Srt s1) ->
    eq_conv (T::e) M M' U ->
    eq_conv e (Abs T M) (Abs T' M') (Prod T U).
intros.
red; apply rst_trans with (Abs T M').
 apply eq_conv_abs_r with s1 s2; trivial.

 apply eq_conv_abs_l with s1 s2; trivial.
 apply eq_conv_inv2 with M; trivial.
Qed.

Lemma eq_conv_app_r : forall e u v v' Ur V s1 s2,
  eq_typ e V V (Srt s1) ->
  eq_typ e u u (Prod V Ur) ->
  eq_typ (V::e) Ur Ur (Srt s2) ->
  eq_conv e v v' V ->
  eq_typ e v v V ->
  eq_conv e (App (Prod u Ur) v) (App (Prod u Ur) v') (subst v Ur).
red; induction 4; intros; eauto with sets.
 apply rst_step.
 apply type_app with V V s1 s2; trivial.

 apply rst_sym.
 apply eq_conv_conv with (subst x Ur) s2.
  apply IHclos_refl_sym_trans; trivial.
  apply eq_conv_inv2 with y; trivial.
  apply eq_conv_sym; trivial.

  apply eq_conv_subst_ty_l with V; trivial.

 apply rst_trans with (App (Prod u Ur) y); auto.
 apply eq_conv_conv with (subst y Ur) s2.
  apply IHclos_refl_sym_trans2; trivial.
  apply eq_conv_inv2 with x; trivial.

  apply eq_conv_sym.
  apply eq_conv_subst_ty_l with V; trivial.
Qed.

Lemma eq_conv_app_m : forall e u v T Ur Ur' s1 s2,
  eq_typ e v v T ->
  eq_typ e T T (Srt s1) ->
  eq_conv (T::e) Ur Ur' (Srt s2) ->
  eq_typ e u u (Prod T Ur) ->
  eq_typ (T::e) Ur Ur (Srt s2) ->
  eq_conv e (App (Prod u Ur) v) (App (Prod u Ur') v) (subst v Ur).
red; induction 3; intros; auto with sets.
 apply rst_step.
 apply type_app with T T s1 s2; trivial.

 apply rst_sym.
 apply eq_conv_conv with (subst v x) s2.
  apply IHclos_refl_sym_trans; trivial.
   apply type_eq_conv with (Prod T y) s2; trivial.
   apply eq_conv_prod_r with s1; trivial.
   apply eq_conv_sym; trivial.

   apply eq_conv_inv2 with y; trivial.
   apply eq_conv_sym; trivial.

  change (Srt s2) with (subst v (Srt s2)).
  apply eq_conv_subst_r with T; trivial.

 apply rst_trans with (App (Prod u y) v); auto.
 apply eq_conv_conv with (subst v y) s2.
  apply IHclos_refl_sym_trans2; trivial.
   apply type_eq_conv with (Prod T x) s2; trivial.
   apply eq_conv_prod_r with s1; trivial.

   apply eq_conv_inv2 with x; trivial.

  change (Srt s2) with (subst v (Srt s2)).
  apply eq_conv_subst_r with T; trivial.
  apply eq_conv_sym; trivial.
Qed.

Lemma eq_conv_app_l : forall e u u' v T Ur s1 s2,
  eq_typ e v v T ->
  eq_typ e T T (Srt s1) ->
  eq_typ (T::e) Ur Ur (Srt s2) ->
  eq_conv e u u' (Prod T Ur) ->
  eq_conv e (App (Prod u Ur) v) (App (Prod u' Ur) v) (subst v Ur).
red; induction 4; intros; auto with sets.
 apply rst_step.
 apply type_app with T T s1 s2; trivial.

 apply rst_trans with (App (Prod y Ur) v); auto.
Qed.

Lemma eq_conv_app : forall e u u' v v' Ur Ur' V s1 s2,
  eq_typ e v v V ->
  eq_typ e V V (Srt s1) ->
  eq_typ e u u (Prod V Ur) ->
  eq_typ (V::e) Ur Ur (Srt s2) ->
  eq_conv e u u' (Prod V Ur) ->
  eq_conv e v v' V ->
  eq_conv (V :: e) Ur Ur' (Srt s2) ->
  eq_conv e (App (Prod u Ur) v) (App (Prod u' Ur') v') (subst v Ur).
intros.
red; apply rst_trans with (App (Prod u' Ur) v).
 apply eq_conv_app_l with V s1 s2; trivial.

 apply rst_trans with (App (Prod u' Ur') v).
  apply eq_conv_app_m with V s1 s2; trivial.
  apply eq_conv_inv2 with u; trivial.

  apply eq_conv_conv with (subst v Ur') s2.
   apply eq_conv_app_r with V s1 s2; trivial.
    apply type_eq_conv with (Prod V Ur) s2.
     apply eq_conv_inv2 with u; trivial.

     apply eq_conv_prod_r with s1; trivial.

    apply eq_conv_inv2 with Ur; trivial.

   apply eq_conv_sym.
   change (Srt s2) with (subst v (Srt s2)).
   apply eq_conv_subst_r with V; trivial.
Qed.

Section Equivalence1.

  Fixpoint unmark_app (t:term) : term :=
    match t with
    | App (Prod u _) v => App (unmark_app u) (unmark_app v)
    | Abs T M => Abs (unmark_app T) (unmark_app M)
    | Prod T U => Prod (unmark_app T) (unmark_app U)
    | _ => t
    end.

  Definition unmark_env (e:env) : env := map unmark_app e.

  Lemma unmark_env_cons_inv : forall e1 T e,
    unmark_env e1 = T :: e ->
    exists2 T', unmark_app T' = T &
    exists2 e', unmark_env e' = e & e1 = T' :: e'.
intros.
destruct e1; try  discriminate.
unfold unmark_env in *.
simpl in H.
injection H; intros.
exists t; trivial.
exists e1; trivial.
Qed.

  Lemma unmark_sort_inv : forall T s, unmark_app T = Srt s -> T = Srt s.
destruct T; try (intros;  discriminate).
 auto.
 destruct T1; intros;  discriminate.
Qed.

  Lemma unmark_prod_inv : forall T A B,
    unmark_app T = Prod A B ->
    exists2 A', unmark_app A' = A &
    exists2 B', unmark_app B' = B & T = Prod A' B'.
destruct T; try (intros;  discriminate).
 destruct T1; intros;  discriminate.

 simpl; intros.
 injection H; intros.
 exists T1; trivial.
 exists T2; trivial.
Qed.

  Lemma unmark_lift : forall n t k,
    unmark_app (lift_rec n t k) = lift_rec n (unmark_app t) k.
induction t; simpl; intros; trivial.
 destruct (le_gt_dec k n0); simpl; trivial.

 rewrite IHt1;  rewrite IHt2; reflexivity.

 destruct t1; simpl in *; auto.
  destruct (le_gt_dec k n0); trivial.

  assert (H := IHt1 k); clear IHt1.
  injection H; intros.
  rewrite IHt2;  rewrite H1; reflexivity.

 rewrite IHt1;  rewrite IHt2; reflexivity.
Qed.

  Lemma unmark_item_lift : forall t e n,
    item_lift t e n -> item_lift (unmark_app t) (unmark_env e) n.
destruct 1; intros.
subst t.
unfold lift.
rewrite unmark_lift.
exists (unmark_app x); trivial.
unfold unmark_env.
elim H0; simpl; intros; auto with coc.
Qed.

  Lemma unmark_env_item : forall e e' n t,
    unmark_env e' = e ->
    item_lift t e n ->
    exists2 t', unmark_app t' = t & item_lift t' e' n.
destruct 2; intros.
subst t.
generalize e' H; clear e' H.
induction H1; intros.
 destruct e'; try  discriminate.
 injection H; intros.
 exists (lift 1 t).
  unfold lift; rewrite unmark_lift.
  rewrite H1; trivial.

  exists t; auto.

 destruct e'; try  discriminate.
 injection H; intros.
 elim (IHitem _ H0); intros.
 exists (lift 1 x0).
  unfold lift; rewrite unmark_lift; rewrite H3.
  change (lift 1 (lift (S n) x) = lift (S (S n)) x).
  rewrite <- simpl_lift.
  trivial.

  unfold lift; apply ins_item_lift_ge with t e'; auto with coc arith.
Qed.

  Lemma unmark_subst : forall N e M M' T,
    eq_typ e M M' T ->
    forall k,
    unmark_app (subst_rec N M k) = subst_rec (unmark_app N) (unmark_app M) k.
induction 1; simpl; intros; auto.
 destruct (lt_eq_lt_dec k v) as [[_| _]| _]; trivial.
   unfold lift; apply unmark_lift.
 rewrite IHeq_typ1;  rewrite IHeq_typ3; trivial.
 rewrite IHeq_typ1;  rewrite IHeq_typ3; trivial.
 rewrite IHeq_typ1;  rewrite IHeq_typ2; trivial.
 rewrite IHeq_typ1;  rewrite IHeq_typ2;  rewrite IHeq_typ3; trivial.
Qed.
  Lemma unmark_subst0 : forall N e M M' T,
    eq_typ e M M' T ->
    unmark_app (subst N M) = subst (unmark_app N) (unmark_app M).
Proof (fun N e M M' T H => unmark_subst N e M M' T H 0).

  Lemma unmark_subst2 : forall N e M M' T,
    eq_typ e M M' T ->
    forall k,
    unmark_app (subst_rec N M' k) = subst_rec (unmark_app N) (unmark_app M') k.
intros.
apply unmark_subst with e M' T.
apply typ_refl2 with M; trivial.
Qed.

  Lemma eq_typ_par_red0 : forall e M M' T,
    eq_typ e M M' T -> par_red1 (unmark_app M) (unmark_app M').
induction 1; intros; simpl; auto with coc.
unfold subst.
rewrite unmark_subst2 with (1 := H1).
fold (subst (unmark_app N') (unmark_app M')).
auto with coc.
Qed.

  Lemma eq_typ_typ : forall e M M' T,
    eq_typ e M M' T ->
    typ (unmark_env e) (unmark_app M) (unmark_app T).
intros.
elim H using eq_typ_mind with (P0 := fun e => Types.wf (unmark_env e));
  simpl; intros; auto with coc.
 constructor; trivial.

 constructor; trivial.
 apply unmark_item_lift; trivial.

 apply Types.type_abs with s1 s2; trivial.

 rewrite unmark_subst0 with (1 := H6).
 apply Types.type_app with (unmark_app V); simpl; trivial.

 apply Types.type_prod with s1; trivial.

 rewrite unmark_subst0 with (1 := H6).
 apply Types.type_app with (unmark_app T0); trivial.
 apply Types.type_abs with s1 s2; trivial.

 apply type_conv with (unmark_app T0) s; trivial.
  apply red_conv.
  apply par_red_red.
  constructor 1.
  apply eq_typ_par_red0 with (1 := H2).

  apply subject_reduction with (unmark_app T0); trivial.
  apply par_red_red.
  constructor 1.
  apply eq_typ_par_red0 with (1 := H2).

 apply type_conv with (unmark_app T') s; trivial.
 apply sym_conv.
 apply red_conv.
 apply par_red_red.
 constructor 1.
 apply eq_typ_par_red0 with (1 := H2).

 constructor.

 unfold unmark_env; simpl.
 apply Types.wf_var with s; trivial.
Qed.

End Equivalence1.

Section CC_Is_Functional.

  Lemma sort_uniqueness : forall e M M1 M2 s1 s2,
    eq_typ e M M1 (Srt s1) ->
    eq_typ e M M2 (Srt s2) ->
    s1 = s2.
intros.
apply conv_sort.
apply typ_unique with (unmark_env e) (unmark_app M); eauto.
 change (Srt s1) with (unmark_app (Srt s1)).
 apply eq_typ_typ with M1; trivial.

 change (Srt s2) with (unmark_app (Srt s2)).
 apply eq_typ_typ with M2; trivial.
Qed.

  Lemma eq_conv_sort_trans : forall e T U V s1 s2,
    eq_conv e T U (Srt s1) ->
    eq_conv e U V (Srt s2) ->
    eq_typ e T T (Srt s1) ->
    eq_conv e T V (Srt s1).
intros.
elim eq_conv_inv with (1 := H0); intros.
 subst V; trivial.

 destruct H2.
 apply eq_conv_trans with U; trivial.
 rewrite sort_uniqueness with e U U U s1 s2; trivial.
 apply eq_conv_inv2 with T; trivial.
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
   apply typ_refl with (1 := H2).

 intros.
 elim H1; intros.
 rewrite H2.
 generalize H0.
 inversion_clear H3; intros.
 rewrite simpl_lift; auto with coc.
 cut (wf l); intros.
  elim H with l (lift (S n0) x); intros; trivial.
   exists x0.
   change (Srt x0) with (lift 1 (Srt x0)).
   apply typ_thinning; auto with coc.

   exists x; auto with coc.

  inversion_clear H3.
  apply typ_wf with (1 := H5).
Qed.


(* type of types *)

  Theorem type_case :
   forall e t t' T, eq_typ e t t' T ->
   exists s, T = Srt s \/ eq_typ e T T (Srt s).
simple induction 1; intros; auto with coc.
 exists kind; auto.

 elim wf_sort_lift with (2 := H1); trivial; intros.
 exists x; auto.

 exists s2; right.
 apply typ_refl with (Prod T' U').
 apply type_prod with s1; auto with coc.

 exists s2; right.
 apply typ_refl with (subst v' Ur').
 change (Srt s2) with (subst v (Srt s2)).
 apply substitution with V; trivial.

 exists s2;auto.

 exists s2; right.
 apply typ_refl with (subst N' U').
 change (Srt s2) with (subst N (Srt s2)).
 apply substitution with T0; trivial.

 exists s;right.
 apply typ_refl2 with (1 := H2).

 exists s;right.
 apply typ_refl with (1 := H2).
Qed.

(* Inversion lemma *)
  Definition inv_type (P : Prop) e t t' T :=
    match t with
    | Srt s1 => forall s,
        s1 = prop -> eq_conv e (Srt kind) T (Srt s) -> t' = (Srt s1) -> P
    | Ref n =>
        forall x s, item_lift x e n -> eq_conv e x T (Srt s) -> t' = Ref n -> P
    | Abs A M =>
        forall A' M' U U' s1 s2,
        eq_typ e A A' (Srt s1) ->
        eq_typ (A :: e) M M' U ->
        eq_typ (A :: e) U U' (Srt s2) ->
        eq_conv e (Prod A U) T (Srt s2) -> t' = Abs A' M' -> P
    | App (Prod u Ur) v =>
        forall u' v' Ur' V V' M M' U s1 s2,
        eq_typ e v v' V ->
        eq_typ e V V' (Srt s1) ->
        eq_typ e u u' (Prod V Ur) ->
        eq_typ (V::e) Ur Ur' (Srt s2) ->
        eq_typ (V::e) M M' U ->
        t' = App (Prod u' Ur') v' \/
        u=Abs V M /\ U = Ur /\ t' = subst v' M' ->
        eq_conv e (subst v Ur) T (Srt s2) -> P
    | Prod A B =>
        forall A' B' s1 s2 s,
        eq_typ e A A' (Srt s1) ->
        eq_typ (A :: e) B B' (Srt s2) ->
        eq_conv e (Srt s2) T (Srt s) -> t' = Prod A' B' -> P
    | _ => True
    end.

  Lemma inv_type_conv :
   forall P e t t' U V s, eq_conv e U V (Srt s) ->
   inv_type P e t t' V -> inv_type P e t t' U.
do 8 intro.
elim eq_conv_inv with (1 := H); intros.
 subst U; trivial.

 destruct H0.
 destruct t; simpl in H1 |- *; intros.
  apply H1 with s; trivial.
  apply eq_conv_sym; apply eq_conv_sort_trans with U s1;
    try apply eq_conv_sym; trivial.

  apply H1 with x s; trivial.
  apply eq_conv_sym; apply eq_conv_sort_trans with U s0;
    try apply eq_conv_sym; trivial.

  apply H1 with A' M' U0 U' s1 s2; trivial.
  apply eq_conv_sort_trans with U s; trivial.
  apply type_prod with s1; trivial.
   apply typ_refl with A'; trivial.
   apply typ_refl with U'; trivial.

  destruct t1; intros; trivial.
  apply H1 with u' v' Ur' V0 V' M M' U0 s1 s2; trivial.
  apply eq_conv_sort_trans with U s; trivial.
  change (Srt s2) with (subst t2 (Srt s2)).
  apply typ_refl with (subst v' Ur').
  apply substitution with V0; trivial.

  apply H1 with A' B' s1 s2 s; trivial.
  apply eq_conv_sym; apply eq_conv_sort_trans with U s0; trivial;
    apply eq_conv_sym; trivial.
Qed.

  Theorem typ_inversion :
    forall P e t t' T, eq_typ e t t' T -> inv_type P e t t' T -> P.
induction 1; simpl; intros;  eauto with coc sets.
 apply H3 with (Abs T' M') N' U' T T' M M' U s1 s2; auto with coc sets.
 apply type_abs with U' s1 s2; trivial.

 apply IHeq_typ1.
 apply inv_type_conv with T' s; auto with coc.

 apply IHeq_typ1.
 apply inv_type_conv with T s; auto with coc.
Existential 1 := prop.
Existential 1 := prop.
Existential 1 := prop.
Qed.

  Lemma eq_typ_not_kind : forall e M M' T,
    eq_typ e M M' T ->
    M <> Srt kind.
Proof.
red; intros; subst M.
apply typ_inversion with (1 := H); red; simpl; intros; trivial.
discriminate.
Qed.


  Lemma red_prod_prod_eq : forall e T U K,
    eq_red e T U K ->
    forall A B, T = Prod A B ->
    forall (P:Prop),
    (forall A' B' s1 s2, U = Prod A' B' ->
     eq_conv e A A' (Srt s1) -> eq_conv (A::e) B B' (Srt s2) -> P) -> P.
induction 1; intros;  eauto with coc sets.
 subst x.
 apply typ_inversion with (1 := H); red; intros.
 eauto with coc.

 elim eq_red_inv with (1 := H); intros.
  subst y;  eapply IHclos_refl_trans2;  eauto.

  apply IHclos_refl_trans1 with (1 := H1); intros.
  apply IHclos_refl_trans2 with (1 := H4); intros.
  destruct H3.
  rewrite H1 in H3.
  apply typ_inversion with (1 := H3); simpl; intros.
  apply H2 with A'0 B'0 s4 s5; trivial.
   apply eq_conv_sort_trans with A' s0; trivial.
    apply eq_conv_sort_trans with A s1; auto with coc.
    apply typ_refl with A'1; trivial.

    apply typ_refl with A'1; trivial.

   apply eq_conv_sort_trans with B' s3; auto with coc.
    apply eq_conv_sort_trans with B s2; auto with coc.
    apply typ_refl with B'1; trivial.

    apply eq_conv_red_env with (A' :: e); trivial.
    constructor 1 with s1.
    apply eq_conv_sym; trivial.

    apply typ_refl with B'1; trivial.
Existential 1:=prop.
Existential 1:=prop.
Qed.

  Lemma red_prod_prod : forall e A B U K,
    eq_red e (Prod A B) U K ->
    forall (P:Prop),
    (forall A' B' s1 s2, U = Prod A' B' -> eq_conv e A A' (Srt s1) ->
     eq_conv (A::e) B B' (Srt s2) -> P) -> P.
intros.
apply red_prod_prod_eq with e (Prod A B) U K A B;  eauto.
Qed.


(* Type uniqueness *)
  Lemma eq_typ_uniqueness :
    forall e M M' T',
    eq_typ e M M' T' ->
    forall M'' T'',
    eq_typ e M M'' T'' ->
    exists s, eq_conv e T' T'' (Srt s).
induction 1; intros.
 apply typ_inversion with (1 := H0); simpl; intros.
 exists s; trivial.

 apply typ_inversion with (1 := H1); simpl; intros.
 rewrite item_lift_fun with (1 := H0) (2 := H2).
 exists s; trivial.

 apply typ_inversion with (1 := H2); simpl; intros.
 exists s3.
 assert (s1 = s0).
  apply sort_uniqueness with e T T' A'; trivial.
 assert (eq_conv (T :: e) U U0 (Srt s2)).
  elim IHeq_typ3 with (1 := H4); intros.
  apply eq_conv_sort_trans with U x; auto with coc.
  apply typ_refl with U'; trivial.
 assert (s2 = s3).
  apply sort_uniqueness with (T :: e) U0 U0 U'0; trivial.
  apply eq_conv_inv2 with U; trivial.
  apply typ_refl with U'; trivial.
 subst s0 s3.
 apply eq_conv_trans with (Prod T U0); trivial.
 apply eq_conv_prod_r with s1; trivial.
 apply typ_refl with T'; trivial.

 apply typ_inversion with (1 := H3); simpl; intros.
 exists s3; trivial.

 apply typ_inversion with (1 := H1); simpl; intros.
 exists s.
 assert (s1 = s0).
  apply sort_uniqueness with e T T' A'; trivial.
 assert (s2 = s3).
  apply sort_uniqueness with (T :: e) U U' B'; trivial.
 subst s0 s3.
 trivial.

 apply typ_inversion with (1 := H3); simpl; intros.
 exists s3; trivial.

 elim IHeq_typ1 with (1 := H1); intros.
 exists s.
 apply eq_conv_sort_trans with T x; auto with coc.
 apply typ_refl2 with T; trivial.

 elim IHeq_typ1 with (1 := H1); intros.
 exists s.
 apply eq_conv_sort_trans with T' x; auto with coc.
 apply typ_refl with T'; trivial.
Qed.

Lemma typ_change : forall e M N T,
  eq_typ e M N T ->
  forall N' T',
  eq_typ e M N' T' ->
  eq_typ e M N T'.
intros.
elim eq_typ_uniqueness with (1 := H) (2 := H0); intros.
apply type_eq_conv with T x; trivial.
Qed.

(* Confluence *)
Lemma str_confl : forall e A B T,
   eq_typ e A B T ->
   forall e' A' B' T',
   eq_typ e' A' B' T' ->
   e = e' -> A = A' ->
   exists2 C, eq_typ e B C T & eq_typ e B' C T'.
fix confl1 5.
destruct 1.
 intros;  subst e' A'.
 apply typ_inversion with (1 := H0); red; intros.
 subst B'.
 exists (Srt prop); trivial.
 constructor; trivial.

 intros;  subst e' A'.
 apply typ_inversion with (1 := H1); red; intros.
 subst B'.
 exists (Ref v); trivial.
 constructor; trivial.

 (* Abs *)
 intros;  subst e' A'.
 apply typ_inversion with (1 := H2); red; intros.
 clear H2;  subst B'.
 elim confl1 with (1 := H) (2 := H3); intros; trivial.
 elim confl1 with (1 := H1) (2 := H4); intros; trivial.
 exists (Abs x x0).
  apply type_exp with (Prod T' U) s2.
   apply type_abs with U' s1 s2; trivial.
    apply typ_red_env with (T :: e); trivial.
    constructor 1 with s1; auto with coc.

    apply typ_red_env with (T :: e); trivial.
    constructor 1 with s1; auto with coc.

   apply type_prod with s1; trivial.
   apply typ_refl with U'; trivial.

  apply type_eq_conv with (2 := H6).
  apply type_exp with (Prod A' U0) s3.
   apply type_abs with U'0 s0 s3; auto.
    apply typ_red_env with (T :: e); trivial.
    constructor 1 with s0; auto with coc.

    apply typ_red_env with (T :: e); trivial.
    constructor 1 with s0; auto with coc.

   apply type_prod with s0; trivial.
   apply typ_refl with U'0; trivial.

 (* App *)
 intros;  subst A'; intros.
 apply typ_inversion with (1 := H3); clear H3; red; intros.
 destruct H9.
  (* App/App *)
  subst e' B'.
  elim eq_typ_uniqueness with (1 := H) (2 := H3); intros s1' conv_V.
  assert (eq_typ (V :: e) Ur Ur'0 (Srt s3)).
   apply typ_red_env with (V0 :: e); trivial.
   constructor 1 with s1'; apply eq_conv_sym; trivial.
  elim confl1 with (1 := H) (2 := H3); intros; trivial.
  elim confl1 with (1 := H1) (2 := H6); intros; trivial.
  elim confl1 with (1 := H2) (2 := H4); trivial; intros.
  exists (App (Prod x0 x1) x).
   apply type_exp with (subst v' Ur') s2.
    apply type_app with V V' s1 s2; trivial.
    apply type_eq_conv with (Prod V Ur) s2; trivial.
    apply eq_conv_prod_r with s1; auto with coc.
    apply typ_refl with V'; trivial.

    change (Srt s2) with (subst v (Srt s2)).
    apply substitution with V; trivial.

   apply type_eq_conv with (2 := H10).
   apply type_exp with (subst v'0 Ur'0) s3.
    apply type_app with V0 V'0 s0 s3; trivial.
     apply type_eq_conv with (Prod V0 Ur) s3; trivial.
     apply eq_conv_prod_r with s0; auto with coc.
     apply typ_refl with V'0; trivial.

     apply typ_red_env with (V :: e); trivial.
     constructor 1 with s1'; auto with coc.

    change (Srt s3) with (subst v (Srt s3)).
    apply substitution with V0; trivial.

  (* App/beta *)
  destruct H9.
  destruct H11.
  subst U B'.
(*  generalize H6 H9; clear H8 H9.*)
  generalize H4 H9; clear H6 H9.
  elim H1; intros; try discriminate; auto. (* induction on sub-derivation... *)
  clear H1 H9 H12 H14.
  injection H16; clear H16; intros.
  elim confl1 with (1 := H) (2 := H3); intros; trivial.
  elim confl1 with (1 := H13) (2 := H8); intros;  subst e0 e' T M0;
     trivial.
  assert (eq_conv e V V0 (Srt s1)).
   elim eq_typ_uniqueness with (1 := H) (2 := H3); intros.
   apply eq_conv_sort_trans with V x1; auto with coc.
   apply typ_refl with V'; trivial.
  exists (subst x x0).
   apply type_exp with (subst v' Ur') s2.
    apply type_beta with T'0 Ur' s1 s2; trivial.
     apply type_red with V0 s4; trivial.
     apply type_eq_conv with V s1; trivial.

     apply typ_refl2 with V0.
     apply typ_change with (Srt s4) V0; trivial.
     apply eq_conv_inv2 with V; trivial.
     apply typ_refl with V'; trivial.

     apply typ_red_env with (V0 :: e).
      constructor 1 with s4; auto with coc.

      apply type_red with Ur s2; trivial.
       elim eq_typ_uniqueness with (1 := H13) (2 := H8); intros.
       apply type_eq_conv with (2 := H4); trivial.

       apply typ_red_env with (V :: e); trivial.
       constructor 1 with s1; trivial.

     apply typ_red_env with (V0 :: e).
      constructor 1 with s4; auto with coc.

      apply typ_red_env with (V :: e).
       constructor 1 with s1; trivial.
       apply typ_refl2 with Ur; trivial.

    change (Srt s2) with (subst v (Srt s2)).
    apply substitution with V; trivial.

   apply type_eq_conv with (2 := H10).
   apply type_exp with (subst v'0 Ur) s2.
    apply substitution with V0; trivial.

    change (Srt s2) with (subst v (Srt s2)).
    apply substitution with V.
     apply typ_refl with Ur'; trivial.

     apply type_eq_conv with V0 s1; auto with coc.
     apply eq_conv_sym; trivial.

 (* Prod *)
 intros;  subst e' A'.
 apply typ_inversion with (1 := H1); red; intros.
 subst B'.
 elim confl1 with (1 := H) (2 := H2); intros; trivial.
 elim confl1 with (1 := H0) (2 := H3); intros; trivial.
 exists (Prod x x0).
  apply type_prod with s1; trivial.
  apply typ_red_env with (T :: e); trivial.
  constructor 1 with s1; auto with coc.

  apply type_eq_conv with (2 := H4).
  apply type_prod with s0; trivial.
  apply typ_red_env with (T :: e); trivial.
  constructor 1 with s0; auto with coc.

 (* beta *)
 intros;  subst e' A'.
 apply typ_inversion with (1 := H3); clear H3; red; intros.
 destruct H8.
  (* beta / App *)
  subst B'.
  clear H7 M0 M'0 U0.
  apply typ_inversion with (1 := H5); clear H5; red; intros.
  subst u'.
  elim confl1 with (1 := H) (2 := H3); intros; trivial.
  elim confl1 with (1 := H1) (2 := H7); intros; trivial.
  assert (eq_conv e V T (Srt s0)).
   elim eq_typ_uniqueness with (1 := H3) (2 := H); intros.
   apply eq_conv_sort_trans with V x1; auto with coc.
   apply typ_refl with V'; trivial.
  exists (subst x x0).
   apply type_exp with (subst N' U) s2.
    apply substitution with T; trivial.

    change (Srt s2) with (subst N (Srt s2)).
    apply substitution with T; trivial.
    apply typ_refl with U'; trivial.

   apply type_eq_conv with (2 := H9).
   apply type_exp with (subst v' Ur') s3.
    apply type_beta with A' Ur' s0 s3; trivial.
     apply type_red with T s4; trivial.
     apply type_eq_conv with V s0; trivial.

     apply typ_refl2 with T.
     apply typ_change with (Srt s4) T; trivial.
     apply eq_conv_inv2 with V; trivial.
     apply typ_refl with V'; trivial.

     apply typ_red_env with (T :: e).
      constructor 1 with s4; auto with coc.

      apply type_red with U s3; trivial.
       elim eq_typ_uniqueness with (1 := H7) (2 := H1); intros.
       apply type_eq_conv with (2 := H16); trivial.

       apply typ_red_env with (V :: e); trivial.
       constructor 1 with s0; trivial.

     apply typ_red_env with (T :: e).
      constructor 1 with s4; auto with coc.

      apply typ_red_env with (V :: e).
       constructor 1 with s0; trivial.
       apply typ_refl2 with U; trivial.

    change (Srt s3) with (subst N (Srt s3)).
    apply substitution with V; trivial.

  (* beta/beta *)
  destruct H8.
  destruct H10.
  clear H5.
  injection H8; clear H8; intros;  subst V M0 U0 B'.
  elim confl1 with (1 := H) (2 := H3); intros; trivial.
  elim confl1 with (1 := H1) (2 := H7); intros; trivial.
  exists (subst x x0).
   apply type_exp with (subst N' U) s2.
    apply substitution with T; trivial.

    change (Srt s2) with (subst N (Srt s2)).
    apply substitution with T; trivial.
    apply typ_refl with U'; trivial.

   apply type_eq_conv with (2 := H9).
   apply type_exp with (subst v' U) s2.
    apply substitution with T; trivial.

    change (Srt s2) with (subst N (Srt s2)).
    apply substitution with T; trivial.
    apply typ_refl with U'; trivial.

 (* conv *)
 intros.
 elim confl1 with (1 := H) (2 := H1); intros; trivial.
 exists x; trivial.
 apply type_red with T s; trivial.

 intros.
 elim confl1 with (1 := H) (2 := H1); intros; auto.
 exists x; trivial.
 apply type_exp with T' s; trivial.
Qed.

  Lemma strip_lemma : forall e A B T,
   eq_red e A B T ->
   forall B',
   eq_typ e A B' T ->
   exists2 C, eq_red e B' C T & eq_typ e B C T.
unfold eq_red; induction 1; intros.
 elim str_confl with (1 := H) (2 := H0); trivial; intros.
 exists x0; auto with sets.

 exists B'; auto with sets.

 elim IHclos_refl_trans1 with (1 := H1); intros.
 elim IHclos_refl_trans2 with (1 := H3); intros.
 exists x1; trivial.
 apply rt_trans with x0; trivial.
Qed.

  Lemma confluence : forall e A B T,
   eq_red e A B T ->
   forall B',
   eq_red e A B' T ->
   exists2 C, eq_red e B' C T & eq_red e B C T.
induction 1; intros.
 elim strip_lemma with (1 := H0) (2 := H); intros.
 exists x0; unfold eq_red; auto with coc sets.

 exists B'; red; auto with sets.

 elim IHclos_refl_trans1 with (1 := H1); intros.
 elim IHclos_refl_trans2 with (1 := H3); intros.
 exists x1; trivial.
 red; apply rt_trans with x0; trivial.
Qed.

  Lemma church_rosser : forall e M M' T,
    eq_conv e M M' T ->
    exists2 N, eq_red e M N T & eq_red e M' N T.
induction 1; intros.
 exists y; red; auto with sets.

 exists x; red; auto with sets.

 destruct IHclos_refl_sym_trans.
 exists x0; trivial.

 destruct IHclos_refl_sym_trans1.
 destruct IHclos_refl_sym_trans2.
 elim confluence with (1 := H2) (2 := H3); intros.
 exists x2.
  red; apply rt_trans with x0; trivial.
  red; apply rt_trans with x1; trivial.
Qed.


(* Inversion of product *)
  Lemma inv_prod_l : forall e A B A' B' s3,
    eq_conv e (Prod A B) (Prod A' B') (Srt s3) ->
    exists s1, eq_conv e A A' (Srt s1).
intros.
elim eq_conv_inv with (1 := H); intros.
 injection H0; intros;  subst A'.
 exists prop; auto with coc.

 destruct H0.
 elim church_rosser with (1 := H); intros.
 apply red_prod_prod with (1 := H2); trivial; intros.
 apply red_prod_prod with (1 := H3); trivial; intros.
 subst x.
 injection H7; clear H7; intros;  subst A'1.
 apply typ_inversion with (1 := H0); simpl; intros.
 exists s5.
 apply eq_conv_sort_trans with A'0 s0; trivial.
  apply eq_conv_sort_trans with A s1; auto with coc.
  apply typ_refl with A'1; trivial.

  apply eq_conv_sym; trivial.

  apply typ_refl with A'1; trivial.
Qed.

  Lemma inv_prod_r : forall e A B A' B' s3,
    eq_conv e (Prod A B) (Prod A' B') (Srt s3) ->
    exists s2, eq_conv (A::e) B B' (Srt s2).
intros.
elim eq_conv_inv with (1 := H); intros.
 injection H0; intros;  subst B'.
 exists prop; auto with coc.

 destruct H0.
 elim church_rosser with (1 := H); intros.
 apply red_prod_prod with (1 := H2); trivial; intros.
 apply red_prod_prod with (1 := H3); trivial; intros.
 subst x.
 injection H7; clear H7; intros;  subst A'1 B'1.
 apply typ_inversion with (1 := H0); simpl; intros.
 exists s6.
 apply eq_conv_sort_trans with B'0 s4.
  apply eq_conv_sort_trans with B s2; auto with coc.
  apply typ_refl with B'1; trivial.

  apply eq_conv_red_env with (A'0 :: e).
   constructor 1 with s1; apply eq_conv_sym; trivial.

   apply eq_conv_red_env with (A' :: e).
    constructor 1 with s0; trivial.
    apply eq_conv_sym; trivial.

  apply typ_refl with B'1; trivial.
Qed.

(* Subject reduction *)
 
Inductive mpar_red1 : term -> term -> Prop :=
    par_beta : forall M M' N N' T U : term,
               mpar_red1 M M' ->
               mpar_red1 N N' ->
               mpar_red1 (App (Prod (Abs T M) U) N) (subst N' M')
  | sort_par_red : forall s, mpar_red1 (Srt s) (Srt s)
  | ref_par_red : forall n : nat, mpar_red1 (Ref n) (Ref n)
  | abs_par_red : forall M M' T T' : term,
                  mpar_red1 M M' ->
                  mpar_red1 T T' -> mpar_red1 (Abs T M) (Abs T' M')
  | app_par_red : forall M M' N N' U U' : term,
                  mpar_red1 M M' ->
                  mpar_red1 N N' ->
                  mpar_red1 U U' ->
                  mpar_red1 (App (Prod M U) N) (App (Prod M' U') N')
  | prod_par_red : forall M M' N N' : term,
                   mpar_red1 M M' ->
                   mpar_red1 N N' -> mpar_red1 (Prod M N) (Prod M' N').

Lemma mpar_red1_refl : forall e t t' u, eq_typ e t t' u -> mpar_red1 t t.
induction 1; auto; try (constructor; auto).
constructor; trivial.
Qed.

 Lemma subject_reduction :
    forall t u, mpar_red1 t u ->
    forall e t' T,
    eq_typ e t t' T ->
    eq_typ e t u T.
induction 1; intros.
 (* beta *)
 apply typ_inversion with (1 := H1); red; intros.
 clear H6 H7 M0 M'0 U0.
 apply typ_inversion with (1 := H4); red; intros.
 apply type_eq_conv with (2 := H8).
 elim inv_prod_l with (1 := H10); intros.
 apply type_beta with A' Ur' s1 s2;  eauto.
  apply type_eq_conv with V x;  eauto.
  apply eq_conv_sym; trivial.

  apply typ_change with (Srt s0) T; trivial.
  apply eq_conv_inv2 with V.
   apply eq_conv_sort_trans with V x; auto with coc.
    apply eq_conv_sym; trivial.
    apply typ_refl with V'; trivial.
   apply typ_refl with V'; trivial.

  elim inv_prod_r with (1 := H10); intros.
  apply type_eq_conv with (2 := H13).
  eauto.

  apply typ_red_env with (V :: e);  eauto.
  constructor 1 with x; apply eq_conv_sym; trivial.

 (* sort *)
 apply typ_inversion with (1 := H); red; intros;  subst t'; trivial.

 (* var *)
 apply typ_inversion with (1 := H); red; intros;  subst t'; trivial.

 (* Abs *)
 apply typ_inversion with (1 := H1); red; intros.
 apply type_eq_conv with (2 := H5).
 apply type_abs with U' s1 s2;  eauto.

 (* App *)
 apply typ_inversion with (1 := H2); red; intros.
 apply type_eq_conv with (2 := H9).
 apply type_app with V V' s1 s2;  eauto.

 (* Prod *)
 apply typ_inversion with (1 := H1); red; intros.
 apply type_eq_conv with (2 := H4).
 apply type_prod with s1;  eauto.
Qed.

Lemma red1_mpar_red1 : forall e x x' T,
  eq_typ e x x' T ->
  forall y,
  par_red1 (unmark_app x) y ->
  exists2 y', mpar_red1 x y' & unmark_app y' = y.
induction 1; simpl; intros;  eauto.
 inversion_clear H0.
   exists (Srt prop); auto.
   constructor.
 inversion_clear H1.
   exists (Ref v); auto; constructor.
 inversion_clear H2.
   elim IHeq_typ1 with (1 := H4); intros.
   elim IHeq_typ3 with (1 := H3); intros.
   exists (Abs x x0).
  constructor; trivial.
  simpl.
    rewrite H5; rewrite H7; trivial.
 generalize IHeq_typ3.
   inversion H3; intros.
  elim IHeq_typ0 with (Abs T M'); intros.
   destruct u; try  discriminate.
    elim IHeq_typ1 with (1 := H8); intros.
      inversion H9.
      exists (subst x0 M'0).
     constructor; trivial.
     apply typ_inversion with (1 := H1); simpl; intros.
       specialize subject_reduction with (1 := H15) (2 := H19); intro.
       specialize typ_refl2 with (1 := H23); intro.
       unfold subst; rewrite unmark_subst with (1 := H24).
        subst x.
       simpl in H10;  injection H10; clear H10; intros.
       rewrite H10; rewrite H12; trivial.
    destruct u1;  discriminate.
   auto with coc.
  elim IHeq_typ1 with (1 := H8); intros.
    elim IHeq_typ3 with (1 := H6); intros.
    exists (App (Prod x0 Ur) x); simpl.
   constructor; trivial.
     apply mpar_red1_refl with (1 := H2).
   rewrite H10; rewrite H12; trivial.
 inversion_clear H1.
   elim IHeq_typ1 with (1 := H2); intros.
   elim IHeq_typ2 with (1 := H3); intros.
   exists (Prod x x0); simpl.
  constructor; trivial.
  rewrite H4; rewrite H6; trivial.
 inversion_clear H3.
  elim IHeq_typ1 with (1 := H5); intros.
    elim IHeq_typ3 with (1 := H4); intros.
    exists (subst x x0).
   constructor; trivial.
   specialize subject_reduction with (1 := H7) (2 := H1); intro.
     specialize typ_refl2 with (1 := H9); intro.
     unfold subst; rewrite unmark_subst with (1 := H10).
     rewrite H6; rewrite H8; trivial.
  inversion_clear H4.
    elim IHeq_typ1 with (1 := H5); intros.
    elim IHeq_typ3 with (1 := H3); intros.
    elim IHeq_typ2 with (1 := H6); intros.
    exists (App (Prod (Abs x1 x0) U) x); simpl.
   constructor; trivial.
    constructor; trivial.
    apply mpar_red1_refl with (1 := H2).
   rewrite H7; rewrite H9; rewrite H11; trivial.
Qed.

  Lemma unmark_sr :
    forall e U U' T M',
    eq_typ e U U' T ->
    red (unmark_app U) M' ->
    exists2 M, unmark_app M = M' & eq_red e U M T.
induction 2; intros.
 exists U; trivial.
   red; trivial.
 destruct IHred.
   elim red1_mpar_red1 with e x x T N; intros.
  exists x0; trivial.
    red; apply rt_trans with x; trivial.
    apply rt_step.
    apply subject_reduction with x; trivial.
    apply eq_red_inv2 with U; trivial.
    apply typ_refl with U'; trivial.
  apply eq_red_inv2 with U; trivial.
    apply typ_refl with U'; trivial.
  apply red1_par_red1.
    rewrite H2; trivial.
Qed.

  Lemma unmark_eq_conv : forall U V e U' V' T T',
    eq_typ e U U' T ->
    eq_typ e V V' T' ->
    unmark_app U = unmark_app V ->
    eq_conv e U V T.
intros U V e U' V' T T' ty_U.
generalize V V' T'; clear V V' T'.
induction ty_U; intros.
 red; apply rst_step.
   simpl in H1.
   destruct V; try  discriminate H1.
  injection H1;clear H1;intro;subst s.
  constructor; trivial.
  destruct V1;  discriminate.
 destruct V; try  discriminate.
   injection H2; clear H2; intros.
     subst v; constructor 2; trivial.
  destruct V1;  discriminate.
 destruct V; try  discriminate.
  simpl in H0;  injection H0; clear H0; intros.
    apply typ_inversion with (1 := H); simpl; intros.
    specialize IHty_U1 with (1 := H2) (2 := H1).
    apply eq_conv_abs with s1 s2; trivial.
   apply typ_refl with T'; trivial.
   apply typ_refl with U'; trivial.
   apply typ_refl with M'; trivial.
   apply IHty_U3 with M'0 U0; trivial.
     apply typ_red_env with (V1 :: e); auto.
     constructor 1 with s1.
     apply eq_conv_sym; trivial.
  destruct V1;  discriminate.
 destruct V0; try  discriminate.
   apply typ_inversion with (1 := H); destruct V0_1; simpl; trivial;
    intros.
   simpl in H0;  injection H0; clear H0; intros.
   specialize IHty_U1 with (1 := H1) (2 := H0).
   specialize IHty_U3 with (1 := H3) (2 := H8).
   apply eq_conv_app with V s1 s2; trivial.
  apply typ_refl with v'; trivial.
  apply typ_refl with V'; trivial.
  apply typ_refl with u'; trivial.
  apply typ_refl with Ur'; trivial.
  assert (eq_typ e V0_1_1 V0_1_1 (Prod V Ur)).
   apply eq_conv_inv2 with u; trivial.
     apply typ_refl with u'; trivial.
   elim eq_typ_uniqueness with (1 := H9) (2 := H3); intros.
     elim inv_prod_r with (1 := H10); intros.
     apply eq_conv_sort_trans with Ur x0; auto with coc.
     apply typ_refl with Ur'; trivial.
 destruct V; try  discriminate.
  destruct V1;  discriminate.
 simpl in H0;  injection H0; clear H0; intros.
    apply typ_inversion with (1 := H); simpl; intros.
    specialize IHty_U1 with (1 := H2) (2 := H1).
    apply eq_conv_prod with s1; trivial.
   apply typ_refl with T'; trivial.
   apply typ_refl with U'; trivial.
   apply IHty_U2 with B' (Srt s3); trivial.
     apply typ_red_env with (V1 :: e); auto.
     constructor 1 with s1.
     apply eq_conv_sym; trivial.
 (* beta *)
 destruct V; try  discriminate.
 apply typ_inversion with (1 := H); destruct V1; simpl; trivial;
   intros.
 simpl in H0.
 destruct V1_1; try  discriminate.
 2:destruct V1_1_1;  discriminate.
 simpl in H0;  injection H0; clear H0; intros.
 apply typ_inversion with (1 := H3); clear H3 H6; simpl; intros.
 specialize IHty_U1 with (1 := H1) (2 := H0).
 specialize IHty_U2 with (1 := H3) (2 := H9).
 clear IHty_U4.
 apply eq_conv_app with T s1 s2; trivial.
  apply typ_refl with N'; trivial.
  apply typ_refl with T'; trivial.

  apply type_abs with U' s1 s2; trivial.
   apply typ_refl with T'; trivial.
   apply typ_refl with M'; trivial.

  apply typ_refl with U'; trivial.

  apply eq_conv_abs with s1 s2; trivial.
   apply typ_refl with T'; trivial.
   apply typ_refl with U'; trivial.
   apply typ_refl with M'; trivial.

   apply IHty_U3 with M'1 U1; trivial.
   apply typ_red_env with (V1_1_1 :: e); trivial.
   constructor 1 with s1.
   apply eq_conv_sym; trivial.

  elim inv_prod_r with (1 := H11); intros.
  apply eq_conv_sort_trans with U1 x.
   assert (eq_typ (V1_1_1 :: e) V1_1_2 V1_1_2 U).
    apply typ_red_env with (T :: e).
     constructor 1 with s1; trivial.

     apply eq_conv_inv2 with M.
      apply IHty_U3 with M'1 U1; trivial.
      apply typ_red_env with (V1_1_1 :: e); trivial.
      constructor 1 with s1.
      apply eq_conv_sym; trivial.

      apply typ_refl with M'; trivial.

   elim eq_typ_uniqueness with (1 := H14) (2 := H6); intros.
   apply eq_conv_sort_trans with U x0; auto with coc.
    apply eq_conv_red_env with (V1_1_1 :: e); trivial.
    constructor 1 with s1.
    apply eq_conv_sym; trivial.

    apply typ_refl with U'; trivial.

   apply eq_conv_red_env with (V1_1_1 :: e); trivial.
   constructor 1 with s1.
   apply eq_conv_sym; trivial.

   apply typ_refl with U'; trivial.
  
 apply eq_conv_conv with T s;  eauto with coc.
 apply eq_conv_conv with T' s;  eauto with coc.
Qed.

  Lemma red_env_unmark_conv : forall e f,
    unmark_env e = unmark_env f ->
    wf e ->
    wf f ->
    clos_refl_trans _ red1_in_env e f.
induction e; intros.
 destruct f; try  discriminate.
   apply rt_refl.
 destruct f; try  discriminate.
   unfold unmark_env in H; simpl in H;  injection H; clear H; intros.
   apply rt_trans with (a :: f).
  elim IHe with f; trivial; intros.
   apply rt_step.
     constructor; trivial.
   apply rt_trans with (a :: y); trivial.
   inversion H0;  eapply typ_wf;  eauto.
   inversion H1;  eapply typ_wf;  eauto.
  apply rt_step.
    inversion_clear H0.
    inversion_clear H1.
    constructor 1 with s.
    apply unmark_eq_conv with T' T'0 (Srt s0); trivial.
    apply typ_red_env_trans with e; trivial.
    apply IHe; trivial.
    eapply typ_wf;  eauto.
    eapply typ_wf;  eauto.
Qed.

  Lemma eq_typ_red_env_unmark : forall e f M M' T,
    unmark_env e = unmark_env f ->
    wf f ->
    eq_typ e M M' T ->
    eq_typ f M M' T.
intros.
apply typ_red_env_trans with e; trivial.
apply red_env_unmark_conv; trivial.
 eapply typ_wf;  eauto.
Qed.

  Lemma unmark_conv_sort : forall e U U' V V' s1 s2,
    eq_typ e U U' (Srt s1) ->
    eq_typ e V V' (Srt s2) ->
    conv (unmark_app U) (unmark_app V) ->
    eq_conv e U V (Srt s1).
intros.
elim Conv.church_rosser with (1 := H1); intros.
elim unmark_sr with (1 := H) (2 := H2); intros.
elim unmark_sr with (1 := H0) (2 := H3); intros.
apply eq_conv_sort_trans with x0 s2.
 apply eq_red_conv; trivial.
 apply eq_conv_trans with x1.
  apply eq_conv_sym.
    apply unmark_eq_conv with x1 x0 (Srt s1).
   apply eq_red_inv2 with V; trivial.
     apply typ_refl with V'; trivial.
   apply eq_red_inv2 with U; trivial.
     apply typ_refl with U'; trivial.
   rewrite H4; trivial.
  apply eq_conv_sym; apply eq_red_conv; trivial.
 apply typ_refl with U'; trivial.
Qed.

  Lemma typ_eq_typ : forall e M T,
    typ e M T ->
    exists2 e', unmark_env e' = e &
    exists2 M', unmark_app M' = M &
    exists2 T', unmark_app T' = T &
    eq_typ e' M' M' T'.
Proof.
intros e M T H.
elim H using typ_mind
  with (P0 := fun e => exists2 e', unmark_env e' = e & wf e');
 clear e M T H; simpl; intros.
 destruct H0.
 exists x; trivial.
 exists (Srt prop); trivial.
 exists (Srt kind); trivial.
 constructor; trivial.

 destruct H0.
 exists x; trivial.
 exists (Ref v); trivial.
 elim unmark_env_item with (1 := H0) (2 := H1); intros.
 exists x0; trivial.
 constructor; trivial.

 destruct H0 as (e', unmk_e, (A, unmk_A, (s1', unmk_s1, ty_A))).
 rewrite unmark_sort_inv with (1 := unmk_s1) in ty_A; clear unmk_s1 s1'.
 destruct H2 as (e1, unmk_e1, (U', unmk_U, (s2', unmk_s2, ty_U))).
 rewrite unmark_sort_inv with (1 := unmk_s2) in ty_U; clear unmk_s2 s2'.
 elim unmark_env_cons_inv with (1 := unmk_e1);
   intros T1 unmk_T1 (e2, unmk_e2, eq_e1); clear unmk_e1; subst e1.
 destruct H4 as (e3, unmk_e3, (M', unmk_M, (U2, unmk_U2, ty_M))).
 elim unmark_env_cons_inv with (1 := unmk_e3);
   intros T2 unmk_T2 (e4, unmk_e4, eq_e2); clear unmk_e3; subst e3.
 exists e'; trivial.
 exists (Abs A M'); simpl.
  rewrite unmk_A; rewrite unmk_M; trivial.
 exists (Prod A U2); simpl.
  rewrite unmk_A; rewrite unmk_U2; trivial.
 apply type_abs with U2 s1 s2; trivial.
  assert (eq_typ (T2::e4) U' U' (Srt s2)).
   apply eq_typ_red_env_unmark with (T1::e2); trivial.
    unfold unmark_env; simpl; fold (unmark_env e2) (unmark_env e4).
    rewrite unmk_T1; rewrite unmk_e2; rewrite unmk_T2; rewrite unmk_e4; trivial.

    eapply typ_wf; eauto.
  apply eq_typ_red_env_unmark with (T2::e4); trivial.
   unfold unmark_env; simpl; fold (unmark_env e4) (unmark_env e').
   rewrite unmk_T2; rewrite unmk_e4; rewrite unmk_A; rewrite unmk_e; trivial.

   apply wf_var with A s1; trivial.
  elim type_case with (1 := ty_M); intros.
  destruct H2.
   subst U2 U.
   rewrite unmark_sort_inv with U' x in H0; auto with coc.

   apply eq_conv_inv2 with U'; trivial.
   apply unmark_eq_conv with (1 := H0) (2 := H2); trivial.
   rewrite unmk_U2; auto.

  apply eq_typ_red_env_unmark with (T2::e4); trivial.
   unfold unmark_env; simpl; fold (unmark_env e4) (unmark_env e').
   rewrite unmk_T2; rewrite unmk_e4; rewrite unmk_A; rewrite unmk_e; trivial.

   apply wf_var with A s1; trivial.

 destruct H0 as (e', unmk_e, (v', unmk_v, (V', unmk_V, ty_v))).
 destruct H2 as (e1, unmk_e1, (u', unmk_u, (U', unmk_U, ty_u))).
 exists e'; trivial.
 specialize unmark_prod_inv with (1 := unmk_U).
 intros (V1, eq_V, (Ur', eq_Ur, eq_U')).
 exists (App (Prod u' Ur') v'); simpl.
  rewrite unmk_u; rewrite unmk_v; trivial.
  subst U'.
  elim type_case with (1 := ty_u); intros s [eq_s|ty_pi];
    try discriminate.
  exists (subst v' Ur').
   unfold subst.
   apply typ_inversion with (1 := ty_pi); simpl; intros.
   rewrite unmark_subst with (1 := H2).
   rewrite unmk_v; rewrite eq_Ur; trivial.

   apply typ_inversion with (1 := ty_pi); simpl; intros.
   apply type_app with V1 A' s1 s2; trivial.
    elim type_case with (1 := ty_v); intros.
    destruct H5.
    subst V' V; simpl in unmk_V.
     rewrite unmark_sort_inv with V1 x; auto with coc.        
      apply type_eq_conv with V' x; trivial.
      apply unmark_eq_conv with V' A' (Srt s1); trivial.

     apply eq_typ_red_env_unmark with e1; trivial.
      rewrite unmk_e; trivial.
      apply typ_wf with (1 := ty_v).

     rewrite eq_V; auto with coc.

    apply eq_typ_red_env_unmark with e1; trivial.
     rewrite unmk_e; trivial.
     apply typ_wf with (1 := ty_v).

    apply eq_typ_red_env_unmark with e1; trivial.
     rewrite unmk_e; trivial.
     apply typ_wf with (1 := ty_v).

    apply typ_refl with B'.
    apply eq_typ_red_env_unmark with (V1 :: e1); trivial.
     unfold unmark_env; simpl.
     fold (unmark_env e1).
     fold (unmark_env e').
     rewrite unmk_e; rewrite unmk_e1; trivial.

     apply wf_var with A' s1.
     apply eq_typ_red_env_unmark with e1; trivial.
      rewrite unmk_e; trivial.
      apply typ_wf with (1 := ty_v).

 destruct H0 as (e', unmk_e, (T', unmk_T, (s1', unmk_s1, ty_T))).
   exists e'; trivial.
   rewrite unmark_sort_inv with (1 := unmk_s1) in ty_T.
   clear unmk_s1 s1'.
   destruct H2 as (e1, unmk_e1, (U', unmk_U, (s2', unmk_s2, ty_U))).
   rewrite unmark_sort_inv with (1 := unmk_s2) in ty_U.
   clear unmk_s2 s2'.
   exists (Prod T' U'); simpl.
  rewrite unmk_T; rewrite unmk_U; trivial.
  exists (Srt s2); trivial.
    apply type_prod with s1; trivial.
    apply eq_typ_red_env_unmark with e1; trivial.
   rewrite unmk_e1.
     rewrite <- unmk_e; rewrite <- unmk_T; trivial.
   apply wf_var with T' s1; trivial.

 destruct H0 as (e', unmk_e, (t', unmk_t, (U', unmk_U, ty_t))).
   destruct H3 as (e1, unmk_e1, (V', unmk_V, (s', unmk_s, ty_V))).
   exists e'; trivial.
   exists t'; trivial.
   exists V'; trivial.
   rewrite unmark_sort_inv with (1 := unmk_s) in ty_V.
   apply type_eq_conv with U' s; trivial.
   assert (exists s' : _, eq_typ e' U' U' (Srt s')).
  elim type_case with (1 := ty_t); intros.
    destruct H0.
   exists s.
      subst U' U; simpl in H1.
     assert (typ e (Srt x) (Srt s)).
    apply Types.subject_reduction with V; trivial.
    apply Conv.church_rosser in H1; destruct H1.
    apply red_normal in H0.
     rewrite H0; trivial.

     red; red; intros.
     inversion H3.

    apply Types.typ_inversion with (1 := H0); simpl; intros.
    destruct x; trivial; intros.
    apply conv_sort in H3; subst s.
    constructor; trivial.
    eapply typ_wf;  eauto.

   exists x; trivial.
  destruct H0.
    apply eq_conv_sym.
    apply unmark_conv_sort with V' U' x; trivial.
   apply eq_typ_red_env_unmark with e1; trivial.
    rewrite unmk_e; trivial.
    apply typ_wf with (1 := ty_t).
   rewrite unmk_U; rewrite unmk_V; auto with coc.

 exists (nil:env); auto.
   constructor.

 destruct H0 as (e', unmk_e, (T', unmk_T, (s', unmk_s, ty_T))).
   exists (T' :: e'); trivial.
  unfold unmark_env; simpl.
    fold (unmark_env e').
    rewrite unmk_e; rewrite unmk_T; trivial.
  rewrite unmark_sort_inv with (1 := unmk_s) in ty_T.
    apply wf_var with T' s; trivial.
Qed.

End CC_Is_Functional.

End Typage.

