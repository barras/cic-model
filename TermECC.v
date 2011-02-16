
Require Export Arith.
Require Export Compare_dec.
Require Export Relations.

Hint Resolve t_step rt_step rt_refl: core.
Hint Unfold transp: core.

Section Termes.

  Inductive sort : Set :=
    | kind : nat -> sort
    | prop : sort.

  Inductive term : Set :=
    | Srt : sort -> term
    | Ref : nat -> term
    | Abs : term -> term -> term
    | App : term -> term -> term
    | Prod : term -> term -> term.

  Fixpoint lift_rec (n : nat) (t : term) (k : nat) {struct t} : term :=
    match t with
    | Srt s => Srt s
    | Ref i =>
        match le_gt_dec k i with
        | left _ => Ref (n + i)
        | right _ => Ref i
        end
    | Abs T M => Abs (lift_rec n T k) (lift_rec n M (S k))
    | App u v => App (lift_rec n u k) (lift_rec n v k)
    | Prod A B => Prod (lift_rec n A k) (lift_rec n B (S k))
    end.

  Definition lift n t := lift_rec n t 0.

  Fixpoint subst_rec (N M : term) (k : nat) {struct M} : term :=
    match M with
    | Srt s => Srt s
    | Ref i =>
        match lt_eq_lt_dec k i with
        | inleft (left _) => Ref (pred i)
        | inleft (right _) => lift k N
        | inright _ => Ref i
        end
    | Abs A B => Abs (subst_rec N A k) (subst_rec N B (S k))
    | App u v => App (subst_rec N u k) (subst_rec N v k)
    | Prod T U => Prod (subst_rec N T k) (subst_rec N U (S k))
    end.

  Definition subst N M := subst_rec N M 0.


  Inductive subterm : term -> term -> Prop :=
    | sbtrm_abs_l : forall A B, subterm A (Abs A B)
    | sbtrm_abs_r : forall A B, subterm B (Abs A B)
    | sbtrm_app_l : forall A B, subterm A (App A B)
    | sbtrm_app_r : forall A B, subterm B (App A B)
    | sbtrm_prod_l : forall A B, subterm A (Prod A B)
    | sbtrm_prod_r : forall A B, subterm B (Prod A B).

  Inductive mem_sort (s : sort) : term -> Prop :=
    | mem_eq : mem_sort s (Srt s)
    | mem_prod_l : forall u v, mem_sort s u -> mem_sort s (Prod u v)
    | mem_prod_r : forall u v, mem_sort s v -> mem_sort s (Prod u v)
    | mem_abs_l : forall u v, mem_sort s u -> mem_sort s (Abs u v)
    | mem_abs_r : forall u v, mem_sort s v -> mem_sort s (Abs u v)
    | mem_app_l : forall u v, mem_sort s u -> mem_sort s (App u v)
    | mem_app_r : forall u v, mem_sort s v -> mem_sort s (App u v).

End Termes.

  Hint Constructors subterm: coc.
  Hint Constructors mem_sort: coc.


Section Beta_Reduction.

  Inductive red1 : term -> term -> Prop :=
    | beta : forall M N T, red1 (App (Abs T M) N) (subst N M)
    | abs_red_l :
        forall M M', red1 M M' -> forall N, red1 (Abs M N) (Abs M' N)
    | abs_red_r :
        forall M M', red1 M M' -> forall N, red1 (Abs N M) (Abs N M')
    | app_red_l :
        forall M1 N1, red1 M1 N1 -> forall M2, red1 (App M1 M2) (App N1 M2)
    | app_red_r :
        forall M2 N2, red1 M2 N2 -> forall M1, red1 (App M1 M2) (App M1 N2)
    | prod_red_l :
        forall M1 N1, red1 M1 N1 -> forall M2, red1 (Prod M1 M2) (Prod N1 M2)
    | prod_red_r :
        forall M2 N2, red1 M2 N2 -> forall M1, red1 (Prod M1 M2) (Prod M1 N2).

  Inductive red (M : term) : term -> Prop :=
    | refl_red : red M M
    | trans_red : forall P N, red M P -> red1 P N -> red M N.

  Inductive conv (M : term) : term -> Prop :=
    | refl_conv : conv M M
    | trans_conv_red : forall P N, conv M P -> red1 P N -> conv M N
    | trans_conv_exp : forall P N, conv M P -> red1 N P -> conv M N.

  Inductive par_red1 : term -> term -> Prop :=
    | par_beta :
        forall M M' N N' T,
        par_red1 M M' ->
        par_red1 N N' -> par_red1 (App (Abs T M) N) (subst N' M')
    | sort_par_red : forall s, par_red1 (Srt s) (Srt s)
    | ref_par_red : forall n, par_red1 (Ref n) (Ref n)
    | abs_par_red :
        forall M M' T T',
        par_red1 M M' -> par_red1 T T' -> par_red1 (Abs T M) (Abs T' M')
    | app_par_red :
        forall M M' N N',
        par_red1 M M' -> par_red1 N N' -> par_red1 (App M N) (App M' N')
    | prod_par_red :
        forall M M' N N',
        par_red1 M M' -> par_red1 N N' -> par_red1 (Prod M N) (Prod M' N').

  Definition par_red := clos_trans term par_red1.

End Beta_Reduction.


  Hint Constructors red1: coc.
  Hint Constructors par_red1: coc.
  Hint Resolve refl_red refl_conv: coc.
  Hint Unfold par_red: coc.


Section Normalisation_Forte.

  Definition normal t := forall u, ~ red1 t u.

  Definition sn := Acc (transp _ red1).

End Normalisation_Forte.

  Hint Unfold sn: coc.


  Lemma inv_lift_sort :  forall s n t k, lift_rec n t k = Srt s -> t = Srt s.
intros.
destruct t; try  discriminate H.
 auto.
 unfold lift_rec in H.
   destruct (le_gt_dec k n0);  discriminate H.
Qed.

  Lemma inv_subst_sort :
    forall s x t k, subst_rec x t k = Srt s -> t = Srt s \/ x = Srt s.
intros.
destruct t; try  discriminate H.
 auto.
 unfold subst_rec in H.
   destruct (lt_eq_lt_dec k n) as [[fv| eqv]| bv]; try  discriminate H.
   right.
   unfold lift in H.
   apply inv_lift_sort with (1 := H).
Qed.


  Lemma lift_ref_ge :
   forall k n p, p <= n -> lift_rec k (Ref n) p = Ref (k + n).
intros; simpl in |- *.
elim (le_gt_dec p n); auto with arith.
intro; absurd (p <= n); auto with arith.
Qed.


  Lemma lift_ref_lt : forall k n p, p > n -> lift_rec k (Ref n) p = Ref n.
intros; simpl in |- *.
elim (le_gt_dec p n); auto with arith.
intro; absurd (p <= n); auto with arith.
Qed.


  Lemma subst_ref_lt : forall u n k, k > n -> subst_rec u (Ref n) k = Ref n.
simpl in |- *; intros.
elim (lt_eq_lt_dec k n); intros; auto with arith.
elim a; intros.
absurd (k <= n); auto with arith.

inversion_clear b in H.
elim gt_irrefl with n; auto with arith.
Qed.


  Lemma subst_ref_gt :
   forall u n k, n > k -> subst_rec u (Ref n) k = Ref (pred n).
simpl in |- *; intros.
elim (lt_eq_lt_dec k n); intros.
elim a; intros; auto with arith.
inversion_clear b in H.
elim gt_irrefl with n; auto with arith.

absurd (k <= n); auto with arith.
Qed.


  Lemma subst_ref_eq : forall u n, subst_rec u (Ref n) n = lift n u.
intros; simpl in |- *.
elim (lt_eq_lt_dec n n); intros.
elim a; intros; auto with coc.
elim lt_irrefl with n; auto with coc.

elim gt_irrefl with n; auto with coc.
Qed.



  Lemma lift_rec0 : forall M k, lift_rec 0 M k = M.
simple induction M; simpl in |- *; intros; auto with coc.
elim (le_gt_dec k n); auto with coc.

rewrite H; rewrite H0; auto with coc.

rewrite H; rewrite H0; auto with coc.

rewrite H; rewrite H0; auto with coc.
Qed.


  Lemma lift0 : forall M, lift 0 M = M.
intros; unfold lift in |- *.
apply lift_rec0; auto with coc.
Qed.


  Lemma simpl_lift_rec :
   forall M n k p i,
   i <= k + n ->
   k <= i -> lift_rec p (lift_rec n M k) i = lift_rec (p + n) M k.
simple induction M; simpl in |- *; intros; auto with coc.
elim (le_gt_dec k n); intros.
rewrite lift_ref_ge; auto with coc.
rewrite plus_assoc; auto with coc.

rewrite plus_comm.
apply le_trans with (k + n0); auto with arith.

rewrite lift_ref_lt; auto with arith.
apply le_gt_trans with k; auto with arith.

rewrite H; auto with arith; rewrite H0; simpl in |- *; auto with arith.

rewrite H; auto with arith; rewrite H0; simpl in |- *; auto with arith.

rewrite H; auto with arith; rewrite H0; simpl in |- *; auto with arith.
Qed.


  Lemma simpl_lift : forall M n, lift (S n) M = lift 1 (lift n M).
intros; unfold lift in |- *.
rewrite simpl_lift_rec; auto with arith.
Qed.


  Lemma permute_lift_rec :
   forall M n k p i,
   i <= k ->
   lift_rec p (lift_rec n M k) i = lift_rec n (lift_rec p M i) (p + k).
simple induction M; simpl in |- *; intros; auto with coc.
elim (le_gt_dec k n); elim (le_gt_dec i n); intros.
rewrite lift_ref_ge; auto with arith.
rewrite lift_ref_ge; auto with arith.
elim plus_assoc_reverse with p n0 n.
elim plus_assoc_reverse with n0 p n.
elim plus_comm with p n0; auto with arith.

apply le_trans with n; auto with arith.

absurd (i <= n); auto with arith.
apply le_trans with k; auto with arith.

rewrite lift_ref_ge; auto with arith.
rewrite lift_ref_lt; auto with arith.

rewrite lift_ref_lt; auto with arith.
rewrite lift_ref_lt; auto with arith.
apply le_gt_trans with k; auto with arith.

rewrite H; auto with arith; rewrite H0; auto with arith.
rewrite plus_n_Sm; auto with arith.

rewrite H; auto with arith; rewrite H0; auto with arith.

rewrite H; auto with arith; rewrite H0; auto with arith.
rewrite plus_n_Sm; auto with arith.
Qed.


  Lemma permute_lift :
   forall M k, lift 1 (lift_rec 1 M k) = lift_rec 1 (lift 1 M) (S k).
intros.
change (lift_rec 1 (lift_rec 1 M k) 0 = lift_rec 1 (lift_rec 1 M 0) (1 + k))
 in |- *.
apply permute_lift_rec; auto with arith.
Qed.


  Lemma simpl_subst_rec :
   forall N M n p k,
   p <= n + k ->
   k <= p -> subst_rec N (lift_rec (S n) M k) p = lift_rec n M k.
simple induction M; simpl in |- *; intros; auto with arith.
elim (le_gt_dec k n); intros.
rewrite subst_ref_gt; auto with arith.
red in |- *; red in |- *.
apply le_trans with (S (n0 + k)); auto with arith.

rewrite subst_ref_lt; auto with arith.
apply le_gt_trans with k; auto with arith.

rewrite H; auto with arith; rewrite H0; auto with arith.
elim plus_n_Sm with n k; auto with arith.

rewrite H; auto with arith; rewrite H0; auto with arith.

rewrite H; auto with arith; rewrite H0; auto with arith.
elim plus_n_Sm with n k; auto with arith.
Qed.


  Lemma simpl_subst :
   forall N M n p, p <= n -> subst_rec N (lift (S n) M) p = lift n M.
intros; unfold lift in |- *.
apply simpl_subst_rec; auto with arith.
Qed.


  Lemma commut_lift_subst_rec :
   forall M N n p k,
   k <= p ->
   lift_rec n (subst_rec N M p) k = subst_rec N (lift_rec n M k) (n + p).
simple induction M; intros; auto with arith.
unfold subst_rec at 1, lift_rec at 2 in |- *.
elim (lt_eq_lt_dec p n); elim (le_gt_dec k n); intros.
elim a0.
case n; intros.
inversion_clear a1.

unfold pred in |- *.
rewrite lift_ref_ge; auto with arith.
rewrite subst_ref_gt; auto with arith.
elim plus_n_Sm with n0 n1.
auto with arith.

apply le_trans with p; auto with arith.

simple induction 1.
rewrite subst_ref_eq.
unfold lift in |- *.
rewrite simpl_lift_rec; auto with arith.

absurd (k <= n); auto with arith.
apply le_trans with p; auto with arith.
elim a; auto with arith.
simple induction 1; auto with arith.

rewrite lift_ref_ge; auto with arith.
rewrite subst_ref_lt; auto with arith.

rewrite lift_ref_lt; auto with arith.
rewrite subst_ref_lt; auto with arith.
apply le_gt_trans with p; auto with arith.

simpl in |- *.
rewrite plus_n_Sm.
rewrite H; auto with arith; rewrite H0; auto with arith.

simpl in |- *; rewrite H; auto with arith; rewrite H0; auto with arith.

simpl in |- *; rewrite plus_n_Sm.
rewrite H; auto with arith; rewrite H0; auto with arith.
Qed.


  Lemma commut_lift_subst :
   forall M N k, subst_rec N (lift 1 M) (S k) = lift 1 (subst_rec N M k).
intros; unfold lift in |- *.
rewrite commut_lift_subst_rec; auto with arith.
Qed.


  Lemma distr_lift_subst_rec :
   forall M N n p k,
   lift_rec n (subst_rec N M p) (p + k) =
   subst_rec (lift_rec n N k) (lift_rec n M (S (p + k))) p.
simple induction M; intros; auto with arith.
unfold subst_rec at 1 in |- *.
elim (lt_eq_lt_dec p n); intro.
elim a.
case n; intros.
inversion_clear a0.

unfold pred, lift_rec at 1 in |- *.
elim (le_gt_dec (p + k) n1); intro.
rewrite lift_ref_ge; auto with arith.
elim plus_n_Sm with n0 n1.
rewrite subst_ref_gt; auto with arith.
red in |- *; red in |- *; apply le_n_S.
apply le_trans with (n0 + (p + k)); auto with arith.
apply le_trans with (p + k); auto with arith.

rewrite lift_ref_lt; auto with arith.
rewrite subst_ref_gt; auto with arith.

simple induction 1.
unfold lift in |- *.
rewrite <- permute_lift_rec; auto with arith.
rewrite lift_ref_lt; auto with arith.
rewrite subst_ref_eq; auto with arith.

rewrite lift_ref_lt; auto with arith.
rewrite lift_ref_lt; auto with arith.
rewrite subst_ref_lt; auto with arith.

simpl in |- *; replace (S (p + k)) with (S p + k); auto with arith.
rewrite H; rewrite H0; auto with arith.

simpl in |- *; rewrite H; rewrite H0; auto with arith.

simpl in |- *; replace (S (p + k)) with (S p + k); auto with arith.
rewrite H; rewrite H0; auto with arith.
Qed.


  Lemma distr_lift_subst :
   forall M N n k,
   lift_rec n (subst N M) k = subst (lift_rec n N k) (lift_rec n M (S k)).
intros; unfold subst in |- *.
pattern k at 1 3 in |- *.
replace k with (0 + k); auto with arith.
apply distr_lift_subst_rec.
Qed.


  Lemma distr_subst_rec :
   forall M N P n p,
   subst_rec P (subst_rec N M p) (p + n) =
   subst_rec (subst_rec P N n) (subst_rec P M (S (p + n))) p.
simple induction M; auto with arith; intros.
unfold subst_rec at 2 in |- *.
elim (lt_eq_lt_dec p n); intro.
elim a.
case n; intros.
inversion_clear a0.

unfold pred, subst_rec at 1 in |- *.
elim (lt_eq_lt_dec (p + n0) n1); intro.
elim a1.
case n1; intros.
inversion_clear a2.

rewrite subst_ref_gt; auto with arith.
rewrite subst_ref_gt; auto with arith.
apply gt_le_trans with (p + n0); auto with arith.

simple induction 1.
rewrite subst_ref_eq; auto with arith.
rewrite simpl_subst; auto with arith.

rewrite subst_ref_lt; auto with arith.
rewrite subst_ref_gt; auto with arith.

simple induction 1.
rewrite subst_ref_lt; auto with arith.
rewrite subst_ref_eq.
unfold lift in |- *.
rewrite commut_lift_subst_rec; auto with arith.

do 3 (rewrite subst_ref_lt; auto with arith).

simpl in |- *; replace (S (p + n)) with (S p + n); auto with arith.
rewrite H; auto with arith; rewrite H0; auto with arith.

simpl in |- *; rewrite H; rewrite H0; auto with arith.

simpl in |- *; replace (S (p + n)) with (S p + n); auto with arith.
rewrite H; rewrite H0; auto with arith.
Qed.


  Lemma distr_subst :
   forall P N M k,
   subst_rec P (subst N M) k = subst (subst_rec P N k) (subst_rec P M (S k)).
intros; unfold subst in |- *.
pattern k at 1 3 in |- *.
replace k with (0 + k); auto with arith.
apply distr_subst_rec.
Qed.



  Lemma one_step_red : forall M N, red1 M N -> red M N.
intros.
apply trans_red with M; auto with coc.
Qed.

  Hint Resolve one_step_red: coc.


  Lemma red1_red_ind :
   forall N P,
   (P:term -> Prop) N ->
   (forall M R, red1 M R -> red R N -> P R -> P M) ->
   forall M, red M N -> P M.
cut
 (forall M N,
  red M N ->
  forall P : term -> Prop,
  P N -> (forall M R, red1 M R -> red R N -> P R -> P M) -> P M).
intros.
apply (H M N); auto with coc.

simple induction 1; intros; auto with coc.
apply H1; auto with coc.
apply H4 with N0; auto with coc.

intros.
apply H4 with R; auto with coc.
apply trans_red with P; auto with coc.
Qed.


  Lemma trans_red_red : forall M N P, red M N -> red N P -> red M P.
intros.
generalize H0 M H.
simple induction 1; auto with coc.
intros.
apply trans_red with P0; auto with coc.
Qed.
 

  Lemma red_red_app :
   forall u u0 v v0, red u u0 -> red v v0 -> red (App u v) (App u0 v0).
simple induction 1.
simple induction 1; intros; auto with coc.
apply trans_red with (App u P); auto with coc.

intros.
apply trans_red with (App P v0); auto with coc.
Qed.


  Lemma red_red_abs :
   forall u u0 v v0, red u u0 -> red v v0 -> red (Abs u v) (Abs u0 v0).
simple induction 1.
simple induction 1; intros; auto with coc.
apply trans_red with (Abs u P); auto with coc.

intros.
apply trans_red with (Abs P v0); auto with coc.
Qed.


  Lemma red_red_prod :
   forall u u0 v v0, red u u0 -> red v v0 -> red (Prod u v) (Prod u0 v0).
simple induction 1.
simple induction 1; intros; auto with coc.
apply trans_red with (Prod u P); auto with coc.

intros.
apply trans_red with (Prod P v0); auto with coc.
Qed.

  Hint Resolve red_red_app red_red_abs red_red_prod: coc.



  Lemma red1_lift :
   forall n u v, red1 u v -> forall k, red1 (lift_rec n u k) (lift_rec n v k).
simple induction 1; simpl in |- *; intros; auto with coc.
rewrite distr_lift_subst; auto with coc.
Qed.

  Hint Resolve red1_lift: coc.


  Lemma red1_subst_r :
   forall a t u,
   red1 t u -> forall k, red1 (subst_rec a t k) (subst_rec a u k).
simple induction 1; simpl in |- *; intros; auto with coc.
rewrite distr_subst; auto with coc.
Qed.


  Lemma red1_subst_l :
   forall t u,
   red1 t u -> forall a k, red (subst_rec t a k) (subst_rec u a k).
simple induction a; simpl in |- *; auto with coc.
intros.
elim (lt_eq_lt_dec k n); intros; auto with coc.
elim a0; auto with coc.
unfold lift in |- *; auto with coc.
Qed.

  Hint Resolve red1_subst_l red1_subst_r: coc.


  Lemma red_prod_prod :
   forall u v t,
   red (Prod u v) t ->
   forall P : Prop,
   (forall a b, t = Prod a b -> red u a -> red v b -> P) -> P.
simple induction 1; intros.
apply H0 with u v; auto with coc.

apply H1; intros.
inversion_clear H4 in H2.
inversion H2.
apply H3 with N1 b; auto with coc.
apply trans_red with a; auto with coc.

apply H3 with a N2; auto with coc.
apply trans_red with b; auto with coc.
Qed.


  Lemma red_sort_sort : forall s t, red (Srt s) t -> t <> Srt s -> False.
simple induction 1; intros; auto with coc.
apply H1.
generalize H2.
case P; intros; try discriminate.
inversion_clear H4.
Qed.



  Lemma one_step_conv_exp : forall M N, red1 M N -> conv N M.
intros.
apply trans_conv_exp with N; auto with coc.
Qed.


  Lemma red_conv : forall M N, red M N -> conv M N.
simple induction 1; auto with coc.
intros; apply trans_conv_red with P; auto with coc.
Qed.

  Hint Resolve one_step_conv_exp red_conv: coc.


  Lemma sym_conv : forall M N, conv M N -> conv N M.
simple induction 1; auto with coc.
simple induction 2; intros; auto with coc.
apply trans_conv_red with P0; auto with coc.

apply trans_conv_exp with P0; auto with coc.

simple induction 2; intros; auto with coc.
apply trans_conv_red with P0; auto with coc.

apply trans_conv_exp with P0; auto with coc.
Qed.

  Hint Immediate sym_conv: coc.


  Lemma trans_conv_conv : forall M N P, conv M N -> conv N P -> conv M P.
intros.
generalize M H; elim H0; intros; auto with coc.
apply trans_conv_red with P0; auto with coc.

apply trans_conv_exp with P0; auto with coc.
Qed.


  Lemma conv_conv_prod :
   forall a b c d, conv a b -> conv c d -> conv (Prod a c) (Prod b d).
intros.
apply trans_conv_conv with (Prod a d).
elim H0; intros; auto with coc.
apply trans_conv_red with (Prod a P); auto with coc.

apply trans_conv_exp with (Prod a P); auto with coc.

elim H; intros; auto with coc.
apply trans_conv_red with (Prod P d); auto with coc.

apply trans_conv_exp with (Prod P d); auto with coc.
Qed.


  Lemma conv_conv_lift :
   forall a b n k, conv a b -> conv (lift_rec n a k) (lift_rec n b k).
intros.
elim H; intros; auto with coc.
apply trans_conv_red with (lift_rec n P k); auto with coc.

apply trans_conv_exp with (lift_rec n P k); auto with coc.
Qed.
 

  Lemma conv_conv_subst :
   forall a b c d k,
   conv a b -> conv c d -> conv (subst_rec a c k) (subst_rec b d k).
intros.
apply trans_conv_conv with (subst_rec a d k).
elim H0; intros; auto with coc.
apply trans_conv_red with (subst_rec a P k); auto with coc.

apply trans_conv_exp with (subst_rec a P k); auto with coc.

elim H; intros; auto with coc.
apply trans_conv_conv with (subst_rec P d k); auto with coc.

apply trans_conv_conv with (subst_rec P d k); auto with coc.
apply sym_conv; auto with coc.
Qed.

  Hint Resolve conv_conv_prod conv_conv_lift conv_conv_subst: coc.


  Lemma refl_par_red1 : forall M, par_red1 M M.
simple induction M; auto with coc.
Qed.

  Hint Resolve refl_par_red1: coc.


  Lemma red1_par_red1 : forall M N, red1 M N -> par_red1 M N.
simple induction 1; auto with coc; intros.
Qed.

  Hint Resolve red1_par_red1: coc.


  Lemma red_par_red : forall M N, red M N -> par_red M N.
red in |- *; simple induction 1; intros; auto with coc.
apply t_trans with P; auto with coc.
Qed.


  Lemma par_red_red : forall M N, par_red M N -> red M N.
simple induction 1.
simple induction 1; intros; auto with coc.
apply trans_red with (App (Abs T M') N'); auto with coc.

intros.
apply trans_red_red with y; auto with coc.
Qed.

  Hint Resolve red_par_red par_red_red: coc.


  Lemma par_red1_lift :
   forall n a b,
   par_red1 a b -> forall k, par_red1 (lift_rec n a k) (lift_rec n b k).
simple induction 1; simpl in |- *; auto with coc.
intros.
rewrite distr_lift_subst; auto with coc.
Qed.


  Lemma par_red1_subst :
   forall a b c d,
   par_red1 a b ->
   par_red1 c d -> forall k, par_red1 (subst_rec a c k) (subst_rec b d k).
simple induction 2; simpl in |- *; auto with coc; intros.
rewrite distr_subst; auto with coc.

elim (lt_eq_lt_dec k n); auto with coc; intros.
elim a0; intros; auto with coc.
unfold lift in |- *.
apply par_red1_lift; auto with coc.
Qed.


  Lemma inv_par_red_abs :
   forall (P : Prop) T U x,
   par_red1 (Abs T U) x ->
   (forall T' U', x = Abs T' U' -> par_red1 U U' -> P) -> P.
do 5 intro.
inversion_clear H; intros.
apply H with T' M'; auto with coc.
Qed.

  Hint Resolve par_red1_lift par_red1_subst: coc.



  Lemma mem_sort_lift :
   forall t n k s, mem_sort s (lift_rec n t k) -> mem_sort s t.
simple induction t; simpl in |- *; intros; auto with coc.
generalize H; elim (le_gt_dec k n); intros; auto with coc.
inversion_clear H0.

inversion_clear H1.
apply mem_abs_l; apply H with n k; auto with coc.

apply mem_abs_r; apply H0 with n (S k); auto with coc.

inversion_clear H1.
apply mem_app_l; apply H with n k; auto with coc.

apply mem_app_r; apply H0 with n k; auto with coc.

inversion_clear H1.
apply mem_prod_l; apply H with n k; auto with coc.

apply mem_prod_r; apply H0 with n (S k); auto with coc.
Qed.


  Lemma mem_sort_subst :
   forall b a n s,
   mem_sort s (subst_rec a b n) -> mem_sort s a \/ mem_sort s b.
simple induction b; simpl in |- *; intros; auto with coc.
generalize H; elim (lt_eq_lt_dec n0 n); intro.
elim a0; intros.
inversion_clear H0.

left.
apply mem_sort_lift with n0 0; auto with coc.

intros.
inversion_clear H0.

inversion_clear H1.
elim H with a n s; auto with coc.

elim H0 with a (S n) s; auto with coc.

inversion_clear H1.
elim H with a n s; auto with coc.

elim H0 with a n s; auto with coc.

inversion_clear H1.
elim H with a n s; auto with coc.

elim H0 with a (S n) s; intros; auto with coc.
Qed.


  Lemma red_sort_mem : forall t s, red t (Srt s) -> mem_sort s t.
intros.
pattern t in |- *.
apply red1_red_ind with (Srt s); auto with coc.
do 4 intro.
elim H0; intros.
elim mem_sort_subst with M0 N 0 s; intros; auto with coc.

inversion_clear H4; auto with coc.

inversion_clear H4; auto with coc.

inversion_clear H4; auto with coc.

inversion_clear H4; auto with coc.

inversion_clear H4; auto with coc.

inversion_clear H4; auto with coc.
Qed.



  Lemma red_normal : forall u v, red u v -> normal u -> u = v.
simple induction 1; auto with coc; intros.
absurd (red1 u N); auto with coc.
absurd (red1 P N); auto with coc.
elim (H1 H3).
unfold not in |- *; intro; apply (H3 N); auto with coc.
Qed.



  Lemma sn_red_sn : forall a b, sn a -> red a b -> sn b.
unfold sn in |- *.
simple induction 2; intros; auto with coc.
apply Acc_inv with P; auto with coc.
Qed.


  Lemma commut_red1_subterm : commut _ subterm (transp _ red1).
red in |- *.
simple induction 1; intros.
exists (Abs z B); auto with coc.

exists (Abs A z); auto with coc.

exists (App z B); auto with coc.

exists (App A z); auto with coc.

exists (Prod z B); auto with coc.

exists (Prod A z); auto with coc.
Qed.


  Lemma subterm_sn : forall a, sn a -> forall b, subterm b a -> sn b.
unfold sn in |- *.
simple induction 1; intros.
apply Acc_intro; intros.
elim commut_red1_subterm with x b y; intros; auto with coc.
apply H1 with x0; auto with coc.
Qed.


  Lemma sn_prod : forall A, sn A -> forall B, sn B -> sn (Prod A B).
unfold sn in |- *.
simple induction 1.
simple induction 3; intros.
apply Acc_intro; intros.
inversion_clear H5; auto with coc.
apply H1; auto with coc.
apply Acc_intro; auto with coc.
Qed.


  Lemma sn_subst : forall T M, sn (subst T M) -> sn M.
intros.
cut (forall t, sn t -> forall m, t = subst T m -> sn m).
intros.
apply H0 with (subst T M); auto with coc.

unfold sn in |- *.
simple induction 1; intros.
apply Acc_intro; intros.
apply H2 with (subst T y); auto with coc.
rewrite H3.
unfold subst in |- *; auto with coc.
Qed.
