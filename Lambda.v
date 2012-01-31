
Require Export Setoid Morphisms.
Require Import Arith.
Require Export Compare_dec.
Require Export Relations.

(* Lambda terms with constants *)


Hint Resolve t_step rt_step rt_refl: core.
Hint Unfold transp: core.

Section Terms.

  Inductive term : Set :=
    | Ref (_:nat)
    | Abs (body:term)
    | App (f arg:term).

  Fixpoint lift_rec (n : nat) (t : term) (k : nat) {struct t} : term :=
    match t with
    | Ref i =>
        match le_gt_dec k i with
        | left _ => Ref (n + i)
        | right _ => Ref i
        end
    | Abs M => Abs (lift_rec n M (S k))
    | App u v => App (lift_rec n u k) (lift_rec n v k)
    end.

  Definition lift n t := lift_rec n t 0.

  (* K: useful to encode computationaly irrelevant subterms *)
  Definition K := Abs (Abs (Ref 1)).
  Definition App2 f x y := App (App f x) y.

  Fixpoint subst_rec (N M : term) (k : nat) {struct M} : term :=
    match M with
    | Ref i =>
        match lt_eq_lt_dec k i with
        | inleft (left _) => Ref (pred i)
        | inleft (right _) => lift k N
        | inright _ => Ref i
        end
    | Abs B => Abs (subst_rec N B (S k))
    | App u v => App (subst_rec N u k) (subst_rec N v k)
    end.

  Definition subst N M := subst_rec N M 0.

  Inductive subterm : term -> term -> Prop :=
    | sbtrm_abs : forall B, subterm B (Abs B)
    | sbtrm_app_l : forall A B, subterm A (App A B)
    | sbtrm_app_r : forall A B, subterm B (App A B).

  Inductive occur (n:nat) : term -> Prop :=
  | occ_var : occur n (Ref n)
  | occ_app_l : forall A B, occur n A -> occur n (App A B)
  | occ_app_r : forall A B, occur n B -> occur n (App A B)
  | occ_abs : forall M, occur (S n) M -> occur n (Abs M).

End Terms.

  Hint Constructors subterm occur.

Section Beta_Reduction.

  Inductive red1 : term -> term -> Prop :=
    | beta : forall M N, red1 (App (Abs M) N) (subst N M)
    | abs_red : forall M M', red1 M M' -> red1 (Abs M) (Abs M')
    | app_red_l :
        forall M1 N1, red1 M1 N1 -> forall M2, red1 (App M1 M2) (App N1 M2)
    | app_red_r :
        forall M2 N2, red1 M2 N2 -> forall M1, red1 (App M1 M2) (App M1 N2).

  Inductive red (M : term) : term -> Prop :=
    | refl_red : red M M
    | trans_red : forall P N, red M P -> red1 P N -> red M N.

  Inductive conv (M : term) : term -> Prop :=
    | refl_conv : conv M M
    | trans_conv_red : forall P N, conv M P -> red1 P N -> conv M N
    | trans_conv_exp : forall P N, conv M P -> red1 N P -> conv M N.

  Definition redp := clos_trans _ red1.

End Beta_Reduction.

  Hint Constructors red red1 conv : coc.


Section StrongNormalisation.

  Definition normal t := forall u, ~ red1 t u.

  Definition sn := Acc (transp _ red1).

End StrongNormalisation.

  Hint Unfold sn: coc.

  Lemma eqterm : forall u v : term, {u = v} + {u <> v}.
Proof.
decide equality.
apply eq_nat_dec.
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

rewrite H; auto with coc.

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

rewrite H; simpl in |- *; auto with arith.

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

rewrite H; auto with arith.
rewrite plus_n_Sm; auto with arith.

rewrite H; auto with arith; rewrite H0; auto with arith.
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

rewrite H; auto with arith.
elim plus_n_Sm with n k; auto with arith.

rewrite H; auto with arith; rewrite H0; auto with arith.
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
rewrite H; auto with arith.

simpl in |- *; rewrite H; rewrite H0; auto with arith.
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
rewrite H; auto with arith.

simpl in |- *; rewrite H; rewrite H0; auto with arith.
Qed.


  Lemma distr_subst :
   forall P N M k,
   subst_rec P (subst N M) k = subst (subst_rec P N k) (subst_rec P M (S k)).
intros; unfold subst in |- *.
pattern k at 1 3 in |- *.
replace k with (0 + k); auto with arith.
apply distr_subst_rec.
Qed.


  Lemma occur_subst : forall k t,
   occur k t <->
   lift_rec 1 (subst_rec (Abs (Ref 0)) t k) k <> t.
split; intros.
 induction H; simpl; intros.
  destruct (lt_eq_lt_dec n n) as [[?|_]|?].
   elim (Lt.lt_irrefl n); trivial.

   discriminate.

   elim (Lt.lt_irrefl n); trivial.

  red; intros.
  injection H0; clear H0; intros; auto.

  red; intros. 
  injection H0; clear H0; intros; auto.

  red; intros.
  injection H0; clear H0; intros; auto.

 revert k H; induction t; simpl; intros.
  destruct (lt_eq_lt_dec k n) as [[?|?]|?]; simpl in H.
   destruct (le_gt_dec k (Peano.pred n)); simpl in *.
    elim H.
    destruct n; simpl; trivial.
    inversion l.

    apply NPeano.Nat.lt_pred_le in g.
    elim (Lt.lt_irrefl n).
    apply Lt.le_lt_trans with k; trivial.

   subst k; auto.

   destruct (le_gt_dec k n).
    elim (Lt.lt_irrefl n).
    apply Lt.lt_le_trans with k; trivial.

    elim H; trivial.

  constructor; apply IHt.
  red; intros; apply H.
  rewrite H0; trivial.

  destruct (eqterm (lift_rec 1 (subst_rec (Abs (Ref 0)) t1 k) k) t1).
   apply occ_app_r.
   apply IHt2.
   red; intros; apply H.
   rewrite e; rewrite H0; trivial.

   apply occ_app_l; auto.
Qed.


(***********************************************************************)
(* One step reduction *)

  Lemma red1_beta : forall M N T,
    T = subst N M -> red1 (App (Abs M) N) T.
intros.
subst T.
constructor.
Qed.

  Lemma red1_lift :
   forall n u v, red1 u v -> forall k, red1 (lift_rec n u k) (lift_rec n v k).
simple induction 1; simpl in |- *; intros; auto with coc.
rewrite distr_lift_subst; auto with coc.
Qed.

  Lemma red1_subst_r :
   forall a t u,
   red1 t u -> forall k, red1 (subst_rec a t k) (subst_rec a u k).
simple induction 1; simpl in |- *; intros; auto with coc.
rewrite distr_subst; auto with coc.
Qed.
  Hint Resolve red1_lift red1_subst_r : coc.

(* Reflexive transitive closure *)

  Instance red_refl : Reflexive red.
red; auto with coc.
Qed.

  Instance red_trans : Transitive red.
red.
induction 2; trivial.
apply trans_red with P; trivial.
Qed.

  Lemma one_step_red : forall M N, red1 M N -> red M N.
intros.
apply trans_red with M; auto with coc.
Qed.
  Hint Resolve one_step_red: coc.

  Instance app_red_morph : Proper (red ==> red ==> red) App.
do 3 red; induction 1; intros.
 induction H; intros; auto with coc.
 transitivity (App x P); auto with coc.

 transitivity (App P y); auto with coc.
Qed.

  Lemma red_red_app :
    forall u u0, red u u0 ->
    forall v v0, red v v0 ->
    red (App u v) (App u0 v0).
Proof app_red_morph.
Hint Resolve red_red_app : coc.

  Instance abs_red_morph : Proper (red ==> red) Abs.
do 2 red; induction 1; intros; auto with coc.
transitivity (Abs P); auto with coc.
Qed.

  Lemma red_red_abs :
    forall u u0, red u u0 -> red (Abs u) (Abs u0).
Proof abs_red_morph.
Hint Resolve red_red_abs : coc.

  Lemma red1_subst_l :
   forall t u,
   red1 t u -> forall a k, red (subst_rec t a k) (subst_rec u a k).
simple induction a; simpl in |- *; auto with coc.
intros.
elim (lt_eq_lt_dec k n); intros; auto with coc.
elim a0; auto with coc.
unfold lift in |- *; auto with coc.
Qed.
  Hint Resolve red1_subst_l: coc.

(* Conversion *)

  Lemma red_conv : forall M N, red M N -> conv M N.
induction 1; auto with coc.
intros; apply trans_conv_red with P; auto with coc.
Qed.
Hint Resolve red_conv: coc.

  Lemma trans_conv_conv : forall M N P, conv M N -> conv N P -> conv M P.
intros.
generalize M H; elim H0; intros; auto with coc.
apply trans_conv_red with P0; auto with coc.

apply trans_conv_exp with P0; auto with coc.
Qed.

  Instance conv_refl : Equivalence conv.
split.
 constructor.

 red; induction 1; intros; auto with coc.
  apply trans_conv_conv with P; auto with coc.
  apply trans_conv_exp with N; auto with coc.

  apply trans_conv_conv with P; auto with coc.

 exact trans_conv_conv.
Qed.

  Lemma red_sym_conv : forall M N, red M N -> conv N M.
intros; symmetry; auto with coc.
Qed.
  Hint Resolve red_sym_conv : coc.


  Instance conv_conv_app : Proper (conv ==> conv ==> conv) App.
do 3 red; intros.
transitivity (App y x0).
 induction H; intros; auto with *.
  constructor 2 with (App P x0); auto with *.
  constructor 3 with (App P x0); auto with *.

 induction H0; intros; auto with *.
  constructor 2 with (App y P); auto with *.
  constructor 3 with (App y P); auto with *.
Qed.

  Instance conv_conv_abs : Proper (conv ==> conv) Abs. 
do 2 red; intros.
induction H; intros; auto with *.
 constructor 2 with (Abs P); auto with *.
 constructor 3 with (Abs P); auto with *.
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
transitivity (subst_rec a d k).
 elim H0; intros; auto with coc.
  transitivity (subst_rec a P k); auto with coc.

  transitivity (subst_rec a P k); auto with coc.

 elim H; intros; auto with coc.
  transitivity (subst_rec P d k); auto with coc.

  transitivity (subst_rec P d k); auto with coc.
Qed.

(* One or more steps *)

  Lemma redp_lift_rec : forall n M M',
    redp M M' -> forall k, redp (lift_rec n M k) (lift_rec n M' k).
unfold redp.
induction 1; intros.
 apply t_step; auto with coc.
 apply t_trans with (lift_rec n y k); trivial.
Qed.

  Lemma redp_abs : forall M M', redp M M' -> redp (Abs M) (Abs M').
induction 1.
 apply t_step; apply abs_red; trivial.
 apply t_trans with (Abs y); trivial.
Qed.

  Lemma redp_app_l :
    forall M1 N1 M2, redp M1 N1 -> redp (App M1 M2) (App N1 M2).
induction 1.
 apply t_step; apply app_red_l; trivial.
 apply t_trans with (App y M2); trivial.
Qed.

  Lemma redp_app_r :
    forall M1 M2 N2, redp M2 N2 -> redp (App M1 M2) (App M1 N2).
induction 1.
 apply t_step; apply app_red_r; trivial.
 apply t_trans with (App M1 y); trivial.
Qed.

  Hint Resolve redp_abs redp_app_l redp_app_r : coc.

  Lemma redp_K : forall M T, redp (App2 K M T) M.
unfold K; intros.
apply t_trans with (App (Abs (lift 1 M)) T); apply t_step.
 apply app_red_l.
 apply red1_beta.
 reflexivity.

 apply red1_beta.
 unfold subst; rewrite simpl_subst; auto.
 symmetry; apply lift0.
Qed.


  Lemma red_lift_inv : forall n t u,
    red1 t u ->
    forall k t',
    t = lift_rec n t' k ->
    exists2 u',
      red1 t' u' & u = lift_rec n u' k.
induction 1; intros.
 destruct t'; try discriminate H.
  simpl in H.
  destruct (le_gt_dec k n0); discriminate H.

  destruct t'1; try discriminate H.
   simpl in H.
   destruct (le_gt_dec k n0); discriminate H.

   exists (subst t'2 t'1); auto with *.
   simpl in H.
   injection H; clear H; intros.
   subst.
   rewrite distr_lift_subst; trivial.

 destruct t'; try discriminate H0.
  simpl in H0.
  destruct (le_gt_dec k n0); discriminate H0.

  simpl in H0; injection H0; clear H0; intro.
  apply IHred1 in H0.
  destruct H0; subst M'.
  exists (Abs x); auto with *.

 destruct t'; try discriminate H0.
  simpl in H0.
  destruct (le_gt_dec k n0); discriminate H0.

  simpl in H0; injection H0; clear H0; intros.
  apply IHred1 in H1.
  destruct H1; subst M2 N1.
  exists (App x t'2); auto with *.

 destruct t'; try discriminate H0.
  simpl in H0.
  destruct (le_gt_dec k n0); discriminate H0.

  simpl in H0; injection H0; clear H0; intros.
  apply IHred1 in H0.
  destruct H0; subst M1 N2.
  exists (App t'1 x); auto with *.
Qed.


  Lemma commut_red1_subterm : commut _ subterm (transp _ red1).
red in |- *.
simple induction 1; intros.
exists (Abs z); auto with coc.

exists (App z B); auto with coc.

exists (App A z); auto with coc.
Qed.

  Lemma subterm_sn : forall a, sn a -> forall b, subterm b a -> sn b.
unfold sn in |- *.
simple induction 1; intros.
apply Acc_intro; intros.
elim commut_red1_subterm with x b y; intros; auto with coc.
apply H1 with x0; auto with coc.
Qed.

  Lemma sn_red_sn : forall x y, sn x -> red x y -> sn y.
unfold sn; intros.
revert H.
induction H0; intros; auto.
apply Acc_inv with P; auto with *.
Qed.

  Lemma sn_var : forall n, sn (Ref n).
constructor; intros.
inversion H.
Qed.

  Lemma sn_abs : forall M, sn M -> sn (Abs M).
unfold sn in |- *.
induction 1; intros.
apply Acc_intro; intros.
inversion_clear H1; auto with coc.
Qed.

  Lemma sn_K : sn K.
apply Acc_intro; intros.
inversion_clear H.
inversion_clear H0.
inversion_clear H.
Qed.


Lemma sn_lift : forall n t k,
  sn t -> sn (lift_rec n t k).
induction 1; intros.
constructor; intros.
red in H1.
apply red_lift_inv with (2:=eq_refl _) in H1.
destruct H1; subst y; auto with coc.
apply H0; trivial.
Qed.


  Lemma sn_K2_reduced1 :
    forall A, sn A ->
    forall B, sn B ->
    sn (App (Abs (lift 1 A)) B).
unfold sn in |- *.
induction 1.
induction 1; intros.
apply Acc_intro; intros.
inversion_clear H3.
 unfold subst; rewrite simpl_subst; simpl; auto with arith; rewrite lift0.
 apply Acc_intro; trivial.

 inversion_clear H4.
 destruct red_lift_inv with (1:=H3) (2:=eq_refl (lift 1 x)).
 subst M'.
 apply H0; auto.
 apply Acc_intro; trivial.

 apply H2; auto.
Qed.

  Lemma sn_K2 :
    forall A, sn A ->
    forall B, sn B ->
    sn (App2 K A B).
unfold sn in |- *.
induction 1.
induction 1; intros.
apply Acc_intro; intros.
inversion_clear H3.
 inversion_clear H4; trivial.
  unfold subst; simpl.
  apply sn_K2_reduced1; constructor; trivial.

  inversion_clear H3.
  inversion_clear H4.
  inversion_clear H3.

  apply H0; auto.
  constructor; trivial.

 apply H2; auto.
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

Hint Resolve sn_abs sn_var sn_lift.

(* Normalization function *)

Definition neutral t :=
  match t with
  | Abs _ => False
  | _ => True
  end.

Inductive nf : term -> Prop :=
| Nf_var : forall n, nf (Ref n)
| Nf_app : forall u v, neutral u -> nf u -> nf v -> nf (App u v)
| Nf_abs : forall t, nf t -> nf (Abs t).

Hint Constructors nf.

Lemma nf_norm : forall t, nf t -> forall u, ~ red1 t u.
red; intros.
revert H.
induction H0; simpl; intros; auto.
 inversion_clear H.
 elim H0.

 inversion_clear H; auto.

 inversion_clear H; auto.

 inversion_clear H; auto.
Qed.

Lemma nf_neutral_open : forall t,
  nf t ->
  neutral t ->
  exists k, occur k t.
induction 1; intros.
 exists n; auto with coc.

 destruct (IHnf1 H).
 exists x; apply occ_app_l; trivial.

 destruct H0.
Qed.

Lemma lift_closed : forall m M n k,
  k <= n ->
  occur n (lift_rec m M k) ->
  m+k <= n /\ occur (n-m) M.
induction M; simpl; intros.
 destruct (le_gt_dec k n).
  inversion_clear H0.
  split; auto with arith.
  replace (m+n-m) with n; auto with arith.

  inversion H0; subst n0.
  elim (Lt.lt_irrefl n); apply Lt.lt_le_trans with k; trivial.

 inversion_clear H0.
 apply IHM in H1; auto with arith.
 destruct H1.
 rewrite <- plus_n_Sm in H0.
 split; auto with arith.
 constructor.
 rewrite <- NPeano.Nat.sub_succ_l; trivial.
 apply Le.le_trans with (m+k); auto with arith.

 inversion_clear H0.
  apply IHM1 in H1; destruct H1; auto with *.
  apply IHM2 in H1; destruct H1; auto with *.
Qed.

Lemma subst_closed : forall N M n k,
  k <= n ->
  occur n (subst_rec N M k) ->
  occur (n-k) N \/ occur (S n) M.
induction M; simpl; intros.
 destruct (lt_eq_lt_dec k n) as [[?|?]|?].
  inversion H0; subst n0.
  right.
  destruct n; simpl; auto with *.
  inversion l.

  left.
  apply lift_closed with (k:=0); auto with arith.

  inversion H0; subst n0.
  elim (Lt.lt_irrefl n); apply Lt.lt_le_trans with k; trivial.

 inversion_clear H0.
 apply IHM in H1.
 destruct H1; auto with *.
 apply Le.le_n_S; trivial.

 inversion_clear H0.
  apply IHM1 in H1; trivial.
  destruct H1; auto.

  apply IHM2 in H1; trivial.
  destruct H1; auto.
Qed.


Lemma red_closed : forall t t',
  red t t' ->
  forall k,
  occur k t' ->
  occur k t.
induction 1; intros; auto.
apply IHred.
revert k H1; clear H IHred t.
induction H0.
 intros.
 destruct subst_closed with (2:=H1); auto with arith.
 replace (k-0) with k in H; auto with *.

 intros.
 inversion_clear H1; apply occ_abs; auto.

 intros.
 inversion_clear H1.
  apply occ_app_l; auto.
  apply occ_app_r; trivial.

 intros.
 inversion_clear H1.
  apply occ_app_l; trivial.
  apply occ_app_r; auto.
Qed.


Lemma red1_dec : forall t, {u|red1 t u}+{nf t}.
induction t; intros.
 right; simpl; trivial.

 destruct IHt.
  destruct s.
  left; exists (Abs x); auto with coc.

  right; simpl; auto.

 destruct IHt1.
  destruct s.
  left; exists (App x t2); auto with coc.

  destruct IHt2.
   destruct s.
   left; exists (App t1 x); auto with coc.

   destruct t1;[right;simpl;auto|left|right;simpl;auto].
repeat constructor; trivial.
   exists (subst t2 t1); auto with coc.
constructor; trivial.
simpl; trivial.
Qed.

Lemma norm : forall t, sn t -> { u | red t u /\ nf u}.
induction 1; intros.
destruct (red1_dec x).
 destruct s.
 destruct (H0 x0); trivial.
 destruct a.
 exists x1; split; trivial.
 transitivity x0; auto with coc.

 exists x; auto with coc.
Qed.

(* Confluence *)

  Theorem church_rosser :
   forall u v, conv u v -> exists2 t, red u t & red v t.
Admitted.

  Theorem confluence :
   forall m u v, red m u -> red m v -> exists2 t, red u t & red v t.
intros.
apply church_rosser.
transitivity m; auto with coc.
Qed.

(* Term-interpretation *)
Require VarMap.

Module LCeq.
  Definition t := term.
  Definition eq := @Logic.eq term.
  Definition eq_equiv : Equivalence eq := eq_equivalence.
End LCeq.
Module I := VarMap.Make(LCeq).

Notation intt := I.map.
Notation eq_intt := I.eq_map.

Import I.
Existing Instance cons_morph.
Existing Instance cons_morph'.
Existing Instance shift_morph.
Existing Instance lams_morph.

Definition ilift (j:intt) : intt :=
  fun k => match k with
  | 0 => Ref 0
  | S n => lift 1 (j n)
  end.

Instance ilift_morph : Proper (eq_intt ==> eq_intt) ilift.
do 4 red; intros.
unfold ilift.
destruct a; simpl; auto.
rewrite H; trivial.
Qed.

Lemma ilift_lams : forall k f j,
  (forall j j', (forall a, lift 1 (j a) = j' a) ->
   forall a, lift 1 (f j a) = f j' a) ->
  eq_intt (ilift (I.lams k f j)) (I.lams (S k) f (ilift j)).
intros.
do 2 red; intros.
destruct a; simpl.
 reflexivity.

 unfold I.lams; simpl.
 destruct (le_gt_dec k a); simpl; trivial.
 apply H.
 unfold I.shift, ilift; simpl; intros; trivial.
Qed.

Lemma ilift_binder : forall u j k,
  eq_intt
    (ilift (fun n => subst_rec u (j n) k))
    (fun n => subst_rec u (ilift j n) (S k)).
red; red; intros.
destruct a; simpl; trivial.
rewrite commut_lift_subst; trivial.
Qed.

Lemma ilift_binder_lift : forall j k,
  eq_intt
    (ilift (fun n => lift_rec 1 (j n) k))
    (fun n => lift_rec 1 (ilift j n) (S k)).
red; red; intros.
destruct a; simpl; trivial.
rewrite permute_lift; trivial.
Qed.

Lemma cross_binder_cons k x y i :
  lift 1 x = y ->
  eq_intt (ilift (I.lams k (I.cons x) i)) (I.lams (S k) (I.cons y) (ilift i)).
do 2 red; intros.
destruct a; simpl.
 reflexivity.

 unfold I.lams; simpl.
 destruct (le_gt_dec k a); simpl; trivial.
 destruct (a - k); simpl; trivial.
Qed.

Lemma cross_binder_shift n k i :
  eq_intt (ilift (I.lams k (I.shift n) i)) (I.lams (S k) (I.shift n) (ilift i)).
do 2 red; intros.
destruct a; simpl.
 reflexivity.

 unfold I.lams; simpl.
 destruct (le_gt_dec k a); simpl; trivial.
Qed.

(* Substitutivity property *)

Definition substitutive (t:intt->term) :=
  forall u j k,
  t (fun n => subst_rec u (j n) k) = subst_rec u (t j) k.
Definition liftable (t:intt->term) :=
  forall j k,
  t (fun n => lift_rec 1 (j n) k) = lift_rec 1 (t j) k.
