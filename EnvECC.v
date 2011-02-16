Require Export Omega.
Require Export MyList.
Require Export TermECC.

  Definition env := list term.

  Definition item_lift t e n :=
    exists2 u, t = lift (S n) u & item u (e:env) n.

(* Thinning *)

  Inductive ins_in_env (A : term) : nat -> env -> env -> Prop :=
    | ins_O : forall e, ins_in_env A 0 e (A :: e)
    | ins_S :
        forall n e f t,
        ins_in_env A n e f ->
        ins_in_env A (S n) (t :: e) (lift_rec 1 t n :: f).

  Hint Resolve ins_O ins_S: coc.

  Lemma ins_item_ge :
   forall A n e f,
   ins_in_env A n e f -> forall v t, n <= v -> item t e v -> item t f (S v).
simple induction 1; auto with coc.
simple destruct v; intros.
inversion_clear H2.

inversion_clear H3; auto with arith coc.
Qed.

  Lemma ins_item_lift_ge :
   forall A n e f,
   ins_in_env A n e f -> forall v t, n <= v ->
   item_lift t e v -> item_lift (lift_rec 1 t n) f (S v).
intros.
destruct H1.
 subst t.
unfold lift in |- *;  rewrite simpl_lift_rec; try  omega.
exists x; trivial.
apply ins_item_ge with (1 := H) (2 := H0) (3 := H2).
Qed.

  Lemma ins_item_lt :
   forall A n e f,
   ins_in_env A n e f ->
   forall v t, n > v -> item t e v -> item (lift_rec 1 t (n-S v)) f v.
induction 1; intros.
 inversion H.
 inversion H1.
   replace (S n - 1) with n; auto with coc.
    auto with arith.
  simpl in |- *.
    constructor.
    apply IHins_in_env; auto.
     omega.
Qed.

  Lemma ins_item_lift_lt :
   forall A n e f,
   ins_in_env A n e f ->
   forall v t, n > v -> item_lift t e v -> item_lift (lift_rec 1 t n) f v.
intros.
destruct H1.
specialize ins_item_lt with (1 := H) (2 := H0) (3 := H2); intro.
 rewrite H1.
exists (lift_rec 1 x (n - S v)); trivial.
unfold lift in |- *.
pattern n at 1 in |- *.
 replace n with (S v + (n - S v)); auto with arith.
 rewrite <- permute_lift_rec; auto with arith.
Qed.

(* Substitution *)

  Inductive sub_in_env (t T : term) : nat -> env -> env -> Prop :=
    | sub_O : forall e : env, sub_in_env t T 0 (T :: e) e
    | sub_S :
        forall e f n u,
        sub_in_env t T n e f ->
        sub_in_env t T (S n) (u :: e) (subst_rec t u n :: f).

  Hint Resolve sub_O sub_S: coc.

  Lemma nth_sub_sup :
   forall t T n e f,
   sub_in_env t T n e f -> forall v u, n <= v -> item u e (S v) -> item u f v.
simple induction 1.
intros.
inversion_clear H1; trivial.

simple destruct v; intros.
inversion_clear H2.

inversion_clear H3; auto with arith coc.
Qed.

  Lemma nth_sub_eq : forall t T n e f, sub_in_env t T n e f -> item T e n.
simple induction 1; auto with coc.
Qed.

  Lemma sub_item_lift_sup :
   forall t T n e f,
   sub_in_env t T n e f -> forall v u, n < v ->
   item_lift u e v -> item_lift (subst_rec t u n) f (pred v).
Proof.
intros.
destruct v.
 inversion H0.
 destruct H1.
    subst u.
    rewrite simpl_subst; auto with arith.
   exists x; trivial.
   apply nth_sub_sup with (1 := H) (3 := H2); auto with arith.
Qed.

  Lemma sub_item_lift_eq : forall t T n e f x,
    sub_in_env t T n e f -> item_lift x e n -> subst_rec t x n = lift n T.
intros.
destruct H0.
 subst x.
 rewrite simpl_subst; auto with arith.
 replace x0 with T; trivial.
apply fun_item with (2 := H1).
apply nth_sub_eq with (1 := H).
Qed.

  Lemma nth_sub_inf :
   forall t T n e f,
   sub_in_env t T n e f ->
   forall v u, n > v -> item_lift u e v -> item_lift (subst_rec t u n) f v.
simple induction 1.
intros.
inversion_clear H0.

simple destruct v; intros.
elim H3; intros.
rewrite H4.
inversion_clear H5.
exists (subst_rec t u n0); auto with coc.
apply commut_lift_subst; auto with coc.

elim H3; intros.
rewrite H4.
inversion_clear H5.
elim H1 with n1 (lift (S n1) x); intros; auto with arith.
exists x0; auto with coc.
rewrite simpl_lift; auto with coc.
pattern (lift (S (S n1)) x0) in |- *.
rewrite simpl_lift; auto with coc.
elim H5.
change
  (subst_rec t (lift 1 (lift (S n1) x)) (S n0) =
   lift 1 (subst_rec t (lift (S n1) x) n0)) in |- *.
apply commut_lift_subst; auto with coc.

exists x; auto with coc.
Qed.


(* Reduction *)
(*
  Inductive red1_in_env : env -> env -> Prop :=
    | red1_env_hd : forall e t u, red1 t u -> red1_in_env (t :: e) (u :: e)
    | red1_env_tl :
        forall e f t, red1_in_env e f -> red1_in_env (t :: e) (t :: f).

  Hint Constructors red1_in_env: coc.

  Lemma red_item :
   forall n t e f,
   item_lift t e n ->
   red1_in_env e f ->
   item_lift t f n \/
   (forall g, trunc (S n) e g -> trunc (S n) f g) /\
   (exists2 u, red1 t u & item_lift u f n).
simple induction n.
do 4 intro.
elim H.
do 3 intro.
rewrite H0.
inversion_clear H1.
intros.
inversion_clear H1.
right.
split; intros.
inversion_clear H1; auto with coc.

exists (lift 1 u).
unfold lift in |- *; auto with coc.

exists u; auto with coc.

left.
exists x; auto with coc.

do 6 intro.
elim H0.
do 3 intro.
rewrite H1.
inversion_clear H2.
intros.
inversion_clear H2.
left.
exists x; auto with coc.

elim H with (lift (S n0) x) l f0; auto with coc; intros.
left.
elim H2; intros.
exists x0; auto with coc.
rewrite simpl_lift.
pattern (lift (S (S n0)) x0) in |- *.
rewrite simpl_lift.
elim H5; auto with coc.

right.
elim H2.
simple induction 2; intros.
split; intros.
inversion_clear H9; auto with coc.

elim H8; intros.
exists (lift (S (S n0)) x1).
rewrite simpl_lift.
pattern (lift (S (S n0)) x1) in |- *.
rewrite simpl_lift.
elim H9; unfold lift at 1 3 in |- *; auto with coc.

exists x1; auto with coc.

exists x; auto with coc.
Qed.
*)

Section Reduction.

  Variable R : term -> term -> Prop.

  Variable R_lift :
    forall x y n k, R x y -> R (lift_rec n x k) (lift_rec n y k).

  Inductive red1_in_env : env -> env -> Prop :=
    | red1_env_hd : forall e t u, R t u -> red1_in_env (t :: e) (u :: e)
    | red1_env_tl :
        forall e f t, red1_in_env e f -> red1_in_env (t :: e) (t :: f).

  Hint Constructors red1_in_env: coc.

  Lemma red_item :
   forall n t e f,
   item_lift t e n ->
   red1_in_env e f ->
   item_lift t f n \/
   (forall g, trunc (S n) e g -> trunc (S n) f g) /\
   (exists2 u, R t u & item_lift u f n).
simple induction n.
do 4 intro.
elim H.
do 3 intro.
rewrite H0.
inversion_clear H1.
intros.
inversion_clear H1.
right.
split; intros.
inversion_clear H1; auto with coc.

exists (lift 1 u).
unfold lift in |- *; auto with coc.

exists u; auto with coc.

left.
exists x; auto with coc.

do 6 intro.
elim H0.
do 3 intro.
rewrite H1.
inversion_clear H2.
intros.
inversion_clear H2.
left.
exists x; auto with coc.

elim H with (lift (S n0) x) l f0; auto with coc; intros.
left.
elim H2; intros.
exists x0; auto with coc.
rewrite simpl_lift.
pattern (lift (S (S n0)) x0) in |- *.
rewrite simpl_lift.
elim H5; auto with coc.

right.
elim H2.
simple induction 2; intros.
split; intros.
inversion_clear H9; auto with coc.

elim H8; intros.
exists (lift (S (S n0)) x1).
rewrite simpl_lift.
pattern (lift (S (S n0)) x1) in |- *.
rewrite simpl_lift.
elim H9; unfold lift at 1 3 in |- *; auto with coc.

exists x1; auto with coc.

exists x; auto with coc.
Qed.

End Reduction.

  Hint Constructors ins_in_env: coc.
  Hint Constructors sub_in_env: coc.
  Hint Constructors red1_in_env: coc.
