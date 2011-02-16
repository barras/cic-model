Require Import Le.
Require Import Gt.
Require Export List.

Set Implicit Arguments.
Unset Strict Implicit.

Section Listes.

  Variable A : Set.

  Let List := list A.


  Inductive item (x : A) : List -> nat -> Prop :=
    | item_hd : forall l, item x (x :: l) 0
    | item_tl : forall l n y, item x l n -> item x (y :: l) (S n).

  Lemma fun_item : forall u v e n, item u e n -> item v e n -> u = v.
simple induction 1; intros.
inversion_clear H0; auto.

inversion_clear H2; auto.
Qed.


  Fixpoint nth_def (d : A) (l : List) (n : nat) {struct l} : A :=
    match l, n with
    | nil, _ => d
    | x :: _, O => x
    | _ :: tl, S k => nth_def d tl k
    end.

  Lemma nth_sound : forall x l n d, item x l n -> nth_def d l n = x.
simple induction 1; simpl in |- *; auto.
Qed.

  Lemma inv_nth_nl : forall x n, ~ item x nil n.
unfold not in |- *; intros.
inversion_clear H.
Qed.

  Lemma inv_nth_cs : forall x y l n, item x (y :: l) (S n) -> item x l n.
intros.
inversion_clear H; auto.
Qed.

  Inductive insert (x : A) : nat -> List -> List -> Prop :=
    | insert_hd : forall l, insert x 0 l (x :: l)
    | insert_tl :
        forall n l il y, insert x n l il -> insert x (S n) (y :: l) (y :: il).


  Inductive trunc : nat -> List -> List -> Prop :=
    | trunc_O : forall e, trunc 0 e e
    | trunc_S : forall k e f x, trunc k e f -> trunc (S k) (x :: e) f.

  Hint Constructors trunc: core.


  Lemma item_trunc :
   forall n e t, item t e n -> exists f : _, trunc (S n) e f.
simple induction n; intros.
inversion_clear H.
exists l; auto.

inversion_clear H0.
elim H with l t; intros; auto.
exists x; auto.
Qed.


  Lemma ins_le :
   forall k f g d x,
   insert x k f g -> forall n, k <= n -> nth_def d f n = nth_def d g (S n).
simple induction 1; auto.
simple destruct n0; intros.
inversion_clear H2.

simpl in |- *; auto with arith.
Qed.

  Lemma ins_gt :
   forall k f g d x,
   insert x k f g -> forall n, k > n -> nth_def d f n = nth_def d g n.
simple induction 1; auto.
intros.
inversion_clear H0.

simple destruct n0; intros.
auto.

simpl in |- *; auto with arith.
Qed.

  Lemma ins_eq : forall k f g d x, insert x k f g -> nth_def d g k = x.
simple induction 1; simpl in |- *; auto.
Qed.




  Lemma list_item :
   forall e n, {t : _ | item t e n} + {forall t, ~ item t e n}.
fix itemrec 1.
intros e n.
case e; [ idtac | intros h f ].
right.
red in |- *; intros.
inversion_clear H.

case n; [ idtac | intros k ].
left.
exists h.
apply item_hd.

elim (itemrec f k).
intros (t, itm_t).
left; exists t.
apply item_tl; auto.

intros not_itm.
right; red in |- *; intros.
elim not_itm with t.
inversion H; trivial.
Defined.

End Listes.

  Hint Constructors item: core.
  Hint Constructors insert: core.
  Hint Constructors trunc: core.

  Fixpoint map (A B : Set) (f : A -> B) (l : list A) {struct l} : list B :=
    match l with
    | nil => nil (A:=B)
    | x :: t => f x :: map f t
    end.


