Require Import Models.

Module Type Judge.
    Parameter sub : Type.
  Module T.
    Parameter term : Type.
    Parameter eq_term : term -> term -> Prop.
    Parameter prop kind : term.
    Parameter Ref : nat -> term.
    Parameter App Abs Prod : term -> term -> term.

    Parameter eq_sub : sub -> sub -> Prop.
    Parameter sub_id : sub.
    Parameter sub_comp : sub -> sub -> sub.
    Parameter sub_lift : nat -> sub -> sub.
    Parameter sub_shift : nat -> sub.
    Parameter sub_cons : term -> sub -> sub.

    Parameter Sub : term -> sub -> term.

    Parameter lift : nat -> term -> term.
    Parameter lift1 : nat -> term -> term.
    Parameter subst : term -> term -> term.
  End T.
  Import T.

  Definition env : Type := list term.

  Module J.
    Parameter typ eq_typ sub_typ : env -> term -> term -> Prop.
    Parameter typ_sub : env -> sub -> env -> Prop.
  End J.
  Import J.

  Module R.
    (** Equivalence and congruence rules *)
    Parameter refl : forall e M, eq_typ e M M.
    Parameter sym : forall e M M', eq_typ e M M' -> eq_typ e M' M. 
    Parameter trans : forall e M M' M'',
      eq_typ e M M' -> eq_typ e M' M'' -> eq_typ e M M''.

    Parameter eq_typ_app : forall e M M' N N',
      eq_typ e M M' ->
      eq_typ e N N' ->
      eq_typ e (App M N) (App M' N').

    Parameter eq_typ_abs : forall e T T' M M',
      eq_typ e T T' ->
      eq_typ (T::e) M M' ->
      eq_typ e (Abs T M) (Abs T' M').

    Parameter eq_typ_prod : forall e T T' U U',
      eq_typ e T T' ->
      eq_typ (T::e) U U' ->
      eq_typ e (Prod T U) (Prod T' U').

    Parameter eq_typ_beta : forall e T M M' N N',
      eq_typ (T::e) M M' ->
      eq_typ e N N' ->
      typ e N T -> (* Typed reduction! *)
      T <> kind ->
      eq_typ e (App (Abs T M) N) (subst N' M').


    (** Typing rules *)
    Parameter typ_prop : forall e, typ e prop kind.

    Parameter typ_var : forall e n T,
      nth_error e n = value T ->
      typ e (Ref n) (lift (S n) T).

    Parameter typ_app : forall e u v V Ur,
      typ e v V ->
      typ e u (Prod V Ur) ->
      V <> kind ->
      typ e (App u v) (subst v Ur).

    Parameter typ_abs : forall e T M U,
      typ (T :: e) M U ->
      U <> kind ->
      typ e (Abs T M) (Prod T U).

    Parameter typ_prod : forall e T U s2,
      s2 = kind \/ s2 = prop ->
      typ (T :: e) U s2 ->
      typ e (Prod T U) s2.

    Parameter typ_conv : forall e M T T',
      typ e M T ->
      eq_typ e T T' ->
      T <> kind ->
      typ e M T'.


    (** Subtyping *)
    Parameter sub_refl : forall e M M',
      eq_typ e M M' -> sub_typ e M M'.

    Parameter sub_trans : forall e M1 M2 M3,
      sub_typ e M1 M2 -> sub_typ e M2 M3 -> sub_typ e M1 M3.

    Parameter typ_subsumption : forall e M T T',
      typ e M T ->
      sub_typ e T T' ->
      T <> kind ->
      typ e M T'.


    (** Substitution *)
    Parameter typ_sub_comp : forall e f g s1 s2,
      typ_sub e s1 f ->
      typ_sub f s2 g ->
      typ_sub e (sub_comp s2 s1) g.

    Parameter typ_Sub : forall e f s m u,
      typ f m u ->
      typ_sub e s f ->
      typ e (Sub m s) (Sub u s).

    Parameter typ_sub_shift1 : forall e ty,
      typ_sub (ty::e) (sub_shift 1) e.

    Parameter typ_sub_lams1 : forall e s f t,
      typ_sub e s f ->
      typ_sub (Sub t s :: e) (sub_lift 1 s) (t::f).

    (** Admissible rules *)
    (* TODO: weakening is an instance of typ_Sub *)
    Parameter weakening : forall e M T A,
      typ e M T ->
      typ (A::e) (lift 1 M) (lift 1 T).

  End R.

End Judge.

Module Type ECC_Rules (M:Judge).
  Import M M.T M.J.

  Parameter type : nat -> term.

  Parameter typ_Prop : forall e, typ e prop (type 0).

  Parameter typ_Type : forall e n, typ e (type n) (type (S n)).
  Parameter cumul_Type : forall e n, sub_typ e (type n) (type (S n)).
  Parameter cumul_Prop : forall e, sub_typ e prop (type 0).

  Parameter typ_prod2 : forall e n T U,
    typ e T (type n) ->
    typ (T :: e) U (type n) ->
    typ e (Prod T U) (type n).

  Parameter sub_typ_covariant : forall e U1 U2 V1 V2,
    U1 <> kind ->
    eq_typ e U1 U2 ->
    sub_typ (U1::e) V1 V2 ->
    sub_typ e (Prod U1 V1) (Prod U2 V2).

End ECC_Rules.

Module Type Nat_Rules (M:Judge).
  Import M M.T M.J.

  Parameter Nat Zero Succ : term.
  Parameter NatRec : term -> term -> term -> term.

  Parameter typ_N : forall e, typ e Nat kind.
  Parameter typ_0 : forall e, typ e Zero Nat.
  Parameter typ_S : forall e, typ e Succ (Prod Nat (lift 1 Nat)).
  Parameter typ_Nrect : forall e n f g P,
    typ e n Nat ->
    typ e f (App P Zero) ->
    typ e g (Prod Nat (Prod (App (lift 1 P) (Ref 0))
               (App (lift 2 P) (App Succ (Ref 1))))) ->
    typ e (NatRec f g n) (App P n).

  Parameter eq_typ_NatRec : forall e f f' g g' n n',
    eq_typ e f f' ->
    eq_typ e g g' ->
    eq_typ e n n' ->
    eq_typ e (NatRec f g n) (NatRec f' g' n').

  Parameter NatRec_eq_0 : forall e f g,
    eq_typ e (NatRec f g Zero) f.

  Parameter NatRec_eq_S : forall e f g n,
    typ e n Nat ->
    eq_typ e (NatRec f g (App Succ n)) (App (App g n) (NatRec f g n)).

End Nat_Rules.

Module Type W_Rules (M:Judge).
  Import M M.T M.J.

  (*Parameter Ordt : set -> term. *)
  Parameter OSucc : term -> term.
  Parameter OSucct : term -> term.

  Parameter WI : term -> term -> term -> term.
  Parameter Wc : term -> term -> term -> term -> term.
  Parameter Wcase : term -> term -> term -> term -> term.
  Parameter WFix : term -> term -> term -> term -> term.

End W_Rules.

Module Type Variance (M:Judge).
  Import M M.T M.J.

  Parameter fenv_ : Type.
  Parameter tenv : fenv_ -> env.
  Parameter push_var : fenv_ -> term -> fenv_.
  Parameter push_ord : fenv_ -> term -> fenv_.
  Parameter push_fun : fenv_ -> term -> term -> fenv_.
  Parameter var_equals : fenv_ -> term -> Prop.
End Variance.
