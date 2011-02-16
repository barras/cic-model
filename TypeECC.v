Require Export ConvECC.
Require Export EnvECC.
Require Import Peano_dec.
Require Import Max.

Section Typage.

  Definition ecc_prod s1 s2 s3 :=
    match s2, s1, s3 with
      prop, _, prop => true
    | kind n, prop, kind n' => if eq_nat_dec n n' then true else false
    | kind n, kind m, kind n' => if eq_nat_dec (max n m) n' then true else false
    | _, _, _ => false
    end.

  Axiom ecc_prod_fun : forall s1 s2 s3 s1' s2' s3',
     ecc_prod s1 s2 s3 = true ->
     ecc_prod s1' s2' s3' = true ->
     s1 = s1' ->
     s2 = s2' ->
     s3 = s3'.

  Inductive wf : env -> Prop :=
    | wf_nil : wf nil
    | wf_var : forall e T s, typ e T (Srt s) -> wf (T :: e)
  with typ : env -> term -> term -> Prop :=
    | type_prop :
        forall e,
        wf e ->
        typ e (Srt prop) (Srt (kind 0))
    | type_kind :
        forall e n,
        wf e ->
        typ e (Srt (kind n)) (Srt (kind (S n)))
    | type_var :
        forall e v t,
        wf e ->
        item_lift t e v ->
        typ e (Ref v) t
    | type_abs :
        forall e T M U s1 s2 s3,
        typ e T (Srt s1) ->
        typ (T :: e) U (Srt s2) ->
        typ (T :: e) M U ->
        ecc_prod s1 s2 s3 = true ->
        typ e (Abs T M) (Prod T U)
    | type_app :
        forall e u v V Ur,
        typ e v V ->
        typ e u (Prod V Ur) ->
        typ e (App u v) (subst v Ur)
    | type_prod :
        forall e T U s1 s2 s3,
        typ e T (Srt s1) ->
        typ (T :: e) U (Srt s2) ->
        ecc_prod s1 s2 s3 = true ->
        typ e (Prod T U) (Srt s3)
    | type_conv :
        forall e t U V s,
        typ e t U ->
        conv U V ->
        typ e V (Srt s) ->
        typ e t V.

  Hint Resolve wf_nil type_prop type_kind type_var: coc.

Scheme typ_mind := Minimality for typ Sort Prop
  with wf_mind := Minimality for wf Sort Prop.


  Lemma typ_wf : forall e t T, typ e t T -> wf e.
simple induction 1; auto with coc.
Qed.

  Hint Resolve typ_wf: coc.


  Lemma wf_sort :
   forall n e f t,
   trunc (S n) e f -> wf e -> item t e n -> exists s, typ f t (Srt s).
simple induction n.
do 4 intro.
inversion_clear H.
inversion_clear H0.
intros.
inversion_clear H0.
inversion_clear H.
eauto with coc.

do 6 intro.
inversion_clear H0.
intros.
inversion_clear H2.
inversion_clear H0.
elim H with e0 f t; intros; eauto with coc.
Qed.



  Definition inv_type (P : Prop) e t T :=
    match t with
    | Srt prop => conv T (Srt (kind 0)) -> P
    | Srt (kind n) => conv T (Srt (kind (S n))) -> P
    | Ref n => forall x, item x e n -> conv T (lift (S n) x) -> P
    | Abs A M =>
        forall s1 s2 s3 U,
        typ e A (Srt s1) ->
        typ (A :: e) M U -> typ (A :: e) U (Srt s2) ->
        ecc_prod s1 s2 s3 = true -> conv T (Prod A U) -> P
    | App u v =>
        forall Ur V,
        typ e v V -> typ e u (Prod V Ur) -> conv T (subst v Ur) -> P
    | Prod A B =>
        forall s1 s2 s3,
        typ e A (Srt s1) -> typ (A :: e) B (Srt s2) ->
        ecc_prod s1 s2 s3 = true -> conv T (Srt s3) -> P
    end.

  Lemma inv_type_conv :
   forall P e t U V, conv U V -> inv_type P e t U -> inv_type P e t V.
do 6 intro.
cut (forall x : term, conv V x -> conv U x).
intro.
case t; simpl in |- *; intros.
generalize H1.
elim s; auto with coc; intros.

apply H1 with x; auto with coc.

apply H1 with s1 s2 s3 U0; auto with coc.

apply H1 with Ur V0; auto with coc.

apply H1 with s1 s2 s3; auto with coc.

intros.
apply trans_conv_conv with V; auto with coc.
Qed.


  Theorem typ_inversion : forall P e t T, typ e t T -> inv_type P e t T -> P.
simple induction 1; simpl in |- *; intros.
auto with coc.

auto with coc.

elim H1; intros.
apply H2 with x; auto with coc.
rewrite H3; auto with coc.

apply H7 with s1 s2 s3 U; auto with coc.

apply H4 with Ur V; auto with coc.

apply H5 with s1 s2 s3; auto with coc.

apply H1.
apply inv_type_conv with V; auto with coc.
Qed.



  Lemma inv_typ_kind :
    forall e T n, typ e (Srt (kind n)) T -> conv T (Srt (kind (S n))).
intros.
apply typ_inversion with e (Srt (kind n)) T; simpl in |- *; auto with coc.
Qed.

  Lemma inv_typ_prop : forall e T, typ e (Srt prop) T -> conv T (Srt (kind 0)).
intros.
apply typ_inversion with e (Srt prop) T; simpl in |- *; auto with coc.
Qed.

  Lemma inv_typ_ref :
   forall (P : Prop) e T n,
   typ e (Ref n) T ->
   (forall U : term, item U e n -> conv T (lift (S n) U) -> P) -> P.
intros.
apply typ_inversion with e (Ref n) T; simpl in |- *; intros; auto with coc.
apply H0 with x; auto with coc.
Qed.

  Lemma inv_typ_abs :
   forall (P : Prop) e A M U,
   typ e (Abs A M) U ->
   (forall s1 s2 s3 T,
    typ e A (Srt s1) ->
    typ (A :: e) M T -> typ (A :: e) T (Srt s2) ->
    ecc_prod s1 s2 s3 = true -> conv (Prod A T) U -> P) ->
   P.
intros.
apply typ_inversion with e (Abs A M) U; simpl in |- *; auto with coc; intros.
apply H0 with s1 s2 s3 U0; auto with coc.
Qed.

  Lemma inv_typ_app :
   forall (P : Prop) e u v T,
   typ e (App u v) T ->
   (forall V Ur, typ e u (Prod V Ur) -> typ e v V -> conv T (subst v Ur) -> P) ->
   P.
intros.
apply typ_inversion with e (App u v) T; simpl in |- *; auto with coc; intros.
apply H0 with V Ur; auto with coc.
Qed.

  Lemma inv_typ_prod :
   forall (P : Prop) e T U s,
   typ e (Prod T U) s ->
   (forall s1 s2 s3,
    typ e T (Srt s1) -> typ (T :: e) U (Srt s2) -> ecc_prod s1 s2 s3 = true ->
    conv (Srt s3) s -> P) -> P.
intros.
apply typ_inversion with e (Prod T U) s; simpl in |- *; auto with coc; intros.
apply H0 with s1 s2 s3; auto with coc.
Qed.



  Lemma typ_weak_weak :
   forall A e t T,
   typ e t T ->
   forall n f,
   ins_in_env A n e f -> wf f -> typ f (lift_rec 1 t n) (lift_rec 1 T n).
simple induction 1; simpl in |- *; intros; auto with coc.
elim (le_gt_dec n v); intros; apply type_var; auto with coc.
apply ins_item_lift_ge with A e0; auto with coc.

apply ins_item_lift_lt with A e0; auto with coc.

cut (wf (lift_rec 1 T0 n :: f)).
intro.
apply type_abs with s1 s2 s3; auto with coc.

apply wf_var with s1; auto with coc.

rewrite distr_lift_subst.
apply type_app with (lift_rec 1 V n); auto with coc.

cut (wf (lift_rec 1 T0 n :: f)).
intro.
apply type_prod with s1 s2; auto with coc.

apply wf_var with s1; auto with coc.

apply type_conv with (lift_rec 1 U n) s; auto with coc.
Qed.


  Theorem thinning :
   forall e t T A,
   typ e t T -> wf (A :: e) -> typ (A :: e) (lift 1 t) (lift 1 T).
unfold lift in |- *.
intros.
inversion_clear H0.
apply typ_weak_weak with A e; auto with coc.
apply wf_var with s; auto with coc.
Qed.


  Lemma thinning_n :
   forall n e f t T,
   trunc n (e:env) (f:env) ->
   typ f t T -> wf e -> typ e (lift n t) (lift n T).
simple induction 1.
intros.
rewrite lift0.
rewrite lift0.
trivial.

intros.
rewrite simpl_lift; auto with coc.
pattern (lift (S k) T) in |- *.
rewrite simpl_lift; auto with coc.
apply thinning; auto with coc.
apply H1; trivial.
inversion_clear H3.
eauto with coc.
Qed.


  Lemma wf_sort_lift :
   forall n e t, wf e -> item_lift t e n -> exists s, typ e t (Srt s).
simple induction n.
simple destruct e; intros.
elim H0; intros.
inversion_clear H2.

elim H0; intros.
rewrite H1.
inversion_clear H2.
inversion_clear H.
exists s.
replace (Srt s) with (lift 1 (Srt s)); auto with coc.
apply thinning; auto with coc.
apply wf_var with s; auto with coc.

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
change (typ (y :: l) (lift 1 (lift (S n0) x)) (lift 1 (Srt x0))) in |- *.
apply thinning; auto with coc.
apply wf_var with s; auto with coc.

exists x; auto with coc.

inversion_clear H3.
eauto with coc.
Qed.


  Lemma typ_sub_weak :
   forall g d t e u U,
   typ g d t ->
   typ e u U ->
   forall f n,
   sub_in_env d t n e f ->
   wf f -> trunc n f g -> typ f (subst_rec d u n) (subst_rec d U n).
Proof.
simple induction 2; simpl in |- *; intros; auto with coc.
destruct (lt_eq_lt_dec n v) as [[fvar|eq_var]|bvar].
constructor; trivial.
apply sub_item_lift_sup with (1 := H3) (2 := fvar) (3 := H2).

subst v; rewrite sub_item_lift_eq with (1 := H3) (2 := H2).
apply thinning_n with g; auto with coc.

constructor; trivial.
apply nth_sub_inf with (1 := H3); trivial.

cut (wf (subst_rec d T n :: f)); intros.
apply type_abs with s1 s2 s3; auto with coc.

apply wf_var with s1; auto with coc.

rewrite distr_subst.
apply type_app with (subst_rec d V n); auto with coc.

cut (wf (subst_rec d T n :: f)); intros.
apply type_prod with s1 s2; auto with coc.

apply wf_var with s1; auto with coc.

apply type_conv with (subst_rec d U0 n) s; auto with coc.
Qed.


  Theorem substitution :
   forall e t u U d,
   typ (t :: (e:env)) u U -> typ e d t -> typ e (subst d u) (subst d U).
intros.
unfold subst in |- *.
apply typ_sub_weak with e t (t :: e); auto with coc.
apply typ_wf with d t; auto with coc.
Qed.




  Theorem type_case : forall e t T, typ e t T -> exists s, typ e T (Srt s).
simple induction 1; intros; auto with coc.
 exists (kind 1); auto with coc.
 exists (kind (S (S n))); auto with coc.
 elim wf_sort_lift with (2 := H1); trivial; intros.
   exists x; auto with coc.
 exists s3.
   apply type_prod with s1 s2; auto with coc.
 destruct H3.
   apply inv_typ_prod with (1 := H3); intros.
   exists s2.
   change (Srt s2) with (subst v (Srt s2)) in |- *.
   apply substitution with V; auto with coc.
 destruct s3.
  exists (kind (S n)); auto with coc.
    constructor.
    apply typ_wf with (1 := H0).
  exists (kind 0).
    constructor.
    apply typ_wf with (1 := H0).
 exists s; trivial.
Qed.



  Lemma typ_red_env :
   forall e t T, typ e t T ->
   forall f, red1_in_env red1 e f -> wf f -> typ f t T.
simple induction 1; intros; auto with coc.

elim red_item with (2 := H1) (3 := H2); auto with coc; intros.
inversion_clear H4.
inversion_clear H6.
elim H1; intros.
elim item_trunc with (1 := H8); intros.
elim wf_sort with (1 := H9) (3 := H8); eauto; intros.
apply type_conv with x x2; auto with coc.
rewrite H6.
replace (Srt x2) with (lift (S v) (Srt x2)); auto with coc.
apply thinning_n with x1; auto with coc.

cut (wf (T0 :: f)); intros.
apply type_abs with s1 s2 s3; auto with coc.

apply wf_var with s1; auto with coc.

apply type_app with V; auto with coc.

cut (wf (T0 :: f)); intros.
apply type_prod with s1 s2; auto with coc.

apply wf_var with s1; auto with coc.

apply type_conv with U s; auto with coc.
Qed.


  Lemma subj_red : forall e t T, typ e t T -> forall u, red1 t u -> typ e u T.
simple induction 1; intros.
inversion_clear H1.

inversion_clear H1.

inversion_clear H2.

inversion_clear H7.
cut (wf (M' :: e0)); intros.
apply type_conv with (Prod M' U) s3; auto with coc.
apply type_abs with s1 s2 s3; auto with coc.
apply typ_red_env with (T0 :: e0); auto with coc.

apply typ_red_env with (T0 :: e0); auto with coc.

apply type_prod with s1 s2; auto with coc.

apply wf_var with s1; auto with coc.

apply type_abs with s1 s2 s3; auto with coc.

elim type_case with (1 := H2); intros.
apply inv_typ_prod with (1 := H5); intros.
generalize H2 H3; clear H2 H3.
inversion_clear H4; intros.
apply inv_typ_abs with (1 := H2); intros.
apply type_conv with (subst v T1) s2; auto with coc.
apply substitution with T0; auto with coc.
apply type_conv with V s0; auto with coc.
apply sym_conv.
apply inv_conv_prod_l with (1 := H13).

unfold subst in |- *.
apply conv_conv_subst; auto with coc.
apply inv_conv_prod_r with (1 := H13); auto with coc.

replace (Srt s2) with (subst v (Srt s2)); auto with coc.
apply substitution with V; auto with coc.

apply type_app with V; auto with coc.

apply type_conv with (subst N2 Ur) s2; auto with coc.
apply type_app with V; auto with coc.

unfold subst in |- *.
apply conv_conv_subst; auto with coc.

replace (Srt s2) with (subst v (Srt s2)); auto with coc.
apply substitution with V; auto with coc.

inversion_clear H5.
apply type_prod with s1 s2; auto with coc.
apply typ_red_env with (T0 :: e0); auto with coc.
apply wf_var with s1; auto with coc.

apply type_prod with s1 s2; auto with coc.

apply type_conv with U s; auto with coc.
Qed.


  Theorem subject_reduction :
   forall e t u, red t u -> forall T, typ e t T -> typ e u T.
simple induction 1; intros; auto with coc.
apply subj_red with P; intros; auto with coc.
Qed.


  Lemma type_reduction : forall e t T U, red T U -> typ e t T -> typ e t U.
intros.
elim type_case with (1 := H0); intros.
apply type_conv with T x; auto with coc.
apply subject_reduction with T; trivial.
Qed.



  Theorem typ_unique :
   forall e t T, typ e t T -> forall U, typ e t U -> conv T U.
simple induction 1; intros.
 apply sym_conv.
   apply inv_typ_prop with e0; auto with coc.
 apply sym_conv.
   apply inv_typ_kind with e0; auto with coc.
 apply inv_typ_ref with e0 U v; auto with coc; intros.
   elim H1; intros.
    rewrite H5.
   elim fun_item with (1 := H3) (2 := H6); auto with coc.
 apply inv_typ_abs with (1 := H7); intros.
   apply trans_conv_conv with (Prod T0 T1); auto with coc.
 apply inv_typ_app with (1 := H4); intros.
   apply trans_conv_conv with (subst v Ur0); auto with coc.
   unfold subst in |- *; apply conv_conv_subst; auto with coc.
   apply inv_conv_prod_r with (1 := H3 _ H5).
 apply inv_typ_prod with (1 := H5); intros.
   apply trans_conv_conv with (Srt s5); auto with coc.
    replace s5 with s3; auto with coc.
   apply ecc_prod_fun with (1 := H4) (2 := H8).
  apply conv_sort.
    auto.
  apply conv_sort; auto.
 apply trans_conv_conv with U; auto with coc.
Qed.


  Lemma typ_conv_conv :
   forall e u U v V, typ e u U -> typ e v V -> conv u v -> conv U V.
intros.
elim church_rosser with (1 := H1); auto with coc; intros.
apply typ_unique with e x.
apply subject_reduction with u; trivial.

apply subject_reduction with v; trivial.
Qed.

End Typage.
