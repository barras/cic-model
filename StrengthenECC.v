Require Import TypeECC.

Lemma lift_inj: forall n t u k, lift_rec n t k = lift_rec n u k -> t = u.
Proof.
induction n; intros.
repeat rewrite lift_rec0 in H; trivial.
apply IHn with k.
rewrite <- simpl_subst_rec with (p:=k) (N:=t); auto with arith.
rewrite <- simpl_subst_rec with (M:=u) (p:=k) (N:=t); auto with arith.
rewrite H; trivial.
Qed.

Lemma lift_ref_inv :
 forall n t k i, 
 lift_rec n t k = Ref i ->
  k > i /\ t = Ref i \/
  n+k <= i /\ t = Ref (i-n).
Proof.
destruct t; try (intros;discriminate).
simpl.
intros k i.
case (le_gt_dec k n0); intros;auto.
injection H;intros; subst i.
right; split;auto with arith.

injection H;intros; subst i.
auto.
Qed.

Lemma lift_srt_inv :
 forall n t k s, 
 lift_rec n t k = Srt s -> t = Srt s.
Proof.
destruct t; simpl; intros; try discriminate; trivial.
destruct (le_gt_dec k n0); discriminate.
Qed.

Lemma lift_abs_inv :
 forall n t k T M, 
 lift_rec n t k = Abs T M ->
 exists2 T', lift_rec n T' k = T &
 exists2 M', lift_rec n M' (S k) = M &
 t = Abs T' M'.
Proof.
destruct t; simpl; intros; try discriminate; trivial.
destruct (le_gt_dec k n0); discriminate.
injection H; eauto.
Qed.

Lemma lift_app_inv :
 forall n t k u v, 
 lift_rec n t k = App u v ->
 exists2 u', lift_rec n u' k = u &
 exists2 v', lift_rec n v' k = v &
 t = App u' v'.
Proof.
destruct t; simpl; intros; try discriminate; trivial.
destruct (le_gt_dec k n0); discriminate.
injection H; eauto.
Qed.

Lemma lift_prod_inv :
 forall n t k T M, 
 lift_rec n t k = Prod T M ->
 exists2 T', lift_rec n T' k = T &
 exists2 M', lift_rec n M' (S k) = M &
 t = Prod T' M'.
Proof.
destruct t; simpl; intros; try discriminate; trivial.
destruct (le_gt_dec k n0); discriminate.
injection H; eauto.
Qed.

Lemma red1_red1_lift_ex : 
  forall n t u, red1 t u -> forall k t', lift_rec n t' k = t ->
   exists2 u', red1 t' u' & u=lift_rec n u' k.
Proof.
induction 1; intros.
apply lift_app_inv in H; destruct H as (U', eqU', (N',eqN', eqt)).
subst N t'.
apply lift_abs_inv in eqU'; destruct eqU' as (T',eqT', (M',eqM', eqU')).
subst T M U'.
rewrite <- distr_lift_subst.
exists (subst N' M'); auto with coc.
(**)
apply lift_abs_inv in H0; destruct H0 as (a,eqa,(b,eqb,eqt')).
subst M N t'.
destruct IHred1 with k a as (a',reda,eqM'); trivial.
subst M'.
exists (Abs a' b); auto with coc.

apply lift_abs_inv in H0; destruct H0 as (a,eqa,(b,eqb,eqt')).
subst M N t'.
destruct IHred1 with (S k) b as (b',redb,eqM'); trivial.
subst M'.
exists (Abs a b'); auto with coc.

apply lift_app_inv in H0; destruct H0 as (a,eqa,(b,eqb,eqt')).
subst M1 M2 t'.
destruct IHred1 with k a as (a',reda,eqM'); trivial.
subst N1.
exists (App a' b); auto with coc.

apply lift_app_inv in H0; destruct H0 as (a,eqa,(b,eqb,eqt')).
subst M1 M2 t'.
destruct IHred1 with k b as (b',redb,eqM'); trivial.
subst N2.
exists (App a b'); auto with coc.

apply lift_prod_inv in H0; destruct H0 as (a,eqa,(b,eqb,eqt')).
subst M1 M2 t'.
destruct IHred1 with k a as (a',reda,eqM'); trivial.
subst N1.
exists (Prod a' b); auto with coc.

apply lift_prod_inv in H0; destruct H0 as (a,eqa,(b,eqb,eqt')).
subst M1 M2 t'.
destruct IHred1 with (S k) b as (b',redb,eqM'); trivial.
subst N2.
exists (Prod a b'); auto with coc.
Qed.

Lemma red_red_lift_ex : 
  forall n t k u,
  red (lift_rec n t k) u ->
  exists2 u', red t u' & u=lift_rec n u' k.
Proof.
induction 1; intros.
exists t; auto with coc.
elim IHred;intros.
elim red1_red1_lift_ex with (1:=H0) (2:=sym_equal H2);intros.
exists x0; trivial.
constructor 2 with x; trivial.
Qed.

Lemma red_lift_lift_inv :
  forall n t u k, red (lift_rec n t k) (lift_rec n u k) -> red t u.
Proof.
intros.
elim red_red_lift_ex with (1 := H); intros.
rewrite (lift_inj _ _ _ _ H1); trivial.
Qed.

Lemma conv_lift_lift_inv :
  forall t u k, conv (lift_rec 1 t k) (lift_rec 1 u k) -> conv t u.
Proof.
intros.
assert (conv (subst_rec (Ref 0) (lift_rec 1 t k) k)
             (subst_rec (Ref 0) (lift_rec 1 u k) k)).
 apply conv_conv_subst; auto with coc.
rewrite simpl_subst_rec in H0; auto.
rewrite simpl_subst_rec in H0; auto.
do 2 rewrite lift_rec0 in H0; trivial.
Qed.

Lemma red_red_lift :
  forall n t u k, red t u -> red (lift_rec n t k) (lift_rec n u k).
induction 1; intros; auto with coc.
constructor 2 with (lift_rec n P k); auto with coc.
Qed.

Lemma red_red_subst :
  forall x t u k, red t u -> red (subst_rec x t k) (subst_rec x u k).
induction 1; intros; auto with coc.
constructor 2 with (subst_rec x P k); auto with coc.
Qed.

  Lemma ins_item_ge_inv :
   forall A n e f,
   ins_in_env A n e f -> forall v t, n <= v -> item t f (S v) -> item t e v.
Proof.
induction 1; intros.
inversion H0; trivial.
destruct v.
inversion H0.
inversion_clear H1; auto 10 with coc arith.
Qed.

  Lemma ins_item_lt_inv :
   forall A n e f,
   ins_in_env A n e f ->
   forall v t, n > v ->
   item_lift t f v ->
   exists2 t', t = lift_rec 1 t' n & item_lift t' e v.
Proof.
induction 1; intros.
inversion H.
destruct v.
destruct H1.
subst t0.
inversion_clear H2.
rewrite permute_lift.
exists (lift 1 t); auto.
exists t; auto.

destruct H1.
inversion_clear H2.
elim IHins_in_env with v (lift (S v) x); intros; auto with arith.
subst t0.
rewrite simpl_lift.
rewrite H2.
rewrite permute_lift.
exists (lift 1 x0); auto.

destruct H4.
subst x0.
rewrite <- simpl_lift.
exists x1; auto.

exists x;auto.
Qed.


Lemma pre_strength :
  forall A e M T,
  typ e M T ->
  forall f k M',
  lift_rec 1 M' k = M ->
  ins_in_env A k f e ->
  wf f ->
  exists2 T', red T (lift_rec 1 T' k) & typ f M' T'.
Proof.
induction 1; intros.
(* prop *)
apply lift_srt_inv in H0; subst M'.
exists (Srt (kind 0)); auto with coc.
constructor; trivial.

(* kind *)
apply lift_srt_inv in H0; subst M'.
exists (Srt (kind (S n))); auto with coc.
constructor; trivial.

(* vars *)
apply lift_ref_inv in H1.
destruct H1.
 destruct H1; subst M'.
 specialize ins_item_lt_inv with (1:=H2) (2:=H1) (3:=H0); intro.
 destruct H4.
 subst t.
 exists x; auto with coc.
 constructor; trivial.

 destruct H1; subst M'.
 destruct v; simpl.
  inversion H1.
 rewrite <- minus_n_O.
 destruct H0.
 assert (k<=v); auto with arith.
 specialize ins_item_ge_inv with (1:=H2) (2:=H5) (3:=H4); intro.
 exists (lift (S v) x).
  subst t.
  unfold lift; rewrite simpl_lift_rec; simpl; auto with arith coc.

  constructor ; trivial.
  exists x; trivial.

(* Abs *)
apply lift_abs_inv in H3; destruct H3 as (T1,eqT,(M1,eqM,eqM')); subst.
destruct IHtyp1 with (M':=T1) (2:=H4) (3:=H5) as (T',reds,tyT1); intros; trivial.
assert (T'=Srt s1).
 apply lift_srt_inv with 1 k.
 rewrite red_normal with (1:=reds); trivial.
 red;red;intros.
 inversion H3.
clear reds; subst T'.
assert (wf (T1 :: f)).
 apply wf_var with s1; trivial.
assert (ins_in_env A (S k) (T1::f) (lift_rec 1 T1 k::e)).
 constructor; trivial.
destruct IHtyp3 with (M':=M1) (2:=H6) (3:=H3) as (U',redU,tyU); intros; trivial.
exists (Prod T1 U'); simpl; auto with coc.
apply type_abs with s1 s2 s3; trivial.
specialize type_case with (1:=tyU);intro.
destruct H7.
replace s2 with x; trivial.
assert (conv (Srt x) (Srt s2)).
 apply typ_conv_conv with (u:=lift_rec 1 U' (S k)) (2:=H0).
  change (Srt x) with (lift_rec 1 (Srt x) (S k)).
  apply typ_weak_weak with (1:=H7) (2:=H6); trivial.
  apply wf_var with s1; trivial.

  apply sym_conv; auto with coc.
apply conv_sort; trivial.

(* App *)
apply lift_app_inv in H1; destruct H1 as (u',equ,(v',eqv,eqM')); subst.
destruct IHtyp2 with (M':=u') (2:=H2) (3:=H3) as (T',redp, tyu'); trivial.
destruct IHtyp1 with (M':=v') (2:=H2) (3:=H3) as (V',redV, tyv'); trivial.
apply red_prod_prod with (1:=redp); intros.
apply lift_prod_inv in H1; destruct H1 as (a',eqa,(b',eqb,eqT')); subst.
clear IHtyp1 IHtyp2.
exists (subst v' b').
 rewrite distr_lift_subst.
 unfold subst.
 apply red_red_subst; trivial.

 apply type_app with a'; trivial.
 apply type_case in tyu'.
 destruct tyu'.
 apply inv_typ_prod with (1:=H1); intros.
 apply type_conv with V' s1; auto with coc.
 apply conv_lift_lift_inv with k.
 apply trans_conv_conv with V; auto with coc.
 apply sym_conv; auto with coc.

(* Prod *)
exists (Srt s3); auto with coc.
apply lift_prod_inv in H2; destruct H2 as (T', eqT', (U', eqU', eqM')); subst.
destruct IHtyp1 with (M':=T') (2:=H3) (3:=H4) as (T1, reds, tyT'); trivial.
assert (T1=Srt s1).
 apply lift_srt_inv with 1 k.
 rewrite red_normal with (1:=reds); trivial.
 red;red;intros.
 inversion H2.
clear reds; subst T1.
assert (wf (T' :: f)).
 apply wf_var with s1; trivial.
assert (ins_in_env A (S k) (T'::f) (lift_rec 1 T' k::e)).
 constructor; trivial.
destruct IHtyp2 with (M':=U') (2:=H5) (3:=H2) as (U1, reds, tyU'); trivial.
apply type_prod with s1 s2; trivial.
apply red_normal in reds.
 symmetry in reds; apply lift_srt_inv in reds.
 subst U1; trivial.

 red; red; intros.
 inversion H6.

(* conv *)
destruct IHtyp1 with (1:=H2) (2:=H3) (3:=H4) as (U', redU, tyM').
elim church_rosser with V (lift_rec 1 U' k); intros.
2:apply trans_conv_conv with U; auto with coc.
apply red_red_lift_ex in H6.
destruct H6 as (U1, redU', eqx); subst x.
exists U1; trivial.
apply type_reduction with U'; trivial.
Qed.

Lemma strengthening_env :
  forall A k e f,
  ins_in_env A k f e ->
  wf e ->
  wf f.
Proof.
induction 1; intros.
 inversion_clear H.
   apply typ_wf with (1 := H0).
 inversion_clear H0.
   apply wf_var with s.
   elim pre_strength with (1 := H1) (M' := t) (3 := H); intros; auto.
   replace (Srt s) with x; trivial.
    apply lift_srt_inv with 1 n.
    symmetry  in |- *.
    apply red_normal; trivial.
    red in |- *; red in |- *; intros.
    inversion H3.
  specialize typ_wf with (1 := H1); auto.
Qed.

Lemma strengthening :
  forall A e f M T k,
  typ e (lift_rec 1 M k) (lift_rec 1 T k) ->
  ins_in_env A k f e ->
  typ f M T.
Proof.
intros.
assert (wff : wf f).
 apply strengthening_env with (1 := H0).
 apply typ_wf with (1 := H).
elim pre_strength with (1 := H) (M' := M) (3 := H0); trivial; intros.
elim type_case with (1 := H); intros.
apply type_conv with x x0; trivial.
 apply sym_conv.
 apply red_conv.
 apply red_lift_lift_inv in H1; trivial.

 elim pre_strength with (1 := H3) (M' := T) (3 := H0); intros; trivial.
 apply red_normal in H4.
  symmetry in H4; apply lift_srt_inv in H4.
  subst x1; trivial.

  red; red; intros.
  inversion H6.
Qed.

Lemma strengthening0 :
  forall A e M T,
  typ (cons A e) (lift 1 M) (lift 1 T) ->
  typ e M T.
Proof.
intros.
apply strengthening with A (A :: e) 0; trivial.
constructor.
Qed.
