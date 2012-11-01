(*This files are the defintions and lemmas about general SN model*)


Require Import SN_CC_Real.

Import ZF CCSN SN.
Import List.

Reserved Notation "[ x , t ] \real A" (at level 60).

(***************************************************************************************)
(*This following lemmas should be put in ObjectSN, about properties of lift and subst*)
(***************************************************************************************)
Lemma lift0 : forall A, eq_trm (lift 0 A) A.
intros; apply eq_trm_intro; intros; [| |destruct A; simpl; trivial].
 unfold lift; rewrite int_lift_rec_eq; rewrite V.lams0; reflexivity.

 unfold lift; rewrite tm_lift_rec_eq; rewrite I.lams0; reflexivity.
Qed.

Lemma lift_rec_acc : forall t m n p q,
  q <= p <= n + q  ->
  eq_trm (lift_rec m p (lift_rec n q t)) (lift_rec (m+n) q t).
intros; apply eq_trm_intro; intros; [| |destruct t; simpl; trivial].
 do 3 rewrite int_lift_rec_eq. unfold V.lams, V.shift. apply int_morph; [|reflexivity].
  do 2 red; intros. destruct (le_gt_dec q a) as [le|gt].
   replace (q+(n+(a-q))) with (n+a) by omega.
   destruct (le_gt_dec p (n+a)) as [le'|gt]; [|omega].
    replace (p+(m+(n+a-p))) with (m+n+a) by omega.
    replace (q+(m+n+(a-q))) with (m+n+a) by omega. reflexivity.

   destruct (le_gt_dec p a) as [le|gt']; [omega|reflexivity].
   
 do 3 rewrite tm_lift_rec_eq. unfold I.lams, I.shift. apply tm_morph; [|reflexivity].
  do 2 red; intros. destruct (le_gt_dec q a) as [le|gt].
   replace (q+(n+(a-q))) with (n+a) by omega.
   destruct (le_gt_dec p (n+a)) as [le'|gt]; [|omega].
    replace (p+(m+(n+a-p))) with (m+n+a) by omega.
    replace (q+(m+n+(a-q))) with (m+n+a) by omega. reflexivity.

   destruct (le_gt_dec p a) as [le|gt']; [omega|reflexivity].
Qed.

Lemma lift_rec_comm : forall t m n p q,
  p <= q ->
  eq_trm (lift_rec m p (lift_rec n q t)) (lift_rec n (m+q) (lift_rec m p t)).
intros; apply eq_trm_intro; intros; [| |destruct t; simpl; trivial].
 do 4 rewrite int_lift_rec_eq. unfold V.lams, V.shift. apply int_morph; [|reflexivity].
  do 2 red; intros. destruct (le_gt_dec q a) as [le|gt].
   replace (q+(n+(a-q))) with (n+a) by omega.
   destruct (le_gt_dec p (n+a)) as [le'|gt]; [|omega].
    destruct (le_gt_dec p a) as [le''|gt]; [|omega].
     replace (p+(m+(a-p))) with (m+a) by omega.
     destruct (le_gt_dec (m+q) (m+a)) as [le'''|gt]; [|omega].
      replace (p+(m+(n+a-p))) with (m+n+a) by omega.
      replace (m+q+(n+(m+a-(m+q)))) with (m+n+a); [reflexivity|omega].

   destruct (le_gt_dec p a) as [le|gt'].
    replace (p+(m+(a-p))) with (m+a) by omega.
    destruct (le_gt_dec (m+q) (m+a)) as [le'|gt']; [omega|reflexivity].
    
    destruct (le_gt_dec (m+q) a) as [le|gt'']; [omega|reflexivity].

 do 4 rewrite tm_lift_rec_eq. unfold I.lams, I.shift. apply tm_morph; [|reflexivity].
  do 2 red; intros. destruct (le_gt_dec q a) as [le|gt].
   replace (q+(n+(a-q))) with (n+a) by omega.
   destruct (le_gt_dec p (n+a)) as [le'|gt]; [|omega].
    destruct (le_gt_dec p a) as [le''|gt]; [|omega].
     replace (p+(m+(a-p))) with (m+a) by omega.
     destruct (le_gt_dec (m+q) (m+a)) as [le'''|gt]; [|omega].
      replace (p+(m+(n+a-p))) with (m+n+a) by omega.
      replace (m+q+(n+(m+a-(m+q)))) with (m+n+a); [reflexivity|omega].

   destruct (le_gt_dec p a) as [le|gt'].
    replace (p+(m+(a-p))) with (m+a) by omega.
    destruct (le_gt_dec (m+q) (m+a)) as [le'|gt']; [omega|reflexivity].
    
    destruct (le_gt_dec (m+q) a) as [le|gt'']; [omega|reflexivity].
Qed.

Lemma subst_lift_ge : forall m n t u k,
  m >= n + k ->
  eq_trm (subst_rec t (S m) (lift_rec (S n) k u)) 
         (lift_rec 1 k (subst_rec t m (lift_rec n k u))).
intros; apply eq_trm_intro; simpl; intros; [| |destruct u; simpl; trivial].
 rewrite int_lift_rec_eq. 
 do 2 rewrite int_subst_rec_eq. do 2 rewrite int_lift_rec_eq.
 apply int_morph; [do 2 red; intros|reflexivity].
  unfold V.lams, V.shift. 
  destruct (le_gt_dec k a).
   replace (k+(S n + (a-k))) with (S n + a) by omega.
   destruct (le_gt_dec (S m) (S n + a)) as [le|gt]; 
     replace (k+(n+(a-k))) with (n+a) by omega.
    destruct (le_gt_dec m (n+a)) as [le'|gt]; [|omega].
     apply V.cons_morph; [apply int_morph; [do 2 red; intros|reflexivity]|do 2 red; intros];
       (destruct (le_gt_dec k (m+a0)) as [le''|gt]; [|omega]);
       (replace (k+(1+(m+a0-k))) with (S m + a0); [reflexivity|omega]).

    destruct (le_gt_dec m (n+a)) as [le|gt']; [omega|].
     destruct (le_gt_dec k (n+a)) as [le|gt'']; [|omega].
      replace (k+(1+(n+a-k))) with (S n + a); [reflexivity|omega].
      
   destruct (le_gt_dec (S m) a) as [le|gt]; [omega|].
    destruct (le_gt_dec m a) as [le|gt']; [omega|reflexivity].

 rewrite tm_lift_rec_eq.
 do 2 rewrite tm_subst_rec_eq. do 2 rewrite tm_lift_rec_eq.
 apply tm_morph; [do 2 red; intros|reflexivity].
  unfold I.lams, I.shift. 
  destruct (le_gt_dec k a).
   replace (k+(S n + (a-k))) with (S n + a) by omega.
   destruct (le_gt_dec (S m) (S n + a)) as [le|gt]; 
     replace (k+(n+(a-k))) with (n+a) by omega.
    destruct (le_gt_dec m (n+a)) as [le'|gt]; [|omega].
     apply I.cons_morph; [apply tm_morph; [do 2 red; intros|reflexivity]|do 2 red; intros];
       (destruct (le_gt_dec k (m+a0)) as [le''|gt]; [|omega]);
       (replace (k+(1+(m+a0-k))) with (S m + a0); [reflexivity|omega]).

    destruct (le_gt_dec m (n+a)) as [le|gt']; [omega|].
     destruct (le_gt_dec k (n+a)) as [le|gt'']; [|omega].
      replace (k+(1+(n+a-k))) with (S n + a); [reflexivity|omega].
      
   destruct (le_gt_dec (S m) a) as [le|gt]; [omega|].
    destruct (le_gt_dec m a) as [le|gt']; [omega|reflexivity].
Qed.
 
Lemma subst_lift_lt : forall m n t u,
  m <= n ->
  eq_trm (subst_rec t m (lift (S n) u)) (lift n u).
intros; apply eq_trm_intro; simpl; intros; [| |destruct u; simpl; trivial].
 unfold lift. rewrite int_subst_rec_eq. do 2 rewrite int_lift_rec_eq.
 do 2 rewrite V.lams0. unfold V.lams, V.shift; simpl.
 apply int_morph; [do 2 red; intros|reflexivity].
  destruct (le_gt_dec m (S (n + a))) as [le|gt]; [|omega].
  destruct m; simpl; [reflexivity|].
   case_eq (n + a - m); intros; simpl; 
     [|replace (S (m + n0)) with (n + a); [reflexivity|]]; omega.

 unfold lift. rewrite tm_subst_rec_eq. do 2 rewrite tm_lift_rec_eq.
 do 2 rewrite I.lams0. unfold I.lams, I.shift; simpl.
 apply tm_morph; [do 2 red; intros|reflexivity].
  destruct (le_gt_dec m (S (n + a))) as [le|gt]; [|omega].
  destruct m; simpl; [reflexivity|].
   case_eq (n + a - m); intros; simpl; 
     [|replace (S (m + n0)) with (n + a); [reflexivity|]]; omega.
Qed.

Lemma subst0_lift : forall A n,
  eq_trm (subst (Ref 0) (lift_rec (S n) 1 A)) (lift_rec n 1 A).
 intros A n; apply eq_trm_intro.
  red; intros i0. rewrite <- int_subst_eq. do 2 rewrite int_lift_rec_eq; simpl.
  assert (eq_val (V.cons (i0 0) (V.shift 1 i0)) i0).
   apply V.cons_ext; reflexivity. rewrite <- H at 3. 
  rewrite <- V.cons_lams; [|do 2 red; intros; rewrite H0; reflexivity].
  rewrite <- V.cons_lams; [|do 2 red; intros; rewrite H0; reflexivity].
  do 2 rewrite V.lams0. rewrite V.shift_split; reflexivity.

  intros j0. rewrite tm_lift_rec_eq. rewrite tm_subst_eq; simpl.
  rewrite <-tm_subst_cons. rewrite tm_lift_rec_eq.
  assert (Lc.eq_intt (I.cons (j0 0) (I.shift 1 j0)) j0).
   apply I.cons_ext; reflexivity. rewrite <- H at 3. 
  rewrite <- I.cons_lams; [|do 2 red; intros; rewrite H0; reflexivity].
  rewrite <- I.cons_lams; [|do 2 red; intros; rewrite H0; reflexivity].
  do 2 rewrite I.lams0. rewrite I.shift_split; trivial.

  destruct A; simpl; trivial.
Qed.

Lemma eq_trm_lift_ref_bd : forall n i k,
  k > i ->
  eq_trm (lift_rec n k (Ref i)) (Ref i).
intros; simpl; split; red; intros.
 unfold V.lams, V.shift. destruct (le_gt_dec k i); [omega|apply H0].

 unfold I.lams, I.shift. destruct (le_gt_dec k i); [omega|apply H0].
Qed.

Definition closed_trm t := forall i1 i2, int i1 t == int i2 t.

(***************************************************************************************)
(*This following lemmas should be put in GenRealSN*)
(***************************************************************************************)

Lemma red_typ : forall e i j M T,
  val_ok e i j -> typ e M T -> T <> None ->
  M <> None /\ [int i M, tm j M] \real int i T.
intros e i j M T val_ok_e typ_M some_T.
red in typ_M; specialize typ_M with (1:=val_ok_e).
destruct typ_M as (some_M, hyp).
split; trivial.
 destruct T; trivial.
  elim some_T; trivial.
Qed.

Lemma real_morph : forall x y u v A B,
  x == y ->
  A == B ->
  u = v ->
  ([x, u] \real A <-> [y, v] \real B).
split; intros; destruct H2; unfold inX in H2.
 split; [unfold inX | rewrite <- H1]; rewrite <- H, <- H0; trivial.

 split; [unfold inX | rewrite H1]; rewrite H, H0; trivial.
Qed.

Lemma typ_subst : forall A B C D e,
  A <> kind ->
  C <> kind ->
  typ (A::e) B (lift 1 C) ->
  typ e D A ->
  typ e (subst D B) C.
red; intros A B C D e HA HC HB HD i j Hok.
apply red_typ with (1:=Hok) in HD; [destruct HD as (_, HD)|trivial].
assert (val_ok (A::e) (V.cons (int i D) i) (I.cons (tm j D) j)) by
  (apply vcons_add_var; trivial).
apply red_typ with (1:=H) in HB; 
  [destruct HB as (HSB, HB)|destruct C; [discriminate|trivial]].
apply in_int_intro; [|destruct B; [discriminate|]|]; trivial.
revert HB; apply real_morph.
 rewrite int_subst_eq; reflexivity.

 rewrite int_cons_lift_eq; reflexivity.

 rewrite tm_subst_eq; rewrite tm_subst_cons; trivial.
Qed.

Lemma weakening_bind : forall A B e C D,
  typ (C :: e) A D ->
  typ ((lift 1 C) :: B :: e) (lift_rec 1 1 A) (lift_rec 1 1 D).
red; intros A B e C D HA i j Hok.
assert (val_ok (C :: e) (V.lams 1 (V.shift 1) i) (I.lams 1 (I.shift 1) j)).
 red in Hok |- *; intros. destruct n.
  simpl in H. injection H; clear H; intros H; subst T.
  assert (value (lift 1 C) = value (lift 1 C)) by trivial.
  specialize Hok with (n:=0) (T:=(lift 1 C)) (1:=H). clear H.
  destruct C; destruct Hok as (_, Hok). 
   do 4 red in Hok. split; [discriminate|do 2 red].
   simpl int in Hok |- *. simpl tm in Hok |- *.
   do 2 rewrite V.lams0 in Hok. rewrite V.lams0. rewrite V.lams_shift. exact Hok.

   do 6 red in Hok. split; [discriminate|do 3 red; simpl tm; trivial].

  specialize Hok with (n:=(S (S n))) (T:=T) (1:=H); clear H.
  destruct Hok as (_, Hok). split; [discriminate|].
  destruct T; [do 2 red in Hok|-*|do 3 red in Hok |-*].
   simpl int in Hok |- *. simpl tm in Hok |- *.
   rewrite V.lams0 in Hok |- *. rewrite V.shift_split.
   rewrite V.lams_shift. do 2 rewrite <- V.shift_split.
   revert Hok; apply real_morph; [|reflexivity|].
    unfold V.lams, V.shift; simpl.
    replace (n-0) with n; [reflexivity|omega].

    unfold I.lams, I.shift; simpl.
    replace (n-0) with n; [reflexivity|omega].

   rewrite kind_ok_lift with (k:=0).
   rewrite eq_trm_lift_ref_fv; [|omega]. 
   unfold I.lams, I.shift; simpl in Hok |- *.
   replace (n-0) with n; [trivial|omega].

red in HA. specialize HA with (1:=H). clear H.
destruct HA as (HSA, HA). 
split; [case_eq A; intros; [discriminate|contradiction]|clear HSA].
destruct D; rewrite tm_lift_rec_eq; 
  [red; do 2 rewrite int_lift_rec_eq|do 2 red; rewrite <- kind_ok_lift]; trivial.
Qed.


(***************************************************************************************)
(*This following definition should be in Lambda.v*)
(***************************************************************************************)
Definition closed_pure_trm t := forall k, ~ Lc.occur k t.


(***************************************************************************************)
(*This following lemma should be in SATnat.v.*)
(*For any natural number, there exists a closed realizer*)
(***************************************************************************************)
Require Import SATnat.

Import Sat.
Import ZFind_nat.

Lemma inSAT_n : forall n, n ∈ NAT -> exists t, inSAT t (cNAT n) /\ closed_pure_trm t.
intros. pattern n; apply NAT_ind; trivial; intros.
 destruct H2 as (t, (HinSAT, Hclsd)). 
 exists t; split; [revert HinSAT; apply fam_mrph; rewrite <- H1; 
   [trivial|reflexivity]|]; trivial.

 exists ZE. split; [apply cNAT_ZE|unfold closed_pure_trm].
  intros k HF. inversion_clear HF. inversion_clear H0. inversion_clear H1.

 destruct H1 as (t, (HinSAT, Hclsd)); exists (Lc.App SU t). 
 split; [apply cNAT_SU; trivial|unfold closed_pure_trm in Hclsd |- *].
  intros k HF. inversion_clear HF.
   inversion_clear H1. inversion_clear H2. inversion_clear H1. inversion_clear H2.
    inversion_clear H1; inversion_clear H2.

    inversion_clear H1; inversion_clear H2; inversion_clear H1.
    
   apply Hclsd in H1; trivial.
Qed.