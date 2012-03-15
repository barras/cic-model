Require Import Lambda.
Require Import ZF ZFpairs ZFnats ZFord.
Require Import Sat.
Require Import Setoid Compare_dec Wf_nat.

(* building the set of lambda-terms with constants *)

Module Lam.
Section LambdaTerms.

  Variable A : set.

  Definition LAMf (X:set) :=
    union2
     (union2
       (replf N (fun n => couple zero n))
       (replf A (fun x => couple (succ zero) x)))
     (union2
       (replf (prodcart X X) (fun p => couple (succ (succ zero)) p))
       (replf X (fun x => couple (succ (succ (succ zero))) x))).

Instance LAMf_mono : Proper (incl_set ==> incl_set) LAMf.
do 2 red; intros.
unfold LAMf.
do 2 apply union2_mono.
 red; auto.

 red; auto.

 apply replf_mono2.
  do 2 red; intros.
  rewrite H1; reflexivity.

  apply prodcart_mono; trivial.

 apply replf_mono2; trivial.
 do 2 red; intros.
 rewrite H1; reflexivity.
Qed.

Instance LAMf_morph : Proper (eq_set ==> eq_set) LAMf.
do 2 red; intros.
apply eq_intro; intros.
 apply (LAMf_mono x y); trivial. 
 red; intros.
 rewrite <- H; auto.

 apply (LAMf_mono y x); trivial. 
 red; intros.
 rewrite H; auto.
Qed.

  Definition Var n := couple zero n.
  Definition Cst x := couple (succ zero) x.
  Definition App a b := couple (succ (succ zero)) (couple a b).
  Definition Abs a := couple (succ (succ (succ zero))) a.

  Lemma LAMf_ind : forall X (P : set -> Prop),
    Proper (eq_set ==> iff) P ->
    (forall n, n \in N -> P (Var n)) ->
    (forall x, x \in A -> P (Cst x)) ->
    (forall a b, a \in X -> b \in X -> P (App a b)) ->
    (forall a, a \in X -> P (Abs a)) ->
    forall a, a \in LAMf X -> P a.
unfold LAMf; intros.
apply union2_elim in H4; destruct H4 as [H4|H4];
 apply union2_elim in H4; destruct H4.
  apply replf_elim in H4.
   destruct H4.
   rewrite H5; auto.

   do 2 red; intros.
   rewrite H6; reflexivity.

  apply replf_elim in H4.
   destruct H4.
   rewrite H5; auto.

   do 2 red; intros.
   rewrite H6; reflexivity.

  apply replf_elim in H4.
   destruct H4.
   specialize surj_pair with (1:=H4); intro.
   rewrite H5; rewrite H6.
   apply H2.
    apply fst_typ with X; trivial.
    apply snd_typ with X; trivial.

   do 2 red; intros.
   rewrite H6; reflexivity.

  apply replf_elim in H4.
   destruct H4.
   rewrite H5; auto.

   do 2 red; intros.
   rewrite H6; reflexivity.
Qed.

  Lemma Var_typ : forall X n,
    n \in N -> Var n \in LAMf X.
intros.
unfold Var, LAMf.
apply union2_intro1; apply union2_intro1; apply replf_intro with n; auto.
 do 2 red; intros.
 rewrite H1; reflexivity.

 reflexivity.
Qed.

  Lemma Cst_typ : forall X x,
    x \in A -> Cst x \in LAMf X.
intros.
unfold Cst, LAMf.
apply union2_intro1; apply union2_intro2; apply replf_intro with x; auto.
 do 2 red; intros.
 rewrite H1; reflexivity.

 reflexivity.
Qed.

  Lemma App_typ : forall X a b,
    a \in X -> b \in X -> App a b \in LAMf X.
intros.
unfold App, LAMf.
apply union2_intro2; apply union2_intro1; apply replf_intro with (couple a b); auto.
 do 2 red; intros.
 rewrite H2; reflexivity.

 apply couple_intro; trivial.

 reflexivity.
Qed.

  Lemma Abs_typ : forall X a,
    a \in X -> Abs a \in LAMf X.
intros.
unfold Abs, LAMf.
apply union2_intro2; apply union2_intro2; apply replf_intro with a; auto.
 do 2 red; intros.
 rewrite H1; reflexivity.

 reflexivity.
Qed.


Require Import ZFrepl ZFfix.

  Definition Lamn n := TI LAMf (nat2ordset n).

  Lemma Lamn_incl_succ : forall k, Lamn k \incl Lamn (S k).
unfold Lamn; simpl; intros.
apply TI_incl; auto with *.
Qed.

  Lemma Lamn_eq : forall k, Lamn (S k) == LAMf (Lamn k).
unfold Lamn; simpl; intros.
apply TI_mono_succ; auto with *.
Qed.

  Lemma Lamn_incl : forall k k', k <= k' -> Lamn k \incl Lamn k'.
induction 1; intros.
 red; auto.
 red; intros.
 apply (Lamn_incl_succ m z); auto.
Qed.

  Definition Lambda := TI LAMf omega.

  Lemma Lambda_intro : forall k, Lamn k \incl Lambda.
unfold Lambda, Lamn; intros.
apply TI_incl; auto with *.
apply isOrd_sup_intro with (S k); simpl; auto.
apply lt_osucc; auto.
Qed.

  Lemma Lambda_elim : forall x,
    x \in Lambda -> exists k, x \in Lamn k.
unfold Lambda, Lamn; intros.
apply TI_elim in H; auto with *.
destruct H.
apply isOrd_sup_elim in H; destruct H.
exists x1.
apply TI_intro with x0; auto with *.
Qed.

  Lemma Lamn_case : forall k (P : set -> Prop),
    Proper (eq_set ==> iff) P ->
    (forall n, n \in N -> P (Var n)) ->
    (forall x, x \in A -> P (Cst x)) ->
    (forall a b k', k' < k -> a \in Lamn k' -> b \in Lamn k' -> P (App a b)) ->
    (forall a k', k' < k -> a \in Lamn k' -> P (Abs a)) ->
    forall a, a \in Lamn k -> P a.
destruct k; intros.
 unfold Lamn in H4.
 rewrite TI_initial in H4; auto with *.
 elim empty_ax with (1:=H4).

 rewrite Lamn_eq in H4.
 elim H4 using LAMf_ind; eauto.
Qed.


  Lemma Lambda_fix : forall (P:set->Prop),
    (forall k,
     (forall k' x, k' < k -> x \in Lamn k' -> P x) ->
     (forall x, x \in Lamn k -> P x)) ->
    forall x, x \in Lambda -> P x.
intros.
apply Lambda_elim in H0; destruct H0.
revert x H0.
elim (lt_wf x0); intros.
eauto.
Qed.

  Lemma Lambda_ind : forall P : set -> Prop,
    Proper (eq_set ==> iff) P ->
    (forall n, n \in N -> P (Var n)) ->
    (forall x, x \in A -> P (Cst x)) ->
    (forall a b, a \in Lambda -> b \in Lambda -> P a -> P b -> P (App a b)) ->
    (forall a, a \in Lambda -> P a -> P (Abs a)) ->
    forall a, a \in Lambda -> P a.
intros.
elim H4 using Lambda_fix; intros.
elim H6 using Lamn_case; intros; eauto.
 apply H2; eauto.
  apply Lambda_intro in H8; trivial.
  apply Lambda_intro in H9; trivial.
 apply H3; eauto.
  apply Lambda_intro in H8; trivial.
Qed.
 

  Lemma Lambda_eqn : Lambda == LAMf Lambda.
apply eq_intro; intros.
 apply Lambda_elim in H; destruct H.
 apply Lamn_incl_succ in H.
 rewrite Lamn_eq in H.
 eapply LAMf_mono with (Lamn x); trivial.
 apply Lambda_intro.

 elim H using LAMf_ind; intros.
  do 2 red; intros.
  rewrite H0; reflexivity.

  apply Lambda_intro with 1; rewrite Lamn_eq.
  apply Var_typ; trivial.

  apply Lambda_intro with 1; rewrite Lamn_eq.
  apply Cst_typ; trivial.

  apply Lambda_elim in H0; destruct H0 as (k,H0).
  apply Lambda_elim in H1; destruct H1 as (k',H1).
  destruct (le_gt_dec k k').
   assert (Lamn k \incl Lamn k').
    apply Lamn_incl; trivial.
   apply Lambda_intro with (S k'); rewrite Lamn_eq.
   apply App_typ; auto.

   assert (Lamn k' \incl Lamn k).
    apply Lamn_incl; auto with arith.
   apply Lambda_intro with (S k); rewrite Lamn_eq.
   apply App_typ; auto.

  apply Lambda_elim in H0; destruct H0 as (k,H0).
  apply Lambda_intro with (S k); rewrite Lamn_eq.
  apply Abs_typ; auto.
Qed.

  Lemma Var_typ0 : forall n,
    n \in N -> Var n \in Lambda.
intros.
rewrite Lambda_eqn; apply Var_typ; trivial.
Qed.

  Lemma Cst_typ0 : forall x,
    x \in A -> Cst x \in Lambda.
intros.
rewrite Lambda_eqn; apply Cst_typ; trivial.
Qed.

  Lemma App_typ0 : forall a b,
    a \in Lambda -> b \in Lambda -> App a b \in Lambda.
intros.
rewrite Lambda_eqn; apply App_typ; trivial.
Qed.

  Lemma Abs_typ0 : forall a,
    a \in Lambda -> Abs a \in Lambda.
intros.
rewrite Lambda_eqn; apply Abs_typ; trivial.
Qed.

End LambdaTerms.
End Lam.

Import Lam.
Import Lambda.

Definition CCLam := Lambda zero.

Fixpoint iLAM (t:term) :=
  match t with
  | Ref n => Lam.Var (nat2set n)
  | Abs M => Lam.Abs (iLAM M)
  | App u v => Lam.App (iLAM u) (iLAM v)
  end.

Lemma iLAM_typ : forall t, iLAM t \in CCLam.
unfold CCLam; induction t; try destruct s; simpl;
 repeat
  (apply Var_typ0 || apply Cst_typ0 || apply App_typ0 || apply Abs_typ0 ||
   (apply succ_intro1; reflexivity) || apply succ_intro2 || apply nat2set_typ);
 trivial.
Qed. 

Ltac inj_pre H :=
  unfold Var, Cst, Lam.App, Lam.Abs in H;
  change (succ (succ (succ zero))) with (nat2set 3) in H;
  change (succ (succ zero)) with (nat2set 2) in H;
  change (succ zero) with (nat2set 1) in H;
  change zero with (nat2set 0) in H.

Ltac inj_lam H :=
  (apply nat2set_inj in H; try discriminate H) ||
  (apply couple_injection in H;
   let H2 := fresh "H" in
   destruct H as (H,H2); inj_lam H; inj_lam H2) ||
  idtac.

Ltac injl H := inj_pre H; inj_lam H.

Lemma iLAM_inj : forall t u,
  iLAM t == iLAM u -> t=u.
fix IH 1.
destruct t; destruct u; simpl;
  intro H; trivial; injl H.
 rewrite H0; trivial.

 rewrite (IH _ _ H0); trivial.

 rewrite (IH _ _ H0); rewrite (IH _ _ H1); trivial.
Qed.


Lemma interSAT_ax : forall A F u,
    A ->
    ((forall x:A, inSAT u (F x)) <->
     inSAT u (interSAT F)).
split; intros.
 apply interSAT_intro; auto.
 apply interSAT_elim; trivial.
Qed.


Definition iSAT S :=
  subset CCLam (fun x => exists2 t, inSAT t S & x == iLAM t).

Instance iSAT_morph : Proper (eqSAT ==> eq_set) iSAT.
do 2 red; intros.
rewrite eqSAT_def in H.
unfold iSAT.
apply subset_ext; intros.
 apply subset_intro; trivial.
 destruct H1.
 exists x1; trivial.
 rewrite H; trivial.

 apply subset_elim1 in H0; trivial.

 apply subset_elim2 in H0.
 destruct H0.
 destruct H1.
 exists x1; trivial.
 exists x2; trivial.
 rewrite <- H; trivial.
Qed.

Definition complSAT (P:term->Prop) :=
  interSAT (fun p:{S|forall t, sn t -> P t -> inSAT t S} => proj1_sig p).

Definition sSAT x :=
  complSAT (fun t => iLAM t \in x).

Instance sSAT_morph : Proper (eq_set ==> eqSAT) sSAT.
do 2 red; intros.
unfold sSAT, complSAT.
apply interSAT_morph_subset; simpl; intros.
 split; intros.
  rewrite <- H in H2; auto.
  rewrite H in H2; auto.

 reflexivity.
Qed.

Lemma iSAT_id : forall S, eqSAT (sSAT (iSAT S)) S.
intros.
rewrite eqSAT_def.
unfold sSAT, complSAT.
intros.
rewrite <- interSAT_ax.
split; intros.
 assert (forall t, sn t -> iLAM t \in iSAT S -> inSAT t S).
  intros.
  unfold iSAT in H1.
  rewrite subset_ax in H1.
  destruct H1 as (_,(x,eq_x,(u,inS,eq_u))).
  rewrite eq_u in eq_x; apply iLAM_inj in eq_x.
  rewrite eq_x; trivial.
 exact (H (exist _ S H0)). 

 destruct x; simpl.
 apply i.
  apply sat_sn in H; trivial.

  unfold iSAT.
  apply subset_intro.
   apply iLAM_typ.

   exists t; trivial; reflexivity.

 exists snSAT; intros.
 apply snSAT_intro; trivial.
Qed.


Definition replSAT F :=
  repl (power CCLam) (fun P y => y == F (sSAT P)).

Lemma replSAT_ax : forall f z,
  Proper (eqSAT ==> eq_set) f ->
  (z \in replSAT f <-> exists A, z == f A).
unfold replSAT.
intros.
rewrite repl_ax.
 split; intros.
  destruct H0 as (y,isSet,(z',eq_z,img)).
  rewrite <- eq_z in img; exists (sSAT y); trivial.

  destruct H0.
  exists (iSAT x).
   apply power_intro; intros.
   unfold iSAT in H1.
   apply subset_elim1 in H1; trivial.

   exists z; try reflexivity.
   rewrite iSAT_id; trivial.

 intros.
 rewrite H1; rewrite H2.
 rewrite H3; reflexivity.
Qed.


 