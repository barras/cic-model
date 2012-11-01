Require Import AbsTheorySem.
Require Import SN_NAT.

Import GenLemmas.
Import SN_CC_Real.
Import ZF SN CCSN.
Import ZFind_nat Sat SATnat SN_NAT.

(*Instantiate the semantic of First Order Theory with Presburger*)
Module PSemSig <: AbsSemSig.

(*Presburger is the uni-sort theroy*)
Definition sort := Nat.

Lemma sort_not_kind : sort <> kind.
Proof. discriminate. Qed.

Lemma typ_sort : forall e, typ e sort kind.
Proof. apply typ_N. Qed.

Lemma sort_clsd : 
  (forall n k, eq_trm (lift_rec n k sort) sort) /\
  (forall t k, eq_trm (subst_rec t k sort) sort).
Proof. split; intros; simpl; split; red; reflexivity. Qed.

Definition wf_clsd_env e := forall i j, val_ok e i j ->
  exists j', val_ok e i j' /\ (forall n, closed_pure_trm (j' n)).

Definition prf_T : trm.
left. 
exists (fun _ => lam props (fun x => lam x (fun y => y)))
  (fun _ => Lc.Abs (Lc.Abs (Lc.Ref 0))).
do 2 red; intros. reflexivity.

do 2 red; intros. reflexivity.

red; intros. reflexivity.

red; intros. reflexivity.

Defined.

Lemma Tprf : forall i j, 
  [int i prf_T, tm j prf_T] \real prod props (fun x => prod x (fun _ => x)).
intros. simpl int; simpl tm.
apply prod_intro_lam.
 do 2 red; intros. apply lam_ext; [|do 2 red; intros]; trivial.

 do 2 red; intros. apply prod_ext; [|do 2 red; intros]; trivial.

 apply Lc.sn_abs. apply Lc.sn_var.

 intros. unfold Lc.subst. simpl Lc.subst_rec.
 apply prod_intro_lam.
  do 2 red; intros; trivial.

  do 2 red; intros; reflexivity.

  apply Lc.sn_var. 
  
  intros. unfold Lc.subst; simpl Lc.subst_rec.
  rewrite Lc.lift0; trivial.
Qed.

Lemma FprfF : forall i j v,
  (forall n : nat, closed_pure_trm (j n)) ->
  [int i v, tm j v] \real prod props (fun p => p) -> False.
intros i j v Hclsd Hv.
assert (forall S, inSAT (Lc.App (tm j v) (Lc.Abs (Lc.Ref 0))) S) as HF.
 intros.
 assert ([mkProp S, Lc.Abs (Lc.Ref 0)] \real props).
  assert (mkProp S ∈ El props).
   rewrite El_props_def. exists S. reflexivity.
  split; trivial.
   rewrite Real_sort; trivial. apply Lc.sn_abs; apply Lc.sn_var.

 apply SN.prod_elim with (x:=mkProp S) (u:=Lc.Abs (Lc.Ref 0)) in Hv; trivial.
  destruct Hv. rewrite Real_mkProp in H1; trivial.
  unfold inX, mkProp at 2 in H0. rewrite El_def in H0.
  apply singl_elim in H0; trivial.
  
  do 2 red; intros; trivial.

 destruct (neutral_not_closed _ HF).
 inversion_clear H.
  apply tm_closed in H0. unfold closed_pure_trm in Hclsd.
    apply False_ind. apply H0. intros. apply Hclsd.

    inversion_clear H0. inversion_clear H.
Qed.


Definition P1 := (lam (mkTY NAT cNAT) (fun x => 
    NATREC (prod props (fun p => prod p (fun p1 => p))) 
    (fun _ _ => prod props (fun p => p)) x)).

Lemma P1_real : [P1, Lc.K]\real prod (mkTY NAT cNAT) (fun _ : X => props).
assert (forall x, x ∈ NAT -> 
  NATREC (prod props (fun p : set => prod p (fun _ : set => p)))
  (fun _ _ : set => prod props (fun p : set => p)) x ∈ El props).
 intros; change (El props) with ((fun _ => El props) x).
  apply NATREC_typ; [do 2 red; reflexivity|do 3 red; reflexivity|trivial| |intros].
   apply impredicative_prod.
    do 2 red; intros; apply prod_ext; [|do 2 red]; trivial.

    intros; apply impredicative_prod; [do 2 red; reflexivity|trivial].

   apply impredicative_prod; [do 2 red |]; trivial.

apply prod_intro_lam.
 do 2 red; intros; apply NATREC_morph; [reflexivity|do 3 red; reflexivity|trivial].
 
 do 2 red; reflexivity.

 apply Lc.sn_abs; apply Lc.sn_var.

 intros; destruct H0 as (Hx, Hu); unfold inX in Hx; rewrite El_def in Hx; split.
  unfold inX; apply H; trivial.

  unfold Lc.subst; simpl Lc.subst_rec. rewrite Real_sort; [clear H|apply H; trivial].
   apply Lc.sn_abs; apply Lc.sn_lift; apply sat_sn in Hu; trivial.
Qed.

Definition P1t : trm.
left. exists (fun _ => P1) (fun _ => Lc.K).
do 2 red; intros. reflexivity.

do 2 red; intros. reflexivity.

red; intros. reflexivity.

red; intros. reflexivity.
Defined.

Lemma P1_ZERO : app P1 ZERO == prod props (fun p => prod p (fun p1 => p)).
unfold P1. rewrite beta_eq.
 rewrite NATREC_0; reflexivity.

 do 2 red; intros. apply NATREC_morph; [reflexivity|do 3 red; intros; reflexivity|trivial].

 rewrite El_def. apply ZERO_typ.
Qed.

Lemma P1_SUCC : forall n, n ∈ NAT -> app P1 (SUCC n) == prod props (fun p => p).
unfold P1; intros; rewrite beta_eq.
 rewrite NATREC_S; [reflexivity|do 3 red; reflexivity|trivial].

 do 2 red; intros; apply NATREC_morph; [reflexivity|do 3 red; reflexivity|trivial].

 rewrite El_def; apply SUCC_typ; trivial.
Qed.


Definition P2 := (lam (mkTY NAT cNAT) (fun x => 
    NATREC (prod props (fun p => p)) 
    (fun _ _ => prod props (fun p => prod p (fun p1 => p))) x)).

Lemma P2_real : [P2, Lc.K]\real prod (mkTY NAT cNAT) (fun _ : X => props).
assert (forall x, x ∈ NAT -> 
  NATREC (prod props (fun p : set => p))
  (fun _ _ : set => prod props (fun p : set => prod p (fun _ : set => p))) x ∈ El props).
 intros; change (El props) with ((fun _ => El props) x).
  apply NATREC_typ; [do 2 red; reflexivity|do 3 red; reflexivity|trivial| |intros].
   apply impredicative_prod; [do 2 red |]; trivial.

   apply impredicative_prod; [do 2 red|]; intros.
    apply prod_ext; [|do 2 red]; trivial.

    apply impredicative_prod; [do 2 red; reflexivity|trivial].

apply prod_intro_lam.
 do 2 red; intros; apply NATREC_morph; [reflexivity|do 3 red; reflexivity|trivial].
 
 do 2 red; reflexivity.

 apply Lc.sn_abs; apply Lc.sn_var.

 intros; destruct H0 as (Hx, Hu); unfold inX in Hx; rewrite El_def in Hx; split.
  unfold inX; apply H; trivial.

  unfold Lc.subst; simpl Lc.subst_rec. rewrite Real_sort; [clear H|apply H; trivial].
   apply Lc.sn_abs; apply Lc.sn_lift; apply sat_sn in Hu; trivial.
Qed.

Definition P2t : trm.
left. exists (fun _ => P2) (fun _ => Lc.K).
do 2 red; intros. reflexivity.

do 2 red; intros. reflexivity.

red; intros. reflexivity.

red; intros. reflexivity.
Defined.


Lemma P2_SUCC : forall n, n ∈ NAT -> 
  app P2 (SUCC n) == prod props (fun p => prod p (fun p1 => p)).
intros; unfold P2; rewrite beta_eq.
 rewrite NATREC_S; [reflexivity|do 3 red; reflexivity|trivial].

 do 2 red; intros. apply NATREC_morph; [reflexivity|do 3 red; intros; reflexivity|trivial].

 rewrite El_def. apply SUCC_typ; trivial.
Qed.

Lemma P2_ZERO : app P2 ZERO == prod props (fun p => p).
unfold P2; rewrite beta_eq.
 rewrite NATREC_0; reflexivity.

 do 2 red; intros; apply NATREC_morph; [reflexivity|do 3 red; reflexivity|trivial].

 rewrite El_def; apply ZERO_typ.
Qed.


Definition P3 x0 := (lam (mkTY NAT cNAT) (fun x => 
    NATREC (prod props (fun p => p)) (fun n _ => app x0 n) x)).

Lemma P3_morph : forall x y, x == y -> P3 x == P3 y.
intros. unfold P3. apply lam_ext; [reflexivity|do 2 red; intros].
 apply NATREC_morph; [reflexivity| |trivial].
  do 2 red; intros. rewrite H2; rewrite H; reflexivity.
Qed.

Definition P3t : trm -> trm.
intros P. left.
exists (fun i => P3 (int i P)) (fun j => tm j P).
do 3 red; intros. apply P3_morph; rewrite H; reflexivity.

do 2 red; intros. rewrite H. reflexivity.

destruct P. destruct i. simpl. apply itm_lift0.
red; intros. reflexivity.

destruct P. destruct i. simpl. apply itm_subst0.
red; intros. reflexivity.
Defined.

Lemma P3_real : forall x0 u, 
  [x0, u]\real prod (mkTY NAT cNAT) (fun _ : set => props) ->
  [P3 x0, u]\real prod (mkTY NAT cNAT) (fun _ : X => props).
intros. 
assert (forall x, x ∈ NAT ->  
  NATREC (prod props (fun p : set => p))
  (fun n _ : set => app x0 n) x ∈ El props).
 intros; change (El props) with ((fun _ => El props) x).
  apply NATREC_typ; [do 2 red; reflexivity|do 3 red; intros; rewrite H1; reflexivity
    |trivial| |intros].
   apply impredicative_prod; [do 2 red |]; trivial.

   specialize (inSAT_n k H1); intros H3. destruct H3 as (x1, (H3, _)).
   apply SN.prod_elim with (x:=k) (u:=x1) in H; [|do 2 red; intros; reflexivity|].
    destruct H as (H, _); unfold inX in H; trivial.

    split; [unfold inX; rewrite El_def|]; trivial.
     rewrite Real_def; [|apply fam_mrph|]; trivial.

apply prod_intro_sn; [|do 2 red; reflexivity|apply real_sn in H; trivial|].
 do 2 red; intros; apply NATREC_morph; [reflexivity
   |do 3 red; intros; rewrite H3; reflexivity|trivial].

 intros. assert (x ∈ NAT).
  destruct H1 as (H1, _). unfold inX in H1; rewrite El_def in H1; trivial.

 apply SN.prod_elim with (x:=x) (u:=u0) in H; [apply H0 in H2|do 2 red; reflexivity|trivial].
  split; [unfold inX|rewrite Real_sort; [apply real_sn in H|]]; trivial.
Qed.

Lemma P3_SUCC : forall n x0, 
  n ∈ NAT -> 
  app (P3 x0) (SUCC n) == app x0 n.
intros; unfold P3; rewrite beta_eq.
 rewrite NATREC_S; [reflexivity|do 3 red; intros; rewrite H0; reflexivity|trivial].

 do 2 red; intros. apply NATREC_morph; 
 [reflexivity|do 3 red; intros; rewrite H2; reflexivity|trivial].

 rewrite El_def. apply SUCC_typ; trivial.
Qed.

Lemma eq_SUCC_eq : forall m n x y,
  m ∈ NAT ->
  n ∈ NAT ->
  [x, y]\real prod (prod (mkTY NAT cNAT) (fun _ : X => props))
  (fun x0 : X => prod (app x0 (SUCC n)) (fun _ : X => app x0 (SUCC m))) ->
  [x, y]\real prod (prod (mkTY NAT cNAT) (fun _ : X => props))
  (fun x0 : X => prod (app x0 n) (fun _ : X => app x0 m)).
intros m n x y Hm Hn HS.

assert (forall m n, m ∈ NAT -> n ∈ NAT ->
prod (prod (mkTY NAT cNAT) (fun _ : X => props))
     (fun x0 : X => prod (app x0 n) (fun _ : X => app x0 m)) ∈ El props).
intros. apply impredicative_prod.
 do 2 red; intros. apply prod_ext; [|do 2 red; intros]; rewrite H2; reflexivity.

 intros; apply impredicative_prod.
  do 2 red; intros; reflexivity.

  apply prod_elim with (x:=m0) in H1; trivial.
   do 2 red; intros; reflexivity.
   
   rewrite El_def; trivial.

assert (prod (prod (mkTY NAT cNAT) (fun _ : X => props))
  (fun x0 : X => prod (app x0 (SUCC n)) (fun _ : X => app x0 (SUCC m))) ∈ El props).
apply H; apply SUCC_typ; trivial.

assert (prod (prod (mkTY NAT cNAT) (fun _ : X => props))
  (fun x0 : X => prod (app x0 n) (fun _ : X => app x0 m)) ∈ El props).
apply H; trivial.

rewrite El_props_def in H0, H1. destruct H0, H1.

assert ((lam (prod (mkTY NAT cNAT) (fun _ => props)) 
(fun x0 => lam (app x0 n) (fun x1 => app (app x (P3 x0)) x1))) ∈
El (prod (prod (mkTY NAT cNAT) (fun _ : X => props))
     (fun x0 : X => prod (app x0 n) (fun _ : X => app x0 m)))).
apply prod_intro.
 do 2 red; intros. apply lam_ext; [rewrite H3; reflexivity|do 2 red; intros; rewrite H5].
  apply app_ext; [|reflexivity].
   apply app_ext; [reflexivity|unfold P3].
    apply lam_ext; [reflexivity|do 2 red; intros].
     apply NATREC_morph;
       [reflexivity|do 2 red; intros; rewrite H3; rewrite H8; reflexivity|trivial].

 do 2 red; intros. apply prod_ext; [|do 2 red; intros]; rewrite H3; reflexivity.

 intros. apply prod_intro.
  do 2 red; intros. rewrite H4; reflexivity.

  do 2 red; intros. reflexivity.

  intros. destruct HS as (HS, _); unfold inX in HS.
  assert (P3 x2 ∈ El (prod (mkTY NAT cNAT) (fun _ : X => props))).
   unfold P3. apply prod_intro.
    do 2 red; intros. 
    apply NATREC_morph; [reflexivity|do 3 red; intros; rewrite H6; reflexivity|trivial].

    do 2 red; intros; reflexivity.

    intros. change (El props) with ((fun _ => El props) x4). apply NATREC_typ; intros.
     do 2 red; intros; reflexivity.

     do 3 red; intros. rewrite H5; reflexivity.

     rewrite El_def in H4; trivial.
    
     apply impredicative_prod; [do 2 red|]; trivial.

     apply prod_elim with (x:=k) in H2; 
       [|do 2 red; intros; reflexivity|rewrite El_def]; trivial.

  apply prod_elim with (x:=(P3 x2)) in HS; [|do 2 red; intros|trivial].
  2 : apply prod_ext; [|do 2 red; intros]; rewrite H6; reflexivity.
  assert (El (prod (app (P3 x2) (SUCC n)) (fun _ : X => app (P3 x2) (SUCC m))) ==
   El (prod (app x2 n) (fun _ : X => app x2 m))).
   apply El_morph; apply prod_ext; [|do 2 red; intros]; rewrite P3_SUCC; trivial; reflexivity.

  rewrite H5 in HS; clear H5.
  apply prod_elim with (x:=x3) in HS; trivial.
   do 2 red; intros; reflexivity.

assert (x == (lam (prod (mkTY NAT cNAT) (fun _ => props)) 
(fun x0 => lam (app x0 n) (fun x1 => app (app x (P3 x0)) x1)))).
 destruct HS as (HS, _); unfold inX in H1.
 rewrite H0 in HS; rewrite H1 in H2. rewrite El_mkProp in HS, H2.
 apply singl_elim in HS; apply singl_elim in H2. rewrite HS, H2; reflexivity.

assert ([lam (prod (mkTY NAT cNAT) (fun _ : set => props))
         (fun x0 : set => lam (app x0 n) (fun  x1 => app (app x (P3 x0)) x1)), y]\real
  prod (prod (mkTY NAT cNAT) (fun _ : X => props))
  (fun x2 : X => prod (app x2 n) (fun _ : X => app x2 m)) ->
  [x, y]\real prod (prod (mkTY NAT cNAT) (fun _ : X => props))
  (fun x2 : X => prod (app x2 n) (fun _ : X => app x2 m))).
apply real_morph; [trivial| |]; reflexivity.

apply H4. clear H0 x0 H x1 H1 H2 H3 H4.
apply prod_intro_sn.
 do 2 red; intros. apply lam_ext; [rewrite H0; reflexivity|do 2 red; intros].
  apply app_ext; trivial.
   apply app_ext; [reflexivity|].
    unfold P3. apply lam_ext; [reflexivity|do 2 red; intros].
     apply NATREC_morph; [reflexivity|do 3 red; intros; rewrite H0, H5; reflexivity|trivial].

 do 2 red; intros. apply prod_ext; [|do 2 red; intros]; rewrite H0; reflexivity.

 apply real_sn in HS; trivial.

 intros. apply prod_intro_sn.
  do 2 red; intros. rewrite H1; reflexivity. 
  
  do 2 red; intros. reflexivity.

  apply SN.prod_elim with (3:=H) in HS.
   apply real_sn in HS; trivial.

   do 2 red; intros. apply prod_ext; [|do 2 red; intros]; rewrite H1; reflexivity.

  intros. apply SN.prod_elim with (x:=P3 x0) (u:=u) in HS; [| |apply P3_real; trivial].
  2 : do 2 red; intros; apply prod_ext; [|do 2 red; intros]; rewrite H2; reflexivity.
   assert ([app x (P3 x0), GenRealSN.Lc.App y u]\real
       prod (app (P3 x0) (SUCC n)) (fun _ : X => app (P3 x0) (SUCC m)) ->
   [app x (P3 x0), GenRealSN.Lc.App y u]\real
       prod (app x0 n) (fun _ : X => app x0 m)).
    apply real_morph; [reflexivity| |reflexivity].
     apply prod_ext; [|do 2 red; intros]; rewrite <- P3_SUCC; trivial; reflexivity.
   
   apply H1 in HS. clear H1.
   apply SN.prod_elim with (x:=x1) (u:=u0) in HS; [|do 2 red; reflexivity|]; trivial.
Qed.


Lemma PredVary : forall e x y i j, 
  wf_clsd_env e ->
  typ e x sort ->
  typ e y sort ->
  val_ok e i j ->
  (exists j', val_ok e i j' /\ (forall n, closed_pure_trm (j' n)) /\
    (exists P, P <> kind /\ [int i P, tm j' P] \real int i (Prod sort prop) /\ 
      exists u, [int i u, tm j' u] \real (app (int i P) (int i x)) /\
        ((exists v, [int i v, tm j' v] \real (app (int i P) (int i y))) -> 
          int i x == int i y))).
intros e x y i j' Hclsd Hx Hy Hok'.
apply Hclsd in Hok'. clear Hclsd j'.
destruct Hok' as (j, (Hok, Hclsd)).
exists j; split; [|split]; trivial.
apply red_typ with (1:=Hok) in Hx; [|discriminate].
destruct Hx as (_, (Hx, _)); unfold inX in Hx; simpl in Hx; rewrite El_def in Hx.
apply red_typ with (1:=Hok) in Hy; [|discriminate].
destruct Hy as (_, (Hy, _)); unfold inX in Hy; simpl in Hy; rewrite El_def in Hy.

set (int_x := int i x) in *. clearbody int_x.
set (int_y := int i y) in *. clearbody int_y.
clear x y e Hok.

revert int_y Hy. pattern int_x; apply NAT_ind; trivial; intros.
 apply H1 in Hy; clear H1. destruct Hy as (P, (HSP, (HP, (u, (Hu, Hv))))).
 exists P; split; [|split]; trivial.
 exists u; split; rewrite <- H0; trivial.

 exists P1t. split; [discriminate|split].
  simpl int; simpl tm. apply P1_real.

  exists prf_T. simpl int; simpl tm.
  rewrite P1_ZERO. split; [apply Tprf with (i:=i) (j:=j)|].
  pattern int_y; apply NAT_ind; [intros|reflexivity|intros|trivial].
   rewrite H0 in H1; apply H1.
   destruct H2 as (v, Hv); exists v; rewrite H0; trivial.

   destruct H1 as (v, HF). rewrite P1_SUCC in HF; trivial.
   apply FprfF in HF; trivial. contradiction.

 pattern int_y; apply NAT_ind; trivial; intros.
  destruct H3 as (P, (HSP, (HP, (u, (Hu, Hv))))).
  exists P; split; [|split]; trivial.
  exists u; split; trivial; intros.
   rewrite <- H2; apply Hv. destruct H3 as (v, H3); exists v; rewrite H2; trivial.

  exists P2t. split; [discriminate|split].
   simpl int; simpl tm; apply P2_real; trivial.
   
   exists prf_T. simpl int; simpl tm.
   rewrite P2_SUCC; trivial. 
   split; [apply Tprf with (i:=i) (j:=j)|].
   intros. destruct H1 as (v, Hv). rewrite P2_ZERO in Hv.
   apply FprfF in Hv; [contradiction|trivial].

  specialize H0 with (1:=H1).
  destruct H0 as (P, (HSP, (HP, (u, (Hu, Hv))))).
  exists (P3t P). split; [discriminate|split].
   simpl int; simpl tm. apply P3_real; trivial.

   exists u; split; [simpl int; rewrite P3_SUCC; trivial|].
    intros. destruct H0 as (v, Hv'). 
    simpl int in Hv'; rewrite P3_SUCC in Hv'; trivial.
    assert (n == n0).
     apply Hv; exists v; trivial.
    rewrite H0; reflexivity.
Qed.

End PSemSig.


(************************************************************************************)
(*Semantic of axioms*)
(************************************************************************************)
Module PSemAx <: SemanticAx PSemSig.

Include SemLogic PSemSig.

Lemma typ_S1 : forall e n,
  typ e n Nat ->
  typ e (App Succ n) Nat.
intros e n Hn.
setoid_replace Nat with (subst n Nat) using relation eq_trm;
  [|simpl; split; red; reflexivity].
apply typ_app with (V:=Nat); [trivial|apply typ_S|discriminate|discriminate].
Qed.

Lemma int_S : forall n i, int i n ∈ NAT ->
  int i (App Succ n) == SUCC (int i n).
intros; simpl.
rewrite beta_eq; [reflexivity| |rewrite El_def; trivial].
 do 2 red; intros; rewrite H1; reflexivity.
Qed.

Definition Add := Abs Nat (Abs Nat (NatRec (Ref 1) (Abs Nat Succ) (Ref 0))).

Lemma typ_Add : forall e, typ e Add (Prod Nat (Prod Nat (lift 2 Nat))).
intros.
apply typ_abs; [left; apply typ_N| |discriminate].
apply typ_abs; [left; apply typ_N| |discriminate].
assert (forall n e, typ e n Nat ->
  eq_typ e (App (Abs Nat Nat) n) Nat).
 intros. setoid_replace Nat with (subst n Nat) using relation eq_trm at 3;
   [|simpl; split; red; reflexivity].
 apply eq_typ_beta; [apply refl|apply refl|trivial|discriminate].

setoid_replace (lift 2 Nat) with Nat using relation eq_trm;
  [|simpl; split; red; reflexivity].
apply typ_conv with (T := App (Abs Nat Nat) (Ref 0)); [|apply H|discriminate|discriminate].
 apply typ_Nrect.
  setoid_replace Nat with (lift 1 Nat) using relation eq_trm at 3;
    [apply typ_var; trivial|simpl; split; red; reflexivity].
  
  apply typ_conv with (T:=Nat); [| |discriminate|discriminate].
   setoid_replace Nat with (lift 2 Nat) using relation eq_trm at 3;
     [apply typ_var; trivial|simpl; split; red; reflexivity].

   apply sym. apply H. apply typ_0.

  apply typ_abs; [left; apply typ_N| |discriminate].
   apply typ_conv with (T:=Prod Nat (lift 1 Nat)); [apply typ_S| |discriminate|discriminate].
    apply sym. apply eq_typ_prod; [| |discriminate].
     unfold lift. rewrite red_lift_abs.
     setoid_replace (lift_rec 1 0 Nat) with Nat using relation eq_trm;
       [apply H|simpl; split; red; reflexivity].
      setoid_replace Nat with (lift 1 Nat) using relation eq_trm at 4;
        [apply typ_var; trivial|simpl; split; red; reflexivity].
      
     unfold lift at 2 3. rewrite red_lift_abs.
     setoid_replace (lift_rec 1 0 Nat) with Nat using relation eq_trm;
       [apply H; apply typ_S1|simpl; split; red; reflexivity].
      setoid_replace Nat with (lift 2 Nat) using relation eq_trm at 6;
        [apply typ_var; trivial|simpl; split; red; reflexivity].

 setoid_replace Nat with (lift 1 Nat) using relation eq_trm at 3;
   [apply typ_var; trivial|simpl; split; red; reflexivity].
Qed.

Lemma typ_Add2 : forall e m n,
  typ e m Nat ->
  typ e n Nat ->
  typ e (App (App Add m) n) Nat.
intros e m n Hm Hn.
setoid_replace Nat with (subst n Nat) using relation eq_trm;
  [|simpl; split; red; reflexivity].
apply typ_app with (V:=Nat); [trivial| |discriminate|discriminate].
setoid_replace (Prod Nat Nat) with (subst m (Prod Nat (lift 2 Nat))) using relation eq_trm;
  [|simpl; split; red; reflexivity].
apply typ_app with (V:=Nat); [trivial|apply typ_Add|discriminate|discriminate].
Qed.

Lemma int_Add : forall n m i M N,  
  int i m ∈ NAT ->
  int i n ∈ NAT ->
  int i m == M ->
  int i n == N ->
  int i (App (App Add m) n) == NATREC M (fun _ => SUCC) N.
intros n m i M N Him Hin Hm Hn.
replace (int i (App (App Add m) n)) with 
  (app (app (lam (mkTY NAT cNAT) (fun x => lam (mkTY NAT cNAT) (fun y => 
    (NATREC x (fun p q => 
      app (app (lam (mkTY NAT cNAT) (fun _ => lam (mkTY NAT cNAT) SUCC)) p) q) y))))
  (int i m)) (int i n)) by reflexivity.
rewrite beta_eq; [  
  |do 2 red; intros; apply lam_ext; [reflexivity|do 2 red; intros; apply NATREC_morph; [|
    do 3 red; intros; rewrite H3, H4; reflexivity|]; trivial]
  |rewrite El_def; trivial].
rewrite beta_eq; [
  |do 2 red; intros; apply NATREC_morph; [reflexivity
    |do 3 red; intros; rewrite H1, H2; reflexivity|trivial]
  |rewrite El_def; trivial].
assert (NATREC (int i m) (fun _ : set => SUCC) (int i n) ==
  NATREC M (fun _ : set => SUCC) N).
 apply NATREC_morph; [|do 3 red; intros; rewrite H0; reflexivity|]; trivial.
rewrite <- H; clear H.

pattern (int i n); apply NAT_ind; [|do 2 rewrite NATREC_0; reflexivity| |trivial]; intros.
 assert (NATREC (int i m) (fun _ : set => SUCC) x == 
   NATREC (int i m) (fun _ : set => SUCC) x').
  apply NATREC_morph; [reflexivity|do 3 red; intros; rewrite H3; reflexivity|trivial].

 rewrite H2 in H1; rewrite <- H1; clear H2. 
 apply NATREC_morph; [reflexivity
   |do 3 red; intros; apply app_ext; [apply app_ext; [reflexivity|]|]; trivial 
   |rewrite H0; reflexivity].
 
 rewrite NATREC_S; [|do 3 red; intros; rewrite H1, H2; reflexivity|trivial].
 rewrite NATREC_S; [|do 3 red; intros; rewrite H2; reflexivity|trivial].
 rewrite beta_eq; [rewrite H0|do 2 red; reflexivity|rewrite El_def; trivial].
 rewrite beta_eq; [reflexivity|do 2 red; intros; rewrite H2; reflexivity
   |rewrite El_def; change NAT with ((fun _ => NAT) n0)].
  apply NATREC_typ; [do 2 red; reflexivity|do 3 red; intros; rewrite H2; reflexivity| |
    |intros; apply SUCC_typ]; trivial.
Qed.

(*Axiom1 : ~ S n = 0*)
Definition ax1_aux := Abs Nat (NatRec True_symb (Abs Nat (Abs prop False_symb)) (Ref 0)).

Lemma P_ax1_aux : forall e, typ e ax1_aux (Prod Nat prop).
intros e. unfold ax1_aux.
assert (forall n e, typ e n Nat ->
  eq_typ e (App (Abs Nat prop) n) prop).
 intros. 
 setoid_replace prop with (subst n prop) using relation eq_trm at 2;
   [apply eq_typ_beta; [apply refl|apply refl|trivial|discriminate]
     |simpl; split; red; reflexivity].

apply typ_abs; [left; apply typ_N| |discriminate].
apply typ_conv with (T := App (Abs Nat prop) (Ref 0));
  [|apply H; setoid_replace Nat with (lift 1 Nat) using relation eq_trm at 2;
    [apply typ_var; trivial|simpl; split; red; reflexivity]
   |discriminate|discriminate].
apply typ_Nrect.
 setoid_replace Nat with (lift 1 Nat) using relation eq_trm at 2;
   [apply typ_var; trivial|simpl; split; red; reflexivity].

 apply typ_conv with (T:=prop); [apply True_symb_typ|apply sym; apply H; apply typ_0
   |discriminate|discriminate].

 apply typ_abs; [left; apply typ_N| |discriminate].
 apply typ_conv with (T:=Prod prop prop); [| |discriminate|discriminate].
  apply typ_abs; [left; apply typ_prop|apply False_symb_typ|discriminate].
  
  apply sym; apply eq_typ_prod; [| |discriminate].
   unfold lift; rewrite red_lift_abs.
   setoid_replace (lift_rec 1 0 Nat) with Nat using relation eq_trm;
     [|simpl; split; red; reflexivity].
   setoid_replace (lift_rec 1 1 prop) with prop using relation eq_trm;
     [apply H|simpl; split; red; reflexivity].
   setoid_replace Nat with (lift 1 Nat) using relation eq_trm at 3;
     [apply typ_var; trivial|simpl; split; red; reflexivity].

   unfold lift at 2; rewrite red_lift_abs.
    setoid_replace (lift_rec 2 0 Nat) with Nat using relation eq_trm;
      [|simpl; split; red; reflexivity].
    setoid_replace (lift_rec 2 1 prop) with prop using relation eq_trm;
      [apply H; apply typ_S1|simpl; split; red; reflexivity].
    setoid_replace Nat with (lift 2 Nat) using relation eq_trm at 4;
      [apply typ_var; trivial|simpl; split; red; reflexivity].
Qed.

Lemma ax1_aux_0 : forall e, eq_typ e True_symb (App ax1_aux Zero).
red; intros e i j Hok; simpl.
rewrite beta_eq; [rewrite NATREC_0; reflexivity| |rewrite El_def; apply ZERO_typ].
 do 2 red; intros. apply NATREC_morph; [reflexivity| |trivial].
  do 3 red; intros. apply app_ext; [apply app_ext|]; trivial.
   apply lam_ext; [|do 2 red; intros]; reflexivity.
Qed.

Lemma ax1_aux_S : forall e n, typ e n Nat -> 
  eq_typ e False_symb (App ax1_aux (App Succ n)).
red; intros e n Hn i j Hok.
apply red_typ with (1:=Hok) in Hn; [destruct Hn as (_, (Hn, _))|discriminate].
unfold inX in Hn; rewrite ElNat_eq in Hn.
generalize (True_symb_typ e); intros HT.
apply red_typ with (1:=Hok) in HT; [destruct HT as (_, (HT, _))|discriminate].
unfold inX in HT; simpl int in HT.
generalize (False_symb_typ e); intros HF.
apply red_typ with (1:=Hok) in HF; [destruct HF as (_, (HF, _))|discriminate].
unfold inX in HF; simpl int in HF.
replace (int i (App ax1_aux (App Succ n))) with 
  (app (lam (mkTY NAT cNAT) (fun x => NATREC (int (V.cons x i) True_symb) (fun p q =>
    app (app (lam (mkTY NAT cNAT) (fun y => lam props (fun z =>
      (int (V.cons z (V.cons y (V.cons x i))) False_symb)))) p) q) x))
  (int i (App Succ n))) by reflexivity.
rewrite int_S; [unfold ax1_aux; simpl int|trivial].
rewrite beta_eq; [
  |do 2 red; intros; apply NATREC_morph; [reflexivity
    |do 3 red; intros; apply app_ext; [apply app_ext; [reflexivity|]|]|]
  |rewrite El_def; apply SUCC_typ]; trivial.
rewrite NATREC_S; [
  |do 3 red; intros; apply app_ext; [apply app_ext; [reflexivity|]|]
  |]; trivial.
rewrite beta_eq;[|do 2 red; reflexivity|rewrite El_def; trivial].
rewrite beta_eq; [reflexivity|do 2 red; reflexivity
  |change (El props) with ((fun _ => El props) (int i n))].
apply NATREC_typ; [do 2 red; reflexivity
  |do 3 red; intros; apply app_ext; [apply app_ext; [reflexivity|]|]; trivial
  | | |intros]; trivial.
rewrite beta_eq; [|do 2 red; reflexivity|rewrite El_def; trivial].
rewrite beta_eq; [|do 2 red; reflexivity|]; trivial.
Qed.

Definition ax1 := forall e, exists t, 
  typ e t (Fall (Neg (EQ_trm Zero (App (App Add (Ref 0)) (App Succ Zero))))).

Lemma P_ax_intro1 : ax1.
unfold ax1. intros e.
generalize (True_symb_intro (EQ_trm Zero (App (App Add (Ref 0)) (App Succ Zero))::Nat::e)).
intros Ht; destruct Ht as (t, Ht).
exists (Abs Nat (Abs (EQ_trm Zero (App (App Add (Ref 0)) (App Succ Zero))) 
(App (App (Ref 0) ax1_aux) t))).
apply typ_abs; [left; apply typ_N|unfold Neg|discriminate].
apply Impl_intro; [|discriminate|].
 apply EQ_trm_typ; [apply typ_0|apply typ_Add2; [|apply typ_S1; apply typ_0]].
  setoid_replace Nat with (lift 1 Nat) using relation eq_trm at 2;
    [apply typ_var; trivial|simpl; split; red; reflexivity].

 setoid_replace (lift 1 False_symb) with (subst t False_symb) using relation eq_trm by
   (simpl; split; red; reflexivity).
 apply typ_app with (V:=True_symb); [trivial|clear Ht|discriminate|discriminate].
 apply typ_conv with (T:=(subst ax1_aux (Prod (App (Ref 0) (lift 2 Zero))
   (App (Ref 1) (lift 3 (App (App Add (Ref 0)) (App Succ Zero))))))); [
     | |discriminate|discriminate].
  apply typ_app with (V:=(Prod Nat prop)); [apply P_ax1_aux| |discriminate|discriminate].
   setoid_replace ((Prod (Prod Nat prop) (Prod (App (Ref 0) (lift 2 Zero))
     (App (Ref 1) (lift 3 (App (App Add (Ref 0)) (App Succ Zero))))))) with 
   (lift 1 ((Prod (Prod Nat prop) (Prod (App (Ref 0) (lift 1 Zero))
     (App (Ref 1) (lift 2 (App (App Add (Ref 0)) (App Succ Zero)))))))) 
   using relation eq_trm; [apply typ_var; trivial
     |unfold lift; do 3 rewrite red_lift_prod; do 11 rewrite red_lift_app].
   rewrite eq_trm_lift_ref_fv; [simpl plus|omega].
   rewrite eq_trm_lift_ref_bd; [|omega].
   rewrite eq_trm_lift_ref_bd; [|omega].
   rewrite eq_trm_lift_ref_fv; [simpl plus|omega].
   rewrite eq_trm_lift_ref_fv; [simpl plus|omega].
   rewrite lift_rec_acc; [simpl plus|omega].
   rewrite lift_rec_acc; [simpl plus|omega].
   rewrite lift_rec_acc; [simpl plus|omega].
   rewrite lift_rec_acc; [simpl plus|omega].
   fold (lift 3 Add). fold (lift 3 Succ). fold (lift 3 Zero). 
   apply Prod_morph; [apply Prod_morph; simpl; split; red|]; reflexivity.

  unfold subst. rewrite red_sigma_prod. do 2 rewrite red_sigma_app.
  rewrite red_sigma_var_eq; [rewrite lift0|discriminate].
  setoid_replace ((subst_rec ax1_aux 0 (lift 2 Zero))) with Zero using relation eq_trm;
    [|simpl; split; red; reflexivity].
  rewrite red_sigma_var_eq; [|discriminate].
  rewrite subst_lift_lt; [|omega].
  apply eq_typ_prod; [rewrite ax1_aux_0; apply refl| |discriminate].
  rewrite ax1_aux_S with (n:=(Ref 2)).
   apply eq_typ_app.
    unfold lift. unfold ax1_aux. rewrite red_lift_abs.
    apply eq_typ_abs; [| |discriminate].
     setoid_replace (lift_rec 1 0 Nat) with Nat using relation eq_trm;
       [apply refl|simpl; split; red; reflexivity].
     
     red; intros; simpl. apply NATREC_morph; [reflexivity| |reflexivity].
      do 3 red; intros. apply app_ext; [apply app_ext; [reflexivity|]|]; trivial.

     red; intros; unfold lift. red in H. 
     assert (nth_error (App ax1_aux Zero :: Prod (Prod Nat prop)
       (Prod (App (Ref 0) (lift 1 Zero)) (App (Ref 1)
         (lift 2 (App (App Add (Ref 0)) (App Succ Zero))))) :: Nat :: e) 2 = 
     value Nat) by trivial.
     specialize H with (1:=H0); clear H0.
     apply in_int_not_kind in H; [|discriminate].
     destruct H as (H, _); unfold inX in H; simpl in H. rewrite El_def in H.
     rewrite int_lift_rec_eq.
     assert (int (V.lams 0 (V.shift 2) i) (Ref 0) == i 2) by 
       (unfold V.lams, V.shift; simpl; reflexivity).
     assert (int (V.lams 0 (V.shift 2) i) (App Succ Zero) == SUCC ZERO) by
       (rewrite int_S; simpl; [reflexivity|apply ZERO_typ]).
     rewrite int_Add with (3:=H0) (4:=H1); 
       [|rewrite H0; trivial|rewrite H1; apply SUCC_typ; apply ZERO_typ].
      rewrite NATREC_S; [rewrite NATREC_0; rewrite int_S; [reflexivity|trivial]
        |do 3 red; intros; rewrite H3; reflexivity|apply ZERO_typ].

  setoid_replace Nat with (lift 3 Nat) using relation eq_trm at 2;
    [apply typ_var; trivial|simpl; split; red; reflexivity].
Qed.


(*Axiom2 : x + 1 = y + 1 -> x = y*)
Definition ax2 := forall e, exists t, typ e t (Fall (Fall (Impl
  (EQ_trm (App (App Add (Ref 0)) (App Succ Zero)) (App (App Add (Ref 1)) (App Succ Zero)))
  (EQ_trm (Ref 0) (Ref 1))))).

Lemma P_ax_intro2 : ax2.
unfold ax2; intros e.
exists (Abs Nat (Abs Nat (Abs (EQ_trm (App (App Add (Ref 0)) (App Succ Zero))
  (App (App Add (Ref 1)) (App Succ Zero))) (Ref 0)))).
apply typ_abs; [left; apply typ_N| |discriminate].
apply typ_abs; [left; apply typ_N| |discriminate].
apply Impl_intro; [|discriminate|].
 apply EQ_trm_typ.
  apply typ_Add2; [|apply typ_S1; apply typ_0].
   setoid_replace Nat with (lift 1 Nat) using relation eq_trm at 3;
     [apply typ_var; trivial|simpl; split; red; reflexivity].

  apply typ_Add2; [|apply typ_S1; apply typ_0].
   setoid_replace Nat with (lift 2 Nat) using relation eq_trm at 3;
     [apply typ_var; trivial|simpl; split; red; reflexivity].

setoid_replace (lift 1 (EQ_trm (Ref 0) (Ref 1))) with 
  (EQ_trm (Ref 1) (Ref 2)) using relation eq_trm; [
    |unfold EQ_trm, lift; repeat rewrite red_lift_prod; repeat rewrite red_lift_app;
      rewrite eq_trm_lift_ref_bd; [|omega]; rewrite lift_rec_acc; [simpl plus|omega];
        rewrite eq_trm_lift_ref_fv; [simpl plus|omega]; rewrite eq_trm_lift_ref_bd; [|omega];
          rewrite lift_rec_acc; [simpl plus|omega]; 
            repeat (rewrite eq_trm_lift_ref_fv; [simpl plus|omega]);
              apply Prod_morph; [apply Prod_morph; simpl; split; red|]; reflexivity].
red; intros. red in H.
assert (nth_error (EQ_trm (App (App Add (Ref 0)) (App Succ Zero))
  (App (App Add (Ref 1)) (App Succ Zero)) :: Nat :: Nat :: e) 0 = value (
    EQ_trm (App (App Add (Ref 0)) (App Succ Zero))
    (App (App Add (Ref 1)) (App Succ Zero)))) by trivial.
assert (nth_error (EQ_trm (App (App Add (Ref 0)) (App Succ Zero))
  (App (App Add (Ref 1)) (App Succ Zero)) :: Nat :: Nat :: e) 1 = value Nat) by trivial.
assert (nth_error (EQ_trm (App (App Add (Ref 0)) (App Succ Zero))
  (App (App Add (Ref 1)) (App Succ Zero)) :: Nat :: Nat :: e) 2 = value Nat) by trivial.
apply H in H0. apply in_int_not_kind in H0; [|discriminate].
apply H in H1. apply in_int_not_kind in H1; [destruct H1 as (H1, _)|discriminate].
unfold inX in H1; simpl in H1; rewrite El_def in H1.
apply H in H2. apply in_int_not_kind in H2; [destruct H2 as (H2, _)|discriminate].
unfold inX in H2; simpl in H2; rewrite El_def in H2.
apply in_int_intro; [clear e H|discriminate|discriminate].
assert ([i 0, j 0]\real (prod (prod (mkTY NAT cNAT) (fun _ => props)) (fun x => 
  prod (app x (i 1)) (fun y => app x (i 2)))) ->
[int i (Ref 0), tm j (Ref 0)]\real int i (EQ_trm (Ref 1) (Ref 2))).
 apply real_morph; simpl; reflexivity.

apply H; clear H.
assert ([int i (Ref 0), tm j (Ref 0)] \real int i (lift 1
  (EQ_trm (App (App Add (Ref 0)) (App Succ Zero))
    (App (App Add (Ref 1)) (App Succ Zero)))) ->
  ([int i (Ref 0), tm j (Ref 0)] \real int (V.shift 1 i)
    (EQ_trm (App (App Add (Ref 0)) (App Succ Zero))
      (App (App Add (Ref 1)) (App Succ Zero))))).
 unfold lift; rewrite int_lift_rec_eq. rewrite V.lams0; trivial.

specialize H with (1:=H0); clear H0.
replace (int (V.shift 1 i) (Prod (Prod Nat prop)
  (Prod (App (Ref 0) (lift 1 (App (App Add (Ref 0)) (App Succ Zero))))
    (App (Ref 1) (lift 2 (App (App Add (Ref 1)) (App Succ Zero))))))) with
  (prod (prod (mkTY NAT cNAT) (fun _ => props)) (fun x =>
    prod (app x (int (V.cons x (V.shift 1 i)) 
      (lift 1 (App (App Add (Ref 0)) (App Succ Zero))))) (fun y =>
        app x (int (V.cons y (V.cons x (V.shift 1 i)))
          (lift 2 (App (App Add (Ref 1)) (App Succ Zero))))))) in H by reflexivity.
assert ([int i (Ref 0), tm j (Ref 0)] \real
  prod (prod (mkTY NAT cNAT) (fun _ : set => props)) (fun x : set =>
    prod (app x (int (V.cons x (V.shift 1 i)) 
      (lift 1 (App (App Add (Ref 0)) (App Succ Zero))))) (fun y : set =>
        app x (int (V.cons y (V.cons x (V.shift 1 i)))
          (lift 2 (App (App Add (Ref 1)) (App Succ Zero)))))) ->
  [i 0, j 0] \real (prod (prod (mkTY NAT cNAT) (fun _ => props)) (fun x =>
    prod (app x (SUCC (i 1))) (fun y => app x (SUCC (i 2)))))).
 apply real_morph; [reflexivity| |reflexivity].
  apply prod_ext; [reflexivity|do 2 red; intros].
   apply prod_ext; [|do 2 red; intros].
    rewrite int_cons_lift_eq. 
    assert (int (V.shift 1 i) (Ref 0) == i 1) by reflexivity.
    assert (int (V.shift 1 i) (App Succ Zero) == SUCC ZERO) by (apply int_S; apply ZERO_typ).
    rewrite int_Add with (3:=H4) (4:=H5); [
      |rewrite H4; trivial|rewrite H5; apply SUCC_typ; apply ZERO_typ].
     rewrite NATREC_S; [rewrite NATREC_0, H3; reflexivity
       |do 3 red; intros; rewrite H7; reflexivity|apply ZERO_typ].

    rewrite split_lift. do 2 rewrite int_cons_lift_eq.
    assert (int (V.shift 1 i) (Ref 1) == i 2) by reflexivity.
    assert (int (V.shift 1 i) (App Succ Zero) == SUCC ZERO) by (apply int_S; apply ZERO_typ).
    rewrite int_Add with (3:=H6) (4:=H7); [
      |rewrite H6; trivial|rewrite H7; apply SUCC_typ; apply ZERO_typ].
     rewrite NATREC_S; [rewrite NATREC_0, H3; reflexivity
       |do 3 red; intros; rewrite H9; reflexivity|apply ZERO_typ].

apply H0 in H; clear H0.
apply eq_SUCC_eq; trivial.
Qed.

(*Axiom 3 : x = x + 0*)
Definition ax3 := forall e, exists t, 
  typ e t (Fall (EQ_trm (Ref 0) (App (App Add (Ref 0)) Zero))).

Lemma P_ax_intro3 : ax3.
unfold ax3.
exists (Abs Nat (Abs (Prod Nat prop) (Abs (App (Ref 0) (Ref 1)) (Ref 0)))).
unfold EQ_trm. unfold lift at 1.
apply typ_abs; [left; apply typ_N| |discriminate].
apply typ_abs; [left; apply typ_prod; 
  [left; trivial|left; apply typ_N|apply typ_prop]| |discriminate].
rewrite (eq_trm_lift_ref_fv 1 0 0); [simpl plus|omega].
apply typ_abs; [right| |discriminate].
 setoid_replace prop with (subst (Ref 1) prop) using relation eq_trm at 2;
   [|simpl; split; red; reflexivity].
  apply typ_app with (V:=Nat); [| |discriminate|discriminate].
   setoid_replace Nat with (lift 2 Nat) using relation eq_trm at 3;
     [apply typ_var; trivial|simpl; split; red; reflexivity].

   setoid_replace (Prod Nat prop) with (lift 1 (Prod Nat prop)) using relation eq_trm at 2;
     [apply typ_var; trivial|simpl; split; red; reflexivity].

apply typ_conv with (T:=(lift 1 (App (Ref 0) (Ref 1)))); 
  [apply typ_var; trivial| |discriminate|discriminate].
unfold lift at 1. rewrite red_lift_app.
do 2 (rewrite eq_trm_lift_ref_fv; [simpl plus|omega]).
apply eq_typ_app; [apply refl|do 2 red; intros].
unfold lift; rewrite int_lift_rec_eq. rewrite V.lams0.
red in H.
assert (nth_error (App (Ref 0) (Ref 1)::Prod Nat prop::Nat::e) 2 = value Nat) by trivial.
specialize H with (1:=H0); clear H0.
apply in_int_not_kind in H; [destruct H as (H, _)|discriminate].
unfold inX in H; simpl in H; rewrite El_def in H.
assert (int (V.shift 2 (fun k : nat => i k)) (Ref 0) == i 2) by reflexivity.
assert (int (V.shift 2 (fun k : nat => i k)) Zero == ZERO) by reflexivity.
rewrite int_Add with (3:=H0) (4:=H1); [rewrite NATREC_0; reflexivity
  |rewrite H0; trivial|rewrite H1; apply ZERO_typ].
Qed.


(*Axiom 4 : (x + y) + 1 = x + (y + 1)*)
Definition ax4 := forall e, exists t, 
  typ e t (Fall(Fall (EQ_trm (App (App Add (App (App Add (Ref 0)) (Ref 1))) 
  (App Succ Zero)) (App (App Add (Ref 0)) (App (App Add (Ref 1)) (App Succ Zero)))))).

Lemma P_ax_intro4 : ax4.
unfold ax4.
exists (Abs Nat (Abs Nat (Abs (Prod Nat prop) 
  (Abs (App (Ref 0) (App (App Add (App (App Add (Ref 1)) (Ref 2)))
    (App Succ Zero))) (Ref 0))))).
apply typ_abs; [left; apply typ_N| |discriminate].
apply typ_abs; [left; apply typ_N| |discriminate].
apply typ_abs; [left; apply typ_prod; [left; trivial|left; apply typ_N|apply typ_prop]| 
  |discriminate].
unfold lift at 1. repeat rewrite red_lift_app.
assert (eq_trm (lift_rec 1 0 Add) Add) as Hadd_lift.
 unfold Add. repeat rewrite red_lift_abs.
 apply Abs_morph; [simpl; split; red; reflexivity|].
  apply Abs_morph; [simpl; split; red; reflexivity|].
   simpl; split; red; intros.
    apply NATREC_morph; [unfold V.lams, V.shift; simpl; apply H| 
      |unfold V.lams, V.shift; simpl; apply H].
     do 3 red; intros. apply app_ext; [apply app_ext; [reflexivity|]|]; trivial.

    unfold I.lams, I.shift; simpl; do 2 rewrite H; trivial.

rewrite Hadd_lift. do 2 (rewrite eq_trm_lift_ref_fv; [simpl plus|omega]).
setoid_replace (lift_rec 1 0 Succ) with Succ using relation eq_trm by 
  (simpl; split; red; reflexivity).
setoid_replace (lift_rec 1 0 Zero) with Zero using relation eq_trm by 
  (simpl; split; red; reflexivity).
apply typ_abs; [right| |discriminate].
 setoid_replace prop with 
   (subst (App (App Add (App (App Add (Ref 1)) (Ref 2))) (App Succ Zero)) prop)
   using relation eq_trm at 2 by (simpl; split; red; reflexivity).
 apply typ_app with (V:=Nat); [| |discriminate|discriminate].
  apply typ_Add2; [|apply typ_S1; apply typ_0].
   apply typ_Add2.
    setoid_replace Nat with (lift 2 Nat) using relation eq_trm at 4;
      [apply typ_var; trivial|simpl; split; red; reflexivity].
 
    setoid_replace Nat with (lift 3 Nat) using relation eq_trm at 4;
      [apply typ_var; trivial|simpl; split; red; reflexivity].

  setoid_replace (Prod Nat prop) with (lift 1 (Prod Nat prop)) using relation eq_trm at 2;
    [apply typ_var; trivial|simpl; split; red; reflexivity].

 apply typ_conv with (T:= lift 1 (App (Ref 0) (App (App Add (App (App Add (Ref 1)) (Ref 2))) 
   (App Succ Zero)))); [apply typ_var; trivial| |discriminate|discriminate].
  unfold lift. rewrite red_lift_app. rewrite eq_trm_lift_ref_fv; [simpl plus|omega].
  apply eq_typ_app; [apply refl|do 2 red; intros].
   red in H.
   assert (nth_error (App (Ref 0) 
     (App (App Add (App (App Add (Ref 1)) (Ref 2))) (App Succ Zero))
     :: Prod Nat prop :: Nat :: Nat :: e) 2 = value Nat) as Hi2 by trivial.
   assert (nth_error (App (Ref 0) 
     (App (App Add (App (App Add (Ref 1)) (Ref 2))) (App Succ Zero))
     :: Prod Nat prop :: Nat :: Nat :: e) 3 = value Nat) as Hi3 by trivial.
   apply H in Hi2; apply in_int_not_kind in Hi2; [|discriminate].
   destruct Hi2 as (Hi2, _); unfold inX in Hi2; simpl in Hi2; rewrite El_def in Hi2.
   apply H in Hi3; apply in_int_not_kind in Hi3; [|discriminate].
   destruct Hi3 as (Hi3, _); unfold inX in Hi3; simpl in Hi3; rewrite El_def in Hi3.
   clear H. do 2 rewrite int_lift_rec_eq. do 2 rewrite V.lams0. 
   assert (int (V.shift 1 (fun k : nat => i k)) (App (App Add (Ref 1)) (Ref 2)) ==
     NATREC (i 2) (fun _ => SUCC) (i 3)).
    assert (int (V.shift 1 (fun k : nat => i k)) (Ref 1) == (i 2)) by reflexivity.
    assert (int (V.shift 1 (fun k : nat => i k)) (Ref 2) == (i 3)) by reflexivity.
    rewrite int_Add with (3:=H) (4:=H0); [reflexivity|rewrite H|rewrite H0]; trivial.
   assert (forall n, int (V.shift n i) (App Succ Zero) == SUCC ZERO) as Hn1 by
     (intros n; apply int_S; apply ZERO_typ).
   rewrite int_Add with (3:=H) (4:=(Hn1 1)); [clear H
     |rewrite H; change NAT with ((fun _ => NAT) (i 3)); apply NATREC_typ; trivial; 
       [do 2 red; intros; reflexivity
       |do 3 red; intros; rewrite H1; reflexivity  
       |intros; apply SUCC_typ; trivial]
     |rewrite (Hn1 1); apply SUCC_typ; apply ZERO_typ].
   assert (int (V.shift 2 (fun k : nat => i k)) (Ref 0) == (i 2)) by reflexivity.
   assert (int (V.shift 2 (fun k : nat => i k)) (App (App Add (Ref 1)) (App Succ Zero)) ==
     NATREC (i 3) (fun _ => SUCC) (SUCC ZERO)).
    assert (int (V.shift 2 (fun k : nat => i k)) (Ref 1) == (i 3)) by reflexivity.
    rewrite int_Add with (3:=H0) (4:=(Hn1 2)); [reflexivity|rewrite H0
      |rewrite (Hn1 2); apply SUCC_typ; apply ZERO_typ]; trivial.
   rewrite int_Add with (3:=H) (4:=H0); [|rewrite H; trivial
     |rewrite H0; change NAT with ((fun _ => NAT) (SUCC ZERO)); apply NATREC_typ; trivial; 
       [do 2 red; reflexivity
       |do 3 red; intros; rewrite H2; reflexivity
       |apply SUCC_typ; apply ZERO_typ
       |intros; apply SUCC_typ; trivial]].
   rewrite NATREC_S; [rewrite NATREC_0
     |do 3 red; intros; rewrite H2; reflexivity|apply ZERO_typ].
   assert (NATREC (i 2) (fun _ : set => SUCC)
     (NATREC (i 3) (fun _ : set => SUCC) (SUCC ZERO)) ==
     NATREC (i 2) (fun _ : set => SUCC) (SUCC (i 3))).
    apply NATREC_morph; [reflexivity
      |do 3 red; intros; rewrite H2; reflexivity
      |rewrite NATREC_S; [rewrite NATREC_0; reflexivity
        |do 3 red; intros; rewrite H2; reflexivity|apply ZERO_typ]].
   
   rewrite H1; clear Hn1 H H0 H1.
   rewrite NATREC_S; [reflexivity|do 3 red; intros; rewrite H0; reflexivity|trivial].
Qed.


(*Induction Schema*)
Definition ax5 := forall e P, typ (Nat::e) P (lift 1 prop) -> exists t,
  typ e t (Impl (subst Zero P) (Impl (Fall (Impl P
  (subst (App (App Add (Ref 0)) (App Succ Zero)) (lift_rec 1 1 P)))) (Fall P))).

Lemma P_ax_intro5 : ax5.
unfold ax5; intros e P HP.
exists (Abs (subst Zero P) (Abs (Prod (lift 1 Nat) (Impl (lift_rec 1 1 P)
  ((lift_rec 1 1 (subst (App (App Add (Ref 0)) (App Succ Zero)) (lift_rec 1 1 P)))))) 
    (Abs (lift 2 Nat) (NatRec (Ref 2) (Ref 1) (Ref 0))))).

red; intros i j Hok.
assert (val_ok (Nat::e) (V.cons ZERO i) (I.cons ZE j)).
 apply vcons_add_var; [trivial| |discriminate].
  split; [unfold inX; rewrite ElNat_eq|rewrite RealNat_eq; [apply cNAT_ZE|]]; apply ZERO_typ.

generalize HP; intros HSP.
apply red_typ with (1:=H) in HSP; [destruct HSP as (HSP, _)|discriminate].
clear H; revert i j Hok.
fold (typ e (Abs (subst Zero P) (Abs (Prod (lift 1 Nat) (Impl (lift_rec 1 1 P)
  ((lift_rec 1 1 (subst (App (App Add (Ref 0)) (App Succ Zero)) (lift_rec 1 1 P)))))) 
    (Abs (lift 2 Nat) ((NatRec (Ref 2) (Ref 1) (Ref 0))))))
  ((Impl (subst Zero P) (Impl (Fall (Impl P (subst (App (App Add (Ref 0)) (App Succ Zero))
    (lift_rec 1 1 P)))) (Fall P))))).
apply Impl_intro; [|discriminate|].
 apply typ_subst with (A:=Nat); [discriminate|discriminate| |apply typ_0].
  setoid_replace prop with (lift 1 prop) using relation eq_trm in HP; [trivial
    |simpl; split; red; reflexivity].

 assert (typ (subst Zero P :: e) (Abs (Prod (lift 1 Nat) (Prod (lift_rec 1 1 P)
   (lift_rec 1 0 (lift_rec 1 1 (subst (App (App Add (Ref 0)) (App Succ Zero))
     (lift_rec 1 1 P)))))) (Abs (lift 1 (lift 1 Nat)) (NatRec (Ref 2) (Ref 1) (Ref 0))))
 (Prod (Prod (lift 1 Nat) (Prod (lift_rec 1 1 P) (lift_rec 1 0 (lift_rec 1 1
   (subst (App (App Add (Ref 0)) (App Succ Zero))
     (lift_rec 1 1 P)))))) (Prod (lift 1 (lift 1 Nat)) (lift_rec 2 1 P))) ->
 typ (subst Zero P :: e) (Abs (Prod (lift 1 Nat) (Impl (lift_rec 1 1 P) (lift_rec 1 1
   (subst (App (App Add (Ref 0)) (App Succ Zero)) (lift_rec 1 1 P)))))
 (Abs (lift 2 Nat) (NatRec (Ref 2) (Ref 1) (Ref 0)))) (lift 1 (Impl
   (Fall (Impl P (subst (App (App Add (Ref 0)) (App Succ Zero))
     (lift_rec 1 1 P)))) (Fall P)))).
  apply typ_morph.
   apply Abs_morph; [reflexivity|apply Abs_morph; [apply split_lift|reflexivity]].
  
   unfold Impl, Fall, lift. rewrite red_lift_prod.
   apply Prod_morph; do 2 rewrite red_lift_prod.
    apply Prod_morph; [reflexivity|apply Prod_morph; [reflexivity|]].
     rewrite (lift_rec_comm _ 1 1 0 1); [reflexivity|omega].
 
    apply Prod_morph; [simpl; split; red; reflexivity|].
     rewrite (lift_rec_acc _ 1 1 2 1); [simpl plus; reflexivity|omega].

 apply H; clear H.
 apply typ_abs; [right| |discriminate].
  apply typ_prod; [right; trivial|left; 
    setoid_replace (lift 1 Nat) with Nat using relation eq_trm; 
      [apply typ_N|split; red; simpl; reflexivity]|].
  apply typ_prod; [right; trivial|right; 
    setoid_replace prop with (lift_rec 1 1 prop) using relation eq_trm; 
      [apply weakening_bind; trivial|split; red; simpl; reflexivity]|].
  setoid_replace prop with (lift 1 (lift_rec 1 1 (lift 1 prop))) using relation eq_trm;
    [|simpl; split; red; reflexivity].
  apply weakening. 
  apply weakening_bind; trivial.
  apply typ_subst with (A:=(lift 1 Nat)); [discriminate|discriminate| |].
   unfold lift; rewrite lift_rec_comm by omega; apply weakening_bind; trivial.

   apply typ_Add2; [|apply typ_S1; apply typ_0].
    setoid_replace Nat with (lift 1 Nat) using relation eq_trm at 2;  
      [apply typ_var; trivial|split; red; simpl; reflexivity].

 apply typ_abs; [left; replace kind with (lift 1 (lift 1 kind)); [|trivial]| 
   |destruct P; [discriminate|trivial]].
  do 2 apply weakening; apply typ_N.

  apply typ_conv with (T:=(App (Abs (lift 1 (lift 1 (lift 1 Nat))) (lift_rec 3 1 P)) (Ref 0))); 
    [| |discriminate|destruct P; [discriminate|trivial]].
   apply typ_Nrect.
    setoid_replace Nat with (lift 1 (lift 1 (lift 1 Nat))) using relation eq_trm at 3;
       [apply typ_var; trivial|simpl; split; red; reflexivity].
     
    apply typ_conv with (T:=(lift 3 (subst Zero P))); [apply typ_var; trivial| 
      |destruct P; [discriminate|trivial]|discriminate].
     rewrite eq_typ_beta with (N':=Zero) (M':=(lift_rec 3 1 P)); [|apply refl|apply refl
        |apply typ_0|discriminate].
      do 2 red; intros. unfold lift, subst.
      rewrite int_subst_rec_eq; simpl; rewrite V.lams0.
      do 2 rewrite int_lift_rec_eq; rewrite V.lams0.
      rewrite int_subst_rec_eq; simpl; rewrite V.lams0. 
      rewrite <- V.cons_lams; [rewrite V.lams0|do 2 red; intros; rewrite H0]; reflexivity.

    apply typ_conv with (T:=(lift 2 (Prod (lift 1 Nat) (Prod (lift_rec 1 1 P)
      (lift_rec 1 0 (lift_rec 1 1 (subst (App (App Add (Ref 0)) (App Succ Zero))
        (lift_rec 1 1 P)))))))); [apply typ_var; trivial| |discriminate|discriminate].
      rewrite split_lift with (n:=1).
      unfold lift. repeat rewrite red_lift_prod.
      repeat rewrite red_lift_abs.
      apply eq_typ_prod; [red; simpl; reflexivity| |discriminate].
       apply eq_typ_prod; [| |destruct P; [discriminate|trivial]].
        rewrite eq_typ_beta with (N':=(Ref 0)) (M':=(lift_rec 1 1 (lift_rec 3 1 P))); 
          [|apply refl|apply refl| |discriminate].
         rewrite subst0_lift. do 2 red; intros.
         do 5 rewrite int_lift_rec_eq. unfold V.lams, V.shift.
         apply int_morph; [do 3 red; intros|reflexivity].
          destruct (le_gt_dec 1 a) as [le|gt]; simpl; reflexivity.

         replace ((lift_rec 1 0 (lift_rec 1 0 (lift_rec 1 0 (lift_rec 1 0 Nat))))) with
           (lift 1 (lift_rec 1 0 (lift_rec 1 0 (lift_rec 1 0 Nat)))) by trivial.
         apply typ_var; trivial.

        rewrite eq_typ_beta with (N':=(App Succ (Ref 1))) 
          (M':=(lift_rec 2 1 (lift_rec 3 1 P))); [|apply refl|apply refl| |discriminate].
         rewrite (lift_rec_acc _ 1 1 2 2) by omega. simpl plus.
         do 2 red; intros. do 3 rewrite int_lift_rec_eq. rewrite V.lams0.
         unfold subst; do 2 rewrite int_subst_rec_eq. do 2 rewrite V.lams0.
         assert (int (V.shift 0 (V.lams 1 (V.shift 1) (V.shift 1 (fun k : nat => 
           V.lams 2 (V.shift 2) i k)))) (Ref 0) == i 1).
          unfold V.lams, V.shift; simpl; reflexivity.
         assert (int (V.shift 0 (V.lams 1 (V.shift 1) (V.shift 1 (fun k : nat => 
           V.lams 2 (V.shift 2) i k)))) (App Succ Zero) == SUCC ZERO).
          rewrite int_S; [simpl; reflexivity|apply ZERO_typ].
         red in H.
         assert (in_int i j (Ref 1) (lift 2 (lift 1 (lift 1 (lift 1 Nat))))).
          apply H; reflexivity.
         
         apply in_int_not_kind in H2; [|discriminate].
         destruct H2 as (Hi1, _); unfold inX in Hi1; simpl in Hi1; rewrite El_def in Hi1.
         rewrite int_Add with (3:=H0) (4:=H1); [|rewrite H0; trivial
           |rewrite H1; apply SUCC_typ; apply ZERO_typ].
         do 3 rewrite int_lift_rec_eq.
         rewrite NATREC_S; [rewrite NATREC_0
           |do 3 red; intros; rewrite H3; reflexivity
           |apply ZERO_typ].
         rewrite int_S; [|simpl; unfold V.shift; trivial].
         do 3 (rewrite <- V.cons_lams; [|do 2 red; intros; rewrite H2; reflexivity]).
         do 3 rewrite V.lams0. unfold V.lams, V.shift; simpl.
         apply int_morph; [do 2 red; intros|reflexivity]. 
          apply V.cons_morph; 
            [|do 3 red; intros; replace (a0-0) with a0; [|omega]]; reflexivity.
      
         apply typ_S1.
         setoid_replace Nat with (lift 2 (lift 1 (lift 1 (lift 1 Nat)))) using relation eq_trm at 4;
           [apply typ_var; trivial|simpl; split; red; reflexivity].

    rewrite eq_typ_beta with (N':=(Ref 0)) (M':=(lift_rec 3 1 P)); 
      [|apply refl|apply refl| |discriminate].
     do 2 red; intros. unfold subst.
     rewrite int_subst_rec_eq. do 2 rewrite int_lift_rec_eq.
     rewrite V.lams0. rewrite <- V.cons_lams; [|do 2 red; intros; rewrite H0; reflexivity].
     rewrite V.lams0; unfold V.shift at 1; simpl. apply int_morph; [|reflexivity].
      apply V.cons_ext; [unfold V.lams, V.shift; simpl
        |rewrite V.shift_lams; rewrite V.lams0; rewrite V.shift_split]; reflexivity.

    apply typ_var; trivial.
Qed.
 
Definition ax := ax1 /\ ax2 /\ ax3 /\ ax4 /\ ax5.

Lemma ax_provable : ax.
unfold ax. split; [apply P_ax_intro1|split; [apply P_ax_intro2
|split; [apply P_ax_intro3|split; [apply P_ax_intro4|apply P_ax_intro5]]]].
Qed.
 
End PSemAx.


(************************************************************************************)
(*Presburger Semantic*)
(************************************************************************************)
Module PresburgerSem <: TheorySem.

Module sig <: AbsSemSig := PSemSig.
Export sig.

Module ax <: SemanticAx PSemSig := PSemAx.
Export ax.

End PresburgerSem.