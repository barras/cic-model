(************************************************************************************)
(************************************************************************************)
(*This files gives the basic semantic for abstract theory*)
(************************************************************************************)
(************************************************************************************)

Require Import List.
Require Import Esub.

Import GenLemmas.
Import SN_CC_Real.
Import ZF SN CCSN.



(************************************************************************************)
(*Abstract signature of semantic*)
(************************************************************************************)
Module Type AbsSemSig.

(*The sort of the theory*)
Parameter sort : trm.
Axiom sort_not_kind : sort <> kind.
Axiom typ_sort : forall e, typ e sort kind.
Axiom sort_clsd : 
  (forall n k, eq_trm (lift_rec n k sort) sort) /\
  (forall t k, eq_trm (subst_rec t k sort) sort).

Definition wf_clsd_env e := forall i j, val_ok e i j ->
  exists j', val_ok e i j' /\ (forall n, closed_pure_trm (j' n)).

Axiom PredVary : forall e x y i j, 
  wf_clsd_env e ->
  typ e x sort ->
  typ e y sort ->
  val_ok e i j ->
  (exists j', val_ok e i j' /\ (forall n, closed_pure_trm (j' n)) /\
    (exists P, P <> kind /\ [int i P, tm j' P] \real int i (Prod sort prop) /\ 
      exists u, [int i u, tm j' u] \real (app (int i P) (int i x)) /\
        ((exists v, [int i v, tm j' v] \real (app (int i P) (int i y))) -> 
          int i x == int i y))).

End AbsSemSig.

(************************************************************************************)
(*This Module describes logic connectors and quantifiers with properties*)
(************************************************************************************)
Module SemLogic (M : AbsSemSig).

Export M.

Definition EQ_trm x y :=
  Prod (Prod sort prop) (Prod (App (Ref 0) (lift 1 x)) (App (Ref 1) (lift 2 y))).

Lemma EQ_trm_elim : forall e x y t,
  wf_clsd_env e ->
  typ e x sort ->
  typ e y sort ->
  typ e t (EQ_trm x y) ->
  eq_typ e x y.
do 2 red; intros e x y t Hclsd Hx Hy Ht i j' Hok'.
generalize PredVary; intro HP. specialize HP with (1:=Hclsd) (2:=Hx) (3:=Hy) (4:=Hok').
destruct HP as (j, (Hok, (_, HP))).
destruct HP as (P, HP).
destruct HP as (HSP, HP).
destruct HP as (HP, Hxy).
destruct Hxy as (u, (Hv, Hxy)).
apply red_typ with (1:=Hok) in Ht; [|discriminate].
destruct Ht as (_, Ht).

apply Hxy; clear Hxy Hclsd e Hx Hy j' Hok' Hok.
unfold EQ_trm in Ht. simpl int in Ht.
apply SN.prod_elim with (x:=int i P) (u:=tm j P) in Ht; [
  |do 2 red; intros; apply prod_ext; [|do 2 red; intros; rewrite H2]; rewrite H0; reflexivity|trivial].
apply SN.prod_elim with (x:=int i u) (u:=tm j u) in Ht.
 exists (App (App t P) u). revert Ht; apply real_morph; simpl; [reflexivity| |reflexivity].
  rewrite split_lift. do 2 rewrite int_cons_lift_eq; reflexivity.

 do 2 red; intros. rewrite H0. reflexivity.

 revert Hv; apply real_morph; [|rewrite int_cons_lift_eq|]; reflexivity.
Qed.

(*False_symb for BF*)
Definition False_symb := Prod prop (Ref 0).

Lemma False_symb_typ : forall e, typ e False_symb prop.
intros; apply typ_prod; [right; trivial|left; apply typ_prop|].
 setoid_replace prop with (lift 1 prop) using relation eq_trm at 2;
   [apply typ_var; trivial|simpl; split; red; reflexivity].
Qed.

Lemma False_symb_elim : forall e t P,
  typ e t False_symb ->
  typ e P prop ->
  typ e (App t P) P.
red; intros e t P Ht HP i j Hok.
generalize HP; intros HSP.
apply red_typ with (1:=Hok) in HSP; [destruct HSP as (HSP, _)|discriminate].
revert i j Hok; fold (typ e (App t P) P).
setoid_replace P with (subst P (Ref 0)) using relation eq_trm at 2;
  [|unfold subst; rewrite red_sigma_var_eq; [rewrite lift0; reflexivity|trivial]].
apply typ_app with (V:=prop); [| |discriminate|discriminate]; trivial. 
Qed.

(*True_symb for TF*)
Definition True_symb := Prod prop (Prod (Ref 0) (Ref 1)).

Lemma True_symb_typ : forall e, typ e True_symb prop.
intro e.
apply typ_prod; [right; trivial|left; apply typ_prop|].
apply typ_prod; [right; trivial|right|].
 setoid_replace prop with (lift 1 prop) using relation eq_trm at 2;
   [apply typ_var; trivial|simpl; split; red; reflexivity].

 setoid_replace prop with (lift 2 prop) using relation eq_trm at 2;
   [apply typ_var; trivial|simpl; split; red; reflexivity].
Qed.

Lemma True_symb_intro : forall e, exists t, typ e t True_symb.
exists (Abs prop (Abs (Ref 0) (Ref 0))).
apply typ_abs; [left; apply typ_prop| |discriminate].
apply typ_abs; [right| |discriminate].
 setoid_replace prop with (lift 1 prop) using relation eq_trm at 2;
   [apply typ_var; trivial|simpl; split; red; reflexivity].

 rewrite <- (eq_trm_lift_ref_fv 1 0 0); [apply typ_var; trivial|omega].
Qed.

(*Impl for implf*)
Definition Impl A B := Prod A (lift 1 B).

Lemma Impl_typ : forall e A B,
  typ e A prop ->
  typ e B prop ->
  typ e (Impl A B) prop.
intros. apply typ_prod; [right|right|]; trivial.
setoid_replace prop with (lift 1 prop) using relation eq_trm;
  [apply weakening; trivial|simpl; split; red; reflexivity].
Qed.

Lemma Impl_intro : forall e b A B, 
  typ e A prop ->
  B <> kind ->
  typ (A::e) b (lift 1 B) -> 
  typ e (Abs A b) (Impl A B).
intros. apply typ_abs; [right| |destruct B; [discriminate|]]; trivial.
Qed.

Lemma Impl_elim : forall e t u A B, 
  A <> kind ->
  B <> kind ->
  typ e t (Impl A B) ->
  typ e u A ->
  typ e (App t u) B.
intros.
setoid_replace B with (subst u (lift 1 B)) using relation eq_trm;
  [|unfold subst; rewrite subst_lift_lt; [rewrite lift0; reflexivity|omega]].
apply typ_app with (V:=A); [| | |destruct B; [discriminate|]]; trivial.
Qed.

(*Neg for neg*)
Definition Neg t := Impl t False_symb.

Lemma Neg_typ : forall e t,
  typ e t prop ->
  typ e (Neg t) prop.
intros; unfold Neg; apply Impl_typ; [trivial|apply False_symb_typ].
Qed.

Lemma Neg_intro : forall na A e,
  typ e na (Impl A False_symb) ->
  typ e na (Neg A).
intros; unfold Neg; trivial.
Qed.

Lemma Neg_elim : forall na A e,
  typ e na (Neg A) ->
  typ e na (Impl A False_symb).
intros; unfold Neg; trivial.
Qed.

(*Conj for conj*)
Definition Conj A B :=
  Prod prop (Prod (Prod (lift 1 A) (Prod (lift 2 B) (Ref 2))) (Ref 1)).

Lemma Conj_typ : forall e A B,
  typ e A prop ->
  typ e B prop ->
  typ e (Conj A B) prop.
intros. 
apply typ_prod; [right|left; apply typ_prop|]; trivial.
apply typ_prod; [right|right|]; trivial.
 apply typ_prod; [right|right|]; trivial.
  setoid_replace prop with (lift 1 prop) using relation eq_trm at 2;
    [apply weakening; trivial|simpl; split; red; reflexivity].

  apply typ_prod; [right; trivial|right|].
   setoid_replace prop with (lift 2 prop) using relation eq_trm at 2;
     [do 2 rewrite split_lift with (n:=1); 
       do 2 apply weakening; trivial
       |simpl; split; red; reflexivity].
   
   setoid_replace prop with (lift 3 prop) using relation eq_trm at 2;
     [apply typ_var; trivial|simpl; split; red; reflexivity].

 setoid_replace prop with (lift 2 prop) using relation eq_trm at 2;
   [apply typ_var; trivial|simpl; split; red; reflexivity].
Qed.

Lemma Conj_intro : forall e A B u v,
  typ e A prop -> 
  typ e B prop ->
  typ e u A /\ typ e v B -> 
  exists t, typ e t (Conj A B).
intros e A B u v HTA HTB H. destruct H as (HA, HB).
exists (Abs prop (Abs (Prod (lift 1 A) (Prod (lift 2 B) (Ref 2))) 
  (App (App (Ref 0) (lift 2 u)) (lift 2 v)))).
red; intros i j Hok.
generalize HTA; intros HSA.
generalize HTB; intros HSB.
apply red_typ with (1:=Hok) in HSA; [destruct HSA as (HSA, _)|discriminate].
apply red_typ with (1:=Hok) in HSB; [destruct HSB as (HSB, _)|discriminate].
revert i j Hok; 
fold (typ e (Abs prop (Abs (Prod (lift 1 A) (Prod (lift 2 B) (Ref 2))) 
  (App (App (Ref 0) (lift 2 u)) (lift 2 v)))) (Conj A B)).
apply typ_abs; [left; apply typ_prop| |discriminate].
apply typ_abs; [right| |discriminate].
 apply typ_prod; [right; trivial|right|].
  setoid_replace prop with (lift 1 prop) using relation eq_trm at 2;
    [apply weakening; trivial|simpl; split; red; reflexivity].
  
  apply typ_prod; [right; trivial|right|].
   setoid_replace prop with (lift 2 prop) using relation eq_trm at 2;
     [do 2 rewrite split_lift with (n:=1);
       do 2 apply weakening; trivial|simpl; split; red; reflexivity].

   setoid_replace prop with (lift 3 prop) using relation eq_trm at 2;
     [apply typ_var; trivial|simpl; split; red; reflexivity].

 setoid_replace (Ref 1) with (subst (lift 2 v) (Ref 2)) using relation eq_trm;
  [|unfold subst; rewrite red_sigma_var_gt; [reflexivity|omega]].
 apply typ_app with (V:=(lift 2 B));
   [| |destruct B; [discriminate|]|discriminate]; trivial.
  rewrite split_lift with (n:=1) at 2.
  rewrite split_lift with (n:=1) (T:=v).
  do 2 apply weakening; trivial.

  setoid_replace (Prod (lift 2 B) (Ref 2)) with 
    (subst (lift 2 u) (lift 1 (Prod (lift 2 B) (Ref 2)))) using relation eq_trm at 2; [
      |unfold subst; unfold lift at 3; rewrite <- simpl_subst_lift_rec; reflexivity].
  apply typ_app with (V:=lift 2 A); 
    [| |destruct A; [discriminate|]|discriminate]; trivial.
   rewrite split_lift with (T:=u). rewrite split_lift with (T:=A) (n:=1).
   do 2 apply weakening; trivial.

   unfold lift at 4. rewrite red_lift_prod.
   rewrite <- split_lift with (n:=2) (T:=B).
   rewrite eq_trm_lift_ref_fv; [simpl|omega].
   assert (eq_trm ((Prod (lift 2 A) (Prod (lift 3 B) (Ref 3)))) 
     (lift 1 (Prod (lift 1 A) (Prod (lift 2 B) (Ref 2))))).
    unfold lift at 3. rewrite red_lift_prod.
    rewrite <- split_lift with (T:=A) (n:=1).
    rewrite red_lift_prod.
    rewrite eq_trm_lift_ref_fv; [|omega].
    unfold lift at 4. rewrite lift_rec_acc; [reflexivity|omega].

   rewrite H. apply typ_var; trivial.
Qed.

Lemma Conj_elim1 : forall e A B t,
  typ e A prop ->
  typ e B prop ->
  typ e t (Conj A B) -> 
  exists u, typ e u A.
intros e A B t HA HB Ht; 
  exists (App (App t A) (Abs A (Abs (lift 1 B) (Ref 1)))).
red; intros i j Hok.
generalize HA; intros HSA.
generalize HB; intros HSB.
apply red_typ with (1:=Hok) in HSA; [destruct HSA as (HSA, _)|discriminate].
apply red_typ with (1:=Hok) in HSB; [destruct HSB as (HSB, _)|discriminate].
revert i j Hok; 
fold (typ e ((App (App t A) (Abs A (Abs (lift 1 B) (Ref 1))))) A).

rewrite (simpl_subst_lift_rec (Abs A (Abs (lift 1 B) (Ref 1))) A 0) at 3.
fold (lift 1 A). fold (subst (Abs A (Abs (lift 1 B) (Ref 1))) (lift 1 A)).
apply typ_app with (V:=Prod A (Prod (lift 1 B) (lift 2 A))); 
  [| |discriminate|destruct A; [discriminate|trivial]].
 apply typ_abs; [right; trivial| |discriminate].
  apply typ_abs; [right|apply typ_var|destruct A; [discriminate|]]; trivial.
   setoid_replace prop with (lift 1 prop) using relation eq_trm;
     [apply weakening; trivial|simpl; split; red; reflexivity].

 unfold Conj in Ht.
 assert (eq_trm ((Prod (Prod A (Prod (lift 1 B) (lift 2 A))) (lift 1 A)))
   (subst A (Prod (Prod (lift 1 A) (Prod (lift 2 B) (Ref 2))) (Ref 1)))).
  unfold subst. do 3 rewrite red_sigma_prod.
  do 2 (rewrite red_sigma_var_eq; trivial).
  do 2 (rewrite subst_lift_lt; [|omega]).
  rewrite lift0; reflexivity.

 rewrite H; clear H.
 apply typ_app with (V:=prop); [trivial|trivial|discriminate|discriminate].
Qed.

Lemma Conj_elim2 : forall e A B t,
  typ e A prop ->
  typ e B prop ->
  typ e t (Conj A B) -> 
  exists u, typ e u B.
intros e A B t HA HB Ht; 
  exists (App (App t B) (Abs A (Abs (lift 1 B) (Ref 0)))).
red; intros i j Hok.
generalize HA; intros HSA.
generalize HB; intros HSB.
apply red_typ with (1:=Hok) in HSA; [destruct HSA as (HSA, _)|discriminate].
apply red_typ with (1:=Hok) in HSB; [destruct HSB as (HSB, _)|discriminate].
revert i j Hok; 
fold (typ e ((App (App t B) (Abs A (Abs (lift 1 B) (Ref 0))))) B).

rewrite (simpl_subst_lift_rec (Abs A (Abs (lift 1 B) (Ref 0))) B 0) at 3.
fold (lift 1 B). fold (subst (Abs A (Abs (lift 1 B) (Ref 0))) (lift 1 B)).
apply typ_app with (V:=Prod A (Prod (lift 1 B) (lift 1 (lift 1 B)))); 
  [| |discriminate|destruct B; [discriminate|trivial]].
 apply typ_abs; [right; trivial| |discriminate].
  apply typ_abs; [right|apply typ_var|destruct B; [discriminate|]]; trivial.
   setoid_replace prop with (lift 1 prop) using relation eq_trm;
     [apply weakening; trivial|simpl; split; red; reflexivity].

 unfold Conj in Ht.
 assert (eq_trm ((Prod (Prod A (Prod (lift 1 B) (lift 2 B))) (lift 1 B)))
   (subst B (Prod (Prod (lift 1 A) (Prod (lift 2 B) (Ref 2))) (Ref 1)))).
  unfold subst. do 3 rewrite red_sigma_prod.
  do 2 (rewrite red_sigma_var_eq; trivial).
  do 2 (rewrite subst_lift_lt; [|omega]).
  rewrite lift0; reflexivity.

 rewrite <- split_lift. rewrite H; clear H.
 apply typ_app with (V:=prop); [trivial|trivial|discriminate|discriminate].
Qed.

(*Disj for disj*)
Definition Disj A B := Prod prop (Prod (Prod (lift 1 A) (Ref 1)) 
  (Prod (Prod (lift 2 B) (Ref 2)) (Ref 2))).

Lemma Disj_typ : forall e A B,
  typ e A prop ->
  typ e B prop ->
  typ e (Disj A B) prop.
intros. apply typ_prod; [right; trivial|left; apply typ_prop|].
apply typ_prod; [right; trivial|right|].
 apply typ_prod; [right; trivial|right|].
  setoid_replace prop with (lift 1 prop) using relation eq_trm at 2;
    [apply weakening; trivial|simpl; split; red; reflexivity].

  setoid_replace prop with (lift 2 prop) using relation eq_trm at 2;
    [apply typ_var; trivial|simpl; split; red; reflexivity].

 apply typ_prod; [right; trivial|right|].
  apply typ_prod; [right; trivial|right|].
   setoid_replace prop with (lift 2 prop) using relation eq_trm at 2;
     [do 2 rewrite split_lift with (n:=1); do 2 apply weakening; trivial
       |simpl; split; red; reflexivity].

   setoid_replace prop with (lift 3 prop) using relation eq_trm at 2;
     [apply typ_var; trivial|simpl; split; red; reflexivity].

  setoid_replace prop with (lift 3 prop) using relation eq_trm at 2;
    [apply typ_var; trivial|simpl; split; red; reflexivity].
Qed.
     
Lemma Disj_intro1 : forall e t A B,
  typ e A prop ->
  typ e B prop ->
  typ e t A  -> 
  exists u, typ e u (Disj A B).
intros e t A B HA HB Ht.
exists (Abs prop (Abs (Prod (lift 1 A) (Ref 1)) 
  (Abs (Prod (lift 2 B) (Ref 2)) (App (Ref 1) (lift 3 t))))).
red; intros i j Hok.
generalize HA; intros HSA.
apply red_typ with (1:=Hok) in HSA; [destruct HSA as (HSA, _)|discriminate].
revert i j Hok;
fold (typ e (Abs prop (Abs (Prod (lift 1 A) (Ref 1)) 
  (Abs (Prod (lift 2 B) (Ref 2)) 
  (App (Ref 1) (lift 3 t))))) (Disj A B)).
apply typ_abs; [left; apply typ_prop| |discriminate].
 apply typ_abs; [right| |discriminate].
  apply typ_prod; [right; trivial|right|].
   setoid_replace prop with (lift 1 prop) using relation eq_trm at 2;
     [apply weakening; trivial|simpl; split; red; reflexivity].

   setoid_replace prop with (lift 2 prop) using relation eq_trm at 2;
     [apply typ_var; trivial|simpl; split; red; reflexivity].
  
  apply typ_abs; [right| |discriminate].
   apply typ_prod; [right; trivial|right|].
    setoid_replace prop with (lift 2 prop) using relation eq_trm at 2;
      [do 2 rewrite split_lift with (n:=1); do 2 apply weakening
        |simpl; split; red; reflexivity]; trivial.

    setoid_replace prop with (lift 3 prop) using relation eq_trm at 2;
      [apply typ_var; trivial|simpl; split; red; reflexivity].

   setoid_replace (Ref 2) with (subst (lift 3 t) (Ref 3)) using relation eq_trm at 2; [
     |unfold subst; rewrite red_sigma_var_gt; [reflexivity|omega]].
   apply typ_app with (V:=(lift 3 A)); 
     [| |destruct A; [discriminate|trivial]|discriminate].
    do 2 rewrite split_lift with (T:=t).
    rewrite split_lift with (T:=A) (n:=2).
    rewrite split_lift with (T:=A) (n:=1).
    do 3 apply weakening; trivial.

    rewrite <- (eq_trm_lift_ref_fv 1 1 2) by omega.
    rewrite split_lift with (n:=2).
    unfold lift at 3. rewrite <- red_lift_prod.
    fold (lift 1 (Prod (lift 2 A) (Ref 2))).
    rewrite <- (eq_trm_lift_ref_fv 1 1 1) at 2 by omega.
    rewrite split_lift with (n:=1) (T:=A).
    unfold lift at 4. rewrite <- red_lift_prod.
    fold (lift 1 (Prod (lift 1 A) (Ref 1))).
    rewrite <- split_lift. apply typ_var; trivial.
Qed.

Lemma Disj_intro2 : forall e t A B,
  typ e A prop ->
  typ e B prop ->
  typ e t B  -> 
  exists u, typ e u (Disj A B).
intros e t A B HA HB Ht.
exists (Abs prop (Abs (Prod (lift 1 A) (Ref 1)) 
  (Abs (Prod (lift 2 B) (Ref 2)) (App (Ref 0) (lift 3 t))))).
red; intros i j Hok.
generalize HB; intros HSB.
apply red_typ with (1:=Hok) in HSB; [destruct HSB as (HSB, _)|discriminate].
revert i j Hok;
fold (typ e (Abs prop (Abs (Prod (lift 1 A) (Ref 1)) 
  (Abs (Prod (lift 2 B) (Ref 2)) (App (Ref 0) (lift 3 t))))) (Disj A B)).
apply typ_abs; [left; apply typ_prop| |discriminate].
 apply typ_abs; [right| |discriminate].
  apply typ_prod; [right; trivial|right|].
   setoid_replace prop with (lift 1 prop) using relation eq_trm at 2;
     [apply weakening; trivial|simpl; split; red; reflexivity].

   setoid_replace prop with (lift 2 prop) using relation eq_trm at 2;
     [apply typ_var; trivial|simpl; split; red; reflexivity].
  
  apply typ_abs; [right| |discriminate].
   apply typ_prod; [right; trivial|right|].
    setoid_replace prop with (lift 2 prop) using relation eq_trm at 2;
      [do 2 rewrite split_lift with (n:=1); do 2 apply weakening
        |simpl; split; red; reflexivity]; trivial.

    setoid_replace prop with (lift 3 prop) using relation eq_trm at 2;
      [apply typ_var; trivial|simpl; split; red; reflexivity].

   setoid_replace (Ref 2) with (subst (lift 3 t) (Ref 3)) using relation eq_trm at 2; [
     |unfold subst; rewrite red_sigma_var_gt; [reflexivity|omega]].
   apply typ_app with (V:=(lift 3 B)); 
     [| |destruct B; [discriminate|trivial]|discriminate].
    do 2 rewrite split_lift with (T:=t).
    rewrite split_lift with (T:=B) (n:=2).
    rewrite split_lift with (T:=B) (n:=1) at 2.
    do 3 apply weakening; trivial.

    rewrite <- (eq_trm_lift_ref_fv 1 1 2) by omega.
    rewrite split_lift with (n:=2).
    unfold lift at 3. rewrite <- red_lift_prod.
    fold (lift 1 (Prod (lift 2 B) (Ref 2))).
    apply typ_var; trivial.
Qed.

Lemma Disj_elim : forall e t t1 t2 A B C,
  typ e A prop ->
  typ e B prop ->
  typ e C prop ->
  typ e t (Disj A B) ->
  typ (A::e) t1 (lift 1 C) ->
  typ (B::e) t2 (lift 1 C) ->
  exists u, typ e u C.
intros e t t1 t2 A B C HA HB HC Ht Ht1 Ht2.
exists (App (App (App t C) (Abs A t1)) (Abs B t2)).
red; intros i j Hok.
generalize HC; intros HSC.
apply red_typ with (1:=Hok) in HSC; [destruct HSC as (HSC, _)|discriminate].
revert i j Hok;
fold (typ e (App (App (App t C) (Abs A t1)) (Abs B t2)) C).
apply Impl_intro in Ht1; [|exact HA|exact HSC].
apply Impl_intro in Ht2; [|exact HB|exact HSC].
setoid_replace C with (subst (Abs B t2) (lift 1 C)) using relation eq_trm at 2; [
  |unfold subst; rewrite subst_lift_lt; [rewrite lift0; reflexivity|omega]].
apply typ_app with (V:=(Impl B C)); 
  [| |discriminate|destruct C; [discriminate|]]; trivial.
setoid_replace (Prod (Impl B C) (lift 1 C)) with
  (subst (Abs A t1) (lift 1 (Prod (Impl B C) (lift 1 C)))) using relation eq_trm; [
    |unfold subst; rewrite subst_lift_lt; [rewrite lift0; reflexivity|omega]].
apply typ_app with (V:=(Impl A C)); [trivial| |discriminate|discriminate].
unfold Impl; unfold Disj in Ht.
unfold lift at 2 3 4. do 2 rewrite red_lift_prod.
rewrite lift_rec_acc; [simpl plus|omega].
fold (lift 1 B) (lift 2 C).
assert (eq_trm 
  (Prod (Prod A (lift 1 C)) (Prod (Prod (lift 1 B) (lift 2 C)) (lift 2 C)))
  (subst C (Prod (Prod (lift 1 A) (Ref 1))
    (Prod (Prod (lift 2 B) (Ref 2)) (Ref 2))))).
 unfold subst. do 4 rewrite red_sigma_prod.
 do 2 (rewrite subst_lift_lt by omega). rewrite lift0.
 do 2 (rewrite red_sigma_var_eq; trivial); reflexivity.

rewrite H; clear H.
apply typ_app with (V:=prop); [| |discriminate|discriminate]; trivial.
Qed.

(*Fall for fall*)
Definition Fall A := Prod sort A.

Lemma Fall_typ : forall e A,
  typ (sort::e) A prop ->
  typ e (Fall A) prop.
intros; apply typ_prod; [right|unfold typs; left; apply typ_sort|];trivial.
Qed.

Lemma Fall_intro : forall e t B,
  typ (sort::e) B prop ->
  typ (sort::e) t B -> 
  typ e (Abs sort t) (Fall B).
intros e t B HB Ht i j Hok'.
assert (exists x, [x, Sat.SatSet.daimon] \real int i sort).
 apply typs_non_empty with (e:=e) (j:=j); [left; apply typ_sort|]; trivial.
destruct H as (x, H).
assert (val_ok (sort :: e) (V.cons x i) (I.cons Sat.SatSet.daimon j)).
 apply vcons_add_var; [| |apply sort_not_kind]; trivial.

generalize HB; intros HSB.
apply red_typ with (1:=H0) in HSB; [destruct HSB as (HSB, _)|discriminate].
clear H H0; revert i j Hok'; fold (typ e (Abs sort t) (Fall B)).
apply typ_abs; [left; apply typ_sort| |]; trivial.
Qed.
  
Lemma Fall_elim : forall e t u B, 
  typ (sort::e) B prop ->
  typ e t (Fall B) -> 
  typ e u sort ->
  typ e (App t u) (subst u B).
red; intros e t u B HB Ht Hu i j Hok.

assert (exists x, [x, Sat.SatSet.daimon] \real int i sort).
 apply typs_non_empty with (e:=e) (j:=j); [left; apply typ_sort|]; trivial.
destruct H as (x, H).
assert (val_ok (sort :: e) (V.cons x i) (I.cons Sat.SatSet.daimon j)).
 apply vcons_add_var; [| |apply sort_not_kind]; trivial.

generalize HB; intros HSB.
apply red_typ with (1:=H0) in HSB; [destruct HSB as (HSB, _)|discriminate].
clear H H0; revert i j Hok; fold (typ e (App t u) (subst u B)).
apply typ_app with (V:=sort); [| |apply sort_not_kind|]; trivial.
Qed.

(*Exst for exst*)
Definition Exst A := Prod prop (
  Prod (Prod (lift 1 sort) (Prod (subst (Ref 0) (lift_rec 2 1 A)) (Ref 2))) (Ref 1)).

Lemma Exst_typ : forall e A,
  typ (sort::e) A prop ->
  typ e (Exst A) prop.
intros e A HA; unfold Exst.
apply typ_prod; [right; trivial|left; apply typ_prop|].
apply typ_prod; [right|right
  |setoid_replace prop with (lift 2 prop) using relation eq_trm at 2;
    [apply typ_var|simpl; split; red; reflexivity]]; trivial.
apply typ_prod; [right; trivial
  |left; setoid_replace kind with (lift 1 kind) using relation eq_trm;
    [apply weakening; apply typ_sort|simpl; split; red; reflexivity]|].
apply typ_prod; [right|right
  |setoid_replace prop with (lift 3 prop) using relation eq_trm at 2;
    [apply typ_var|simpl; split; red; reflexivity]]; trivial.
rewrite subst0_lift.
setoid_replace prop with (lift_rec 1 1 prop) using relation eq_trm at 2;
  [apply weakening_bind; trivial|simpl; split; red; reflexivity].
Qed.

Lemma Exst_intro : forall e A p a, 
  typ (sort::e) A prop ->
  typ e a sort -> 
  typ e p (subst a A) ->
  exists t, typ e t (Exst A).
intros e A p a HA Ha Hp. 
exists (Abs prop (Abs (Prod (lift 1 sort) (Prod (subst (Ref 0) (lift_rec 2 1 A)) (Ref 2))) 
  (App (App (Ref 0) (lift 2 a)) (lift 2 p)))).
red; intros i j Hok.
assert (exists x, [x, Sat.SatSet.daimon] \real int i sort).
 apply typs_non_empty with (e:=e) (j:=j); [left; apply typ_sort|]; trivial.
destruct H as (x, H).
assert (val_ok (sort :: e) (V.cons x i) (I.cons Sat.SatSet.daimon j)).
 apply vcons_add_var; [| |apply sort_not_kind]; trivial.

generalize HA; intros HSA.
apply red_typ with (1:=H0) in HSA; [destruct HSA as (HSA, _)|discriminate].
clear H H0; revert i j Hok;
fold (typ e (Abs prop (Abs (Prod (lift 1 sort) (Prod (subst (Ref 0) (lift_rec 2 1 A)) (Ref 2))) 
  (App (App (Ref 0) (lift 2 a)) (lift 2 p)))) (Exst A)).
apply typ_abs; [left; apply typ_prop| |discriminate].
apply typ_abs; [right| |discriminate].
 apply typ_prod; [right; trivial
   |left; setoid_replace kind with (lift 1 kind) using relation eq_trm;
     [apply weakening; apply typ_sort|simpl; split; red; reflexivity]|].
  apply typ_prod; [right; trivial|right; rewrite subst0_lift|].
   setoid_replace prop with (lift_rec 1 1 prop) using relation eq_trm at 2;
     [apply weakening_bind; trivial|simpl; split; red; reflexivity].

   setoid_replace prop with (lift 3 prop) using relation eq_trm at 2;
     [apply typ_var; trivial|simpl; split; red; reflexivity].

 setoid_replace (Ref 1) with (subst (lift 2 p) (Ref 2)) using relation eq_trm; [
   |unfold subst; rewrite red_sigma_var_gt; [reflexivity|omega]].
 apply typ_app with (V:=(lift 2 (subst a A))); 
   [| |destruct A; [discriminate|trivial]|discriminate].
  do 2 rewrite split_lift with (n:=1). do 2 apply weakening; trivial.

  assert (eq_trm (Prod (lift 2 (subst a A)) (Ref 2)) 
    (subst (lift 2 a) (Prod (subst (Ref 0) (lift_rec 3 1 A)) (Ref 3)))).
   unfold subst at 2. rewrite red_sigma_prod. rewrite red_sigma_var_gt; [|omega].
   apply Prod_morph; [rewrite subst0_lift|reflexivity].
    apply eq_trm_intro; intros.
     unfold lift, subst. rewrite int_lift_rec_eq.
     do 2 rewrite int_subst_rec_eq. do 2 rewrite int_lift_rec_eq. do 5 rewrite V.lams0.
     rewrite <- V.cons_lams; [rewrite V.lams0|do 2 red; intros; rewrite H]; reflexivity.

     unfold lift, subst. rewrite tm_lift_rec_eq.
     do 2 rewrite tm_subst_rec_eq. do 2 rewrite tm_lift_rec_eq. do 5 rewrite I.lams0. 
     rewrite <- I.cons_lams; [rewrite I.lams0|do 2 red; intros; rewrite H]; reflexivity.

     destruct A; simpl; trivial.

   rewrite H; clear H.
   apply typ_app with (V:=(lift 2 sort)); [| | |discriminate].
    do 2 rewrite split_lift with (n:=1). do 2 apply weakening; trivial.

    assert (eq_trm (Prod (subst (Ref 0) (lift_rec 3 1 A)) (Ref 3))
      (lift_rec 1 1 (Prod (subst (Ref 0) (lift_rec 2 1 A)) (Ref 2)))).
     rewrite red_lift_prod. rewrite eq_trm_lift_ref_fv by omega.
     apply Prod_morph; [|simpl plus; reflexivity].
      do 2 rewrite subst0_lift. rewrite lift_rec_acc; [simpl; reflexivity|omega].

    rewrite H; clear H. rewrite split_lift with (n:=1).
    unfold lift at 2. rewrite <- red_lift_prod. apply typ_var; trivial.

    case_eq sort; intros; [discriminate|apply sort_not_kind in H; contradiction].
Qed.
          
Lemma Exst_elim : forall e t1 t2 A C, 
  typ (sort::e) A prop -> 
  typ e C prop -> 
  typ e t1 (Exst A) ->
  typ (A::sort::e) t2 (lift 2 C) ->
  exists t, typ e t C.
intros e t1 t2 A C HA HC Ht1 Ht2.
exists (App (App t1 C) (Abs sort (Abs A t2))).
red; intros i j Hok.
generalize HC; intros HSC.
apply red_typ with (1:=Hok) in HSC; [destruct HSC as (HSC, _)|discriminate].
revert i j Hok; fold (typ e (App (App t1 C) (Abs sort (Abs A t2))) C).
apply typ_abs in Ht2; [|right|destruct C; [discriminate|]]; trivial.
apply typ_abs in Ht2; [|left; apply typ_sort|discriminate].

assert (eq_trm C (subst (Abs sort (Abs A t2)) (lift 1 C))).
 unfold subst; rewrite subst_lift_lt; [rewrite lift0; reflexivity|omega].

rewrite H at 2; clear H.
apply typ_app with (V:=(Prod sort (Prod A (lift 2 C))));
  [|unfold Exst in Ht1|discriminate|destruct C; [discriminate|]]; trivial.
assert (eq_trm (Prod (Prod sort (Prod A (lift 2 C))) (lift 1 C))
  (subst C (Prod (Prod (lift 1 sort) (Prod (subst (Ref 0) (lift_rec 2 1 A)) ((Ref 2)))) (Ref 1)))).
 unfold subst. do 3 rewrite red_sigma_prod. 
 rewrite (subst0_lift A 1). do 2 (rewrite red_sigma_var_eq; [|trivial]).
 rewrite subst_lift_lt; [rewrite lift0|omega].
 apply Prod_morph; [|reflexivity].
  apply Prod_morph; [reflexivity|].
   apply Prod_morph; [|reflexivity].
    apply eq_trm_intro; [| |destruct A; simpl; trivial]; intros.
     rewrite int_subst_rec_eq. rewrite int_lift_rec_eq.
     apply int_morph; [do 2 red; intros|reflexivity].
      destruct a; unfold V.lams, V.shift; simpl; intros; 
        [|replace (a-0) with a by omega]; reflexivity.

     rewrite tm_subst_rec_eq. rewrite tm_lift_rec_eq.
     apply tm_morph; [do 2 red; intros|reflexivity].
      destruct a; unfold I.lams, I.shift; simpl; intros; 
        [|replace (a-0) with a by omega]; reflexivity.

rewrite H; clear H.
apply typ_app with (V:=prop); [| |discriminate|discriminate]; trivial.
Qed.

(*Equation is encoded impredicatively*)
Lemma EQ_trm_typ : forall x y e, 
  typ e x sort ->
  typ e y sort ->
  typ e (EQ_trm x y) prop.
intros; apply typ_prod; [right; trivial|left|].
 apply typ_prod; [left; trivial|left; apply typ_sort|apply typ_prop].

 apply typ_prod; [right; trivial|right|].
  setoid_replace prop with (subst (lift 1 x) prop) using relation eq_trm at 2;
    [|simpl; split; red; reflexivity].
  apply typ_app with (V:=(lift 1 sort)); 
    [apply weakening; trivial| | |discriminate].
   setoid_replace (Prod (lift 1 sort) prop) with (lift 1 (Prod sort prop)) using relation eq_trm;
     [apply typ_var; trivial
       |unfold lift; rewrite red_lift_prod; apply Prod_morph; [|simpl; split; red]; reflexivity].

   case_eq sort; intros H1; [discriminate|apply sort_not_kind in H1; contradiction].
  
  setoid_replace prop with (subst (lift 2 y) prop) using relation eq_trm at 2;
    [|simpl; split; red; reflexivity].
  apply typ_app with (V:=(lift 2 sort)); 
    [do 2 rewrite split_lift with (n:=1); do 2 apply weakening; trivial| | |discriminate].
   setoid_replace (Prod (lift 2 sort) prop) with (lift 2 (Prod sort prop)) using relation eq_trm;
     [apply typ_var; trivial|].
    unfold lift; rewrite red_lift_prod; apply Prod_morph; [|simpl; split; red]; reflexivity.

   case_eq sort; intros H1; [discriminate|apply sort_not_kind in H1; contradiction].
Qed.

End SemLogic.


(************************************************************************************************)
(*This module represents axioms and prove them*)
(************************************************************************************************)
Module Type SemanticAx (M : AbsSemSig).

Include SemLogic M.

(*Specific theory axioms. Required : they can be proved in the SN model*)
Parameter ax : Prop.
Parameter ax_provable : ax.

End SemanticAx.


(************************************************************************************************)
(*Full interpretation of the theory*)
(************************************************************************************************)
Module Type TheorySem.

Declare Module sig : AbsSemSig.
Export sig.

Declare Module ax : SemanticAx sig.
Export ax.

End TheorySem.





