Require Import List.
Require Import Compare_dec.
Require Import Omega.

(******************************************************************************************)
(*It is the syntax model of the theory*)
(******************************************************************************************)
Module Type TheorySyn.

(*The set of first-order terms*)
Parameter foterm : Set.

(*Lift term*)
Parameter lift_trm_rec : foterm -> nat -> nat -> foterm.
Definition lift_trm t n := lift_trm_rec t n 0.

(*Substitute term*)
Parameter subst_trm_rec : foterm -> foterm -> nat -> foterm.
Definition subst_trm M N := subst_trm_rec M N 0.

(*fv_trm_rec list all free variables in a term with a binder k*)
(*The free variables are used for indexes in a context in which the term is well typed*)
(*So, the free variables are subtracted by the binder k*)
Parameter fv_trm_rec : foterm -> (*k*)nat -> list nat.
Definition fv_trm t := fv_trm_rec t 0.

(*First-order formula*)
Parameter 
  (foformula : Set)
  (eq_fotrm : foterm -> foterm -> foformula)
  (TF : foformula)
  (BF   : foformula)
  (neg : foformula -> foformula)
  (conj : foformula -> foformula -> foformula)
  (disj : foformula -> foformula -> foformula)
  (implf : foformula -> foformula -> foformula)
  (fall : foformula -> foformula)
  (exst : foformula -> foformula).

(*Lift formula*)
Parameter lift_fml_rec : foformula -> nat -> nat -> foformula.
Definition lift_fml t n := lift_fml_rec t n 0.
Parameter lift_fml_split : forall f n k, 
  lift_fml_rec f (S n) k = lift_fml_rec (lift_fml_rec f n k) 1 k.

(*Substitute formula*)
Parameter subst_fml_rec : foformula -> foterm -> nat -> foformula.
Definition subst_fml f N := subst_fml_rec f N 0.

(*Free variables in a formula, the idea is the same with definition fv_trm*)
Parameter fv_fml_rec : foformula -> nat -> list nat.
Definition fv_fml f := fv_fml_rec f 0.
Parameter fv_fml_eq_trm : forall x y,
  fv_fml (eq_fotrm x y) = (fv_trm x) ++ (fv_trm y).
Parameter fv_fml_neg : forall f,
  fv_fml (neg f) = fv_fml f.
Parameter fv_fml_conj : forall x y,
  fv_fml (conj x y) = (fv_fml x) ++ (fv_fml y).
Parameter fv_fml_disj : forall x y,
  fv_fml (disj x y) = (fv_fml x) ++ (fv_fml y).
Parameter fv_fml_implf : forall x y,
  fv_fml (implf x y) = (fv_fml x) ++ (fv_fml y).
Parameter fv_fml_fall : forall f,
  fv_fml (fall f) = (fv_fml_rec f 1).
Parameter fv_fml_exst : forall f,
  fv_fml (exst f) = (fv_fml_rec f 1).
Parameter in_S_fv_fml : forall f n k, 
  In (S n) (fv_fml_rec f k) <-> In n (fv_fml_rec f (S k)).
Parameter in_fv_fml_subst : forall f n N k k',
  In (S n) (fv_fml_rec f (k+k')) ->
  In n (fv_fml_rec (subst_fml_rec f N k') (k+k')).

(*Well-typed term and foformula*)
Definition hyp_ok_trm (hyp:list (option foformula)) t := 
  forall n, In n (fv_trm t) -> nth_error hyp n = Some None.
Definition hyp_ok_fml (hyp:list (option foformula)) f := 
  forall n, In n (fv_fml f) -> nth_error hyp n = Some None.

(*Theory Axioms*)
Parameter ax : list (option foformula) -> foformula -> Prop.

(*Derivation rules for the first order theory*)
Inductive deriv : list (option foformula) -> foformula -> Prop :=
| hyp_judge : forall f hyp n, 
  nth_error hyp n = Some (Some f) ->
  hyp_ok_fml hyp (lift_fml f (S n)) ->
  deriv hyp (lift_fml f (S n))
| ax_intro : forall f hyp, ax hyp f -> deriv hyp f
| true_intro : forall hyp, deriv hyp TF
| false_elim : forall hyp f, deriv hyp BF -> hyp_ok_fml hyp f -> deriv hyp f
| neg_intro : forall hyp f, deriv hyp (implf f BF) -> deriv hyp (neg f)
| neg_elim : forall hyp f, deriv hyp (neg f) -> deriv hyp (implf f BF)
| conj_intro : forall hyp f1 f2, 
  deriv hyp f1 -> deriv hyp f2 -> deriv hyp (conj f1 f2)
| conj_elim1 : forall hyp f1 f2,
  deriv hyp (conj f1 f2) -> deriv hyp f1
| conj_elim2 : forall hyp f1 f2,
  deriv hyp (conj f1 f2) -> deriv hyp f2
| disj_intro1 : forall hyp f1 f2, 
  deriv hyp f1 -> hyp_ok_fml hyp f2 -> deriv hyp (disj f1 f2)
| disj_intro2 : forall hyp f1 f2, 
  hyp_ok_fml hyp f1 ->
  deriv hyp f2 -> deriv hyp (disj f1 f2)
| disj_elim : forall hyp f1 f2 f3,
  deriv hyp (disj f1 f2) -> deriv (Some f1::hyp) (lift_fml f3 1) -> 
  deriv (Some f2::hyp) (lift_fml f3 1) -> deriv hyp f3
| impl_intro : forall hyp f1 f2,
  hyp_ok_fml hyp f1 ->
  deriv ((Some f1)::hyp) (lift_fml f2 1) -> deriv hyp (implf f1 f2)
| impl_elim : forall hyp f1 f2,
  deriv hyp (implf f1 f2) -> deriv hyp f1 -> deriv hyp f2
| fall_intro : forall hyp f,
  deriv (None::hyp) f -> deriv hyp (fall f)
| fall_elim : forall hyp f u, 
  hyp_ok_trm hyp u -> deriv hyp (fall f) -> deriv hyp (subst_fml f u)
| exst_intro : forall hyp f N, hyp_ok_trm hyp N -> 
  deriv hyp (subst_fml f N) -> deriv hyp (exst f)
| exst_elim : forall hyp f f1, 
  deriv hyp (exst f) -> 
  deriv (Some f::None::hyp) (lift_fml f1 2) -> deriv hyp f1.

(*Any derivable formula should well typed*)
Parameter deriv_well_typed : forall hyp f, deriv hyp f -> hyp_ok_fml hyp f.

Parameter hyp_ok_weakening : forall hyp t f',
  hyp_ok_fml (t :: hyp) (lift_fml f' 1) ->
  hyp_ok_fml hyp f'.

End TheorySyn.
(************************************************************************************)


Require Import GenLemmas.

Import SN_CC_Real.
Import ZF SN CCSN.


(************************************************************************************)
(*Sematic model of the first order theory*)
(************************************************************************************)

(*Constant part of the first oder theory, independent with the signature*)
Module FOTheory_Cst.

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

End FOTheory_Cst.


(*Specific part of a first-order theory, provide the signature of the theory*)
Module Type TheorySem.

Include FOTheory_Cst.

(*The sort of the theory*)
Parameter sort : trm.
Parameter sort_not_kind : sort <> kind.
Parameter sort_not_empty : exists t, forall e, typ e t sort.

(*The sort is closed, since it is first-order*)
Parameter sort_closed : forall i1 i2, 
  int i1 sort == int i2 sort.


(*The equivalence relation of the theory*)
Parameter EQ_trm : trm -> trm -> trm.

Parameter EQ_trm_typ : forall x y e, 
  typ e x sort ->
  typ e y sort ->
  typ e (EQ_trm x y) prop.

Parameter const_env : nat -> list trm.
Parameter const_env0 : const_env 0 = nil.
Parameter const_envS : forall n, const_env (S n) = sort :: (const_env n).

Parameter EQ_trm_eq_typ : forall n x y t,
  typ (const_env n) x sort ->
  typ (const_env n) y sort ->
  typ (const_env n) t (EQ_trm x y) ->
  eq_typ (const_env n) x y.

(*Fall for fall, dependent on the sort*)
Parameter Fall : trm -> trm.
Parameter Fall_typ : forall e A,
  typ (sort :: e) A prop ->
  typ e (Fall A) prop.
Parameter Fall_intro : forall e t B,
  typ (sort::e) B prop ->
  typ (sort::e) t B -> 
  typ e (Abs sort t) (Fall B).
Parameter Fall_elim : forall e t u B, 
  typ (sort::e) B prop ->
  typ e t (Fall B) -> 
  typ e u sort ->
  typ e (App t u) (subst u B).

(*Exst for exst, dependent on the sort*)
Parameter Exst : trm -> trm.
Parameter Exst_typ : forall e A,
  typ (sort::e) A prop ->
  typ e (Exst A) prop.
Parameter Exst_intro : forall e A p a, 
  typ (sort::e) A prop ->
  typ e a sort -> 
  typ e p (subst a A) ->
  exists t, typ e t (Exst A).
Parameter Exst_elim : forall e t1 t2 A C, 
  typ (sort::e) A prop -> 
  typ e C prop -> 
  typ e t1 (Exst A) ->
  typ (A::sort::e) t2 (lift 2 C) ->
  exists t, typ e t C.

(*Specific theory axioms. Required : they can be proved in the SN model*)
Parameter ax : Prop.
Parameter ax_provable : ax.

End TheorySem.
(************************************************************************************)


(************************************************************************************)
(*Interpretation form symtax model to sematic model*)
(************************************************************************************)

Require Import SN_NAT.

Module Type InterpTheory (M1 : TheorySyn) (M2 : TheorySem).

Import M1 M2.

(*Interpretation first-order term*)
Parameter intp_fotrm : foterm -> trm.

(*Interpretation is not kind*)
Parameter intp_fotrm_not_kind : forall t, intp_fotrm t <> kind.

(*Properties about lift and interpretation term*)
Parameter lift_intp_lift_trm_rec : forall t n k, 
  eq_trm (lift_rec n k (intp_fotrm t)) 
         (intp_fotrm (lift_trm_rec t n k)).
Parameter lift_intp_lift_trm : forall t n,
  eq_trm (lift n (intp_fotrm t)) 
         (intp_fotrm (lift_trm t n)).

(*Properties about substitution and interpretation term*)
Parameter subst_intp_subst_trm_rec : forall t N k, 
  eq_trm (subst_rec (intp_fotrm N) k (intp_fotrm t)) 
         (intp_fotrm (subst_trm_rec t N k)).
Parameter subst_intp_subst_trm : forall t N, 
  eq_trm (subst (intp_fotrm N) (intp_fotrm t)) 
         (intp_fotrm (subst_trm t N)).

(*Interpretation of foformula*)
Parameter intp_fofml : foformula -> trm.
Parameter intp_fofml_not_kind : forall f, intp_fofml f <> kind.
Parameter intp_eq_fml : forall x y, 
  intp_fofml (eq_fotrm x y) = EQ_trm (intp_fotrm x) (intp_fotrm y).
Parameter intp_TF : intp_fofml TF = True_symb.
Parameter intp_BF : intp_fofml BF = False_symb.
Parameter intp_neg : forall f,
  intp_fofml (neg f) = Neg (intp_fofml f).
Parameter intp_conj : forall x y,
  intp_fofml (conj x y) = Conj (intp_fofml x) (intp_fofml y).
Parameter intp_disj : forall x y,
  intp_fofml (disj x y) = Disj (intp_fofml x) (intp_fofml y).
Parameter intp_implf : forall x y,
  intp_fofml (implf x y) = Impl (intp_fofml x) (intp_fofml y).
Parameter intp_fall : forall f,
  intp_fofml (fall f) = Fall (intp_fofml f).
Parameter intp_exst : forall f,
  intp_fofml (exst f) = Exst (intp_fofml f).

(*Properties about lift and interpretation formula*)
Parameter lift_intp_lift_fml_rec : forall f n k,
  eq_trm (lift_rec n k (intp_fofml f)) 
         (intp_fofml (lift_fml_rec f n k)).      
Parameter lift_intp_lift_fml : forall f n,
  eq_trm (lift n (intp_fofml f)) 
         (intp_fofml (lift_fml f n)).

(*Properties about substitution and interpretation foformula*) 
Parameter subst_intp_subst_fml_rec : forall f N k,
  eq_trm (subst_rec (intp_fotrm N) k (intp_fofml f)) 
         (intp_fofml (subst_fml_rec f N k)).
Parameter subst_intp_subst_fml : forall f N,
  eq_trm (subst (intp_fotrm N) (intp_fofml f)) 
         (intp_fofml (subst_fml f N)).

(*Interpretation of the context*)
Parameter intp_hyp : list (option foformula) -> list trm.
Parameter intp_nil : intp_hyp nil = nil.
Parameter intp_hyp_cons_fml : forall x e,
  intp_hyp (Some x :: e) = intp_fofml x :: intp_hyp e.
Parameter intp_hyp_cons_sort : forall e,
  intp_hyp (None :: e) = sort :: intp_hyp e.
Parameter intp_hyp_nth_fml : forall hyp f n, 
  nth_error hyp n = Some (Some f) ->
  nth_error (intp_hyp hyp) n = Some (intp_fofml f).
Parameter intp_hyp_nth_trm : forall hyp n, 
  nth_error hyp n = value None ->
  nth_error (intp_hyp hyp) n = value sort.

(*The interpretation of foterm is sort*)
Parameter intp_fotrm_sort : forall hyp t,
  hyp_ok_trm hyp t ->
  typ (intp_hyp hyp) (intp_fotrm t) sort.

(*The interpretation of the foformula is prop*)
Parameter intp_fofml_prop : forall f hyp,
  hyp_ok_fml hyp f ->
  typ (intp_hyp hyp) (intp_fofml f) prop.

(*Axioms in first-order theory is provable in the associated module*)
Parameter intp_ax : forall hyp f, 
  M1.ax hyp f -> 
  exists t, typ (intp_hyp hyp) t (intp_fofml f).

End InterpTheory.