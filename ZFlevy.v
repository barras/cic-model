Require Import Sublogic.
Require Import ZFdef.
Require Import ZF.

Lemma ex_ex2 A P Q : @ex2 A P Q <-> exists x:A, P x /\ Q x.
split; destruct 1; [eauto|].
destruct H; eauto.
Qed.

Definition icons {A:Type} (x:A) (f:nat->A) (k:nat) : A :=
  match k with 0 => x | S k => f k end.

Lemma ex_set : exists _:set, True.
exists empty; trivial.
(*destruct empty_ex; eauto.*)
Qed.




  Lemma fa_eq_var_iff y P :
    Proper (eq_set==>iff) P ->
    (forall x, x == y -> P x) <-> P y.
split; intros; auto with *.
rewrite H1; trivial.
Qed.

  Lemma ex_eq_var_iff y P :
    Proper (eq_set==>iff) P ->
    (exists x, x == y /\ P x) <-> P y.
split; intros; eauto with *.
*destruct H0 as (x,(?,?)).
 rewrite <- H0; trivial.
*exists y; auto with *.
Qed.


  Lemma fa_empty_iff P : (forall x, x ∈ empty -> P x) <-> True.
split;[trivial|intros].
apply empty_ax in H0; contradiction.
Qed.

  Lemma ex_empty_iff P : (exists x, x ∈ empty /\ P x) <-> False.
split;[intros|contradiction].
destruct H as (x,(?,_)).
apply empty_ax in H; trivial.
Qed.


  Lemma fa_pair_iff a b P :
    Proper (eq_set==>iff) P ->
    (forall x, x ∈ pair a b -> P x) <-> P a /\ P b.
intros Pm.
split; intros; auto.
destruct H.
rewrite pair_ax in H0; destruct H0; rewrite H0; trivial.
Qed.

  Lemma ex_pair_iff a b P :
    Proper (eq_set==>iff) P ->
    (exists x, x ∈ pair a b /\ P x) <-> P a \/ P b.
intros Pm.
split; intros.
*destruct H as (x,(?,?)).
 apply pair_ax in H.
 destruct H; rewrite H in H0; auto.
*destruct H; [exists a|exists b]; split; trivial.
Qed.

  Lemma fa_union_iff a P :
    (forall x, x ∈ union a -> P x) <->
    (forall y, y ∈ a -> forall x, x ∈ y -> P x).
split; intros.
*apply H; apply union_ax; eauto.
*apply union_ax in H0; destruct H0; eauto.
Qed.

  Lemma ex_union_iff a P :
    (exists x, x ∈ union a /\ P x) <->
    (exists y, y ∈ a /\ exists x, x ∈ y /\ P x).
split; intros.
*destruct H as (x,(?,?)).
 apply union_ax in H; destruct H; eauto.
*destruct H as (y,(?,(x,(?,?)))); exists x; split;[|trivial].
 apply union_ax; eauto.
Qed.
  
  Lemma fa_subset_iff a P Q :
    Proper (eq_set==>iff) P ->
    (forall x, x ∈ subset a P -> Q x) <->
    (forall x, x ∈ a -> P x -> Q x).
intros Pm.
split; intros.
*apply H; apply subset_intro; trivial.
*apply subset_ax in H0; destruct H0 as (?,(x',?,?)).
 rewrite <- H1 in H2; auto.
Qed.

  Lemma ex_subset_iff a P Q :
    Proper (eq_set==>iff) P ->
    (exists x, x ∈ subset a P /\ Q x) <->
    (exists x, x ∈ a /\ (P x /\ Q x)).
intros Pm.
split; intros.
*destruct H as (x,(?,?)).
 apply subset_ax in H; destruct H as (?,(x',?,?)).
rewrite <- H1 in H2; eauto.
*destruct H as (x,(?&?&?)).
 exists x; split; trivial.
 apply subset_intro; trivial.
Qed.

  Lemma fa_replf_iff a F P :
    Proper (eq_set==>iff) P ->
    ext_fun a F ->
    (forall x, x ∈ replf a F -> P x) <-> (forall z, z ∈ a -> P (F z)).
intros Pm Fext.
split; intros.
*apply H.
 rewrite replf_ax; eauto with *.
*rewrite replf_ax in H0; trivial.
 destruct H0 as (z,?,?).
 rewrite H1; auto.
Qed.


  
(* Levy's ΣΠ hierarchy adapted to intuitionistic formulas *)

Inductive qu := Sig | Prd.

Definition opp := fun k => match k with Sig => Prd | Prd => Sig end.

Definition var_set := list set.
Definition is_var (a:set) (v:var_set) := In a v.
Definition push_var (a:set)(v:var_set) := a::v.

Definition incl_vars (v1 v2:var_set) :=
  forall x, is_var x v1 -> is_var x v2.

Lemma push_var_incl x v1 v2 :
  incl_vars v1 v2 -> incl_vars (x::v1) (x::v2).
unfold incl_vars, is_var; simpl.
destruct 2; auto.
Qed.
Hint Resolve push_var_incl : core.

(* [vars] is used to aoid using Skolem symbols *)
Inductive levy (vars : var_set) : qu -> nat -> Prop -> Prop :=
| F_ext A B k n : (A<->B) -> levy vars k n A -> levy vars k n B
(* Delta 0 *)
| F_eq x y k n : is_var x vars -> is_var y vars -> levy vars k n (x == y)
| F_in x y k n : is_var x vars -> is_var y vars -> levy vars k n (x ∈ y)
| F_T k n : levy vars k n True
| F_F k n : levy vars k n False
| F_and A B k n : levy vars k n A -> levy vars k n B -> levy vars k n (A/\B)
| F_or A B k n  : levy vars k n A -> levy vars k n B -> levy vars k n (A\/B)
| F_imp A B k n : levy vars (opp k) n A -> levy vars k n B -> levy vars k n (A->B)
| F_bfa A B k n : is_var A vars ->
                  (forall x, levy (push_var x vars) k n (B x)) ->
                  levy vars k n (forall x:set, x ∈ A -> B x)
| F_bex A B k n : is_var A vars ->
                  (forall x, levy (push_var x vars) k n (B x)) ->
                  levy vars k n (exists x:set, x ∈ A /\ B x)
(* unbounded quantifiers *)
| F_fa_prd B n : (forall x, levy (push_var x vars) Prd (S n) (B x)) -> levy vars Prd (S n) (forall x:set, B x)
| F_fa_alt B n : (forall x, levy (push_var x vars) Sig n     (B x)) -> levy vars Prd (S n) (forall x:set, B x)
| F_ex_sig B n : (forall x, levy (push_var x vars) Sig (S n) (B x)) -> levy vars Sig (S n) (exists x:set, B x)
| F_ex_alt B n : (forall x, levy (push_var x vars) Prd n     (B x)) -> levy vars Sig (S n) (exists x:set, B x).

Parameter F_bfa_ext : forall vars A B k n, (forall x, levy (push_var x vars) k n (x ∈ A)) ->
                  (forall x, levy (push_var x vars) k n (B x)) ->
                  levy vars k n (forall x:set, x ∈ A -> B x).
Parameter F_bex_ext : forall vars A B k n, (forall x, levy (push_var x vars) k n (x ∈ A)) ->
                  (forall x, levy (push_var x vars) k n (B x)) ->
                  levy vars k n (exists x:set, x ∈ A /\ B x).

Instance form_morph : forall vars k n, Proper (iff ==> iff) (levy vars k n).
do 2 red; intros.
split; apply F_ext; auto with *.
Qed.

Lemma F_bex2 vars A B k n :
  is_var A vars ->
  (forall x, levy (push_var x vars) k n (B x)) ->
  levy vars k n (exists2 x:set, x ∈ A & B x).
intros.
rewrite ex_ex2.
constructor; trivial.
Qed.

Lemma F_bex2_ext vars A B k n :
  (forall x, levy (push_var x vars) k n (x ∈ A)) ->
  (forall x, levy (push_var x vars) k n (B x)) ->
  levy vars k n (exists2 x:set, x ∈ A & B x).
intros.
rewrite ex_ex2.
apply F_bex_ext; trivial.
Qed.


Lemma dummy_ex (A:Prop) : A -> exists _:set, A.
intros.
destruct ex_set; eauto.
Qed.
Lemma dummy_fa (A:Prop) : (set->A) -> A.
intros.
destruct ex_set; auto.
Qed.

Lemma levy_thin_vars vars vars' k n A :
  levy vars k n A ->
  incl_vars vars vars' ->
  levy vars' k n A.
intros Hl; revert vars'; induction Hl; intros; try (constructor; eauto; fail).
apply F_ext with A; auto.
Qed.

Lemma levy_str v k n x A :
  is_var x v ->
  levy (push_var x v) k n A ->
  levy v k n A.
intros; apply levy_thin_vars with (push_var x v); trivial.
destruct 1; subst; simpl; auto.
Qed.

Lemma levy_thin1 x vars k n A :
  levy vars k n A ->
  levy (push_var x vars) k n A.
intros; apply levy_thin_vars with (1:=H).
red; simpl; auto.
Qed.
Lemma levy_thin2 x y vars k n A :
  levy (push_var y vars) k n A ->
  levy (push_var y (push_var x vars)) k n A.
intros; apply levy_thin_vars with (1:=H).
red; destruct 1; simpl; auto.
Qed.
Lemma levy_thin3 x y z vars k n A :
  levy (push_var z (push_var y vars)) k n A ->
  levy (push_var z (push_var y (push_var x vars))) k n A.
intros; apply levy_thin_vars with (1:=H).
red; destruct 1 as [?|[?|?]]; simpl; auto.
Qed.
Hint Resolve levy_thin1 levy_thin2 levy_thin3 : core.

  Lemma levy_dummy_ex vars n A :
    levy vars Prd n     A ->
    levy vars Sig (S n) A.
intros.
apply F_ext with (exists _:set, A). 
split;[destruct 1;trivial|apply dummy_ex].
apply F_ex_alt; intros z; auto.
Qed.

  Lemma levy_dummy_fa vars n A :
    levy vars Sig n     A ->
    levy vars Prd (S n) A.
intros.
apply F_ext with (set -> A). 
split;[apply dummy_fa|auto].
apply F_fa_alt; intros z; auto.
Qed.

  Lemma levy0 vars k k' A :
    levy vars k  0 A ->
    levy vars k' 0 A.
intros Hl; revert k'.
remember 0 as n.
revert Heqn.
induction Hl; intros; try (discriminate || constructor; eauto; fail).
apply F_ext with A; auto.
Qed.
  

  Lemma levy_lift vars k k' n A :
    levy vars k  n     A ->
    levy vars k' (S n) A.
intros Hl; revert k'; induction Hl; intros; try (constructor; eauto; fail).
*apply F_ext with A; trivial.
*destruct k'.
 +apply levy_dummy_ex.
  constructor; trivial.
 +constructor; auto.
*destruct k'.
 +apply levy_dummy_ex.
  constructor; trivial.
 +apply F_fa_alt; trivial.
*destruct k'.
 +constructor; auto.
 +apply levy_dummy_fa.
  constructor; trivial.
*destruct k'.
 +apply F_ex_alt; auto.
 +apply levy_dummy_fa.
  constructor; trivial.
Qed.


  Module FO.

Definition pvar (f:var_set -> set) : Prop :=
  exists n, forall i, List.nth_default empty i n == f i.


Definition bind (B:set->var_set->Prop) (i:var_set) : Prop :=
  match i with
  | x::i => B x i
  | _ => True
  end.
  
Inductive plevy : qu -> nat -> (var_set->Prop) -> Prop :=
| PF_ext A B k n : (forall i, A i<->B i) -> plevy k n A -> plevy k n B
(* Delta 0 *)
| PF_eq x y k n : pvar x -> pvar y -> plevy k n (fun i=> x i == y i)
| PF_in x y k n : pvar x -> pvar y -> plevy k n (fun i=>x i ∈ y i)
| PF_T k n : plevy k n (fun _=>True)
| PF_F k n : plevy k n (fun _=>False)
| PF_and A B k n : plevy k n A -> plevy k n B -> plevy k n (fun i =>A i/\B i)
| PF_or A B k n  : plevy k n A -> plevy k n B -> plevy k n (fun i =>A i\/B i)
| PF_imp A B k n : plevy (opp k) n A -> plevy k n B -> plevy k n (fun i=>A i->B i)
| PF_bfa A B k n : pvar A ->
                   plevy k n (bind B) ->
                   plevy k n (fun i=>forall x:set, x ∈ A i -> B x i)
| PF_bex A B k n : pvar A ->
                   plevy k n (bind B) ->
                   plevy k n (fun i =>exists x:set, x ∈ A i /\ B x i)
(* unbounded quantifiers *)
| PF_fa_prd B n : plevy Prd (S n) (bind B) -> plevy Prd (S n) (fun i=>forall x:set, B x i)
| PF_fa_alt B n : plevy Sig n     (bind B) -> plevy Prd (S n) (fun i=>forall x:set, B x i)
| PF_ex_sig B n : plevy Sig (S n) (bind B) -> plevy Sig (S n) (fun i=>exists x:set, B x i)
| PF_ex_alt B n : plevy Prd n     (bind B) -> plevy Sig (S n) (fun i=>exists x:set, B x i).

Inductive form :=
| feq (n m:nat)
| fin (n m:nat)
| ftr | ffa
| f_and (f1 f2:form)
| f_or (f1 f2:form)
| f_imp (f1 f2:form)
| f_fa (f:form)
| f_ex (f:form).

Fixpoint fint (f:form) : var_set -> Prop :=
  match f with
  | feq n m => fun i => List.nth_default empty i n == List.nth_default empty i m
  | fin n m => fun i => List.nth_default empty i n ∈ List.nth_default empty i m
  | ftr => fun _ => True | ffa => fun _ => False
  | f_and P Q => fun i => fint P i /\ fint Q i
  | f_or P Q => fun i => fint P i \/ fint Q i
  | f_imp P Q => fun i => fint P i -> fint Q i
  | f_fa P => fun i => forall x:set, fint P (push_var x i)
  | f_ex P => fun i => exists x:set, fint P (push_var x i)
  end.

(*Fixpoint frel (M *)

Lemma plevy_levy k n A :
  plevy k n A -> forall i, levy i k n (A i).
induction 1.
*intros; apply F_ext with (A i); auto.
*destruct H.
 destruct H0.
 constructor.
 admit.
 admit.
*admit.
*constructor.
*constructor.
*constructor; trivial. 
*constructor; trivial. 
*constructor; trivial. 
*constructor.
 admit.
 intros; apply (IHplevy (x::i)).
*constructor.
 admit.
 intros; apply (IHplevy (x::i)).
*intros; apply F_fa_prd.
 intros; apply (IHplevy (x::i)).
*intros; apply F_fa_alt.
 intros; apply (IHplevy (x::i)).
*intros; apply F_ex_sig.
 intros; apply (IHplevy (x::i)).
*intros; apply F_ex_alt.
 intros; apply (IHplevy (x::i)).
Admitted.

  

  Lemma plevy_ex_form k n A :
  plevy k n A -> exists f, forall i, A i <-> fint f i.
induction 1.
*destruct IHplevy as (f,?); exists f; intros.
 rewrite <-H; trivial.
*destruct H; destruct H0.
 exists (feq x0 x1); simpl; intros.
 rewrite H,H0; reflexivity. 
*destruct H; destruct H0.
 exists (fin x0 x1); simpl; intros.
 rewrite H,H0; reflexivity. 
*exists ftr; reflexivity.
*exists ffa; reflexivity.
*destruct IHplevy1; destruct IHplevy2.
 exists (f_and x x0); intros; apply and_iff_morphism; trivial.
*destruct IHplevy1; destruct IHplevy2.
 exists (f_or x x0); intros; apply or_iff_morphism; trivial.
*destruct IHplevy1; destruct IHplevy2.
 exists (f_imp x x0); intros; apply impl_morph; trivial.
*destruct H; destruct IHplevy.
 exists (f_fa (f_imp (fin 0 (S x)) x0)); simpl; unfold nth_default; simpl.
 intros; apply fa_morph; intros.
 apply impl_morph; intros.
 2:apply (H1 (x1::i)).
 unfold nth_default in H.
 rewrite H; reflexivity.
*destruct H; destruct IHplevy.
 exists (f_ex (f_and (fin 0 (S x)) x0)); simpl; unfold nth_default; simpl.
 intros; apply ex_morph; intro.
 apply and_iff_morphism; intros.
 2:apply (H1 (a::i)).
 unfold nth_default in H.
 rewrite H; reflexivity.
*destruct IHplevy.
 exists (f_fa x); simpl.
 intros; apply fa_morph; intros.
 apply (H0 (x0::i)).
*destruct IHplevy.
 exists (f_fa x); simpl.
 intros; apply fa_morph; intros.
 apply (H0 (x0::i)).
*destruct IHplevy.
 exists (f_ex x); simpl.
 intros; apply ex_morph; intro.
 apply (H0 (a::i)).
*destruct IHplevy.
 exists (f_ex x); simpl.
 intros; apply ex_morph; intro.
 apply (H0 (a::i)).
Qed.

(*
Inductive plevy : qu -> nat -> (var_set->Prop) -> Prop :=
| PF_ext A B k n : (forall i, A i<->B i) -> plevy k n A -> plevy k n B
(* Delta 0 *)
| PF_eq x y k n : pvar x -> pvar y -> plevy k n (fun i=> x i == y i)
| PF_in x y k n : pvar x -> pvar y -> plevy k n (fun i=>x i ∈ y i)
| PF_T k n : plevy k n (fun _=>True)
| PF_F k n : plevy k n (fun _=>False)
| PF_and A B k n : plevy k n A -> plevy k n B -> plevy k n (fun i =>A i/\B i)
| PF_or A B k n  : plevy k n A -> plevy k n B -> plevy k n (fun i =>A i\/B i)
| PF_imp A B k n : plevy (opp k) n A -> plevy k n B -> plevy k n (fun i=>A i->B i)
| PF_bfa A B k n : pvar A ->
                   plevy k n B ->
                   plevy k n (fun i=>forall x:set, x ∈ A i -> B (push_var x i))
| PF_bex A B k n : pvar A ->
                   plevy k n B ->
                   plevy k n (fun i =>exists x:set, x ∈ A i /\ B (push_var x i))
(* unbounded quantifiers *)
| PF_fa_prd B n : plevy Prd (S n) B -> plevy Prd (S n) (fun i=>forall x:set, B (push_var x i))
| PF_fa_alt B n : plevy Sig n     B -> plevy Prd (S n) (fun i=>forall x:set, B (push_var x i))
| PF_ex_sig B n : plevy Sig (S n) B -> plevy Sig (S n) (fun i=>exists x:set, B (push_var x i))
| PF_ex_alt B n : plevy Prd n     B -> plevy Sig (S n) (fun i=>exists x:set, B (push_var x i)).
*)

End FO.
  
(**)
(*
  Definition bounded k v n a :=
    exists x, is_var x v /\ exists R, forall z, z ∈ a <->  *)
  
  Lemma levy_eq_set v k n a b:
  levy v k n (a ⊆ b) ->
  levy v k n (b ⊆ a) ->
  levy v k n (a==b).
intros lva lvb.
apply F_ext with (a ⊆ b /\ b ⊆ a); [|constructor; trivial].
rewrite eq_set_ax.
split; [destruct 1; split; auto|].
intros.
split; red; intros; apply H; auto.
Qed.
  
  Definition levy_set v k n (a:set) :=
    forall z, levy (push_var z v) k n (z ∈ a).

  Definition levy_set_eq v k n (a:set) :=
    forall z, levy (push_var z v) k n (z == a).

  Lemma levy_set_thin1 x vars k n a :
    levy_set vars k n a ->
    levy_set (push_var x vars) k n a.
intros lva z; apply levy_thin_vars with (1:=lva z).
destruct 1; simpl; auto.
Qed.
  Lemma levy_set_thin2 x y vars k n a :
    levy_set (push_var y vars) k n a ->
    levy_set (push_var y (push_var x vars)) k n a.
intros lva z; apply levy_thin_vars with (1:=lva z).
destruct 1 as [?|[?|?]]; simpl; auto.
Qed.
Hint Resolve levy_set_thin1 levy_set_thin2 : core.

  
  Lemma levy_incl_set v k n x b:
    is_var x v -> (*levy_set v k n a ->*)
    levy_set v k n b ->
    levy v k n (x ⊆ b).
constructor; trivial.
Qed.

(*
  Lemma levy_incl_set v k n x b:
    is_var x v -> (*levy_set v k n a ->*)
    levy_set v k n b ->
    levy v k n (x ⊆ b).
constructor; trivial.
Qed.
*)

  Lemma in_set_def a x :
    a ∈ x <-> exists y, y ∈ x /\ y==a.
split; [exists a; split; auto with *|destruct 1 as (y,(?,?))].
rewrite <- H0; trivial.
Qed.
    
    
Lemma ex_eq_delta v n a P :
  Proper (eq_set==>iff) P ->
  levy_set_eq v Sig (S n) a ->
  (forall k x, levy (push_var x v) k (S n) (P x)) ->
  forall k, levy v k (S n) (exists x, x==a /\ P x).
intros.
destruct k.
*apply F_ex_sig; constructor;[apply H0|apply H1].
*apply F_ext with (forall x, x==a -> P x).
 {apply forall_eq_intro; intros.
  split;[ exists x';auto|destruct 1].
  destruct H3.
  rewrite H2,<-H3; trivial. }
 apply F_fa_prd; intros.
 constructor.
 apply H0. 
 apply H1.
Qed.

Lemma fa_in_delta v n a P :
  Proper (eq_set ==> iff) P ->
  levy_set_eq v Sig (S n) a ->
  (forall k x, levy (push_var x v) k (S n) (P x)) ->
  forall k, levy v k (S n) (forall x, x ∈ a -> P x).
intros Pm lva lvP k.
apply F_ext with (exists y, y==a /\ forall x, x∈y -> P x).
{split; intros.
 *destruct H as (y,(eqy,?)).
  rewrite <-eqy in H0; auto.
 *exists a; split; [reflexivity|trivial]. }
apply  ex_eq_delta; trivial.
*intros ?? h; apply fa_morph; intro; rewrite h; reflexivity.
*intros.
 constructor; [simpl; auto|].
 intros.
 apply levy_thin2; auto.
Qed.
Lemma ex_in_delta v n a P :
  Proper (eq_set ==> iff) P ->
  levy_set_eq v Sig (S n) a ->
  (forall k x, levy (push_var x v) k (S n) (P x)) ->
  forall k, levy v k (S n) (exists x, x ∈ a /\ P x).
intros Pm lva lvP k.
apply F_ext with (exists y, y==a /\ exists x, x∈y /\ P x).
{split; intros.
 *destruct H as (y,(eqy,(x,(?,?)))).
  rewrite eqy in H; eauto.
 *exists a; split; [reflexivity|trivial]. }
apply  ex_eq_delta; trivial.
*intros ?? h; apply ex_morph; intro; rewrite h; reflexivity.
*intros.
 constructor; [simpl; auto|].
 intros.
 apply levy_thin2; auto.
Qed.

Lemma levy_cut_delta (v : var_set) (n : nat) (P : set -> Prop) (y : set) :
  Proper (eq_set ==> iff) P ->
  levy_set_eq v Sig (S n) y ->
  (forall x k, levy (x :: v) k (S n) (P x)) ->
  forall k, levy v k (S n) (P y).
intros Pm lvy lvP k.
apply F_ext with (exists x:set, x==y /\ P x).
{split;intros;[|exists y; auto with *].
 destruct H as (x&eqx&?); rewrite <-eqx; trivial. }
apply ex_eq_delta; trivial.
Qed.


  

(* Some Δ_0 formlulae *)
  Lemma levy_empty v k n : levy_set v k n empty.
intros z.
setoid_replace (z ∈ empty) with False; [constructor|].
split; [apply empty_ax|contradiction].
Qed.

  Lemma levy_fa_empty v k n P :
    levy v k n (forall x, x ∈ empty -> P x).
rewrite fa_empty_iff.
constructor.      
Qed.

  Lemma levy_empty_eq v k n : levy_set_eq v k n empty.
intros z.
apply levy_eq_set.
*apply levy_incl_set; [simpl; auto|].
 apply levy_empty.
*apply levy_fa_empty.
Qed.
    
  Lemma levy_pair v k n a b :
    is_var a v -> is_var b v -> levy_set v k n (pair a b).
intros va vb z; rewrite pair_ax.
constructor; constructor; simpl; auto.
Qed.

  
  Lemma levy_pair_eq v k n a b :
    is_var a v -> is_var b v -> levy_set_eq v k n (pair a b).
intros va vb x; apply levy_eq_set.
*constructor;[simpl; auto|].
 intros z.
 apply levy_pair; simpl; auto.
*unfold incl_set; rewrite fa_pair_iff.
 +constructor; constructor; simpl; auto.
 +do 2 red; intros ? ? h; rewrite h; reflexivity. 
Qed.
 
  Lemma levy_set_pair v k n a b :
    levy_set_eq v k n a ->
    levy_set_eq v k n b ->
    levy_set v k n (pair a b).
intros lva lvb z.
rewrite pair_ax.
constructor; trivial.
Qed.

  Lemma levy_set_pair_eq v k n a b : 
    levy_set_eq v k n a ->
    levy_set_eq v k n b ->
    levy_set_eq v k n (pair a b).
intros lva lvb x.
apply levy_eq_set.
*constructor;[simpl; auto|].
 intros z.
 apply levy_set_pair; auto.
 intros z'; apply levy_thin2; trivial.
 intros z'; apply levy_thin2; trivial.
*unfold incl_set; rewrite fa_pair_iff.
 constructor.
 rewrite in_set_def; constructor; [simpl; auto|].
 intros z'; apply levy_thin2; trivial.
 rewrite in_set_def; constructor; [simpl; auto|].
 intros z'; apply levy_thin2; trivial.
 intros ?? h; rewrite h; reflexivity.
Qed.

  Lemma union_def z a :
    z ∈ union a <-> exists y, y ∈ a /\ z ∈ y.
rewrite union_ax.
split; destruct 1; eauto.
destruct H; eauto.
Qed.
  
  Lemma levy_union v k n a :
    is_var a v ->
    levy_set v k n (union a).
intros va x.
rewrite union_def.
constructor; [simpl; auto|].
constructor; simpl; auto.
Qed.

  Lemma levy_union_eq v k n a :
    is_var a v ->
    levy_set_eq v k n (union a).
intros va x.
apply levy_eq_set.
*constructor; [simpl; auto|].
 apply levy_union; simpl; auto.
*unfold incl_set.
 rewrite fa_union_iff.
 constructor; [simpl; auto|].
 constructor; [simpl; auto|].
 constructor; simpl; auto.
Qed.

(*
  Lemma fa_power_iff a P :
    (forall x, x ∈ power a -> P x) <-> (forall x, x ⊆ a -> P x).
*)
  Lemma levy_power v k n a :
    is_var a v ->
    levy_set v k n (power a).
intros va x.
rewrite power_ax.
constructor; [simpl; auto|].
constructor; simpl; auto.
Qed.


  (* power set is Π_1 *)
  Lemma levy_power_eq v n a :
    is_var a v ->
    levy_set_eq v Prd (S n) (power a).
intros va x.
apply levy_eq_set.
*constructor; [simpl;auto|].
 intros; apply levy_power; simpl; auto.
*apply F_fa_prd.
 constructor; [apply levy_power; simpl; auto|].
 constructor; simpl; auto.
Qed.


  Lemma levy_subset v k n a P :
    is_var a v ->
    (forall x, levy (x::v) k n (P x)) ->
    levy_set v k n (subset a P).
intros va lvP z.
setoid_replace (z ∈ subset a P) with (exists z', z' ∈ a /\ z==z' /\ P z').
*constructor; [simpl; auto|].
 intros x; constructor; [constructor; simpl; auto|auto].
*rewrite subset_ax.
 split; destruct 1.
  destruct H0 as (x',?,?); exists x'; split; [|split]; auto with *.
  rewrite <- H0; trivial.

  destruct H as (?&?&?).
  rewrite H0; split; [trivial|exists x; trivial].
Qed.

  Lemma levy_subset_eq v k n a P :
    Proper (eq_set==>iff) P ->
    is_var a v ->
    (* P is Δ_n *)
    (forall k' x, levy (x::v) k' n (P x)) ->
    levy_set_eq v k n (subset a P).
intros Pm va lvP z.
apply levy_eq_set.
*constructor; [simpl;auto|].
 intros; apply levy_subset; simpl; auto.
*unfold incl_set; rewrite fa_subset_iff; trivial.
 constructor;[simpl; auto|].
 intros x.
 constructor;[|constructor; simpl; auto].
 apply levy_thin2; auto.
Qed.
  
  Lemma levy_replf v k n a F :
    ext_fun a F ->
    is_var a v ->
    (forall x, levy_set_eq (x::v) k n (F x)) ->
    levy_set v k n (replf a F).
intros Fext va lvF z.
rewrite replf_ax; trivial.
apply F_bex2; [simpl; auto|].
intros x.
apply levy_thin_vars with (1:=lvF x z).
destruct 1 as [?|[?|?]]; simpl; auto.
Qed.

(*  
  Lemma levy_replf_eq v k n a F :
    ext_fun a F ->
    is_var a v ->
    (forall x, levy_set_eq (x::v) k n (F x)) ->
    levy_set_eq v k n (replf a F).
intros Fext va lvF z.
apply levy_eq_set.
*constructor; [simpl; auto|].
 apply levy_replf; simpl; auto.
 intros x z'.
 apply levy_thin_vars with (1:=lvF x z').
 destruct 1 as [?|[?|?]]; simpl; auto.
*unfold incl_set; rewrite fa_replf_iff; trivial.
 2:do 2 red; intros ?? h; rewrite h; reflexivity.
 constructor; [simpl; auto|].

  Qed.
 *)
  

  Require Import ZFpairs.

  Transparent couple.

  Lemma levy_couple v k n a b :
    levy_set_eq v k n a ->
    levy_set_eq v k n b ->
    levy_set v k n (couple a b).
unfold couple.
intros lva lvb.
apply levy_set_pair; apply levy_set_pair_eq; trivial.
Qed.

  Lemma levy_couple_eq v k n a b :
    levy_set_eq v k n a ->
    levy_set_eq v k n b ->
    levy_set_eq v k n (couple a b).
intros lva lvb x.
unfold couple.
apply levy_set_pair_eq; apply levy_set_pair_eq; trivial.
Qed.

  Lemma prodcart_def x a b :
    x ∈ prodcart a b <-> exists y, y∈a /\ exists z, z∈b /\ x == couple y z.
*split; [intros|].
+exists (fst x); split.
 apply fst_typ with (1:=H).
 exists (snd x); split.
 apply snd_typ with (1:=H).
 apply surj_pair with (1:=H).
+destruct 1 as (y&?&z&?&?).
 rewrite H1; apply couple_intro; trivial.
Qed.

  Lemma fa_prodcart_iff a b P :
    Proper (eq_set ==> iff) P ->
    (forall x, x ∈ prodcart a b -> P x) <->
      (forall x, x∈a -> forall y, y∈b -> P (couple x y)).
intros Pm; split; intros.
*apply H.
 apply couple_intro; trivial.
*apply prodcart_def in H0.
 destruct H0 as (y&?&z&?&?).
 rewrite H2; auto.
Qed.
 
    
  Lemma levy_prodcart v k n a b :
    is_var a v ->
    is_var b v ->
    levy_set v k n (prodcart a b).
intros va vb x.
rewrite prodcart_def.
constructor; [simpl;auto|intros a'].
constructor; [simpl;auto|intros b'].
apply levy_thin_vars with (x::a'::b'::nil).
2:destruct 1 as [?|[?|[?|[ ]]]]; simpl; auto.
apply levy_couple_eq; constructor; simpl; auto.
Qed.

  Lemma levy_prodcart_eq v k n a b :
    is_var a v ->
    is_var b v ->
    levy_set_eq v k n (prodcart a b).
intros va vb z.
apply levy_eq_set.
*constructor; [simpl;auto|].
 intros; apply levy_prodcart; simpl; auto.
*unfold incl_set; rewrite fa_prodcart_iff; trivial.
 2:intros ?? h; rewrite h; reflexivity.
 constructor;[simpl; auto|].
 intros x.
 constructor;[simpl; auto|].
 intros y.
 rewrite in_set_def; constructor; [simpl; auto|].
 intros z'.
 apply levy_couple_eq; constructor; simpl; auto.
Qed.


Transparent fst snd.

(*Lemma fa_fst_iff z x P :
  (forall z, z ∈ fst x -> P x) <->
    (forall
  
  is_var x v ->
    levy_set v k n (fst x).
*)

  Lemma levy_fst v k n x :
    is_var x v ->
    levy_set v k n (fst x).
intros vx z.
unfold fst.
rewrite union_def.
rewrite ex_subset_iff.
2:intros ?? h; rewrite h; reflexivity.
rewrite ex_union_iff.
constructor; [simpl;auto |].
constructor; [simpl;auto |].
constructor.
*rewrite in_set_def.
 constructor; [simpl;auto |].
 apply levy_pair_eq; simpl; auto.
*constructor; simpl; auto.
Qed.

Lemma levy_fst_eq v k n x :
    is_var x v ->
    levy_set_eq v k n (fst x).
intros vx z.
apply levy_eq_set; unfold incl_set.
*constructor; [simpl;auto |].
 apply levy_fst; simpl; auto.
*unfold fst.
 rewrite fa_union_iff.
 rewrite fa_subset_iff.
 2:intros ?? h;rewrite h; reflexivity.
 rewrite fa_union_iff.
 constructor; [simpl;auto |].
 constructor; [simpl;auto |].
 constructor.
 +rewrite in_set_def; constructor; [simpl;auto |].
  apply levy_pair_eq; simpl; auto.
 +constructor; [simpl;auto |].
  constructor; simpl;auto.
Qed.

Lemma levy_snd v k n x :
    is_var x v ->
    levy_set v k n (snd x).
intros vx z.
unfold snd.
rewrite union_def.
rewrite ex_subset_iff.
2:intros ?? h; rewrite h; reflexivity.
rewrite ex_union_iff.
constructor; [simpl;auto |].
constructor; [simpl;auto |].
constructor; [|constructor; simpl;auto].
apply levy_eq_set; unfold incl_set.
*rewrite fa_pair_iff.
 2:intros ?? h;rewrite h; reflexivity.
 constructor; [|apply levy_union; simpl;auto].
 rewrite in_set_def.
 rewrite ex_union_iff.
 constructor; [simpl;auto |intro].
 constructor; [simpl;auto |intro].
 apply levy_fst_eq; simpl; auto.
*rewrite fa_union_iff.
 constructor; [simpl;auto |intro].
 constructor; [simpl;auto |intro].
 apply levy_set_pair. 
  apply levy_fst_eq; simpl; auto.
  constructor; simpl; auto.
Qed.

  Lemma fa_snd_iff x P :
    (forall y, y ∈ snd x -> P y) <->
    (forall z, z ∈ x ->
               forall z', z' ∈ z -> pair (fst x) z' == union x ->
                          forall y, y ∈ z' -> P y).
unfold snd.
rewrite fa_union_iff.
rewrite fa_subset_iff.
2:intros ?? h;rewrite h; reflexivity.
rewrite fa_union_iff.
reflexivity.
Qed.

  Lemma levy_snd_aux v k n x y:
    is_var x v ->
    is_var y v ->
    levy v k n (pair (fst x) y == union x).
intros vx vy.
apply levy_eq_set; unfold incl_set.
+rewrite fa_pair_iff.
 2:intros ?? h; rewrite h; reflexivity.
 apply levy_thin_vars with (push_var y v).
 2:destruct 1; simpl; subst; auto.
 constructor;[|apply levy_union; simpl; auto].
 rewrite in_set_def.
 rewrite ex_union_iff.
 constructor; [simpl; auto|].
 constructor; [simpl; auto|].
 apply levy_fst_eq; simpl; auto.
+rewrite fa_union_iff.
 constructor; [simpl; auto|].
 constructor; [simpl; auto|].
 apply levy_set_pair;[|constructor;simpl;auto].    
 apply levy_fst_eq; simpl; auto.
Qed.
  

  Lemma levy_snd_eq v k n x :
    is_var x v ->
    levy_set_eq v k n (snd x).
intros vx z.
apply levy_eq_set; unfold incl_set.
*constructor; [simpl;auto |].
 apply levy_snd; simpl; auto.
*rewrite fa_snd_iff.
 constructor; [simpl;auto |].
 constructor; [simpl;auto |].
 constructor.
 +apply levy_snd_aux; simpl; auto.
 +constructor; [simpl; auto|].
  constructor; simpl; auto.
Qed.

  
Require Import ZFcoc.

Lemma props_def x :
  x ∈ props <-> forall y, y ∈ x -> y == empty.
split; intros.
*apply props_proof_irrelevance with (1:=H)(2:=H0).
*apply power_intro; intros.
rewrite H with (1:=H0).
 apply singl_intro.
Qed. 

Lemma levy_props k v n : levy_set v k n props.
intros z.
rewrite props_def.
constructor; [simpl; auto|].
intros x.
apply levy_empty_eq.
Qed.

Lemma eq_props_cl_def (nnpp:forall P:Prop,~~P->P) :
  props == pair empty (singl empty).
apply eq_set_ax; split; intros.
*unfold props in H; rewrite power_ax in H.
 apply nnpp; intros h.
 assert (exists y, y ∈ x).
 {apply nnpp; intros h'; apply h.
  apply pair_ax; left.
  apply empty_ext.
  red;intros; eauto. }
 apply h; apply pair_ax; right.
 apply singl_ext. 
 destruct H0.
 specialize H with (1:=H0).
 apply singl_elim in H. 
 rewrite H in H0; trivial.
 intros; apply singl_elim; auto.
*apply pair_ax in H; destruct H; rewrite H; apply power_ax; intros;[|trivial].
 apply empty_ax in H0; contradiction.
Qed.
 
  Lemma levy_props_eq v n :
    levy_set_eq v Prd (S n) props.
intros z.
apply levy_eq_set; unfold incl_set.
*constructor; [simpl;auto|intros z'].
 apply levy_props. 
*apply F_fa_prd; intros P.
 constructor.
  apply levy_props.
  constructor; simpl; auto.
Qed.
  
  Require Import ZFrelations.

Transparent func dep_func cc_prod app cc_app.


Lemma levy_rel v k n a b :
    is_var a v ->
    is_var b v ->
    levy_set v k n (rel a b).
intros lva lvb x.
setoid_replace (x ∈ rel a b) with (x ⊆ prodcart a b).
*constructor; [simpl; auto|intros z].
 apply levy_prodcart; simpl; auto.
*unfold rel; rewrite power_ax.
 reflexivity.
Qed.

Lemma cc_app_def f x z :
  z ∈ cc_app f x <-> exists p, p ∈ f /\ p == couple x z.
rewrite <- couple_in_app.
split; [eauto with *|intros].
destruct H as (p,(?,eqp)); rewrite <-eqp; trivial.
Qed.

Lemma fa_cc_app_iff f x P :
  (forall z, z ∈ cc_app f x -> P z) <->
  (forall p, p ∈ f -> forall c, c ∈ p -> forall z, z ∈ c -> p == couple x z -> P z).
split; intros.
*apply H.
 apply cc_app_def.
 exists p; auto.
*apply cc_app_def in H0.
 destruct H0 as (p&?&?).
 apply H with p (pair x z); auto.
 rewrite H1; unfold couple; auto.
Qed.
Lemma ex_cc_app_iff f x P :
  (exists z, z ∈ cc_app f x /\ P z) <->
  (exists p, p ∈ f /\ exists c, c ∈ p /\ exists z, z ∈ c /\ p == couple x z /\ P z).
split; intros.
*destruct H as (z&?&?).
 apply cc_app_def in H.
 destruct H as (p,(?,?)).
 exists p; split;[trivial|].
 exists (pair x z); split;[rewrite H1;apply pair_intro2|].
 exists z; split; auto with *.
*destruct H as (p&?&c&?&z&?&?&?).
 exists z; split;[|trivial].
 apply cc_app_def.
 exists p; auto.
Qed.

Lemma levy_cc_app v k n x y :
  is_var x v ->
  levy_set_eq v k n y ->
  levy_set v k n (cc_app x y).
intros vx lvy z.
rewrite cc_app_def.
constructor;[simpl;auto|].
intros.
apply levy_couple_eq.
 intro; apply levy_thin2; apply lvy.
 constructor; simpl; auto.
Qed.

Lemma levy_cc_app_eq v k n x y :
  is_var x v ->
  (forall k', levy_set_eq v k' n y) ->
  levy_set_eq v k n (cc_app x y).
intros vx lvy z.
apply levy_eq_set.
*constructor;[simpl;auto|].
 apply levy_cc_app; simpl; auto.
 intro; apply levy_thin2; trivial.
 apply lvy.
*unfold incl_set; rewrite fa_cc_app_iff.
 constructor;[simpl;auto|].
 constructor;[simpl;auto|].
 constructor;[simpl;auto|].
 constructor;[| constructor;simpl;auto].
 apply levy_str with x0;[simpl;auto|].
 apply levy_couple_eq.
  intro; do 4 apply levy_thin2; apply lvy.
  constructor; simpl; auto.
Qed.


Lemma fa_cc_lam_iff a f P :
  Proper (eq_set ==> iff) P ->
  ext_fun a f -> 
  (forall z, z ∈ cc_lam a f -> P z) <->
    (forall x, x ∈ a -> forall y, y ∈ f x -> P (couple x y)).
intros Pm fext.  
split; intros.
*apply H.
 rewrite cc_lam_def;[|trivial].
 eauto with *.
*rewrite cc_lam_def in H0;[|trivial].
 destruct H0 as (x,?,(y,?,?)).
 rewrite H2; eauto. 
Qed.

 
Lemma cc_prod_def f a b :
  ext_fun a b ->
  f ∈ cc_prod a b <->
        (forall p, p ∈ f -> exists x, x ∈ a /\ exists y, y ∈ b x /\
                              exists y', y' ∈ y /\ p == couple x y') /\
          (forall x, x∈a -> exists y, y ∈ b x /\
                              (forall y', y' ∈ y -> couple x y' ∈ f) /\
                     forall p, p ∈ f -> x == fst p ->
                               exists y', y' ∈ y /\ p == couple x y').
intros bext.
unfold cc_prod.
rewrite replf_ax.  
2:{intros ??? h.
   apply cc_lam_ext;[reflexivity|].
   intros ??? h'; rewrite h,h'; reflexivity. }
split; intros.
*destruct H as (f',tyf',eqf).
 split ;intros.
 +rewrite eqf in H.
  rewrite cc_lam_def in H.
  destruct H as (x,tyx,(y',?,eqp)).
  exists x; split ;[trivial|].
  assert (app f' x ∈ b x).
  {apply dep_func_elim with (1:=tyf'); trivial. }
  exists (app f' x); split; [trivial|].
  exists y'; auto.  
  {do 2 red; intros. rewrite H1; reflexivity. }
 +assert (aux : app f' x ∈ b x).
  {apply dep_func_elim with (1:=tyf'); trivial. }
  exists (app f' x); split; [trivial|].
  split; intros.  
  ++rewrite eqf.
    rewrite cc_lam_def.
    2:do 2 red; intros ??? h; rewrite h; reflexivity.
    exists x; [trivial|].
    exists y'; auto with *.
  ++rewrite eqf in H0.
    rewrite cc_lam_def in H0.
    2:do 2 red; intros ??? h; rewrite h; reflexivity.
    destruct H0 as (x',?,(y',?,eqp)).
    assert (eqx: x==x').
    {rewrite H1,eqp,fst_def; reflexivity. }
    rewrite <-eqx in H2,eqp; eauto.
*destruct H.
 exists (lam a (cc_app f)).
 apply dep_func_intro; trivial.
  do 2 red; intros; apply cc_app_morph; auto with *.
 +intros.
  destruct H0 with (1:=H1) as (y&?&?&?).
  assert (eqy : y == cc_app f x).
  {apply eq_set_ax; intros z.
   rewrite <- couple_in_app.
   split; [auto|].
   intros.
   destruct H4 with (1:=H5); [rewrite fst_def; reflexivity|].
   destruct H6.
   apply couple_injection in H7; destruct H7.
   rewrite <-H8 in H6; trivial.  }
  rewrite <-eqy; trivial.
 +transitivity (cc_lam a (cc_app f)).
  ++apply cc_eta_eq'.
    red; intros.
    destruct H with (1:=H1).
    destruct H2 as (?&y&?&?&?&?).
    rewrite H5,fst_def,snd_def; auto with *.
  ++apply cc_lam_ext;[reflexivity|].
    intros z z' tyz eqz.
    rewrite beta_eq; auto.
     rewrite eqz; reflexivity.    
     do 2 red; intros ??? h; rewrite h; reflexivity.
     rewrite <-eqz; trivial.
Qed.

Lemma levy_cc_prod v k n a b :
  ext_fun a b ->
  is_var a v ->
  (forall x v' P,
   is_var x v' /\ incl_vars v v' ->
   (forall y, levy (push_var y v') k n (P y)) ->
   levy v' k n (exists y, y ∈ b x /\ P y)) ->         
  levy_set v k n (cc_prod a b).
intros bext va lvb z.
rewrite cc_prod_def;[|trivial].
constructor.
*constructor;[simpl;auto|].
 constructor;[simpl;auto|].
 intros; apply lvb; [unfold incl_vars;simpl;auto|].
 constructor;[simpl;auto|].
 intros; apply levy_str with x; simpl; auto 10.
 apply levy_couple_eq; constructor; simpl; auto 10.
*constructor;[simpl;auto|].
 intros; apply lvb; [unfold incl_vars;simpl;auto|].
 constructor.
 +constructor;[simpl; auto|].
  intros; rewrite in_set_def.
  constructor; [simpl;auto 10|].
  apply levy_couple_eq; constructor; simpl; auto 10.
 +constructor;[simpl;auto 10|].
  constructor.
  ++apply levy_str with x; [simpl;auto 10|].
    apply levy_fst_eq; simpl; auto.
  ++constructor;[simpl; auto|].
    intros.
    apply levy_str with x0; [simpl;auto 10|].
    apply levy_couple_eq; constructor; simpl; auto 10.
Qed.

Lemma levy_cc_prod_eq v n a b :
  ext_fun a b ->
  is_var a v ->
  (forall k x v' P,
   is_var x v' /\ incl_vars v v' ->
   (forall y, levy (push_var y v') k (S n) (P y)) ->
   levy v' k (S n) (exists y, y ∈ b x /\ P y)) ->         
  levy_set_eq v Prd (S n) (cc_prod a b).
intros bext va lvb z.
apply levy_eq_set; unfold incl_set.
*constructor; [simpl; auto|].
 apply levy_cc_prod; simpl; auto.
 intros.
 apply lvb; auto.
 destruct H; split; auto.
 red in H1; red; intros; apply H1; simpl;auto. 
*apply F_fa_prd; intros f.
 constructor;[|constructor; simpl; auto]. 
 apply levy_cc_prod; simpl; auto.
 intros.
 apply lvb; auto.
 destruct H; split; auto.
 red in H1; red; intros; apply H1; simpl;auto. 
Qed.

(* non-dependent standard functions *)

Lemma func_def f a b :
  f ∈ func a b <->
    (forall p, p ∈ f -> p ∈ prodcart a b) /\
      (forall x, x∈a -> exists y, y∈b /\ couple x y ∈ f /\
                        forall y', y' ∈ b -> couple x y' ∈ f -> y==y').
unfold func; rewrite subset_ax.
unfold rel.
rewrite power_ax.
apply and_iff_morphisml; [reflexivity|intros ? _].
apply exists_eq_intro; intros f' eqf.
split; intros.
*destruct H0 as (ftot,ffun).
 destruct ftot with (1:=H1) as (y,?,?).
 rewrite <-eqf in H2.
 exists y; split;[trivial|split;[trivial|]].
 intros.
 rewrite eqf in H2, H4; eauto.
*split; intros.
 destruct H0 with (1:=H1) as (y,(?,(?,_))).
 rewrite eqf in H3; exists y; trivial.

 rewrite <-eqf in H1,H2.  
 destruct (proj1 (prodcart_def _ _ _) (H _ H1)) as (x1&?&y1&?&?).
 apply couple_injection in H5; destruct H5.
 rewrite <-H5 in H3.
 rewrite <-H6 in H4.
 clear x1 y1 H5 H6.
 destruct H0 with (1:=H3) as (y0&?&?&?).
 rewrite <-H7 with (1:=H4)(2:=H1).
 rewrite <-H7 with (2:=H2); [reflexivity|].
 destruct (proj1 (prodcart_def _ _ _) (H _ H2)) as (x2&_&y2&?&?).
 apply couple_injection in H9; destruct H9.
 rewrite H10; trivial.
Qed.
  
  Lemma levy_func v k n a b :
    is_var a v ->
    is_var b v ->
    levy_set v k n (func a b).
intros va vb f.
rewrite func_def.
constructor.
*constructor;[simpl;auto|].
 apply levy_prodcart; simpl; auto.
*constructor;[simpl;auto|intros x].
 constructor;[simpl;auto|intros y].
 constructor; [rewrite in_set_def; constructor;
               [simpl; auto|apply levy_couple_eq]; constructor; simpl; auto|].
 constructor;[simpl;auto|].
 constructor;[|constructor;simpl;auto].
 rewrite in_set_def; constructor; [simpl;auto|].
 apply levy_couple_eq; constructor; simpl; auto.
Qed.


Lemma app_def f x z :
  z ∈ app f x <-> exists p, p∈f /\ p==couple x (snd p) /\ z ∈ snd p.
unfold app.
split; intros.
*rewrite union_ax in H.
 destruct H.
 rewrite subset_ax in H0; destruct H0.
 destruct H1.
 rewrite <-H1 in H2; clear x1 H1.
 exists (couple x x0); split; trivial.
 rewrite snd_def.
 split;[reflexivity|trivial].
*destruct H as (p&?&?&?).
 rewrite union_ax.
 exists (snd p); [trivial|].
 rewrite subset_ax.
 rewrite H0 in H.
 split.
  unfold rel_image.
  apply subset_intro.
   rewrite union_def; exists (pair x (snd p)); split; auto.
   rewrite union_ax; exists (couple x (snd p)); trivial.
   unfold couple; auto.
   exists x; trivial.   
 exists (snd p); [reflexivity|trivial].
Qed.

Lemma fa_app_iff f x P :
  (forall z, z ∈ app f x -> P z) <->
    (forall p, p ∈ f -> p==couple x (snd p) -> forall z, z∈snd p -> P z).
split; intros.
*apply H.
 rewrite app_def.
 exists p; split; auto.
*rewrite app_def in H0.
 destruct H0 as (p&?&?&?); eauto.
Qed.


  Lemma levy_app_eq v k n f x :
    is_var f v ->
    is_var x v ->
    levy_set_eq v k n (app f x).
intros vf vx y.
assert (aux : forall v k' y, is_var y v -> is_var x v ->
                             levy v k' n (y == couple x (snd y))).
{intros v' k' y0 vy vx_.
 apply levy_thin_vars with (push_var y0 v').
 2:destruct 1; subst; simpl; auto.
 apply levy_couple_eq; [constructor;simpl;auto|].
 apply levy_snd_eq; simpl; auto. }
apply levy_eq_set.
*constructor;[simpl;auto|intros z].
 rewrite app_def.
 constructor; [simpl; auto|].
 constructor; [apply aux; simpl; auto|].
 apply levy_thin_vars with (push_var z (push_var x0 nil)).
 2:destruct 1 as [?|[?|[ ]]]; subst; simpl; auto.
 apply levy_snd; simpl; auto.
*unfold incl_set; rewrite fa_app_iff.
 constructor; [simpl; auto|].
 constructor; [apply aux; simpl; auto|].
 rewrite fa_snd_iff.
 constructor; [simpl; auto|].
 constructor; [simpl; auto|].
 constructor.
 +apply levy_snd_aux; simpl; auto.
 +constructor; [simpl; auto|].
  constructor; simpl; auto 10.    
Qed.
 

Lemma levy_cc_app_in_comp v n a b :
  levy_set_eq v Sig (S n) a ->
  levy_set_eq v Sig (S n) b ->
  forall k, levy_set v k (S n) (cc_app a b).
intros lva lvb k z.
revert k; apply levy_cut_delta with (P:=fun x=>z∈cc_app x b)(y:=a).
{intros ?? h; rewrite h; reflexivity. }
{intro; apply levy_thin2; trivial. }
intros a'.
apply levy_cut_delta with (P:=fun x=>z∈cc_app a' x)(y:=b).
{intros ?? h; rewrite h; reflexivity. }
{intro; do 2 apply levy_thin2; trivial. }
intros b' k. 
apply levy_str with z; simpl; auto.
apply levy_cc_app;[|constructor]; simpl; auto.
Qed.
Lemma levy_cc_app_comp v n a b :
  levy_set_eq v Sig (S n) a ->
  levy_set_eq v Sig (S n) b ->
  forall k, levy_set_eq v k (S n) (cc_app a b).
intros lva lvb k z.
revert k; apply levy_cut_delta with (P:=fun x=>z==cc_app x b)(y:=a).
{intros ?? h; rewrite h; reflexivity. }
{intro; apply levy_thin2; trivial. }
intros a'.
apply levy_cut_delta with (P:=fun x=>z==cc_app a' x)(y:=b).
{intros ?? h; rewrite h; reflexivity. }
{intro; do 2 apply levy_thin2; trivial. }
intros b' k. 
apply levy_str with z; simpl; auto.
apply levy_cc_app_eq;[|constructor]; simpl; auto.
Qed.

Lemma levy_cc_lam_in_comp v n a b :
  morph1 b ->
  levy_set_eq v Sig (S n) a ->
  (forall x, levy_set_eq (push_var x v) Sig (S n) (b x)) ->
  forall k, levy_set v k (S n) (cc_lam a b).
intros bm lva lvb k z.
rewrite cc_lam_def; [|auto].
rewrite ex_ex2.
revert k; apply ex_in_delta.  
+intros ?? h; apply ex2_morph; intro;rewrite h; reflexivity.
+intro; apply levy_thin2; apply lva.
+intros k x.
 rewrite ex_ex2.
 revert k; apply ex_in_delta.  
 ++intros ?? h; rewrite h; reflexivity.
 ++intro; apply levy_thin3; apply lvb.
 ++intros k y.
   apply levy_str with z; simpl; auto 10.
   apply levy_couple_eq; constructor; simpl; auto.
Qed.

Lemma levy_cc_lam_comp v n a b :
  morph1 b ->
  levy_set_eq v Sig (S n) a ->
  (forall x, levy_set_eq (push_var x v) Sig (S n) (b x)) ->
  forall k, levy_set_eq v k (S n) (cc_lam a b).
intros bm lva lvb k z.
apply levy_eq_set.
*constructor;[simpl;auto|].
 intros.
 apply levy_thin2.
 apply levy_cc_lam_in_comp; trivial.
*unfold incl_set.
 rewrite fa_cc_lam_iff;[|intros ?? h; rewrite h; reflexivity|auto].
 revert k; apply fa_in_delta.
 +intros ?? h; apply fa_morph; intro; rewrite h; reflexivity.
 +intro; apply levy_thin2; apply lva.
 +intros k x.
  revert k; apply fa_in_delta.
  ++intros ?? h; rewrite h; reflexivity.
  ++intro; apply levy_thin3; apply lvb.
  ++intros k y.
    rewrite in_set_def.
    constructor; [simpl;auto|intros].
    apply levy_str with x0; simpl; auto 10.
    apply levy_couple_eq; constructor; simpl; auto.
Qed.


Lemma levy_ho_cut_delta (v : var_set) (n : nat) (P : (set->set) -> Prop) (f : set->set)(dom:set) :
  morph1 f ->
  Proper (eq_fun dom ==> iff) P ->
  levy_set_eq v Sig (S n) dom ->
  (forall x, levy_set_eq (push_var x v) Sig (S n) (f x)) ->
  (forall f k, levy (f :: v) k (S n) (P (cc_app f))) ->
  forall k, levy v k (S n) (P f).
intros fm Pm lvdom lvf lvP k.
apply F_ext with (exists x:set, x==cc_lam dom f /\ P (cc_app x)).
{split;intros.
 *destruct H as (g&eqg&?).
  revert H; apply Pm.
  intros x x' tyx e.
  rewrite <-e; clear x' e.
  rewrite eqg, cc_beta_eq; auto with *.
 *exists (cc_lam dom f); split;[reflexivity|].
  revert H; apply Pm.
  intros x x' tyx e.
  rewrite <-e; clear x' e.
  rewrite cc_beta_eq; auto with *. }
apply ex_eq_delta;[| |intros; apply lvP].
*intros g h eqgh.
 apply Pm; red; intros; apply cc_app_morph; trivial.
*clear k; apply levy_cc_lam_comp;[apply fm|apply lvdom|apply lvf].
Qed.


Lemma levy_cc_prod_in_comp v n a b :
  morph1 b ->
  levy_set_eq v Sig (S n) a ->
  (forall x, levy_set_eq (push_var x v) Sig (S n) (b x)) ->
  forall k, levy_set v k (S n) (cc_prod a b).
intros bm lva lvb k z.
rewrite cc_prod_def;[|auto].
constructor.
*constructor;[simpl;auto|].
 intros x; revert k; apply ex_in_delta.
 {intros ?? h; apply ex_morph; intro; apply and_iff_morphism;[rewrite h; reflexivity|].
  apply ex_morph; intro; rewrite h; reflexivity. }
 {intro; do 2 apply levy_thin2; apply lva. }
 intros k y; revert k; apply ex_in_delta.
 {intros ?? h; apply ex_morph; intro; rewrite h; reflexivity. }
 {intro; do 2 apply levy_thin3; apply lvb. }
 intros k b'.
 constructor;[simpl;auto|].
 intros; apply levy_str with x; simpl; auto 10.
 apply levy_couple_eq; constructor; simpl; auto 10.
*revert k;apply fa_in_delta.
 {intros ?? h; apply ex_morph; intro; apply and_iff_morphism;[rewrite h; reflexivity|].
  apply and_iff_morphism; apply fa_morph; intro;[rewrite h; reflexivity|].
  apply impl_morph;[reflexivity|intros].
  apply impl_morph;[rewrite h;reflexivity|intros].
  apply ex_morph; intro; rewrite h; reflexivity. }
 {intro; apply levy_thin2; apply lva. }
 intros k x; revert k; apply ex_in_delta.
 {intros ?? h; apply and_iff_morphism; apply fa_morph; intro;[rewrite h; reflexivity|].
  apply impl_morph;[reflexivity|intros].
  apply impl_morph;[reflexivity|intros].
  apply ex_morph; intro; rewrite h; reflexivity. }
 {intro; apply levy_thin3; apply lvb. }
 intros k y.
 constructor.
 +constructor;[simpl;auto|].
  intros; rewrite in_set_def.
  constructor;[simpl;auto|].
  apply levy_couple_eq; constructor; simpl; auto 10.
 +constructor;[simpl;auto|].
  constructor.
  ++apply levy_str with x; simpl; auto 10.
    apply levy_fst_eq; simpl; auto 10.
  ++constructor;[simpl;auto 10|].
    intros; apply levy_str with x0; simpl; auto 10.
    apply levy_couple_eq; constructor; simpl; auto 10.
Qed.


Lemma levy_cc_prod_comp v n a b :
  morph1 b ->
  levy_set_eq v Sig (S (S n)) a ->
  (forall x, levy_set_eq (push_var x v) Sig (S (S n)) (b x)) ->
  forall k, levy_set_eq v k (S (S n)) (cc_prod a b).
intros bm lva lvb k z.
apply levy_eq_set.
*constructor;[simpl;auto|].
 intros.
 apply levy_thin2.
 apply levy_cc_prod_in_comp; trivial.
*unfold incl_set.
 revert k; apply levy_cut_delta with (P:=fun a=>forall z', z'∈cc_prod a b->z'∈z)(y:=a).
 {intros ?? h; apply fa_morph; intros; apply impl_morph;[|reflexivity].
  apply in_set_morph;[reflexivity|].
  apply cc_prod_ext;[trivial|red;auto]. }
 {intro; apply levy_thin2; apply lva. }
 intros a' k.  
 revert k; apply levy_ho_cut_delta with (P:=fun f=>forall z',z'∈cc_prod a' f->z'∈z)
                                        (dom:=a')(f:=b); auto.
 +intros ?? h; apply fa_morph; intros; apply impl_morph;[|reflexivity].
  apply in_set_morph;[reflexivity|].
  apply cc_prod_ext;[reflexivity|red;auto].
 +constructor; simpl; auto.
 +intros x z'; do 2 apply levy_thin3; apply lvb.
 +intros b' k.
  apply levy_lift with Prd. 
  apply F_fa_prd.
  intros f; constructor;[|constructor;simpl;auto].
  apply levy_cc_prod_in_comp; trivial.
  ++intros ?? h; rewrite h; reflexivity.
  ++constructor; simpl; auto.
  ++intros x z'.
    apply levy_cc_app_eq;[|constructor];simpl; auto.
Qed.


Require Import ModelCC.

Import BuildModel T J R.

Module Sigma2.

Definition levy_int (t:term) n :=
  forall i v,
  (forall k, k<n -> is_var (i k) v) ->
  levy_set v Sig 2 (int t i) /\
  levy_set_eq v Sig 2 (int t i).

Lemma d2_ref n k : n<k -> levy_int (Ref n) k.
split; simpl.
constructor; simpl; auto.
constructor; simpl; auto.
Qed.

Lemma d2_props k : levy_int prop k.
split; simpl.
apply levy_props.
intros z; apply levy_lift with (k:=Prd).
apply levy_props_eq.
Qed.

Lemma d2_app M N k :
  levy_int M k ->
  levy_int N k ->
  levy_int (App M N) k.
split; simpl; intros z.
*apply levy_cc_app_in_comp.
  apply H; simpl; auto.
  apply H0; simpl; auto.
*apply levy_cc_app_comp.
  apply H; simpl; auto.
  apply H0; simpl; auto.
Qed.

Lemma d2_abs M N k :
  levy_int M k ->
  levy_int N (S k) ->
  levy_int (Abs M N) k.
split; simpl; intros z.
*apply levy_cc_lam_in_comp.
 +intros ?? h; rewrite h; reflexivity.
 +apply H; simpl; auto.
 +intros; apply H0.
  destruct k0; simpl; auto with arith.
*apply levy_cc_lam_comp.
 +intros ?? h; rewrite h; reflexivity.
 +apply H; simpl; auto.
 +intros; apply H0.
  destruct k0; simpl; auto with arith.
Qed.

Lemma d2_prod M N k :
  levy_int M k ->
  levy_int N (S k) ->
  levy_int (Prod M N) k.
split; simpl; intros z.
*apply levy_cc_prod_in_comp.
 +intros ?? h; rewrite h; reflexivity.
 +apply H; simpl; auto.
 +intros; apply H0.
  destruct k0; simpl; auto with arith.
*apply levy_cc_prod_comp.
 +intros ?? h; rewrite h; reflexivity.
 +apply H; simpl; auto.
 +intros; apply H0.
  destruct k0; simpl; auto with arith.
Qed.

End Sigma2.

(* ok: delta 2 *)
Module Delta2.
  
Definition d2_int (t:term) n :=
  forall k i v,
  (forall k, k<n -> is_var (i k) v) ->
  levy_set v k 2 (int t i) /\
  levy_set_eq v k 2 (int t i).

Lemma d2_ref n k : n<k -> d2_int (Ref n) k.
split; simpl.
constructor; simpl; auto.
constructor; simpl; auto.
Qed.

Lemma d2_props k : d2_int prop k.
split; simpl.
apply levy_props.
intros z; apply levy_lift with (k:=Prd).
apply levy_props_eq.
Qed.

Lemma d2_app M N k :
  d2_int M k ->
  d2_int N k ->
  d2_int (App M N) k.
split; simpl; intros z.
*apply levy_cc_app_in_comp.
  apply H; simpl; auto.
  apply H0; simpl; auto.
*apply levy_cc_app_comp.
  apply H; simpl; auto.
  apply H0; simpl; auto.
Qed.
  
Lemma d2_abs M N k :
  d2_int M k ->
  d2_int N (S k) ->
  d2_int (Abs M N) k.
split; simpl; intros z.
*apply levy_cc_lam_in_comp.
 +intros ?? h; rewrite h; reflexivity.
 +apply H; simpl; auto.
 +intros; apply H0.
  destruct k1; simpl; auto with arith.
*apply levy_cc_lam_comp.
 +intros ?? h; rewrite h; reflexivity.
 +apply H; simpl; auto.
 +intros; apply H0.
  destruct k1; simpl; auto with arith.
Qed.

Lemma d2_prod M N k :
  d2_int M k ->
  d2_int N (S k) ->
  d2_int (Prod M N) k.
split; simpl; intros z.
*apply levy_cc_prod_in_comp.
 +intros ?? h; rewrite h; reflexivity.
 +apply H; simpl; auto.
 +intros; apply H0.
  destruct k1; simpl; auto with arith.
*apply levy_cc_prod_comp.
 +intros ?? h; rewrite h; reflexivity.
 +apply H; simpl; auto.
 +intros; apply H0.
  destruct k1; simpl; auto with arith.
Qed.

End Delta2.

Import Sigma2.

(**********************************************************)

Require Import ZFnats.

Lemma levy_succ_eq v k n x y :
  is_var x v ->
  is_var y v ->
  levy v k n (x == succ y).
intros vx vy; apply levy_eq_set; unfold incl_set.
*constructor;[simpl;auto|].
 intros z; unfold succ.
 rewrite union2_ax; constructor; [constructor;simpl;auto|].
 apply levy_pair; simpl; auto.
*unfold succ, union2.
 rewrite fa_union_iff, fa_pair_iff.
 2:intros ?? h; apply fa_morph; intro; rewrite h; reflexivity.
 constructor; [constructor; [simpl;auto|constructor; simpl;auto]|].
 unfold singl; rewrite fa_pair_iff.
 2:intros ?? h; rewrite h; reflexivity.
 do 2 constructor; simpl; auto.
Qed.

Definition N_inductive a :=
  empty ∈ a /\ forall x, x ∈ a -> succ x ∈ a.

Instance N_inductive_morph : Proper (eq_set==>iff) N_inductive.
do 2 red; intros.
unfold N_inductive.
apply and_iff_morphism;[rewrite H;reflexivity|].
apply fa_morph; intro; rewrite H;reflexivity.
Qed.

(* Being inductive is Δ_0 *)
Lemma levy_N_inductive v k n x :
  is_var x v ->
  levy v k n (N_inductive x).
intros vx.
constructor.
*rewrite in_set_def; constructor;[ simpl; auto|].
 intros; apply levy_empty_eq.
*constructor;[simpl; auto|intros z].
 rewrite in_set_def; constructor;[simpl;auto|].
 intros; apply levy_succ_eq; simpl; auto.
Qed.

Lemma N_induc : N_inductive N.
split; intros; [apply zero_typ|].
apply succ_typ; trivial.
Qed.
  
Lemma eq_N_iff x :
  x == N <-> x ⊆ N /\ N_inductive x.
split; intros.
*rewrite H.
 split;[reflexivity|]. 
 apply N_induc.  
*destruct H.
 apply incl_eq; trivial.
 red; intros. 
 elim H1 using N_ind; intros; auto.
 +rewrite <-H3; trivial.
 +apply H0.
 +apply H0; trivial.
Qed.

Lemma N_case n : n ∈ N -> n==empty \/ exists k, k ∈ n /\ k ∈ N /\ n==succ k.
intros.
elim H using N_ind; intros.
*destruct H2 as [?|(y&?&?)]; [left|right; exists y; split]; rewrite <-H1; trivial.
*left; reflexivity.  
*right; exists n0; split;[|split;[trivial|reflexivity]].
 apply union2_intro2; apply singl_intro.
Qed.

Lemma N_def z : z ∈ N <->
                (z==empty \/ exists y, y ∈ z /\ z==succ y) /\
                (forall y, y∈z -> y==empty \/ exists y', y' ∈ y /\ y==succ y').
split; intros.
*split;[destruct N_case with (1:=H) as [?|(k&?&_&?)]; eauto|intros].
 destruct N_case with y as [?|(k&?&_&?)]; eauto.
 revert y H0; elim H using N_ind; intros.
 rewrite <-H1 in H3; auto.
 apply empty_ax in H0; contradiction.
 apply le_case in H2; destruct H2;[rewrite H2; trivial|auto].
*destruct H as (zcase&hered).
 revert zcase hered.
 elim z using wf_ax; intros.
 destruct zcase as [eqx|(k&klt&eqx)]; rewrite eqx; [apply zero_typ|apply succ_typ].
 apply H; auto.
 intros ??; apply hered.
 rewrite eqx.
 apply union2_intro1; trivial.
Qed.

Lemma levy_N v k n:
  levy_set v k n N.
intros z.
rewrite N_def.
constructor.
*constructor;[apply levy_empty_eq|constructor;[simpl;auto|]].
 intros; apply levy_succ_eq; simpl; auto.
*constructor; [simpl;auto|].
 constructor;[apply levy_empty_eq|].
 constructor; [simpl;auto|].
 intros; apply levy_succ_eq; simpl; auto.
Qed.

Lemma levy_N_eq v k n:
  levy_set_eq v k n N.
red; intros.
rewrite eq_N_iff.
constructor.
*constructor; [simpl; auto|].
 intros; apply levy_N.
*apply levy_N_inductive; simpl; auto.
Qed.


Require Import ZFwdom ZFlist.


Parameter List_alt_def : forall a, List a == sup N (fun n => func n a).
Parameter Cons_alt_def : forall a l, 
  Cons a l == singl (couple zero a) ∪ replf l (fun p => couple (succ (fst p)) (snd p)).  

Lemma List_def a l :
  l ∈ List a <-> l==empty \/ exists c, c ∈ l /\ exists p, p ∈ c /\
                              exists n, n ∈ p /\ exists y, y ∈ p /\ c==couple n y /\
                              n ∈ N /\ l ∈ func (succ n) a.
rewrite List_alt_def, sup_ax.
2:intros ??? h; rewrite h; reflexivity.
split; intros.
*destruct H as (n,tyn,lfun).
 revert lfun; elim tyn using N_ind; intros.
 +apply H1; rewrite H0; trivial.
 +left.
  apply empty_ext; intros z abs.
  rewrite func_def in lfun.
  destruct lfun as (lrel,_).
  apply lrel in abs.
  rewrite prodcart_def in abs.
  destruct abs as (y,(abs,_)).
  apply empty_ax in abs; trivial.
 +right.
  clear H0.
  assert (exists y, couple n0 y ∈ l).
  {rewrite func_def in lfun.
   destruct lfun as (lrel,lfun).
   destruct lfun with n0 as (y,(_,(inl,_)));
     [apply union2_intro2; apply singl_intro|eauto]. }
  destruct H0 as (y,?).
  exists (couple n0 y); split;[trivial|].
  exists (pair n0 y); split;[apply pair_intro2|].
  exists n0; split; [auto|].
  exists y; split; [auto|].
  split;[reflexivity|split;trivial].
*destruct H as [?|(c&inl&p&_&n&_&y&_&eqc&tyn&tyl)].
 +exists zero; [apply zero_typ|].
  rewrite H. 
  rewrite func_def; split; intros.
   apply empty_ax in H0; contradiction.  
   apply empty_ax in H0; contradiction.  
 +exists (succ n); trivial.
  apply succ_typ; trivial.
Qed.

Lemma eq_list_iff x a :
  x == List a <-> x ⊆ List a /\
                  empty ∈ x /\ forall l, l∈x -> forall y, y ∈ a -> Cons y l ∈ x.
rewrite eq_set_ax.  
split; intros.
*split.
 +red; intros; apply H; trivial. 
 +split; intros; [apply H;apply Nil_typ|].
  apply H; apply Cons_typ; [trivial|apply H; trivial].
*destruct H as (?&?&?).
 split;[apply H|].
 intros h; elim h using List_ind; intros; auto.
 intros ?? e; rewrite e; reflexivity.
Qed.

Lemma ex_ub_iff P ub :
  (forall x, P x -> x ∈ ub) ->
  (exists x, P x) <-> exists x, x ∈ ub /\ P x.
split; intros.
*destruct H0 as (x,p); eauto.
*destruct H0 as (x,(tyx,p)); eauto.
Qed.
Lemma fa_ub_iff P Q ub :
  (forall x, P x -> x ∈ ub) ->
  (forall x, P x -> Q x) <-> forall x, x ∈ ub -> P x -> Q x.
split; intros; auto.
Qed.

Lemma levy_func_ub v k n a b aub bub :
  is_var aub v ->
  is_var bub v ->
  a ⊆ aub ->
  b ⊆ bub ->
  (forall k', levy_set v k' n a) ->
  (forall k', levy_set v k' n b) ->
  levy_set v k n (func a b).
intros vua vub ua_def ub_def lvua lvub z.
rewrite func_def.
constructor.
*constructor;[simpl;auto|].
 intros z'; rewrite prodcart_def.
 rewrite ex_ub_iff with (ub:=aub);[|destruct 1; auto].
 constructor; [simpl;auto|intros x].
 constructor.
  do 2 apply levy_thin2; apply lvua.
  rewrite ex_ub_iff with (ub:=bub);[|destruct 1; auto].
 constructor; [simpl;auto|intros y].
 constructor.
  do 3 apply levy_thin2; apply lvub.
 apply levy_str with z'; [simpl; auto| apply levy_couple_eq];constructor;simpl;auto.
*rewrite fa_ub_iff with (ub:=aub);[|auto].
 constructor;[simpl;auto|intros x].
 constructor.
   apply levy_thin2; apply lvua.
 rewrite ex_ub_iff with (ub:=bub);[|destruct 1; auto].
 constructor;[simpl;auto|intros y].
 constructor.
  do 2 apply levy_thin2; apply lvub.
 constructor; [rewrite in_set_def; constructor;
               [simpl; auto|apply levy_couple_eq]; constructor; simpl; auto|].
 rewrite fa_ub_iff with (ub:=bub);[|auto].
 constructor;[simpl;auto|intros].
 constructor.
   do 3 apply levy_thin2; apply lvub.
 constructor;[|constructor;simpl;auto].
 rewrite in_set_def; constructor; [simpl;auto|].
 apply levy_couple_eq; constructor; simpl; auto.
Qed.

Lemma levy_func_succ_ub v k n x a aub:
  is_var x v ->
  is_var aub v ->
  (a ⊆ aub) ->
  (forall k', levy_set v k' n a) ->
  levy_set v k n (func (succ x) a).
intros vx vaub ub_def lva z.
*rewrite func_def.
 constructor.
 +constructor;[simpl;auto 10|].
  intros; rewrite prodcart_def.
  unfold succ,union2.
  rewrite ex_union_iff.
  rewrite ex_pair_iff.
  2:intros ?? h; apply ex_morph; intro; rewrite h; reflexivity.
  constructor.
   constructor;[simpl;auto|].
   intros; rewrite ex_ub_iff with (ub:=aub);[|destruct 1;auto].
   constructor;[simpl;auto|].
   intros; constructor;[do 3 apply levy_thin2; apply lva|].
   intros; eapply levy_str;[|apply levy_couple_eq;constructor]; simpl; auto.

   unfold singl; rewrite ex_pair_iff.
   2:intros ?? h; apply ex_morph; intro; rewrite h; reflexivity.
   constructor.
    intros; rewrite ex_ub_iff with (ub:=aub);[|destruct 1;auto].
    constructor;[simpl;auto|].
    intros; constructor;[do 2 apply levy_thin2; apply lva|].
    eapply levy_str;[|apply levy_couple_eq;constructor]; simpl; auto 10.

    intros; rewrite ex_ub_iff with (ub:=aub);[|destruct 1;auto].
    constructor;[simpl;auto|].
    intros; constructor;[do 2 apply levy_thin2; apply lva|].
    eapply levy_str;[|apply levy_couple_eq;constructor]; simpl; auto 10.
 +unfold succ,union2.
  rewrite fa_union_iff.
  rewrite fa_pair_iff.
  2:intros ?? h; apply fa_morph; intro; rewrite h; reflexivity.
  constructor.
   constructor;[simpl;auto|].
   intros; rewrite ex_ub_iff with (ub:=aub);[|destruct 1;auto].
   constructor;[simpl;auto|].
   intros; constructor;[do 2 apply levy_thin2; apply lva|].
   constructor.
    rewrite in_set_def; constructor; [simpl; auto 10|].
    apply levy_couple_eq; constructor; simpl; auto 10.
    intros; rewrite fa_ub_iff with (ub:=aub);[|auto].
    constructor;[simpl;auto|].
    intros; constructor;[do 3 apply levy_thin2; apply lva|].
    constructor.
     rewrite in_set_def; constructor; [simpl; auto 10|].
     apply levy_couple_eq; constructor; simpl; auto 10.

     constructor; simpl; auto 10.

   unfold singl; rewrite fa_pair_iff.
   2:intros ?? h; apply ex_morph; intro;
     apply and_iff_morphism;[|apply and_iff_morphism;[|apply fa_morph;intro]];
     try rewrite h; reflexivity.
   constructor.
    intros; rewrite ex_ub_iff with (ub:=aub);[|destruct 1;auto].
    constructor;[simpl;auto|].
    intros; constructor;[apply levy_thin2; apply lva|].
    constructor.
     rewrite in_set_def; constructor; [simpl; auto 10|].
     apply levy_couple_eq; constructor; simpl; auto 10.
     intros; rewrite fa_ub_iff with (ub:=aub);[|auto].
     constructor;[simpl;auto|].
     intros; constructor;[do 2 apply levy_thin2; apply lva|].
     constructor.
      rewrite in_set_def; constructor; [simpl; auto 10|].
      apply levy_couple_eq; constructor; simpl; auto 10.

      constructor; simpl; auto 10.

    intros; rewrite ex_ub_iff with (ub:=aub);[|destruct 1;auto].
    constructor;[simpl;auto|].
    intros; constructor;[apply levy_thin2; apply lva|].
    constructor.
     rewrite in_set_def; constructor; [simpl; auto 10|].
     apply levy_couple_eq; constructor; simpl; auto 10.
     intros; rewrite fa_ub_iff with (ub:=aub);[|auto].
     constructor;[simpl;auto|].
     intros; constructor;[do 2 apply levy_thin2; apply lva|].
     constructor.
      rewrite in_set_def; constructor; [simpl; auto 10|].
      apply levy_couple_eq; constructor; simpl; auto 10.

      constructor; simpl; auto 10.
Qed.

Lemma levy_func_succ v k n x a:
  is_var x v ->
  is_var a v ->
  levy_set v k n (func (succ x) a).
intros vx va.
apply levy_func_succ_ub with (aub:=a); auto with *.
constructor; simpl; auto.
Qed.

Lemma levy_list v k n a:
  is_var a v ->
  levy_set v k n (List a).
intros va z.
rewrite List_def.
constructor;[apply levy_empty_eq|constructor;[simpl;auto|]].
constructor; [simpl;auto|].
constructor; [simpl;auto|].
constructor; [simpl;auto|].
constructor;[|constructor].
*apply levy_thin_vars with (push_var x (push_var x1 (push_var x2 nil)));
   [apply levy_couple_eq;constructor;simpl;auto|].
 destruct 1 as [?|[?|[?|[ ]]]]; simpl;auto.
*apply levy_thin_vars with (push_var x1 nil);[apply levy_N|].
 destruct 1 as [?|[ ]]; simpl; auto.
*apply levy_str with z; [|apply levy_func_succ];simpl; auto 10.
Qed.

Lemma levy_succ_fst_eq v k n x :
  is_var x v ->
  levy_set_eq v k n (succ (fst x)).
intros vx z; unfold succ.
apply levy_eq_set.
*constructor;[simpl;auto|].
 intros; rewrite union2_ax; constructor.
  apply levy_fst; simpl; auto.
  apply levy_set_pair; apply levy_fst_eq; simpl; auto.
*unfold incl_set, union2.
 rewrite fa_union_iff.
 rewrite fa_pair_iff.
 2:intros ?? h; apply fa_morph; intro; rewrite h; reflexivity.
 constructor. 
 +unfold fst.
  rewrite fa_union_iff.
  rewrite fa_subset_iff.
  2:intros ?? h; rewrite h; reflexivity.
  rewrite fa_union_iff.
  constructor;[simpl;auto|].
  constructor;[simpl;auto|].
  constructor.
   rewrite in_set_def; constructor;[simpl;auto|].
   apply levy_pair_eq;constructor;simpl;auto.
  constructor;[simpl;auto|].
  constructor;simpl;auto.
 +unfold singl.
  rewrite fa_pair_iff.
  2:intros ?? h; rewrite h; reflexivity.
  rewrite in_set_def; constructor; (constructor;[simpl;auto|]);
    apply levy_fst_eq; simpl;auto.
Qed.

Lemma levy_Cons_eq v k n x l :
  is_var x v ->
  is_var l v ->
  levy_set_eq v k n (Cons x l).
intros vx vl z.
rewrite Cons_alt_def.  
apply levy_eq_set; unfold incl_set.
*constructor; [simpl;auto|].
 intros; rewrite union2_ax.
 constructor. 
 apply levy_set_pair;
   (apply levy_couple_eq;[apply levy_empty_eq|constructor;simpl;auto]).
 apply levy_replf; simpl; auto.
  intros ??? h; rewrite h; reflexivity.
 intros y c.  
 apply levy_couple_eq.
  apply levy_succ_fst_eq; simpl; auto.
 apply levy_snd_eq; simpl; auto.
*unfold singl, union2.
 rewrite fa_union_iff.
 rewrite fa_pair_iff.
 2:intros ?? h; apply fa_morph; intro; rewrite h; reflexivity.
 constructor. 
 +rewrite fa_pair_iff.
  2:intros ?? h; rewrite h; reflexivity.
  constructor. 
   rewrite in_set_def; constructor;[simpl;auto|].
   apply levy_couple_eq;[|constructor;simpl;auto].
   apply levy_empty_eq.
   rewrite in_set_def; constructor;[simpl;auto|].
   apply levy_couple_eq;[|constructor;simpl;auto].
   apply levy_empty_eq.
 +rewrite fa_replf_iff.
  2:intros ?? h; rewrite h; reflexivity.
  2:intros ??? h; rewrite h; reflexivity.
  constructor; [simpl;auto|].
  intros; rewrite in_set_def; constructor;[simpl;auto|].
  intros; apply levy_couple_eq.
   apply levy_succ_fst_eq; simpl; auto.
   apply levy_snd_eq; simpl; auto.
Qed.
 
Lemma levy_list_eq v k n a:
  is_var a v ->
  levy_set_eq v k n (List a).
intros va x.
rewrite eq_list_iff.
constructor;[|constructor].
*constructor; [simpl; auto|].
 intros; apply levy_list; simpl; auto.
*rewrite in_set_def; constructor;[simpl;auto|].
 intros; apply levy_empty_eq.
*constructor;[simpl;auto|].
 constructor;[simpl;auto|].
 intros; rewrite in_set_def.
 constructor; [simpl;auto|].  
 intros; apply levy_Cons_eq; simpl; auto.
Qed.

(*
Lemma Wdom_def a b ub :
  ext_fun a b ->
  (forall x, x ∈ a -> b x ⊆ ub) ->
  w ∈ Wdom a b <->
   w ⊆ prodcart (sup a b) a /\
    
         rel (List (sup A B)) A 
*)


Lemma levy_Wdom v k n a b ulb :
  is_var a v ->
  is_var ulb v ->
  ext_fun a b ->
  (List (sup a b) ⊆ ulb) ->
  (sup a b ⊆ ulb) ->
  (forall k' x z, levy (push_var z (push_var x v)) k' n (z ∈ b x)) ->
  levy_set v k n (Wdom a b).
intros va vub bext ulb_def ub_def lvb z.
unfold Wdom, rel.
rewrite power_ax.
constructor; [simpl;auto|intros c].
rewrite prodcart_def.
rewrite ex_ub_iff with (ub:=ulb).
2:destruct 1; auto.
constructor; [simpl;auto|intros x].
constructor.
*rewrite List_def.
 constructor.
  apply levy_empty_eq.
 constructor; [simpl;auto|].
 constructor; [simpl;auto|].
 constructor; [simpl;auto|].
 constructor; [simpl;auto|].
 constructor;[|constructor].
 +apply levy_str with x0; [simpl;auto 10|apply levy_couple_eq;constructor;simpl;auto].
 +apply levy_str with x2; [simpl;auto 10|apply levy_N].
 +apply levy_str with x; [|apply levy_func_succ_ub with (aub:=ulb)];simpl;auto 10.
  red; intros k' z0.
  rewrite sup_ax; trivial.
  rewrite ex_ex2.
  constructor; [simpl;auto 10|].
  intros; eapply levy_thin_vars;[apply (lvb k')|].
  destruct 1 as [?|[?|?]]; simpl;auto 10.
*constructor; [simpl;auto 10|].
 intros; apply levy_str with c; [|apply levy_couple_eq;constructor];simpl;auto.
Qed.

Require Import ZFw.


Parameter Form : set.
Parameter Feq : set -> set -> set.
Parameter Feq_typ : forall n, n ∈ N -> forall m, m ∈ N -> Feq n m ∈ Form.
Parameter Fin : set -> set -> set.
Parameter Fin_typ : forall n, n ∈ N -> forall m, m ∈ N -> Fin n m ∈ Form.
Parameter Fand For Fimp : set -> set -> set.
Parameter Fand_typ : forall P Q, P ∈ Form -> Q ∈ Form -> Fand P Q ∈ Form.
Parameter For_typ : forall P Q, P ∈ Form -> Q ∈ Form -> For P Q ∈ Form.
Parameter Fimp_typ : forall P Q, P ∈ Form -> Q ∈ Form -> Fimp P Q ∈ Form.
Parameter Ffa Fex : set -> set.
Parameter Ffa_typ : forall P, P ∈ Form -> Ffa P ∈ Form.
Parameter Fex_typ : forall P, P ∈ Form -> Fex P ∈ Form.

Parameter Fint_var : set -> set -> set.
Parameter Fint : set -> set -> Prop.
Parameter Fint_eq : forall i m n,
  Fint i (Feq m n) <-> Fint_var i m == Fint_var i n.
Parameter Fint_in : forall i m n,
  Fint i (Feq m n) <-> Fint_var i m ∈ Fint_var i n.
Parameter Fint_and : forall i P Q,
  Fint i (Fand P Q) <-> (Fint i P /\ Fint i Q).
Parameter Fint_or : forall i P Q,
  Fint i (For P Q) <-> (Fint i P \/ Fint i Q).
Parameter Fint_imp : forall i P Q,
  Fint i (Fimp P Q) <-> (Fint i P -> Fint i Q).
Parameter Fint_fa : forall i P,
  Fint i (Ffa P) <-> (forall x:set, Fint (Cons x i) P).
Parameter Fint_ex : forall i P,
  Fint i (Fex P) <-> (exists x:set, Fint (Cons x i) P).

Parameter Fint_morph : Proper (eq_set==>eq_set==>iff) Fint.
Existing Instance Fint_morph.
(*
Fixpoint list2set (l:list set) : set :=
  match l with
  | nil => Nil
  | x::l => Cons x (list2set l)
  end.

Definition Levy i k n P :=
  forall v:var_set, list2set v = i ->
  levy v k n (Fint i P).

Lemma Levy_and i k n P Q :
  Levy i k n P -> Levy i k n Q -> Levy i k n (Fand P Q).
unfold Levy; intros.
specialize H with (1:=H1).
specialize H0 with (1:=H1).
rewrite Fint_and.
constructor; trivial.
Qed.*)
(*Lemma Levy_fa_prd i n P :
  (forallLevy i Prd (S n) P -> Levy i Prd (S n) (Ffa P).*)

Parameter Levy : qu -> nat -> set -> Prop.

Definition isList x :=
  forall P:set->Prop,
    Proper (eq_set==>iff) P ->
    P Nil ->
    (forall x l, P l -> P (Cons x l)) ->
    P x.


Definition uniq R x y :=
  forall x', x'==x -> forall y', R x' y' <-> y==y'.

Lemma uniq_repl_rel I R : ZFrepl.repl_rel I (uniq R).
unfold uniq; split; intros.
*rewrite H2;[rewrite H1;reflexivity|rewrite H0; trivial].
*apply H0 with (x':=x);[reflexivity|].
 rewrite H1; reflexivity.
Qed.

Definition repl' I R := repl I (uniq R).
  

Definition levy_repl k n U :=
  forall i,
  forall I, I ∈ U ->
  forall R, R ∈ Form ->
  Levy k n R ->
  (forall x, x ∈ I -> forall y, y ∈ U -> forall y', y' ∈ U ->
   Fint (Cons y (Cons x i)) R -> Fint (Cons y' (Cons x i)) R -> y==y') ->
  repl' I (fun x y => y ∈ U /\ Fint (Cons y (Cons x i)) R) ∈ U.


Definition Ug_inductive X U :=
  X ∈ U /\
  (forall x, x ∈ U -> forall y, y ∈ x -> y ∈ U) /\
  (forall x, x ∈ U -> forall y, y ∈ U -> pair x y ∈ U) /\
  (forall x, x ∈ U -> power x ∈ U) /\
  (forall x, x ∈ U -> union x ∈ U) /\
  levy_repl Sig 3 U.
(*
    (forall v I R, ZFrepl.repl_rel I R -> I ∈ U ->
                (forall x y, x ∈ I -> R x y -> y ∈ U) ->
                (forall x y, is_var x v -> is_var y v -> levy v Sig 3 (R x y)) ->
                repl I R ∈ U).
*)

Lemma repl_eq_iff : forall p a R,
  ZFrepl.repl_rel a R ->
  p == repl a R <->
  (forall x y, x ∈ a -> R x y -> y ∈ p) /\
  (forall y, y ∈ p -> exists2 x, x ∈ a & R x y).
split; intros.
*split; intros.
 +rewrite H0.
  apply repl_ax; eauto.
   apply H.
   apply H.
 +rewrite H0 in H1.
  apply repl_ax in H1; trivial.
  apply H.
  apply H.
*destruct H0.
 apply ZFrepl.repl_ext; trivial.
Qed.



Lemma levy_levy_repl v n k m U :
  is_var U v ->
  levy v Prd (S n) (levy_repl k m U).
intros vU.
unfold levy_repl.
apply F_fa_prd; intros i.
constructor;[simpl;auto|intros I].
apply F_fa_prd; intros R.
constructor.
{admit. (* ∈Form Σ_1 *) }
constructor.
{admit. (* Levy Σ_1 *) }
constructor.
{constructor;[simpl;auto|intros x].
 constructor;[simpl;auto|intros y].
 constructor;[simpl;auto 10|intros y'].
 constructor.
  admit. (* Fint Π_1 *)
 constructor.
  admit. (* Fint Π_1 *)
 constructor; simpl; auto. }
rewrite in_set_def.
constructor;[simpl;auto|intros y].
unfold repl'; rewrite repl_eq_iff.
2:apply uniq_repl_rel.
assert (uniq_iff : forall a b,
b ∈ U /\
  Fint (Cons b (Cons a i)) R /\
  (forall y' : set, y' ∈ U -> Fint (Cons y' (Cons a i)) R -> b == y') <->
  uniq (fun x y0 => y0 ∈ U /\ Fint (Cons y0 (Cons x i)) R) a b).
{unfold uniq; split; intros.
 destruct H as (?&?&?).
 rewrite H0. 
 split; intros.
 destruct H3; auto.  
 rewrite <-H3; auto.
 assert (aux := H a (reflexivity _)).
 split;[apply aux;reflexivity|].
 split;[apply aux;reflexivity|].
 intros.
 apply aux; auto. }
constructor.
*apply F_fa_prd; intros a.
 apply F_fa_prd; intros b.
 constructor;[constructor;simpl;auto 10|].
 constructor;[|constructor;simpl;auto 10].
 apply F_ext with (1:=uniq_iff a b).
 constructor;[constructor; simpl; auto 10|].  
 constructor.
  admit. (* Fint Σ_1 *)
 constructor;[simpl;auto 10|intros y'].
 constructor;[|constructor;simpl;auto 10].
 admit. (* Fint Π_1 *)
*constructor;[simpl;auto 10|intros b].
 rewrite ex_ex2.
 constructor;[simpl;auto 10|intros a].
 apply F_ext with (1:=uniq_iff a b).
 constructor;[constructor; simpl; auto 10|].  
 constructor.
  admit. (* Fint Π_1 *)
 constructor;[simpl;auto 10|intros y'].
 constructor;[|constructor;simpl;auto 10].
 admit. (* Fint Σ_1 *)
Admitted.

  
  Lemma levy_Ug_inductive v n X U :
  is_var X v ->
  is_var U v ->
  levy v Prd (S n) (Ug_inductive X U).
intros vX vU.
constructor;[|constructor;[|constructor;[|constructor;[|constructor]]]].
*constructor; simpl; auto.
*constructor;[simpl;auto|].
 constructor;[simpl;auto|].
 constructor;simpl;auto.
*constructor;[simpl;auto|].
 constructor;[simpl;auto|].
 intros.
 rewrite in_set_def.
 constructor;[simpl;auto|].
 apply levy_pair_eq; simpl; auto.
*constructor;[simpl;auto|].
 intros.
 rewrite in_set_def.
 constructor;[simpl;auto|].
 apply levy_power_eq; simpl; auto. (* Π_1 *)
*constructor;[simpl;auto|].
 intros.
 rewrite in_set_def.
 constructor;[simpl;auto|].
 apply levy_union_eq; simpl; auto.
*apply levy_levy_repl; trivial.
Qed.
(*
*assert (var_set_def : var_set = {l|l ∈ List U}) by admit.
 assert (Form : set) by admit.
 assert (form_def : (set -> Prop) = {f|f ∈ Form}) by admit.
assert (admit : forall P:Prop,P) by admit.
 apply F_ext with
   (forall v (tyv:v ∈ List U), forall I, I∈U -> forall R, R ∈ func I Form ->
    let R' := fun x y => @eq_rect_r Type _ (fun A=>A) (exist (fun f=>f∈Form) (ZFrelations.app R x) (app_typ _ _ _ _ (admit (R∈func I Form))(*tyR*) (admit (x ∈ I)))) _
                           form_def y in
    ZFrepl.repl_rel I R' -> 
    (forall x y, x ∈ I -> R' x y -> y ∈ U) ->
    (forall x, x ∈ v -> forall y, y ∈ v ->
      levy (eq_rect_r (fun A=> A) (exist (fun l=>l∈List U) v (admit (v∈List U))(*tyv*)) var_set_def) Sig 3 (R' x y)) ->
    repl I R' ∈ U).
 {split; intros.
  *pose (Rs := lam I (fun x => proj1_sig (@eq_rect _ _ (fun A=>A) (R x) _ form_def))).
   pose (R' := fun x y => eq_rect_r (fun A=>A) (exist (fun f=>f∈Form)
                                                  (ZFrelations.app Rs x)
               (app_typ _ _ _ _ (admit (Rs ∈ func I Form)) (admit (x∈I)))) form_def y).
   assert (RR' : (eq_set==>eq_set==>iff)%signature R R').
   {do 2 red; intros.
    unfold R'.
    unfold Rs.
(*    erewrite eq_exist_curried.
    Unshelve.    *)
    admit. }
   rewrite (ZFrepl.repl_morph_raw I I (reflexivity I) R R' RR').
   pose (v' := @eq_rect _ _ (fun A=>A) v0 _ var_set_def).
   assert (v'set : forall x, x ∈ proj1_sig v' <-> is_var x v0).
   {unfold v'.
    admit. }
  +apply H with (v:=proj1_sig v').
   ++apply proj2_sig.
   ++trivial.
   ++apply lam_is_func.
      intros ??? h.
      admit.     
      intros; apply proj2_sig.
   ++change (ZFrepl.repl_rel I R').
      destruct H0; split; intros.
      do 2 red in RR'.
      apply ->RR'.
      eapply H0;[exact H5|exact H6 |exact H7 |].
      apply <-RR'.
      apply H8.
      reflexivity.
      reflexivity.
      reflexivity.
      reflexivity.
      apply H4 with (1:=H5).
      revert H6; apply RR'; reflexivity.
      revert H7; apply RR'; reflexivity.
    ++intros.
      change (R' x y) in H5.      
      apply H2 with x; trivial.
      revert H5; apply RR'; reflexivity.
    ++intros.
      apply v'set in H4.      
      apply v'set in H5.      
      replace (admit (proj1_sig v' ∈ List U)) with (proj2_sig v') by admit.
      replace (exist (fun l=>l∈List U) (proj1_sig v') (proj2_sig v')) with v'.
      replace (eq_rect_r (fun A=>A) v' var_set_def) with v0.
      change (levy v0 Sig 3 (R' x y)).
      rewrite <- (RR' x x (reflexivity x) y y (reflexivity y)).
      apply H3; trivial.
      unfold v'.
      case var_set_def; simpl; reflexivity.
      destruct v'; simpl; trivial.
  *admit. }
 apply F_fa_prd.
 intros v0.
 constructor.
  admit.
 constructor;[simpl;auto|intros I].
 apply F_fa_prd.
 intros R.
 constructor.
  admit.
simpl; set (R' :=
       fun x y : set =>
       eq_rect_r (fun A : Type => A)
         (exist (fun f : set => f ∈ Form) (ZFrelations.app R x)
            (app_typ R x I Form (admit (R ∈ func I Form)) (admit (x ∈ I)))) form_def y ).
 constructor.
 {constructor.
   apply F_ext with (forall x,x∈I->forall x',x'∈I->forall y,y∈I->forall y',y'∈I->x==x'->y==y'->R' x y->R' x' y').
   {split; intros; eauto.
    revert H3; apply H; trivial.   
    
    
 ;[simpl;
      auto.
      
      unfold v'.
      destruct var_set_def.

        apply (RR' x x (reflexivity x) y y (reflexivity y)); trivial.
      apply <-RR';reflexivity.

      
     rewrite <-(RR' _ _ (reflexivity _)(reflexivity _)) in H8|-*.
    
    apply levy_pair_eq; simpl; auto.

  
*rewrite in_set_def; constructor;[ simpl; auto|].
 intros; apply levy_empty_eq.
*constructor;[simpl; auto|intros z].
 rewrite in_set_def; constructor;[simpl;auto|].
 intros y.
 unfold succ, union2.
 (**)
 apply levy_eq_set.
 +constructor;[simpl;auto|].
  intros z'; rewrite union_def.
  rewrite ex_pair_iff.
  constructor; [constructor; simpl; auto|].  
  apply levy_pair; simpl; auto.
  intros ?? h; rewrite h; reflexivity.
 +unfold incl_set.
  rewrite fa_union_iff.
  rewrite fa_pair_iff.
  constructor.
  ++constructor; [simpl;auto|].
    constructor; simpl; auto.
  ++unfold singl; rewrite fa_pair_iff.
    constructor; constructor; simpl; auto.
    intros ?? h; rewrite h; reflexivity.
  ++intros ?? h.
    apply fa_morph; intros z'.
    rewrite h; reflexivity.
Qed.
*)

Definition U_inductive X V :=
  (forall x, x ∈ V -> forall y, y ∈ x -> y ∈ V) /\
  X ∈ V /\
  (forall A, A ∈ V -> forall B, B ∈ V -> is_cc_fun A B ->
   (exists v:var_set, levy_set_eq v Sig 2 B) ->
   (forall x, x ∈ A -> cc_app B x ∈ V) -> cc_prod A (cc_app B) ∈ V).
   (*  /\ W A (cc_app B) ∈ V).*)

Instance U_inductive_morph : Proper(eq_set==>eq_set==>iff) U_inductive.
do 3 red; intros.
apply and_iff_morphism;[|apply and_iff_morphism].
*apply fa_morph; intros x1.
 apply impl_morph;[rewrite H0;reflexivity|intros _].
 apply fa_morph; intros y1.
 rewrite H0; reflexivity.
*rewrite H,H0; reflexivity.
*apply fa_morph; intros A.
 apply impl_morph;[rewrite H0;reflexivity|intros _].
 apply fa_morph; intros B.
 apply impl_morph;[rewrite H0;reflexivity|intros _].
 apply impl_morph;[reflexivity|intros _].
 apply fa_morph; intros _.
 apply impl_morph;[|rewrite H0;reflexivity].
 apply fa_morph; intros x1.
 rewrite H0; reflexivity.
Qed. 
 
Definition Univ (U:set) (a:set) :=
  subset U (fun x => forall V, U_inductive a V -> x ∈ V).

Lemma Univ_def U a x :
  x ∈ Univ U a <-> x ∈ U /\ forall V, U_inductive a V -> x ∈ V.
unfold Univ; rewrite subset_ax.
apply and_iff_morphism;[reflexivity|].
split; intros.
destruct H as (x',eqx,?).
rewrite eqx; auto.
exists x; auto with *.
Qed.

Require Import ZFgrothendieck.
Section Univ_closure.
  Variable X U : set.
  Hypothesis GU : grot_univ U.
  Hypothesis XinU : X ∈ U.

  Lemma U_X : X ∈ Univ U X.
apply Univ_def; split;[trivial|].
intros.
apply H.
Qed.

  Lemma U_trans x y : x ∈ Univ U X -> y ∈ x -> y ∈ Univ U X. 
intros Ux yx.
apply Univ_def in Ux; destruct Ux.
apply Univ_def; split; intros.
apply G_trans with x; trivial. 
apply (proj1 H1) with x; auto.
Qed.

  Lemma U_prod :
    forall A, A ∈ Univ U X -> forall B, B ∈ Univ U X -> is_cc_fun A B ->
    (exists v, levy_set_eq v Sig 2 B) ->
    (forall x, x ∈ A -> cc_app B x ∈ Univ U X) ->
    cc_prod A (cc_app B) ∈ Univ U X.
intros A UA B UB Bfun lvB UBimg.
apply Univ_def.
split.
*apply Univ_def in UA; destruct UA.
 apply G_cc_prod; trivial.
  intros ??? h; rewrite h; reflexivity.
 intros.
 apply UBimg in H1.  
 apply Univ_def in H1; destruct H1; trivial.
*intros. 
 apply Univ_def in UA; destruct UA.
 apply Univ_def in UB; destruct UB.
 apply H; auto.
 intros.
 apply UBimg in H4.
 apply Univ_def in H4; destruct H4; auto.
Qed.

  Lemma U_induc : U_inductive X (Univ U X).
split;[|split]; intros.
*apply U_trans with x; trivial.
*apply U_X.
*apply U_prod; trivial.
Qed.

 Lemma Univ_ind_def x :
   x ∈ Univ U X <-> forall V, U_inductive X V -> x ∈ V.
split; intros.
*apply Univ_def in H; destruct H; auto.
*apply H; apply U_induc.
Qed.

 Lemma Univ_ind_def' x :
   x ∈ Univ U X <-> forall V, V ⊆ U -> U_inductive X V -> x ∈ V.
split; intros.
*apply Univ_def in H; destruct H; auto.
*apply H; [|apply U_induc].
 red; intros.
 apply Univ_def in H0; destruct H0; trivial.
Qed.

  Lemma U_eq_def x : x == Univ U X <-> x ⊆ Univ U X /\ U_inductive X x.
split; intros.
*rewrite H.
 split;[reflexivity|]. 
 apply U_induc.  
*destruct H.
 apply incl_eq; trivial.
 red; intros. 
 apply Univ_def in H1.
 destruct H1; auto.
Qed.


  Lemma levy_is_cc_fun v k n a f :
    is_var a v ->
    is_var f v ->
    levy v k n (is_cc_fun a f).
intros va vf.
unfold is_cc_fun.
constructor; [simpl;auto|].
constructor.
*apply levy_str with x; [simpl; auto|].
 apply levy_couple_eq.
  apply levy_fst_eq; simpl; auto.
  apply levy_snd_eq; simpl; auto.
*rewrite in_set_def.
 constructor;[simpl;auto|].
 apply levy_fst_eq; simpl; auto.
Qed.
  
  Lemma levy_U_inductive v n x :
    is_var x v ->
    levy_set_eq v Prd (S n) X ->
    levy v Prd (S n) (U_inductive X x).
intros vx lvX.
unfold U_inductive.
constructor;[|constructor].
*constructor;[simpl;auto|].
 constructor;[simpl;auto|].
 constructor;simpl;auto.
*rewrite in_set_def.
 constructor;[simpl;auto|].
 apply lvX. 
*constructor;[simpl;auto|].
 constructor;[simpl;auto|].
 constructor.
 {apply levy_is_cc_fun; simpl; auto. }
 constructor.
 {admit. } (* ∃v.levy Σ_1 *)
 constructor.
 {constructor;[simpl;auto|].
  intros; rewrite in_set_def.
  constructor;[simpl;auto|].
  apply levy_cc_app_eq; simpl; auto.
  constructor; simpl; auto. }
 intros; rewrite in_set_def.
 constructor;[simpl;auto|].
 intros.
 apply levy_cc_prod_eq;
   [intros ??? h; rewrite h; reflexivity|simpl;auto|].
 intros.  
 destruct H.
 red in H1; simpl in H1.
 rewrite ex_cc_app_iff.
 constructor;[simpl;auto|].
 constructor;[simpl;auto|].
 constructor;[simpl;auto|].
 constructor.
 +apply levy_str with x4; [simpl; auto|].
  apply levy_couple_eq; constructor; simpl; auto.
 +do 2 apply levy_thin2; trivial.
Admitted.
  

  Lemma levy_univ v n :
    is_var X v ->
    levy_set v Prd (S (S n)) (Univ U X).
intros vX z.
rewrite Univ_ind_def.
apply F_fa_prd; intros V.
constructor; [|constructor; simpl;auto].
apply levy_lift with Prd.
apply levy_U_inductive; simpl; auto.
constructor; simpl;auto.
Qed.
  
  Lemma levy_univ_eq v n :
    is_var X v ->
    levy_set_eq v Prd (S (S n)) (Univ U X).
intros vX z.
rewrite U_eq_def.
constructor.
*constructor;[simpl;auto|].
 apply levy_univ; simpl; auto.
*apply levy_U_inductive; simpl; auto.
 constructor; simpl; auto.
Qed.
  
  
End Univ_closure.
  
