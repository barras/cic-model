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
Hint Resolve levy_thin1 levy_thin2 : core.

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
    
  Lemma levy_cut v k n P y a :
    (Proper (eq_set==>iff) P) ->
    (P y -> y ∈ a) ->
    is_var a v ->
    (forall x, levy (x::v) k n (x==y)) ->
    (forall x, levy (x::v) k n (P x)) ->
    levy v k n (P y).
intros Pm Pa va lve lvp.                              
apply F_ext with (exists z, z ∈ a /\ z==y /\ P z).
*split.
  destruct 1 as (z&_&eqz&?).
  rewrite <- eqz; trivial.
 intros.
 exists y; auto with *.
*constructor;[trivial|].
 constructor; trivial.
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
  
  Require Import ZFwfr.
(*
 forall Rsub : set -> set,
       morph1 Rsub ->
       forall (F : (set -> set) -> set -> set) (xx : set),
       (forall (x x' : set) (f f' : set -> set),
        ZFrepl.WFRle Rsub x xx ->
        (forall y y' : set, y ∈ Rsub x -> y == y' -> f y == f' y') -> x == x' -> F f x == F f' x') ->
       Acc (fun x y : set => x ∈ Rsub y) xx -> WFR Rsub F xx == F (WFR Rsub F) xx
  *)
  (**)
(*  Lemma levy_pair_eq v k n x a b :
    (forall z, levy (z::v) k n (z==a)) ->
    (forall z, levy (z::v) k n (z==b)) ->
    is_var x v ->
    levy v k n (x==pair a b).
intros lva lvb xv.
apply levy_cut with (a:=x) (P:=fun a' => x == pair a' b) (y:=a); auto.
*do 2 red; intros; rewrite H; reflexivity.
*intros.
 rewrite H; auto. 
*constructor; simpl; auto.
*intros a'.
 apply levy_cut with (a:=x) (P:=fun b' => x == pair a' b') (y:=b); auto.
+do 2 red; intros; rewrite H; reflexivity.
+intros.
 rewrite H; auto. 
+constructor; simpl; auto.
+intros b'.
 eapply levy_thin_vars; [apply lvb|].
 destruct 1; simpl; auto 10.
+intros b'.
 apply d0_levy.
 eapply levy_thin_vars; [apply d0_pair_eq|].
 destruct 1 as [?|[?|[?|[ ]]]]; simpl; auto 10.
 rewrite H in xv; auto.
Qed.
*)

    
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
(*
Lemma fa_props_iff :
  (forall z, z∈props -> P z) <->
    (forall x, x∈z 
*)
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
    is_var a v (*levy_set v k n a*) ->
    is_var b v (*levy_set v k n b*) ->
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

(*
Lemma cc_lam_alt_def a f uf z :
  ext_fun a f -> 
  uf == sup a f ->
  z ∈ cc_lam a f <->
    exists x, x ∈ a /\ exists y, y ∈ uf /\ y ∈ f x /\ z == couple x y.
intros fext uf_def.  
rewrite cc_lam_def; [|trivial].
rewrite ex_ex2.
apply ex_morph; intros x.
apply and_iff_morphisml;[reflexivity|intros tyx _].
rewrite ex_ex2.
apply ex_morph; intros y.
rewrite uf_def, sup_ax; trivial.
split; intros.
*destruct H.
 split; auto.
 exists x; trivial. 
*destruct H; auto.
Qed.

Lemma fa_cc_lam_iff_ub a f uf P :
  Proper (eq_set ==> iff) P ->
  ext_fun a f -> 
  uf == sup a f ->
  (forall z, z ∈ cc_lam a f -> P z) <->
    (forall x, x ∈ a -> forall y, y ∈ uf -> y ∈ f x -> P (couple x y)).
intros Pm fext uf_def.  
split; intros.
*apply H.
 apply cc_lam_alt_def with (uf:=uf); trivial.
 exists x; split;[trivial|].
 exists y; split;[trivial|auto with *].
*apply cc_lam_alt_def with (uf:=uf) in H0; trivial.
 destruct H0 as (x&?&y&?&?&?).
 rewrite H3; eauto. 
Qed.
*)

Lemma levy_cc_lam_delta v n x f :
  ext_fun x f ->
  is_var x v ->
  (forall y, levy_set_eq (push_var y v) Sig (S n) (f y)) ->
  forall k, levy_set v k (S n) (λ y ∈ x, f y).
intros fext xv lvf k z.
rewrite cc_lam_def; trivial.
rewrite ex_ex2.
constructor;[simpl;auto|].
intros.
rewrite ex_ex2.
revert k; apply ex_in_delta.
*intros ?? h; rewrite h; reflexivity.
*intro; eapply levy_thin_vars; [apply lvf|].
 destruct 1 as [?|[?|?]]; simpl; auto. 
*intros.
 apply levy_str with z; simpl; auto 10.
 apply levy_couple_eq; constructor; simpl; auto.
Qed.

(*
 Lemma levy_cc_lam_delta_eq v n x f :
  is_var x v ->
  (forall k y, levy_set_eq (push_var y v) k (S n) (f y)) ->
  forall k, levy_set_eq v k (S n) (λ y ∈ x, f y).
red; intros.
  *)
 
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
  (forall x v' P, (*Proper (eq_set==>iff) P ->*)
   is_var x v' /\ incl_vars v v' ->
   (forall y, levy (push_var y v') k n (P y)) ->
   levy v' k n (exists y, y ∈ b x /\ P y)) ->         
  levy_set v k n (cc_prod a b).
intros bext va lvb z.
rewrite cc_prod_def;[|trivial].
constructor.
*constructor;[simpl;auto|].
 constructor;[simpl;auto|].
 intros; apply lvb;
   [(*intros ?? h;apply ex_morph;intro;rewrite h;reflexivity|*)unfold incl_vars;simpl;auto|].
 constructor;[simpl;auto|].
 intros; apply levy_str with x; simpl; auto 10.
 apply levy_couple_eq; constructor; simpl; auto 10.
*constructor;[simpl;auto|].
 intros; apply lvb; [(*|*)unfold incl_vars;simpl;auto|].
 (*{intros ?? h;apply and_iff_morphism.
  *apply fa_morph; intros y'; rewrite h; reflexivity.
  *apply fa_morph; intros p; apply fa_morph; intros _; apply fa_morph; intros _.
   apply ex_morph; intros y'; rewrite h; reflexivity. }*)
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
  (forall k x v' P, (*Proper (eq_set==>iff) P ->*)
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
 destruct H(*0*); split; auto.
 red in H1(*2*); red; intros; apply H1(*2*); simpl;auto. 
*apply F_fa_prd; intros f.
 constructor;[|constructor; simpl; auto]. 
 apply levy_cc_prod; simpl; auto.
 intros.
 apply lvb; auto.
 destruct H(*0*); split; auto.
 red in H1(*2*); red; intros; apply H1(*2*); simpl;auto. 
Qed.

 
Lemma levy_cc_prod_app v k n a b :
  is_var a v ->
  is_var b v ->
  levy_set v k n (cc_prod a (cc_app b)).
intros va vb.
apply levy_cc_prod;[intros ??? h; rewrite h; reflexivity|trivial|].
intros.
destruct H.
red in H1.
rewrite ex_cc_app_iff.
constructor;[simpl;auto|].
constructor;[simpl;auto|].
constructor;[simpl;auto|].
constructor.
*apply levy_str with x0; [simpl;auto 10|].
 apply levy_couple_eq; constructor; simpl; auto 10.
*do 2 apply levy_thin2; trivial.
Qed.

Lemma cc_prod_def_ub f a b ub :
  ext_fun a b ->
  (forall x, x ∈ a -> b x ⊆ ub) ->
  f ∈ cc_prod a b <->
        (forall p, p ∈ f -> exists x, x ∈ a /\ exists y, y ∈ ub /\ y ∈ b x /\
                              exists y', y' ∈ y /\ p == couple x y') /\
          (forall x, x∈a -> exists y, y ∈ ub /\ y ∈ b x /\
                              (forall y', y' ∈ y -> couple x y' ∈ f) /\
                     forall p, p ∈ f -> x == fst p ->
                               exists y', y' ∈ y /\ p == couple x y').
intros bext ub_def.
unfold cc_prod.
rewrite replf_ax.  
split; intros.
*destruct H as (f',tyf',eqf).
 split ;intros.
 +rewrite eqf in H.
  rewrite cc_lam_def in H.
  destruct H as (x,tyx,(y',?,eqp)).
  exists x; split ;[trivial|].
  assert (app f' x ∈ b x).
  {apply dep_func_elim with (1:=tyf'); trivial. }
  exists (app f' x); split; [|split;[trivial|]].
   apply (ub_def x); trivial.
  exists y'; auto.  
  {do 2 red; intros. rewrite H1; reflexivity. }
 +assert (aux : app f' x ∈ b x).
  {apply dep_func_elim with (1:=tyf'); trivial. }
  exists (app f' x); split; [|split;[trivial|]].
   apply (ub_def x); trivial.
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
  destruct H0 with (1:=H1) as (y&_&?&?&?).
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
    destruct H2 as (?&y&_&?&?&?&?).
    rewrite H5,fst_def,snd_def; auto with *.
  ++apply cc_lam_ext;[reflexivity|].
    intros z z' tyz eqz.
    rewrite beta_eq; auto.
     rewrite eqz; reflexivity.    
     do 2 red; intros ??? h; rewrite h; reflexivity.
     rewrite <-eqz; trivial.
*do 2 red; intros.
 apply cc_lam_ext;[reflexivity|].
 red; intros.
 rewrite H0,H2; reflexivity.
Qed.

Lemma levy_cc_prod_ub v k n a b ub :
  is_var a v ->
  is_var ub v ->
  ext_fun a b ->
  (forall x, x ∈ a -> b x ⊆ ub) ->
  (forall x z, levy (push_var z (push_var x v)) k n (z ∈ b x)) ->
  levy_set v k n (cc_prod a b).
intros va vub bext ub_def lvb z.
rewrite cc_prod_def_ub with (ub:=ub); trivial.
constructor.
*constructor;[simpl;auto|].
 constructor;[simpl;auto|].
 constructor;[simpl;auto|].
 intros z'.
 constructor.
  apply levy_thin_vars with (1:=lvb x0 z').
  destruct 1 as [?|[?|?]]; simpl; auto.
 constructor;[simpl;auto|].
 intros.
 apply levy_thin_vars with (push_var x (push_var x0 (push_var x1 nil)));
   [apply levy_couple_eq;constructor; simpl;auto|].
 destruct 1 as [?|[?|[?|[ ]]]]; simpl; auto.
*constructor;[simpl;auto|].
 constructor;[simpl;auto|].
 intros z'.
 constructor.
  apply levy_thin_vars with (1:=lvb x z').
  destruct 1 as [?|[?|?]]; simpl; auto.
 constructor.
  constructor;[simpl;auto|].
  intros; rewrite in_set_def; constructor;[simpl;auto|].
  apply levy_couple_eq; constructor; simpl; auto.

  constructor;[simpl;auto|].
  constructor.
   apply levy_thin_vars with (push_var x (push_var x0 nil)).
   apply levy_fst_eq; simpl; auto.
   destruct 1 as [?|[?|[ ]]]; simpl; auto.

   constructor;[simpl;auto|].
   intros.
   apply levy_thin_vars with (push_var x0 (push_var x (push_var x1 nil))).
    apply levy_couple_eq; constructor; simpl; auto.
    destruct 1 as [?|[?|[?|[ ]]]]; simpl; auto.
Qed.

Lemma levy_cc_prod_ub' v k n a b ub :
  is_var a v ->
  is_var ub v ->
  ext_fun a b ->
  (forall x z, levy (push_var z (push_var x v)) k n (z ∈ b x)) ->
  levy_set v k n (cc_prod a (fun x => ub ∩ b x)).
intros.
apply levy_cc_prod_ub with (ub:=ub); trivial.
*do 2 red; intros.
 rewrite (H1 x x'); auto with *.
*intros.
 apply inter2_incl1.
*intros.
 rewrite inter2_def.
 constructor.
  constructor; simpl; auto.
  auto.
Qed.  

Lemma levy_cc_arr_ub v k n a b :
  is_var a v ->
  is_var b v ->
  levy_set v k n (cc_arr a b).
intros va vb.
apply levy_cc_prod_ub with (ub:=b); auto with *.
constructor; simpl; auto.
Qed.
  
Lemma levy_cc_prod_eq_ub v n a b ub :
  is_var a v ->
  is_var ub v ->
  ext_fun a b ->
  (forall x, x ∈ a -> b x ⊆ ub) ->
  (* z∈b(x) is Δ_{n+1} *)
  (forall k x z, levy (push_var z (push_var x v)) k (S n) (z ∈ b x)) ->
  levy_set_eq v Prd (S n) (cc_prod a b).
intros va vub bext ub_def lvb z.
apply levy_eq_set.
*constructor; [simpl;auto|].
 apply levy_cc_prod_ub with (ub:=ub); simpl; auto.
 intros x z'; eapply levy_thin_vars; [apply (lvb Prd x z')|].
 destruct 1 as [?|[?|?]]; simpl; auto.
*apply F_fa_prd.
 constructor.
  apply levy_cc_prod_ub with (ub:=ub); simpl; auto.
  intros x' z'; eapply levy_thin_vars; [apply (lvb Sig x' z')|].
  destruct 1 as [?|[?|?]]; simpl; auto.
 constructor; simpl; auto.
Qed.

Lemma levy_cc_prod_eq_ub' v n a b ub :
  is_var a v ->
  is_var ub v ->
  ext_fun a b ->
  (* z∈b(x) is Δ_{n+1} *)
  (forall k x z, levy (push_var z (push_var x v)) k (S n) (z ∈ b x)) ->
  levy_set_eq v Prd (S n) (cc_prod a (fun x => ub ∩ b x)).
intros.
apply levy_cc_prod_eq_ub with (ub:=ub); trivial.
*do 2 red; intros.
 rewrite (H1 x x'); auto with *.
*intros.
 apply inter2_incl1.
*intros.
 rewrite inter2_def.
 constructor.
  constructor; simpl; auto.
  auto.
Qed.  


Lemma levy_cc_arr_eq_ub v n a b :
  is_var a v ->
  is_var b v ->
  levy_set_eq v Prd (S n) (cc_arr a b).
intros va vb.
apply levy_cc_prod_eq_ub with (ub:=b); auto with *.
constructor; simpl; auto.
Qed.

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

(*Lemma fa_ex_iff :
  (forall x, (exists y, P x y) -> Q x) <-> (forall 


                                 Lemma fa_ex_iff :
  (forall x, (P x <-> exists y, y ∈ a /\ P' x y )) ->
  (forall x, P x -> Q x) <-> (forall *)
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


(*Definition bounded v x :=
  is_var x v \/ 
  x == empty \/
  (exists a b, x == pair a b) \/
  (exists a, x == union a) \/
  (exists a P, x == subset a P) \/
  (exists a F, x == replf a F). 
*)
(*inductive bounded*)
(*
Lemma F_fa_bounded v k n x P :
  Proper (eq_set==>iff) P ->
  bounded v x ->
  (forall z, levy (push_var z v) k n (P z)) ->
  levy v k n (forall z, z∈x -> P z).
intros Pm bx lvP.
destruct bx as [?|[?|[(a&b&?)|[(a,?)|[(a&Q&?)|(a&F&?)]]]]].
*constructor; simpl; auto.
*apply F_ext with True;[|constructor].
 split; [intros|trivial].
 rewrite H in H1; apply empty_ax in H1; contradiction.
*admit. (*setoid_replace (forall z, z∈x->P z)
   with (forall z, z∈pair a b ->z==P z).
 2:apply fa_morph; intros z; rewrite H; reflexivity.
 rewrite fa_pair_iff; [|trivial].
 constructor.
         *)
*setoid_replace (forall z, z∈x->P z)
   with (forall z, z∈union a ->P z).
 2:apply fa_morph; intros z; rewrite H; reflexivity.
 rewrite fa_union_iff.
 constructor; [simpl;auto|]. admit. (* Hrec... *)
 intros y.
 constructor; [simpl;auto|auto].
*setoid_replace (forall z, z∈x->P z)
   with (forall z, z∈subset a Q ->P z).
 2:apply fa_morph; intros z; rewrite H; reflexivity.
 rewrite fa_subset_iff.
2:admit. (* Qm *)
constructor; [simpl;auto|]. admit. (* Hrec... *)
 intros y.
 constructor; auto.
 admit. (* Q levy opp *)
*setoid_replace (forall z, z∈x->P z)
   with (forall z, z∈replf a F ->P z).
 2:apply fa_morph; intros z; rewrite H; reflexivity.
 rewrite fa_replf_iff; trivial.
2:admit. (* Fext *)
constructor; [simpl;auto|]. admit. (* Hrec... *)
 intros y.
 constructor; auto.
 admit. (* Q levy opp *)
*
 *)

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
 
  
Lemma prod_ub_sup A A' ub B :
  ext_fun A B ->
  A==A' ->
  ub == sup A B ->
  (Π x ∈ A', B x) == (Π x ∈ A, ub ∩ B x).
intros; symmetry; apply cc_prod_ext;[trivial|].
red; intros.
rewrite H1.
apply eq_set_ax; intros z.
rewrite inter2_def.
rewrite sup_ax; trivial.
rewrite <- (H x x'); trivial.
split;[destruct 1;trivial|split;trivial].   
exists x; trivial.
Qed.


Lemma levy_in_eq v k n A :
levy_set v k n A ->
(forall x, (*levy_set v k n A ->*) levy (push_var x v) k n (forall z, z ∈ A -> z ∈ x)) ->
levy_set v k n A /\ levy_set_eq v k n A.
split; trivial.
intros z.
apply levy_eq_set; unfold incl_set;[|auto].
constructor; [simpl; auto|].
intros; apply levy_thin2; trivial.
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
*apply F_ext with
   (exists x, x==int M i /\
    exists y, y==int N i /\ z ∈ cc_app x y).
 +split; intros.
   destruct H2 as (x&?&y&?&?).
   rewrite H2,H3 in H4; trivial.
   exists (int M i); split;[reflexivity|].   
   exists (int N i); split;[reflexivity|].   
   trivial.
 +apply ex_eq_delta.
   intros ?? h; apply ex_morph; intro; rewrite h; reflexivity.
   apply H; simpl; auto.  
  intros ??; apply ex_eq_delta.
   intros ?? h; rewrite h; reflexivity.
   apply H0; simpl; auto.  
  intros.
  apply levy_str with z; simpl; auto.
  apply levy_cc_app; simpl; auto.
  constructor; simpl; auto.
*apply F_ext with
   (exists x, x==int M i /\
    exists y, y==int N i /\ z == cc_app x y).
 +split; intros.
   destruct H2 as (x&?&y&?&?).
   rewrite H2,H3 in H4; trivial.
   exists (int M i); split;[reflexivity|].   
   exists (int N i); split;[reflexivity|].   
   trivial.
 +apply ex_eq_delta.
   intros ?? h; apply ex_morph; intro; rewrite h; reflexivity.
   apply H; simpl; auto.  
  intros ??; apply ex_eq_delta.
   intros ?? h; rewrite h; reflexivity.
   apply H0; simpl; auto.  
  intros.
  apply levy_str with z; simpl; auto.
  apply levy_cc_app_eq; simpl; auto.
  constructor; simpl; auto.
Qed.
  
Lemma d2_abs M N k :
  levy_int M k ->
  levy_int N (S k) ->
  levy_int (Abs M N) k.
red; intros; apply levy_in_eq; simpl; intros z.
*rewrite cc_lam_def.
 2:intros ??? h; rewrite h; reflexivity.
 rewrite ex_ex2.
 apply ex_in_delta.  
 +intros ?? h; apply ex2_morph; intro; rewrite h; reflexivity.
 +apply H; simpl; auto.
 +intros.
  rewrite ex_ex2.
  apply ex_in_delta.  
  ++intros ?? h; rewrite h; reflexivity.
  ++apply H0.
    destruct k1; simpl; auto with arith.
  ++intros.
    apply levy_str with z; simpl; auto 10.
    apply levy_couple_eq; constructor; simpl; auto.
*(*intros _.*)
 rewrite fa_cc_lam_iff.
 2:intros ?? h; rewrite h; reflexivity.
 2:intros ??? h; rewrite h; reflexivity.
 apply fa_in_delta.
 +intros ?? h; apply fa_morph; intro; rewrite h; reflexivity.
 +apply H; simpl; auto.
 +intros.
  apply fa_in_delta.
  ++intros ?? h; rewrite h; reflexivity.
  ++apply H0.
    destruct k1; simpl; auto with arith.
  ++intros.
    rewrite in_set_def.
    constructor; [simpl;auto|intros].
    apply levy_str with x1; simpl; auto 10.
    apply levy_couple_eq; constructor; simpl; auto.
Qed.

Lemma d2_prod M N k :
  levy_int M k ->
  levy_int N (S k) ->
  levy_int (Prod M N) k.
red; intros; apply levy_in_eq; simpl; intros z.
*rewrite cc_prod_def.
 2:intros ??? h; rewrite h; reflexivity.
 constructor.
 +constructor;[simpl;auto|].
  intros; apply ex_in_delta.
  ++intros ?? h; apply ex_morph; intro; apply and_iff_morphism;[rewrite h; reflexivity|].
    apply ex_morph; intro; rewrite h; reflexivity.
  ++apply H; simpl; auto.
  ++intros; revert k0; apply ex_in_delta.
    +++intros ?? h; apply ex_morph; intro; rewrite h; reflexivity.
    +++apply H0.
       destruct k0; simpl; auto with arith.
    +++intros.
       constructor;[simpl;auto|].
       intros.
       apply levy_str with x; simpl; auto 10.
       apply levy_couple_eq; constructor; simpl; auto 10.
 +apply fa_in_delta.
  ++intros ?? h; apply ex_morph; intro; apply and_iff_morphism;[rewrite h; reflexivity|].
    apply and_iff_morphism; apply fa_morph; intro;[rewrite h; reflexivity|].
    apply impl_morph;[reflexivity|intros].
    apply impl_morph;[rewrite h;reflexivity|intros].
    apply ex_morph; intro; rewrite h; reflexivity.
  ++apply H; simpl; auto.
  ++intros; revert k0; apply ex_in_delta.
    +++intros ?? h; apply and_iff_morphism; apply fa_morph; intro;[rewrite h; reflexivity|].
       apply impl_morph;[reflexivity|intros].
       apply impl_morph;[reflexivity|intros].
       apply ex_morph; intro; rewrite h; reflexivity.
    +++apply H0.
       destruct k0; simpl; auto with arith.
    +++intros.
       constructor.
        constructor;[simpl;auto|].
        intros; rewrite in_set_def.
        constructor;[simpl;auto|].
        apply levy_couple_eq; constructor; simpl; auto 10.

        constructor;[simpl;auto|].
        constructor.
         apply levy_str with x; simpl; auto 10.
         apply levy_fst_eq; simpl; auto 10.

         constructor;[simpl;auto 10|].
         intros; apply levy_str with x1; simpl; auto 10.
         apply levy_couple_eq; constructor; simpl; auto 10.
*apply F_ext with
   (exists m, m == int M i /\
    exists nf, nf == cc_lam m (fun x => int N (V.cons x i)) /\
    forall f, f ∈ cc_prod m (cc_app nf) -> f ∈ z).
 {split; intros.
  *destruct H2 as (m&eqm&nf&eqnf&?).
   apply H2.
   revert H3; apply eq_elim.   
   symmetry; apply cc_prod_ext;[trivial|].
   intros ??? h.
   rewrite eqnf, cc_beta_eq; auto with *.
    rewrite h; reflexivity.
    intros ??? h'; rewrite h'; reflexivity.
  *exists (int M i); split;[reflexivity|].    
   eexists;split;[reflexivity|].
   intros; apply H2.
   revert H3; apply eq_elim.
   apply cc_prod_ext;[reflexivity|].   
   intros ??? h.
   rewrite cc_beta_eq; auto with *.
    rewrite h; reflexivity.
    intros ??? h'; rewrite h'; reflexivity. }
 apply ex_eq_delta.
 +intros ?? h; apply ex_morph; intro.
  apply and_iff_morphism.
   apply eq_set_morph; [reflexivity|]. 
   apply cc_lam_ext;[trivial|].
   intros ??? h'; rewrite h'; reflexivity.

   apply fa_morph; intro f.
   rewrite h; reflexivity.
 +apply H; simpl; auto.
 +intros; revert k0; apply ex_eq_delta.
  ++intros ?? h; apply fa_morph; intro; rewrite h; reflexivity.
  ++intro.
    apply levy_eq_set; unfold incl_set.
    {constructor; [simpl;auto|].
     apply levy_cc_lam_delta; simpl; auto.
      intros ??? h; rewrite h; reflexivity.
     intros; apply H0.
     destruct k0; simpl; auto 10 with arith. }
    {rewrite fa_cc_lam_iff.
     *constructor; [simpl;auto|].
      intros; apply fa_in_delta.
      +intros ?? h; rewrite h; reflexivity.
      +apply H0.
       destruct k0; simpl;auto 10 with arith.
      +intros; rewrite in_set_def.
       constructor; [simpl;auto 10|].
       apply levy_couple_eq; constructor; simpl; auto 10.
     *intros ?? h; rewrite h; reflexivity.
     *intros ??? h; rewrite h; reflexivity. }
  ++intros; apply levy_lift with Prd. 
    apply F_fa_prd.
    constructor;[|constructor; simpl;auto]. 
    apply levy_cc_prod_app; simpl; auto.
Qed.

(*
  Lemma d2_arr_ub M N k :
  d2_int M k ->
  d2_int N k ->
  d2_int (Prod M (lift 1 N)) k.
split; simpl; intros z.
*apply F_ext with
   (exists x, x==int M i /\
    exists y, y==int N i /\
    z ∈ cc_arr x y).
 +split; intros.
   destruct H2 as (x&?&y&?&?).
   revert H4; apply eq_elim.
   apply cc_prod_ext;[trivial|].
   intros ??? h.
   rewrite simpl_int_lift1; trivial.

   exists (int M i); split;[reflexivity|].   
   exists (int N i); split;[reflexivity|].   
   revert H2; apply eq_incl.
   apply cc_prod_ext;[reflexivity|].
   intros ??? h.
   rewrite simpl_int_lift1; reflexivity.

 +apply ex_eq_delta.
   intros ?? h.
   apply ex_morph; intro.
   rewrite h; reflexivity.

   apply H; simpl; auto.  
  intros.
  apply ex_eq_delta.
   intros ?? h.
   rewrite h; reflexivity.
   apply H0; simpl; auto.  
  intros.
  apply levy_str with z; simpl; auto.
  apply levy_cc_arr_ub; simpl; auto.
*apply F_ext with
   (exists x, x==int M i /\
    exists y, y==int N i /\
    z == cc_arr x y).
 +split; intros.
   destruct H2 as (x&?&y&?&?).
   rewrite H4.
   apply cc_prod_ext;[trivial|].
   intros ??? h.
   rewrite simpl_int_lift1; trivial.

   exists (int M i); split;[reflexivity|].   
   exists (int N i); split;[reflexivity|].   
   rewrite H2.
   apply cc_prod_ext;[reflexivity|].
   intros ??? h.
   rewrite simpl_int_lift1; reflexivity.

 +apply ex_eq_delta.
   intros ?? h.
   apply ex_morph; intro.
   rewrite h; reflexivity.

   apply H; simpl; auto.  
  intros.
  apply ex_eq_delta.
   intros ?? h.
   rewrite h; reflexivity.
   apply H0; simpl; auto.  
  intros.
  apply levy_str with z; simpl; auto.
  apply levy_lift with Prd.
  apply levy_cc_arr_eq_ub; simpl; auto.
Qed.
*)

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
*apply F_ext with
   (exists x, x==int M i /\
    exists y, y==int N i /\ z ∈ cc_app x y).
 +split; intros.
   destruct H2 as (x&?&y&?&?).
   rewrite H2,H3 in H4; trivial.
   exists (int M i); split;[reflexivity|].   
   exists (int N i); split;[reflexivity|].   
   trivial.
 +apply ex_eq_delta.
   intros ?? h; apply ex_morph; intro; rewrite h; reflexivity.
   apply H; simpl; auto.  
  intros ??; apply ex_eq_delta.
   intros ?? h; rewrite h; reflexivity.
   apply H0; simpl; auto.  
  intros.
  apply levy_str with z; simpl; auto.
  apply levy_cc_app; simpl; auto.
  constructor; simpl; auto.
*apply F_ext with
   (exists x, x==int M i /\
    exists y, y==int N i /\ z == cc_app x y).
 +split; intros.
   destruct H2 as (x&?&y&?&?).
   rewrite H2,H3 in H4; trivial.
   exists (int M i); split;[reflexivity|].   
   exists (int N i); split;[reflexivity|].   
   trivial.
 +apply ex_eq_delta.
   intros ?? h; apply ex_morph; intro; rewrite h; reflexivity.
   apply H; simpl; auto.  
  intros ??; apply ex_eq_delta.
   intros ?? h; rewrite h; reflexivity.
   apply H0; simpl; auto.  
  intros.
  apply levy_str with z; simpl; auto.
  apply levy_cc_app_eq; simpl; auto.
  constructor; simpl; auto.
Qed.
  
Lemma d2_abs M N k :
  d2_int M k ->
  d2_int N (S k) ->
  d2_int (Abs M N) k.
red; intros; apply levy_in_eq; simpl; intros z.
*rewrite cc_lam_def.
 2:intros ??? h; rewrite h; reflexivity.
 rewrite ex_ex2.
 apply ex_in_delta.  
 +intros ?? h; apply ex2_morph; intro; rewrite h; reflexivity.
 +apply H; simpl; auto.
 +intros.
  rewrite ex_ex2.
  apply ex_in_delta.  
  ++intros ?? h; rewrite h; reflexivity.
  ++apply H0.
    destruct k2; simpl; auto with arith.
  ++intros.
    apply levy_str with z; simpl; auto 10.
    apply levy_couple_eq; constructor; simpl; auto.
*(*intros _.*)
 rewrite fa_cc_lam_iff.
 2:intros ?? h; rewrite h; reflexivity.
 2:intros ??? h; rewrite h; reflexivity.
 apply fa_in_delta.
 +intros ?? h; apply fa_morph; intro; rewrite h; reflexivity.
 +apply H; simpl; auto.
 +intros.
  apply fa_in_delta.
  ++intros ?? h; rewrite h; reflexivity.
  ++apply H0.
    destruct k2; simpl; auto with arith.
  ++intros.
    rewrite in_set_def.
    constructor; [simpl;auto|intros].
    apply levy_str with x1; simpl; auto 10.
    apply levy_couple_eq; constructor; simpl; auto.
Qed.



Lemma d2_prod M N k :
  d2_int M k ->
  d2_int N (S k) ->
  d2_int (Prod M N) k.
red; intros; apply levy_in_eq; simpl; intros z.
*rewrite cc_prod_def.
 2:intros ??? h; rewrite h; reflexivity.
 constructor.
 +constructor;[simpl;auto|].
  intros; revert k0; apply ex_in_delta.
  ++intros ?? h; apply ex_morph; intro; apply and_iff_morphism;[rewrite h; reflexivity|].
    apply ex_morph; intro; rewrite h; reflexivity.
  ++apply H; simpl; auto.
  ++intros; revert k0; apply ex_in_delta.
    +++intros ?? h; apply ex_morph; intro; rewrite h; reflexivity.
    +++apply H0.
       destruct k0; simpl; auto with arith.
    +++intros.
       constructor;[simpl;auto|].
       intros.
       apply levy_str with x; simpl; auto 10.
       apply levy_couple_eq; constructor; simpl; auto 10.
 +revert k0; apply fa_in_delta.
  ++intros ?? h; apply ex_morph; intro; apply and_iff_morphism;[rewrite h; reflexivity|].
    apply and_iff_morphism; apply fa_morph; intro;[rewrite h; reflexivity|].
    apply impl_morph;[reflexivity|intros].
    apply impl_morph;[rewrite h;reflexivity|intros].
    apply ex_morph; intro; rewrite h; reflexivity.
  ++apply H; simpl; auto.
  ++intros; revert k0; apply ex_in_delta.
    +++intros ?? h; apply and_iff_morphism; apply fa_morph; intro;[rewrite h; reflexivity|].
       apply impl_morph;[reflexivity|intros].
       apply impl_morph;[reflexivity|intros].
       apply ex_morph; intro; rewrite h; reflexivity.
    +++apply H0.
       destruct k0; simpl; auto with arith.
    +++intros.
       constructor.
        constructor;[simpl;auto|].
        intros; rewrite in_set_def.
        constructor;[simpl;auto|].
        apply levy_couple_eq; constructor; simpl; auto 10.

        constructor;[simpl;auto|].
        constructor.
         apply levy_str with x; simpl; auto 10.
         apply levy_fst_eq; simpl; auto 10.

         constructor;[simpl;auto 10|].
         intros; apply levy_str with x1; simpl; auto 10.
         apply levy_couple_eq; constructor; simpl; auto 10.
*apply F_ext with
   (exists m, m == int M i /\
    exists nf, nf == cc_lam m (fun x => int N (V.cons x i)) /\
    forall f, f ∈ cc_prod m (cc_app nf) -> f ∈ z).
 {split; intros.
  *destruct H2 as (m&eqm&nf&eqnf&?).
   apply H2.
   revert H3; apply eq_elim.   
   symmetry; apply cc_prod_ext;[trivial|].
   intros ??? h.
   rewrite eqnf, cc_beta_eq; auto with *.
    rewrite h; reflexivity.
    intros ??? h'; rewrite h'; reflexivity.
  *exists (int M i); split;[reflexivity|].    
   eexists;split;[reflexivity|].
   intros; apply H2.
   revert H3; apply eq_elim.
   apply cc_prod_ext;[reflexivity|].   
   intros ??? h.
   rewrite cc_beta_eq; auto with *.
    rewrite h; reflexivity.
    intros ??? h'; rewrite h'; reflexivity. }
 revert k0; apply ex_eq_delta.
 +intros ?? h; apply ex_morph; intro.
  apply and_iff_morphism.
   apply eq_set_morph; [reflexivity|]. 
   apply cc_lam_ext;[trivial|].
   intros ??? h'; rewrite h'; reflexivity.

   apply fa_morph; intro f.
   rewrite h; reflexivity.
 +apply H; simpl; auto.
 +intros; revert k0; apply ex_eq_delta.
  ++intros ?? h; apply fa_morph; intro; rewrite h; reflexivity.
  ++intro.
    apply levy_eq_set; unfold incl_set.
    {constructor; [simpl;auto|].
     apply levy_cc_lam_delta; simpl; auto.
      intros ??? h; rewrite h; reflexivity.
     intros; apply H0.
     destruct k0; simpl; auto 10 with arith. }
    {rewrite fa_cc_lam_iff.
     *constructor; [simpl;auto|].
      intros; apply fa_in_delta.
      +intros ?? h; rewrite h; reflexivity.
      +apply H0.
       destruct k0; simpl;auto 10 with arith.
      +intros; rewrite in_set_def.
       constructor; [simpl;auto 10|].
       apply levy_couple_eq; constructor; simpl; auto 10.
     *intros ?? h; rewrite h; reflexivity.
     *intros ??? h; rewrite h; reflexivity. }
  ++intros; apply levy_lift with Prd. 
    apply F_fa_prd.
    constructor;[|constructor; simpl;auto]. 
    apply levy_cc_prod_app; simpl; auto.
Qed.

  Lemma d2_arr_ub M N k :
  d2_int M k ->
  d2_int N k ->
  d2_int (Prod M (lift 1 N)) k.
split; simpl; intros z.
*apply F_ext with
   (exists x, x==int M i /\
    exists y, y==int N i /\
    z ∈ cc_arr x y).
 +split; intros.
   destruct H2 as (x&?&y&?&?).
   revert H4; apply eq_elim.
   apply cc_prod_ext;[trivial|].
   intros ??? h.
   rewrite simpl_int_lift1; trivial.

   exists (int M i); split;[reflexivity|].   
   exists (int N i); split;[reflexivity|].   
   revert H2; apply eq_incl.
   apply cc_prod_ext;[reflexivity|].
   intros ??? h.
   rewrite simpl_int_lift1; reflexivity.

 +apply ex_eq_delta.
   intros ?? h.
   apply ex_morph; intro.
   rewrite h; reflexivity.

   apply H; simpl; auto.  
  intros.
  apply ex_eq_delta.
   intros ?? h.
   rewrite h; reflexivity.
   apply H0; simpl; auto.  
  intros.
  apply levy_str with z; simpl; auto.
  apply levy_cc_arr_ub; simpl; auto.
*apply F_ext with
   (exists x, x==int M i /\
    exists y, y==int N i /\
    z == cc_arr x y).
 +split; intros.
   destruct H2 as (x&?&y&?&?).
   rewrite H4.
   apply cc_prod_ext;[trivial|].
   intros ??? h.
   rewrite simpl_int_lift1; trivial.

   exists (int M i); split;[reflexivity|].   
   exists (int N i); split;[reflexivity|].   
   rewrite H2.
   apply cc_prod_ext;[reflexivity|].
   intros ??? h.
   rewrite simpl_int_lift1; reflexivity.

 +apply ex_eq_delta.
   intros ?? h.
   apply ex_morph; intro.
   rewrite h; reflexivity.

   apply H; simpl; auto.  
  intros.
  apply ex_eq_delta.
   intros ?? h.
   rewrite h; reflexivity.
   apply H0; simpl; auto.  
  intros.
  apply levy_str with z; simpl; auto.
  apply levy_lift with Prd.
  apply levy_cc_arr_eq_ub; simpl; auto.
Qed.

End Delta2.

Import Sigma2.

(**********************************************************)

Require Import ZFnats.

Definition N_inductive a :=
  empty ∈ a /\ forall x, x ∈ a -> succ x ∈ a.

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

Lemma eq_N_iff x :
  x == N <-> x ⊆ N /\ N_inductive x.
rewrite eq_set_ax.  
split; intros.
*split.
 +red; intros; apply H; trivial. 
 +split; intros; [apply H;apply zero_typ|].
  apply H; apply succ_typ; apply H; trivial.
  *destruct H as (?&?&?).
   split;[apply H|].
   intros h; elim h using N_ind; intros; auto.
   rewrite <-H3; trivial.
Qed.

    
(* If we only have well foundation of transitive sets...

Definition N_elts_aux z :=
  (forall a, a∈z -> forall b, b∈a -> b∈z) /\
  (forall y, y∈z -> (forall a, a∈y -> forall b, b∈a -> b ∈y) /\
                     (y==empty \/ exists y', y' ∈ y /\ y==succ y')).
Definition N_elts z :=
  (z==empty \/ exists y, y ∈ z /\ z==succ y) /\ N_elts_aux z.

(*
Axiom reg :
  forall x, (exists y, y ∈ x) -> exists y, y ∈ x /\ forall z, z ∈ x -> ~ z ∈ y.
Axiom nnpp:forall P:Prop,~~P->P.
Lemma reg_acc x :
  (forall y z, y ∈ x -> z ∈ y -> z ∈ x) ->
  Acc in_set x.
intros xtr.
constructor; intros.
apply nnpp; intro nacc.
destruct reg with (subset x (fun y => ~Acc in_set y)) as (y'&?&?).
*exists y; apply subset_intro; trivial.
*apply subset_ax in H0; destruct H0 as (?,(w,?,?)).
 apply H3; constructor; intros.
 rewrite <-H2 in H4.
 apply nnpp; intros nacc'.
 apply (H1 y0); [|trivial].
 apply subset_intro; [eauto|trivial].
Qed.*)

Lemma N_def z : z ∈ N <-> N_elts z.
split; intros.
*unfold N_elts, N_elts_aux.
 split;[destruct N_case with (1:=H) as [?|(k&?&_&?)]; eauto|split; intros].
 +apply lt_trans with a; trivial.
 +split; intros.
  ++apply lt_trans with a; trivial.
    clear a H1 b H2.
    revert y H0; elim H using N_ind; intros.
     rewrite <-H1 in H3; auto.
     apply empty_ax in H0; contradiction.
     apply le_case in H2; destruct H2;[rewrite H2; trivial|auto].
  ++destruct N_case with y as [?|(k&?&_&?)]; eauto.
    revert y H0; elim H using N_ind; intros.
     rewrite <-H1 in H3; auto.
     apply empty_ax in H0; contradiction.
     apply le_case in H2; destruct H2;[rewrite H2; trivial|auto].
*destruct H as (zcase&_(*ztr*)&hered).
 revert zcase hered.
 clear.
 elim z using wf_ax; intros.
 destruct zcase as [eqx|(k&klt&eqx)]; rewrite eqx; [apply zero_typ|apply succ_typ].
 apply H; auto.
  apply hered; auto.

  intros; apply hered.
  rewrite eqx.
  apply union2_intro1; trivial.
Qed.
*)
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

Lemma levy_N v k n:
  levy_set v k n N.
intros z.
rewrite N_def.
constructor(*;[|constructor]*).
*constructor;[apply levy_empty_eq|constructor;[simpl;auto|]].
 intros; apply levy_succ_eq; simpl; auto.
*constructor; [simpl;auto|].
 constructor;[apply levy_empty_eq|].
 constructor; [simpl;auto|].
 intros; apply levy_succ_eq; simpl; auto.
(**constructor;[simpl;auto|].
 constructor;[simpl;auto|].
 constructor;simpl;auto.
*constructor; [simpl;auto|].
 constructor.
 +constructor; [simpl;auto|].
  constructor; [simpl;auto|].
  constructor;simpl;auto.   
 +constructor;[apply levy_empty_eq|].
  constructor; [simpl;auto|].
  intros; apply levy_succ_eq; simpl; auto. *)
Qed.

Lemma levy_N_eq v k n:
  levy_set_eq v k n N.
red; intros.
rewrite eq_N_iff.
constructor;[|constructor].
*constructor; [simpl; auto|].
 intros; apply levy_N.
*rewrite in_set_def; constructor;[simpl;auto|].
 intros; apply levy_empty_eq.
*constructor;[simpl;auto|].
 intros; rewrite in_set_def.
 constructor; [simpl;auto|].  
 intros; apply levy_succ_eq; simpl; auto.
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
  



 (* definable sets *)

  Definition cls := set -> Prop.

  Definition eq_cls (c1 c2 : cls) := (eq_set ==> iff)%signature c1 c2.

  Definition cls_set (a:set) (c : cls) :=
    forall z, z ∈ a <-> c z.

  Definition is_set (c:cls) := exists a, cls_set a c.

  Definition levy_cls vars k n (c:cls) := forall z, levy (z::vars) k n (c z).

  
  Definition empty_cls : cls := fun z => False.
  Definition pair_cls (a b:set) : cls := fun z => z==a \/ z==b.
  Definition union_cls (a:set) : cls := fun z => exists b, b∈a /\ z∈b.
  Definition power_cls (a:set) : cls := fun z => forall b, b ∈ z -> b ∈ a.
  Definition subset_cls (a:set) (P:set->Prop) : cls :=
    fun z => z∈a /\ exists2 z', z==z' & P z'.
  Definition repl_cls (a:set) (f:set->cls) : cls :=
    fun z => exists x, x∈a /\ cls_set z (f x).

  Definition succ_cls (x:set) : cls :=
    fun p => p==x \/ (x ∈ p /\ forall z, z∈p -> z==x).
  Definition is_succ (x x':set) : Prop :=
    x ∈ x' /\ exists p, p ∈ x' /\ x ∈ p /\ forall z, z ∈ p -> z==z.
  Definition inductive : cls :=
    fun I => empty ∈ I /\ forall x, x ∈ I -> exists x', x' ∈ I /\ is_succ x x'.  
  Definition infty_cls : cls :=
    fun z => forall I, inductive I -> z ∈ I.

  Lemma empty_cls_set : cls_set empty empty_cls.
split; intros; [|contradiction].
apply empty_ax in H; trivial.
Qed.
  Lemma pair_cls_set a b : cls_set (pair a b) (pair_cls a b).
red; unfold pair_cls.
apply pair_ax.
Qed.
  Lemma union_cls_set a : cls_set (union a) (union_cls a).
red; unfold union_cls; intros.
rewrite union_ax.
split; destruct 1; eauto.
destruct H; eauto.
Qed.
  Lemma power_cls_set a : cls_set (power a) (power_cls a).
red; unfold power_cls; intros.
apply power_ax.
Qed.
  Lemma subset_cls_set a P : cls_set (subset a P) (subset_cls a P).
red; unfold subset_cls; intros.
apply subset_ax.
Qed.
  Lemma succ_cls_def x :
    exists xx,
      cls_set xx (pair_cls x x) /\
        eq_cls (succ_cls x) (pair_cls x xx).
exists (pair x x).
split.
apply pair_cls_set.
do 2 red; unfold succ_cls.
split; intros.
*destruct H0;[left;rewrite <-H;trivial|right].
 destruct H0.
 rewrite H in H0. 
 apply pair_ext; trivial.
 left; apply H1. 
 rewrite H; trivial.
*destruct H0; [left; rewrite H; trivial|right].
 split; intros.
  rewrite H,H0; auto.
  rewrite H,H0 in H1.
  apply pair_ax in H1; destruct H1; trivial.
Qed.


  Require Import ZFpairs.
  
  
(* We assume a fully existential IZF *)
Declare Module M : Zermelo_Ex_sig CoqSublogicThms.

Import CoqSublogicThms M.

Instance eq_set_equiv: Equivalence eq_set.
Proof.
split; red; intros; rewrite eq_set_ax in *; intros.
 reflexivity.
 symmetry; trivial.
 transitivity (x0 ∈ y); trivial.
Qed.

Lemma eq_set_morph : Proper (eq_set ==> eq_set ==> iff) eq_set.
auto with *.
Qed.

Instance in_set_morph : Proper (eq_set ==> eq_set ==> iff) in_set.
apply morph_impl_iff2; auto with *.
do 4 red; intros.
apply in_reg with x; trivial.
rewrite eq_set_ax in H0.
apply H0; trivial.
Qed.


Inductive form : Prop -> qu -> nat -> Prop :=
| F_eq x y k n : form (x == y) k n
| F_in x y k n : form (x ∈ y) k n
| F_T k n : form True k n
| F_F k n : form False k n
| F_and A B k n : form A k n -> form B k n -> form (A/\B) k n
| F_or A B k n : form A k n -> form B k n -> form (A\/B) k n
| F_imp A B k n : form A (opp k) n -> form B k n -> form (A->B) k n
| F_bfa A B k n : (forall x, form (B x) k n) -> form (forall x:set, x ∈ A -> B x) k n
| F_fa_prd B n : (forall x, form (B x) Prd (S n)) -> form (forall x:set, B x) Prd (S n)
| F_fa_alt B n : (forall x, form (B x) Sig n) -> form (forall x:set, B x) Prd (S n)
| F_bex A B k n : (forall x, form (B x) k n) -> form (exists x:set, x ∈ A /\ B x) k n
| F_ex_sig B n : (forall x, form (B x) Sig (S n)) -> form (exists x:set, B x) Sig (S n)
| F_ex_alt B n : (forall x, form (B x) Prd n) -> form (exists x:set, B x) Sig (S n)
| F_ext A B k n : (A<->B) -> form A k n -> form B k n.

Instance form_morph : Proper (iff ==> eq ==> eq ==> iff) form.
do 4 red; intros.
subst y0 y1.
split; apply F_ext; auto with *.
Qed.
Lemma ex_ex2 A P Q : @ex2 A P Q <-> exists x:A, P x /\ Q x.
split; destruct 1; [eauto|].
destruct H; eauto.
Qed.

Lemma F_bex2 A B k n : (forall x, form (B x) k n) -> form (exists2 x:set, x ∈ A & B x) k n.
intros.
rewrite ex_ex2.
constructor; trivial.
Qed.



(*
Parameter
 (repl_ex : forall a (R:set->set->Prop),
    (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x ∈ a -> R x y -> R x y' -> y == y') ->
    #exists b, forall x, x ∈ b <-> #exists2 y, y ∈ a & R y x).
*)

Definition is_set_def (P:set->Prop) :=
  exists2 x, P x & forall y, P y -> x==y.

Lemma is_set_def_ex_fa P Q :
  Proper (eq_set==>iff) Q ->
  is_set_def P -> ((forall x, P x -> Q x) <-> (exists2 x, P x & Q x)).
intros Qm (a,da,ua).
split; intros; [eauto|].
destruct H as (a',da',qa').
rewrite <- ua with (1:=H0).
rewrite ua with (1:=da'); trivial.
Qed.

Lemma is_set_def_ext P Q :
  pointwise_relation _ iff P Q ->
  is_set_def P <-> is_set_def Q.
intros Peq; unfold is_set_def.
apply ex2_morph; intros x; [trivial|].
apply fa_morph; intros y.
apply impl_morph; [trivial|].
intros _.
reflexivity.
Qed.

Definition is_pair (isa isb : set -> Prop) c :=
  exists2 a, isa a & exists2 b, isb b & a ∈ c /\ b ∈ c /\ forall z, z∈c -> (z==a \/ z==b).

Lemma is_set_pair isa isb :
  is_set_def isa -> is_set_def isb -> is_set_def (is_pair isa isb).
intros (a, da, ua) (b,db,ub).
destruct pair_ex with a b as (c,dc).
exists c.
*unfold is_pair.
 exists a;[trivial|].
 exists b;[trivial|].
 split;[apply dc;left;reflexivity|].
 split;[apply dc;right;reflexivity|].
 intros.
 apply dc; trivial.
*intros.
 red in H.
 destruct H as (a',da',(b',db',(?&?&?))).
 apply eq_set_ax.
 intros z.
 rewrite dc.
 rewrite (ua _ da').
 rewrite (ub _ db').
 split;[|auto].
 destruct 1 as [h|h]; rewrite h; trivial.
Qed.

Lemma pair_form P Q n:
  (forall a, form (P a) Sig n) ->
  (forall a, form (Q a) Sig n) ->
  forall a, form (is_pair P Q a) Sig n.
intros.
unfold is_pair.
rewrite ex_ex2.
constructor; intros x.
constructor;[trivial|].
rewrite ex_ex2.
constructor; intros y.
constructor;[trivial|].
repeat constructor.
Qed.


Definition is_empty x := forall z, z ∈ x -> False.

Lemma is_set_empty : is_set_def is_empty.
destruct empty_ex as (a,?); exists a; trivial.
intros.
apply eq_set_ax; split; intros.
apply H in H1; contradiction.
apply H0 in H1; contradiction.
Qed.

Lemma empty_form k n:
  forall a, form (is_empty a) k n.
intros.
constructor.
intros; constructor.
Qed.

Definition is_union isa c :=
  exists2 a, isa a & forall z, z ∈ c <-> (exists2 y, z ∈ y & y ∈ a).

Lemma is_set_union isa :
  is_set_def isa -> is_set_def (is_union isa).
intros (a, da, ua).
destruct union_ex with a as (c,dc).
exists c.
*unfold is_union.
 exists a;trivial.
*intros.
 red in H.
 destruct H as (a',da',def).
 apply eq_set_ax.
 intros z.
 rewrite dc, def.
 apply ex2_morph; intros b;[reflexivity|].
 rewrite (ua _ da'); reflexivity.
Qed.

Lemma union_form P n:
  (forall a, form (P a) Sig n) ->
  forall a, form (is_union P a) Sig n.
intros.
unfold is_union.
rewrite ex_ex2.
constructor; intros x.
constructor;[trivial|].
apply F_ext with ((forall z, z ∈ a -> exists y, y ∈ x /\ z ∈ y) /\ (forall y, y ∈ x -> forall z, z ∈ y -> z ∈ a)).
*split; intros.
 destruct H0.
 split; intros.
  destruct (H0 _ H2) as (?,(?,?)); eauto.   
  destruct H2; eauto.
 split; intros.
 rewrite H0 in H1.
 destruct H1;eauto.
 rewrite H0.
 eauto.
*constructor.
 constructor; intros z.
 constructor; intros y.
 constructor.
 repeat constructor.
Qed.



Definition is_power isa c :=
  exists2 a, isa a &
               forall z, z ∈ c <-> (forall y, y ∈ z -> y ∈ a)) ]
  
Inductive replf_form : ((nat->set)->set)->Prop :=
|


Definition t_pair : Prop
