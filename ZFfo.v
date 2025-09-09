Require Import ZF.

Definition icons {A} (x : A) (f : nat -> A) (k : nat) :=
  match k with
  | 0 => x
  | S k0 => f k0
  end.

Lemma in_set_def a x :
    a ∈ x <-> exists y, y ∈ x /\ y==a.
split; [exists a; split; auto with *|destruct 1 as (y,(?,?))].
rewrite <- H0; trivial.
Qed.

Definition lft (f:nat->nat) :=
  fun k => match k with 0=>0|S k'=>S (f k')end.

Definition fvs := nat->set.

Definition fvar (f : fvs->set) : Prop :=
  exists k, f = (fun vs => vs k).

Lemma fvi k : fvar (fun fv => fv k).
  exists k; reflexivity.
Qed.

(*Lemma fo_form_ex P :
  fo_form P ->
  exists A, A ∈ Form /\ forall vs l, (forall k, Fint_var l (nat2set k) == vs k) ->
                                     P (fun _=>True) vs <-> Fint l A.
induction 1.
*destruct IHfo_form as (Q & Qty & Qdef); exists Q;split;[trivial|intros].
 rewrite <-H; auto.
*destruct H as (k,?). 
 destruct H0 as (k',?). 
 subst  x y.
 exists (Feq (nat2set k) (nat2set k')); split.
  apply Feq_typ; apply nat2set_typ. 
 intros. 
 rewrite Fint_eq;[|apply nat2set_typ|apply nat2set_typ].
 rewrite !H; reflexivity.
*destruct H as (k,?). 
 destruct H0 as (k',?). 
 subst  x y.
 exists (Fin (nat2set k) (nat2set k')); split.
  apply Fin_typ; apply nat2set_typ. 
 intros. 
 rewrite Fint_in;[|apply nat2set_typ|apply nat2set_typ].
 rewrite !H; reflexivity.
*exists (Fimp Fbot Fbot); split;[apply Fimp_typ; apply Fbot_typ|]. 
 intros.  
 rewrite Fint_imp;[|apply Fbot_typ|apply Fbot_typ].
 split; intros; trivial.
*exists Fbot; split; [apply Fbot_typ|intros].
 split; intros; [contradiction|].
 apply Fint_bot in H0; trivial.
*destruct IHfo_form1 as (A'&?&?).
 destruct IHfo_form2 as (B'&?&?).
 exists (Fand A' B'); split; [apply Fand_typ; trivial|intros].
 rewrite Fint_and; trivial.
 apply and_iff_morphism; auto.
*destruct IHfo_form1 as (A'&?&?).
 destruct IHfo_form2 as (B'&?&?).
 exists (For A' B'); split; [apply For_typ; trivial|intros].
 rewrite Fint_or; trivial.
 apply or_iff_morphism; auto.
*destruct IHfo_form1 as (A'&?&?).
 destruct IHfo_form2 as (B'&?&?).
 exists (Fimp A' B'); split; [apply Fimp_typ; trivial|intros].
 rewrite Fint_imp; trivial.
 apply impl_morph; auto.
*destruct IHfo_form as (B'&?&?).
 exists (Ffa B'); split; [apply Ffa_typ; trivial|intros].
 rewrite Fint_fa; trivial.
 apply fa_morph; intros x.
 rewrite <-H1 with (vs:=icons x vs).
 +unfold bind; simpl.
  split; auto.
 +destruct k; simpl.
  apply Fiv_0.
  rewrite Fiv_S; trivial.
*destruct IHfo_form as (B'&?&?).
 exists (Fex B'); split; [apply Fex_typ; trivial|intros].
 rewrite Fint_ex; trivial.
 apply ex_morph; intros x.
 rewrite <-H1 with (vs:=icons x vs).
 +unfold bind; simpl.
  split; [destruct 1|]; auto.
 +destruct k; simpl.
  apply Fiv_0.
  rewrite Fiv_S; trivial.
Qed.
*)
Definition bind {B} (A:set->fvs->B) : fvs -> B :=
  fun vs => A (vs 0) (fun k => vs (S k)).
Inductive fo_form : (fvs->Prop) -> Prop :=
| FO_ext A B : (forall vs, (A vs<->B vs)) -> fo_form A -> fo_form B
| FO_eq x y  : fvar x -> fvar y -> fo_form (fun vs => x vs == y vs)
| FO_in x y  : fvar x -> fvar y -> fo_form (fun vs => x vs ∈ y vs)
| FO_T       : fo_form (fun vs => True)
| FO_F       : fo_form (fun vs => False)
| FO_and A B : fo_form A -> fo_form B -> fo_form (fun vs => A vs/\B vs)
| FO_or A B  : fo_form A -> fo_form B -> fo_form (fun vs => A vs\/B vs)
| FO_imp A B : fo_form A -> fo_form B -> fo_form (fun vs => A vs->B vs)
| FO_fa B    : fo_form (bind B) ->
               fo_form (fun vs => forall x:set, B x vs)
| FO_ex B    : fo_form (bind B) ->
               fo_form (fun vs => exists x:set, B x vs).
  
Ltac atom :=
  constructor; eexists; reflexivity.


Ltac fo_trivial :=
  first[apply FO_eq; apply fvi
       |apply FO_in; apply fvi
       |apply FO_T
       |apply FO_F].

Instance fo_form_param (P : fvs -> Prop) :
  fo_form P ->
  Proper (pointwise_relation nat eq_set ==> iff) P.
do 2 red; induction 1; intros vs vs' evs; try reflexivity.
*do 2 rewrite <-H; auto.
*destruct H as (k,?); subst x.
 destruct H0 as (k',?); subst y.
 rewrite (evs k); rewrite (evs k'); reflexivity.
*destruct H as (k,?); subst x.
 destruct H0 as (k',?); subst y.
 rewrite (evs k); rewrite (evs k'); reflexivity.
*apply and_iff_morphism; auto.
*apply or_iff_morphism; auto.
*apply impl_morph; auto.
*apply fa_morph; intros x.
 apply (IHfo_form (icons x vs) (icons x vs')).
 red; destruct a; simpl; auto with *.
*apply ex_morph; intro x.
 apply (IHfo_form (icons x vs) (icons x vs')).
 red; destruct a; simpl; auto with *.
Qed.
  
  Lemma fo_form_ren P f :
    fo_form P -> fo_form (fun i => P (fun k => i (f k))).
intros foP; revert f; induction foP; try constructor; auto; intros.
*apply FO_ext with (fun i => A (fun k => i (f k))); auto.
*destruct H as (k,?); subst x; exists (f k); trivial.
*destruct H0 as (k,?); subst y; exists (f k); trivial.
*destruct H as (k,?); subst x; exists (f k); trivial.
*destruct H0 as (k,?); subst y; exists (f k); trivial.
*apply (IHfoP (lft f)).
*apply (IHfoP (lft f)).
Qed.

  
Definition fo_in (t:fvs->set) :=
  fo_form (fun i => i 0 ∈ t (fun k => i (S k))).
Definition fo_eq (t:fvs->set) :=
  fo_form (fun i => i 0 == t (fun k => i (S k))).

Lemma fo_in_eq t :
  fo_in t ->
  fo_eq t.
intros.
apply FO_ext with (fun i => forall z, z ∈ i 0 <-> z ∈ t (fun k => i (S k))).
{intros; rewrite eq_set_ax; reflexivity. }
constructor; constructor; constructor; try fo_trivial.
apply fo_form_ren with (f:=lft S)(1:=H).
apply fo_form_ren with (f:=lft S)(1:=H).
Qed.
Lemma fo_eq_in t :
  fo_eq t ->
  fo_in t.
intros.
apply FO_ext with (fun i => exists z, z == t (fun k=>i(S k)) /\ i 0 ∈ z).
{split; intros.
 destruct H0 as (?&?&?).
 revert H1; apply eq_elim; trivial.
 exists (t (fun k => vs(S k))); split; [reflexivity|trivial]. }
constructor; constructor.
apply fo_form_ren with (f:=lft S)(1:=H).
fo_trivial.
Qed.

Lemma fo_in_proj k :
  fo_in (fun i => i k).
fo_trivial.
Qed.
Lemma fo_eq_proj k :
  fo_eq (fun i => i k).
fo_trivial.
Qed.

Lemma fo_in_in u v :
  fo_in u ->
  fo_in v ->
  fo_form (fun i => u i ∈ v i).
intros.
apply FO_ext with (fun i => exists z, z ∈ v i /\ z == u i).
{intros; rewrite in_set_def; reflexivity. }
constructor; constructor; trivial.
apply fo_in_eq; trivial.
Qed.
Lemma fo_eq_eq u v :
  fo_eq u ->
  fo_eq v ->
  fo_form (fun i => u i == v i).
intros.
apply FO_ext with (fun i => exists z, z == u i /\ z == v i).
{split; intros.
 destruct H1 as (?&?&?).
 rewrite <-H1; trivial.
 exists (u vs);split;[reflexivity|trivial]. }
constructor; constructor; trivial.
Qed.



Lemma fo_T P :
  (forall vs, P vs) ->
  fo_form P.
intros.
apply FO_ext with (fun _ => True);[|constructor].
split;trivial.
Qed.
Lemma fo_F P :
  (forall vs, ~ P vs) ->
  fo_form P.
intros.
apply FO_ext with (fun _ => False);[|constructor].
split;[intros [ ]|apply H].
Qed.
Lemma fo_ex2 P Q :
  fo_form (bind P) ->
  fo_form (bind Q) ->
  fo_form (fun i => exists2 x, P x i & Q x i).
intros.
apply FO_ext with (fun i=>exists x, P x i /\ Q x i).  
{intros; symmetry; apply ex_ex2. }
constructor; constructor; trivial.
Qed.
Ltac fo_step :=
  fo_trivial ||
  (first [apply FO_and
         |apply FO_or
         |apply FO_imp
         |apply FO_fa
         |apply FO_ex
         |apply fo_ex2];
   try fo_trivial).

(* ZF axioms *)
Lemma fo_empty :
  fo_in (fun _ => empty).
apply fo_F.
intros; apply empty_ax.
Qed.

Lemma fo_pair u v :
  fo_in u ->
  fo_in v ->
  fo_in (fun i => pair (u i) (v i)).
intros.
eapply FO_ext.
{intros vs; symmetry; apply pair_ax. }
fo_step; apply fo_in_eq; trivial.
Qed.

Lemma fo_union u :
  fo_in u ->
  fo_in (fun i => union (u i)).
intros.
eapply FO_ext.
{intros vs; symmetry; apply union_ax. }
fo_step.
unfold bind; simpl.
apply fo_form_ren with (1:=H)(f:=lft S).
Qed.

Lemma fo_subset u P :
  fo_in u ->
  fo_form (bind P) ->
  fo_in (fun i => subset (u i) (fun x => P x i)).
intros.
eapply FO_ext.
{intros vs; symmetry; apply subset_ax. }
repeat fo_step.
 apply H.
 apply fo_form_ren with (1:=H0)(f:=lft S).
Qed.

Lemma fo_power u :
  fo_in u ->
  fo_in (fun i => power (u i)).
intros.
eapply FO_ext.
{intros vs; symmetry; apply power_ax. }
repeat fo_step.
apply fo_form_ren with (1:=H)(f:=lft S).
Qed.

Lemma fo_replf u f :
  fo_in u ->
  fo_eq (bind f) ->
  fo_in (fun i => replf (u i) (fun x => f x i)).
intros.
eapply FO_ext.
{intros vs; symmetry; apply replf_ax.
 do 2 red; intros.
 apply fo_form_param in H0.
 do 2 red in H0.
 unfold bind in H0.
 apply H0 with (x:=icons (f x (fun k => vs (S k))) (icons x (fun k => vs (S k))))
               (y:=icons (f x (fun k => vs (S k))) (icons x' (fun k => vs (S k))));
   [intros [|[|k]];simpl|reflexivity]; auto with *. }
repeat fo_step.
apply fo_form_ren with (1:=H)(f:=lft S).
unfold bind; simpl.
apply fo_eq_eq; [fo_trivial|].
apply fo_form_ren with (1:=H0)(f:=lft (lft S)).
Qed.

Lemma fo_repl u R :
  fo_in u ->
  fo_form (bind (fun x => bind (R x))) ->
  (forall i x y y', x ∈ u i -> R x y i -> R x y' i -> y == y') ->
  fo_in (fun i => repl (u i) (fun x y => R x y i)).
intros.
eapply FO_ext.
{intros vs; symmetry; apply repl_ax.
 *intros.
  revert H5; apply iff_impl.
  apply fo_form_param in H0.
  do 2 red in H0.
  unfold bind in H0.
  apply H0 with (x:=icons x (icons y (fun k => vs (S k))))
                (y:=icons x' (icons y' (fun k => vs (S k))));
    intros [|[|k]];simpl; auto with *.
 *intros; apply H1 with (fun k=>vs (S k)) x; trivial. }
repeat fo_step.
*apply fo_form_ren with (1:=H)(f:=lft S).
*apply H0.
Qed.
Lemma fo_repl_cond u R :
  fo_in u ->
  fo_form (bind (fun x => bind (R x))) ->
  fo_in (fun i => cond_set (forall x y y', x ∈ u i -> R x y i -> R x y' i -> y==y')
                    (repl (u i) (fun x y => R x y i))).
intros.
eapply FO_ext.
{intros vs; symmetry; eapply transitivity;[apply cond_set_ax|].
 eapply transitivity;[apply and_comm|].
 apply and_iff_morphisml;[reflexivity|].
 intros Runiq _.
 apply repl_ax; trivial.
 intros.
 revert H4; apply iff_impl.
 apply fo_form_param in H0.
 do 2 red in H0.
 unfold bind in H0.
 apply H0 with (x:=icons x (icons y (fun k => vs (S k))))
               (y:=icons x' (icons y' (fun k => vs (S k))));
    intros [|[|k]];simpl; auto with *. }
repeat fo_step.
*apply fo_form_ren with (1:=H)(f:=fun k => S(S(lft S k))).
*apply fo_form_ren with (1:=H0)(f:=icons 2 (icons 1 (fun k=>S(S(S(S k)))))).
*apply fo_form_ren with (1:=H0)(f:=icons 2 (icons 0 (fun k=>S(S(S(S k)))))).
*apply fo_form_ren with (1:=H)(f:=fun k => lft S k).
*apply H0.
Qed.



Ltac fo_set :=
  first[apply fo_empty
       |apply fo_pair
       |apply fo_union
       |apply fo_power
       |apply fo_subset
       |apply fo_replf].

(* Derived set theoretical notions *)

Require Import ZFpairs.

Transparent fst snd couple prodcart.

Lemma fo_couple u v:
  fo_in u ->
  fo_in v ->
  fo_in (fun i => couple (u i) (v i)).
intros.
repeat fo_set; trivial.
Qed.

Lemma fo_fst u :
  fo_in u ->
  fo_in (fun i => fst (u i)).
unfold fst.
intros.
repeat fo_set; trivial.
apply fo_in_in; [apply fo_pair;fo_trivial|].
apply fo_form_ren with (1:=H)(f:=lft S).
Qed.

Lemma fo_snd u :
  fo_in u ->
  fo_in (fun i => snd (u i)).
unfold fst.
intros.
repeat fo_set; trivial.
apply fo_eq_eq; apply fo_in_eq.
*apply fo_pair;[apply fo_fst|fo_trivial].
 apply fo_form_ren with (1:=H)(f:=lft S).
*apply fo_union.
 apply fo_form_ren with (1:=H)(f:=lft S).
Qed.

Lemma fo_prodcart u v :
  fo_in u ->
  fo_in v ->
  fo_in (fun i => prodcart (u i) (v i)).
intros.
repeat fo_set; trivial.
unfold bind; simpl.
repeat fo_step; unfold bind; simpl.
*apply fo_form_ren with (1:=H)(f:=lft S).
*apply fo_form_ren with (1:=H0)(f:=lft (fun k =>S(S k))).
*apply fo_eq_eq; [fo_trivial|apply fo_in_eq].
 apply fo_couple; fo_trivial.
Qed.

Opaque fst snd couple prodcart.

Require Import ZFrelations.
Transparent cc_app cc_lam cc_prod dep_func func ZFrelations.app.

Lemma fo_app u v :
  fo_in u ->
  fo_in v ->
  fo_in (fun i => ZFrelations.app (u i) (v i)).
intros fou fov.
repeat fo_set; trivial; unfold bind; simpl.
*fo_step; apply fo_in_in.
 +apply fo_couple; fo_trivial.
 +apply fo_form_ren with (1:=fou)(f:=lft (fun k=>S(S k))).
*apply fo_in_in.
 +apply fo_couple; [|fo_trivial].
  apply fo_form_ren with (1:=fov)(f:=lft S).
 +apply fo_form_ren with (1:=fou)(f:=lft S).
Qed.

Lemma fo_cc_app u v :
  fo_in u ->
  fo_in v ->
  fo_in (fun i => cc_app (u i) (v i)).
intros fou fov.
repeat fo_set; trivial; unfold bind; simpl.
*apply fo_eq_eq; apply fo_in_eq.
 +apply fo_fst; fo_trivial.
 +apply fo_form_ren with (1:=fov)(f:=lft S).
*fo_step; apply fo_in_in;[apply fo_couple;fo_trivial|].
 fo_set.
 +apply fo_form_ren with (1:=fou)(f:=lft (fun k=>S(S k))).
 +apply fo_eq_eq; apply fo_in_eq.
  apply fo_fst; fo_trivial.  
  apply fo_form_ren with (1:=fov)(f:=lft (fun k=>S(S(S k)))).
Qed.
Lemma fo_cc_lam u v :
  fo_in u ->
  fo_in (bind v) ->
  fo_in (fun i => cc_lam (u i) (fun x => v x i)).
intros fou fov.
repeat fo_set; trivial; unfold bind; simpl.
apply fo_in_eq; apply fo_replf; trivial.
apply fo_in_eq; apply fo_couple; fo_trivial.
Qed.
Lemma fo_cc_prod u v :
  fo_in u ->
  fo_in (bind v) ->
  fo_in (fun i => cc_prod (u i) (fun x => v x i)).
intros fou fov.
repeat fo_set; trivial; unfold bind; simpl.
*apply fo_prodcart; [trivial|].
 unfold dep_image.
 fo_set.
 apply fo_replf; trivial.
 apply fo_in_eq; trivial. 
*repeat fo_step.
 +apply fo_form_ren with (1:=fou)(f:=lft S).
 +unfold bind.
  apply fo_in_in;[fo_trivial|].
  repeat fo_set.
  apply fo_form_ren with (1:=fou)(f:=lft(fun k=>S(S(S k)))).
  apply fo_in_eq.
  apply fo_form_ren with (1:=fov)(f:=lft(lft(fun k=>S(S(S k))))).
 +apply fo_in_in;[|fo_trivial].
  apply fo_couple; fo_trivial.
 +apply fo_in_in;[|fo_trivial].
  apply fo_couple; fo_trivial.
 +apply fo_in_in;[|fo_trivial].
  apply fo_couple; fo_trivial.
*repeat fo_step.
 +apply fo_form_ren with (1:=fou)(f:=lft (fun k=>S k)).
 +apply fo_in_in.
  ++apply fo_app; fo_trivial.
  ++apply fo_form_ren with (1:=fov)(f:=lft (lft(fun k=>S k))).
*apply fo_in_eq; apply fo_cc_lam.
 +apply fo_form_ren with (1:=fou)(f:=lft S).
 +apply fo_app; fo_trivial.
Qed.

Opaque cc_app cc_lam cc_prod.

Require Import ZFnats ZFlist ZFwdom.

Lemma fo_N :
  fo_in (fun _ => N).
Admitted.
Opaque N.

Lemma fo_natrec f g u :
  fo_in f ->
  fo_in (bind (fun x => bind (g x))) ->
  fo_in u ->
  fo_in (fun i => natrec (f i) (fun x y => g x y i) (u i)).
Admitted.

Lemma fo_List A :
  fo_in A ->
  fo_in (fun i => List (A i)).
Admitted.

Lemma fo_Wdom A B :
  fo_in A ->
  fo_in (bind B) ->
  fo_in (fun i => Wdom (A i) (fun x=>B x i)).
intros foA foB.
repeat fo_set.
apply fo_prodcart; [|trivial].
apply fo_List.
apply fo_union.
apply fo_replf; trivial.
apply fo_in_eq; trivial.
Qed.

Lemma fo_Wsup u v :
  fo_in u ->
  fo_in v ->
  fo_in (fun i => Wsup (u i) (v i)).
intros fou fov.
repeat fo_set; trivial.
*apply fo_couple; [apply fo_empty|trivial].
*apply fo_couple; [apply fo_empty|trivial].
*apply fo_eq_eq; apply fo_in_eq; [fo_trivial|].
 apply fo_couple; [apply fo_fst; fo_trivial|].
 apply fo_couple; [apply fo_fst; apply fo_snd;fo_trivial|].
 apply fo_snd; apply fo_snd; fo_trivial.
*apply fo_in_eq; apply fo_couple; [apply fo_couple|].
 +apply fo_fst; fo_trivial.
 +apply fo_fst; apply fo_snd; fo_trivial.
 +apply fo_snd; apply fo_snd; fo_trivial.
Qed. 

Lemma fo_Wf A B X :
  fo_in A ->
  fo_in (bind B) ->
  fo_in X ->
  fo_in (fun i => Wf (A i) (fun x=>B x i) (X i)).
intros foA foB foX.
repeat fo_set; [trivial|].
apply fo_in_eq; repeat fo_set.
*apply fo_cc_prod; trivial.
 apply fo_form_ren with (1:=foX)(f:=lft (fun k=>S(S k))); simpl.
*apply fo_in_eq; apply fo_Wsup; fo_trivial.
Qed.

Opaque Wdom Wsup Wf.

Require Import ZFw.


Lemma fo_W A B :
  fo_in A ->
  fo_in (bind B) ->
  fo_in (fun i => W (A i) (fun x=>B x i)).
intros foA foB.
repeat fo_set.
*apply fo_Wdom; trivial.
*repeat fo_step.
 apply fo_in_in; [fo_trivial|].
 apply fo_Wdom.
 +apply fo_form_ren with (1:=foA)(f:=lft (fun k=>S(S k))).
 +apply fo_form_ren with (1:=foB)(f:=lft(lft(fun k=>S(S k)))).
*unfold ZFtarski.post_fix.
 repeat fo_step.
 apply fo_in_in; [fo_trivial|].
 apply fo_Wf;[| |fo_trivial].
 +apply fo_form_ren with (1:=foA)(f:=lft (fun k=>S(S k))); simpl.
 +apply fo_form_ren with (1:=foB)(f:=lft(lft (fun k=>S(S k)))); simpl.
*repeat fo_step.
 apply fo_in_in; [fo_trivial|].
 repeat fo_set.
 +apply fo_Wdom.
  ++apply fo_form_ren with (1:=foA)(f:=lft (fun k=>S(S k))); simpl.
  ++apply fo_form_ren with (1:=foB)(f:=lft(lft (fun k=>S(S k)))); simpl.
 +repeat fo_step.
  apply fo_in_in; [fo_trivial|].
  apply fo_Wdom.
  ++apply fo_form_ren with (1:=foA)(f:=lft (fun k=>S(S(S(S k))))); simpl.
  ++apply fo_form_ren with (1:=foB)(f:=lft(lft (fun k=>S(S(S(S k)))))); simpl.
 +unfold ZFtarski.post_fix.
  repeat fo_step.
  apply fo_in_in; [fo_trivial|].
  apply fo_Wf;[| |fo_trivial].
  ++apply fo_form_ren with (1:=foA)(f:=lft (fun k=>S(S(S(S k))))); simpl.
  ++apply fo_form_ren with (1:=foB)(f:=lft(lft (fun k=>S(S(S(S k)))))); simpl.
Qed.
