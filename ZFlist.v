Require Import Wf_nat.
Require Import ZF ZFpairs ZFnats.
Require Import ZFrepl ZFord ZFfix.

Section ListDefs.

  Variable A : set.

  Definition Nil := empty.
  Definition Cons := couple.

  Definition LISTf (X:set) :=
    singl empty ∪ sup A (fun x => replf X (fun l => couple x l)).

Lemma ext1 : forall x X, ext_fun X (fun l => couple x l).
do 2 red; intros.
rewrite H0; reflexivity.
Qed.

Lemma ext2 : forall X, ext_fun A (fun x => replf X (fun l => couple x l)).
do 2 red; intros.
apply replf_morph_raw; auto with *.
red; intros.
rewrite H0; rewrite H1; reflexivity.
Qed.

Hint Resolve ext1 ext2.

Instance LISTf_mono : Proper (incl_set ==> incl_set) LISTf.
do 2 red; intros.
unfold LISTf.
apply union2_mono.
 red; auto.

 red; intros.
 rewrite sup_ax in H0|-*; trivial.
 destruct H0.
 exists x0; trivial.
 rewrite replf_ax in H1|-*; trivial.
 destruct H1.
 exists x1; auto.
Qed.

Instance LISTf_morph : Proper (eq_set ==> eq_set) LISTf.
do 2 red; intros.
apply eq_intro; intros.
 apply (LISTf_mono x y); trivial. 
 red; intros.
 rewrite <- H; auto.

 apply (LISTf_mono y x); trivial. 
 red; intros.
 rewrite H; auto.
Qed.

  Lemma LISTf_ind : forall X (P : set -> Prop),
    Proper (eq_set ==> iff) P ->
    P Nil ->
    (forall x l, x ∈ A -> l ∈ X -> P (Cons x l)) ->
    forall a, a ∈ LISTf X -> P a.
unfold LISTf; intros.
apply union2_elim in H2; destruct H2 as [H2|H2].
 apply singl_elim in H2.
 rewrite H2; trivial.

 rewrite sup_ax in H2; trivial.
 destruct H2.
 rewrite replf_ax in H3; trivial.
 destruct H3.
 rewrite H4; auto.
Qed.

  Lemma Nil_typ0 : forall X, Nil ∈ LISTf X.
intros.
unfold Nil, LISTf.
apply union2_intro1; apply singl_intro.
Qed.

  Lemma Cons_typ0 : forall X x l,
    x ∈ A -> l ∈ X -> Cons x l ∈ LISTf X.
intros.
unfold Cons, LISTf.
apply union2_intro2.
rewrite sup_ax; trivial.
exists x; trivial.
rewrite replf_ax; trivial.
exists l; auto with *.
Qed.

  (* LIST_case is f when l is Nil, or g when l is Cons *)
  Definition LIST_case l f g :=
    cond_set (l == Nil) f ∪ cond_set (l == Cons (fst l) (snd l)) g.

  Global Instance LIST_case_morph : Proper (eq_set==>eq_set==>eq_set==>eq_set) LIST_case.
do 4 red; intros; unfold LIST_case.
apply union2_morph.
 rewrite H; rewrite H0; reflexivity.

 rewrite H; rewrite H1; reflexivity.
Qed.

  Lemma LIST_case_Nil f g : LIST_case Nil f g == f.
unfold LIST_case.
rewrite eq_set_ax; intros z.
rewrite union2_ax.
rewrite cond_set_ax.
rewrite cond_set_ax.
intuition.
apply discr_mt_pair in H1; contradiction.
Qed.

  Lemma LIST_case_Cons x l f g : LIST_case (Cons x l) f g == g.
unfold LIST_case.
rewrite eq_set_ax; intros z.
rewrite union2_ax.
rewrite cond_set_ax.
rewrite cond_set_ax.
intuition.
 symmetry in H1; apply discr_mt_pair in H1; contradiction.

 right; split; trivial.
 unfold Cons; rewrite fst_def; rewrite snd_def; reflexivity.
Qed.


  Definition Lstn n := TI LISTf (nat2ordset n).

  Lemma Lstn_incl_succ : forall k, Lstn k ⊆ Lstn (S k).
unfold Lstn; simpl; intros.
apply TI_incl; auto with *.
Qed.

  Lemma Lstn_eq : forall k, Lstn (S k) == LISTf (Lstn k).
unfold Lstn; simpl; intros.
apply TI_mono_succ; auto with *.
Qed.

  Lemma Lstn_incl : forall k k', (k <= k')%nat -> Lstn k ⊆ Lstn k'.
induction 1; intros.
 red; auto.
 red; intros.
 apply (Lstn_incl_succ m z); auto.
Qed.


  Definition List := TI LISTf omega.

  Lemma List_intro : forall k, Lstn k ⊆ List.
unfold List, Lstn; intros.
apply TI_incl; auto with *.
apply isOrd_sup_intro with (S k); simpl; auto.
apply lt_osucc; auto.
Qed.

  Lemma List_elim : forall x,
    x ∈ List -> exists k, x ∈ Lstn k.
unfold List, Lstn; intros.
apply TI_elim in H; auto with *.
destruct H.
apply isOrd_sup_elim in H; destruct H.
exists x1.
apply TI_intro with x0; auto with *.
Qed.

  Lemma Lstn_case : forall k (P : set -> Prop),
    Proper (eq_set ==> iff) P ->
    P Nil ->
    (forall x l k', (k' < k)%nat -> x ∈ A -> l ∈ Lstn k' -> P (Cons x l)) ->
    forall a, a ∈ Lstn k -> P a.
destruct k; intros.
 unfold Lstn in H2.
 rewrite TI_initial in H2; auto with *.
 elim empty_ax with (1:=H2).

 rewrite Lstn_eq in H2.
 elim H2 using LISTf_ind; eauto.
Qed.



  Lemma List_fix : forall (P:set->Prop),
    (forall k,
     (forall k' x, (k' < k)%nat -> x ∈ Lstn k' -> P x) ->
     (forall x, x ∈ Lstn k -> P x)) ->
    forall x, x ∈ List -> P x.
intros.
apply List_elim in H0; destruct H0.
revert x H0.
elim (lt_wf x0); intros.
eauto.
Qed.

  Lemma List_ind : forall P : set -> Prop,
    Proper (eq_set ==> iff) P ->
    P Nil ->
    (forall x l, x ∈ A -> l ∈ List -> P l -> P (Cons x l)) ->
    forall a, a ∈ List -> P a.
intros.
elim H2 using List_fix; intros.
elim H4 using Lstn_case; intros; eauto.
apply H1; eauto.
apply List_intro in H7; trivial.
Qed.
 
  Lemma List_eqn : List == LISTf List.
apply eq_intro; intros.
 apply List_elim in H; destruct H.
 apply Lstn_incl_succ in H.
 rewrite Lstn_eq in H.
 eapply LISTf_mono with (Lstn x); trivial.
 apply List_intro.

 elim H using LISTf_ind; intros.
  do 2 red; intros.
  rewrite H0; reflexivity.

  apply List_intro with 1; rewrite Lstn_eq.
  apply Nil_typ0; trivial.

  apply List_elim in H1; destruct H1 as (k,H1).
  apply List_intro with (S k); rewrite Lstn_eq.
  apply Cons_typ0; auto.
Qed.

  Lemma Nil_typ : Nil ∈ List.
intros.
rewrite List_eqn; apply Nil_typ0; trivial.
Qed.

  Lemma Cons_typ : forall x l,
    x ∈ A -> l ∈ List -> Cons x l ∈ List.
intros.
rewrite List_eqn; apply Cons_typ0; trivial.
Qed.

End ListDefs.

Instance List_mono : Proper (incl_set ==> incl_set) List.
do 3 red; intros.
elim H0 using List_ind; intros.
 do 2 red; intros.
 rewrite H1; reflexivity.

 apply Nil_typ.

 apply Cons_typ; auto.
Qed.

Instance List_morph : morph1 List.
do 2 red; intros.
apply eq_intro; intros.
 revert z H0; apply List_mono.
 rewrite H; auto with *.

 revert z H0; apply List_mono.
 rewrite H; auto with *.
Qed.
