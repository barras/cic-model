Require Import Wf_nat.
Require Import ZF ZFpairs ZFnats.
Require Import ZFord ZFfix.

Section ListDefs.

  Variable A : set.

  Definition Nil := empty.
  Definition Cons := couple.

  Definition LISTf (X:set) := singl empty ∪ prodcart A X.

Instance LISTf_mono : Proper (incl_set ==> incl_set) LISTf.
do 2 red; intros.
unfold LISTf.
apply union2_mono; auto with *.
apply prodcart_mono; auto with *.
Qed.

Instance LISTf_morph : Proper (eq_set ==> eq_set) LISTf.
apply Fmono_morph.
apply LISTf_mono.
Qed.

  Hint Resolve LISTf_morph LISTf_mono : core.
  
  Lemma LISTf_ind : forall X (P : set -> Prop),
    Proper (eq_set ==> iff) P ->
    P Nil ->
    (forall x l, x ∈ A -> l ∈ X -> P (Cons x l)) ->
    forall a, a ∈ LISTf X -> P a.
unfold LISTf; intros.
apply union2_elim in H2; destruct H2 as [H2|H2].
 apply singl_elim in H2.
 rewrite H2; trivial.

 rewrite surj_pair with (1:=H2).
 apply H1.
  apply fst_typ in H2; trivial.
  apply snd_typ in H2; trivial.
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
apply couple_intro; trivial.
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
intuition auto with *.
apply discr_mt_couple in H1; contradiction.
Qed.

  Lemma LIST_case_Cons x l f g : LIST_case (Cons x l) f g == g.
unfold LIST_case.
rewrite eq_set_ax; intros z.
rewrite union2_ax.
rewrite cond_set_ax.
rewrite cond_set_ax.
intuition.
 symmetry in H1; apply discr_mt_couple in H1; contradiction.

 right; split; trivial.
 unfold Cons; rewrite fst_def; rewrite snd_def; reflexivity.
Qed.

  Definition List := TI LISTf omega.

  Lemma List_eqn : List == LISTf List.
apply eq_intro; intros.
*unfold List.
 rewrite <- TI_mono_succ; auto.
 revert H; apply TI_incl; auto.
*elim H using LISTf_ind.
 +do 2 red; intros.
  rewrite H0; reflexivity.
 +apply TI_intro with (osucc zero); auto.
  apply Nil_typ0.
 +intros.
  apply TI_elim in H1; auto.
  destruct H1 as (o,tyo,tyl).  
  apply TI_intro with (osucc o); auto.
  apply Cons_typ0; trivial.
  rewrite TI_mono_succ; auto.
  apply isOrd_inv with omega; trivial.  
Qed.

  Lemma List_ind : forall P : set -> Prop,
    Proper (eq_set ==> iff) P ->
    P Nil ->
    (forall x l, x ∈ A -> l ∈ List -> P l -> P (Cons x l)) ->
    forall a, a ∈ List -> P a.
intros.
revert a H2.
unfold List.
elim isOrd_omega using isOrd_ind; intros.
apply TI_elim in H5; auto.
destruct H5 as (o,oo,tya).
elim tya using LISTf_ind; trivial.
intros.
apply H1; eauto.
revert H6; apply TI_incl; auto.
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
apply Fmono_morph.
apply List_mono.
Qed.
