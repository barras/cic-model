Require Import ZF ZFpairs ZFsum ZFfix ZFnats ZFrelations ZFord ZFcard ZFcont.
Require Import ZFstable ZFrank ZFgrothendieck ZFinaccessible.
Import IZF ZFrepl.

Lemma discr_mt_pair : forall a b, ~ empty == pair a b.
red; intros.
apply (empty_ax a).
rewrite H.
apply pair_intro1.
Qed.

Section W_theory.

Variable A : set.
Variable B : set -> set.
Hypothesis Bmorph : morph1 B.

Require Import ZFcoc ZFlist.

Definition W_F X := sigma A (fun x => cc_prod (B x) (fun _ => X)).

Lemma W_F_mono : Proper (incl_set ==> incl_set) W_F.
unfold W_F; do 3 red; intros.
rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ H0)).
apply couple_intro_sigma.
 red; red; intros.
 apply cc_prod_ext; auto with *.
 red; intros; auto with *.

 apply fst_typ_sigma in H0; trivial.

 apply snd_typ_sigma with (y:=fst z) in H0; auto with *.
  revert H0; apply cc_prod_covariant; auto with *.

  red; red; intros.
  apply cc_prod_ext; auto with *.
  red; intros; auto with *.
Qed.

(* *)
Definition Wdom := rel (List (sup A B)) A.

Definition Wsup x :=
  union2 (singl (couple Nil (fst x)))
   (sup (B (fst x)) (fun y =>
      replf (cc_app (snd x) y)
        (fun p => couple (Cons y (fst p)) (snd p)))).

Instance Wsup_morph : Proper (eq_set ==> eq_set) Wsup.
do 2 red; intros.
unfold Wsup.
apply union2_morph.
 rewrite H; reflexivity.

 apply sup_morph.
  rewrite H; reflexivity.
  red; intros.
  apply replf_morph_raw; auto.
   rewrite H; rewrite H1; reflexivity.

   red; intros.
   rewrite H1; rewrite H2; reflexivity.
Qed.

Lemma wext1 : forall i y,
  ext_fun y (fun p => couple (Cons i (fst p)) (snd p)).
do 2 red; intros.
rewrite H0; reflexivity.
Qed.

Lemma wext2 : forall X f,
  ext_fun X (fun y =>
     replf (cc_app f y) (fun p => couple (Cons y (fst p)) (snd p))).
do 2 red; intros.
apply replf_morph_raw; auto.
 rewrite H0; reflexivity.

 red; intros.
 rewrite H0; rewrite H1; reflexivity.
Qed.
Hint Resolve wext1 wext2.

Lemma Wsup_def :
  forall x p,
  (p \in Wsup x <->
   p == couple Nil (fst x) \/
   exists2 i, i \in B (fst x) &
   exists2 q, q \in cc_app (snd x) i &
   p == couple (Cons i (fst q)) (snd q)).
intros.
unfold Wsup.
split; intros.
 apply union2_elim in H; destruct H;[left|right].
  apply singl_elim in H; trivial.

  rewrite sup_ax in H; trivial.
  destruct H as (i,?,?); exists i; trivial.
  rewrite replf_ax in H0; trivial.

 destruct H as [eqp|(i,?,(q,?,eqp))]; rewrite eqp; clear eqp.  
  apply union2_intro1.
  apply singl_intro.

  apply union2_intro2.
  rewrite sup_ax; trivial.
  exists i; trivial.
  rewrite replf_ax; trivial.
  exists q; auto with *.
Qed.

Lemma Wsup_hd_prop : forall a x,
  couple Nil a \in Wsup x <-> a == fst x.
split; intros.
 apply union2_elim in H; destruct H.
  apply singl_elim in H.
  apply couple_injection in H; destruct H; trivial.

  rewrite sup_ax in H; trivial.
  destruct H.
  rewrite replf_ax in H0; trivial.
  destruct H0.
  apply couple_injection in H1; destruct H1 as (H1,_).
   apply discr_mt_pair in H1; contradiction.

 rewrite H.
 unfold Wsup.
 apply union2_intro1.
 apply singl_intro.
Qed.

Let tys : forall x X, x \in W_F X -> snd x \in cc_prod (B (fst x)) (fun _ => X).
intros.
apply snd_typ_sigma with (y:=fst x) in H; auto with *.
red; red; intros.
apply cc_prod_ext; auto with *.
red; auto with *.
Qed.

Lemma Wsup_tl_prop : forall i l a x,
  x \in W_F Wdom ->
  (couple (Cons i l) a \in Wsup x <->
   i \in B (fst x) /\ couple l a \in cc_app (snd x) i).
intros.
assert (tyx : fst x \in A).
 apply fst_typ_sigma in H; trivial.
assert (tyf : snd x \in cc_prod (B (fst x)) (fun _ => Wdom)).
 apply tys; trivial.
split; intros.
 apply union2_elim in H0; destruct H0.
  apply singl_elim in H0.
  apply couple_injection in H0; destruct H0 as (H0,_).
  symmetry in H0.
  apply discr_mt_pair in H0; contradiction.

  rewrite sup_ax in H0; trivial.
  destruct H0.
  rewrite replf_ax in H1; trivial.
  destruct H1.
  apply couple_injection in H2; destruct H2.
  apply couple_injection in H2; destruct H2.
  rewrite H2.
  split; trivial.
  apply cc_prod_elim with (x:=x0) in tyf; trivial.
  rewrite H4; rewrite H3.
  rewrite <- surj_pair with (List (sup A B)) A; trivial.
  apply power_elim with (1:=tyf); trivial.

 destruct H0.
 unfold Wsup.
 apply union2_intro2.
 rewrite sup_ax; trivial.
 exists i; trivial.
 rewrite replf_ax; trivial.
 exists (couple l a); trivial.
 rewrite fst_def.
 rewrite snd_def; reflexivity.
Qed.

Lemma Wsup_inj : forall x x',
  x \in W_F Wdom ->
  x' \in W_F Wdom ->
  Wsup x == Wsup x' -> x == x'.
intros.
assert (fst x == fst x').
 generalize (Wsup_hd_prop (fst x) x); intro.
 generalize (Wsup_hd_prop (fst x) x'); intro.
 apply H3.
 rewrite <- H1.
 apply H2.
 reflexivity.
assert (snd x == snd x').
 specialize cc_eta_eq with (1:=tys _ _ H); intros.
 specialize cc_eta_eq with (1:=tys _ _ H0); intros.
 rewrite H3; rewrite H4.
 apply cc_lam_ext.
  apply Bmorph; trivial.

  red; intros.
  assert (x'0 \in B (fst x')).
   rewrite <- H6; rewrite <- H2; trivial.
  assert (cc_app (snd x) x0 \incl prodcart (List (sup A B)) A).
   red; intros.
   apply power_elim with (2:=H8).
   apply cc_prod_elim with (1:=tys _ _ H); trivial.
  assert (cc_app (snd x') x'0 \incl prodcart (List (sup A B)) A).
   red; intros.
   apply power_elim with (2:=H9); trivial.
   apply cc_prod_elim with (1:=tys _ _ H0); trivial.
  generalize (fun z l => Wsup_tl_prop x0 l z _ H); intros.
  generalize (fun z l => Wsup_tl_prop x'0 l z _ H0); intros.
  apply eq_intro; intros.
   generalize (surj_pair _ _ _ (H8 _ H12)); intro.
   rewrite H13.
   apply H11.
   rewrite <- H6; rewrite <- H1.
   apply <- H10.
   rewrite <- H13; auto.

   generalize (surj_pair _ _ _ (H9 _ H12)); intro.
   rewrite H13.
   apply H10.
   rewrite H1; rewrite H6.
   apply <- H11.
   rewrite <- H13; auto.
apply subset_elim1 in H.
apply subset_elim1 in H0.
rewrite (surj_pair _ _ _ H).
rewrite (surj_pair _ _ _ H0).
rewrite H2; rewrite H3; reflexivity.
Qed.

Lemma Wsup_typ_gen : forall x,
  x \in W_F Wdom ->
  Wsup x \in Wdom.
intros.
apply power_intro; intros.
rewrite Wsup_def in H0.
destruct H0 as [eqz|(i,?,(q,?,eqz))]; rewrite eqz; clear z eqz.
 apply couple_intro; trivial.
  apply Nil_typ.
  apply fst_typ_sigma in H; trivial.

 assert (q \in prodcart (List (sup A B)) A).
  apply power_elim with (2:=H1).
  apply cc_prod_elim with (1:=tys _ _ H); trivial.
 apply couple_intro.
  apply Cons_typ.
   rewrite sup_ax.
   2:red; red; intros; apply Bmorph; trivial.
   exists (fst x); trivial.
   apply fst_typ_sigma in H; trivial.

   apply fst_typ with (1:=H2).

  apply snd_typ with (1:=H2).
Qed.

Definition Wf X := replf (W_F X) Wsup.

Lemma wfext1 : forall X, ext_fun (W_F X) Wsup.
do 2 red; intros.
rewrite H0; reflexivity.
Qed.
Hint Resolve wfext1.

Lemma Wf_intro : forall x X,
  x \in W_F X ->
  Wsup x \in Wf X.
intros.
unfold Wf.
rewrite replf_ax; trivial.
exists x; auto with *.
Qed.

Lemma Wf_elim : forall a X,
  a \in Wf X ->
  exists2 x, x \in W_F X &
  a == Wsup x.
intros.
unfold Wf in H.
rewrite replf_ax in H; trivial.
Qed.

Lemma Wf_mono : Proper (incl_set ==> incl_set) Wf.
do 3 red; intros.
apply Wf_elim in H0; destruct H0 as (f,?,?).
rewrite H1; apply Wf_intro; trivial.
clear H1; revert f H0.
apply W_F_mono; trivial.
Qed.
Hint Resolve Wf_mono.

Lemma Wf_typ : forall X,
  X \incl Wdom -> Wf X \incl Wdom.
red; intros.
apply Wf_elim in H0; destruct H0 as (x,?,?).
rewrite H1.
apply Wsup_typ_gen; trivial.
clear H1; revert x H0.
apply W_F_mono; trivial.
Qed.
Hint Resolve Wf_typ.


Definition W := Ffix Wf Wdom.

Lemma Wtyp : W \incl Wdom.
apply Ffix_inA.
Qed.

Lemma Wi_W : forall o, isOrd o -> TI Wf o \incl W.
apply TI_Ffix; auto.
Qed.

Lemma TI_Wf_elim : forall a o,
  isOrd o ->
  a \in TI Wf o ->
  exists2 o', lt o' o &
  exists2 x, x \in W_F (TI Wf o') &
  a == Wsup x.
intros.
apply TI_elim in H0; trivial.
2:apply Fmono_morph; trivial.
destruct H0.
apply Wf_elim in H1.
eauto.
Qed.

  Lemma Wf_subterm : forall o a,
    isOrd o ->
    a \in TI Wf o ->
    a \in Wf (fsub Wf Wdom a).
intros.
apply TI_Wf_elim in H0; trivial.
destruct H0 as (w',?,(x,?,?)).
symmetry in H2; apply in_reg with (1:=H2).
apply Wf_intro; trivial.
assert (xsp := surj_pair _ _ _ (subset_elim1 _ _ _ H1)).
rewrite (cc_eta_eq _ _ _ (tys _ _ H1)) in xsp.
rewrite xsp.
apply couple_intro_sigma; auto with *.
 red; red; intros; auto with *.
 apply cc_prod_ext; auto with *.
 red; auto with *.

 apply fst_typ_sigma in H1; trivial.

 apply cc_prod_intro; intros; auto.
  red; red; intros.
  rewrite H4; reflexivity.

  apply subset_intro.
   apply Wtyp.
   apply Wi_W with w'.
    apply isOrd_inv with o; trivial.
    apply cc_prod_elim with (1:=tys _ _ H1); trivial.

   intros.
   apply Wf_elim in H5.
   destruct H5 as (x',?,?).
   rewrite H6 in H2.
   apply Wsup_inj in H2; trivial.
    rewrite H2.
    apply cc_prod_elim with (1:=tys _ _ H5).
    rewrite <- H2; trivial.

    revert H1; apply W_F_mono.
    transitivity W; [apply Wi_W|apply Wtyp].
    apply isOrd_inv with o; trivial.

    revert H5; apply W_F_mono; auto with *.
Qed.
Hint Resolve Wf_subterm.


Lemma Wsup_typ : forall o x,
  isOrd o ->
  x \in W_F (TI Wf o) ->
  Wsup x \in TI Wf (osucc o).
intros.
rewrite TI_mono_succ; auto.
apply Wf_intro; trivial.
Qed.

Lemma W_ind : forall (P:set->Prop),
  Proper (eq_set ==> iff) P ->
  (forall o' x, isOrd o' -> x \in W_F (TI Wf o') ->
   (forall i, i \in B (fst x) -> P (cc_app (snd x) i)) -> P (Wsup x)) ->
  forall a, a \in W -> P a.
intros.
unfold W in H1; rewrite Ffix_def in H1; auto.
destruct H1.
revert a H2.
apply isOrd_ind with (2:=H1); intros.
apply TI_Wf_elim in H5; trivial.
destruct H5 as (o',?,(x',?,?)).
rewrite H7; clear a H7.
apply H0 with o'; trivial.
 apply isOrd_inv with y; trivial.

 intros.
 apply H4 with o'; trivial.
 apply cc_prod_elim with (1:=tys _ _ H6); trivial.
Qed.

(* The closure ordinal of W *)
  Definition W_ord := Ffix_ord Wf Wdom.

  Lemma W_o_o : isOrd W_ord.
apply Ffix_o_o; auto.
Qed.
Hint Resolve W_o_o.

  Lemma W_post : forall a,
   a \in W ->
   a \in TI Wf W_ord.
apply Ffix_post; eauto.
Qed.

  Lemma W_eqn : W == Wf W.
apply Ffix_eqn; eauto.
Qed.

End W_theory.
