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

Require Import ZFlist.

Definition Wdom := rel (List (sup A B)) A.

Definition Wsup x f :=
  union2 (singl (couple Nil x))
   (sup (B x) (fun y =>
      replf (f y) (fun p => couple (Cons y (fst p)) (snd p)))).

Instance Wsup_morph : Proper (eq_set ==> (eq_set ==> eq_set) ==> eq_set) Wsup.
do 3 red; intros.
unfold Wsup.
apply union2_morph.
 rewrite H; reflexivity.

 apply sup_morph; auto with *.
 red; intros.
 apply replf_morph_raw; auto.
 red; intros.
 unfold Cons.
 rewrite H2; rewrite H3; reflexivity.
Qed.

Lemma wext1 : forall i y,
  ext_fun y (fun p => couple (Cons i (fst p)) (snd p)).
do 2 red; intros.
rewrite H0; reflexivity.
Qed.

Require Import ZFcoc.
Lemma wext2 : forall X f,
  ext_fun X (fun y =>
     replf (cc_app f y) (fun p => couple (Cons y (fst p)) (snd p))).
do 2 red; intros.
apply replf_morph_raw; auto.
 rewrite H0; reflexivity.

 red; intros.
 rewrite H0; rewrite H1; reflexivity.
Qed.
(*Lemma wext20 : forall X f,
  morph1 f ->
  ext_fun X (fun y =>
     replf (f y) (fun p => couple (Cons y (fst p)) (snd p))).
do 2 red; intros.
apply replf_morph_raw; auto.
red; intros.
rewrite H1; rewrite H2; reflexivity.
Qed.
*)
Hint Resolve wext1 (*wext20*) wext2.

Lemma Wsup_def :
  forall x f p,
  (p \in Wsup x (cc_app f) <->
   p == couple Nil x \/
   exists2 i, i \in B x &
   exists2 q, q \in cc_app f i &
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

(*
Lemma Wsup_def : forall x f p,
  morph1 f ->
  (p \in Wsup x f <->
   p == couple Nil x \/
   exists2 i, i \in B x &
   exists2 q, q \in f i &
   p == couple (Cons i (fst q)) (snd q)).
intros.
unfold Wsup.
split; intros.
 apply union2_elim in H0; destruct H0;[left|right].
  apply singl_elim in H0; trivial.

  rewrite sup_ax in H0; auto.
  destruct H0 as (i,?,?); exists i; trivial.
  rewrite replf_ax in H1; trivial.

 destruct H0 as [eqp|(i,?,(q,?,eqp))]; rewrite eqp; clear eqp.  
  apply union2_intro1.
  apply singl_intro.

  apply union2_intro2.
  rewrite sup_ax; auto.
  exists i; trivial.
  rewrite replf_ax; trivial.
  exists q; auto with *.
Qed.
*)


Lemma Wsup_hd_prop : forall a x f,
  couple Nil a \in Wsup x (cc_app f) <-> a == x.
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

Lemma Wsup_tl_prop : forall i l a x f,
  f \in cc_prod (B x) (fun _ => Wdom) ->
  (couple (Cons i l) a \in Wsup x (cc_app f) <->
   i \in B x /\ couple l a \in cc_app f i).
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
  apply cc_prod_elim with (x:=x0) in H; trivial.
  rewrite H4; rewrite H3.
  rewrite <- surj_pair with (List (sup A B)) A; trivial.
  apply power_elim with (1:=H); trivial.

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

(*
Lemma Wsup_tl_prop : forall i l a x f,
  morph1 f ->
  (forall i, i \in B x -> f i \in Wdom) ->
  (couple (Cons i l) a \in Wsup x f <->
   i \in B x /\ couple l a \in f i).
split; intros.
 apply union2_elim in H1; destruct H1.
  apply singl_elim in H1.
  apply couple_injection in H1; destruct H1 as (H1,_).
  symmetry in H1.
  apply discr_mt_pair in H1; contradiction.

  rewrite sup_ax in H1; auto.
  destruct H1.
  rewrite replf_ax in H2; trivial.
  destruct H2.
  apply couple_injection in H3; destruct H3.
  apply couple_injection in H3; destruct H3.
  rewrite H3.
  split; trivial.
  apply H0 in H1.
  rewrite H5; rewrite H4.
  rewrite <- surj_pair with (List (sup A B)) A; trivial.
  apply power_elim with (1:=H1); trivial.

 destruct H1.
 unfold Wsup.
 apply union2_intro2.
 rewrite sup_ax; auto.
 exists i; trivial.
 rewrite replf_ax; trivial.
 exists (couple l a); trivial.
 rewrite fst_def.
 rewrite snd_def; reflexivity.
Qed.
*)

Lemma Wsup_inj : forall x x' f f',
  f \in cc_prod (B x) (fun _ => Wdom) ->
  f' \in cc_prod (B x') (fun _ => Wdom) ->
  Wsup x (cc_app f) == Wsup x' (cc_app f') ->
  x == x' /\ f == f'.
intros.
assert (x==x').
 generalize (Wsup_hd_prop x x f); intro.
 generalize (Wsup_hd_prop x x' f'); intro.
 apply H3.
 rewrite <- H1.
 apply H2.
 reflexivity.
split; trivial.
specialize cc_eta_eq with (1:=H); intros.
specialize cc_eta_eq with (1:=H0); intros.
rewrite H3; rewrite H4.
apply cc_lam_ext.
 apply Bmorph; trivial.

 red; intros.
 assert (x'0 \in B x').
  rewrite <- H6; rewrite <- H2; trivial.
 assert (cc_app f x0 \incl prodcart (List (sup A B)) A).
  red; intros.
  apply cc_prod_elim with (x:=x0) in H; trivial.
  apply power_elim with (1:=H); trivial.
 assert (cc_app f' x'0 \incl prodcart (List (sup A B)) A).
  red; intros.
  apply cc_prod_elim with (x:=x'0) in H0; trivial.
  apply power_elim with (1:=H0); trivial.
 generalize (fun z l => Wsup_tl_prop x0 l z _ _ H); intros.
 generalize (fun z l => Wsup_tl_prop x'0 l z _ _ H0); intros.
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
Qed.

Lemma Wsup_typ_gen : forall x f,
  x \in A ->
  f \in cc_prod (B x) (fun _ => Wdom) ->
  Wsup x (cc_app f) \in Wdom.
intros.
apply power_intro; intros.
rewrite Wsup_def in H1.
destruct H1 as [eqz|(i,?,(q,?,eqz))]; rewrite eqz; clear z eqz.
 apply couple_intro; trivial.
 apply Nil_typ.

 assert (q \in prodcart (List (sup A B)) A).
  apply cc_prod_elim with (x:=i) in H0; trivial.
  apply power_elim with (1:=H0)(2:=H2).
 apply couple_intro.
  apply Cons_typ.
   rewrite sup_ax.
   2:red; red; intros; apply Bmorph; trivial.
   exists x; trivial.

   apply fst_typ with (1:=H3).

  apply snd_typ with (1:=H3).
Qed.

Definition Wf X :=
  sup A (fun x => replf (cc_prod (B x) (fun _ => X)) (fun f => Wsup x (cc_app f))).

Lemma wfext1 : forall x X,
  ext_fun (cc_prod (B x) (fun _ : set => X))
      (fun f => Wsup x (cc_app f)).
do 2 red; intros.
rewrite H0; reflexivity.
Qed.

Lemma wfext2: forall X,
 ext_fun A
   (fun x =>
    replf (cc_prod (B x) (fun _ : set => X))
      (fun f => Wsup x (cc_app f))).
do 2 red; intros.
apply replf_morph_raw.
 apply cc_prod_ext; auto.
 red; intros; auto with *.

 red; intros.
 rewrite H0; rewrite H1; reflexivity.
Qed.
Hint Resolve wfext1 wfext2.

Lemma Wf_intro : forall x f X,
  x \in A ->
  f \in cc_prod (B x) (fun _ => X) ->
  Wsup x (cc_app f) \in Wf X.
intros.
unfold Wf.
rewrite sup_ax; trivial.
exists x; trivial.
rewrite replf_ax; trivial.
exists f; auto with *.
Qed.


Lemma Wf_mono : Proper (incl_set ==> incl_set) Wf.
do 3 red; intros.
unfold Wf in H0|-*.
rewrite sup_ax in H0|-*; trivial.
destruct H0.
exists x0; trivial.
rewrite replf_ax in H1|-*; trivial.
destruct H1.
exists x1; trivial.
clear H2; revert x1 H1.
apply cc_prod_covariant; auto with *.
Qed.
Hint Resolve Wf_mono.

Lemma Wf_typ : forall X,
  X \incl Wdom -> Wf X \incl Wdom.
unfold Wf; red; intros.
rewrite sup_ax in H0; trivial.
destruct H0 as (x,xty,?).
rewrite replf_ax in H0; trivial.
destruct H0.
rewrite H1.
apply Wsup_typ_gen; trivial.
clear H1; revert x0 H0.
apply cc_prod_covariant; auto with *.
Qed.

Lemma Wf_fp : fp_props Wdom Wf.
split; intros.
 apply Wf_typ; trivial.
 apply Wf_mono; trivial.
Qed.

(********************)
Section WithoutKnaster.

Definition W := subset Wdom (fun a => exists2 o, isOrd o & a \in TI Wf o).

Lemma Wtyp : W \incl Wdom.
red; intros.
apply subset_elim1 in H; trivial.
Qed.

Lemma Wi_W : forall o, isOrd o -> TI Wf o \incl W.
intros.
apply isOrd_ind with (2:=H); intros.
red; intros.
apply TI_elim in H3; auto with *.
2:apply Fmono_morph; trivial.
destruct H3.
unfold W.
apply subset_intro.
 revert z H4; apply Wf_typ.
 transitivity W; auto.
 apply Wtyp.
exists (osucc x); auto.
 apply isOrd_succ; apply isOrd_inv with y; trivial.

 rewrite TI_mono_succ; auto.
 apply isOrd_inv with y; trivial.
Qed.

Lemma W_def : forall a, a \in W <-> exists2 o, isOrd o & a \in TI Wf o.
unfold W; intros.
rewrite subset_ax.
split; intros.
 destruct H.
 destruct H0.
 destruct H1.
 exists x0; trivial.
 rewrite H0; trivial.

 destruct H.
 split.
  apply Wtyp.
  revert a H0; apply Wi_W; trivial.

  exists a; auto with *.
  exists x; trivial.
Qed.


Lemma W_ind0 : forall (P:set->Prop) o,
  Proper (eq_set ==> iff) P ->
  isOrd o ->
  (forall o' x f, lt o' o -> x \in A -> f \in cc_prod (B x) (fun _ => TI Wf o') ->
   (forall i, i \in B x -> P (cc_app f i)) -> P (Wsup x (cc_app f))) ->
  forall a, a \in TI Wf o -> P a.
intros.
revert H1 a H2.
apply isOrd_ind with (2:=H0); intros.
apply TI_elim in H5; trivial.
2:apply Fmono_morph; trivial.
destruct H5.
unfold Wf at 1 in H6.
rewrite sup_ax in H6; trivial.
destruct H6.
rewrite replf_ax in H7; trivial.
destruct H7.
rewrite H8.
apply H4 with x; trivial.
 intros.
 apply H3 with x; trivial.
  intros.
  apply H4 with o'; auto.
  apply isOrd_trans with x; trivial.
 apply cc_prod_elim with (1:=H7); trivial.
Qed.

Lemma W_ind : forall (P:set->Prop),
  Proper (eq_set ==> iff) P ->
  (forall o' x f, isOrd o' -> x \in A -> f \in cc_prod (B x) (fun _ => TI Wf o') ->
   (forall i, i \in B x -> P (cc_app f i)) -> P (Wsup x (cc_app f))) ->
  forall a, a \in W -> P a.
intros.
apply subset_elim2 in H1; destruct H1.
rewrite H1; destruct H2.
apply W_ind0 with (4:=H3); intros; trivial.
apply H0 with o'; trivial.
apply isOrd_inv with x0; trivial.
Qed.

Definition W_rel F a y :=
  forall R:set->set->Prop,
  Proper (eq_set ==> eq_set ==> iff) R ->
  (forall o x f g,
   isOrd o ->
   ext_fun (B x) g ->
   x \in A ->
   f \in cc_prod (B x) (fun _ => TI Wf o) ->
   (forall i, i \in B x -> R (cc_app f i) (g i)) ->
   R (Wsup x (cc_app f)) (F x g)) ->
  R a y.

  Instance W_rel_morph :
    forall F, Proper (eq_set ==> eq_set ==> iff) (W_rel F).
Admitted.

Section Wrel.

  Variable F : set -> (set -> set) -> set.
  Hypothesis Fm :
    forall x x' g g', x == x' -> eq_fun (B x) g g' -> F x g == F x' g'.
                                                                             
  Lemma W_rel_intro : forall o x f g,
    isOrd o -> 
    x \in A -> 
    f \in cc_prod (B x) (fun _ => TI Wf o) ->
    ext_fun (B x) g ->
    (forall y, y \in B x -> W_rel F (cc_app f y) (g y)) ->
    W_rel F (Wsup x (cc_app f)) (F x g).
red; intros.                                                                 
apply H5 with o; trivial; intros.
apply H3; trivial.                                                           
Qed.                                                                         
                                                                             
  Lemma W_rel_inv0 : forall a y,
    W_rel F a y ->
    forall o x f,
    isOrd o ->
    x \in A ->
    f \in cc_prod (B x) (fun _ => TI Wf o) ->
    a == Wsup x (cc_app f) ->
    exists2 g,
      ext_fun (B x) g /\
      (forall y, y \in B x -> W_rel F (cc_app f y) (g y)) &                 
      y == F x g.
intros a y Wr.
apply (@proj2 (W_rel F a y)).
apply Wr; intros.
 admit. (* mrph *)

 split.
  apply W_rel_intro with o; auto.
  intros.
  apply H3; trivial.

  intros.
  apply Wsup_inj in H7; trivial.
  2:revert H2; apply cc_prod_covariant; auto with *.
  2:intros; transitivity W; [apply Wi_W|apply Wtyp]; trivial.
  2:revert H6; apply cc_prod_covariant; auto with *.
  2:intros; transitivity W; [apply Wi_W|apply Wtyp]; trivial.
  destruct H7.
  exists g.
   split; intros.
    red; red; intros.
    apply H0; trivial.
    rewrite H7; trivial.

    rewrite <- H7 in H9; rewrite <- H8.
    apply H3; trivial.

  apply Fm; trivial.
Qed.

  Lemma W_rel_inv : forall o x f y,
    isOrd o ->
    x \in A -> 
    f \in cc_prod (B x) (fun _ => TI Wf o) ->
    W_rel F (Wsup x (cc_app f)) y ->
    exists2 g,
      ext_fun (B x) g /\
      (forall y, y \in B x -> W_rel F (cc_app f y) (g y)) &                 
      y == F x g.
intros.
apply W_rel_inv0 with (1:=H2) (o:=o); auto with *.
Qed.

  Lemma W_rel_fun :
    forall x y, W_rel F x y -> forall y', W_rel F x y' -> y == y'.
intros x y H.
apply H; intros.
 admit. (* mrph *)
apply W_rel_inv with (o:=o) in H5; trivial; destruct H5.
destruct H5.
rewrite H6; clear y' H6.
apply Fm; auto with *; intros.
red; intros.
apply H4; trivial.
rewrite H8 in H6|-*.
auto.
Qed.

Require Import ZFrepl.

  Lemma W_rel_def : forall o a, isOrd o -> a \in TI Wf o -> exists y, W_rel F a y.
intros.
apply W_ind0 with (4:=H0); intros; trivial.
 admit. (*mrph*)
assert (forall z, z \in B x -> uchoice_pred (fun y => W_rel F (cc_app f z) y)).
 intros.
 specialize H4 with (1:=H5).
 destruct H4.
 split; intros.
  rewrite <- H6; trivial.
 split; intros.
  exists x0; trivial.
 apply W_rel_fun with (cc_app f z); trivial.
exists (F x (fun z => uchoice (fun y => W_rel F (cc_app f z) y))).
apply W_rel_intro with o'; intros; trivial.
 apply isOrd_inv with o; trivial.
 admit. (*ext*)
apply uchoice_def; auto.
Qed.

  Lemma W_rel_choice_pred : forall o a, isOrd o -> a \in TI Wf o ->
    uchoice_pred (fun y => W_rel F a y).
split; intros.
 rewrite <- H1; trivial.
split; intros.
 apply W_rel_def with o; trivial.
apply W_rel_fun with a; trivial.
Qed.

  Definition W_rec o := uchoice (fun y => W_rel F o y).

Lemma Wsup_typ : forall o x f,
  isOrd o ->
  x \in A ->
  f \in cc_prod (B x) (fun _ => TI Wf o) ->
  Wsup x (cc_app f) \in TI Wf (osucc o).
intros.
rewrite TI_mono_succ; auto.
apply Wf_intro; trivial.
Qed.

  Lemma W_eqn2 : forall o x f,
    isOrd o ->
    x \in A ->
    f \in cc_prod (B x) (fun _ => TI Wf o) ->
    W_rec (Wsup x (cc_app f)) == F x (fun i => W_rec (cc_app f i)).
intros.
unfold W_rec.
generalize (uchoice_def _ (W_rel_choice_pred _ _ (isOrd_succ _ H) (Wsup_typ _ _ _ H H0 H1))); intro.
apply W_rel_inv with (o:=o) in H2; auto.
destruct H2.
destruct H2.
rewrite H3.
apply Fm; auto with *.
red; intros.
rewrite H6 in H5.
generalize (uchoice_def _ (W_rel_choice_pred _ _ H (cc_prod_elim _ _ _ _ H1 H5))); intro.
specialize H4 with (1:=H5).
rewrite <- W_rel_fun with (1:=H4) (2:=H7).
apply H2; trivial.
rewrite H6; trivial.
Qed.

End Wrel.

  Definition W_assign a :=
    W_rec (fun x g => sup (B x) (fun i => osucc (g i))) a.

  Lemma W_a_ord : forall a, a \in W -> isOrd (W_assign a).
intros.
apply W_ind with (3:=H); intros.
 admit. (* mrph *)
unfold W_assign.
rewrite W_eqn2 with (o:=o'); trivial.
 apply isOrd_supf; auto.
 admit. (*ext *)
 admit. (* ext *)
Qed.

Hint Resolve W_a_ord.

  Lemma W_ord_tot : forall a,
   a \in W ->
   a \in TI Wf (osucc (W_assign a)).
intros.
apply W_ind with (3:=H); intros.
 admit. (* mrph *)
rewrite TI_mono_succ; trivial.
 2:apply W_a_ord; apply (Wi_W (osucc o')); auto.
 2:apply Wsup_typ; trivial.
 apply Wf_intro; trivial.
 rewrite cc_eta_eq with (1:=H2).
 apply cc_prod_intro.
  admit. (*ext*)
  auto.

  intros.
  apply TI_intro with (W_assign (cc_app f x0)).
   apply Fmono_morph; trivial.

   apply W_a_ord.
   apply (Wi_W (osucc o')); auto.
   apply Wsup_typ; trivial.

   unfold W_assign at 2.
   rewrite W_eqn2 with (o:=o'); trivial.
    rewrite sup_ax.
    2:admit. (* ext*)
    exists x0; trivial.
    apply lt_osucc.
    apply W_a_ord.
    rewrite W_def.
    exists o'; auto.
    apply cc_prod_elim with (1:=H2); trivial.

    admit. (* ext *)

   rewrite <- TI_mono_succ; auto.
   apply W_a_ord.
   rewrite W_def; exists o'; trivial.
   apply cc_prod_elim with (1:=H2); trivial.
Qed.

  Definition W_ord :=
    sup W (fun a => osucc (W_assign a)).

  Lemma W_o_o : isOrd W_ord.
apply isOrd_supf; auto.
admit. (* ext *)
Qed.
Hint Resolve W_o_o.
Hint Resolve Fmono_morph.

  Lemma W_post : forall a,
   a \in W ->
   a \in TI Wf W_ord.
intros.
apply TI_intro with (W_assign a); auto.
 unfold W_ord; rewrite sup_ax.
 2:admit. (* ext*)
 exists a; trivial.
 apply lt_osucc; auto.

 rewrite <- TI_mono_succ; auto.
 apply W_ord_tot; trivial.
Qed.

  Lemma W_eqn : W == Wf W.
apply eq_intro; intros.
rewrite W_def in H; destruct H.
apply Wf_mono with (TI Wf x).
 apply Wi_W; trivial.

 rewrite <- TI_mono_succ; auto.
 revert H0; apply TI_incl; auto.

 assert (z \in TI Wf (osucc W_ord)).
  rewrite TI_mono_succ; auto.
  revert H; apply Wf_mono.
  red; intros; apply W_post; trivial.
 rewrite W_def; exists (osucc W_ord); auto.
Qed.

End WithoutKnaster.

(********************)
(*
Section WithKnaster.

Definition W := least_fp Wdom Wf.

Lemma Wtyp : W \incl Wdom.
apply lfp_typ.
apply Wf_fp.
Qed.

Lemma W_eqn : W == Wf W.
symmetry.
apply knaster_tarski.
apply Wf_fp.
Qed.

Lemma Wsup_typ : forall x f,
  x \in A ->
  f \in cc_prod (B x) (fun _ => W) ->
  Wsup x (cc_app f) \in W.
intros.
rewrite W_eqn.
apply Wf_intro; trivial.
Qed.

Lemma W_ind : forall P:set->Prop,
  Proper (eq_set ==> iff) P ->
  (forall x f, x \in A -> f \in cc_prod (B x) (fun _ => W) ->
   (forall i, i \in B x -> P (cc_app f i)) -> P (Wsup x (cc_app f))) ->
  forall a, a \in W -> P a.
intros.
assert (W \incl subset W P).
apply lower_bound.
unfold M'.
apply subset_intro.
 apply power_intro; intros.
 apply Wtyp.
 apply subset_elim1 in H2; trivial.

 red; red; intros.
 unfold Wf in H2.
 rewrite sup_ax in H2; trivial.
 destruct H2.
 rewrite replf_ax in H3; trivial.
 destruct H3.
 rewrite H4; clear z H4.
 assert (x0 \in cc_prod (B x) (fun _ => W)).
  revert x0 H3; apply cc_prod_covariant; auto with *.
  red; intros.
  apply subset_elim1 in H4; trivial.
 apply subset_intro.
  apply Wsup_typ; trivial.

  apply H0; intros; auto.
  specialize cc_prod_elim with (1:=H3) (2:=H5); intros.
  apply subset_elim2 in H6.
  destruct H6.
  rewrite H6; trivial.

apply H2 in H1.
apply subset_elim2 in H1.
destruct H1.
rewrite H1; trivial.
Qed.


Definition W_rel F a y :=
  forall R:set->set->Prop,
  Proper (eq_set ==> eq_set ==> iff) R ->
  (forall x f g,
   ext_fun (B x) g ->
   x \in A ->
   f \in cc_prod (B x) (fun _ => W) ->
   (forall i, i \in B x -> R (cc_app f i) (g i)) ->
   R (Wsup x (cc_app f)) (F x g)) ->
  R a y.

  Instance W_rel_morph :
    forall F, Proper (eq_set ==> eq_set ==> iff) (W_rel F).
Admitted.

Section Wrel.

  Variable F : set -> (set -> set) -> set.
  Hypothesis Fm :
    forall x x' g g', x == x' -> eq_fun (B x) g g' -> F x g == F x' g'.
                                                                             
  Lemma W_rel_intro : forall x f g,
    x \in A -> 
    f \in cc_prod (B x) (fun _ => W) ->
    ext_fun (B x) g ->
    (forall y, y \in B x -> W_rel F (cc_app f y) (g y)) ->
    W_rel F (Wsup x (cc_app f)) (F x g).
red; intros.                                                                 
apply H4; trivial; intros.                                                   
apply H2; trivial.                                                           
Qed.                                                                         
                                                                             
  Lemma W_rel_inv0 : forall a y,
    W_rel F a y ->
    forall x f,
    x \in A ->
    f \in cc_prod (B x) (fun _ => W) ->
    a == Wsup x (cc_app f) ->
    exists2 g,
      ext_fun (B x) g /\
      (forall y, y \in B x -> W_rel F (cc_app f y) (g y)) &                 
      y == F x g.
intros a y Wr.
apply (@proj2 (W_rel F a y)).
apply Wr; intros.
 admit. (* mrph *)

 split.
  apply W_rel_intro; auto.
  intros.
  apply H2; trivial.

  intros.
  apply Wsup_inj in H5; trivial.
  2:revert H1; apply cc_prod_covariant; auto with *.
  2:intros; apply Wtyp.
  2:revert H4; apply cc_prod_covariant; auto with *.
  2:intros; apply Wtyp.
  destruct H5.
  exists g.
   split; intros.
    red; red; intros.
    apply H; trivial.
    rewrite H5; trivial.

    rewrite <- H5 in H7; rewrite <- H6.
    apply H2; trivial.

  apply Fm; trivial.
Qed.

  Lemma W_rel_inv : forall x f y,
    x \in A -> 
    f \in cc_prod (B x) (fun _ => W) ->
    W_rel F (Wsup x (cc_app f)) y ->
    exists2 g,
      ext_fun (B x) g /\
      (forall y, y \in B x -> W_rel F (cc_app f y) (g y)) &                 
      y == F x g.
intros.
apply W_rel_inv0 with (1:=H1); auto with *.
Qed.

  Lemma W_rel_fun :
    forall x y, W_rel F x y -> forall y', W_rel F x y' -> y == y'.
intros x y H.
apply H; intros.
 admit. (* mrph *)
apply W_rel_inv in H4; trivial; destruct H4.
destruct H4.
rewrite H5; clear y' H5.
apply Fm; auto with *; intros.
red; intros.
apply H3; trivial.
rewrite H7 in H5|-*.
auto.
Qed.

Require Import ZFrepl.

  Lemma W_rel_def : forall a, a \in W -> exists y, W_rel F a y.
intros.
apply W_ind with (3:=H); intros.
 admit. (*mrph*)
assert (forall z, z \in B x -> uchoice_pred (fun y => W_rel F (cc_app f z) y)).
 intros.
 specialize H2 with (1:=H3).
 destruct H2.
 split; intros.
  rewrite <- H4; trivial.
 split; intros.
  exists x0; trivial.
 apply W_rel_fun with (cc_app f z); trivial.
exists (F x (fun z => uchoice (fun y => W_rel F (cc_app f z) y))).
apply W_rel_intro; intros; trivial.
 admit. (*ext*)
apply uchoice_def; auto.
Qed.

  Lemma W_rel_choice_pred : forall a, a \in W ->
    uchoice_pred (fun y => W_rel F a y).
split; intros.
 rewrite <- H0; trivial.
split; intros.
 apply W_rel_def; trivial.
apply W_rel_fun with a; trivial.
Qed.

  Definition W_rec o := uchoice (fun y => W_rel F o y).

  Lemma W_eqn2 : forall x f,
    x \in A ->
    f \in cc_prod (B x) (fun _ => W) ->
    W_rec (Wsup x (cc_app f)) == F x (fun i => W_rec (cc_app f i)).
intros.
unfold W_rec.
generalize (uchoice_def _ (W_rel_choice_pred _ (Wsup_typ _ _ H H0))); intro.
apply W_rel_inv in H1; trivial.
destruct H1.
destruct H1.
rewrite H2.
apply Fm; auto with *.
red; intros.
rewrite H5 in H4.
generalize (uchoice_def _ (W_rel_choice_pred _ (cc_prod_elim _ _ _ _ H0 H4))); intro.
specialize H3 with (1:=H4).
rewrite <- W_rel_fun with (1:=H3) (2:=H6).
apply H1; trivial.
rewrite H5; trivial.
Qed.

End Wrel.

  Definition W_assign a :=
    W_rec (fun x g => sup (B x) (fun i => osucc (g i))) a.

  Lemma W_a_ord : forall a, a \in W -> isOrd (W_assign a).
intros.
apply W_ind with (3:=H); intros.
 admit. (* mrph *)
unfold W_assign.
rewrite W_eqn2; trivial.
 apply isOrd_supf; auto.
 admit. (*ext *)

 admit. (* ext *)
Qed.

Hint Resolve W_a_ord.

  Lemma W_ord_tot : forall a,
   a \in W ->
   a \in TI Wf (osucc (W_assign a)).
intros.
apply W_ind with (3:=H); intros.
 admit. (* mrph *)
rewrite TI_mono_succ; trivial.
 apply Wf_intro; trivial.
 2:apply W_a_ord; apply Wsup_typ; trivial.
 rewrite cc_eta_eq with (1:=H1).
 apply cc_prod_intro.
  admit. (*ext*)
  auto.

  intros.
  apply TI_intro with (W_assign (cc_app f x0)).
   apply Fmono_morph; trivial.

   apply W_a_ord; apply Wsup_typ; trivial.

   unfold W_assign at 2.
   rewrite W_eqn2; trivial.
   2:admit. (* ext*)
   rewrite sup_ax.
   2:admit. (* ext*)
   exists x0; trivial.
   apply lt_osucc.
   apply W_a_ord.
   apply cc_prod_elim with (1:=H1); trivial.

   rewrite <- TI_mono_succ; auto.
   apply W_a_ord.
   apply cc_prod_elim with (1:=H1); trivial.
Qed.

  Definition W_ord :=
    sup W (fun a => osucc (W_assign a)).

  Lemma W_o_o : isOrd W_ord.
apply isOrd_supf; auto.
admit. (* ext *)
Qed.
Hint Resolve W_o_o.
Hint Resolve Fmono_morph.

  Lemma W_post : forall a,
   a \in W ->
   a \in TI Wf W_ord.
intros.
apply TI_intro with (W_assign a); auto.
 unfold W_ord; rewrite sup_ax.
 2:admit. (* ext*)
 exists a; trivial.
 apply lt_osucc; auto.

 rewrite <- TI_mono_succ; auto.
 apply W_ord_tot; trivial.
Qed.

  Lemma W_o_fix : W == TI Wf W_ord.
apply eq_intro; intros.
 apply W_post; trivial.

 revert z H.
 pattern W_ord; apply isOrd_ind; auto.
 intros.
 apply TI_elim in H2; auto.
 destruct H2.
 rewrite W_eqn.
 revert z H3.
 apply Wf_mono.
 red; eauto.
Qed.
*)