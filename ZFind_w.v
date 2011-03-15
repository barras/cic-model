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

Lemma Wf_elim : forall a X,
  a \in Wf X ->
  exists2 x, x \in A &
  exists2 f, f \in cc_prod (B x) (fun _ => X) &
  a == Wsup x (cc_app f).
intros.
unfold Wf in H.
rewrite sup_ax in H; trivial.
destruct H.
rewrite replf_ax in H0; trivial.
destruct H0.
eauto.
Qed.

Lemma Wf_mono : Proper (incl_set ==> incl_set) Wf.
do 3 red; intros.
apply Wf_elim in H0; destruct H0 as (i,?,(f,?,?)).
rewrite H2; apply Wf_intro; trivial.
clear H2; revert f H1.
apply cc_prod_covariant; auto with *.
Qed.
Hint Resolve Wf_mono.

Lemma Wf_typ : forall X,
  X \incl Wdom -> Wf X \incl Wdom.
red; intros.
apply Wf_elim in H0; destruct H0 as (x,?,(f,?,?)).
rewrite H2.
apply Wsup_typ_gen; trivial.
clear H2; revert f H1.
apply cc_prod_covariant; auto with *.
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
  exists2 x, x \in A &
  exists2 f, f \in cc_prod (B x) (fun _ => TI Wf o') &
  a == Wsup x (cc_app f).
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
destruct H0 as (w',?,(x,?,(f,?,?))).
symmetry in H3; apply in_reg with (1:=H3).
apply Wf_intro; trivial.
rewrite (cc_eta_eq _ _ _ H2).
apply cc_prod_intro; intros; auto.
 red; red; intros.
 rewrite H5; reflexivity.

 apply subset_intro.
  apply Wtyp.
  apply Wi_W with w'.
   apply isOrd_inv with o; trivial.
   apply cc_prod_elim with (1:=H2); trivial.

  intros.
  apply Wf_elim in H6.
  destruct H6 as (x',?,(f',?,?)).
  rewrite H8 in H3.
  apply Wsup_inj in H3; trivial.
   destruct H3.
   rewrite H9.
   apply cc_prod_elim with (1:=H7).
   rewrite <- H3; trivial.

   revert H2; apply cc_prod_covariant; auto with *.
   transitivity W; [apply Wi_W|apply Wtyp].
   apply isOrd_inv with o; trivial.

   revert H7; apply cc_prod_covariant; auto with *.
Qed.
Hint Resolve Wf_subterm.

Lemma Wsup_typ : forall o x f,
  isOrd o ->
  x \in A ->
  f \in cc_prod (B x) (fun _ => TI Wf o) ->
  Wsup x (cc_app f) \in TI Wf (osucc o).
intros.
rewrite TI_mono_succ; auto.
apply Wf_intro; trivial.
Qed.

Lemma W_ind : forall (P:set->Prop),
  Proper (eq_set ==> iff) P ->
  (forall o' x f, isOrd o' -> x \in A -> f \in cc_prod (B x) (fun _ => TI Wf o') ->
   (forall i, i \in B x -> P (cc_app f i)) -> P (Wsup x (cc_app f))) ->
  forall a, a \in W -> P a.
intros.
unfold W in H1; rewrite Ffix_def in H1; auto.
destruct H1.
revert a H2.
apply isOrd_ind with (2:=H1); intros.
apply TI_Wf_elim in H5; trivial.
destruct H5 as (o',?,(x',?,(f',?,?))).
rewrite H8; clear a H8.
apply H0 with o'; trivial.
 apply isOrd_inv with y; trivial.

 intros.
 apply H4 with o'; trivial.
 apply cc_prod_elim with (1:=H7); trivial.
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
