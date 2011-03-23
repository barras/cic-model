Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFord ZFfix ZFstable.
Require Import ZFcoc ZFlist.
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


(* The intended type operator *)
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

Lemma cc_prod_stable : forall dom F,
  morph2 F ->
  (forall x, stable (fun y => F y x)) ->
  stable (fun y => cc_prod dom (F y)).
intros dom F Fm Fs.
assert (Hm : morph1 (fun y => cc_prod dom (F y))).
 do 2 red; intros.
 apply cc_prod_ext; auto with *.
 red; intros; apply Fm; auto.
red; red ;intros.
destruct inter_wit with (2:=H) as (w,H0); trivial.
assert (forall x, x \in X -> z \in cc_prod dom (F x)).
 intros.
 apply inter_elim with (1:=H).
 rewrite replf_ax; auto.
 exists x; auto with *.
clear H.
assert (z \in cc_prod dom (F w)) by auto.
rewrite (cc_eta_eq _ _ _ H).
apply cc_prod_intro.
 red; red; intros; apply cc_app_morph; auto with *.

 red; red; intros; apply Fm; auto with *.

 intros.
 apply Fs.
 apply inter_intro.
  intros.
  rewrite replf_ax in H3; auto.
  2:red;red;intros;apply Fm; auto with *.
  destruct H3.
  rewrite H4; apply H1 in H3.
  apply cc_prod_elim with (1:=H3); trivial.

  exists (F w x); rewrite replf_ax.
  2:red;red;intros; apply Fm; auto with *.
  eauto with *.
Qed.

Lemma W_F_stable : stable W_F.
unfold W_F.
apply sigma_stable; auto with *.
 do 2 red; reflexivity.

 do 3 red; intros; apply cc_prod_ext; auto with *.
 red; trivial.

 apply cst_stable.

 intro.
 apply cc_prod_stable.
  do 3 red;auto.

  intros _; apply id_stable.
Qed.

Let tys : forall x X, x \in W_F X -> snd x \in cc_prod (B (fst x)) (fun _ => X).
intros.
apply snd_typ_sigma with (y:=fst x) in H; auto with *.
red; red; intros.
apply cc_prod_ext; auto with *.
red; auto with *.
Qed.

Lemma WF_eta : forall X x,
  x \in W_F X ->
  x == couple (fst x) (cc_lam (B (fst x)) (cc_app (snd x))).
intros.
transitivity (couple (fst x) (snd x)).
 eapply surj_pair with (1:=subset_elim1 _ _ _ H).

 apply couple_morph; auto with *.
 eapply cc_eta_eq with (1:=tys _ _ H).
Qed.


(* The construction domain and the constructor *)
Definition Wdom := rel (List (sup A B)) A.

Definition Wsup f x :=
  union2 (singl (couple Nil (fst x)))
   (sup (B (fst x)) (fun y =>
      replf (f (cc_app (snd x) y))
        (fun p => couple (Cons y (fst p)) (snd p)))).

Instance Wsup_morph :
  Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) Wsup.
do 3 red; intros.
unfold Wsup.
apply union2_morph.
 rewrite H0; reflexivity.

 apply sup_morph.
  rewrite H0; reflexivity.
  red; intros.
  apply replf_morph_raw; auto.
   apply H; rewrite H0; rewrite H2; reflexivity.

   red; intros.
   rewrite H2; rewrite H3; reflexivity.
Qed.

Lemma wext1 : forall i y,
  ext_fun y (fun p => couple (Cons i (fst p)) (snd p)).
do 2 red; intros.
rewrite H0; reflexivity.
Qed.

Lemma wext2 : forall X f g,
  morph1 f ->
  ext_fun X (fun y =>
     replf (f (cc_app g y)) (fun p => couple (Cons y (fst p)) (snd p))).
do 2 red; intros.
apply replf_morph_raw; auto.
 rewrite H1; reflexivity.

 red; intros.
 rewrite H1; rewrite H2; reflexivity.
Qed.
Hint Resolve wext1 wext2.

Lemma Wsup_def :
  forall x f p,
  morph1 f ->
  (p \in Wsup f x <->
   p == couple Nil (fst x) \/
   exists2 i, i \in B (fst x) &
   exists2 q, q \in f (cc_app (snd x) i) &
   p == couple (Cons i (fst q)) (snd q)).
intros x f p fm; intros.
unfold Wsup.
split; intros.
 apply union2_elim in H; destruct H;[left|right].
  apply singl_elim in H; trivial.

  rewrite sup_ax in H; auto.
  destruct H as (i,?,?); exists i; trivial.
  rewrite replf_ax in H0; trivial.

 destruct H as [eqp|(i,?,(q,?,eqp))]; rewrite eqp; clear eqp.  
  apply union2_intro1.
  apply singl_intro.

  apply union2_intro2.
  rewrite sup_ax; auto.
  exists i; trivial.
  rewrite replf_ax; trivial.
  exists q; auto with *.
Qed.

Lemma Wsup_hd_prop : forall a f x,
  morph1 f ->
  (couple Nil a \in Wsup f x <-> a == fst x).
split; intros.
 apply union2_elim in H0; destruct H0.
  apply singl_elim in H0.
  apply couple_injection in H0; destruct H0; trivial.

  rewrite sup_ax in H0; auto.
  destruct H0.
  rewrite replf_ax in H1; trivial.
  destruct H1.
  apply couple_injection in H2; destruct H2 as (H2,_).
   apply discr_mt_pair in H2; contradiction.

 rewrite H0.
 unfold Wsup.
 apply union2_intro1.
 apply singl_intro.
Qed.

Lemma Wsup_tl_prop : forall X i l a f x,
  x \in W_F X ->
  morph1 f ->
  (forall b, b \in X -> f b \in Wdom) ->
  (couple (Cons i l) a \in Wsup f x <->
   i \in B (fst x) /\ couple l a \in f (cc_app (snd x) i)).
intros X i l a f x H mf tyf.
assert (tyx : fst x \in A).
 apply fst_typ_sigma in H; trivial.
split; intros.
 apply union2_elim in H0; destruct H0.
  apply singl_elim in H0.
  apply couple_injection in H0; destruct H0 as (H0,_).
  symmetry in H0.
  apply discr_mt_pair in H0; contradiction.

  rewrite sup_ax in H0; auto.
  destruct H0.
  rewrite replf_ax in H1; trivial.
  destruct H1.
  apply couple_injection in H2; destruct H2.
  apply couple_injection in H2; destruct H2.
  rewrite H2.
  split; trivial.
  assert (ty := cc_prod_elim _ _ _ _ (tys _ _ H) H0).
  apply tyf in ty.
  rewrite H4; rewrite H3.
  rewrite <- surj_pair  with (List (sup A B)) A; trivial.
  apply power_elim with (1:=ty); trivial.

 destruct H0.
 unfold Wsup.
 apply union2_intro2.
 rewrite sup_ax; auto.
 exists i; trivial.
 rewrite replf_ax; trivial.
 exists (couple l a); trivial.
 rewrite fst_def.
 rewrite snd_def; reflexivity.
Qed.

Lemma Wsup_inj : forall X Y f f' x x',
  morph1 f ->
  morph1 f' ->
  (forall y, y \in X -> f y \in Wdom) -> 
  (forall y, y \in Y -> f' y \in Wdom) -> 
  x \in W_F X ->
  x' \in W_F Y ->
  (forall y y', y \in X -> y' \in Y -> f y == f' y' -> y == y') ->
  Wsup f x == Wsup f' x' -> x == x'.
intros X Y f f' x x' fm f'm tyf tyf' H H0 injf H1.
assert (fst x == fst x').
 generalize (Wsup_hd_prop (fst x) f x fm); intro.
 generalize (Wsup_hd_prop (fst x) f' x' f'm); intro.
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
  assert (f (cc_app (snd x) x0) \incl prodcart (List (sup A B)) A).
   red; intros.
   apply power_elim with (2:=H8).
   apply tyf.
   apply cc_prod_elim with (1:=tys _ _ H); trivial.
  assert (f' (cc_app (snd x') x'0) \incl prodcart (List (sup A B)) A).
   red; intros.
   apply power_elim with (2:=H9); trivial.
   apply tyf'.
   apply cc_prod_elim with (1:=tys _ _ H0); trivial.
  generalize (fun z l => Wsup_tl_prop _ x0 l z _ _ H fm tyf); intros.
  generalize (fun z l => Wsup_tl_prop _ x'0 l z _ _ H0 f'm tyf'); intros.
  apply injf.
   apply cc_prod_elim with (1:=tys _ _ H); trivial.
   apply cc_prod_elim with (1:=tys _ _ H0); trivial.
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

Lemma Wsup_typ_gen : forall X x f,
  morph1 f ->
  (forall y, y \in X -> f y \in Wdom) ->
  x \in W_F X ->
  Wsup f x \in Wdom.
intros.
apply power_intro; intros.
rewrite Wsup_def in H2; trivial.
destruct H2 as [eqz|(i,?,(q,?,eqz))]; rewrite eqz; clear z eqz.
 apply couple_intro; trivial.
  apply Nil_typ.
  apply fst_typ_sigma in H1; trivial.

 assert (q \in prodcart (List (sup A B)) A).
  apply power_elim with (2:=H3).
  apply H0.
  apply cc_prod_elim with (1:=tys _ _ H1); trivial.
 apply couple_intro.
  apply Cons_typ.
   rewrite sup_ax.
   2:red; red; intros; apply Bmorph; trivial.
   exists (fst x); trivial.
   apply fst_typ_sigma in H1; trivial.

   apply fst_typ with (1:=H4).

  apply snd_typ with (1:=H4).
Qed.

(* The type operator on the construction domain *)
Definition Wf X := replf (W_F X) (Wsup (fun x =>x)).

Instance idm : Proper (eq_set ==> eq_set) (fun x => x).
do 2 red; intros; auto.
Qed.

Lemma wfext1 : forall X, ext_fun (W_F X) (Wsup (fun x => x)).
do 2 red; intros.
rewrite H0; reflexivity.
Qed.
Hint Resolve wfext1.

Lemma Wf_intro : forall x X,
  x \in W_F X ->
  Wsup (fun x => x) x \in Wf X.
intros.
unfold Wf.
rewrite replf_ax; trivial.
exists x; auto with *.
Qed.

Lemma Wf_elim : forall a X,
  a \in Wf X ->
  exists2 x, x \in W_F X &
  a == Wsup (fun x => x) x.
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
Hint Resolve Wf_mono Fmono_morph.

Lemma Wf_typ : forall X,
  X \incl Wdom -> Wf X \incl Wdom.
red; intros.
apply Wf_elim in H0; destruct H0 as (x,?,?).
rewrite H1.
apply Wsup_typ_gen with X; auto with *.
Qed.
Hint Resolve Wf_typ.

Lemma Wf_stable : forall X,
  X \incl power Wdom ->
  inter (replf X Wf) \incl Wf (inter X).
red; intros X Xty z H.
unfold Wf.
assert (forall a, a \in X -> z \in Wf a).
 intros.
 apply inter_elim with (1:=H).
 rewrite replf_ax.
 2:red;red;intros;apply Fmono_morph; trivial.
 exists a; auto with *.
rewrite replf_ax.
2:red;red;intros;apply Wsup_morph; trivial; apply idm.
destruct inter_wit with (2:=H).
 apply Fmono_morph; trivial.
assert (z \in Wf x); auto.
apply Wf_elim in H2.
destruct H2.
exists x0; auto.
apply W_F_stable.
apply inter_intro.
 intros.
 rewrite replf_ax in H4.
 2:red;red;intros;apply Fmono_morph; auto.
 2:apply W_F_mono.
 destruct H4.
 rewrite H5; clear y H5.
 specialize H0 with (1:=H4).
 apply Wf_elim in H0; destruct H0.
 rewrite H3 in H5; apply Wsup_inj with (X:=x) (Y:=x1)in H5; trivial;
    try (apply idm).
  rewrite H5; trivial.

  intros; apply power_elim with (1:=Xty _ H1); trivial.

  intros; apply power_elim with (1:=Xty _ H4); trivial.

 exists (W_F x).
 rewrite replf_ax.
 2:red;red;intros;apply Fmono_morph;auto.
 2:apply W_F_mono.
 exists x; auto with *.
Qed.
Hint Resolve Wf_stable.

(* The fixpoint *)

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
  a == Wsup (fun x => x) x.
intros.
apply TI_elim in H0; trivial.
2:apply Fmono_morph; trivial.
destruct H0.
apply Wf_elim in H1.
eauto.
Qed.

Lemma Wsup_typ : forall o x,
  isOrd o ->
  x \in W_F (TI Wf o) ->
  Wsup (fun x => x) x \in TI Wf (osucc o).
intros.
rewrite TI_mono_succ; auto.
apply Wf_intro; trivial.
Qed.

Lemma W_ind : forall (P:set->Prop),
  Proper (eq_set ==> iff) P ->
  (forall o' x, isOrd o' -> x \in W_F (TI Wf o') ->
   (forall i, i \in B (fst x) -> P (cc_app (snd x) i)) ->
   P (Wsup (fun x => x) x)) ->
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




Parameter WFm : (set -> set) -> set -> set.
Parameter WFmm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) WFm.
Parameter WFmtyp : forall X Y f x,
  (forall a, a \in X -> f a \in Y) ->
  x \in W_F X ->
  WFm f x \in W_F Y.



  Definition trad := Fix_rec Wf Wdom WFm.

Let Gm_prf : forall (x x' : set) (g g' : set -> set),
 x \in Wdom ->
 eq_fun (fsub Wf Wdom x) g g' -> x == x' -> WFm g x == WFm g' x'.
admit.
(*intros.
apply Wsupi_morph; trivial.
admit.*)
Qed.

Instance trad_morph : morph1 trad.
red; red; intros.
unfold trad.
unfold Fix_rec.
apply uchoice_morph_raw; red; intros.
apply Ffix_rel_morph; trivial.
Qed.

  Lemma trad_ok : forall o,
    isOrd o ->
    forall x,
    x \in TI Wf o ->
    trad x \in TI W_F o.
intros o oo.
apply isOrd_ind with (2:=oo); intros.
unfold trad.
rewrite Fr_eqn with (o:=y); auto.
fold trad.
apply TI_Wf_elim in H2; trivial.
destruct H2 as (o',?,(x',?,?)).
apply TI_intro with o'; auto.
 apply Fmono_morph; apply W_F_mono.

 apply WFmtyp with (TI Wf o'); auto with *.

 rewrite H4.
 rewrite <- TI_mono_succ; auto.
 2:apply isOrd_inv with y; trivial.
 apply Wsup_typ; trivial.
 apply isOrd_inv with y; trivial.
Qed.




Definition Wsupi f a :=
  union (subset Wdom (fun b => Wsup f b == a)).


Instance Wsupi_morph :
  Proper ((eq_set==>eq_set) ==> eq_set ==> eq_set) Wsupi.
do 3 red; intros.
unfold Wsupi.
apply union_morph.
apply subset_morph; auto with *.
red; intros.
rewrite H; rewrite H0; reflexivity.
Qed.

Lemma Wsupi_inj : forall f f' a a',
  (forall x x', f x == f' x' -> x == x') ->
  Wsupi f a == Wsupi f' a' -> a == a'.
Admitted.

Lemma Wsupi_inv : forall f a,
  Wsupi f (Wsup f a) == a.
Admitted.

Lemma Wsupi_typ : forall X Y f x,
  morph1 f ->
  (forall a, a \in X -> f a \in Y) ->
  x \in Wf X ->
  Wsupi f x \in W_F Y.
intros.
apply Wf_elim in H1.
destruct H1.
rewrite H2.
admit.
Qed.

  Definition trad := Fix_rec Wf Wdom Wsupi.

  Definition trad := Fix_rec Wf Wdom
    (fun g x => couple (hd x)
       (cc_lam (B (hd x)) (fun i => g (tl x i)))).

Let Gm_prf : forall (x x' : set) (g g' : set -> set),
 x \in Wdom ->
 eq_fun (fsub Wf Wdom x) g g' -> x == x' -> Wsupi g x == Wsupi g' x'.
intros.
apply Wsupi_morph; trivial.
admit.
Qed.

Instance trad_morph : morph1 trad.
red; red; intros.
unfold trad.
unfold Fix_rec.
apply uchoice_morph_raw; red; intros.
apply Ffix_rel_morph; trivial.
Qed.

  Lemma trad_ok : forall o,
    isOrd o ->
    forall x,
    x \in TI Wf o ->
    trad x \in TI W_F o.
intros o oo.
apply isOrd_ind with (2:=oo); intros.
unfold trad.
rewrite Fr_eqn with (o:=y); auto.
fold trad.
apply TI_Wf_elim in H2; trivial.
destruct H2 as (o',?,(x',?,?)).
apply TI_intro with o'; auto.
 apply Fmono_morph; apply W_F_mono.

 apply Wsupi_typ with (TI Wf o'); auto with *.

 rewrite H4.
 rewrite <- TI_mono_succ; auto.
 2:apply isOrd_inv with y; trivial.
 apply Wsup_typ; trivial.
 apply isOrd_inv with y; trivial.
Qed.

  Lemma trad_inj : forall o,
    isOrd o ->
    forall x y o', x \in TI Wf o ->
    isOrd o' ->
    y \in TI Wf o' ->
    trad x == trad y -> x == y.
intros o oo.
apply isOrd_ind with (2:=oo).
intros o1 ord1 _ Hrec x y o2 xty ord2 yty eqtr.
unfold trad in eqtr.
rewrite Fr_eqn with (o:=o1) in eqtr; auto.
rewrite Fr_eqn with (o:=o2) in eqtr; auto.
apply TI_Wf_elim in xty; trivial.
destruct xty as (o1', ?, (c1,?,?)).
apply TI_Wf_elim in yty; trivial.
destruct yty as (o2', ?, (c2,?,?)).
apply Wsupi_inj in eqtr; trivial.
intros.
admit.
Qed.

  Definition trad1 o y :=
    union (subset (TI Wf o) (fun x => trad x == y)).

  Lemma trad_surj : forall o,
    isOrd o ->
    forall y,
    y \in TI W_F o ->
    trad1 o y \in TI Wf o /\ trad (trad1 o y) == y.
intros o oo.
apply isOrd_ind with (2:=oo); intros o'; intros.
apply TI_elim in H2; auto with *.
2:apply Fmono_morph; apply W_F_mono.
destruct H2.
pose (y' := Wsupi trad y).
assert (tyy' : y' \in W_F (TI Wf x)).
 unfold y'.
 eapply Wsupi_typ.


 apply couple_intro_sigma; auto with *.
  do 2 red; intros.
  apply cc_prod_ext; auto with *.
  red; reflexivity.

  apply fst_typ_sigma in H3; trivial.

  apply cc_prod_intro; intros.
   do 2 red; intros.
   unfold trad1. (* trad1 ext*)
   apply union_morph.
   apply subset_morph; auto with *.
   red; intros.
   rewrite H5; reflexivity.

   do 2 red; reflexivity.

   destruct H1 with (1:=H2) (y:=cc_app (snd y) x0); trivial.
   apply cc_prod_elim with (1:=tys _ _ H3); trivial.
assert (tyx' : Wsup y' \in TI Wf o').
 apply TI_intro with x; trivial.
  apply Fmono_morph; trivial.
 apply Wf_intro; trivial.
assert (trad (Wsup y') == y).
 unfold trad; rewrite Fr_eqn with (o:=o'); auto with *.
 rewrite WF_eta with (1:=H3).
 assert (hd (Wsup y') == fst y).
  rewrite hd_eq with (1:=tyy').
  unfold y'; rewrite fst_def; reflexivity.
 apply couple_morph; trivial.
 apply cc_lam_ext.
  rewrite H4; reflexivity.
 red; intros.
 destruct H1 with (1:=H2) (y:=cc_app (snd y) x0).
  apply cc_prod_elim with (1:=tys _ _ H3); trivial.
  rewrite <- H4; trivial.

  fold trad.
  rewrite tl_eq with (X:=TI Wf x); auto. 
   unfold y'; rewrite snd_def.
   rewrite cc_beta_eq.
    rewrite H8.
    rewrite H6; reflexivity.

    red; red; intros.
    unfold trad1. (* trad1 ext*)
    apply union_morph.
    apply subset_morph; auto with *.
    red; intros.
    rewrite H10; reflexivity.

    rewrite <- H4; trivial.

    transitivity W; [apply Wi_W|apply Wtyp].
    apply isOrd_inv with o'; trivial.

    unfold y'; rewrite fst_def.
    rewrite <- H4; trivial.
assert (trad1 o' y == Wsup y').
 apply union_subset_singl with (y:=Wsup y') (y':=Wsup y');
   intros; auto with *.
 rewrite <- H8 in H7; apply trad_inj with (o:=o') (o':=o') in H7; trivial. 
rewrite H5; auto.



; trivial.
 in eqtr.

apply couple_injection in eqtr; destruct eqtr as (eqhd, eqtl).
rewrite H1 in eqhd|-*; rewrite H4 in eqhd|-*.
apply Wsup_morph.
rewrite hd_eq with (1:=H0) in eqhd.
rewrite hd_eq with (1:=H3) in eqhd.
rewrite (WF_eta _ _ H0).
rewrite (WF_eta _ _ H3).
apply couple_morph; trivial.
apply cc_lam_ext; intros; auto.
red; intros.
rewrite <- tl_eq with (2:=H0); trivial.
2:transitivity W;[apply Wi_W|apply Wtyp]; eauto using isOrd_inv.
rewrite <- tl_eq with (2:=H3); trivial.
2:transitivity W;[apply Wi_W|apply Wtyp]; eauto using isOrd_inv.
2:rewrite <- H6; rewrite <- eqhd; trivial.
assert (cc_app (cc_lam (B (hd x)) (fun i => trad (tl x i))) x0 ==
        cc_app (cc_lam (B (hd y)) (fun i => trad (tl y i))) x').
 apply cc_app_morph; trivial.
rewrite cc_beta_eq in H7.
rewrite cc_beta_eq in H7.
rewrite <- H1; rewrite <- H4; apply Hrec with o1' o2'; trivial.
 rewrite H1; rewrite tl_eq with (2:=H0); trivial.
 2:transitivity W;[apply Wi_W|apply Wtyp]; eauto using isOrd_inv.
 apply cc_prod_elim with (1:=tys _ _ H0); trivial.

 apply isOrd_inv with o2; trivial.

 rewrite H4; rewrite tl_eq with (2:=H3); trivial.
 2:transitivity W;[apply Wi_W|apply Wtyp]; eauto using isOrd_inv.
 apply cc_prod_elim with (1:=tys _ _ H3); trivial.
 rewrite <- H6; rewrite <- eqhd; trivial.

 rewrite <- H6; rewrite <- eqhd; trivial.

 do 2 red; intros.
 apply trad_morph.
 apply tlm; auto with *.

 rewrite <- H6; rewrite H4; rewrite hd_eq with (1:=H3); rewrite <- eqhd;
   trivial.

 do 2 red; intros.
 apply trad_morph.
 apply tlm; auto with *.

 rewrite H1; rewrite hd_eq with (1:=H0); trivial.
Qed.


(***)

Definition hd x := union (subset A (fun a => couple Nil a \in x)).

Instance hdm : morph1 hd.
do 2 red; intros.
unfold hd.
apply union_morph.
apply subset_morph; auto with *.
red; intros.
rewrite H; reflexivity.
Qed.

Lemma hd_eq : forall x X, x \in W_F X -> hd (Wsup x) == fst x.
intros; unfold hd.
apply union_subset_singl with (fst x); auto with *.
 apply fst_typ_sigma in H; trivial.

 apply Wsup_hd_prop; reflexivity.

 intros.
 apply Wsup_hd_prop in H2.
 apply Wsup_hd_prop in H3.
 rewrite H2; rewrite H3; reflexivity.
Qed.

Definition tl x i :=
  subset (prodcart (List (sup A B)) A)
    (fun p => couple (Cons i (fst p)) (snd p) \in x).

Instance tlm : morph2 tl.
do 3 red; intros.
unfold tl.
apply subset_morph; auto with *.
red; intros.
rewrite H; rewrite H0; reflexivity.
Qed.

Lemma tl_typ : forall x i, x \in Wdom -> tl x i \in Wdom.
intros.
unfold tl.
apply power_intro; intros.
apply subset_elim1 in H0; trivial.
Qed.

Lemma tl_eq : forall X x i, X \incl Wdom -> x \in W_F X ->
  i \in B (fst x) ->
  tl (Wsup x) i == cc_app (snd x) i.
intros.
unfold tl.
symmetry; apply subset_ext; intros.
 apply Wsup_tl_prop in H3.
  destruct H3.
  rewrite (surj_pair _ _ _ H2); trivial.

  revert H0; apply W_F_mono; trivial.

 apply power_elim with (2:=H2).
 apply H.
 apply cc_prod_elim with (1:=tys _ _ H0); trivial.

 exists x0; auto with *.
 apply Wsup_tl_prop.
  revert H0; apply W_F_mono; trivial.

  split; trivial.
  assert (x0 \in prodcart (List (sup A B)) A).
   apply power_elim with (2:=H2).
   apply H.
   apply cc_prod_elim with (1:=tys _ _ H0); trivial.
  rewrite <- (surj_pair _ _ _ H3); trivial.
Qed.

  Definition trad := Fix_rec Wf Wdom
    (fun g x => couple (hd x)
       (cc_lam (B (hd x)) (fun i => g (tl x i)))).

Let Gm_prf :
 forall (x0 x' : set) (g g' : set -> set),
   x0 \in Wdom ->
   eq_fun (fsub Wf Wdom x0) g g' ->
   x0 == x' ->
   couple (hd x0) (cc_lam (B (hd x0)) (fun i : set => g (tl x0 i))) ==
   couple (hd x') (cc_lam (B (hd x')) (fun i : set => g' (tl x' i))).
intros.
apply couple_morph.
 rewrite H1; reflexivity.

 apply cc_lam_ext.
  rewrite H1; reflexivity.

  red; intros.
  apply H0.
   apply subset_intro; intros.
    apply tl_typ; trivial.

    apply Wf_elim in H5.
    destruct H5.
    rewrite H6.
    assert (x \in B (fst x1)).
     rewrite H6 in H2; rewrite hd_eq with (1:=H5) in H2; trivial.
    rewrite tl_eq with (X:=X); trivial.
    apply cc_prod_elim with (1:=tys _ _ H5); trivial.

   apply tlm; trivial.
Qed.
Hint Resolve Gm_prf.

Instance trad_morph : morph1 trad.
red; red; intros.
unfold trad.
unfold Fix_rec.
apply uchoice_morph_raw; red; intros.
apply Ffix_rel_morph; trivial.
Qed.

  Lemma trad_ok : forall o,
    isOrd o ->
    forall x,
    x \in TI Wf o ->
    trad x \in TI W_F o.
intros o oo.
apply isOrd_ind with (2:=oo); intros.
unfold trad.
rewrite Fr_eqn with (o:=y); auto.
apply TI_Wf_elim in H2; trivial.
destruct H2 as (o',?,(x',?,?)).
apply TI_intro with o'; auto.
 apply Fmono_morph; apply W_F_mono.

 assert (x \in Wf (TI Wf o')).
  rewrite <- TI_mono_succ; auto.
  2:apply isOrd_inv with y; trivial.
  rewrite H4; apply Wsup_typ; trivial.
  apply isOrd_inv with y; trivial.
 assert (hd x == fst x').
  rewrite H4.
  rewrite hd_eq with (TI Wf o'); auto with *.
 apply couple_intro_sigma.
  red; red; intros; apply cc_prod_ext; auto with *.
  red; reflexivity.

  rewrite H6.
  apply fst_typ_sigma in H3; trivial.

  apply cc_prod_intro; intros.
   red; red; intros.
   apply uchoice_morph_raw.
   2:red;red;reflexivity.
   red; intros.
   apply Ffix_rel_morph; trivial.
   apply tlm; auto with *.

  apply H1; trivial.
  rewrite H4.

  rewrite tl_eq with (TI Wf o'); trivial.
   apply tys in H3.
   apply cc_prod_elim with (1:=H3); trivial.
   rewrite <- H6; trivial.

   transitivity W; [apply Wi_W; trivial|apply Wtyp].
   apply isOrd_inv with y; trivial.

   rewrite <- H6; trivial.
Qed.

  Lemma trad_inj : forall o,
    isOrd o ->
    forall x y o', x \in TI Wf o ->
    isOrd o' ->
    y \in TI Wf o' ->
    trad x == trad y -> x == y.
intros o oo.
apply isOrd_ind with (2:=oo).
intros o1 ord1 _ Hrec x y o2 xty ord2 yty eqtr.
unfold trad in eqtr.
rewrite Fr_eqn with (o:=o1) in eqtr; auto.
rewrite Fr_eqn with (o:=o2) in eqtr; auto.
apply couple_injection in eqtr; destruct eqtr as (eqhd, eqtl).
apply TI_Wf_elim in xty; trivial.
destruct xty as (o1', ?, (c1,?,?)).
apply TI_Wf_elim in yty; trivial.
destruct yty as (o2', ?, (c2,?,?)).
rewrite H1 in eqhd|-*; rewrite H4 in eqhd|-*.
apply Wsup_morph.
rewrite hd_eq with (1:=H0) in eqhd.
rewrite hd_eq with (1:=H3) in eqhd.
rewrite (WF_eta _ _ H0).
rewrite (WF_eta _ _ H3).
apply couple_morph; trivial.
apply cc_lam_ext; intros; auto.
red; intros.
rewrite <- tl_eq with (2:=H0); trivial.
2:transitivity W;[apply Wi_W|apply Wtyp]; eauto using isOrd_inv.
rewrite <- tl_eq with (2:=H3); trivial.
2:transitivity W;[apply Wi_W|apply Wtyp]; eauto using isOrd_inv.
2:rewrite <- H6; rewrite <- eqhd; trivial.
assert (cc_app (cc_lam (B (hd x)) (fun i => trad (tl x i))) x0 ==
        cc_app (cc_lam (B (hd y)) (fun i => trad (tl y i))) x').
 apply cc_app_morph; trivial.
rewrite cc_beta_eq in H7.
rewrite cc_beta_eq in H7.
rewrite <- H1; rewrite <- H4; apply Hrec with o1' o2'; trivial.
 rewrite H1; rewrite tl_eq with (2:=H0); trivial.
 2:transitivity W;[apply Wi_W|apply Wtyp]; eauto using isOrd_inv.
 apply cc_prod_elim with (1:=tys _ _ H0); trivial.

 apply isOrd_inv with o2; trivial.

 rewrite H4; rewrite tl_eq with (2:=H3); trivial.
 2:transitivity W;[apply Wi_W|apply Wtyp]; eauto using isOrd_inv.
 apply cc_prod_elim with (1:=tys _ _ H3); trivial.
 rewrite <- H6; rewrite <- eqhd; trivial.

 rewrite <- H6; rewrite <- eqhd; trivial.

 do 2 red; intros.
 apply trad_morph.
 apply tlm; auto with *.

 rewrite <- H6; rewrite H4; rewrite hd_eq with (1:=H3); rewrite <- eqhd;
   trivial.

 do 2 red; intros.
 apply trad_morph.
 apply tlm; auto with *.

 rewrite H1; rewrite hd_eq with (1:=H0); trivial.
Qed.


  Definition trad1 o y :=
    union (subset (TI Wf o) (fun x => trad x == y)).

  Lemma trad_surj : forall o,
    isOrd o ->
    forall y,
    y \in TI W_F o ->
    trad1 o y \in TI Wf o /\ trad (trad1 o y) == y.
intros o oo.
apply isOrd_ind with (2:=oo); intros o'; intros.
apply TI_elim in H2; auto with *.
2:apply Fmono_morph; apply W_F_mono.
destruct H2.
pose (y' := couple (fst y)
       (cc_lam (B (fst y)) (fun i => trad1 x (cc_app (snd y) i)))).
assert (tyy' : y' \in W_F (TI Wf x)).
 apply couple_intro_sigma; auto with *.
  do 2 red; intros.
  apply cc_prod_ext; auto with *.
  red; reflexivity.

  apply fst_typ_sigma in H3; trivial.

  apply cc_prod_intro; intros.
   do 2 red; intros.
   unfold trad1. (* trad1 ext*)
   apply union_morph.
   apply subset_morph; auto with *.
   red; intros.
   rewrite H5; reflexivity.

   do 2 red; reflexivity.

   destruct H1 with (1:=H2) (y:=cc_app (snd y) x0); trivial.
   apply cc_prod_elim with (1:=tys _ _ H3); trivial.
assert (tyx' : Wsup y' \in TI Wf o').
 apply TI_intro with x; trivial.
  apply Fmono_morph; trivial.
 apply Wf_intro; trivial.
assert (trad (Wsup y') == y).
 unfold trad; rewrite Fr_eqn with (o:=o'); auto with *.
 rewrite WF_eta with (1:=H3).
 assert (hd (Wsup y') == fst y).
  rewrite hd_eq with (1:=tyy').
  unfold y'; rewrite fst_def; reflexivity.
 apply couple_morph; trivial.
 apply cc_lam_ext.
  rewrite H4; reflexivity.
 red; intros.
 destruct H1 with (1:=H2) (y:=cc_app (snd y) x0).
  apply cc_prod_elim with (1:=tys _ _ H3); trivial.
  rewrite <- H4; trivial.

  fold trad.
  rewrite tl_eq with (X:=TI Wf x); auto. 
   unfold y'; rewrite snd_def.
   rewrite cc_beta_eq.
    rewrite H8.
    rewrite H6; reflexivity.

    red; red; intros.
    unfold trad1. (* trad1 ext*)
    apply union_morph.
    apply subset_morph; auto with *.
    red; intros.
    rewrite H10; reflexivity.

    rewrite <- H4; trivial.

    transitivity W; [apply Wi_W|apply Wtyp].
    apply isOrd_inv with o'; trivial.

    unfold y'; rewrite fst_def.
    rewrite <- H4; trivial.
assert (trad1 o' y == Wsup y').
 apply union_subset_singl with (y:=Wsup y') (y':=Wsup y');
   intros; auto with *.
 rewrite <- H8 in H7; apply trad_inj with (o:=o') (o':=o') in H7; trivial. 
rewrite H5; auto.
Qed.


  Definition W2 := TI W_F W_ord.

  Lemma W2_eqn : W2 == W_F W2.
unfold W2 at 2.
rewrite <- TI_mono_succ; auto.
2:apply W_F_mono.
apply eq_intro; intros.
 unfold W2; 
 revert H; apply TI_incl; auto.
 apply W_F_mono.

 apply trad_surj in H; auto.
 destruct H.
 rewrite <- H0.
 apply trad_ok; auto.
 apply W_post.
 revert H; apply Wi_W; auto.
Qed.


End W_theory.
