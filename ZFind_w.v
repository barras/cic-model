Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFord ZFfix (*ZFstable*).
Require Import ZFgrothendieck.
Require Import ZFcoc ZFlist.
Import IZF ZFrepl.

Section W_theory.

Variable A : set.
Variable B : set -> set.
Hypothesis Bext : ext_fun A B.

(* The intended type operator *)
Definition W_F X := sigma A (fun x => cc_prod (B x) (fun _ => X)).

Lemma wfm1 : forall X, ext_fun A (fun x => cc_prod (B x) (fun _ => X)).
do 2 red; intros.
apply cc_prod_ext; auto.
red; intros; reflexivity.
Qed.
Hint Resolve wfm1.

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
Qed.

Lemma W_F_stable : stable W_F.
unfold W_F.
apply sigma_stable'; auto with *.
 intros; apply cc_prod_ext; auto with *.
 red; trivial.

 intros.
 apply cc_prod_stable; intros; auto.
 apply id_stable.
Qed.

Let tys : forall x X, x \in W_F X -> snd x \in cc_prod (B (fst x)) (fun _ => X).
intros.
apply snd_typ_sigma with (y:=fst x) in H; auto with *.
Qed.

  Definition WFmap f x :=
    couple (fst x) (cc_lam (B (fst x)) (fun i => f (cc_app (snd x) i))).

  Lemma WFmap_ext : forall f f' x x',
    fst x \in A ->
    fst x == fst x' ->
    (forall i i', i \in B (fst x) -> i == i' ->
     f (cc_app (snd x) i) == f' (cc_app (snd x') i')) ->
    WFmap f x == WFmap f' x'.
intros.
apply couple_morph; trivial.
apply cc_lam_ext; auto.
Qed.

  Lemma WFmap_morph : forall X f f',
    eq_fun X f f' ->
    eq_fun (W_F X) (WFmap f) (WFmap f').
red; intros.
apply WFmap_ext; intros.
 apply fst_typ_sigma in H0; trivial.

 apply fst_morph; trivial.

 apply H.
  apply tys in H0.
  apply cc_prod_elim with (1:=H0); trivial.

  rewrite H1; rewrite H3; reflexivity.
Qed.

Lemma WFmap_comp : forall f g X Y x,
  ext_fun X g ->
  ext_fun Y f ->
  (forall x, x \in X -> g x \in Y) ->
  x \in W_F X ->
  WFmap f (WFmap g x) == WFmap (fun x => f (g x)) x.
intros.
unfold WFmap.
apply couple_morph.
 rewrite fst_def. 
 auto with *.

 symmetry; apply cc_lam_ext; intros.
  apply Bext.
   apply fst_typ_sigma in H2; trivial.

   rewrite fst_def.
   reflexivity.

  red; intros.
  apply H0.
   apply H1.
   apply tys in H2.
   apply cc_prod_elim with (1:=H2); trivial.

   rewrite snd_def.
   rewrite cc_beta_eq; auto with *.
    apply H.
     apply tys in H2; apply cc_prod_elim with (1:=H2); trivial.
     rewrite H4; reflexivity.

    do 2 red; intros.
    apply H.
     apply tys in H2; apply cc_prod_elim with (1:=H2); trivial.
     rewrite H6; reflexivity.

    rewrite <- H4; trivial.
Qed.

Lemma WF_eta : forall X x,
  x \in W_F X ->
  x == WFmap (fun x => x) x.
intros.
transitivity (couple (fst x) (snd x)).
 eapply surj_pair with (1:=subset_elim1 _ _ _ H).

 apply couple_morph; auto with *.
 eapply cc_eta_eq with (1:=tys _ _ H).
Qed.

  Lemma WFmap_inj : forall X Y g g' x x',
    x \in W_F X -> x' \in W_F Y ->
    ext_fun X g -> ext_fun Y g' ->
    (forall a a', a \in X -> a' \in Y -> g a == g' a' -> a == a') ->
    WFmap g x == WFmap g' x' -> x == x'.
unfold WFmap; intros.
apply couple_injection in H4; destruct H4 as (eqhd, eqtl).
rewrite (WF_eta _ _ H).
rewrite (WF_eta _ _ H0).
apply couple_morph; trivial.
apply cc_lam_ext; intros; auto.
 apply Bext; trivial.
 apply fst_typ_sigma in H; trivial.
red; intros.
assert (cc_app (cc_lam (B (fst x)) (fun i => g (cc_app (snd x) i))) x0 ==
        cc_app (cc_lam (B (fst x')) (fun i => g' (cc_app (snd x') i))) x'0).
 apply cc_app_morph; trivial.
rewrite cc_beta_eq in H6; trivial.
rewrite cc_beta_eq in H6.
 apply H3 in H6; trivial.
  apply cc_prod_elim with (1:=tys _ _ H); trivial.
  apply cc_prod_elim with (1:=tys _ _ H0); trivial.
  revert H4; apply in_set_morph; auto with *.
  symmetry; apply Bext; trivial.
  apply fst_typ_sigma in H; trivial.

 red; red; intros.
 apply H2.
  apply cc_prod_elim with (1:=tys _ _ H0); trivial.
  rewrite H8; reflexivity.

 revert H4; apply in_set_morph; auto with *.
 symmetry; apply Bext; trivial.
 apply fst_typ_sigma in H; trivial.

 red; red; intros.
 apply H1.
  apply cc_prod_elim with (1:=tys _ _ H); trivial.
  rewrite H8; reflexivity.
Qed.

  Lemma WFmap_typ : forall X Y f x,
    ext_fun X f ->
    x \in W_F X ->
    (forall a, a \in X -> f a \in Y) ->
    WFmap f x \in W_F Y.
unfold WFmap; intros.
apply couple_intro_sigma; trivial.
 apply subset_elim1 in H0; apply fst_typ in H0; trivial.

 apply cc_prod_intro.
  red; red; intros.
  apply H.
   apply cc_prod_elim with (1:=tys _ _ H0); trivial.
   rewrite H3; reflexivity.

  red; red; reflexivity.

  intros.
  apply H1.
  apply cc_prod_elim with (1:=tys _ _ H0); trivial.
Qed.


(* The construction domain and the constructor *)
Definition Wdom := rel (List (sup A B)) A.

Definition Wsup x :=
  union2 (singl (couple Nil (fst x)))
   (sup (B (fst x)) (fun y =>
      replf (cc_app (snd x) y)
        (fun p => couple (Cons y (fst p)) (snd p)))).

Lemma Wsup_morph : forall X, ext_fun (W_F X) Wsup.
do 2 red; intros.
unfold Wsup.
apply union2_morph.
 rewrite H0; reflexivity.

 apply sup_morph.
  apply Bext.
   apply fst_typ_sigma in H; trivial.
   apply fst_morph; trivial.

  red; intros.
  apply replf_morph_raw; auto.
   rewrite H0; rewrite H2; reflexivity.

   red; intros.
   rewrite H2; rewrite H3; reflexivity.
Qed.

Lemma wext1 : forall i y,
  ext_fun y (fun p => couple (Cons i (fst p)) (snd p)).
do 2 red; intros.
rewrite H0; reflexivity.
Qed.

Lemma wext2 : forall X g,
  ext_fun X (fun y =>
     replf (cc_app g y) (fun p => couple (Cons y (fst p)) (snd p))).
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
intros x p; intros.
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

Lemma Wsup_hd_prop : forall a x,
  (couple Nil a \in Wsup x <-> a == fst x).
split; intros.
 apply union2_elim in H; destruct H.
  apply singl_elim in H.
  apply couple_injection in H; destruct H; trivial.

  rewrite sup_ax in H; auto.
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

Lemma Wsup_tl_prop : forall X i l a x,
  x \in W_F X ->
  X \incl Wdom ->
  (couple (Cons i l) a \in Wsup x <->
   i \in B (fst x) /\ couple l a \in cc_app (snd x) i).
intros X i l a x H inclX.
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
  apply inclX in ty.
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

Lemma Wsup_inj : forall X Y x x',
  X \incl Wdom ->
  Y \incl Wdom ->
  x \in W_F X ->
  x' \in W_F Y ->
  Wsup x == Wsup x' -> x == x'.
intros X Y x x' tyf tyf' H H0 H1.
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
  apply Bext; trivial.
  apply fst_typ_sigma in H; trivial.

  red; intros.
  assert (x'0 \in B (fst x')).
   revert H5; apply in_set_morph; auto with *.
   apply Bext; auto with *.
   apply fst_typ_sigma in H0; trivial.
  assert (cc_app (snd x) x0 \incl prodcart (List (sup A B)) A).
   red; intros.
   apply power_elim with (2:=H8).
   apply tyf.
   apply cc_prod_elim with (1:=tys _ _ H); trivial.
  assert (cc_app (snd x') x'0 \incl prodcart (List (sup A B)) A).
   red; intros.
   apply power_elim with (2:=H9); trivial.
   apply tyf'.
   apply cc_prod_elim with (1:=tys _ _ H0); trivial.
  generalize (fun z l => Wsup_tl_prop _ x0 l z _ H tyf); intros.
  generalize (fun z l => Wsup_tl_prop _ x'0 l z _ H0 tyf'); intros.
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

Lemma Wsup_typ_gen : forall X x,
  X \incl Wdom ->
  x \in W_F X ->
  Wsup x \in Wdom.
intros.
apply power_intro; intros.
rewrite Wsup_def in H1; trivial.
destruct H1 as [eqz|(i,?,(q,?,eqz))]; rewrite eqz; clear z eqz.
 apply couple_intro; trivial.
  apply Nil_typ.
  apply fst_typ_sigma in H0; trivial.

 assert (q \in prodcart (List (sup A B)) A).
  apply power_elim with (2:=H2).
  apply H.
  apply cc_prod_elim with (1:=tys _ _ H0); trivial.
 apply couple_intro.
  apply Cons_typ.
   rewrite sup_ax; trivial.
   exists (fst x); trivial.
   apply fst_typ_sigma in H0; trivial.

   apply fst_typ with (1:=H3).

  apply snd_typ with (1:=H3).
Qed.

(* The type operator on the construction domain *)
Definition Wf X := replf (W_F X) Wsup.

Hint Resolve Wsup_morph.

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
rewrite replf_ax; auto.
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
 rewrite H3 in H5; apply Wsup_inj with (X:=x) (Y:=x1)in H5; trivial.
  rewrite H5; trivial.

  red; intros; apply power_elim with (1:=Xty _ H1); trivial.

  red; intros; apply power_elim with (1:=Xty _ H4); trivial.

 exists (W_F x).
 rewrite replf_ax.
 2:red;red;intros;apply Fmono_morph;auto.
 2:apply W_F_mono.
 exists x; auto with *.
Qed.

(*Hint Resolve Wf_stable.*)

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
  a == Wsup x.
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
  Wsup x \in TI Wf (osucc o).
intros.
rewrite TI_mono_succ; auto.
apply Wf_intro; trivial.
Qed.

Lemma W_ind : forall (P:set->Prop),
  Proper (eq_set ==> iff) P ->
  (forall o' x, isOrd o' -> x \in W_F (TI Wf o') ->
   (forall i, i \in B (fst x) -> P (cc_app (snd x) i)) ->
   P (Wsup x)) ->
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
apply Wf_stable.
Qed.

  Lemma W_eqn : W == Wf W.
apply Ffix_eqn; eauto.
apply Wf_stable.
Qed.


(***************************************)

  Definition Wsupi x := union (subset (W_F W) (fun y => Wsup y == x)).

  Instance Wsupi_morph : morph1 Wsupi.
do 2 red; intros.
unfold Wsupi.
apply union_morph; apply subset_morph; auto with *.
red; intros.
rewrite H; reflexivity.
Qed.

  Lemma Wsupi_def : forall X x,
    x \in W_F X ->
    X \incl W ->
    Wsupi (Wsup x) == x.
unfold Wsupi; intros.
apply union_subset_singl with (y':=x); auto with *.
 revert H; apply W_F_mono; auto.

 intros.
 rewrite <- H4 in H3.
 apply Wsup_inj with (X:=W) (Y:=W) in H3; auto with *.
 apply Ffix_inA.
 apply Ffix_inA.
Qed.

(* translation Wf X --> W_F Y given translation g:X-->Y *)
  Definition trF g x := WFmap g (Wsupi x).

  Lemma trF_decomp : forall X g x y,
    ext_fun X g ->
    x \in W_F X ->
    X \incl W ->
    y == Wsup x ->
    trF g y == WFmap g x.
intros.
unfold trF.
assert (Wsupi y == x).
 rewrite H2.
 apply Wsupi_def with X; auto with *.
apply (WFmap_morph X); trivial.
 rewrite H3; trivial.
Qed.

Lemma Wfsub_intro : forall X x i,
  x \in W_F X ->
  X \incl W ->
  i \in B (fst x) ->
  cc_app (snd x) i \in fsub Wf Wdom (Wsup x).
intros.
apply subset_intro.
 apply H0.
 apply cc_prod_elim with (1:=tys _ _ H); trivial.

 intros.
 apply Wf_elim in H3.
 destruct H3.
 apply Wsup_inj with (X:=X)(Y:=X0) in H4; auto.
  rewrite <- H4 in H3.
  apply cc_prod_elim with (1:=tys _ _ H3); trivial.

  transitivity W;[trivial|apply Ffix_inA].
  transitivity W;[trivial|apply Ffix_inA].
Qed. 

Let Gm_prf : forall (x x' : set) (g g' : set -> set),
   x \in W ->
   eq_fun (fsub Wf Wdom x) g g' ->
   x == x' ->
   trF g x == trF g' x'.
intros.
unfold trF.
apply WFmap_ext.
 rewrite W_eqn in H.
 apply Wf_elim in H.
 destruct H.
 rewrite H2.
 rewrite Wsupi_def with W; auto with *.
 apply fst_typ_sigma in H; trivial.

 rewrite H1; reflexivity.

 intros.
 unfold W in H; rewrite Ffix_def in H; auto with *.
 destruct H.
 apply TI_Wf_elim in H4; trivial.
 destruct H4.
 destruct H5.
 assert (Wsupi x == x2).
  rewrite H6; rewrite Wsupi_def with (TI Wf x1); auto with *.
  apply Wi_W; eauto using isOrd_inv.
 assert (cc_app (snd (Wsupi x)) i \in fsub Wf Wdom (Wsup (Wsupi x))).
  apply Wfsub_intro with (TI Wf x1); auto with *.
   rewrite H7; trivial.

   apply Wi_W; eauto using isOrd_inv.
 rewrite (fsub_morph Wf Wdom (Wsup (Wsupi x)) x) in H8.
  apply H0; trivial.
  rewrite H1; rewrite H3; reflexivity.

  transitivity (Wsup x2); auto with *.
  symmetry; apply Wsup_morph with (TI Wf x1); auto with *.
Qed.
Hint Resolve Gm_prf.


Lemma trF_typ : forall X Y x g,
  ext_fun X g ->
  X \incl W ->
  (forall x, x \in X -> g x \in Y) ->
  x \in Wf X ->
  trF g x \in W_F Y.
intros.
apply Wf_elim in H2; destruct H2.
rewrite trF_decomp with (2:=H2) (4:=H3); trivial.
apply WFmap_typ with X; trivial.
Qed.

  Lemma trF_inj : forall X Y g g' x x',
    X \incl W -> Y \incl W ->
    x \in Wf X -> x' \in Wf Y ->
    ext_fun X g -> ext_fun Y g' ->
    (forall a a', a \in X -> a' \in Y -> g a == g' a' -> a == a') ->
    trF g x == trF g' x' -> x == x'.
intros X Y g g' x x' Xi Yi H H0 gm g'm H1 H2.
apply Wf_elim in H; destruct H.
apply Wf_elim in H0; destruct H0.
(*rewrite trF_decomp with (2:=H) (3:=H3) in H2; trivial.
  produces ill-typed proof term rejected at Qed *)
rewrite trF_decomp with (2:=H) (4:=H3) in H2; trivial.
rewrite trF_decomp with (2:=H0) (4:=H4) in H2; trivial.
apply WFmap_inj with (X:=X)(Y:=Y) in H2; trivial.
rewrite H3; rewrite H4; apply Wsup_morph with X; auto with *.
Qed.

  Definition trad := Fix_rec Wf Wdom trF.

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
assert (oo' : isOrd o').
 apply isOrd_inv with y; trivial.
apply TI_intro with o'; auto.
 apply Fmono_morph; apply W_F_mono.

 apply trF_typ with (TI Wf o'); auto with *.
  apply Wi_W; trivial.

  rewrite H4.
  rewrite <- TI_mono_succ; auto.
  apply Wsup_typ; trivial.
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
apply trF_inj with (TI Wf o1') (TI Wf o2') trad trad; auto with *.
 apply Wi_W;eauto using isOrd_inv.
 apply Wi_W;eauto using isOrd_inv.

 rewrite <- TI_mono_succ; eauto using isOrd_inv.
 rewrite H1; apply Wsup_typ; eauto using isOrd_inv.

 rewrite <- TI_mono_succ; eauto using isOrd_inv.
 rewrite H4; apply Wsup_typ; eauto using isOrd_inv.

 intros.
 apply Hrec with o1' o2'; eauto using isOrd_inv.
Qed.

  Definition trad1 y :=
    union (subset W (fun x => trad x == y)).

  Instance trad1m : morph1 trad1.
do 2 red; intros.
unfold trad1.
apply union_morph.
apply subset_morph.
 reflexivity.

 red; intros.
 rewrite H; reflexivity.
Qed.

  Lemma trad_surj : forall o,
    isOrd o ->
    forall y,
    y \in TI W_F o ->
    trad1 y \in TI Wf o /\ trad (trad1 y) == y.
intros o oo.
apply isOrd_ind with (2:=oo); intros o'; intros.
apply TI_elim in H2; auto with *.
2:apply Fmono_morph; apply W_F_mono.
destruct H2.
assert (ty_tr_y : Wsup (WFmap trad1 y) \in TI Wf o').
 apply TI_intro with x; auto with *.
 rewrite <- TI_mono_succ; eauto using isOrd_inv.
 apply Wsup_typ; eauto using isOrd_inv.
 apply WFmap_typ with (TI W_F x); auto with *.
 intros.
 apply H1; trivial.
assert (trad (Wsup (WFmap trad1 y)) == y).
 unfold trad; rewrite Fr_eqn with (o:=o'); fold trad; auto with *.
 unfold trF.
 transitivity (WFmap trad (WFmap trad1 y)).
  apply WFmap_morph with (TI Wf x); auto with *.
   red; intros; apply trad_morph; trivial.

   rewrite Wsupi_def with (TI Wf x).
    apply WFmap_typ with (TI W_F x); auto with *.
    intros.
    apply H1; trivial.

    apply WFmap_typ with (TI W_F x); auto with *.
    intros.
    apply H1; trivial.

   apply Wi_W; eauto using isOrd_inv.

   apply Wsupi_def with (TI Wf x).
    apply WFmap_typ with (TI W_F x); auto with *.
    intros.
    apply H1; trivial.

    apply Wi_W; eauto using isOrd_inv.

  generalize (WF_eta _ _ H3); intro.
  apply @transitivity with (3:=symmetry H4); auto with *.
  rewrite WFmap_comp with (TI W_F x) (TI Wf x); auto with *.
   apply WFmap_ext; auto with *.
    apply fst_typ_sigma in H3; trivial.

    intros.
    rewrite <- H6.
    apply H1 with x; trivial.
    apply cc_prod_elim with (1:=tys _ _ H3); trivial.

   intros.
   apply H1; trivial.
assert (trad1 y == Wsup (WFmap trad1 y)).
 apply union_subset_singl with (y':=Wsup (WFmap trad1 y));
   intros; auto with *.
  apply Wi_W with o'; trivial.

  unfold W in H5,H6.
  rewrite Ffix_def in H5,H6; auto with *.
  destruct H5; destruct H6.
  rewrite <- H8 in H7; apply trad_inj with (o:=x0) (o':=x1) in H7; trivial. 

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

(* Recursor on W2 *)

Require Import ZFfunext ZFfixrec.

Section Recursor.

  Hint Resolve W_F_mono.

  Lemma Wi_fix :
    forall (P:set->Prop) o,
    isOrd o ->
    (forall i, isOrd i -> i \incl o ->
     (forall i' m, lt i' i -> m \in TI W_F i' -> P m) ->
     forall n, n \in TI W_F i -> P n) ->
    forall n, n \in TI W_F o -> P n.
intros P o is_ord Prec.
induction is_ord using isOrd_ind; intros; eauto.
Qed.

  Variable ord : set.
  Hypothesis oord : isOrd ord.

  Variable F : set -> set -> set.
  Hypothesis Fm : morph2 F.

  Variable U : set -> set -> set.
  Hypothesis Umono : forall o o' x x',
    isOrd o' -> o' \incl ord -> isOrd o -> o \incl o' ->
    x \in TI W_F o -> x == x' ->
    U o x \incl U o' x'.

  Let Ty o := cc_prod (TI W_F o) (U o).
  Hypothesis Ftyp : forall o f, isOrd o -> o \incl ord ->
    f \in Ty o -> F o f \in Ty (osucc o).

  Let Q o f := forall x, x \in TI W_F o -> cc_app f x \in U o x.

  Definition Wi_ord_irrel :=
    forall o o' f g,
    isOrd o' -> o' \incl ord -> isOrd o -> o \incl o' ->
    f \in Ty o -> g \in Ty o' ->
    fcompat (TI W_F o) f g ->
    fcompat (TI W_F (osucc o)) (F o f) (F o' g).

  Hypothesis Firrel : Wi_ord_irrel.

  Definition WREC := REC F.

Lemma Umorph : forall o o', isOrd o' -> o' \incl ord -> o == o' ->
    forall x x', x \in TI W_F o -> x == x' -> U o x == U o' x'. 
intros.
apply incl_eq.
 apply Umono; auto.
  rewrite H1; trivial.
  rewrite H1; reflexivity.

 apply Umono; auto.
  rewrite H1; trivial.
  rewrite H1; trivial.
  rewrite H1; reflexivity.
  rewrite <- H3; rewrite <- H1; trivial.
  symmetry; trivial.
Qed.

Lemma Uext : forall o, isOrd o -> o \incl ord -> ext_fun (TI W_F o) (U o).
red; red; intros.
apply Umorph; auto with *.
Qed.


  Lemma WREC_typing : forall o f, isOrd o -> o \incl ord -> 
    is_cc_fun (TI W_F o) f -> Q o f -> f \in Ty o.
intros.
rewrite cc_eta_eq' with (1:=H1).
apply cc_prod_intro; intros; auto.
 do 2 red; intros.
 rewrite H4; reflexivity.

 apply Uext; trivial.
Qed.


Lemma Wi_cont : forall o,
   isOrd o -> TI W_F o == sup o (fun o' => TI W_F (osucc o')).
intros.
rewrite TI_eq; auto.
apply sup_morph; auto with *.
red; intros.
rewrite <- TI_mono_succ; eauto using isOrd_inv.
apply TI_morph; apply osucc_morph; trivial.
Qed.

Let Qm :
   forall o o',
   isOrd o ->
   o \incl ord ->
   o == o' -> forall f f', fcompat (TI W_F o) f f' -> Q o f -> Q o' f'.
intros.
unfold Q in H3|-*; intros.
rewrite <- H1 in H4.
specialize H3 with (1:=H4).
red in H2; rewrite <- H2; trivial.
revert H3; apply Umono; auto with *.
 rewrite <- H1; trivial.
 rewrite <- H1; trivial.
 rewrite <- H1; reflexivity.
Qed.

Let Qcont : forall o f : set,
 isOrd o ->
 o \incl ord ->
 is_cc_fun (TI W_F o) f ->
 (forall o' : set, o' \in o -> Q (osucc o') f) -> Q o f.
intros.
red; intros.
apply TI_elim in H3; auto.
destruct H3.
rewrite <- TI_mono_succ in H4; eauto using isOrd_inv.
generalize (H2 _ H3 _ H4).
apply Umono; eauto using isOrd_inv with *.
red; intros.
apply isOrd_plump with x0; eauto using isOrd_inv.
apply olts_le in H5; trivial.
Qed.

Let Qtyp : forall o f,
 isOrd o ->
 o \incl ord ->
 is_cc_fun (TI W_F o) f ->
 Q o f -> is_cc_fun (TI W_F (osucc o)) (F o f) /\ Q (osucc o) (F o f).
intros.
assert (F o f \in Ty (osucc o)).
 apply Ftyp; trivial.
 apply WREC_typing; trivial.
split.
 apply cc_prod_is_cc_fun in H3; trivial.

 red; intros.
 apply cc_prod_elim with (1:=H3); trivial.
Qed.

  Lemma Firrel_W : stage_irrelevance ord (TI W_F) Q F.
red; red; intros.
destruct H1 as (oo,(ofun,oty)); destruct H2 as (o'o,(o'fun,o'ty)).
apply Firrel; trivial.
 apply WREC_typing; trivial. 
 transitivity o'; trivial.

 apply WREC_typing; trivial. 
Qed.
Hint Resolve Firrel_W.

  (* Main properties of WREC: typing and equation *)
  Lemma WREC_wt : WREC ord \in Ty ord.
intros.
refine ((fun h => WREC_typing
          ord (WREC ord) oord (reflexivity _) (proj1 h) (proj2 h)) _).
apply REC_wt with (T:=TI W_F) (Q:=Q); auto.
 apply TI_morph.

 apply Wi_cont.
Qed.

  Lemma WREC_ind : forall P x,
    Proper (eq_set==>eq_set==>eq_set==>iff) P ->
    (forall o x, isOrd o -> lt o ord ->
     x \in W_F (TI W_F o) ->
     (forall y, y \in TI W_F o -> P o y (cc_app (WREC ord) y)) ->
     forall w, isOrd w -> w \incl ord -> lt o w ->
     P w x (cc_app (F ord (WREC ord)) x)) ->
    x \in TI W_F ord ->
    P ord x (cc_app (WREC ord) x).
intros.
unfold WREC.
apply REC_ind with (T:=TI W_F) (Q:=Q); auto.
 apply TI_morph.

 apply Wi_cont.

 intros.
 apply TI_elim in H4; auto.
 destruct H4 as (o',?,?).
 apply H0 with o'; eauto using isOrd_inv.
 red; auto.
Qed.

  Lemma WREC_expand : forall n,
    n \in TI W_F ord -> cc_app (WREC ord) n == cc_app (F ord (WREC ord)) n.
intros.
apply REC_expand with (T:=TI W_F) (Q:=Q); auto.
 apply TI_morph.

 apply Wi_cont.
Qed.

End Recursor.



Section W_Univ.

(* Universe facts *)
  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : omega \in U.  

  Hypothesis aU : A \in U.
  Hypothesis bU : forall a, a \in A -> B a \in U.

  Lemma G_Wdom : Wdom \in U.
unfold Wdom.
apply G_rel; trivial.
apply G_List; trivial.
apply G_sup; trivial.
Qed.

  Lemma G_W : W \in U.
apply G_subset; trivial.
apply G_Wdom.
Qed.

  Lemma G_W_F X : X \in U -> W_F X \in U.
intros.
unfold W_F.
apply G_sigma; intros; trivial.
apply G_cc_prod; auto.
Qed.

  Lemma G_W_ord : W_ord \in U.
unfold W_ord.
unfold Ffix_ord.
apply G_osup; intros; trivial.
 do 2 red; intros; apply osucc_morph.
 unfold Fix_rec.
 apply uchoice_morph_raw.
 red; intros.
 apply Ffix_rel_morph; trivial.

 apply isOrd_succ.
 apply F_a_ord; auto.

 apply G_Ffix; trivial.
 apply G_Wdom; trivial.

 unfold osucc; apply G_subset; trivial; apply G_power; trivial.
 apply subset_elim1 with (P:=isOrd).
 apply Fix_rec_typ with U; auto.
  intros; apply F_a_morph; trivial.

  red; intros.
  apply G_trans with (2:=H0); trivial.
  apply G_Ffix; trivial.
  apply G_Wdom.

  intros.
  apply subset_intro.
   unfold F_a.
   apply G_osup; trivial.
    do 2 red; intros; apply osucc_morph; apply H0; trivial.

    intros.
    apply isOrd_succ.
    apply H2 in H3.
    apply subset_elim2 in H3; destruct H3.
    rewrite H3; trivial.

    unfold fsub.
    apply G_subset; trivial.
    apply G_W; trivial.

    intros.
    unfold osucc.
    apply G_subset; trivial.
    apply G_power; trivial.
    apply H2 in H3.
    apply subset_elim1 in H3; trivial.

    apply isOrd_osup.
     do 2 red; intros; apply osucc_morph; apply H0; trivial.

     intros.
     apply isOrd_succ.
     apply H2 in H3.
     apply subset_elim2 in H3; destruct H3.
     rewrite H3; trivial.
Qed.


  Lemma G_W2 : W2 \in U.
apply G_TI; intros; trivial.
 do 2 red; intros; apply sigma_ext; intros; auto with *.
 apply cc_prod_morph; auto with *.
 red; trivial.

 apply G_W_ord.

 apply G_W_F; trivial.
Qed.

End W_Univ.

End W_theory.

(* More on W_F: *)
(*
Lemma W_F_morph : Proper (eq_set ==> (eq_set ==> eq_set) ==> eq_set ==> eq_set) W_F.
do 4 red; intros.
unfold W_F.
apply sigma_ext; trivial.
intros.
apply cc_prod_ext; auto with *.
red; trivial.
Qed.
*)

Lemma W_F_ext : forall A A' B B' X X',
  A == A' ->
  eq_fun A B B' ->
  X == X' ->
  W_F A B X == W_F A' B' X'.
unfold W_F; intros.
apply sigma_ext; trivial.
intros.
apply cc_prod_ext; auto with *.
red; auto.
Qed.

Hint Resolve wfm1.
