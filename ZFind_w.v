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

  Definition WFmap f x :=
    couple (fst x) (cc_lam (B (fst x)) (fun i => f (cc_app (snd x) i))).

  Lemma WFmap_ext : forall f f' x x',
    fst x == fst x' ->
    (forall i i', i \in B (fst x) -> i == i' ->
     f (cc_app (snd x) i) == f' (cc_app (snd x') i')) ->
    WFmap f x == WFmap f' x'.
intros.
apply couple_morph; trivial.
apply cc_lam_ext.
 rewrite H; reflexivity.

 red; intros; auto.
Qed.

  Instance WFmap_morph : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) WFmap.
do 3 red; intros.
apply WFmap_ext.
 rewrite H0; reflexivity.

 intros.
 apply H.
 rewrite H0; rewrite H2; reflexivity.
Qed.

Lemma WFmap_comp : forall f g x,
  morph1 f ->
  morph1 g ->
  WFmap f (WFmap g x) == WFmap (fun x => f (g x)) x.
intros.
assert (fst (WFmap g x) == fst x).
 unfold WFmap; rewrite fst_def; reflexivity.
apply WFmap_ext; trivial.
intros.
rewrite H1 in H2.
apply H.
unfold WFmap.
rewrite snd_def.
rewrite cc_beta_eq; trivial.
 rewrite H3; reflexivity.

 do 2 red; intros.
 rewrite H5; reflexivity.
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
    morph1 g -> morph1 g' ->
    (forall a a', a \in X -> a' \in Y -> g a == g' a' -> a == a') ->
    WFmap g x == WFmap g' x' -> x == x'.
unfold WFmap; intros.
apply couple_injection in H4; destruct H4 as (eqhd, eqtl).
rewrite (WF_eta _ _ H).
rewrite (WF_eta _ _ H0).
apply couple_morph; trivial.
apply cc_lam_ext; intros; auto.
red; intros.
assert (cc_app (cc_lam (B (fst x)) (fun i => g (cc_app (snd x) i))) x0 ==
        cc_app (cc_lam (B (fst x')) (fun i => g' (cc_app (snd x') i))) x'0).
 apply cc_app_morph; trivial.
rewrite cc_beta_eq in H6; trivial.
rewrite cc_beta_eq in H6.
 apply H3 in H6; trivial.
  apply cc_prod_elim with (1:=tys _ _ H); trivial.
  apply cc_prod_elim with (1:=tys _ _ H0); trivial.
  rewrite <- eqhd; rewrite <- H5; trivial.

 red; red; intros.
 rewrite H8; reflexivity.

 rewrite <- eqhd; rewrite <- H5; trivial.

 red; red; intros.
 rewrite H8; reflexivity.
Qed.

  Lemma WFmap_typ : forall X Y f x,
    morph1 f ->
    x \in W_F X ->
    (forall a, a \in X -> f a \in Y) ->
    WFmap f x \in W_F Y.
unfold WFmap; intros.
apply couple_intro_sigma.
 red; red; intros.
 apply cc_prod_ext.
  apply Bmorph; trivial.

  red; intros; reflexivity.

 apply subset_elim1 in H0; apply fst_typ in H0; trivial.

 apply cc_prod_intro.
  red; red; intros.
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

Instance Wsup_morph : morph1 Wsup.
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

(* could use hd_eq and tl_eq... *)
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
  apply Bmorph; trivial.

  red; intros.
  assert (x'0 \in B (fst x')).
   rewrite <- H6; rewrite <- H2; trivial.
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
   rewrite sup_ax.
   2:red; red; intros; apply Bmorph; trivial.
   exists (fst x); trivial.
   apply fst_typ_sigma in H0; trivial.

   apply fst_typ with (1:=H3).

  apply snd_typ with (1:=H3).
Qed.

(* The type operator on the construction domain *)
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
Qed.

  Lemma W_eqn : W == Wf W.
apply Ffix_eqn; eauto.
Qed.


(***************************************)

  Definition Wsupi x := union (subset (W_F Wdom) (fun y => Wsup y == x)).

  Instance Wsupi_morph : morph1 Wsupi.
do 2 red; intros.
unfold Wsupi.
apply union_morph; apply subset_morph; auto with *.
red; intros.
rewrite H; reflexivity.
Qed.

  Lemma Wsupi_def : forall X x,
    x \in W_F X ->
    X \incl Wdom ->
    Wsupi (Wsup x) == x.
unfold Wsupi; intros.
apply union_subset_singl with (y':=x); auto with *.
 revert H; apply W_F_mono; auto.

 intros.
 rewrite <- H4 in H3.
 apply Wsup_inj with (X:=Wdom) (Y:=Wdom) in H3; auto with *.
Qed.

(* translation Wf X --> W_F Y given translation g:X-->Y *)
  Definition trF g x := WFmap g (Wsupi x).

  Lemma trF_decomp : forall X g x y,
    morph1 g ->
    x \in W_F X ->
    X \incl Wdom ->
    y == Wsup x ->
    trF g y == WFmap g x.
intros.
unfold trF.
apply WFmap_morph; trivial.
rewrite H2.
apply Wsupi_def with X; auto with *.
Qed.

Lemma Wfsub_intro : forall X x i,
  x \in W_F X ->
  X \incl Wdom ->
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
Qed. 

Let Gm_prf : forall (x x' : set) (g g' : set -> set),
   x \in W ->
   eq_fun (fsub Wf Wdom x) g g' ->
   x == x' ->
   trF g x == trF g' x'.
intros.
unfold trF.
apply WFmap_ext.
 rewrite H1; reflexivity.

 intros.
 unfold W in H; rewrite Ffix_def in H; auto with *.
 destruct H.
 apply TI_Wf_elim in H4; trivial.
 destruct H4.
 destruct H5.
 assert (Wsupi x == x2).
  rewrite H6; rewrite Wsupi_def with (TI Wf x1); auto with *.
  transitivity W; [apply Wi_W; eauto using isOrd_inv|apply Wtyp].
 assert (cc_app (snd (Wsupi x)) i \in fsub Wf Wdom (Wsup (Wsupi x))).
  apply Wfsub_intro with (TI Wf x1); auto with *.
   rewrite H7; trivial.

   transitivity W; [apply Wi_W; eauto using isOrd_inv|apply Wtyp].
 rewrite (fsub_morph Wf Wdom (Wsup (Wsupi x)) x) in H8.
  apply H0; trivial.
  rewrite H1; rewrite H3; reflexivity.

  rewrite H7; auto with *.
Qed.
Hint Resolve Gm_prf.


Lemma trF_typ : forall X Y x g,
  morph1 g ->
  X \incl Wdom ->
  (forall x, x \in X -> g x \in Y) ->
  x \in Wf X ->
  trF g x \in W_F Y.
intros.
apply Wf_elim in H2; destruct H2.
rewrite trF_decomp with (2:=H2) (4:=H3); trivial.
apply WFmap_typ with X; trivial.
Qed.

  Lemma trF_inj : forall X Y g g' x x',
    X \incl Wdom -> Y \incl Wdom ->
    x \in Wf X -> x' \in Wf Y ->
    morph1 g -> morph1 g' ->
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
rewrite H3; rewrite H4; apply Wsup_morph; auto with *.
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
  transitivity W; [apply Wi_W|apply Wtyp]; trivial.

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
 transitivity W; [apply Wi_W|apply Wtyp];eauto using isOrd_inv.
 transitivity W; [apply Wi_W|apply Wtyp];eauto using isOrd_inv.

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
 rewrite Wsupi_def with (TI Wf x).
  generalize (WF_eta _ _ H3); intro.
  apply @transitivity with (3:=symmetry H4); auto with *.
  rewrite WFmap_comp; auto with *.
  apply WFmap_ext; auto with *.
  intros.
  rewrite <- H6.
  apply H1 with x; trivial.
  apply cc_prod_elim with (1:=tys _ _ H3); trivial.

  apply WFmap_typ with (TI W_F x); auto with *.
  intros.
  apply H1; trivial.

  transitivity W; [apply Wi_W; eauto using isOrd_inv|apply Wtyp].
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

End W_theory.
