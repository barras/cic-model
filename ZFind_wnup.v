Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFord ZFfix ZFstable.
Require Import ZFcoc ZFlist.
Import IZF ZFrepl.

(* A dependent version of ZFind_w: Arg is the type of indexes
   This should support non-uniform parameters.
 *)
Require ZFind_w.
Module W0 := ZFind_w.

(* -->  ZFcoc *)
Lemma cc_prod_intro' : forall (dom dom': set) (f F : set -> set),
       ext_fun dom f ->
       ext_fun dom' F ->
       dom == dom' ->
       (forall x : set, x \in dom -> f x \in F x) ->
       cc_lam dom f \in cc_prod dom' F.
intros.
cut (cc_lam dom f \in cc_prod dom F).
 apply cc_prod_covariant; auto with *.
apply cc_prod_intro; intros; auto.
do 2 red; intros.
apply H0; trivial.
rewrite <- H1; trivial.
Qed.

Section W_theory.

Variable Arg : set.
Variable A : set -> set.
Variable B : set -> set -> set.
Variable C : set -> set -> set -> set.
Hypothesis Am : morph1 A.
Hypothesis Bm : morph2 B.
Hypothesis Cm : Proper (eq_set==>eq_set==>eq_set==>eq_set) C.
Hypothesis Cty : forall a x y,
  a \in Arg ->
  x \in A a ->
  y \in B a x ->
  C a x y \in Arg.


(* The intended type operator: parameter is not part of the data-structure *)
Definition W_Fd (X:set->set) a :=
  sigma (A a) (fun x => cc_prod (B a x) (fun y => X (C a x y))).

Instance W_Fd_morph : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) W_Fd.
unfold W_Fd; do 3 red; intros.
apply sigma_morph; auto.
red; intros.
apply cc_prod_morph.
 apply Bm; auto.

 red; intros; apply H; apply Cm; trivial.
Qed.

Require Import ZFfixfun.
Existing Instance TIF_morph.

Lemma W_Fd_mono : mono_fam Arg W_Fd.
do 2 red; intros.
unfold W_Fd.
apply sigma_mono; intros; auto with *.
 do 2 red; intros; apply cc_prod_morph;[apply Bm|red; intros;apply H; apply Cm]; auto with *.
 do 2 red; intros; apply cc_prod_morph;[apply Bm|red; intros;apply H0; apply Cm]; auto with *.

 apply cc_prod_covariant; auto with *.
  do 2 red; intros; apply H0; apply Cm; auto with *.

  apply Bm; auto with *.

  intros.
  rewrite <- H4.
  auto.
Qed.
Hint Resolve W_Fd_mono.

Lemma W_Fd_eta w X a :
  morph1 X ->
  w \in W_Fd X a ->
  w == couple (fst w) (cc_lam (B a (fst w)) (fun i => cc_app (snd w) i)).
intros.
transitivity (couple (fst w) (snd w)).
 apply surj_pair with (1:=subset_elim1 _ _ _ H0).

 apply couple_morph;[reflexivity|].
 apply snd_typ_sigma with (y:=fst w) in H0; auto with *.
  apply cc_eta_eq with (1:=H0).

  do 2 red; intros.
  apply cc_prod_ext.
   apply Bm; auto with *.

   red; intros; apply H; apply Cm; auto with *.
Qed.

Lemma W_Fd_intro X x x' a a' f :
  morph1 X ->
  morph1 f ->
  a \in Arg ->
  a == a' ->
  x \in A a' ->
  x == x' ->
  (forall i, i \in B a x' -> f i \in X (C a x' i)) ->
  couple x (cc_lam (B a x') f) \in W_Fd X a'.
intros.
apply couple_intro_sigma; trivial.
 do 2 red; intros.
 apply cc_prod_ext.
  apply Bm; auto with *.

  red; intros.
  apply H; apply Cm; auto with *.

 apply cc_prod_intro'; intros; auto.
  do 2 red; intros; apply H; apply Cm; auto with *.
  apply Bm; auto with *.
  rewrite <- H2; rewrite H4; auto.
Qed.

(* The intermediate W type: carries parameter value *)
Definition A' := sigma Arg A.
Definition B' a' := B (fst a') (snd a').
Instance B'_morph : morph1 B'.
do 2 red; intros; apply Bm; [apply fst_morph|apply snd_morph]; trivial.
Qed.

Lemma B'ext : ext_fun A' B'.
auto with *.
Qed.
Hint Resolve B'ext.

(* constraint on parameter *)
Inductive instance w a : Prop :=
| I_node :
    a == fst (fst w) ->
    (forall i, i \in B' (fst w) -> instance (cc_app (snd w) i) (C a (snd (fst w)) i)) ->
    instance w a.

Instance instance_morph : Proper (eq_set==>eq_set==>iff) instance.
apply morph_impl_iff2; auto with *.
do 4 red; intros.
revert y y0 H H0.
induction H1; intros.
constructor; intros.
 rewrite <- H3; rewrite <- H2; trivial.

 apply H1 with i.
  rewrite H2; trivial.
  rewrite H2; reflexivity.
  rewrite H3; rewrite H2; reflexivity.
Qed.

(* We show there is an iso between the intended type (W_Fd)
   and the encoding (W0.W2 A' B')
 *)
Definition trad :=
  W0.WREC (fun o F => cc_lam (TI (W0.W_F A' B') (osucc o))
    (fun w => couple (snd (fst w)) (cc_lam (B' (fst w)) (fun i => cc_app F (cc_app (snd w) i))))).

Lemma trad_body_m2 F :
  morph1 (fun w => couple (snd (fst w)) (cc_lam (B' (fst w)) (fun i => cc_app F (cc_app (snd w) i)))).
do 2 red; intros.
apply couple_morph.
 rewrite H; reflexivity.

 apply cc_lam_ext.
  rewrite H; reflexivity.

  red; intros.
  rewrite H; rewrite H1; reflexivity.
Qed.
Hint Resolve trad_body_m2.

Lemma trad_body_morph :
  morph2
     (fun o F => cc_lam (TI (W0.W_F A' B') (osucc o))
        (fun w => couple (snd (fst w)) (cc_lam (B' (fst w)) (fun i => cc_app F (cc_app (snd w) i))))).
do 3 red; intros.
apply cc_lam_ext.
 rewrite H; reflexivity.

 red; intros.
 apply couple_morph.
  rewrite H2; reflexivity.

  apply cc_lam_ext; intros.
   rewrite H2; reflexivity.

   red; intros.
   rewrite H4; rewrite H0; rewrite H2; reflexivity.
Qed.

Let Q (o:set) := TI (fun X => sup Arg (fun a => W0.W_F (A a) (fun x => B a x) X)) o.

Lemma trad_codom_mono : forall o o',
 isOrd o' ->
 isOrd o ->
 o \incl o' ->
 Q o \incl Q o'.
intros.
apply TI_mono; auto.
do 3 red; intros.
rewrite sup_ax in H3|-*.
 destruct H3 as (a,?,?); exists a; trivial.
 revert H4; apply W0.W_F_mono; auto.
  do 2 red; intros; apply Bm; auto with *.

 do 2 red; intros; apply W0.W_F_ext; auto with *.
 red; intros; apply Bm; trivial.

 do 2 red; intros; apply W0.W_F_ext; auto with *.
 red; intros; apply Bm; trivial.
Qed.

Lemma trad_body_ty : forall o f,
 isOrd o ->
 f \in
 cc_arr (TI (W0.W_F A' B') o) (Q o) ->
 cc_lam (TI (W0.W_F A' B') (osucc o))
   (fun w => couple (snd (fst w)) (cc_lam (B' (fst w)) (fun i => cc_app f (cc_app (snd w) i)))) \in
 cc_arr (TI (W0.W_F A' B') (osucc o)) (Q (osucc o)).
intros.
apply cc_arr_intro; intros.
 admit.

 rewrite TI_mono_succ in H1; auto.
 2:apply W0.W_F_mono; trivial.
 assert (fst (fst x) \in Arg).
  apply fst_typ_sigma in H1; apply fst_typ_sigma in H1; trivial.
 apply TI_intro with o; auto with *.
  admit.
 rewrite sup_ax.
 2:admit.
 exists (fst (fst x)); auto.
 apply couple_intro_sigma; auto.
  admit.

  apply fst_typ_sigma in H1; apply snd_typ_sigma with (y:=fst(fst x)) in H1; auto with *.

  apply cc_arr_intro; intros.
   admit.

   apply cc_arr_elim with (1:=H0).
   apply snd_typ_sigma with (y:=fst x) in H1; auto with *.
   apply cc_arr_elim with (1:=H1); trivial.
Qed.

Lemma trad_irrel o :
 isOrd o ->
 W0.Wi_ord_irrel A' B' o
   (fun o0 F =>
    cc_lam (TI (W0.W_F A' B') (osucc o0))
      (fun w =>
       couple (snd (fst w))
         (cc_lam (B' (fst w)) (fun i => cc_app F (cc_app (snd w) i)))))
   (fun o w => Q o).
do 2 red; intros.
 rewrite cc_beta_eq; trivial.
 2:admit.
 rewrite cc_beta_eq; trivial.
 2:admit.
  apply couple_morph; auto with *.
  apply cc_lam_ext; auto with *.
  red; intros.
  rewrite H9.
  apply H6.
  rewrite TI_mono_succ in H7; auto.
  2:apply W0.W_F_mono; trivial.
  apply snd_typ_sigma with (y:=fst x) in H7; auto with *.
  apply cc_arr_elim with (1:=H7); trivial.
  rewrite <- H9; trivial.

  revert H7; apply TI_mono; auto with *.
   apply W0.W_F_mono; trivial.

   red; intros.
   apply ole_lts; eauto using isOrd_inv.
   transitivity o0; trivial; apply olts_le; auto.
Qed. 
Hint Resolve trad_body_morph trad_codom_mono trad_body_ty trad_irrel.


Lemma trad_ind P ord x :
  isOrd ord ->
  Proper (eq_set ==> eq_set ==> eq_set ==> iff) P ->
  (forall o w,
   isOrd o ->
   lt o ord ->
   w \in W0.W_F A' B' (TI (W0.W_F A' B') o) ->
   (forall y,
    y \in TI (W0.W_F A' B') o -> P o y (cc_app (trad ord) y)) ->
   forall u,
   isOrd u ->
   u \incl ord -> lt o u ->
   P u w (couple (snd (fst w))
           (cc_lam (B' (fst w)) (fun i => cc_app (trad ord) (cc_app (snd w) i))))) ->
  x \in TI (W0.W_F A' B') ord -> P ord x (cc_app (trad ord) x).
unfold trad; intros.
apply W0.WREC_ind with (A:=A') (B:=B') (U:=fun o w => Q o); intros; auto.
 apply trad_body_ty; trivial.
rewrite cc_beta_eq; eauto.
 rewrite <- TI_mono_succ in H5; auto.
 2:apply W0.W_F_mono; trivial.
 revert H5; apply TI_incl; auto with *.
  apply W0.W_F_mono; trivial.

  apply lt_osucc_compat; trivial.
Qed.

Lemma trad_eqn o w :
  isOrd o ->
  w \in TI (W0.W_F A' B') o -> 
  cc_app (trad o) w ==
  couple (snd (fst w))
           (cc_lam (B' (fst w)) (fun i => cc_app (trad o) (cc_app (snd w) i))).
intros.
pattern o at 0, w, (cc_app (trad o) w).
apply trad_ind; intros; trivial.
 apply morph_impl_iff3; auto with *.
 do 5 red; intros.
 rewrite <- H3; rewrite H4.
 apply couple_morph;[rewrite H2;reflexivity|apply cc_lam_morph; intros].
  unfold B'; rewrite H2; reflexivity.
  red; intros; rewrite H2; rewrite H5; reflexivity.

 reflexivity.
Qed.


Lemma trad_fcompat o o' :
  isOrd o -> 
  isOrd o' ->
  o \incl o' ->
  forall w, w \in TI (W0.W_F A' B') o ->
  cc_app (trad o) w == cc_app (trad o') w.
intros.
apply trad_ind; auto.
 admit.

 intros.
 rewrite trad_eqn; auto.
  apply couple_morph; auto with *.
  apply cc_lam_ext; intros; auto with *.
  red; intros.
  rewrite <- H11.
  apply H6.
  apply snd_typ_sigma with (y:=fst w0) in H5; auto with *.
  apply cc_arr_elim with (1:=H5); trivial.

  rewrite <- TI_mono_succ in H5; auto.
  2:apply W0.W_F_mono; trivial.
  revert H5; apply TI_mono; auto with *.
   apply W0.W_F_mono; trivial.

   red; intros.
   apply H1.
   apply isOrd_plump with o0; eauto using isOrd_inv.
   apply olts_le in H5; trivial.
Qed.

Lemma trad_ty : forall o,
  isOrd o ->
  forall w,
  w \in TI (W0.W_F A' B') o ->
  instance w (fst (fst w)) ->
  cc_app (trad o) w \in TIF Arg W_Fd o (fst (fst w)).
unfold trad.
intros.
revert H1.
apply trad_ind; intros; trivial.
  intros; auto.
 do 4 red; intros.
 split; intros.
  rewrite <- H2 in H5; generalize (H4 H5); rewrite H3.
  apply eq_elim.
  apply TIF_morph; auto with *.
  rewrite H2; reflexivity.

  rewrite H2 in H5; generalize (H4 H5); rewrite <- H3.
  apply eq_elim.
  apply TIF_morph; auto with *.
  rewrite H2; reflexivity.

 clear w H0; rename w0 into w.
 destruct H8 as (eqa,H8).
 assert (tyff : fst (fst w) \in Arg).
  apply fst_typ_sigma in H3.
  apply fst_typ_sigma in H3; trivial.
 assert (tysf : snd (fst w) \in A (fst (fst w))).
  apply fst_typ_sigma in H3.
  apply snd_typ_sigma with (y:=fst(fst w)) in H3; auto with *.
 assert (tys : forall i, i \in B' (fst w) -> cc_app (snd w) i \in TI (W0.W_F A' B') o0).
  intros.
  apply snd_typ_sigma with (y:=fst w) in H3; auto with *.
  apply cc_arr_elim with (1:=H3); trivial.
 apply TIF_intro with o0; trivial with *.
 apply couple_intro_sigma; trivial.
   admit.

   apply cc_prod_intro; intros.
    do 2 red; intros.
    rewrite H9; reflexivity.

    do 2 red; intros.
    rewrite H9; reflexivity.

    assert (cc_app (trad o) (cc_app (snd w) x) \in TIF Arg W_Fd o0 (fst (fst (cc_app (snd w) x)))).
     apply H4; auto.
     destruct H8 with (1:=H0).
     split;[reflexivity|intros].
     rewrite <- H9; auto.
    revert H9; apply eq_elim.
    apply (TIF_morph Arg W_Fd); auto with *.
    destruct H8 with (1:=H0).
    symmetry; trivial.
Qed.

Lemma trad_inj o o' w w' a :
  isOrd o ->
  isOrd o' ->
  w \in TI (W0.W_F A' B') o ->
  w' \in TI (W0.W_F A' B') o' ->
  cc_app (trad o) w == cc_app (trad o') w' ->
  instance w a ->
  instance w' a ->
  w == w'.
intros oo oo' tyw; revert o' oo' w' a.
apply trad_ind with (x:=w); trivial; clear w tyw; intros.
 admit.

 rewrite trad_eqn with (o:=o') in H7; trivial.
 destruct TI_elim with (3:=H6) as (o'',lto',w'ty); auto with *.
  do 2 red; intros; apply W0.W_F_ext; auto with *.
  red; intros; apply Bm; [apply fst_morph|apply snd_morph];trivial.
 rewrite W0.WF_eta with (2:=H1); trivial.
 rewrite W0.WF_eta with (2:=w'ty); trivial.
 unfold W0.WFmap.
 apply couple_injection in H7; destruct H7.
 assert (fst w == fst w').
  apply fst_typ_sigma in H1; trivial.
  rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ H1)).

  apply fst_typ_sigma in w'ty; trivial.
  rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ w'ty)).
  destruct H8 as (H8,_); destruct H9 as (H9,_).
  rewrite <- H8; rewrite <- H9; rewrite H7; reflexivity.
 assert (forall i, i \in B' (fst w) ->
   cc_app (trad o) (cc_app (snd w) i) == cc_app (trad o') (cc_app (snd w') i)).
  intros.
  generalize (cc_app_morph _ _ H10 _ _ (reflexivity i)).
  rewrite cc_beta_eq; trivial.
   rewrite cc_beta_eq; trivial.
    admit.
    unfold B'; rewrite <- H11; trivial.
   admit.
 apply couple_morph; trivial.
 apply cc_lam_ext; intros.
  unfold B'; rewrite H11; reflexivity.

  red; intros.
  rewrite <- H14; clear x' H14.
  apply H2 with (a:=C (fst (fst w)) (snd (fst w)) x) (o':=o'); auto.
   apply snd_typ_sigma with (y:=fst w) in H1; auto with *.
   apply cc_arr_elim with (1:=H1); trivial.

   apply snd_typ_sigma with (y:=fst w) in w'ty; auto with *.
   specialize cc_arr_elim with (1:=w'ty) (2:=H13).
   apply TI_incl; auto.
   apply W0.W_F_mono; trivial.

   destruct H8.
   rewrite <- H8; auto.

   destruct H9.
   rewrite H11; rewrite <- H9; apply H14.
   unfold B'; rewrite <- H11; trivial.
Qed.

Definition Wi o a := TIF Arg W_Fd o a.

Instance Wi_morph : morph2 Wi.
unfold Wi; apply TIF_morph.
Qed.

Lemma trad_surj : forall o w a,
  isOrd o ->
  a \in Arg ->
  w \in Wi o a ->
  exists2 w', w' \in TI (W0.W_F A' B') o /\ instance w' a &
    w == cc_app (trad o) w'.
intros o w a oo; revert w a.
pattern o at 1 2; apply isOrd_ind with (2:=oo); intros.
apply TIF_elim in H3; auto with *.
destruct H3 as (o',lty,wty).
Require Import ZFiso.
pose (trad_inv i := iso_inv (subset (TI (W0.W_F A' B') o') (fun w' => instance w' (C a (fst w) i)))
        (cc_app (trad o)) (cc_app (snd w) i)).
assert (invw : forall i, i \in B a (fst w) ->
   trad_inv i \in TI (W0.W_F A' B') o' /\
   instance (trad_inv i) (C a (fst w) i) /\
   cc_app (trad o) (trad_inv i) == cc_app (snd w) i).
 unfold trad_inv.
 intros.
 destruct H1 with o' (cc_app (snd w) i) (C a (fst w) i) as (w',(?,?),?); trivial.
  apply Cty; trivial.
  apply fst_typ_sigma in wty; trivial.

  apply snd_typ_sigma with (y:=fst w) in wty; auto with *.
  2:admit.
  apply cc_prod_elim with (1:=wty); trivial.

  unfold iso_inv.
  rewrite union_subset_singl with (y:=w') (y':=w'); auto with *.
   apply subset_intro; trivial.

   intros.
   rewrite <- H10 in H9.
   apply trad_inj with (a:=C a (fst w) i) in H9; auto.
    apply subset_elim1 in H7.
    revert H7; apply TI_incl; auto.
     admit.
     red; auto.

    apply subset_elim1 in H8.
    revert H8; apply TI_incl; auto.
     admit.
     red; auto.

    apply subset_elim2 in H7; destruct H7.
    rewrite H7; trivial.

    apply subset_elim2 in H8; destruct H8.
    rewrite H8; trivial.
pose (w' := couple (couple a (fst w))
        (cc_lam (B a (fst w)) (fun i =>
      iso_inv (subset (TI (W0.W_F A' B') o') (fun w' => instance w' (C a (fst w) i)))
         (cc_app (trad o)) (cc_app (snd w) i)))).
assert (tyw' : w' \in TI (W0.W_F A' B') y).
 apply TI_intro with o'; trivial.
  do 2 red; intros; apply W0.W_F_ext; auto with *.
  red; intros; apply Bm; [apply fst_morph|apply snd_morph]; trivial.

  apply couple_intro_sigma.
   admit.

   apply couple_intro_sigma; auto with *.
   apply fst_typ_sigma in wty; trivial.

  apply cc_prod_intro'; intros.
   admit.
   admit.

   apply Bm; [rewrite fst_def|rewrite snd_def]; reflexivity.

  apply (invw x H3).
exists w'.
 split; trivial.
 split; intros.
  unfold w'; rewrite fst_def; rewrite fst_def; reflexivity.

  unfold w'.
  rewrite fst_def.
  rewrite snd_def.
  rewrite snd_def.
  unfold B',w' in H3; rewrite fst_def in H3; rewrite fst_def in H3; rewrite snd_def in H3.
  rewrite cc_beta_eq; trivial.
  2:admit.
  apply (invw i H3).

 rewrite trad_eqn; trivial.
  transitivity (couple (fst w) (cc_lam (B a (fst w)) (fun i => cc_app (snd w) i))).
   apply W_Fd_eta with (2:=wty).
   do 2 red; intros; apply TIF_morph; auto with *.
  apply couple_morph.
   unfold w'; rewrite fst_def; rewrite snd_def; reflexivity.

   apply cc_lam_ext; intros.
    unfold B',w'; rewrite fst_def.
    rewrite fst_def; rewrite snd_def; reflexivity.

    red; intros.
    unfold w'; rewrite snd_def.
    rewrite cc_beta_eq.
     2:admit.
     2:rewrite <- H4; trivial.
    fold (trad_inv x').
    rewrite H4; symmetry; apply invw.
    rewrite <- H4; trivial.

  revert tyw'; apply TI_mono; auto.
  admit.
Qed.

Definition W_ord := W0.W_ord A' B'.

Lemma W_o_o : isOrd W_ord.
apply W0.W_o_o; trivial.
Qed.
Hint Resolve W_o_o.

Definition W := Wi W_ord.

Lemma W_eqn a : a \in Arg -> W a == W_Fd W a.
unfold W,Wi; intros.
rewrite <- TIF_mono_succ; auto with *.
apply eq_intro; intros.
 revert H0; apply TIF_incl; auto with *.

 apply trad_surj in H0; auto.
 destruct H0 as (w',(?,?),?).
 rewrite TI_mono_succ in H0; auto.
 2:apply W0.W_F_mono; trivial.
 unfold W_ord in H0; fold (W0.W2 A' B') in H0.
 rewrite <- W0.W2_eqn in H0; trivial.
 rewrite H2.
 destruct H1.
 rewrite H1.
 rewrite <- trad_fcompat with (4:=H0); auto.
  apply trad_ty; auto.
  split; auto with *.
  intros.
  rewrite <- H1; auto.

  red; intros; apply isOrd_trans with W_ord; auto.
Qed.


(* Universe facts *)

Require Import ZFgrothendieck.

Section W_Univ.

  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : omega \in U.  

  Hypothesis ArgU : Arg \in U.
  Hypothesis aU : forall a, a \in Arg -> A a \in U.
  Hypothesis bU : forall a x, a \in Arg -> x \in A a -> B a x \in U.

  Lemma G_W_Fd X :
    morph1 X ->
    (forall a, a \in Arg -> X a \in U) ->
    forall a, a \in Arg -> W_Fd X a \in U.
unfold W_Fd; intros.
apply G_sigma; intros; auto.
 admit.

 apply G_cc_prod; intros; auto.
 admit.
Qed.


  Lemma G_app f x : f \in U -> x \in U -> app f x \in U.
intros.
unfold app.
apply G_union; trivial.
apply G_subset; trivial.
unfold rel_image.
apply G_subset; trivial.
apply G_union; trivial.
apply G_union; trivial.
Qed.

 Lemma G_cc_app f x : f \in U -> x \in U -> cc_app f x \in U.
intros.
unfold cc_app.
unfold rel_image.
apply G_subset; trivial.
apply G_union; trivial.
apply G_union; trivial.
apply G_subset; trivial.
Qed.

  Lemma G_cc_lam dom f :
    ext_fun dom f ->
    dom \in U ->
    (forall x, x \in dom -> f x \in U) ->
    cc_lam dom f \in U.
intros.
unfold cc_lam.
apply G_union; trivial.
apply G_replf; auto with *.
intros.
apply G_replf; auto with *.
intros.
apply G_couple; trivial.
 apply G_trans with dom; trivial.

 apply G_trans with (f x); auto.
Qed.

  Lemma G_Wi o a : isOrd o -> o \in U -> a \in Arg -> Wi o a \in U.
unfold TIF; intros.
apply G_cc_app.
2:apply G_trans with Arg; trivial.
apply G_TR; trivial.
 admit.
 admit.

 intros.
 apply G_cc_lam; trivial; intros.
  admit.

  apply G_sup; trivial.
   admit.

   intros.
   apply G_W_Fd; intros; auto.
    apply cc_app_morph; reflexivity.

    apply G_cc_app; auto.
    apply G_trans with Arg; trivial.
Qed.

  Lemma G_W_ord : W_ord \in U.
apply W0.G_W_ord; trivial.
 apply G_sigma; trivial.
 do 2 red; intros; apply Am; trivial.

 intros.
 apply bU.
  apply fst_typ_sigma in H; trivial.

  apply snd_typ_sigma with (y:=fst a) in H; auto with *.
Qed.

  Lemma G_W a : a \in Arg -> W a \in U.
intros.
unfold W.
apply G_Wi; auto.
apply G_W_ord.
Qed.

End W_Univ.

End W_theory.

(* More on W_Fd: *)

Section MoreMorph.

Local Notation E := eq_set.
Lemma W_Fd_morph_all : Proper ((E==>E)==>(E==>E==>E)==>(E==>E==>E==>E)==>(E==>E)==>E==>E) W_Fd.
do 6 red; intros.
unfold W_Fd.
apply sigma_morph.
 apply H; trivial.

 red; intros.
 apply cc_prod_morph.
  apply H0; trivial.

  red; intros.
  apply H2; apply H1; trivial.
Qed.

Lemma Wi_morph_all : Proper (E==>(E==>E)==>(E==>E==>E)==>(E==>E==>E==>E)==>E==>E==>E) Wi.
do 7 red; intros.
unfold Wi.
unfold TIF.
apply cc_app_morph; trivial.
apply TR_morph; trivial.
do 2 red; intros.
apply cc_lam_morph; trivial.
red; intros.
apply sup_morph; trivial.
red; intros.
apply W_Fd_morph_all; trivial.
apply cc_app_morph.
apply H5; trivial.
Qed.

Lemma W_ord_morph_all : Proper (E==>(E==>E)==>(E==>E==>E)==>E) W_ord.
do 4 red; intros.
unfold W_ord.
Admitted.

Lemma W_morph_all : Proper (E==>(E==>E)==>(E==>E==>E)==>(E==>E==>E==>E)==>E==>E) W.
do 6 red; intros.
unfold W.
apply Wi_morph_all; trivial.
apply W_ord_morph_all; auto.
Qed.

End MoreMorph.


Section W_Simulation.

Variable Arg : set.
Variable A : set -> set.
Variable B : set -> set -> set.
Variable C : set -> set -> set -> set.
Hypothesis Am : morph1 A.
Hypothesis Bm : morph2 B.
Hypothesis Cm : Proper (eq_set==>eq_set==>eq_set==>eq_set) C.
Hypothesis Cty : forall a x y,
  a \in Arg ->
  x \in A a ->
  y \in B a x ->
  C a x y \in Arg.

Variable Arg' : set.
Variable A' : set -> set.
Variable B' : set -> set -> set.
Variable C' : set -> set -> set -> set.
Hypothesis Am' : morph1 A'.
Hypothesis Bm' : morph2 B'.
Hypothesis Cm' : Proper (eq_set==>eq_set==>eq_set==>eq_set) C'.
Hypothesis Cty' : forall a x y,
  a \in Arg' ->
  x \in A' a ->
  y \in B' a x ->
  C' a x y \in Arg'.

Lemma W_simul f p p' o o':
  morph1 f ->
  (forall p, p \in Arg -> f p \in Arg') ->
  (forall p, p \in Arg -> A p == A' (f p)) ->
  (forall p a, p \in Arg -> a \in A p -> B p a == B' (f p) a) ->
  (forall p a b, p \in Arg -> a \in A p -> b \in B p a ->
   f (C p a b) == C' (f p) a b) ->
  isOrd o ->
  p \in Arg ->
  f p == p' ->
  o == o' ->
  Wi Arg A B C o p == Wi Arg' A' B' C' o' p'.
intros.
transitivity (Wi Arg' A' B' C' o p').
 2:apply Wi_morph_all; auto with *.
clear o' H7.
revert p p' H5 H6; apply isOrd_ind with (2:=H4); intros.
clear o H4 H6; rename y into o.
assert (forall o', lt o' o ->
  W_Fd A B C (TIF Arg (W_Fd A B C) o') p ==
  W_Fd A' B' C' (TIF Arg' (W_Fd A' B' C') o') p').
 intros.
 unfold W_Fd.
 apply sigma_ext; intros; auto.
  rewrite <- H9; auto.

  apply cc_prod_ext; intros.
   rewrite <- H9; rewrite <- H10; auto.

   red; intros. 
   apply H7; trivial.
    apply Cty; auto.

    rewrite <- H9; rewrite <- H10; rewrite <- H12; auto.
apply eq_intro; intros.
 apply TIF_elim in H6; auto with *.
 2:apply W_Fd_morph; trivial.
 2:apply W_Fd_mono; trivial.
 destruct H6 as (o',?,?).
 rewrite H4 in H10; trivial.
 apply TIF_intro with o'; trivial.
  apply W_Fd_morph; trivial.
  apply W_Fd_mono; trivial.
  rewrite <- H9; auto.

 apply TIF_elim in H6; auto with *.
 2:apply W_Fd_morph; trivial.
 2:apply W_Fd_mono; trivial.
 2:rewrite <- H9; auto.
 destruct H6 as (o',?,?).
 rewrite <- H4 in H10; trivial.
 apply TIF_intro with o'; trivial.
  apply W_Fd_morph; trivial.
  apply W_Fd_mono; trivial.
Qed.

End W_Simulation.


(* --> ? *)
Definition if_prop P x y :=
  union2 (cond_set P x) (cond_set (~P) y).

Instance if_prop_morph : Proper (iff ==> eq_set ==> eq_set ==> eq_set) if_prop.
do 4 red; intros.
unfold if_prop.
apply union2_morph.
 apply cond_set_morph; auto.
 apply cond_set_morph; auto.
 rewrite H; reflexivity.
Qed.

Lemma if_left (P:Prop) x y : P -> if_prop P x y == x.
unfold if_prop; intros.
apply eq_intro; intros.
 apply union2_elim in H0; destruct H0.
  rewrite cond_set_ax in H0.
  destruct H0; trivial.

  rewrite cond_set_ax in H0; destruct H0; contradiction.

 apply union2_intro1; rewrite cond_set_ax; auto.
Qed.

Lemma if_right (P:Prop) x y : ~P -> if_prop P x y == y.
unfold if_prop; intros.
apply eq_intro; intros.
 apply union2_elim in H0; destruct H0.
  rewrite cond_set_ax in H0; destruct H0; contradiction.

  rewrite cond_set_ax in H0.
  destruct H0; trivial.

 apply union2_intro2; rewrite cond_set_ax; auto.
Qed.



Section BigParameter.
(* Waiving the universe constraint on Arg: *)

Variable Arg : set.
Variable A : set -> set.
Variable B : set -> set -> set.
Variable C : set -> set -> set -> set.
Hypothesis Am : morph1 A.
Hypothesis Bm : morph2 B.
Hypothesis Cm : Proper (eq_set==>eq_set==>eq_set==>eq_set) C.
Hypothesis Cty : forall a x y,
  a \in Arg ->
  x \in A a ->
  y \in B a x ->
  C a x y \in Arg.

Let L X a :=
  union2 (singl empty) 
    (sigma (A a) (fun x => sigma (B a x) (fun y => X (C a x y)))).


Instance Lmorph : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) L.
do 3 red; intros.
apply union2_morph;[reflexivity|].
apply sigma_morph; auto.
red; intros.
apply sigma_morph.
 apply Bm; auto.

 red; intros.
 apply H; apply Cm; trivial.
Qed.
Hint Resolve Lmorph.

Lemma L_intro1 X a : empty \in L X a.
apply union2_intro1.
apply singl_intro.
Qed.

Lemma L_intro2 a x y q X :
  morph1 X ->
  a \in Arg ->
  x \in A a ->
  y \in B a x ->
  q \in X (C a x y) ->
  couple x (couple y q) \in L X a.
unfold L; intros.
apply union2_intro2.
apply couple_intro_sigma; trivial.
 admit.

 apply couple_intro_sigma; trivial.
 admit.
Qed.

Definition L_match q f g :=
  if_prop (q==empty) f (g (fst q) (fst (snd q)) (snd (snd q))).

Lemma L_elim a q X :
  morph1 X ->
  a \in Arg ->
  q \in L X a ->
  q == empty \/
  exists2 x, x \in A a &
  exists2 y, y \in B a x &
  exists2 q', q' \in X (C a x y) &
  q == couple x (couple y q').
intros.
destruct union2_elim with (1:=H1);[left|right].
 apply singl_elim in H2; trivial.

 clear H1.
 assert (fst q \in A a).
  apply fst_typ_sigma in H2; auto.
 exists (fst q); trivial.
 assert (q == couple (fst q) (snd q)).
  apply surj_pair with (1:=subset_elim1 _ _ _ H2).
 apply snd_typ_sigma with (y:=fst q) in H2; auto with *. 
 2:admit.
 assert (fst (snd q) \in B a (fst q)).
  apply fst_typ_sigma in  H2; trivial.
 exists (fst (snd q)); trivial.
 exists (snd (snd q)).
  apply snd_typ_sigma with (y:=fst (snd q)) in H2; auto with *.
  admit.

  apply transitivity with (1:=H3).
  apply couple_morph; [reflexivity|].
  apply surj_pair with (1:=subset_elim1 _ _ _ H2).
Qed.





Lemma Lmono : mono_fam Arg L.
do 3 red; intros.
destruct L_elim with (3:=H3) as [znil|(x,xty,(y,yty,(q,qty,zcons)))]; trivial.
 rewrite znil; apply L_intro1.

 rewrite zcons; apply L_intro2; trivial.
 revert qty; apply H1.
 apply Cty; auto.
Qed.
Hint Resolve Lmono.

(* Arg' a == 1 + { x : A a ; y : B a x ; l : Arg' (C a x y) } *)
Definition Arg' : set -> set := TIF Arg L omega.

Instance Arg'_morph : morph1 Arg'.
apply TIF_morph; reflexivity.
Qed.

Lemma Arg'_ind P :
  Proper (eq_set ==> eq_set ==> iff) P ->
  (forall a, a\in Arg -> P a empty) ->
  (forall a x y q,
   a \in Arg ->
   x \in A a ->
   y \in B a x ->
   q \in Arg' (C a x y) ->
   P (C a x y) q ->
   P a (couple x (couple y q))) ->
  forall a q,
  a \in Arg -> 
  q \in Arg' a ->
  P a q.
unfold Arg'; intros.
revert a q H2 H3; elim isOrd_omega using isOrd_ind; intros.
rename y into o.
apply TIF_elim in H6; trivial.
destruct H6 as (o',?,?); trivial.
destruct L_elim with (3:=H7) as [qnil|(x,xty,(y,yty,(q',q'ty,qcons)))]; trivial.
 apply TIF_morph; reflexivity.

 rewrite qnil; auto.

 rewrite qcons.
 apply H1; trivial.
  revert q'ty; apply TIF_mono; auto.
  apply isOrd_inv with o; trivial.

  apply H4 with o'; trivial.
  apply Cty; trivial.
Qed.

Lemma Arg'_eqn a :
  a \in Arg ->
  Arg' a == L Arg' a.
intros.
apply eq_intro; intros.
 apply Arg'_ind with (5:=H0); intros; trivial.
  apply morph_impl_iff2; auto with *.
  do 4 red; intros.
  rewrite <- H2; rewrite <- H1; trivial.

  apply L_intro1.

  apply L_intro2; trivial with *.

 destruct L_elim with (3:=H0) as [qnil|(x,xty,(y,yty,(q,qty,qcons)))];
   trivial with *.
  apply TIF_intro with (osucc zero); auto with *.
  rewrite qnil; apply L_intro1.

  apply TIF_elim in qty; auto.
  destruct qty as (o,oo,qty).
  apply TIF_intro with (osucc o); auto.
  rewrite qcons; apply L_intro2; auto.
   apply TIF_morph; reflexivity.

   rewrite TIF_mono_succ; auto.
   eauto using isOrd_inv.
Qed.

Lemma Arg'_intro1 a :
  a \in Arg ->
  empty \in Arg' a.
intros.
rewrite Arg'_eqn; trivial.
apply L_intro1.
Qed.

Lemma Arg'_intro2 a x y q :
  a \in Arg ->
  x \in A a ->
  y \in B a x ->
  q \in Arg' (C a x y) ->
  couple x (couple y q) \in Arg' a.
intros.
rewrite Arg'_eqn; trivial.
apply L_intro2; trivial with *.
Qed.

Require Import ZFfixrec.

Section Arg'_recursor.

Variable f : set -> set.
Variable g : set -> set -> set -> (set -> set) -> set -> set.
Hypothesis fm : morph1 f.
Hypothesis gm :
  Proper (eq_set==>eq_set==>eq_set==>(eq_set==>eq_set)==>eq_set==>eq_set) g.
Definition Arg'_rec_rel q h :=
  forall P,
  Proper (eq_set==>(eq_set==>eq_set)==>iff) P ->
  P empty f ->
  (forall x y q' h,
   morph1 h ->
   P q' h ->
   P (couple x (couple y q')) (g x y q' h)) ->
  P q h.

Instance Arg'_rec_rel_morph : Proper (eq_set==>(eq_set==>eq_set)==>iff) Arg'_rec_rel.
apply morph_impl_iff2; auto with *.
do 5 red; intros.
cut (P x x0).
 apply H2; symmetry; trivial.
apply H1; trivial.
Qed.

Lemma Arg'_case q0 h :
  Arg'_rec_rel q0 h ->
  Arg'_rec_rel q0 h /\
  (q0 == empty -> (eq_set==>eq_set)%signature h f) /\
  forall x y q,
  q0 == couple x (couple y q) ->
  exists2 h', morph1 h' &
  Arg'_rec_rel q h' /\ (eq_set==>eq_set)%signature h (g x y q h').
intro H; apply H; intros.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 destruct H2; split; intros.
  revert H2; apply Arg'_rec_rel_morph; symmetry; auto.

  destruct H3; split; intros.
   rewrite <- H0 in H5; rewrite <- H1; auto.

   rewrite <- H0 in H5.
   destruct H4 with (1:=H5).
   exists x2; trivial.
   destruct H7; split; trivial.
   transitivity x0; auto with *.

 split; [red; auto|split;intros; auto].
 apply discr_mt_pair in H0; contradiction.

 destruct H1 as (?,(?,?)).
 split; [|split]; intros.
  red; intros.
  apply H6; trivial.
  apply H1; trivial.

  symmetry in H4; apply discr_mt_pair in H4; contradiction.

  exists h0; trivial.
  apply couple_injection in H4; destruct H4. 
  apply couple_injection in H5; destruct H5. 
  split; trivial.
   rewrite <- H6; trivial.

   apply gm; trivial.
Qed.
 

Lemma Arg'_uniq q h q' h':
  Arg'_rec_rel q h ->
  Arg'_rec_rel q' h' ->
  q == q' -> (eq_set==>eq_set)%signature h h'.
intros qrel.
revert q' h'.
apply qrel; intros.
 admit.

 apply Arg'_case in H.
 destruct H as (_,(?,_)).
 symmetry in H0|-*; auto.

 apply Arg'_case in H1.
 destruct H1 as (H1,(_,?)).
 destruct H3 with x y q'; auto with *.
 destruct H5.
 rewrite H6.
 apply gm; auto with *.
 apply H0 with q'; auto with *.
Qed.

Lemma Arg'_ex a q :
  a \in Arg ->
  q \in Arg' a ->
  exists2 h, morph1 h & Arg'_rec_rel q h.
intros.
pattern a, q; apply Arg'_ind with (5:=H0); intros; trivial.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 destruct H3.
 exists x1; trivial.
 rewrite <- H2; trivial.

 exists f; auto.
 red; auto.

 destruct H5.
 exists (g x y q0 x0).
  apply gm; auto with *.

  red; intros.
  apply H9; trivial.
  apply H6; trivial.
Qed.

Definition Arg'_rec q x :=
  uchoice (fun y => exists2 f, morph1 f & Arg'_rec_rel q f /\ y == f x).

Lemma Arg'_rec_morph : morph2 Arg'_rec.
do 3 red; intros.
apply uchoice_morph_raw.
red; intros.
split; intros.
 destruct H2.
 exists x2; trivial.
 rewrite <- H; rewrite <- H0; rewrite <- H1; auto.

 destruct H2.
 exists x2; trivial.
 rewrite H; rewrite H0; rewrite H1; auto.
Qed.

Lemma uchoice_Arg'_rec a q x :
  a \in Arg ->
  q \in Arg' a ->
  uchoice_pred (fun y => exists2 f, morph1 f & Arg'_rec_rel q f /\ y == f x).
intros.
split;[|split]; intros.
 destruct H2 as (h,?,(?,?)).
 exists h; trivial.
 split; trivial.
 rewrite <- H1; trivial.

 destruct Arg'_ex with (2:=H0); trivial.
 exists (x0 x); exists x0; auto with *.

 destruct H1 as (h,?,(?,?)); destruct H2 as (h',?,(?,?)).
 specialize Arg'_uniq with (1:=H3) (2:=H5); intro.
 rewrite H4; rewrite H6; apply H7; auto with *.
Qed.

Lemma Arg'_def a q :
  a \in Arg ->
  q \in Arg' a ->
  Arg'_rec_rel q (Arg'_rec q).
intros.
generalize
 (fun x => uchoice_def _ (uchoice_Arg'_rec a q x H H0)); intro.
destruct Arg'_ex with (2:=H0); trivial.
generalize H3; apply Arg'_rec_rel_morph; auto with *.
red; intros.
destruct (H1 x0) as (h,?,(?,?)).
transitivity (h y).
 rewrite <- H4; trivial.

 apply Arg'_uniq with (1:=H6)(2:=H3); reflexivity.
Qed.


Lemma Arg'_rec_mt a x :
  a \in Arg ->
  Arg'_rec empty x == f x.
intros.
destruct (uchoice_def _ (uchoice_Arg'_rec a empty x H (Arg'_intro1 _ H)))
 as (h,?,(?,?)).
transitivity (h x); trivial.
apply Arg'_uniq with empty empty; auto with *.
red; auto.
Qed.

Lemma Arg'_rec_cons a x y q z :
  a \in Arg ->
  x \in A a ->
  y \in B a x ->
  q \in Arg' (C a x y) ->
  Arg'_rec (couple x (couple y q)) z == g x y q (Arg'_rec q) z.
intros.
specialize Arg'_def with (1:=H) (2:=Arg'_intro2 _ _ _ _ H H0 H1 H2); intro.
apply Arg'_case in H3.
destruct H3 as (?,(_,?)).
destruct (H4 x y q); auto with *.
clear H4; destruct H6.
rewrite (H6 z z); auto with *.
apply gm; auto with *.
apply Arg'_uniq with (1:=H4)(q':=q); auto with *.
apply Arg'_def with (C a x y); trivial.
apply Cty; auto.
Qed.


End Arg'_recursor.

Definition Dec a q :=
  Arg'_rec (fun a => a) (fun x y q' F a => F (C a x y)) q a.


Lemma Dec_mt a : a \in Arg -> Dec a empty == a.
unfold Dec; intros.
rewrite Arg'_rec_mt with (a:=a); auto with *.
 do 2 red; auto.

 do 6 red; intros.
 apply H3.
 apply Cm; trivial.
Qed.

Lemma Dec_cons a x y q :
  a \in Arg ->
  x \in A a ->
  y \in B a x ->
  q \in Arg' (C a x y) ->
  Dec a (couple x (couple y q)) == Dec (C a x y) q.
intros.
unfold Dec.
apply Arg'_rec_cons with (a:=a); trivial.
 do 2 red; auto.

 do 6 red; intros.
 apply H6.
 apply Cm; trivial.
Qed.


Instance Dec_morph : morph2 Dec.
unfold Dec; do 3 red; intros.
apply Arg'_rec_morph; trivial.
Qed.


Lemma Dec_typ a q :
  a \in Arg ->
  q \in Arg' a ->
  Dec a q \in Arg.
intros.
apply Arg'_ind with (5:=H0); intros; auto with *.
 do 3 red; intros.
 rewrite H1; rewrite H2; reflexivity.

 rewrite Dec_mt; auto.

 rewrite Dec_cons; auto.
Qed.

Definition extln q x y :=
  Arg'_rec (fun _ => couple x (couple y empty))
    (fun x' y' q' F z => couple x' (couple y' (F z))) q empty.

Instance extln_morph : Proper (eq_set==>eq_set==>eq_set==>eq_set) extln.
Admitted.

Lemma extln_cons a x y q x' y' :
  a \in Arg ->
  x \in A a ->
  y \in B a x ->
  q \in Arg' (C a x y) ->
  x' \in A (Dec (C a x y) q) ->
  y' \in B (Dec (C a x y) q) x' ->
  extln (couple x (couple y q)) x' y' == couple x (couple y (extln q x' y')).
intros.
unfold extln at 1.
rewrite Arg'_rec_cons with (a:=a); auto.
 reflexivity.

 do 2 red; auto with *.

 do 6 red; intros.
 apply couple_morph;[|apply couple_morph;[|apply H8]]; trivial.
Qed.

Lemma extln_nil a x y :
  a \in Arg ->
  x \in A a ->
  y \in B a x ->
  extln empty x y == couple x (couple y empty).
intros.
unfold extln at 1.
rewrite Arg'_rec_mt with (a:=a); auto with *.

 do 2 red; auto with *.

 do 6 red; intros.
 apply couple_morph;[|apply couple_morph;[|apply H5]]; trivial.
Qed.

Lemma extln_typ : forall a q x y,
  a \in Arg ->
  q \in Arg' a ->
  x \in A (Dec a q) ->
  y \in B (Dec a q) x ->
  extln q x y \in Arg' a.
intros a q x y aty qty; revert x y; apply Arg'_ind with (5:=qty); trivial; intros.
 admit.

 rewrite Dec_mt in H0,H1; trivial.
 rewrite extln_nil with (a:=a0); trivial.
 apply Arg'_intro2; auto.
 apply Arg'_intro1; trivial.
 apply Cty; auto.

 rewrite Dec_cons in H4,H5; auto.
 rewrite extln_cons with (a:=a0); auto.
 apply Arg'_intro2; auto.
Qed.


Definition A'' a q := A (Dec a q).
Definition B'' a q := B (Dec a q).
Definition WW a := W (Arg' a) (A'' a) (B'' a) extln empty.

Instance A''_morph a : morph1 (A'' a).
unfold A''.
do 2 red; intros.
rewrite H; reflexivity.
Qed.

Instance B''_morph a : morph2 (B'' a).
unfold B''; do 3 red; intros.
rewrite H; rewrite H0; reflexivity.
Qed.


Lemma WW_eqn a : a \in Arg -> WW a == W_Fd A B C WW a.
intros.
unfold WW.
rewrite W_eqn; auto with *.
 apply sigma_ext.
  apply Am.
  apply Dec_mt; trivial.

  intros.
  unfold A'' in H0; rewrite Dec_mt in H0; trivial.
  symmetry; symmetry in H1.
  apply cc_prod_ext; intros.
   apply Bm; trivial.
   symmetry; apply Dec_mt; trivial.

   red; intros.

   apply W_simul with (f:=fun q => couple x (couple x0 q)); intros ; auto with *.
    apply extln_typ; auto.
    apply Cty; auto.
    rewrite H1; trivial.

    apply extln_typ; auto.

    do 2 red; intros; rewrite H4; reflexivity.

    apply Arg'_intro2; trivial.
     rewrite <- H1; trivial.
     rewrite <- H1; trivial.

    apply Am.
    rewrite Dec_cons; trivial.
     rewrite H1; reflexivity.
     rewrite <- H1; trivial.
     rewrite <- H1; trivial.

    apply Bm; auto with *.
    rewrite Dec_cons; trivial.
     rewrite H1; reflexivity.
     rewrite <- H1; trivial.
     rewrite <- H1; trivial.

    rewrite extln_cons with (a:=a); auto with *.
     rewrite <- H1; trivial.
     rewrite <- H1; trivial.
     rewrite <- H1; trivial.
     rewrite <- H1; trivial.

    apply W_o_o; auto with *.

    apply Arg'_intro1; trivial.
    apply Cty; auto.
    rewrite H1; trivial.

    rewrite <- extln_nil with (a:=a); auto with *.
     rewrite H3; reflexivity.
     rewrite <- H1; trivial.

    admit. (* TODO: W_ord does not depend on a... *)

 intros.
 apply extln_typ; trivial.

 apply Arg'_intro1; trivial.
Qed.

Section UniverseFacts.

  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : omega \in U.  

  (* We don't assume Arg is in U... *)
  Hypothesis aU : forall a, a \in Arg -> A a \in U.
  Hypothesis bU : forall a x, a \in Arg -> x \in A a -> B a x \in U.


  (* ... but Arg' is in U *)
  Lemma G_Arg' : forall a, a \in Arg -> Arg' a \in U.
unfold Arg'.
elim isOrd_omega using isOrd_ind; intros.
rewrite TIF_eq; auto.
apply G_sup; trivial.
 admit.

 apply G_incl with omega; trivial.

 intros.
 apply G_union2; trivial.
  apply G_singl; trivial.
  apply G_trans with omega; auto.
  apply zero_omega.

  apply G_sigma; auto.
   admit.

   intros.
   apply G_sigma; auto.
   admit.
Qed.


  Lemma G_WW a : a \in Arg -> WW a \in U.
intros.
unfold WW.
apply G_W; intros; auto with *.
 apply extln_typ; auto.

 apply G_Arg'; trivial.

 apply aU.
 apply Dec_typ; trivial.

 apply bU; trivial.
 apply Dec_typ; trivial. 

 apply Arg'_intro1; trivial.
Qed.

End UniverseFacts.

End BigParameter.