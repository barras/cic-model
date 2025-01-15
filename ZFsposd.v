Require Import ZF ZFpairs ZFsum ZFrelations ZFord ZFfix ZFfixfun.
Require Import ZFstable ZFiso ZFind_w ZFspos.

(** Inductive families. Indexes are modelled as a constraint over an inductive
    type defined without considering the index values.
 *)
(*
Section FamiliesAsSubsets.

  Variable I : set.
  Variable A : set.
  Variable F : set -> set.
  Hypothesis Fmono : Proper (incl_set==>incl_set) F.

  Variable Fd : (set->set)->set->set.
  Hypothesis Fdmono : mono_fam I Fd.
  
  Variable R : set->set->Prop. (* [R i x] means object x has index a∈I *)
  Hypothesis Rm : Proper (eq_set==>eq_set==>iff) R.
  Hypothesis F_subset :
    forall X, morph1 X ->
    forall i, i ∈ I ->
    Fd X i == subset (F (sup A X)) (R i).




*)
  
Require Import ZFind_wd.

Section InductiveFamily.

Variable Arg : set.

(** Given a function [f] that computes the index of any element of [X],
    [index(f)] shall compute the index of any element of [F(X)] it assumes
    the index information is stored within the data (not the case of non-uniform
    parameters...).
 *)
Record dpositive := mkDPositive {
  carrier :> positive;
  dpos_oper : (set -> set) -> set -> set;
  w3 : set -> set -> set;
  w4 : set -> set -> Prop
}.

Definition eqdpos (p1 p2:dpositive) :=
  eqpos p1 p2 /\
  (forall X X' a a', (eq_set==>eq_set)%signature X X' -> a==a' -> dpos_oper p1 X a == dpos_oper p2 X' a') /\
  (forall x x' i i', x==x' -> i==i' -> w3 p1 x i == w3 p2 x' i') /\
  (forall x x' i i', x==x' -> i==i' -> (w4 p1 x i <-> w4 p2 x' i')).

Instance eqdpos_sym : Symmetric eqdpos.
red; intros.
destruct H as (?&?&?&?); split;[|split;[|split]]; intros; symmetry; auto.
+apply H0; symmetry; trivial.
+ apply H1; symmetry; trivial.
+apply H2; symmetry; trivial.
Qed.
  
Instance eqdpos_trans : Transitive eqdpos.
red; intros.
destruct H as (?&?&?&?); destruct H0 as (?&?&?&?).
split;[|split;[|split]]; intros.
+transitivity y; trivial.
+transitivity (dpos_oper y X a); auto with *.
 apply H1; [|reflexivity].
 transitivity X'; auto with *.
+transitivity (w3 y x0 i); auto with *.
+transitivity (w4 y x0 i); auto with *.
Qed.

Instance eqdpos_morph : Proper (eqdpos==>eqdpos==>iff) eqdpos.
do 3 red; intros.
split; intros.
+transitivity x;[auto with *|].
 transitivity x0;[auto with *|trivial].
+transitivity y;[auto with *|].
 transitivity y0;[trivial|auto with *].
Qed.

Record isDPositive (p:dpositive) := {
  dpos_pos : isPositive p;
  dpm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) (dpos_oper p);
  dpmono : mono_fam Arg (dpos_oper p);
  w3m : morph2 (w3 p);
  w4m : Proper (eq_set==>eq_set==>iff) (w4 p);
  w3typ : forall x i, x ∈ w1 p -> i ∈ w2 p x -> w3 p x i ∈ Arg;
  dpm_iso : forall X a,
    ext_fun Arg X ->
    a ∈ Arg ->
    dpos_oper p X a == subset (pos_oper p (sup Arg X))
      (fun w => let w := wf p w in
       w4 p (fst w) a /\ forall i, i ∈ w2 p (fst w) -> cc_app (snd w) i ∈ X (w3 p (fst w) i))
}.

Definition dINDi p := TIF Arg (dpos_oper p).

Existing Instance dpm.
Hint Resolve dpmono : core.

Lemma dINDi_succ_eq : forall p o a,
  isDPositive p -> isOrd o -> a ∈ Arg -> dINDi p (osucc o) a == dpos_oper p (dINDi p o) a.
intros.
unfold dINDi.
apply TIF_mono_succ; auto with *.
Qed.

Lemma INDi_mono : forall p o o',
  isDPositive p -> isOrd o -> isOrd o' -> o ⊆ o' ->
  incl_fam Arg (dINDi p o) (dINDi p o').
intros.
red; intros.
assert (tm := TIF_mono); red in tm.
unfold dINDi.
apply tm; auto with *.
Qed.

Definition dIND (p:dpositive) := dINDi p (IND_clos_ord p).

Lemma dINDi_INDi p o :
  isDPositive p ->
  isOrd o ->
  forall a, a ∈ Arg ->
  dINDi p o a ⊆ INDi p o .
intros dp oo.
elim oo using isOrd_ind; intros.
red; intros.
apply TIF_elim in H3; auto.
2:apply dp.
destruct H3 as (y',?,?).
rewrite (dpm_iso _ dp) in H4; auto with *.
2:do 2 red; intros; apply TIF_morph; auto with *.
apply subset_elim1 in H4.
apply TI_intro with y'; trivial.
 apply Fmono_morph; apply dp.
revert H4; apply dp.
apply sup_lub.
do 2 red; intros; apply TIF_morph; auto with *.
intros.
apply H1; trivial.
Qed.

Lemma dINDi_inter_INDi p o :
  isDPositive p ->
  isOrd o ->
  forall x a o',
  isOrd o' ->
  a ∈ Arg ->
  x ∈ dINDi p o a ->
  x ∈ INDi p o' ->             
  x ∈ dINDi p o' a.
intros dp oo.
elim oo using isOrd_ind; intros.
apply TI_elim in H5; auto.
2:apply Fmono_morph; apply dp.
destruct H5 as (o'',?,?).
apply TIF_elim in H4; auto.
2:apply dp.
destruct H4 as (y',?,?).
apply TIF_intro with o''; auto with *.
rewrite (dpm_iso _ dp) in H7; trivial.
2:do 2 red; intros; apply TIF_morph; auto with *.
rewrite subset_ax in H7.
destruct H7 as (?,(x',eqx,(?,?))).
rewrite eqx in H7,H6 |- *.
clear eqx x.
assert (x_wf := H6).
apply dp in x_wf.
apply W_F_elim in x_wf.
2:apply dp.
assert (forall i, i ∈ w2 p (fst (wf p x')) ->
                      cc_app (snd (wf p x')) i ∈ TIF Arg (dpos_oper p) o'' (w3 p (fst (wf p x')) i)).
{intros.
 apply dp in H7.
 apply H1 with (z:=y'); trivial.
 +apply isOrd_inv with o'; trivial.
 +apply dp; trivial.
  apply fst_typ_sigma in H7; trivial.
 +apply H9; trivial.
 +apply x_wf; trivial. }
clear H9 H1.
rewrite (dpm_iso _ dp); trivial.
2:do 2 red; intros; apply TIF_morph; auto with *.
apply subset_intro; [|split; trivial].
assert (iso1 := w_iso _ (dpos_pos _ dp) (sup Arg (TIF Arg (dpos_oper p) o''))).
assert (iso2 := w_iso _ (dpos_pos _ dp) (TI (pos_oper p) o'')).
apply iso_fun_narrow with (1:=iso1)(2:=iso2); trivial.
+apply dp.
 apply sup_lub.
 do 2 red; intros; apply TIF_morph; auto with *.
 intros.
 apply dINDi_INDi; trivial.
 apply isOrd_inv with o'; trivial.
+destruct x_wf as (?&?&?).
 rewrite H11.
 apply W_F_intro; auto with *.
 apply dp.
 do 2 red; intros; apply cc_app_morph; auto with *.
 intros.
 rewrite sup_ax; auto with *.
 2:do 2 red; intros; apply TIF_morph; auto with *.
 exists (w3 p (fst (wf p x')) i).
 apply dp; auto.
 apply H10; trivial.
Qed.
 
Lemma dIND_eq : forall p a, isDPositive p -> a ∈ Arg -> dIND p a == dpos_oper p (dIND p) a.
intros p a dp tya.
assert (oo : isOrd (IND_clos_ord p)).
{unfold IND_clos_ord.
 apply W_ord_o.
 apply dp. }
apply incl_eq.
+unfold dIND; rewrite <- dINDi_succ_eq; trivial.
 apply INDi_mono; auto with *.
 red; intros; apply isOrd_trans with (IND_clos_ord p); auto.
+intros z tyz.
 apply dINDi_inter_INDi with (osucc(IND_clos_ord p)); auto.
 *rewrite dINDi_succ_eq; trivial. 
 *rewrite (dpm_iso _ dp) in tyz; trivial.
  2:do 2 red; intros; apply TIF_morph; auto with *.
  apply subset_elim1 in tyz.
  fold (IND p).
  rewrite IND_eq; [|apply dp].
  revert tyz; apply dp.
  apply sup_lub.
  do 2 red; intros; apply TIF_morph; auto with *.
  intros.
  apply dINDi_INDi; trivial.
Qed.

Lemma dINDi_dIND : forall p o,
  isDPositive p ->
  isOrd o ->
  forall a, a ∈ Arg ->
  dINDi p o a ⊆ dIND p a.
intros.
apply TIF_pre_fix; auto.
 apply H.
apply TIF_morph; reflexivity.
clear a H1; red; intros.
rewrite <- dIND_eq; trivial.
reflexivity.
Qed.

(** Library of dependent positive operators *)

(** Constraint on the index: corresponds to the conclusion of the constructor *)
Definition dpos_inst i :=
  mkDPositive (pos_cst (singl empty)) (fun _ a => cond_set (i==a) (singl empty))
    (fun _ _ => empty) (fun _ a => i==a).

Lemma dpos_inst_morph : Proper (eq_set==>eqdpos) dpos_inst.
do 2 red; intros.
split;[|split;[|split]]; simpl; intros; auto with *.
+apply pos_cst_morph; reflexivity.
+apply cond_set_morph;[|reflexivity].
 rewrite H,H1; reflexivity.
+rewrite H,H1; reflexivity.
Qed.

Lemma isDPos_inst i : isDPositive (dpos_inst i).
constructor; simpl; intros.
 apply isPos_cst.

 do 3 red; intros.
 rewrite H0; reflexivity.

 do 2 red; intros.
 reflexivity.

 do 3 red; reflexivity.

 do 3 red; intros.
 rewrite H0; reflexivity.

 apply empty_ax in H0; contradiction.

 apply eq_set_ax; intros z.
 rewrite cond_set_ax; rewrite subset_ax.
 split; destruct 1; split; trivial.
  exists z; auto with *.
  split; intros; trivial.
  apply empty_ax in H3; contradiction.

  destruct H2 as (?,_,(?,_)); trivial.
Qed.

Definition dpos_cst A :=
  mkDPositive (pos_cst A) (fun _ _ => A) (fun _ _ => empty) (fun _ _ => True).

Instance dpos_cst_morph : Proper (eq_set==>eqdpos) dpos_cst.
do 2 red; intros.
split;[|split;[|split]]; simpl; intros; auto with *.
apply pos_cst_morph; trivial.
Qed.

Lemma isDPos_cst A : isDPositive (dpos_cst A).
constructor; simpl; intros.
 apply isPos_cst.

 do 3 red; reflexivity.

 do 2 red; intros; reflexivity.

 do 3 red; reflexivity.

 do 3 red; reflexivity.

 apply empty_ax in H0; contradiction.

 apply eq_set_ax; intros z.
 rewrite subset_ax.
 split;[split|destruct 1]; trivial.
 exists z;[reflexivity|].
 split; intros; trivial.
 apply empty_ax in H2; contradiction.
Qed.

Definition dpos_rec j := mkDPositive pos_rec (fun X _ => X j) (fun _ _ => j) (fun _ _ => True).

 Instance dpos_rec_morph : Proper (eq_set==>eqdpos) dpos_rec.
do 2 red; intros.
split;[|split;[|split]]; simpl; intros; auto with *.
apply pos_rec_morph.
Qed.

Lemma isDPos_rec j : j ∈ Arg -> isDPositive (dpos_rec j).
constructor; simpl; intros; trivial.
 apply isPos_rec.

 do 3 red; intros.
 apply H0; reflexivity.

 do 2 red; intros.
 apply H2; trivial.

 do 3 red; reflexivity.

 do 3 red; reflexivity.

 apply subset_ext; intros.
  destruct H3.
  rewrite sup_ax in H2; trivial.
  destruct H2 as (b,?,?).
  assert (h := H4 _ (singl_intro empty)).
  unfold trad_reccall,comp_iso in h.
  rewrite snd_def in h; rewrite cc_beta_eq in h; trivial.
  apply singl_intro.

  rewrite sup_ax; trivial.
  exists j; trivial.

  exists x; [reflexivity|].
  split;[trivial|intros].
  unfold trad_reccall, comp_iso.
  rewrite snd_def; rewrite cc_beta_eq; trivial.
Qed.

Definition dpos_sum (F G:dpositive) :=
  mkDPositive (pos_sum F G)
    (fun X a => sum (dpos_oper F X a) (dpos_oper G X a))
    (fun x i => sum_case (fun x1 => w3 F x1 i) (fun x2 => w3 G x2 i) x)
    (fun x i => (forall x1, x == inl x1 -> w4 F x1 i) /\
                (forall x2, x == inr x2 -> w4 G x2 i)).

Lemma isDPos_sum F G :
  isDPositive F ->
  isDPositive G ->
  isDPositive (dpos_sum F G).
intros Fdp Gdp.
destruct (Fdp) as (Fp,Fdm,Fdmo,F3m,F4m,Fty,Fdep).
destruct (Gdp) as (Gp,Gdm,Gdmo,G3m,G4m,Gty,Gdep).
constructor; simpl; intros.
*apply isPos_sum; trivial.

*do 3 red; intros.
 apply sum_morph.
  apply Fdm; trivial.
  apply Gdm; trivial.

*do 2 red; intros.
 apply sum_mono.
  apply Fdmo; trivial.
  apply Gdmo; trivial.

*do 3 red; intros.
 apply sum_case_morph; trivial.
  red; intros.
  apply F3m; trivial.

  red; intros.
  apply G3m; trivial.

*do 3 red; intros.
 apply and_iff_morphism.
  apply fa_morph; intros x1.
  rewrite <- H.
  apply fa_morph; intros _.
  apply F4m; auto with *.

  apply fa_morph; intros x2.
  rewrite <- H.
  apply fa_morph; intros _.
  apply G4m; auto with *.

*apply sum_case_ind0 with (2:=H); intros.
  do 2 red; intros.
  rewrite H1; reflexivity.

  rewrite H2; rewrite dest_sum_inl.
  apply Fty; trivial.
  assert (F2m := w2m _ Fp).
  rewrite sum_case_inl0 in H0; eauto.
  revert H0; apply eq_elim; symmetry; apply F2m; trivial.
  rewrite H2; rewrite dest_sum_inl; reflexivity.

  rewrite H2; rewrite dest_sum_inr.
  apply Gty; trivial.
  assert (G2m := w2m _ Gp).
  rewrite sum_case_inr0 in H0; eauto.
  revert H0; apply eq_elim; symmetry; apply G2m; trivial.
  rewrite H2; rewrite dest_sum_inr; reflexivity.

*rewrite Fdep,Gdep; trivial.
 clear Fdep Gdep.
 rewrite subset_sum.
 apply sum_morph.
 +apply subset_morph;[reflexivity|].
  red; intros. 
  symmetry; apply exists_eq_intro; intros x' eqx; symmetry.
  assert (eqt : trad_sum (wf F) (wf G) x' == couple (inl (fst (wf F x))) (snd (wf F x))).
  {rewrite trad_sum_inl with (p:=x); [reflexivity| |symmetry; trivial].
   apply (w_iso _ Fp empty). }
  apply and_iff_morphism.
  {split; intros.
     split; intros.
     revert H2; apply (w4m _ Fdp); auto with *.
     rewrite eqt,fst_def in H3.
     apply inl_inj in H3; symmetry; trivial.

     rewrite eqt,fst_def in H3.
     apply discr_sum in H3; contradiction.

     destruct H2 as (H2,_).
     apply H2.     
     rewrite eqt, fst_def; reflexivity. }
  {apply fa_morph; intros i.
    apply impl_morph;[|intros].
    +apply in_set_morph;[reflexivity|].
     rewrite sum_case_inl0.
      apply (w2m _ Fp).
      rewrite eqt, fst_def, dest_sum_inl; reflexivity.
      exists(fst (wf F x)).
      rewrite eqt, fst_def; reflexivity.
    +apply in_set_morph.
      rewrite eqt, snd_def; reflexivity.

      apply H.
      apply Fty; trivial.
      apply (iso_typ (w_iso _ Fp (sup Arg X))) in H1.
      apply fst_typ_sigma in H1; trivial.

      rewrite sum_case_inl0.
      apply w3m; [trivial| |reflexivity].
      rewrite eqt, fst_def, dest_sum_inl; reflexivity.
      exists (fst (wf F x)).
      rewrite eqt, fst_def; reflexivity. }
 +apply subset_morph;[reflexivity|].
  red; intros. 
  symmetry; apply exists_eq_intro; intros x' eqx; symmetry.
  assert (eqt : trad_sum (wf F) (wf G) x' == couple (inr (fst (wf G x))) (snd (wf G x))).
  {rewrite trad_sum_inr with (p:=x); [reflexivity| |symmetry; trivial].
   apply (w_iso _ Gp empty). }
  apply and_iff_morphism.
  {split; intros.
     split; intros.
     rewrite eqt,fst_def in H3.
     symmetry in H3; apply discr_sum in H3; contradiction.

     revert H2; apply (w4m _ Gdp); auto with *.
     rewrite eqt,fst_def in H3.
     apply inr_inj in H3; symmetry; trivial.

     destruct H2 as (_,H2).
     apply H2.     
     rewrite eqt, fst_def; reflexivity. }
  {apply fa_morph; intros i.
    apply impl_morph;[|intros].
    +apply in_set_morph;[reflexivity|].
     rewrite sum_case_inr0.
      apply (w2m _ Gp).
      rewrite eqt, fst_def, dest_sum_inr; reflexivity.
      exists(fst (wf G x)).
      rewrite eqt, fst_def; reflexivity.
    +apply in_set_morph.
      rewrite eqt, snd_def; reflexivity.

      apply H.
      apply Gty; trivial.
      apply (iso_typ (w_iso _ Gp (sup Arg X))) in H1.
      apply fst_typ_sigma in H1; trivial.

      rewrite sum_case_inr0.
      apply w3m; [trivial| |reflexivity].
      rewrite eqt, fst_def, dest_sum_inr; reflexivity.
      exists (fst (wf G x)).
      rewrite eqt, fst_def; reflexivity. }
Qed.

Definition dpos_consrec (F G:dpositive) :=
  mkDPositive (pos_consrec F G)
    (fun X a => prodcart (dpos_oper F X a) (dpos_oper G X a))
    (fun x => sum_case (w3 F (fst x)) (w3 G (snd x)))
    (fun x i => w4 F (fst x) i /\ w4 G (snd x) i).

Instance dpos_consrec_morph : Proper (eqdpos==>eqdpos==>eqdpos) dpos_consrec.
do 3 red; intros.
unfold dpos_consrec.
split;[|split;[|split]]; simpl; intros.
+apply pos_consrec_morph; [apply H|apply H0].
+apply prodcart_morph.
  apply H; trivial.
  apply H0; trivial.
+apply sum_case_morph; trivial.
  red; intros; apply H; trivial.  
  apply fst_morph; trivial.
  red; intros; apply H0; trivial.  
  apply snd_morph; trivial.
+apply and_iff_morphism.
 apply H; trivial.
  apply fst_morph; trivial.
  red; intros; apply H0; trivial.  
  apply snd_morph; trivial.
Qed.
 
Lemma isDPos_consrec F G :
  isDPositive F ->
  isDPositive G ->
  isDPositive (dpos_consrec F G).
intros Fdp Gdp.
destruct (Fdp) as (Fp,Fdm,Fdmo,F3m,F4m,Fty,Fdep).
destruct (Gdp) as (Gp,Gdm,Gdmo,G3m,G4m,Gty,Gdep).
assert (w2mF := w2m _ Fp).
assert (w2mG := w2m _ Gp).
constructor; simpl; intros.
*apply isPos_consrec; trivial.

*do 3 red; intros.
 apply prodcart_morph.
  apply Fdm; trivial.
  apply Gdm; trivial.

*do 2 red; intros.
 apply prodcart_mono.
  apply Fdmo; trivial.
  apply Gdmo; trivial.

*do 3 red; intros.
 apply sum_case_morph; trivial.
  red; intros.
  apply F3m; trivial.
  apply fst_morph; trivial.

  red; intros.
  apply G3m; trivial.
  apply snd_morph; trivial.

*do 3 red; intros.
 apply and_iff_morphism.
  apply F4m; trivial.
  apply fst_morph; trivial.

  apply G4m; trivial.
  apply snd_morph; trivial.

*apply sum_case_ind with (6:=H0); intros.
  do 2 red; intros.
  rewrite H1; reflexivity.

  apply F3m; reflexivity.

  apply G3m; reflexivity.

  apply Fty; trivial.
  apply fst_typ in H; trivial.

  apply Gty; trivial.
  apply snd_typ in H; trivial.

*assert (wfmF := iso_funm (w_iso _ Fp (sup Arg X))).
 assert (wfmG := iso_funm (w_iso _ Gp (sup Arg X))).
rewrite Fdep,Gdep; trivial.
 clear Fdep Gdep.
 rewrite subset_prodcart.
 apply subset_morph;[reflexivity|].
 red; intros z tyz.
 apply exists_eq_intro; intros x eqx.
 apply exists_eq_intro; intros y eqy.
 specialize fst_typ with (1:=tyz) as tyx.
 specialize snd_typ with (1:=tyz) as tyy.
 assert (eqt: trad_prodcart (w2 F) (w2 G) (wf F) (wf G) z ==
                couple (couple (fst (wf F x)) (fst (wf G y)))
                     (cc_lam (sum (w2 F (fst (wf F x))) (w2 G (fst (wf G y))))
                        (fun i => sum_case (cc_app (snd (wf F x))) (cc_app (snd (wf G y))) i))).
 {apply trad_prodcart_eq; trivial. }
 assert (taut : forall A B C D, (A/\B)/\(C/\D) <-> ((A/\C)/\(B/\D))) by intuition auto.
 rewrite taut; clear taut.
 apply and_iff_morphism.
 {apply and_iff_morphism.
  apply F4m;[|reflexivity].
  rewrite eqt, !fst_def; reflexivity.
  apply G4m;[|reflexivity].
  rewrite eqt, !fst_def, snd_def; reflexivity. }
 {rewrite  currify_sum.
  apply and_iff_morphism.
  {apply fa_morph; intros i.
   apply impl_morph; [|intros tyi].
   {apply in_set_morph;[reflexivity|].
    rewrite trad_prodcart_eq with (5:=eqx)(6:=eqy), !fst_def; trivial.
    reflexivity. }
   {symmetry; apply forall_eq_intro.
    intros j eqj.
    apply in_set_morph.
    +apply trad_prodcart_snd_inl_eq; trivial.
    +symmetry; apply H.
      apply Fty; trivial.
      rewrite eqx in tyx.
      apply (w_iso _ Fp (sup Arg X)) in tyx.
      apply fst_typ_sigma in tyx; trivial.
     
      rewrite sum_case_inl0; [|eauto].
      rewrite eqt, !fst_def, eqj, dest_sum_inl; reflexivity. } }
  {apply fa_morph; intros i.
   apply impl_morph; [|intros tyi].
   {apply in_set_morph;[reflexivity|].
    rewrite trad_prodcart_eq with (5:=eqx)(6:=eqy), fst_def, snd_def; trivial.
    reflexivity. }
   {symmetry; apply forall_eq_intro.
    intros j eqj.
    apply in_set_morph.
    +apply trad_prodcart_snd_inr_eq; trivial.
    +symmetry; apply H.
      apply Gty; trivial.
      rewrite eqy in tyy.
      apply (w_iso _ Gp (sup Arg X)) in tyy.
      apply fst_typ_sigma in tyy; trivial.
     
      rewrite sum_case_inr0; [|eauto].
      rewrite eqt, fst_def, snd_def, eqj, dest_sum_inr; reflexivity. } } }
Qed.

Definition dpos_norec (A:set) (F:set->dpositive) :=
  mkDPositive (pos_norec A F)
    (fun X a => sigma A (fun y => dpos_oper (F y) X a))
    (fun x i => w3 (F (fst x)) (snd x) i)
    (fun x i => w4 (F (fst x)) (snd x) i).
 
Lemma isDPos_norec A F :
  Proper (eq_set ==> eqdpos) F ->
  (forall x, x ∈ A -> isDPositive (F x)) ->
  isDPositive (dpos_norec A F).
constructor; simpl; intros.
*apply isPos_consnonrec.
  do 2 red; intros.
  apply H in H1.
  apply H1.

  intros.
  apply H0; trivial.

*do 3 red; intros.
 apply sigma_morph; auto with *.
 red; intros.
 apply H; trivial.

*do 2 red; intros.
 apply sigma_mono; auto with *.
  do 2 red; intros. 
  apply H in H6.
  apply H6; auto with *.

  do 2 red; intros. 
  apply H in H6.
  apply H6; auto with *.

  intros.
  transitivity (dpos_oper (F x) Y a).
   apply H0; trivial.

   red; intro; apply eq_elim.
   apply (H _ _ H6); auto with *.

*do 3 red; intros.
 assert (ef := fst_morph _ _ H1).
 assert (es := snd_morph _ _ H1).
 apply H in ef.
 destruct ef as (?,(?,(?,?))).
 apply H5; trivial.

*do 3 red; intros.
 assert (ef := fst_morph _ _ H1).
 assert (es := snd_morph _ _ H1).
 apply H in ef.
 destruct ef as (?,(?,(?,?))).
 apply H6; trivial.

*assert (fty := fst_typ_sigma _ _ _ H1).
 apply snd_typ_sigma with (y:=fst x) in H1; auto with *.
  apply H0; trivial.

  do 2 red; intros.
  apply H in H4.
  apply H4.

*rewrite subset_sigma.
 2:{do 2 red; intros.
    apply pos_oper_morph;[|reflexivity].
    apply H; trivial. }
 apply sigma_ext;[reflexivity|].
 intros x x' tyx eqx.
 specialize H0 with (1:=tyx).
 destruct (H0) as (Fp,Fdm,Fdmo,F3m,F4m,Fty,Fdep).
 rewrite Fdep; trivial.
 apply subset_morph.
 {apply pos_oper_morph;[|reflexivity].
  apply H; trivial. }
 {red.
  intros z tyz.
  symmetry; apply exists_eq_intro.
  intros c eqc; symmetry.
  assert (eqt : trad_sigma (fun x=>wf(F x)) c ==
                  couple (couple x (fst (wf (F x) z))) (snd (wf (F x) z))).
  {apply trad_sigma_eq;[|symmetry; trivial].
   do 3 red; intros.
   apply H; trivial.
   rewrite eqx; trivial. }
  apply and_iff_morphism.
  +apply H;[| |reflexivity].
   rewrite eqt, !fst_def; reflexivity.
   rewrite eqt, !fst_def, snd_def; reflexivity.
  +apply fa_morph; intros i.
   apply impl_morph; intros.
   {apply in_set_morph;[reflexivity|].
    apply H.
     rewrite eqt, !fst_def; reflexivity.
     rewrite eqt, !fst_def, snd_def; reflexivity. }
   {apply in_set_morph.
    +rewrite eqt, snd_def; reflexivity.
    +apply H1.
     {apply Fty; trivial.
      apply (w_iso _ Fp) in tyz.
      apply fst_typ_sigma in tyz; trivial. }
     {apply H;[| |reflexivity].
       rewrite eqt, !fst_def; reflexivity.
      rewrite eqt, !fst_def, snd_def; reflexivity. } } }
Qed.

Definition dpos_param (A:set) (F:set->dpositive) :=
  mkDPositive (pos_param A F)
    (fun X a => cc_prod A (fun y => dpos_oper (F y) X a))
    (fun x i => w3 (F (fst i)) (cc_app x (fst i)) (snd i))
    (fun x i => forall k, k ∈ A -> w4 (F k) (cc_app x k) i).
 
Lemma isDPos_param A F :
  Proper (eq_set ==> eqdpos) F ->
  (forall x, x ∈ A -> isDPositive (F x)) ->
  isDPositive (dpos_param A F).
constructor; simpl; intros.
*apply isPos_param.
  do 2 red; intros.
  apply H in H1.
  apply H1.

  intros.
  apply H0; trivial.

*do 3 red; intros.
 apply cc_prod_ext; auto with *.
 red; intros.
 apply H; trivial.

*do 2 red; intros.
 apply cc_prod_covariant; intros; auto with *.
  do 2 red; intros. 
  apply H in H6.
  apply H6; auto with *.

  apply H0; trivial.

*do 3 red; intros.
 assert (ef := fst_morph _ _ H2).
 assert (es := snd_morph _ _ H2).
 apply H in ef.
 destruct ef as (?,(?,(?,?))).
 apply H5; trivial.
 apply cc_app_morph; trivial.
 apply fst_morph; trivial.

*do 3 red; intros.
 apply fa_morph; intros k.
 apply fa_morph; intros kty.
 apply H0; trivial.
 rewrite H1; reflexivity.

*assert (fty := fst_typ_sigma _ _ _ H2).
 apply snd_typ_sigma with (y:=fst i) in H2; auto with *.
  apply H0; trivial.
  apply cc_prod_elim with (1:=H1); trivial.

  do 2 red; intros.
  apply H; trivial.
  rewrite H4; reflexivity.

*set (P:=fun y w => let w0 := wf (F y) w in
                       w4 (F y) (fst w0) a /\
                         (forall i, i ∈ w2 (F y) (fst w0) ->
                                    cc_app (snd w0) i ∈ X (w3 (F y) (fst w0) i))).
 rewrite <- subset_cc_prod
   with (B:=fun y =>pos_oper (F y) (sup Arg X))
        (P:=fun y w => let w0 := wf (F y) w in
                       w4 (F y) (fst w0) a /\
                         (forall i, i ∈ w2 (F y) (fst w0) ->
                                    cc_app (snd w0) i ∈ X (w3 (F y) (fst w0) i))).
 2:{do 2 red; intros.
    apply H;[trivial|reflexivity]. }
 2:{intros.
    specialize H0 with (1:=H3).
    specialize (H _ _ H4) as eqp.
    rewrite (dpm_iso _ H0); trivial.
    apply subset_morph.    
    apply eqp; reflexivity.
    change (eq_pred (pos_oper (F x) (sup Arg X)) (P x) (P x')).
    red; intros.
    assert (e1 : wf (F x) x0 == wf (F x') x0).
    {apply eqp; reflexivity. }
    assert (e2 := fst_morph _ _ e1).
    apply and_iff_morphism.
     apply eqp;[trivial|reflexivity].    
    apply fa_morph; intros i.
    apply impl_morph; intros.     
     apply in_set_morph;[reflexivity|].
     apply eqp; trivial.
     apply in_set_morph; [rewrite e1; reflexivity|].
     apply H1.
      apply H0; trivial.
      apply H0 in H5.
      apply fst_typ_sigma in H5; trivial.
      apply eqp;[trivial|reflexivity]. }
 apply subset_morph; [reflexivity|].
 intros f tyf.
 rewrite currify_sigma.
 2:{do 2 red; intros.
    apply H; trivial.
    apply cc_app_morph; trivial.
    reflexivity. }
 2:{intros.
    revert H5; apply in_set_morph; symmetry.
    apply cc_app_morph; [reflexivity|trivial].
    apply H1.
    {apply sigma_elim in H3.
     2:{do 2 red; intros.
        apply H; trivial.
        apply cc_app_morph; [reflexivity|trivial]. }
     destruct H3 as (eqc & tyx & tyy).
     specialize H0 with (1:=tyx).
     destruct (H0) as (Fp,Fdm,Fdmo,F3m,F4m,Fty,_).
     destruct (Fp) as (opm,w2m,wiso).
     destruct (wiso (sup Arg X)) as (wfm,wfty,_,_).
     rewrite trad_cc_prod_fst_eq with (y:=cc_app f (fst x)); trivial.
     2:do 3 red; intros; apply H; trivial.
     2:do 3 red; intros; apply H; trivial.
     2:reflexivity.
     apply Fty.
     +apply cc_prod_elim with (2:=tyx) in tyf.
      apply wfty in tyf.
      apply fst_typ_sigma in tyf; trivial.
     +apply eq_elim with (2:=tyy).
      apply w2m.
      apply trad_cc_prod_fst_eq; trivial.
      do 3 red; intros; apply H; trivial.
      do 3 red; intros; apply H; trivial.
      reflexivity. }
    {apply H;[rewrite H4;reflexivity| |rewrite H4; reflexivity].
     apply cc_app_morph; [reflexivity|rewrite H4;reflexivity]. } }
 rewrite and_forall_commut.
 apply fa_morph; intros x.
 rewrite and_forall_commut.
 apply fa_morph; intros tyx.
 apply exists_eq_intro; intros.
 specialize H0 with (1:=tyx).
 destruct (H0) as (Fp,Fdm,Fdmo,F3m,F4m,Fty,_).
 destruct (Fp) as (opm,w2m,wiso).
 destruct (wiso (sup Arg X)) as (wfm,wfty,_,_).
 assert (w2m' : morph2 (fun a => w2 (F a))) by (do 3 red; intros; apply H; trivial).
 assert (wfm' : morph2 (fun a => wf (F a))) by (do 3 red; intros; apply H; trivial).
 clear wiso.
 apply and_iff_morphism.
 {rewrite trad_cc_prod_fst_eq with (4:=H3); trivial.
  reflexivity. }
 {apply fa_morph; intros i.
  apply impl_morph; intros.
  {rewrite trad_cc_prod_fst_eq with (4:=H3); trivial.
   reflexivity. }
  {apply in_set_morph.
   {rewrite trad_cc_prod_snd_eq with (5:=H3); trivial.
    reflexivity. }
   {apply H1.
    {apply Fty; trivial.
     apply cc_prod_elim with (2:=tyx) in tyf.
     rewrite H3 in tyf.
     apply wfty in tyf.
     apply fst_typ_sigma in tyf; trivial. }
    {apply H;[rewrite fst_def;reflexivity| |rewrite snd_def; reflexivity].
     rewrite fst_def.
     rewrite trad_cc_prod_fst_eq with (4:=H3); trivial.
     reflexivity. } } } }
Qed.


End InductiveFamily.


(** * Universe constraints: predicativity *)

Require Import ZFgrothendieck.

Section InductiveUniverse.

  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : omega ∈ U.

  Let Unonmt : empty ∈ U.
apply G_trans with omega; trivial.
Qed.

  Variable Arg : set.
    (* Here the universe of Arg matters... but we should be able
     to avoid it (same argument as non-uniform parameters *)
  Hypothesis G_arg : Arg ∈ U.

  Definition dpos_universe (p:dpositive) := pos_universe U (carrier p).
  
  Variable p : dpositive.
  Hypothesis p_ok : isDPositive Arg p.
  Hypothesis p_univ : dpos_universe p.

  Variable a : set.
  Hypothesis tya : a ∈ Arg.
  
  Lemma G_dIND : dIND Arg p a ∈ U.
unfold dIND, dINDi.
apply G_TIF; trivial; try apply p_ok.
+clear a tya; intros.
 rewrite (dpm_iso _ _ p_ok); auto.
 apply G_subset; trivial.
 apply p_univ.
 apply G_sup; auto.
 
+unfold IND_clos_ord.
 apply W_ord_o; apply p_ok.

+unfold IND_clos_ord; apply G_W_ord; trivial.
  apply p_ok.
  apply p_univ.
  apply p_univ.
Qed.

  Lemma G_dINDi o : isOrd o -> dINDi Arg p o a ∈ U.
intros.
apply G_incl with (dIND Arg p a); trivial.
 apply G_dIND; trivial.

 apply dINDi_dIND; trivial.
Qed.

  (* In a univalent model, Arg definitely should be in U to prove [dpos_univ_inst]:
     "indices matter" *)
  Lemma dpos_univ_inst i : dpos_universe (dpos_inst i).
apply pos_univ_cst; trivial.
apply G_singl; trivial.
Qed.
  
  Lemma dpos_univ_cst A : A ∈ U -> dpos_universe (dpos_cst A).
apply pos_univ_cst; trivial.
Qed.

  Lemma dpos_univ_rec j : dpos_universe (dpos_rec j).
apply pos_univ_rec; trivial.
Qed.

  Lemma dpos_univ_sum p1 p2 :
    dpos_universe p1 -> dpos_universe p2 -> dpos_universe (dpos_sum p1 p2).
apply pos_univ_sum; trivial.
Qed.

  Lemma dpos_univ_prodcart p1 p2 :
    dpos_universe p1 -> dpos_universe p2 -> dpos_universe (dpos_consrec p1 p2).
apply pos_univ_prodcart; trivial.
Qed.

  Lemma dpos_univ_norec A p' :
    Proper (eq_set==>eqdpos) p' ->
    A ∈ U -> (forall x, x ∈ A -> dpos_universe (p' x)) ->
       dpos_universe (dpos_norec A p').
intros; apply pos_univ_norec; trivial.
do 2 red; intros; apply H; trivial.
Qed.

  Lemma dpos_univ_param A p' :
    Proper (eq_set==>eqdpos) p' ->
    A ∈ U -> (forall x, x ∈ A -> dpos_universe (p' x)) ->
       dpos_universe (dpos_param A p').
intros; apply pos_univ_param; trivial.
do 2 red; intros; apply H; trivial.
Qed.

End InductiveUniverse.

(******************************************************************************)
(* Summary of what has been constructed here *)

Module Wd.

Section Wd.
(** Parameters of W-types *)
Variable A : set.
Variable B : set -> set.
Hypothesis Bext : ext_fun A B.

(** Index type *)
Variable Arg : set.

(** Constraints on the subterms *)
Hypothesis f : set -> set -> set.
Hypothesis fm : morph2 f.
Hypothesis ftyp : forall x i,
  x ∈ A -> i ∈ B x -> f x i ∈ Arg.

(** Instance introduced by the constructors *)
Hypothesis g : set -> set.
Hypothesis gm : morph1 g.

Definition Wdp : dpositive :=
  dpos_norec A (fun x => dpos_consrec (dpos_param (B x) (fun i => dpos_rec (f x i))) (dpos_inst (g x))).

Definition Wsup x h := couple x (couple (cc_lam (B x) h) empty).

Lemma sup_typ X x h :
  morph1 X ->
  morph1 h ->
  x ∈ A ->
  (forall i, i ∈ B x -> h i ∈ X (f x i)) ->
  Wsup x h ∈ dpos_oper Wdp X (g x).
simpl; intros.
apply couple_intro_sigma; trivial.
 do 2 red; intros.
 apply prodcart_morph.
  apply cc_prod_ext; auto.
  red; intros; apply H. 
  apply fm; auto.
 apply cond_set_morph; auto with *.
 rewrite H4; reflexivity.

 apply couple_intro.
  apply cc_prod_intro; intros; auto with *.
  do 2 red; intros; apply H; apply fm; auto with *. 

  rewrite cond_set_ax; split.
   apply singl_intro.
   reflexivity.
Qed.

End Wd.
End Wd.
  
