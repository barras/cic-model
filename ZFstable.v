
Require Import ZFsum ZFpairs ZFrelations ZFnats ZFord ZFfix.
Import IZF.

Lemma morph_is_ext : forall F X, morph1 F -> ext_fun X F.
red; red; intros.
apply H; trivial.
Qed.
Hint Resolve morph_is_ext.

(* Extentionality *)
Lemma cst_is_ext : forall X o, ext_fun o (fun _ => X).
do 2 red; reflexivity.
Qed.
Hint Resolve cst_is_ext.

Lemma sum_is_ext : forall o F G,
  ext_fun o F ->
  ext_fun o G ->
  ext_fun o (fun y => sum (F y) (G y)).
do 2 red; intros.
rewrite (H x x'); trivial.
rewrite (H0 x x'); trivial.
reflexivity.
Qed.
Hint Resolve sum_is_ext.

Lemma func_is_ext : forall x X F,
  ext_fun x F ->
  ext_fun x (fun x => func X (F x)).
do 2 red; intros.
apply func_morph; auto.
reflexivity.
Qed.
Hint Resolve func_is_ext.

Lemma increasing_is_ext : forall F,
  increasing F ->
  forall o, isOrd o ->
  ext_fun o F.
intros F Fincr o H.
red; red; intros.
apply eq_intro.
 apply Fincr.
  rewrite <- H1; eauto using isOrd_inv.
  eauto using isOrd_inv.
  rewrite H1; reflexivity.
 apply Fincr.
  eauto using isOrd_inv.
  rewrite <- H1; eauto using isOrd_inv.
  rewrite H1; reflexivity.
Qed.
Hint Resolve increasing_is_ext.

(* Stable functions *)

Definition stable2 F :=
  forall X Y, inter2 (F X) (F Y) \incl F (inter2 X Y).

Definition stable F :=
  forall X,
  inter (replf X F) \incl F (inter X).

Lemma stable2_weaker :
  forall F, morph1 F -> stable F -> stable2 F.
red; red; intros.
apply H0.
rewrite inter2_def in H1; destruct H1.
apply inter_intro.
 intros.
 rewrite replf_ax in H3.
  destruct H3.
  rewrite H4.
  apply pair_elim in H3; destruct H3; rewrite H3; trivial.

  red; red; intros; apply H; trivial.

 exists (F X).
 rewrite replf_ax.
  exists X; auto with *.

  red; red; intros; apply H; trivial.
Qed.

Lemma cst_stable : forall A, stable (fun _ => A).
red; red; intros.
apply inter_elim with (1:=H) (y:=A).
destruct inter_wit with (2:=H).
 red; red; reflexivity.
rewrite replf_ax; auto.
exists x; auto with *.
Qed.

Lemma id_stable : stable (fun x => x).
red; red; intros.
destruct inter_wit with (2:=H).
 red; red; auto.
apply inter_intro; eauto.
intros.
apply inter_elim with (1:=H).
rewrite replf_ax.
2:red; red; auto.
exists y;auto with *.
Qed.

Lemma power_stable : stable power.
red; red; intros.
apply power_intro; intros.
destruct inter_non_empty with (1:=H).
rewrite replf_ax in H1.
2:red;red;intros;apply power_morph; trivial.
destruct H1.
apply inter_intro; eauto.
clear H2 H3 H1 x0 x.
intros.
assert (z \in power y).
 apply inter_elim with (1:=H).
 rewrite replf_ax.
 2:red;red;intros;apply power_morph; trivial.
 exists y; auto with *.
rewrite power_ax in H2; auto.
Qed.


Lemma prodcart_stable : forall F G,
  morph1 F ->
  morph1 G ->
  stable F ->
  stable G ->
  stable (fun y => prodcart (F y) (G y)).
intros F G Fm Gm Fs Gs.
red; red ;intros.
destruct inter_wit with (2:=H) as (w,H0).
 do 2 red; intros.
 rewrite H0; reflexivity.
assert (forall x, x \in X -> z \in prodcart (F x) (G x)).
 intros.
 apply inter_elim with (1:=H).
 rewrite replf_ax.
  exists x; auto with *.

  red; red; intros.
  rewrite H3; reflexivity.
clear H.
assert (z \in prodcart (F w) (G w)) by auto.
rewrite (surj_pair _ _ _ H).
apply couple_intro.
 apply Fs.
 apply inter_intro.
  intros.
  rewrite replf_ax in H2; trivial.
  2:red;red;auto.
  destruct H2.
  rewrite H3; apply H1 in H2; apply fst_typ in H2; trivial.

  exists (F w); rewrite replf_ax; auto.
  eauto with *.

 apply Gs.
 apply inter_intro.
  intros.
  rewrite replf_ax in H2; auto.
  destruct H2.
  rewrite H3; apply H1 in H2; apply snd_typ in H2; trivial.

  exists (G w); rewrite replf_ax; auto.
  eauto with *.
Qed.

Lemma sigma_stable : forall F G,
  morph1 F ->
  morph2 G ->
  stable F ->
  (forall x, stable (fun y => G y x)) ->
  stable (fun y => sigma (F y) (G y)).
intros F G Fm Gm Fs Gs.
assert (Hm : morph1 (fun y => sigma (F y) (G y))).
 do 2 red; intros.
 apply subset_morph.
  apply prodcart_morph; auto with *.
  apply union_morph.
  apply replf_morph; auto with *.
  red; intros.
  apply Gm; trivial.

 red; intros.
 rewrite H; reflexivity.
red; red ;intros.
destruct inter_wit with (2:=H) as (w,H0); trivial.
assert (forall x, x \in X -> z \in sigma (F x) (G x)).
 intros.
 apply inter_elim with (1:=H).
 rewrite replf_ax; auto.
 exists x; auto with *.
clear H.
assert (z \in sigma (F w) (G w)) by auto.
rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ H)).
apply couple_intro_sigma.
 red;red;intros;apply Gm; auto with *.

 apply Fs.
 apply inter_intro.
  intros.
  rewrite replf_ax in H2; auto.
  destruct H2.
  rewrite H3; apply H1 in H2; apply fst_typ_sigma in H2; trivial.

  exists (F w); rewrite replf_ax; auto.
  eauto with *.

 apply Gs.
 apply inter_intro.
  intros.
  rewrite replf_ax in H2.
   destruct H2.
   rewrite H3; apply H1 in H2; apply snd_typ_sigma with (y:=fst z) in H2;
   auto with *.
   red; red; intros; apply Gm; auto with *.

   red; red; intros; apply Gm; auto with *.

  exists (G w (fst z)); rewrite replf_ax.
  2:red;red;intros; apply Gm; auto with *.
  eauto with *.
Qed.

Lemma sum_stable : forall F G,
  morph1 F ->
  morph1 G ->
  stable F ->
  stable G ->
  stable (fun y => sum (F y) (G y)).
intros F G Fm Gm Fs Gs.
red; red ;intros.
destruct inter_wit with (2:=H) as (w,H0).
 do 2 red; intros.
 rewrite H0; reflexivity.
assert (forall x, x \in X -> z \in sum (F x) (G x)).
 intros.
 apply inter_elim with (1:=H).
 rewrite replf_ax.
  exists x; auto with *.

  red; red; intros.
  rewrite H3; reflexivity.
clear H.
assert (z \in sum (F w) (G w)) by auto.
apply sum_ind with (3:=H); intros.
 rewrite H3; apply inl_typ.
 apply Fs; eauto.
 apply inter_intro.
  intros.
  rewrite replf_ax in H4.
  2:red;red;intros;apply Fm; trivial.
  destruct H4.
  rewrite H5; clear H5 y.
  assert (z \in sum (F x0) (G x0)) by auto.
  apply sum_ind with (3:=H5); intros.
   rewrite H7 in H3; apply inl_inj in H3; rewrite <-H3; trivial.

   rewrite H3 in H7; apply discr_sum in H7; contradiction.

  exists (F w).
  rewrite replf_ax.
  2:red;red;intros;apply Fm;trivial.
  exists w; auto with *.

 rewrite H3; apply inr_typ.
 apply Gs; eauto.
 apply inter_intro.
  intros.
  rewrite replf_ax in H4.
  2:red;red;intros;apply Gm; trivial.
  destruct H4.
  rewrite H5; clear H5 y0.
  assert (z \in sum (F x) (G x)) by auto.
  apply sum_ind with (3:=H5); intros.
   rewrite H7 in H3; apply discr_sum in H3; contradiction.

   rewrite H7 in H3; apply inr_inj in H3; rewrite <-H3; trivial.

  exists (G w).
  rewrite replf_ax.
  2:red;red;intros;apply Gm;trivial.
  exists w; auto with *.
Qed.

Lemma func_stable : forall A,
  stable (func A).
red; red; intros.
destruct inter_wit with (2:=H); eauto with *.
assert (forall x, x \in X -> z \in func A x).
 intros.
 apply inter_elim with (1:=H).
 rewrite replf_ax.
  exists x0; auto with *.

  red; red; intros.
  rewrite H3; reflexivity.
clear H.
assert (z \in func A x) by auto.
apply func_narrow with x; trivial.
intros.
apply inter_intro; eauto.
intros.
apply app_typ with A; auto.
Qed.

(* Stability of ordinal-indexed families *)

Definition stable2_ord F :=
  forall x, isOrd x ->
  forall y, isOrd y ->
  inter2 (F x) (F y) \incl F (inter2 x y).

Definition stable_ord F :=
  forall X,
  (forall x, x \in X -> isOrd x) ->
  inter (replf X F) \incl F (inter X).

Lemma compose_stable : forall F G,
  Proper (incl_set ==> incl_set) F ->
  morph1 G ->
  stable F ->
  stable_ord G ->
  stable_ord (fun o => F (G o)).
intros F G Fm Gm Fs Gs.
red; intros.
transitivity (F (inter (replf X G))).
 red; intros.
 apply Fs.
 rewrite compose_replf; trivial.
  red; red; intros; apply Gm; trivial.

  apply Fmono_morph in Fm.
  red; red; intros; apply Fm; trivial.

 apply Fm.
 apply Gs; trivial.
Qed.
 
Lemma TI_stable2 : forall F,
  Proper (incl_set ==> incl_set) F ->
  stable2 F ->
  stable2_ord (TI F).
intros F Fm Fs.
assert (Fm' : morph1 F).
 red; red ;intros.
 apply eq_intro; intros.
  revert H0; apply Fm.
  rewrite H; reflexivity.

  revert H0; apply Fm.
  rewrite H; reflexivity.
red; induction 1 using isOrd_ind; intros.
red; intros.
rewrite inter2_def in H3 ;destruct H3.
apply TI_elim in H3; auto; destruct H3.
apply TI_elim in H4; auto; destruct H4.
apply TI_intro with (inter2 x0 x1); auto.
 apply isOrd_inter2; auto.

 rewrite inter2_def; split.
  apply isOrd_plump with x0; trivial.
   apply isOrd_inter2; eauto using isOrd_inv.
   apply inter2_incl1.

  apply isOrd_plump with x1; trivial.
   apply isOrd_inter2; eauto using isOrd_inv.
   apply inter2_incl2.
assert (h := conj H5 H6); clear H5 H6; rewrite <- inter2_def in h.
apply Fs in h.
revert h; apply Fm.
apply H1; auto.
apply isOrd_inv with y0; trivial.
Qed.

Lemma TI_stable : forall F,
  Proper (incl_set ==> incl_set) F ->
  stable F ->
  stable_ord (TI F).
intros F Fmono Fs.
assert (Fm : morph1 F).
 apply Fmono_morph; trivial.
cut (forall o, isOrd o ->
  forall X, o == inter X ->
  (forall x, x \in X -> isOrd x) ->
  inter (replf X (TI F)) \incl TI F (inter X)).
 red; intros.
 apply H with (inter X); auto with *.
 apply isOrd_inter; auto.
induction 1 using isOrd_ind; red; intros.
assert (eX : ext_fun X (TI F)).
 red; red; intros; apply TI_morph; trivial.
assert (eN : forall X, ext_fun X F).
 red; red; intros; apply Fm; trivial.
pose (Y := subset (union X) (fun y => z \in F (TI F y))).
assert (oY : forall y, y \in Y -> isOrd y).
 unfold Y; intros.
 apply subset_elim1 in H5.
 apply union_elim in H5; destruct H5.
 eauto using isOrd_inv.
assert (eY : ext_fun Y (TI F)).
 red; red; intros.
 apply TI_morph; trivial.
assert (wX : exists w, w \in X).
 destruct inter_non_empty with (1:=H4).
 rewrite replf_ax in H5; trivial.
 destruct H5.
 exists x0; trivial.
destruct wX as (wx,wX).
assert (wY : exists w, w \in Y).
 assert (z \in TI F wx).
  apply inter_elim with (1:=H4).
  rewrite replf_ax; trivial.
  exists wx; auto with *.
 apply TI_elim in H5; auto.
 destruct H5.
 exists x.
 apply subset_intro; trivial.
 apply union_intro with wx; trivial.
destruct wY as (wy,wY).
assert (ltY : lt (inter Y) (inter X)).
 apply inter_intro; eauto.
 intros.
 assert (z \in TI F y0).
  apply inter_elim with (1:=H4).
  rewrite replf_ax; trivial.
  exists y0; auto with *.
 apply TI_elim in H6; auto.
 destruct H6.
 apply isOrd_plump with x; auto.
  apply isOrd_inter; auto.

  red; intros.
  apply inter_elim with (1:=H8).
  apply subset_intro; trivial.
  apply union_intro with y0; trivial.
assert (inter (replf Y (TI F)) \incl TI F (inter Y)).
 apply H1 with (inter Y); auto with *.
 rewrite H2; trivial.
apply TI_intro with (inter Y); auto.
 apply isOrd_inter; auto.
apply Fmono with (1:=H5).
apply Fs.
apply inter_intro.
 intros.
 rewrite replf_ax in H6; trivial.
 destruct H6.
 rewrite replf_ax in H6; trivial.
 destruct H6.
 apply subset_elim2 in H6; destruct H6.
 setoid_replace y0 with (F (TI F x1)); trivial.
 rewrite H7; apply Fm.
 rewrite H8; apply TI_morph; trivial.

 exists (F (TI F wy)).
 rewrite replf_ax; trivial.
 exists (TI F wy); auto with *.
 rewrite replf_ax; trivial.
 exists wy; auto with *.
Qed.

