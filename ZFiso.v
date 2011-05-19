Require Import basic ZF ZFpairs ZFsum ZFrelations ZFcoc.
Import IZF.

Set Implicit Arguments.

Record iso_fun X Y f : Prop := {
  iso_funm : morph1 f;
  iso_typ : forall x, x \in X -> f x \in Y;
  iso_inj : forall x x', x \in X -> x' \in X -> f x == f x' -> x == x';
  iso_surj : forall y, y \in Y -> exists2 x, x \in X & f x == y
}.
Existing Instance iso_funm.

Lemma iso_fun_morph :
  Proper (eq_set ==> eq_set ==> (eq_set ==> eq_set) ==> iff) iso_fun.
apply morph_impl_iff3; eauto with *.
do 5 red; intros.
constructor; intros.
 do 2 red; intros.
 transitivity (x1 x2); auto with *.
 symmetry; apply H1; reflexivity.

 rewrite <- H in H3; rewrite <- (H1 _ _ (reflexivity _)); rewrite <- H0.
 apply (iso_typ H2); trivial.

 rewrite <- H in H3,H4.
 apply (iso_inj H2); trivial.
 do 2 rewrite (H1 _ _ (reflexivity _)); trivial.

 rewrite <- H0 in H3.
 destruct (iso_surj H2) with y2; trivial.
 exists x2.
  rewrite <- H; trivial.

  rewrite <- H5; symmetry; apply H1; reflexivity.
Qed.

Lemma eq_iso_fun : forall X Y f, morph1 f -> X == Y -> (forall x, x \in X -> f x == x) ->
  iso_fun X Y f.
constructor; intros; trivial.
 rewrite H1; trivial.
 rewrite <- H0; trivial.

 rewrite H1 in H4; trivial.
 rewrite H4; auto.

 rewrite <- H0 in H2.
 eauto.
Qed.
 
Lemma id_iso_fun : forall X, iso_fun X X (fun x => x).
intros.
apply eq_iso_fun; auto with *.
do 2 red; auto.
Qed.

Definition iso_inv X f y := union (subset X (fun x => f x == y)).

Instance iso_inv_morph : Proper (eq_set ==> (eq_set ==> eq_set) ==> eq_set ==> eq_set) iso_inv.
do 4 red; intros.
unfold iso_inv.
apply union_morph; apply subset_morph; trivial.
red; intros.
rewrite (H0 _ _ (reflexivity _)); rewrite H1; reflexivity.
Qed.

Lemma iso_inv_eq : forall X Y f y,
   iso_fun X Y f -> y \in Y -> f (iso_inv X f y) == y.
destruct 1; intros.
unfold iso_inv.
destruct iso_surj0 with y; trivial.
rewrite union_subset_singl with (y:=x) (y':=x); auto with *.
intros.
apply iso_inj0; trivial.
transitivity y; auto with *.
Qed.

Lemma iso_inv_eq2 : forall X Y f x,
   iso_fun X Y f -> x \in X -> iso_inv X f (f x) == x.
destruct 1; intros.
unfold iso_inv.
rewrite union_subset_singl with (y:=x) (y':=x); auto with *.
intros.
apply iso_inj0; trivial.
transitivity (f x); auto with *.
Qed.

Lemma iso_inv_typ : forall X Y f y,
   iso_fun X Y f -> y \in Y -> iso_inv X f y \in X.
destruct 1; intros.
unfold iso_inv.
destruct iso_surj0 with y; trivial.
rewrite union_subset_singl with (y:=x) (y':=x); auto with *.
intros.
apply iso_inj0; trivial.
transitivity y; auto with *.
Qed.

Lemma iso_fun_sym : forall X Y f, iso_fun X Y f -> iso_fun Y X (iso_inv X f).
constructor; intros.
 do 2 red; intros.
 apply union_morph; apply subset_morph; auto with *.
 red; intros.
 rewrite H0; reflexivity.

 apply iso_inv_typ with (1:=H); trivial.

 apply (iso_funm H) in H2.
 rewrite iso_inv_eq with (1:=H) in H2; trivial.
 rewrite iso_inv_eq with (1:=H) in H2; trivial.

 exists (f y); auto.  
  apply (iso_typ H); trivial.

  apply iso_inv_eq2 with (1:=H); trivial.
Qed.

Lemma iso_fun_trans_eq : forall X Y Z f g h,
  morph1 h ->
  (forall x, x \in X -> g (f x) == h x) ->
  iso_fun X Y f ->
  iso_fun Y Z g ->
  iso_fun X Z h.
intros.
constructor; intros; trivial.
 rewrite <- H0; trivial.
 apply (iso_typ H2).
 apply (iso_typ H1); trivial.

 do 2 (rewrite <- H0 in H5; trivial).
 apply (iso_inj H2) in H5.
  apply (iso_inj H1) in H5; trivial.

  apply (iso_typ H1); trivial.
  apply (iso_typ H1); trivial.

 destruct (iso_surj H2 H3).
 destruct (iso_surj H1 H4).
 exists x0; trivial.
 rewrite <- H0; auto.
 generalize (iso_funm H2); intro.
 rewrite H7; trivial.
Qed.

Definition comp_iso (f:set->set) (g:set->set) := fun x => g (f x).

Lemma iso_fun_trans : forall X Y Z f g, iso_fun X Y f -> iso_fun Y Z g ->
  iso_fun X Z (comp_iso f g).
unfold comp_iso; intros.
apply iso_fun_trans_eq with Y f g; auto with *.
do 2 red; intros.
apply (iso_funm H0).
apply (iso_funm H); trivial.
Qed.

(* Disjoint sum *)

Definition sum_isomap f g :=
  sum_case (fun x => inl (f x)) (fun y => inr (g y)).

Instance sum_isomap_morph : Proper ((eq_set ==> eq_set) ==> (eq_set ==> eq_set) ==> eq_set ==> eq_set)
  sum_isomap.
do 4 red; intros.
unfold sum_isomap.
apply sum_case_morph; trivial.
 red; intros; apply inl_morph; apply H; trivial.
 red; intros; apply inr_morph; apply H0; trivial.
Qed.

Lemma sum_iso_fun_morph : forall X X' Y Y' f g,
  iso_fun X X' f -> iso_fun Y Y' g ->
  iso_fun (sum X Y) (sum X' Y') (sum_isomap f g).
unfold sum_isomap; intros.
assert (m1 : morph1 (fun x => inl (f x))).
 do 2 red; intros.
 apply inl_morph; apply iso_funm with (1:=H); trivial.
assert (m1' : morph1 (fun x => inr (g x))).
 do 2 red; intros.
 apply inr_morph; apply iso_funm with (1:=H0); trivial.
constructor; intros.
 apply sum_case_morph; auto.

 apply sum_ind with (3:=H1); intros.
  rewrite H3; rewrite sum_case_inl; auto.
  apply inl_typ.
  apply (iso_typ H); trivial.

  rewrite H3; rewrite sum_case_inr; auto.
  apply inr_typ.
  apply (iso_typ H0); trivial.

 apply sum_ind with (3:=H1); intros;
   apply sum_ind with (3:=H2); intros.
  rewrite H5 in H3; trivial; rewrite H7 in H3; trivial.
  do 2 (rewrite sum_case_inl in H3; trivial).
  apply inl_inj in H3.
  apply (iso_inj H) in H3; trivial.
  rewrite H5; rewrite H7; rewrite H3; reflexivity.

  rewrite H5 in H3; trivial; rewrite H7 in H3; trivial.
  rewrite sum_case_inl in H3; trivial; rewrite sum_case_inr in H3; trivial.
  apply discr_sum in H3; contradiction.

  rewrite H5 in H3; trivial; rewrite H7 in H3; trivial.
  rewrite sum_case_inl in H3; trivial; rewrite sum_case_inr in H3; trivial.
  symmetry in H3.
  apply discr_sum in H3; contradiction.

  rewrite H5 in H3; trivial; rewrite H7 in H3; trivial.
  do 2 (rewrite sum_case_inr in H3; trivial).
  apply inr_inj in H3.
  apply (iso_inj H0) in H3; trivial.
  rewrite H5; rewrite H7; rewrite H3; reflexivity.

 apply sum_ind with (3:=H1); intros.
  destruct (iso_surj H) with (1:=H2).
  exists (inl x0).
   apply inl_typ; trivial.

   rewrite sum_case_inl; trivial.
   rewrite H3; rewrite H5; reflexivity.

  destruct (iso_surj H0) with (1:=H2).
  exists (inr x).
   apply inr_typ; trivial.

   rewrite sum_case_inr; trivial.
   rewrite H3; rewrite H5; reflexivity.
Qed.

Definition sum_isocomm := sum_case inr inl.

Instance sum_isocomm_morph : morph1 sum_isocomm.
do 2 red; intros; unfold sum_isocomm.
apply sum_case_morph; auto with *.
 apply inr_morph.
 apply inl_morph.
Qed.

Lemma sum_comm_iso_fun :
  forall X Y, iso_fun (sum X Y) (sum Y X) sum_isocomm.
unfold sum_isocomm; constructor; intros.
 auto with *.

 apply sum_ind with (3:=H); intros.
  rewrite H1; rewrite sum_case_inl; trivial with *.
  apply inr_typ; trivial.

  rewrite H1; rewrite sum_case_inr; trivial with *.
  apply inl_typ; trivial.

 apply sum_ind with (3:=H); intros y yty xeq; rewrite xeq in H1|-*;
   [rewrite sum_case_inl in H1|rewrite sum_case_inr in H1]; trivial with *;
   (apply sum_ind with (3:=H0); intros y' yty' xeq'; rewrite xeq' in H1|-*;
   [rewrite sum_case_inl in H1|rewrite sum_case_inr in H1]; trivial with *).
  apply inr_inj in H1.
  rewrite H1; reflexivity.

  symmetry in H1; apply discr_sum in H1; contradiction.

  apply discr_sum in H1; contradiction.

  apply inl_inj in H1.
  rewrite H1; reflexivity.

 apply sum_ind with (3:=H); intros.
  exists (inr x).
   apply inr_typ; trivial.

  rewrite sum_case_inr; auto with *.

  exists (inl y0).
   apply inl_typ; trivial.

  rewrite sum_case_inl; auto with *.
Qed.

Definition sum_isoassoc :=
  sum_case (sum_case inl (fun y => inr (inl y))) (fun z => inr (inr z)).

Instance sum_isoassoc_morph : morph1 sum_isoassoc.
do 2 red; intros; unfold sum_isoassoc.
apply sum_case_morph; trivial.
 red; intros.
 apply sum_case_morph; trivial.
  apply inl_morph.

  red; intros.
  rewrite H1; reflexivity.

 red; intros.
 rewrite H0; reflexivity.
Qed.

Lemma sum_assoc_iso_fun :
  forall X Y Z, iso_fun (sum (sum X Y) Z) (sum X (sum Y Z)) sum_isoassoc.
unfold sum_isoassoc; intros.
assert (m1 : morph1 (fun y => inr (inl y))).
 do 2 red; intros.
 rewrite H; reflexivity.
assert (m2 : morph1 (fun y => inr (inr y))).
 do 2 red; intros.
 rewrite H; reflexivity.
assert (m3 : morph1 (sum_case inl (fun y => inr (inl y)))).
 do 2 red; intros; apply sum_case_morph; trivial with *.
 apply inl_morph.
constructor; intros.
 apply sum_isoassoc_morph.

 apply sum_ind with (3:=H); intros.
  rewrite H1; auto with *.
  rewrite sum_case_inl; trivial.
  apply sum_ind with (3:=H0); intros.
   rewrite H3; auto with *.
   rewrite sum_case_inl; auto with *.
   apply inl_typ; trivial.

   rewrite H3; auto with *.
   rewrite sum_case_inr; auto with *.
   apply inr_typ; apply inl_typ; trivial.

  rewrite H1; auto with *.
  rewrite sum_case_inr; auto with *.
  apply inr_typ; apply inr_typ; trivial.

 apply sum_ind with (3:=H); intros y yty xeq; rewrite xeq in H1|-*;
   [rewrite sum_case_inl in H1|rewrite sum_case_inr in H1]; trivial with *;
   (apply sum_ind with (3:=H0); intros y' yty' xeq'; rewrite xeq' in H1|-*;
   [rewrite sum_case_inl in H1|rewrite sum_case_inr in H1]; trivial with *).
  apply sum_ind with (3:=yty); intros z zty yeq; rewrite yeq in H1|-*;
    [rewrite sum_case_inl in H1|rewrite sum_case_inr in H1]; trivial with *;
    (apply sum_ind with (3:=yty'); intros z' zty' yeq'; rewrite yeq' in H1|-*;
    [rewrite sum_case_inl in H1|rewrite sum_case_inr in H1]; trivial with *).
   apply inl_inj in H1; rewrite H1; reflexivity.

   apply discr_sum in H1; contradiction.

   symmetry in H1; apply discr_sum in H1; contradiction.

   apply inr_inj in H1; apply inl_inj in H1; rewrite H1; reflexivity.

  apply sum_ind with (3:=yty); intros z zty yeq; rewrite yeq in H1|-*;
    [rewrite sum_case_inl in H1|rewrite sum_case_inr in H1]; trivial with *.
   apply discr_sum in H1; contradiction.

   apply inr_inj in H1; apply discr_sum in H1; contradiction.

  symmetry in H1.
  apply sum_ind with (3:=yty'); intros z' zty' yeq'; rewrite yeq' in H1|-*;
    [rewrite sum_case_inl in H1|rewrite sum_case_inr in H1]; trivial with *.
   apply discr_sum in H1; contradiction.

   apply inr_inj in H1; apply discr_sum in H1; contradiction.

  apply inr_inj in H1; apply inr_inj in H1.
  rewrite H1; reflexivity.

 apply sum_ind with (3:=H); intros.
  exists (inl (inl x)).
   apply inl_typ; apply inl_typ; trivial.

   rewrite sum_case_inl; auto; rewrite sum_case_inl; auto with *.

  apply sum_ind with (3:=H0); intros.
   exists (inl (inr x)).
    apply inl_typ; apply inr_typ; trivial.

    rewrite sum_case_inl; auto; rewrite sum_case_inr; auto with *.
    rewrite H1; rewrite H3; reflexivity.

   exists (inr y1).
    apply inr_typ; trivial.

    rewrite sum_case_inr; auto with *.
    rewrite H1; rewrite H3; reflexivity.
Qed.

(* Dependent pairs *)

Definition sigma_isomap f g :=
  fun p => couple (f (fst p)) (g (fst p) (snd p)).

Instance sigma_isomap_morph : Proper ((eq_set ==> eq_set) ==> (eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set)
  sigma_isomap.
do 4 red; intros.
unfold sigma_isomap.
apply couple_morph.
 apply H; rewrite H1; reflexivity.
 apply H0; rewrite H1; reflexivity.
Qed.

Lemma sigma_iso_fun_morph : forall A A' B B' f g,
  ext_fun A B ->
  ext_fun A' B' ->
  morph2 g ->
  iso_fun A A' f ->
  (forall x x', x \in A -> f x == x' -> iso_fun (B x) (B' x') (g x)) ->
  iso_fun (sigma A B) (sigma A' B') (sigma_isomap f g).
unfold sigma_isomap; intros.
constructor; intros.
 apply sigma_isomap_morph; trivial.
 apply (iso_funm H2).

 assert (fst x \in A).
  apply fst_typ_sigma in H4; trivial.
 apply couple_intro_sigma; trivial.
  apply (iso_typ H2); trivial.

  apply (iso_typ (H3 _ _ H5 (reflexivity _))).
  apply snd_typ_sigma with (2:=H4); auto with *.

 assert (fst x \in A).
  apply fst_typ_sigma in H4; trivial.
 apply couple_injection in H6; destruct H6. 
 apply (iso_inj H2) in H6.
 2:apply fst_typ_sigma in H4; trivial.
 2:apply fst_typ_sigma in H5; trivial.
 rewrite <- H6 in H8.
 apply (iso_inj (H3 _ _ H7 (reflexivity _))) in H8.
  rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ H4)).
  rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ H5)).
  rewrite H6; rewrite H8; reflexivity.

  apply snd_typ_sigma with (2:=H4); auto with *.

  apply snd_typ_sigma with (2:=H5); auto with *.

 destruct (iso_surj H2 (y:=fst y)).
  apply fst_typ_sigma in H4; trivial.
 destruct (iso_surj (H3 _ _ H5 H6) (y:=snd y)).
  apply snd_typ_sigma with (2:=H4); auto with *.
 exists (couple x x0).
  apply couple_intro_sigma; auto.

  generalize (iso_funm H2); intro.
  rewrite fst_def; rewrite snd_def.
  rewrite H6; rewrite H8.
  symmetry; apply surj_pair with (1:=subset_elim1 _ _ _ H4).
Qed.

Lemma sigma_iso_fun_1_l : forall x F,
  ext_fun (singl x) F ->
  iso_fun (sigma (singl x) F) (F x) snd.
constructor; intros; auto with *.
 apply snd_typ_sigma with (2:=H0); trivial.
 apply fst_typ_sigma in H0.
 apply singl_elim in H0; auto with *.

 assert (fst x0 == fst x').
  apply fst_typ_sigma in H1.
  apply singl_elim in H1; auto with *.
  rewrite H1.
  apply fst_typ_sigma in H0.
  apply singl_elim in H0; auto with *.
 rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ H0)).
 rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ H1)).
 rewrite H2; rewrite H3; reflexivity.

 exists (couple x y).  
  apply couple_intro_sigma; auto.
  apply singl_intro.

  apply snd_def.
Qed.

Lemma sigma_iso_fun_1_r : forall A B,
  ext_fun A B ->
  (forall x, x \in A -> iso_fun (B x) (singl empty) (fun _ => empty)) ->
  iso_fun (sigma A B) A fst.
intros.
constructor; intros; auto with *.
 apply fst_typ_sigma in H1; trivial.

 assert (forall x y y', x \in A -> y \in B x -> y' \in B x -> y == y').
  intros.
  apply (iso_inj (H0 _ H4)); auto with *.
 rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ H1)).
 rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ H2)).
 apply couple_morph; trivial.
 apply H4 with (fst x); trivial.
  apply fst_typ_sigma in H1; trivial.

  apply snd_typ_sigma with (2:=H1); auto with *.

  apply snd_typ_sigma with (2:=H2); auto with *.

 destruct (iso_surj (H0 _ H1) (y:=empty)).
  apply singl_intro.
 exists (couple y x).
  apply couple_intro_sigma; auto.

  apply fst_def.
Qed.

Definition sigma_isoassoc :=
  fun t => couple (couple (fst t) (fst (snd t))) (snd (snd t)).

Instance sigma_isoassoc_morph : morph1 sigma_isoassoc.
do 2 red; intros; unfold sigma_isoassoc.
rewrite H; reflexivity.
Qed.

Lemma iso_sigma_sigma : forall A B C,
  ext_fun A B ->
  (forall x x' y y', x \in A -> x == x' -> y \in B x -> y == y' -> C x y == C x' y') ->
  iso_fun (sigma A (fun x => sigma (B x) (fun y => C x y)))
          (sigma (sigma A B) (fun p => C (fst p) (snd p)))
          sigma_isoassoc.
unfold sigma_isoassoc; constructor; intros.
 apply sigma_isoassoc_morph.

 assert (fst x \in A).
  apply fst_typ_sigma in H1; trivial.
 assert (snd x \in sigma (B (fst x)) (fun y => C (fst x) y)).
  apply snd_typ_sigma with (2:=H1); auto with *.
  do 2 red; intros.
  apply sigma_morph; auto with *.
 clear H1.
 assert (fst (snd x) \in B (fst x)).
  apply fst_typ_sigma in H3; trivial.
 assert (snd (snd x) \in C (fst x) (fst (snd x))).
  apply snd_typ_sigma with (2:=H3); auto with *.
  do 2 red; intros.
  auto with *.
 clear H3.
 apply couple_intro_sigma; auto with *.
  do 2 red; intros.
  apply H0; auto with *.
   apply fst_typ_sigma in H3; trivial.
   rewrite H5; reflexivity.
   apply snd_typ_sigma with (2:=H3); auto with *.
   rewrite H5; reflexivity.

  apply couple_intro_sigma; auto with *.

  apply eq_elim with (2:=H4).
  apply H0; auto.
   rewrite fst_def; reflexivity.
   rewrite snd_def; reflexivity.

 apply couple_injection in H3; destruct H3.
 apply couple_injection in H3; destruct H3.
 rewrite (surj_pair _ _ _ (subset_elim1 _ _ _  H1)).
 rewrite (surj_pair _ _ _ (subset_elim1 _ _ _  H2)).
 apply couple_morph; trivial.
 assert (snd x \in sigma (B (fst x)) (fun y => C (fst x) y)).
  apply snd_typ_sigma with (2:=H1); auto with *.
  do 2 red; intros.
  apply sigma_morph; auto with *.
 assert (snd x' \in sigma (B (fst x)) (fun y => C (fst x) y)).
  apply snd_typ_sigma with (2:=H2); auto with *.
  do 2 red; intros.
  apply sigma_morph; auto with *.
 rewrite (surj_pair _ _ _ (subset_elim1 _ _ _  H6)).
 rewrite (surj_pair _ _ _ (subset_elim1 _ _ _  H7)).
 apply couple_morph; trivial.

 exists (couple (fst (fst y)) (couple (snd (fst y)) (snd y))).
  apply couple_intro_sigma.
   do 2 red; intros.
   apply sigma_morph; auto with *.

   apply fst_typ_sigma in H1.
   apply fst_typ_sigma in H1; trivial.

   apply couple_intro_sigma.
    do 2 red; intros.
    apply H0; auto with *.
    apply fst_typ_sigma in H1.
    apply fst_typ_sigma in H1; trivial.

    apply fst_typ_sigma in H1.
    apply snd_typ_sigma with (2:=H1); auto with *.

    apply snd_typ_sigma with (2:=H1); auto with *.
    do 2 red; intros.
    apply H0; auto with *.
     apply fst_typ_sigma in H2; trivial.
     rewrite H3; reflexivity.
     apply snd_typ_sigma with (2:=H2); auto with *.
     rewrite H3; reflexivity.

  rewrite snd_def.
  rewrite fst_def.
  rewrite fst_def.
  rewrite snd_def.
  specialize fst_typ_sigma with (1:=H1); intros.
  rewrite <- (surj_pair _ _ _ (subset_elim1 _ _ _ H2)).
  rewrite <- (surj_pair _ _ _ (subset_elim1 _ _ _ H1)).
  reflexivity.
Qed.

Definition sum_sigma_iso :=
  sum_case (fun p1 => couple (inl (fst p1)) (snd p1))
           (fun p2 => couple (inr (fst p2)) (snd p2)).

Instance sum_sigma_iso_morph : morph1 sum_sigma_iso.
do 2 red; intros; unfold sum_sigma_iso.
apply sum_case_morph; trivial.
 red; intros.
 rewrite H0; reflexivity.

 red; intros.
 rewrite H0; reflexivity.
Qed.

Lemma iso_fun_sum_sigma : forall A1 A2 B1 B2,
  morph1 B1 ->
  morph1 B2 ->
  iso_fun (sum (sigma A1 B1) (sigma A2 B2))
          (sigma (sum A1 A2) (sum_case B1 B2))
          sum_sigma_iso.
unfold sum_sigma_iso; intros A1 A2 B1 B2 bm1 bm2.
assert (m1 : morph1 (fun p1 => couple (inl (fst p1)) (snd p1))).
 do 2 red; intros.
 rewrite H; reflexivity.
assert (m2 : morph1 (fun p2 => couple (inr (fst p2)) (snd p2))).
 do 2 red; intros.
 rewrite H; reflexivity.
assert (m3 : ext_fun (sum A1 A2) (sum_case B1 B2)).
 do 2 red; intros.
 apply sum_case_morph; auto.
constructor; intros.
 apply sum_case_morph; [apply m1|apply m2].

 apply sum_ind with (3:=H); intros.
  rewrite H1; rewrite sum_case_inl; auto.
  apply couple_intro_sigma; auto.
   apply inl_typ.
   apply fst_typ_sigma in H0; trivial.

   rewrite sum_case_inl; trivial.
   apply snd_typ_sigma with (2:=H0); auto with *.

  rewrite H1; rewrite sum_case_inr; auto.
  apply couple_intro_sigma; auto.
   apply inr_typ.
   apply fst_typ_sigma in H0; trivial.

   rewrite sum_case_inr; trivial.
   apply snd_typ_sigma with (2:=H0); auto with *.

 apply sum_ind with (3:=H); intros y yty xeq; rewrite xeq in H1|-*;
   [rewrite sum_case_inl in H1|rewrite sum_case_inr in H1]; trivial with *;
   (apply sum_ind with (3:=H0); intros y' yty' xeq'; rewrite xeq' in H1|-*;
   [rewrite sum_case_inl in H1|rewrite sum_case_inr in H1]; trivial with *);
   apply couple_injection in H1; destruct H1.
  apply inl_inj in H1.
  rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ yty)).
  rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ yty')).
  rewrite H1; rewrite H2; reflexivity.

  apply discr_sum in H1; contradiction.

  symmetry in H1; apply discr_sum in H1; contradiction.

  apply inr_inj in H1.
  rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ yty)).
  rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ yty')).
  rewrite H1; rewrite H2; reflexivity.

 assert (m4 : morph1 (fun x => inl (couple x (snd y)))).
  do 2 red; intros.
  rewrite H0; reflexivity.
 assert (m4' : morph1 (fun x => inr (couple x (snd y)))).
  do 2 red; intros.
  rewrite H0; reflexivity.
 exists (sum_case (fun x => inl (couple x (snd y))) (fun x => inr (couple x (snd y))) (fst y)).
  apply sum_ind with (3:=fst_typ_sigma _ _ _ H); intros.
   rewrite H1; trivial.
   rewrite sum_case_inl; trivial.
   apply inl_typ.
   apply couple_intro_sigma; auto with *.
   apply snd_typ_sigma with (y:=fst y) in H; auto with *.
   rewrite H1 in H; trivial.
   rewrite sum_case_inl in H; trivial.

   rewrite H1; trivial.
   rewrite sum_case_inr; trivial.
   apply inr_typ.
   apply couple_intro_sigma; auto with *.
   apply snd_typ_sigma with (y:=fst y) in H; auto with *.
   rewrite H1 in H; trivial.
   rewrite sum_case_inr in H; trivial.

  apply sum_ind with (3:=fst_typ_sigma _ _ _ H); intros.
   rewrite H1; trivial.
   rewrite sum_case_inl; trivial.
   rewrite sum_case_inl; trivial.
   rewrite fst_def; rewrite  snd_def.
   rewrite <- H1.
   rewrite <- surj_pair with (1:=subset_elim1 _ _ _ H); auto with *.

   rewrite H1; trivial.
   rewrite sum_case_inr; trivial.
   rewrite sum_case_inr; trivial.
   rewrite fst_def; rewrite  snd_def.
   rewrite <- H1.
   rewrite <- surj_pair with (1:=subset_elim1 _ _ _ H); auto with *.
Qed.

(* Cartesian product *)

(* --> ZFpairs *)
Lemma sigma_nodep : forall A B,
  prodcart A B == sigma A (fun _ => B).
intros.
apply eq_intro; intros.
 generalize (fst_typ _ _ _ H); intro.
 generalize (snd_typ _ _ _ H); intro.
 apply subset_intro; trivial.
 rewrite (surj_pair _ _ _ H).
 apply couple_intro; trivial.
 apply union_intro with B; trivial.
 apply replf_intro with (fst z); auto with *.

 apply subset_elim1 in H.
 generalize (fst_typ _ _ _ H); intro.
 generalize (snd_typ _ _ _ H); intro.
 rewrite (surj_pair _ _ _ H).
 apply couple_intro; trivial.
 apply union_elim in H1; destruct H1.
 rewrite replf_ax in H2; auto with *.
 destruct H2.
 rewrite <- H3; trivial.
Qed.

Lemma prodcart_iso_fun_morph : forall X X' Y Y' f g,
  iso_fun X X' f -> iso_fun Y Y' g ->
  iso_fun (prodcart X Y) (prodcart X' Y') (sigma_isomap f (fun _ => g)).
intros.
cut (iso_fun (sigma X (fun _ => Y)) (sigma X' (fun _ => Y'))
       (sigma_isomap f (fun _ => g))).
 apply iso_fun_morph.
  apply sigma_nodep.

  apply sigma_nodep.

  red; intros.
  apply sigma_isomap_morph; trivial.
   apply (iso_funm H).

   red; intros.
   apply (iso_funm H0).
apply sigma_iso_fun_morph; auto.
do 2 red; intros.
apply (iso_funm H0).
Qed.

Lemma prodcart_comm_iso_fun :
  forall X Y, iso_fun (prodcart X Y) (prodcart Y X) (fun p => couple (snd p) (fst p)).
constructor; intros.
 do 2 red; intros.
 rewrite H; reflexivity.

 apply couple_intro.
  apply snd_typ in H; trivial.
  apply fst_typ in H; trivial.

 apply couple_injection in H1; destruct H1.
 rewrite (surj_pair _ _ _ H).
 rewrite (surj_pair _ _ _ H0).
 apply couple_morph; trivial.

 exists (couple (snd y) (fst y)).
  apply couple_intro.
   apply snd_typ in H; trivial.
   apply fst_typ in H; trivial.

  rewrite fst_def; rewrite snd_def.
  symmetry; apply surj_pair with (1:=H). 
Qed.


(*
Lemma prodcart_assoc_iso_fun :
  forall X Y Z,
  iso_fun (prodcart (prodcart X Y) Z) (prodcart X (prodcart Y Z))
    (fun t => couple (fst (fst t)) (couple (snd (fst t)) (snd t))).
intros.
cut (iso_fun (sigma (sigma X (fun _ => Y)) (fun _ => Z))
             (sigma X (fun _ => (sigma Y (fun _ => Z)))) sigma_isoassoc).
 apply iso_fun_morph.
  rewrite (sigma_nodep X).
  apply sigma_nodep.

  rewrite (sigma_nodep Y).
  rewrite sigma_nodep; reflexivity.

  unfold sigma_isoassoc; red; intros.
*)
Lemma iso_fun_prodcart_sigma : forall A1 A2 B1 B2,
  morph1 B1 ->
  morph1 B2 ->
  iso_fun (prodcart (sigma A1 B1) (sigma A2 B2))
    (sigma (prodcart A1 A2)
      (fun p => prodcart (B1 (fst p)) (B2 (snd p))))
    (fun q => couple (couple (fst (fst q)) (fst (snd q)))
                     (couple (snd (fst q)) (snd (snd q)))).
constructor; intros.
 do 2 red; intros.
 rewrite H1; reflexivity.

 generalize (fst_typ _ _ _ H1); intro.
 generalize (snd_typ _ _ _ H1); intro.
 clear H1.
 apply couple_intro_sigma.
  do 2 red; intros.
  rewrite H4; reflexivity.

  apply couple_intro.
   apply fst_typ_sigma in H2; trivial.
   apply fst_typ_sigma in H3; trivial.

  apply couple_intro.
   rewrite fst_def.
   apply snd_typ_sigma with (2:=H2); auto with *.

   rewrite snd_def.
   apply snd_typ_sigma with (2:=H3); auto with *.

 apply couple_injection in H3; destruct H3.
 apply couple_injection in H3; destruct H3.
 apply couple_injection in H4; destruct H4.
 rewrite surj_pair  with (1:=H1);
 rewrite surj_pair  with (1:=H2).
 rewrite surj_pair with (1:=subset_elim1 _ _ _ (fst_typ _ _ _ H1)).
 rewrite surj_pair with (1:=subset_elim1 _ _ _ (snd_typ _ _ _ H1)).
 rewrite surj_pair with (1:=subset_elim1 _ _ _ (fst_typ _ _ _ H2)).
 rewrite surj_pair with (1:=subset_elim1 _ _ _ (snd_typ _ _ _ H2)).
 apply couple_morph; apply couple_morph; trivial.

 exists (couple (couple (fst (fst y)) (fst (snd y))) (couple (snd (fst y)) (snd (snd y)))).
  generalize (fst_typ_sigma _ _ _ H1); intros.
  apply snd_typ_sigma with (y:=fst y) in H1; auto with *.
   apply couple_intro.
    apply couple_intro_sigma; auto with *.
     apply fst_typ in H2; trivial.
     apply fst_typ in H1; trivial.

    apply couple_intro_sigma; auto with *.
     apply snd_typ in H2; trivial.
     apply snd_typ in H1; trivial.

    do 2 red; intros.
    rewrite H4; reflexivity.

  repeat (rewrite fst_def || rewrite snd_def).
  assert (H2:=H1).
  generalize (fst_typ_sigma _ _ _ H1); intros.
  apply snd_typ_sigma with (y:=fst y) in H2; auto with *.
   rewrite <- surj_pair with (1:=H3).
   rewrite <- surj_pair with (1:=H2).
   rewrite <- surj_pair with (1:=subset_elim1 _ _ _ H1); reflexivity.

   do 2 red; intros.
   rewrite H5; reflexivity.
Qed.

(* Dependent product *)

Definition cc_prod_isomap A A' f g :=
  fun fct => cc_lam A' (fun x' => let x := iso_inv A f x' in g x (cc_app fct x)).

Lemma cc_prod_isomap_morph : Proper
  (eq_set ==> eq_set ==> (eq_set ==> eq_set) ==> (eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set)
  cc_prod_isomap.
do 6 red; intros.
unfold cc_prod_isomap.
apply cc_lam_ext; intros; auto.
red; intros.
apply H2.
 apply iso_inv_morph; trivial.

 apply cc_app_morph; trivial.
 apply iso_inv_morph; trivial.
Qed.
 
Lemma cc_prod_iso_fun_morph : forall A A' B B' f g,
  ext_fun A B ->
  ext_fun A' B' ->
  morph2 g ->
  iso_fun A A' f ->
  (forall x x', x \in A -> f x == x' -> iso_fun (B x) (B' x') (g x)) ->
  iso_fun (cc_prod A B) (cc_prod A' B') (cc_prod_isomap A A' f g).
unfold cc_prod_isomap; constructor; intros.
 apply cc_prod_isomap_morph; auto with *.
 apply (iso_funm H2).

 apply cc_prod_intro; trivial; intros.
  do 2 red; intros.
  generalize (iso_funm H2); intro.
  rewrite <- H6.
  reflexivity.

  assert (iso_inv A f x0 \in A).
   apply iso_inv_typ with (1:=H2); trivial.
  assert (f (iso_inv A f x0) == x0).
   apply iso_inv_eq with (1:=H2); trivial.
  apply (iso_typ (H3 _ _ H6 H7)).
  apply cc_prod_elim with (1:=H4); trivial.

 assert (fm := iso_funm H2).
 rewrite (cc_eta_eq _ _ _ H4).
 rewrite (cc_eta_eq _ _ _ H5).
 apply cc_lam_ext; intros; auto with *.
 red; intros.
 assert (iso_inv A f (f x0) == x0).
  apply iso_inv_eq2 with (1:=H2); trivial.
 generalize (cc_app_morph _ _ H6 _ _ (reflexivity (f x0))).
 rewrite cc_beta_eq.
  3:apply (iso_typ H2); trivial.
  rewrite cc_beta_eq.
  3:apply (iso_typ H2); trivial.
   simpl; intro.
   rewrite H9 in H10.
   rewrite <- H8.
   apply (iso_inj (H3 _ _ H7 (reflexivity _))); trivial.
    apply cc_prod_elim with (1:=H4); trivial.
    apply cc_prod_elim with (1:=H5); trivial.

   do 2 red; intros.
   rewrite H11; reflexivity.

  do 2 red; intros.
  rewrite H11; reflexivity.

 assert (fm := iso_funm H2).
 exists (cc_lam A (fun x => iso_inv (B x) (g x) (cc_app y (f x)))).
  apply cc_prod_intro; intros; auto.
   do 2 red; intros.
   apply iso_inv_morph; auto with *.
   rewrite H6; reflexivity.

   apply iso_inv_typ with (1:=H3 _ _ H5 (reflexivity _)).
   apply cc_prod_elim with (1:=H4).
   apply (iso_typ H2); trivial.

  rewrite (cc_eta_eq _ _ _ H4).
  apply cc_lam_ext; intros; auto with *.
  red; intros.
  assert (f (iso_inv A f x) == x).
   apply iso_inv_eq with (1:=H2); trivial.
  rewrite cc_beta_eq.
   3:apply iso_inv_typ with (1:=H2); trivial.
   transitivity (cc_app y (f (iso_inv A f x))).
   2:rewrite H7; rewrite H6; reflexivity.
   apply iso_inv_eq with (B' x); trivial.
    apply H3; auto with *.
    apply iso_inv_typ with (1:=H2); trivial.

    rewrite H7.
    apply cc_prod_elim with (1:=H4); trivial.

   do 2 red; intros.
   apply iso_inv_morph; auto with *.
   rewrite H9; reflexivity.
Qed.

Lemma cc_prod_iso_fun_0_l : forall F,
  iso_fun (cc_prod empty F) (singl empty) (fun _ => empty).
intros.
constructor; intros; auto with *.
 do 2 red; reflexivity.

 apply singl_intro.

 rewrite (cc_eta_eq _ _ _ H).
 rewrite (cc_eta_eq _ _ _ H0).
 apply cc_lam_ext; auto with *.
 red; intros.
 apply empty_ax in H2; contradiction.

 exists (cc_lam empty (fun _ => empty)).
  apply cc_prod_intro; intros; auto with *.
   do 2 red; intros.
   apply empty_ax in H0; contradiction.

   apply empty_ax in H0; contradiction.

  apply singl_elim in H; auto with *.
Qed.

Definition cc_prod_iso1l x := fun f => cc_app f x.

Lemma cc_prod_iso_fun_1_l : forall x F,
  (forall x', x == x' -> F x == F x') ->
  iso_fun (cc_prod (singl x) F) (F x) (cc_prod_iso1l x).
unfold cc_prod_iso1l; constructor; intros.
 do 2 red; intros.
 rewrite H0; reflexivity.

 apply cc_prod_elim with (1:=H0).
 apply singl_intro.

 rewrite (cc_eta_eq _ _ _ H0).
 rewrite (cc_eta_eq _ _ _ H1).
 apply cc_lam_ext; auto with *.
 red; intros.
 rewrite <- H4. 
 apply singl_elim in H3; rewrite H3; trivial.

 exists (cc_lam (singl x) (fun _ => y)).
  apply cc_prod_intro; intros.
   do 2 red; reflexivity.

   do 2 red; intros.
   apply singl_elim in H1.
   transitivity (F x).
    symmetry; auto with *.
    apply H; rewrite <- H1; trivial.

   apply singl_elim in H1.
   symmetry in H1.
   rewrite <- H with (1:=H1); trivial.

  rewrite cc_beta_eq; auto with *.
  apply singl_intro.
Qed.

Lemma cc_prod_iso_fun_1_r : forall A F,
  ext_fun A F ->
  (forall x, x \in A -> iso_fun (F x) (singl empty) (fun _ => empty)) ->
  iso_fun (cc_prod A F) (singl empty) (fun _ => empty).
constructor; intros.
 do 2 red; reflexivity.

 apply singl_intro.

 rewrite (cc_eta_eq _ _ _ H1).
 rewrite (cc_eta_eq _ _ _ H2).
 apply cc_lam_ext; intros; auto with *.
 red; intros.
 rewrite <- H5.
 apply (iso_inj (H0 _ H4)); auto with *.
  apply cc_prod_elim with (1:=H1); trivial.
  apply cc_prod_elim with (1:=H2); trivial.

 exists (cc_lam A (fun x => iso_inv (F x) (fun _ => empty) empty)).
  apply cc_prod_intro; intros; trivial.
   do 2 red; intros.
   unfold iso_inv.
   apply union_morph; apply subset_morph; auto with *.

   apply iso_inv_typ with (1:=H0 _ H2).
   apply singl_intro.

  apply singl_elim in H1; auto with *.
Qed.

Definition cc_prod_isocurry A B :=
  fun f2 => cc_lam (sigma A B) (fun p => cc_app (cc_app f2 (fst p)) (snd p)).

Lemma cc_prod_curry_iso_fun : forall A B C,
  ext_fun A B ->
  (forall x x' y y', x \in A -> x == x' -> y \in B x -> y == y' -> C x y == C x' y') ->
  iso_fun (cc_prod A (fun x => cc_prod (B x) (fun y => C x y)))
    (cc_prod (sigma A B) (fun p => C (fst p) (snd p)))
    (cc_prod_isocurry A B).
unfold cc_prod_isocurry; constructor; intros.
 do 2 red; intros.
 apply cc_lam_ext; intros; auto with *.
 red; intros.
 rewrite H1; rewrite H3; reflexivity.

 apply cc_prod_intro; intros.
  do 2 red; intros.
  rewrite H3; reflexivity.

  do 2 red; intros.
  apply H0.
   apply fst_typ_sigma in H2; trivial.

   rewrite H3; reflexivity.

   apply snd_typ_sigma with (2:=H2); auto with *.
 
   rewrite H3; reflexivity.

  apply cc_prod_elim with (dom := B (fst x0)) (F:=fun y => C (fst x0) y).
   apply cc_prod_elim with (1:=H1).
   apply fst_typ_sigma in H2; trivial.

   apply snd_typ_sigma with (2:=H2); auto with *.

 rewrite (cc_eta_eq _ _ _ H1).
 rewrite (cc_eta_eq _ _ _ H2).
 apply cc_lam_ext; intros; auto with *.
 red; intros.
 rewrite <- H5.
  clear x'0 H5.
 rewrite (cc_eta_eq _ _ _ (cc_prod_elim _ _ _ _ H1 H4)).
 rewrite (cc_eta_eq _ _ _ (cc_prod_elim _ _ _ _ H2 H4)).
 apply cc_lam_ext; intros; auto with *.
 red; intros.
 rewrite <- H6.
 clear x'0 H6.
 assert (couple x0 x1 \in sigma A B).
  apply couple_intro_sigma; trivial.
 generalize (cc_app_morph _ _ H3 _ _ (reflexivity (couple x0 x1))).
 rewrite cc_beta_eq; trivial.
 2:do 2 red; intros; rewrite H8; reflexivity.
 rewrite cc_beta_eq; trivial.
 2:do 2 red; intros; rewrite H8; reflexivity.
 rewrite fst_def; rewrite snd_def; trivial.

 exists (cc_lam A (fun x => cc_lam (B x) (fun y' => cc_app y (couple x y')))).
  apply cc_prod_intro; intros; auto with *.
   do 2 red; intros.
   apply cc_lam_ext; intros; auto with *.
   red; intros.
   rewrite H3; rewrite H5; reflexivity.

   do 2 red; intros.
   apply cc_prod_ext; intros; auto with *.
   red; intros; auto.

   apply cc_prod_intro; intros; auto with *.
    do 2 red; intros.
    rewrite H4; reflexivity.

    do 2 red; intros; auto with *.

    assert (couple x x0 \in sigma A B).
     apply couple_intro_sigma; auto with *.
    specialize cc_prod_elim with (1:=H1) (2:=H4); intro.
    apply eq_elim with (2:=H5).
    symmetry; apply H0; auto with *.
     rewrite fst_def; reflexivity.
     rewrite snd_def; reflexivity.

  transitivity (cc_lam (sigma A B) (fun p => cc_app y p)).
  2:symmetry; apply cc_eta_eq with (1:=H1).
  apply cc_lam_ext; intros; auto with *.
  red; intros.
  rewrite <- H3; clear x' H3.
  rewrite cc_beta_eq.
  3:apply fst_typ_sigma in H2; trivial.
   rewrite cc_beta_eq.
    rewrite <- (surj_pair _ _ _ (subset_elim1 _ _ _ H2)); auto with *.

    do 2 red; intros.
    rewrite H4; reflexivity.

    apply snd_typ_sigma with (2:=H2); auto with *.

   do 2 red; intros.
   apply cc_lam_ext; auto with *.
   red; intros.
   rewrite H4; rewrite H6; reflexivity.
Qed.

Definition cc_prod_sigma_iso A :=
  fun fct => couple (cc_lam A (fun x => fst (cc_app fct x)))
                    (cc_lam A (fun x => snd (cc_app fct x))). 

Instance cc_prod_sigma_iso_morph : morph2 cc_prod_sigma_iso.
do 3 red; intros.
unfold cc_prod_sigma_iso.
apply couple_morph.
 apply cc_lam_ext; trivial.
 red; intros.
 rewrite H0; rewrite H2; reflexivity.
 
 apply cc_lam_ext; trivial.
 red; intros.
 rewrite H0; rewrite H2; reflexivity.
Qed.
 
Lemma iso_fun_cc_prod_sigma : forall A B C,
  morph1 B ->
  morph2 C ->
  iso_fun (cc_prod A (fun x => sigma (B x) (fun y => C x y)))
    (sigma (cc_prod A B) (fun f => cc_prod A (fun x => C x (cc_app f x))))
    (cc_prod_sigma_iso A).
intros A B C Bm Cm.
unfold cc_prod_sigma_iso; constructor; intros.
 apply cc_prod_sigma_iso_morph; reflexivity.

 apply couple_intro_sigma.
  do 2 red; intros.
  apply cc_prod_ext; intros; auto with *.
  red; intros.
  rewrite H3; rewrite H1; reflexivity.

  apply cc_prod_intro; intros; auto with *.
   do 2 red; intros.
   rewrite H1; reflexivity.

   specialize cc_prod_elim with (1:=H) (2:=H0); intro.
   apply fst_typ_sigma in H1; trivial.

  apply cc_prod_intro; intros.
   do 2 red; intros.
   rewrite H1; reflexivity.

   do 2 red; intros.
   apply Cm; trivial.
   apply cc_app_morph; trivial.
   apply cc_lam_ext; intros; auto with *.
   red; intros.
   rewrite H3 ;reflexivity.

   specialize cc_prod_elim with (1:=H) (2:=H0); intro.
   apply snd_typ_sigma with (2:=H1); auto with *.
    do 2 red; intros; apply Cm; auto with *.

    rewrite cc_beta_eq; auto with *.
    do 2 red; intros.
    rewrite H3; reflexivity.

 apply couple_injection in H1; destruct H1.
 rewrite (cc_eta_eq _ _ _ H).
 rewrite (cc_eta_eq _ _ _ H0).
 apply cc_lam_ext; intros; auto with *.
 red; intros.
 rewrite <- H4 in H4|-*; clear x'0.
 generalize (cc_app_morph _ _ H1 _ _ H4);
 generalize (cc_app_morph _ _ H2 _ _ H4).
 repeat rewrite cc_beta_eq; auto; try (do 2 red; intros; rewrite H6; reflexivity).
 intros.
 specialize cc_prod_elim with (1:=H) (2:=H3); intro.
 specialize cc_prod_elim with (1:=H0) (2:=H3); intro.
 rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ H7)).
 rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ H8)).
 rewrite H5; rewrite H6; reflexivity.

 exists (cc_lam A (fun x => couple (cc_app (fst y) x) (cc_app (snd y) x))).
  apply cc_prod_intro; intros.
   do 2 red; intros.
   rewrite H1; reflexivity.

   do 2 red; intros.
   apply sigma_morph; intros; auto with *.
   apply Cm; auto with *.

   apply couple_intro_sigma.
    do 2 red; intros; apply Cm; auto with *.

    apply fst_typ_sigma in H.
    apply cc_prod_elim with (1:=H); trivial.

    apply snd_typ_sigma with (y:= fst y) in H; auto with *.
     apply cc_prod_elim with (1:=H); trivial.

     do 2 red; intros.
     apply cc_prod_ext; auto with *.
     red; intros.
     rewrite H2; rewrite H4; reflexivity.

  rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ H)).
  apply couple_morph.
   apply fst_typ_sigma in H.
   rewrite (cc_eta_eq _ _ _ H).
   apply cc_lam_ext; intros; auto with *.
   red; intros.
   rewrite <- H1.
   clear H1 x'.
   rewrite cc_beta_eq; trivial.
    apply fst_def.

    do 2 red; intros.
    rewrite H2; reflexivity.

   apply snd_typ_sigma with (y:=fst y) in H; auto with *.
    rewrite (cc_eta_eq _ _ _ H).
    apply cc_lam_ext; intros; auto with *.
    red; intros.
    rewrite <- H1.
    clear H1 x'.
    rewrite cc_beta_eq; trivial.
     apply snd_def.

     do 2 red; intros.
     rewrite H2; reflexivity.

    do 2 red; intros.
    apply cc_prod_ext; intros; auto with *.
    red; intros.
    rewrite H1; rewrite H3; reflexivity.
Qed.

Definition prodcart_cc_prod_iso D :=
  fun p => cc_lam D (sum_case (cc_app (fst p)) (cc_app (snd p))).

Instance prodcart_cc_prod_iso_morph : morph2 prodcart_cc_prod_iso.
do 3 red; intros.
unfold prodcart_cc_prod_iso.
apply cc_lam_ext; intros; auto with *.
red; intros.
apply sum_case_morph; trivial.
 red; intros.
 rewrite H0; rewrite H3; reflexivity.

 red; intros.
 rewrite H0; rewrite H3; reflexivity.
Qed.

Lemma iso_fun_prodcart_cc_prod : forall A1 A2 F1 F2,
  morph1 F1 ->
  morph1 F2 ->
  iso_fun (prodcart (cc_prod A1 F1) (cc_prod A2 F2))
    (cc_prod (sum A1 A2) (sum_case F1 F2))
    (prodcart_cc_prod_iso (sum A1 A2)).
constructor; intros.
 apply prodcart_cc_prod_iso_morph; reflexivity.

 apply cc_prod_intro; intros.
  do 2 red; intros.
  apply sum_case_morph; auto with *.
   apply cc_app_morph; reflexivity.
   apply cc_app_morph; reflexivity.

  do 2 red; intros.
  apply sum_case_morph; trivial.

  apply sum_ind with (3:=H2); intros.
   rewrite H4.
   rewrite sum_case_inl; auto with *.
   2:apply cc_app_morph; reflexivity.
   rewrite sum_case_inl; auto with *.
   apply cc_prod_elim with (1:=fst_typ _ _ _ H1); trivial.

   rewrite H4.
   rewrite sum_case_inr; auto with *.
   2:apply cc_app_morph; reflexivity.
   rewrite sum_case_inr; auto with *.
   apply cc_prod_elim with (1:=snd_typ _ _ _ H1); trivial.

 unfold prodcart_cc_prod_iso in H3.
 rewrite surj_pair with (1:=H1).
 rewrite surj_pair with (1:=H2).
 apply couple_morph.
  apply fst_typ in H1.
  apply fst_typ in H2.
  rewrite cc_eta_eq  with (1:=H1).
  rewrite cc_eta_eq  with (1:=H2).
  apply cc_lam_ext; intros; auto with *.
  red; intros.
  rewrite <- H5; clear H5 x'0.
  generalize (cc_app_morph _ _  H3 _ _ (reflexivity (inl x0))).
  rewrite cc_beta_eq.
   3:apply inl_typ; trivial.
   rewrite sum_case_inl.
   2:apply cc_app_morph; reflexivity.
   rewrite cc_beta_eq.
    3:apply inl_typ; trivial.
    rewrite sum_case_inl; trivial.
    apply cc_app_morph; reflexivity.

    do 2 red; intros.
    apply sum_case_morph; trivial.
     apply cc_app_morph; reflexivity.
     apply cc_app_morph; reflexivity.

   do 2 red; intros.
   apply sum_case_morph; trivial.
    apply cc_app_morph; reflexivity.
    apply cc_app_morph; reflexivity.

  apply snd_typ in H1.
  apply snd_typ in H2.
  rewrite cc_eta_eq  with (1:=H1).
  rewrite cc_eta_eq  with (1:=H2).
  apply cc_lam_ext; intros; auto with *.
  red; intros.
  rewrite <- H5; clear H5 x'0.
  generalize (cc_app_morph _ _  H3 _ _ (reflexivity (inr x0))).
  rewrite cc_beta_eq.
   3:apply inr_typ; trivial.
   rewrite sum_case_inr.
   2:apply cc_app_morph; reflexivity.
   rewrite cc_beta_eq.
    3:apply inr_typ; trivial.
    rewrite sum_case_inr; trivial.
    apply cc_app_morph; reflexivity.

    do 2 red; intros.
    apply sum_case_morph; trivial.
     apply cc_app_morph; reflexivity.
     apply cc_app_morph; reflexivity.

   do 2 red; intros.
   apply sum_case_morph; trivial.
    apply cc_app_morph; reflexivity.
    apply cc_app_morph; reflexivity.

 exists (couple (cc_lam A1 (fun a => cc_app y (inl a))) (cc_lam A2 (fun b => cc_app y (inr b)))).
  apply couple_intro.
   apply cc_prod_intro; intros; auto with *.
    do 2 red; intros.
    rewrite H3; reflexivity.

    setoid_replace (F1 x) with (sum_case F1 F2 (inl x)).
     apply cc_prod_elim with (1:=H1).
     apply inl_typ; trivial.

     rewrite sum_case_inl; auto with *.

   apply cc_prod_intro; intros; auto with *.
    do 2 red; intros.
    rewrite H3; reflexivity.

    setoid_replace (F2 x) with (sum_case F1 F2 (inr x)).
     apply cc_prod_elim with (1:=H1).
     apply inr_typ; trivial.

     rewrite sum_case_inr; auto with *.

  unfold prodcart_cc_prod_iso.
  transitivity (cc_lam (sum A1 A2) (fun a => cc_app y a)).
  2:symmetry; apply cc_eta_eq with (1:=H1).
  apply cc_lam_ext; intros; auto with *.
  red; intros.
  rewrite <- H3; clear H3 x'.
  apply sum_ind with (3:=H2); intros.
   rewrite H4.
   rewrite sum_case_inl; auto with *.
    rewrite fst_def.
    rewrite cc_beta_eq; auto with *.
    do 2 red; intros.
    rewrite H6; reflexivity.

    apply cc_app_morph; reflexivity.

   rewrite H4.
   rewrite sum_case_inr; auto with *.
    rewrite snd_def.
    rewrite cc_beta_eq; auto with *.
    do 2 red; intros.
    rewrite H6; reflexivity.

    apply cc_app_morph; reflexivity.
Qed.

(* Hiding the morphism away *)
(*
Record iso X Y : Type := {
  iso_f : set -> set;
  is_iso : iso_fun X Y iso_f
}.

Lemma eq_iso : forall x y, x == y -> iso x y.
exists (fun x => x).
apply eq_iso_fun; intros; auto with *.
do 2 red; auto.
Defined.

Lemma iso_sym : forall X Y, iso X Y -> iso Y X.
destruct 1.
exists (iso_inv X iso_f0); auto.
apply iso_fun_sym; trivial.
Defined.

Lemma iso_trans : forall X Y Z, iso X Y -> iso Y Z -> iso X Z.
destruct 1; destruct 1.
exists (fun a => iso_f1 (iso_f0 a)).
apply iso_fun_trans with (1:=is_iso0); trivial.
Defined.

Lemma sum_iso_morph : forall X X' Y Y',
  iso X X' -> iso Y Y' -> iso (sum X Y) (sum X' Y').
destruct 1; destruct 1.
econstructor.
apply sum_iso_fun_morph; eauto.
Defined.

Lemma sum_comm_iso :
  forall X Y, iso (sum X Y) (sum Y X).
intros.
econstructor.
eapply sum_comm_iso_fun.
Defined.

Lemma sum_assoc_iso :
  forall X Y Z, iso (sum (sum X Y) Z) (sum X (sum Y Z)).
intros.
econstructor.
apply sum_assoc_iso_fun.
Defined.

Lemma sigma_iso_morph : forall A A' B B' f,
  iso_fun A A' f ->
  (forall x x', x \in A -> f x == x' -> iso (B x) (B' x')) ->
  iso (sigma A B) (sigma A' B').

Lemma prodcart_iso_morph : forall X X' Y Y',
  iso X X' -> iso Y Y' -> iso (prodcart X Y) (prodcart X' Y').

Lemma prodcart_comm_iso :
  forall X Y, iso (prodcart X Y) (prodcart Y X).
Lemma prodcart_assoc_iso :
  forall X Y Z, iso (prodcart (prodcart X Y) Z) (prodcart X (prodcart Y Z)).


Lemma sigma_iso_morph_eq : forall A A' B B',
  A == A' ->
  (forall x x', x \in A -> x == x' -> iso (B x) (B' x')) ->
  iso (sigma A B) (sigma A' B').
intros.
apply sigma_iso_morph with (fun x => x); trivial.
apply eq_iso_fun; auto with *.
Qed.

Lemma cc_prod_iso_morph : forall A A' B B' f,
  iso_fun A A' f ->
  (forall x x', x \in A -> f x == x' -> iso (B x) (B' x')) ->
  iso (cc_prod A B) (cc_prod A' B').
Admitted.

Lemma cc_prod_iso_morph_eq : forall A A' B B',
  A == A' ->
  (forall x x', x \in A -> x == x' -> iso (B x) (B' x')) ->
  iso (cc_prod A B) (cc_prod A' B').
intros.
apply cc_prod_iso_morph with (fun x => x); trivial.
apply eq_iso_fun; auto with *.
Qed.

Lemma sigma_iso_1_l : forall x F,
  iso (sigma (singl x) F) (F x).

Lemma sigma_iso_1_r : forall A B,
  (forall x, x \in A -> iso (B x) (singl empty)) ->
  iso (sigma A B) A.

Lemma cc_prod_0_l : forall F,
  iso (cc_prod empty F) (singl empty).

Parameter cc_prod_1_l : forall x F,
  iso (cc_prod (singl x) F) (F x).

Parameter cc_prod_1_r : forall A F,
  (forall x, x \in A -> iso (F x) (singl empty)) ->
  iso (cc_prod A F) (singl empty).

Lemma iso_sum_sigma : forall A1 A2 B1 B2,
  iso (sum (sigma A1 B1) (sigma A2 B2))
    (sigma (sum A1 A2) (sum_case B1 B2)).
Admitted.
Lemma iso_prodcart_sigma : forall A1 A2 B1 B2,
  iso (prodcart (sigma A1 B1) (sigma A2 B2))
    (sigma (prodcart A1 A2)
      (fun p => prodcart (B1 (fst p)) (B2 (snd p)))).
Admitted.
Lemma iso_prodcart_cc_prod : forall A1 A2 F1 F2,
  iso (prodcart (cc_prod A1 F1) (cc_prod A2 F2))
    (cc_prod (sum A1 A2) (sum_case F1 F2)).
Admitted.

Lemma iso_sigma_sigma : forall A B C,
  iso (sigma A (fun x => sigma (B x) (fun y => C x y)))
    (sigma (sigma A B) (fun p => C (fst p) (snd p))).
Admitted.
Lemma iso_cc_prod_sigma : forall A B C,
  iso (cc_prod A (fun x => sigma (B x) (fun y => C x y)))
    (sigma (cc_prod A B) (fun f => cc_prod A (fun x => C x (cc_app f x)))). 
Admitted.

Lemma cc_prod_curry : forall A B C,
  iso (cc_prod A (fun x => cc_prod (B x) (fun y => C x y)))
    (cc_prod (sigma A B) (fun p => C (fst p) (snd p))).
Admitted.
*)
