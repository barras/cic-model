Require Import basic ZF ZFpairs ZFsum ZFrelations.
Require Import ZFcont.
Require Import ZFord ZFfix ZFfunext ZFfixrec.
Require Import ZFfixfun.

Set Implicit Arguments.

(** * Isomorphisms *)

Record iso_fun X Y f : Prop := {
  iso_funm : morph1 f;
  iso_typ : typ_fun f X Y;
  iso_inj : forall x x', x ∈ X -> x' ∈ X -> f x == f x' -> x == x';
  iso_surj : forall y, y ∈ Y -> exists2 x, x ∈ X & f x == y
}.

Lemma iso_fun_ext X X' Y Y' f f' :
  morph1 f' ->
  X==X' ->
  Y==Y' ->
  eq_fun X f f' ->
  iso_fun X Y f ->
  iso_fun X' Y' f'.
intros.
constructor; intros; trivial.
 red; intros.
 rewrite <- H0 in H4.
 rewrite <- H1.
 rewrite <- (H2 _ _ H4 (reflexivity x)).
 apply (iso_typ H3); trivial.

 rewrite <- H0 in H4,H5.
 rewrite <- (H2 _ _ H4 (reflexivity x)) in H6.
 rewrite <- (H2 _ _ H5 (reflexivity x')) in H6.
 apply (iso_inj H3) in H6; trivial.

 rewrite <- H1 in H4.
 destruct (iso_surj H3) with y; trivial.
 rewrite (H2 _ _ H5 (reflexivity x)) in H6.
 rewrite H0 in H5.
 eauto.
Qed.

Instance iso_fun_morph : Proper (eq_set==>eq_set==>(eq_set==>eq_set)==>iff) iso_fun.
apply morph_impl_iff3; auto with *.
do 4 red; intros.
red; apply iso_fun_ext; trivial.
 red; transitivity x1; auto with *.

 red; auto.
Qed.

Lemma iso_change_rhs : forall X Y Y' f,
  Y == Y' ->
  iso_fun X Y f ->
  iso_fun X Y' f.
intros.
generalize (iso_funm H0); intro.
rewrite <- H; trivial.
Qed.

Lemma eq_iso_fun X Y f :
  morph1 f ->
  X == Y ->
  (forall x, x ∈ X -> f x == x) ->
  iso_fun X Y f.
constructor; intros; trivial.
 red; intros.
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

(** Inverse and symmetry *)

Definition iso_inv X f y := union (subset X (fun x => f x == y)).

Instance iso_inv_morph0 : forall A f, morph1 (iso_inv A f).
do 2 red; intros.
unfold iso_inv.
apply union_morph.
apply subset_ext; intros.  (* strengthened subset_morph *)
 apply subset_intro; trivial.
 rewrite H; trivial.

 apply subset_elim1 in H0; trivial.

 apply subset_elim2 in H0; destruct H0.
 rewrite H in H1; eauto.
Qed.

Lemma iso_inv_ext A A' f f' x x' :
  A == A' ->
  eq_fun A f f' ->
  x == x' ->
  iso_inv A f x == iso_inv A' f' x'.
intros.
unfold iso_inv.
apply union_morph.
apply subset_morph; intros; trivial.
red; intros.
rewrite <- H1; rewrite (H0 _ _ H2 (reflexivity _)); reflexivity.
Qed.

Instance iso_inv_morph : Proper (eq_set ==> (eq_set ==> eq_set) ==> eq_set ==> eq_set) iso_inv.
do 4 red; intros.
unfold iso_inv.
apply union_morph; apply subset_morph; trivial.
red; intros.
rewrite (H0 _ _ (reflexivity _)); rewrite H1; reflexivity.
Qed.

Lemma iso_inv_eq : forall X Y f y,
   iso_fun X Y f -> y ∈ Y -> f (iso_inv X f y) == y.
destruct 1; intros.
unfold iso_inv.
destruct iso_surj0 with y; trivial.
refine (transitivity _ _);
 [apply iso_funm0;
  apply union_subset_singl with (y:=x)(y':=x); auto with *|];
 auto with *.
intros.
apply iso_inj0; trivial.
transitivity y; auto with *.
Qed.

Lemma iso_inv_eq2 : forall X Y f x,
   iso_fun X Y f -> x ∈ X -> iso_inv X f (f x) == x.
destruct 1; intros.
unfold iso_inv.
rewrite union_subset_singl with (y:=x) (y':=x); auto with *.
intros.
apply iso_inj0; trivial.
transitivity (f x); auto with *.
Qed.

Lemma iso_inv_typ : forall X Y f y,
   iso_fun X Y f -> y ∈ Y -> iso_inv X f y ∈ X.
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

 red; intros.
 apply iso_inv_typ with (1:=H); trivial.

 apply (iso_funm H) in H2.
 rewrite iso_inv_eq with (1:=H) in H2; trivial.
 rewrite iso_inv_eq with (1:=H) in H2; trivial.

 exists (f y); auto.  
  apply (iso_typ H); trivial.

  apply iso_inv_eq2 with (1:=H); trivial.
Qed.

(** Composition and transitivity *)

Lemma iso_fun_trans_eq : forall X Y Z f g h,
  (forall x, g (f x) == h x) ->
  iso_fun X Y f ->
  iso_fun Y Z g ->
  iso_fun X Z h.
intros.
constructor; intros.
 do 2 red; intros.
  rewrite <- H; trivial.
  rewrite <- H.
  apply (iso_funm H1).
  apply (iso_funm H0); trivial.

 red; intros.
 rewrite <- H; trivial.
 apply (iso_typ H1).
 apply (iso_typ H0); trivial.

 do 2 (rewrite <- H in H4; trivial).
 apply (iso_inj H1) in H4.
  apply (iso_inj H0) in H4; trivial.

  apply (iso_typ H0); trivial.
  apply (iso_typ H0); trivial.

 destruct (iso_surj H1 H2).
 destruct (iso_surj H0 H3).
 exists x0; trivial.
 rewrite <- H; auto.
 rewrite <- H4; apply (iso_funm H1); trivial.
Qed.

Definition comp_iso (f:set->set) (g:set->set) := fun x => g (f x).

Lemma iso_fun_trans : forall X Y Z f g, iso_fun X Y f -> iso_fun Y Z g ->
  iso_fun X Z (comp_iso f g).
unfold comp_iso; intros.
apply iso_fun_trans_eq with Y f g; auto with *.
Qed.

Lemma comp_iso_morph : Proper ((eq_set ==> eq_set) ==> (eq_set ==> eq_set) ==> eq_set ==> eq_set) comp_iso.
unfold comp_iso; do 4 red; intros.
apply H0; apply H; trivial.
Qed.

Lemma comp_iso_eq_fun : forall A B f f' g g',
  (forall x, x ∈ A -> f x ∈ B) ->
  eq_fun A f f' ->
  eq_fun B g g' ->
  eq_fun A (comp_iso f g) (comp_iso f' g').
unfold comp_iso; red; intros; auto.
Qed.

Lemma comp_iso_typ X Y Z f g :
  typ_fun f X Y ->
  typ_fun g Y Z ->
  typ_fun (comp_iso f g) X Z.
unfold typ_fun, comp_iso; auto.
Qed.

(** Other properties of isomorphisms *)

(* Alternative introduction rule (when inverse is easy to express) *)

Lemma iso_intro : forall X Y f g,
  morph1 f ->
  (forall x, x ∈ X -> f x ∈ Y /\ g (f x) == x) ->
  (forall y y', y ∈ Y -> y == y' -> g y == g y' /\ g y ∈ X /\ f (g y) == y) ->
  iso_fun X Y f.
intros.
constructor; trivial.
 red; intros.
 apply H0; trivial.

 intros.
 rewrite <- (proj2 (H0 _ H2)); rewrite <- (proj2 (H0 _ H3)).
 apply H1; auto.
 apply H0; trivial.

 intros.
 exists (g y).
  apply H1 with y; auto with *.

  apply H1 with y; auto with *.
Qed.


Lemma iso_fun_inj X1 X2 Y f :
  iso_fun X1 Y f ->
  iso_fun X2 Y f ->
  X1 ⊆ X2 ->
  X1 == X2.
intros.
apply eq_intro; intros; auto.
assert (tyz1 := iso_typ H0 H2).
assert (tyz2 := iso_inv_typ H tyz1).
assert (eqz1 := iso_inv_eq H tyz1).
apply (iso_inj H0) in eqz1; auto.
rewrite <- eqz1; trivial.
Qed.

Lemma iso_fun_narrow X1 X2 Y1 Y2 f x :
  iso_fun X1 Y1 f ->
  iso_fun X2 Y2 f ->
  X1 ⊆ X2 ->
  x ∈ X2 ->
  f x ∈ Y1 ->
  x ∈ X1.
intros.
assert (ty1 := iso_inv_typ H H3).
assert (ty2 := iso_typ H ty1).
assert (eq1 := iso_inv_eq H H3).
apply (iso_inj H0) in eq1; trivial.
 rewrite <- eq1; trivial.

 apply H1.
 apply (iso_inv_typ H); trivial.
Qed.


(** * Disjoint sum *)

Definition sum_isomap f g :=
  sum_case (fun x => inl (f x)) (fun y => inr (g y)).

Lemma sum_isomap_morph : Proper ((eq_set ==> eq_set) ==> (eq_set ==> eq_set) ==> eq_set ==> eq_set) sum_isomap.
unfold sum_isomap; do 4 red; intros.
apply sum_case_morph; trivial.
 red; intros; apply inl_morph; auto.
 red; intros; apply inr_morph; auto.
Qed.

Lemma sum_isomap_ext : forall A B f f' g g',
  eq_fun A f f' ->
  eq_fun B g g' ->
  eq_fun (sum A B) (sum_isomap f g) (sum_isomap f' g').
unfold sum_isomap; intros.
apply sum_case_ext.
 red; intros; apply inl_morph; auto.
 red; intros; apply inr_morph; auto.
Qed.

Lemma sum_isomap_typ X X' Y Y' f g :
  typ_fun f X X' ->
  typ_fun g Y Y' ->
  typ_fun (sum_isomap f g) (sum X Y) (sum X' Y').
unfold typ_fun, sum_isomap; intros tyf tyg x tyx.
apply sum_ind with (3:=tyx); intros.
 rewrite sum_case_inl0; eauto.
 apply inl_typ.
 apply tyf.
 rewrite H0; rewrite dest_sum_inl; trivial.

 rewrite sum_case_inr0; eauto.
 apply inr_typ.
 apply tyg.
 rewrite H0; rewrite dest_sum_inr; trivial.
Qed.


Lemma sum_iso_fun_morph : forall X X' Y Y' f g,
  iso_fun X X' f -> iso_fun Y Y' g ->
  iso_fun (sum X Y) (sum X' Y') (sum_isomap f g).
intros.
constructor; intros.
 apply sum_isomap_morph.
  apply (iso_funm H).
  apply (iso_funm H0).

 apply sum_isomap_typ with (1:=iso_typ H) (2:=iso_typ H0); trivial.

 unfold sum_isomap in H3.
 apply sum_ind with (3:=H1); intros;
   apply sum_ind with (3:=H2); intros.
  rewrite sum_case_inl0 in H3; eauto.
  rewrite sum_case_inl0 in H3; eauto.
  apply inl_inj in H3.
  assert (dest_sum x == x0).
   rewrite H5; apply dest_sum_inl.
  assert (dest_sum x' == x1).
   rewrite H7; apply dest_sum_inl.
  apply (iso_inj H) in H3; trivial.
  2:rewrite H8; trivial.
  2:rewrite H9; trivial.
  rewrite H5; rewrite H7; rewrite <- H8; rewrite <- H9; rewrite H3; reflexivity.

  rewrite sum_case_inl0 in H3; eauto.
  rewrite sum_case_inr0 in H3; eauto.
  apply discr_sum in H3; contradiction.

  rewrite sum_case_inr0 in H3; eauto.
  rewrite sum_case_inl0 in H3; eauto.
  symmetry in H3; apply discr_sum in H3; contradiction.

  rewrite sum_case_inr0 in H3; eauto.
  rewrite sum_case_inr0 in H3; eauto.
  apply inr_inj in H3.
  assert (dest_sum x == y).
   rewrite H5; apply dest_sum_inr.
  assert (dest_sum x' == y0).
   rewrite H7; apply dest_sum_inr.
  apply (iso_inj H0) in H3; trivial.
  2:rewrite H8; trivial.
  2:rewrite H9; trivial.
  rewrite H5; rewrite H7; rewrite <- H8; rewrite <- H9; rewrite H3; reflexivity.

 apply sum_ind with (3:=H1); intros.
  destruct (iso_surj H) with (1:=H2).
  exists (inl x0).
   apply inl_typ; trivial.

   unfold sum_isomap.
   rewrite sum_case_inl0; eauto with *.
   2:econstructor;reflexivity. (* should be solved by eauto... *)
   rewrite H3; apply inl_morph.
   refine (transitivity _ H5); symmetry; apply (iso_funm H); trivial.
   rewrite dest_sum_inl; reflexivity.

  destruct (iso_surj H0) with (1:=H2).
  exists (inr x).
   apply inr_typ; trivial.

   unfold sum_isomap.
   rewrite sum_case_inr0; eauto with *.
   2:econstructor;reflexivity. (* should be solved by eauto... *)
   rewrite H3; apply inr_morph.
   refine (transitivity _ H5); symmetry; apply (iso_funm H0); trivial.
   rewrite dest_sum_inr; reflexivity.
Qed.

Definition sum_isocomm := sum_case inr inl.

Instance sum_isocomm_morph : morph1 sum_isocomm.
do 2 red; intros; unfold sum_isocomm.
apply sum_case_morph; auto with *.
 apply inr_morph.
 apply inl_morph.
Qed.

Lemma sum_isocomm_typ X Y:
  typ_fun sum_isocomm (sum X Y) (sum Y X).
unfold typ_fun, sum_isocomm; intros.
apply sum_ind with (3:=H); intros.
 rewrite H1; rewrite sum_case_inl; trivial with *.
 apply inr_typ; trivial.

 rewrite H1; rewrite sum_case_inr; trivial with *.
 apply inl_typ; trivial.
Qed.

Lemma sum_isocomm_invol : forall X Y x,
  x ∈ sum X Y -> sum_isocomm (sum_isocomm x) == x.
unfold sum_isocomm; intros.
apply sum_ind with (3:=H); intros.
 rewrite H1; rewrite sum_case_inl; trivial with *.
 rewrite sum_case_inr; auto with *.

 rewrite H1; rewrite sum_case_inr; trivial with *.
 rewrite sum_case_inl; auto with *.
Qed.

Lemma sum_comm_iso_fun :
  forall X Y, iso_fun (sum X Y) (sum Y X) sum_isocomm.
intros.
apply iso_intro with sum_isocomm; intros; auto with *.
 split.
  apply sum_isocomm_typ; trivial.
  apply sum_isocomm_invol with (1:=H).

 split;[|split].
  apply sum_isocomm_morph; trivial.
  apply sum_isocomm_typ; trivial.
  apply sum_isocomm_invol with (1:=H).
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

Instance inlr_morph : morph1 (fun y => inr (inl y)).
do 2 red; intros.
 rewrite H; reflexivity.
Qed.

Instance inrr_morph : morph1 (fun y => inr (inr y)).
 do 2 red; intros.
 rewrite H; reflexivity.
Qed.

Instance sclr_morph : morph1 (sum_case inl (fun y => inr (inl y))).
do 2 red; intros; apply sum_case_morph; auto with *.
 apply inl_morph.
 apply inlr_morph.
Qed.

Lemma sum_isoassoc_typ : forall X Y Z,
  typ_fun sum_isoassoc (sum (sum X Y) Z) (sum X (sum Y Z)).
unfold typ_fun, sum_isoassoc; intros.
apply sum_ind with (3:=H); intros.
 rewrite H1; auto with *.
 rewrite sum_case_inl; trivial with *.
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
Qed.

Lemma sum_assoc_iso_fun :
  forall X Y Z, iso_fun (sum (sum X Y) Z) (sum X (sum Y Z)) sum_isoassoc.
unfold sum_isoassoc; intros.
constructor; intros.
 apply sum_isoassoc_morph.

 apply sum_isoassoc_typ; trivial.

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

   rewrite sum_case_inl; auto with *; rewrite sum_case_inl; auto with *.

  apply sum_ind with (3:=H0); intros.
   exists (inl (inr x)).
    apply inl_typ; apply inr_typ; trivial.

    rewrite sum_case_inl; auto with *; rewrite sum_case_inr; auto with *.
    rewrite H1; rewrite H3; reflexivity.

   exists (inr y1).
    apply inr_typ; trivial.

    rewrite sum_case_inr; auto with *.
    rewrite H1; rewrite H3; reflexivity.
Qed.

(** * Dependent pairs *)

Definition sigma_isomap f g :=
  fun p => couple (f (fst p)) (g (fst p) (snd p)).

Instance sigma_isomap_morph :
  Proper ((eq_set ==> eq_set) ==> (eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) sigma_isomap.
unfold sigma_isomap; do 4 red; intros.
apply couple_morph.
 apply fst_morph in H1; auto.

 apply H0.
  apply fst_morph; trivial.
  apply snd_morph; trivial.
Qed.

Lemma sigma_isomap_ext A B f f' g g' :
  ext_fun A B ->
  eq_fun A f f' ->
  (forall x x' y y', x ∈ A -> x == x' -> y ∈ B x -> y == y' -> g x y == g' x' y') ->
  eq_fun (sigma A B) (sigma_isomap f g) (sigma_isomap f' g').
unfold sigma_isomap; red; intros.
apply couple_morph.
 apply fst_typ_sigma in H2; apply fst_morph in H3; auto.

 apply H1.
  apply fst_typ_sigma in H2; trivial.
  apply fst_morph; trivial.
  apply snd_typ_sigma with (2:=H2); auto with *.
  apply snd_morph; trivial.
Qed.


Lemma sigma_isomap_typ A A' B B' f g :
  ext_fun A B ->
  ext_fun A' B' ->
  typ_fun f A A' ->
  (forall x, x ∈ A -> typ_fun (g x) (B x) (B' (f x))) ->
  typ_fun (sigma_isomap f g) (sigma A B) (sigma A' B').
unfold typ_fun, sigma_isomap; intros eB eB' tyf tyg x tyx.
assert (fst x ∈ A).
 apply fst_typ_sigma in tyx; trivial.
apply couple_intro_sigma; auto.
apply tyg; trivial.
apply snd_typ_sigma with (2:=tyx); auto with *.
Qed.

Lemma sigma_iso_fun_morph : forall A A' B B' f g,
  ext_fun A B ->
  ext_fun A' B' ->
  morph2 g ->
  iso_fun A A' f ->
  (forall x x', x ∈ A -> f x == x' -> iso_fun (B x) (B' x') (g x)) ->
  iso_fun (sigma A B) (sigma A' B') (sigma_isomap f g).
intros.
constructor; intros.
 apply sigma_isomap_morph; intros; auto.
 apply (iso_funm H2).

 apply sigma_isomap_typ; intros; trivial.
  exact (iso_typ H2).
  exact (iso_typ (H3 _ _ H4 (reflexivity _))).

 assert (fst x ∈ A).
  apply fst_typ_sigma in H4; trivial.
 apply couple_injection in H6; destruct H6. 
 apply (iso_inj H2) in H6.
 2:apply fst_typ_sigma in H4; trivial.
 2:apply fst_typ_sigma in H5; trivial.
 assert (g (fst x) (snd x) == g (fst x) (snd x')).
  rewrite <- H6 in H8; trivial.
 apply (iso_inj (H3 _ _ H7 (reflexivity _))) in H9.
  rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ H4)).
  rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ H5)).
  rewrite H6; rewrite H9; reflexivity.

  apply snd_typ_sigma with (2:=H4); auto with *.

  apply snd_typ_sigma with (2:=H5); auto with *.

 destruct (iso_surj H2 (y:=fst y)).
  apply fst_typ_sigma in H4; trivial.
 destruct (iso_surj (H3 _ _ H5 H6) (y:=snd y)).
  apply snd_typ_sigma with (2:=H4); auto with *.
 exists (couple x x0).
  apply couple_intro_sigma; auto.

  refine (transitivity _ _);[|symmetry; apply surj_pair with (1:=subset_elim1 _ _ _ H4)].
  apply couple_morph.
   rewrite <- H6; symmetry; apply (iso_funm H2); trivial.
   symmetry; apply fst_def.

   rewrite <- H8; symmetry; apply H1; trivial.
    symmetry; apply fst_def.
    symmetry; apply snd_def.
Qed.


Lemma sigma_iso_fun_1_l : forall x F,
  ext_fun (singl x) F ->
  iso_fun (sigma (singl x) F) (F x) snd.
constructor; intros; auto with *.
 red; intros.
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

Lemma sigma_iso_fun_1_l' : forall x F,
  ext_fun (singl x) F ->
  iso_fun (F x) (sigma (singl x) F) (couple x).
intros.
constructor; intros; auto with *.
 do 2 red; intros; apply couple_morph; auto with *.

 red; intros.
 apply couple_intro_sigma; auto.
 apply singl_intro.

 apply couple_injection in H2; destruct H2; trivial.

 assert (fst y == x).
  apply fst_typ_sigma in H0.
  apply singl_elim in H0; trivial.
 exists (snd y).
  apply eq_elim with (F (fst y)).
   apply H; trivial.
   rewrite H1; apply singl_intro.
  apply snd_typ_sigma with (2:=H0); auto with *.

  rewrite <- H1.
  symmetry; apply surj_pair with (1:=subset_elim1 _ _ _ H0).
Qed.

Lemma sigma_iso_fun_1_r : forall A B,
  ext_fun A B ->
  (forall x, x ∈ A -> iso_fun (B x) (singl empty) (fun _ => empty)) ->
  iso_fun (sigma A B) A fst.
intros.
constructor; intros; auto with *.
 red; intros.
 apply fst_typ_sigma in H1; trivial.

 assert (forall x y y', x ∈ A -> y ∈ B x -> y' ∈ B x -> y == y').
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

Definition sigma_1r_iso f x := couple x (f x).

Lemma sigma_1r_iso_typ A B f :
  ext_fun A B ->
  (forall x, x ∈ A -> f x ∈ B x) ->
  typ_fun (sigma_1r_iso f) A (sigma A B).
intros eB tyf x H.
unfold sigma_1r_iso.
apply couple_intro_sigma; auto.
Qed.

Lemma sigma_iso_fun_1_r' : forall A B f,
  ext_fun A B ->
  morph1 f ->
  (forall x, x ∈ A -> iso_fun (singl empty) (B x) (fun _ => f x)) ->
  iso_fun A (sigma A B) (sigma_1r_iso f).
intros.
unfold sigma_1r_iso.
constructor; intros; auto with *.
 do 2 red; intros; apply couple_morph; auto.

 apply sigma_1r_iso_typ; trivial.
 intros.
 apply (iso_typ (H1 _ H2) (singl_intro empty)).

 apply couple_injection in H4; destruct H4; trivial.

 exists (fst y).
  apply fst_typ_sigma in H2; trivial.

 generalize (fst_typ_sigma _ _ _ H2); intros.
 destruct (iso_surj (H1 _ H3)) with (snd y).
  apply snd_typ_sigma with (2:=H2); auto with *.
 rewrite H5.
 symmetry; apply surj_pair with (1:=subset_elim1 _ _ _ H2).
Qed.

Definition sigma_isoassoc :=
  fun t => couple (couple (fst t) (fst (snd t))) (snd (snd t)).

Instance sigma_isoassoc_morph : morph1 sigma_isoassoc.
do 2 red; intros; unfold sigma_isoassoc.
rewrite H; reflexivity.
Qed.

Lemma sigma_isoassoc_typ A B C :
  ext_fun A B ->
  ext_fun2 A B C ->
  typ_fun sigma_isoassoc
    (sigma A (fun x => sigma (B x) (fun y => C x y)))
    (sigma (sigma A B) (fun p => C (fst p) (snd p))).
intros eB eC x tyx.
assert (fst x ∈ A).
 apply fst_typ_sigma in tyx; trivial.
assert (snd x ∈ sigma (B (fst x)) (fun y => C (fst x) y)).
 apply snd_typ_sigma with (2:=tyx); auto with *.
 do 2 red; intros.
 apply sigma_ext; auto with *.
clear tyx.
assert (fst (snd x) ∈ B (fst x)).
 apply fst_typ_sigma in H0; trivial.
assert (snd (snd x) ∈ C (fst x) (fst (snd x))).
 apply snd_typ_sigma with (2:=H0); auto with *.
 do 2 red; intros.
 auto with *.
clear H0.
apply couple_intro_sigma; auto with *.
 do 2 red; intros.
 apply eC; auto with *.
  apply fst_typ_sigma in H0; trivial.
  rewrite H3; reflexivity.
  apply snd_typ_sigma with (2:=H0); auto with *.
  rewrite H3; reflexivity.

 apply couple_intro_sigma; auto with *.

 apply eq_elim with (2:=H2).
 apply eC; auto.
  rewrite fst_def; reflexivity.
  rewrite snd_def; reflexivity.
Qed.


Lemma iso_sigma_sigma : forall A B C,
  ext_fun A B ->
  ext_fun2 A B C ->
  iso_fun (sigma A (fun x => sigma (B x) (fun y => C x y)))
          (sigma (sigma A B) (fun p => C (fst p) (snd p)))
          sigma_isoassoc.
unfold sigma_isoassoc; constructor; intros.
 apply sigma_isoassoc_morph.

 apply sigma_isoassoc_typ; trivial.

 apply couple_injection in H3; destruct H3.
 apply couple_injection in H3; destruct H3.
 rewrite (surj_pair _ _ _ (subset_elim1 _ _ _  H1)).
 rewrite (surj_pair _ _ _ (subset_elim1 _ _ _  H2)).
 apply couple_morph; trivial.
 assert (snd x ∈ sigma (B (fst x)) (fun y => C (fst x) y)).
  apply snd_typ_sigma with (2:=H1); auto with *.
  do 2 red; intros.
  apply sigma_ext; auto with *.
 assert (snd x' ∈ sigma (B (fst x)) (fun y => C (fst x) y)).
  apply snd_typ_sigma with (2:=H2); auto with *.
  do 2 red; intros.
  apply sigma_ext; auto with *.
 rewrite (surj_pair _ _ _ (subset_elim1 _ _ _  H6)).
 rewrite (surj_pair _ _ _ (subset_elim1 _ _ _  H7)).
 apply couple_morph; trivial.

 exists (couple (fst (fst y)) (couple (snd (fst y)) (snd y))).
  apply couple_intro_sigma.
   do 2 red; intros.
   apply sigma_ext; auto with *.

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

Instance cpl_inl_morph : morph1 (fun p1 => couple (inl (fst p1)) (snd p1)).
 do 2 red; intros.
 rewrite H; reflexivity.
Qed.
Instance cpl_inr_morph : morph1 (fun p2 => couple (inr (fst p2)) (snd p2)).
 do 2 red; intros.
 rewrite H; reflexivity.
Qed.

Lemma sum_sigma_iso_typ A1 A2 B1 B2 :
  ext_fun A1 B1 ->
  ext_fun A2 B2 ->
  typ_fun sum_sigma_iso
    (sum (sigma A1 B1) (sigma A2 B2))
    (sigma (sum A1 A2) (sum_case B1 B2)).
intros eB1 eB2 x tyx.
unfold sum_sigma_iso.
apply sum_ind with (3:=tyx); intros.
 rewrite sum_case_inl0; eauto.
 rewrite H0; rewrite dest_sum_inl.
 apply couple_intro_sigma; auto.
  apply sum_case_ext; trivial.

  apply inl_typ.
  apply fst_typ_sigma in H; trivial.

  rewrite sum_case_inl0.
   apply snd_typ_sigma with A1; auto.
   apply dest_sum_inl.

   exists (fst x0); auto with *.

 rewrite sum_case_inr0; eauto.
 rewrite H0; rewrite dest_sum_inr.
 apply couple_intro_sigma; auto.
  apply sum_case_ext; trivial.

  apply inr_typ.
  apply fst_typ_sigma in H; trivial.

  rewrite sum_case_inr0.
   apply snd_typ_sigma with A2; auto.
   apply dest_sum_inr.

   exists (fst y); auto with *.
Qed.

Lemma iso_fun_sum_sigma : forall A1 A2 B1 B2,
  ext_fun A1 B1 ->
  ext_fun A2 B2 ->
  iso_fun (sum (sigma A1 B1) (sigma A2 B2))
          (sigma (sum A1 A2) (sum_case B1 B2))
          sum_sigma_iso.
unfold sum_sigma_iso; intros A1 A2 B1 B2 bm1 bm2.
constructor; intros.
 apply sum_sigma_iso_morph.

 apply sum_sigma_iso_typ; trivial.

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
   2:apply sum_case_ext; trivial.
   rewrite sum_case_inl0 in H; eauto.
   revert H; apply eq_elim; apply bm1;
     rewrite H1; rewrite dest_sum_inl; auto with *.

   rewrite H1; trivial.
   rewrite sum_case_inr; trivial.
   apply inr_typ.
   apply couple_intro_sigma; auto with *.
   apply snd_typ_sigma with (y:=fst y) in H; auto with *.
   2:apply sum_case_ext; trivial.
   rewrite sum_case_inr0 in H; eauto.
   revert H; apply eq_elim; apply bm2;
     rewrite H1; rewrite dest_sum_inr; auto with *.

  apply sum_ind with (3:=fst_typ_sigma _ _ _ H); intros.
   rewrite H1; trivial.
   rewrite sum_case_inl; trivial.
   rewrite sum_case_inl; trivial with *.
   rewrite fst_def; rewrite  snd_def.
   rewrite <- H1.
   rewrite <- surj_pair with (1:=subset_elim1 _ _ _ H); auto with *.

   rewrite H1; trivial.
   rewrite sum_case_inr; trivial.
   rewrite sum_case_inr; trivial with *.
   rewrite fst_def; rewrite  snd_def.
   rewrite <- H1.
   rewrite <- surj_pair with (1:=subset_elim1 _ _ _ H); auto with *.
Qed.

(** * Cartesian product *)

Lemma prodcart_iso_fun_morph : forall X X' Y Y' f g,
  iso_fun X X' f -> iso_fun Y Y' g ->
  iso_fun (prodcart X Y) (prodcart X' Y') (sigma_isomap f (fun _ => g)).
intros.
assert (fm := iso_funm H).
assert (gm := iso_funm H0).
cut (iso_fun (sigma X (fun _ => Y)) (sigma X' (fun _ => Y'))
       (sigma_isomap f (fun _ => g))).
 apply iso_fun_morph.
  apply sigma_nodep.

  apply sigma_nodep.

  red; intros.
  unfold sigma_isomap.
  rewrite H1; reflexivity.
apply sigma_iso_fun_morph; auto.
do 3 red; intros; apply gm; trivial.
Qed.

Lemma sigma_isomap_typ_prod A A' B B' f g :
  typ_fun f A A' ->
  typ_fun g B B' ->
  typ_fun (sigma_isomap f (fun _ => g)) (prodcart A B) (prodcart A' B').
red; intros.
rewrite sigma_nodep in H1|-*.
revert H1; apply sigma_isomap_typ; trivial.
Qed.


Lemma prodcart_comm_iso_fun :
  forall X Y, iso_fun (prodcart X Y) (prodcart Y X) (fun p => couple (snd p) (fst p)).
constructor; intros.
 do 2 red; intros.
 rewrite H; reflexivity.

 red; intros.
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

Definition prodcart_sigma_iso q :=
  couple (couple (fst (fst q)) (fst (snd q)))
         (couple (snd (fst q)) (snd (snd q))).

Lemma prodcart_sigma_iso_typ A1 A2 B1 B2 :
  ext_fun A1 B1 ->
  ext_fun A2 B2 ->
  typ_fun prodcart_sigma_iso
    (prodcart (sigma A1 B1) (sigma A2 B2))
    (sigma (prodcart A1 A2) (fun p => prodcart (B1 (fst p)) (B2 (snd p)))).
intros eB1 eB2 x H.
assert (ef : ext_fun (prodcart A1 A2)
     (fun p => prodcart (B1 (fst p)) (B2 (snd p)))).
 do 2 red; intros.
 apply prodcart_morph.
  apply eB1.
   apply fst_typ in H0; trivial.
   apply fst_morph; trivial.
  apply eB2.
   apply snd_typ in H0; trivial.
   apply snd_morph; trivial.
generalize (fst_typ _ _ _ H); intro.
generalize (snd_typ _ _ _ H); intro.
clear H.
apply couple_intro_sigma; trivial.
 apply couple_intro.
  apply fst_typ_sigma in H0; trivial.
  apply fst_typ_sigma in H1; trivial.

 apply couple_intro.
  apply snd_typ_sigma with (2:=H0); auto with *.
  rewrite fst_def; reflexivity.

  apply snd_typ_sigma with (2:=H1); auto with *.
  rewrite snd_def; reflexivity.
Qed.

Lemma iso_fun_prodcart_sigma : forall A1 A2 B1 B2,
  ext_fun A1 B1 ->
  ext_fun A2 B2 ->
  iso_fun (prodcart (sigma A1 B1) (sigma A2 B2))
    (sigma (prodcart A1 A2) (fun p => prodcart (B1 (fst p)) (B2 (snd p))))
    prodcart_sigma_iso.
unfold prodcart_sigma_iso; intros.
assert (ef : ext_fun (prodcart A1 A2)
     (fun p => prodcart (B1 (fst p)) (B2 (snd p)))).
 do 2 red; intros.
 apply prodcart_morph.
  apply H.
   apply fst_typ in H1; trivial.
   apply fst_morph; trivial.
  apply H0.
   apply snd_typ in H1; trivial.
   apply snd_morph; trivial.
constructor; intros.
 do 2 red; intros.
 rewrite H1; reflexivity.

 apply prodcart_sigma_iso_typ; trivial.

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

  repeat (rewrite fst_def || rewrite snd_def).
  assert (H2:=H1).
  generalize (fst_typ_sigma _ _ _ H1); intros.
  apply snd_typ_sigma with (y:=fst y) in H2; auto with *.
  rewrite <- surj_pair with (1:=H3).
  rewrite <- surj_pair with (1:=H2).
  rewrite <- surj_pair with (1:=subset_elim1 _ _ _ H1); reflexivity.
Qed.

(** * Dependent product *)

Definition cc_prod_isomap A' f g :=
  fun fct => cc_lam A' (fun x' => g (f x') (cc_app fct (f x'))).

Instance cc_prod_isomap_morph :
  Proper (eq_set ==> (eq_set ==> eq_set) ==> (eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) cc_prod_isomap.
unfold cc_prod_isomap; do 5 red; intros.
apply cc_lam_morph; trivial.
red; intros; apply H1; auto.
apply cc_app_morph; auto.
Qed.

Lemma cc_prod_isomap_ext A B A' A'' f f' g g' :
  A' == A'' ->
  ext_fun A B ->
  eq_fun A' f f' ->
  typ_fun f A' A ->
  (forall x x' y y', x ∈ A' -> x == x' -> y ∈ B (f x) -> y == y' ->
   g (f x) y == g' (f' x') y') ->
  eq_fun (cc_prod A B) (cc_prod_isomap A' f g) (cc_prod_isomap A'' f' g').
unfold cc_prod_isomap; red; intros.
apply cc_lam_ext; trivial.
red; intros.
apply H3; trivial.
 apply cc_prod_elim with (1:=H4); auto.
 apply cc_app_morph; auto with *.
Qed.

Lemma cc_prod_isomap_typ A A' B B' f g :
  ext_fun A' B' ->
  morph1 f ->
  morph2 g ->
  typ_fun f A' A ->
  (forall x, x ∈ A' -> typ_fun (g (f x)) (B (f x)) (B' x)) ->
  typ_fun (cc_prod_isomap A' f g) (cc_prod A B) (cc_prod A' B').
intros eB' fm gm tyf tyg x H. 
unfold cc_prod_isomap.
apply cc_prod_intro; trivial; intros.
 do 2 red; intros.
 apply gm; auto with *.
 apply cc_app_morph; auto with *.

 apply tyg; trivial.
 apply cc_prod_elim with (1:=H); auto.
Qed.

Lemma cc_prod_iso_fun_morph : forall A A' B B' f g,
  ext_fun A B ->
  ext_fun A' B' ->
  morph2 g ->
  iso_fun A' A f ->
  (forall x, x ∈ A' -> iso_fun (B (f x)) (B' x) (g (f x))) ->
  iso_fun (cc_prod A B) (cc_prod A' B') (cc_prod_isomap A' f g).
intros.
assert (fm := iso_funm H2).
assert (tyf := iso_typ H2).
assert (gext : forall h h' x x',
  x ∈ A' ->
  x == x' ->
  h ∈ cc_prod A B ->
  h == h' ->
  g (f x) (cc_app h (f x)) ==
  g (f x') (cc_app h' (f x'))).
 intros.
 apply H1; auto.
 apply cc_app_morph; auto.
unfold cc_prod_isomap; constructor; intros.
 apply cc_prod_isomap_morph; intros; auto with *.

 apply cc_prod_isomap_typ; intros; trivial.
 exact (iso_typ (H3 _ H4)).

 rewrite (cc_eta_eq _ _ _ H4).
 rewrite (cc_eta_eq _ _ _ H5).
 apply cc_lam_ext; intros; auto with *.
 red; intros.
 destruct (iso_surj H2) with x0; trivial.
 generalize (cc_app_morph _ _ H6 _ _ (reflexivity x1)).
 rewrite cc_beta_eq; trivial.
  rewrite cc_beta_eq; trivial.
   intro.
   rewrite <- H8; rewrite <- H10.
   apply (iso_inj (H3 _ H9)) in H11; trivial.
    apply cc_prod_elim with (1:=H4); trivial.
    rewrite <- H10 in H7; trivial.

    apply cc_prod_elim with (1:=H5); trivial.
    rewrite <- H10 in H7; trivial.

   do 2 red; intros.
   apply gext; auto with *.

  do 2 red; intros.
  apply gext; auto with *.

 assert (f'm : ext_fun A (fun x => let x' := iso_inv A' f x in
                                   iso_inv (B (f x')) (g (f x')) (cc_app y x'))).
  do 2 red; intros.
  apply iso_inv_ext; auto.
   apply H.
    apply tyf.
    apply iso_inv_typ with (1:=H2); trivial.

    apply fm.
    apply iso_inv_morph0; trivial.

   red; intros.
   apply H1; auto with *.
   rewrite H6; reflexivity.

   apply cc_app_morph; auto with *.
   apply iso_inv_morph0; trivial.
 exists (cc_lam A (fun x => let x' := iso_inv A' f x in
                            iso_inv (B (f x')) (g (f x')) (cc_app y x'))).
  apply cc_prod_intro; intros; auto.
  assert (iso_inv A' f x ∈ A').
   apply iso_inv_typ with (1:=H2); trivial.
  assert (f (iso_inv A' f x) == x).
   apply iso_inv_eq with (1:=H2); trivial.
  apply eq_elim with (B (f (iso_inv A' f x))).
   symmetry; apply H; auto with *.
  apply iso_inv_typ with (1:=H3 _ H6).
  apply cc_prod_elim with (1:=H4); trivial.

  rewrite (cc_eta_eq _ _ _ H4).
  apply cc_lam_ext; intros; auto with *.
  red; intros.
  assert (x == iso_inv A' f (f x)).
   symmetry.
   apply iso_inv_eq2 with (1:=H2); auto.
  transitivity (g (f x) (iso_inv (B (f x)) (g (f x)) (cc_app y x))).
   symmetry; apply H1; auto with *.
   rewrite cc_beta_eq; auto.
   apply iso_inv_morph; auto with *.
   apply cc_app_morph; auto with *.

   rewrite iso_inv_eq with (1:=H3 _ H5).
    apply cc_app_morph; auto with *.
    apply cc_prod_elim with (1:=H4); trivial.
Qed.

Lemma cc_prod_iso_fun_0_l : forall a F,
  iso_fun (cc_prod empty F) (singl a) (fun _ => a).
intros.
constructor; intros; auto with *.
 do 2 red; reflexivity.

 red; intros.
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

Lemma cc_prod_iso_fun_0_l' : forall a F,
  iso_fun (singl a) (cc_prod empty F) (fun _ => cc_lam empty (fun _ => empty)).
constructor; intros.
 do 2 red; intros.
 apply cc_lam_ext; auto with *.
 red; intros.
 apply empty_ax in H0; contradiction.

 red; intros.
 apply cc_prod_intro; intros; auto with *.
  do 2 red; intros.
  apply empty_ax in H0; contradiction.

  apply empty_ax in H0; contradiction.

 apply singl_elim in H; apply singl_elim in H0; rewrite H0; trivial.

 exists a.
  apply singl_intro.

  refine (transitivity _ (symmetry (cc_eta_eq _ _ _ H))).
  apply cc_lam_ext; auto with *.
  red; intros.
  apply empty_ax in H0; contradiction.
Qed.

Definition cc_prod_iso1l x := fun f => cc_app f x.

Lemma cc_prod_iso_fun_1_l : forall x F,
  (forall x', x == x' -> F x == F x') ->
  iso_fun (cc_prod (singl x) F) (F x) (cc_prod_iso1l x).
unfold cc_prod_iso1l; constructor; intros.
 do 2 red; intros.
 rewrite H0; reflexivity.

 red; intros.
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

Lemma cc_prod_iso_fun_1_l' : forall x F,
  (forall x', x == x' -> F x == F x') ->
  iso_fun (F x) (cc_prod (singl x) F) (fun y => cc_lam (singl x) (fun _ => y)).
constructor; intros.
 do 2 red; intros.
 apply cc_lam_ext; intros; auto with *.
 red; trivial.

 red; intros.
 apply cc_prod_intro; intros.
  do 2 red; reflexivity.

  do 2 red; intros.
  apply singl_elim in H1.
  rewrite H1 in H2; symmetry in H1.
  transitivity (F x);[symmetry|]; auto.

  revert H0; apply eq_elim.
  apply singl_elim in H1; symmetry in H1; auto.

 generalize (cc_app_morph _ _ H2 _ _ (reflexivity x)).
 rewrite cc_beta_eq; auto with *.
 2:apply singl_intro.
 rewrite cc_beta_eq; auto with *.
 apply singl_intro.

 exists (cc_app y x).
  apply cc_prod_elim with (1:=H0).
  apply singl_intro.

  refine (transitivity _ (symmetry (cc_eta_eq _ _ _ H0))).
  apply cc_lam_ext; auto with *.
  red; intros.
  apply singl_elim in H1.
  rewrite H1 in H2; apply cc_app_morph;auto with *.
Qed.

Lemma cc_prod_iso_fun_1_r : forall A F,
  ext_fun A F ->
  (forall x, x ∈ A -> iso_fun (F x) (singl empty) (fun _ => empty)) ->
  iso_fun (cc_prod A F) (singl empty) (fun _ => empty).
constructor; intros.
 do 2 red; reflexivity.

 red; intros.
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

Lemma cc_prod_isocurry_typ A B C :
  ext_fun A B ->
  ext_fun2 A B C ->
  typ_fun (cc_prod_isocurry A B)
    (cc_prod A (fun x => cc_prod (B x) (fun y => C x y)))
    (cc_prod (sigma A B) (fun p => C (fst p) (snd p))).
intros eB eC x H.
unfold cc_prod_isocurry.
apply cc_prod_intro; intros.
 do 2 red; intros.
 rewrite H1; reflexivity.

 do 2 red; intros.
 apply eC.
  apply fst_typ_sigma in H0; trivial.
  rewrite H1; reflexivity.
  apply snd_typ_sigma with (2:=H0); auto with *.
  rewrite H1; reflexivity.

 apply cc_prod_elim with (dom := B (fst x0)) (F:=fun y => C (fst x0) y).
  apply cc_prod_elim with (1:=H).
  apply fst_typ_sigma in H0; trivial.

  apply snd_typ_sigma with (2:=H0); auto with *.
Qed.

Lemma cc_prod_curry_iso_fun : forall A B C,
  ext_fun A B ->
  ext_fun2 A B C ->
  iso_fun (cc_prod A (fun x => cc_prod (B x) (fun y => C x y)))
    (cc_prod (sigma A B) (fun p => C (fst p) (snd p)))
    (cc_prod_isocurry A B).
unfold cc_prod_isocurry; constructor; intros.
 do 2 red; intros.
 apply cc_lam_ext; intros; auto with *.
 red; intros.
 rewrite H1; rewrite H3; reflexivity.

 apply cc_prod_isocurry_typ; trivial.

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
 assert (couple x0 x1 ∈ sigma A B).
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

    assert (couple x x0 ∈ sigma A B).
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

Lemma cc_prod_sigma_iso_typ A B C :
  ext_fun A B ->
  ext_fun2 A B C ->
  typ_fun (cc_prod_sigma_iso A)
    (cc_prod A (fun x => sigma (B x) (fun y => C x y)))
    (sigma (cc_prod A B) (fun f => cc_prod A (fun x => C x (cc_app f x)))).
intros eB eC x H.
unfold cc_prod_sigma_iso.
apply couple_intro_sigma.
 do 2 red; intros.
 apply cc_prod_ext; intros; auto with *.
 red; intros.
 apply eC; auto with *.
  apply cc_prod_elim with (1:=H0); trivial.
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
  apply eC; trivial.
   rewrite cc_beta_eq; auto with *.
    specialize cc_prod_elim with (1:=H) (2:=H0); intros.
    apply fst_typ_sigma in H2; trivial.

    do 2 red; intros.
    rewrite H3; reflexivity.
    
   apply cc_app_morph; trivial.
   apply cc_lam_ext; intros; auto with *.
   red; intros.
   rewrite H3 ;reflexivity.

  specialize cc_prod_elim with (1:=H) (2:=H0); intro.
  apply snd_typ_sigma with (2:=H1); auto with *.
   do 2 red; intros; apply eC; auto with *.

   rewrite cc_beta_eq; auto with *.
   do 2 red; intros.
   rewrite H3; reflexivity.
Qed.

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
  ext_fun A B ->
  ext_fun2 A B C ->
  iso_fun (cc_prod A (fun x => sigma (B x) (fun y => C x y)))
    (sigma (cc_prod A B) (fun f => cc_prod A (fun x => C x (cc_app f x))))
    (cc_prod_sigma_iso A).
intros A B C Bm Cm.
unfold cc_prod_sigma_iso; constructor; intros.
 apply cc_prod_sigma_iso_morph; reflexivity.

 apply cc_prod_sigma_iso_typ; trivial.

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
   apply sigma_ext; intros; auto with *.

   apply couple_intro_sigma.
    do 2 red; intros; apply Cm; auto with *.

    apply fst_typ_sigma in H.
    apply cc_prod_elim with (1:=H); trivial.

    apply snd_typ_sigma with (y:= fst y) in H; auto with *.
     apply cc_prod_elim with (1:=H); trivial.

     do 2 red; intros.
     apply cc_prod_ext; auto with *.
     red; intros.
     apply Cm; auto.
      apply cc_prod_elim with (1:=H1); trivial.
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
    apply Cm; trivial.
     apply cc_prod_elim with (1:=H0); trivial.
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

Lemma prodcart_cc_prod_iso_typ A1 A2 F1 F2 :
  ext_fun A1 F1 ->
  ext_fun A2 F2 ->
  typ_fun (prodcart_cc_prod_iso (sum A1 A2))
    (prodcart (cc_prod A1 F1) (cc_prod A2 F2))
    (cc_prod (sum A1 A2) (sum_case F1 F2)).
intros eF1 eF2 x H.
unfold prodcart_cc_prod_iso.
apply cc_prod_intro; intros.
 do 2 red; intros.
 apply sum_case_morph; auto with *.
  apply cc_app_morph; reflexivity.
  apply cc_app_morph; reflexivity.

 do 2 red; intros.
 apply sum_case_ext with (A1:=A1) (A2:=A2); trivial.

 apply sum_ind with (3:=H0); intros.
  rewrite sum_case_inl0; eauto.
  rewrite sum_case_inl0; eauto.
  apply fst_typ in H.
  apply cc_prod_elim with (1:=H); trivial.
  rewrite H2; rewrite dest_sum_inl; trivial.

  rewrite sum_case_inr0; eauto.
  rewrite sum_case_inr0; eauto.
  apply snd_typ in H.
  apply cc_prod_elim with (1:=H); trivial.
  rewrite H2; rewrite dest_sum_inr; trivial.
Qed.

Lemma iso_fun_prodcart_cc_prod : forall A1 A2 F1 F2,
  ext_fun A1 F1 ->
  ext_fun A2 F2 ->
  iso_fun (prodcart (cc_prod A1 F1) (cc_prod A2 F2))
    (cc_prod (sum A1 A2) (sum_case F1 F2))
    (prodcart_cc_prod_iso (sum A1 A2)).
constructor; intros.
 apply prodcart_cc_prod_iso_morph; reflexivity.

 apply prodcart_cc_prod_iso_typ; trivial.

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

     rewrite sum_case_inl0.
     2:exists x; reflexivity.
     apply H; trivial.
     rewrite dest_sum_inl; reflexivity.

   apply cc_prod_intro; intros; auto with *.
    do 2 red; intros.
    rewrite H3; reflexivity.

    setoid_replace (F2 x) with (sum_case F1 F2 (inr x)).
     apply cc_prod_elim with (1:=H1).
     apply inr_typ; trivial.

     rewrite sum_case_inr0.
     2:exists x; reflexivity.
     apply H0; trivial.
     rewrite dest_sum_inr; reflexivity.

  unfold prodcart_cc_prod_iso.
  transitivity (cc_lam (sum A1 A2) (fun a => cc_app y a)).
  2:symmetry; apply cc_eta_eq with (1:=H1).
  apply cc_lam_ext; intros; auto with *.
  red; intros.
  rewrite <- H3; clear H3 x'.
  apply sum_ind with (3:=H2); intros.
   rewrite sum_case_inl0; eauto with *.
   rewrite fst_def.
   rewrite H4; rewrite dest_sum_inl.
   rewrite cc_beta_eq; auto with *.
   do 2 red; intros.
   rewrite H6; reflexivity.

   rewrite sum_case_inr0; eauto with *.
   rewrite snd_def.
   rewrite H4; rewrite dest_sum_inr.
   rewrite cc_beta_eq; auto with *.
   do 2 red; intros.
   rewrite H6; reflexivity.
Qed.


(** * Transfinite iteration *)

Section TI_iso.

  Definition TI_iso F g o :=
    cc_app (REC (fun o f => cc_lam (F (TI F o)) (g (cc_app f))) o).

Lemma iso_cont : forall F G o f,
  Proper (incl_set ==> incl_set) F ->
  Proper (incl_set ==> incl_set) G ->
  morph1 f ->
  isOrd o ->
  (forall o', o' ∈ o -> iso_fun (TI F (osucc o')) (TI G (osucc o')) f) ->
  iso_fun (TI F o) (TI G o) f.
intros F G o f Fmono Gmono fm oo iso'.
assert (Fm := Fmono_morph _ Fmono).
assert (Gm := Fmono_morph _ Gmono).
constructor; intros; trivial.
 red; intros. 
 apply TI_elim in H; trivial.
 destruct H.
 apply TI_intro with x0; trivial.
 rewrite <- TI_mono_succ; eauto using isOrd_inv.
 apply (iso_typ (iso' _ H)).
 rewrite TI_mono_succ; eauto using isOrd_inv.

 apply TI_elim in H; trivial.
 destruct H.
 apply TI_elim in H0; trivial.
 destruct H0.
 red in H,H0.
 assert (exists2 z, z ∈ o & x ∈ F (TI F z) /\ x' ∈ F (TI F z)).
  destruct (isOrd_dir _ oo x0 x1); trivial.
  destruct H5.
  exists x2; trivial.
  split.
   revert H2; apply Fmono.
   apply TI_mono; eauto using isOrd_inv.

   revert H3; apply Fmono.
   apply TI_mono; eauto using isOrd_inv.
 destruct H4.
 destruct H5.
 apply (iso_inj (iso' _ H4)); trivial.
  rewrite TI_mono_succ; eauto using isOrd_inv.
  rewrite TI_mono_succ; eauto using isOrd_inv.

 apply TI_elim in H; auto.
 destruct H.
 destruct (iso_surj (iso' _ H)) with y.
  rewrite TI_mono_succ; eauto using isOrd_inv.
 exists x0; trivial.
 apply TI_intro with x; trivial.
 rewrite <- TI_mono_succ; eauto using isOrd_inv.
Qed.

  Variable F G : set -> set.
  Variable g : (set -> set) -> set -> set.
  Hypothesis Fmono : Proper (incl_set ==> incl_set) F.
  Hypothesis Gmono : Proper (incl_set ==> incl_set) G.
  Hypothesis gm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) g.
  Hypothesis gext : forall o f f',
    morph1 f ->
    isOrd o ->
    eq_fun (TI F o) f f' ->
    eq_fun (F (TI F o)) (g f) (g f').
  Hypothesis isog' : forall o f, isOrd o ->
    iso_fun (TI F o) (TI G o) f -> iso_fun (F (TI F o)) (G (TI G o)) (g f).

  Let Fm := Fmono_morph _ Fmono.
  Let Gm := Fmono_morph _ Gmono.
  Let egf : forall o' f, isOrd o' -> ext_fun (F (TI F o')) (g (cc_app f)).
do 2 red; intros.
apply gm; trivial.
apply cc_app_morph; auto with *.
Qed.

  Lemma TI_iso_recursor ord :
    recursor ord (TI F)
      (fun o f => iso_fun (TI F o) (TI G o) (cc_app f))
      (fun o f => cc_lam (F (TI F o)) (g (cc_app f))).
constructor; intros.
 apply TI_morph.

 rewrite TI_eq; auto.
 apply sup_morph; auto with *.
 red; intros.
 rewrite TI_mono_succ; auto with *.
  apply Fm.
  apply TI_morph; trivial.

  rewrite <- H1; apply isOrd_inv with o; trivial.

 revert H3; apply iso_fun_ext; auto with *.
  apply cc_app_morph; reflexivity.
  apply TI_morph; trivial.
  apply TI_morph; trivial.

  red; intros.
  rewrite <- H4; auto.

  apply iso_cont; trivial.
  apply cc_app_morph; reflexivity.

 do 3 red; intros.
 apply cc_lam_ext.
  apply Fm; apply TI_morph; auto.

  red; intros.
  apply gm; trivial.
  apply cc_app_morph; auto with *.

 clear H0; rename H1 into ffun, H2 into fiso.
 split.
  rewrite TI_mono_succ; auto with *.
  apply is_cc_fun_lam; auto.

  apply isog' in fiso; trivial.
  revert fiso; apply iso_fun_ext.
   apply cc_app_morph; reflexivity.
   symmetry; apply TI_mono_succ; eauto using isOrd_inv.
   symmetry; apply TI_mono_succ; eauto using isOrd_inv.

   red; intros.  
   rewrite cc_beta_eq; auto.
    rewrite H1; reflexivity.

    rewrite <- H1; trivial.

 (* irrel : *)
 red; intros.
 clear H.
 red; intros.
 destruct H1 as (oo0,(ofun,oiso)); destruct H2 as (oo',(o'fun,o'iso)).
 rewrite cc_beta_eq; auto.
 2:rewrite TI_mono_succ in H; auto with *.
 rewrite cc_beta_eq; auto.
  apply (@gext o); auto with *.
   apply cc_app_morph; auto with *.

   red; intros.
   rewrite <- H2; auto.

   rewrite <- TI_mono_succ; auto.

  rewrite TI_mono_succ in H; auto with *.
  revert H; apply Fmono; apply TI_mono; auto.
Qed.

  Lemma TI_iso_fun o:
    isOrd o ->
    iso_fun (TI F o) (TI G o) (TI_iso F g o) /\
    (forall x, x ∈ TI F o -> TI_iso F g o x == g (TI_iso F g o) x).
intros oord.
split; intros.
 apply REC_typing with (1:=oord) (2:=TI_iso_recursor _).

 unfold TI_iso.
 rewrite REC_expand with (2:=TI_iso_recursor _) (1:=oord); trivial.
 rewrite cc_beta_eq; auto with *.
 rewrite <- TI_mono_succ; auto.
 revert H; apply TI_incl; auto.
Qed.

  Lemma TI_iso_irrel o' o'' :
    isOrd o' ->
    isOrd o'' ->
    o' ⊆ o'' ->
    eq_fun (TI F o') (TI_iso F g o') (TI_iso F g o'').
red; intros.
unfold TI_iso at 2; rewrite <- H3.
apply REC_ord_irrel with (2:=TI_iso_recursor o''); auto with *.
Qed.

  Lemma TI_iso_fixpoint o :
    isOrd o ->
    (TI F o == F (TI F o) <-> TI G o == G (TI G o)).
intros oord.
assert (iso1 := proj1 (TI_iso_fun oord)).
assert (iso2 := isog' oord iso1).
assert (same_iso : eq_fun (TI F o) (TI_iso F g o) (g (TI_iso F g o))).
 red; intros.
 transitivity (TI_iso F g o x').
  unfold TI_iso; rewrite H0; auto with *.
 rewrite H0 in H.
 apply TI_iso_fun; trivial.
assert (iso1' : iso_fun (TI F o) (TI G o) (g (TI_iso F g o))).
 revert iso1; apply iso_fun_ext; auto with *.
 apply gm.
 apply cc_app_morph; reflexivity.
clear iso1.
split; intros.
 apply iso_fun_sym in iso1'.
 apply iso_fun_inj with (TI F o) (iso_inv (TI F o) (g (TI_iso F g o))); trivial.
  apply iso_fun_sym.
  generalize iso2; apply iso_fun_morph; auto with *.
  apply iso_funm in iso2; trivial.

  rewrite <- TI_mono_succ; auto.
  apply TI_incl; auto.

 apply iso_fun_inj with (TI G o) (g (TI_iso F g o)); trivial.
  apply iso_change_rhs with (G (TI G o)); auto with *.

  rewrite <- TI_mono_succ; auto.
  apply TI_incl; auto.
Qed.


End TI_iso.


Section TIF_iso.

  Variable A : set.
  Variable F G : (set -> set) -> set -> set.
  Hypothesis Fm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) F.
  Hypothesis Gm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) G.
  Hypothesis Fmono : mono_fam A F.
  Hypothesis Gmono : mono_fam A G.

Lemma TIF_iso_cont : forall o f,
  (forall a, a ∈ A -> morph1 (f a)) ->
  isOrd o ->
  (forall a o', a ∈ A -> o' ∈ o ->
   iso_fun (TIF A F (osucc o') a) (TIF A G (osucc o') a) (f a)) ->
  forall a, a ∈ A -> iso_fun (TIF A F o a) (TIF A G o a) (f a).
intros o f fm oo iso' a tya.
constructor; intros; auto.
 red; intros. 
 apply TIF_elim in H; trivial.
 destruct H.
 apply TIF_intro with x0; trivial.
 rewrite <- TIF_mono_succ; eauto using isOrd_inv.
 apply (iso_typ (iso' _ _ tya H)).
 rewrite TIF_mono_succ; eauto using isOrd_inv.

 apply TIF_elim in H; trivial.
 destruct H.
 apply TIF_elim in H0; trivial.
 destruct H0.
 red in H,H0.
 assert (exists2 z, z ∈ o & x ∈ F (TIF A F z) a /\ x' ∈ F (TIF A F z) a).
  destruct (isOrd_dir _ oo x0 x1); trivial.
  destruct H5.
  exists x2; trivial.
  split.
   revert H2; apply Fmono; auto with *.
    apply TIF_morph; reflexivity.
    apply TIF_morph; reflexivity.
   red; intros.
   transitivity (TIF A F x2 a0).
    apply TIF_mono; eauto using isOrd_inv.

    red; intro; apply eq_elim.
    apply TIF_morph; auto with *.

   revert H3; apply Fmono; auto with *.
    apply TIF_morph; reflexivity.
    apply TIF_morph; reflexivity.
   red; intros.
   transitivity (TIF A F x2 a0).
    apply TIF_mono; eauto using isOrd_inv.

    red; intro; apply eq_elim.
    apply TIF_morph; auto with *.
 destruct H4.
 destruct H5.
 apply (iso_inj (iso' _ _ tya H4)); trivial.
  rewrite TIF_mono_succ; eauto using isOrd_inv.
  rewrite TIF_mono_succ; eauto using isOrd_inv.

 apply TIF_elim in H; auto.
 destruct H.
 destruct (iso_surj (iso' _ _ tya H)) with y.
  rewrite TIF_mono_succ; eauto using isOrd_inv.
 exists x0; trivial.
 apply TIF_intro with x; trivial.
 rewrite <- TIF_mono_succ; eauto using isOrd_inv.
Qed.


  Let fmrph g f o :
    isOrd o ->
    Proper ((eq_set==>eq_set==>eq_set)==>eq_set==>eq_set==>eq_set) g ->
    ext_fun (sigma A (fun a' => TIF A F (osucc o) a'))
     (fun p => g (fun x y => cc_app f (couple x y)) (fst p) (snd p)).
do 2 red; intros.
apply H0.
2:apply fst_morph; trivial.
2:apply snd_morph; trivial.
do 2 red; intros.
rewrite H3; rewrite H4; reflexivity.
Qed.

  Definition TIF_iso g o a x :=
    cc_app (REC (fun o f =>
         cc_lam (sigma A (fun a' => TIF A F (osucc o) a'))
              (fun p => g (fun x y => cc_app f (couple x y)) (fst p) (snd p))) o)
      (couple a x).


  Variable g : (set -> set -> set) -> set -> set -> set.
  Hypothesis gm : Proper ((eq_set==>eq_set==>eq_set)==>eq_set==>eq_set==>eq_set) g.
  Hypothesis gext :
     forall X f f', morph1 X -> morph2 f -> morph2 f' ->
     (forall a, a ∈ A -> eq_fun (X a) (f a) (f' a)) ->
     forall a, a ∈ A -> eq_fun (F X a) (g f a) (g f' a).
  Hypothesis isog :
     forall X Y f, morph1 X -> morph1 Y -> morph2 f ->
     (forall a, a ∈ A -> iso_fun (X a) (Y a) (f a)) ->
      forall a, a ∈ A -> iso_fun (F X a) (G Y a) (g f a).

  Variable o : set.
  Variable oo : isOrd o.

  Lemma TIF_iso_recursor :
    recursor o (fun o => sigma A (fun a' => TIF A F o a'))
      (fun o f => forall a, a ∈ A -> iso_fun (TIF A F o a) (TIF A G o a) (fun x => cc_app f (couple a x)))
      (fun o f =>  cc_lam (sigma A (fun a' => TIF A F (osucc o) a'))
            (fun p => g (fun x y => cc_app f (couple x y)) (fst p) (snd p))).
constructor; intros.
 do 2 red; intros; apply sigma_morph; auto with *.
 red; intros; apply TIF_morph; auto with *.

 rewrite <- sigma_cont.
 2:do 3 red; intros; apply TIF_morph; auto with *.
 2:apply osucc_morph; trivial.
 apply sigma_ext; intros; auto with *.
 rewrite TIF_eq; auto with *.
 apply sup_morph; intros; auto with *.
 red; intros.
 rewrite <- TIF_mono_succ; eauto using isOrd_inv.
 apply TIF_morph; trivial.
 apply osucc_morph; trivial.

 (* iso *)
 generalize (H3 _ H4); apply iso_fun_ext; auto with *.
  do 2 red; intros. rewrite H5; reflexivity.
  apply TIF_morph; auto with *.
  apply TIF_morph; auto with *.

  red; intros.
  rewrite <- H6; apply H2.
  apply couple_intro_sigma; trivial.
  do 2 red; intros; apply TIF_morph; auto with *.

 (* Q continuity *)
 apply TIF_iso_cont with (f:=fun a0 x => cc_app f (couple a0 x)); auto.
 do 2 red; intros.
 rewrite H5; reflexivity.

 (* F morph *)
 do 3 red; intros.
 apply cc_lam_morph; intros.
  apply sigma_morph; auto with *.
  red; intros; apply TIF_morph; trivial.
  apply osucc_morph; trivial.

  red; intros.
  apply gm.
   do 2 red; intros.
   rewrite H0; rewrite H2; rewrite H3; reflexivity.

   apply fst_morph; trivial.

   apply snd_morph; trivial.

 (* Q typing *)
 split.
  apply is_cc_fun_lam; auto.

  intros.
  apply isog with (a:=a) in H2; trivial.
  2:apply TIF_morph; auto with *.
  2:apply TIF_morph; auto with *.
   revert H2; apply iso_fun_ext.
    do 2 red; intros. apply cc_app_morph;[reflexivity|].
    rewrite H2; reflexivity.

    symmetry; apply TIF_mono_succ; eauto using isOrd_inv.
    symmetry; apply TIF_mono_succ; eauto using isOrd_inv.

    red; intros.  
    rewrite cc_beta_eq; auto.
     apply gm.
      do 2 red; intros; apply cc_app_morph; auto with *.
      apply couple_morph; trivial.

      symmetry; apply fst_def.

      rewrite snd_def; auto with *.

    apply couple_intro_sigma; trivial.
     do 2 red; intros; apply TIF_morph; auto with *.

     rewrite <- H4.
     rewrite TIF_mono_succ; auto.

   do 3 red; intros.
   rewrite H4, H5; reflexivity.

 (* irrel : *)
 red; intros.
 red; intros.
 destruct H1 as (oo0,(ofun,oiso)); destruct H2 as (oo',(o'fun,o'iso)).
 rewrite cc_beta_eq; auto.
 assert (tyfx := fst_typ_sigma _ _ _ H4).
 rewrite cc_beta_eq; auto.
  red in gext.
  apply gext with (X:=TIF A F o0); auto with *.
   apply TIF_morph; auto with *.
   do 3 red; intros; apply cc_app_morph; auto with *.
   apply couple_morph; trivial.
   do 3 red; intros; apply cc_app_morph; auto with *.
   apply couple_morph; trivial.

   red; intros.
   rewrite <- H5; apply H3.
   apply couple_intro_sigma; trivial.
   do 2 red; intros; apply TIF_morph; auto with *.

   apply snd_typ_sigma with (y:=fst x) in H4; auto with *.
   2:do 2 red; intros; apply TIF_morph; auto with *.
   revert H4; apply eq_elim.
   apply TIF_mono_succ; auto with *.

  revert H4; apply sigma_mono; auto with *.
   do 2 red; intros; apply TIF_morph; auto with *.

   do 2 red; intros; apply TIF_morph; auto with *.

   intros.
   transitivity (TIF A F (osucc o') x0).
    apply TIF_mono; auto with *.
    red; intros.
    apply ole_lts; eauto using isOrd_inv.
    apply olts_le in H4; transitivity o0; trivial.

    red; intro; apply eq_elim.
    apply TIF_morph; auto with *.
Qed.


  Lemma TIF_iso_fun :
    (forall a, a ∈ A -> iso_fun (TIF A F o a) (TIF A G o a) (TIF_iso g o a)) /\
    (forall a x, a ∈ A -> x ∈ TIF A F o a -> TIF_iso g o a x == g (TIF_iso g o) a x) /\
    (forall a o' x, isOrd o' -> o' ⊆ o -> a ∈ A -> x ∈ TIF A F o' a ->
     TIF_iso g o' a x == TIF_iso g o a x).
split.
 intros a tya.
 unfold TIF_iso.
 revert a tya.
 apply REC_typing with (2:=TIF_iso_recursor) (1:=oo).

split.
 intros a x tya tyx.
 assert (couple a x ∈ sigma A (fun a' => TIF A F o a')).
  apply couple_intro_sigma; trivial.
  do 2 red; intros; apply TIF_morph; auto with *.
 unfold TIF_iso; rewrite REC_expand with (2:=TIF_iso_recursor) (1:=oo); trivial.
 rewrite cc_beta_eq; auto with *.
  apply gm.
   do 2 red; intros.
   apply cc_app_morph; auto with *.
   apply couple_morph; trivial.

   apply fst_def.

   apply snd_def.

 revert H; apply sigma_mono; auto with *.
  do 2 red; intros; apply TIF_morph; auto with *.
  do 2 red; intros; apply TIF_morph; auto with *.

  intros.
  transitivity (TIF A F (osucc o) x0).
   apply TIF_mono; auto.
   red; intros; apply isOrd_trans with o; auto.

   red; intro; apply eq_elim.
   apply TIF_morph; auto with *.

 intros a o' x oo' ole aty xty.
 unfold TIF_iso.
 apply REC_ord_irrel with (1:=oo) (2:=TIF_iso_recursor); auto with *.
 apply couple_intro_sigma; trivial.
 do 2 red; intros; apply TIF_morph; auto with *.
Qed.

End TIF_iso.

Lemma TIF_iso_morph :
  Proper (eq_set==>((eq_set==>eq_set)==>eq_set==>eq_set)==>((eq_set==>eq_set==>eq_set)==>
          eq_set==>eq_set==>eq_set)==>eq_set==>eq_set==>eq_set==>eq_set)
    TIF_iso.
do 7 red; intros.
unfold TIF_iso.
apply cc_app_morph.
2:apply couple_morph; trivial.
apply REC_morph_gen; trivial.
do 2 red; intros.
apply cc_lam_ext.
 apply sigma_morph; auto.
 red; intros.
 apply TIF_morph_gen; trivial.
 apply osucc_morph; trivial.
red; intros.
apply H1.
 do 2 red; intros.
 apply cc_app_morph; trivial.
 apply couple_morph; trivial.

 apply fst_morph; trivial.
 apply snd_morph; trivial.
Qed.
