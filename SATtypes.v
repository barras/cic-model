
Require Import ZF ZFpairs ZFsum ZFind_nat Sat.
Require Import ZFlambda.
Require Import Lambda.
Module Lc:=Lambda.

Set Implicit Arguments.

(** Unit type *)

Definition unitSAT :=
  interSAT (fun C => prodSAT C C).

Definition ID := Lc.Abs (Lc.Ref 0).

Lemma ID_intro : inSAT ID unitSAT.
apply interSAT_intro with (1:=snSAT).
intros.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
rewrite Lc.lift0.
trivial.
Qed.

(** Disjoint sum *)

Definition INL (t:term) :=
  Lc.Abs (Lc.Abs (Lc.App (Lc.Ref 1) (Lc.lift 2 t))).
Definition INR (t:term) :=
  Lc.Abs (Lc.Abs (Lc.App (Lc.Ref 0) (Lc.lift 2 t))).


Definition sumReal (X Y:set->SAT) (a:set) : SAT :=
  interSAT (fun C =>
     prodSAT (piSAT0 (fun x => a==inl x) X (fun _ => C))
    (prodSAT (piSAT0 (fun x => a==inr x) Y (fun _ => C))
     C)).

Lemma Real_sum_case X Y a RX RY C t b1 b2 :
  a ∈ sum X Y ->
  inSAT t (sumReal RX RY a) ->
  inSAT b1 (piSAT0 (fun x => a==inl x) RX (fun _ => C)) ->
  inSAT b2 (piSAT0 (fun x => a==inr x) RY (fun _ => C)) ->
  inSAT (Lc.App2 t b1 b2) C.
intros.
apply interSAT_elim with (x:=C) in H0.
eapply prodSAT_elim;[apply prodSAT_elim with (1:=H0)|]; trivial.
Qed.

Lemma Real_inl RX RY x t :
  Proper (eq_set ==> eqSAT) RX ->
  inSAT t (RX x) ->
  inSAT (INL t) (sumReal RX RY (inl x)).
intros.
apply interSAT_intro; auto.
intros.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
unfold Lc.subst; rewrite Lc.simpl_subst; auto.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
unfold Lc.subst; repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
apply piSAT0_elim with (x:=x) (u:=t) in H1; auto with *.
Qed.

Lemma Real_inr RX RY x t :
  Proper (eq_set ==> eqSAT) RY ->
  inSAT t (RY x) ->
  inSAT (INR t) (sumReal RX RY (inr x)).
intros.
apply interSAT_intro; auto.
intros.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
unfold Lc.subst; rewrite Lc.simpl_subst; auto.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
unfold Lc.subst; repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
apply piSAT0_elim with (x:=x) (u:=t) in H2; auto with *.
Qed.


(** Transfinite iteration *)

Require Import ZFfixrec.
Require Import ZFrelations.
Require Import ZFord ZFfix.

Definition tiSAT (F:set->set) (A:(set->SAT)->set->SAT) (o:set) (x:set) : SAT :=
  sSAT (cc_app (REC (fun o' f => cc_lam (TI F (osucc o'))
                                   (fun y => iSAT (A (fun z => sSAT (cc_app f z)) y))) o) x).

Lemma tiSAT_ext1 A F f o :
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  ext_fun (TI F (osucc o)) (fun y => iSAT (A (fun z => sSAT (cc_app f z)) y)).
do 2 red; intros.
apply iSAT_morph.
apply H; trivial.
red; intros.
apply sSAT_morph.
rewrite H2; reflexivity.
Qed.
Hint Resolve tiSAT_ext1.

Instance tiSAT_morph F A :
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  Proper (eq_set ==> eq_set ==> eqSAT) (tiSAT F A).
do 3 red; intros.
unfold tiSAT.
apply sSAT_morph.
apply cc_app_morph; trivial.
apply REC_morph; trivial.
do 3 red; intros.
apply cc_lam_ext; auto with *.
 rewrite H2; reflexivity.

 red; intros.
 apply iSAT_morph.
 apply H; trivial.
 red; intros.
 rewrite H3; rewrite H6; reflexivity.
Qed.

Lemma tiSAT_recursor o A F :
  Proper (incl_set==>incl_set) F ->
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  (forall R R' o', isOrd o' -> o' ⊆ o -> (forall x x', x ∈ TI F o' -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o ->
  recursor o (TI F)
    (fun o f => forall x, x∈TI F o -> cc_app f x == iSAT(sSAT(cc_app f x)))
    (fun o' f => cc_lam (TI F (osucc o')) (fun y => iSAT (A (fun z => sSAT (cc_app f z)) y))).
intros Fm Am Aext oo.
split; intros.
 apply TI_morph.

 apply TI_mono_eq; trivial.

 red in H2.
 rewrite <- H1 in H4.
 rewrite <- H2; auto.

 apply TI_elim in H3; auto.
 destruct H3.
 rewrite <- TI_mono_succ in H4; trivial.
 2:apply isOrd_inv with o0; trivial.
 eauto.

 do 3 red; intros.
 apply cc_lam_ext.
  rewrite H; reflexivity.

  red; intros.
  apply iSAT_morph.
  apply Am; trivial.
  red; intros.
  rewrite H0; rewrite H3; reflexivity.

 split; intros.
  apply is_cc_fun_lam; auto.

  rewrite cc_beta_eq; auto.
  rewrite iSAT_id; reflexivity.

 red; red; intros.
 rewrite cc_beta_eq; auto.
 rewrite cc_beta_eq; auto.
  apply iSAT_morph.
  apply Aext with o0; auto with *.
   apply H1.
   transitivity o'; trivial.
  intros.
  apply sSAT_morph.
  rewrite <- H6.
  apply H3; trivial.

  revert H4; apply TI_mono; auto with *.
   apply isOrd_succ; apply H2.
   apply isOrd_succ; apply H1.
   apply osucc_mono; trivial.
    apply H1.
    apply H2.
Qed.


Lemma tiSAT_eq o A F :
  Proper (incl_set==>incl_set) F ->
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  (forall R R' o', isOrd o' -> o' ⊆ o -> (forall x x', x ∈ TI F o' -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o ->
  forall x,
  x ∈ TI F o ->
  eqSAT (tiSAT F A o x) (A (tiSAT F A o) x).
intros.
unfold tiSAT.
specialize tiSAT_recursor with (1:=H) (2:=H0) (3:=H1) (4:=H2); intro rec.
rewrite REC_expand with (1:=H2) (2:=rec) (3:=H3).
rewrite cc_beta_eq.
 rewrite iSAT_id.
 reflexivity.

 do 2 red; intros.
 apply iSAT_morph.
 apply H0; trivial.
 red; intros.
 apply sSAT_morph.
 apply cc_app_morph; trivial.
 reflexivity.

 revert H3; apply TI_incl; auto.
Qed.

Lemma tiSAT_mono o1 o2 A F:
  Proper (incl_set==>incl_set) F ->
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  (forall R R' o', isOrd o' -> o' ⊆ o2 -> (forall x x', x ∈ TI F o' -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o1 ->
  isOrd o2 ->
  o1 ⊆ o2 ->
  forall x,
  x ∈ TI F o1 ->
  eqSAT (tiSAT F A o1 x) (tiSAT F A o2 x).
intros.
specialize tiSAT_recursor with (1:=H) (2:=H0) (3:=H1) (4:=H3); intro rec.
unfold tiSAT at 2.
rewrite <- REC_ord_irrel with (2:=rec) (o:=o1); auto with *.
reflexivity.
Qed.

Lemma tiSAT_succ_eq o A F :
  Proper (incl_set==>incl_set) F ->
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  (forall R R' o', isOrd o' -> o' ⊆ osucc o -> (forall x x', x ∈ TI F o' -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o ->
  forall x,
  x ∈ TI F (osucc o) ->
  eqSAT (tiSAT F A (osucc o) x) (A (tiSAT F A o) x).
intros.
rewrite tiSAT_eq; auto.
apply H1 with o; auto with *.
 red; intros; apply isOrd_trans with o; auto.
intros.
transitivity (tiSAT F A o x0).
 symmetry; apply tiSAT_mono; auto with *.
 red; intros; apply isOrd_trans with o; auto.

 apply tiSAT_morph; auto with *.
Qed.

