
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

(*
Definition sumSAT (X Y:SAT) :=
  interSAT (fun C => prodSAT (prodSAT X C) (prodSAT (prodSAT Y C) C)).

Lemma INL_intro X Y t :
  inSAT t X -> inSAT (INL t) (sumSAT X Y).
intros.
apply interSAT_intro; trivial.
intros.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
unfold Lc.subst; rewrite Lc.simpl_subst; auto.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
unfold Lc.subst; repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0; auto.
apply prodSAT_elim with (1:=H0); trivial.
Qed.

Lemma INR_intro X Y t :
  inSAT t Y -> inSAT (INR t) (sumSAT X Y).
intros.
apply interSAT_intro; trivial.
intros.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
unfold Lc.subst; rewrite Lc.simpl_subst; auto.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
unfold Lc.subst; rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0; auto.
apply prodSAT_elim with (1:=H1); trivial.
Qed.
*)

(*Definition cartSAT (X Y:SAT) :=
  interSAT (fun C => prodSAT (prodSAT X (prodSAT Y C)) C).

Definition COUPLE (t u:term) :=
  Lc.Abs (Lc.App2 (Lc.Ref 0) (lift 1 t) (lift 1 u)).

Lemma COUPLE_intro X Y t u :
  inSAT t X ->
  inSAT u Y ->
  inSAT (COUPLE t u) (cartSAT X Y).
intros.
apply interSAT_intro; trivial.
intros.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
unfold Lc.subst; repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
apply prodSAT_elim with (2:=H0).
apply prodSAT_elim with (2:=H); trivial.
Qed.
*)

Definition sumReal (X Y:set->SAT) (a:set) : SAT :=
  interSAT (fun C =>
     prodSAT (depSAT (fun x => a==inl x) (fun x => prodSAT (X x) C))
    (prodSAT (depSAT (fun x => a==inr x) (fun x => prodSAT (Y x) C))
     C)).

Lemma Real_sum_case X Y a RX RY C t b1 b2 :
  a ∈ sum X Y ->
  inSAT t (sumReal RX RY a) ->
  (inSAT b1 (depSAT (fun x => a==inl x) (fun x => prodSAT (RX x) C))) ->
  (inSAT b2 (depSAT (fun x => a==inr x) (fun x => prodSAT (RY x) C))) ->
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
apply depSAT_elim with (P:=fun x'=>inl x==inl x')(x:=x) in H1; auto with *.
apply prodSAT_elim with (1:=H1); trivial.
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
apply depSAT_elim with (P:=fun x'=>inr x==inr x')(x:=x) in H2; auto with *.
apply prodSAT_elim with (1:=H2); trivial.
Qed.

(* trop complique:
Record ufamily := mkuFam {
  ufam :> set -> SAT;
  ufam_mrph : Proper (eq_set==>eqSAT) ufam
}.

Definition sumReal (RX RY:set->SAT) (a:set) : SAT :=
  interSAT (fun F:ufamily =>
    prodSAT (depSAT (fun x => a==inl x) (fun x => prodSAT (RX x) (F (inl x))))
   (prodSAT (depSAT (fun x => a==inr x) (fun x => prodSAT (RY x) (F (inr x))))
    (F a))).


Lemma Real_sum_case X Y a f g RX RY C t b1 b2 :
  Proper (eq_set ==> eqSAT) C ->
  morph1 f ->
  morph1 g ->
  a ∈ sum X Y ->
  inSAT t (sumReal RX RY a) ->
  (inSAT b1 (depSAT (fun x => a==inl x) (fun x => prodSAT (RX x) (C (f x))))) ->
  (inSAT b2 (depSAT (fun x => a==inr x) (fun x => prodSAT (RY x) (C (g x))))) ->
  inSAT (Lc.App2 t b1 b2) (C (sum_case f g a)).
intros.
pose (F x := C (sum_case f g x)).
assert (Fm : forall x y, x==y -> eqSAT (F x) (F y)).
 intros.
 apply H.
 apply sum_case_morph; trivial.
pose (FF := @mkuFam F Fm).
apply interSAT_elim with (x:=FF) in H3.
eapply prodSAT_elim;[eapply prodSAT_elim with (1:=H3)|].
 split.
  apply sat_sn in H4; trivial.

  intros (x,?); simpl.
  red; intros.
  change (inSAT (App b1 u) (F (inl x))).
  unfold F.
  rewrite sum_case_inl; auto.
  apply depSAT_elim with (P:=fun x => a==inl x)(x:=x) in H4; trivial.
  apply prodSAT_elim with (1:=H4); trivial.

 split.
  apply sat_sn in H5; trivial.

  intros (x,?); simpl.
  red; intros.
  change (inSAT (App b2 u) (F (inr x))).
  unfold F.
  rewrite sum_case_inr; auto.
  apply depSAT_elim with (P:=fun x=>a==inr x)(x:=x) in H5; trivial.
  apply prodSAT_elim with (1:=H5); trivial.
Qed.

Lemma Real_inl RX RY x t :
  Proper (eq_set ==> eqSAT) RX ->
  inSAT t (RX x) ->
  inSAT (INL t) (sumReal RX RY (inl x)).
intros.
apply interSAT_intro.
 exists (fun _ => snSAT); do 2 red; reflexivity.
intros.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
unfold Lc.subst; rewrite Lc.simpl_subst; auto.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
unfold Lc.subst; repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
apply depSAT_elim with (P:=fun x'=>inl x==inl x')(x:=x) in H1; auto with *.
apply prodSAT_elim with (1:=H1); trivial.
Qed.
Lemma Real_inr RX RY x t :
  Proper (eq_set ==> eqSAT) RY ->
  inSAT t (RY x) ->
  inSAT (INR t) (sumReal RX RY (inr x)).
intros.
apply interSAT_intro.
 exists (fun _ => snSAT); do 2 red; reflexivity.
intros.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
unfold Lc.subst; rewrite Lc.simpl_subst; auto.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
unfold Lc.subst; repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
apply depSAT_elim with (P:=fun x'=>inr x==inr x')(x:=x) in H2; auto with *.
apply prodSAT_elim with (1:=H2); trivial.
Qed.
*)
(* moins bon: depend de X et Y... *)
(*
Record family T := mkFam {
  fam :> set -> SAT;
  fam_mrph : forall x y,  x ∈ T -> x == y -> eqSAT (fam x) (fam y)
}.
Definition sumReal (X Y:set) (RX RY:set->SAT) (a:set) : SAT :=
  interSAT (fun F:family(sum X Y) =>
    prodSAT (depSAT X (fun x => prodSAT (RX x) (F (inl x))))
   (prodSAT (depSAT Y (fun x => prodSAT (RY x) (F (inr x))))
    (F a))).

Lemma sum_narrow X Y a :
  a ∈ sum X Y ->
  a ∈ sum (sum_case (fun x => singl x) (fun _ => empty) a) 
          (sum_case (fun _ => empty) (fun x => singl x) a).
intros.
assert (m1 : morph1 (fun x => singl x)).
 auto with *.
assert (m2 : morph1 (fun _ => empty)).
 do 2 red; auto with *.
apply sum_ind with (3:=H); intros.
 rewrite H1.
 apply inl_typ.
 rewrite sum_case_inl; trivial.
 apply singl_intro.

 rewrite H1.
 apply inr_typ.
 rewrite sum_case_inr; trivial.
 apply singl_intro.
Qed.

Lemma Real_sum_case X Y a f g RX RY C t b1 b2 :
  Proper (eq_set ==> eqSAT) C ->
  morph1 f ->
  morph1 g ->
  a ∈ sum X Y ->
  inSAT t (sumReal X Y RX RY a) ->
  (inSAT b1 (depSAT X (fun x => prodSAT (RX x) (C (f x))))) ->
  (inSAT b2 (depSAT Y (fun x => prodSAT (RY x) (C (g x))))) ->
  inSAT (Lc.App2 t b1 b2) (C (sum_case f g a)).
intros.
pose (F x := C (sum_case f g x)).
assert (Fm : forall x y, x ∈ sum X Y -> x==y -> eqSAT (F x) (F y)).
 intros.
 apply H.
 apply sum_case_morph; trivial.
pose (FF := mkFam F Fm).
apply interSAT_elim with (x:=FF) in H3.
eapply prodSAT_elim;[eapply prodSAT_elim with (1:=H3)|].
 split.
  apply sat_sn in H4; trivial.

  intros (x,?); simpl.
  red; intros.
  change (inSAT (App b1 u) (F (inl x))).
  unfold F.
  rewrite sum_case_inl; auto.
  apply depSAT_elim with (x:=x) in H4; trivial.
  apply prodSAT_elim with (1:=H4); trivial.

 split.
  apply sat_sn in H5; trivial.

  intros (x,?); simpl.
  red; intros.
  change (inSAT (App b2 u) (F (inr x))).
  unfold F.
  rewrite sum_case_inr; auto.
  apply depSAT_elim with (x:=x) in H5; trivial.
  apply prodSAT_elim with (1:=H5); trivial.
Qed.

Lemma Real_inl X Y RX RY x t :
  Proper (eq_set ==> eqSAT) RX ->
  x ∈ X ->
  inSAT t (RX x) ->
  inSAT (INL t) (sumReal X Y RX RY (inl x)).
intros.
apply interSAT_intro.
 exists (fun _ => snSAT); reflexivity.
intros.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
unfold Lc.subst; rewrite Lc.simpl_subst; auto.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
unfold Lc.subst; repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
apply depSAT_elim with (x:=x) in H2; trivial.
apply prodSAT_elim with (1:=H2); trivial.
Qed.
Lemma Real_inr X Y RX RY x t :
  Proper (eq_set ==> eqSAT) RY ->
  x ∈ Y ->
  inSAT t (RY x) ->
  inSAT (INR t) (sumReal X Y RX RY (inr x)).
intros.
apply interSAT_intro.
 exists (fun _ => snSAT); reflexivity.
intros.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
unfold Lc.subst; rewrite Lc.simpl_subst; auto.
apply prodSAT_intro; intros.
unfold Lc.subst; simpl Lc.subst_rec.
unfold Lc.subst; repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
apply depSAT_elim with (x:=x) in H3; trivial.
apply prodSAT_elim with (1:=H3); trivial.
Qed.
*)


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

(** NAT *)

Definition fNAT (A:set->SAT) : set->SAT :=
  sumReal (fun _ => unitSAT) A.

Lemma fNAT_morph :
   Proper ((eq_set ==> eqSAT) ==> eq_set ==> eqSAT) fNAT.
do 3 red; intros.
unfold fNAT.
unfold sumReal.
apply interSAT_morph.
apply indexed_relation_id.
intros.
apply prodSAT_morph.
 unfold depSAT.
 apply interSAT_morph_subset; intros; auto with *.
 rewrite H0; reflexivity.

 apply prodSAT_morph; auto with *.
 unfold depSAT.
 apply interSAT_morph_subset; simpl; intros; auto with *.
  rewrite H0; reflexivity.

  apply prodSAT_morph; auto with *.
Qed.
Hint Resolve fNAT_morph.

Lemma fNAT_irrel (R R' : set -> SAT) (o : set) :
 isOrd o ->
 (forall x x' : set, x ∈ TI NATf o -> x == x' -> eqSAT (R x) (R' x')) ->
 forall x x' : set,
 x ∈ TI NATf (osucc o) -> x == x' -> eqSAT (fNAT R x) (fNAT R' x').
intros.
unfold fNAT.
apply interSAT_morph.
apply indexed_relation_id; intro C.
apply prodSAT_morph.
 apply interSAT_morph_subset; simpl; intros; auto with *.
 rewrite H2; reflexivity.

 apply prodSAT_morph; auto with *.
 apply interSAT_morph_subset; simpl; intros; auto with *.
  rewrite H2; reflexivity.

  apply prodSAT_morph; auto with *.
  apply H0; auto with *.
  rewrite TI_mono_succ in H1; auto.
  rewrite Px in H1; apply sum_inv_r in H1; trivial.
Qed.

Lemma Real_ZERO_gen A :
  inSAT (INL ID) (fNAT A ZERO).
apply Real_inl.
 do 2 red; reflexivity.

 apply ID_intro.
Qed.

Lemma Real_SUCC_gen A n t :
  Proper (eq_set==>eqSAT) A ->
  inSAT t (A n) ->
  inSAT (INR t) (fNAT A (SUCC n)).
intros.
apply Real_inr; trivial.
Qed.

Lemma Real_NATCASE_gen X A C n nt ft gt:
  Proper (eq_set ==> eqSAT) C ->
  n ∈ NATf X ->
  inSAT nt (fNAT A n) ->
  inSAT ft (C ZERO) ->
  inSAT gt (depSAT (fun x => x ∈ X) (fun x => prodSAT (A x) (C (SUCC x)))) ->
  inSAT (Lc.App2 nt (Lc.Abs (Lc.lift 1 ft)) gt) (C n).
intros Cm nty nreal freal greal.
apply Real_sum_case with ZFind_basic.UNIT X n (fun _ => unitSAT) A; trivial.
 apply depSAT_intro.
  apply Lc.sn_abs.
  apply Lc.sn_lift.
  apply sat_sn in freal; trivial.

  intros.
  rewrite H in nty; apply sum_inv_l in nty.
  apply ZFind_basic.unit_elim in nty.
  rewrite nty in H.
  apply prodSAT_intro; intros.
  unfold Lc.subst; rewrite Lc.simpl_subst; auto.
  rewrite Lc.lift0; trivial.
  rewrite H; trivial.

 apply depSAT_intro.
  apply sat_sn in greal; trivial.

  intros.
  rewrite H in nty; apply sum_inv_r in nty.
  apply prodSAT_intro'; intros.
  rewrite H.
  apply prodSAT_elim with (2:=H0).
  apply depSAT_elim with (P:=fun x => x ∈ X)(x:=x) in greal; trivial.
Qed.

Definition fNATi o := tiSAT NATf fNAT o.

Instance fNATi_morph :
  Proper (eq_set ==> eq_set ==> eqSAT) fNATi.
apply tiSAT_morph; auto.
Qed.

Lemma fNATi_mono o1 o2:
  isOrd o1 ->
  isOrd o2 ->
  o1 ⊆ o2 ->
  forall x,
  x ∈ NATi o1 ->
  eqSAT (fNATi o1 x) (fNATi o2 x).
intros.
apply tiSAT_mono; trivial.
intros; apply fNAT_irrel with (o:=o'); trivial.
Qed.

Lemma fNATi_succ_eq o x :
  isOrd o ->
  x ∈ NATi (osucc o) ->
  eqSAT (fNATi (osucc o) x) (fNAT (fNATi o) x).
intros.
apply tiSAT_succ_eq; auto.
intros; apply fNAT_irrel with (o:=o'); trivial.
Qed.

Lemma fNATi_fix x :
  x ∈ NAT ->
  eqSAT (fNATi omega x) (fNAT (fNATi omega) x).
intros.
apply tiSAT_eq; auto with *.
intros; apply fNAT_irrel with (o:=o'); trivial.
Qed.

Lemma Real_ZERO o :
  isOrd o ->
  inSAT (INL ID) (fNATi (osucc o) ZERO).
intros.
rewrite fNATi_succ_eq; trivial.
 apply Real_ZERO_gen.

 apply ZEROi_typ; trivial.
Qed.

Lemma Real_SUCC o n t :
  isOrd o ->
  n ∈ NATi o ->
  inSAT t (fNATi o n) ->
  inSAT (INR t) (fNATi (osucc o) (SUCC n)).
intros.
rewrite fNATi_succ_eq; trivial.
 apply Real_inr; trivial.
 apply fNATi_morph; reflexivity.

 apply SUCCi_typ; trivial.
Qed.


Lemma Real_NATCASE o C n nt ft gt:
  isOrd o ->
  Proper (eq_set ==> eqSAT) C ->
  n ∈ NATi (osucc o) ->
  inSAT nt (fNATi (osucc o) n) ->
  inSAT ft (C ZERO) ->
  inSAT gt (depSAT (fun x => x ∈ NATi o) (fun x => prodSAT (fNATi o x) (C (SUCC x)))) ->
  inSAT (Lc.App2 nt (Lc.Abs (Lc.lift 1 ft)) gt) (C n).
intros oo Cm nty nreal freal greal.
rewrite fNATi_succ_eq in nreal; trivial.
unfold NATi in nty; rewrite TI_mono_succ in nty; auto.
apply Real_NATCASE_gen with (2:=nty) (3:=nreal); auto.
Qed.

(** * Structural fixpoint: *)

(** NATFIX m n --> m (NATFIX m) n when n is a (sum) constructor.
   let G m := "\n. (match n with inl _ => m | inr _ => m end) m n"
   let G m := \n. n (\_.m) (\_.m) m n
    G m -/-> ; G m (inl a) --> m m (inl a); G m (inr b) --> m m (inr b)
   NATFIX m n := G (\x. m (G x)) n
     --> (\x. m (G x)) (\x. m (G x)) n
     --> m (G (\x. m (G x))) n == m (NATFIX m) n
 *)

Definition guard_sum m :=
  Lc.Abs (Lc.App2 (Lc.App2 (Lc.Ref 0) (Lc.Abs (Lc.lift 2 m)) (Lc.Abs (Lc.lift 2 m)))
            (Lc.lift 1 m) (Lc.Ref 0)).

(** (G m n) reduces to (m m n) when n is a constructor. Note that
    n need not be closed. *)
Lemma G_sim : forall m n,
  (exists t c, (c=0\/c=1) /\ n = Lc.Abs (Lc.Abs (Lc.App (Lc.Ref c) t))) ->
  Lc.redp (Lc.App (guard_sum m) n) (Lc.App2 m m n).
intros m n (t,(c,(eqc,eqn))).
unfold guard_sum.
eapply t_trans.
 apply t_step.
 apply Lc.beta.
unfold Lc.subst; simpl.
repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
apply Lc.redp_app_l.
apply Lc.redp_app_l.
rewrite eqn.
eapply t_trans.
 apply t_step.
 apply Lc.app_red_l.
 apply Lc.beta.
destruct eqc; subst c.
 unfold Lc.subst; simpl.
 eapply t_trans.
  apply t_step.
  apply Lc.beta.
 unfold Lc.subst; simpl.
 rewrite Lc.lift0.
 apply t_step.
 apply Lc.red1_beta.
 unfold Lc.subst; rewrite Lc.simpl_subst; auto.
 rewrite Lc.lift0; trivial.

 unfold Lc.subst; simpl.
 eapply t_trans.
  apply t_step.
  apply Lc.beta.
 unfold Lc.subst; simpl; rewrite Lc.simpl_subst_rec; auto.
 rewrite Lc.lift_rec0.
 apply t_step.
 apply Lc.red1_beta.
 unfold Lc.subst; rewrite Lc.simpl_subst; auto.
 rewrite Lc.lift0; trivial.
Qed.

(*
Definition guard_couple m :=
  Lc.Abs (Lc.App2 (Lc.App (Lc.Ref 0) (Lc.Abs (Lc.Abs (Lc.lift 3 m)))) (Lc.lift 1 m) (Lc.Ref 0)).

(** (G m n) reduces to (m m n) when n is a constructor. Note that
    n need not be closed. *)
Lemma G_sim : forall m n,
  (exists t1 t2, n = Lc.Abs (Lc.App2 (Lc.Ref 0) t1 t2)) ->
  Lc.redp (Lc.App (guard_couple m) n) (Lc.App2 m m n).
intros m n (t1,(t2,eqn)).
unfold guard_couple.
eapply t_trans.
 apply t_step.
 apply Lc.beta.
unfold Lc.subst; simpl.
repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
apply Lc.redp_app_l.
apply Lc.redp_app_l.
rewrite eqn.
eapply t_trans.
 apply t_step.
 apply Lc.beta.
unfold Lc.subst; simpl.
rewrite Lc.lift0.
eapply t_trans.
 apply t_step.
 apply Lc.app_red_l.
 apply Lc.beta.
unfold Lc.subst; simpl.
rewrite Lc.simpl_subst; auto.
apply t_step.
apply Lc.red1_beta.
unfold Lc.subst; simpl.
rewrite Lc.simpl_subst; auto.
rewrite Lc.lift0; trivial.
Qed.
*)

Lemma G_sat A k m t X :
  k ∈ NAT ->
  inSAT t (fNAT A k) ->
  inSAT (Lc.App2 m m t) X ->
  inSAT (Lc.App (guard_sum m) t) X.
intros.
unfold guard_sum.
apply inSAT_exp; intros.
 right; apply sat_sn in H0; trivial.
unfold Lc.subst; simpl Lc.subst_rec.
repeat rewrite Lc.simpl_subst; auto.
repeat rewrite Lc.lift0.
revert X H1; apply inSAT_context.
apply inSAT_context.
intros.
apply Real_NATCASE_gen with (X:=NAT) (A:=A) (C:=fun _ => S) (n:=k); auto.
 do 2 red; reflexivity.

 rewrite NAT_eq in H; trivial.

 apply depSAT_intro; intros.
  apply Lc.sn_abs.
  apply Lc.sn_lift.
  apply sat_sn in H1; trivial.

  apply prodSAT_intro; intros.
  unfold Lc.subst; simpl Lc.subst_rec.
  rewrite Lc.simpl_subst; auto.
  rewrite Lc.lift0; trivial.
Qed.

Lemma sn_G_inv m : Lc.sn (guard_sum m) -> Lc.sn m.
intros.
unfold guard_sum in H.
eapply subterm_sn in H;[|constructor].
eapply subterm_sn in H;[|apply sbtrm_app_l].
eapply subterm_sn in H;[|apply sbtrm_app_r].
apply sn_lift_inv with (1:=H) (2:=eq_refl).
Qed.


Definition NATFIX m :=
  guard_sum (Lc.Abs (Lc.App  (Lc.lift 1 m) (guard_sum (Lc.Ref 0)))).

(** NATFIX reduces as a fixpoint combinator when applied to a constructor *)
Lemma NATFIX_sim : forall m n,
  (exists t c, (c=0\/c=1) /\ n = Lc.Abs (Lc.Abs (Lc.App (Lc.Ref c) t))) ->
  Lc.redp (Lc.App (NATFIX m) n) (Lc.App2 m (NATFIX m) n).
intros.
unfold NATFIX at 1.
eapply t_trans.
 apply G_sim; trivial.
apply Lc.redp_app_l.
apply t_step.
apply Lc.red1_beta.
set (t1 := Lc.Abs (Lc.App (Lc.lift 1 m) (guard_sum (Lc.Ref 0)))).
unfold Lc.subst; simpl.
rewrite Lc.simpl_subst; auto.
rewrite Lc.lift0.
reflexivity.
Qed.

(** The guard is needed mainly here: NATFIX m does not reduce *)
Lemma sn_natfix o m X B:
  isOrd o ->
  inSAT m (interSAT (fun o':{o'|o' ∈ osucc o} => let o1:=proj1_sig o' in
        prodSAT (depSAT (fun n => n ∈ NATi o1) (fun n => prodSAT (fNATi o1 n) (X o1 n))) (B o'))) ->
  sn (NATFIX m).
intros.
assert (empty ∈ osucc o).
 apply isOrd_plump with o; auto with *.
  red; intros.
  apply empty_ax in H1; contradiction.
  apply lt_osucc; trivial.
apply interSAT_elim with (x:=exist (fun o'=>o'∈ osucc o) empty H1) in H0.
simpl proj1_sig in H0.
unfold NATFIX.
assert (sn (Lc.Abs (Lc.App (Lc.lift 1 m) (guard_sum (Lc.Ref 0))))).
 apply sn_abs.
 assert (inSAT (guard_sum (Lc.Ref 0)) (depSAT(fun n => n ∈ NATi empty) (fun n => prodSAT (fNATi empty n) (X empty n)))).
  apply depSAT_intro; intros.
   apply sn_abs.
   constructor; intros.
   apply nf_norm in H2; try contradiction.
   repeat constructor.

   apply prodSAT_intro'; intros.
   eapply G_sat with (A:=fNATi empty) (k:=x).
    revert H2; apply NATi_NAT; auto with *.

    unfold fNATi.
    rewrite <- tiSAT_succ_eq; auto.
     2:intros; apply fNAT_irrel with (o:= o'); trivial.
     2:revert H2; apply TI_incl; auto.
    rewrite fNATi_mono with (o2:=osucc empty) in H3; auto.
    red; intros.
    apply empty_ax in H4; contradiction.

    apply prodSAT_elim with (A:=snSAT).
    2:apply sat_sn in H3; trivial.
    apply prodSAT_elim with (A:=snSAT).
    apply varSAT.
    apply varSAT.

 specialize prodSAT_elim with (1:=H0)(2:=H2); intro.
 apply sat_sn in H3; trivial.
 apply sn_subst with (Ref 0).
 unfold Lc.subst; simpl.
 rewrite simpl_subst; auto.
 rewrite lift0; auto.

apply sn_abs.
apply prodSAT_elim with (A:=snSAT) (B:=snSAT).
2:simpl; auto with *.
apply prodSAT_elim with (A:=snSAT).
 apply prodSAT_elim with (A:=snSAT).
  apply prodSAT_elim with (A:=snSAT).
   apply varSAT.
   apply sn_abs; apply sn_lift; trivial.
  apply sn_abs; apply sn_lift; trivial.
 apply sn_lift; trivial.
Qed.


Lemma NATFIX_sat : forall o m X,
  isOrd o ->
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ NATi y ->
   inclSAT (X y n) (X y' n)) ->
  inSAT m (interSAT (fun o':{o'|o' ∈ osucc o} => let o1:=proj1_sig o' in let o2 := osucc o1 in
        prodSAT (depSAT (fun n => n ∈ NATi o1) (fun n => prodSAT (fNATi o1 n) (X o1 n)))
                (depSAT (fun n => n ∈ NATi o2) (fun n => prodSAT (fNATi o2 n) (X o2 n))))) ->
  inSAT (NATFIX m) (depSAT (fun n => n ∈ NATi o) (fun n => prodSAT (fNATi o n) (X o n))).
intros o m X oo Xmono msat.
elim oo using isOrd_ind; intros.
apply depSAT_intro.
 apply sn_natfix with (o:=o) (X:=X) (2:=msat); trivial.

intros x i.
assert (tyx : x ∈ NAT).
 apply NATi_NAT with y; trivial.
apply TI_elim in i; auto with *.
destruct i as (z,?,?).
assert (zo : isOrd z).
 apply isOrd_inv with y; trivial.
unfold NATFIX.
rewrite <- ZFfix.TI_mono_succ in H3; auto with *.
apply prodSAT_intro'.
intros t tty.
assert (tty' : inSAT t (fNAT (fNATi z) x)).
 rewrite <- fNATi_succ_eq; trivial.
 rewrite fNATi_mono with (o2:=y); auto.
 red; intros.
 apply isOrd_plump with z; trivial.
  apply isOrd_inv with (osucc z); auto.
  apply olts_le in H4; trivial.
apply G_sat with (2:=tty'); trivial.
eapply inSAT_context; intros.
 apply inSAT_exp.
  left; simpl.
  apply Bool.orb_true_r.

  unfold Lc.subst; simpl Lc.subst_rec.
  repeat rewrite Lc.simpl_subst; auto.
  rewrite Lc.lift0.
  change (inSAT (Lc.App m (NATFIX m)) S).
  eexact H4.
rewrite <- fNATi_succ_eq in tty'; trivial.
apply Xmono with (osucc z); eauto using isOrd_inv.
 red; intros.
 apply isOrd_plump with z; trivial.
  eauto using isOrd_inv.
  apply olts_le; trivial.
apply prodSAT_elim with (A:=fNATi (osucc z) x); trivial.
assert (z ∈ osucc o).
 apply isOrd_trans with o; auto.
 apply H0; trivial.
apply interSAT_elim with (x:=exist (fun o'=>o' ∈ osucc o) z H4) in msat.
simpl proj1_sig in msat.
specialize H1 with (1:=H2).
specialize prodSAT_elim with (1:=msat) (2:=H1); intro.
apply (depSAT_elim x H5); trivial.
Qed.
