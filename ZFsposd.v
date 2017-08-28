Require Import ZF ZFpairs ZFsum ZFrelations ZFord ZFfix ZFfixfun.
Require Import ZFstable ZFiso ZFind_w ZFspos.

(** Inductive families. Indexes are modelled as a constraint over an inductive
    type defined without considering the index values.
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
Hint Resolve dpmono.

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

Lemma dIND_eq : forall p a, isDPositive p -> a ∈ Arg -> dIND p a == dpos_oper p (dIND p) a.
unfold dIND; intros.
unfold dINDi.
assert (oo : isOrd (IND_clos_ord p)).
 unfold IND_clos_ord.
 apply W_o_o.
 apply H.
(**)
rewrite TIF_eq; auto with *.
apply incl_eq.
red; intros.
 rewrite sup_ax in H1.
 destruct H1.
 revert H2; apply (dpmono _ H); auto with *.
  apply TIF_morph; reflexivity.
  apply TIF_morph; reflexivity.
 red; intros.
 apply TIF_incl; auto with *.
 do 2 red; intros.
 apply dpm; trivial.
  apply TIF_morph; trivial.
 reflexivity.

 red; intros.
 rewrite sup_ax.
rewrite (dpm_iso _ H) in H1.
assert (H1' := subset_elim1 _ _ _ H1).
Admitted.

Lemma dINDi_dIND : forall p o,
  isDPositive p ->
  isOrd o ->
  forall a, a ∈ Arg ->
  dINDi p o a ⊆ dIND p a.
induction 2 using isOrd_ind; intros.
unfold dINDi.
rewrite TIF_eq; auto with *.
red; intros.
rewrite sup_ax in H4.
 destruct H4.
 rewrite dIND_eq; trivial.
 revert H5; apply H; auto.
  apply TIF_morph; reflexivity.

  unfold dIND, dINDi.
  do 2 red; intros; apply TIF_morph; auto with *.

  red; intros.
  apply H2; trivial.

 do 2 red; intros; apply dpm; auto with *.
 red; intros.
 apply TIF_morph; auto with *.
Qed.


(** Library of dependent positive operators *)

(** Constraint on the index: corresponds to the conclusion of the constructor *)
Definition dpos_inst i :=
  mkDPositive (pos_cst (singl empty)) (fun _ a => cond_set (i==a) (singl empty))
    (fun _ _ => empty) (fun _ a => i==a).

Lemma isDPos_inst i : isDPositive (dpos_inst i).
constructor; simpl; intros.
 apply isPos_cst.

 do 4 red; intros.
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

Definition dpos_cst A := mkDPositive (pos_cst A) (fun _ _ => A) (fun _ _ => empty) (fun _ _ => True).

Lemma isDPos_cst A : isDPositive (dpos_cst A).
constructor; simpl; intros.
 apply isPos_cst.

 do 4 red; reflexivity.

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

Lemma isDPos_rec j : j ∈ Arg -> isDPositive (dpos_rec j).
constructor; simpl; intros; trivial.
 apply isPos_rec.

 do 4 red; intros.
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

Require Import ZFsum.

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
intros (Fp,Fdm,Fdmo,F3m,F4m,Fty,Fdep) (Gp,Gdm,Gdmo,G3m,G4m,Gty,Gdep).
constructor; simpl; intros.
 apply isPos_sum; trivial.

 do 4 red; intros.
 apply sum_morph.
  apply Fdm; trivial.
  apply Gdm; trivial.

 do 2 red; intros.
 apply sum_mono.
  apply Fdmo; trivial.
  apply Gdmo; trivial.

 do 3 red; intros.
 apply sum_case_morph; trivial.
  red; intros.
  apply F3m; trivial.

  red; intros.
  apply G3m; trivial.

 do 3 red; intros.
 apply and_iff_morphism.
  apply fa_morph; intros x1.
  rewrite <- H.
  apply fa_morph; intros _.
  apply F4m; auto with *.

  apply fa_morph; intros x2.
  rewrite <- H.
  apply fa_morph; intros _.
  apply G4m; auto with *.

 apply sum_case_ind0 with (2:=H); intros.
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

(*
 apply eq_intro; intros.
  apply subset_intro.
   apply sum_ind with (3:=H1); intros.
    rewrite H3; apply inl_typ.
    rewrite Fdep in H2; trivial.
    apply subset_elim1 in H2; trivial.

    rewrite H3; apply inr_typ.
    rewrite Gdep in H2; trivial.
    apply subset_elim1 in H2; trivial.

    split;[split|]; intros.
     assert (z == inl (couple x1 (snd (dest_sum z)))).
      apply sum_ind with (3:=H1); intros.
       unfold trad_sum, comp_iso in 

     admit.

     unfold trad_sum,comp_iso in H4.
     unfold sum_sigma_iso in H4.
     rewrite sum_case_inl0 in H4.
      rewrite fst_def in H4.
      apply discr_sum in H4; contradiction.

      exists (wf F x).
      unfold sum_isomap.
      rewrite sum_case_inl0; eauto.
      apply inl_morph.
      symmetry; apply (iso_funm (w_iso F Fp (sup Arg X))).
       apply subset_elim1 in H2; trivial.
       rewrite H3; rewrite dest_sum_inl; reflexivity.

  apply sum_ind with (3:=H1); intros.
*)
 admit.
Qed.

Definition dpos_consrec (F G:dpositive) :=
  mkDPositive (pos_consrec F G)
    (fun X a => prodcart (dpos_oper F X a) (dpos_oper G X a))
    (fun x => sum_case (w3 F (fst x)) (w3 G (snd x)))
    (fun x i => w4 F (fst x) i /\ w4 G (snd x) i).

Lemma isDPos_consrec F G :
  isDPositive F ->
  isDPositive G ->
  isDPositive (dpos_consrec F G).
intros (Fp,Fdm,Fdmo,F3m,F4m,Fty,?) (Gp,Gdm,Gdmo,G3m,G4m,Gty,?).
constructor; simpl; intros.
 apply isPos_consrec; trivial.

 do 4 red; intros.
 apply prodcart_morph.
  apply Fdm; trivial.
  apply Gdm; trivial.

 do 2 red; intros.
 apply prodcart_mono.
  apply Fdmo; trivial.
  apply Gdmo; trivial.

 do 3 red; intros.
 apply sum_case_morph; trivial.
  red; intros.
  apply F3m; trivial.
  apply fst_morph; trivial.

  red; intros.
  apply G3m; trivial.
  apply snd_morph; trivial.

 do 3 red; intros.
 apply and_iff_morphism.
  apply F4m; trivial.
  apply fst_morph; trivial.

  apply G4m; trivial.
  apply snd_morph; trivial.

 apply sum_case_ind with (6:=H0); intros.
  do 2 red; intros.
  rewrite H1; reflexivity.

  apply F3m; reflexivity.

  apply G3m; reflexivity.

  apply Fty; trivial.
  apply fst_typ in H; trivial.

  apply Gty; trivial.
  apply snd_typ in H; trivial.

 admit.
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
 apply isPos_consnonrec.
  do 2 red; intros.
  apply H in H1.
  apply H1.

  intros.
  apply H0; trivial.

 do 4 red; intros.
 apply sigma_morph; auto with *.
 red; intros.
 apply H; trivial.

 do 2 red; intros.
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

 do 3 red; intros.
 assert (ef := fst_morph _ _ H1).
 assert (es := snd_morph _ _ H1).
 apply H in ef.
 destruct ef as (?,(?,(?,?))).
 apply H5; trivial.

 do 3 red; intros.
 assert (ef := fst_morph _ _ H1).
 assert (es := snd_morph _ _ H1).
 apply H in ef.
 destruct ef as (?,(?,(?,?))).
 apply H6; trivial.

 assert (fty := fst_typ_sigma _ _ _ H1).
 apply snd_typ_sigma with (y:=fst x) in H1; auto with *.
  apply H0; trivial.

  do 2 red; intros.
  apply H in H4.
  apply H4.

 admit.
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
 apply isPos_param.
  do 2 red; intros.
  apply H in H1.
  apply H1.

  intros.
  apply H0; trivial.

 do 4 red; intros.
 apply cc_prod_ext; auto with *.
 red; intros.
 apply H; trivial.

 do 2 red; intros.
 apply cc_prod_covariant; intros; auto with *.
  do 2 red; intros. 
  apply H in H6.
  apply H6; auto with *.

  apply H0; trivial.

 do 3 red; intros.
 assert (ef := fst_morph _ _ H2).
 assert (es := snd_morph _ _ H2).
 apply H in ef.
 destruct ef as (?,(?,(?,?))).
 apply H5; trivial.
 apply cc_app_morph; trivial.
 apply fst_morph; trivial.

 do 3 red; intros.
 apply fa_morph; intros k.
 apply fa_morph; intros kty.
 apply H0; trivial.
 rewrite H1; reflexivity.

 assert (fty := fst_typ_sigma _ _ _ H2).
 apply snd_typ_sigma with (y:=fst i) in H2; auto with *.
  apply H0; trivial.
  apply cc_prod_elim with (1:=H1); trivial.

  do 2 red; intros.
  apply H; trivial.
  rewrite H4; reflexivity.

 admit.
Qed.


End InductiveFamily.

(** Examples *)

Module Vectors.

Require Import ZFnats.

Definition vect A :=
  dpos_sum
    (* vect 0 *)
    (dpos_inst zero)
    (* forall n:N, A -> vect n -> vect (S n) *)
    (dpos_norec N (fun k => dpos_consrec (dpos_cst A) (dpos_consrec (dpos_rec k) (dpos_inst (succ k))))).

Lemma vect_pos A : isDPositive N (vect A).
unfold vect; intros.
apply isDPos_sum.
 apply isDPos_inst.

 apply isDPos_norec.
  do 2 red; intros.
  admit.

  intros.
  apply isDPos_consrec.
   apply isDPos_cst.
  apply isDPos_consrec.
   apply isDPos_rec; trivial.

   apply isDPos_inst.
Qed.

Definition nil := inl empty.

Lemma nil_typ A X :
  morph1 X ->
  nil ∈ dpos_oper (vect A) X zero.
simpl; intros.
apply inl_typ.
rewrite cond_set_ax; split.
 apply singl_intro.
 reflexivity.
Qed.

Definition cons k x l :=
  inr (couple k (couple x (couple l empty))).

Lemma cons_typ A X k x l :
  morph1 X ->
  k ∈ N ->
  x ∈ A ->
  l ∈ X k ->
  cons k x l ∈ dpos_oper (vect A) X (succ k).
simpl; intros.
apply inr_typ.
apply couple_intro_sigma; trivial.
 admit.

 apply couple_intro; trivial.
 apply couple_intro; trivial.
 rewrite cond_set_ax; split.
  apply singl_intro.
  reflexivity.
Qed.

End Vectors.


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
 admit.

 apply couple_intro.
  apply cc_prod_intro; intros; auto with *.
  do 2 red; intros; apply H; apply fm; auto with *. 

  rewrite cond_set_ax; split.
   apply singl_intro.
   reflexivity.
Qed.

End Wd.
End Wd.