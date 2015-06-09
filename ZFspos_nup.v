Require Import ZF ZFpairs ZFsum ZFrelations ZFord ZFfix ZFfixfun.
Require Import ZFstable ZFiso ZFind_w ZFspos.

(** Inductive families. Indexes are modelled as a constraint over an inductive
    type defined without considering the index values.
 *)

Require ZFind_wnup.
Module W0 := ZFind_wnup.

Section InductiveFamily.

Variable Arg : set.

Record dpositive := mkDPositive {
  dp_oper : (set -> set) -> set -> set;
  w1 : set -> set;
  w2 : set -> set -> set;
  w3 : set -> set -> set -> set;
  dp_iso : set -> set -> set
}.

(*
Definition eqdpos (p1 p2:dpositive) :=
  eqpos p1 p2 /\
  (forall X X' a a', (eq_set==>eq_set)%signature X X' -> a==a' -> dpos_oper p1 X a == dpos_oper p2 X' a') /\
  (forall x x' i i', x==x' -> i==i' -> w3 p1 x i == w3 p2 x' i').
*)
Class isDPositive (p:dpositive) := {
  dopm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) (dp_oper p);
  dpmono : mono_fam Arg (dp_oper p);
  w1m : morph1 (w1 p);
  w2m : morph2 (w2 p);
  w3m : Proper (eq_set==>eq_set==>eq_set==>eq_set) (w3 p);
  w3typ : forall a x i, a ∈ Arg -> x ∈ w1 p a -> i ∈ w2 p a x -> w3 p a x i ∈ Arg;
  dpm : morph2 (dp_iso p);
  dpm_iso : forall a X, a ∈ Arg -> morph1 X -> iso_fun (dp_oper p X a) (W0.W_Fd (w1 p) (w2 p) (w3 p) X a) (dp_iso p a)
}.

Definition dINDi p := TIF Arg (dp_oper p).

Existing Instance dopm.
Existing Instance dpm.
Existing Instance w1m.
Existing Instance w2m.
Existing Instance w3m.
Hint Resolve dpmono.

Lemma dINDi_succ_eq : forall p o a,
  isDPositive p -> isOrd o -> a ∈ Arg -> dINDi p (osucc o) a == dp_oper p (dINDi p o) a.
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

Definition dIND_clos_ord (p:dpositive) := W0.W_ord Arg (w1 p) (w2 p).

Lemma isOrd_clos_ord p : isDPositive p -> isOrd (dIND_clos_ord p).
intros.
unfold dIND_clos_ord.
apply W0.W_o_o; auto with *.
Qed.
Hint Resolve isOrd_clos_ord.

(*
Definition dIND_clos_ord (p:dpositive) a :=
  W0.W_ord (W0.Arg' Arg (w1 p) (w2 p) (w3 p) a)
           (W0.A'' (w1 p) (w3 p) a)
           (W0.B'' (w2 p) (w3 p) a).
*)
Definition dIND (p:dpositive) a := dINDi p (dIND_clos_ord p) a.

Instance dINDi_morph p : morph2 (dINDi p).
do 3 red; intros.
unfold dINDi.
apply TIF_morph; trivial.
Qed.

Instance dIND_morph p : isDPositive p -> morph1 (dIND p).
intros.
do 2 red; intros.
unfold dIND.
apply dINDi_morph; auto with *.
Qed.


Definition WFdmap p f a x :=
  couple (fst x) (λ i ∈ w2 p a (fst x), f (w3 p a (fst x) i) (cc_app (snd x) i)).

Instance WFdmapm : forall p, isDPositive p ->
  Proper ((eq_set==>eq_set==>eq_set)==>eq_set==>eq_set==>eq_set) (WFdmap p).
do 5 red; intros.
unfold WFdmap.
apply couple_morph.
 apply fst_morph; trivial.
apply cc_lam_morph.
 apply w2m; trivial.
 apply fst_morph; trivial.

 red; intros.
 apply H0.
  apply w3m; trivial.
  apply fst_morph; trivial.

  apply cc_app_morph; trivial.
  apply snd_morph; trivial.
Qed.

Let wiso p f a :=
  comp_iso (dp_iso p a) (WFdmap p f a).

Instance wisom : forall p, isDPositive p -> 
 Proper ((eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set ==> eq_set) (wiso p).
do 4 red; intros.
unfold wiso.
unfold comp_iso.
apply WFdmapm; trivial.
apply dpm; trivial.
Qed.

Lemma wiso_iso : forall p X Y f,
  (forall a, a ∈ Arg -> iso_fun (X a) (Y a) (f a)) ->
  forall a, a ∈ Arg ->
   iso_fun (W0.W_Fd (w1 p) (w2 p) (w3 p) X a)
     (W0.W_Fd (w1 p) (w2 p) (w3 p) Y a) (WFdmap p f a).
Admitted.

Lemma wiso_iso' : forall p X Y f,
  isDPositive p ->
  morph1 X ->
  (forall a, a ∈ Arg -> iso_fun (X a) (Y a) (f a)) ->
  forall a, a ∈ Arg ->
  iso_fun (dp_oper p X a) (W0.W_Fd (w1 p) (w2 p) (w3 p) Y a) (wiso p f a).
intros.
unfold wiso.
eapply iso_fun_trans.
 apply dpm_iso; trivial.

 apply wiso_iso; trivial.
Qed.

Lemma wiso_ext p X f f' :
  isDPositive p ->
   morph1 X ->
   morph2 f ->
   morph2 f' ->
   (forall a0 : set, a0 ∈ Arg -> eq_fun (X a0) (f a0) (f' a0)) ->
   forall a0 : set,
   a0 ∈ Arg -> eq_fun (dp_oper p X a0) (wiso p f a0) (wiso p f' a0).
red; intros.
unfold wiso, comp_iso, WFdmap.
apply couple_morph.
 apply fst_morph.
 apply dpm; auto with *.

 apply cc_lam_ext.
  apply w2m; auto with *.
  apply fst_morph.
  apply dpm; auto with *.
 red; intros.
 red in H3.
 assert (eq3: w3 p a0 (fst (dp_iso p a0 x)) x0 == w3 p a0 (fst (dp_iso p a0 x')) x'0).
  apply w3m; auto with *.
  apply fst_morph.
  apply dpm; auto with *.
 rewrite <- eq3.
 assert (ty : dp_iso p a0 x ∈ W0.W_Fd (w1 p) (w2 p) (w3 p) X a0).
  apply dpm_iso; trivial.
 apply H3.
  apply w3typ; trivial.
  apply fst_typ_sigma in ty; trivial.

  eapply snd_typ_sigma in ty;[| |reflexivity].
   apply cc_prod_elim with (1:=ty); trivial.

   do 2 red; intros.
   apply cc_prod_morph.
    apply w2m; auto with *.

    red; intros.
    apply H0.
    apply w3m; auto with *.

   apply cc_app_morph; trivial.
   apply snd_morph.
   apply dpm; auto with *.
Qed.


Lemma dIND_eq : forall p a, isDPositive p -> a ∈ Arg -> dIND p a == dp_oper p (dIND p) a.
intros.
pose (isow := TIF_iso Arg (dp_oper p) (wiso p) (dIND_clos_ord p)).
destruct TIF_iso_fun with (A:=Arg) (F:=dp_oper p) (G:=W0.W_Fd (w1 p) (w2 p) (w3 p)) (g:=wiso p)
  (o:=dIND_clos_ord p) as (isof, expTI); trivial.
  apply dopm.

  apply W0.W_Fd_morph; auto with *.
  auto.

  apply W0.W_Fd_mono; auto with *.
  apply w3typ.

  apply wisom; trivial.

  intros.
  apply wiso_ext; trivial.

  intros.
  apply wiso_iso'; trivial.

  auto.
fold isow in isof,expTI.
eapply iso_fun_inj with (f:=wiso p isow a)
  (Y:=W0.Wi Arg (w1 p) (w2 p) (w3 p) (dIND_clos_ord p) a).
 unfold W0.Wi, dIND.
 unfold dINDi.
 generalize (isof _ H0). 
  assert (isowm : morph2 isow).
   admit.
 apply iso_fun_ext.
  apply wisom; auto with *.

  reflexivity.
  reflexivity.
  red; intros.
(*  assert (wm := wisom _ H).*)
  rewrite <- H2.
  apply expTI; trivial.

 unfold dIND_clos_ord.
 fold (W0.W Arg (w1 p) (w2 p) (w3 p) a).
 apply iso_change_rhs with  (W0.W_Fd  (w1 p) (w2 p) (w3 p) (W0.W Arg (w1 p) (w2 p) (w3 p)) a).
  symmetry; apply W0.W_eqn; auto with *.
  apply w3typ.
 apply wiso_iso'; trivial.
  auto with *.

 unfold dIND, dINDi.
 rewrite <- TIF_mono_succ; auto with *.
 apply TIF_incl; auto with *.
Qed.

Lemma dINDi_dIND : forall p o,
  isDPositive p ->
  isOrd o ->
  forall a, a ∈ Arg ->
  dINDi p o a ⊆ dIND p a.
intros.
unfold dIND, dINDi.
apply TIF_pre_fix; auto with *.
red; intros.
change (dp_oper p (dIND p) a0 ⊆ dIND p a0).
rewrite <- dIND_eq; trivial.
reflexivity.
Qed.

(** Library of dependent positive operators *)

(** Constraint on the index: corresponds to the conclusion of the constructor *)
Require Import ZFcoc.
(*Definition dpos_inst (i:set->set) :=
  mkDPositive (fun a => pos_cst (P2p (i a == a))) (fun _ a => P2p (i a == a))
    (fun a _ _ => a).

(*Lemma isDPos_inst i : morph1 i -> isDPositive (dpos_inst i).
constructor; simpl; intros.
 apply isPos_cst.

 do 4 red; intros.
 rewrite H1; reflexivity.

 do 2 red; intros.
 reflexivity.

 do 4 red; intros; trivial.

 trivial.
Qed.
*)
*)
Definition trad_cst :=
  sigma_1r_iso (fun _ => cc_lam empty (fun _ => empty)).

Lemma iso_cst : forall A X i,
  iso_fun (A i) (W0.W_Fd A (fun _ _ => empty) (fun i _ _ => i) X i) trad_cst.
intros.
unfold trad_cst, W0.W_Fd.
apply sigma_iso_fun_1_r'; intros; auto with *.
 do 2 red; reflexivity.
apply cc_prod_iso_fun_0_l'.
Qed.

Definition dpos_cst A :=
  mkDPositive (fun X i => A i) A (fun i a => empty) (fun i _ _ => i) (fun _ => trad_cst).

Lemma isDPos_cst A : morph1 A -> isDPositive (dpos_cst A).
intros.
constructor; simpl; intros; auto.
 do 3 red; intros; auto.

 do 2 red; intros.
 reflexivity.

 do 3 red; intros; reflexivity.

 do 3 red; auto.

 red; intros; auto.

 do 3 red; intros.
 admit.

 apply iso_cst.
Qed.


Definition dpos_rec j :=
  mkDPositive (fun X i => X (j i)) (fun _ => singl empty) (fun _ _ => singl empty) (fun i _ _ => j i)
    (fun _ => trad_reccall).

Lemma isDPos_rec j : morph1 j ->
  typ_fun j Arg Arg -> isDPositive (dpos_rec j).
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
intros (Fp,Fdm,Fdmo,F3m,F4m,Fty) (Gp,Gdm,Gdmo,G3m,G4m,Gty).
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