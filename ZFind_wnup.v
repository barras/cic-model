Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFord ZFfix ZFstable.
Require Import ZFcoc ZFlist.
Require Import ZFfixfun.
Import ZFrepl.
Existing Instance TIF_morph.

(** A dependent version of ZFind_w: Arg is the type of indexes
   This should support non-uniform parameters.
 *)
Require ZFind_w.
Module W0 := ZFind_w.

Hint Resolve W0.W_F_mono Fmono_morph.

Section W_theory.

(** We want to model the following inductive type with non-uniform parameter a:
[[
Inductive Wd (a:Arg) :=
| C : forall (x:A a), (forall (i:B a x), Wd (f a x i)) -> Wd a.
]]
*)

Variable Arg : set.
Variable A : set -> set.
Variable B : set -> set -> set.
Variable f : set -> set -> set -> set.
Hypothesis Am : morph1 A.
Hypothesis Bm : morph2 B.
Hypothesis fm : Proper (eq_set==>eq_set==>eq_set==>eq_set) f.
Hypothesis ftyp : forall a x y,
  a ∈ Arg ->
  x ∈ A a ->
  y ∈ B a x ->
  f a x y ∈ Arg.


(** The intended type operator: parameter is not part of the data-structure *)

Definition W_Fd (X:set->set) a :=
  sigma (A a) (fun x => cc_prod (B a x) (fun y => X (f a x y))).

Definition Wi o a := TIF Arg W_Fd o a.

Instance Wi_morph : morph2 Wi.
unfold Wi; apply TIF_morph.
Qed.

Instance W_Fd_morph : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) W_Fd.
unfold W_Fd; do 3 red; intros.
apply sigma_morph; auto.
red; intros.
apply cc_prod_morph.
 apply Bm; auto.

 red; intros; apply H; apply fm; trivial.
Qed.


Lemma W_Fd_mono : mono_fam Arg W_Fd.
do 2 red; intros.
unfold W_Fd.
apply sigma_mono; intros; auto with *.
 do 2 red; intros; apply cc_prod_morph;[apply Bm|red; intros;apply H; apply fm]; auto with *.
 do 2 red; intros; apply cc_prod_morph;[apply Bm|red; intros;apply H0; apply fm]; auto with *.

 apply cc_prod_covariant; auto with *.
  do 2 red; intros; apply H0; apply fm; auto with *.

  apply Bm; auto with *.

  intros.
  rewrite <- H4.
  auto.
Qed.
Hint Resolve W_Fd_mono.

Lemma W_Fd_eta w X a :
  morph1 X ->
  w ∈ W_Fd X a ->
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

   red; intros; apply H; apply fm; auto with *.
Qed.

Lemma W_Fd_intro X x x' a a' g :
  morph1 X ->
  a ∈ Arg ->
  a == a' ->
  x ∈ A a' ->
  x == x' ->
  ext_fun (B a x') g ->
  (forall i, i ∈ B a x' -> g i ∈ X (f a x' i)) ->
  couple x (cc_lam (B a x') g) ∈ W_Fd X a'.
intros.
apply couple_intro_sigma; trivial.
 do 2 red; intros.
 apply cc_prod_ext.
  apply Bm; auto with *.

  red; intros.
  apply H; apply fm; auto with *.

 apply cc_prod_intro'; intros; auto.
  do 2 red; intros; apply H; apply fm; auto with *.
  apply Bm; auto with *.
  rewrite <- H1; rewrite H3; auto.
Qed.


(**************************************************)

(** The intermediate W-type: the parameter is turned into a constructor argument that
    we later on constrain (like indexes of inductive families)
    Arg appears in the data, so if it is big, the resulting inductive type is big.
 *)

Definition A' := sigma Arg A.
Definition B' a' := B (fst a') (snd a').
Instance B'_morph : morph1 B'.
do 2 red; intros; apply Bm; [apply fst_morph|apply snd_morph]; trivial.
Qed.

Lemma B'ext : ext_fun A' B'.
auto with *.
Qed.
Hint Resolve B'ext.

Lemma A'_intro a x :
  a ∈ Arg ->
  x ∈ A a ->
  couple a x ∈ A'.
intros; apply couple_intro_sigma; auto.
Qed.

Lemma A'_elim x :
  x ∈ A' -> fst x ∈ Arg /\ snd x ∈ A (fst x) /\ x == couple (fst x) (snd x).
intros.
assert (eqx := surj_pair _ _ _ (subset_elim1 _ _ _ H)).
specialize fst_typ_sigma with (1:=H); intros.
apply snd_typ_sigma with (y:=fst x) in H; auto with *.
Qed.

(** [instance a w] means tree [w] corresponds to the member of the family with
    index value [a]:
    - the Arg component of A' must be [a]
    - the condition is hereditary
 *)
Inductive instance a w : Prop :=
| I_node :
    a == fst (fst w) ->
    (forall i, i ∈ B' (fst w) -> instance (f a (snd (fst w)) i) (cc_app (snd w) i)) ->
    instance a w.

Instance instance_morph : Proper (eq_set==>eq_set==>iff) instance.
apply morph_impl_iff2; auto with *.
do 4 red; intros.
revert y y0 H H0.
induction H1; intros.
constructor; intros.
 rewrite <- H3; rewrite <- H2; trivial.

 apply H1 with i.
  rewrite H3; trivial.
  rewrite H3; rewrite H2; reflexivity.
  rewrite H3; reflexivity.
Qed.

(** We show there is an iso between the intended type (Wi)
   and the encoding (W0.W A' B'):
   tr (f:X->Y) : W0.W_F A' B' X --> U_a (W_Fd (A a) (B a) Y) 
   See also more refined result below.
 *)
Definition tr f w :=
  couple (snd (fst w)) (cc_lam (B'(fst w)) (fun i => f (cc_app (snd w) i))).

Instance tr_morph : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) tr.
do 3 red; intros.
unfold tr.
apply couple_morph.
 rewrite H0; reflexivity.

 apply cc_lam_morph.
  rewrite H0; reflexivity.

  red; intros.
  apply H; rewrite H0; rewrite H1; reflexivity.
Qed.

Let tr_cont o z :
 isOrd o ->
 (z ∈ TI (W0.W_F A' B') o <->
  (exists2 o', o' ∈ o & z ∈ TI (W0.W_F A' B') (osucc o'))).
intros.
rewrite TI_mono_eq; auto.
rewrite sup_ax; auto with *.
do 2 red; intros; apply TI_morph.
rewrite H1; reflexivity.
Qed.

Let tr_ext o g g' :
 isOrd o ->
 eq_fun (TI (W0.W_F A' B') o) g g' ->
 eq_fun (TI (W0.W_F A' B') (osucc o)) (tr g) (tr g').
red; intros.
unfold tr.
apply couple_morph.
 rewrite H2; reflexivity.

 unfold B'; apply cc_lam_ext.
  rewrite H2; reflexivity.

  red; intros.
  apply H0.
   rewrite TI_mono_succ in H1; auto.
   apply W0.W_F_elim in H1; auto.
   destruct H1 as (_,(?,_)); auto.

   rewrite H2; rewrite H4; reflexivity.
Qed.

Require Import ZFiso.

(** Isomorphism result for the step function.
    - the parameter constraint on subterms (of type X) is modelled by P *)
Lemma tr_iso a X Y P g :
  Proper (eq_set==>eq_set==>iff) P ->
  morph1 Y ->
  a ∈ Arg ->
  (forall a, a ∈ Arg -> iso_fun (subset X (P a)) (Y a) g) ->
  let Wd := subset (W0.W_F A' B' X)
     (fun w => fst (fst w) == a /\
        forall i, i ∈ B a (snd (fst w)) -> P (f a (snd (fst w)) i) (cc_app (snd w) i)) in
  iso_fun Wd (W_Fd Y a) (tr g).
intros Pm; intros.
unfold tr.
assert (gm : forall x x', x ∈ Wd -> x == x' ->
             eq_fun (B' (fst x)) (fun i => g (cc_app (snd x) i)) (fun i => g (cc_app (snd x') i))).
 do 2 red; intros.
 unfold Wd in H2; rewrite subset_ax in H2; destruct H2 as (?,(w,?,(?,?))).
 apply W0.W_F_elim in H2; auto.
 destruct H2 as (?,(?,_)).
 apply A'_elim in H2; destruct H2 as (?,(?,_)).
 apply (iso_funm (H1 _ (ftyp _ _ _ H2 H10 H4))).
  apply subset_intro; auto.
  unfold B' in H4; rewrite H6 in H4|-*; rewrite H7 in H4|-*; auto.

  rewrite H3; rewrite H5; reflexivity.
constructor; intros.
 do 2 red; intros.
 unfold B'.
 assert (h:=H2); unfold Wd in h;
   rewrite subset_ax in h; destruct h as (?,(w,eqx,(?,?))).
 apply W0.W_F_elim in H4; auto.
 destruct H4 as (?,(?,_)).
 apply A'_elim in H4; destruct H4 as (?,(?,_)).
 apply couple_morph.
  rewrite H3; reflexivity.

  apply cc_lam_ext.
   rewrite H3; reflexivity.

   apply gm; trivial.

 (* typ *)
 red; intros.
 assert (h:=H2); unfold Wd in h; rewrite subset_ax in h; destruct h.
 destruct H4 as (x0,eqx0,(inst,insts)); rewrite <- eqx0 in inst.
 apply W0.W_F_elim in H3; auto.
 destruct H3 as (ty1,(ty2,eqx)).
 apply A'_elim in ty1; destruct ty1 as (tya,(tyx,eqy)).
 apply W_Fd_intro; intros; auto with *.
  rewrite <- inst; trivial.

  apply gm; auto with *.

  specialize ty2 with (1:=H2).
  apply (iso_typ (H1 _ (ftyp _ _ _ tya tyx H3))).
  apply subset_intro; auto.
  rewrite inst in H3,tyx|-*.
  rewrite eqx0.
  apply insts; rewrite <- eqx0; auto.

 (* inj *)
 assert (h:=H2); unfold Wd in h; rewrite subset_ax in h; destruct h.
 destruct H6 as (x0,eqx0,(inst,insts)); rewrite <- eqx0 in inst.
 apply W0.W_F_elim in H5; auto.
 destruct H5 as (ty1,(ty2,eqx)).
 assert (h:=H3); unfold Wd in h; rewrite subset_ax in h; destruct h.
 destruct H6 as (x1,eqx1,(inst',insts')); rewrite <- eqx1 in inst'.
 apply W0.W_F_elim in H5; auto.
 destruct H5 as (ty1',(ty2',eqx')).
 rewrite eqx; rewrite eqx'.
 assert (h:=ty1); apply A'_elim in h; destruct h as (tya,(tyx,eqy)).
 assert (h:=ty1'); apply A'_elim in h; destruct h as (tya',(tyx',eqy')).
 apply W0.WFi_inv in H4; intros.
  destruct H4.
  apply W0.WFi_ext with A'; intros; auto with *.
   rewrite eqy; rewrite eqy'.
   rewrite inst; rewrite inst'; rewrite H4; reflexivity.

   red; intros.
   generalize (H5 _ _ H7 H8); intro.
   unfold B' in H7; rewrite inst in tyx,H7.
   apply (iso_inj (H1 _ (ftyp _ _ _ H0 tyx H7))) in H9; auto.
    apply subset_intro; auto.
     rewrite <- inst in H7; auto.
    rewrite eqx0.
    apply insts; rewrite <- eqx0; auto.

    apply subset_intro; auto.
     rewrite H6 in H7.
     rewrite H8 in H7.
     rewrite <- inst' in H7; auto.
    rewrite H6 in H7|-*; rewrite eqx1 in H7|-*; rewrite <- H8; apply insts'; auto.

   apply gm; auto with *.
   apply gm; auto with *.

  rewrite eqy; rewrite eqy'.
  rewrite inst; rewrite inst'; rewrite H5; reflexivity.

 (* surj *)
 specialize fst_typ_sigma with (1:=H2); intros ty1.
 assert (eqy := surj_pair _ _ _ (subset_elim1 _ _ _ H2)).
 apply snd_typ_sigma with (y:=fst y) in H2; auto with *.
Focus 2.
do 2 red; intros; apply cc_prod_morph.
 rewrite H4; reflexivity.
 red; intros.
 rewrite H4; rewrite H5; reflexivity.

 assert (bm : ext_fun (B' (couple a (fst y)))
    (fun i => iso_inv (subset X (P (f a (fst y) i))) g (cc_app (snd y) i))).
  do 2 red; intros.
  apply iso_inv_ext.
   apply subset_morph; auto with *.
   red; intros; rewrite H4; reflexivity.

   apply H1; apply ftyp; trivial.
   unfold B' in H3; rewrite fst_def in H3; rewrite snd_def in H3; trivial.

   rewrite H4; reflexivity.
 exists (couple (couple a (fst y)) (cc_lam (B' (couple a (fst y)))
    (fun i => iso_inv (subset X (P (f a (fst y) i))) g (cc_app (snd y) i)))).
  apply subset_intro.
   apply W0.W_F_intro; intros; auto with *.
    apply A'_intro; auto.

    unfold B' in H3; rewrite fst_def in H3; rewrite snd_def in H3.
    apply cc_prod_elim with (2:=H3) in H2.
    apply iso_inv_typ with (1:=H1 _ (ftyp _ _ _ H0 ty1 H3)) in H2.
    apply subset_elim1 in H2; trivial.

   split; intros.
    rewrite fst_def; rewrite fst_def; reflexivity.

    rewrite fst_def in H3|-*.
    rewrite snd_def in H3|-*.
    rewrite snd_def.
    rewrite cc_beta_eq; trivial.
     apply cc_prod_elim with (2:=H3) in H2.
     apply iso_inv_typ with (1:=H1 _ (ftyp _ _ _ H0 ty1 H3)) in H2.
     apply subset_elim2 in H2; destruct H2.
     rewrite <- H2 in H4; auto.

     unfold B'; rewrite fst_def; rewrite snd_def; trivial.     

  apply transitivity with (2:=symmetry eqy).
  apply couple_morph.
   rewrite fst_def; rewrite snd_def; reflexivity.

   rewrite cc_eta_eq with (1:=H2).
   symmetry.
   apply cc_lam_ext.
    unfold B'; rewrite fst_def.
    rewrite fst_def; rewrite snd_def; reflexivity.

    red; intros.
    assert (cc_app (snd y) x ∈ Y (f a (fst y) x)).
     apply cc_prod_elim with (1:=H2); trivial.
    transitivity (g (iso_inv (subset X (P(f a(fst y) x'))) g (cc_app (snd y) x'))).
     rewrite H4 in H3,H5|-*.
     rewrite iso_inv_eq with (1:=H1 _ (ftyp _ _ _ H0 ty1 H3)); auto with *.

     rewrite H4 in H3.
     apply (iso_funm (H1 _ (ftyp _ _ _ H0 ty1 H3))).
      apply iso_inv_typ with (1:=H1 _ (ftyp _ _ _ H0 ty1 H3)).
      rewrite <- H4; trivial.

      rewrite snd_def.
      rewrite cc_beta_eq; auto with *.

      unfold B'; rewrite fst_def; rewrite snd_def; trivial.
Qed.

Require Import ZFlimit.

Lemma tr_iso_it a o :
  isOrd o ->
  a ∈ Arg ->
  iso_fun (subset (TI (W0.W_F A' B') o) (instance a))
          (TIF Arg W_Fd o a) (TRF tr o).
intros oo; revert a; elim oo using isOrd_ind; intros.
constructor; intros.
 do 2 red; intros.
 unfold TRF; apply TRF_morph; auto with *.

 red; intros.
 rewrite subset_ax in H3; destruct H3.
 destruct H4 as (x',eqx,inst); rewrite <- eqx in inst; clear x' eqx.
 apply TI_elim in H3; auto.
 destruct H3 as (o', ?,?).
 rewrite TRF_indep with (T:=TI(W0.W_F A' B')) (o':=o'); intros; auto with *.
  apply TIF_intro with o'; auto with *.
  assert (h:=H1 _ H3); apply tr_iso with (a:=a) in h; auto with *.
  apply (iso_typ h).
  apply subset_intro; trivial.
  destruct inst; split; intros; auto with *.
  apply H6.
  unfold B'; rewrite <- H5; trivial.

  rewrite TI_mono_succ; auto with *.
  apply isOrd_inv with y; auto.

 rewrite subset_ax in H3; destruct H3.
 destruct H6.
 rewrite subset_ax in H4; destruct H4.
 destruct H8.
 apply TI_elim in H3; auto.
 destruct H3.
 apply TI_elim in H4; auto.
 destruct H4.
 assert (x2 ⊔ x3 ∈ y).
  apply osup2_lt; auto.
 assert (h:=H1 _ H12); apply tr_iso with (a:=a) in h; auto with *.
 rewrite TRF_indep with (T:=TI(W0.W_F A' B'))(o':=x2 ⊔ x3) in H5; intros; auto with *.
  rewrite TRF_indep with (T:=TI(W0.W_F A' B'))(o':=x2 ⊔ x3) in H5; intros; auto with *.
   apply (iso_inj h) in H5; trivial.
    apply subset_intro.
     revert H10; apply W0.W_F_mono; auto with *.
     apply TI_mono; auto with *.
      apply isOrd_osup2; eauto using isOrd_inv.
      eauto using isOrd_inv.
      apply osup2_incl1; eauto using isOrd_inv.

     rewrite <- H6 in H7; destruct H7; split; auto with *.
     intros.
     apply H13; unfold B'; rewrite <- H7; trivial.

    apply subset_intro.
     revert H11; apply W0.W_F_mono; auto with *.
     apply TI_mono; auto with *.
      apply isOrd_osup2; eauto using isOrd_inv.
      eauto using isOrd_inv.
      apply osup2_incl2; eauto using isOrd_inv.

     rewrite <- H8 in H9; destruct H9; split; auto with *.
     intros.
     apply H13; unfold B'; rewrite <- H9; trivial.

   rewrite TI_mono_succ; eauto using isOrd_inv.
   revert H11; apply W0.W_F_mono; auto.
   apply TI_mono; auto with *.
    apply isOrd_osup2; eauto using isOrd_inv.
    eauto using isOrd_inv.
    apply osup2_incl2; eauto using isOrd_inv.

  rewrite TI_mono_succ; eauto using isOrd_inv.
  revert H10; apply W0.W_F_mono; auto.
  apply TI_mono; auto with *.
   apply isOrd_osup2; eauto using isOrd_inv.
   eauto using isOrd_inv.
   apply osup2_incl1; eauto using isOrd_inv.

 (* surj *)
 apply TIF_elim in H3; auto with *.
 destruct H3.
 assert (h:=H1 _ H3); apply tr_iso with (a:=a) in h; auto with *.
 destruct (iso_surj h) with y0; trivial.
 rewrite subset_ax in H5; destruct H5.
 destruct H7.
 destruct H8.
 exists x0.
  apply subset_intro.
   apply TI_intro with x; auto.

   constructor; intros.
    rewrite H7; auto with *.

    rewrite H7.
    apply H9.
    unfold B' in H10; rewrite H7 in H10; rewrite H8 in H10; trivial.

  rewrite TRF_indep with (T:=TI(W0.W_F A' B')) (o':=x); auto with *.
  rewrite TI_mono_succ; auto.
  apply isOrd_inv with y; trivial.
Qed.

(** * Fixpoint *)

Definition W_ord := W0.W_ord A' B'.

Lemma W_o_o : isOrd W_ord.
apply W0.W_o_o; trivial.
Qed.
Hint Resolve W_o_o.

Definition W := Wi W_ord.

Lemma W_eqn a : a ∈ Arg -> W a == W_Fd W a.
unfold W,Wi; intros.
rewrite <- TIF_mono_succ; auto with *.
apply eq_intro; intros.
 revert H0; apply TIF_incl; auto with *.

 destruct (iso_surj (tr_iso_it _ _ (isOrd_succ _ W_o_o) H)) with z; trivial.
 rewrite subset_ax in H1; destruct H1.
 destruct H3.
 rewrite <- H3 in H4; clear x0 H3.
 rewrite TI_mono_succ in H1; auto.
 unfold W_ord in H1; fold (W0.W A' B') in H1.
 rewrite <- W0.W_eqn in H1; trivial.
 rewrite <- H2.
 apply in_reg with (TRF tr W_ord x).
  apply TI_elim in H1; auto with *.
  destruct H1.
  rewrite TRF_indep with (T:=TI(W0.W_F A' B')) (o':=x0); auto with *.
   rewrite TRF_indep with (T:=TI(W0.W_F A' B')) (o':=x0); auto with *.
    apply isOrd_trans with W_ord; auto.

    rewrite TI_mono_succ; eauto using isOrd_inv.

   rewrite TI_mono_succ; eauto using isOrd_inv.

 apply (iso_typ (tr_iso_it _ _ W_o_o H)).  
 apply subset_intro; trivial.
Qed.

Lemma W_post o :
  isOrd o -> 
  incl_fam Arg (Wi o) W.
intros oo; elim oo using isOrd_ind; intros.
red; red; intros.
apply TIF_elim in H3; auto with *.
destruct H3.
specialize H1 with (1:=H3).
apply W_Fd_mono in H1.
2:apply TIF_morph; reflexivity.
2:apply TIF_morph; reflexivity.
apply H1 in H4; trivial.
rewrite W_eqn; trivial.
Qed.

(** * Universe facts *)

Require Import ZFgrothendieck.

Section W_Univ.

  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : omega ∈ U.  

  (** The size of Arg matters: *)
  Hypothesis ArgU : Arg ∈ U.
  Hypothesis aU : forall a, a ∈ Arg -> A a ∈ U.
  Hypothesis bU : forall a x, a ∈ Arg -> x ∈ A a -> B a x ∈ U.

  Lemma G_W_Fd X :
    morph1 X ->
    (forall a, a ∈ Arg -> X a ∈ U) ->
    forall a, a ∈ Arg -> W_Fd X a ∈ U.
unfold W_Fd; intros.
apply G_sigma; intros; auto.
 do 2 red; intros.
 apply cc_prod_ext.
  rewrite H3; reflexivity.

  red; intros.
  rewrite H3; rewrite H5; reflexivity.

 apply G_cc_prod; intros; auto.
 do 2 red; intros.
 rewrite H4; reflexivity.
Qed.

  Lemma G_Wi o a : isOrd o -> o ∈ U -> a ∈ Arg -> Wi o a ∈ U.
unfold Wi.
unfold TIF; intros.
apply G_cc_app; trivial.
2:apply G_trans with Arg; trivial.
apply G_TR; trivial.
 do 3 red; intros.
 apply cc_lam_morph; auto with *.
 red; intros.
 apply sup_morph; trivial.
 red; intros.
 apply W_Fd_morph; trivial.
 red; intros.
 apply cc_app_morph; auto.

 intros.
 apply cc_lam_morph; auto with *; red; intros.
 apply sup_morph; auto with *.
 red; intros.
 apply W_Fd_morph; auto with *.
 apply cc_app_morph; auto with *.

 intros.
 apply G_cc_lam; trivial; intros.
  do 2 red; intros; apply sup_morph; auto with *.
  red; intros.
  apply W_Fd_morph; auto with *.
  apply cc_app_morph; auto with *.

  apply G_sup; trivial.
   do 2 red; intros.
   apply W_Fd_morph; auto with *.
   apply cc_app_morph; auto with *.

   intros.
   apply G_W_Fd; intros; auto.
    apply cc_app_morph; reflexivity.

    apply G_cc_app; auto.
    apply G_trans with Arg; trivial.
Qed.

  Lemma G_W_ord : W_ord ∈ U.
apply W0.G_W_ord; trivial.
 apply G_sigma; trivial.
 do 2 red; intros; apply Am; trivial.

 intros.
 apply bU.
  apply fst_typ_sigma in H; trivial.

  apply snd_typ_sigma with (y:=fst a) in H; auto with *.
Qed.

  Lemma G_W a : a ∈ Arg -> W a ∈ U.
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
apply ZFord.TR_morph; trivial.
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

(** * Morphism between two instances of W-types
 *)
Section W_Simulation.

Variable Arg : set.
Variable A : set -> set.
Variable B : set -> set -> set.
Variable f : set -> set -> set -> set.
Hypothesis Am : morph1 A.
Hypothesis Bm : morph2 B.
Hypothesis fm : Proper (eq_set==>eq_set==>eq_set==>eq_set) f.
Hypothesis ftyp : forall a x y,
  a ∈ Arg ->
  x ∈ A a ->
  y ∈ B a x ->
  f a x y ∈ Arg.

Variable Arg' : set.
Variable A' : set -> set.
Variable B' : set -> set -> set.
Variable f' : set -> set -> set -> set.
Hypothesis Am' : morph1 A'.
Hypothesis Bm' : morph2 B'.
Hypothesis fm' : Proper (eq_set==>eq_set==>eq_set==>eq_set) f'.
Hypothesis ftyp' : forall a x y,
  a ∈ Arg' ->
  x ∈ A' a ->
  y ∈ B' a x ->
  f' a x y ∈ Arg'.

Lemma W_simul g p p' o o':
  morph1 g ->
  (forall p, p ∈ Arg -> g p ∈ Arg') ->
  (forall p, p ∈ Arg -> A p == A' (g p)) ->
  (forall p a, p ∈ Arg -> a ∈ A p -> B p a == B' (g p) a) ->
  (forall p a b, p ∈ Arg -> a ∈ A p -> b ∈ B p a ->
   g (f p a b) == f' (g p) a b) ->
  isOrd o ->
  p ∈ Arg ->
  g p == p' ->
  o == o' ->
  Wi Arg A B f o p == Wi Arg' A' B' f' o' p'.
intros.
transitivity (Wi Arg' A' B' f' o p').
 2:apply Wi_morph_all; auto with *.
clear o' H7.
revert p p' H5 H6; apply isOrd_ind with (2:=H4); intros.
clear o H4 H6; rename y into o.
assert (forall o', lt o' o ->
  W_Fd A B f (TIF Arg (W_Fd A B f) o') p ==
  W_Fd A' B' f' (TIF Arg' (W_Fd A' B' f') o') p').
 intros.
 unfold W_Fd.
 apply sigma_ext; intros; auto.
  rewrite <- H9; auto.

  apply cc_prod_ext; intros.
   rewrite <- H9; rewrite <- H10; auto.

   red; intros. 
   apply H7; trivial.
    apply ftyp; auto.

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

(** Support for definitions by case *)
(* --> ? *)
Definition if_prop P x y :=
  cond_set P x ∪ cond_set (~P) y.

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


(** * Waiving the universe constraint on Arg: *)

Section BigParameter.

Variable Arg : set.
Variable A : set -> set.
Variable B : set -> set -> set.
Variable f : set -> set -> set -> set.
Hypothesis Am : morph1 A.
Hypothesis Bm : morph2 B.
Hypothesis fm : Proper (eq_set==>eq_set==>eq_set==>eq_set) f.
Hypothesis ftyp : forall a x y,
  a ∈ Arg ->
  x ∈ A a ->
  y ∈ B a x ->
  f a x y ∈ Arg.

(** Encoding big parameters as (small) paths from a fixed parameter [a].
    First, the type operator. *)
Let L X a :=
  singl empty ∪ sigma (A a) (fun x => sigma (B a x) (fun y => X (f a x y))).


Instance Lmorph : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) L.
do 3 red; intros.
apply union2_morph;[reflexivity|].
apply sigma_morph; auto.
red; intros.
apply sigma_morph.
 apply Bm; auto.

 red; intros.
 apply H; apply fm; trivial.
Qed.
Hint Resolve Lmorph.

Lemma L_intro1 X a : empty ∈ L X a.
apply union2_intro1.
apply singl_intro.
Qed.

Lemma L_intro2 a x y q X :
  morph1 X ->
  a ∈ Arg ->
  x ∈ A a ->
  y ∈ B a x ->
  q ∈ X (f a x y) ->
  couple x (couple y q) ∈ L X a.
unfold L; intros.
apply union2_intro2.
apply couple_intro_sigma; trivial.
 do 2 red; intros; apply sigma_morph.
  apply Bm; auto with *.

  red; intros; apply H; apply fm; auto with *.

 apply couple_intro_sigma; trivial.
 do 2 red; intros; apply H; apply fm; auto with *.
Qed.

Definition L_match q f g :=
  if_prop (q==empty) f (g (fst q) (fst (snd q)) (snd (snd q))).

Lemma L_elim a q X :
  morph1 X ->
  a ∈ Arg ->
  q ∈ L X a ->
  q == empty \/
  exists2 x, x ∈ A a &
  exists2 y, y ∈ B a x &
  exists2 q', q' ∈ X (f a x y) &
  q == couple x (couple y q').
intros.
destruct union2_elim with (1:=H1);[left|right].
 apply singl_elim in H2; trivial.

 clear H1.
 assert (fst q ∈ A a).
  apply fst_typ_sigma in H2; auto.
 exists (fst q); trivial.
 assert (q == couple (fst q) (snd q)).
  apply surj_pair with (1:=subset_elim1 _ _ _ H2).
 apply snd_typ_sigma with (y:=fst q) in H2; auto with *.
  2:do 2 red; intros; apply sigma_morph.
  2: apply Bm; auto with *.
  2: red; intros; apply H; apply fm; auto with *.
 assert (fst (snd q) ∈ B a (fst q)).
  apply fst_typ_sigma in  H2; trivial.
 exists (fst (snd q)); trivial.
 exists (snd (snd q)).
  apply snd_typ_sigma with (y:=fst (snd q)) in H2; auto with *.
  do 2 red; intros; apply H; apply fm; auto with *.

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
 apply ftyp; auto.
Qed.
Hint Resolve Lmono.

(** The fixpoint: paths
    Arg' a == 1 + { x : A a ; y : B a x ; l : Arg' (f a x y) } *)
Definition Arg' : set -> set := TIF Arg L omega.

Instance Arg'_morph : morph1 Arg'.
apply TIF_morph; reflexivity.
Qed.

Lemma Arg'_ind P :
  Proper (eq_set ==> eq_set ==> iff) P ->
  (forall a, a∈ Arg -> P a empty) ->
  (forall a x y q,
   a ∈ Arg ->
   x ∈ A a ->
   y ∈ B a x ->
   q ∈ Arg' (f a x y) ->
   P (f a x y) q ->
   P a (couple x (couple y q))) ->
  forall a q,
  a ∈ Arg -> 
  q ∈ Arg' a ->
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
  apply ftyp; trivial.
Qed.

Lemma Arg'_eqn a :
  a ∈ Arg ->
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
  a ∈ Arg ->
  empty ∈ Arg' a.
intros.
rewrite Arg'_eqn; trivial.
apply L_intro1.
Qed.

Lemma Arg'_intro2 a x y q :
  a ∈ Arg ->
  x ∈ A a ->
  y ∈ B a x ->
  q ∈ Arg' (f a x y) ->
  couple x (couple y q) ∈ Arg' a.
intros.
rewrite Arg'_eqn; trivial.
apply L_intro2; trivial with *.
Qed.

Require Import ZFfixrec.

Section Arg'_recursor.

Variable g : set -> set.
Variable h : set -> set -> set -> (set -> set) -> set -> set.
Hypothesis gm : morph1 g.
Hypothesis hm :
  Proper (eq_set==>eq_set==>eq_set==>(eq_set==>eq_set)==>eq_set==>eq_set) h.
Definition Arg'_rec_rel q f' :=
  forall P,
  Proper (eq_set==>(eq_set==>eq_set)==>iff) P ->
  P empty g ->
  (forall x y q' f',
   morph1 f' ->
   P q' f' ->
   P (couple x (couple y q')) (h x y q' f')) ->
  P q f'.

Instance Arg'_rec_rel_morph : Proper (eq_set==>(eq_set==>eq_set)==>iff) Arg'_rec_rel.
apply morph_impl_iff2; auto with *.
do 5 red; intros.
cut (P x x0).
 apply H2; symmetry; trivial.
apply H1; trivial.
Qed.

Lemma Arg'_case q0 f' :
  Arg'_rec_rel q0 f' ->
  Arg'_rec_rel q0 f' /\
  (q0 == empty -> (eq_set==>eq_set)%signature f' g) /\
  forall x y q,
  q0 == couple x (couple y q) ->
  exists2 h', morph1 h' &
  Arg'_rec_rel q h' /\ (eq_set==>eq_set)%signature f' (h x y q h').
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

  exists f'0; trivial.
  apply couple_injection in H4; destruct H4. 
  apply couple_injection in H5; destruct H5. 
  split; trivial.
   rewrite <- H6; trivial.

   apply hm; trivial.
Qed.
 

Lemma Arg'_uniq q f1 q' f1':
  Arg'_rec_rel q f1 ->
  Arg'_rec_rel q' f1' ->
  q == q' -> (eq_set==>eq_set)%signature f1 f1'.
intros qrel.
revert q' f1'.
apply qrel; intros.
 do 3 red; intros.
 apply fa_morph; intros q'.
 apply fa_morph; intros f1'.
 rewrite H.
 apply fa_morph; intros _.
 apply fa_morph; intros _.
 split; intros.
  rewrite <- H0; trivial.
  rewrite H0; trivial.

 apply Arg'_case in H.
 destruct H as (_,(?,_)).
 symmetry in H0|-*; auto.

 apply Arg'_case in H1.
 destruct H1 as (H1,(_,?)).
 destruct H3 with x y q'; auto with *.
 destruct H5.
 rewrite H6.
 apply hm; auto with *.
 apply H0 with q'; auto with *.
Qed.

Lemma Arg'_ex a q :
  a ∈ Arg ->
  q ∈ Arg' a ->
  exists2 f', morph1 f' & Arg'_rec_rel q f'.
intros.
pattern a, q; apply Arg'_ind with (5:=H0); intros; trivial.
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 destruct H3.
 exists x1; trivial.
 rewrite <- H2; trivial.

 exists g; auto.
 red; auto.

 destruct H5.
 exists (h x y q0 x0).
  apply hm; auto with *.

  red; intros.
  apply H9; trivial.
  apply H6; trivial.
Qed.

Definition Arg'_rec q x :=
  uchoice (fun y => exists2 f', morph1 f' & Arg'_rec_rel q f' /\ y == f' x).

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
  a ∈ Arg ->
  q ∈ Arg' a ->
  uchoice_pred (fun y => exists2 f', morph1 f' & Arg'_rec_rel q f' /\ y == f' x).
intros.
split;[|split]; intros.
 destruct H2 as (f',?,(?,?)).
 exists f'; trivial.
 split; trivial.
 rewrite <- H1; trivial.

 destruct Arg'_ex with (2:=H0); trivial.
 exists (x0 x); exists x0; auto with *.

 destruct H1 as (f1,?,(?,?)); destruct H2 as (f1',?,(?,?)).
 specialize Arg'_uniq with (1:=H3) (2:=H5); intro.
 rewrite H4; rewrite H6; apply H7; auto with *.
Qed.

Lemma Arg'_def a q :
  a ∈ Arg ->
  q ∈ Arg' a ->
  Arg'_rec_rel q (Arg'_rec q).
intros.
generalize
 (fun x => uchoice_def _ (uchoice_Arg'_rec a q x H H0)); intro.
destruct Arg'_ex with (2:=H0); trivial.
generalize H3; apply Arg'_rec_rel_morph; auto with *.
red; intros.
destruct (H1 x0) as (f',?,(?,?)).
transitivity (f' y).
 rewrite <- H4; trivial.

 apply Arg'_uniq with (1:=H6)(2:=H3); reflexivity.
Qed.


Lemma Arg'_rec_mt a x :
  a ∈ Arg ->
  Arg'_rec empty x == g x.
intros.
destruct (uchoice_def _ (uchoice_Arg'_rec a empty x H (Arg'_intro1 _ H)))
 as (f',?,(?,?)).
transitivity (f' x); trivial.
apply Arg'_uniq with empty empty; auto with *.
red; auto.
Qed.

Lemma Arg'_rec_cons a x y q z :
  a ∈ Arg ->
  x ∈ A a ->
  y ∈ B a x ->
  q ∈ Arg' (f a x y) ->
  Arg'_rec (couple x (couple y q)) z == h x y q (Arg'_rec q) z.
intros.
specialize Arg'_def with (1:=H) (2:=Arg'_intro2 _ _ _ _ H H0 H1 H2); intro.
apply Arg'_case in H3.
destruct H3 as (?,(_,?)).
destruct (H4 x y q); auto with *.
clear H4; destruct H6.
rewrite (H6 z z); auto with *.
apply hm; auto with *.
apply Arg'_uniq with (1:=H4)(q':=q); auto with *.
apply Arg'_def with (f a x y); trivial.
apply ftyp; auto.
Qed.


End Arg'_recursor.

(** Decoding paths as a parameter value *)
Definition Dec a q :=
  Arg'_rec (fun a => a) (fun x y q' F a => F (f a x y)) q a.


Lemma Dec_mt a : a ∈ Arg -> Dec a empty == a.
unfold Dec; intros.
rewrite Arg'_rec_mt with (a:=a); auto with *.
 do 2 red; auto.

 do 6 red; intros.
 apply H3.
 apply fm; trivial.
Qed.

Lemma Dec_cons a x y q :
  a ∈ Arg ->
  x ∈ A a ->
  y ∈ B a x ->
  q ∈ Arg' (f a x y) ->
  Dec a (couple x (couple y q)) == Dec (f a x y) q.
intros.
unfold Dec.
apply Arg'_rec_cons with (a:=a); trivial.
 do 2 red; auto.

 do 6 red; intros.
 apply H6.
 apply fm; trivial.
Qed.


Instance Dec_morph : morph2 Dec.
unfold Dec; do 3 red; intros.
apply Arg'_rec_morph; trivial.
Qed.


Lemma Dec_typ a q :
  a ∈ Arg ->
  q ∈ Arg' a ->
  Dec a q ∈ Arg.
intros.
apply Arg'_ind with (5:=H0); intros; auto with *.
 do 3 red; intros.
 rewrite H1; rewrite H2; reflexivity.

 rewrite Dec_mt; auto.

 rewrite Dec_cons; auto.
Qed.

(** Extending a path *)
Definition extln q x y :=
  Arg'_rec (fun _ => couple x (couple y empty))
    (fun x' y' q' F z => couple x' (couple y' (F z))) q empty.

Instance extln_morph : Proper (eq_set==>eq_set==>eq_set==>eq_set) extln.
do 4 red; intros.
unfold extln.
unfold Arg'_rec.
apply uchoice_morph_raw.
red; intros.
apply ex2_morph'; intros; auto with *.
unfold Arg'_rec_rel.
apply and_iff_morphism.
 apply fa_morph; intros P.
 apply fa_morph; intros Pm.
 apply impl_morph.
  apply Pm; auto with *.
  red; intros; rewrite H0; rewrite H1; reflexivity.

  intros _.
  apply fa_morph; intros _.
  apply Pm; auto with *.

 rewrite H2; reflexivity.
Qed.

Lemma extln_cons a x y q x' y' :
  a ∈ Arg ->
  x ∈ A a ->
  y ∈ B a x ->
  q ∈ Arg' (f a x y) ->
  x' ∈ A (Dec (f a x y) q) ->
  y' ∈ B (Dec (f a x y) q) x' ->
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
  a ∈ Arg ->
  x ∈ A a ->
  y ∈ B a x ->
  extln empty x y == couple x (couple y empty).
intros.
unfold extln at 1.
rewrite Arg'_rec_mt with (a:=a); auto with *.

 do 2 red; auto with *.

 do 6 red; intros.
 apply couple_morph;[|apply couple_morph;[|apply H5]]; trivial.
Qed.

Lemma extln_typ : forall a q x y,
  a ∈ Arg ->
  q ∈ Arg' a ->
  x ∈ A (Dec a q) ->
  y ∈ B (Dec a q) x ->
  extln q x y ∈ Arg' a.
intros a q x y aty qty; revert x y; apply Arg'_ind with (5:=qty); trivial; intros.
 do 3 red; intros.
 apply fa_morph; intros x1.
 apply fa_morph; intros y1.
 rewrite H; rewrite H0; reflexivity.

 rewrite Dec_mt in H0,H1; trivial.
 rewrite extln_nil with (a:=a0); trivial.
 apply Arg'_intro2; auto.
 apply Arg'_intro1; trivial.
 apply ftyp; auto.

 rewrite Dec_cons in H4,H5; auto.
 rewrite extln_cons with (a:=a0); auto.
 apply Arg'_intro2; auto.
Qed.

(** [WW] is the encoded type with small index
 *)
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

Instance WWf_morph a' : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set)
     (W_Fd (A'' a') (B'' a') extln).
do 3 red; intros.
apply W_Fd_morph; auto with *.
Qed.

(** Proving that the closure ordinal does not grow by changing the path base
    (from [a] to [f a x y])
 *)

Section SmallerParameter.

Import ZFfix.

Variable (a x y : set)
 (tya : a ∈ Arg)
 (tyx : x ∈ A a)
 (tyy : y ∈ B a x).
Let a' := f a x y.
Variable
 (tya' : a' ∈ Arg).

Let cs q := couple x (couple y q).

Let arg'2arg : typ_fun cs (Arg' a') (Arg' a).
red; intros.
apply Arg'_intro2; trivial.
Qed.

Let csa p := couple (cs (fst p)) (snd p).
Let csam : morph1 csa.
do 2 red; intros.
unfold csa, cs.
rewrite H; reflexivity.
Qed.
Existing Instance csam.

Lemma a'2a : typ_fun csa (A' (Arg' a') (A'' a')) (A' (Arg' a) (A'' a)).
red; intros.
apply A'_elim in H; auto with *.
destruct H as (?,(?,_)).
apply A'_intro; auto with *.
unfold A'' in H0|-*.
unfold cs; rewrite Dec_cons; auto.
Qed.

Let ea z : ext_fun (A' (Arg' z) (A'' z)) (B' (B'' z)).
do 2 red; intros.
unfold B', B''.
rewrite H0; reflexivity.
Qed.

Let idx_incl : sup (A' (Arg' a') (A'' a')) (B' (B'' a')) ⊆ sup (A' (Arg' a) (A'' a)) (B' (B'' a)).
red; intros.
rewrite sup_ax in H|-*; auto with *.
destruct H.
unfold B', B'' in H0|-*.
assert (h:=H); apply a'2a in h.
exists (couple (couple x (couple y (fst x0))) (snd x0)); trivial.
rewrite fst_def; rewrite snd_def.
rewrite Dec_cons; auto.
apply fst_typ_sigma in H; trivial.
Qed.

Let csw w := replf w (fun p => couple (fst p) (csa (snd p))).
Let cswe w : ext_fun w (fun p => couple (fst p) (csa (snd p))).
do 2 red; intros.
rewrite H0; reflexivity.
Qed.
Let cswm : morph1 csw.
unfold csw; do 2 red; intros.
apply replf_morph; trivial.
red; intros.
rewrite H1; reflexivity.
Qed.
Existing Instance cswm.

Notation Fa := (W0.Wf (A' (Arg' a) (A'' a)) (B' (B'' a))).
Notation Fa' := (W0.Wf (A' (Arg' a') (A'' a')) (B' (B'' a'))).
Notation dom_a := (W0.Wdom (A' (Arg' a) (A'' a)) (B' (B'' a))).
Notation dom_a' := (W0.Wdom (A' (Arg' a') (A'' a')) (B' (B'' a'))).

Let dom_incl : typ_fun csw dom_a' dom_a.
unfold W0.Wdom.
red; intros.
apply power_intro; intros.
unfold csw in H0; rewrite replf_ax in H0; trivial.
destruct H0.
specialize power_elim with (1:=H) (2:=H0); intro.
rewrite H1; apply couple_intro.
 apply fst_typ in H2.
 revert H2; apply List_mono; trivial.

 apply a'2a.
 apply snd_typ in H2; trivial.
Qed.


Let cswse b g : ext_fun b (fun i => csw (cc_app g i)).
do 2 red; intros.
rewrite H0; reflexivity.
Qed.

Let csw_sup : forall w X,
  w ∈ W0.W_F (A' (Arg' a') (A'' a')) (B' (B'' a')) X ->
  csw (W0.Wsup (B' (B'' a')) w) ==
  W0.Wsup (B' (B'' a)) (couple (csa (fst w))
     (cc_lam (B' (B'' a) (csa (fst w))) (fun i => csw (cc_app (snd w) i)))).
 intros.
 assert (fst (fst w) ∈ Arg' a').
  apply fst_typ_sigma in H.
  apply fst_typ_sigma in H; trivial.
 apply eq_set_ax; intros z.
 unfold csw at 1.
 rewrite replf_ax; trivial.
 split; intros.
  destruct H1.
  rewrite W0.Wsup_def in H1|-*.
   rewrite fst_def.
   destruct H1; [left|right].
    rewrite H2; rewrite H1; rewrite fst_def; rewrite snd_def; reflexivity.

    destruct H1 as (i,?,(q,?,?)).
    rewrite H4 in H2; rewrite fst_def in H2; rewrite snd_def in H2.
    exists i.
     unfold B', B''.
     rewrite fst_def.
     unfold csa; rewrite fst_def; rewrite snd_def.
     unfold cs; rewrite Dec_cons; auto.
    exists (couple (fst q) (csa(snd q))).
     rewrite snd_def.
     rewrite cc_beta_eq; trivial.
      unfold csw; rewrite replf_ax; auto with *.
      exists q; auto with *.
     unfold B', B''.
     unfold csa; rewrite fst_def; rewrite snd_def.
     unfold cs; rewrite Dec_cons; auto.

    rewrite fst_def; rewrite snd_def; trivial.

  rewrite W0.Wsup_def in H1.
   destruct H1.
   rewrite fst_def in H1.
   exists (couple Nil (fst w)).
    rewrite W0.Wsup_def; left; reflexivity.

    rewrite fst_def; rewrite snd_def; trivial.

   destruct H1 as (i,?,(q,?,?)).
    rewrite snd_def in H2.
    unfold B',B'' in H1; rewrite fst_def in H1.
    rewrite cc_beta_eq in H2; auto.
    unfold csw in H2; rewrite replf_ax in H2; trivial.
    destruct H2.
    exists (couple (Cons i (fst q)) (snd x0)).
     rewrite W0.Wsup_def; right.
     exists i.
      unfold csa in H1; rewrite fst_def in H1; rewrite snd_def in H1.
      unfold cs in H1; rewrite Dec_cons in H1; auto.
     exists x0; trivial.
     rewrite H4; rewrite fst_def; reflexivity.

     rewrite H3; rewrite H4; do 2 rewrite fst_def; do 2 rewrite snd_def.
     reflexivity.
Qed.

Let Fa_typ : forall X Y,
  typ_fun csw X Y ->
  typ_fun csw (Fa' X) (Fa Y).
red; intros.
apply W0.Wf_elim in H0; auto with *.
destruct H0 as (w,?,?).
rewrite H1; clear x0 H1.
rewrite csw_sup with (1:=H0).
apply W0.Wf_intro; trivial.
apply W0.W_F_elim in H0; trivial.
destruct H0 as (?,(?,_)).
apply W0.W_F_intro; trivial.
 apply a'2a; trivial.

 intros.
 apply H.
 apply H1.
 unfold B', B'', csa in H2|-*.
 rewrite fst_def in H2; rewrite snd_def in H2.
 unfold cs in H2; rewrite Dec_cons in H2; trivial.
 apply  fst_typ_sigma in H0; trivial.
Qed.

Let Fa_mono z : Proper (incl_set==>incl_set) (W0.Wf (A' (Arg' z) (A'' z)) (B' (B'' z))).
apply W0.Wf_mono; trivial.
Qed.

Let Fa_dom z : forall X,
  X ⊆ W0.Wdom (A' (Arg' z) (A'' z)) (B' (B'' z)) ->
  W0.Wf (A' (Arg' z) (A'' z)) (B' (B'' z)) X ⊆ W0.Wdom (A' (Arg' z) (A'' z)) (B' (B'' z)).
apply W0.Wf_typ; trivial.
Qed.

Let dom_ti_incl : forall o, isOrd o -> typ_fun csw (TI Fa' o) (TI Fa o).
 induction 1 using isOrd_ind; red; intros.
 apply TI_elim in H2; auto with *.
 destruct H2.
 specialize H1 with (1:=H2).
 apply TI_intro with x1; auto with *.
 apply Fa_typ with (1:=H1); trivial.
Qed.

Let fix_incl : typ_fun csw (Ffix Fa' dom_a') (Ffix Fa dom_a).
 red; intros.
 rewrite Ffix_def in H|-*; auto.
 destruct H.
 exists x1; [exact H|].
 apply dom_ti_incl; auto.
Qed.

Lemma wsup_fsub A0 B0 (bm : ext_fun A0 B0) o w :
  isOrd o ->
  w ∈ W0.W_F A0 B0 (TI (W0.Wf A0 B0) o) ->
  fsub (W0.Wf A0 B0) (W0.Wdom A0 B0) (W0.Wsup B0 w) == replf (B0 (fst w)) (fun i => cc_app (snd w) i).
intros.
assert (tyw :=H0).
apply W0.W_F_elim in H0; trivial.
destruct H0 as (ty1,(ty2,eqw)).
rewrite eq_set_ax; intros z.
unfold fsub.
rewrite subset_ax.
split; intros.
 destruct H0 as (?,(z',eqz,?)).
 rewrite eqz in H0|-*; clear z eqz. 
 apply H1.
  red; intros ? h.
  rewrite replf_ax in h.
  2:do 2 red; intros; apply cc_app_morph; auto with *.
  destruct h.
  rewrite H3.
  generalize (ty2 _ H2).
  apply W0.Wi_W'; trivial.

  apply W0.Wf_intro; trivial.
  apply in_reg with (1:=symmetry eqw).
  apply W0.W_F_intro; trivial.
   do 2 red; intros; apply cc_app_morph; auto with *.
  intros.
  rewrite replf_ax.
  2:do 2 red; intros; apply cc_app_morph; auto with *.
  exists i; auto with *.

 rewrite replf_ax in H0.
 2:do 2 red; intros; apply cc_app_morph; auto with *.
 destruct H0 as (i,?,?).
 split.
  rewrite H1.
  generalize (ty2 _ H0).
  apply W0.Wi_W'; trivial.

  exists z;[reflexivity|].
  intros.
  rewrite H1.
  apply W0.Wf_elim in H3; trivial.
  destruct H3 as (w',?,?).
  apply W0.Wsup_inj with (4:=tyw) (5:=H3) in H4; trivial.
   rewrite <- H4 in H3; apply W0.W_F_elim in H3; trivial.
   destruct H3 as (_,(?,_)); auto.

   rewrite W0.Wi_W'; [apply Ffix_inA|trivial|trivial].

   rewrite H2; apply Ffix_inA; trivial.
Qed.


Let csw_fsub : forall o w,
  isOrd o ->
  w ∈ Fa' (TI Fa' o) ->
  typ_fun csw (fsub Fa' dom_a' w) (fsub Fa dom_a (csw w)).
red; intros.
apply W0.Wf_elim in H0; [|trivial].
destruct H0 as (w',?,?).
Existing Instance fsub_morph.
rewrite H2 in H1.
rewrite wsup_fsub with (3:=H0) in H1; trivial.
rewrite replf_ax in H1.
2:do 2 red; intros; apply cc_app_morph; auto with *.
destruct H1 as (i,?,?).
rewrite H3; clear x0 H3.
rewrite H2.
rewrite csw_sup with (1:=H0).
rewrite wsup_fsub with (o:=o); trivial.
 rewrite replf_ax.
 2:do 2 red; intros; apply cc_app_morph; auto with *.
 assert (i ∈ B' (B'' a) (csa (fst w'))).
  unfold B',B''.
  unfold csa; rewrite fst_def; rewrite snd_def.
  unfold cs; rewrite Dec_cons; trivial.
  apply fst_typ_sigma in H0; apply fst_typ_sigma in H0; trivial.
 exists i.
  unfold B',B''; rewrite fst_def; assumption.

  rewrite snd_def.
  rewrite cc_beta_eq; auto with *.

 apply W0.W_F_intro; intros; auto.
  apply a'2a; apply fst_typ_sigma in H0; trivial.

  apply dom_ti_incl; trivial.
  apply W0.W_F_elim in H0; trivial.
  destruct H0 as (?,(?,_)).
  apply H4.
  unfold B',B'',csa in H3; rewrite fst_def in H3; rewrite snd_def in H3.
  unfold cs in H3; rewrite Dec_cons in H3; auto.
  apply fst_typ_sigma in H0; trivial.
Qed.

Let Fra'_ord : forall x,
  x ∈ Ffix Fa' dom_a' ->
  isOrd (Fix_rec Fa' dom_a' (F_a Fa' dom_a') x).
apply F_a_ord; auto with *.
Qed.

Let Fra_ord : forall x,
  x ∈ Ffix Fa' dom_a' ->
  isOrd (Fix_rec Fa dom_a (F_a Fa dom_a) (csw x)).
intros.
apply F_a_ord.
 auto.
 auto.
 apply fix_incl; trivial. 
Qed.

Let F_a_ext : forall (x x' : set) (g g' : set -> set),
 x ∈ Ffix Fa dom_a ->
 eq_fun (fsub Fa dom_a x) g g' ->
 x == x' -> F_a Fa dom_a g x == F_a Fa dom_a g' x'.
intros; apply F_a_morph; trivial.
Qed.
Let F_a'_ext : forall (x x' : set) (g g' : set -> set),
 x ∈ Ffix Fa' dom_a' ->
 eq_fun (fsub Fa' dom_a' x) g g' ->
 x == x' -> F_a Fa' dom_a' g x == F_a Fa' dom_a' g' x'.
intros; apply F_a_morph; trivial.
Qed.

Lemma Faord : forall x,
  x ∈ Ffix Fa' dom_a' ->
  Fix_rec Fa' dom_a' (F_a Fa' dom_a') x ⊆
  Fix_rec Fa dom_a (F_a Fa dom_a) (csw x).
intros.
rewrite Ffix_def in H; auto.
destruct H.
revert x0 H0; elim H using isOrd_ind; intros.
rewrite Fr_eqn with (o:=y0); auto.
rewrite Fr_eqn with (o:=y0); auto.
2: apply dom_ti_incl; auto.
unfold F_a at 1 3.
apply osup_lub.
 apply ZFfix.Fe1; trivial.
 apply isOrd_osup.
  apply ZFfix.Fe1; trivial.
  intros; apply isOrd_succ; apply F_a_ord; auto.
  apply subset_elim1 in H4; trivial.
red; intros.
apply TI_elim in H3; [|auto|auto].
destruct H3 as (o',?,?).
apply osup_intro with (x:=csw x2).
 apply ZFfix.Fe1; trivial.

 apply csw_fsub with o'; auto with *.
 apply isOrd_inv with y0; trivial.

 revert z H5; apply osucc_mono; auto.
  apply Fra'_ord.
  apply subset_elim1 in H4; trivial.

  apply Fra_ord.
  apply subset_elim1 in H4; trivial.

  apply H2 with o'; trivial.
  unfold fsub in H4; apply subset_elim2 in H4.
  destruct H4 as (x',?,?).
  rewrite H4; apply H5; trivial.
  apply TI_Ffix; auto.
  apply isOrd_inv with y0; trivial.
Qed.


Lemma smaller_parameter :
  W_ord (Arg' a') (A'' a') (B'' a') ⊆ W_ord (Arg' a) (A'' a) (B'' a).
unfold W_ord.
unfold W0.W_ord.
unfold Ffix_ord.
apply osup_lub.
 apply ZFfix.Fe1.
 apply isOrd_osup.
  apply ZFfix.Fe1; trivial.
  intros; apply isOrd_succ; apply F_a_ord; auto.
red; intros.
apply osup_intro with (x:=csw x0).
 apply ZFfix.Fe1; trivial.

 apply fix_incl; trivial.

 revert H0; apply osucc_mono; auto.
 apply Faord; trivial.
Qed.

End SmallerParameter.


Lemma WW_eqn a : a ∈ Arg -> WW a == W_Fd A B f WW a.
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
   set (a' := f a x' x0).
   assert (tya' : a' ∈ Arg).
    unfold a'; apply ftyp; auto.
    rewrite H1; trivial.
   unfold W.
   set (Wo1 := W_ord (Arg' a') (A'' a') (B'' a')).
   set (Wo := W_ord (Arg' a) (A'' a) (B'' a)).
   assert (Wo1 ⊆ Wo).
    (* Wo1 is smaller than Wo because there are less parameters reachable from
       [f a x x' x0] than from [a]. *)
    apply smaller_parameter; trivial.
    rewrite H1; trivial.
   transitivity (Wi (Arg' a') (A'' a') (B'' a') extln Wo empty).
    apply incl_eq.
     unfold Wi; apply TIF_mono; auto with *.
      apply W_Fd_mono; auto with *; intros.
      apply extln_typ; trivial.    
      apply Arg'_intro1; trivial.
      apply W_o_o; auto with *.
      apply W_o_o; auto with *.

     apply W_post; intros; auto with *.
      intros; apply extln_typ; trivial.
      apply W_o_o; auto with *.
      apply Arg'_intro1; trivial.
   apply W_simul with (g:=fun q => couple x (couple x0 q)); intros ; auto with *.
    apply extln_typ; auto.

    apply extln_typ; auto.

    do 2 red; intros; rewrite H5; reflexivity.

    apply Arg'_intro2; trivial.
     rewrite <- H1; trivial.
     rewrite <- H1; trivial.

    apply Am.
    rewrite Dec_cons; trivial.
     unfold a'; rewrite H1; reflexivity.
     rewrite <- H1; trivial.
     rewrite <- H1; trivial.

    apply Bm; auto with *.
    rewrite Dec_cons; trivial.
     unfold a'; rewrite H1; reflexivity.
     rewrite <- H1; trivial.
     rewrite <- H1; trivial.

    rewrite extln_cons with (a:=a); auto with *.
     rewrite <- H1; trivial.
     rewrite <- H1; trivial.
     rewrite <- H1; trivial.
     rewrite <- H1; trivial.

    apply W_o_o; auto with *.

    apply Arg'_intro1; trivial.

    rewrite <- extln_nil with (a:=a); auto with *.
     rewrite H3; reflexivity.
     rewrite <- H1; trivial.

 intros.
 apply extln_typ; trivial.

 apply Arg'_intro1; trivial.
Qed.

(** Showing the encoding [WW] is small even when Arg is big
 *)

Section UniverseFacts.

  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : omega ∈ U.  

  (** We don't assume Arg is in U... *)
  Hypothesis aU : forall a, a ∈ Arg -> A a ∈ U.
  Hypothesis bU : forall a x, a ∈ Arg -> x ∈ A a -> B a x ∈ U.


  (* ... but Arg' is in U *)
  Lemma G_Arg' : forall a, a ∈ Arg -> Arg' a ∈ U.
unfold Arg'.
elim isOrd_omega using isOrd_ind; intros.
rewrite TIF_eq; auto.
apply G_sup; trivial.
 do 2 red; intros; apply Lmorph; auto with *.
 apply TIF_morph; trivial.

 apply G_incl with omega; trivial.

 intros.
 apply G_union2; trivial.
  apply G_singl; trivial.
  apply G_trans with omega; auto.
  apply zero_omega.

  apply G_sigma; auto.
   do 2 red; intros; apply sigma_morph.
    apply Bm; auto with *.

    red; intros.
    apply TIF_morph; auto with *.
    apply fm; auto with *.

   intros.
   apply G_sigma; auto.
   do 2 red; intros.
   apply TIF_morph; auto with *.
   apply fm; auto with *.
Qed.


  Lemma G_WW a : a ∈ Arg -> WW a ∈ U.
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

Section Test.
Let x := (WW_eqn, G_WW).
Print Assumptions x.
End Test.
