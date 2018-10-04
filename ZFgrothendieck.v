Require Import ZF.
Require Import ZFpairs ZFsum ZFrelations ZFrepl ZFwf ZFord ZFfix ZFfixfun.
Require Import ZFstable.
Require Import ZFlist.

Record grot_univ (U:set) : Prop := {
  G_trans : forall x y, y ∈ x -> x ∈ U -> y ∈ U;
  G_pair : forall x y, x ∈ U -> y ∈ U -> pair x y ∈ U;
  G_power : forall x, x ∈ U -> power x ∈ U;
  G_union_repl : forall I R, repl_rel I R -> I ∈ U ->
                (forall x y, x ∈ I -> R x y -> y ∈ U) ->
                union (repl I R) ∈ U }.

Instance grot_univ_morph : Proper (eq_set==>iff) grot_univ.
apply morph_impl_iff1; auto with *.
do 3 red; intros.
destruct H0 as (Gtr,G2,Gpow,Gsup).
split; intros.
 rewrite <- H in H1|-*; eauto.

 rewrite <- H in H0,H1|-*; auto.

 rewrite <- H in H0|-*; auto.

 rewrite <- H in H1|-*.
 apply Gsup; intros; auto.
 rewrite H; eauto.
Qed.

Lemma grot_empty : grot_univ empty.
split; intros.
 elim empty_ax with (1:=H0).
 elim empty_ax with (1:=H0).
 elim empty_ax with (1:=H).
 elim empty_ax with (1:=H0).
Qed.

(* grot_succ empty == HF *)

Section GrothendieckUniverse.

Variable U : set.
Hypothesis grot : grot_univ U.

Lemma G_incl : forall x y, x ∈ U -> y ⊆ x -> y ∈ U.
intros.
apply G_trans with (power x); trivial.
 rewrite power_ax; auto.

 apply G_power; trivial.
Qed.

Lemma G_subset : forall x P, x ∈ U -> subset x P ∈ U.
intros.
apply G_incl with x; trivial.
red; intros.
apply subset_elim1 in H0; trivial.
Qed.

Lemma G_singl : forall x, x ∈ U -> singl x ∈ U.
unfold singl; intros; apply G_pair; auto.
Qed.

Lemma G_repl : forall A R,
  repl_rel A R ->
  A ∈ U ->
  (forall x y, x ∈ A -> R x y -> y ∈ U) ->
  repl A R ∈ U.
intros.
assert (repl_rel A (fun x y => exists2 z, R x z & y == singl z)).
 destruct H as (Rext,Rfun).
 split; intros.
  destruct H4.
  exists x0.
   apply Rext with x x0; auto; try reflexivity.
   transitivity y; auto; symmetry; auto.

   destruct H2; destruct H3.
   rewrite H4; rewrite H5.
   apply singl_morph.
   eauto.
setoid_replace (repl A R) with
 (union (repl A (fun x y => exists2 z, R x z & y == singl z))).
 apply G_union_repl; trivial.
 destruct 2.
 rewrite H5.
 apply G_singl; eauto.

 apply union_ext; intros.
  elim repl_elim with (2:=H4); trivial; intros.
  destruct H6.
  rewrite H7 in H3.
  rewrite (singl_elim _ _ H3).
  apply repl_intro with x0; trivial.

  elim repl_elim with (2:=H3); trivial; intros.
  exists (singl x).
   apply singl_intro.

   apply repl_intro with x0; trivial.
   exists x; trivial; reflexivity.
Qed.

Lemma G_union : forall x, x ∈ U -> union x ∈ U.
intros.
setoid_replace x with (repl x (fun y z => z==y)).
apply G_union_repl; trivial; intros.
 apply repl_rel_fun with (f:=fun x:set=>x).
 do 2 red; auto.

 rewrite H1; apply G_trans with x; trivial.
 apply repl_ext; intros.
  apply repl_rel_fun with (f:=fun x:set=>x).
  do 2 red; auto.

  rewrite H1; trivial.

  exists y; trivial; reflexivity.
Qed.

Lemma G_replf : forall A F,
  ext_fun A F ->
  A ∈ U ->
  (forall x, x ∈ A -> F x ∈ U) ->
  replf A F ∈ U.
unfold replf; intros; apply G_repl; intros; auto.
 apply repl_rel_fun; trivial.
 rewrite H3; auto.
Qed.

Lemma G_union2 : forall x y, x ∈ U -> y ∈ U -> x ∪ y ∈ U.
intros.
unfold union2.
apply G_union.
apply G_pair; trivial.
Qed.

Lemma G_sup A B :
  ext_fun A B ->
  A ∈ U ->
  (forall x, x ∈ A -> B x ∈ U) ->
  sup A B ∈ U.
intros.
apply G_union; trivial.
apply G_replf; trivial.
Qed.

Lemma G_nat x : x ∈ U -> ZFnats.N ⊆ U.
red; intros.
elim H0 using ZFnats.N_ind; intros.
 rewrite <- H2; trivial.

 apply G_incl with x; trivial.

 apply G_union2; trivial.
 apply G_singl; trivial.
Qed.

Lemma G_prodcart : forall A B, A ∈ U -> B ∈ U -> prodcart A B ∈ U.
intros.
unfold prodcart.
apply G_subset; intros; trivial.
apply G_power; trivial.
apply G_power; trivial.
apply G_union2; trivial.
Qed.

Lemma G_couple : forall x y, x ∈ U -> y ∈ U -> couple x y ∈ U.
intros.
unfold couple.
apply G_pair; trivial.
 apply G_singl; trivial.

 apply G_pair; trivial.
Qed.

  Lemma G_sum X Y : X ∈ U -> Y ∈ U -> sum X Y ∈ U.
unfold sum; intros.
apply G_union2; apply G_prodcart; trivial.
 apply G_singl; apply G_nat with X; trivial.
 apply ZFnats.zero_typ.

 apply G_singl; apply G_nat with X; trivial.
 apply ZFnats.succ_typ;  apply ZFnats.zero_typ.
Qed.

Lemma G_sumcase A B f g a :
  morph1 f ->
  morph1 g ->
  a ∈ sum A B ->
  (forall a, a ∈ A -> f a ∈ U) ->
  (forall a, a ∈ B -> g a ∈ U) ->
  sum_case f g a ∈ U.
intros.
apply sum_case_ind with (6:=H1); intros; auto.
apply morph_impl_iff1; auto with *.
do 3 red; intros.
rewrite <- H4; trivial.
Qed.

Lemma G_rel : forall A B, A ∈ U -> B ∈ U -> rel A B ∈ U.
intros.
unfold rel.
apply G_power; trivial.
apply G_prodcart; trivial.
Qed.

Lemma G_func : forall A B, A ∈ U -> B ∈ U -> func A B ∈ U.
intros.
unfold func.
apply G_subset; intros; trivial.
apply G_rel; trivial.
Qed.

Lemma G_dep_func : forall X Y,
  ext_fun X Y ->
  X ∈ U ->
  (forall x, x ∈ X -> Y x ∈ U) ->
  dep_func X Y ∈ U.
intros.
unfold dep_func.
apply G_subset; intros; trivial.
apply G_func; trivial.
unfold dep_image.
apply G_union; trivial.
apply G_replf; trivial.
Qed.

Lemma G_app f x :
  f ∈ U -> x ∈ U -> app f x ∈ U.
unfold app; intros.
apply G_union.
apply G_subset.
unfold rel_image.
apply G_subset.
apply G_union; trivial.
apply G_union; trivial.
Qed.

  Lemma G_sigma A B :
    ext_fun A B ->
    A ∈ U ->
    (forall x, x ∈ A -> B x ∈ U) ->
    sigma A B ∈ U.
intros.
apply G_subset; trivial.
apply G_prodcart; trivial.
apply G_sup; trivial.
Qed.

  Lemma G_cc_lam A F :
    ext_fun A F ->
    A ∈ U ->
    (forall x, x ∈ A -> F x ∈ U) ->
    cc_lam A F ∈ U.
intros.
unfold cc_lam.
apply G_sup; intros; trivial.
 do 2 red; intros; apply replf_morph; auto.
 red; intros; apply couple_morph; trivial.
apply G_replf; intros; auto.
 do 2 red; intros; apply couple_morph; auto with *.

 apply G_couple; trivial.
  apply G_trans with A; trivial.

  apply G_trans with (F x); auto.
Qed.

  Lemma G_cc_app f x :
    f ∈ U -> x ∈ U -> cc_app f x ∈ U.
unfold cc_app; intros.
unfold rel_image.
apply G_subset.
apply G_union.
apply G_union.
apply G_subset; trivial.
Qed.

  Lemma G_cc_prod A B :
    ext_fun A B ->
    A ∈ U ->
    (forall x, x ∈ A -> B x ∈ U) ->
    cc_prod A B ∈ U.
intros.
unfold cc_prod.
apply G_replf; auto with *.
 apply G_dep_func; intros; auto with *.

 intros.
 apply G_cc_lam; intros; auto.
  do 2 red; intros; apply app_morph; auto with *.

  apply G_app.
   apply G_trans with (dep_func A B); trivial.
   apply G_dep_func; trivial.

   apply G_trans with A; trivial.
Qed.

  Lemma G_TR F o :
    Proper ((eq_set==>eq_set)==>eq_set==>eq_set) F ->
    (forall o f f', isOrd o -> eq_fun o f f' -> F f o == F f' o) ->
    isOrd o ->
    o ∈ U ->
    (forall f o, ext_fun o f -> o ∈ U ->
     (forall o', o' ∈ o -> f o' ∈ U) ->
     F f o ∈ U) ->
    TR F o ∈ U.
intros Fm Fext oo oU FU.
apply TR_typ with (X:=fun _ => U); auto.
 do 2 red; reflexivity.
intros.
apply FU; auto.
apply G_incl with o; trivial.
Qed.

  Lemma G_TI F o :
    morph1 F ->
    isOrd o ->
    o ∈ U ->
    (forall x, x ∈ U -> F x ∈ U) ->
    TI F o ∈ U.
intros.
apply G_TR; trivial; intros.
 do 3 red; intros.
 apply sup_morph; auto.
 red; intros; auto.

 apply sup_morph; auto with *.
 red; intros.
 apply H; auto.

 apply G_sup; auto.
 do 2 red; intros; apply H; auto.
Qed.

Lemma G_osup2 x y :
  isOrd x -> x ∈ U -> y ∈ U -> x ⊔ y ∈ U.
intro wfx; revert y; induction wfx using isOrd_ind.
intros.
rewrite osup2_def; trivial.
 apply G_union2; trivial.
  apply G_union2; trivial.

  apply G_union; trivial.
  apply G_replf; trivial; intros.
   do 2 red; intros; apply replf_morph; auto with *.
   red; intros; apply osup2_morph; trivial.

   apply G_replf; trivial; intros.
    do 2 red; intros; apply osup2_morph; auto with *.

    eauto using G_trans.
Qed.

  Lemma G_Ffix F A : A ∈ U -> Ffix F A ∈ U.
intros.
unfold Ffix.
apply G_subset; trivial.
Qed.

  Lemma G_TIF A F :
    Proper ((eq_set==>eq_set)==>eq_set==>eq_set) F ->
    mono_fam A F ->
    (forall X a, a ∈ A -> morph1 X -> typ_fun X A U -> F X a ∈ U) ->
    forall o a, isOrd o -> o ∈ U -> a ∈ A -> TIF A F o a ∈ U.
intros Fm Fmono Uty o a oo oty aty.
revert a aty.
apply isOrd_ind with (2:=oo); intros o' oo' o'le orec; intros.
rewrite TIF_eq; trivial.
apply G_sup; trivial.
 do 2 red; intros.
 apply Fm; auto with *.
 apply TIF_morph; trivial.

 apply G_incl with o; trivial.

 intros.
 apply Uty; trivial.
  apply TIF_morph; auto with *.

  red; intros.
  apply orec; trivial.
Qed.

Section NonTrivial.

  Hypothesis Unontriv : empty ∈ U.

End NonTrivial.


Section Infinite.

  Hypothesis Uinf : omega ∈ U.

  Lemma G_inf_nontriv : empty ∈ U.
apply G_trans with omega; trivial.
apply zero_omega.
Qed.
  Hint Resolve G_inf_nontriv.


  Lemma G_List A : A ∈ U -> List A ∈ U.
intros.
unfold List.
apply G_TI; intros; trivial.
 apply LISTf_morph.

 unfold LISTf.
 apply G_union2; trivial.
  apply G_pair; trivial; apply G_trans with omega; trivial; apply zero_omega.

  apply G_prodcart; trivial.  
Qed.


  Lemma G_N : ZFnats.N ∈ U.
pose (f := fun X => singl ZFnats.zero ∪ replf X ZFnats.succ).
assert (fm : morph1 f).
 do 2 red; intros.
 apply union2_morph; auto with *.
 apply replf_morph; trivial.
 red; intros; apply ZFnats.succ_morph; trivial.
assert (ZFnats.N ⊆ TI f omega).
 red; intros.
 apply ZFnats.nat2set_reflect in H.
 destruct H.
 rewrite H.
 clear z H.
 induction x; simpl.
  apply TI_intro with empty; trivial.
  apply union2_intro1.
  apply singl_intro.

  apply TI_elim in IHx; trivial.
  destruct IHx.
  apply TI_intro with (osucc x0); auto.
  apply union2_intro2.
  rewrite replf_ax.
  2:do 2 red; intros; apply ZFnats.succ_morph; trivial.
  exists (ZFnats.nat2set x); auto with *.
  apply TI_intro with x0; auto.
   eauto using isOrd_inv.

   apply lt_osucc; eauto using isOrd_inv.
apply G_incl with (2:=H); trivial.
apply G_TI; trivial; intros.
apply G_union2; trivial.
 apply G_singl; trivial.

 apply G_replf; trivial.
  do 2 red; intros; apply ZFnats.succ_morph; trivial.

  intros.
  unfold ZFnats.succ.
  apply G_union2; eauto using G_trans.
  apply G_singl; trivial.
  apply G_trans with x; trivial.
Qed.

Lemma G_osup I f :
  ext_fun I f ->
  (forall x, x ∈ I -> isOrd (f x)) ->
  I ∈ U ->
  (forall x, x ∈ I -> f x ∈ U) ->
  osup I f ∈ U.
intros ef ford IU fU.
apply osup_univ; trivial; intros.
 apply G_sup; trivial.

 apply G_singl.
 apply G_osup2; eauto using G_trans.

 apply G_N.
Qed.

  Lemma G_Ffix_ord F A :
    Proper (incl_set ==> incl_set) F ->
    (forall X, X ⊆ A -> F X ⊆ A) ->
    A ∈ U ->
    Ffix_ord F A ∈ U.
intros.
assert (Fm := Fmono_morph _ H).
unfold Ffix_ord.
apply G_osup; intros; trivial.
 do 2 red; intros; apply osucc_morph.
 apply Fix_rec_morph; auto with *.
 do 2 red; intros.
 apply F_a_morph_gen; auto with *.

 apply isOrd_succ.
 apply F_a_ord; auto.

 apply G_Ffix; trivial.

 unfold osucc; apply G_subset; trivial; apply G_power; trivial.
 apply subset_elim1 with (P:=isOrd).
 apply Fix_rec_typ; auto; intros.
  apply F_a_morph; trivial.

  unfold F_a.
  apply subset_intro.
   apply G_osup.
    do 2 red; intros.
    apply osucc_morph; apply H3; trivial.

    intros.
    apply isOrd_succ.
    apply H5 in H6.
    apply subset_elim2 in H6; destruct H6.
    rewrite H6; trivial.

    unfold fsub.
    apply G_subset; trivial.
    apply G_Ffix; trivial.

    intros.
    unfold osucc.
    apply G_subset; trivial.
    apply G_power; trivial.
    apply H5 in H6.
    apply subset_elim1 in H6; trivial.

   apply isOrd_osup.
    do 2 red; intros; apply osucc_morph; apply H3; trivial.

    intros.
    apply isOrd_succ.
    apply H5 in H6.
    apply subset_elim2 in H6; destruct H6.
    rewrite H6; trivial.
Qed.

End Infinite.

(*
Section ZF_Universe.

  Hypothesis coll_ax : forall A (R:set->set->Prop), 
    (forall x x' y y', x ∈ A -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x, x ∈ A -> exists y, R x y) ->
    exists B, forall x, x ∈ A -> exists2 y, y ∈ B & R x y.

  (* Grothendieck universe is closed by collection *)
  Hypothesis G_coll : forall A (R:set->set->Prop), 
    A ∈ U ->
    (forall x x' y y', x ∈ A -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x, x ∈ A -> exists2 y, y ∈ U & R x y) ->
    exists2 B, B ∈ U & forall x, x ∈ A -> exists2 y, y ∈ B & R x y.


  Lemma G_ttcoll : forall A (R:set->set->Prop),
  (forall x x' y y', x ∈ A -> x == x' -> y == y' -> R x y -> R x' y') ->
  (forall x, x ∈ A -> exists y, R x y) ->
  A ⊆ U ->
  exists2 X, morph1 X &
  (forall x, x ∈ A -> X x ∈ U) /\
  exists2 f, morph2 f &
    forall x, x ∈ A -> exists2 i, i ∈ X x & R x (f x i).
intros.


intros.
destruct (coll_ax A R) as (B,HB); trivial.


End ZF_Universe.
*)

End GrothendieckUniverse.

(** Intersection *)

Lemma grot_inter : forall UU,
  (exists x, x ∈ UU) ->
  (forall x, x ∈ UU -> grot_univ x) ->
  grot_univ (inter UU).
destruct 1.
split; intros.
 apply inter_intro; intros; eauto.
 destruct (H0 _ H3) as (trans,_,_,_).
 apply trans with x0; trivial.
 apply inter_elim with (1:=H2); trivial.

 apply inter_intro; intros; eauto.
 destruct (H0 _ H3) as (_,clos_pair,_,_).
 apply clos_pair; eapply inter_elim; eauto.

 apply inter_intro; intros; eauto.
 destruct (H0 _ H2) as (_,_,clos_pow,_).
 apply clos_pow; eapply inter_elim; eauto.

 apply inter_intro; intros; eauto.
 destruct (H0 _ H4) as (_,_,_,clos_union).
 apply clos_union; trivial; intros; eapply inter_elim; eauto.
Qed.

Lemma grot_intersection : forall (P:set->Prop) x,
  grot_univ x -> P x ->
  grot_univ (subset x (fun y => forall U, grot_univ U -> P U -> y ∈ U)).
intros.
split; intros.
 apply subset_intro; intros.
  apply G_trans with x0; trivial.
  apply subset_elim1 with (1:=H2).

  elim subset_elim2 with (1:=H2); intros.
  apply G_trans with x0; auto.
  rewrite H5; auto.

 apply subset_intro; intros.
  apply G_pair; trivial.
   apply subset_elim1 with (1:=H1).
   apply subset_elim1 with (1:=H2).

  elim subset_elim2 with (1:=H1); intros.
  elim subset_elim2 with (1:=H2); intros.
  rewrite H5; rewrite H7.
  apply G_pair; auto.
   
 apply subset_intro; intros.
  apply G_power; trivial.
  apply subset_elim1 with (1:=H1).

  elim subset_elim2 with (1:=H1); intros.
  rewrite H4.
  apply G_power; auto.

 apply subset_intro; intros.
  apply G_union_repl; intros; trivial.
   apply subset_elim1 with (1:=H2).
   apply subset_elim1 with (1:=H3 _ _ H4 H5).

  apply G_union_repl; intros; auto.
   elim subset_elim2 with (1:=H2); intros.
   rewrite H6; auto.

   elim subset_elim2 with (1:=H3 _ _ H6 H7); intros.
   rewrite H8; auto.
Qed.

(** Successor *)

Definition grot_succ_pred x y :=
  grot_univ y /\ x ∈ y /\ forall U, grot_univ U -> x ∈ U -> y ⊆ U.

Instance grot_succ_pred_morph : Proper (eq_set==>eq_set==>iff) grot_succ_pred.
do 3 red; intros.
apply and_iff_morphism.
 apply grot_univ_morph; trivial.
apply and_iff_morphism.
 apply in_set_morph; trivial.
apply fa_morph; intros U.
rewrite H; rewrite H0; reflexivity.
Qed.

Definition grot_succ U := uchoice (grot_succ_pred U).

Instance grot_succ_morph : morph1 grot_succ.
do 2 red; intros.
apply uchoice_morph_raw.
apply grot_succ_pred_morph; trivial.
Qed.

Lemma grot_succ_incl x y :
  x ∈ grot_succ y ->
  uchoice_pred (grot_succ_pred x) ->
  uchoice_pred (grot_succ_pred y) ->
  grot_succ x ⊆ grot_succ y.
intros.
specialize uchoice_def with (1:=H0); intros (_,(_,xmin)).
specialize uchoice_def with (1:=H1); intros (?,(?,_)).
apply xmin; trivial.
Qed.

Lemma grot_succ_mono x y :
  x ⊆ y ->
  uchoice_pred (grot_succ_pred x) ->
  uchoice_pred (grot_succ_pred y) ->
  grot_succ x ⊆ grot_succ y.
intros.
apply grot_succ_incl; trivial.
specialize uchoice_def with (1:=H1); intros (?,(?,_)).
apply G_incl with y; trivial.
Qed.

Definition grot_succ_U U x :=
  subset U (fun y => forall V, grot_univ V -> x ∈ V -> y ∈ V).

Instance grot_succ_U_morph : morph2 grot_succ_U.
do 3 red; intros; apply subset_morph; trivial.
red; intros.
apply fa_morph; intros z.
rewrite H0; reflexivity.
Qed.

(** Build the successor from a larger universe *)
Lemma grot_succ_from_U U x :
  grot_univ U ->
  x ∈ U ->
  grot_succ_pred x (grot_succ_U U x).
split;[|split]; intros.
 apply grot_intersection; trivial.

 apply subset_intro; auto.

 red; intros.
 unfold grot_succ_U in H3; rewrite subset_ax in H3; destruct H3 as (?,(z',eqz,?)).
 rewrite eqz; auto.
Qed.

Lemma grot_succ_ex x y :
  grot_succ_pred x y ->
  uchoice_pred (grot_succ_pred x).
split;[|split]; intros.
 revert H1; apply grot_succ_pred_morph; auto with *.

 exists y; trivial.

 destruct H0 as (?,(?,?)).
 destruct H1 as (?,(?,?)).
 apply incl_eq; auto.
Qed.

Lemma grot_succ_U_typ x :
  uchoice_pred (grot_succ_pred x) ->
  grot_univ (grot_succ x).
intro.
apply uchoice_def in H; apply H.
Qed.

Lemma grot_succ_U_in x :
  uchoice_pred (grot_succ_pred x) ->
  x ∈ grot_succ x.
intro.
apply uchoice_def in H; destruct H as (_,(?,_)); trivial.
Qed.

Lemma grot_succ_U_lst U x :
  grot_univ U ->
  x ∈ U ->
  grot_succ x ⊆ U.
intros.
specialize grot_succ_from_U with (1:=H)(2:=H0); intro.
apply grot_succ_ex in H1.
apply uchoice_def in H1.
destruct H1 as (_,(_,?)); auto.
Qed.

(** The Tarski-Grothendieck set theory *)

Definition grothendieck := forall x, exists2 U, grot_univ U & x ∈ U.

Section TarskiGrothendieck.

Variable gr : grothendieck.

Lemma grot_inter_unique : forall x, uchoice_pred (grot_succ_pred x).
intros.
destruct (gr x) as (U, gU, xU).
specialize grot_succ_from_U with (1:=gU) (2:=xU); intro.
apply grot_succ_ex in H; trivial.
Qed.

Lemma grot_succ_typ : forall x, grot_univ (grot_succ x).
intros.
apply grot_succ_U_typ.
apply grot_inter_unique.
Qed.

Lemma grot_succ_in : forall x, x ∈ grot_succ x.
intros.
apply grot_succ_U_in.
apply grot_inter_unique.
Qed.

End TarskiGrothendieck.
