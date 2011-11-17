Require Import ZF.
Require Import ZFpairs ZFrelations ZFrepl ZFwf ZFord ZFfix.
Require Import ZFcoc.
Require Import ZFlist.
Import IZF.

Record grot_univ (U:set) : Prop := {
  G_trans : forall x y, y \in x -> x \in U -> y \in U;
  G_pair : forall x y, x \in U -> y \in U -> pair x y \in U;
  G_power : forall x, x \in U -> power x \in U;
  G_union_repl : forall I R, repl_rel I R -> I \in U ->
                (forall x y, x \in I -> R x y -> y \in U) ->
                union (repl I R) \in U }.

Lemma grot_univ_ext : forall U U',
  U == U' -> grot_univ U -> grot_univ U'.
destruct 2; split; intros.
 rewrite <- H in H1|-*; eauto.

 rewrite <- H in H0,H1|-*; auto.

 rewrite <- H in H0|-*; auto.

 rewrite <- H in H1|-*.
 apply G_union_repl0; intros; auto.
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

Lemma G_incl : forall x y, x \in U -> y \incl x -> y \in U.
intros.
apply G_trans with (power x); trivial.
 rewrite power_ax; auto.

 apply G_power; trivial.
Qed.

Lemma G_subset : forall x P, x \in U -> subset x P \in U.
intros.
apply G_incl with x; trivial.
red; intros.
apply subset_elim1 in H0; trivial.
Qed.

Lemma G_singl : forall x, x \in U -> singl x \in U.
unfold singl; intros; apply G_pair; auto.
Qed.

Lemma G_repl : forall A R,
  repl_rel A R ->
  A \in U ->
  (forall x y, x \in A -> R x y -> y \in U) ->
  repl A R \in U.
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

Lemma G_union : forall x, x \in U -> union x \in U.
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
  A \in U ->
  (forall x, x \in A -> F x \in U) ->
  replf A F \in U.
unfold replf; intros; apply G_repl; intros; auto.
 apply repl_rel_fun; trivial.
 rewrite H3; auto.
Qed.

Lemma G_union2 : forall x y, x \in U -> y \in U -> union2 x y \in U.
intros.
unfold union2.
apply G_union.
apply G_pair; trivial.
Qed.

Lemma G_prodcart : forall A B, A \in U -> B \in U -> prodcart A B \in U.
intros.
unfold prodcart.
apply G_subset; intros; trivial.
apply G_power; trivial.
apply G_power; trivial.
apply G_union2; trivial.
Qed.

Lemma G_couple : forall x y, x \in U -> y \in U -> couple x y \in U.
intros.
unfold couple.
apply G_pair; trivial.
 apply G_singl; trivial.

 apply G_pair; trivial.
Qed.

Lemma G_rel : forall A B, A \in U -> B \in U -> rel A B \in U.
intros.
unfold rel.
apply G_power; trivial.
apply G_prodcart; trivial.
Qed.

Lemma G_func : forall A B, A \in U -> B \in U -> func A B \in U.
intros.
unfold func.
apply G_subset; intros; trivial.
apply G_rel; trivial.
Qed.

Lemma G_dep_func : forall X Y,
  ext_fun X Y ->
  X \in U ->
  (forall x, x \in X -> Y x \in U) ->
  dep_func X Y \in U.
intros.
unfold dep_func.
apply G_subset; intros; trivial.
apply G_func; trivial.
unfold dep_image.
apply G_union_repl; trivial; intros.
 apply repl_rel_fun; trivial.

 rewrite H3; auto.
Qed.

  Lemma G_sup A B :
    ext_fun A B ->
    A \in U ->
    (forall x, x \in A -> B x \in U) ->
    sup A B \in U.
intros.
apply G_union; trivial.
apply G_replf; trivial.
Qed.

  Lemma G_sigma A B :
    ext_fun A B ->
    A \in U ->
    (forall x, x \in A -> B x \in U) ->
    sigma A B \in U.
intros.
apply G_subset; trivial.
apply G_prodcart; trivial.
apply G_sup; trivial.
Qed.

  Lemma G_cc_prod A B :
    ext_fun A B ->
    A \in U ->
    (forall x, x \in A -> B x \in U) ->
    cc_prod A B \in U.
intros.
unfold cc_prod.
apply G_replf; auto with *.
 apply G_dep_func; intros; auto with *.

 intros.
 unfold cc_lam.
 apply G_union; trivial.
 apply G_replf; trivial.
  apply cc_lam_fun2.
  do 2 red; intros; apply app_morph; auto with *.

  intros.
  assert (app x x0 \in U).
   unfold app.
   apply G_union; trivial.
   apply G_subset; trivial.
   unfold rel_image.
   apply G_subset; trivial.
   apply G_union; trivial.
   apply G_union; trivial.
   apply G_trans with (2:=H2); trivial.
   apply G_dep_func; intros; auto with *.
  apply G_replf; intros; trivial.
  apply G_couple; trivial.
   apply G_trans with A; trivial.

   apply G_trans with (app x x0); trivial.
Qed.

  Lemma G_TR F o :
    Proper ((eq_set==>eq_set)==>eq_set==>eq_set) F ->
    (forall o f f', isOrd o -> eq_fun o f f' -> F f o == F f' o) ->
    isOrd o ->
    o \in U ->
    (forall f o, ext_fun o f -> o \in U ->
     (forall o', o' \in o -> f o' \in U) ->
     F f o \in U) ->
    TR F o \in U.
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
    o \in U ->
    (forall x, x \in U -> F x \in U) ->
    TI F o \in U.
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
  isWf x -> x \in U -> y \in U -> osup2 x y \in U.
intro wfx; revert y; induction wfx using isWf_ind.
intros.
rewrite osup2_def; trivial.
 apply G_union2; trivial.
  apply G_union2; trivial.

  apply G_union; trivial.
  apply G_replf; trivial; intros.
   do 2 red; intros; apply replf_morph; auto with *.
   red; intros; apply osup2m; trivial.

   apply G_replf; trivial; intros.
    do 2 red; intros; apply osup2m; auto with *.

    apply H; eauto using G_trans.
Qed.

  Lemma G_Ffix F A : A \in U -> Ffix F A \in U.
intros.
unfold Ffix.
apply G_subset; trivial.
Qed.
(*
  Lemma G_Ffix_ord F A : A \in U -> Ffix_ord F A \in U.
intros.
unfold Ffix_ord.
apply G_osup; intros; trivial.
 do 2 red; intros; apply osucc_morph.
 admit.

 apply isOrd_succ.
 apply F_a_ord; auto.

 apply G_Ffix; trivial.
 apply G_Wdom; trivial.

 unfold osucc; apply G_subset; trivial; apply G_power; trivial.
 unfold Fix_rec.
 admit.
Qed.
*)

Section NonTrivial.

  Hypothesis Unontriv : empty \in U.

End NonTrivial.


Section Infinite.

  Hypothesis Uinf : omega \in U.

  Lemma G_inf_nontriv : empty \in U.
apply G_trans with omega; trivial.
apply zero_omega.
Qed.
  Hint Resolve G_inf_nontriv.


  Lemma G_List A : A \in U -> List A \in U.
intros.
unfold List.
apply G_TI; intros; trivial.
 apply LISTf_morph.

 unfold LISTf.
 apply G_union2; trivial.
  apply G_pair; trivial; apply G_trans with omega; trivial; apply zero_omega.

  apply G_sup; trivial.  
   do 2 red; intros; apply replf_morph; auto with *.
   red; intros; apply couple_morph; trivial.

   intros.
   apply G_replf; intros; trivial.
   apply G_couple; eauto using G_trans.
Qed.


  Lemma G_N : ZFnats.N \in U.
pose (f := fun X => union2 (singl ZFnats.zero) (replf X ZFnats.succ)).
assert (fm : morph1 f).
 do 2 red; intros.
 apply union2_morph; auto with *.
 apply replf_morph; trivial.
 red; intros; apply ZFnats.succ_morph; trivial.
assert (ZFnats.N \incl TI f omega).
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
  (forall x, x \in I -> isOrd (f x)) ->
  I \in U ->
  (forall x, x \in I -> f x \in U) ->
  osup I f \in U.
intros ef ford IU fU.
apply osup_univ; trivial; intros.
 apply G_sup; trivial.

 apply G_singl.
 apply G_osup2; eauto using G_trans.

 apply G_N.
Qed.

End Infinite.

(*
Section ZF_Universe.

  Hypothesis coll_ax : forall A (R:set->set->Prop), 
    (forall x x' y y', x \in A -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x, x \in A -> exists y, R x y) ->
    exists B, forall x, x \in A -> exists2 y, y \in B & R x y.

  (* Grothendieck universe is closed by collection *)
  Hypothesis G_coll : forall A (R:set->set->Prop), 
    A \in U ->
    (forall x x' y y', x \in A -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x, x \in A -> exists2 y, y \in U & R x y) ->
    exists2 B, B \in U & forall x, x \in A -> exists2 y, y \in B & R x y.


  Lemma G_ttcoll : forall A (R:set->set->Prop),
  (forall x x' y y', x \in A -> x == x' -> y == y' -> R x y -> R x' y') ->
  (forall x, x \in A -> exists y, R x y) ->
  A \incl U ->
  exists2 X, morph1 X &
  (forall x, x \in A -> X x \in U) /\
  exists2 f, morph2 f &
    forall x, x \in A -> exists2 i, i \in X x & R x (f x i).
intros.


intros.
destruct (coll_ax A R) as (B,HB); trivial.


End ZF_Universe.
*)

End GrothendieckUniverse.

Lemma grot_inter : forall UU,
  (exists x, x \in UU) ->
  (forall x, x \in UU -> grot_univ x) ->
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
  grot_univ (subset x (fun y => forall U, grot_univ U -> P U -> y \in U)).
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

Definition grot_succ_pred x y :=
  grot_univ y /\ x \in y /\ forall U, grot_univ U -> x \in U -> y \incl U.


Definition grothendieck := forall x, exists2 U, grot_univ U & x \in U.

Section TarskiGrothendieck.

Variable gr : grothendieck.

Lemma grot_inter_unique : forall x, uchoice_pred (grot_succ_pred x).
unfold grot_succ_pred.
split; intros.
 destruct H0 as (H0,(H1,H2)).
 split.
  apply grot_univ_ext with x0; trivial.

  split; intros.
   rewrite <- H; trivial.
   rewrite <- H; auto.

 split; intros.
  elim gr with x; intros.
  exists (subset x0 (fun y =>
    forall U, grot_univ U -> x \in U -> y \in U)).
  split; intros.
   apply (grot_intersection (fun U => x \in U) x0); trivial.

   split; intros.
    apply subset_intro; trivial.

    red; intros.
    elim subset_elim2 with (1:=H3); intros.
    rewrite H4; auto.

 destruct H as (gr_x0,(in_x0,lst_x0)).
 destruct H0 as (gr_x',(in_x',lst_x')).
 red in lst_x0, lst_x'|-.
 apply eq_intro; eauto.
Qed.

Definition grot_succ U := uchoice (grot_succ_pred U).

Lemma grot_succ_typ : forall x, grot_univ (grot_succ x).
intros.
destruct (uchoice_def (grot_succ_pred x)).
 exact (grot_inter_unique x).

 trivial.
Qed.

Lemma grot_succ_in : forall x, x \in grot_succ x.
intros.
destruct (uchoice_def (grot_succ_pred x)).
 exact (grot_inter_unique x).

 destruct H0; trivial.
Qed.

End TarskiGrothendieck.
