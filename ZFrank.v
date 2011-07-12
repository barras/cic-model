Require Import ZF ZFnats ZFord ZFstable ZFfix.
Import IZF.

  (* Von Neumann universes *)
  Definition VN := TI power.

Instance VN_morph : morph1 VN.
do 2 red; intros.
apply TI_morph; trivial.
Qed.

  Lemma VN_def : forall x z,
    isOrd x ->
    (z \in VN x <-> exists2 y, y \in x & z \incl VN y).
split; intros.
 apply TI_elim in H0; auto with *.
 destruct H0.
 exists x0; trivial.
 red; intros.
 eauto using power_elim.

 destruct H0.
 apply TI_intro with x0; auto with *.
 apply power_intro; auto.
Qed.

  Lemma VN_trans : forall o x y,
    isOrd o ->
    x \in VN o ->
    y \in x ->
    y \in VN o.
intros.
rewrite VN_def in H0; trivial.
destruct H0.
apply H2 in H1.
revert H1; apply TI_incl; auto with *.
apply power_mono.
Qed.

  Lemma VN_incl : forall o x y,
    isOrd o ->
    y \incl x ->
    x \in VN o ->
    y \in VN o.
intros.
rewrite VN_def in H1|-*; auto with *.
destruct H1.
exists x0; trivial.
transitivity x; trivial.
Qed.

Lemma VN_mono : forall o x,
  isOrd o ->
  lt x o -> VN x \in VN o.
intros.
rewrite (VN_def o); trivial.
exists x; auto with *.
Qed.

Lemma VN_mono_le : forall o o',
  isOrd o ->
  isOrd o' ->
  o \incl o' ->
  VN o \incl VN o'.
red; intros.
rewrite VN_def in H2|-*; trivial.
destruct H2.
exists x; auto.
Qed.

  Lemma VN_stable : stable_ord VN.
unfold VN.
apply TI_stable.
 apply power_mono.

 apply power_stable.
Qed.
 
Lemma VN_compl : forall x z, isOrd x -> isOrd z -> z \in VN x -> VN z \in VN x. 
intros x z xo; revert z.
induction xo using isOrd_ind; intros.
rewrite VN_def in H2|-*; auto with *.
destruct H2.
exists x0; trivial.
red; intros.
rewrite VN_def in H4; auto with *.
destruct H4.
apply VN_incl with (VN x1); eauto using isOrd_inv.
Qed.

Lemma VN_intro :
  forall x, isOrd x -> x \incl VN x.
induction 1 using isOrd_ind; red; intros.
rewrite VN_def; trivial.
eauto.
Qed.

Lemma VN_succ : forall x, isOrd x -> power (VN x) == VN (osucc x).
intros.
unfold VN.
symmetry; apply TI_mono_succ; trivial.
apply power_mono.
Qed.


  Lemma VN_ord_inv : forall o x, isOrd o -> isOrd x -> x \in VN o -> lt x o.
intros o x xo; revert x.
induction xo using isOrd_ind; intros.
rewrite VN_def in H2; trivial; destruct H2.
apply isOrd_plump with x0; trivial.
red; intros.
apply H0; auto.
apply isOrd_inv with x; trivial.
Qed.


  Lemma VN_subset : forall o x P, isOrd o -> x \in VN o -> subset x P \in VN o.
intros.
apply VN_incl with x; trivial.
red; intros.
apply subset_elim1 in H1; trivial.
Qed.

  Lemma VN_union : forall o x, isOrd o -> x \in VN o -> union x \in VN o.
intros.
rewrite VN_def in H0|-*; trivial.
destruct H0.
exists x0; trivial.
red; intros.
apply union_elim in H2; destruct H2.
apply VN_trans with x1; eauto using isOrd_inv.
Qed.

  Lemma VNsucc_power : forall o x,
    isOrd o ->
    x \in VN o ->
    power x \in VN (osucc o).
intros.
rewrite <- VN_succ; trivial.
apply power_intro; intros.
apply VN_incl with x; trivial.
red; eauto using power_elim.
Qed.

  Lemma VNsucc_pair : forall o x y, isOrd o ->
    x \in VN o -> y \in VN o -> pair x y \in VN (osucc o).
intros.
rewrite <- VN_succ; trivial.
rewrite power_ax; intros.
apply pair_elim in H2; destruct H2; rewrite H2; trivial.
Qed.


  Lemma VNlim_def : forall o x, limitOrd o ->
    (x \in VN o <-> exists2 o', lt o' o & x \in VN o').
destruct 1; rewrite VN_def; trivial.
split; intros.
 destruct H1.
 exists (osucc x0); auto.
 rewrite <- VN_succ; auto.
  rewrite power_ax; auto.
  apply isOrd_inv with o; trivial.

 destruct H1.
 exists x0; trivial.
 red; intros.
 apply VN_trans with x; trivial.
 apply isOrd_inv with o; trivial.
Qed.


  Lemma VNlim_power : forall o x, limitOrd o -> x \in VN o -> power x \in VN o.
intros.
rewrite VNlim_def in H0|-*; trivial.
destruct H0.
exists (osucc x0).
 apply H; trivial.

 apply VNsucc_power; trivial.
 apply isOrd_inv with o; trivial.
 apply H.
Qed.

(*
  Lemma VNlim_pair : forall o x y, isDir o -> limitOrd o ->
    x \in VN o -> y \in VN o -> pair x y \in VN o.
intros o x y dir lim; intros.
rewrite VNlim_def in H,H0|-*; auto.
destruct H; destruct H0.
assert (o0 : isOrd x0) by eauto using isOrd_inv.
assert (o1 : isOrd x1) by eauto using isOrd_inv.
destruct (dir x0 x1); trivial.
destruct H4.
assert (ou : isOrd x2) by eauto using isOrd_inv.
exists (osucc x2).
 apply lim; trivial.

 apply VNsucc_pair.
  apply isOrd_inv with o; trivial.
  apply lim.

  revert H1; apply VN_mono_le; trivial.
  revert H2; apply VN_mono_le; trivial.
Qed.
*)

  Lemma VNlim_pair : forall o x y, limitOrd o ->
    x \in VN o -> y \in VN o -> pair x y \in VN o.
intros o x y lim; intros.
rewrite VNlim_def in H,H0|-*; auto.
destruct H; destruct H0.
assert (o0 : isOrd x0) by eauto using isOrd_inv.
assert (o1 : isOrd x1) by eauto using isOrd_inv.
exists (osucc (osup2 x0 x1)).
 apply lim.
 apply osup2_lt; auto.

 apply VNsucc_pair.
  apply isOrd_osup2; trivial.

  revert H1; apply VN_mono_le; trivial; [apply isOrd_osup2|apply osup2_incl1]; auto.
  revert H2; apply VN_mono_le; trivial; [apply isOrd_osup2|apply osup2_incl2]; auto.
Qed.


Require Import ZFrelations.

  Lemma VN_func : forall o A B,
    isOrd o ->
    A \in VN o ->
    B \in VN o ->
    func A B \in VN (osucc (osucc (osucc (osucc o)))).
unfold func; intros.
apply VN_subset; auto.
unfold rel.
apply VNsucc_power; auto.
unfold ZFpairs.prodcart.
apply VN_subset; auto.
apply VNsucc_power; auto.
apply VNsucc_power; auto.
unfold union2.
apply VN_union; auto.
apply VNsucc_pair; trivial.
Qed.



Definition VN_regular o :=
  forall x F,
  ext_fun x F ->
  x \in VN o ->
  (forall y, y \in x -> F y \in VN o) ->
  sup x F \in VN o.

Definition bound_ord A o :=
  forall F, ext_fun A F ->
  (forall n, n \in A -> lt (F n) o) ->
  lt (osup A F) o.

Lemma VN_reg_ord : forall o,
  isOrd o -> 
  VN_regular o ->
  forall x F,
  ext_fun x F ->
  x \in VN o ->
  (forall y, y \in x -> lt (F y) o) ->
  lt (osup x F) o.
intros.
apply VN_ord_inv; trivial.
 apply isOrd_osup; eauto using isOrd_inv.

admit.
(* TODO: fix
unfold osup.
unfold ord_sup.
 apply H0; intros; trivial.
 apply VN_intro; trivial.
 apply H3; trivial.*)
Qed.

Definition VN_inaccessible o :=
  limitOrd o /\ VN_regular o.

Require Import ZFrepl.

Definition VN_regular_rel o :=
  forall x R,
  repl_rel x R ->
  x \in VN o ->
  (forall y z, y \in x -> R y z -> z \in VN o) ->
  union (repl x R) \in VN o.

Definition VN_inaccessible_rel o :=
  limitOrd o /\ VN_regular_rel o.

Section UnionClosure.

  Variable mu : set.
  Hypothesis mu_ord : isOrd mu.
  Hypothesis mu_lim : forall x, lt x mu -> lt (osucc x) mu.
  Hypothesis mu_reg : VN_regular_rel mu.

  Lemma VN_regular_weaker : VN_regular mu.
red; intros.
apply mu_reg; trivial; intros.
 apply repl_rel_fun; trivial.

 rewrite H3; auto.
Qed.

Let mul : limitOrd mu := conj mu_ord mu_lim.

(*
  Lemma isDir_regular : isDir mu.
red; intros.
pose (R := fun n z => n==zero /\ z==osucc x \/ n==osucc zero /\ z==osucc y).
assert (repl_rel (osucc (osucc zero)) R).
 split; intros.
  unfold R; rewrite <- H2; rewrite <- H3; trivial.

  destruct H2 as [(e1,e2)|(e1,e2)];
  destruct H3 as [(e1',e2')|(e1',e2')];
  rewrite e2; rewrite e2'; try reflexivity.
   assert (h:=lt_osucc zero isOrd_zero); rewrite e1' in e1;
   rewrite e1 in h; apply lt_antirefl in h; trivial; contradiction.

   assert (h:=lt_osucc zero isOrd_zero); rewrite e1' in e1;
   rewrite <- e1 in h; apply lt_antirefl in h; trivial; contradiction.
exists (union (repl (osucc (osucc zero)) R)).
 apply VN_ord_inv; trivial.
  apply isOrd_union; intros.
  apply repl_elim in H2; trivial.
  destruct H2.
  destruct H3 as [(_,e)|(_,e)]; rewrite e; eauto using isOrd_inv.

  apply mu_reg; auto.
   apply VN_intro; auto.
   do 2 apply mu_lim.
   apply isOrd_plump with x; trivial.
   red; intros.
   elim empty_ax with z; trivial.

   intros.   
   destruct H3 as [(_,e)|(_,e)]; rewrite e; apply VN_intro; trivial;
   apply mu_lim; trivial.

 split; red; intros.
  apply union_intro with (osucc x).
   apply isOrd_trans with x; eauto using isOrd_inv, lt_osucc.

   apply repl_intro with zero; trivial.
    apply isOrd_trans with (osucc zero); auto.

    left; split; auto with *.

  apply union_intro with (osucc y).
   apply isOrd_trans with y; eauto using isOrd_inv, lt_osucc.

   apply repl_intro with (osucc zero); trivial.
    apply lt_osucc; auto.

    right; split; auto with *.
Qed.
*)

  Lemma VN_clos_pair : forall x y,
    x \in VN mu -> y \in VN mu -> pair x y \in VN mu.
intros.
apply VNlim_pair; trivial.
(*apply isDir_regular.*)
Qed.

  Definition lt_cardf a b :=
    forall F, ext_fun a F ->
    exists2 y, y \in b & forall x, x \in a -> ~ y == F x.

  Lemma VN_cardf : forall a,
    a \in VN mu -> lt_cardf a mu.
red; intros.
pose (mu' := osup (subset a (fun x => F x \in mu)) F).
assert (ext : ext_fun (subset a (fun x : set => F x \in mu)) F).
 red; red; intros.
 apply H0; trivial.
 apply subset_elim1 in H1; trivial.
assert (mu' \in mu).
 unfold mu'; apply VN_reg_ord; auto.
  exact VN_regular_weaker.

  apply VN_incl with a; trivial.
  red; intros.
  apply subset_elim1 in H1; trivial.

  intros.
  rewrite subset_ax in H1; destruct H1.
  destruct H2.
  setoid_replace (F y) with (F x); trivial.
  apply H0; auto.
assert (isOrd mu').
 eauto using isOrd_inv.
exists (osucc mu').
 apply mu_lim; trivial.

 red; intros.
 apply (lt_antirefl mu'); trivial.
 unfold mu' at 2.
 apply osup_intro with x; trivial.
  apply subset_intro; trivial.
  rewrite <- H4.
  apply mu_lim; trivial.

  rewrite <- H4; apply lt_osucc; auto.
Qed.


Require Import ZFcard.

  Lemma VNcard : forall x,
    x \in VN mu -> lt_card x mu.
red; red; intros.
destruct H0 as (R,?,(?,?)).
rewrite VN_def in H; auto; destruct H.
pose (mu' := osup (subset x (fun x' => exists2 w, w \in mu & R w x'))
              (fun x' => uchoice (fun o => o \in mu /\ R o x'))).
assert (ext : ext_fun (subset x (fun x' => exists2 w, w \in mu & R w x'))
   (fun x' => uchoice (fun o => o \in mu /\ R o x'))).
 red; red; intros.
 apply uchoice_morph_raw.
 red; intros.
 rewrite H5; rewrite H6; reflexivity.
assert (mu' \in mu).
 unfold mu'; apply VN_reg_ord; auto.
  exact VN_regular_weaker.

  apply VN_subset; trivial.
  rewrite VN_def; trivial.
  exists x0; trivial.

  intros.
  rewrite subset_ax in H4; destruct H4.
  destruct H5.
  destruct H6.
  rewrite <- H5 in H7; clear x1 H5.
  assert (uchoice_pred (fun o => o \in mu /\ R o y)).
   split; [|split]; intros; eauto.
    rewrite <- H5; trivial.

    destruct H5; destruct H8.
    eauto with *.
  destruct (uchoice_def _ H5); trivial.
assert (mu == mu').
 apply eq_intro; intros.
  destruct (H1 _ (mu_lim _ H5)).
  unfold mu'.
  apply osup_intro with (x:=x1).
   do 2 red; intros; apply uchoice_morph_raw.
   red; intros.
   rewrite H9; rewrite H10; reflexivity.

   apply subset_intro; trivial.
   exists (osucc z); trivial.
   apply mu_lim; trivial.

   rewrite <- (uchoice_ext _ (osucc z)).
    apply lt_osucc; eauto using isOrd_inv.

    split; [|split]; intros; eauto.
     rewrite <- H8; trivial.

     exists (osucc z); auto.
     split; auto.
     apply mu_lim; trivial.

     destruct H8; destruct H9.
     eauto with *.

    split; trivial.
    apply mu_lim; trivial.

  apply isOrd_trans with mu'; trivial.
rewrite <- H5 in H4.
revert H4; apply lt_antirefl; trivial.
Qed.

  Lemma reg_card : isCard mu.
split; trivial.
intros.
apply VNcard.
apply VN_intro; trivial.
Qed.

End UnionClosure.

(*
Require Import ZFcard.
Require Import ZFrepl.
(*Require Import ZFordcl ZFord_equiv.*)
Import ZFord.

  Lemma repl_rel_incl : forall x y R,
    x \incl y ->
    repl_rel y R ->
    repl_rel x R.
destruct 2.
split; intros; eauto.
Qed.

Section Inaccessible.

  Variable mu : set.
  Variable mu_ord : isOrd mu.
  Variable mu_lim : forall x, lt x mu -> lt (osucc x) mu.
  Variable mu_regular : regular mu.

  Lemma VNcard : forall x,
    x \in VN mu -> lt_card x mu.
red; red; intros.
destruct H0.

Admitted.

  Lemma VNlim_clos_union_repl : forall I R,
    repl_rel I R ->
    I \in VN mu ->
    (forall x y, x \in I -> R x y -> y \in VN mu) ->
    union (repl I R) \in VN mu.
unfold VN; intros.
pose (I' := subset I (fun x => exists y, R x y)).
assert (rrI' : repl_rel I' R).
 apply repl_rel_incl with I; trivial.
 red; intros.
 apply subset_elim1 in H2; trivial.
assert (repl I R == repl I' R).
 apply eq_intro; intros.
  apply repl_elim in H2; auto.
  destruct H2.
  apply repl_intro with x; auto.
  apply subset_intro; auto.
  exists z; trivial.

  apply repl_mono2 with I'; auto.
  red; intros.
  apply subset_elim1 in H3; trivial.
rewrite H2; clear H2.
assert (stgI' : I' \in VN mu).
 apply VN_incl with I; trivial; red; intros.
 apply subset_elim1 in H2; trivial.
clear H0.
pose (G := fun x => least_ord mu
   (fun n => forall y, R x y -> y \in VN n)).
assert (Gm : ext_fun I' G).
 unfold G, VN; do 2 red; intros.
 apply least_ord_morph; intros; auto; try reflexivity.
 assert (TI power x0 == TI power x'0).
  apply TI_morph; trivial.
 split; intros.
  rewrite <- H5.
  apply H6.
  destruct H.
  apply H with x' y; trivial.
   apply subset_elim1 in H0.
   rewrite <- H2; trivial.

   symmetry; trivial.
   reflexivity.
   
  rewrite H5.
  apply H6.
  destruct H.
  apply H with x y; trivial.
   apply subset_elim1 in H0; trivial.
   reflexivity.
apply TI_elim in stgI'; auto with *.
destruct stgI'.
assert (Fprop : forall x, x \in I' ->
  (forall y, R x y -> y \in VN (G x)) /\ lt (G x) mu).
 intros.
 assert (exists y, R x0 y).
  specialize subset_elim2 with (1:=H3); destruct 1.
  destruct H5.
  exists x2.
  apply H with (4:=H5); auto.
   apply subset_elim1 in H3; trivial.
   rewrite <- H4; trivial.
   symmetry; trivial.
   reflexivity.
 apply subset_elim1 in H3.
 destruct H4.
 specialize H1 with (1:=H3) (2:=H4).
 apply TI_elim in H1; auto with *.
 destruct H1.
 rewrite <- TI_mono_succ in H5; auto with *.
 2:exact power_mono.
 2:apply isOrd_inv with mu; trivial.
 destruct least_ord1 with
    (o:=mu) (P:=fun n => forall y, R x0 y -> y \in VN n)
    (x:=osucc x2); intros; auto.
  setoid_replace (VN x') with (VN x3); auto.
  symmetry; unfold VN; apply TI_morph; trivial.

  setoid_replace y with x1; auto.
  destruct H; eauto.

  destruct H7.
  destruct H8.
  split; eauto.
  apply le_lt_trans with (osucc x2); auto.
  red in H8; rewrite succ_equiv in H8; auto.
  apply ZFord.isOrd_succ.
  apply ZFord.isOrd_inv with mu; trivial.
assert (Fmu := fun x h => proj2 (Fprop x h)).
assert (Fspec := fun x h => proj1 (Fprop x h)).
clear Fprop.
assert (Ford : forall x, x \in I' -> isOrd (G x)).
 intros.
 apply isOrd_inv with mu; auto.
assert (lt (sup I' G) mu).
 apply mu_regular; intros; auto.
 apply VNcard.
 apply TI_intro with x; auto.
 exact power_morph.
apply TI_intro with (sup I' G); auto with *.
apply power_intro; intros.
apply union_elim in H4; destruct H4.
apply repl_elim in H5; trivial.
destruct H5.
apply VN_trans with x0; auto.
 apply isOrd_inv with mu; auto.

 apply TI_mono with (G x1); eauto.
  exact power_mono.
  apply isOrd_inv with mu; auto.
Qed.


End Inaccessible.

Section InaccessibleCard.

  Variable mu : set.
  Variable mu_card : isCard mu.
  Variable mu_lim : forall x, lt x mu -> lt (osucc x) mu.
  Variable mu_regular : regular_card mu.

  Let mu_ord : isOrd mu.
destruct mu_card; trivial.
Qed.
  Let mu_lt : forall x, lt x mu -> lt_card x mu.
destruct mu_card; trivial.
Qed.

  Lemma lt_card_lt : forall x, isOrd x -> lt_card x mu -> lt x mu.
unfold lt_card; intros.
destruct (ZFordcl.ClassicOrdinal.ord_total mu x); trivial.
 apply isOrd_eqv1; auto.
 apply isOrd_eqv1; auto.

 elim H0.
 apply ZFordcl.ord_le_incl in H1; try (apply isOrd_eqv1; auto; fail).
 apply incl_le_card in H1; trivial.
Qed.


  Lemma VNcard' : forall x,
    x \in VN mu -> lt_card x mu.
Admitted.

  Lemma VNreg_clos_sup : forall I F,
    ext_fun I F ->
    I \in VN mu ->
    (forall x, x \in I -> F x \in VN mu) ->
    sup I F \in VN mu.
unfold VN; intros.
pose (G := fun x => least_ord mu (fun n => F x \in VN n)).
assert (Gm : ext_fun I G).
 unfold G, VN; do 2 red; intros.
 apply least_ord_morph; intros; trivial; try reflexivity.
  apply isOrd_eqv1; trivial.
 assert (TI power x0 == TI power x'0).
  apply TI_morph; trivial.
 rewrite <- H6.
 rewrite (H x x'); trivial.
 reflexivity.
apply TI_elim in H0; auto with *.
destruct H0.
assert (Fprop : forall x, x \in I -> F x \in VN (G x) /\ lt (G x) mu).
 intros.
 specialize H1 with (1:=H3).
 apply TI_elim in H1; auto with *.
 destruct H1.
 rewrite <- TI_mono_succ in H4; auto with *.
 2:exact power_mono.
 2:apply isOrd_inv with mu; trivial.
 destruct least_ord1 with
    (o:=mu) (P:=fun n => F x0 \in VN n)
    (x:=osucc x1); intros; auto.
  setoid_replace (VN x') with (VN x2); auto.
  symmetry; unfold VN; apply TI_morph; trivial.

  destruct H6.
  destruct H7.
  split; eauto.
  apply le_lt_trans with (osucc x1); auto.
  red in H7; rewrite succ_equiv in H7; auto.
  apply ZFord.isOrd_succ.
  apply ZFord.isOrd_inv with mu; trivial.
assert (Fmu := fun x h => proj2 (Fprop x h)).
assert (Fspec := fun x h => proj1 (Fprop x h)).
clear Fprop.
assert (Ford : forall x, x \in I -> isOrd (G x)).
 intros.
 apply isOrd_inv with mu; auto.
assert (sup_ord : isOrd (sup I G)).
 apply isOrd_supf; trivial.
assert (lt (sup I G) mu).
 apply lt_card_lt; trivial.
 apply mu_regular; intros; auto.
 apply VNcard'.
 apply TI_intro with x; auto with *.
apply TI_intro with (sup I G); auto with *.
apply power_intro; intros.
rewrite sup_ax in H4; auto.
destruct H4.
apply VN_trans with (F x0); auto.
apply TI_mono with (G x0); eauto.
exact power_mono.
Qed.


End InaccessibleCard.
*)