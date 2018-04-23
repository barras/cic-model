Require Import ZF ZFnats ZFord ZFstable ZFfix.

  (* Von Neumann universes *)
  Definition VN := TI power.

Instance VN_morph : morph1 VN.
do 2 red; intros.
apply TI_morph; trivial.
Qed.

  Lemma VN_def : forall x z,
    isOrd x ->
    (z ∈ VN x <-> exists2 y, y ∈ x & z ⊆ VN y).
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
    x ∈ VN o ->
    y ∈ x ->
    y ∈ VN o.
intros.
rewrite VN_def in H0; trivial.
destruct H0.
apply H2 in H1.
revert H1; apply TI_incl; auto with *.
apply power_mono.
Qed.

  Lemma VN_incl : forall o x y,
    isOrd o ->
    y ⊆ x ->
    x ∈ VN o ->
    y ∈ VN o.
intros.
rewrite VN_def in H1|-*; auto with *.
destruct H1.
exists x0; trivial.
transitivity x; trivial.
Qed.

Lemma VN_mono : forall o x,
  isOrd o ->
  lt x o -> VN x ∈ VN o.
intros.
rewrite (VN_def o); trivial.
exists x; auto with *.
Qed.

Lemma VN_mono_le : forall o o',
  isOrd o ->
  isOrd o' ->
  o ⊆ o' ->
  VN o ⊆ VN o'.
red; intros.
rewrite VN_def in H2|-*; trivial.
destruct H2.
exists x; auto.
Qed.

  Lemma VN_stable : stable_ord VN.
unfold VN.
apply TI_stable with (fun _ => True); auto with *.
 apply power_mono.

 do 2 red; reflexivity.

 apply power_stable.
Qed.
 
Lemma VN_compl : forall x z, isOrd x -> isOrd z -> z ∈ VN x -> VN z ∈ VN x. 
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
  forall x, isOrd x -> x ⊆ VN x.
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


  Lemma VN_ord_inv : forall o x, isOrd o -> isOrd x -> x ∈ VN o -> lt x o.
intros o x xo; revert x.
induction xo using isOrd_ind; intros.
rewrite VN_def in H2; trivial; destruct H2.
apply isOrd_plump with x0; trivial.
red; intros.
apply H0; auto.
apply isOrd_inv with x; trivial.
Qed.


  Lemma VN_subset : forall o x P, isOrd o -> x ∈ VN o -> subset x P ∈ VN o.
intros.
apply VN_incl with x; trivial.
red; intros.
apply subset_elim1 in H1; trivial.
Qed.

  Lemma VN_union : forall o x, isOrd o -> x ∈ VN o -> union x ∈ VN o.
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
    x ∈ VN o ->
    power x ∈ VN (osucc o).
intros.
rewrite <- VN_succ; trivial.
apply power_intro; intros.
apply VN_incl with x; trivial.
red; eauto using power_elim.
Qed.

  Lemma VNsucc_pair : forall o x y, isOrd o ->
    x ∈ VN o -> y ∈ VN o -> pair x y ∈ VN (osucc o).
intros.
rewrite <- VN_succ; trivial.
rewrite power_ax; intros.
apply pair_elim in H2; destruct H2; rewrite H2; trivial.
Qed.


  Lemma VNlim_def : forall o x, limitOrd o ->
    (x ∈ VN o <-> exists2 o', lt o' o & x ∈ VN o').
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


  Lemma VNlim_power : forall o x, limitOrd o -> x ∈ VN o -> power x ∈ VN o.
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
    x ∈ VN o -> y ∈ VN o -> pair x y ∈ VN o.
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
    x ∈ VN o -> y ∈ VN o -> pair x y ∈ VN o.
intros o x y lim; intros.
rewrite VNlim_def in H,H0|-*; auto.
destruct H; destruct H0.
assert (o0 : isOrd x0) by eauto using isOrd_inv.
assert (o1 : isOrd x1) by eauto using isOrd_inv.
exists (osucc (x0 ⊔ x1)).
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
    A ∈ VN o ->
    B ∈ VN o ->
    func A B ∈ VN (osucc (osucc (osucc (osucc o)))).
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

Require Import ZFwf.

Lemma VN_wf o x : isOrd o -> x ∈ VN o -> isWf x.
intros oo; revert x; induction oo using isOrd_ind.
intros.
apply isWf_intro; intros.
rewrite VN_def in H1; trivial; destruct H1.
apply H3 in H2; eauto.
Qed.

Lemma VN_osup2 o :
  isOrd o ->
  forall x y,
  x ∈ VN o ->
  y ∈ VN o ->
  x ⊔ y ∈ VN o.
induction 1 using isOrd_ind; intros.
rewrite VN_def in H2,H3|-*; trivial.
destruct H2.
destruct H3.
exists (x0 ⊔ x1).
 apply osup2_lt; trivial.

 red; intros.
 rewrite osup2_ax in H6.
 2:apply isWf_intro; intros; eauto using VN_wf, isOrd_inv.
 assert (x ⊆ VN (x0 ⊔ x1)).
  red; intros.
  apply H4 in H7; revert H7; apply VN_mono_le.
   apply isOrd_inv with y; trivial.
   apply isOrd_osup2; eauto using isOrd_inv.
   apply osup2_incl1; eauto using isOrd_inv.
 assert (y0 ⊆ VN (x0 ⊔ x1)).
  red; intros.
  apply H5 in H8; revert H8; apply VN_mono_le.
   apply isOrd_inv with y; trivial.
   apply isOrd_osup2; eauto using isOrd_inv.
   apply osup2_incl2; eauto using isOrd_inv.
 destruct H6 as [?|[?|(x',?,(y',?,?))]]; auto.
 rewrite H10; apply H1; auto.
 apply osup2_lt; trivial.
Qed.

(*
Let N_TI :
  let f := fun X => union2 (singl zero) (replf X succ) in N ⊆ TI f omega.
intro f.
red; intros.
assert (fm : morph1 f).
 do 2 red; intros.
 apply union2_morph; auto with *.
 apply replf_morph; trivial.
 red; intros; apply succ_morph; trivial.
apply nat2set_reflect in H.
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
 2:do 2 red; intros; apply succ_morph; trivial.
 exists (ZFnats.nat2set x); auto with *.
 apply TI_intro with x0; auto.
  eauto using isOrd_inv.

  apply lt_osucc; eauto using isOrd_inv.
Qed. (* cf ZFgrothendieck *)
*)

Lemma VN_N : N ⊆ VN omega.
red; intros.
elim H using N_ind; simpl; intros.
 rewrite <- H1; trivial.

 apply VN_intro; trivial.
 apply zero_omega.

 unfold succ.
 apply VN_union; trivial.
 apply VNlim_pair; trivial.
 apply VNlim_pair; trivial.
Qed.


Definition VN_regular o :=
  forall x F,
  ext_fun x F ->
  x ∈ VN o ->
  (forall y, y ∈ x -> F y ∈ VN o) ->
  sup x F ∈ VN o.

Definition bound_ord A o :=
  forall F, ext_fun A F ->
  (forall n, n ∈ A -> lt (F n) o) ->
  lt (osup A F) o.



Lemma VN_ord_sup F o :
  isOrd o ->
  VN_regular o ->
  omega ∈ o ->
  (forall n, F n ∈ VN o) ->
  ord_sup F ∈ VN o.
intros.
apply ord_sup_typ; trivial; intros.
apply H0; trivial.
 do 2 red; intros; apply H3; trivial.

 apply VN_incl with (VN omega); trivial.
  apply VN_N.

  apply VN_mono; trivial.
Qed.


Lemma VN_reg_ord : forall o,
  isOrd o -> 
  VN_regular o ->
  omega ∈ o ->
  forall x F,
  ext_fun x F ->
  x ∈ VN o ->
  (forall y, y ∈ x -> lt (F y) o) ->
  lt (osup x F) o.
intros.
apply VN_ord_inv; trivial.
 apply isOrd_osup; eauto using isOrd_inv.

 apply osup_univ; intros; trivial.
  apply isOrd_inv with o; auto.

  apply H0; trivial.

  rewrite VN_def in H5; trivial; destruct H5.
  apply H9 in H7; apply H9 in H8.
  rewrite VN_def; trivial.
  exists x1; trivial.
  red; intros.
  apply singl_elim in H10; rewrite H10; apply VN_osup2; eauto using isOrd_inv.

  apply VN_incl with (VN omega); trivial. (* N ∈ VN o needed ? (cf osup_univ) *)
   apply VN_N.

   apply VN_mono; trivial.

  apply VN_intro; auto.
  apply H4; trivial.
Qed.

Definition VN_inaccessible o :=
  limitOrd o /\ VN_regular o.

Require Import ZFrepl.

Definition VN_regular_rel o :=
  forall x R,
  repl_rel x R ->
  x ∈ VN o ->
  (forall y z, y ∈ x -> R y z -> z ∈ VN o) ->
  union (repl x R) ∈ VN o.

Definition VN_inaccessible_rel o :=
  limitOrd o /\ VN_regular_rel o.

Section UnionClosure.

  Variable mu : set.
  Hypothesis mu_ord : isOrd mu.
  Hypothesis mu_lim : forall x, lt x mu -> lt (osucc x) mu.
  Hypothesis mu_reg : VN_regular_rel mu.
  Hypothesis mu_inf : omega ∈ mu.


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
    x ∈ VN mu -> y ∈ VN mu -> pair x y ∈ VN mu.
intros.
apply VNlim_pair; trivial.
(*apply isDir_regular.*)
Qed.

End UnionClosure.

