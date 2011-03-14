Require Import ZF ZFrelations ZFnats ZFord.
Import IZF.

Section IterMonotone.

  Variable F : set -> set.
  Variable Fmono : Proper (incl_set ==> incl_set) F.

  Instance Fmono_morph: Proper (eq_set ==> eq_set) F.
do 2 red; intros.
apply eq_intro; intros.
 apply Fmono with x; trivial.
 red; intros.
 rewrite <- H; trivial.

 apply Fmono with y; trivial.
 red; intros.
 rewrite H; trivial.
Qed.
Hint Resolve Fmono_morph.

  Lemma TI_mono : increasing (TI F).
do 2 red; intros.
apply TI_elim in H2; intros; auto with *.
destruct H2.
apply TI_intro with x0; auto with *.
apply H1 in H2; trivial.
Qed.

  Lemma TI_incl : forall o, isOrd o ->
    forall o', lt o' o ->
    TI F o' \incl TI F o.
intros.
apply TI_mono; trivial; auto.
 apply isOrd_inv with o; trivial.
 red; intros; apply isOrd_trans with o'; trivial.
Qed.

  Lemma TI_mono_succ : forall o,
    isOrd o ->
    TI F (osucc o) == F (TI F o).
intros.
assert (Fext : ext_fun (osucc o) (fun o' => F (TI F o'))).
 generalize (isOrd_succ _ H); auto.
rewrite TI_eq; auto.
 apply eq_intro; intros.
  rewrite sup_ax in H0; trivial.
  destruct H0.
  apply Fmono with (TI F x); trivial.
  apply TI_mono; trivial.
   apply isOrd_inv with (osucc o); auto.
   apply olts_le; trivial.

 rewrite sup_ax; trivial.
 exists o; trivial.
 apply lt_osucc; trivial.
Qed.

  Lemma TI_mono_eq : forall o,
    isOrd o ->
    TI F o == sup o (fun o' => TI F (osucc o')).
intros.
rewrite TI_eq; auto.
apply sup_morph; auto with *.
red; intros.
rewrite <- TI_mono_succ.
 apply TI_morph.
 rewrite H1; reflexivity.

 apply isOrd_inv with o; trivial.
Qed.

  Lemma TI_pre_fix : forall fx o,
     isOrd o ->
     F fx \incl fx ->
     TI F o \incl fx.
intros.
induction H using isOrd_ind; intros.
red; intros.
apply H0.
elim TI_elim with (3:=H3); intros; auto with *.
apply Fmono with (TI F x); auto.
Qed.

End IterMonotone.


Section KnasterTarski.

Variable A : set.
Variable F : set -> set.

Record fp_props : Prop :=
 { typ : forall x, x \incl A -> F x \incl A;
(*   morph : morph1 F;*)
   mono : forall x x',
     x' \incl A -> x \incl x' -> F x \incl F x'}.

Hypothesis Ffix : fp_props.

Lemma fx_mrph : forall x x', x \incl A -> x == x' -> F x == F x'.
intros.
apply eq_intro; intros.
 revert z H1; apply mono; trivial.
 rewrite <- H0; trivial.
 rewrite H0; auto with *.

 revert z H1; apply mono; trivial.
 rewrite H0; auto with *.
Qed.

Let Ftyp := Ffix.(typ).
Let Fmono := Ffix.(mono).

Definition is_lfp x :=
  F x == x /\ forall y, y \incl A -> F y \incl y -> x \incl y.

Definition pre_fix x := x \incl F x.
Definition post_fix x := F x \incl x.

Lemma post_fix_A : post_fix A.
red; intros.
apply Ftyp; auto with *.
Qed.

Definition M' := subset (power A) post_fix.

Lemma member_A : A \in M'.
unfold M'.
apply subset_intro.
 apply power_intro; auto.

 apply post_fix_A.
Qed.

Lemma post_fix1 : forall x, x \in M' -> F x \incl x.
unfold M'; intros.
elim subset_elim2 with (1:=H); intros.
red; intros.
red in H1. red in H1.
rewrite H0.
apply subset_elim1 in H.
apply H1.
apply Fmono with x; trivial.
 rewrite <- H0; red; intros.
 apply power_elim with x; trivial.

 rewrite H0; auto with *.
Qed.

Definition least_fp := inter M'.

Lemma lfp_typ : least_fp \incl A.
unfold least_fp, M'.
red; intros.
apply inter_elim with (1:=H).
apply subset_intro.
 apply power_intro; auto.

 apply post_fix_A.
Qed.

Lemma lower_bound : forall x, x \in M' -> least_fp \incl x.
unfold least_fp, M'; red; intros.
apply inter_elim with (1:=H0); auto.
Qed.

Lemma post_fix2 : forall x, x \in M' -> F least_fp \incl F x.
intros.
apply Fmono.
 apply subset_elim1 in H.
 red; intros.
 apply power_elim with x; trivial.

 apply lower_bound; trivial.
Qed.


Lemma post_fix_lfp : post_fix least_fp.
red; red; intros.
unfold least_fp.
apply inter_intro.
2:exists A; apply member_A.
intros.
apply post_fix1 with (1:=H0).
apply post_fix2 with (1:=H0).
trivial.
Qed.

Lemma incl_f_lfp : F least_fp \in M'.
unfold M'; intros.
apply subset_intro.
 apply power_intro.
 apply Ftyp.
 apply lfp_typ.

 red; intros.
 apply Fmono.
  apply lfp_typ.

  apply post_fix_lfp; trivial.
Qed.

Lemma knaster_tarski : is_lfp least_fp.
split.
 apply eq_intro; intros.
  apply (post_fix_lfp z H); trivial.

  apply (lower_bound (F least_fp)); trivial.
  apply incl_f_lfp; trivial.

 intros.
 apply lower_bound.
 unfold M'.
 apply subset_intro; trivial.
 apply power_intro; trivial.
Qed.
(*
  Lemma TI_incl_lstfix : forall o,
     isOrd o ->
     TI F o \incl least_fp.
intros.
induction H using isOrd_ind; intros.
red; intros.
apply TI_elim in H2; auto.
2:admit.
destruct H2.
apply post_fix_lfp.
revert z H3.
apply Fmono; auto.
apply lfp_typ.
Qed.

  Definition lstfx' :=
    subset A (fun x => exists2 o, isOrd o & x \in TI F o).

  Lemma pofx' : post_fix lstfx'.
red; red; intros.

unfodl lstfx' in *.
*)

End KnasterTarski.

