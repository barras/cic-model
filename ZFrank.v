Require Import ZF ZFnats ZFwf ZFord ZFstable ZFfix.

(* The rank of a set (defined by ∈-induction) *)
Definition rk := WFR (fun x=>x) (fun f x => osup x (fun x' => osucc (f x'))).

#[global]Instance rk_morph : morph1 rk.
intros ?? h.
apply WFR_morph; auto with *.
*intros ?? h'; trivial.  
*intros ?? h' ?? h''.
 apply osup_morph;[trivial|].
 intros ??? h'''.
 apply osucc_morph; auto.
Qed.

Lemma rk_def X : isWf X -> rk X == osup X (fun x => osucc (rk x)).
intros acc; unfold rk; rewrite WFR_eqn; auto with *; [|rewrite <- isWf_acc;trivial].
intros.
apply osup_morph;[trivial|].
intros ??? h.
apply osucc_morph; auto.
Qed.

(*Lemma rk_in_def x z :
  isWf x ->
  z ∈ rk x <-> exists y, y ∈ x /\ z ∈ power (rk y).
intros.
rewrite rk_def; [|trivial].
  apply (wf_ax
*)
(*Lemma rk_in_def x z :
  z ∈ rk x <-> isWf x /\ exists y, y ∈ x /\ z ∈ power (rk y).
split; intros.
*specialize WFR_non_mt with (1:=H); intro wfx.
 apply isWf_acc in wfx.
 split; [trivial|].
 rewrite rk_def in H; [|trivial].

 osup_elim.
 def
 apply (wf_ax
*)
Lemma rk_isOrd X : isWf X -> isOrd (rk X).
induction 1 using isWf_ind; intros.
rewrite rk_def;[|trivial].
apply isOrd_osup; auto.
intros ??? h.
rewrite h; reflexivity.
Qed.

Local Lemma auxm : forall a, ext_fun a (fun x0 => osucc (rk x0)).
intros ???? h; rewrite h; reflexivity.
Qed.
Hint Resolve auxm : core.

Lemma rk_strict_mono x y : isWf y -> x ∈ y -> rk x ∈ rk y.
intros wfy.
rewrite (rk_def y); [|trivial].
intros; apply osup_intro with x; auto.
apply lt_osucc.
apply rk_isOrd; trivial.
apply isWf_inv with y; trivial.
Qed.

(* Uses foundation axiom *)
Instance rk_mono : Proper (incl_set ==> incl_set) rk.
do 2 red; intros.
assert (wfy : isWf y).
{apply wf_ax; intros; apply isWf_intro; trivial. }
assert (wfx : isWf x).
{eauto using isWf_incl. }
rewrite !rk_def; trivial.
apply osup_lub; intros; auto.
*apply isOrd_osup; auto.
 intros; apply isOrd_succ.
 apply rk_isOrd; eauto using isWf_inv.
*red; intros; apply osup_intro with x0; auto.
Qed. 

(****************************************************************************)
(* Von Neumann universes *)

Definition VN := TI power.

Instance VN_morph : morph1 VN.
do 2 red; intros.
apply TI_morph; trivial.
(*apply power_morph.*)
Qed.

Lemma VN_wf x z : z ∈ VN x -> isWf x.
intros.
apply WFR_non_mt in H.
apply isWf_acc; trivial.
Qed.

  Lemma VN_eq_def x : isWf x -> VN x == sup x (fun y => power (VN y)).
intros; apply WFR_eqn; [auto with *| |rewrite <- isWf_acc; trivial].
intros.
clear H0.
apply sup_morph; trivial.
red; intros.
apply power_morph; auto.
Qed.

  Lemma VN_in_def x z : isWf x -> z ∈ VN x <-> exists2 y, y ∈ x & z ⊆ VN y.
intros.
rewrite VN_eq_def, sup_ax; [|intros ??? h; rewrite h; reflexivity|trivial].
apply ex2_morph; [reflexivity|intro y].
rewrite power_ax; reflexivity.
Qed.

  Lemma VN_in_def' x z : z ∈ VN x <-> isWf x /\ exists2 y, y ∈ x & z ⊆ VN y.
split; intros.
*specialize VN_wf with (1:=H); split; trivial.
 apply VN_in_def; trivial.
*destruct H.
 apply VN_in_def; trivial.
Qed.

  (* restricted to ordinals *)
  Lemma VN_ord_def : forall x z,
    isOrd x ->
    (z ∈ VN x <-> exists2 y, y ∈ x & z ⊆ VN y).
intros; apply VN_in_def.
apply isOrd_wf; trivial.
Qed.

  Lemma VN_trans o x y :
    x ∈ VN o ->
    y ∈ x ->
    y ∈ VN o.
intros.
specialize VN_wf with (1:=H) as wfo.
revert x y H H0; elim wfo using isWf_ind; intros.
clear o wfo.
rewrite VN_in_def in H1|-*; trivial.
destruct H1 as (w,?,?).
exists w; trivial.
red; intros.
apply H0 with y; auto.
Qed.

  Lemma VN_trans' x : trans (fun y => y ∈ VN x).
intros y z.
apply VN_trans.
Qed.
  
  Lemma VN_incl o x y :
    y ⊆ x ->
    x ∈ VN o ->
    y ∈ VN o.
intros.
rewrite VN_in_def' in H0|-*.
destruct H0 as (?,(w,?,?)).
split; [trivial|exists w; auto].
transitivity x; trivial.
Qed.

Lemma VN_plump x : plump (fun y => y ∈ VN x).
red; intros.
apply VN_incl with x0; trivial.
Qed.


(*Instance VN_mono_le : Proper (incl_set ==> incl_set) VN.
do 2 red; intros.
intros z inx.

rewrite !VN_def.
assert (morph1 (fun y => power (VN y))) by (intros ?? h; rewrite h; reflexivity).
rewrite !sup_ax; auto.
intros(w,?,?); exists w; auto.
Qed.
*)
Lemma VN_mono : forall o x,
  isOrd o ->
  lt x o -> VN x ∈ VN o.
intros.
rewrite (VN_ord_def o); trivial.
exists x; auto with *.
Qed.

Lemma VN_mono_le : forall o o',
  isOrd o ->
  isOrd o' ->
  o ⊆ o' ->
  VN o ⊆ VN o'.
red; intros.
rewrite VN_ord_def in H2|-*; trivial.
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
 
Lemma VN_compl x z : z ∈ VN x -> VN z ∈ VN x. 
intros zinx; specialize VN_wf with (1:=zinx); intro wfx.
revert z zinx; induction wfx using isWf_ind; intros.
rewrite VN_in_def in zinx|-*; auto with *.
destruct zinx.
exists x; trivial.
red; intros.
rewrite VN_in_def in H2; auto with *.
*destruct H2.
 apply VN_incl with (VN x0); auto.
*apply VN_wf in H2; trivial.
Qed.

(*
Lemma VN_compl : forall x z, isOrd x -> isOrd z -> z ∈ VN x -> VN z ∈ VN x. 
intros x z xo; revert z.
induction xo using isOrd_ind; intros.
rewrite VN_ord_def in H2|-*; auto with *.
destruct H2.
exists x0; trivial.
red; intros.
rewrite VN_def in H4; auto with *.
destruct H4.
apply VN_incl with (VN x1); eauto using isOrd_inv.
Qed.
*)

Lemma VN_intro x : isWf x -> x ⊆ VN x.
intros wfx; pattern x; elim wfx using isWf_ind; red; intros.
apply VN_in_def; trivial.
exists z; auto.
Qed.

(*Lemma VN_intro :
  forall x, isOrd x -> x ⊆ VN x.
induction 1 using isOrd_ind; red; intros.
rewrite VN_def; trivial.
eauto.
Qed.
*)
Lemma VN_succ : forall x, isOrd x -> power (VN x) == VN (osucc x).
intros.
unfold VN.
symmetry; apply TI_mono_succ; trivial.
apply power_mono.
Qed.


  Lemma VN_ord_inv : forall o x, isOrd o -> isOrd x -> x ∈ VN o -> lt x o.
intros o x xo; revert x.
induction xo using isOrd_ind; intros.
rewrite VN_ord_def in H2; trivial; destruct H2.
apply isOrd_plump with x0; trivial.
red; intros.
apply H0; auto.
apply isOrd_inv with x; trivial.
Qed.
(*
Lemma VN_ord_incl o o' : isOrd o -> isOrd o' -> o' ∈  VN o -> o' ∈ o.
intros oo oo' invn.
revert o' oo' invn; elim oo using isOrd_ind; intros.
clear o oo H0.
apply VN_in_def in invn.
destruct invn as (o,?,?).
apply isOrd_plump with o; auto.
red; intros.
apply H1; eauto using isOrd_inv.
Qed.
*)

  Lemma VN_subset o x P : x ∈ VN o -> subset x P ∈ VN o.
intros.
apply VN_incl with x; trivial.
red; intros.
apply subset_elim1 in H0; trivial.
Qed.

  Lemma VN_union o x : x ∈ VN o -> union x ∈ VN o.
intros.
rewrite VN_in_def' in H|-*; trivial.
destruct H as (?,(y,?,?)); split; [trivial|].
exists y; trivial.
red; intros.
apply union_elim in H2; destruct H2.
apply VN_trans with x0; auto.
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
destruct 1; rewrite VN_ord_def; trivial.
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

Local Transparent ZFpairs.couple ZFpairs.prodcart.
Lemma VNlim_couple o x y :
  limitOrd o ->
  x ∈ VN o ->
  y ∈ VN o ->
  ZFpairs.couple x y ∈ VN o.
intros.
unfold ZFpairs.couple.
apply VNlim_pair; trivial.
 apply VNlim_pair; trivial.
 apply VNlim_pair; trivial.
Qed.
Lemma VNlim_prodcart o A B :
  limitOrd o ->
  A ∈ VN o ->
  B ∈ VN o ->
  ZFpairs.prodcart A B ∈ VN o.
intros.
unfold ZFpairs.prodcart.
assert (oo := proj1 H).
apply VN_subset; trivial.
apply VNlim_power; trivial.
apply VNlim_power; trivial.
apply VN_union; trivial.
apply VNlim_pair; trivial.
Qed.  

Lemma VN_prodcart o A B :
    isOrd o ->
    A ∈ VN o ->
    B ∈ VN o ->
    ZFpairs.prodcart A B ∈ VN (osucc (osucc (osucc o))).
intros.
unfold ZFpairs.prodcart.
apply VN_subset; auto.
apply VNsucc_power; auto.
apply VNsucc_power; auto.
unfold union2.
apply VN_union; auto.
apply VNsucc_pair; trivial.
Qed.
Opaque ZFpairs.couple ZFpairs.prodcart.

Local Transparent func.
Lemma VN_func : forall o A B,
    isOrd o ->
    A ∈ VN o ->
    B ∈ VN o ->
    func A B ∈ VN (osucc (osucc (osucc (osucc o)))).
unfold func; intros.
apply VN_subset; auto.
unfold rel.
apply VNsucc_power; auto.
apply VN_prodcart; trivial.
Qed.
Opaque func.

Require Import ZFwf.
(*
Lemma VN_wf o x : isOrd o -> x ∈ VN o -> isWf x.
intros oo; revert x; induction oo using isOrd_ind.
intros.
apply isWf_intro; intros.
rewrite VN_def in H1; trivial; destruct H1.
apply H3 in H2; eauto.
Qed.
*)
Lemma VN_osup2 o :
  isOrd o ->
  forall x y (xo:isOrd x),
  x ∈ VN o ->
  y ∈ VN o ->
  x ⊔ y ∈ VN o.
induction 1 using isOrd_ind; intros.
rewrite VN_ord_def in H2,H3|-*; trivial.
destruct H2.
destruct H3.
exists (x0 ⊔ x1).
 apply osup2_lt; trivial.

 red; intros.
 rewrite osup2_ax in H6; trivial.
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
 2:apply isOrd_inv with x; trivial.
 apply osup2_lt; trivial.
Qed.

Lemma VN_N : N ⊆ VN omega.
red; intros.
elim H using N_ind; simpl; intros.
 rewrite <- H1; trivial.

 apply VN_intro; auto.

 unfold succ.
 apply VN_union; trivial.
 apply VNlim_pair; trivial.
 apply VNlim_pair; trivial.
Qed.


(*****************************************************************************)
(* Building Zermelo universes (as Von Neuman universe of a limit ordinal) *)

Definition isVNlim X := exists o, limitOrd o /\ X == VN o.
 
Instance isVNlim_morph : Proper (eq_set ==> iff) isVNlim.
unfold isVNlim.
do 2 red; intros.
apply ex_morph; intros o.
apply and_iff_morphism; [reflexivity|].
rewrite H; reflexivity.
Qed.

Lemma VNlim_sup (f : set -> set) :
  ext_fun N f ->
  (forall k, k ∈ N -> isVNlim (f k)) ->
  (forall k, k ∈ N -> f k ⊆ f (succ k)) ->
  isVNlim (sup N f).
intros fext Kf fmono.
pose (frk := fun k => subset (f k) isOrd).
assert (frkext : ext_fun N frk).
{do 2 red; intros.
 apply subset_morph; [auto|].
 red; reflexivity. }
assert (Kf' : forall k, k ∈ N -> limitOrd (frk k) /\ f k == VN (frk k)).
{intros k tyk.
 destruct Kf with (1:=tyk) as (o & lo & eqf).
 assert (frk k == o).
 {apply eq_set_ax; split; intros.
  *apply subset_ax in H.
   destruct H as (?,(x',eqx, xo)).
   rewrite <- eqx in xo.
   eapply VN_ord_inv; [apply lo|trivial|].
   rewrite <- eqf; trivial.
  *apply subset_intro;[|eauto using isOrd_inv].
   rewrite eqf.
   apply VN_intro; auto. }
 rewrite H; auto. }
assert (limfo : forall k, k ∈ N -> limitOrd (frk k)).
{intros; apply Kf'; trivial. }
assert (feq : forall k, k ∈ N -> f k == VN (frk k)).
{intros; apply Kf'; trivial. }
assert (lims : limitOrd (sup N frk)).
{split.
 {apply isOrd_supf; intros; trivial.
 *apply limfo; trivial.
 *exists (max x y); [apply max_typ; trivial|].
  assert (fmono_le : forall x y, x ∈ N -> y ∈ N -> x <= y -> f x ⊆ f y).
  {intros.
   elim H3 using Nle_ind'; trivial; intros.
   *rewrite (fext x0 m'); trivial.
    reflexivity.
   *rewrite <- (fext (succ n) sn'); trivial;[|apply succ_typ; trivial].
    rewrite <- fmono; trivial. } 
  split; red; intros.
  +apply subset_ax in H1.
   destruct H1 as (?,(z',?,?)).
   rewrite <- H2 in H3.
   apply subset_intro;[|trivial].
   revert H1; apply fmono_le; auto.
  +apply subset_ax in H1.
   destruct H1 as (?,(z',?,?)).
   rewrite <- H2 in H3.
   apply subset_intro;[|trivial].
   revert H1; apply fmono_le; auto. }
 {intros.
  rewrite sup_ax in H|-*; trivial.
  destruct H as (k,?,?).
  exists k; trivial.
  apply limfo; trivial. }}
exists (sup N frk); split; [trivial|].
apply eq_set_ax; intros x.
rewrite sup_ax; [|trivial].
split; intros.
*destruct H as (k,?,?).
 apply VN_mono_le with (frk k); auto.
 rewrite <- feq; auto.
*rewrite VN_in_def' in H.
 destruct H as (_,(y,?,?)).
 rewrite sup_ax in H; [|trivial].
 destruct H as (k,?,?).
 exists k; trivial.
 rewrite feq; auto.
 apply VN_incl with (VN y); auto.
 apply VN_mono; auto.
Qed.


Definition VNlim_compl X := VN (next_limOrd (rk X)).

Instance VNlim_compl_mono : Proper (incl_set ==> incl_set) VNlim_compl.
do 2 red; intros.
assert (isOrd (rk x)) by (apply rk_isOrd;  apply wf_ax; apply isWf_intro).
assert (isOrd (rk y)) by (apply rk_isOrd;  apply wf_ax; apply isWf_intro).
apply VN_mono_le.
*apply limOrd_next_limOrd; trivial.
*apply limOrd_next_limOrd; trivial.
*apply next_limOrd_mono; auto using rk_isOrd.
 apply rk_mono; trivial.
Qed.


Lemma VN_rk_ext X : isWf X -> X ⊆ VN (rk X).
intros wfX z inX.
revert z inX; induction wfX using isWf_ind; intros.
rewrite VN_ord_def;[|apply rk_isOrd;trivial].
exists (rk z); auto.
*rewrite rk_def with (X:=a);[|trivial].
 apply osup_intro with (x:=z); trivial.
 apply lt_osucc; apply rk_isOrd.
 apply isWf_inv with a; trivial.
*red; auto.
Qed.

Lemma VNlim_ext X : isWf X -> X ⊆ VNlim_compl X.
red; intros.
unfold VNlim_compl.
assert (isOrd (rk X)) by (auto using rk_isOrd).
apply VN_mono_le with (rk X); auto.
*apply limOrd_next_limOrd; auto.
*red; intros.
 apply isOrd_trans with (rk X); auto.
 apply limOrd_next_limOrd; auto.
 apply next_limOrd_intro1; trivial.
*apply VN_rk_ext; trivial.
Qed.

Lemma VNlim_compl_ok X : isWf X -> isVNlim (VNlim_compl X).
exists (next_limOrd (rk X)); split;[|reflexivity].
apply limOrd_next_limOrd; auto.
apply rk_isOrd; trivial.
Qed.





(**********************************************************************)

Section VN_Universes.

  Variable U : set.

  Hypothesis U_trans : forall x y, y ∈ x -> x ∈ U -> y ∈ U.
  Hypothesis U_pair : forall x y, x ∈ U -> y ∈ U -> pair x y ∈ U.
  Hypothesis U_union : forall x, x ∈ U -> union x ∈ U.
  Hypothesis U_power : forall x, x ∈ U -> power x ∈ U.

  Lemma U_incl : forall x y, y ⊆ x -> x ∈ U -> y ∈ U.
intros.
apply U_trans with (power x); auto.
apply power_intro; trivial.
Qed.
  
(*  Hypothesis U_incl : forall x y, y ⊆ x -> x ∈ U -> y ∈ U.*)

  Definition VN_ord := subset U isOrd.

  Lemma VN_ord_ax z : z ∈ VN_ord <-> z ∈ U /\ isOrd z.
unfold VN_ord; rewrite subset_ax.
apply and_iff_morphism; [reflexivity|].
apply exists_eq_intro; intros.
rewrite H; reflexivity.
Qed.
(*
  Lemma U_osup2 x y : isOrd x -> isOrd y -> x ∈ U -> y ∈ U -> x⊔y ∈ U.
    Admitted.

    Lemma VN_osup2' o :
  isOrd o ->
  forall x y,
  x ∈ o ->
  y ∈ o ->
  x ∈ U ->
  y ∈ U ->
  x ⊔ y ∈ U.
induction 1 using isOrd_ind; intros.
assert (xo : isOrd x) by eauto using isOrd_inv.
assert (yo : isOrd y0) by eauto using isOrd_inv.
rewrite osup2_def; trivial.
apply U_union; apply U_pair.
 apply U_union; apply U_pair; trivial.

rewrite VN_def in H2,H3|-*; trivial.
destruct H2.
destruct H3.
exists (x0 ⊔ x1).
 apply osup2_lt; trivial.

 red; intros.
 rewrite osup2_ax in H6; trivial.
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
 2:apply isOrd_inv with x; trivial.
 apply osup2_lt; trivial.
Qed. *)
(*
  Lemma isOrd_VN_ord : isOrd VN_ord.
apply isOrd_intro; intros.
*rewrite VN_ord_ax in H1|-*.
 destruct H1.
 split; trivial.
 apply U_incl with b; trivial.
*red; intros.
 rewrite VN_ord_ax in H,H0.
 destruct H; destruct H0.
 exists (x⊔y); [|split;[apply osup2_incl1|apply osup2_incl2];trivial].
 rewrite VN_ord_ax; split; [|apply isOrd_osup2;trivial].
 apply U_osup2; trivial.
*rewrite VN_ord_ax in H; destruct H; trivial.
Qed.
 *)
  
End VN_Universes.

(* Regularity and inaccessible cardinals.  *)
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
  ext_fun N F ->
  isOrd o ->
  VN_regular o ->
  omega ∈ o ->
  (forall n, n ∈ N -> F n ∈ VN o) ->
  ord_sup F ∈ VN o.
intros Fext oo oreg oinf H.
apply ord_sup_typ; trivial; intros.
apply oreg; trivial.
 apply VN_incl with (VN omega); trivial.
  apply VN_N.

  apply VN_mono; trivial.
Qed.


Lemma VN_reg_ord : forall o,
  isOrd o -> 
  VN_regular o ->
  omega ∈ o ->
  forall x F (xo:isOrd x),
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

  rewrite VN_ord_def in H5; trivial; destruct H5.
  apply H9 in H7; apply H9 in H8.
  rewrite VN_ord_def; trivial.
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
unfold sup.
rewrite replf_def; trivial.
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


Lemma isWf_VN X : isWf X -> isWf (VN X).
induction 1 using isWf_ind.
rewrite VN_eq_def;[|trivial].
apply isWf_union.
apply isWf_intro; intros.
rewrite replf_ax in H1; auto with *.
destruct H1 as (b,?,?).
rewrite H2.
apply isWf_power; auto.
Qed.
Hint Resolve isWf_VN : core.

Lemma rk_VN o : isOrd o -> rk (VN o) == o.
intros oo; elim oo using isOrd_ind; intros.
clear H0 o oo.  
rewrite rk_def; auto.
apply incl_eq.
*apply osup_lub; intros; auto.
 rewrite VN_in_def' in H0.
 destruct H0 as (wfy,(z,?,?)).
 assert (isWf (VN z)).
 {apply isWf_VN.
  apply isWf_inv with y; trivial. }
 transitivity (osucc (rk (VN z))).
 +apply osucc_mono; eauto using rk_isOrd, isWf_incl.
  apply rk_mono; auto.
 +rewrite H1; trivial.
  red; intros.
  apply isOrd_plump with z; auto.
   apply isOrd_inv with (osucc z); auto.
   apply isOrd_succ; auto.
   apply isOrd_inv with y; trivial.
   apply olts_le; trivial.
*red; intros.
 assert (isOrd z) by eauto using isOrd_inv.
 apply osup_intro with (VN z); auto.
 +apply VN_compl; auto.
  apply VN_intro; auto.
 +rewrite H1; trivial.
  apply lt_osucc; auto.
Qed. 
