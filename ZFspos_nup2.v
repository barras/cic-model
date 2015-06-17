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
  dp_oper : (set -> set) -> set;
  w1 : set;
  w2 : set -> set;
  w3 : set -> set -> set;
  dp_iso : set -> set
}.

Class eqdpos (p1 p2: dpositive) := {
  eq_dop : ((eq_set==>eq_set)==>eq_set)%signature (dp_oper p1) (dp_oper p2);
  eq_dw1 : w1 p1 == w1 p2;
  eq_dw2 : (eq_set==>eq_set)%signature (w2 p1) (w2 p2);
  eq_dw3 : (eq_set==>eq_set==>eq_set)%signature (w3 p1) (w3 p2);
  eq_diso : (eq_set==>eq_set)%signature (dp_iso p1) (dp_iso p2)
}.

Instance eqdpos_sym : Symmetric eqdpos.
red; intros.
split; repeat red; symmetry; apply H; symmetry; trivial.
Qed.

Instance eqdpos_trans : Transitive eqdpos.
red; intros.
split; repeat red; intros; (eapply transitivity; [apply H|apply H0]); eauto with *.
transitivity x0; trivial.
symmetry; trivial.
Qed.
 
Class isPositive (p:dpositive) := {
  prefl : eqdpos p p;
  dpmo : forall X Y, morph1 X -> morph1 Y -> incl_fam Arg X Y -> dp_oper p X ⊆ dp_oper p Y;
  w3ty : forall x i, x ∈ w1 p -> i ∈ w2 p x -> w3 p x i ∈ Arg;
  dpiso : forall  X, morph1 X ->
    iso_fun (dp_oper p X) (W0.W_Fd (fun _ => w1 p) (fun _ => w2 p) (fun _ => w3 p) X empty)
      (dp_iso p)
}.
Existing Instance prefl.

Section InstancesPos.

  Variable p : dpositive.
  Hypothesis posp : isPositive p.

 Instance opm : Proper ((eq_set ==> eq_set) ==> eq_set) (dp_oper p).
do 3 red; intros.
apply posp; trivial.
Qed.

 Instance ww2m : morph1 (w2 p).
do 3 red; intros.
apply posp; trivial.
Qed.

 Instance ww3m : morph2 (w3 p).
do 4 red; intros.
apply posp; trivial.
Qed.

 Instance pm : morph1 (dp_iso p).
do 3 red; intros.
apply posp; trivial.
Qed.

End InstancesPos.
Existing Instance opm.
Existing Instance pm.
Existing Instance ww2m.
Existing Instance ww3m.


  (** The predicativity condition: the operator remains within U.
     We also need the invariant that w1 and w2 also belong to the universe U
   *)
  Record pos_universe U p := {
    G_dp_oper : forall X, morph1 X -> typ_fun X Arg U -> dp_oper p X ∈ U;
    G_w1 : w1 p ∈ U;
    G_w2 : forall x, x ∈ w1 p -> w2 p x ∈ U
  }.


Notation dp_oper' p := (fun X a => dp_oper (p a) X).
Notation w1' p := (fun a => w1 (p a)).
Notation w2' p := (fun a => w2 (p a)).
Notation w3' p := (fun a => w3 (p a)).

Class isDPositive (p:set->dpositive) := {
  eqdpos_refl : Proper (eq_set==>eqdpos) p;
  dpmono : mono_fam Arg (dp_oper' p);
  w3typ : forall a x i, a ∈ Arg -> x ∈ w1 (p a) -> i ∈ w2 (p a) x -> w3 (p a) x i ∈ Arg;
  dpm_iso : forall a X, a ∈ Arg -> morph1 X ->
    iso_fun (dp_oper (p a) X) (W0.W_Fd (w1' p) (w2' p) (w3' p) X a)
      (dp_iso (p a))
}.

Lemma isDP_intro p :
  Proper (eq_set==>eqdpos) p ->
  (forall a, a ∈ Arg -> isPositive (p a)) ->
  isDPositive p.
split; auto.
 do 2 red; intros.
 assert (h := H0 _ H4).
 apply dpmo; trivial.

 intros.
 assert (h := H0 _ H1).
 apply w3ty; trivial.

 intros.
 assert (h := H0 _ H1).
 apply dpiso; trivial.
Qed.

Lemma isDP_elim p :
  isDPositive p ->
  (forall a, a ∈ Arg -> isPositive (p a)).
split; intros.
 apply H; reflexivity.

 apply H; trivial.

 apply H; trivial.

 apply H; trivial.
Qed.


Existing Instance  eqdpos_refl.
Hint Resolve dpmono.

Section Instances.

  Variable p : set->dpositive.
  Hypothesis posp : isDPositive p.


 Instance dopm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) (dp_oper' p).
do 3 red; intros.
apply posp; trivial.
Qed.

 Instance w1m : morph1 (w1' p).
do 2 red; intros.
apply posp; trivial.
Qed.

 Instance w2m : morph2 (w2' p).
do 3 red; intros.
apply posp; trivial.
Qed.

 Instance w3m : Proper (eq_set==>eq_set==>eq_set==>eq_set) (w3' p).
do 4 red; intros.
apply posp; trivial.
Qed.

 Instance dpm : morph2 (fun a => dp_iso (p a)).
do 3 red; intros.
apply posp; trivial.
Qed.
(*
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

Existing Instance dopm.
Existing Instance dpm.
Existing Instance w1m.
Existing Instance w2m.
Existing Instance w3m.

Instance eqdpos_refl p :
  isDPositive p -> eqdpos p p.
split.
 apply dopm.
 apply w1m.
 apply w2m.
 apply w3m.
 apply dpm.
Qed.
*)
End Instances.
Existing Instance dopm.
Existing Instance dpm.
Existing Instance w1m.
Existing Instance w2m.
Existing Instance w3m.



Definition dINDi p := TIF Arg (dp_oper' p).

Instance dINDi_morph p : morph2 (dINDi p).
do 3 red; intros.
unfold dINDi.
apply TIF_morph; trivial.
Qed.

Lemma dINDi_succ_eq : forall p o a,
  isDPositive p -> isOrd o -> a ∈ Arg -> dINDi p (osucc o) a == dp_oper (p a) (dINDi p o).
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

Definition dIND_clos_ord (p:set->dpositive) := W0.W_ord Arg (w1' p) (w2' p).

Lemma isOrd_clos_ord p : isDPositive p -> isOrd (dIND_clos_ord p).
intros.
unfold dIND_clos_ord.
apply W0.W_o_o; auto with *.
Qed.
Hint Resolve isOrd_clos_ord.

Definition dIND (p:set->dpositive) a := dINDi p (dIND_clos_ord p) a.

Instance dIND_morph p : isDPositive p -> morph1 (dIND p).
intros.
do 2 red; intros.
unfold dIND.
apply dINDi_morph; auto with *.
Qed.

Let wiso p f a :=
  comp_iso (dp_iso (p a)) (W0.W_Fd_map (w2' p) (w3' p) f a).

Instance wisom : forall p, isDPositive p -> 
 Proper ((eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set ==> eq_set) (wiso p).
do 4 red; intros.
unfold wiso.
unfold comp_iso.
apply W0.W_Fd_map_morph; trivial.
 apply w2m; trivial.
 apply w3m; trivial.
 apply dpm; trivial.
Qed.

Lemma wiso_iso : forall p X Y f,
  isDPositive p ->
  morph1 X ->
  morph1 Y ->
  morph2 f ->
  (forall a, a ∈ Arg -> iso_fun (X a) (Y a) (f a)) ->
  forall a, a ∈ Arg ->
   iso_fun (W0.W_Fd (w1' p) (w2' p) (w3' p) X a)
     (W0.W_Fd (w1' p) (w2' p) (w3' p) Y a) (W0.W_Fd_map (w2' p) (w3' p) f a).
intros.
apply W0.W_Fd_map_iso with (Arg:=Arg); auto with *.
apply w3typ.
Qed.

Lemma wiso_iso' : forall p X Y f,
  isDPositive p ->
  morph1 X ->
  morph1 Y ->
  morph2 f ->
  (forall a, a ∈ Arg -> iso_fun (X a) (Y a) (f a)) ->
  forall a, a ∈ Arg ->
  iso_fun (dp_oper (p a) X) (W0.W_Fd (w1' p) (w2' p) (w3' p) Y a) (wiso p f a).
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
   a0 ∈ Arg -> eq_fun (dp_oper (p a0) X) (wiso p f a0) (wiso p f' a0).
red; intros.
unfold wiso, comp_iso, W0.W_Fd_map.
apply couple_morph.
 apply fst_morph.
 apply dpm; auto with *.

 apply cc_lam_ext.
  apply w2m; auto with *.
  apply fst_morph.
  apply dpm; auto with *.
 red; intros.
 red in H3.
 assert (eq3: w3 (p a0) (fst (dp_iso (p a0) x)) x0 == w3 (p a0) (fst (dp_iso (p a0) x')) x'0).
  apply w3m; auto with *.
  apply fst_morph.
  apply dpm; auto with *.
 rewrite <- eq3.
 assert (ty : dp_iso (p a0) x ∈ W0.W_Fd (w1' p) (w2' p) (w3' p) X a0).
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

Let isow p := TIF_iso Arg (dp_oper' p) (wiso p).

Let isowm p o : isDPositive p -> morph2 (isow p o).
do 3 red; intros.
unfold isow.
apply TIF_iso_morph; auto with *.
 apply dopm; trivial.

 apply wisom; trivial.
Qed.

Lemma wiso_proof p o :
  isDPositive p ->
  isOrd o -> 
  (forall a,
   a ∈ Arg ->
   iso_fun (TIF Arg (dp_oper' p) o a) (W0.Wi Arg (w1' p) (w2' p) (w3' p) o a) (isow p o a)) /\
  (forall a x,
   a ∈ Arg ->
   x ∈ TIF Arg (dp_oper' p) o a ->
   isow p o a x == wiso p (isow p o) a x) /\
  (forall a o' x, isOrd o' -> o' ⊆ o -> a ∈ Arg -> x ∈ TIF Arg (dp_oper' p) o' a ->
   isow p o' a x == isow p o a x).
intros.
apply TIF_iso_fun; auto.
 apply dopm; trivial.

 apply W0.W_Fd_morph; auto with *.

 apply W0.W_Fd_mono; auto with *.
 apply w3typ; trivial.

 apply wisom; trivial.

 intros.
 apply wiso_ext; trivial.

 intros.
 apply wiso_iso'; trivial.
Qed.

Definition dIND_clos_ord_a (p:set->dpositive) a := W0.W_ord_a Arg (w1' p) (w2' p) (w3' p) a.
Lemma isOrd_clos_ord_a p a : isDPositive p -> a ∈ Arg -> isOrd (dIND_clos_ord_a p a).
unfold dIND_clos_ord_a.
intros.
apply W0.isOrd_W_ord_a; trivial.
 apply w2m; trivial.
Qed.

Lemma dIND_small p a :
 isDPositive p ->
 a ∈ Arg ->
 dIND p a == dINDi p (W0.W_ord_a Arg (w1' p) (w2' p) (w3' p) a) a.
intros.
unfold dIND, dINDi.
assert (tmp := W0.W_eqn_a).
symmetry.
destruct wiso_proof with (1:=H) (2:=isOrd_clos_ord _ H) as (iso_hyp&iso_eqn&iso_indep).
destruct wiso_proof with (1:=H) (2:=isOrd_clos_ord_a _ _ H H0) as (iso_hyp'&iso_eqn'&iso_indep').
apply iso_fun_inj with (f:=isow p (dIND_clos_ord p) a)
  (Y:=W0.Wi Arg (w1' p) (w2' p) (w3' p) (dIND_clos_ord p) a).
 unfold dIND_clos_ord.
 fold (W0.W Arg (w1' p) (w2' p) (w3' p) a).
 generalize (iso_hyp' _ H0).
 apply iso_fun_ext.
  apply isowm; auto with *.
  reflexivity.
  rewrite W0.W_eqn_a; auto with *.
   reflexivity.
   apply w3typ.
  red; intros.
  transitivity (isow p (dIND_clos_ord_a p a) a x').
   apply isowm; auto with *.
   fold (dIND_clos_ord p).
   apply iso_indep.
    apply isOrd_clos_ord_a; trivial.
(*    trivial.
    apply W0.W_o_o; auto with *.*)
    unfold dIND_clos_ord_a.
    unfold dIND_clos_ord.
    apply W0.W_ord_a_smaller; trivial.
     apply w1m; trivial.
     apply w2m; trivial.
     apply w3m; trivial.
     apply w3typ; trivial.
    trivial.
    rewrite <- H2; trivial.
 generalize (iso_hyp _ H0).
 apply iso_fun_ext.
  apply isowm; auto with *.
  reflexivity.
  reflexivity.
  red; intros.
  apply isowm; auto with *.
apply TIF_mono.
 apply dopm; trivial.
 apply dpmono; trivial.
 trivial.
 apply isOrd_clos_ord; trivial.
 apply W0.isOrd_W_ord_a.
  apply w2m; trivial.
unfold dIND_clos_ord.
    apply W0.W_ord_a_smaller; trivial.
     apply w1m; trivial.
     apply w2m; trivial.
     apply w3m; trivial.
     apply w3typ; trivial.
Qed.

Lemma dIND_eq : forall p a, isDPositive p -> a ∈ Arg -> dIND p a == dp_oper' p (dIND p) a.
intros.
assert (tmp := isowm _ (dIND_clos_ord p) H).
destruct wiso_proof with (1:=H) (2:=isOrd_clos_ord _ H) as (iso_hyp&iso_eqn&_).
apply iso_fun_inj with (f:=wiso p (isow p (dIND_clos_ord p)) a)
  (Y:=W0.Wi Arg (w1' p) (w2' p) (w3' p) (dIND_clos_ord p) a).
 unfold W0.Wi, dIND.
 unfold dINDi.
 generalize (iso_hyp _ H0).
 apply iso_fun_ext.
  apply wisom; auto with *.

  reflexivity.
  reflexivity.

  red; intros.
  rewrite (tmp _ _ (reflexivity a) _ _ H2).
  apply iso_eqn; trivial.
  rewrite <- H2; trivial.

 unfold dIND_clos_ord.
 fold (W0.W Arg (w1' p) (w2' p) (w3' p) a).
 apply iso_change_rhs with  (W0.W_Fd  (w1' p) (w2' p) (w3' p) (W0.W Arg (w1' p) (w2' p) (w3' p)) a).
  symmetry; apply W0.W_eqn; auto with *.
  apply w3typ.
 apply wiso_iso'; trivial.
  auto with *.

  apply W0.W_morph_all; auto with *.
   apply w1m; trivial.
   apply w2m; trivial.
   apply w3m; trivial.

 unfold dIND, dINDi.
 rewrite <- TIF_mono_succ with (F:=dp_oper' p); auto with *.
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
change (dp_oper (p a0) (dIND p) ⊆ dIND p a0).
rewrite <- dIND_eq; trivial.
reflexivity.
Qed.

(** * Universe constraints: predicativity *)

Require Import ZFgrothendieck.

  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : omega ∈ U.

  Let Unonmt : empty ∈ U.
apply G_trans with omega; trivial.
apply zero_omega.
Qed.

Section Universes.

  Variable p : set->dpositive.
  Hypothesis p_ok : isDPositive p.

  Definition dpos_universe U p := forall a, a ∈ Arg -> pos_universe U (p a).

  Hypothesis p_univ : dpos_universe U p.


  Lemma G_dIND a : a ∈ Arg -> dIND p a ∈ U.
unfold dpos_universe in p_univ.
intros aty.
rewrite dIND_small; trivial.
unfold dINDi.
apply G_TIF; trivial.
 apply dopm; trivial.

 apply p_ok.

 intros.
 apply G_dp_oper; auto.

 apply W0.isOrd_W_ord_a.
  apply w2m; trivial.

 apply W0.G_W_ord_a; trivial.
  apply w1m; trivial.
  apply w2m; trivial.
  apply w3m; trivial.
  apply w3typ; trivial.

  apply p_univ.

  intros.
  apply p_univ; trivial.
Qed.

  Lemma G_dINDi o a : isOrd o -> a ∈ Arg -> dINDi p o a ∈ U.
intros.
apply G_incl with (dIND p a); trivial.
 apply G_dIND; trivial.

 apply dINDi_dIND; trivial.
Qed.


End Universes.


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
  sigma_1r_iso (fun _ => λ _ ∈ empty, empty).

Lemma iso_cst : forall A X i,
  iso_fun A (W0.W_Fd (fun _ => A) (fun _ _ => empty) (fun i _ _ => i) X i) trad_cst.
intros.
unfold trad_cst, W0.W_Fd.
apply sigma_iso_fun_1_r'; intros; auto with *.
 do 2 red; reflexivity.
apply cc_prod_iso_fun_0_l'.
Qed.

Definition dpos_cst A :=
  mkDPositive (fun _ => A) A (fun a => empty) (fun _ _ => empty) trad_cst.

Instance dpos_cst_morph : Proper (eq_set==>eqdpos) dpos_cst.
constructor; repeat red; simpl; intros; auto with *.
apply couple_morph;[|apply cc_lam_morph;[|red;intros]]; auto with *.
Qed.

Lemma isPos_cst A : isPositive (dpos_cst A).
constructor; simpl; intros; auto with *.
 apply dpos_cst_morph; reflexivity.

 apply empty_ax in H0; contradiction.

 apply iso_cst.
Qed.

Lemma isUPos_cst A : A ∈ U -> pos_universe U (dpos_cst A).
split; simpl; auto.
Qed.


Definition dpos_inst j i :=
  dpos_cst (P2p (i==j)).

Instance dpos_inst_morph : Proper (eq_set==>eq_set==>eqdpos) dpos_inst.
do 3 red; intros.
apply dpos_cst_morph; trivial.
rewrite H,H0; reflexivity.
Qed.

Lemma isDPos_inst j i : isPositive (dpos_inst j i).
unfold dpos_inst.
apply isPos_cst.
Qed.

Lemma isUPos_inst j i : pos_universe U (dpos_inst i j).
split; simpl; auto.
 intros.
 apply G_trans with props; trivial.
  apply P2p_typ.
  apply G_power; trivial.
  apply G_singl; trivial.

 apply G_trans with props; trivial.
  apply P2p_typ.
  apply G_power; trivial.
  apply G_singl; trivial.
Qed.

Definition trad_reccall :=
  comp_iso (fun x => λ _ ∈ singl empty, x) (couple empty).

(*Lemma iso_reccall : forall X j i,
  morph1 X ->
  morph1 j ->
  iso_fun (X (j i)) (W0.W_Fd (fun _ => singl empty) (fun _ _ => singl empty) (fun i _ _ => j i) X i)
    trad_reccall.
intros.
unfold trad_reccall, W0.W_Fd.
eapply iso_fun_trans.
2:apply sigma_iso_fun_1_l'; auto.
apply cc_prod_iso_fun_1_l' with (F:=fun _ => X (j i)).
reflexivity.
Qed.
*)
Definition dpos_rec j :=
  mkDPositive (fun X => X j) (singl empty) (fun _ => singl empty) (fun _ _ => j)
    trad_reccall.

Instance dpos_rec_morph : Proper (eq_set==>eqdpos) dpos_rec.
split; repeat red; simpl; intros; auto with *.
apply couple_morph;[|apply cc_lam_morph;[|red;intros]]; auto with *.
Qed.

Lemma isDPos_rec j : j ∈ Arg -> isPositive (dpos_rec j).
constructor; simpl; intros; auto.
 apply dpos_rec_morph; reflexivity.

 apply iso_reccall; trivial.
Qed.

Lemma isUPos_rec j : j ∈ Arg -> pos_universe U (dpos_rec j).
constructor; simpl; intros; auto.
 apply G_singl; trivial.
 apply G_singl; trivial.
Qed.

Require Import ZFsum.
(*
Lemma cc_prod_sum_case_commut A1 A2 B1 B2 Y1 Y2 x:
  morph2 Y1 ->
  morph2 Y2 ->
  x ∈ sum A1 A2 ->
  sum_case (fun x => cc_prod (B1 x) (Y1 x)) (fun x => cc_prod (B2 x) (Y2 x)) x ==
  cc_prod (sum_case B1 B2 x) (fun i => sum_case (fun x => Y1 x i) (fun x => Y2 x i) x).
intros.
apply sum_ind with (3:=H1); intros.
 rewrite sum_case_inl0; eauto.
 apply cc_prod_ext.
  rewrite sum_case_inl0.
   reflexivity.
  exists x0; trivial.

  red; intros.
  rewrite sum_case_inl0; eauto.
  rewrite <- H5; auto with *.

 rewrite sum_case_inr0; eauto.
 apply cc_prod_ext.
  rewrite sum_case_inr0.
   reflexivity.
  exists y; trivial.

  red; intros.
  rewrite sum_case_inr0; eauto.
  rewrite <- H5; auto with *.
Qed.
*)

Definition trad_sum f g :=
  comp_iso (sum_isomap f g) sum_sigma_iso.

(*Lemma iso_trad_sum F G X a :
  morph1 X ->
  isDPositive F ->
  isDPositive G  ->
  a ∈ Arg -> 
  iso_fun (sum (dp_oper F X a) (dp_oper G X a))
     (W0.W_Fd (fun a => sum (w1 F a) (w1 G a))
        (fun a => sum_case (w2 F a) (w2 G a))
        (fun a x i => sum_case (fun x : set => w3 F a x i)
                               (fun x : set => w3 G a x i) x) X a)
     (trad_sum (@dp_iso F a) (@dp_iso G a)).
intros.
unfold W0.W_Fd, trad_sum.
eapply iso_fun_trans.
 apply sum_iso_fun_morph;[apply H0|apply H1]; trivial.

 eapply iso_change_rhs.
 2:apply iso_fun_sum_sigma; auto.
 apply sigma_ext; auto with *.
 intros.
 rewrite cc_prod_sum_case_commut with (3:=H3).
  apply cc_prod_ext.
   apply sum_case_morph; auto with *.
    apply w2m; trivial; reflexivity.
    apply w2m; trivial; reflexivity.
  red; intros.
  apply sum_ind with (3:=H3); intros.
   rewrite H8 in H4; symmetry in H4.
   rewrite sum_case_inl0; eauto.
   rewrite sum_case_inl0; eauto.
   apply H.
   apply w3m; auto with *.
   rewrite H4,H8; reflexivity.

   rewrite H8 in H4; symmetry in H4.
   rewrite sum_case_inr0; eauto.
   rewrite sum_case_inr0; eauto.
   apply H.
   apply w3m; auto with *.
   rewrite H4,H8; reflexivity.

  do 3 red; intros.
  apply H; apply w3m; auto with *.

  do 3 red; intros.
  apply H; apply w3m; auto with *.

 do 2 red; intros.
 apply cc_prod_ext.
  apply w2m; auto with *.
 red; intros.
 apply H; apply w3m; auto with *.

 do 2 red; intros.
 apply cc_prod_ext.
  apply w2m; auto with *.
 red; intros.
 apply H; apply w3m; auto with *.
Qed.
*)

Definition dpos_sum (F G:dpositive) :=
  mkDPositive
    (fun X => sum (dp_oper F X) (dp_oper G X))
    (sum (w1 F) (w1 G))
    (sum_case (w2 F) (w2 G))
    (fun x i => sum_case (fun x => w3 F x i) (fun x => w3 G x i) x)
    (trad_sum (dp_iso F) (dp_iso G)).

Instance dpos_sum_morph : Proper (eqdpos ==> eqdpos ==> eqdpos) dpos_sum.
split; repeat red; simpl; intros.
 apply sum_morph; apply eq_dop; trivial.

 apply sum_morph; apply eq_dw1; trivial.

 apply sum_case_morph; trivial; apply eq_dw2; trivial.

 apply sum_case_morph; trivial.
  red; intros; apply eq_dw3; trivial.
  red; intros; apply eq_dw3; trivial.

 unfold trad_sum, comp_iso, sum_sigma_iso.
 apply sum_case_morph.
  red; intros.
  rewrite H2; reflexivity.
  red; intros.
  rewrite H2; reflexivity.

  unfold sum_isomap.
  apply sum_case_morph; auto.
   red; intros.
   apply inl_morph; apply H; trivial.

   red; intros.
   apply inr_morph; apply H0; trivial.
Qed.

Lemma isDPos_sum F G :
  isPositive F ->
  isPositive G ->
  isPositive (dpos_sum F G).
intros Fp Gp.
constructor; simpl; intros.
 apply dpos_sum_morph; auto with *.

 apply sum_mono.
  apply dpmo; trivial.
  apply dpmo; trivial.

 apply sum_case_ind0 with (2:=H).
  do 2 red; intros.
  rewrite H1; reflexivity.

  intros.
  apply w3ty; trivial.
   rewrite H2; rewrite dest_sum_inl; trivial.

   rewrite H2 in H0|-*.
   rewrite dest_sum_inl.
   rewrite sum_case_inl in H0; auto with *.

  intros.
  apply w3ty; trivial.
   rewrite H2; rewrite dest_sum_inr; trivial.

   rewrite H2 in H0|-*.
   rewrite dest_sum_inr.
   rewrite sum_case_inr in H0; auto with *.

(* apply iso_trad_sum; trivial.*)
clear; admit.
Qed.

Lemma isUPos_sum F G :
  isPositive F ->
  isPositive G ->
  pos_universe U F ->
  pos_universe U G ->
  pos_universe U (dpos_sum F G).
intros pF pG UF UG.
split; simpl; intros.
 apply G_sum; trivial.
  apply UF; trivial.
  apply UG; trivial.

 apply G_sum; trivial.
  apply UF; trivial.
  apply UG; trivial.

 apply G_sumcase with (3:=H).
  apply ww2m; trivial.
  apply ww2m; trivial.
  apply UF.
  apply UG.
Qed.

(*
Lemma iso_prodcart : forall X1 X2 A1 A2 B1 B2 f1 f2 Y f g a,
   morph1 Y ->
   a ∈ Arg ->
   morph1 (B1 a) ->
   morph1 (B2 a) ->
   morph2 (f1 a) ->
   morph2 (f2 a) ->
   iso_fun X1 (W0.W_Fd A1 B1 f1 Y a) f ->
   iso_fun X2 (W0.W_Fd A2 B2 f2 Y a) g ->
   iso_fun (prodcart X1 X2)
     (W0.W_Fd (fun a => prodcart (A1 a) (A2 a))
     (fun a x => sum (B1 a (fst x)) (B2 a (snd x)))
     (fun a x => sum_case (f1 a (fst x)) (f2 a (snd x))) Y a)
     (trad_prodcart (B1 a) (B2 a) f g).
intros.
unfold W0.W_Fd, ZFspos.trad_prodcart.
eapply iso_fun_trans.
 apply prodcart_iso_fun_morph; [apply H5|apply H6].
assert (m1 : ext_fun (A1 a) (fun x => cc_prod (B1 a x) (fun i => Y (f1 a x i)))).
 do 2 red; intros.
 apply cc_prod_ext; auto with *.
 red; intros.
 apply H.
 apply H3; auto with *.
assert (m1' : ext_fun (A2 a) (fun x => cc_prod (B2 a x) (fun i => Y (f2 a x i)))).
 do 2 red; intros.
 apply cc_prod_ext; auto with *.
 red; intros.
 apply H.
 apply H4; auto with *.
assert (m2: ext_fun (prodcart (A1 a) (A2 a)) (fun x => sum (B1 a (fst x)) (B2 a (snd x)))).
 do 2 red; intros.
 apply sum_morph.
  apply H1.
  rewrite H8; reflexivity.
  apply H2.
  rewrite H8; reflexivity.
eapply iso_fun_trans.
 apply iso_fun_prodcart_sigma; auto.

 apply sigma_iso_fun_morph; auto.
  do 2 red; intros.
  apply prodcart_morph.
   apply m1.
    apply fst_typ in H7; trivial.
    apply fst_morph; trivial.
   apply m1'.
    apply snd_typ in H7; trivial.
    apply snd_morph; trivial.

  do 2 red; intros.
  apply cc_prod_ext; auto.
  red; intros.
  apply H.
  apply sum_case_morph; auto.
   apply H3.
   apply fst_morph; trivial.
   apply H4.
   apply snd_morph; trivial.

  do 3 red; intros.
  apply prodcart_cc_prod_iso_morph; auto with *.
  rewrite H7; reflexivity.

  apply id_iso_fun.

  intros.
  eapply iso_change_rhs.
  2:apply iso_fun_prodcart_cc_prod; auto.
  apply cc_prod_ext; auto.
  red; intros.
  apply sum_case_ind0 with (2:=H9); auto with *.
   do 2 red; intros.
   rewrite H11; reflexivity.

   intros.
   rewrite H12 in H10; symmetry in H10.
   rewrite sum_case_inl0; eauto.
   rewrite H10,H8,H12; reflexivity.

   intros.
   rewrite H12 in H10; symmetry in H10.
   rewrite sum_case_inr0; eauto.
   rewrite H10,H8,H12; reflexivity.

   do 2 red; intros.
   apply H; apply H3; auto with *.

   do 2 red; intros.
   apply H; apply H4; auto with *.
Qed.
*)
Definition dpos_consrec (F G:dpositive) :=
  mkDPositive
    (fun X => prodcart (dp_oper F X) (dp_oper G X))
    (prodcart (w1 F) (w1 G))
    (fun x => sum (w2 F (fst x)) (w2 G (snd x)))
    (fun x => sum_case (w3 F (fst x)) (w3 G (snd x)))
    (ZFspos.trad_prodcart (w2 F) (w2 G) (dp_iso F) (dp_iso G)).

Instance dpos_consrec_morph : Proper (eqdpos ==> eqdpos ==> eqdpos) dpos_consrec.
split; repeat red; simpl; intros.
 apply prodcart_morph; apply eq_dop; trivial.

 apply prodcart_morph; apply eq_dw1; trivial.

 apply sum_morph; apply eq_dw2; trivial.
  apply fst_morph; trivial.
  apply snd_morph; trivial.

 apply sum_case_morph; trivial; apply eq_dw3; trivial.
  apply fst_morph; trivial.
  apply snd_morph; trivial.

 unfold trad_prodcart, comp_iso.
 unfold sigma_isomap.
 assert (tmp1 :
   prodcart_sigma_iso
           (couple (dp_iso x (fst x1)) (dp_iso x0 (snd x1))) ==
   prodcart_sigma_iso
           (couple (dp_iso y (fst y1)) (dp_iso y0 (snd y1)))).
  unfold prodcart_sigma_iso.
  assert (tmp1 : dp_iso x (fst x1) == dp_iso y (fst y1)).
   apply eq_diso; trivial.
   apply fst_morph; trivial.
  assert (tmp2 : dp_iso x0 (snd x1) == dp_iso y0 (snd y1)).
   apply eq_diso; trivial.
   apply snd_morph; trivial.
  rewrite tmp1,tmp2; reflexivity.
 apply couple_morph.
  rewrite tmp1; reflexivity.

  unfold prodcart_cc_prod_iso.
  apply cc_lam_morph.
   apply sum_morph.
    apply eq_dw2; trivial.
    rewrite tmp1; reflexivity.
    apply eq_dw2; trivial.
    rewrite tmp1; reflexivity.
   red; intros.
   apply sum_case_morph; trivial.
    red; intros.
    rewrite tmp1,H3; reflexivity.

    red; intros.
    rewrite tmp1,H3; reflexivity.
Qed.

Lemma isDPos_consrec F G :
  isPositive F ->
  isPositive G ->
  isPositive (dpos_consrec F G).
intros Fp Gp.
constructor; simpl; intros.
 apply dpos_consrec_morph.
  apply Fp.
  apply Gp.

 apply prodcart_mono; apply dpmo; trivial.

 apply sum_case_ind0 with (2:=H0); intros.
  do 2 red; intros.
  rewrite H1; reflexivity.

  apply w3ty; trivial.
  apply fst_typ in H; trivial.
  rewrite H2,dest_sum_inl; trivial.

  apply w3ty; trivial.
  apply snd_typ in H; trivial.
  rewrite H2,dest_sum_inr; trivial.

clear; admit.
(*
 apply iso_prodcart; auto with *.
  apply dpm_iso; trivial.
  apply dpm_iso; trivial.*)
Qed.

Lemma isUPos_consrec F G :
  pos_universe U F ->
  pos_universe U G ->
  pos_universe U (dpos_consrec F G).
intros UF UG.
split; simpl; intros.
 apply G_prodcart; trivial.
  apply UF; trivial.
  apply UG; trivial.

 apply G_prodcart; trivial.
  apply UF; trivial.
  apply UG; trivial.

 apply G_sum; trivial.
  apply UF.
  apply fst_typ in H; trivial.
  apply UG.
  apply snd_typ in H; trivial.
Qed.


Definition dpos_norec (A:set) (F:set->dpositive) :=
  mkDPositive
    (fun X => Σ y ∈ A, dp_oper (F y) X)
    (Σ y ∈ A, w1 (F y))
    (fun x => w2 (F (fst x)) (snd x))
    (fun x => w3 (F (fst x)) (snd x))
    (ZFspos.trad_sigma (fun y => dp_iso (F y))).
(*
Lemma iso_arg_norec : forall P X A B f Y a h,
  morph1 Y ->
  a ∈ Arg ->
  ext_fun (P a) X -> 
  morph2 A ->
  Proper (eq_set==>eq_set==>eq_set==>eq_set) B ->
  Proper (eq_set==>eq_set==>eq_set==>eq_set==>eq_set) f ->
  morph2 h ->
  (forall x, x ∈ P a -> iso_fun (X x) (W0.W_Fd (fun a => A a x) (fun a => B a x) (fun a => f a x) Y a) (h x)) ->
  iso_fun (sigma (P a) X)
   (W0.W_Fd (fun a => sigma (P a) (A a))
            (fun a x => B a (fst x) (snd x))
            (fun a x => f a (fst x) (snd x)) Y a)
   (trad_sigma h).
intros.
unfold W0.W_Fd, ZFspos.trad_sigma.
eapply iso_fun_trans.
 apply sigma_iso_fun_morph with (4:=id_iso_fun _)
  (B':=fun x => W0.W_Fd (fun a => A a x) (fun a => B a x) (fun a => f a x) Y a); trivial.
  do 2 red; intros.
   unfold W0.W_Fd.
   apply sigma_morph; auto with *.
    apply H2; auto with *.
   red; intros.
   apply cc_prod_morph.
    apply H3; auto with *.
   red; intros.
   apply H; apply H4; auto with *.

  intros.
  rewrite H8 in H7.
  specialize H6 with (1:=H7).
  revert H6; apply iso_fun_morph; auto with *.
  rewrite <- H8 in H7; auto.

 unfold W0.W_Fd.
 apply iso_sigma_sigma; auto.
  do 2 red; intros; apply H2; auto with *.

  do 2 red; intros.
  apply cc_prod_morph.
   apply H3; auto with *.
  red; intros.
  apply H; apply H4; auto with *.
Qed.
*)
Instance dpos_norec_morph :
  Proper (eq_set==>(eq_set==>eqdpos)==>eqdpos) dpos_norec.
do 3 red; intros.
split; repeat red; simpl; intros.
 apply sigma_morph; auto with *.
 red; intros.
 assert (m := H0 _ _ H2).
 apply eq_dop; trivial.

 apply sigma_morph; auto with *.
 red; intros.
 apply H0 in H1.
 apply eq_dw1; trivial.

 assert (eqf := fst_morph _ _ H1).
 apply snd_morph in H1.
 apply H0 in eqf.
 apply eq_dw2; trivial.

 assert (eqf := fst_morph _ _ H1).
 apply snd_morph in H1.
 apply H0 in eqf.
 apply eq_dw3; trivial.

 unfold trad_sigma, comp_iso, sigma_isoassoc, sigma_isomap.
 rewrite !fst_def,!snd_def.
 assert (eqp := H0 _ _ (fst_morph _ _ H1)).
 rewrite (eq_diso _ _ (snd_morph _ _ H1)).
 rewrite H1.
 reflexivity.
Qed.

Lemma isDPos_norec A F :
  Proper (eq_set ==> eqdpos) F ->
  (forall x, x ∈ A -> isPositive (F x)) ->
  isPositive (dpos_norec A F).
constructor; simpl; intros.
 apply dpos_norec_morph; auto with *.

 apply sigma_mono; auto with *.
  do 2 red; intros. 
  apply H in H5.
  apply eq_dop; auto with *.

  do 2 red; intros. 
  apply H in H5.
  apply eq_dop; auto with *.

  intros.
  transitivity (dp_oper (F x) Y).
   apply H0 in H4; trivial.
   apply dpmo; auto.

   apply H in H5.
   red; intro; apply eq_elim.
   apply eq_dop; auto with *.

 apply sigma_elim in H1.
  destruct H1 as (_ & x1 & x2).
  specialize H0 with (1:=x1).
  apply w3ty; trivial.

  do 2 red; intros.
  apply H in H4.
  apply eq_dw1; auto with *.

clear; admit.
(*
 apply iso_arg_norec with (P:=A) (A:=fun a y => w1 (F y) a)
   (B:=fun a y => w2 (F y) a) (f:=fun a y => w3 (F y) a); auto.
  do 2 red; intros.
  apply H0 in H5.
  apply eq_dop; auto with *.

  do 3 red; intros.
  apply H0 in H5.
  apply eq_dw1; auto with *.

  do 4 red; intros.
  apply H0 in H5.
  apply eq_dw2; auto with *.

  do 5 red; intros.
  apply H0 in H5.
  apply eq_dw3; auto with *.

  do 3 red; intros.
  apply H0 in H4.
  apply eq_diso; auto with *.

  intros.
  specialize H1 with (1:=H2) (2:=H4).
  apply dpm_iso; trivial.
*)
Qed.

Lemma isUPos_norec A F :
  Proper (eq_set ==> eqdpos) F ->
  A ∈ U ->
  (forall x, x ∈ A -> pos_universe U (F x)) ->
  pos_universe U (dpos_norec A F).
intros Fm UA UF.
split; simpl; intros.
 apply G_sigma; trivial.
  do 2 red; intros.
  assert (eqf := Fm _ _ H2).
  apply eq_dop; trivial.

  intros.
  apply UF; trivial.

 apply G_sigma; trivial.
  do 2 red; intros.
  assert (eqf := Fm _ _ H0).
  apply eq_dw1; trivial.

  intros.
  apply UF; trivial.

 apply sigma_elim in H.
  destruct H as (_&ty1&ty2).
  specialize UF with (1:=ty1).
  apply UF; trivial.

  do 2 red; intros.
  apply Fm in H1.
  apply H1.
Qed.

Definition dpos_param (A:set) (F:set->dpositive) :=
  mkDPositive
    (fun X => Π y ∈ A, dp_oper (F y) X)
    (Π y ∈ A, w1 (F y))
    (fun x => Σ z ∈ A, w2 (F z) (cc_app x z))
    (fun x i => w3 (F (fst i)) (cc_app x (fst i)) (snd i))
    (ZFspos.trad_cc_prod A (fun z => w2 (F z)) (fun y => dp_iso (F y))).

(*Lemma iso_param : forall P X A B f Y a h,
  morph1 Y ->
  a ∈ Arg ->
  ext_fun (P a) X -> 
  morph2 A ->
  Proper (eq_set==>eq_set==>eq_set==>eq_set) B ->
  Proper (eq_set==>eq_set==>eq_set==>eq_set==>eq_set) f ->
  morph2 h ->
  (forall x, x ∈ P a -> iso_fun (X x) (W0.W_Fd (fun a => A a x) (fun a => B a x) (fun a => f a x) Y a) (h x)) ->
  iso_fun (cc_prod (P a) X)
   (W0.W_Fd (fun a => cc_prod (P a) (A a))
            (fun a x => Σ z ∈ P a, B a z (cc_app x z))
            (fun a x i => f a (fst i) (cc_app x (fst i)) (snd i)) Y a)
   (trad_cc_prod (P a) (fun z => B a z) h).
intros.
unfold W0.W_Fd, ZFspos.trad_cc_prod.
eapply iso_fun_trans.
 apply cc_prod_iso_fun_morph with (4:=id_iso_fun _)
  (B':=fun x => W0.W_Fd (fun a => A a x) (fun a => B a x) (fun a => f a x) Y a); trivial.
  do 2 red; intros.
   unfold W0.W_Fd.
   apply sigma_morph; auto with *.
    apply H2; auto with *.
   red; intros.
   apply cc_prod_morph.
    apply H3; auto with *.
   red; intros.
   apply H; apply H4; auto with *.

 eapply iso_fun_trans.
  apply iso_fun_cc_prod_sigma; trivial.
   do 2 red; intros; apply H2; auto with *.
   do 2 red; intros.
   apply cc_prod_morph.
    apply H3; auto with *.
   red; intros.
   apply H.
   apply H4; auto with *.

  apply sigma_iso_fun_morph; intros; auto.
   do 2 red; intros.
   apply cc_prod_morph; auto with *.
   red; intros.
   apply cc_prod_morph; auto with *.
    apply H3; auto with *.
    apply cc_app_morph; trivial.
   red;intros.
   apply H.
   apply H4; auto with *.
   apply cc_app_morph; trivial.

   do 2 red; intros.
   apply cc_prod_morph; auto with *.
    apply sigma_morph; auto with *.
    red; intros.
    apply H3; auto with *.
    apply cc_app_morph; trivial.
   red; intros.
   apply H.
   rewrite H8,H9; reflexivity.

   do 3 red; intros.
   unfold cc_prod_isocurry.
   apply cc_lam_ext.
    apply sigma_morph; auto with *.
    red; intros.
    apply H3; auto with *.
    apply cc_app_morph; trivial.
   red; intros.
   rewrite H8,H10; reflexivity.

   apply id_iso_fun.

   eapply iso_change_rhs.
   2:apply cc_prod_curry_iso_fun.
    simpl; apply cc_prod_morph; auto with *.
     apply sigma_ext; intros; auto with *.
     apply H3; auto with *.
     apply cc_app_morph; auto.
    red; intros.
    rewrite H8,H9; reflexivity.

   do 2 red; intros.
   rewrite H8,H10; reflexivity.

   do 2 red; intros.
   rewrite H8,H10,H12; reflexivity.
Qed.
*)
Instance dpos_param_morph :
  Proper (eq_set==>(eq_set==>eqdpos)==>eqdpos) dpos_param.
split; repeat red; simpl; intros.
 apply cc_prod_morph; auto with *.
 red; intros.
 assert (m := H0 _ _ H2).
 apply eq_dop; trivial.

 apply cc_prod_morph; auto with *.
 red; intros.
 apply H0 in H1.
 apply eq_dw1; trivial.

 apply sigma_morph; auto with *.
 red; intros.
 assert (eqp := H0 _ _ H2).
 apply eq_dw2; trivial.
 apply cc_app_morph; trivial.

 assert (eqp := H0 _ _ (fst_morph _ _ H2)).
 apply eq_dw3; trivial.
  apply cc_app_morph; trivial.
  apply fst_morph; trivial.
  apply snd_morph; trivial.

(* assert (tmp1 :
   cc_prod_isomap (x x1) (fun x3 => x3) (fun y3 => dp_iso (x0 y3) x1) x2 ==
   cc_prod_isomap (y y1) (fun x3 => x3) (fun y3 => dp_iso (y0 y3) y1) y2).
  unfold cc_prod_isomap.
  apply cc_lam_morph; auto with *.
  red; intros.
  assert (eqf := H0 _ _ H3).
  apply eq_diso; trivial.
  apply cc_app_morph; trivial.
 assert (tmp2 :
     cc_prod_sigma_iso (x x1)
        (cc_prod_isomap (x x1) (fun x3 => x3)
           (fun y3 => dp_iso (x0 y3) x1) x2) ==
     cc_prod_sigma_iso (y y1)
        (cc_prod_isomap (y y1) (fun x3 => x3)
           (fun y3 => dp_iso (y0 y3) y1) y2)).
  unfold cc_prod_sigma_iso.
  apply couple_morph.
   apply cc_lam_morph; auto with *.
   red; intros.
   apply fst_morph; apply cc_app_morph; trivial.

   apply cc_lam_morph; auto with *.
   red; intros.
   apply snd_morph.
   apply cc_app_morph; trivial.
 apply couple_morph.
  apply fst_morph; trivial.   

  unfold cc_prod_isocurry.
  apply cc_lam_morph.
   apply sigma_morph; auto with *.
   red; intros.
   assert (eqf := H0 _ _ H3).
   apply eq_dw2; trivial.
   apply cc_app_morph; trivial.
   apply fst_morph; trivial.

   red; intros.
   rewrite tmp2, H3.
   reflexivity.
*)
clear; admit.
Qed.

Lemma isDPos_param A F :
  Proper (eq_set ==> eqdpos) F ->
  (forall x, x ∈ A -> isPositive (F x)) ->
  isPositive (dpos_param A F).
constructor; simpl; intros.
 apply dpos_param_morph; auto with *.

 apply cc_prod_covariant; auto with *.
  do 2 red; intros. 
  apply H in H5.
  apply eq_dop; auto with *.

  intros.
  apply H0 in H4; trivial.
  apply dpmo; auto.

 apply sigma_elim in H2.
  destruct H2 as (_ & x1 & x2).
  specialize H0 with (1:=x1).
  apply w3ty; trivial.
  apply cc_prod_elim with (1:=H1); trivial.

  do 2 red; intros.
  assert (eqp := H _ _ H4).
  apply eq_dw2; auto with *.
  apply cc_app_morph; auto with *.

clear; admit.
(* apply iso_param with (P:=A) (A:=fun a y => w1 (F y) a)
   (B:=fun a y => w2 (F y) a) (f:=fun a y => w3 (F y) a); auto.
  do 2 red; intros.
  apply H0 in H5.
  apply eq_dop; auto with *.

  do 3 red; intros.
  apply H0 in H5.
  apply eq_dw1; auto with *.

  do 4 red; intros.
  apply H0 in H5.
  apply eq_dw2; auto with *.

  do 5 red; intros.
  apply H0 in H5.
  apply eq_dw3; auto with *.

  do 3 red; intros.
  apply H0 in H4.
  apply eq_diso; auto with *.

  intros.
  specialize H1 with (1:=H2) (2:=H4).
  apply dpm_iso; trivial.*)
Qed.

Lemma isUPos_param A F :
  Proper (eq_set ==> eqdpos) F ->
  A ∈ U ->
  (forall x, x ∈ A -> pos_universe U (F x)) ->
  pos_universe U (dpos_param A F).
intros Fm UA UF.
split; simpl; intros.
 apply G_cc_prod; trivial.
  do 2 red; intros.
  assert (eqf := Fm _ _ H2).
  apply eq_dop; trivial.

  intros.
  apply UF; trivial.

 apply G_cc_prod; trivial.
  do 2 red; intros.
  assert (eqf := Fm _ _ H0).
  apply eq_dw1; trivial.

  intros.
  apply UF; trivial.

 apply G_sigma; trivial.
  do 2 red; intros.
  assert (Fm' := Fm _ _ H1).
  apply Fm'.
  rewrite H1; reflexivity.

  intros.
  specialize UF with (1:=H0).
  apply UF; trivial.
  apply cc_prod_elim with (1:=H); trivial.
Qed.

End InductiveFamily.
(*
Instance dp_oper_morph_gen : Proper (eqdpos==>(eq_set==>eq_set)==>eq_set==>eq_set) dp_oper.
do 4 red; intros.
apply eq_dop; trivial.
Qed.

Instance dINDi_morph_gen : Proper (eq_set==>eqdpos==>eq_set==>eq_set==>eq_set) dINDi.
do 5 red; intros.
unfold dINDi.
apply TIF_morph_gen; auto.
do 2 red; intros.
apply eq_dop; trivial.
Qed.

Instance dIND_clos_ord_morph_gen : Proper (eq_set==>eqdpos==>eq_set) dIND_clos_ord.
do 4 red; intros.
unfold dIND_clos_ord.
apply W0.W_ord_morph_all; trivial.
 apply eq_dw1.
 apply eq_dw2.
Qed.

Instance dIND_morph_gen : Proper (eq_set==>eqdpos==>eq_set==>eq_set) dIND.
do 4 red; intros.
unfold dIND.
apply dINDi_morph_gen; trivial.
apply dIND_clos_ord_morph_gen; trivial.
Qed.
*)
(** Examples *)

Module Vectors.

Require Import ZFnats.

Definition vect A a :=
  dpos_sum
    (* vect 0 *)
    (dpos_inst zero a)
    (* forall n:N, A -> vect n -> vect (S n) *)
    (dpos_norec N
       (fun k => dpos_consrec (dpos_cst A)
                (dpos_consrec (dpos_rec k) (dpos_inst (succ k) a)))).

Lemma vect_pos A : isDPositive N (vect A).
apply isDP_intro.
 do 2 red; intros.
 unfold vect.
 apply dpos_sum_morph.
  apply dpos_inst_morph; auto with *.
  apply dpos_norec_morph; auto with *.
  red; intros.
  apply dpos_consrec_morph; auto with *.
   apply dpos_cst_morph; reflexivity.
  apply dpos_consrec_morph; auto with *.
   apply dpos_rec_morph; trivial.
   apply dpos_inst_morph; auto with *.
   rewrite H0; reflexivity.
intros a aty.
unfold vect; intros.
apply isDPos_sum.
 apply isDPos_inst.

 apply isDPos_norec.
  do 2 red; intros.
  apply dpos_consrec_morph.
   apply dpos_cst_morph.
   reflexivity.

   apply dpos_consrec_morph.
    apply dpos_rec_morph; red; trivial.
    apply dpos_inst_morph; auto with *.
    apply succ_morph; trivial.

  intros.
  apply isDPos_consrec.
   apply isPos_cst.
  apply isDPos_consrec.
   apply isDPos_rec; trivial.

   apply isDPos_inst.
Qed.

Definition nil := inl empty.

Lemma nil_typ A X :
  morph1 X ->
  nil ∈ dp_oper (vect A zero) X.
simpl; intros.
apply inl_typ.
unfold P2p.
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
  cons k x l ∈ dp_oper (vect A (succ k)) X.
simpl; intros.
apply inr_typ.
apply couple_intro_sigma; trivial.
 do 2 red; intros.
 rewrite H4; reflexivity.

 apply couple_intro; trivial.
 apply couple_intro; trivial.
 unfold P2p.
 rewrite cond_set_ax; split.
  apply singl_intro.
  reflexivity.
Qed.

End Vectors.


Module Wd.

Section Wd.
(** Parameters of W-types (with nup) *)
Variable Arg : set.
Variable A : set -> set.
Variable B : set -> set -> set.
Variable f : set -> set -> set -> set.
Hypothesis Am : morph1 A.
Hypothesis Bm : morph2 B.
Hypothesis fm : Proper (eq_set==>eq_set==>eq_set==>eq_set) f.
Hypothesis ftyp : forall a x i,
  a ∈ Arg -> x ∈ A a -> i ∈ B a x -> f a x i ∈ Arg.

Definition Wdp a : dpositive :=
  dpos_norec (A a) (fun x => dpos_param (B a x) (fun i => dpos_rec (f a x i))).

Definition Wsup a x h := couple x (cc_lam (B a x) h).

Lemma sup_typ a X x h :
  morph1 X ->
  morph1 h ->
  a ∈ Arg ->
  x ∈ A a ->
  (forall i, i ∈ B a x -> h i ∈ X (f a x i)) ->
  Wsup a x h ∈ dp_oper (Wdp a) X.
simpl; intros.
apply couple_intro_sigma; trivial.
 do 2 red; intros.
 apply cc_prod_morph.
  apply Bm; auto with *.
  red; intros.
  rewrite H5,H6; reflexivity.

 apply cc_prod_intro; intros; auto with *.
 do 2 red; intros; apply H; apply fm; auto with *. 
Qed.

End Wd.
End Wd.