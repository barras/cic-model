(** Specialized version of transfinite recursion where the case of limit
   ordinals is union and the stage ordinal is fed to the step function.  *)

Require Import ZF ZFrelations ZFnats ZFord ZFfunext.
(** Same as ZFfixrec, but without the upper bound for the ordinal
    (used in ZFiso) *)


Section TransfiniteIteration.

  (** (F o x) produces value for stage o+1 given x the value for stage o *)
  Variable F : set -> set -> set.
  Hypothesis Fmorph : morph2 F.

Let G f o := sup o (fun o' => F o' (f o')).

Let Gm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) G.
do 3 red; intros.
unfold G.
apply sup_morph; trivial.
red; intros.
apply Fmorph; trivial.
apply H; trivial.
Qed.

Let Gmorph : forall o f f', eq_fun o f f' -> G f o == G f' o.
unfold G; intros.
apply sup_morph; auto with *.
red; intros.
apply Fmorph; auto.
Qed.

  (** Definition of the recursor *)
  Definition REC := TR G.

  Instance REC_morph : morph1 REC.
unfold REC; do 2 red; intros.
apply TR_morph; auto with *.
Qed.

  Lemma REC_fun_ext : forall x, isOrd x -> ext_fun x (fun y => F y (REC y)).
do 2 red; intros.
apply Fmorph; eauto using isOrd_inv.
apply REC_morph; trivial.
Qed.
Hint Resolve REC_fun_ext.

  Lemma REC_eq : forall o,
    isOrd o ->
    REC o == sup o (fun o' => F o' (REC o')).
intros.
unfold REC.
apply TR_eqn; auto.
Qed.

  Lemma REC_intro : forall o o' x,
    isOrd o ->
    lt o' o ->
    x ∈ F o' (REC o') ->
    x ∈ REC o.
intros.
rewrite REC_eq; trivial.
rewrite sup_ax; auto.
exists o'; trivial.
Qed.

  Lemma REC_elim : forall o x,
    isOrd o ->
    x ∈ REC o ->
    exists2 o', lt o' o & x ∈ F o' (REC o').
intros.
rewrite REC_eq in H0; trivial.
rewrite sup_ax in H0; auto.
Qed.

  Lemma REC_mono : increasing REC.
do 2 red; intros.
apply REC_elim in H2; intros; auto with *.
destruct H2.
apply REC_intro with x0; auto with *.
apply H1 in H2; trivial.
Qed.

  Lemma REC_incl : forall o, isOrd o ->
    forall o', lt o' o ->
    REC o' ⊆ REC o.
intros.
apply REC_mono; trivial; auto.
apply isOrd_inv with o; trivial.
Qed.

  Lemma REC_initial : REC zero == empty.
apply empty_ext; red; intros.
apply REC_elim in H.
 destruct H.
 elim empty_ax with (1:=H).

 apply isOrd_zero.
Qed.

  Lemma REC_typ : forall n X,
    isOrd n ->
    (forall o a, lt o n -> a ∈ X o -> F o a ∈ X (osucc o)) ->
    (forall m G, isOrd m -> m ⊆ n ->
     ext_fun m G ->
     (forall x, lt x m -> G x ∈ X (osucc x)) -> sup m G ∈ X m) ->
    REC n ∈ X n.
induction 1 using isOrd_ind; intros.
rewrite REC_eq; trivial.
apply H3 with (G:=fun o => F o (REC o)); intros; auto with *.
apply H2; trivial.
apply H1; intros; trivial.
 apply H2; trivial.
 apply isOrd_trans with x; trivial.

 apply H3; trivial.
 rewrite H6.
 red; intros.
 apply isOrd_trans with x; trivial.
Qed.

End TransfiniteIteration.
Hint Resolve REC_fun_ext.

(*
(** When the operator is monotone, we have additional properties: *)

Section IterMonotone.

  Variable F : set -> set -> set.
  Hypothesis Fmorph : morph2 F.
  Variable Fmono : forall o o', isOrd o -> isOrd o' -> o ⊆ o' ->
    REC F o ⊆ REC F o' -> F o (REC F o) ⊆ F o' (REC F o').


  Lemma REC_mono_succ : forall o,
    isOrd o ->
    REC F (osucc o) == F o (REC F o).
intros.
apply eq_intro; intros.
 apply REC_elim in H0; auto.
 destruct H0.
 assert (isOrd x).
  apply isOrd_inv with (osucc o); auto.
 revert H1; apply Fmono; auto.
  apply olts_le; auto.

  apply REC_mono; auto.
  apply olts_le; auto.

 apply REC_intro with o; auto.
Qed.

  Lemma REC_mono_eq : forall o,
    isOrd o -> 
    REC F o == sup o (fun x => REC F (osucc x)).
intros.
rewrite REC_eq; auto.
apply sup_morph; auto with *.
red; intros.
rewrite <- REC_mono_succ.
 apply REC_morph; auto.
 rewrite H1; reflexivity.

 apply isOrd_inv with o; trivial.
Qed.

End IterMonotone.
*)
Existing Instance REC_morph.

(** Building a function by transfinite iteration. The domain of the
    function grows along the iteration process.
 *)

(* Attempt to abstract over the lattice of object built by recursion:

  Variable compat : set -> set -> set -> Prop.
  Variable compatM : Proper (eq_set ==> eq_set ==> eq_set ==> iff) compat.

  Definition directed o F :=
    forall x y, x ∈ o -> isOrd y -> y ⊆ x ->
    compat (osucc y) (F y) (F x).

  Hypothesis prd_sup_lub : forall o F g,
  isOrd o ->
  directed o F ->
  (forall x, lt x o -> compat (osucc x) (F x) g) ->
  compat o (sup o F) g.


  Hypothesis prd_sup : forall o F x,
  isOrd o ->
  directed o F ->
  x ∈ o ->
  compat (osucc x) (F x) (sup o F).

  Hypothesis prd_union : forall o F,
  isOrd o ->
  directed o F ->
  sup o F ∈ U o.
*)

Section Recursor.

  (** The domain of the function to build (indexed by ordinals): *)
  Variable T : set -> set.

  (** An invariant (e.g. typing) *)
  Variable Q : set -> set -> Prop.

  Let Ty o f := isOrd o /\ is_cc_fun (T o) f /\ Q o f.

  (** The step function *)
  Variable F : set -> set -> set.

  Definition stage_irrelevance :=
    forall o o' f g,
    o ⊆ o' ->
    Ty o f -> Ty o' g ->
    fcompat (T o) f g ->
    fcompat (T (osucc o)) (F o f) (F o' g).

  (** Assumptions *)
  Record recursor := mkRecursor {
    rec_dom_m    : morph1 T;
    rec_dom_cont : forall o, isOrd o ->
      T o == sup o (fun o' => T (osucc o'));
    rec_inv_m : forall o o',
      isOrd o -> o == o' ->
      forall f f', fcompat (T o) f f' -> Q o f -> Q o' f';
    rec_inv_cont : forall o f,
      isOrd o ->
      is_cc_fun (T o) f ->
      (forall o', o' ∈ o -> Q (osucc o') f) ->
      Q o f;
    rec_body_m : morph2 F;
    rec_body_typ : forall o f,
      isOrd o ->
      is_cc_fun (T o) f -> Q o f ->
      is_cc_fun (T (osucc o)) (F o f) /\ Q (osucc o) (F o f);
    rec_body_irrel : stage_irrelevance
  }.

  Hypothesis Hrecursor : recursor.
  Let Tm := rec_dom_m Hrecursor.
  Let Tcont := rec_dom_cont Hrecursor.
  Let Qm := rec_inv_m Hrecursor.
  Let Qcont := rec_inv_cont Hrecursor.
  Let Fm := rec_body_m Hrecursor.
  Let Ftyp := rec_body_typ Hrecursor.
  Let Firrel := rec_body_irrel Hrecursor.


(* Derived properties *)

  Lemma Tmono o o' : isOrd o -> o' ∈ o ->
    T (osucc o') ⊆ T o.
red; intros.
rewrite Tcont; trivial.
rewrite sup_ax.
 exists o'; trivial.

 do 2 red; intros; apply Tm; apply osucc_morph; trivial.
Qed.

  Lemma Ftyp' o f : Ty o f -> Ty (osucc o) (F o f).
intros.
destruct H as (oo,(ofun,oq)); split; auto.
Qed.

Definition fincr o :=
 fdirected o (fun z => T (osucc z)) (fun z => F z (REC F z)).
Hint Unfold fincr.

(* New proof *)

Lemma fincr_cont o :
  isOrd o ->
  (forall z, z ∈ o -> fincr (osucc z)) ->
  fincr o.
intros oo incrlt.
do 3 red; intros.
assert (xo : isOrd x) by eauto using isOrd_inv.
assert (yo : isOrd y) by eauto using isOrd_inv.
pose (z:=x ⊔ y).
assert (zo : isOrd z).
 apply isOrd_osup2; trivial.
assert (z ∈ o).
 apply osup2_lt; trivial.
do 3 red in incrlt.
apply incrlt with z; trivial.
 apply isOrd_plump with z; auto.
  apply osup2_incl1; auto.
  apply lt_osucc; auto.
 apply isOrd_plump with z; auto.
  apply osup2_incl2; auto.
  apply lt_osucc; auto.
Qed.

Definition inv z := Ty z (REC F z) /\ fincr (osucc z).


Lemma fty_step o : isOrd o ->
  (forall z, z ∈ o -> Ty z (REC F z)) ->
  fincr o ->
  Ty o (REC F o).
intros oo tylt incrlt.
assert (is_cc_fun (T o) (REC F o)).
 rewrite Tcont; trivial.
 rewrite REC_eq; trivial.
 apply prd_union; auto; intros.
  red; red; intros; apply Tm.
  rewrite H0; reflexivity.

  apply Ftyp'; auto.
split; trivial.
split; trivial.
apply Qcont; trivial; intros.
assert (isOrd o') by eauto using isOrd_inv.
apply Qm with (osucc o') (F o' (REC F o')); auto with *.
 rewrite REC_eq with (o:=o); trivial.
 apply prd_sup with (A:=fun z => T(osucc z)) (F:=fun z => F z (REC F z));
   intros; auto.
 apply Ftyp'; auto.

 apply Ftyp'; auto.
Qed.


Lemma finc_ext x z :
  isOrd x -> isOrd z ->
  (forall w, w ∈ x -> Ty w (REC F w)) ->
  fincr x ->
  z ⊆ x ->
  fcompat (T z) (REC F z) (REC F x).
intros xo zo tylt incrlt inc.
rewrite Tcont; trivial.
rewrite REC_eq with (o:=z); auto.
apply prd_sup_lub; intros; auto with *.
 red; red; intros; apply Tm.
 rewrite H0; reflexivity.

 apply Ftyp'; auto.

 red; auto.

 rewrite REC_eq with (o:=x); trivial.
 apply prd_sup with (A:=fun z => T (osucc z))
   (F:=fun z => F z (REC F z)); auto; intros.
 apply Ftyp'; auto.
Qed.

Lemma finc_ext2 o o' z :
  isOrd o -> isOrd o' ->
  (forall w, w ∈ o ⊔ o' -> Ty w (REC F w)) ->
  fincr (o ⊔ o') ->
  z ∈ T o ->
  z ∈ T o' ->
  cc_app (REC F o) z == cc_app (REC F o') z.
transitivity (cc_app (REC F (o ⊔ o')) z).
 apply finc_ext; auto with *.
  apply isOrd_osup2; trivial.
  apply osup2_incl1; auto.

 symmetry; apply finc_ext; auto with *.
  apply isOrd_osup2; trivial.
  apply osup2_incl2; auto.
Qed.

Lemma finc_step o :
  isOrd o ->
  (forall z, z ∈ o -> Ty z (REC F z)) ->
  fincr o ->
  fincr (osucc o).
unfold fincr, fdirected; intros oo tylt fo.
red; intros.
assert (xo : isOrd x) by eauto using isOrd_inv.
assert (yo : isOrd y) by eauto using isOrd_inv.
apply olts_le in H.
apply olts_le in H0.
set (z := x ⊔ y).
assert (isOrd z).
 apply isOrd_osup2; eauto using isOrd_inv.
assert (z ⊆ o).
 apply osup2_lub; auto.
assert (forall w, isOrd w -> w ⊆ o -> fincr w).
 red; red; auto.
rewrite inter2_def in H1; destruct H1.
transitivity (cc_app (F z (REC F z)) x0).
 apply Firrel; auto with *.
  apply osup2_incl1; auto.

  apply fty_step; auto.

  apply fty_step; auto.

  apply finc_ext; intros; auto.
  apply osup2_incl1; auto.

 symmetry; apply Firrel; auto with *.
  apply osup2_incl2; auto.

  apply fty_step; auto.

  apply fty_step; auto.

  apply finc_ext; intros; auto.
  apply osup2_incl2; auto.
Qed.

(** Invariant [inv] holds for any ordinal up to [ord]. *)
Lemma REC_inv o :
  isOrd o -> inv o.
intros oo.
induction oo using isOrd_ind.
split.
 apply fty_step; intros; trivial.
  apply H0; trivial.

  apply fincr_cont; trivial.
  apply H0; trivial.

 apply finc_step; intros; trivial.
  apply H0; trivial.

  apply fincr_cont; trivial.
  apply H0; trivial.
Qed.

Lemma REC_step o o' :
  isOrd o ->
  isOrd o' ->
  o ⊆ o' ->
  fcompat (T o) (REC F o) (F o' (REC F o')).
intros.
destruct REC_inv with o'; trivial.
rewrite REC_eq with (o:=o) at 1; trivial.
rewrite Tcont; trivial.
(*assert (o ⊆ osucc o').
 admit.*)
(* red; intros; apply isOrd_trans with o; auto.*)
apply prd_sup_lub; intros; auto.
 red; red; intros; apply Tm.
 rewrite H5; reflexivity.

 apply Ftyp'; auto.
 apply REC_inv; eauto using isOrd_inv.

 red; intros; apply H3.
  apply isOrd_trans with o; auto.
  apply ole_lts; auto.
  apply isOrd_trans with o; auto.
  apply ole_lts; auto.

 red; intros.
 apply H3.
  apply isOrd_trans with o; auto.
  apply ole_lts; auto.

  apply lt_osucc; trivial.

  rewrite inter2_def; split; trivial.
  revert H5; apply Tmono; auto.
  apply isOrd_trans with o; auto.
  apply ole_lts; auto.
Qed.

Section REC_Eqn.

  Variable ord : set.
  Hypothesis oord : isOrd ord.

Let oordlt := fun o olt => isOrd_inv _ o oord olt.

  Lemma REC_wt : is_cc_fun (T ord) (REC F ord) /\ Q ord (REC F ord).
apply REC_inv; auto with *.
Qed.

  Lemma REC_typing : Q ord (REC F ord).
apply REC_wt.
Qed.

  Lemma REC_ord_irrel o o' x:
    isOrd o ->
    isOrd o' ->
    o ⊆ o' ->
    x ∈ T o ->
    cc_app (REC F o) x == cc_app (REC F o') x.
intros.
apply finc_ext; intros; trivial.
 apply REC_inv; eauto using isOrd_inv.

 apply fincr_cont; intros; trivial.
 apply REC_inv; eauto using isOrd_inv.
Qed.


  Lemma REC_ind P x :
    Proper (eq_set==>eq_set==>eq_set==>iff) P ->
    (forall o x, isOrd o -> o ⊆ ord ->
     x ∈ T o ->
     (forall o' y, lt o' o -> y ∈ T o' -> P o' y (cc_app (REC F ord) y)) ->
     P o x (cc_app (F ord (REC F ord)) x)) ->
    x ∈ T ord ->
    P ord x (cc_app (REC F ord) x).
intros Pm Hrec tyx.
revert x tyx; apply isOrd_ind with (2:=oord); intros.
rewrite (REC_step y ord H oord H0 x); trivial.
apply Hrec; trivial.
intros.
assert (fcompat (T o') (REC F o') (REC F ord)).
 apply finc_ext; auto with *.
  eauto using isOrd_inv.

  intros.
  apply REC_inv; eauto using isOrd_inv.

  do 2 red; intros.
  apply (REC_inv ord); auto with *.
   apply isOrd_trans with ord; auto.
   apply isOrd_trans with ord; auto.
rewrite <- (H4 y0); trivial.
auto.
Qed.

  Lemma REC_ext G :
    is_cc_fun (T ord) G ->
    (forall o', o' ∈ ord ->
     REC F o' == cc_lam (T o') (cc_app G) ->
     fcompat (T (osucc o')) G (F o' (cc_lam (T o') (cc_app G)))) ->
    REC F ord == G.
intros.
rewrite (cc_eta_eq' _ _ H).
apply fcompat_typ_eq with (T ord); auto.
 apply REC_inv; auto with *.

 apply is_cc_fun_lam.
 do 2 red; intros; apply cc_app_morph; auto with *.
cut ((forall z, z ∈ ord -> Ty z (cc_lam (T z) (cc_app G))) /\
     fcompat (T ord) (cc_lam (T ord) (cc_app G)) (REC F ord)).
 destruct 1; red; intros.
 symmetry; auto.
apply isOrd_ind with (2:=oord); intros.
assert (QG: forall z, z ∈ y -> Ty z (cc_lam (T z) (cc_app G))).
 intros.
 split;[|split].
  apply isOrd_inv with y; trivial.

  apply is_cc_fun_lam.
  do 2 red; intros; apply cc_app_morph; auto with *.

  apply Qm with z (REC F z).
   apply isOrd_inv with y; trivial.

   reflexivity.

   red; intros; symmetry.
   apply H3; trivial.
 
   apply REC_inv; eauto using isOrd_inv.
split; trivial.
red; intros.
rewrite cc_beta_eq; trivial.
2:do 2 red; intros; apply cc_app_morph; auto with *.
rewrite Tcont in H4; trivial.
rewrite sup_ax in H4.
 2:do 2 red; intros; apply Tm; apply osucc_morph; trivial.
destruct H4.
assert (tyRx0 : Ty x0 (REC F x0)).
 apply REC_inv; eauto using isOrd_inv.
red in H0; rewrite H0 with (o':=x0) (x:=x); auto.
 transitivity (cc_app (F y (REC F y)) x).
  apply Firrel; auto with *.
   apply REC_inv; trivial.

   destruct (H3 _ H4) as (_,?).
   red; intros.
   rewrite (H6 x1 H7).
   apply REC_ord_irrel; auto with *.
   apply isOrd_inv with y; trivial.

  symmetry; apply REC_step; auto with *.
  revert H5; apply Tmono; trivial.

 destruct tyRx0 as (_,(Rx0fun,_)).
 destruct H3 with x0 as (_,?); trivial.
 red in H6.
 rewrite cc_eta_eq' with (1:=Rx0fun).
 apply cc_lam_ext; auto with *.
 red; intros; symmetry.
 rewrite <- H8; rewrite <- H6 with (1:=H7).
 symmetry; apply cc_beta_eq; trivial.
 do 2 red; intros; apply cc_app_morph; auto with *.
Qed.

  Lemma REC_expand : forall x,
    x ∈ T ord -> cc_app (REC F ord) x == cc_app (F ord (REC F ord)) x.
apply REC_step; auto with *.
Qed.

  Lemma REC_eqn :
    REC F ord == cc_lam (T ord) (fun x => cc_app (F ord (REC F ord)) x).
intros.
rewrite (cc_eta_eq' (T ord) (REC F ord)).
2:apply REC_inv; auto with *.
apply cc_lam_ext; auto with *.
red; intros.
rewrite <- H0.
apply REC_expand; trivial.
Qed.

  (* Assumptions allow to proof the fix equation up to the succ of ord. *)
  Lemma REC_unfold : REC F (osucc ord) == F ord (REC F ord).
rewrite REC_eq; auto with *.
rewrite eq_set_ax; intros z.
rewrite sup_ax; auto with *.
split; intros.
 destruct H as (o',o'lt,zty).
 assert (o'o : isOrd o') by eauto using isOrd_inv.
 assert (o'le : o' ⊆ ord) by (apply olts_le; auto).
 assert (is_cc_fun (T (osucc o')) (F o' (REC F o'))).
  apply Ftyp'; trivial.
  apply REC_inv; auto with *.
 assert (is_cc_fun (T (osucc ord)) (F ord (REC F ord))).
  apply Ftyp'; auto with *.
  apply REC_inv; auto with *.
 rewrite cc_eta_eq' with (1:=H) in zty.
 rewrite cc_eta_eq' with (1:=H0).
 rewrite cc_lam_def in zty|-*.
 2:intros ? ? _ eqn; rewrite eqn; reflexivity.
 2:intros ? ? _ eqn; rewrite eqn; reflexivity.
 destruct zty as (n', n'ty, (y, yty, eqz)).
 exists n'.
  rewrite Tcont; auto.
  rewrite sup_ax.
  2:do 2 red; intros; apply Tm; apply osucc_morph; trivial.
  exists o'; trivial.
 exists y; trivial.
 revert yty; apply eq_elim.
 apply Firrel; auto with *.
  apply REC_inv; auto.
  apply REC_inv; auto with *.
 red; intros.
 apply REC_ord_irrel; auto with *.

 exists ord;[apply lt_osucc;trivial|trivial].
Qed.

  Record is_rec_stage (*(F:set->set->set) (T:set->set) (Q:set->set->Prop)*)
         (rec:set->set) (o:set) :=
    mkIsRec {
        rec_typ : is_cc_fun (T o) (rec o) /\ Q o (rec o);
        rec_irr :
          forall o', isOrd o' -> o' ⊆ o ->
                       fcompat (T o') (rec o') (rec o);
        rec_expand : fcompat (T o) (rec o) (F o (rec o))
(*        rec_unfold : fcompat (T (osucc o)) (rec F (osucc o)) (F o (rec F o))*)
      }.

  Definition is_rec (*F T Q*) rec :=
    forall o', isOrd o' -> is_rec_stage (*F T Q*) rec o'.

  Lemma REC_stage : is_rec (REC F).
Proof.
split.
 apply REC_inv; trivial.

 red; intros.
 apply REC_ord_irrel; trivial.

 red; intros.
 apply REC_step; trivial.
 reflexivity.
Qed.

End REC_Eqn.

End Recursor.

Global Instance REC_morph_gen : Proper ((eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) REC.
do 4 red; intros.
unfold REC.
apply TR_morph; trivial.
do 2 red; intros.
apply sup_morph; trivial.
red; intros.
apply H; trivial.
apply H1; trivial.
Qed.

(* begin hide *)
(*Module Hidden.
(* Building a function by recursion over an ordinal. The step function is given
   the ordinal (to determine the domain of the function used for recursive calls)
   but the result shouldn't depend on it. This is called "stage irrelevance". *)

Section RecGen.
  Variable ord : set.
  Variable oord : isOrd ord.

Let oordlt := fun o olt => isOrd_inv _ o oord olt.

  Variable P : set -> set -> Prop. 
  Hypothesis Pm : Proper (eq_set ==> eq_set ==> iff) P.
(*
  Hypothesis Pcont : forall o f,
    isOrd o ->
    o ⊆ ord ->
    (forall o', o' ∈ o -> P (osucc o') f) ->
    P o f.
*)
  Hypothesis Pcont' : forall o f,
    morph1 f ->
    isOrd o ->
    o ⊆ ord ->
    (forall o', o' ∈ o -> P (osucc o') (f o')) ->
(* directed... *)
    P o (sup o f).

  Variable F : set -> set -> set.

  Hypothesis Fm : morph2 F.

  Hypothesis Ftyp : forall o f,
    isOrd o -> o ⊆ ord ->
    P o f ->
    P (osucc o) (F o f).
(*
  Variable compat : set -> set -> set -> Prop.
  Hypothesis compat_morph : Proper (eq_set ==> eq_set ==> eq_set ==> iff) compat.

  Definition stage_irrelevance :=
    forall o o' f g,
    o' ⊆ ord ->
    o ⊆ o' ->
    P o f -> P o' g ->
    compat o f g ->
    compat (osucc o) (F o f) (F o' g).

  Hypothesis Firrel : stage_irrelevance.
*)

  Lemma REC_inv_gen : forall z, isOrd z -> z ⊆ ord -> P z (REC F z).
induction 1 using isOrd_ind; intros.
rewrite REC_eq; trivial.
apply Pcont'; trivial.
 do 2 red; intros.
 apply Fm; trivial.
 apply REC_morph; trivial.

 intros.
 apply Ftyp; auto.
 apply isOrd_inv with y; trivial.
Qed.
End RecGen.


Section HigherRecursor.


  (* The domain of the function to build: *)
  Variable T : set -> set.
  Hypothesis Tm : morph1 T.
  Hypothesis Tcont : forall o,
    isOrd o ->
    T o == sup o (fun o' => T (osucc o')).

  Lemma Tmono' : forall o o', isOrd o -> o' ∈ o ->
    T (osucc o') ⊆ T o.
red; intros.
rewrite Tcont; trivial.
rewrite sup_ax.
 exists o'; trivial.

 do 2 red; intros; apply Tm; apply osucc_morph; trivial.
Qed.

  (* The invariant (e.g. typing) *)
  Variable Q : set -> (set -> set) -> Prop.
  Hypothesis Qm : Proper (eq_set==>(eq_set==>eq_set)==>iff) Q.
  Hypothesis Qext : forall o,
    isOrd o ->
    forall f f',
    eq_fun (T o) f f' ->
    Q o f -> Q o f'.
  Hypothesis Qcont : forall o f,
    morph1 f ->
    isOrd o ->
    (forall o', o' ∈ o -> Q (osucc o') f) ->
    Q o f.
  Lemma Qm' o o' :
   isOrd o ->
   o == o' ->
   forall f f',
   fcompat (T o) f f' -> Q o (cc_app f) -> Q o' (cc_app f').
intros.
assert (morph1 (cc_app f)).
 apply cc_app_morph; reflexivity.
rewrite <- H0.
revert H2; apply Qext; auto with *.
red; intros.
rewrite <- H4; auto.
Qed.

  Lemma Qcont' o f :
   isOrd o ->
   is_cc_fun (T o) f ->
   (forall o', o' ∈ o -> Q (osucc o') (cc_app f)) -> Q o (cc_app f).
intros.
apply Qcont; trivial; intros.
apply cc_app_morph; reflexivity.
Qed.

  Let Ty o f := isOrd o /\ Q o f.

  Variable F : (set -> set) -> (set -> set).

  Hypothesis Fm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) F.

  Hypothesis Ftyp : forall o f,
    morph1 f ->
    isOrd o ->
    Q o f ->
    Q (osucc o) (F f).

  Hypothesis Fext : forall o f g,
    isOrd o ->
    eq_fun (T o) f g ->
    eq_fun (T (osucc o)) (F f) (F g).
(*
  Lemma Ftyp'' : forall o f,
   isOrd o ->
   o ⊆ ord ->
   is_cc_fun (T o) f ->
   Q o (cc_app f) ->
   is_cc_fun (T (osucc o)) (cc_lam (T (osucc o)) (F (cc_app f))) /\
   Q (osucc o) (cc_app (cc_lam (T (osucc o)) (F (cc_app f)))).
intros.
split.
 apply is_cc_fun_lam.
 do 2 red; intros; apply Fm; trivial.
 red; intros; apply cc_app_morph; auto with *.

 apply Qext with (F (cc_app f)); auto with *.
admit.
  red; intros.
  rewrite cc_beta_eq.
   apply Fm; trivial.
   apply cc_app_morph; reflexivity.

   do 2 red; intros; apply Fm; trivial.
   apply cc_app_morph; reflexivity.

   rewrite <- H4; trivial.

  apply Ftyp; trivial.
  apply cc_app_morph; reflexivity.
Qed.
*)
  Lemma Ftyp''' : forall o f,
   isOrd o ->
   is_cc_fun (T o) f ->
   Q o (cc_app f) ->
   is_cc_fun (T (osucc o)) (cc_lam (T (osucc o)) (F (cc_app f))) /\
   Q (osucc o) (cc_app (cc_lam (T (osucc o)) (F (cc_app f)))).
intros.
split.
 apply is_cc_fun_lam.
 do 2 red; intros; apply Fm; trivial.
 red; intros; apply cc_app_morph; auto with *.

 apply Qext with (F (cc_app f)); auto with *.
  red; intros.
  rewrite cc_beta_eq.
   apply Fm; trivial.
   apply cc_app_morph; reflexivity.

   do 2 red; intros; apply Fm; trivial.
   apply cc_app_morph; reflexivity.

   rewrite <- H3; trivial.

  apply Ftyp; trivial.
  apply cc_app_morph; reflexivity.
Qed.


  Lemma Firrel' : stage_irrelevance T (fun o f => Q o (cc_app f))
   (fun o f => cc_lam (T (osucc o)) (F (cc_app f))).
do 2 red; intros.
destruct H0 as (oo,(?,?)).
destruct H1 as (oo',(?,?)).
rewrite cc_beta_eq; trivial.
 rewrite cc_beta_eq; trivial.
  apply Fext with (o:=o); auto with *.
   red; intros.
   rewrite <- H7; auto.

  do 2 red; intros.
  apply Fm; auto with *.
  apply cc_app_morph; auto with *.

  revert H3; apply Tmono'; auto.
  apply ole_lts; trivial.

 do 2 red; intros.
 apply Fm; auto with *.
 apply cc_app_morph; auto with *.
Qed.

  Instance RECf_b_morph :
    morph2 (fun o f => cc_lam (T (osucc o)) (F (cc_app f))).
do 3 red; intros.
apply cc_lam_ext.
 rewrite H; reflexivity.

 red; intros; apply Fm; trivial.
 red; intros; apply cc_app_morph; trivial.
Qed.

  Hint Resolve Qm' Qcont' Ftyp''' Firrel' RECf_b_morph.

  Lemma RECf_recursor : recursor T
    (fun o f => Q o (cc_app f))
    (fun o f => cc_lam (T (osucc o)) (F (cc_app f))).
intros.
(*assert (w_tr : forall y, isOrd y -> y ⊆ w -> y ⊆ ord).
 red; intros.
 apply isOrd_trans with w; auto.
 red; auto.*)
split; trivial.
 intros; eapply Qm'; eauto.

 intros; apply Qcont'; auto.

 intros; apply Ftyp'''; auto.
Qed.

  Hint Resolve RECf_recursor.

  Definition RECf o :=
    cc_app (REC (fun o f => cc_lam (T (osucc o)) (F (cc_app f))) o).


(*
  Lemma RECf_typing : Q ord (RECf ord).
unfold RECf; apply REC_typing with (T:=T); eauto.
Qed.


  Lemma RECf_ind : forall P x,
    Proper (eq_set==>eq_set==>eq_set==>iff) P ->
    (forall o x, isOrd o -> o ⊆ ord ->
     x ∈ T o ->
     (forall o' y, lt o' o -> y ∈ T o' -> P o' y (RECf ord y)) ->
     P o x (F (RECf ord) x)) ->
    x ∈ T ord ->
    P ord x (RECf ord x).
unfold RECf; intros.
apply REC_ind with (T:=T) (Q:=fun o f => Q o (cc_app f)); eauto.
intros.
 rewrite cc_beta_eq.
  apply H0; auto.

  do 2 red; intros.
  apply Fm; trivial.
  apply cc_app_morph; reflexivity.

  rewrite Tcont in H4; trivial.
  rewrite sup_ax in H4.
   destruct H4.
   revert H6; apply Tmono'; auto.
   apply isOrd_trans with o; auto.
   apply ole_lts; auto.

   do 2 red; intros.
   rewrite H7; reflexivity.
Qed.
*)

  Lemma RECf_step : forall o w, isOrd w ->
    isOrd o ->
    o ⊆ w ->
    eq_fun (T o) (RECf o) (cc_app (cc_lam (T(osucc w)) (F (RECf w)))).
intros.
unfold RECf.
set (FF := fun o f => cc_lam (T (osucc o)) (F (cc_app f))).
red; intros.
rewrite <- H3; clear x' H3.
fold (FF w (REC FF w)).
(*assert (wkord : forall o, o ⊆ w -> o ⊆ ord).
 intros.
 transitivity w; trivial.
 red; intros; apply isOrd_trans with w; trivial.*)
apply REC_step with (T:=T)(Q:=fun o f => Q o (cc_app f));
  intros; eauto with *.
Qed.

  Lemma RECf_indep0 o o' :
    o ∈ ord ->
    o' ∈ ord ->
    o ⊆ o' ->
    eq_fun (T o) (RECf o) (RECf o').
red; intros.
unfold RECf at 2; rewrite <- H3; clear x' H3.
fold (RECf o' x).
transitivity (cc_app (cc_lam (T (osucc o')) (F (RECf o'))) x).
 apply RECf_step; eauto using isOrd_inv with *.
symmetry.
apply RECf_step; eauto using isOrd_inv with *.
assert (oo:isOrd o).
 eauto using isOrd_inv.
rewrite Tcont in H2; trivial.
rewrite sup_ax in H2;[destruct H2|].
 revert H3; apply Tmono'; auto.
 eauto using isOrd_inv.

 do 2 red; intros.
 rewrite H4; reflexivity.
Qed.
    
  Lemma RECf_indep o o' x :
    o ∈ ord ->
    o' ∈ ord ->
    x ∈ T o ->
    x ∈ T o' ->
    RECf o x == RECf o' x .
intros.
transitivity (RECf (o ⊔ o') x).
 apply RECf_indep0; auto with *.
  apply osup2_lt; auto.
  apply osup2_incl1; eauto using isOrd_inv.

 symmetry.
 apply RECf_indep0; auto with *.
  apply osup2_lt; auto.
  apply osup2_incl2; eauto using isOrd_inv.
Qed.


  Lemma RECf_ind0 : forall P x,
    Proper (eq_set==>eq_set==>eq_set==>iff) P ->
    forall w, lt w ord ->
    (forall o x, isOrd o -> o ⊆ w ->
     x ∈ T o ->
     (forall o' y, lt o' o -> y ∈ T o' -> P o' y (RECf w y)) ->
     P o x (F (RECf w) x)) ->
    x ∈ T w ->
    P w x (RECf w x).
unfold RECf; intros P x H w ltw; intros.
assert (wo : isOrd w).
 apply isOrd_inv with ord; trivial.
assert (wkord : forall o, o ⊆ w -> o ⊆ ord).
 intros.
 transitivity w; trivial.
 red; intros; apply isOrd_trans with w; trivial.
apply REC_ind with (T:=T) (Q:=fun o f => Q o (cc_app f)); eauto.
intros.
 rewrite cc_beta_eq.
  apply H0; auto.

  do 2 red; intros.
  apply Fm; trivial.
  apply cc_app_morph; reflexivity.

  rewrite Tcont in H4; trivial.
  rewrite sup_ax in H4.
   destruct H4.
   revert H6; apply Tmono'; auto.
   apply isOrd_trans with o; auto.
   apply ole_lts; auto.

   do 2 red; intros.
   rewrite H7; reflexivity.
Qed.

  Lemma RECf_eqn o x :
    o ∈ ord ->
    x ∈ T o ->
    RECf o x == F (RECf o) x.
intros.
apply RECf_ind0 with (P:=fun _ x w => w==F(RECf o)x); intros; auto with*.
apply morph_impl_iff3; auto with *.
do 5 red; intros.
rewrite <- H3; rewrite H4.
apply Fm; auto.
apply cc_app_morph; reflexivity.
Qed.


  Definition RECF x :=
    sup (subset ord (fun o' => x ∈ T (osucc o'))) (fun o' => F (RECf o') x).


  Lemma RECF_def x z :
    z ∈ RECF x <->
    exists2 o', o' ∈ ord /\ x ∈ T (osucc o') & z ∈ F (RECf o') x.
unfold RECF; rewrite sup_ax.
 apply ex2_morph; red; intros; try reflexivity.
 rewrite subset_ax.
 apply and_iff_morphism;[reflexivity|].
 split; intros.
  destruct H.
  rewrite H; trivial.

  exists a; auto with *.

 do 2 red; intros.
 apply Fm; auto with *.
 red; intros.
 apply cc_app_morph; trivial.
 apply REC_morph; trivial.
Qed.


  Lemma RECF_eq o' :
    o' ∈ ord ->
    eq_fun (T (osucc o')) (F (RECf o')) RECF.
intros o'ord.
assert (oo':isOrd o').
 eauto using isOrd_inv.
assert (oincl' :  osucc o' ⊆ ord).
 red; intros.
 apply isOrd_plump with o'; eauto using isOrd_inv, olts_le.
red; intros.
transitivity (F (RECf o') x').
 apply Fm; trivial.
 apply cc_app_morph; reflexivity.
rewrite H0 in H; clear x H0; rename x' into x.
apply eq_intro; intros.
 rewrite RECF_def.
 exists o'; auto.

 rewrite RECF_def in H0; destruct H0 as (o'',(o''ord,xino''),zino'').
 revert zino''; apply eq_elim; clear z.
 assert (o''o : isOrd o'').
  eauto using isOrd_inv.
 transitivity (F (RECf (o'' ⊔ o')) x).
  apply Fext with (o:=o''); auto with *.
  red; intros.
  unfold RECf at 2; rewrite <- H1; clear x' H1.
  apply RECf_indep; auto.
   apply osup2_lt; auto.

   rewrite Tcont in H0; trivial.
   rewrite sup_ax in H0.
    destruct H0.
    revert H1; apply Tmono'; auto.
     apply isOrd_osup2; trivial.

     revert H0; apply osup2_incl1; auto.

    do 2 red; intros.
    rewrite H2; reflexivity.

  symmetry.
  apply Fext with (o:=o'); auto with *.
  red; intros.
  unfold RECf at 2; rewrite <- H1; clear x' H1.
  apply RECf_indep; auto.
   apply osup2_lt; auto.

   rewrite Tcont in H0; trivial.
   rewrite sup_ax in H0.
    destruct H0.
    revert H1; apply Tmono'; auto.
     apply isOrd_osup2; trivial.

     revert H0; apply osup2_incl2; auto.

    do 2 red; intros.
    rewrite H2; reflexivity.
Qed.


  Lemma RECF_eqn x : x ∈ T ord -> RECF x == F RECF x.
intros.
rewrite Tcont in H; trivial.
rewrite sup_ax in H.
 destruct H as (o,?,?).
 assert (oo : isOrd o).
  eauto using isOrd_inv.
 rewrite <- (RECF_eq o H x x); auto with *.
 apply Fext with (o:=o); eauto with *.
 clear x H0; red; intros.
 rewrite RECf_eqn; trivial.
 apply RECF_eq; auto with *.

 rewrite Tcont in H0; trivial.
 rewrite sup_ax in H0.
  destruct H0 as (o',?,?).
  revert H2; apply Tmono'; auto.
  apply isOrd_trans with o; auto.

  do 2 red; intros.
  rewrite H3; reflexivity.

 do 2 red; intros.
 rewrite H1; reflexivity.
Qed.


  Lemma RECF_typing : Q ord RECF.
apply Qcont; auto with *.
 do 2 red; intros.
 apply sup_morph.
  apply subset_morph; auto with *.
  red; intros.
  rewrite H; reflexivity.

  red; intros.
  apply Fm; trivial.
  apply cc_app_morph.
  apply REC_morph; trivial.

 intros.
 assert (oo':isOrd o').
  eauto using isOrd_inv.
 assert (oincl' :  osucc o' ⊆ ord).
  red; intros.
  apply isOrd_plump with o'; eauto using isOrd_inv, olts_le.
 apply Qext with (F (RECf o')); auto.
  apply RECF_eq; trivial.

  apply Ftyp; trivial.
   apply cc_app_morph; reflexivity.

   red; intros; apply isOrd_trans with o'; trivial.

   unfold RECf.
   assert (wkord : forall o, o ⊆ o' -> o ⊆ ord).
    red; intros.
    apply isOrd_trans with o'; trivial.
    red; auto.
   apply REC_typing with (T:=T); eauto with *.
Qed.

End HigherRecursor.
End Hidden.
 *)
(* end hide *)