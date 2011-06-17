Require Import ZF ZFrelations ZFnats ZFord ZFfix ZFfixfuntyp.
Import IZF.

Require Import ZFstable.
Require Import ZFfunext.
Require Import ZFcoc.
(*
  Variable compat : set -> set -> set -> Prop.
  Variable compatM : Proper (eq_set ==> eq_set ==> eq_set ==> iff) compat.

  Definition directed o F :=
    forall x y, x \in o -> isOrd y -> y \incl x ->
    compat (osucc y) (F y) (F x).

  Hypothesis prd_sup_lub : forall o F g,
  isOrd o ->
  directed o F ->
  (forall x, lt x o -> compat (osucc x) (F x) g) ->
  compat o (sup o F) g.


  Hypothesis prd_sup : forall o F x,
  isOrd o ->
  directed o F ->
  x \in o ->
  compat (osucc x) (F x) (sup o F).

  Hypothesis prd_union : forall o F,
  isOrd o ->
  directed o F ->
  sup o F \in U o.
*)

Lemma ord_lt_le : forall o o', isOrd o -> o' \in o -> o' \incl o.
red; intros; apply isOrd_trans with o'; trivial.
Qed.
Hint Resolve ord_lt_le.

Section Recursor.

  Variable ord : set.
  Hypothesis oord : isOrd ord.
Let oordlt := fun o olt => isOrd_inv _ o oord olt.


  (* The domain of the function to build: *)
  Variable T : set -> set.
  Hypothesis Tm : morph1 T.
  Hypothesis Tcont : forall o,
    isOrd o ->
    T o == sup o (fun o' => T (osucc o')).
  Hypothesis Tstab : stable2_ord T.


  Lemma Tmono : forall o o', isOrd o -> o' \in o ->
    T (osucc o') \incl T o.
red; intros.
rewrite Tcont; trivial.
rewrite sup_ax.
 exists o'; trivial.

 do 2 red; intros; apply Tm; apply osucc_morph; trivial.
Qed.

  (* The invariant (e.g. typing) *)
  Variable Q : set -> set -> Prop.
  Hypothesis Qm : forall o o',
    isOrd o -> o \incl ord -> o == o' ->
    forall f f', fcompat (T o) f f' -> Q o f -> Q o' f'.
  Hypothesis Qcont : forall o f,
    isOrd o ->
    o \incl ord ->
    is_cc_fun (T o) f ->
    (forall o', o' \in o -> Q (osucc o') f) ->
    Q o f.

  Let Ty o f := isOrd o /\ is_cc_fun (T o) f /\ Q o f.

  Variable F : set -> set -> set.

  Hypothesis Fm : forall o o' f f',
    isOrd o -> o == o' -> f == f' ->
    F o f == F o' f'.

  Hypothesis Ftyp : forall o f,
    isOrd o -> o \incl ord ->
    is_cc_fun (T o) f -> Q o f -> is_cc_fun (T (osucc o)) (F o f) /\ Q (osucc o) (F o f).

  Lemma Ftyp' : forall o f, o \incl ord -> Ty o f -> Ty (osucc o) (F o f).
intros.
destruct H0 as (oo,(ofun,oq)); split; auto.
Qed.

  Definition stab_fix_prop :=
    forall o o' f g,
    o' \incl ord ->
    o \incl o' ->
    Ty o f -> Ty o' g ->
    fcompat (T o) f g ->
    fcompat (T (osucc o)) (F o f) (F o' g).

  Hypothesis Fstab : stab_fix_prop.

(*
Let Tym : Proper (eq_set ==> eq_set ==> iff) Ty.
apply morph_impl_iff2; auto with *.
unfold Ty; do 4 red; intros.
destruct H1 as ((xo,xle),(xfun,xq)); split;[|split].
 rewrite <- H; auto.

 rewrite <- H; rewrite <- H0; trivial.

 revert xq; apply Qm; trivial.
  eauto using isOrd_inv.

  
 red; intros.
 apply cc_app_morph; auto with *.
Qed.
Existing Instance Tym.
*)

  Definition REC := TIO F.

Definition fincr o :=
 fdirected o (fun z => T (osucc z)) (fun z => F z (TIO F z)).
Hint Unfold fincr.

(* New proof *)

Lemma fincr_cont : forall o,
  isOrd o ->
  (forall z, z \in o -> fincr (osucc z)) ->
  fincr o.
intros o oo incrlt.
do 3 red; intros.
assert (xo : isOrd x) by eauto using isOrd_inv.
assert (yo : isOrd y) by eauto using isOrd_inv.
assert (tyx := H1).
rewrite inter2_def in H1; destruct H1.
apply Tstab in tyx; auto.
rewrite inter2_succ in tyx; trivial.
set (z := inter2 x y) in tyx.
assert (zo : isOrd z).
 apply isOrd_inter2; eauto using isOrd_inv.
assert (z \in o).
 apply isOrd_plump with x; auto.
 apply inter2_incl1.
transitivity (cc_app (F z (TIO F z)) x0).
 do 3 red in incrlt.
 apply incrlt with x; trivial.
  apply lt_osucc; trivial.

  apply ole_lts; auto.
  apply inter2_incl1.

  rewrite inter2_def; auto.

 do 3 red in incrlt.
 apply incrlt with y; trivial.
  apply ole_lts; auto.
  apply inter2_incl2.

  apply lt_osucc; trivial.

  rewrite inter2_def; auto.
Qed.



Definition inv z := Ty z (TIO F z) /\ fincr (osucc z).


Lemma fty_step : forall o, isOrd o ->
  o \incl ord ->
  (forall z, z \in o -> Ty z (TIO F z)) ->
  fincr o ->
  Ty o (TIO F o).
intros o oo ole tylt incrlt.
assert (is_cc_fun (T o) (TIO F o)).
 rewrite Tcont; trivial.
 rewrite TIO_eq; trivial.
 apply prd_union; auto; intros.
  red; red; intros; apply Tm.
  rewrite H0; reflexivity.

  apply Ftyp'; auto.
split; trivial.
split; trivial.
apply Qcont; trivial; intros.
assert (isOrd o') by eauto using isOrd_inv.
apply Qm with (osucc o') (F o' (TIO F o')); auto with *.
 red; intros.
 apply isOrd_plump with o'; eauto using isOrd_inv, olts_le.

 rewrite TIO_eq with (o:=o); trivial.
 apply prd_sup with (A:=fun z => T(osucc z)) (F:=fun z => F z (TIO F z));
   intros; auto.
 apply Ftyp'; auto.

 apply Ftyp'; auto.
Qed.


Lemma finc_ext x z :
  isOrd x -> isOrd z ->
  x \incl ord ->
  (forall w, w \in x -> Ty w (TIO F w)) ->
  fincr x ->
  z \incl x ->
  fcompat (T z) (TIO F z) (TIO F x).
intros xo zo zle tylt incrlt inc.
rewrite Tcont; trivial.
rewrite TIO_eq with (o:=z); auto.
apply prd_sup_lub; intros; auto with *.
 red; red; intros; apply Tm.
 rewrite H0; reflexivity.

 apply Ftyp'; auto.

 red; auto.

 rewrite TIO_eq with (o:=x); trivial.
 apply prd_sup with (A:=fun z => T (osucc z))
   (F:=fun z => F z (TIO F z)); auto; intros.
 apply Ftyp'; auto.
Qed.


Lemma finc_step : forall o,
  isOrd o ->
  o \incl ord ->
  (forall z, z \in o -> Ty z (TIO F z)) ->
  fincr o ->
  fincr (osucc o).
unfold fincr, fdirected; intros o oo ole tylt fo.
red; intros.
assert (xo : isOrd x) by eauto using isOrd_inv.
assert (yo : isOrd y) by eauto using isOrd_inv.
apply olts_le in H.
apply olts_le in H0.
apply Tstab in H1; auto.
rewrite inter2_succ in H1; trivial.
set (z := inter2 x y) in H1.
assert (isOrd z).
 apply isOrd_inter2; eauto using isOrd_inv.
assert (z \incl o).
 transitivity x; trivial.
 apply inter2_incl1.
assert (forall w, isOrd w -> w \incl o -> fincr w).
 red; red; auto.
transitivity (cc_app (F z (TIO F z)) x0).
 symmetry; apply Fstab; auto with *.
  transitivity o; trivial.

  apply inter2_incl1.

  apply fty_step; auto.
  transitivity o; trivial.

  apply fty_step; auto.
  transitivity o; trivial.

  apply finc_ext; intros; auto.
   transitivity o; trivial.
  apply inter2_incl1.

 apply Fstab; auto with *.
  transitivity o; trivial.

  apply inter2_incl2.

  apply fty_step; auto.
  transitivity o; trivial.

  apply fty_step; auto.
  transitivity o; trivial.

  apply finc_ext; intros; auto.
  transitivity o; trivial.
  apply inter2_incl2.
Qed.


Lemma REC_inv : forall o,
  isOrd o -> o \incl ord -> inv o.
intros o oo ole.
induction oo using isOrd_ind.
split.
 apply fty_step; intros; trivial.
  transitivity o; trivial.

  apply H0; trivial.

  apply fincr_cont; trivial.
  apply H0; trivial.

 apply finc_step; intros; trivial.
  transitivity o; trivial.

  apply H0; trivial.

  apply fincr_cont; trivial.
  apply H0; trivial.
Qed.

Lemma REC_step : forall o,
  isOrd o ->
  o \incl ord ->
  fcompat (T o) (REC o) (F o (REC o)).
intros.
destruct REC_inv with o; trivial.
unfold REC at 1.
rewrite TIO_eq with (o:=o); trivial.
rewrite Tcont; trivial.
assert (o \incl osucc o).
 red; intros; apply isOrd_trans with o; auto.
apply prd_sup_lub; intros; auto.
 red; red; intros; apply Tm.
 rewrite H5; reflexivity.

 apply Ftyp'; auto.
 apply REC_inv; eauto using isOrd_inv.

 red; auto.

 red; intros.
 apply H2.
  apply isOrd_trans with o; auto.

  apply lt_osucc; trivial.

  rewrite inter2_def; split; trivial.
  revert H5; apply Tmono; auto.
Qed.


Section REC_Eqn.

  Lemma REC_wt : is_cc_fun (T ord) (REC ord) /\ Q ord (REC ord).
apply REC_inv; auto with *.
Qed.

  Lemma REC_typ : Q ord (REC ord).
apply REC_wt.
Qed.

  Lemma REC_expand : forall x,
    x \in T ord -> cc_app (REC ord) x == cc_app (F ord (REC ord)) x.
apply REC_step; auto with *.
Qed.

  Lemma REC_eqn :
    REC ord == cc_lam (T ord) (fun x => cc_app (F ord (REC ord)) x).
intros.
rewrite (cc_eta_eq' (T ord) (REC ord)).
2:apply REC_inv; auto with *.
apply cc_lam_ext; auto with *.
red; intros.
rewrite <- H0.
apply REC_expand; trivial.
Qed.

End REC_Eqn.


End Recursor.



(* Old proof *)
(*
Definition inv z := Ty z (TIO F z) /\ fincr z.

Section InductionStep.

  Variable o : set.
  Hypothesis oo : isOrd o.
  Hypothesis inv_lt_o : forall z, lt z o -> inv z.

  Let ty_lt_o : forall z, lt z o -> Ty z (TIO F z).
intros.
apply inv_lt_o; trivial.
Qed.

  Let incr_lt_o : forall z, lt z o -> fincr z.
intros.
apply inv_lt_o; trivial.
Qed.

  Let oo' : forall z, lt z o -> isOrd z.
intros.
apply isOrd_inv with o; try red; auto.
Qed.



Lemma Fext : forall x,
  isOrd x -> x \incl o -> ext_fun x (fun o' : set => F o' (TIO F o')).
do 2 red; intros.
assert (isOrd x0) by (apply isOrd_inv with x; trivial).
assert (isOrd x') by (rewrite <- H2; trivial).
apply H0 in H1.
assert (Ty x' (TIO F x')).
 apply ty_lt_o.
 rewrite <- H2; trivial.
apply fcompat_typ_eq with (T (osucc x0)).
 apply Ftyp'; auto.

 rewrite (Tm _ _ (osucc_morph _ _ H2)).
 apply Ftyp'; auto.

 apply Fstab; auto.
  rewrite H2; reflexivity.

  red; intros.
  apply cc_app_morph; auto with *.
  apply TIO_morph; trivial.
Qed.


Lemma fincr_ext : forall x x', isOrd x -> lt x' o -> x \incl x' ->
  fcompat (T x) (TIO F x) (TIO F x').
intros.
assert (ox: isOrd x').
 apply isOrd_inv with o; auto.
rewrite Tcont; trivial.
rewrite TIO_eq; auto.
apply prd_sup_lub; intros; auto with *.
 red; red; intros; apply Tm.
 rewrite H3; reflexivity.

 apply Ftyp'.
 apply ty_lt_o.
 apply isOrd_trans with x'; trivial.
 red; auto.

 apply incr_lt_o.
 apply isOrd_plump with x'; trivial.

 intros.
 rewrite TIO_eq with (o:=x'); trivial.
 apply prd_sup with (A:=fun z => T (osucc z))
   (F:=fun z => F z (TIO F z)); auto; intros.
  apply Ftyp'.
  apply ty_lt_o.
  apply isOrd_trans with x'; trivial.

  red in incr_lt_o; auto.
Qed.

Lemma fincr_step : fincr o.
red; red; red; intros.
(*set (z:=union2 x y).
assert (lt z o).
 unfold z.
transitivity (cc_app (F z (TIO F z)) x0).
 apply Fstab; auto with *.
admit.
admit.
apply ty_lt_o.
*)
specialize (Tstab _ (isOrd_succ _ (isOrd_inv _ _ oo H)) _
            (isOrd_succ _ (isOrd_inv _ _ oo H0)) _ H1).
rewrite inter2_succ in Tstab; eauto using isOrd_inv.
set (z := inter2 x y) in Tstab.
assert (isOrd z).
 apply isOrd_inter2; eauto using isOrd_inv.
assert (lt z o).
 apply isOrd_plump with x; trivial.
 apply inter2_incl1.
rewrite inter2_def in H1; destruct H1.
transitivity (cc_app (F z (TIO F z)) x0).
 symmetry; apply Fstab; auto with *.
  apply inter2_incl1.

  apply fincr_ext; auto with *.
  apply inter2_incl1.

 apply Fstab; auto with *.
  red; auto.

  apply inter2_incl2.

  apply fincr_ext; auto with *.
  apply inter2_incl2.
Qed.

Lemma ftyp_step : Ty o (TIO F o).
assert (is_cc_fun (T o) (TIO F o)).
 rewrite Tcont; trivial.
 rewrite TIO_eq; trivial.
 apply prd_union; auto; intros.
  red; red; intros; apply Tm.
  rewrite H0; reflexivity.

  apply Ftyp'.
  apply inv_lt_o; trivial.
split; trivial.
split; trivial.
apply Qcont; trivial; intros.
assert (isOrd o') by eauto using isOrd_inv.
apply Qm with (osucc o') (F o' (TIO F o')); auto with *.
 rewrite TIO_eq with (o:=o); trivial.
 apply prd_sup with (A:=fun z => T(osucc z)) (F:=fun z => F z (TIO F z));
   intros; auto.
  apply Ftyp'.
  apply inv_lt_o; trivial.

  apply fincr_step.

 apply Ftyp'; trivial.
 apply inv_lt_o; trivial.
Qed.

Lemma finv_step : inv o.
split.
 apply ftyp_step.

 apply fincr_step.
Qed.

End InductionStep.


  Lemma REC_inv : forall o, isOrd o -> inv o.
intros.
apply isOrd_ind with (2:=H); intros.
apply finv_step; auto.
Qed.

  Lemma REC_wt : forall o, isOrd o -> Ty o (REC o).
intros.
destruct REC_inv with (1:=H); trivial.
Qed.

  Lemma REC_ty_weak : forall o o',
    isOrd o ->
    lt o' o ->
    is_cc_fun (T (osucc o')) (F o' (REC o')).
intros.
apply Ftyp'.
apply REC_wt; eauto using isOrd_inv.
Qed.

  Lemma REC_step : forall o,
    isOrd o ->
    fcompat (T o) (REC o) (F o (REC o)).
intros.
unfold REC at 1.
rewrite TIO_eq with (o:=o); trivial.
rewrite Tcont; trivial.
apply prd_sup_lub; intros; auto.
 red; red; intros; apply Tm.
 rewrite H1; reflexivity.

 apply REC_ty_weak with (o:=o); trivial.

 destruct REC_inv with (1:=H); trivial.

 apply Fstab; auto with *.
  red; intros; apply isOrd_trans with x; auto.

  apply REC_wt.
  apply isOrd_inv with o; trivial.

  apply REC_wt; trivial.

  apply fincr_ext with (osucc o); auto with *.
   intros; apply REC_inv.
   eauto using isOrd_inv.

   eauto using isOrd_inv.

   red; intros; apply isOrd_trans with x; trivial.
Qed.

Section REC_Eqn.

  Variable o : set.
  Hypothesis o_ord : isOrd o.

  Lemma REC_expand : forall n,
    n \in T o -> cc_app (REC o) n == cc_app (F o (REC o)) n.
apply REC_step; trivial.
Qed.


  Lemma REC_eqn :
    REC o == cc_lam (T o) (fun x => cc_app (F o (REC o)) x).
intros.
rewrite (cc_eta_eq' (T o) (REC o)).
2:apply REC_wt; auto.
apply cc_lam_ext; auto with *.
red; intros.
rewrite <- H0.
apply REC_expand; trivial.
Qed.

End REC_Eqn.

End Recursor.

*)