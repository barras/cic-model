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
(*  Hypothesis Tstab : stable2_ord T.*)


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

  Hypothesis Fm : morph2 F.
  Hypothesis Fext : forall o f f',
    isOrd o -> f == f' -> F o f == F o f'.

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
pose (z:=osup2 x y).
assert (zo : isOrd z).
 apply isOrd_osup2; trivial.
assert (z \in o).
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
set (z := osup2 x y).
assert (isOrd z).
 apply isOrd_osup2; eauto using isOrd_inv.
assert (z \incl o).
 apply osup2_lub; auto.
assert (forall w, isOrd w -> w \incl o -> fincr w).
 red; red; auto.
rewrite inter2_def in H1; destruct H1.
transitivity (cc_app (F z (TIO F z)) x0).
 apply Fstab; auto with *.
  transitivity o; trivial.

  apply osup2_incl1; auto.

  apply fty_step; auto.
  transitivity o; trivial.

  apply fty_step; auto.
  transitivity o; trivial.

  apply finc_ext; intros; auto.
   transitivity o; trivial.
  apply osup2_incl1; auto.

 symmetry; apply Fstab; auto with *.
  transitivity o; trivial.

  apply osup2_incl2; auto.

  apply fty_step; auto.
  transitivity o; trivial.

  apply fty_step; auto.
  transitivity o; trivial.

  apply finc_ext; intros; auto.
  transitivity o; trivial.
  apply osup2_incl2; auto.
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

