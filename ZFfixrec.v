Require Import ZF ZFrelations ZFnats ZFord ZFfix.
Import IZF.

Require Import ZFstable.
Require Import ZFfunext.
Require Import ZFcoc.

(* Specialized version of transfinite recursion where the case of limit
   ordinals is union and the stage ordinal is fed to the step function.  *)
Section TransfiniteIteration.

  (* (F o x) produces value for stage o+1 given x the value for stage o *)
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
    x \in F o' (REC o') ->
    x \in REC o.
intros.
rewrite REC_eq; trivial.
rewrite sup_ax; auto.
exists o'; trivial.
Qed.

  Lemma REC_elim : forall o x,
    isOrd o ->
    x \in REC o ->
    exists2 o', lt o' o & x \in F o' (REC o').
intros.
rewrite REC_eq in H0; trivial.
rewrite sup_ax in H0; auto.
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
    (forall o a, lt o n -> a \in X o -> F o a \in X (osucc o)) ->
    (forall m G, isOrd m -> m \incl n ->
     ext_fun m G ->
     (forall x, lt x m -> G x \in X (osucc x)) -> sup m G \in X m) ->
    REC n \in X n.
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

Section IterMonotone.

  Variable F : set -> set -> set.
  Hypothesis Fmorph : morph2 F.
  Variable Fmono : forall o o', isOrd o -> isOrd o' -> o \incl o' ->
    REC F o \incl REC F o' -> F o (REC F o) \incl F o' (REC F o').

  Lemma REC_mono : increasing (REC F).
do 2 red; intros.
apply REC_elim in H2; intros; auto with *.
destruct H2.
apply REC_intro with x0; auto with *.
apply H1 in H2; trivial.
Qed.

  Lemma REC_incl : forall o, isOrd o ->
    forall o', lt o' o ->
    REC F o' \incl REC F o.
intros.
apply REC_mono; trivial; auto.
apply isOrd_inv with o; trivial.
Qed.


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

Existing Instance REC_morph.


(* Attempt to abstract over the lattice of object built by recursion:

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

(* Building a function by recursion over an ordinal. The step function is given
   the ordinal (to determine the domain of the function used for recursive calls)
   but the result shouldn't depend on it. This is called "stage irrelevance". *)


Section Recursor.

  (* The maximal ordinal we are allowed to apply the recursive function *)
  Variable ord : set.
  Hypothesis oord : isOrd ord.

Let oordlt := fun o olt => isOrd_inv _ o oord olt.

  (* The domain of the function to build: *)
  Variable T : set -> set.
  Hypothesis Tm : morph1 T.
  Hypothesis Tcont : forall o,
    isOrd o ->
    T o == sup o (fun o' => T (osucc o')).

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

  Hypothesis Ftyp : forall o f,
    isOrd o -> o \incl ord ->
    is_cc_fun (T o) f -> Q o f ->
    is_cc_fun (T (osucc o)) (F o f) /\ Q (osucc o) (F o f).

  Lemma Ftyp' : forall o f, o \incl ord -> Ty o f -> Ty (osucc o) (F o f).
intros.
destruct H0 as (oo,(ofun,oq)); split; auto.
Qed.

  Definition stage_irrelevance :=
    forall o o' f g,
    o' \incl ord ->
    o \incl o' ->
    Ty o f -> Ty o' g ->
    fcompat (T o) f g ->
    fcompat (T (osucc o)) (F o f) (F o' g).

  Hypothesis Firrel : stage_irrelevance.

Definition fincr o :=
 fdirected o (fun z => T (osucc z)) (fun z => F z (REC F z)).
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

Definition inv z := Ty z (REC F z) /\ fincr (osucc z).


Lemma fty_step : forall o, isOrd o ->
  o \incl ord ->
  (forall z, z \in o -> Ty z (REC F z)) ->
  fincr o ->
  Ty o (REC F o).
intros o oo ole tylt incrlt.
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
 red; intros.
 apply isOrd_plump with o'; eauto using isOrd_inv, olts_le.

 rewrite REC_eq with (o:=o); trivial.
 apply prd_sup with (A:=fun z => T(osucc z)) (F:=fun z => F z (REC F z));
   intros; auto.
 apply Ftyp'; auto.

 apply Ftyp'; auto.
Qed.


Lemma finc_ext x z :
  isOrd x -> isOrd z ->
  x \incl ord ->
  (forall w, w \in x -> Ty w (REC F w)) ->
  fincr x ->
  z \incl x ->
  fcompat (T z) (REC F z) (REC F x).
intros xo zo zle tylt incrlt inc.
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


Lemma finc_step : forall o,
  isOrd o ->
  o \incl ord ->
  (forall z, z \in o -> Ty z (REC F z)) ->
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
transitivity (cc_app (F z (REC F z)) x0).
 apply Firrel; auto with *.
  transitivity o; trivial.

  apply osup2_incl1; auto.

  apply fty_step; auto.
  transitivity o; trivial.

  apply fty_step; auto.
  transitivity o; trivial.

  apply finc_ext; intros; auto.
   transitivity o; trivial.
  apply osup2_incl1; auto.

 symmetry; apply Firrel; auto with *.
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
  fcompat (T o) (REC F o) (F o (REC F o)).
intros.
destruct REC_inv with o; trivial.
rewrite REC_eq with (o:=o) at 1; trivial.
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

  Lemma REC_wt : is_cc_fun (T ord) (REC F ord) /\ Q ord (REC F ord).
apply REC_inv; auto with *.
Qed.

  Lemma REC_typing : Q ord (REC F ord).
apply REC_wt.
Qed.

  Lemma REC_expand : forall x,
    x \in T ord -> cc_app (REC F ord) x == cc_app (F ord (REC F ord)) x.
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

End REC_Eqn.

End Recursor.

