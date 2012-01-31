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

(* When the operator is monotone, we have additional properties: *)

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

Section RecGen.
  Variable ord : set.
  Variable oord : isOrd ord.

Let oordlt := fun o olt => isOrd_inv _ o oord olt.

  Variable P : set -> set -> Prop. 
  Hypothesis Pm : Proper (eq_set ==> eq_set ==> iff) P.
(*
  Hypothesis Pcont : forall o f,
    isOrd o ->
    o \incl ord ->
    (forall o', o' \in o -> P (osucc o') f) ->
    P o f.
*)
  Hypothesis Pcont' : forall o f,
    morph1 f ->
    isOrd o ->
    o \incl ord ->
    (forall o', o' \in o -> P (osucc o') (f o')) ->
(* directed... *)
    P o (sup o f).

  Variable F : set -> set -> set.

  Hypothesis Fm : morph2 F.

  Hypothesis Ftyp : forall o f,
    isOrd o -> o \incl ord ->
    P o f ->
    P (osucc o) (F o f).
(*
  Variable compat : set -> set -> set -> Prop.
  Hypothesis compat_morph : Proper (eq_set ==> eq_set ==> eq_set ==> iff) compat.

  Definition stage_irrelevance :=
    forall o o' f g,
    o' \incl ord ->
    o \incl o' ->
    P o f -> P o' g ->
    compat o f g ->
    compat (osucc o) (F o f) (F o' g).

  Hypothesis Firrel : stage_irrelevance.
*)

  Lemma REC_inv_gen : forall z, isOrd z -> z \incl ord -> P z (REC F z).
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

Lemma finc_ext2 o o' z :
  isOrd o -> isOrd o' ->
  o \incl ord ->
  o' \incl ord ->
  (forall w, w \in osup2 o o' -> Ty w (REC F w)) ->
  fincr (osup2 o o') ->
  z \in T o ->
  z \in T o' ->
  cc_app (REC F o) z == cc_app (REC F o') z.
transitivity (cc_app (REC F (osup2 o o')) z).
 apply finc_ext; auto with *.
  apply isOrd_osup2; trivial.
  apply osup2_lub; trivial.
  apply osup2_incl1; auto.

 symmetry; apply finc_ext; auto with *.
  apply isOrd_osup2; trivial.
  apply osup2_lub; trivial.
  apply osup2_incl2; auto.
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

Lemma REC_step' : forall o o',
  isOrd o ->
  isOrd o' ->
  o \incl o' ->
  o' \incl ord ->
  fcompat (T o) (REC F o) (F o' (REC F o')).
intros.
destruct REC_inv with o'; trivial.
rewrite REC_eq with (o:=o) at 1; trivial.
rewrite Tcont; trivial.
(*assert (o \incl osucc o').
 admit.*)
(* red; intros; apply isOrd_trans with o; auto.*)
apply prd_sup_lub; intros; auto.
 red; red; intros; apply Tm.
 rewrite H6; reflexivity.

 apply Ftyp'; auto.
 apply REC_inv; eauto using isOrd_inv.

 red; intros; apply H4.
  apply isOrd_trans with o; auto.
  apply ole_lts; auto.
  apply isOrd_trans with o; auto.
  apply ole_lts; auto.

 red; intros.
 apply H4.
  apply isOrd_trans with o; auto.
  apply ole_lts; auto.

  apply lt_osucc; trivial.

  rewrite inter2_def; split; trivial.
  revert H6; apply Tmono; auto.
  apply isOrd_trans with o; auto.
  apply ole_lts; auto.
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

Lemma REC_step0 : forall o o',
  isOrd o ->
  isOrd o' ->
  o \in o' ->
  o' \incl ord ->
  fcompat (T (osucc o)) (REC F o') (F o (REC F o)).
red; intros.
destruct REC_inv with o'; trivial.
do 2 red in H5.
transitivity (cc_app (F o' (REC F o')) x).
 apply REC_step; auto.
 apply Tmono with (o':=o); auto.

 apply H5.
  apply lt_osucc; trivial.
  apply isOrd_trans with o'; auto.
  rewrite inter2_def; split; trivial.
  apply Tmono with (o':=o); auto.
  apply isOrd_trans with o'; auto.
Qed.


Section REC_Eqn.

  Lemma REC_wt : is_cc_fun (T ord) (REC F ord) /\ Q ord (REC F ord).
apply REC_inv; auto with *.
Qed.

  Lemma REC_typing : Q ord (REC F ord).
apply REC_wt.
Qed.

  Lemma REC_ind : forall P x,
    Proper (eq_set==>eq_set==>eq_set==>iff) P ->
    (forall o x, isOrd o -> o \incl ord ->
     x \in T o ->
     (forall o' y, lt o' o -> y \in T o' -> P o' y (cc_app (REC F ord) y)) ->
     P o x (cc_app (F ord (REC F ord)) x)) ->
    x \in T ord ->
    P ord x (cc_app (REC F ord) x).
intros.
revert x H1; apply isOrd_ind with (2:=oord); intros.
rewrite (REC_step' y ord H1 oord H2 (fun _ x => x) x); trivial.
apply H0; trivial.
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
rewrite <- (H7 y0); trivial.
auto.
Qed.

  Lemma REC_ext G :
    is_cc_fun (T ord) G ->
    (forall o', o' \in ord ->
     fcompat (T (osucc o')) G (F o' (cc_lam (T o') (cc_app G)))) ->
    REC F ord == G.
intros.
rewrite (cc_eta_eq' _ _ H).
apply fcompat_typ_eq with (T ord); auto.
 apply REC_inv; auto with *.

 apply is_cc_fun_lam.
 admit.
cut ((forall z, z \in ord -> Ty z (cc_lam (T z) (cc_app G))) /\
     fcompat (T ord) (cc_lam (T ord) (cc_app G)) (REC F ord)).
 destruct 1; red; intros.
 symmetry; auto.
apply isOrd_ind with (2:=oord); intros.
assert (QG: forall z, z \in y -> Ty z (cc_lam (T z) (cc_app G))).
 intros.
 split;[|split].
  apply isOrd_inv with y; trivial.

  apply is_cc_fun_lam.
  do 2 red; intros; apply cc_app_morph; auto with *.

  apply Qm with z (REC F z); eauto using isOrd_inv with *.
   red; intros; symmetry.
   apply H3; trivial.
 
   apply REC_inv; eauto using isOrd_inv.
split; trivial.
red; intros.
rewrite cc_beta_eq; trivial.
 2:admit.
rewrite Tcont in H4; trivial.
rewrite sup_ax in H4.
 2:do 2 red; intros; apply Tm; apply osucc_morph; trivial.
destruct H4.
rewrite (H0 _ (H2 _ H4) x); trivial.
rewrite (fun h => REC_step0 x0 y h H1 H4 H2 x); trivial.
2:eauto using isOrd_inv.
apply Firrel; auto.
 red; auto.

 apply REC_inv; eauto using isOrd_inv.

 apply H3; trivial.
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


Section HigherRecursor.

  (* The maximal ordinal we are allowed to apply the recursive function *)
  Variable ord : set.
  Hypothesis oord : isOrd ord.

  (* The domain of the function to build: *)
  Variable T : set -> set.
  Hypothesis Tm : morph1 T.
  Hypothesis Tcont : forall o,
    isOrd o ->
    T o == sup o (fun o' => T (osucc o')).

  (* The invariant (e.g. typing) *)
  Variable Q : set -> (set -> set) -> Prop.
  Hypothesis Qm : Proper (eq_set==>(eq_set==>eq_set)==>iff) Q.
  Hypothesis Qext : forall o,
    isOrd o -> o \incl ord ->
    forall f f',
    eq_fun (T o) f f' ->
    Q o f -> Q o f'.
  Hypothesis Qcont : forall o f,
    morph1 f ->
    isOrd o ->
    o \incl ord ->
    (forall o', o' \in o -> Q (osucc o') f) ->
    Q o f.
  Lemma Qm' : forall o o',
   isOrd o ->
   o \incl ord ->
   o == o' ->
   forall f f',
   fcompat (T o) f f' -> Q o (cc_app f) -> Q o' (cc_app f').
intros.
assert (morph1 (cc_app f)).
 apply cc_app_morph; reflexivity.
rewrite <- H1.
revert H3; apply Qext; auto with *.
red; intros.
rewrite <- H5; auto.
Qed.

  Lemma Qcont' : forall o f,
   isOrd o ->
   o \incl ord ->
   is_cc_fun (T o) f ->
   (forall o', o' \in o -> Q (osucc o') (cc_app f)) -> Q o (cc_app f).
intros.
apply Qcont; trivial; intros.
apply cc_app_morph; reflexivity.
Qed.

  Let Ty o f := isOrd o /\ Q o f.

  Variable F : (set -> set) -> (set -> set).

  Hypothesis Fm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) F.

  Hypothesis Ftyp : forall o f,
    morph1 f ->
    isOrd o -> o \incl ord ->
    Q o f ->
    Q (osucc o) (F f).

  Hypothesis Fext : forall o f g,
    isOrd o ->
    o \incl ord ->
    eq_fun (T o) f g ->
    eq_fun (T (osucc o)) (F f) (F g).
(*
  Lemma Ftyp'' : forall o f,
   isOrd o ->
   o \incl ord ->
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
   osucc o \incl ord ->
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

   rewrite <- H4; trivial.

  apply Ftyp; trivial.
  apply cc_app_morph; reflexivity.
  red; intros; apply H0; auto.
  apply isOrd_trans with o; auto.
Qed.


  Lemma Firrel' : stage_irrelevance ord T (fun o f => Q o (cc_app f))
   (fun o f => cc_lam (T (osucc o)) (F (cc_app f))).
do 2 red; intros.
destruct H1 as (oo,(?,?)).
destruct H2 as (oo',(?,?)).
rewrite cc_beta_eq; trivial.
 rewrite cc_beta_eq; trivial.
  apply Fext with (o:=o); auto with *.
   transitivity o'; trivial.

   red; intros.
   rewrite <- H8; auto.

  do 2 red; intros.
  apply Fm; auto with *.
  apply cc_app_morph; auto with *.

  revert H4; apply Tmono; auto.
  apply ole_lts; trivial.

 do 2 red; intros.
 apply Fm; auto with *.
 apply cc_app_morph; auto with *.
Qed.

  Definition RECf o :=
    cc_app (REC (fun o f => cc_lam (T (osucc o)) (F (cc_app f))) o).

  Instance RECf_b_morph :
    morph2 (fun o f => cc_lam (T (osucc o)) (F (cc_app f))).
do 3 red; intros.
apply cc_lam_ext.
 rewrite H; reflexivity.

 red; intros; apply Fm; trivial.
 red; intros; apply cc_app_morph; trivial.
Qed.

  Hint Resolve Qm' Qcont' Ftyp''' Firrel' RECf_b_morph.

(*
  Lemma RECf_typing : Q ord (RECf ord).
unfold RECf; apply REC_typing with (T:=T); eauto.
Qed.


  Lemma RECf_ind : forall P x,
    Proper (eq_set==>eq_set==>eq_set==>iff) P ->
    (forall o x, isOrd o -> o \incl ord ->
     x \in T o ->
     (forall o' y, lt o' o -> y \in T o' -> P o' y (RECf ord y)) ->
     P o x (F (RECf ord) x)) ->
    x \in T ord ->
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
   revert H6; apply Tmono; auto.
   apply isOrd_trans with o; auto.
   apply ole_lts; auto.

   do 2 red; intros.
   rewrite H7; reflexivity.
Qed.
*)

  Lemma RECf_step : forall o w,
    lt w ord ->
    isOrd o ->
    o \incl w ->
    eq_fun (T o) (RECf o) (cc_app (cc_lam (T(osucc w)) (F (RECf w)))).
intros.
unfold RECf.
set (FF := fun o f => cc_lam (T (osucc o)) (F (cc_app f))).
red; intros.
rewrite <- H3; clear x' H3.
fold (FF w (REC FF w)).
assert (wo : isOrd w).
 apply isOrd_inv with ord; trivial.
assert (wkord : forall o, o \incl w -> o \incl ord).
 intros.
 transitivity w; trivial.
 red; intros; apply isOrd_trans with w; trivial.
apply REC_step' with (ord:=w)(T:=T)(Q:=fun o f => Q o (cc_app f));
  intros; eauto with *.
 apply Ftyp'''; auto.
 red; intros.
 apply le_lt_trans with o0; auto.
 apply isOrd_plump with w; auto.

 red; intros.
 apply Firrel'; auto.
Qed.

  Lemma RECf_indep0 o o' :
    o \in ord ->
    o' \in ord ->
    o \incl o' ->
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
 revert H3; apply Tmono; auto.
 eauto using isOrd_inv.

 do 2 red; intros.
 rewrite H4; reflexivity.
Qed.
    
  Lemma RECf_indep o o' x :
    o \in ord ->
    o' \in ord ->
    x \in T o ->
    x \in T o' ->
    RECf o x == RECf o' x .
intros.
transitivity (RECf (osup2 o o') x).
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
    (forall o x, isOrd o -> o \incl w ->
     x \in T o ->
     (forall o' y, lt o' o -> y \in T o' -> P o' y (RECf w y)) ->
     P o x (F (RECf w) x)) ->
    x \in T w ->
    P w x (RECf w x).
unfold RECf; intros P x H w ltw; intros.
assert (wo : isOrd w).
 apply isOrd_inv with ord; trivial.
assert (wkord : forall o, o \incl w -> o \incl ord).
 intros.
 transitivity w; trivial.
 red; intros; apply isOrd_trans with w; trivial.
apply REC_ind with (T:=T) (Q:=fun o f => Q o (cc_app f)); eauto.
 intros; apply Ftyp'''; trivial.
 red; intros.
 apply le_lt_trans with o; auto.
 apply isOrd_plump with w; auto.

 red; intros.
 apply Firrel'; auto.
intros.
 rewrite cc_beta_eq.
  apply H0; auto.

  do 2 red; intros.
  apply Fm; trivial.
  apply cc_app_morph; reflexivity.

  rewrite Tcont in H4; trivial.
  rewrite sup_ax in H4.
   destruct H4.
   revert H6; apply Tmono; auto.
   apply isOrd_trans with o; auto.
   apply ole_lts; auto.

   do 2 red; intros.
   rewrite H7; reflexivity.
Qed.

  Lemma RECf_eqn o x :
    o \in ord ->
    x \in T o ->
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
    sup (subset ord (fun o' => x \in T (osucc o'))) (fun o' => F (RECf o') x).


  Lemma RECF_def x z :
    z \in RECF x <->
    exists2 o', o' \in ord /\ x \in T (osucc o') & z \in F (RECf o') x.
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
    o' \in ord ->
    eq_fun (T (osucc o')) (F (RECf o')) RECF.
intros o'ord.
assert (oo':isOrd o').
 eauto using isOrd_inv.
assert (oincl' :  osucc o' \incl ord).
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
 transitivity (F (RECf (osup2 o'' o')) x).
  apply Fext with (o:=o''); auto with *.
  red; intros.
  unfold RECf at 2; rewrite <- H1; clear x' H1.
  apply RECf_indep; auto.
   apply osup2_lt; auto.

   rewrite Tcont in H0; trivial.
   rewrite sup_ax in H0.
    destruct H0.
    revert H1; apply Tmono; auto.
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
    revert H1; apply Tmono; auto.
     apply isOrd_osup2; trivial.

     revert H0; apply osup2_incl2; auto.

    do 2 red; intros.
    rewrite H2; reflexivity.
Qed.


  Lemma RECF_eqn x : x \in T ord -> RECF x == F RECF x.
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
  revert H2; apply Tmono; auto.
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
 assert (oincl' :  osucc o' \incl ord).
  red; intros.
  apply isOrd_plump with o'; eauto using isOrd_inv, olts_le.
 apply Qext with (F (RECf o')); auto.
  apply RECF_eq; trivial.

  apply Ftyp; trivial.
   apply cc_app_morph; reflexivity.

   red; intros; apply isOrd_trans with o'; trivial.

   unfold RECf.
   assert (wkord : forall o, o \incl o' -> o \incl ord).
    red; intros.
    apply isOrd_trans with o'; trivial.
    red; auto.
   apply REC_typing with (T:=T); eauto with *.
    intros; apply Ftyp'''; auto.
    red; intros; apply oincl'.
    apply isOrd_plump with o'; eauto using isOrd_inv.
     transitivity o; trivial; apply olts_le; trivial.
     apply lt_osucc; eauto using isOrd_inv.

    red; intros; apply Firrel'; trivial.
    red; intros; apply isOrd_trans with o'; auto.
    red; auto.
Qed.

End HigherRecursor.
