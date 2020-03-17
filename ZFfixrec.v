(** Specialized version of transfinite recursion where the case of limit
   ordinals is union and the stage ordinal is fed to the step function.  *)

Require Import ZF ZFrelations ZFnats ZFord ZFfunext.

Definition continuous (T:set->set) :=
  forall o, isOrd o -> T o == sup o (fun o' => T (osucc o')).

Lemma cont_is_mono X :
  morph1 X -> continuous X -> increasing X.
intros Xm Xcont o o' oo oo' leo.
rewrite (Xcont o'); trivial.
apply sup_lub; intros.
 do 2 red; intros.
 rewrite H0; reflexivity.
rewrite (Xcont o); trivial.
apply sup_incl with (F:=fun o'=>X(osucc o')); auto.
do 2 red; intros.
rewrite H1; reflexivity.
Qed.

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

Section RecursorWithInvariant.

  (** The maximal ordinal we are allowed to iterate over *)
  Variable ord : set.
  Hypothesis oord : isOrd ord.

Let oordlt := fun o olt => isOrd_inv _ o oord olt.

  (** The domain of the function to build (indexed by ordinals): *)
  Variable T : set -> set.

  (** [Q o f] expresses an invariant (e.g. typing) satisfied by the
      recursor on domain [T o]. It shall *not* use [f] outside of [T o].
      In particular, it should not imply that the domain of [f] is limited
      to [T o]. *)
  Variable Q : set -> set -> Prop.

  Let Ty o f := isOrd o /\ is_cc_fun (T o) f /\ Q o f.

  (** The step function *)
  Variable F : set -> set -> set.


  (** Definition of the properties of a recursor *)
  Section Spec.

  Variable f : set -> set.
  (** The condition expressing that [f] satisfies the recursive equation [F] up to [o]. *)
  Record recursor_spec := mkRecSpec {
    RXm : morph1 T;
    (* Domain is continuous *)
    RXcont : continuous T;
    (* typing *)
    Rtyp : forall o',
        isOrd o' -> o' ⊆ ord ->
        is_cc_fun (T o') (f o') /\ Q o' (f o');
    (* equation *)
    Reqn : forall o1 o2 n,
        isOrd o1 -> isOrd o2 -> o1 ⊆ ord -> o2 ⊆ ord ->
        n ∈ T o1 ->
        n ∈ T (osucc o2) ->
        cc_app (f o1) n == cc_app (F o2 (f o2)) n
  }.

  Hypothesis isrec : recursor_spec.

  Let Xm := RXm isrec.
  Let Xcont := RXcont isrec.
  Let Req := Reqn isrec.

  Let Xmono := cont_is_mono _ Xm Xcont.
  
  Lemma rec_spec_typ o' :
    isOrd o' ->
    o' ⊆ ord ->
    is_cc_fun (T o') (f o') /\ Q o' (f o').
apply (Rtyp isrec).
Qed.

  Lemma rec_spec_eqn_succ o' x :
    o' ∈ ord ->
    x ∈ T (osucc o') ->
    cc_app (f (osucc o')) x == cc_app (F o' (f o')) x.
intros.
assert (oo' : isOrd o') by eauto using isOrd_inv.
apply Req; auto.
red; intros; apply isOrd_plump with o'; auto.
 apply isOrd_inv with (osucc o'); auto.
 apply olts_le; auto.
Qed.

  Lemma rec_spec_irr o1 o2 x :
    isOrd o1 -> isOrd o2 -> o1 ⊆ o2 -> o2 ⊆ ord ->
    x ∈ T o1 ->
    cc_app (f o1) x == cc_app (f o2) x.
intros.
rewrite Req with (o1:=o2) (o2:=o2); auto.
 rewrite Req with (o1:=o1) (o2:=o2); auto with *.
  transitivity o2; trivial.

  revert H3; apply Xmono; auto.
  apply ord_lt_le; auto; apply ole_lts; auto.

 revert H3; apply Xmono; auto.

 revert H3; apply Xmono; auto.
 apply ord_lt_le; auto; apply ole_lts; auto.
Qed.

  Lemma rec_spec_eqn o' x :
    isOrd o' -> o' ⊆ ord ->
    x ∈ T o' ->
    cc_app (f o') x == cc_app (F o' (f o')) x.
intros.
apply Req; auto.
revert H1; apply Xmono; auto with *.
apply ord_lt_le; auto; apply lt_osucc; auto.
Qed.

Lemma recursor_ind : forall P x,
    Proper (eq_set==>eq_set==>eq_set==>iff) P ->
    (forall o x, isOrd o -> o ⊆ ord ->
     x ∈ T o ->
     (forall o' y, lt o' o -> y ∈ T o' -> P o' y (cc_app (f ord) y)) ->
     P o x (cc_app (F ord (f ord)) x)) ->
    x ∈ T ord ->
    P ord x (cc_app (f ord) x).
intros P x Pm Hrec tyx.
revert x tyx; apply isOrd_ind with (2:=oord); intros.
rewrite Reqn with (1:=isrec) (o2:=ord); auto with *.
 apply Hrec; auto.
 intros.
 rewrite <- rec_spec_irr with (o1:=o'); auto with *.
 eauto using isOrd_inv.

 revert tyx; apply cont_is_mono; auto with *.
 red; intros; apply isOrd_trans with y; auto.
 apply ole_lts; auto.
Qed.

  End Spec.

  (** Next section establishes conditions for the existence of a recursor *) 
  Section RecursorDef.
  
  (** NB: [osucc o] may exceed ord. What if we use [osucc o ∩ ord] instead? *)
  Definition stage_irrelevance :=
    forall o o' f g,
    o' ⊆ ord ->
    o ⊆ o' ->
    Ty o f -> Ty o' g ->
    fcompat (T o) f g ->
    fcompat (T (osucc o)) (F o f) (F o' g).

  (** Assumptions *)
  Record recursor_hyps := mkRecursor {
    rec_dom_m    : morph1 T;
    (** Domain is continuous *)
    rec_dom_cont : continuous T;
    (** [Q o f] depends upon [f] only within domain [T o] *)
    rec_inv_m : forall o o',
      isOrd o -> o ⊆ ord -> o == o' ->
      forall f f', fcompat (T o) f f' -> Q o f -> Q o' f';
    (** Invariant is continuous *)
    rec_inv_cont : forall o f,
      isOrd o ->
      o ⊆ ord ->
      is_cc_fun (T o) f ->
      (forall o', o' ∈ o -> Q (osucc o') f) ->
      Q o f;
    rec_body_m : morph2 F;
    (** The step function preserves the invariant *)
    rec_body_typ : forall o f,
      isOrd o -> o ∈ ord ->
      is_cc_fun (T o) f -> Q o f ->
      is_cc_fun (T (osucc o)) (F o f) /\ Q (osucc o) (F o f);
    (** The step function is "stage irrelevant" *)
    rec_body_irrel : stage_irrelevance
  }.

  Hypothesis Hrecursor : recursor_hyps.
  Let Tm := rec_dom_m Hrecursor.
  Let Tcont := rec_dom_cont Hrecursor.
  Let Qm := rec_inv_m Hrecursor.
  Let Qcont := rec_inv_cont Hrecursor.
  Let Fm := rec_body_m Hrecursor.
  Let Ftyp := rec_body_typ Hrecursor.
  Let Firrel := rec_body_irrel Hrecursor.

(* Derived properties *)

  Lemma Tmono : forall o o', isOrd o -> o' ∈ o ->
    T (osucc o') ⊆ T o.
red; intros.
red in Tcont; rewrite Tcont; trivial.
rewrite sup_ax.
 exists o'; trivial.

 do 2 red; intros; apply Tm; apply osucc_morph; trivial.
Qed.

  Lemma Ftyp' : forall o f, o ∈ ord -> Ty o f -> Ty (osucc o) (F o f).
intros.
destruct H0 as (oo,(ofun,oq)); split; auto.
Qed.

Definition fincr o :=
 fdirected o (fun z => T (osucc z)) (fun z => F z (REC F z)).
Hint Unfold fincr.

(* New proof *)

Lemma fincr_cont : forall o,
  isOrd o ->
  (forall z, z ∈ o -> fincr (osucc z)) ->
  fincr o.
intros o oo incrlt.
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


Lemma fty_step : forall o, isOrd o ->
  o ⊆ ord ->
  (forall z, z ∈ o -> Ty z (REC F z)) ->
  fincr o ->
  Ty o (REC F o).
intros o oo ole tylt incrlt.
assert (is_cc_fun (T o) (REC F o)).
 red in Tcont; rewrite Tcont; trivial.
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
  x ⊆ ord ->
  (forall w, w ∈ x -> Ty w (REC F w)) ->
  fincr x ->
  z ⊆ x ->
  fcompat (T z) (REC F z) (REC F x).
intros xo zo zle tylt incrlt inc.
red in Tcont; rewrite Tcont; trivial.
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
  o ⊆ ord ->
  o' ⊆ ord ->
  (forall w, w ∈ o ⊔ o' -> Ty w (REC F w)) ->
  fincr (o ⊔ o') ->
  z ∈ T o ->
  z ∈ T o' ->
  cc_app (REC F o) z == cc_app (REC F o') z.
transitivity (cc_app (REC F (o ⊔ o')) z).
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
  o ⊆ ord ->
  (forall z, z ∈ o -> Ty z (REC F z)) ->
  fincr o ->
  fincr (osucc o).
unfold fincr, fdirected; intros o oo ole tylt fo.
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

(** Invariant [inv] holds for any ordinal up to [ord]. *)
Lemma REC_inv : forall o,
  isOrd o -> o ⊆ ord -> inv o.
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

Lemma REC_step : forall o o' x,
  isOrd o ->
  isOrd o' ->
  o ⊆ o' ->
  o' ⊆ ord ->
  x ∈ T o ->
  cc_app (REC F o) x == cc_app (F o' (REC F o')) x.
intros.
destruct REC_inv with o'; trivial.
rewrite REC_eq with (o:=o) at 1; trivial.
red in Tcont; rewrite Tcont in H3; trivial.
revert x H3; apply prd_sup_lub; intros; auto.
 red; red; intros; apply Tm.
 rewrite H6; reflexivity.

 apply Ftyp'; auto.
 apply REC_inv; eauto using isOrd_inv.

 red; intros; apply H5.
  apply isOrd_trans with o; auto.
  apply ole_lts; auto.
  apply isOrd_trans with o; auto.
  apply ole_lts; auto.

 red; intros.
 apply H5.
  apply isOrd_trans with o; auto.
  apply ole_lts; auto.

  apply lt_osucc; trivial.

  rewrite inter2_def; split; trivial.
  revert H6; apply Tmono; auto.
  apply isOrd_trans with o; auto.
  apply ole_lts; auto.
Qed.

Lemma REC_ord_irrel o o' x:
    isOrd o ->
    isOrd o' ->
    o ⊆ o' ->
    o' ⊆ ord ->
    x ∈ T o ->
    cc_app (REC F o) x == cc_app (REC F o') x.
intros.
apply finc_ext; intros; trivial.
 apply REC_inv; eauto using isOrd_inv.

 apply fincr_cont; intros; trivial.
 apply REC_inv; eauto using isOrd_inv.
Qed.

Lemma REC_recursor_spec :
  recursor_spec (REC F).
split; intros; trivial.
 apply REC_inv; trivial.

 pose (o' := o1⊔o2).
 assert (oo' : isOrd o') by (apply isOrd_osup2; trivial).
 assert (le1 : o1 ⊆ o') by (apply osup2_incl1; trivial).
 assert (le2 : o2 ⊆ o') by (apply osup2_incl2; trivial).
 assert (leo : o' ⊆ ord) by (apply osup2_lub; trivial).
 rewrite REC_ord_irrel with (o':=o1⊔o2); trivial.
 rewrite REC_step with (o':=o1⊔o2); auto with *.
 symmetry.
 apply Firrel; auto.
  apply REC_inv; auto.
  apply REC_inv; auto.

  red; intros.
  apply REC_ord_irrel; trivial.

 revert H3; apply cont_is_mono; auto.
Qed. 

End RecursorDef.

End RecursorWithInvariant.

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


Section RecursorExt.

  Variable T T' : set->set.
  Variable Q Q' : set->set->Prop.
  Variable F F' : set->set->set.
  Variable f f' : set->set.
  Variable o o' : set.
  Hypothesis oo : isOrd o.
  Hypothesis oo' : isOrd o'.
  Hypothesis frec : recursor_spec o T Q F f.
  Hypothesis f'rec : recursor_spec o' T' Q' F' f'.
  Hypothesis leo : o ⊆ o'.
  Hypothesis Tincl : forall z, isOrd z -> z ⊆ o -> T z ⊆ T' z.
  Hypothesis Fincl : forall z, isOrd z -> z ⊆ o ->
   forall g g',
   is_cc_fun (T z) g ->
   is_cc_fun (T' z) g' ->
   Q z g ->
   Q' z g' ->
   fcompat (T z) g g' ->
   fcompat (T (osucc z)) (F z g) (F' z g').
  
  Lemma recursor_ext0 :
    fcompat (T o) (f o) (f' o).
red.
elim oo using isOrd_ind; intros.
assert (Tcont := RXcont _ _ _ _ _ frec).
red in Tcont; rewrite Tcont in H2; auto.
assert (leyo' : y ⊆ o') by (transitivity o; auto).
apply sup_ax in H2; auto with *.
 destruct H2 as (z,?,?).
 assert (zo : isOrd z) by eauto using isOrd_inv.
 assert (x ∈ T y).
  revert H3; apply cont_is_mono; auto with *.
  apply (RXm _ _ _ _ _ frec).
  red; intros; apply isOrd_plump with z; auto.
   eauto using isOrd_inv.
   apply olts_le; auto.
 rewrite (Reqn _ _ _ _ _ frec) with (o2:=z); auto.
 rewrite (Reqn _ _ _ _ _ f'rec) with (o2:=z); auto with *.
 apply Fincl; auto.
  apply rec_spec_typ with (1:=frec); auto.
  apply rec_spec_typ with (1:=f'rec); auto.
  apply rec_spec_typ with (1:=frec); auto.
  apply rec_spec_typ with (1:=f'rec); auto.
 red; intros.
 apply H1; auto.

 revert H4; apply Tincl; auto.

 revert H3; apply Tincl; auto.
 red; intros; apply isOrd_plump with z; auto.
  eauto using isOrd_inv.
  apply olts_le; auto.

do 2 red; intros.
apply (RXm _ _ _ _ _ frec). 
rewrite H4; reflexivity.
Qed.

  Lemma recursor_ext :
    fcompat (T o) (f o) (f' o').
red; intros.
transitivity (cc_app (f' o) x).
 apply recursor_ext0; trivial.

 apply rec_spec_irr with (1:=f'rec); auto with *.
 revert H; apply Tincl; auto with *.
Qed.

End RecursorExt.

(** Case where the invariant is just a typing condition *)

Section TypedRecursor.

  (** The domain, indexed by ordinals *)
  Variable X : set -> set.
  (** The co-domain *)
  Variable U : set -> set -> set.

  Let Q' o f := forall x, x ∈ X o -> cc_app f x ∈ U o x.

  Lemma Qty o f :
    ext_fun (X o) (U o) ->
    isOrd o ->
    (is_cc_fun (X o) f /\ Q' o f <-> f ∈ cc_prod (X o) (U o)).
intros Um.
split; intros.
 destruct H0.
 rewrite cc_eta_eq' with (1:=H0).
 apply cc_prod_intro; auto.
 do 2 red; intros; apply cc_app_morph; auto with *.

 split.
  rewrite cc_eta_eq with (1:=H0).
  apply is_cc_fun_lam.
  do 2 red; intros; apply cc_app_morph; auto with *.

  red; intros.
  apply cc_prod_elim with (1:=H0); trivial.
Qed.

Section RecursorSpecification.

  Hypothesis F : set -> set -> set.
  Hypothesis f : set -> set.
  Hypothesis o : set.
  Hypothesis oo : isOrd o.

  Definition typed_recursor_spec :=
    recursor_spec o X Q' F f.
  
  Hypothesis isrec : typed_recursor_spec.

  Lemma typed_rec_typ o' :
    ext_fun (X o') (U o') ->
    isOrd o' ->
    o' ⊆ o ->
    f o' ∈ (Π x ∈ X o', U o' x).
intros.
apply Qty; auto.
apply (Rtyp _ _ _ _ _ isrec); trivial.
Qed.

  Lemma typed_rec_eqn_succ o' x :
    o' ∈ o ->
    x ∈ X (osucc o') ->
    cc_app (f (osucc o')) x == cc_app (F o' (f o')) x.
intros.
assert (oo' : isOrd o') by eauto using isOrd_inv.
apply (Reqn _ _ _ _ _ isrec); auto.
red; intros; apply isOrd_plump with o'; auto.
 apply isOrd_inv with (osucc o'); auto.
 apply olts_le; auto.
Qed.

  Lemma typed_rec_eqn o' x :
    isOrd o' -> o' ⊆ o ->
    x ∈ X o' ->
    cc_app (f o') x == cc_app (F o' (f o')) x.
intros.
apply (Reqn _ _ _ _ _ isrec); auto.
revert H1; apply (cont_is_mono _ (RXm _ _ _ _ _ isrec) (RXcont _ _ _ _ _ isrec)); auto with *.
apply ord_lt_le; auto; apply lt_osucc; auto.
Qed.

End RecursorSpecification.

Section RecursorDefinition.
  
  Hypothesis F : set -> set -> set.
  Hypothesis O : set.
  Hypothesis Oo : isOrd O.
  
  Definition typed_recursor_hyps :=
    recursor_hyps O X Q' F.

  Section Constructor. 

    Hypothesis
    (RHXm : morph1 X)
    (* Domain is continuous *)
    (RHXcont : continuous X)
(*    (Oo : isOrd O)*)
(*    (RHUm : morph2 U)*)
    (* Co-domain is monotonic *)
    (RHUmono : forall o o' x x',
        isOrd o ->
        o ⊆ o' ->
        o' ∈ osucc O ->
        x ∈ X o ->
        x == x' ->
        U o x ⊆ U o' x')
    (RHm : morph2 F)
    (* Recursive equation is well-typed *)
    (RHtyp : forall o,
        o ∈ O ->
        forall f,
        f ∈ (Π x ∈ X o, U o x) ->
        F o f
          ∈ (Π x ∈ X (osucc o), U (osucc o) x))
    (* Recursive equation is stage irrelevant *)
    (RHirr : forall o o' f g,
        isOrd o ->
        o ⊆ o' ->
        o' ∈ osucc O ->
        f ∈ (Π x ∈ X o, U o x) ->
        g ∈ (Π x ∈ X o', U o' x) ->
        fcompat (X o) f g ->
        fcompat (X (osucc o)) (F o f) (F o' g)).

Let Uext o : isOrd o -> o ⊆ O -> ext_fun (X o) (U o).
red; intros.
red; intros.
apply incl_eq; apply RHUmono; eauto with *.
 apply ole_lts; auto.
 apply ole_lts; auto.
 rewrite <- H2; trivial.
Qed.

Let Q'm :
   forall o o',
   isOrd o ->
   o ⊆ O ->
   o == o' -> forall f f', fcompat (X o) f f' -> Q' o f -> Q' o' f'.
intros.
unfold Q' in H3|-*; intros.
generalize RHXm; intros. (* ? *)
rewrite <- H1 in H4.
specialize H3 with (1:=H4).
red in H2; rewrite <- H2; trivial.
revert H3; apply RHUmono; auto with *.
 rewrite <- H1; reflexivity.
 rewrite <- H1; apply ole_lts; trivial.
Qed.

Let Q'cont : forall o f : set,
 isOrd o ->
 o ⊆ O ->
 is_cc_fun (X o) f ->
 (forall o' : set, o' ∈ o -> Q' (osucc o') f) -> Q' o f.
intros.
red; intros.
red in RHXcont; rewrite RHXcont in H3; trivial.
apply sup_ax in H3.
 destruct H3 as (o',?,?).
generalize (H2 _ H3 _ H4).
apply RHUmono; eauto using isOrd_inv with *.
 red; intros.
 apply isOrd_plump with o'; eauto using isOrd_inv.
 apply olts_le in H5; trivial.

 apply ole_lts; auto.
do 2 red; intros; apply RHXm; apply osucc_morph; trivial.
Qed.

Let Q'typ : forall o f,
 isOrd o ->
 o ∈ O ->
 is_cc_fun (X o) f ->
 Q' o f -> is_cc_fun (X (osucc o)) (F o f) /\ Q' (osucc o) (F o f).
intros.
assert (isOrd o) by eauto using isOrd_inv.
apply Qty; auto.
 apply Uext; auto.
 red; intros; apply isOrd_plump with o; trivial.
  eauto using isOrd_inv.
  apply olts_le; trivial.
apply RHtyp; trivial.
apply Qty; auto.
Qed.
    
  Lemma mkTypedRec : typed_recursor_hyps.
split; trivial.
 red; intros.
 destruct H1 as (?,?).
 destruct H2 as (?,?).
 apply RHirr; auto.
  apply ole_lts; auto.

  apply Qty; auto.
  apply Uext; auto.
  transitivity o'; auto.

  apply Qty; auto.
Qed.

End Constructor.

  Lemma typed_recursor :
    typed_recursor_hyps ->
    typed_recursor_spec F (REC F) O.
apply REC_recursor_spec; trivial.
Qed.

End RecursorDefinition.

End TypedRecursor.
  
Section TypedRecursorExt.

  Variable T T' : set->set.
  Variable U U' : set->set->set.
  Variable F F' : set->set->set.
  Variable f f' : set->set.
  Variable o o' : set.
  Hypothesis oo : isOrd o.
  Hypothesis oo' : isOrd o'.
  Hypothesis frec : typed_recursor_spec T U F f o.
  Hypothesis f'rec : typed_recursor_spec T' U' F' f' o'.
  Hypothesis leo : o ⊆ o'.
  Hypothesis Tincl : forall z, isOrd z -> z ⊆ o -> T z ⊆ T' z.
  Hypothesis Fincl : forall z, isOrd z -> z ⊆ o ->
   forall g g',
   g ∈ (Π x ∈ T z, U z x) -> 
   g' ∈ (Π x ∈ T' z, U' z x) -> 
   fcompat (T z) g g' ->
   fcompat (T (osucc z)) (F z g) (F' z g').
  
  Lemma typed_recursor_ext :
    (forall z, isOrd z -> z ⊆ o -> ext_fun (T z) (U z)) ->
    (forall z, isOrd z -> z ⊆ o -> ext_fun (T' z) (U' z)) ->
    fcompat (T o) (f o) (f' o').
intros Uext U'ext.
apply recursor_ext with (3:=frec) (4:=f'rec); auto.
intros.
 apply Fincl; auto.

 apply Qty; auto with *.
 apply Qty; auto with *.
Qed.

End TypedRecursorExt.
  
(* begin hide *)
Module Hidden.
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

  (* The maximal ordinal we are allowed to apply the recursive function *)
  Variable ord : set.
  Hypothesis oord : isOrd ord.

  (* The domain of the function to build: *)
  Variable T : set -> set.
  Hypothesis Tm : morph1 T.
  Hypothesis Tcont : continuous T.

  Lemma Tmono' : forall o o', isOrd o -> o' ∈ o ->
    T (osucc o') ⊆ T o.
red; intros.
red in Tcont; rewrite Tcont; trivial.
rewrite sup_ax.
 exists o'; trivial.

 do 2 red; intros; apply Tm; apply osucc_morph; trivial.
Qed.

  (* The invariant (e.g. typing) *)
  Variable Q : set -> (set -> set) -> Prop.
  Hypothesis Qm : Proper (eq_set==>(eq_set==>eq_set)==>iff) Q.
  Hypothesis Qext : forall o,
    isOrd o -> o ⊆ ord ->
    forall f f',
    eq_fun (T o) f f' ->
    Q o f -> Q o f'.
  Hypothesis Qcont : forall o f,
    morph1 f ->
    isOrd o ->
    o ⊆ ord ->
    (forall o', o' ∈ o -> Q (osucc o') f) ->
    Q o f.
  Lemma Qm' : forall o o',
   isOrd o ->
   o ⊆ ord ->
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
   o ⊆ ord ->
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
    isOrd o -> o ⊆ ord ->
    Q o f ->
    Q (osucc o) (F f).

  Hypothesis Fext : forall o f g,
    isOrd o ->
    o ⊆ ord ->
    eq_fun (T o) f g ->
    eq_fun (T (osucc o)) (F f) (F g).

  Lemma Ftyp''' : forall o f,
   isOrd o ->
   osucc o ⊆ ord ->
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

  revert H4; apply Tmono'; auto.
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

  Lemma RECf_recursor_hyps : forall w, w ∈ ord -> recursor_hyps w T
    (fun o f => Q o (cc_app f))
    (fun o f => cc_lam (T (osucc o)) (F (cc_app f))).
intros.
assert (w_tr : forall y, isOrd y -> y ⊆ w -> y ⊆ ord).
 red; intros.
 apply isOrd_trans with w; auto.
 red; auto.
split; trivial.
 intros; eapply Qm'; eauto.

 intros; apply Qcont'; auto.

 intros; apply Ftyp'''; auto.
 red; intros.
 apply le_lt_trans with o; auto.
 apply isOrd_trans with w; auto.

 red; intros.
 apply Firrel'; auto.
 destruct H3; auto.
Qed.

  Definition RECf o :=
    cc_app (REC (fun o f => cc_lam (T (osucc o)) (F (cc_app f))) o).


  Lemma RECf_recursor : forall w, w ∈ ord -> recursor_spec w T
    (fun o f => Q o (cc_app f))
    (fun o f => cc_lam (T (osucc o)) (F (cc_app f)))
    (REC (fun o f => cc_lam (T (osucc o)) (F (cc_app f)))).
intros.
apply REC_recursor_spec with (2:=RECf_recursor_hyps _ H).
eauto using isOrd_inv.
Qed.
  

  Lemma RECf_step : forall o w,
    lt w ord ->
    isOrd o ->
    o ⊆ w ->
    eq_fun (T o) (RECf o) (cc_app (cc_lam (T(osucc w)) (F (RECf w)))).
intros.
unfold RECf.
set (FF := fun o f => cc_lam (T (osucc o)) (F (cc_app f))).
red; intros.
rewrite <- H3; clear x' H3.
fold (FF w (REC FF w)).
assert (wo : isOrd w).
 apply isOrd_inv with ord; trivial.
assert (wkord : forall o, o ⊆ w -> o ⊆ ord).
 intros.
 transitivity w; trivial.
 red; intros; apply isOrd_trans with w; trivial.
apply Reqn with (1:=RECf_recursor _ H); auto with *.
revert H2; apply cont_is_mono; auto.
rewrite H1.
red; intros; apply isOrd_trans with w; auto.
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
red in Tcont; rewrite Tcont in H2; trivial.
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
apply recursor_ind with (2:=RECf_recursor _ ltw); auto.
intros.
 rewrite cc_beta_eq.
  apply H0; auto.

  do 2 red; intros.
  apply Fm; trivial.
  apply cc_app_morph; reflexivity.

  red in Tcont; rewrite Tcont in H4; trivial.
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

   red in Tcont; rewrite Tcont in H0; trivial.
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

   red in Tcont; rewrite Tcont in H0; trivial.
   rewrite sup_ax in H0.
    destruct H0.
    revert H1; apply Tmono'; auto.
     apply isOrd_osup2; trivial.

     revert H0; apply osup2_incl2; auto.

    do 2 red; intros.
    rewrite H2; reflexivity.
Qed.


(*  Lemma RECF_eqn x : x ∈ T ord -> RECF x == F RECF x.
intros.
red in Tcont; rewrite Tcont in H; trivial.
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
*)

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
   apply rec_spec_typ with (1:=RECf_recursor _ H); auto with *.
Qed.

End HigherRecursor.
End Hidden.
(* end hide *)