Require Import ZF ZFsum ZFfix ZFnats ZFrelations ZFord ZFcard ZFstable ZFcont.
Import IZF ZFrepl.


(***************************************************************************)
(* Elementary types: *)

Definition UNIT := succ zero.
Lemma unit_typ : zero \in UNIT.
unfold UNIT.
apply succ_intro1.
reflexivity.
Qed.

Lemma unit_elim : forall p, p \in UNIT -> p == zero.
unfold UNIT; intros.
elim le_case with (1:=H); intros; trivial.
elim empty_ax with p; trivial.
Qed.

Definition BOOL := succ (succ zero).
Definition TRUE := zero.
Definition FALSE := succ zero.

Lemma true_typ : TRUE \in BOOL.
unfold TRUE, BOOL.
apply succ_intro2.
apply succ_intro1.
reflexivity.
Qed.

Lemma false_typ : FALSE \in BOOL.
unfold FALSE, BOOL.
apply succ_intro1.
reflexivity.
Qed.

Lemma bool_elim : forall b, b \in BOOL -> b == TRUE \/ b == FALSE.
unfold BOOL, TRUE, FALSE; intros.
elim le_case with (1:=H); intros; auto.
elim le_case with (1:=H0); intros; auto.
elim empty_ax with (1:=H1).
Qed.

Definition EQ A x y :=
  subset (singl empty) (fun _ => x \in A /\ x == y).

Definition REFL := empty.

Lemma refl_typ : forall A x, x \in A -> REFL \in EQ A x x.
unfold EQ, REFL; intros.
apply subset_intro; auto with *.
apply singl_intro.
Qed.

(* Rk: this property implies K (p \in EQ A x x -> p == REFL) *)
Lemma EQ_elim : forall A x y p,
  p \in EQ A x y -> x \in A /\ x == y /\ p == REFL.
unfold EQ; intros.
rewrite subset_ax in H; destruct H.
apply singl_elim in H.
destruct H0.
destruct H1; auto.
Qed.

Lemma EQ_ind : forall A P,
  Proper (eq_set ==> eq_set ==> iff) P ->
  forall x y p, P x REFL -> p \in EQ A x y -> P y p.
intros.
apply EQ_elim in H1.
revert H0; apply H.
 symmetry; apply H1.
 apply H1.
Qed.

Section Nat_theory.

(***************************************************************************)
(* Natural numbers *)

Section TypeConstructor.

  Definition NATf X := sum UNIT X.

  Lemma sum_ext_natf : forall A, ext_fun A NATf.
do 2 red; intros.
unfold NATf.
rewrite H0; reflexivity.
Qed.

  Instance NATf_mono : Proper (incl_set ==> incl_set) NATf.
do 2 red; intros.
unfold NATf.
apply sum_mono; trivial.
red; trivial.
Qed.
Hint Resolve NATf_mono Fmono_morph.
  Instance NATf_morph : Proper (eq_set ==> eq_set) NATf.
apply Fmono_morph; trivial.
Qed.


Definition ZERO := inl zero.
Definition SUCC x := inr x.

  Lemma NATf_discr : forall n, ~ ZERO == SUCC n.
red; intros.
apply discr_sum in H; trivial.
Qed.

  Lemma SUCC_inj : forall n m, SUCC n == SUCC m -> n == m.
unfold SUCC.
apply inr_inj.
Qed.

  Lemma ZERO_typ_gen : forall X, ZERO \in sum UNIT X.
unfold ZERO; intros.
apply inl_typ.
apply unit_typ.
Qed.

  Lemma SUCC_typ_gen : forall x X, x \in X -> SUCC x \in sum UNIT X.
unfold SUCC; intros.
apply inr_typ; trivial.
Qed.

  Lemma NATf_case : forall X (P:Prop) x,
    (x == ZERO -> P) ->
    (forall n, n \in X -> x == SUCC n -> P) ->
    x \in NATf X -> P.
intros.
unfold NATf in H.
apply sum_ind with (3:=H1); intros.
 apply H.
 apply unit_elim in H2.
 rewrite H2 in H3; trivial.

 apply H0 with y; trivial.
Qed.

Lemma NATf_stable : stable NATf.
unfold NATf.
apply sum_stable.
 red; red; reflexivity.
 red; red; auto.

 apply cst_stable.
 apply id_stable.
Qed.

Lemma NATf_stable2 : stable2 NATf.
Proof stable2_weaker _ NATf_morph NATf_stable.

End TypeConstructor.

Hint Resolve NATf_mono Fmono_morph.

Section IterationNat.

  Definition NATi := TI NATf.

  Instance NATi_morph : morph1 NATi.
unfold NATi; intros.
apply TI_morph; auto.
Qed.
(*
  Lemma NATi_morph : forall x x', isOrd x -> x == x' -> NATi x == NATi x'.
unfold NATi; intros.
apply TI_morph; auto.
Qed.
*)

  Lemma NATfun_ext : forall x, ext_fun x (fun n => NATf (NATi n)).
do 2 red; intros.
apply NATf_morph.
apply NATi_morph; trivial.
Qed.
(*
  Lemma NATfun_ext : forall x, isOrd x -> ext_fun x (fun n => NATf (NATi n)).
do 2 red; intros.
apply NATf_morph.
apply NATi_morph; trivial.
apply isOrd_inv with x; auto.
Qed.
*)
Hint Resolve NATfun_ext.


Lemma NATi_stable : stable_ord NATi.
apply TI_stable; auto.
apply NATf_stable.
Qed.

Lemma NATi_stable2 : stable2_ord NATi.
unfold NATi.
apply TI_stable2; auto.
apply NATf_stable2.
Qed.

Lemma NATfun_stable : stable_ord (fun n => NATf (NATi n)).
apply compose_stable with (F:=NATf) (G:=NATi); auto with *.
 apply NATf_stable.
 apply NATi_stable.
Qed.

Lemma NATfun_stable2 : stable2_ord (fun n => NATf (NATi n)).
red; red; intros.
apply NATf_stable2 in H1.
revert H1; apply NATf_mono.
apply NATi_stable2; trivial.
Qed.

(* Case analysis *)

Section CaseAnalysis.

  (* Case scheme *)

  Lemma NATi_case : forall (P:set->Prop) o n,
    isOrd o ->
    (forall x x', x \in NATi o -> x == x' -> P x -> P x') ->
    P ZERO ->
    (forall m o', lt o' o -> m \in NATi o' -> P (SUCC m)) ->    
    n \in NATi o -> P n.
intros.
apply TI_elim in H3; auto.
destruct H3.
apply NATf_case with (3:=H4); intros.
 apply H0 with ZERO; trivial.
  apply TI_intro with x; auto.
  apply ZERO_typ_gen.

  symmetry; trivial.

 apply H0 with (SUCC n0); eauto.
 2:symmetry; trivial.
 apply TI_intro with x; auto.
 apply SUCC_typ_gen; auto.
Qed.

  (* Pattern-matching *)

  Variable fZ : set.
  Variable fS : set -> set.

  Definition NATCASE (n:set) :=
    union
   (union2 (subset (singl fZ) (fun _ => n == ZERO))
           (subset (singl (fS (dest_sum n)))
               (fun _ => exists k, n == SUCC k))).


Instance NATCASE_m1 : morph1 fS -> morph1 NATCASE.
do 2 red; intros.
unfold NATCASE.
apply union_morph.
apply union2_morph.
 apply subset_morph.
  reflexivity.

  red; intros.
  rewrite H0; reflexivity.

 apply subset_morph.
  rewrite H0; reflexivity.

  red; intros.
  apply ex_morph; red; intros.
  rewrite H0; reflexivity.
Qed.


Lemma NATCASE_ZERO : NATCASE ZERO == fZ.
unfold NATCASE.
apply eq_intro; intros.
 rewrite union_ax in H; destruct H.
 apply union2_elim in H0; destruct H0.
  apply subset_elim1 in H0.
  apply singl_elim in H0.
  rewrite <- H0; trivial.

  apply subset_elim2 in H0; destruct H0. 
  destruct H1.
  apply NATf_discr in H1; contradiction.

 apply union_intro with fZ; trivial.
 apply union2_intro1.
 apply subset_intro.
  apply singl_intro.
  reflexivity.
Qed.


Lemma NATCASE_SUCC : forall n,
  (forall x, x == n -> fS x == fS n) ->
  NATCASE (SUCC n) == fS n.
unfold NATCASE; intros.
apply eq_intro; intros.
 rewrite union_ax in H0; destruct H0.
 apply union2_elim in H1; destruct H1.
  apply subset_elim2 in H1; destruct H1. 
  symmetry in H2; apply NATf_discr in H2; contradiction.

  apply subset_elim1 in H1.
  apply singl_elim in H1.
  rewrite <- (H _ (dest_sum_inr n)).
  rewrite H1 in H0; trivial.

 apply union_intro with (fS n); trivial.
 apply union2_intro2.
 apply subset_intro.
  apply singl_intro_eq.
  symmetry; auto using dest_sum_inr.

  exists n; reflexivity.
Qed.

Lemma NATCASE_typ :
  forall (P:set->set) o,
  morph1 P ->
  morph1 fS ->
  isOrd o ->
  fZ \in P ZERO ->
  (forall n, n \in NATi o -> fS n \in P (SUCC n)) ->
  forall n,
  n \in NATi (osucc o) ->
  NATCASE n \in P n.
intros.
pattern n; apply NATi_case with (o:=osucc o); intros; auto.
 rewrite <- H6; trivial.

 rewrite NATCASE_ZERO; trivial.

 rewrite NATCASE_SUCC; auto.
 apply H3.
 revert H6; apply TI_mono; auto.
  eauto using isOrd_inv.

  apply olts_le; trivial.
Qed.

End CaseAnalysis.

Lemma NATCASE_morph_gen : forall fZ fZ' fS fS' c c',
  c == c' ->
  fZ == fZ' ->
  (forall x x', c == SUCC x -> x == x' -> fS x == fS' x') ->
  NATCASE fZ fS c == NATCASE fZ' fS' c'.
unfold NATCASE; intros.
apply union_morph.
apply union2_morph.
 apply subset_morph.
  rewrite H0; reflexivity.

  red; intros.
  rewrite H; reflexivity.

 apply eq_intro; intros.
  rewrite subset_ax in H2; destruct H2.
  destruct H3.
  destruct H4.
  apply subset_intro.
   rewrite <- (H1 (ZFpairs.snd c) (ZFpairs.snd c')); auto with *.
    transitivity (SUCC x0); trivial.
    rewrite H4.
    unfold SUCC,inr; rewrite ZFpairs.snd_def; reflexivity.

    rewrite H; reflexivity.

   exists x0; rewrite <- H; trivial.

  rewrite subset_ax in H2; destruct H2.
  destruct H3.
  destruct H4.
  apply subset_intro.
   rewrite (H1 (ZFpairs.snd c) (ZFpairs.snd c')); auto with *.
    rewrite H.
    transitivity (SUCC x0); trivial.
    rewrite H4.
    unfold SUCC,inr; rewrite ZFpairs.snd_def; reflexivity.

    rewrite H; reflexivity.

   exists x0; rewrite H; trivial.
Qed.

Instance NATCASE_morph : Proper
  (eq_set ==> (eq_set ==> eq_set) ==> eq_set ==> eq_set) NATCASE.
do 4 red; intros.
apply NATCASE_morph_gen; auto.
Qed.

(* Fixpoints *)

Require Import ZFfunext ZFfixfuntyp.

Section Recursor.

  Lemma NATi_fix :
    forall (P:set->Prop) o,
    isOrd o ->
    (forall i, isOrd i -> i \incl o ->
     (forall i' m, lt i' i -> m \in NATi i' -> P m) ->
     forall n, n \in NATi i -> P n) ->
    forall n, n \in NATi o -> P n.
intros P o is_ord Prec.
induction is_ord using isOrd_ind; intros; eauto.
Qed.


(* Recursor *)

  Notation prod := ZFcoc.cc_prod.

  Variable eps : set.
  Hypothesis epsOrd : isOrd eps.
  Variable F : set -> set -> set.
  Hypothesis Fm : forall o o' f f',
    isOrd o -> o == o' -> f == f' ->
    F o f == F o' f'.
  Variable U : set -> set -> set.
(*
Hypothesis Um_eq : forall o o', lt o' eps -> o == o' ->
    forall x x', x \in NATi o -> x == x' -> U o x == U o' x'. *)
  Hypothesis Um : forall o o', lt o' eps -> isOrd o -> o \incl o' ->
    forall x x', x \in NATi o -> x == x' -> U o x \incl U o' x'.
  Let Ty o := prod (NATi o) (U o).
  Hypothesis Ftyp : forall o f, isOrd o -> lt (osucc o) eps ->
    f \in Ty o -> F o f \in Ty (osucc o).

  Definition stab_fix_prop :=
    forall o o' f g,
    isOrd o -> lt o' eps -> o \incl o' ->
    f \in Ty o -> g \in Ty o' ->
    fcompat (NATi o) f g ->
    fcompat (NATf (NATi o)) (F o f) (F o' g).

  Hypothesis Fstab : stab_fix_prop.


  Definition NATREC := TIO F.

Lemma Um_eq : forall o o', lt o' eps -> o == o' ->
    forall x x', x \in NATi o -> x == x' -> U o x == U o' x'. 
intros.
apply incl_eq.
 apply Um; auto.
  rewrite H0; apply isOrd_inv with eps; trivial.
  rewrite H0; reflexivity.

 apply Um; auto.
  rewrite H0; trivial.
  apply isOrd_inv with eps; trivial.
  rewrite H0; reflexivity.
  rewrite <- H2; rewrite <- H0; trivial.
  symmetry; trivial.
Qed.

Lemma Umorph : forall o, lt o eps -> ext_fun (NATi o) (U o).
red; red; intros.
apply Um_eq; auto with *.
Qed.

Lemma Umorph' : forall x, lt x eps ->
  ext_fun (sup x (fun o' => NATf (TI NATf o'))) (U x).
red; red; intros.
apply (Umorph x); trivial.
unfold NATi; rewrite TI_eq; auto.
apply isOrd_inv with eps; trivial.
Qed.

Lemma prod_rewr : forall o,
  lt o eps ->
  prod (TI NATf o) (U o) == prod (sup o (fun z => NATf (NATi z))) (U o).
intros.
apply ZFcoc.cc_prod_ext.
(*apply dep_func_ext.*)
2:apply Umorph; trivial.
apply TI_eq; auto.
apply isOrd_inv with eps; trivial.
Qed.

Lemma Umorph'': forall x o,
  lt o eps ->
  lt x o ->
  ext_fun (NATf (TI NATf x)) (U o).
red; red; intros.
apply Um_eq; auto with *.
apply TI_intro with x; auto.
apply isOrd_inv with eps; trivial.
Qed.
(*
Instance Ty_morph : morph1 Ty.
unfold Ty; do 2 red; intros.
apply ZFcoc.cc_prod_ext.
 apply NATi_morph; trivial.

 red; intros.
 apply Um_eq; auto.
 auto.
*)

Lemma prod_rewrs : forall o o',
  lt o' eps ->
  lt o o' ->
  Ty (osucc o) \incl prod (NATf (TI NATf o)) (U o').
intros.
assert (isOrd o').
 apply isOrd_inv with eps; trivial.
assert (isOrd o).
 apply isOrd_inv with o'; trivial.
assert (osucc o \incl o').
 red; intros.
 apply le_lt_trans with o; auto.
apply ZFcoc.cc_prod_covariant.
(*apply dep_func_mono.*)
(* do 2 red; intros.
 apply Um_eq; auto with *.
 apply isOrd_plump with o'; auto.*)

 do 2 red; intros.
 apply Um_eq; auto with *.
 rewrite <- TI_mono_succ in H4; auto.
 apply TI_mono with (osucc o); auto.

 apply TI_mono_succ; auto.
 
 intros.
 apply Um; auto with *.
Qed.

Lemma prod_rewr_weak : forall o o' f,
  lt o eps ->
  lt o' o ->
  f \in Ty o' ->
  F o' f \in prod (NATf (TI NATf o')) (U o).
intros.
apply prod_rewrs; trivial.
apply Ftyp; auto.
 eauto using isOrd_inv.

 apply le_lt_trans with o; trivial.
 apply lt_osucc_compat; trivial.
 apply isOrd_inv with eps; trivial.
Qed.

Definition fincr o :=
 fdirected o (fun z => NATf (NATi z)) (fun z => F z (TIO F z)).
Hint Unfold fincr.


Definition inv z := TIO F z \in Ty z /\ fincr z.


Section InductionStep.


Section TypeStrengthen.
(* An attempt to avoid using monotonicity of U.
   Fails for the moment for limit ordinals... *)
  Variable o : set.
  Hypothesis oo : isOrd o.
  Hypothesis le_eps : o \incl eps.
  Hypothesis ty_lt_o : forall z, lt z o -> TIO F z \in Ty z.

  Let oo' : forall z, lt z o -> isOrd z.
intros.
apply isOrd_inv with eps; try red; auto.
Qed.

  Definition Usup x' a :=
    sup (subset (osucc x') (fun z => a \in NATi z))
               (fun z => U z a).

  Lemma eU_ext : forall a o', isOrd o' ->
 o' \incl eps -> a \in NATi o' ->
 ext_fun (subset o' (fun z => a \in NATi z))
   (fun z => U z a).
 red; red; intros.
 apply Um_eq; auto with *.
  rewrite <- H3.
  apply subset_elim1 in H2; red; auto.

  apply subset_elim2 in H2; destruct H2.
  rewrite H2; trivial.
Qed.

  Lemma eUsup_ext : forall x' o', lt x' eps ->
    lt o' eps ->
    ext_fun (NATf (TI NATf o')) (Usup x').
 red; red; intros.
 unfold Usup.
 apply sup_morph.
  apply subset_morph; auto with *.
  red; intros.
  rewrite H2; reflexivity.

  red; intros.
  apply Um_eq; auto.
   rewrite <- H4.
   apply subset_elim1 in H3.
   apply isOrd_plump with x'; auto.
    eauto using isOrd_inv.

    apply olts_le; trivial.

   apply subset_elim2 in H3; destruct H3.
   rewrite H3; trivial.
Qed.

  Lemma ftyp_weak : forall o' x', lt o' x' -> lt x' o ->
  F o' (TIO F o') \in prod (NATf (TI NATf o')) (Usup x').
intros.
apply ZFcoc.cc_prod_covariant with
  (dom := NATi(osucc o'))(F:=U (osucc o')).
 apply eUsup_ext; try red; auto.
 apply isOrd_trans with x'; try red; auto.

 apply TI_mono_succ; auto.
 apply isOrd_inv with x'; auto.

 red; intros.
 unfold Usup; rewrite sup_ax.
  exists (osucc o'); trivial.
  apply subset_intro; trivial.
  apply lt_osucc_compat; auto.

  apply eU_ext; auto.
   red; intros.
   apply isOrd_plump with x'; auto.
    apply isOrd_inv with (osucc x'); auto.

    apply olts_le; trivial.

    revert H1; apply TI_incl; auto.
    apply lt_osucc_compat; auto.

 apply Ftyp; auto.
  eauto using isOrd_inv.

  apply isOrd_plump with x'; auto.
   apply isOrd_succ; apply isOrd_inv with x'; auto.

   red; intros.
   apply le_lt_trans with o'; auto.

  apply ty_lt_o.
  apply isOrd_trans with x'; trivial.
Qed.

End TypeStrengthen.

Section S1.

  Variable o : set.
  Hypothesis oo : isOrd o.
  Hypothesis le_eps : o \incl eps.
  Hypothesis inv_lt_o : forall z, lt z o -> inv z.

  Let ty_lt_o : forall z, lt z o -> TIO F z \in Ty z.
intros.
apply inv_lt_o; trivial.
Qed.

  Let incr_lt_o : forall z, lt z o -> fincr z.
intros.
apply inv_lt_o; trivial.
Qed.

  Let oo' : forall z, lt z o -> isOrd z.
intros.
apply isOrd_inv with eps; try red; auto.
Qed.


Lemma fincr_ext : forall x x', isOrd x -> lt x' o -> x \incl x' ->
  fcompat (NATi x) (TIO F x) (TIO F x').
intros.
assert (ox: isOrd x').
 apply isOrd_inv with o; auto.
rewrite TIO_eq; auto.
unfold NATi; rewrite TI_eq; auto.
apply prd_sup_lub with (B:=Usup x'); intros; auto with *.
 apply eUsup_ext.
  red; auto.

  apply isOrd_trans with x'; try red; auto.

 apply ftyp_weak with o; auto.
 red; auto.

 apply incr_lt_o.
 apply isOrd_plump with x'; trivial.

 intros.
 rewrite (TIO_eq _ Fm x'); auto.
 apply prd_sup with (A:=fun z => NATf (NATi z))
   (F:=fun z => F z (TIO F z)) (B:=Usup x'); auto; intros.
  apply eUsup_ext.
   red; auto.

   apply isOrd_trans with x'; try red; auto.

  apply ftyp_weak with o; auto.

  red in incr_lt_o; auto.
Qed.
(* proof using monotonicity of U:
apply prd_sup_lub with (B:=U x'); intros; auto.
 apply Umorph''; red; auto.

 apply prod_rewr_weak; try red; auto.

  apply ty_lt_o.
  apply H1 in H2.
  apply isOrd_trans with x'; auto.

 apply incr_lt_o.
 apply isOrd_plump with x'; trivial.

 rewrite (TIO_eq _ Fm x'); auto.
 apply prd_sup with (A:=fun z => NATf (NATi z)) (F:=fun z => F z (TIO F z))
   (B:=U x'); auto; intros.
  apply Umorph''; red; auto.

  apply prod_rewr_weak; trivial.
   red; auto.

   apply ty_lt_o.
   apply isOrd_trans with x'; auto.

  red in incr_lt_o; auto.
Qed.
*)

Lemma fincr_step : fincr o.
red; red; red; intros.
specialize (NATfun_stable2 _ (isOrd_inv _ _ oo H) _ (isOrd_inv _ _ oo H0) _ H1); intro.
set (z := inter2 x y) in H2.
assert (isOrd z).
 apply isOrd_inter2; eauto using isOrd_inv.
assert (lt z o).
 apply isOrd_plump with x; trivial.
 apply inter2_incl1.
rewrite inter2_def in H1; destruct H1.
transitivity (ZFcoc.cc_app (F z (TIO F z)) x0).
 symmetry; apply Fstab; auto with *.
  red; auto.

  apply inter2_incl1.

  apply fincr_ext; auto with *.
  apply inter2_incl1.

 apply Fstab; auto with *.
  red; auto.

  apply inter2_incl2.

  apply fincr_ext; auto with *.
  apply inter2_incl2.
Qed.

End S1.

  Variable o : set.
  Hypothesis lt_eps : lt o eps.
  Hypothesis lt_inv : forall z, lt z o -> inv z.

  Let oo : isOrd o.
apply isOrd_inv with eps; trivial.
Qed.
  Let le_eps : o \incl eps.
red; intros.
apply isOrd_trans with o; trivial.
Qed.

Lemma fincr2 : fincr o.
apply fincr_step; trivial.
Qed.

Lemma ftyp_step : TIO F o \in Ty o.
rewrite TIO_eq; auto.
unfold Ty.
rewrite prod_rewr; trivial.
apply prd_union; auto; intros.
 apply Umorph''; trivial.

 apply prod_rewr_weak; auto.
 apply lt_inv; trivial.

 apply fincr_step; trivial.
Qed.

Lemma finv_step : inv o.
split.
 apply ftyp_step.

 apply fincr_step; trivial.
Qed.

End InductionStep.

  Lemma NATREC_inv : forall o, lt o eps -> inv o.
intros.
assert (isOrd o).
 apply isOrd_inv with eps; trivial.
apply isOrd_ind with (2:=H0); intros.
apply finv_step; auto.
apply isOrd_plump with o; auto.
Qed.


  Lemma NATREC_wt : forall o, lt o eps -> NATREC o \in Ty o.
intros.
destruct NATREC_inv with (1:=H); trivial.
Qed.


  Lemma NATREC_ty_weak : forall o o',
    lt o eps ->
    lt o' o ->
    F o' (TIO F o') \in prod (NATf (TI NATf o')) (U o).
intros.
apply prod_rewr_weak; trivial.
apply NATREC_wt.
apply isOrd_trans with o; trivial.
Qed.

  Lemma NATREC_step : forall o,
    lt o eps ->
    fcompat (NATi o) (NATREC o) (F o (NATREC o)).
intros.
assert (isOrd o).
 apply isOrd_inv with eps; trivial.
unfold NATREC at 1.
rewrite TIO_eq; auto.
unfold NATi; rewrite TI_eq; auto.
apply prd_sup_lub with (B:=U o); intros; auto.
 apply Umorph''; trivial.

 apply NATREC_ty_weak; trivial.

 destruct NATREC_inv with (1:=H); trivial.

 apply Fstab; auto with *.
  apply isOrd_inv with o; auto.

  red; intros; apply isOrd_trans with x; auto.

  apply NATREC_wt.
  apply isOrd_trans with o; trivial.

  apply NATREC_wt; trivial.

  apply fincr_ext with eps; auto with *.
   apply NATREC_inv.

   apply isOrd_inv with  o; trivial.

   red; intros; apply isOrd_trans with x; trivial.
Qed.


Section NATREC_Eqn.

  Variable o : set.
  Hypothesis lt_eps : lt o eps.

  Let o_ord : isOrd o.
apply isOrd_inv with eps; trivial.
Qed.

  Lemma NATREC_expand : forall n,
    n \in NATi o -> ZFcoc.cc_app (NATREC o) n == ZFcoc.cc_app (F o (NATREC o)) n.
intros.
apply NATREC_step; trivial.
Qed.

  Lemma NATREC_eqn :
    NATREC o == ZFcoc.cc_lam (NATi o) (fun x => ZFcoc.cc_app (F o (NATREC o)) x).
intros.
rewrite (ZFcoc.cc_eta_eq (NATi o) (U o) (NATREC o)).
2:apply NATREC_wt; auto.
apply ZFcoc.cc_lam_ext; auto with *.
red; intros.
rewrite <- H0.
apply NATREC_expand; trivial.
Qed.

End NATREC_Eqn.

End Recursor.


Lemma NATREC_morph :
  forall f1 f2,
  (eq_set ==> eq_set ==> eq_set)%signature f1 f2 ->
  forall o1 o2, isOrd o1 ->
  o1 == o2 ->
  NATREC f1 o1 == NATREC f2 o2.
intros.
unfold NATREC.
unfold TIO.
apply TR_morph_gen; trivial; intros.
apply sup_morph; intros; auto.
red; intros.
apply H; auto.
Qed.

Section NatFixpoint.

(* NAT : the least fixpoint *)

  Definition NAT := NATi omega.

  Lemma NAT_continuous : forall F,
    ext_fun omega F ->
    NATf (sup omega F) == sup omega (fun n => NATf (F n)).
intros.
unfold NATf.
rewrite <- sum_cont; auto.
rewrite <- cst_cont.
 reflexivity.

 exists zero; apply zero_omega.
Qed.

  Lemma NAT_eq : NAT == NATf NAT.
unfold NAT, NATi.
apply eq_intro; intros.
 rewrite <- TI_mono_succ; auto.
 apply TI_incl with omega; auto.

 unfold NATf in H at 1.
 rewrite TI_eq in H; auto.
 rewrite (cst_cont UNIT omega) in H; auto.
 2:exists zero; auto.
 rewrite sum_cont in H; auto.
 rewrite sup_ax in H.
 2:do 2 red; intros; apply NATf_morph; eapply NATfun_ext; eauto.
 destruct H.
 rewrite <- TI_mono_succ in H0; auto.
 apply TI_intro with (osucc x); auto.
 apply isOrd_inv with omega; trivial.
Qed.

  Lemma NATi_NAT : forall o,
    isOrd o ->
    NATi o \incl NAT.
induction 1 using isOrd_ind; intros.
unfold NATi.
rewrite TI_eq; auto.
red; intros.
rewrite sup_ax in H2; auto.
destruct H2.
rewrite NAT_eq.
apply NATf_mono with (NATi x); auto.
Qed.

  Lemma ZERO_typ : ZERO \in NAT.
rewrite NAT_eq.
apply ZERO_typ_gen.
Qed.

  Lemma SUCC_typ : forall n, n \in NAT -> SUCC n \in NAT.
intros.
rewrite NAT_eq.
apply SUCC_typ_gen; trivial.
Qed.

  Lemma NAT_fix :
    forall (P:set->Prop),
    (forall o, isOrd o ->
     (forall o' m, lt o' o -> m \in NATi o' -> P m) ->
     forall n, n \in NATi o -> P n) ->
    forall n, n \in NAT -> P n.
intros.
apply NATi_fix with (P:=P) (o:=omega); intros; auto.
apply H with i; trivial.
Qed.

  Lemma NAT_ind : forall (P:set->Prop),
    (forall x x', x \in NAT -> x == x' -> P x -> P x') ->
    P ZERO ->
    (forall n, n \in NAT -> P n -> P (SUCC n)) ->    
    forall n, n \in NAT -> P n.
intros.
elim H2 using NAT_fix; intros.
elim H5 using NATi_case; trivial; intros.
 apply H with x; trivial.
 apply NATi_NAT with o; trivial.

 apply H1; eauto.
 apply NATi_NAT with o'; trivial.
 apply isOrd_inv with o; trivial.
Qed.

  Fixpoint nat2NAT (n:nat) : set :=
    match n with
    | 0 => ZERO
    | S k => SUCC (nat2NAT k)
    end.

  Lemma nat2NAT_reflect : forall x,
    x \in NAT -> exists n, x == nat2NAT n.
intros.
elim H using NAT_ind; intros.
 destruct H2.
 exists x1.
 rewrite <- H1; rewrite H2; reflexivity.

 exists 0; reflexivity.

 destruct H1.
 exists (S x0); unfold SUCC; rewrite H1; reflexivity.
Qed.

End NatFixpoint.

End IterationNat.

(**)
Hint Resolve NATfun_ext.

Section NatConvergence.

Require Import ZFrank.

  Variable o : set.
  Hypothesis limo : limitOrd o.
  Hypothesis diro : isDir o.

  Let oo : isOrd o.
Proof proj1 limo.

  Let zer : forall x, x \in VN o -> zero \in VN o.
intros.
apply VN_incl with x; auto.
red; intros.
elim empty_ax with z; trivial.
Qed.

  Let suc : forall x, x \in VN o -> succ x \in VN o.
unfold succ.
intros.
apply VN_union; trivial.
apply VNlim_pair; auto.
apply VNlim_pair; auto.
Qed.

  Lemma NATf_size_gen :
    forall X, X \in VN o -> NATf X \in VN o.
intros.
unfold NATf.
unfold sum.
apply VN_subset; trivial.
unfold ZFpairs.prodcart.
apply VN_subset; trivial.
apply VNlim_power; trivial.
apply VNlim_power; trivial.
apply VN_union; trivial.
apply VNlim_pair; eauto.
apply VN_union; trivial.
apply VNlim_pair; eauto.
Qed.

  Hypothesis zer_o : zero \in VN o.

  Lemma NATf_size_gen_le : forall X,
    X \incl VN o -> NATf X \incl VN o.
red; intros.
apply NATf_case with (3:=H0); intros.
 rewrite H1.
 unfold ZERO, inl.
 unfold ZFpairs.couple.
 apply VNlim_pair; trivial.
  apply VNlim_pair; trivial.
  apply VNlim_pair; trivial.

 rewrite H2; unfold SUCC.
 unfold inr.
 unfold ZFpairs.couple.
 apply VNlim_pair; trivial.
  apply VNlim_pair; auto.

  apply VNlim_pair; auto.
Qed.

End NatConvergence.

  (* Showing that omega is the closing ordinal for NAT *)

  Lemma NAT_incl_omega : NAT \incl VN omega.
apply TI_pre_fix; auto.
apply NATf_size_gen_le; auto with *.
apply VN_intro; trivial.
apply zero_omega.
Qed.

  Lemma NAT_typ : forall o, isOrd o -> lt omega o -> NAT \in VN o.
intros.
rewrite VN_def; trivial.
exists omega; trivial.
apply NAT_incl_omega.
Qed.


Section NatUniverse.

  (* The universe where we build the inductive type *)
  Variable U : set.
  Hypothesis has_cstr : forall X, X \in U -> sum UNIT X \in U.
  Hypothesis has_empty : empty \in U.
  Hypothesis has_limit : forall F,
    ext_fun omega F ->
    increasing F ->
    (forall n, n \in omega -> F n \in U) -> sup omega F \in U.

  Lemma has_fin_limit : forall n F,
    lt n omega ->
    ext_fun n F ->
    increasing F ->
    (forall m, lt m n -> F m \in U) -> sup n F \in U.
Admitted.

  Lemma NATfun_incr : increasing (fun z => NATf (NATi z)).
red; intros.
apply NATf_mono.
apply TI_mono; auto.
Qed.

  Hint Resolve NATfun_incr.

  Lemma NATi_pre_typ : forall n, lt n omega -> NATi n \in U.
intros.
apply isOrd_sup_elim in H.
destruct H.
revert n H.
induction x; simpl in *; intros.
 elim empty_ax with (1:=H).

 unfold NATi; rewrite TI_eq; auto.
 apply has_fin_limit; intros; auto.
  apply isOrd_trans with (2:=H); auto.
  apply isOrd_sup_intro with (S (S x)); simpl.
  apply lt_osucc_compat; auto.

  apply has_cstr.
  apply IHx.
  apply olts_le in H.
  apply H in H0; trivial.

 apply isOrd_inv with (2:=H); auto.
Qed.

  Lemma NAT_typU : NAT \in U.
unfold NAT, NATi.
rewrite TI_eq; auto.
apply has_limit; intros; auto.
apply has_cstr.
apply NATi_pre_typ; trivial.
Qed.

End NatUniverse.


End Nat_theory.

Hint Resolve NATf_mono Fmono_morph NATfun_ext.

Module Example.
(* Abel's counter-example: *)

Import ZFcoc.

Definition arr A B := cc_prod A (fun _ => B).

Lemma arr_intro : forall A B F,
  (forall x, x \in A -> F x \in B) ->
  cc_lam A F \in arr A B.
Admitted.

Lemma arr_elim : forall f x A B,
  f \in arr A B -> 
  x \in A ->
  cc_app f x \in B.
Admitted.

Definition U o := arr (arr NAT (NATi (osucc o))) NAT.

Definition shift f := cc_lam NAT (fun n =>
  NATCASE ZERO (fun m => m) (cc_app f (SUCC n))).

Lemma shift_typ : forall o f,
  isOrd o ->
  f \in arr NAT (NATi (osucc (osucc o))) ->
  shift f \in arr NAT (NATi (osucc o)).
intros.
unfold shift.
apply arr_intro; intros.
apply NATCASE_typ with (o:=osucc o)(P:=fun _=> NATi (osucc o)); auto.
 admit.
 admit.
 unfold NATi; rewrite TI_mono_succ; auto.
 apply ZERO_typ_gen.

 apply arr_elim with (1:=H0).
 apply SUCC_typ; trivial.
Qed.

Definition loopF o loop :=
  ZFcoc.cc_lam (NATi (osucc o)) (fun _ =>
  ZFcoc.cc_lam (arr NAT (NATi (osucc (osucc o)))) (fun f =>
  NATCASE
    ZERO
    (fun n =>
     NATCASE
       ZERO
       (fun m => cc_app (cc_app loop m) (shift f))
       n)
    (cc_app f ZERO))).

Lemma loopF_typ : forall o lp,
  isOrd o ->
  lp \in arr (NATi o) (U o) ->
  loopF o lp \in arr (NATi (osucc o)) (U (osucc o)).
unfold loopF, U; intros.
apply arr_intro; intros y ?.
apply arr_intro; intros f ?.
apply NATCASE_typ with (o:=osucc o) (P:=fun _ => NAT); auto.
 admit.
 admit.

 apply ZERO_typ.

 intros.
 apply NATCASE_typ with (o:=o) (P:=fun _=>NAT); auto.
  admit.
  admit.

  apply ZERO_typ.

  intros.
  apply arr_elim with (arr NAT (NATi (osucc o))).
   apply arr_elim with (NATi o); trivial.

   apply shift_typ; trivial.

 apply arr_elim with NAT; trivial.
 apply ZERO_typ.
Qed.

 Lemma sfp : forall o, isOrd o ->
   stab_fix_prop o loopF (fun _ => U).
red; red; intros.
unfold loopF.
rewrite <- TI_mono_succ in H6; auto.
rewrite cc_beta_eq; auto.
rewrite cc_beta_eq; auto.
 apply cc_lam_ext.
  admit.

  red; intros.
  apply NATCASE_morph_gen; intros; auto with *.
   rewrite H8; auto with *.
  apply NATCASE_morph_gen; intros; auto with *.
  apply cc_app_morph.
   rewrite <- H12.
   apply H5.
   assert (cc_app x0 ZERO \in (NATi (osucc (osucc o0)))).
    apply arr_elim with NAT; auto.
    apply ZERO_typ.
   apply TI_elim in H13; auto.
   destruct H13.
   rewrite H9 in H14.
   assert (x1 \in NATi x3).
    apply NATf_case with (3:=H14); intros.
     symmetry in H15; apply NATf_discr in H15; contradiction.

     apply SUCC_inj in H16.
     rewrite H16; trivial.
   apply TI_elim in H15; eauto using isOrd_inv.
   destruct H15.
   rewrite H11 in H16.
   assert (x2 \in NATi x4).
    apply NATf_case with (3:=H16); intros.
     symmetry in H17; apply NATf_discr in H17; contradiction.

     apply SUCC_inj in H18.
     rewrite H18; trivial.
   revert H17; apply TI_mono; eauto using isOrd_inv.
   apply olts_le in H13.
   apply H13 in H15.
   apply olts_le in H15; auto.

   unfold shift.
   apply cc_lam_ext; auto with *.
   red; intros.
   apply NATCASE_morph; auto with *.
    red; intros; auto.

    rewrite H8; rewrite H14; reflexivity.

 revert H6; apply TI_mono; auto with *.
  eauto using isOrd_inv.

  red; intros.
  apply ole_lts; eauto using isOrd_inv.
  apply olts_le in H6.
  rewrite H6; trivial.
Qed.


End Example.