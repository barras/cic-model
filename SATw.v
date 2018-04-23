
Require Import ZF ZFpairs ZFsum ZFrelations ZFord ZFfix ZFgrothendieck ZFfunext.
Require Import ZFlambda Sat SATtypes.
Require Import Lambda.
Module Lc:=Lambda.
Require Import ZFcoc.

(** The abstract set-theoretical model of W-types, upon which the realizability
    interpretation is built.
 *)
Module Type W_PartialModel.

  Parameter W_F : set -> (set -> set) -> set -> set.
  Parameter W_F_mono : forall A B, morph1 B ->
    Proper (incl_set==>incl_set) (W_F A B).
  Existing Instance W_F_mono.
  Parameter W_F_ext : forall A A' B B' X X',
    A == A' ->
    eq_fun A B B' -> X == X' -> W_F A B X == W_F A' B' X'.
  Parameter mkw : set -> set -> set.
  Parameter mkw_morph: morph2 mkw.
  Parameter w1 w2 : set -> set.
  Parameter w1_morph : morph1 w1.
  Parameter w2_morph : morph1 w2.
  Parameter w1_eq : forall x f, w1 (mkw x f) == x.
  Parameter w2_eq : forall x f, w2 (mkw x f) == f.
  Parameter discr_mt_mkw : forall x f,
    ~ empty == mkw x f.

  Parameter W_F_intro : forall A B, morph1 B ->
    forall X x f,
    x ∈ A ->
    f ∈ (Π i ∈ B x, cc_bot X) ->
    mkw x f ∈ W_F A B X.
  Parameter W_F_elim : forall A B, morph1 B ->
    forall X x,
    x ∈ W_F A B X ->
    w1 x ∈ A /\ w2 x ∈ (Π _ ∈ B (w1 x), cc_bot X) /\ x == mkw (w1 x) (w2 x).

  Parameter W_ord : set -> (set -> set) -> set.
  Parameter W_ord_ord : forall A B, morph1 B ->
    isOrd (W_ord A B).

  Parameter W_fix : forall A B, morph1 B ->
    TI (W_F A B) (W_ord A B) ==
    W_F A B (TI (W_F A B) (W_ord A B)).

  Parameter G_W_F : forall A B,
       morph1 B ->
       forall U,
       grot_univ U ->
       A ∈ U ->
       (forall a, a ∈ A -> B a ∈ U) ->
       forall X, X ∈ U -> W_F A B X ∈ U.
  Parameter G_W_ord : forall A B, morph1 B ->
    forall U, grot_univ U -> omega ∈ U ->
    A ∈ U -> (forall a : set, a ∈ A -> B a ∈ U) -> W_ord A B ∈ U.

  Parameter WREC : (set -> set -> set) -> set -> set.
  Parameter WREC_morph : Proper ((eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) WREC.

  Record WREC_assumptions A B O M U : Prop := WREC_intro {
    WBm : morph1 B;
    Wo : isOrd O;
    WMm : morph2 M;
    WUm : morph2 U;
    WU_mt : forall o x, empty ∈ U o x;
    WMtyp : forall o,
        o ∈ osucc O ->
        forall f,
        f ∈ (Π x ∈ cc_bot (TI (W_F A B) o), U o x) ->
        M o f
        ∈ (Π x ∈ cc_bot (TI (W_F A B) (osucc o)), U (osucc o) x);
    WMirr : forall o o' f g,
        isOrd o ->
        o ⊆ o' ->
        o' ∈ osucc O ->
        f ∈ (Π x ∈ cc_bot (TI (W_F A B) o), U o x) ->
        g ∈ (Π x ∈ cc_bot (TI (W_F A B) o'), U o' x) ->
        fcompat (cc_bot (TI (W_F A B) o)) f g ->
        fcompat (cc_bot (TI (W_F A B) (osucc o))) (M o f) (M o' g);
    WUmono : forall o o' x,
        isOrd o ->
        o ⊆ o' ->
        o' ∈ osucc O ->
        x ∈ cc_bot (TI (W_F A B) o) ->
        U o x ⊆ U o' x
  }.

  Parameter WREC_typ : forall A B O M U,
    WREC_assumptions A B O M U ->
    forall o, isOrd o -> o ⊆ O ->
    WREC M o ∈ (Π x ∈ cc_bot (TI (W_F A B) o), U o x).
  Parameter WREC_irr : forall A B O M U,
    WREC_assumptions A B O M U ->
    forall o o' x, isOrd o -> isOrd o' -> o ⊆ o' -> o' ⊆ O ->
    x ∈ cc_bot (TI (W_F A B) o) ->
    cc_app (WREC M o) x == cc_app (WREC M o') x.
  Parameter WREC_unfold : forall A B O M U,
    WREC_assumptions A B O M U ->
    forall o n, isOrd o -> o ⊆ O ->
    n ∈ TI (W_F A B) (osucc o) ->
    cc_app (WREC M (osucc o)) n == cc_app (M o (WREC M o)) n.
(*  Parameter WREC_eqn : forall A B O M U,
    WREC_assumptions A B O M U ->
    forall o n,
       isOrd o ->
       o ⊆ O ->
       n ∈ TI (W_F A B) o ->
       cc_app (WREC M o) n == cc_app (M o (WREC M o)) n.*)
  Parameter WREC_strict : forall A B O M U,
    WREC_assumptions A B O M U ->
    forall o,
       isOrd o -> o ⊆ O -> cc_app (WREC M o) empty == empty.

End W_PartialModel.

Module W_Facts (M:W_PartialModel).
Import M.

Lemma mt_not_in_W_F : forall A B, morph1 B ->
    forall o x,
    isOrd o -> x ∈ TI (W_F A B) o -> ~ x == empty.
intros.
apply TI_elim in H1; auto with *.
destruct H1.
apply W_F_elim in H2; trivial.
destruct H2 as (_,(_,eqx)); rewrite eqx.
intros h; symmetry in h; apply discr_mt_mkw in h; trivial.
Qed.

Lemma W_stages : forall A B, morph1 B ->
    forall o, isOrd o ->
    TI (W_F A B) o ⊆ TI (W_F A B) (W_ord A B).
intros A B Bm o oo.
elim oo using isOrd_ind; intros.
red; intros.
apply TI_elim in H2; auto with *.
destruct H2 as (o',lty,tyz).
rewrite W_fix; trivial.
revert tyz; apply W_F_mono; auto.
Qed.
Lemma WREC_eqn : forall A B O M U,
    WREC_assumptions A B O M U ->
    forall o n,
       isOrd o ->
       o ⊆ O ->
       n ∈ TI (W_F A B) o ->
       cc_app (WREC M o) n == cc_app (M o (WREC M o)) n.
intros.
apply TI_inv in H2; auto with *.
2:apply W_F_mono; trivial.
2:apply (WBm _ _ _ _ _ H).
destruct H2 as (o',lto,tyn).
assert (oo' : isOrd o') by eauto using isOrd_inv.
assert (leo : o' ⊆ O).
 red; intros; apply isOrd_trans with o'; auto.
  apply Wo with (1:=H).
  apply H1; trivial.
rewrite <- WREC_irr with (1:=H)(o:=osucc o'); auto with *.
 rewrite WREC_unfold with (1:=H)(4:=tyn); auto with *.
apply (WMirr _ _ _ _ _ H); auto with *.
 apply ole_lts; trivial.
 apply WREC_typ with (1:=H); auto.
 apply WREC_typ with (1:=H); auto.

 red; intros.
 apply WREC_irr with (1:=H); auto with *.

red; intros.
apply isOrd_plump with o'; trivial.
 apply isOrd_inv with (osucc o'); auto.
 apply olts_le; trivial.
Qed.
(*
Lemma WREC_unfold' : forall A B O M U,
    WREC_assumptions A B O M U ->
    forall o n, isOrd o -> o ⊆ O ->
    n ∈ TI (W_F A B) (osucc o) ->
    cc_app (WREC M (osucc o)) n == cc_app (M o (WREC M o)) n.
*)


Lemma WREC_ext A A' B B' F F' U U' o o' :
  isOrd o ->
  isOrd o' ->
  o ⊆ o' ->
  A == A' ->
  eq_fun A B B' ->
  WREC_assumptions A B o F U ->
  WREC_assumptions A' B' o' F' U' ->
  (forall z, isOrd z -> z ⊆ o ->
   forall f f',
   f ∈ (Π x ∈ cc_bot (TI (W_F A B) z), U z x) ->
   f' ∈ (Π x ∈ cc_bot (TI (W_F A' B') o'), U' o' x) ->
   fcompat (cc_bot (TI (W_F A B) z)) f f' ->
   fcompat (TI (W_F A B) (osucc z)) (F z f) (F' o' f')) -> 
  fcompat (cc_bot (TI (W_F A B) o)) (WREC F o) (WREC F' o').
intros oo oo' ole eqA eqB oko oko' eqF.
elim oo using isOrd_ind; intros.
red; intros.
apply cc_bot_ax in H2; destruct H2.
 rewrite H2; rewrite WREC_strict with (1:=oko); auto with *.
 rewrite WREC_strict with (1:=oko'); auto with *.

 apply TI_inv in H2; auto with *.
 2:apply W_F_mono.
 2:apply (WBm _ _ _ _ _ oko).
 destruct H2 as (o'',?,?).
 assert (o_o'' : isOrd o'') by eauto using isOrd_inv.
 assert (o''_y : osucc o'' ⊆ y).
  red; intros; apply le_lt_trans with o''; auto.
 rewrite WREC_eqn with (1:=oko'); auto with *.
  transitivity (cc_app (F o'' (WREC F o'')) x).
   rewrite WREC_eqn with (1:=oko); auto with *.
    symmetry; apply (WMirr _ _ _ _ _ oko); auto with *.
     apply ole_lts; trivial.
     apply WREC_typ with (1:=oko); auto with *.
     apply WREC_typ with (1:=oko); auto with *.

     red; intros.
     apply WREC_irr with (1:=oko); auto with *.

    revert H3; apply TI_mono; auto with *.
    apply W_F_mono.
    apply (WBm _ _ _ _ _ oko).

   red in eqF; apply eqF; auto with *.
    apply WREC_typ with (1:=oko); auto with *.
    apply WREC_typ with (1:=oko'); auto with *.

  assert (x ∈ TI (W_F A' B') (osucc o'')).
   revert H3; apply eq_elim; apply TI_morph_gen; auto with *.
   red; intros; apply W_F_ext; trivial.
  revert H4; apply TI_mono; auto with *.
   apply W_F_mono.
   apply (WBm _ _ _ _ _ oko').

   transitivity y; trivial.
   transitivity o; trivial.
Qed.

End W_Facts.

Set Implicit Arguments.

(** W-types *)

Module Make (W:W_PartialModel).

Module WFacts := W_Facts W.
Import W.
Export WFacts.
Existing Instance W_F_mono.

Section Wtypes.

Variable A : set.
Variable B : set -> set.
Hypothesis B_morph : morph1 B.
Let Bext : ext_fun A B.
auto with *.
Qed.

Notation WF := (W_F A B).

Variable RA : set -> SAT.
Variable RB : set -> set -> SAT.
Hypothesis RA_morph : Proper (eq_set ==> eqSAT) RA.
Hypothesis RB_morph : Proper (eq_set ==> eq_set ==> eqSAT) RB.

Definition rW (X:set->SAT) (w:set) : SAT :=
  sigmaReal RA
    (fun x f => piSAT0 (fun i => i ∈ B x) (RB x) (fun i => X (cc_app f i)))
    (couple (w1 w) (w2 w)).

Lemma rW_morph :
   Proper ((eq_set ==> eqSAT) ==> eq_set ==> eqSAT) rW.
do 3 red; intros.
unfold rW.
apply sigmaReal_morph_gen; auto with *.
 do 2 red; intros.
 apply piSAT0_morph; intros; auto with *.
  red; intros.
  rewrite H1; reflexivity.

  apply RB_morph; auto with *.

  apply H.
  rewrite H2; reflexivity.

 rewrite H0; reflexivity.
Qed.
Hint Resolve rW_morph.


Lemma rW_mono_gen' Y X X':
  (forall x x', x ∈ cc_bot Y -> x==x' -> inclSAT (X x) (X' x')) ->
  forall x x', x ∈ WF Y -> x==x' -> inclSAT (rW X x) (rW X' x').
intros Xmono x x' xty eqx'.
unfold rW.
apply cartSAT_mono.
 rewrite eqx'; reflexivity.

 eapply piSAT0_mono with (f:=fun x => x); auto with *.
  intros; rewrite eqx'; trivial.

  intros; rewrite eqx'; reflexivity.

  intros i ity.
  apply Xmono.
  2:rewrite eqx'; reflexivity.
  rewrite snd_def.
  apply W_F_elim in xty; trivial.
  destruct xty as (xty,(fty,_)); auto.
  assert (ity' : i ∈ B (w1 x)).
   revert ity; apply eq_elim; apply Bext.
    rewrite fst_def, <-eqx'; trivial.
    rewrite fst_def, <-eqx'; reflexivity.
  apply cc_prod_elim with (1:=fty) (2:=ity').
Qed.

Lemma rW_mono_gen Y X X':
  (forall x, x ∈ cc_bot Y -> inclSAT (X x) (X' x)) ->
  forall x, x ∈ WF Y -> inclSAT (rW X x) (rW X' x).
intros Xmono x xty.
apply cartSAT_mono; auto with *.
eapply piSAT0_mono with (f:=fun x => x); auto with *.
intros i ity.
apply Xmono.
rewrite snd_def.
apply W_F_elim in xty; trivial.
destruct xty as (xty,(fty,_)); auto.
assert (ity' : i ∈ B (w1 x)).
 revert ity; apply eq_elim; apply Bext.
  rewrite fst_def; trivial.
  rewrite fst_def; reflexivity.
apply cc_prod_elim with (1:=fty) (2:=ity').
Qed.

Lemma rW_mono FX X X':
  FX ⊆ WF FX ->
  inclFam (cc_bot FX) X X' ->
  inclFam FX (rW X) (rW X').
red; intros.
apply H in H1.
revert H1; apply rW_mono_gen; trivial.
Qed.

Lemma rW_irrel (R R' : set -> SAT) (o : set) :
 isOrd o ->
 (forall x x' : set, x ∈ cc_bot (TI WF o) -> x == x' -> eqSAT (R x) (R' x')) ->
 forall x x' : set,
 x ∈ TI WF (osucc o) -> x == x' -> eqSAT (rW R x) (rW R' x').
intros.
rewrite TI_mono_succ in H1; auto with *.
split.
 apply rW_mono_gen' with (Y:=TI WF o); auto.
 intros.
 rewrite H0 with (2:=H4); auto with *.

 apply rW_mono_gen' with (Y:=TI WF o); auto with *.
  intros.
  rewrite H0 with (2:=symmetry H4); auto with *.
  rewrite <- H4; trivial.

  rewrite <- H2; trivial.
Qed.
(*
Lemma rW_irrel (R R' : set -> SAT) (o : set) :
 isOrd o ->
 (forall x x' : set, x ∈ TI WF o -> x == x' -> eqSAT (R x) (R' x')) ->
 forall x x' : set,
 x ∈ TI WF (osucc o) -> x == x' -> eqSAT (rW R x) (rW R' x').
intros.
unfold rW.
unfold sigmaReal.
apply interSAT_morph.
apply indexed_relation_id; intros S.
apply prodSAT_morph; auto with *.
apply piSAT0_morph; intros; auto with *.
 red; intros.
 rewrite H2; reflexivity.

 apply prodSAT_morph; auto with *.
 apply piSAT0_morph; intros; auto with *.
 apply condSAT_morph_gen.
  rewrite H2; reflexivity.

  intros.
  apply H0.
   rewrite TI_mono_succ in H1; auto with *.
   2:apply W_F_mono; trivial.
   unfold W_F in H1.
   apply W_F_elim in H1; trivial.
   destruct H1 as (_,(?,_)); auto.
   apply fst_morph in H3; rewrite fst_def in H3.
   rewrite <- H3 in H5.
   specialize H1 with (1:=H5).
   rewrite cc_bot_ax in H1; destruct H1; trivial.
   contradiction.

   rewrite H2; reflexivity.
Qed.
*)
Definition WC x f := COUPLE x f.

Lemma Real_WC_gen X RX a b x f :
  Proper (eq_set==>eqSAT) RX ->
  mkw a b ∈ WF X ->
  inSAT x (RA a) ->
  inSAT f (piSAT0 (fun i => i ∈ B a) (RB a) (fun i => RX (cc_app b i))) ->
  inSAT (WC x f) (rW RX (mkw a b)).
intros.
unfold rW, WC.
apply Real_couple; trivial.
 do 3 red; intros.
 apply piSAT0_morph; intros.
  red; intros.
  rewrite H3; reflexivity.

  apply RB_morph; auto with *.

  rewrite H4; reflexivity.

 rewrite w1_eq; trivial.

 revert H2; apply piSAT0_morph.
  red; intros.
  rewrite w1_eq; reflexivity.

  intros.
  rewrite w1_eq; reflexivity.

  intros.
  rewrite w2_eq; reflexivity.
Qed.

Definition WCASE b n := Lc.App n b.

Lemma WC_iota b x f :
  Lc.redp (WCASE b (WC x f)) (Lc.App2 b x f).
unfold WCASE, WC.
apply COUPLE_iota.
Qed.


Lemma Real_WCASE_gen X RX C n nt bt:
  Proper (eq_set ==> eqSAT) C ->
  n ∈ WF X ->
  inSAT nt (rW RX n) ->
  inSAT bt (piSAT0 (fun x => x ∈ A) RA (fun x =>
            piSAT0 (fun f => f ∈ cc_arr (B x) (cc_bot X))
                   (fun f => piSAT0 (fun i => i ∈ B x) (RB x)
                      (fun i => RX (cc_app f i)))
                   (fun f => C (mkw x f)))) ->
  inSAT (WCASE bt nt) (C n).
intros Cm nty xreal breal.
destruct W_F_elim with (2:=nty) as (ty1,(ty2,n_eq)); trivial.
setoid_replace (C n) with (C (mkw (fst (couple (w1 n) (w2 n))) (snd (couple (w1 n) (w2 n))))).
 2:rewrite fst_def, snd_def, <-n_eq; reflexivity.
eapply Real_sigma_elim with (C:=fun c => C (mkw (fst c) (snd c))) (4:=xreal).
3:apply couple_intro_sigma with (2:=ty1)(B:=fun a=>Π _ ∈ B a, cc_bot X)(3:=ty2).
 do 2 red; intros.
 apply cc_arr_morph; auto with *.

 do 2 red; intros.
 rewrite H; reflexivity.

 do 2 red; intros.
 apply cc_arr_morph; auto with *.

 revert breal; apply piSAT0_morph; auto with *.
 intros.
 apply piSAT0_morph; auto with *.
  reflexivity.
 intros.
 rewrite fst_def, snd_def.
 reflexivity.
Qed.

(*********************************)
(* Fixpoint *)

Definition W' := TI WF (W_ord A B).

Lemma W'_eq : W' == WF W'.
unfold W' at 2.
rewrite <- W_fix; auto with *.
unfold W'.
reflexivity.
Qed.

Lemma nmt_W' : ~ empty ∈ W'.
intro.
apply mt_not_in_W_F in H; auto with *.
apply W_ord_ord; trivial.
(*unfold W_ord.
apply Ffix_o_o; auto with *.
 apply Wf_mono'; trivial.
apply Wf_typ'; trivial.*)
Qed.
Hint Resolve nmt_W'.

(*Definition rWi := fixSAT W' rW.

Lemma rWi_neutral S :
  inclSAT (rWi empty) S.
intros.
apply fixSAT_outside_domain; auto with *.
intros.
apply rW_mono; trivial.
rewrite <- W'_eq; reflexivity.
Qed.

Lemma rWi_eq x :
  x ∈ W' ->
  eqSAT (rWi x) (rW rWi x).
intros xty.
apply fixSAT_eq; auto with *.
intros.
apply rW_mono; trivial.
rewrite <- W'_eq; reflexivity.
Qed.

Lemma Real_WC o n x f :
  isOrd o ->
  n ∈ TI WF (osucc o) ->
  inSAT x (RA (fst n)) ->
  inSAT f (piSAT0 (fun i => i ∈ B (fst n)) (RB (fst n)) (fun i => rWi (cc_app (snd n) i))) ->
  inSAT (WC x f) (rWi n).
intros.
rewrite rWi_eq.
2:revert H0; apply W_stages'; auto with *.
assert (eqn : n == couple (fst n) (snd n)).
 rewrite TI_mono_succ in H0; auto with *.
 apply sigma_elim in H0; auto with *.
 apply H0.
setoid_replace (rW rWi n) with (rW rWi (couple (fst n) (snd n))).
2:apply rW_morph; auto with *.
2:apply fixSAT_morph; auto with *.
2:apply rW_morph.
eapply Real_WC_gen with (X:=W'); auto with *.
 do 2 red; intros.
 apply fixSAT_morph; auto with *.
 apply rW_morph.

 rewrite <- eqn.
 rewrite <- W'_eq.
 revert H0; apply W_stages'; auto with *.

 apply piSAT0_intro; intros.
  apply sat_sn in H2; trivial.
 apply piSAT0_elim' in H2; red in H2.
 specialize H2 with (1:=H3) (2:=H4).
 assert (tysub : cc_app (snd n) x0 ∈ cc_bot (TI WF o)).
  rewrite TI_mono_succ in H0; auto with *.
  apply W_F_elim in H0; trivial.
  apply H0; trivial.
 rewrite cc_bot_ax in tysub; destruct tysub.
  rewrite H5 in H2.
  revert H2; apply rWi_neutral; trivial.

  rewrite condSAT_ok; trivial.
  apply mt_not_in_W_F in H5; trivial.
Qed.
*)

(*********************************)
(* Iterated operator *)

Definition rWi o := tiSAT WF rW o.

Instance rWi_morph :
  Proper (eq_set ==> eq_set ==> eqSAT) rWi.
apply tiSAT_morph; auto.
Qed.

Lemma rWi_mono o1 o2:
  isOrd o1 ->
  isOrd o2 ->
  o1 ⊆ o2 ->
  forall x,
  x ∈ TI WF o1 ->
  eqSAT (rWi o1 x) (rWi o2 x).
intros.
apply tiSAT_mono; trivial.
 apply W_F_mono; trivial.

 intros; apply rW_irrel with (o:=o'); trivial.
 intros; apply H5; trivial.
 apply cc_bot_ax in H8; destruct H8;[right|left]; trivial.
 intros h; apply mt_not_in_W_F in h; auto.
Qed.

Lemma rWi_succ_eq o x :
  isOrd o ->
  x ∈ TI WF (osucc o) ->
  eqSAT (rWi (osucc o) x) (rW (rWi o) x).
intros.
apply tiSAT_succ_eq; auto.
 apply W_F_mono; trivial.

 intros; apply rW_irrel with (o:=o'); trivial.
 intros; apply H3; trivial.
 apply cc_bot_ax in H6; destruct H6;[right|left]; trivial.
 intros h; apply mt_not_in_W_F in h; auto.
Qed.
(*
Lemma rWi_fix x :
  x ∈ W_F A B ->
  eqSAT (rWi W_omega x) (rW (rWi omega) x).
intros.
apply tiSAT_eq; auto with *.
 apply W_F_mono; trivial.

 
intros; apply rW_irrel with (o:=o'); trivial.
Qed.
*)

Lemma rWi_neutral o :
  isOrd o ->
  eqSAT (rWi o empty) neuSAT.
intros.
apply tiSAT_outside_domain; auto with *.
 intros; apply rW_irrel with (o:=o'); trivial.
 intros; apply H2; trivial.
 apply cc_bot_ax in H5; destruct H5;[right|left]; trivial.
 intros h; apply mt_not_in_W_F in h; auto.

 intro.
 apply mt_not_in_W_F in H0; auto with *.
Qed.


Lemma Real_WC o n x f :
  isOrd o ->
  n ∈ TI WF (osucc o) ->
  inSAT x (RA (w1 n)) ->
  inSAT f (piSAT0 (fun i => i ∈ B (w1 n)) (RB (w1 n)) (fun i => rWi o (cc_app (w2 n) i))) ->
  inSAT (WC x f) (rWi (osucc o) n).
intros.
rewrite rWi_succ_eq; trivial.
rewrite TI_mono_succ in H0; trivial.
2:apply W_F_mono; trivial.
assert (nty := H0).
apply W_F_elim in H0; trivial.
destruct H0 as (?,(?,?)).
rewrite (rW_morph (rWi_morph (reflexivity o)) H4).
apply Real_WC_gen with (TI WF o); auto with *.
 apply rWi_morph; reflexivity.
 rewrite <- H4; trivial.
Qed.

Lemma Real_WCASE o C n nt bt:
  isOrd o ->
  Proper (eq_set ==> eqSAT) C ->
  n ∈ TI WF (osucc o) ->
  inSAT nt (rWi (osucc o) n) ->
  inSAT bt (piSAT0 (fun x => x ∈ A) RA (fun x =>
            piSAT0 (fun f => f ∈ cc_arr (B x) (cc_bot (TI WF o)))
                   (fun f => piSAT0 (fun i => i ∈ B x) (RB x) (fun i => rWi o (cc_app f i)))
                   (fun f => C (mkw x f)))) ->
  inSAT (WCASE bt nt) (C n).
intros oo Cm nty nreal breal.
rewrite rWi_succ_eq in nreal; trivial.
rewrite TI_mono_succ in nty; auto with *.
apply Real_WCASE_gen with (2:=nty) (3:=nreal); trivial.
Qed.

(** * Structural fixpoint: *)

Lemma G_sat o x t m (X:SAT):
  isOrd o ->
  x ∈ TI WF o ->
  inSAT t (rWi o x) ->
  inSAT m X ->
  inSAT (Lc.App2 WHEN_COUPLE t m) X.
intros oo xty xsat msat.
apply TI_elim in xty; auto with *.
destruct xty as (o',o'lt,xty).
assert (isOrd o') by eauto using isOrd_inv.
assert (osucc o' ⊆ o).
 red; intros; apply le_lt_trans with o'; trivial.
assert (xty' : x ∈ TI WF (osucc o')).
 rewrite TI_mono_succ; auto with *.
rewrite <- rWi_mono with (o1:=osucc o') in xsat; auto.
rewrite rWi_succ_eq in xsat; trivial.
eapply WHEN_COUPLE_sat with (1:=xsat); trivial.
Qed.

(* specialized fix *)

Definition WFIX := FIXP WHEN_COUPLE.

Lemma WC_iotafix m x f :
  Lc.redp (Lc.App (WFIX m) (WC x f)) (Lc.App2 m (WFIX m) (WC x f)).
apply FIXP_sim.
intros.
apply WHEN_COUPLE_iota; trivial.
unfold is_couple, WC, COUPLE; eauto.
Qed.


(* m is always used with guarded arguments, so its domain does not
   include empty *)
Lemma WFIX_sat : forall o m X,
  let FIX_ty o := piSAT0 (fun n => n ∈ cc_bot (TI WF o)) (rWi o) (X o) in
  let FIX_ty' o := piSAT0 (fun n => n ∈ TI WF o) (rWi o) (X o) in
  isOrd o ->
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ TI WF y ->
   inclSAT (X y n) (X y' n)) ->
  inSAT m (piSAT0 (fun o' => o' ∈ osucc o)
             (fun o1 => FIX_ty o1) (fun o1 => FIX_ty' (osucc o1))) ->
  inSAT (WFIX m) (FIX_ty o).
intros o m X FIX_ty FIX_ty' oo Xmono msat.
apply FIXP_sat0 with (*(6:=WHEN_COUPLE_neutral)*) (7:=G_sat) (8:=msat); trivial; intros.
 rewrite cc_bot_ax in H1; destruct H1.
  left; rewrite H1; apply rWi_neutral; trivial.

  right.
  apply TI_elim in H1; auto with *.
  destruct H1 as (z,zty,xty).
  exists z; trivial.
  rewrite TI_mono_succ; auto with *.
   apply isOrd_inv with y; trivial.

 exists empty; trivial.

 intros.
 apply rWi_mono; trivial.

intros; apply neuSAT_def; apply WHEN_COUPLE_neutral; apply neuSAT_def; trivial.
Qed.
(*
Lemma WFIX_sat_trunc : forall o m X,
  let FIX_ty o := piSAT0 (fun n => n ∈ cc_bot (TI WF o)) (rWi o) (X o) in
  let FIX_ty' o := piSAT0 (fun n => n ∈ TI WF o) (rWi o) (X o) in
  isOrd o ->
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ TI WF y ->
   inclSAT (X y n) (X y' n)) ->
  inSAT m (piSAT0 (fun o' => o' ∈ osucc o)
             (fun o1 => FIX_ty o1) (fun o1 => FIX_ty' (osucc o1 ∩ o))) ->
  inSAT (WFIX m) (FIX_ty o).
intros.
assert (inSAT (WFIX m) (piSAT0 (fun n => n ∈ cc_bot (TI WF o)) (rWi o) (X (o∩o)))).
 apply WFIX_sat with (X:=fun o' => X (o'∩o)); trivial.

 intros.
 apply H0; auto with *.
  apply isOrd_inter2; trivial.
  apply isOrd_inter2; trivial.
 admit.
 apply inter2_incl2.
 admit.

 revert H1; apply piSAT0_mono with (f:=fun x=>x); auto with *.
  intros.
  apply piSAT0_mono with (f:=fun x=>x); auto with *.
  intros.
  apply H0; auto with *.
  apply isOrd_inter2; trivial.
  apply isOrd_inv with (osucc o); auto.
  apply isOrd_inv with (osucc o); auto.
  apply inter2_incl1.
  apply olts_le in H1; trivial.
admit.

  intros.
  apply piSAT0_mono with (f:=fun x=>x); auto with *.
   admit.

  intros.


ter2; trivial.


 admit.
*)

Lemma WREC_sat o F RF  U RU :
  Proper (eq_set==>eq_set==>eq_set==>eqSAT) RU ->
  isOrd o ->
  WREC_assumptions A B o F U ->
  (forall o' o'' x y y', isOrd o' -> isOrd o'' -> o' ⊆ o'' -> o'' ⊆ o ->
   x ∈ TI (W_F A B) o' ->
   y ∈ U o' x ->
   y == y' ->
   inclSAT (RU o' x y) (RU o'' x y')) ->
  let FIX_ty o' f :=
      piSAT0 (fun n => n ∈ cc_bot (TI (W_F A B) o'))
             (rWi o')
             (fun n => RU o' n (cc_app f n)) in
  (forall o' f u,
   isOrd o' ->
   o' ⊆ o ->
   f ∈ (Π w ∈ cc_bot (TI (W_F A B) o'), U o' w) ->
   inSAT u (FIX_ty o' f) ->
   inSAT (Lc.App RF u) (FIX_ty (osucc o') (F o' f))) ->
  inSAT (WFIX RF) (FIX_ty o (WREC F o)).
intros RUm oo ty RUmono FIX_ty satF.
eapply WFIX_sat with (X:=fun o n => RU o n (cc_app (WREC F o) n)); trivial.
 intros.
 apply RUmono; auto.
  apply cc_prod_elim with (dom := cc_bot (TI (W_F A B) y)) (F := U y); auto.
  apply WREC_typ with (1:=ty); trivial.
  transitivity y'; trivial.

  eapply WREC_irr with (1:=ty); auto.

 apply piSAT0_intro'. 
 2:exists o; apply lt_osucc; trivial.
 intros.
 assert (xo : isOrd x) by eauto using isOrd_inv.
 apply olts_le in H.
(* apply inSAT_exp;[right;apply sat_sn in H0;trivial|].*)
 assert (Wty : WREC F x ∈ Π w ∈ cc_bot (TI (W_F A B) x), U x w).
  apply WREC_typ with (1:=ty); trivial.
 specialize satF with (1:=xo)(2:=H)(3:=Wty)(4:=H0).
 revert satF; apply piSAT0_mono with (f:=fun x=>x); auto with *.
 intros.
 rewrite WREC_unfold with (1:=ty); auto with *.
Qed.

End Wtypes.


Lemma rWi_ext X X' Y Y' RX RX' RY RY' o o' x x' :
  morph1 Y ->
  X == X' ->
  ZF.eq_fun X Y Y' ->
  (eq_set==>eqSAT)%signature RX RX' ->
  (forall x x', x ∈ X -> x==x' -> (eq_set==>eqSAT)%signature (RY x) (RY' x')) ->
  isOrd o ->
  o == o' ->
  x == x' ->
  eqSAT (rWi X Y RX RY o x) (rWi X' Y' RX' RY' o' x').
intros Ym.
intros.
unfold rWi.
unfold tiSAT.
apply ZFlambda.sSAT_morph.
apply cc_app_morph; trivial.
apply TR_ext_ord; intros; auto with *.
apply sup_morph; auto with *.
red; intros.
apply cc_lam_ext.
 apply TI_morph_gen.
  red; intros.
  apply W_F_ext; trivial.
(*  apply cc_bot_morph; trivial.*)

  apply osucc_morph; trivial.

 red; intros.
 assert (x0o: isOrd x0) by eauto using isOrd_inv.
 apply ZFlambda.iSAT_morph.
 apply cartSAT_morph.
 apply H1; rewrite !fst_def, H14; reflexivity.

  assert (w1 x1 ∈ X).
   assert (ext_fun X Y).
    apply eq_fun_ext in H0; trivial.
   apply TI_elim in H13; auto with *.
    destruct H13 as (ooo,?,?).
    apply W_F_elim in H16; trivial.
    destruct H16 as (?,_); trivial.
  apply piSAT0_morph; intros.
   red; intros.
   apply eq_set_ax; apply H0.
    rewrite fst_def; trivial.
    rewrite H14; reflexivity.

   apply H2; auto with *.
    rewrite fst_def; trivial.
    rewrite H14; reflexivity.

   apply ZFlambda.sSAT_morph.
   apply cc_app_morph.
    rewrite H8; trivial.
    apply H7; trivial.

    rewrite !snd_def.
    rewrite H14; reflexivity.
Qed.

Instance rWi_morph_gen : Proper
  (eq_set==>(eq_set==>eq_set)==>(eq_set==>eqSAT)==>(eq_set==>eq_set==>eqSAT)==>eq_set==>eq_set==>eqSAT) rWi.
do 7 red; intros.
unfold rWi.
unfold tiSAT.
apply ZFlambda.sSAT_morph.
apply cc_app_morph; trivial.
apply TR_morph; trivial.
do 3 red; intros.
apply sup_morph; auto.
red; intros.
apply cc_lam_ext.
 apply TI_morph_gen.
  red; intros.
  apply W_F_ext; trivial.
   red; intros; auto with *.

(*   apply cc_bot_morph; trivial.*)

  apply osucc_morph; trivial.

 red; intros.
 apply ZFlambda.iSAT_morph.
 apply cartSAT_morph.
  apply H1.
  rewrite H10; reflexivity.

  apply piSAT0_morph; intros.
   red; intros.
   apply eq_set_ax; apply H0.
   rewrite H10; reflexivity.

   apply H2; auto with *; rewrite H10; reflexivity.

   apply ZFlambda.sSAT_morph.
   apply cc_app_morph.
    apply H5; trivial.

    rewrite H10; reflexivity.
Qed.

End Make.
