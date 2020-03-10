
Require Import ZF ZFpairs ZFsum ZFrelations ZFord ZFfix ZFgrothendieck.
Require Import ZFlambda Sat SATtypes.
Require Import Lambda.
Module Lc:=Lambda.
Require Import ZFcoc.
Require Models.

(** The abstract set-theoretical model of W-types, upon which the realizability
    interpretation is built.
 *)
(*
Module Type CCforWaddon (Import S:Models.CC_Model).
  Parameter empty : X.
  Parameter cc_bot : X -> X.
  Parameter cc_bot_ax : forall x z, z ∈ cc_bot x <-> z == empty \/ z ∈ x.
End CCforWaddon.

Module Type CCforW := Models.CC_Model <+ CCforWaddon.
*)
Module Type Wconstructor (*(Import S:CCforW)*).
  Notation X:=set.
  Notation eqX:=eq_set.
  
  Parameter mkw : X -> X -> X.
  Parameter mkw_morph: Proper (eqX==>eqX==>eqX) mkw.
  Parameter w1 w2 : X -> X.
  Parameter w1_morph : Proper (eqX==>eqX) w1.
  Parameter w2_morph : Proper (eqX==>eqX) w2.
  Parameter w1_eq : forall x f, w1 (mkw x f) == x.
  Parameter w2_eq : forall x f, w2 (mkw x f) == f.
  Parameter discr_mt_mkw : forall x f,
    ~ empty == mkw x f.

End Wconstructor.

Set Implicit Arguments.

(** W-types *)

Module Make (*(Import SM : CCforW)*) (Import W:Wconstructor (*SM*)).

Section Wtypes.

Variable A : set.
Variable B : set -> set.
Hypothesis B_morph : morph1 B.
Let Bext : ext_fun A B.
auto with *.
Qed.

Variable RA : set -> SAT.
Variable RB : set -> set -> SAT.
Hypothesis RA_morph : Proper (eq_set ==> eqSAT) RA.
Hypothesis RB_morph : Proper (eq_set ==> eq_set ==> eqSAT) RB.

(* needs injectivity of mkw 
Definition rW (X:set->SAT) (w:set) : SAT :=
  depSAT
    (fun x => x ∈ A)
    (fun x => depSAT (fun f => w = mkw x f)
                     (fun f => cartSAT (RA x)
                                       (piSAT0 (fun i => i ∈ B x) (RB x)
                                               (fun i => X (cc_app f i))))). *)
(*
Definition rW (RX:set->SAT) (w:set) : SAT :=
  interSAT (fun C:{C:set->SAT|Proper(eq_set==>eqSAT)C}=>
                            let C := proj1_sig C in
                            prodSAT (piSAT0 (fun x => x ∈ A) RA
                                            (fun x => piSAT0 (fun f => f ∈ cc_arr (B x) (cc_bot X))
                                                             (fun f => piSAT0(fun i => i ∈ B x) (RB x)
                                                                             (fun i => RX (cc_app f i)))
                                                             (fun f => C (mkw x f))))
                                    (C w)).

Instance rW_morph :
   Proper (eq_set ==> (eq_set ==> eqSAT) ==> eq_set ==> eqSAT) rW.
Admitted.

Hint Resolve rW_morph.

Lemma rW_mono X : monoFam (rW.
Admitted.

Lemma rW_neutral X :
  eqSAT (rW X empty) neuSAT.
Admitted.
*)

Definition rW (X:set->SAT) (w:set) : SAT :=
  condSAT (~ empty == w /\ w1 w ∈ A)
  (sigmaReal RA
    (fun x f => piSAT0 (fun i => i ∈ B x) (RB x) (fun i => X (cc_app f i)))
    (couple (w1 w) (w2 w))).

Instance rW_morph :
   Proper ((eq_set ==> eqSAT) ==> eq_set ==> eqSAT) rW.
do 3 red; intros.
unfold rW.
apply condSAT_morph.
 rewrite H0; reflexivity.
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


Lemma rW_mono : monoFam rW.
red; intros X X' Xmono x.
apply condSAT_ext; trivial.
intros _ xnmt.
apply cartSAT_mono; auto with *.
eapply piSAT0_mono with (f:=fun x => x); auto with *.
Qed.

Lemma rW_neutral X :
  eqSAT (rW X empty) neuSAT.
apply neuSAT_ext.
apply condSAT_neutral.
intro h; apply h; reflexivity.
Qed.

Definition WC x f := COUPLE x f.

Lemma Real_WC_gen RX a b x f :
  Proper (eq_set==>eqSAT) RX ->
  a ∈ A ->
  inSAT x (RA a) ->
  inSAT f (piSAT0 (fun i => i ∈ B a) (RB a) (fun i => RX (cc_app b i))) ->
  inSAT (WC x f) (rW RX (mkw a b)).
intros RXm tya satx satf.
unfold rW, WC.
rewrite condSAT_ok.
2:split;[apply discr_mt_mkw|rewrite w1_eq; trivial].
apply Real_couple; trivial.
 do 3 red; intros.
 apply piSAT0_morph; intros.
  red; intros.
  rewrite H; reflexivity.

  apply RB_morph; auto with *.

  rewrite H0; reflexivity.

 rewrite w1_eq; trivial.

 revert satf; apply piSAT0_morph.
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

Lemma Real_WCASE_gen X RX C n nt bt :
  Proper (eq_set ==> eqSAT) C ->
  w1 n ∈ A ->
  w2 n ∈ cc_arr (B (w1 n)) (cc_bot X) ->
  n == mkw (w1 n) (w2 n) ->
  inSAT nt (rW RX n) ->
  inSAT bt (piSAT0 (fun x => x ∈ A) RA (fun x =>
            piSAT0 (fun f => f ∈ cc_arr (B x) (cc_bot X))
                   (fun f => piSAT0 (fun i => i ∈ B x) (RB x)
                      (fun i => RX (cc_app f i)))
                   (fun f => C (mkw x f)))) ->
  inSAT (WCASE bt nt) (C n).
intros Cm ty1 ty2 n_eq xreal breal.
setoid_replace (C n) with (C (mkw (fst (couple (w1 n) (w2 n))) (snd (couple (w1 n) (w2 n))))).
2:rewrite fst_def, snd_def, <- n_eq; reflexivity.
unfold rW in xreal; rewrite condSAT_ok in xreal.
2:split;[rewrite n_eq; apply discr_mt_mkw|trivial].
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

Definition rWi := fixSAT rW.

Instance rWi_morph :
  Proper (eq_set ==> eqSAT) rWi.
do 2 red; intros.
unfold rWi.
apply fixSAT_morph0; auto with *.
Qed.

Lemma rWi_eq x : eqSAT (rWi x) (rW rWi x).
(*intros xty.*)
apply fixSAT_eq; auto with *.
(*red; intros.*)
apply rW_mono.
(*apply rW_mono with (Y:=W'); trivial.
rewrite <- W'_eq; trivial.*)
Qed.


Lemma rWi_neutral :
  eqSAT (rWi empty) neuSAT.
rewrite rWi_eq; auto.
apply rW_neutral.
Qed.

Lemma Real_WC (*X*) a b x f :
  a ∈ A ->
(*  b ∈ cc_arr (B a) (cc_bot X) ->*)
  inSAT x (RA a) ->
  inSAT f (piSAT0 (fun i => i ∈ B a) (RB a) (fun i => rWi (cc_app b i))) ->
  inSAT (WC x f) (rWi (mkw a b)).
intros.
(*assert (mkw a b ∈ WF X).
 apply W_F_intro; trivial.*)
rewrite rWi_eq.
eapply Real_WC_gen (*with (X:=X)*); auto with *.
Qed.

Lemma Real_WCASE X C n nt bt:
  Proper (eq_set ==> eqSAT) C ->
  n == empty \/
  w1 n ∈ A /\ w2 n ∈ cc_arr (B (w1 n)) (cc_bot X) /\ n == mkw (w1 n) (w2 n) ->
  inSAT nt (rWi n) ->
  inSAT bt (piSAT0 (fun x => x ∈ A) RA (fun x =>
            piSAT0 (fun f => f ∈ cc_arr (B x) (cc_bot X))
                   (fun f => piSAT0 (fun i => i ∈ B x) (RB x) (fun i => rWi (cc_app f i)))
                   (fun f => C (mkw x f)))) ->
  inSAT (WCASE bt nt) (C n).
intros Cm nty nreal breal.
rewrite rWi_eq in nreal; trivial.
destruct nty as [nmt|(ty1&ty2&n_eq)].
(*apply cc_bot_ax in nty; destruct nty as [nmt|nty].*)
 rewrite nmt, rW_neutral, neuSAT_def in nreal.
 unfold WCASE.
 apply prodSAT_elim with (2:=breal); trivial.

 apply Real_WCASE_gen with (2:=ty1)(3:=ty2) (5:=nreal); trivial.
Qed.

(** * Structural fixpoint: *)

Lemma G_sat' x t m (U:SAT):
  inSAT t (rWi x) ->
  inSAT m U ->
  inSAT (Lc.App2 WHEN_COUPLE t m) U.
intros xsat msat.
rewrite rWi_eq in xsat; trivial.
apply condSAT_smaller in xsat.
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

Lemma WFIX_sat o X U m :
  (forall y n, isOrd y -> n ∈ X y -> exists2 y', y' ∈ y & n ∈ X (osucc y'))->
  let FIX_ty o := piSAT0 (fun n => n ∈ cc_bot (X o)) rWi (U o) in
  let FIX_ty' o := piSAT0 (fun n => n ∈ X o) rWi (U o) in
  isOrd o ->
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ X y ->
   inclSAT (U y n) (U y' n)) ->
  inSAT m (piSAT0 (fun o' => o' ∈ o)
                  (fun o1 => FIX_ty o1) (fun o1 => FIX_ty' (osucc o1))) ->
  inSAT m (prodSAT (FIX_ty empty) snSAT) ->
  inSAT (WFIX m) (FIX_ty o).
intros Xmono FIX_ty FIX_ty' oo Umono msat mneutr.
unfold WFIX.
eapply FIXP_sat with (RT := rWi) (7:=msat); trivial; intros.
 rewrite cc_bot_ax in H1; destruct H1.
  left; rewrite H1; apply rWi_neutral; trivial.

  right; auto.

 exists empty; trivial.

 intros; apply neuSAT_def;
   apply WHEN_COUPLE_neutral; apply neuSAT_def; trivial.

 apply G_sat' with (x:=x); auto with *.
Qed.

Lemma WREC_sat o X F RF U RU wrec :
  Proper (eq_set==>eq_set==>eq_set==>eqSAT) RU ->
  (forall y n, isOrd y -> n ∈ X y -> exists2 y', y' ∈ y & n ∈ X (osucc y'))->
  isOrd o ->
  (forall o' o'' x y y', isOrd o' -> isOrd o'' -> o' ⊆ o'' -> o'' ⊆ o ->
   x ∈ X o' ->
   y ∈ U o' x ->
   y == y' ->
   inclSAT (RU o' x y) (RU o'' x y')) ->
  let FIX_ty o' f :=
      piSAT0 (fun n => n ∈ cc_bot (X o'))
             rWi
             (fun n => RU o' n (cc_app f n)) in
  (forall o' f u,
   o' ∈ o ->
   f ∈ (Π w ∈ cc_bot (X o'), U o' w) ->
   inSAT u (FIX_ty o' f) ->
   inSAT (Lc.App RF u) (FIX_ty (osucc o') (F o' f))) ->
  inSAT RF (prodSAT (FIX_ty empty (wrec empty)) snSAT) ->
  (forall y, isOrd y -> y ⊆ o ->
   wrec y ∈ cc_prod (cc_bot (X y)) (U y)) ->
  (forall y y', isOrd y -> isOrd y' -> y ⊆ o -> y' ⊆ y ->
   ZFfunext.fcompat (cc_bot (X y')) (wrec y') (wrec y)) ->
  (forall y, y ∈ o ->
   ZFfunext.fcompat (X (osucc y)) (wrec (osucc y)) (F y (wrec y))) ->
(*  (forall x, x ∈ X (osucc o) ->
             cc_app (wrec o) x == cc_app (F o (wrec o)) x) ->*)
  inSAT (WFIX RF) (FIX_ty o (wrec o)).
intros RUm Xincr oo RUmono FIX_ty satF Fneutr wrec_ty wrec_irr wrec_eqn.
eapply WFIX_sat with (U:=fun o n => RU o n (cc_app (wrec o) n)); trivial.
 intros.
 apply RUmono; auto.
  apply cc_prod_elim with (dom := cc_bot (X y)) (F := U y); auto.
  apply wrec_ty; auto.
  transitivity y'; trivial.

  apply wrec_irr; auto.

 apply piSAT0_intro; intros.
  apply sat_sn in Fneutr; trivial.
 assert (xo : isOrd x) by eauto using isOrd_inv.
 assert (leo : x ⊆ o).
  red; intros; apply isOrd_trans with x; trivial.
 assert (Wty : wrec x ∈ Π w ∈ cc_bot (X x), U x w).
  apply wrec_ty; trivial.
 specialize satF with (1:=H) (2:=Wty) (3:=H0).
 revert satF; apply piSAT0_mono with (f:=fun x=>x); auto with *.
 intros.
 red in wrec_eqn.
 rewrite wrec_eqn; auto with *.
Qed.

Lemma WREC_sat_gen o X F RF U RU wrec :
  Proper (eq_set==>eq_set==>eq_set==>eqSAT) RU ->
  (forall y n, isOrd y -> n ∈ X y -> exists2 y', y' ∈ y & n ∈ X (osucc y'))->
  isOrd o ->
  (forall o' o'' x y y', isOrd o' -> isOrd o'' -> o' ⊆ o'' -> o'' ⊆ o ->
   x ∈ X o' ->
   y ∈ U o' x ->
   y == y' ->
   inclSAT (RU o' x y) (RU o'' x y')) ->
  let FIX_ty o' f :=
      piSAT0 (fun n => n ∈ cc_bot (X o'))
             rWi
             (fun n => RU o' n (cc_app f n)) in
  (forall o' f u,
   o' ∈ cc_bot o ->
   f ∈ (Π w ∈ cc_bot (X o'), U o' w) ->
   inSAT u (FIX_ty o' f) ->
   inSAT (Lc.App RF u) (FIX_ty (osucc o') (F o' f))) ->
  (forall y, isOrd y -> y ⊆ o ->
   wrec y ∈ cc_prod (cc_bot (X y)) (U y)) ->
  (forall y y', isOrd y -> isOrd y' -> y ⊆ o -> y' ⊆ y ->
   ZFfunext.fcompat (cc_bot (X y')) (wrec y') (wrec y)) ->
  (forall y, y ∈ o ->
   ZFfunext.fcompat (X (osucc y)) (wrec (osucc y)) (F y (wrec y))) ->
(*  (forall x, x ∈ X (osucc o) ->
             cc_app (wrec o) x == cc_app (F o (wrec o)) x) ->*)
  inSAT (WFIX RF) (FIX_ty o (wrec o)).
intros RUm Xincr oo RUmono FIX_ty satF wrec_ty wrec_irr wrec_eqn.
eapply WREC_sat; eauto.
apply prodSAT_intro'; intros.
apply snSAT_intro.
eapply sat_sn.
eapply satF with (o':=empty) (f:=wrec empty); auto.
Qed.

End Wtypes.


Lemma rWi_ext X X' Y Y' RX RX' RY RY' x x' :
  morph1 Y ->
  morph1 Y' ->
  X == X' ->
  ZF.eq_fun X Y Y' ->
  (eq_set==>eqSAT)%signature RX RX' ->
  (forall x x', x ∈ X -> x==x' -> (eq_set==>eqSAT)%signature (RY x) (RY' x')) ->
  x == x' ->
  eqSAT (rWi X Y RX RY x) (rWi X' Y' RX' RY' x').
intros Ym Ym' eqX.
intros.
unfold rWi.
unfold fixSAT.
(*assert (eqW: W' X Y == W' X' Y').
 unfold W'.
 apply incl_eq.
 transitivity (TI (W_F X' Y') (W_ord X Y)).
  apply eq_incl.
  apply TI_morph_gen; auto with *.
   red; intros.
   apply W_F_ext; auto.

  apply W_stages; trivial.
  apply W_ord_ord; trivial.

 transitivity (TI (W_F X Y) (W_ord X' Y')).
  apply eq_incl; symmetry.
  apply TI_morph_gen; auto with *.
   red; intros.
   apply W_F_ext; auto.

  apply W_stages; trivial.
  apply W_ord_ord; trivial.*)
apply interSAT_morph_subset; simpl; intros.
 apply and_iff_morphism; [reflexivity|].
 apply fa_morph; intros w.
  apply fa_morph; intros u.
  apply impl_morph;[|reflexivity].
  apply inSAT_morph; trivial.
  unfold rW.
  apply condSAT_morph_gen; auto with *.
   rewrite eqX; reflexivity.
  intros (wnmt,ty1).
(*  assert (ty1 : w1 w ∈ X).
admit.*) (*
   assert (ext_fun X Y).
    apply eq_fun_ext in H0; trivial.
   apply cc_bot_ax in tyw; destruct tyw.
    elim wnmt; auto with *.
   apply TI_elim in H5; auto with *.
   2:apply W_ord_ord; trivial.
   destruct H5 as (ooo,?,?).
   apply W_F_elim in H6; trivial.
   apply H6.*)
  apply cartSAT_morph.
   apply H0; reflexivity.

   apply piSAT0_morph; intros.
    red; intros.
    apply in_set_morph; auto with *.
    apply H; auto with *.
    rewrite fst_def; trivial.

    apply H1; auto with *.
    rewrite fst_def; trivial.

    reflexivity.

 apply Px; trivial.
Qed.

Instance rWi_morph_gen : Proper
  (eq_set==>(eq_set==>eq_set)==>(eq_set==>eqSAT)==>(eq_set==>eq_set==>eqSAT)==>eq_set==>eqSAT) rWi.
do 6 red; intros.
apply rWi_ext; auto with *.
 red; transitivity y0; auto with *.
 red; transitivity x0; auto with *.
 red; auto.
Qed.

Opaque rWi.

End Make.
