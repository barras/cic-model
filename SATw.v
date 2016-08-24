
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

(*Lemma W_F_elim X x :
  x ∈ W_F X ->
  fst x ∈ A /\
  (forall i, i ∈ B (fst x) -> cc_app (snd x) i ∈ cc_botX) /\
  x ==couple (fst x) (cc_lam (B (fst x)) (cc_app (snd x))). 
*)

  Parameter W_ord : set -> (set -> set) -> set.
  Parameter W_fix : forall A B, morph1 B ->
    TI (W_F A B) (W_ord A B) ==
    W_F A B (TI (W_F A B) (W_ord A B)).
  Parameter W_stages : forall A B, morph1 B ->
    forall o, isOrd o ->
    TI (W_F A B) o ⊆ TI (W_F A B) (W_ord A B).
  Parameter mt_not_in_W_F : forall A B, morph1 B ->
    forall o x,
    isOrd o -> x ∈ TI (W_F A B) o -> ~ x == empty.

  Parameter W_ord_ord : forall A B, morph1 B ->
    isOrd (W_ord A B).

  Parameter G_W_ord : forall A B, morph1 B ->
    forall U, grot_univ U -> omega ∈ U ->
    A ∈ U -> (forall a : set, a ∈ A -> B a ∈ U) -> W_ord A B ∈ U.
  Parameter G_W_F : forall A B,
       morph1 B ->
       forall U,
       grot_univ U ->
       A ∈ U ->
       (forall a, a ∈ A -> B a ∈ U) ->
       forall X, X ∈ U -> W_F A B X ∈ U.

  Parameter WREC : (set -> set -> set) -> set -> set.
  Parameter WREC_morph : Proper ((eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) WREC.
  Parameter WREC_typ :
    forall A B, morph1 B ->
    forall O, isOrd O ->
    forall M, morph2 M ->
    forall U, morph2 U ->
    (forall o x, empty ∈ U o x) ->
    (forall o',
        o' ∈ osucc O ->
        forall f,
        f ∈ (Π x ∈ cc_bot (TI (W_F A B) o'), U o' x) ->
        M o' f
        ∈ (Π x ∈ cc_bot (TI (W_F A B) (osucc o')), U (osucc o') x)) ->
    (forall o' o'' f g,
        isOrd o' ->
        o' ⊆ o'' ->
        o'' ∈ osucc O ->
        f ∈ (Π x ∈ cc_bot (TI (W_F A B) o'), U o' x) ->
        g ∈ (Π x ∈ cc_bot (TI (W_F A B) o''), U o'' x) ->
        fcompat (cc_bot (TI (W_F A B) o')) f g ->
        fcompat (cc_bot (TI (W_F A B) (osucc o'))) (M o' f) (M o'' g)) ->
    (forall o' o'' x,
        isOrd o' ->
        o' ⊆ o'' ->
        o'' ∈ osucc O ->
        x ∈ cc_bot (TI (W_F A B) o') ->
        U o' x ⊆ U o'' x) ->

    forall o,
       isOrd o ->
       o ⊆ O ->
       WREC M o
       ∈ (Π x ∈ cc_bot (TI (W_F A B) o), U o x).
  Parameter WREC_irr :
    forall A B, morph1 B ->
    forall O, isOrd O ->
    forall M, morph2 M ->
    forall U, morph2 U ->
    (forall o x, empty ∈ U o x) ->
    (forall o',
        o' ∈ osucc O ->
        forall f,
        f ∈ (Π x ∈ cc_bot (TI (W_F A B) o'), U o' x) ->
        M o' f
        ∈ (Π x ∈ cc_bot (TI (W_F A B) (osucc o')), U (osucc o') x)) ->
    (forall o' o'' f g,
        isOrd o' ->
        o' ⊆ o'' ->
        o'' ∈ osucc O ->
        f ∈ (Π x ∈ cc_bot (TI (W_F A B) o'), U o' x) ->
        g ∈ (Π x ∈ cc_bot (TI (W_F A B) o''), U o'' x) ->
        fcompat (cc_bot (TI (W_F A B) o')) f g ->
        fcompat (cc_bot (TI (W_F A B) (osucc o'))) (M o' f) (M o'' g)) ->
    (forall o' o'' x,
        isOrd o' ->
        o' ⊆ o'' ->
        o'' ∈ osucc O ->
        x ∈ cc_bot (TI (W_F A B) o') ->
        U o' x ⊆ U o'' x) ->

    forall o o' x,
       isOrd o ->
       isOrd o' ->
       o ⊆ o' ->
       o' ⊆ O ->
       x ∈ cc_bot (TI (W_F A B) o) ->
       cc_app (WREC M o) x == cc_app (WREC M o') x.
  Parameter WREC_unfold :
    forall A B, morph1 B ->
    forall O, isOrd O ->
    forall M, morph2 M ->
    forall U, morph2 U ->
    (forall o x, empty ∈ U o x) ->
    (forall o',
        o' ∈ osucc O ->
        forall f,
        f ∈ (Π x ∈ cc_bot (TI (W_F A B) o'), U o' x) ->
        M o' f
        ∈ (Π x ∈ cc_bot (TI (W_F A B) (osucc o')), U (osucc o') x)) ->
    (forall o' o'' f g,
        isOrd o' ->
        o' ⊆ o'' ->
        o'' ∈ osucc O ->
        f ∈ (Π x ∈ cc_bot (TI (W_F A B) o'), U o' x) ->
        g ∈ (Π x ∈ cc_bot (TI (W_F A B) o''), U o'' x) ->
        fcompat (cc_bot (TI (W_F A B) o')) f g ->
        fcompat (cc_bot (TI (W_F A B) (osucc o'))) (M o' f) (M o'' g)) ->
    (forall o' o'' x,
        isOrd o' ->
        o' ⊆ o'' ->
        o'' ∈ osucc O ->
        x ∈ cc_bot (TI (W_F A B) o') ->
        U o' x ⊆ U o'' x) ->

    forall o n,
       isOrd o ->
       o ⊆ O ->
       n ∈ TI (W_F A B) (osucc o) ->
       cc_app (WREC M (osucc o)) n == cc_app (M o (WREC M o)) n.
  Parameter WREC_eqn :
    forall A B, morph1 B ->
    forall O, isOrd O ->
    forall M, morph2 M ->
    forall U, morph2 U ->
    (forall o x, empty ∈ U o x) ->
    (forall o',
        o' ∈ osucc O ->
        forall f,
        f ∈ (Π x ∈ cc_bot (TI (W_F A B) o'), U o' x) ->
        M o' f
        ∈ (Π x ∈ cc_bot (TI (W_F A B) (osucc o')), U (osucc o') x)) ->
    (forall o' o'' f g,
        isOrd o' ->
        o' ⊆ o'' ->
        o'' ∈ osucc O ->
        f ∈ (Π x ∈ cc_bot (TI (W_F A B) o'), U o' x) ->
        g ∈ (Π x ∈ cc_bot (TI (W_F A B) o''), U o'' x) ->
        fcompat (cc_bot (TI (W_F A B) o')) f g ->
        fcompat (cc_bot (TI (W_F A B) (osucc o'))) (M o' f) (M o'' g)) ->
    (forall o' o'' x,
        isOrd o' ->
        o' ⊆ o'' ->
        o'' ∈ osucc O ->
        x ∈ cc_bot (TI (W_F A B) o') ->
        U o' x ⊆ U o'' x) ->

    forall o n,
       isOrd o ->
       o ⊆ O ->
       n ∈ TI (W_F A B) o ->
       cc_app (WREC M o) n == cc_app (M o (WREC M o)) n.
  Parameter WREC_strict :
    forall A B, morph1 B ->
    forall O, isOrd O ->
    forall M, morph2 M ->
    forall U, morph2 U ->
    (forall o x, empty ∈ U o x) ->
    (forall o',
        o' ∈ osucc O ->
        forall f,
        f ∈ (Π x ∈ cc_bot (TI (W_F A B) o'), U o' x) ->
        M o' f
        ∈ (Π x ∈ cc_bot (TI (W_F A B) (osucc o')), U (osucc o') x)) ->
    (forall o' o'' f g,
        isOrd o' ->
        o' ⊆ o'' ->
        o'' ∈ osucc O ->
        f ∈ (Π x ∈ cc_bot (TI (W_F A B) o'), U o' x) ->
        g ∈ (Π x ∈ cc_bot (TI (W_F A B) o''), U o'' x) ->
        fcompat (cc_bot (TI (W_F A B) o')) f g ->
        fcompat (cc_bot (TI (W_F A B) (osucc o'))) (M o' f) (M o'' g)) ->
    (forall o' o'' x,
        isOrd o' ->
        o' ⊆ o'' ->
        o'' ∈ osucc O ->
        x ∈ cc_bot (TI (W_F A B) o') ->
        U o' x ⊆ U o'' x) ->
    forall o,
       isOrd o -> o ⊆ O -> cc_app (WREC M o) empty == empty.

End W_PartialModel.

Set Implicit Arguments.

(*
Lemma sigmaReal_mono A A' B B' x x' :
  inclSAT (A (fst x)) (A' (fst x')) ->
  inclSAT (B (fst x) (snd x)) (B' (fst x') (snd x')) ->
  inclSAT (sigmaReal A B x) (sigmaReal A' B' x').
intros; apply cartSAT_mono; trivial.

Lemma sigmaReal_mono_gen A A' B B' x x' :
  (forall a a', a==a' -> inclSAT (A a) (A' a')) ->
  (forall a a' b b', a==a' -> b==b' -> inclSAT (B a b) (B' a' b')) ->
  x == x' ->
  inclSAT (sigmaReal A B x) (sigmaReal A' B' x').
unfold sigmaReal.
intros.
apply cartSAT_mono.
 apply H; rewrite H1; reflexivity.
 apply H0; rewrite H1; reflexivity.
Qed.
*)

(** W-types *)

Module Make (W:W_PartialModel).
Import W.

Section Wtypes.

Variable A : set.
Variable B : set -> set.
Hypothesis B_morph : morph1 B.
Let Bext : ext_fun A B.
auto with *.
Qed.



Notation WF := (W_F A B).

Existing Instance W_F_mono.


Variable RA : set -> SAT.
Variable RB : set -> set -> SAT.
Hypothesis RA_morph : Proper (eq_set ==> eqSAT) RA.
Hypothesis RB_morph : Proper (eq_set ==> eq_set ==> eqSAT) RB.

Definition rW (X:set->SAT) (w:set) : SAT :=
  sigmaReal RA (fun x f => piSAT0 (fun i => i ∈ B x) (RB x)
    (fun i => condSAT (~cc_app f i==empty) (X (cc_app f i))))
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

  apply condSAT_morph.
   rewrite H2; reflexivity.

   apply H.
   rewrite H2; reflexivity.

 rewrite H0; reflexivity.
Qed.
Hint Resolve rW_morph.


Lemma rW_mono_gen' Y X X':
  (forall x x', x ∈ Y -> x==x' -> inclSAT (X x) (X' x')) ->
  forall x x', x ∈ WF Y -> x==x' -> inclSAT (rW X x) (rW X' x').
intros Xmono x x' xty eqx'.
unfold rW.
apply cartSAT_mono.
 rewrite eqx'; reflexivity.

 eapply piSAT0_mono with (f:=fun x => x); auto with *.
  intros; rewrite eqx'; trivial.

  intros; rewrite eqx'; reflexivity.

  intros i ity.
  apply condSAT_ext; auto with *.
   rewrite <- eqx'; trivial.

   intros nmt _.
   rewrite snd_def in nmt.
   apply Xmono.
   2:rewrite eqx'; reflexivity.
   rewrite snd_def.
   apply W_F_elim in xty; trivial.
   destruct xty as (xty,(fty,_)); auto.
   assert (ity' : i ∈ B (w1 x)).
    revert ity; apply eq_elim; apply Bext.
     rewrite fst_def, <-eqx'; trivial.
     rewrite fst_def, <-eqx'; reflexivity.
   specialize cc_prod_elim with (1:=fty) (2:=ity'); intros yty.
   rewrite cc_bot_ax in yty; destruct yty; trivial.
   contradiction.
Qed.

Lemma rW_mono_gen Y X X':
  (forall x, x ∈ Y -> inclSAT (X x) (X' x)) ->
  forall x, x ∈ WF Y -> inclSAT (rW X x) (rW X' x).
intros Xmono x xty.
apply cartSAT_mono; auto with *.
eapply piSAT0_mono with (f:=fun x => x); auto with *.
intros i ity.
apply condSAT_ext; auto with *.
intros nmt _.
rewrite snd_def in nmt.
apply Xmono.
rewrite snd_def.
apply W_F_elim in xty; trivial.
destruct xty as (xty,(fty,_)); auto.
assert (ity' : i ∈ B (w1 x)).
 revert ity; apply eq_elim; apply Bext.
  rewrite fst_def; trivial.
  rewrite fst_def; reflexivity.
specialize cc_prod_elim with (1:=fty) (2:=ity'); intros yty.
rewrite cc_bot_ax in yty; destruct yty; trivial.
contradiction.
Qed.

Lemma rW_mono FX X X':
  FX ⊆ WF FX ->
  inclFam FX X X' ->
  inclFam FX (rW X) (rW X').
red; intros.
apply H in H1.
revert H1; apply rW_mono_gen; trivial.
Qed.

Lemma rW_irrel (R R' : set -> SAT) (o : set) :
 isOrd o ->
 (forall x x' : set, x ∈ TI WF o -> x == x' -> eqSAT (R x) (R' x')) ->
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
  inSAT f (piSAT0 (fun i => i ∈ B a) (RB a)
            (fun i => condSAT (~cc_app b i==empty) (RX (cc_app b i)))) ->
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
                      (fun i => condSAT (~cc_app f i==empty) (RX (cc_app f i))))
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
Qed.

Lemma rWi_succ_eq o x :
  isOrd o ->
  x ∈ TI WF (osucc o) ->
  eqSAT (rWi (osucc o) x) (rW (rWi o) x).
intros.
apply tiSAT_succ_eq; auto.
 apply W_F_mono; trivial.

 intros; apply rW_irrel with (o:=o'); trivial.
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

 apply piSAT0_intro; intros.
  apply sat_sn in H2; trivial.
 specialize cc_prod_elim with (1:=H3) (2:=H5); intros yty.
 apply piSAT0_elim' in H2; red in H2.
 specialize H2 with (1:=H5) (2:=H6).
 rewrite cc_bot_ax in yty; destruct yty.
  rewrite H7 in H2.
  apply neuSAT_def.
  rewrite rWi_neutral in H2; trivial.

  rewrite condSAT_ok; trivial.
  apply mt_not_in_W_F in H7; trivial.
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
revert bt breal.
apply piSAT0_mono with (f:=fun x=>x); auto with *.
intros x xty.
apply piSAT0_mono with (f:=fun x=>x); auto with *.
intros f fty.
apply piSAT0_mono with (f:=fun x=>x); auto with *.
intros i ity.
apply condSAT_smaller.
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
apply sup_morph; auto.
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
  apply H1; rewrite !fst_def, H12; reflexivity.

  assert (w1 x1 ∈ X).
   assert (ext_fun X Y).
    apply eq_fun_ext in H0; trivial.
   apply TI_elim in H11; auto with *.
    destruct H11 as (ooo,?,?).
    apply W_F_elim in H14; trivial.
    destruct H14 as (?,_); trivial.
  apply piSAT0_morph; intros.
   red; intros.
   apply eq_set_ax; apply H0.
    rewrite fst_def; trivial.
    rewrite H12; reflexivity.

   apply H2; auto with *.
    rewrite fst_def; trivial.
    rewrite H12; reflexivity.

   apply condSAT_morph.
    rewrite H12; reflexivity.

    apply ZFlambda.sSAT_morph.
    apply cc_app_morph.
     apply H6; trivial.

     rewrite !snd_def.
     rewrite H12; reflexivity.
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

   apply condSAT_morph.
    rewrite H10; reflexivity.

    apply ZFlambda.sSAT_morph.
    apply cc_app_morph.
     apply H5; trivial.

     rewrite H10; reflexivity.
Qed.

End Make.
