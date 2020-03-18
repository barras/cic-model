
Require Import ZF ZFpairs ZFsum Sat.
Require Import ZFlambda.
Require Import Lambda.

Set Implicit Arguments.

Definition inclFam (F G:set->SAT) :=
  forall x, inclSAT (F x) (G x).

(** Unit type *)

Definition unitSAT :=
  interSAT (fun C => prodSAT C C).

Definition ID := Abs (Ref 0).

Lemma ID_intro0 S : inSAT ID (prodSAT S S).
apply prodSAT_intro; intros.
unfold subst; simpl subst_rec.
rewrite lift0.
trivial.
Qed.

Lemma ID_intro : inSAT ID unitSAT.
apply interSAT_intro with (1:=snSAT).
apply ID_intro0.
Qed.

(** Disjoint sum *)

Definition INL (t:term) :=
  Abs (Abs (App (Ref 1) (lift 2 t))).
Definition INR (t:term) :=
  Abs (Abs (App (Ref 0) (lift 2 t))).

Lemma INL_iota t1 t2 a :
  redp (App2 (INL a) t1 t2) (App t1 a).
unfold INL.
eapply t_trans;[apply redp_app_l;apply t_step;apply red1_beta; reflexivity|].
unfold subst; simpl.
rewrite simpl_subst; trivial.
apply t_step; apply red1_beta.
unfold subst; simpl.
repeat rewrite simpl_subst; trivial.
repeat rewrite lift0; trivial.
Qed.

Lemma INR_iota t1 t2 a :
  redp (App2 (INR a) t1 t2) (App t2 a).
unfold INR.
eapply t_trans;[apply redp_app_l;apply t_step;apply red1_beta; reflexivity|].
unfold subst; simpl.
rewrite simpl_subst; trivial.
apply t_step; apply red1_beta.
unfold subst; simpl.
rewrite simpl_subst; trivial.
repeat rewrite lift0; trivial.
Qed.

Definition WHEN_SUM :=
  Abs (App2 (Ref 0) (Abs ID) (Abs ID)).

Definition WHEN_SUM_INL a u :
  redp (App2 WHEN_SUM (INL a) u) u.
unfold WHEN_SUM.
eapply t_trans.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
rewrite lift0.
eapply t_trans.
 apply redp_app_l.
 apply INL_iota.
eapply t_trans.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
apply t_step; apply red1_beta.
unfold subst; simpl.
rewrite lift0; reflexivity.
Qed.

Definition WHEN_SUM_INR a u :
  redp (App2 WHEN_SUM (INR a) u) u.
unfold WHEN_SUM.
eapply t_trans.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
rewrite lift0.
eapply t_trans.
 apply redp_app_l.
 apply INR_iota.
eapply t_trans.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
apply t_step; apply red1_beta.
unfold subst; simpl.
rewrite lift0; reflexivity.
Qed.

Lemma WHEN_SUM_neutral t :
  inSAT t (prodSAT snSAT (prodSAT snSAT neuSAT)) ->
  inSAT (App WHEN_SUM t) neuSAT.
intros.
unfold WHEN_SUM.
apply inSAT_exp;[simpl;auto|].
unfold subst; simpl; rewrite lift0.
apply prodSAT_elim with snSAT.
2:apply snSAT_intro; auto.
apply prodSAT_elim with snSAT; trivial.
apply snSAT_intro; auto.
Qed.

Lemma WHEN_SUM_neutral2 t :
  inSAT t neuSAT ->
  inSAT (Lambda.App WHEN_SUM t) (prodSAT snSAT (prodSAT snSAT (prodSAT snSAT neuSAT))).
intros; apply -> neuSAT_def.
apply WHEN_SUM_neutral.
apply -> neuSAT_def; trivial.
Qed.

(** Qu: can we derive sumReal from sumSAT ?
    Or, is there a way to say that the second branch only needs to be SN when the
    the set denotation uses inl ?
 *)
(*
Definition sumSAT X Y : SAT :=
  interSAT (fun C => prodSAT (prodSAT X C) (prodSAT (prodSAT Y C) C)).

Lemma sumSAT_intro1 X Y t :
  inSAT t X ->
  inSAT (INL t) (sumSAT X Y).
intros tsat.
apply interSAT_intro;[exact snSAT|].
intros C.
apply prodSAT_intro; intros b1 b1sat.
unfold subst; simpl.
rewrite simpl_subst; auto with *.
apply prodSAT_intro; intros b2 b2sat.
unfold subst; simpl.
rewrite !simpl_subst, !lift0; auto with *.
apply prodSAT_elim with X; trivial.
Qed.

Lemma sumSAT_intro2 X Y t :
  inSAT t Y ->
  inSAT (INR t) (sumSAT X Y).
intros tsat.
apply interSAT_intro;[exact snSAT|].
intros C.
apply prodSAT_intro; intros b1 b1sat.
unfold subst; simpl.
rewrite simpl_subst; auto with *.
apply prodSAT_intro; intros b2 b2sat.
unfold subst; simpl.
rewrite !simpl_subst, !lift0; auto with *.
apply prodSAT_elim with Y; trivial.
Qed.

Lemma sumSAT_case X Y C t b1 b2 :
  inSAT t (sumSAT X Y) ->
  inSAT b1 (prodSAT X C) ->
  inSAT b2 (prodSAT Y C) ->
  inSAT (App2 t b1 b2) C.
intros tsat b1sat b2sat.
apply prodSAT_elim with (2:=b2sat).
apply prodSAT_elim with (2:=b1sat).
apply interSAT_elim with (1:=tsat).
Qed.

  Definition sumReal (X Y:set->SAT) (a:set) : SAT :=
  sumSAT
    (condSAT (exists x, a==inl x) (X (dest_sum a)))
    (condSAT (exists y, a==inr y) (Y (dest_sum a))).
 
Lemma Real_inl RX RY x y t :
  Proper (eq_set ==> eqSAT) RX ->
  inSAT t (RX x) ->
  y == inl x ->
  inSAT (INL t) (sumReal RX RY y).
intros.
unfold sumReal.
apply sumSAT_intro1.
rewrite condSAT_ok;[|eauto].
rewrite H1, dest_sum_inl; trivial.
Qed.

Lemma Real_inr RX RY x y t :
  Proper (eq_set ==> eqSAT) RY ->
  inSAT t (RY x) ->
  y == inr x ->
  inSAT (INR t) (sumReal RX RY y).
intros.
unfold sumReal.
apply sumSAT_intro2.
rewrite condSAT_ok;[|eauto].
rewrite H1, dest_sum_inr; trivial.
Qed.

Lemma Real_sum_case a RX RY C t b1 b2 :
  inSAT t (sumReal RX RY a) ->
  inSAT b1 (prodSAT (condSAT (exists x, a==inl x) (RX (dest_sum a))) C) ->
  inSAT b2 (prodSAT (condSAT (exists x, a==inr x) (RY (dest_sum a))) C) ->
  inSAT (App2 t b1 b2) C.
intros.
unfold sumReal in H0.
apply sumSAT_case with (1:=H); trivial.
Qed.
 
(* First attempt with depSAT *)
  Definition sumReal (X Y:set->SAT) (a:set) : SAT :=
  sumSAT
    (depSAT (fun x => a==inl x) X)
    (depSAT (fun y => a==inr y) Y).
 
Lemma Real_inl RX RY x y t :
  Proper (eq_set ==> eqSAT) RX ->
  inSAT t (RX x) ->
  y == inl x ->
  inSAT (INL t) (sumReal RX RY y).
intros.
unfold sumReal.
apply sumSAT_intro1.
apply depSAT_intro'; [eauto|intros].
rewrite H1 in H2; apply inl_inj in H2.
rewrite <- H2; trivial.
Qed.

Lemma Real_inr RX RY x y t :
  Proper (eq_set ==> eqSAT) RY ->
  inSAT t (RY x) ->
  y == inr x ->
  inSAT (INR t) (sumReal RX RY y).
intros.
unfold sumReal.
apply sumSAT_intro2.
apply depSAT_intro'; [eauto|intros].
rewrite H1 in H2; apply inr_inj in H2.
rewrite <- H2; trivial.
Qed.

Lemma Real_sum_case a RX RY C t b1 b2 :
  inSAT t (sumReal RX RY a) ->
  inSAT b1 (prodSAT (depSAT (fun x => a==inl x) RX) C) ->
  inSAT b2 (prodSAT (depSAT (fun x => a==inr x) RY) C) ->
  inSAT (App2 t b1 b2) C.
intros.
unfold sumReal in H0.
apply sumSAT_case with (1:=H); trivial.
Qed.
*)

Definition sumReal (X Y:set->SAT) (a:set) : SAT :=
  interSAT (fun C =>
     prodSAT (piSAT0 (fun x => a==inl x) X (fun _ => C))
    (prodSAT (piSAT0 (fun x => a==inr x) Y (fun _ => C))
     C)).

Lemma sumReal_mono X X' Y Y':
  inclFam X X' ->
  inclFam Y Y' ->
  inclFam (sumReal X Y) (sumReal X' Y').
red; intros.
unfold sumReal.
apply interSAT_mono; intros C.
apply prodSAT_mono.
 red; apply piSAT0_mono with (f:=fun x=>x); auto with *.
apply prodSAT_mono; auto with *.
red; apply piSAT0_mono with (f:=fun x=>x); auto with *.
Qed.

Lemma Real_inl RX RY x y t :
  Proper (eq_set ==> eqSAT) RX ->
  inSAT t (RX x) ->
  y == inl x ->
  inSAT (INL t) (sumReal RX RY y).
intros.
apply interSAT_intro; auto.
intros.
apply prodSAT_intro; intros.
unfold subst; simpl subst_rec.
unfold subst; rewrite simpl_subst; auto.
apply prodSAT_intro; intros.
unfold subst; simpl subst_rec.
unfold subst; repeat rewrite simpl_subst; auto.
repeat rewrite lift0.
apply piSAT0_elim with (2:=H1) (3:=H0) in H2; trivial.
Qed.

Lemma Real_inr RX RY x y t :
  Proper (eq_set ==> eqSAT) RY ->
  inSAT t (RY x) ->
  y == inr x ->
  inSAT (INR t) (sumReal RX RY y).
intros.
apply interSAT_intro; auto.
intros.
apply prodSAT_intro; intros.
unfold subst; simpl subst_rec.
unfold subst; rewrite simpl_subst; auto.
apply prodSAT_intro; intros.
unfold subst; simpl subst_rec.
unfold subst; repeat rewrite simpl_subst; auto.
repeat rewrite lift0.
apply piSAT0_elim with (2:=H1) (3:=H0) in H3; auto with *.
Qed.


Lemma Real_sum_case a RX RY C t b1 b2 :
  inSAT t (sumReal RX RY a) ->
  inSAT b1 (piSAT0 (fun x => a==inl x) RX (fun _ => C)) ->
  inSAT b2 (piSAT0 (fun x => a==inr x) RY (fun _ => C)) ->
  inSAT (App2 t b1 b2) C.
intros.
apply interSAT_elim with (x:=C) in H.
eapply prodSAT_elim;[apply prodSAT_elim with (1:=H)|]; trivial.
Qed.

Lemma Real_sum_case0 a RX RY C t b1 b2 :
  Proper (eq_set==>eqSAT) RX ->
  Proper (eq_set==>eqSAT) RY ->
  inSAT t (sumReal RX RY a) ->
  inSAT b1 (prodSAT (condSAT (exists x, a==inl x) (RX (dest_sum a))) C) ->
  inSAT b2 (prodSAT (condSAT (exists x, a==inr x) (RY (dest_sum a))) C) ->
  inSAT (App2 t b1 b2) C.
intros XM Ym; intros.
apply Real_sum_case with (1:=H).
 apply piSAT0_intro; intros.
  apply sat_sn in H0; trivial.
 apply prodSAT_elim with (1:=H0).
 rewrite condSAT_ok; [|eauto].
 rewrite H2,dest_sum_inl; trivial.
 
 apply piSAT0_intro; intros.
  apply sat_sn in H1; trivial.
 apply prodSAT_elim with (1:=H1).
 rewrite condSAT_ok; [|eauto].
 rewrite H2,dest_sum_inr; trivial.
Qed.
(*Lemma Real_sum_case0 a RX RY C t b1 b2 :
  Proper (eq_set==>eqSAT) RX ->
  Proper (eq_set==>eqSAT) RY ->
  inSAT t (sumReal RX RY a) ->
  inSAT b1 (prodSAT (depSAT (fun x => a==inl x) RX) C) ->
  inSAT b2 (prodSAT (depSAT (fun x => a==inr x) RY) C) ->
  inSAT (App2 t b1 b2) C.
intros XM Ym; intros.
apply Real_sum_case with (1:=H).
 apply piSAT0_intro; intros.
  apply sat_sn in H0; trivial.
 apply prodSAT_elim with (1:=H0).
 apply depSAT_intro'; [eauto|intros].
 rewrite H2 in H4; apply inl_inj in H4.
 rewrite <- H4; trivial.
 
 apply piSAT0_intro; intros.
  apply sat_sn in H1; trivial.
 apply prodSAT_elim with (1:=H1).
 apply depSAT_intro'; [eauto|intros].
 rewrite H2 in H4; apply inr_inj in H4.
 rewrite <- H4; trivial.
Qed.*)

Lemma sumReal_mt RX RY :
  inclSAT (sumReal RX RY empty) (prodSAT snSAT (prodSAT snSAT neuSAT)).
red; intros.
apply prodSAT_intro'; intros.
apply sat_sn in H0.
apply prodSAT_intro'; intros.
apply sat_sn in H1.
apply Real_sum_case with (1:=H).
 apply piSAT0_intro; trivial.
 intros.
 apply discr_mt_couple in H2; contradiction.

 apply piSAT0_intro; trivial.
 intros.
 apply discr_mt_couple in H2; contradiction.
Qed.

Lemma WHEN_SUM_sat RA RB S x t m :
  inSAT t (sumReal RA RB x) ->
  inSAT m S ->
  inSAT (App2 WHEN_SUM t m) S.
intros tsat msat.
unfold WHEN_SUM.
eapply inSAT_context.
 intros.
 apply inSAT_exp;[simpl;auto|].
 unfold subst; simpl.
 rewrite lift0.
 exact H.
apply prodSAT_elim with S; trivial.
apply Real_sum_case with (1:=tsat); auto.
 apply piSAT0_intro; intros; auto.
 apply inSAT_exp;[right; apply sat_sn in H0;trivial|].
 unfold subst; simpl.
 apply ID_intro0.

 apply piSAT0_intro; intros; auto.
 apply inSAT_exp;[right; apply sat_sn in H0;trivial|].
 unfold subst; simpl.
 apply ID_intro0.
Qed.


(** * Sigma-types *)

Definition COUPLE t1 t2 :=
  Abs (App2 (Ref 0) (lift 1 t1) (lift 1 t2)).

Lemma COUPLE_iota t1 t2 b:
  redp (App (COUPLE t1 t2) b) (App2 b t1 t2).
unfold COUPLE.
apply t_step; apply red1_beta.
unfold subst; simpl.
repeat rewrite simpl_subst; trivial.
repeat rewrite lift0; trivial.
Qed.

Definition is_couple t := exists a b, t = Abs (App2 (Ref 0) a b).


(** (WHEN_COUPLE t) reduces to the identity when t is a couple, or is
    neutral when t is. *)
Definition WHEN_COUPLE :=
  Abs (App (Ref 0) (Abs (Abs ID))).

Lemma WHEN_COUPLE_iota t u :
  is_couple t ->
  redp (App2 WHEN_COUPLE t u) u.
intros (a,(b,eqt)).
subst t.
unfold WHEN_COUPLE.
eapply t_trans.
 apply redp_app_l.
 apply t_step.
 apply beta.
unfold subst; simpl.
rewrite lift0.
eapply t_trans.
 apply redp_app_l.
 apply t_step.
 apply beta.
unfold subst; simpl.
rewrite lift0.
eapply t_trans.
 apply redp_app_l.
 apply redp_app_l.
 apply t_step.
 apply beta.
unfold subst; simpl.
eapply t_trans.
 apply redp_app_l.
 apply t_step.
 apply beta.
unfold subst; simpl.
apply t_step; apply red1_beta.
unfold subst; simpl.
rewrite lift0; reflexivity.
Qed.

Lemma WHEN_COUPLE_neutral t :
  inSAT t (prodSAT snSAT neuSAT) ->
  inSAT (App WHEN_COUPLE t) neuSAT.
intros.
unfold WHEN_COUPLE.
apply inSAT_exp;[simpl;auto|].
unfold subst; simpl; rewrite lift0.
apply prodSAT_elim with snSAT; trivial.
apply snSAT_intro; auto.
Qed.

Lemma WHEN_COUPLE_neutral2 t :
  inSAT t neuSAT ->
  inSAT (Lambda.App WHEN_COUPLE t) (prodSAT snSAT (prodSAT snSAT (prodSAT snSAT neuSAT))).
intros; apply -> neuSAT_def.
apply WHEN_COUPLE_neutral.
apply -> neuSAT_def; trivial.
Qed.

Definition cartSAT (X Y:SAT) : SAT :=
  interSAT (fun C => prodSAT (prodSAT X (prodSAT Y C)) C).

Instance cartSAT_mono : Proper (inclSAT ==> inclSAT ==> inclSAT) cartSAT.
unfold cartSAT.
do 3 red; intros.
apply interSAT_mono; intros C.
apply prodSAT_mono; auto with *.
apply prodSAT_mono; auto with *.
apply prodSAT_mono; auto with *.
Qed.

Instance cartSAT_morph : Proper (eqSAT ==> eqSAT ==> eqSAT) cartSAT.
do 3 red; intros.
apply interSAT_morph.
apply indexed_relation_id.
intros C.
rewrite H,H0; reflexivity.
Qed.


Lemma cartSAT_intro X Y t1 t2 :
  inSAT t1 X ->
  inSAT t2 Y ->
  inSAT (COUPLE t1 t2) (cartSAT X Y).
intros.
apply interSAT_intro.
 exact snSAT.
intros C.
apply prodSAT_intro; intros.
unfold subst; simpl subst_rec.
repeat rewrite simpl_subst; auto.
repeat rewrite lift0.
apply prodSAT_elim with (2:=H0).
apply prodSAT_elim with (2:=H).
trivial.
Qed.

Lemma cartSAT_case X Y C t b :
  inSAT t (cartSAT X Y) ->
  inSAT b (prodSAT X (prodSAT Y C)) ->
  inSAT (App t b) C.
intros.
apply prodSAT_elim with (2:=H0).
apply interSAT_elim with (1:=H).
Qed.

Lemma WHEN_COUPLE_sat A B S t m :
  inSAT t (cartSAT A B) ->
  inSAT m S ->
  inSAT (App2 WHEN_COUPLE t m) S.
intros tsat msat.
unfold WHEN_COUPLE.
eapply inSAT_context.
 intros.
 apply inSAT_exp;[simpl;auto|].
 unfold subst; simpl.
 rewrite lift0.
 exact H.
apply prodSAT_elim with S; trivial.
apply cartSAT_case with (1:=tsat).
apply prodSAT_intro; intros a asat.
unfold subst; simpl.
apply prodSAT_intro; intros b bsat.
unfold subst; simpl.
apply prodSAT_intro; intros c csat.
unfold subst; simpl.
rewrite lift0; trivial.
Qed.

(* Deprecated: sigmaReal *)
Definition sigmaReal (X:set->SAT) (Y:set->set->SAT) (a:set) : SAT :=
  cartSAT (X (fst a)) (Y (fst a) (snd a)).

Instance sigmaReal_morph_gen :
  Proper ((eq_set ==> eqSAT) ==> (eq_set ==> eq_set ==> eqSAT) ==>
          eq_set ==> eqSAT) sigmaReal.
do 4 red; intros.
apply cartSAT_morph.
 apply H; rewrite H1; reflexivity.
 apply H0; rewrite H1; reflexivity.
Qed.

Instance sigmaReal_morph X Y :
  Proper (eq_set ==> eqSAT) X ->
  Proper (eq_set ==> eq_set ==> eqSAT) Y ->
  Proper (eq_set ==> eqSAT) (sigmaReal X Y).
intros; apply sigmaReal_morph_gen; auto with *.
Qed.

Lemma Real_couple x y X Y t1 t2 :
  Proper (eq_set ==> eqSAT) X ->
  Proper (eq_set ==> eq_set ==> eqSAT) Y ->
  inSAT t1 (X x) ->
  inSAT t2 (Y x y) ->
  inSAT (COUPLE t1 t2) (sigmaReal X Y (couple x y)).
intros.
unfold sigmaReal.
rewrite fst_def,snd_def.
apply cartSAT_intro; trivial.
Qed.

Lemma Real_sigma_elim X Y RX RY a C t b :
  ext_fun X Y ->
  Proper (eq_set ==> eqSAT) C ->
  a ∈ sigma X Y ->
  inSAT t (sigmaReal RX RY a) ->
  inSAT b (piSAT0 (fun x => x∈X) RX
           (fun x => piSAT0 (fun y => y ∈ Y x) (RY x) (fun y => C(couple x y)))) ->
  inSAT (App t b) (C a).
intros.
apply sigma_elim in H1; auto with *.
destruct H1 as (eqa,(ty1,ty2)).
apply cartSAT_case with (1:=H2).
apply prodSAT_intro'.
intros ta asat.
apply piSAT0_elim with (2:=ty1)(3:=asat) in H3.
apply prodSAT_intro'.
intros tb bsat.
apply piSAT0_elim with (2:=ty2)(3:=bsat) in H3.
rewrite <- eqa in H3.
trivial.
Qed.


  (** Fixpoint *)

Definition monoFam (A:(set->SAT)->set->SAT) :=
  forall X X', inclFam X X' -> inclFam (A X) (A X').

Definition fixSAT (A:(set->SAT)->set->SAT) (x:set) : SAT :=
  interSAT (fun X:{X|Proper(eq_set==>eqSAT)X /\ inclFam (A X) X} =>
            proj1_sig X x).

Instance fixSAT_morph0 A :
  Proper (eq_set ==> eqSAT) (fixSAT A).
do 2 red; intros.
apply interSAT_morph_subset.
 reflexivity.
simpl.
intros X _ (Xm, Xpost).
auto.
Qed.

Instance fixSAT_morph : Proper (((eq_set==>eqSAT)==>eq_set==>eqSAT)==>eq_set==>eqSAT) fixSAT.
do 3 red; intros.
apply interSAT_morph_subset; simpl.
 intros X.
 apply and_iff_morphisml; auto with *.
 intros Xm _.
 apply fa_morph; intros z.
 apply inclSAT_morph; auto with *.
 apply H; auto with *.

 intros.
 apply Px; trivial.
Qed.

Lemma fixSAT_lower_bound A X :
  Proper (eq_set==>eqSAT) X ->
  inclFam (A X) X ->
  inclFam (fixSAT A) X.
do 2 red; intros.
apply interSAT_elim with
  (x:=existT (fun X=>Proper (eq_set==>eqSAT) X /\ inclFam (A X) X)
         X (conj H H0)) in H1; simpl in H1.
trivial.
Qed.

Lemma post_fix_lfp A :
  monoFam A ->
  inclFam (A (fixSAT A)) (fixSAT A).
intros Amono x.
red; intros.
unfold fixSAT.
eapply interSAT_intro.
 exists (fun _ => snSAT).
 split.
  do 2 red; reflexivity.
 do 2 red; intros.
 apply snSAT_intro.
 apply sat_sn in H0; trivial.
intros (X,(Xm,Xpost)); simpl. 
apply Xpost; trivial.
apply Amono with (X:=fixSAT A); trivial.
apply fixSAT_lower_bound; trivial.
Qed.

Lemma pre_fix_lfp A :
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  monoFam A ->
  inclFam (fixSAT A) (A (fixSAT A)).
intros Am Amono.
apply fixSAT_lower_bound; trivial.
 do 2 red; intros.
 apply Am; trivial.
 apply fixSAT_morph0.
apply Amono; trivial.
apply post_fix_lfp; trivial.
Qed.

Lemma fixSAT_eq A :
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  monoFam A ->
  forall x,
  eqSAT (fixSAT A x) (A (fixSAT A) x).
split.
 apply pre_fix_lfp; trivial.
 apply post_fix_lfp; trivial.
Qed.

(** * Structural fixpoint. *)

(** To avoid non-termination, we need to insert a "guard" operator G to control
    the self-application of the fixpoint.
 *)


Definition GUARD G :=
  Abs (Abs (App (App (App (App (lift 2 G) (Ref 0)) (Ref 1)) (Ref 1)) (Ref 0))).

Lemma GUARD_sim G m t :
  (forall u, redp (App2 G t u) u) ->
  redp (App2 (GUARD G) m t) (App2 m m t).
intros; unfold GUARD.
eapply t_trans.
 apply redp_app_l.
 apply t_step; apply beta.
unfold subst; simpl.
rewrite simpl_subst; auto.
eapply t_trans.
 apply t_step; apply beta.
unfold subst; simpl.
rewrite !simpl_subst; trivial.
rewrite !lift0.
apply redp_app_l.
apply redp_app_l.
apply H.
Qed.
  
Lemma GUARD_sat G m t S :
  inSAT (App2 (App2 G t m) m t) S ->
  inSAT (App2 (GUARD G) m t) S.
intros.
eapply inSAT_context.
 intros.
 apply inSAT_exp;[simpl;rewrite Bool.orb_true_r;auto|].
 unfold subst; simpl.
 rewrite simpl_subst; auto.
 exact H0.
apply inSAT_exp;[simpl;rewrite Bool.orb_true_r;auto|].
unfold subst; simpl subst_rec.
repeat rewrite simpl_subst; auto.
repeat rewrite lift0.
trivial.
Qed.

Lemma GUARD_neutral G m t :
  sn m ->
  inSAT (App G t) (prodSAT snSAT (prodSAT snSAT (prodSAT snSAT neuSAT))) ->
  inSAT (App2 (GUARD G) m t) neuSAT.
intros.
apply GUARD_sat.
apply snSAT_intro in H.
apply prodSAT_elim with snSAT.
 apply prodSAT_elim with (2:=H).
 apply prodSAT_elim with (2:=H).
 trivial.
apply snSAT_intro.
apply sat_sn in H0.
apply subterm_sn with (1:=H0); auto.
Qed.


Definition guard_sum := GUARD WHEN_SUM.

Lemma guard_sum_INL : forall m n,
  redp (App2 guard_sum m (INL n)) (App2 m m (INL n)).
intros.
apply GUARD_sim.
intro; apply WHEN_SUM_INL.
Qed.
Lemma guard_sum_INR : forall m n,
  redp (App2 guard_sum m (INR n)) (App2 m m (INR n)).
intros.
apply GUARD_sim.
intro; apply WHEN_SUM_INR.
Qed.

Lemma guard_sum_neutral m t :
  sn m ->
  inSAT t (prodSAT snSAT (prodSAT snSAT neuSAT)) ->
  inSAT (App2 guard_sum m t) neuSAT.
unfold guard_sum; intros.
apply GUARD_neutral; trivial.
apply neuSAT_def.
apply WHEN_SUM_neutral; trivial.
Qed.

Definition guard_couple := GUARD WHEN_COUPLE.

Lemma guard_couple_iota : forall m a b,
  redp (App2 guard_couple m (COUPLE a b)) (App2 m m (COUPLE a b)).
intros.
apply GUARD_sim.
intro; apply WHEN_COUPLE_iota.
unfold is_couple, COUPLE; eauto.
Qed.

Lemma guard_couple_neutral m t :
  sn m ->
  inSAT t (prodSAT snSAT neuSAT) ->
  inSAT (App2 guard_couple m t) neuSAT.
unfold guard_couple; intros.
apply GUARD_neutral; trivial.
apply neuSAT_def.
apply WHEN_COUPLE_neutral; trivial.
Qed.


Definition FIXP G m :=
  App (GUARD G) (Abs (App (lift 1 m) (App (lift 1 (GUARD G)) (Ref 0)))).

(** when the guard expands when applied to n (e.g. when it's a constructor),
    then the fixpoint unrolls once. *)
Lemma FIXP_sim : forall G m n,
  (forall u, redp (App2 G n u) u) ->
  redp (App (FIXP G m) n) (App2 m (FIXP G m) n).
intros G m n Gsim.
unfold FIXP at 1.
eapply t_trans.
 apply GUARD_sim; trivial.
apply redp_app_l.
apply t_step.
apply red1_beta.
set (t1 := Abs (App (lift 1 m) (App (lift 1 (GUARD G)) (Ref 0)))).
unfold subst; simpl.
rewrite !simpl_subst; auto.
rewrite simpl_subst_rec; auto.
rewrite !lift0.
rewrite lift_rec0.
reflexivity.
Qed.

Lemma FIXP_sn G m:
  (forall m, sn m -> sn (App (GUARD G) m)) ->
  sn (App m (App (GUARD G) (Ref 0))) ->
  sn (FIXP G m).
intros snG satm.
unfold FIXP.
apply snG; trivial.
apply sn_abs.
apply sn_subst with (Ref 0).
unfold subst; simpl.
rewrite simpl_subst; auto.
rewrite simpl_subst_rec; auto.
rewrite lift0.
rewrite lift_rec0.
exact satm.
Qed.

Lemma FIXP_neutral G m t A B C:
  (exists w, w ∈ A) ->
  (forall t, inSAT t (piSAT0 (fun x => x ∈ A) B C) -> sn (App m t)) ->
  (forall x n t S,
   x ∈ A ->
   inSAT n (B x) -> inSAT t S -> inSAT (App2 G n t) S) ->
  inSAT (App G t) (prodSAT snSAT (prodSAT snSAT (prodSAT snSAT neuSAT))) ->
  inSAT (App (FIXP G m) t) neuSAT.
intros Awit msat Gsat Gneutr.
apply GUARD_neutral; trivial.
eapply sat_sn with (prodSAT neuSAT _).
apply prodSAT_intro; intros.
unfold subst, subst_rec; fold subst_rec.
rewrite !simpl_subst, !lift0; auto.
simpl.
apply snSAT_intro.
apply msat.
apply piSAT0_intro'; intros; trivial.
apply GUARD_sat.
apply prodSAT_elim with (2:=H1).
apply prodSAT_elim with (2:=H).
apply Gsat with (2:=H1); trivial.
apply neuSAT_def; trivial.
Qed.


Require Import ZFord.
(*Require Import ZFcoc.*)

Section FIXP_Reducibility.

  Variable G : term.

  Variable bot : set.
  
  Variable T:set->set.
  Let Tbot o := bot ∪ T o.
(*  Variable Tbot:set->set.*)
  Variable RT:set->SAT.
  
  (* Saturation property of guard G *)
  Hypothesis Gneutr : forall t,
      inSAT t neuSAT ->
      inSAT (App G t) (prodSAT snSAT (prodSAT snSAT (prodSAT snSAT neuSAT))).
  Hypothesis Gsat : forall o x t m (X:SAT),
      isOrd o -> x ∈ T o ->
      inSAT t (RT x) ->
      inSAT m X ->
      inSAT (App2 G t m) X.

  Variable o:set.
  Hypothesis oo : isOrd o.

  (* strict domain values form a continuous sequence *)
  Hypothesis Tcont : forall y n,
      isOrd y -> y ⊆ o ->
      n ∈ Tbot y ->
      eqSAT (RT n) neuSAT \/ exists2 y', y' ∈ y & n ∈ T (osucc y').

  (* Tbot is not empty *)
  Hypothesis Tbot_nmt :
    forall o, isOrd o -> exists w, w ∈ Tbot o.


  Section NonDependent.
    
  Variable RU:set->set->SAT.
  Let FIX_bot o := piSAT0 (fun n => n ∈ Tbot o) RT (RU o).
  Let FIX_strict o := piSAT0 (fun n => n ∈ T o) RT (RU o).

  (* monotonicity of RU *)
  Hypothesis RUmono : forall y y' n,
      isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o ->
      n ∈ T y ->
      inclSAT (RU y n) (RU y' n).

  Variable m:term.

  Hypothesis msat :
    inSAT m (piSAT0 (fun o' => o' ∈ o)
                    (fun o' => FIX_bot o') (fun o' => FIX_strict (osucc o'))).
  Hypothesis mneutr :
    inSAT m (prodSAT (FIX_bot empty) snSAT).

  Lemma FIXP_sat : inSAT (FIXP G m) (FIX_bot o).
elim oo using isOrd_ind; intros.
apply piSAT0_intro'; [|apply  Tbot_nmt;trivial].
intros x u xty0 ureal.
unfold FIXP.
assert (sn (Abs (App (lift 1 m) (App (lift 1 (GUARD G)) (Ref 0))))).
 (* neutral case *)
 eapply sat_sn.
 apply prodSAT_intro with (A:=neuSAT).
 intros v vsat.
 match goal with |- inSAT _ ?T =>
   change (inSAT (App (subst v (lift 1 m)) (App (subst v (lift 1 (GUARD G))) (lift 0 v))) T)
 end.
 unfold subst; rewrite !simpl_subst; trivial.
 rewrite !lift0.
 apply prodSAT_elim with (1:=mneutr).
 eapply piSAT0_intro'.
 2:apply Tbot_nmt; auto.
 intros n nt nty nsat.
 apply GUARD_sat.
 apply prodSAT_elim with (2:=nsat).
 apply prodSAT_elim with (2:=vsat).
 apply prodSAT_elim with (2:=vsat).
 apply Tcont in nty; auto.
 destruct nty as [?|(y',?,_)].
  rewrite H2 in nsat. 
  specialize Gneutr with (1:=nsat).
 revert Gneutr; apply prodSAT_mono; auto with *.
  apply neuSAT_inf.
 apply prodSAT_mono; auto with *.
  apply neuSAT_inf.
 apply prodSAT_mono; auto with *.
  rewrite H2.
  apply neuSAT_inf.
  apply neuSAT_inf.

  apply empty_ax in H2; contradiction.
apply GUARD_sat.
apply Tcont in xty0; trivial.
destruct xty0 as [?|(y',?,?)].
 apply prodSAT_elim with (2:=ureal).
 apply prodSAT_elim with (2:=snSAT_intro H2).
 eapply prodSAT_elim;[|apply (snSAT_intro H2)].
 rewrite H3 in ureal.
 specialize Gneutr with (1:=ureal); revert Gneutr.
 apply prodSAT_mono; auto with *.
 apply prodSAT_mono; auto with *.
 apply prodSAT_mono; auto with *.
  red; red; intros.
  apply sat_sn in H4; trivial.
 apply neuSAT_inf.

 specialize H1 with (1:=H3).
 assert (isOrd y') by eauto using isOrd_inv.
 assert (zlt : osucc y' ⊆ y).
  red; intros; apply le_lt_trans with y'; auto.
 eapply inSAT_context.
  apply inSAT_context.
  intros.
  apply Gsat with (2:=H4); auto.
  exact H6.
 eapply inSAT_context.
  intros.
  apply inSAT_exp.
   left; simpl; rewrite !Bool.orb_true_r; trivial.
  unfold subst; simpl.
  rewrite simpl_subst; auto.
  rewrite simpl_subst_rec; auto.
  rewrite !lift0.
  rewrite !lift_rec0.
  change (inSAT (App m (FIXP G m)) S).
  exact H6.
 apply RUmono with (osucc y'); auto.
 assert (y' ∈ o).
  apply H0; trivial.
 eapply piSAT0_elim with (3:=ureal).
  apply piSAT0_elim with (1:=msat); auto.

  trivial.
Qed.

  End NonDependent.

  Require Import ZFrelations ZFfixrec ZFrecbot.
  
  Section Dependent.

    Variable U : set -> set -> set.
    Variable F : set -> set -> set.
    Variable recursor : set -> set.
    Hypothesis isrec : typed_bot_recursor_spec bot T U F recursor o.

    Variable RU:set->set->set->SAT.
    Hypothesis RUm : Proper (eq_set ==> eq_set ==> eq_set ==> eqSAT) RU.

    (* monotonicity of RU *)
    Hypothesis RUmono : forall o' o'' x y y',
      isOrd o' ->
      isOrd o'' ->
      o' ⊆ o'' ->
      o'' ⊆ o ->
      x ∈ T o' -> y ∈ U o' x -> y == y' -> inclSAT (RU o' x y) (RU o'' x y').
    
    Let FIX_ty o f:=
      piSAT0 (fun n => n ∈ Tbot o) RT (fun n => RU o n (cc_app f n)).

    Variable m:term.

    Hypothesis msat : forall o' f u,
        isOrd o' ->
        o' ∈ singl empty ∪ o ->
        f ∈ (Π w ∈ Tbot o', U o' w) ->
        inSAT u (FIX_ty o' f) ->
        inSAT (App m u) (FIX_ty (osucc o') (F o' f)).

    Let RU' o n := RU o n (cc_app (recursor o) n).
    
    Lemma recursor_sat : inSAT (FIXP G m) (FIX_ty o (recursor o)).
unfold FIX_ty.
apply FIXP_sat with (RU:=RU').
{unfold RU'; intros.
 apply RUmono; auto.
  assert (tyr : recursor y ∈ Π x ∈ Tbot y, U y x).
   apply typed_bot_rec_typ with (1:=isrec); auto.
   transitivity y'; trivial.
  apply cc_prod_elim with (1:=tyr).
  apply union2_intro2; trivial.

  apply typed_bot_rec_irr with (1:=isrec); auto.
  apply union2_intro2; trivial. }
{apply piSAT0_intro.
 {assert (inSAT (App m daimon) (FIX_ty (osucc empty) (F empty (recursor empty)))).
  {apply msat; auto.
    apply union2_intro1; apply singl_intro.
   apply typed_bot_rec_typ with (1:=isrec); auto.
    apply varSAT. }
  apply sat_sn in H.
  apply subterm_sn with (App m daimon); auto. }
 {intros.
  assert (xo : isOrd x) by eauto using isOrd_inv.
  assert (Wty : recursor x ∈ Π w ∈ Tbot x, U x w).
   apply typed_bot_rec_typ with (1:=isrec); trivial.
   red; intros; apply isOrd_trans with x; auto.
  specialize msat with (1:=xo)(2:=union2_intro2 _ _ _ H)(3:=Wty)(4:=H0).
  revert msat; apply piSAT0_mono with (f:=fun x=>x); auto with *.
   intros; apply union2_intro2; trivial.

   intros.
   unfold RU'.
   rewrite typed_bot_rec_eqn_succ with (2:=isrec); auto with *. } }
{apply prodSAT_intro'; intros.
 assert (inSAT (App m v) (FIX_ty (osucc empty) (F empty (recursor empty)))).
  apply msat; auto.
   apply union2_intro1; apply singl_intro.
  apply typed_bot_rec_typ with (1:=isrec); auto.

  apply snSAT_intro.
  apply sat_sn with (1:=H0). }
Qed.

(*
Lemma FIXP_sat G o T U RT m X :
  let FIX_bot o := piSAT0 (fun n => n ∈ U o) RT (X o) in
  let FIX_strict o := piSAT0 (fun n => n ∈ T o) RT (X o) in
  isOrd o ->
  (* strict domain values form a continuous sequence *)
  (forall y n, isOrd y -> y ⊆ o -> n ∈ U y ->
   eqSAT (RT n) neuSAT \/ exists2 y', y' ∈ y & n ∈ T (osucc y')) ->
  (* U is not empty *)
  (forall o, isOrd o -> exists w, w ∈ U o) ->
  (* monotonicity of X *)
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ T y ->
   inclSAT (X y n) (X y' n)) ->
  (* Saturation property of guard G *)
  (forall t,
   inSAT t neuSAT ->
   inSAT (App G t) (prodSAT snSAT (prodSAT snSAT (prodSAT snSAT neuSAT)))) ->
  (forall o x t m (X:SAT),
   isOrd o -> x ∈ T o ->
   inSAT t (RT x) ->
   inSAT m X ->
   inSAT (App2 G t m) X) ->
  (* Saturation of the body *)
  inSAT m (piSAT0 (fun o' => o' ∈ o)
    (fun o' => FIX_bot o') (fun o' => FIX_strict (osucc o'))) ->
  inSAT m (prodSAT (FIX_bot empty) snSAT) ->
  (* *)
  inSAT (FIXP G m) (FIX_bot o).
intros FIX_bot FIX_strict oo Tcont Ubot Xmono Gneutr Gsat msat mneutr.
elim oo using isOrd_ind; intros.
apply piSAT0_intro'; [|apply  Ubot;trivial].
intros x u xty0 ureal.
unfold FIXP.
assert (sn (Abs (App (lift 1 m) (App (lift 1 (GUARD G)) (Ref 0))))).
 (* neutral case *)
 eapply sat_sn.
 apply prodSAT_intro with (A:=neuSAT).
 intros v vsat.
 match goal with |- inSAT _ ?T =>
   change (inSAT (App (subst v (lift 1 m)) (App (subst v (lift 1 (GUARD G))) (lift 0 v))) T)
 end.
 unfold subst; rewrite !simpl_subst; trivial.
 rewrite !lift0.
 apply prodSAT_elim with (1:=mneutr).
 eapply piSAT0_intro'.
 2:apply Ubot; auto.
 intros n nt nty nsat.
 apply GUARD_sat.
 apply prodSAT_elim with (2:=nsat).
 apply prodSAT_elim with (2:=vsat).
 apply prodSAT_elim with (2:=vsat).
 apply Tcont in nty; auto.
 destruct nty as [?|(y',?,_)].
  rewrite H2 in nsat. 
  specialize Gneutr with (1:=nsat).
 revert Gneutr; apply prodSAT_mono; auto with *.
  apply neuSAT_inf.
 apply prodSAT_mono; auto with *.
  apply neuSAT_inf.
 apply prodSAT_mono; auto with *.
  rewrite H2.
  apply neuSAT_inf.
  apply neuSAT_inf.

  apply empty_ax in H2; contradiction.
apply GUARD_sat.
apply Tcont in xty0; trivial.
destruct xty0 as [?|(y',?,?)].
 apply prodSAT_elim with (2:=ureal).
 apply prodSAT_elim with (2:=snSAT_intro H2).
 eapply prodSAT_elim;[|apply (snSAT_intro H2)].
 rewrite H3 in ureal.
 specialize Gneutr with (1:=ureal); revert Gneutr.
 apply prodSAT_mono; auto with *.
 apply prodSAT_mono; auto with *.
 apply prodSAT_mono; auto with *.
  red; red; intros.
  apply sat_sn in H4; trivial.
 apply neuSAT_inf.

 specialize H1 with (1:=H3).
 assert (isOrd y') by eauto using isOrd_inv.
 assert (zlt : osucc y' ⊆ y).
  red; intros; apply le_lt_trans with y'; auto.
 eapply inSAT_context.
  apply inSAT_context.
  intros.
  apply Gsat with (2:=H4); auto.
  exact H6.
 eapply inSAT_context.
  intros.
  apply inSAT_exp.
   left; simpl; rewrite !Bool.orb_true_r; trivial.
  unfold subst; simpl.
  rewrite simpl_subst; auto.
  rewrite simpl_subst_rec; auto.
  rewrite !lift0.
  rewrite !lift_rec0.
  change (inSAT (App m (FIXP G m)) S).
  exact H6.
 apply Xmono with (osucc y'); auto.
 assert (y' ∈ o).
  apply H0; trivial.
 eapply piSAT0_elim with (3:=ureal).
  apply piSAT0_elim with (1:=msat); auto.

  trivial.
Qed.
 *)
    End Dependent.
End FIXP_Reducibility.
