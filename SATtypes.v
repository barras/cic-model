
Require Import ZF ZFpairs ZFsum Sat.
Require Import ZFlambda.
Require Import Lambda.

Set Implicit Arguments.

(** Unit type *)

Definition unitSAT :=
  interSAT (fun C => prodSAT C C).

Definition ID := Abs (Ref 0).

Lemma ID_intro : inSAT ID unitSAT.
apply interSAT_intro with (1:=snSAT).
intros.
apply prodSAT_intro; intros.
unfold subst; simpl subst_rec.
rewrite lift0.
trivial.
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

Definition sumReal (X Y:set->SAT) (a:set) : SAT :=
  interSAT (fun C =>
     prodSAT (piSAT0 (fun x => a==inl x) X (fun _ => C))
    (prodSAT (piSAT0 (fun x => a==inr x) Y (fun _ => C))
     C)).

Lemma Real_sum_case X Y a RX RY C t b1 b2 :
  a ∈ sum X Y ->
  inSAT t (sumReal RX RY a) ->
  inSAT b1 (piSAT0 (fun x => a==inl x) RX (fun _ => C)) ->
  inSAT b2 (piSAT0 (fun x => a==inr x) RY (fun _ => C)) ->
  inSAT (App2 t b1 b2) C.
intros.
apply interSAT_elim with (x:=C) in H0.
eapply prodSAT_elim;[apply prodSAT_elim with (1:=H0)|]; trivial.
Qed.

Lemma Real_inl RX RY x t :
  Proper (eq_set ==> eqSAT) RX ->
  inSAT t (RX x) ->
  inSAT (INL t) (sumReal RX RY (inl x)).
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
apply piSAT0_elim with (x:=x) (u:=t) in H1; auto with *.
Qed.

Lemma Real_inr RX RY x t :
  Proper (eq_set ==> eqSAT) RY ->
  inSAT t (RY x) ->
  inSAT (INR t) (sumReal RX RY (inr x)).
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
apply piSAT0_elim with (x:=x) (u:=t) in H2; auto with *.
Qed.

(** Sigma-types *)

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

Definition sigmaReal (X:set->SAT) (Y:set->set->SAT) (a:set) : SAT :=
  interSAT (fun C => prodSAT
     (piSAT0 (fun x => a==couple x (snd a)) X (fun x => prodSAT (Y x (snd a)) C))
     C).

Instance sigmaReal_morph X Y :
  Proper (eq_set ==> eqSAT) X ->
  Proper (eq_set ==> eq_set ==> eqSAT) Y ->
  Proper (eq_set ==> eqSAT) (sigmaReal X Y).
do 2 red; intros.
apply interSAT_morph.
apply indexed_relation_id; intros C.
apply prodSAT_morph; auto with *.
apply piSAT0_morph; intros; auto with *.
 red; intros.
 rewrite H1; reflexivity.

 apply prodSAT_morph; auto with *.
 rewrite H1; reflexivity.
Qed.

Lemma Real_couple x y X Y t1 t2 :
  Proper (eq_set ==> eqSAT) X ->
  Proper (eq_set ==> eq_set ==> eqSAT) Y ->
  inSAT t1 (X x) ->
  inSAT t2 (Y x y) ->
  inSAT (COUPLE t1 t2) (sigmaReal X Y (couple x y)).
intros.
apply interSAT_intro.
 exact snSAT.
intros C.
apply prodSAT_intro; intros.
unfold subst; simpl subst_rec.
repeat rewrite simpl_subst; auto.
repeat rewrite lift0.
apply piSAT0_elim' in H3; red in H3.
apply prodSAT_elim with (2:=H2).
rewrite <- (snd_def x y).
apply H3; trivial.
rewrite snd_def; reflexivity.
Qed.
(*
Lemma Real_sigma_elim X Y a C t b :
  inSAT t (sigmaReal X Y a) ->
  inSAT b (prodSAT (X (fst a)) (prodSAT (Y (fst a) (snd a)) C)) ->
  inSAT (App t b) C.
intros.
apply interSAT_elim with (x:=C) in H.
apply prodSAT_elim with (1:=H) (2:=H0).
Qed.
*)
Lemma Real_sigma_elim X Y RX RY a C t b :
  ext_fun X Y ->
  Proper (eq_set ==> eqSAT) C ->
  a ∈ sigma X Y ->
  inSAT t (sigmaReal RX RY a) ->
  inSAT b (piSAT0 (fun x => x∈X) RX
           (fun x => piSAT0 (fun y => y ∈ Y x) (RY x) (fun y => C(couple x y)))) ->
  inSAT (App t b) (C a).
intros.
assert (eqa := surj_pair _ _ _ (subset_elim1 _ _ _ H1)).
rewrite eqa.
unfold sigmaReal in H2.
refine (prodSAT_elim _ (interSAT_elim H2 _) _).
apply piSAT0_intro; intros.
 apply sat_sn in H3; trivial.
apply prodSAT_intro'; intros.
rewrite eqa in H4; apply couple_injection in H4; destruct H4 as (?,_).
rewrite H4.
refine (piSAT0_elim' (piSAT0_elim' H3 x _ _ H5) (snd a) _ _ H6).
 apply fst_typ_sigma in H1; rewrite H4 in H1; trivial.

 apply snd_typ_sigma with (A:=X); auto with *.
Qed.

(** * Structural fixpoint. *)

(** To avoid non-termination, we need to insert a "guard" operator G to control
    the self-application of the fixpoint.
 *)

Definition FIXP G m :=
  App G (Abs (App (lift 1 m) (App (lift 1 G) (Ref 0)))).

(** when the guard expands when applied to n (e.g. when it's a constructor),
    then the fixpoint unrolls once. *)
Lemma FIXP_sim : forall G m n,
  (forall m, redp (App2 G m n) (App2 m m n)) ->
  redp (App (FIXP G m) n) (App2 m (FIXP G m) n).
intros G m n Gsim.
unfold FIXP at 1.
eapply t_trans.
 apply Gsim.
apply redp_app_l.
apply t_step.
apply red1_beta.
set (t1 := Abs (App (lift 1 m) (App (lift 1 G) (Ref 0)))).
unfold subst; simpl.
repeat rewrite simpl_subst; auto.
repeat rewrite lift0.
reflexivity.
Qed.

Lemma FIXP_sn G m:
  (forall m, sn m -> sn (App G m)) ->
  sn (App m (App G (Ref 0))) ->
  sn (FIXP G m).
intros snG satm.
unfold FIXP.
apply snG; trivial.
apply sn_abs.
apply sn_subst with (Ref 0).
unfold subst; simpl.
repeat rewrite simpl_subst; auto.
repeat rewrite lift0; auto.
Qed.

Require Import ZFord.

Lemma FIXP_sat0 G o T U RT m X :
  let FIX_bot o := piSAT0 (fun n => n ∈ U o) (RT o) (X o) in
  let FIX_strict o := piSAT0 (fun n => n ∈ T o) (RT o) (X o) in
  isOrd o ->
  (* strict domain values form a continuous sequence *)
  (forall y n, isOrd y -> y ⊆ o -> n ∈ T y -> exists2 y', y' ∈ y & n ∈ T (osucc y')) ->
  (* U is not empty *)
  (forall o, isOrd o -> exists w, w ∈ U o) ->
  (* monotonicity of RT and X *)
  (forall y y' n, isOrd y -> isOrd y' -> n ∈ T y -> y ⊆ y' -> y' ⊆ o ->
   eqSAT (RT y n) (RT y' n)) ->
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ T y ->
   inclSAT (X y n) (X y' n)) ->
  (* Saturation property of guard G *)
  (forall o x t m (X:SAT), isOrd o -> x ∈ U o ->
   inSAT t (RT o x) ->
   sn m ->
   (x ∈ T o -> inSAT (App2 m m t) X) ->
   inSAT (App2 G m t) X) ->

  inSAT m (piSAT0 (fun o' => o' ∈ osucc o)
    (fun o' => FIX_bot o') (fun o' => FIX_strict (osucc o'))) ->
  inSAT (FIXP G m) (FIX_bot o).
intros FIX_bot FIX_strict oo Tcont Ubot Rirrel Xmono Gsat msat.
elim oo using isOrd_ind; intros.
apply piSAT0_intro'; [|apply  Ubot;trivial].
intros x u xty0 ureal.
apply Gsat with (2:=xty0); trivial.
 (* neutral case *)
 eapply sat_sn.
 apply prodSAT_intro with (A:=interSAT(fun S=>S)).
 intros v vsat.
 unfold subst; simpl subst_rec.
 rewrite !simpl_subst; trivial.
 rewrite !lift0.
 match goal with |- inSAT _ ?S =>
   change (inSAT (App m (App G v)) S)
 end.
 apply piSAT0_elim' in msat; red in msat.
 apply msat with (x:=y); auto with *.
  apply ole_lts; auto.

  apply piSAT0_intro'; intros; [|apply Ubot; trivial].
  eapply Gsat with (2:=H2); trivial.
   apply sat_sn in vsat; trivial.

   intros _.
   eapply prodSAT_elim;[|apply H3].
   eapply prodSAT_elim;[|apply vsat].
   apply interSAT_elim with (1:=vsat).

 (* closed case *)
 intros xty.
 eapply inSAT_context; intros.
  apply inSAT_exp; simpl.
    left; simpl.
    rewrite Bool.orb_true_r.
    apply Bool.orb_true_r.

    unfold subst; simpl subst_rec.
    repeat rewrite simpl_subst; auto.
    repeat rewrite lift0.
    change (inSAT (App m (FIXP G m)) S).
    eexact H2.
 apply Tcont in xty; trivial.
 destruct xty as (z,zty,xty).
 specialize H1 with (1:=zty).
 assert (zo : isOrd z).
  apply isOrd_inv with y; trivial.
 assert (zlt : osucc z ⊆ y).
  red; intros; apply le_lt_trans with z; auto.
 assert (ureal' : inSAT u (RT (osucc z) x)).
  rewrite <- Rirrel with (3:=xty) in ureal; auto.
 apply Xmono with (osucc z); auto.
 assert (z ∈ osucc o).
  apply isOrd_trans with o; auto.
  apply H0; trivial.
 apply piSAT0_elim' in msat; red in msat.
 specialize msat with (1:=H2) (2:=H1).
 apply piSAT0_elim' in msat; red in msat.
 apply msat; trivial.
Qed.


(* deprecated: *)
Lemma FIXP_sat G o T RT m X :
  let FIX_ty o := piSAT0 (fun n => n ∈ T o) (RT o) (X o) in
  isOrd o ->
  (forall m, sn m -> sn (App G m)) ->
  (forall o x t m (X:SAT), isOrd o -> x ∈ T o ->
   inSAT t (RT o x) ->
   inSAT (App2 m m t) X ->
   inSAT (App2 G m t) X) ->
  (forall y n, isOrd y -> y ⊆ o -> n ∈ T y -> exists2 y', y' ∈ y & n ∈ T (osucc y')) ->
  (forall y y' n, isOrd y -> isOrd y' -> n ∈ T y -> y ⊆ y' -> y' ⊆ o ->
   eqSAT (RT y n) (RT y' n)) ->

  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ T y ->
   inclSAT (X y n) (X y' n)) ->
  inSAT m (piSAT0 (fun o' => o' ∈ osucc o) (fun o' => FIX_ty o') (fun o' => FIX_ty (osucc o'))) ->
  inSAT (FIXP G m) (FIX_ty o).
intros FIX_ty oo snG Gsat Tcont Rirrel Xmono msat.
elim oo using isOrd_ind; intros.
apply piSAT0_intro.
 apply FIXP_sn; trivial.
 apply piSAT0_elim' in msat; red in msat.
 eapply sat_sn; apply msat with (x:=o).
  apply lt_osucc; trivial.

  apply piSAT0_intro; intros.
   apply snG.
   apply sn_var.

   apply Gsat with (2:=H2); trivial.
   eapply prodSAT_elim; [|eexact H3].
   apply prodSAT_elim with snSAT;apply varSAT.

intros x u xty0 ureal.
destruct Tcont with (3:=xty0) as (z,?,?); trivial.
specialize H1 with (1:=H2).
assert (zo : isOrd z).
 apply isOrd_inv with y; trivial.
assert (osucc z ⊆ y).
 red; intros.
 apply isOrd_plump with z; trivial.
  eauto using isOrd_inv.
  apply olts_le; trivial.

assert (ureal' : inSAT u (RT (osucc z) x)).
 apply Rirrel with (3:=H3) (4:=H4); auto.
unfold FIXP.
apply Gsat with (2:=H3)(3:=ureal') (x:=x); auto.
eapply inSAT_context; intros.
 apply inSAT_exp.
  left; simpl.
  rewrite Bool.orb_true_r.
  apply Bool.orb_true_r.

  unfold subst; simpl subst_rec.
  repeat rewrite simpl_subst; auto.
  repeat rewrite lift0.
  change (inSAT (App m (FIXP G m)) S).
  eexact H5.
apply Xmono with (osucc z); auto.
assert (z ∈ osucc o).
 apply isOrd_trans with o; auto.
 apply H0; trivial.
apply piSAT0_elim' in msat; red in msat.
specialize msat with (1:=H5) (2:=H1).
apply piSAT0_elim' in msat; red in msat; auto.
Qed.


(** Transfinite iteration *)

Require Import ZFfixrec.
Require Import ZFrelations.
Require Import ZFord ZFfix.

Definition tiSAT (F:set->set) (A:(set->SAT)->set->SAT) (o:set) (x:set) : SAT :=
  sSAT (cc_app (REC (fun o' f => cc_lam (TI F (osucc o'))
                                   (fun y => iSAT (A (fun z => sSAT (cc_app f z)) y))) o) x).

Lemma tiSAT_ext1 A F f o :
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  ext_fun (TI F (osucc o)) (fun y => iSAT (A (fun z => sSAT (cc_app f z)) y)).
do 2 red; intros.
apply iSAT_morph.
apply H; trivial.
red; intros.
apply sSAT_morph.
rewrite H2; reflexivity.
Qed.
Hint Resolve tiSAT_ext1.

Instance tiSAT_morph F A :
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  Proper (eq_set ==> eq_set ==> eqSAT) (tiSAT F A).
do 3 red; intros.
unfold tiSAT.
apply sSAT_morph.
apply cc_app_morph; trivial.
apply REC_morph; trivial.
do 3 red; intros.
apply cc_lam_ext; auto with *.
 rewrite H2; reflexivity.

 red; intros.
 apply iSAT_morph.
 apply H; trivial.
 red; intros.
 rewrite H3; rewrite H6; reflexivity.
Qed.

Lemma tiSAT_recursor o A F :
  Proper (incl_set==>incl_set) F ->
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  (forall R R' o', isOrd o' -> o' ⊆ o -> (forall x x', x ∈ TI F o' -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o ->
  recursor o (TI F)
    (fun o f => forall x, x∈TI F o -> cc_app f x == iSAT(sSAT(cc_app f x)))
    (fun o' f => cc_lam (TI F (osucc o')) (fun y => iSAT (A (fun z => sSAT (cc_app f z)) y))).
intros Fm Am Aext oo.
split; intros.
 apply TI_morph.

 apply TI_mono_eq; trivial.

 red in H2.
 rewrite <- H1 in H4.
 rewrite <- H2; auto.

 apply TI_elim in H3; auto.
 destruct H3.
 rewrite <- TI_mono_succ in H4; trivial.
 2:apply isOrd_inv with o0; trivial.
 eauto.

 do 3 red; intros.
 apply cc_lam_ext.
  rewrite H; reflexivity.

  red; intros.
  apply iSAT_morph.
  apply Am; trivial.
  red; intros.
  rewrite H0; rewrite H3; reflexivity.

 split; intros.
  apply is_cc_fun_lam; auto.

  rewrite cc_beta_eq; auto.
  rewrite iSAT_id; reflexivity.

 red; red; intros.
 rewrite cc_beta_eq; auto.
 rewrite cc_beta_eq; auto.
  apply iSAT_morph.
  apply Aext with o0; auto with *.
   apply H1.
   transitivity o'; trivial.
  intros.
  apply sSAT_morph.
  rewrite <- H6.
  apply H3; trivial.

  revert H4; apply TI_mono; auto with *.
   apply isOrd_succ; apply H2.
   apply isOrd_succ; apply H1.
   apply osucc_mono; trivial.
    apply H1.
    apply H2.
Qed.


Lemma tiSAT_eq o A F :
  Proper (incl_set==>incl_set) F ->
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  (forall R R' o', isOrd o' -> o' ⊆ o -> (forall x x', x ∈ TI F o' -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o ->
  forall x,
  x ∈ TI F o ->
  eqSAT (tiSAT F A o x) (A (tiSAT F A o) x).
intros.
unfold tiSAT.
specialize tiSAT_recursor with (1:=H) (2:=H0) (3:=H1) (4:=H2); intro rec.
rewrite REC_expand with (1:=H2) (2:=rec) (3:=H3).
rewrite cc_beta_eq.
 rewrite iSAT_id.
 reflexivity.

 do 2 red; intros.
 apply iSAT_morph.
 apply H0; trivial.
 red; intros.
 apply sSAT_morph.
 apply cc_app_morph; trivial.
 reflexivity.

 revert H3; apply TI_incl; auto.
Qed.


Lemma tiSAT_outside_domain o A F S :
  Proper (incl_set==>incl_set) F ->
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  (forall R R' o', isOrd o' -> o' ⊆ o -> (forall x x', x ∈ TI F o' -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o ->
  forall x,
  ~ x ∈ TI F o ->
  inclSAT (tiSAT F A o x) S.
intros.
specialize tiSAT_recursor with (1:=H) (2:=H0) (3:=H1) (4:=H2); intro rec.
unfold tiSAT.
red; intros.
rewrite REC_eqn with (2:=rec) in H4; trivial.
fold (tiSAT F A o) in H4.
rewrite cc_app_outside_domain with (dom:=TI F o) in H4; trivial.
2:apply is_cc_fun_lam.
2:do 2 red; intros; apply cc_app_morph; auto with *.
unfold sSAT,complSAT in H4.
assert (H4' := fun h => interSAT_elim H4 (exist _ S h)); clear H4; simpl in H4'.
apply H4'; intros.
apply empty_ax in H5; contradiction.
Qed.


Lemma tiSAT_mono o1 o2 A F:
  Proper (incl_set==>incl_set) F ->
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  (forall R R' o', isOrd o' -> o' ⊆ o2 -> (forall x x', x ∈ TI F o' -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o1 ->
  isOrd o2 ->
  o1 ⊆ o2 ->
  forall x,
  x ∈ TI F o1 ->
  eqSAT (tiSAT F A o1 x) (tiSAT F A o2 x).
intros.
specialize tiSAT_recursor with (1:=H) (2:=H0) (3:=H1) (4:=H3); intro rec.
unfold tiSAT at 2.
rewrite <- REC_ord_irrel with (2:=rec) (o:=o1); auto with *.
reflexivity.
Qed.

Lemma tiSAT_succ_eq o A F :
  Proper (incl_set==>incl_set) F ->
  Proper ((eq_set==>eqSAT)==>eq_set==>eqSAT) A ->
  (forall R R' o', isOrd o' -> o' ⊆ osucc o -> (forall x x', x ∈ TI F o' -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o ->
  forall x,
  x ∈ TI F (osucc o) ->
  eqSAT (tiSAT F A (osucc o) x) (A (tiSAT F A o) x).
intros.
rewrite tiSAT_eq; auto.
apply H1 with o; auto with *.
 red; intros; apply isOrd_trans with o; auto.
intros.
transitivity (tiSAT F A o x0).
 symmetry; apply tiSAT_mono; auto with *.
 red; intros; apply isOrd_trans with o; auto.

 apply tiSAT_morph; auto with *.
Qed.

(* useful ?
Lemma FIXP_TI_sat G o F A m X :
  let FIX_ty o := piSAT0 (fun n => n ∈ TI F o) (tiSAT F A o) (X o) in
  Proper (incl_set ==> incl_set) F ->
  Proper ((eq_set ==> eqSAT) ==> eq_set ==> eqSAT) A ->
  (forall R R' o', isOrd o' -> o' ⊆ o -> (forall x x', x ∈ TI F o' -> x==x' -> eqSAT (R x) (R' x')) ->
   forall x x', x ∈ TI F (osucc o') -> x==x' -> eqSAT (A R x) (A R' x')) ->
  isOrd o ->
  (forall m, sn m -> sn (App G m)) ->
  (forall o x t m (X:SAT), isOrd o -> x ∈ TI F o ->
   inSAT t (tiSAT F A o x) ->
   inSAT (App2 m m t) X ->
   inSAT (App2 G m t) X) ->
  (forall y y' n, isOrd y -> isOrd y' -> y ⊆ y' -> y' ⊆ o -> n ∈ TI F y ->
   inclSAT (X y n) (X y' n)) ->
  inSAT m (piSAT0 (fun o' => o' ∈ osucc o)
             (fun o1 => FIX_ty o1) (fun o1 => FIX_ty (osucc o1))) ->
  inSAT (FIXP G m) (FIX_ty o).
intros.
apply FIXP_sat; trivial.
 intros.
 apply TI_elim in H9; auto.
 destruct H9 as (o',?,?); exists o'; trivial.
 rewrite TI_mono_succ; eauto using isOrd_inv.

 intros.
 apply tiSAT_mono; trivial.
 intros.
 apply H1 with (o':=o'); trivial.
 transitivity y'; trivial.
Qed.

*)