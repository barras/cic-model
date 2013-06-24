Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFord ZFfix ZFstable.
Require Import ZFgrothendieck ZFcoc.
Require Import ZFlist.
Import ZFrepl.

(** In this file we develop the theory of W-types in Prop:
    - typing
    - existence of a fixpoint
    - recursor
 *)

Section W_Prop_theory.

(** * Definition and properties of the W-type operator *)

Variable A : set.
Variable B : set -> set.
Hypothesis Bext : ext_fun A B.

(* The intended type operator *)
Definition W_F X := sup A (fun x => cc_arr (B x) X).

Lemma wfm1 : forall X, ext_fun A (fun x => cc_arr (B x) X).
do 2 red; intros.
apply cc_arr_morph; auto with *.
Qed.
Hint Resolve wfm1.

Lemma W_F_intro X a f :
  ext_fun (B a) f ->
  a ∈ A ->
  (forall i, i ∈ B a -> f i ∈ X) ->
  cc_lam (B a) f ∈ W_F X.
intros.
unfold W_F; rewrite sup_ax; auto.
exists a; trivial.
apply cc_arr_intro; intros; auto with *.
Qed.

Lemma W_F_elim X x :
  x ∈ W_F X ->
  exists2 w, w ∈ A &
  (forall i, i ∈ B w -> cc_app x i ∈ X) /\
  x == cc_lam (B w) (cc_app x). 
intros.
unfold W_F in H; rewrite sup_ax in H; auto.
destruct H as (w,?,?); exists w; trivial.
split; intros.
 apply cc_arr_elim with (1:=H0); trivial.

 apply cc_eta_eq in H0; trivial.
Qed.

Instance W_F_mono : Proper (incl_set ==> incl_set) W_F.
do 3 red; intros.
apply W_F_elim in H0; destruct H0 as (w,?,(?,?)).
rewrite H2.
apply W_F_intro; auto.
do 2 red; intros; apply cc_app_morph; auto with *.
Qed.

Instance W_F_morph : morph1 W_F.
apply Fmono_morph; auto with *.
Qed.

(* W_F not stable! *)


Lemma W_F_bound : W_F (singl empty) ⊆ singl empty.
red; intros.
apply W_F_elim in H.
destruct H as (w,?,(?,?)).
rewrite H1.
apply singl_intro_eq.
apply cc_impredicative_lam.
 do 2 red; intros; apply cc_app_morph; auto with *.

 intros.
 apply singl_elim; auto.
Qed.

Lemma W_F_typ X : X ⊆ singl empty -> W_F X ⊆ singl empty.
intros.
transitivity (W_F (singl empty)).
 apply W_F_mono; trivial.

 apply W_F_bound.
Qed.

  Definition W := FIX (singl empty) W_F.

  Lemma W_typ : W ∈ props.
apply power_intro.
change (W ⊆ singl prf_trm).
apply lfp_typ.
apply W_F_typ.
Qed.

  Lemma W_eqn : W == W_F W.
symmetry; apply FIX_eqn.
 apply W_F_mono.

 apply W_F_typ.
Qed.

  Definition Wi := TI W_F.

  Lemma Wi_mono o o' : isOrd o -> isOrd o' -> o ⊆ o' -> Wi o ⊆ Wi o'.
intros.
apply TI_mono; trivial.
apply W_F_mono.
Qed.

  Lemma Wi_W o : isOrd o -> Wi o ⊆ W.
intros.
apply TI_FIX; trivial.
 apply W_F_mono.
 apply W_F_typ.
Qed.

  Lemma W_case (P:set->Prop) :
    Proper (eq_set ==> iff) P ->
    (forall x f, x ∈ A ->
     f ∈ cc_arr (B x) W ->
     P f) ->
    forall a, a ∈ W -> P a.
intros.
cut (a ∈ subset W P).
 intros.
 rewrite subset_ax in H2; destruct H2 as (_,(a',?,?)).
 rewrite H2; trivial.
revert a H1.
apply lower_bound.
unfold M'.
apply subset_intro.
 apply power_intro; intros.
 apply subset_elim1 in H1.
 apply power_elim with (2:=H1).
 apply W_typ.

 do 2 red; intros.
 apply subset_intro.
  rewrite W_eqn.
  revert H1; apply W_F_mono.
  red; intros.
  apply subset_elim1 in H1; trivial.

  apply W_F_elim in H1.
  destruct H1 as (w,?,(?,?)).
  rewrite H3; apply H0 with w; trivial.
  apply cc_arr_intro; intros.
   do 2 red; intros; apply cc_app_morph; auto with *.

   specialize H2 with (1:=H4).
   apply subset_elim1 in H2; trivial.
Qed.

  Lemma Wi_case o (P:set->Prop) :
    isOrd o ->
    Proper (eq_set ==> iff) P ->
    (forall x f, x ∈ A ->
     f ∈ cc_arr (B x) (Wi o) ->
     P f) ->
    forall a, a ∈ Wi (osucc o) -> P a.
intros.
unfold Wi in H2; rewrite TI_mono_succ in H2; auto.
2:apply W_F_mono.
apply W_F_elim in H2.
destruct H2 as (w,?,(?,?)).
apply H1 with w; trivial.
rewrite H4; apply cc_arr_intro; intros; auto.
do 2 red; intros; apply cc_app_morph; auto with *.
Qed. 


  Lemma Wi_ind o (P:set->Prop) :
    isOrd o ->
    Proper (eq_set==>iff) P ->
    (forall o', isOrd o' -> o' ⊆ o ->
     (forall a, a ∈ Wi o' -> P a) ->
     (forall a, a ∈ Wi (osucc o') -> P a)) ->
    forall a, a ∈ Wi o -> P a.
intros oo Pm Hrec.
apply isOrd_ind with (2:=oo); intros.
apply TI_elim in H2; auto with *.
destruct H2 as (o',?,?).
apply Hrec with o'.
 apply isOrd_inv with y; trivial.

 transitivity y; trivial.
 red; intros; apply isOrd_trans with o'; trivial.

 intros.
 apply H1 with o'; trivial.

 unfold Wi; rewrite TI_mono_succ; auto with *.
 apply isOrd_inv with y; trivial.
Qed.

  Lemma W_ind (P:set->Prop) :
    Proper (eq_set==>iff) P ->
    (forall X, X ⊆ W ->
     (forall a, a ∈ X -> P a) ->
     (forall a, a ∈ W_F X -> P a)) ->
    forall a, a ∈ W -> P a.
intros.
cut (a ∈ subset W P).
 intros.
 apply subset_elim2 in H2.
 destruct H2 as (a',eqa,?).
 rewrite eqa; trivial.
revert a H1; apply lower_bound.
unfold M'.
apply subset_intro.
 apply power_intro; intros.
 apply subset_elim1 in H1.
 apply power_elim with (1:=W_typ); trivial.

 do 2 red; intros.
 apply subset_intro.
  rewrite W_eqn.
  revert H1; apply W_F_mono.
  red; intros.
  apply subset_elim1 in H1; trivial.

  apply H0 with (subset W P); trivial.
   red; intros.
   apply subset_elim1 in H2; trivial.

   intros.
   apply subset_elim2 in H2.
   destruct H2 as (a',eqa,?).
   rewrite eqa; trivial.
Qed.

Section WindColl.

Hypothesis coll_ax :
  forall A (R:set->set->Prop), 
  Proper (eq_set ==> eq_set ==> iff) R ->
  exists B, forall x, x ∈ A ->
         (exists y, R x y) -> exists2 y, y ∈ B & R x y.

  Lemma same_fix :
    W == Ffix W_F (singl zero).
assert (Ffix W_F (singl zero) == W_F (Ffix W_F (singl zero))).
 apply Ffix_fix_coll; trivial.
  apply W_F_mono.

  apply W_F_typ.
apply incl_eq.
 apply lower_bound.
 apply subset_intro.
  apply power_intro; intros.
  apply Ffix_inA in H0; trivial.

  red; intros.
  rewrite <- H; reflexivity.

 red; intros.
 rewrite Ffix_def in H0.
 2:apply W_F_mono.
 2:apply W_F_typ.
 destruct H0.
 revert H1; apply TI_FIX; trivial.
 apply W_F_mono.
 apply W_F_typ.
Qed.

  Lemma W_ind_coll (P:set->Prop) :
    Proper (eq_set ==> iff) P ->
    (forall o, isOrd o ->
     (forall a, a ∈ Wi o -> P a) ->
     (forall a, a ∈ Wi (osucc o) -> P a)) ->
    forall a, a ∈ W -> P a.
intros.
rewrite same_fix in H1.
destruct Ffix_fix_coll_stage with (1:=W_F_mono) (2:=W_F_typ); trivial.
apply H3 in H1.
apply Wi_ind with (o:=x); trivial.
intros.
apply H0 with (o:=o'); trivial.
Qed.

End WindColl.

(** Recursor on W *)

Require Import ZFfunext ZFfixrec.

Section Recursor.

  Hint Resolve W_F_mono.

  Lemma Wi_fix :
    forall (P:set->Prop) o,
    isOrd o ->
    (forall i, isOrd i -> i ⊆ o ->
     (forall i' m, lt i' i -> m ∈ TI W_F i' -> P m) ->
     forall n, n ∈ TI W_F i -> P n) ->
    forall n, n ∈ TI W_F o -> P n.
intros P o is_ord Prec.
induction is_ord using isOrd_ind; intros; eauto.
Qed.

  Variable ord : set.
  Hypothesis oord : isOrd ord.

  Variable F : set -> set -> set.
  Hypothesis Fm : morph2 F.

  Variable U : set -> set -> set.
  Hypothesis Umono : forall o o' x x',
    isOrd o' -> o' ⊆ ord -> isOrd o -> o ⊆ o' ->
    x ∈ TI W_F o -> x == x' ->
    U o x ⊆ U o' x'.

  Let Ty o := cc_prod (TI W_F o) (U o).
  Hypothesis Ftyp : forall o f, isOrd o -> o ⊆ ord ->
    f ∈ Ty o -> F o f ∈ Ty (osucc o).

  Let Q o f := forall x, x ∈ TI W_F o -> cc_app f x ∈ U o x.

  Definition Wi_ord_irrel :=
    forall o o' f g,
    isOrd o' -> o' ⊆ ord -> isOrd o -> o ⊆ o' ->
    f ∈ Ty o -> g ∈ Ty o' ->
    fcompat (TI W_F o) f g ->
    fcompat (TI W_F (osucc o)) (F o f) (F o' g).

  Hypothesis Firrel : Wi_ord_irrel.

  Definition WREC := REC F.

Lemma Umorph : forall o o', isOrd o' -> o' ⊆ ord -> o == o' ->
    forall x x', x ∈ TI W_F o -> x == x' -> U o x == U o' x'. 
intros.
apply incl_eq.
 apply Umono; auto.
  rewrite H1; trivial.
  rewrite H1; reflexivity.

 apply Umono; auto.
  rewrite H1; trivial.
  rewrite H1; trivial.
  rewrite H1; reflexivity.
  rewrite <- H3; rewrite <- H1; trivial.
  symmetry; trivial.
Qed.

Lemma Uext : forall o, isOrd o -> o ⊆ ord -> ext_fun (TI W_F o) (U o).
red; red; intros.
apply Umorph; auto with *.
Qed.


  Lemma WREC_typing : forall o f, isOrd o -> o ⊆ ord -> 
    is_cc_fun (TI W_F o) f -> Q o f -> f ∈ Ty o.
intros.
rewrite cc_eta_eq' with (1:=H1).
apply cc_prod_intro; intros; auto.
 do 2 red; intros.
 rewrite H4; reflexivity.

 apply Uext; trivial.
Qed.


Let Wi_cont : forall o,
   isOrd o -> TI W_F o == sup o (fun o' => TI W_F (osucc o')).
apply TI_mono_eq; trivial.
Qed.

Let Qm :
   forall o o',
   isOrd o ->
   o ⊆ ord ->
   o == o' -> forall f f', fcompat (TI W_F o) f f' -> Q o f -> Q o' f'.
intros.
unfold Q in H3|-*; intros.
rewrite <- H1 in H4.
specialize H3 with (1:=H4).
red in H2; rewrite <- H2; trivial.
revert H3; apply Umono; auto with *.
 rewrite <- H1; trivial.
 rewrite <- H1; trivial.
 rewrite <- H1; reflexivity.
Qed.

Let Qcont : forall o f : set,
 isOrd o ->
 o ⊆ ord ->
 is_cc_fun (TI W_F o) f ->
 (forall o' : set, o' ∈ o -> Q (osucc o') f) -> Q o f.
intros.
red; intros.
apply TI_elim in H3; auto with *.
destruct H3.
rewrite <- TI_mono_succ in H4; eauto using isOrd_inv.
generalize (H2 _ H3 _ H4).
apply Umono; eauto using isOrd_inv with *.
red; intros.
apply isOrd_plump with x0; eauto using isOrd_inv.
apply olts_le in H5; trivial.
Qed.

Let Qtyp : forall o f,
 isOrd o ->
 o ⊆ ord ->
 is_cc_fun (TI W_F o) f ->
 Q o f -> is_cc_fun (TI W_F (osucc o)) (F o f) /\ Q (osucc o) (F o f).
intros.
assert (F o f ∈ Ty (osucc o)).
 apply Ftyp; trivial.
 apply WREC_typing; trivial.
split.
 apply cc_prod_is_cc_fun in H3; trivial.

 red; intros.
 apply cc_prod_elim with (1:=H3); trivial.
Qed.

  Lemma Firrel_W : stage_irrelevance ord (TI W_F) Q F.
red; red; intros.
destruct H1 as (oo,(ofun,oty)); destruct H2 as (o'o,(o'fun,o'ty)).
apply Firrel; trivial.
 apply WREC_typing; trivial. 
 transitivity o'; trivial.

 apply WREC_typing; trivial. 
Qed.

  Lemma WREC_recursor : recursor ord (TI W_F) Q F.
split; auto.
 apply TI_morph.

 apply Firrel_W.
Qed.
Hint Resolve WREC_recursor.

  (* Main properties of WREC: typing and equation *)
  Lemma WREC_wt : WREC ord ∈ Ty ord.
intros.
apply WREC_typing; auto with *.
 apply REC_wt with (1:=oord) (2:=WREC_recursor).
 apply REC_wt with (1:=oord) (2:=WREC_recursor).
Qed.

  Lemma WREC_ind : forall P x,
    Proper (eq_set==>eq_set==>eq_set==>iff) P ->
    (forall o x, isOrd o -> lt o ord ->
     x ∈ W_F (TI W_F o) ->
     (forall y, y ∈ TI W_F o -> P o y (cc_app (WREC ord) y)) ->
     forall w, isOrd w -> w ⊆ ord -> lt o w ->
     P w x (cc_app (F ord (WREC ord)) x)) ->
    x ∈ TI W_F ord ->
    P ord x (cc_app (WREC ord) x).
intros.
unfold WREC.
apply REC_ind with (2:=WREC_recursor); auto.
intros.
apply TI_elim in H4; auto with *.
destruct H4 as (o',?,?).
apply H0 with o'; eauto using isOrd_inv.
red; auto.
Qed.

  Lemma WREC_expand : forall n,
    n ∈ TI W_F ord -> cc_app (WREC ord) n == cc_app (F ord (WREC ord)) n.
intros.
apply REC_expand with (2:=WREC_recursor) (Q:=Q); auto.
Qed.

  Lemma WREC_irrel o o' :
    isOrd o ->
    isOrd o' ->
    o ⊆ o' ->
    o' ⊆ ord ->
    eq_fun (TI W_F o) (cc_app (WREC o)) (cc_app (WREC o')).
red; intros.
rewrite <- H4.
apply REC_ord_irrel with (2:=WREC_recursor); auto with *.
Qed.

End Recursor.


End W_Prop_theory.
