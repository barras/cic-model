Require Import ZF ZFpairs ZFsum ZFrelations ZFcoc ZFord ZFfix.
Require Import ZFstable ZFiso ZFind_w.

(** Here we define the (semantic) notion of strictly positiveness.
   We then show that it fulfills all the requirements for the existence
   of a fixpoint:
   - monotonicity
   - isomorphism with a W-type
 *)

(* Qu: does this notion of strict positivity is powerful enough to build a model
   of IZF?
   - partial answer: if we are in ZF + one Grothendieck universe (i.e. closed by
     collection), then the fixpoint of (fun X -> sigma U (fun Y => cc_arr Y X))
     is the type Ens.set, and since we have a skolemized collection, we can
     prove that this W-type can interpret ZF theory.  *)


(** * General properties of "strictly positive" inductive definitions *)

Record positive := mkPositive {
  pos_oper : set -> set ;
  w1 : set;
  w2 : set->set;
  wf : set -> set
}.

Definition eqpos p1 p2 :=
  (eq_set==>eq_set)%signature (pos_oper p1) (pos_oper p2) /\
  w1 p1 == w1 p2 /\
  (eq_set==>eq_set)%signature (w2 p1) (w2 p2) /\
  (eq_set==>eq_set)%signature (wf p1) (wf p2).

Instance eqpos_sym : Symmetric eqpos.
red; intros.
destruct H as (?,(?,(?,?))); split; [|split;[|split]]; symmetry; trivial.
Qed.
  
Instance eqpos_trans : Transitive eqpos.
red; intros.
destruct H as (?,(?,(?,?))); destruct H0 as (?,(?,(?,?))).
split; [|split;[|split]]; eapply transitivity; eauto.
Qed.

Record isPositive (p:positive) := {
  pos_mono : Proper (incl_set ==> incl_set) (pos_oper p);
  w2m : ext_fun (w1 p) (w2 p);
  w_iso : forall X, iso_fun (pos_oper p X) (W_F (w1 p) (w2 p) X) (wf p)
}.

Instance pos_oper_morph : Proper (eqpos==>eq_set==>eq_set) pos_oper.
do 3 red; intros.
apply H; trivial.
Qed.
Instance w1_morph : Proper (eqpos==>eq_set) w1.
do 2 red; intros.
apply H; trivial.
Qed.
Instance w2_morph : Proper (eqpos==>eq_set==>eq_set) w2.
do 3 red; intros.
apply H; trivial.
Qed.
Instance wf_morph : Proper (eqpos==>eq_set==>eq_set) wf.
do 3 red; intros.
apply H; trivial.
Qed.

(* pos_oper is stable by isomorphism with W_F *)
Lemma pos_oper_stable : forall p, isPositive p ->
  stable (pos_oper p).
intros.
red; red; intros.
assert (WFm : ext_fun X (W_F (w1 p) (w2 p))).
 do 2 red; intros; apply W_F_ext; auto with *.
 apply H.
assert (posm : morph1 (pos_oper p)).
 do 2 red; intros.
 apply (Fmono_morph _ (pos_mono p H)); trivial.
assert (posm' : ext_fun X (pos_oper p)).
 do 2 red; intros; apply posm; trivial.
destruct inter_wit with (2:=H0) as (w,?); trivial.
apply iso_fun_narrow with
 (1:=w_iso _ H (inter X)) (2:=w_iso _ H w).
 apply pos_mono; trivial.
 red; intros.
 apply inter_elim with (1:=H2); trivial.

 apply inter_elim with (1:=H0).
 rewrite replf_ax; eauto with *.

 apply W_F_stable;[apply H|].
 apply inter_intro; intros.
 rewrite replf_ax in H2; trivial.
 destruct H2.
 rewrite H3.
 apply (iso_typ (w_iso _ H x)).
 apply inter_elim with (1:=H0).
 rewrite replf_ax; eauto with *.

 econstructor; rewrite replf_ax; eauto with *.
Qed.


(****************************************************)
(** General properties of positive definitions (independent of convergence) *)

  Definition INDi p o :=
    TI (pos_oper p) o.

  Instance INDi_morph_gen : Proper (eqpos ==> eq_set ==> eq_set) INDi.
do 3 red; intros.
unfold INDi.
apply TR_morph; trivial.
do 2 red; intros.
apply sup_morph; trivial.
red; intros.
apply pos_oper_morph; auto.
Qed.

  Instance INDi_morph p : isPositive p -> morph1 (INDi p).
do 2 red; intros.
unfold INDi.
apply TR_morph; trivial.
do 2 red; intros.
apply sup_morph; trivial.
red; intros.
apply Fmono_morph;auto.
apply H.
Qed.

  Lemma INDi_succ_eq : forall p o,
    isPositive p -> isOrd o -> INDi p (osucc o) == pos_oper p (INDi p o).
unfold INDi; intros.
apply TI_mono_succ; auto with *.
apply H.
Qed.

  Lemma INDi_stable : forall p, isPositive p -> stable_ord (INDi p).
unfold INDi; intros.
apply TI_stable.
 apply H.
 apply pos_oper_stable; trivial.
Qed.

  Lemma INDi_mono : forall p o o',
    isPositive p -> isOrd o -> isOrd o' -> o \incl o' ->
    INDi p o \incl INDi p o'.
intros.
apply TI_mono; auto with *.
apply H.
Qed.

(** * Convergence *)

Section InductiveFixpoint.

  Variable p : positive.
  Hypothesis p_ok : isPositive p.

  Let Wpf := pos_oper p.
  Let Wp := W (w1 p) (w2 p).
  Let Wff := Wf (w1 p) (w2 p).

  Let Wd := Wdom (w1 p) (w2 p).

  Let Bext : ext_fun (w1 p) (w2 p).
apply p_ok.
Qed.
  Let Wff_mono : Proper (incl_set ==> incl_set) Wff.
apply Wf_mono; trivial.
Qed.
  Let Wff_typ : forall X, X \incl Wd -> Wff X \incl Wd.
intros.
apply Wf_typ; trivial.
Qed.

  (** The closure ordinal *)
  Definition IND_clos_ord := W_ord (w1 p) (w2 p).
  Definition IND := INDi p IND_clos_ord.


  Let WFf := W_F (w1 p) (w2 p).
  Let Wp2 := W2 (w1 p) (w2 p).

Definition wf' f := comp_iso (wf p) (WFmap (w2 p) f).

Lemma wf'iso X Y f :
  iso_fun X Y f ->
  iso_fun (pos_oper p X) (WFf Y) (wf' f).
intros isof.
unfold wf'.
apply iso_fun_trans with (1:=w_iso _ p_ok X).
apply WFmap_iso; trivial.
Qed.

  Lemma IND_eq : IND == pos_oper p IND.
pose (isow := TI_iso (pos_oper p) wf' IND_clos_ord).
destruct TI_iso_fun with 
  (F:=pos_oper p) (G:=WFf) (g:=wf') (o:=IND_clos_ord) as
 (isof, expTI); intros.
 apply p_ok.

 apply W_F_mono; trivial.

 red; intros; unfold wf', comp_iso.
 apply WFmap_morph with (1:=Bext) (X:=X); trivial.
  apply (iso_typ (w_iso _ p_ok X)); trivial.
  apply (iso_funm (w_iso _ p_ok X)); trivial.

 apply wf'iso; trivial.

 apply W_o_o; trivial.
fold isow in expTI, isof.
apply iso_fun_inj with Wp2 (wf' isow).
 generalize isof; apply iso_fun_morph; try reflexivity.
 red; intros.
 rewrite <- expTI.
  apply (iso_funm isof); trivial.
  rewrite <- H0; trivial.

 apply iso_change_rhs with (1:=symmetry (W2_eqn _ _ Bext)).
 apply wf'iso; trivial.

 unfold IND, INDi; red; intros.
 rewrite <- TI_mono_succ; auto with *.
 2:apply p_ok; trivial.
 2:apply W_o_o; trivial.  
 revert H; apply TI_incl.
  apply p_ok; trivial.
  apply isOrd_succ; apply W_o_o; trivial.
  apply lt_osucc; apply W_o_o; trivial.
Qed.

  Lemma INDi_IND : forall o,
    isOrd o ->
    INDi p o \incl IND.
induction 1 using isOrd_ind; intros.
unfold INDi.
rewrite TI_eq; auto.
2:apply Fmono_morph; apply p_ok.
red; intros.
rewrite sup_ax in H2; auto.
 destruct H2.
 rewrite IND_eq.
 revert H3; apply p_ok; auto.
 apply H1; trivial.

 do 2 red; intros; apply Fmono_morph; auto.
  apply p_ok; auto.
  apply TI_morph; trivial.
Qed.

End InductiveFixpoint.

(** * A library of positive operators *)

(** A library of positive operators that generate all inductive types:
   - constant
   - recursive subterm
   - sum
   - prodcart
   - sigma
   - cc_prod
   - nested...
 *)

(** Non-recursive arguments *)
Definition trad_cst :=
  sigma_1r_iso (fun _ => cc_lam empty (fun _ => empty)).

Lemma iso_cst : forall A X,
  iso_fun A (W_F A (fun _ => empty) X) trad_cst.
intros.
unfold trad_cst, W_F.
apply sigma_iso_fun_1_r'; intros; auto with *.
apply cc_prod_iso_fun_0_l'.
Qed.

Definition pos_cst A :=
  mkPositive (fun _ => A) A (fun _ => empty) trad_cst.

Lemma isPos_cst A : isPositive (pos_cst A).
unfold pos_cst; constructor; simpl.
 do 3 red; auto.

 do 2 red; reflexivity.

 intros; apply iso_cst.
Qed.

(** Recursive subterm *)

Definition trad_reccall :=
  comp_iso (fun x => cc_lam (singl empty) (fun _ => x)) (couple empty).

Lemma iso_reccall : forall X,
  iso_fun X (W_F (singl empty) (fun _ => singl empty) X) trad_reccall.
intros.
unfold trad_reccall, W_F.
eapply iso_fun_trans.
 apply cc_prod_iso_fun_1_l' with (F:=fun _ => X); reflexivity.

 apply sigma_iso_fun_1_l' with (F:=fun _ => _).
 do 2 red; reflexivity.
Qed.

Definition pos_rec :=
  mkPositive (fun X => X) (singl empty) (fun _ => singl empty) trad_reccall.

Lemma isPos_rec : isPositive pos_rec.
unfold pos_rec; constructor; simpl.
 do 3 red; auto.

 do 2 red; auto with *.

 intros; apply iso_reccall.
Qed.

(** Disjoint sum *)

Definition trad_sum f g :=
  comp_iso (sum_isomap f g) sum_sigma_iso.

Lemma cc_prod_sum_case_commut A1 A2 B1 B2 Y x x':
  ext_fun A1 B1 ->
  ext_fun A2 B2 ->
  x \in sum A1 A2 ->
  x == x' ->
  sum_case (fun x => cc_arr (B1 x) Y) (fun x => cc_arr (B2 x) Y) x ==
  cc_arr (sum_case B1 B2 x') Y.
intros.
apply sum_ind with (3:=H1); intros.
 rewrite sum_case_inl0; eauto.
 apply cc_arr_morph;[|reflexivity].
 rewrite sum_case_inl0.
  apply H.
   rewrite H4; rewrite dest_sum_inl; trivial.
   apply dest_sum_morph; trivial.
  exists x0; rewrite <- H2; trivial.

 rewrite sum_case_inr0; eauto.
 apply cc_arr_morph;[|reflexivity].
 rewrite sum_case_inr0.
  apply H0.
   rewrite H4; rewrite dest_sum_inr; trivial.
   apply dest_sum_morph; trivial.
  exists y; rewrite <- H2; trivial.
Qed.

Lemma W_F_sum_commut A1 A2 B1 B2 X:
  ext_fun A1 B1 ->
  ext_fun A2 B2 ->
  sigma (sum A1 A2)
    (sum_case (fun x => cc_arr (B1 x) X) (fun x => cc_arr (B2 x) X)) ==
  W_F (sum A1 A2) (sum_case B1 B2) X.
unfold W_F; intros.
apply sigma_ext; intros; auto with *.
apply cc_prod_sum_case_commut with (1:=H) (2:=H0); auto with *.
Qed.

Lemma iso_sum : forall X1 X2 A1 A2 B1 B2 Y f g,
  ext_fun A1 B1 ->
  ext_fun A2 B2 ->
  iso_fun X1 (W_F A1 B1 Y) f ->
  iso_fun X2 (W_F A2 B2 Y) g ->
  iso_fun (sum X1 X2) (W_F (sum A1 A2) (sum_case B1 B2) Y) (trad_sum f g).
intros.
unfold W_F, trad_sum.
eapply iso_fun_trans.
 apply sum_iso_fun_morph;[apply H1|apply H2].

 eapply iso_change_rhs.
 2:apply iso_fun_sum_sigma; auto.
 apply W_F_sum_commut; trivial.
Qed.

Definition pos_sum F G :=
  mkPositive (fun X => sum (pos_oper F X) (pos_oper G X))
    (sum (w1 F) (w1 G)) (sum_case (w2 F) (w2 G)) (trad_sum (wf F) (wf G)).

Lemma isPos_sum F G :
  isPositive F ->
  isPositive G ->
  isPositive (pos_sum F G).
unfold pos_sum; constructor; simpl.
 do 2 red; intros.
 apply sum_mono; apply pos_mono; trivial.

 red; intros; apply sum_case_ext; apply w2m; trivial.

 intros.
 apply iso_sum; auto using w2m, w_iso.
Qed.

(** Concatenating recursive argument *)

Definition trad_prodcart B1 B2 f g :=
  comp_iso (sigma_isomap f (fun _ => g))
  (comp_iso prodcart_sigma_iso
           (sigma_isomap (fun x => x)
              (fun x => prodcart_cc_prod_iso (sum (B1 (fst x)) (B2 (snd x)))))).

Lemma iso_prodcart : forall X1 X2 A1 A2 B1 B2 Y f g,
   ext_fun A1 B1 ->
   ext_fun A2 B2 ->
   iso_fun X1 (W_F A1 B1 Y) f ->
   iso_fun X2 (W_F A2 B2 Y) g ->
   iso_fun (prodcart X1 X2)
     (W_F (prodcart A1 A2) (fun i => sum (B1 (fst i)) (B2 (snd i))) Y)
     (trad_prodcart B1 B2 f g).
intros.
unfold W_F, trad_prodcart.
eapply iso_fun_trans.
 apply prodcart_iso_fun_morph; [apply H1|apply H2].
assert (m1 : ext_fun A1 (fun x => cc_arr (B1 x) Y)) by auto.
assert (m1' : ext_fun A2 (fun x => cc_arr (B2 x) Y)) by auto.
assert (m2: ext_fun (prodcart A1 A2) (fun x => sum (B1 (fst x)) (B2 (snd x)))).
 do 2 red; intros.
 apply sum_morph.
  apply H.
   apply fst_typ in H3; trivial.
   apply fst_morph; trivial.
  apply H0.
   apply snd_typ in H3; trivial.
   apply snd_morph; trivial.
eapply iso_fun_trans.
 apply iso_fun_prodcart_sigma; auto.

 apply sigma_iso_fun_morph; auto.
  do 2 red; intros.
  apply prodcart_morph.
   apply m1.
    apply fst_typ in H3; trivial.
    apply fst_morph; trivial.
   apply m1'.
    apply snd_typ in H3; trivial.
    apply snd_morph; trivial.

  red; intros.
  apply prodcart_cc_prod_iso_morph; auto with *.

  apply id_iso_fun.

  intros.
  eapply iso_change_rhs.
  2:apply iso_fun_prodcart_cc_prod; auto.
  apply cc_prod_ext; auto.
  red; intros.
  apply sum_case_ind with (6:=H5); auto with *.
   do 2 red; intros.
   rewrite H7; reflexivity.

   do 2 red; reflexivity.
   do 2 red; reflexivity.
Qed.

Definition pos_consrec F G :=
  mkPositive (fun X => prodcart (pos_oper F X) (pos_oper G X))
    (prodcart (w1 F) (w1 G))
    (fun c => sum (w2 F (fst c)) (w2 G (snd c)))
    (trad_prodcart (w2 F) (w2 G) (wf F) (wf G)).

Lemma isPos_consrec F G :
  isPositive F ->
  isPositive G ->
  isPositive (pos_consrec F G). 
intros.
unfold pos_consrec; constructor; simpl.
 do 2 red; intros; apply prodcart_mono; apply pos_mono; trivial.

 do 2 red; intros; apply sum_morph; apply w2m; trivial.
  apply fst_typ in H1; trivial.
  apply fst_morph; trivial.
  apply snd_typ in H1; trivial.
  apply snd_morph; trivial.

 intros; apply iso_prodcart; auto using w2m, w_iso.
Qed.

(** Concatenating non-recursive argument *)

Definition trad_sigma f :=
  comp_iso (sigma_isomap (fun x => x) f) sigma_isoassoc.

Definition pos_norec A F :=
  mkPositive
    (fun X => sigma A (fun x => pos_oper (F x) X))
    (sigma A (fun x => w1 (F x)))
    (fun c => w2 (F (fst c)) (snd c))
    (trad_sigma (fun x => wf (F x))). 

Lemma iso_arg_norec : forall P X A B Y f,
  ext_fun P X -> 
  ext_fun P A ->
  ext_fun2 P A B ->
  ext_fun2 P X f ->
  (forall x, x \in P -> iso_fun (X x) (W_F (A x) (B x) Y) (f x)) ->
  iso_fun (sigma P X)
   (W_F (sigma P A) (fun p => B (fst p) (snd p)) Y)
   (trad_sigma f).
intros.
unfold W_F, trad_sigma.
eapply iso_fun_trans.
 apply sigma_iso_fun_morph
  with (1:=H) (3:=H2)(4:=id_iso_fun _)(B':=fun x => W_F (A x) (B x) Y).
  do 2 red; intros.
  apply W_F_ext; auto with *.
  red; auto with *.

  intros.
  eapply iso_change_rhs.
  2:apply H3; trivial.
  apply W_F_ext; auto with *.
  red; auto with *.

 unfold W_F.
 apply iso_sigma_sigma; auto.
 red; intros.
 apply cc_arr_morph; auto with *.
Qed.


Lemma isPos_consnonrec A F :
  Proper (eq_set ==> eqpos) F ->
  (forall x, x \in A -> isPositive (F x)) ->
  isPositive (pos_norec A F).
constructor; simpl.
 do 2 red; intros; apply sigma_mono; intros; auto with *.
  do 2 red; intros; apply pos_oper_morph; auto with *.
  do 2 red; intros; apply pos_oper_morph; auto with *.

  rewrite <- H3.
  apply pos_mono; auto.

 do 2 red; intros.
 rewrite H2; reflexivity.

 intros X; apply iso_arg_norec with (B:=fun x y => w2 (F x) y); intros.
  do 2 red; intros; apply pos_oper_morph; auto with *.
  do 2 red; intros; apply w1_morph; auto with *.
  red; intros; apply w2_morph; auto with *.
  red; intros; apply wf_morph; auto with *.

  apply H0; trivial.
Qed.


(** Indexed recursive subterms *)

Definition trad_cc_prod P B f :=
  comp_iso (cc_prod_isomap P (fun x => x) f)
  (comp_iso (cc_prod_sigma_iso P)
      (sigma_isomap (fun x => x)
                    (fun x => cc_prod_isocurry P (fun y => B y (cc_app x y))))).

Lemma iso_param : forall P X A B Y f,
  ext_fun P X -> 
  ext_fun P A ->
  ext_fun2 P A B ->
  ext_fun2 P X f ->
  (forall x, x \in P -> iso_fun (X x) (W_F (A x) (B x) Y) (f x)) ->
  iso_fun (cc_prod P X)
   (W_F (cc_prod P A) (fun p => sigma P (fun x => B x (cc_app p x))) Y)
   (trad_cc_prod P B f).
intros.
unfold W_F, trad_cc_prod.
eapply iso_fun_trans.
 apply cc_prod_iso_fun_morph with (B':=fun x => W_F (A x) (B x) Y); trivial.
  do 2 red; intros.
  apply W_F_ext; auto with *.
  red; auto with *.

  apply id_iso_fun.

 eapply iso_fun_trans.
  apply iso_fun_cc_prod_sigma; trivial.
  red; intros.
  apply cc_arr_morph; auto with *.

  apply sigma_iso_fun_morph; intros; auto.
   do 2 red; intros.
   apply cc_prod_ext; auto with *.
   red; intros.
   apply cc_arr_morph; auto with *.
   apply H1; auto with *.
    apply cc_prod_elim with (1:=H4); trivial.
    apply cc_app_morph; auto.

   apply wfm1.
   do 2 red; intros.
   apply sigma_ext; intros; auto with *.
   apply H1; trivial.
    apply cc_prod_elim with (1:=H4); trivial.
    apply cc_app_morph; auto.

   red; intros.
   unfold cc_prod_isocurry.
   apply cc_lam_ext.
    apply sigma_ext; intros; auto with *.
    apply H1; trivial.
     apply cc_prod_elim with (1:=H4); trivial.
     apply cc_app_morph; auto.

    red; intros.
    rewrite H7; rewrite H9; reflexivity.

   apply id_iso_fun.

   eapply iso_change_rhs.
   2:apply cc_prod_curry_iso_fun.
    simpl; apply cc_arr_morph; auto with *.
    apply sigma_ext; intros; auto with *.
    apply H1; trivial.
     apply cc_prod_elim with (1:=H4); trivial.
     apply cc_app_morph; auto.

    do 2 red; intros; apply H1; trivial.
     apply cc_prod_elim with (1:=H4); trivial.
     apply cc_app_morph; auto with *.

    red; reflexivity.
Qed.

Definition pos_param A F :=
  mkPositive
    (fun X => cc_prod A (fun x => pos_oper (F x) X))
    (cc_prod A (fun x => w1 (F x)))
    (fun f => sigma A (fun x => w2 (F x) (cc_app f x)))
    (trad_cc_prod A (fun a => w2 (F a)) (fun a => wf (F a))).

Lemma isPos_param A F :
  Proper (eq_set ==> eqpos) F ->
  (forall x, x \in A -> isPositive (F x)) ->
  isPositive (pos_param A F).
unfold pos_param; constructor; simpl.
 do 2 red; intros; apply cc_prod_covariant; intros; auto with *.
  do 2 red; intros; apply pos_oper_morph; auto with *.
  apply H0; trivial.

 do 2 red; intros.
 apply sigma_ext; intros; auto with *.
 rewrite <- H2; rewrite <- H4; reflexivity.

 intros X; apply iso_param with (B:=fun x y => w2 (F x) y); intros.
  do 2 red; intros; apply pos_oper_morph; auto with *.
  do 2 red; intros; apply w1_morph; auto with *.
  red; intros; apply w2_morph; auto with *.
  red; intros; apply wf_morph; auto with *.

  apply H0; trivial.
Qed.


(** * Universe constraints: predicativity *)

Require Import ZFgrothendieck.

Section InductiveUniverse.

  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : omega \in U.

  Let Unonmt : empty \in U.
apply G_trans with omega; trivial.
apply zero_omega.
Qed.


  (** The predicativity condition: the operator remains within U.
     We also need the invariant that w1 and w2 also belong to the universe U
   *)
  Record pos_universe p := {
    G_pos_oper : forall X, X \in U -> pos_oper p X \in U;
    G_w1 : w1 p \in U;
    G_w2 : forall x, x \in w1 p -> w2 p x \in U
  }.

  Variable p : positive.
  Hypothesis p_ok : isPositive p.
  Hypothesis p_univ : pos_universe p.

  Lemma G_IND : IND p \in U.
unfold IND, INDi.
apply G_TI; trivial.
 apply Fmono_morph; apply p_ok.

 unfold IND_clos_ord.
 apply W_o_o; apply p_ok.

 unfold IND_clos_ord; apply G_W_ord; trivial.
  apply p_ok.
  apply p_univ.
  apply p_univ.

 apply p_univ.
Qed.

  Lemma G_INDi o : isOrd o -> INDi p o \in U.
intros.
apply G_incl with (IND p); trivial.
 apply G_IND; trivial.

 apply INDi_IND; trivial.
Qed.

  Lemma pos_univ_cst A : A \in U -> pos_universe (pos_cst A).
split; simpl; intros; trivial.
Qed.

  Lemma pos_univ_rec : pos_universe pos_rec.
split; simpl; intros; auto.
 apply G_singl; trivial.
 apply G_singl; trivial.
Qed.

  Lemma pos_univ_sum p1 p2 :
    pos_universe p1 -> pos_universe p2 -> pos_universe (pos_sum p1 p2).
destruct 1; destruct 1; split; simpl; intros.
 apply G_sum; auto.

 apply G_sum; auto.

 apply sum_case_ind0 with (2:=H); intros.
  apply morph_impl_iff1; auto with *.
  do 3 red; intros.
  rewrite <- H0; trivial.

  apply G_w4.
  rewrite H1; rewrite dest_sum_inl; trivial.

  apply G_w6.
  rewrite H1; rewrite dest_sum_inr; trivial.
Qed.

  Lemma pos_univ_prodcart p1 p2 :
    pos_universe p1 -> pos_universe p2 -> pos_universe (pos_consrec p1 p2).
destruct 1; destruct 1; split; simpl; intros.
 apply G_prodcart; auto.

 apply G_prodcart; auto.

 apply G_sum; auto.
  apply fst_typ in H; auto.
  apply snd_typ in H; auto.
Qed.

  Lemma pos_univ_norec A p' :
    Proper (eq_set==>eqpos) p' ->
    A \in U -> (forall x, x \in A -> pos_universe (p' x)) ->
       pos_universe (pos_norec A p').
split; simpl; intros.
 apply G_sigma; intros; trivial.
  do 2 red; intros.
  apply pos_oper_morph; auto with *.

  apply H1; trivial.

 apply G_sigma; intros; trivial.
  do 2 red; intros; apply w1_morph; auto.

  apply H1; trivial.

  apply H1; trivial.
   apply fst_typ_sigma in H2; trivial.

   apply snd_typ_sigma with (y:=fst x) in H2; auto with *.
   do 2 red; intros; apply w1_morph; auto.
Qed.

  Lemma pos_univ_param A p' :
    Proper (eq_set==>eqpos) p' ->
    A \in U -> (forall x, x \in A -> pos_universe (p' x)) ->
       pos_universe (pos_param A p').
split; simpl; intros.
 apply G_cc_prod; intros; trivial.
  do 2 red; intros.
  apply pos_oper_morph; auto with *.

  apply H1; trivial.

 apply G_cc_prod; intros; trivial.
  do 2 red; intros; apply w1_morph; auto.

  apply H1; trivial.

  apply G_sigma; intros; auto.
   do 2 red; intros; apply w2_morph; auto.
   rewrite H4; reflexivity.

   apply H1; trivial.
   apply cc_prod_elim with (1:=H2); trivial.
Qed.


End InductiveUniverse.

