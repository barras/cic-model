Require Import ZF ZFpairs ZFsum ZFrelations ZFcoc ZFord ZFfix.
Import IZF.

Require Import ZFstable.

(* Here we define the (semantic) notion of strictly positiveness.
   We then show that it fulfills all the requirements for the existence
   of a fixpoint:
   - monotonicity
   - stability
   - isomorphism with an instance of W
 *)

(* Qu: does this notion of strict positivity is powerful enough to build a model
   of IZF? *)

Inductive positive :=
| P_Cst (A:set)
| P_Rec
| P_Sum (p1 p2:positive)
| P_ConsRec (p1 p2:positive)
| P_ConsNoRec (A:set) (p:set->positive)
| P_Param (A:set) (p:set->positive).


Inductive eq_pos : positive -> positive -> Prop :=
| EP_Cst : forall A A', A == A' -> eq_pos (P_Cst A) (P_Cst A')
| EP_Rec : eq_pos P_Rec P_Rec
| EP_Sum : forall p1 p2 q1 q2,
   eq_pos p1 p2 -> eq_pos q1 q2 -> eq_pos (P_Sum p1 q1) (P_Sum p2 q2)
| EP_ConsRec : forall p1 p2 q1 q2,
   eq_pos p1 p2 -> eq_pos q1 q2 -> eq_pos (P_ConsRec p1 q1) (P_ConsRec p2 q2)
| EP_ConsNoRec : forall A A' p1 p2,
   A == A' ->
   (forall x x', x == x' -> eq_pos (p1 x) (p2 x')) ->
   eq_pos (P_ConsNoRec A p1) (P_ConsNoRec A' p2)
| EP_Param : forall A A' p1 p2,
   A == A' ->
   (forall x x', x == x' -> eq_pos (p1 x) (p2 x')) ->
   eq_pos (P_Param A p1) (P_Param A' p2).

Instance eq_pos_sym : Symmetric eq_pos.
red; induction 1; constructor; auto with *.
Qed.

Instance eq_pos_trans : Transitive eq_pos.
red.
intros x y z ep1 ep2; revert z ep2; induction ep1; intros; inversion_clear ep2;
  constructor; intros; eauto with *.
 transitivity A'; trivial.
 transitivity A'; trivial.

 transitivity A'; trivial.
Qed.

Lemma eq_pos_left : forall p1 p2, eq_pos p1 p2 -> eq_pos p1 p1.
intros.
transitivity p2; trivial.
symmetry; trivial.
Qed.

Lemma pos_rect : forall (P:positive->Type),
  (forall A, P (P_Cst A)) ->
  P P_Rec ->
  (forall p1 p2, eq_pos p1 p1 -> eq_pos p2 p2 -> P p1 -> P p2 -> P (P_Sum p1 p2)) ->
  (forall p1 p2, eq_pos p1 p1 -> eq_pos p2 p2 -> P p1 -> P p2 -> P (P_ConsRec p1 p2)) ->
  (forall A p,
   (forall x x', x == x' -> eq_pos (p x) (p x')) ->
   (forall x, x \in A -> P (p x)) ->
   P (P_ConsNoRec A p)) ->
  (forall A p,
   (forall x x', x == x' -> eq_pos (p x) (p x')) ->
   (forall x, x \in A -> P (p x)) ->
   P (P_Param A p)) ->
  forall p, eq_pos p p -> P p.
intros.
induction p; trivial.
 assert (eq_pos p1 p1 /\ eq_pos p2 p2) by (inversion H; auto with *).
 destruct H0; auto.

 assert (eq_pos p1 p1 /\ eq_pos p2 p2) by (inversion H; auto with *).
 destruct H0; auto.

 apply X3; intros.
  inversion_clear H; auto.

  apply X5.
  inversion H; auto with *.

 apply X4; intros.
  inversion_clear H; auto.

  apply X5.
  inversion H; auto with *.
Defined.


Fixpoint pos_oper p X :=
  match p with
  | P_Cst A => A
  | P_Rec => X
  | P_Sum p1 p2 => sum (pos_oper p1 X) (pos_oper p2 X)
  | P_ConsRec p1 p2 => prodcart (pos_oper p1 X) (pos_oper p2 X)
  | P_ConsNoRec A p => sigma A (fun x => pos_oper (p x) X)
  | P_Param A p => cc_prod A (fun x => pos_oper (p x) X)
  end.

Let eqfcst : forall X Y, eq_fun X (fun _ => Y) (fun _ => Y).
red; reflexivity.
Qed.
Hint Resolve eqfcst.


Lemma pos_oper_morph :
  Proper (eq_pos ==> eq_set ==> eq_set) pos_oper.
do 2 red; intros.
red.
induction H; simpl; intros; auto with *.
 apply sum_morph; auto.

 apply prodcart_morph; auto.

 apply sigma_ext; auto with *.

 apply cc_prod_ext; intros; auto.
 red; auto.
Qed.

Lemma pos_oper_mono :
  Proper (eq_pos ==> incl_set ==> incl_set) pos_oper.
do 2 red; intros.
red.
induction H; simpl; intros; auto with *.
 rewrite H; reflexivity.

 apply sum_mono; auto.

 apply prodcart_mono; auto.

 apply sigma_mono; auto with *.
  do 2 red; intros.
  apply pos_oper_morph; auto with *.
  transitivity (p2 x'); auto with *.
  symmetry.
  rewrite H4 in H3; auto with *.

  do 2 red; intros.
  apply pos_oper_morph; auto with *.
  rewrite <- H in H3.
  transitivity (p1 x0); auto with *.
  symmetry; auto with *.

  rewrite H; reflexivity.

 apply cc_prod_covariant; auto with *.
 do 2 red; intros.
 apply pos_oper_morph; auto with *.
 rewrite <- H in H3.
 transitivity (p1 x0); auto with *.
 symmetry; auto with *.
Qed.

Lemma sp_mono : forall p, eq_pos p p -> Proper (incl_set ==> incl_set) (pos_oper p).
do 2 red; intros.
apply pos_oper_mono; trivial.
Qed.

Lemma sp_morph : forall p, eq_pos p p -> morph1 (pos_oper p).
intros.
apply ZFfix.Fmono_morph.
apply sp_mono; trivial.
Qed.

Hint Resolve sp_morph.

Lemma sp_stable : forall p, eq_pos p p -> stable (pos_oper p).
intros.
apply pos_rect with (7:=H); simpl; intros.
 apply cst_stable.

 apply id_stable.

 apply sum_stable; eauto.

 apply prodcart_stable; eauto.

 apply sigma_stable'; trivial; intros.
 apply pos_oper_morph; auto.

 apply cc_prod_stable; trivial; intros.
 apply pos_oper_morph; auto.
Qed.


  Definition INDi p o :=
    TI (pos_oper p) o.

  Instance INDi_morph : Proper (eq_pos ==> eq_set ==> eq_set) INDi.
do 3 red; intros.
unfold INDi.
apply TR_morph_gen; trivial.
do 2 red; intros.
apply sup_morph; trivial.
red; intros.
apply pos_oper_morph; auto.
Qed.

  Lemma INDi_succ_eq : forall p o,
    eq_pos p p -> isOrd o -> INDi p (osucc o) == pos_oper p (INDi p o).
unfold INDi; intros.
apply TI_mono_succ; auto with *.
apply pos_oper_mono; trivial.
Qed.

  Lemma INDi_stable : forall p, eq_pos p p -> stable_ord (INDi p).
unfold INDi; intros.
apply TI_stable.
 apply pos_oper_mono; trivial.

 apply sp_stable; trivial.
Qed.

  Lemma INDi_mono : forall p o o',
    eq_pos p p -> isOrd o -> isOrd o' -> o \incl o' ->
    INDi p o \incl INDi p o'.
intros.
apply TI_mono; auto with *.
apply sp_mono; trivial.
Qed.


(*****************************************************************)
(* Convergence of INDi.
 * First we show any strictly positive definition is isomorphic to an
 * instance of W the type of well-founded tress.
 *)

Require Import ZFind_w.
Require Import ZFiso.


(* Label part of the constructor *)
Fixpoint pos_to_w1 p :=
  match p with
  | P_Cst A => A
  | P_Rec => singl empty
  | P_Sum p1 p2 => sum (pos_to_w1 p1) (pos_to_w1 p2)
  | P_ConsRec p1 p2 => prodcart (pos_to_w1 p1) (pos_to_w1 p2)
  | P_ConsNoRec X p => sigma X (fun x => pos_to_w1 (p x))
  | P_Param X p => cc_prod X (fun x => pos_to_w1 (p x))
  end.

Instance pos_to_w1_morph : Proper (eq_pos ==> eq_set) pos_to_w1.
do 2 red.
induction 1; simpl; intros; auto with *.
 rewrite IHeq_pos1; rewrite IHeq_pos2; reflexivity.

 rewrite IHeq_pos1; rewrite IHeq_pos2; reflexivity.

 apply sigma_ext; auto.

 apply cc_prod_ext; auto.
 red; auto.
Qed.

(* Subterm index part of the constructor *)
Fixpoint pos_to_w2 p :=
  match p with
  | P_Cst A => (fun _ => empty)
  | P_Rec => (fun _ => singl empty)
  | P_Sum p1 p2 => sum_case (pos_to_w2 p1) (pos_to_w2 p2)
  | P_ConsRec p1 p2 =>
      (fun c => sum (pos_to_w2 p1 (fst c)) (pos_to_w2 p2 (snd c)))
  | P_ConsNoRec X p =>
      (fun c => pos_to_w2 (p (fst c)) (snd c))
  | P_Param X p =>
      (fun f => sigma X (fun x => pos_to_w2 (p x) (cc_app f x)))
  end.

Instance pos_to_w2_morph : Proper (eq_pos ==> eq_set ==> eq_set) pos_to_w2.
do 3 red.
induction 1; simpl; intros; auto with *.
 (* Sum *)
 apply sum_case_morph; auto.

 (* ConsRec *)
 apply sum_morph.
  apply IHeq_pos1; apply fst_morph; trivial.
  apply IHeq_pos2; apply snd_morph; trivial.

 (* ConsNoRec *)
 apply H1.
  apply fst_morph; trivial.
  apply snd_morph; trivial.

 (* Param *)
 apply sigma_morph; auto.
 red; intros.
 apply H1; trivial.
 apply cc_app_morph; trivial.
Qed.
(*
Lemma pos_to_w2_morph : forall x y,
   eq_pos x y ->
   forall x0 y0, x0 \in pos_to_w1 x -> x0 == y0 -> pos_to_w2 x x0 == pos_to_w2 y y0.
induction 1; simpl; intros; auto with *.
 apply sum_case_ext with (pos_to_w1 p1) (pos_to_w1 q1); auto.

 apply sum_morph.
  apply IHeq_pos1.
   apply fst_typ in H1; trivial.
   apply fst_morph; trivial.
  apply IHeq_pos2.
   apply snd_typ in H1; trivial.
   apply snd_morph; trivial.

 apply H1.
  apply fst_typ_sigma in H2; trivial.

  apply fst_morph; trivial.

  apply snd_typ_sigma with (y:=fst x0) in H2; auto with *.
  do 2 red; intros.
  apply pos_to_w1_morph.
  transitivity (p2 x'); auto with *.
  symmetry; apply H0; auto with *.
  rewrite <- H5; trivial.

  apply snd_morph; trivial.

 apply sigma_ext; intros; auto.
 apply H1; trivial.
  apply cc_prod_elim with (1:=H2); trivial.

  apply cc_app_morph; trivial.
Qed.
*)
Lemma pos_to_w2_morph' :
  forall p, eq_pos p p -> ext_fun (pos_to_w1 p) (pos_to_w2 p).
do 2 red; intros.
apply pos_to_w2_morph; trivial.
Qed.


Definition trad_cst :=
  sigma_1r_iso (fun _ => cc_lam empty (fun _ => empty)).

Lemma iso_cst : forall A X,
  iso_fun A (W_F A (fun _ => empty) X) trad_cst.
intros.
unfold trad_cst, W_F.
apply sigma_iso_fun_1_r'; intros; auto with *.
apply cc_prod_iso_fun_0_l'.
Qed.


Definition trad_reccall f :=
  comp_iso f (comp_iso (fun x => cc_lam (singl empty) (fun _ => x)) (couple empty)).

Lemma iso_reccall : forall X Y f,
  iso_fun X Y f ->
  iso_fun X (W_F (singl empty) (fun _ => singl empty) Y) (trad_reccall f).
intros.
unfold trad_reccall, W_F.
eapply iso_fun_trans with (1:=H).
eapply iso_fun_trans.
 apply cc_prod_iso_fun_1_l' with (F:=fun _ => Y); reflexivity.

 apply sigma_iso_fun_1_l' with (F:=fun _ => _).
 do 2 red; reflexivity.
Qed.


Definition trad_sum f g :=
  comp_iso (sum_isomap f g) sum_sigma_iso.

Lemma cc_prod_sum_case_commut A1 A2 B1 B2 Y x x':
  ext_fun A1 B1 ->
  ext_fun A2 B2 ->
  x \in sum A1 A2 ->
  x == x' ->
  sum_case (fun x => cc_prod (B1 x) (fun _ => Y))
     (fun x => cc_prod (B2 x) (fun _ => Y)) x ==
  cc_prod (sum_case B1 B2 x') (fun _ => Y).
intros.
apply sum_ind with (3:=H1); intros.
 rewrite sum_case_inl0; eauto.
 apply cc_prod_ext; intros; auto with *.
 rewrite sum_case_inl0.
  apply H.
   rewrite H4; rewrite dest_sum_inl; trivial.
   apply dest_sum_morph; trivial.
  exists x0; rewrite <- H2; trivial.

 rewrite sum_case_inr0; eauto.
 apply cc_prod_ext; intros; auto with *.
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
    (sum_case (fun x => cc_prod (B1 x) (fun _ => X))
              (fun x => cc_prod (B2 x) (fun _ => X))) ==
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
assert (m1 : ext_fun A1 (fun x => cc_prod (B1 x) (fun _ => Y))) by auto.
assert (m1' : ext_fun A2 (fun x => cc_prod (B2 x) (fun _ => Y))) by auto.
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


Definition trad_sigma f :=
  comp_iso (sigma_isomap (fun x => x) f) sigma_isoassoc.

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
 apply cc_prod_ext; auto with *.
Qed.

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
  apply cc_prod_ext; auto.

  apply sigma_iso_fun_morph; intros; auto.
   do 2 red; intros.
   apply cc_prod_ext; auto with *.
   red; intros.
   apply cc_prod_ext; trivial.
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
    apply cc_prod_ext; trivial.
    apply sigma_ext; intros; auto with *.
    apply H1; trivial.
     apply cc_prod_elim with (1:=H4); trivial.
     apply cc_app_morph; auto.

    do 2 red; intros; apply H1; trivial.
     apply cc_prod_elim with (1:=H4); trivial.
     apply cc_app_morph; auto with *.

    red; reflexivity.
Qed.

Fixpoint trad_pos_w f p :=
  match p with 
  | P_Cst A => trad_cst
  | P_Rec => trad_reccall f
  | P_Sum p1 p2 => trad_sum (trad_pos_w f p1) (trad_pos_w f p2)
  | P_ConsRec p1 p2 =>
      trad_prodcart (pos_to_w2 p1) (pos_to_w2 p2) (trad_pos_w f p1) (trad_pos_w f p2)
  | P_ConsNoRec A p => trad_sigma (fun a => trad_pos_w f (p a))
  | P_Param A p => trad_cc_prod A (fun a => pos_to_w2 (p a)) (fun a => trad_pos_w f (p a))
  end.


Lemma trad_pos_w_morph_gen :
  forall X Y f f' p p',
  eq_pos p p' -> eq_fun X f f' -> typ_fun f X Y ->
  eq_fun (pos_oper p X) (trad_pos_w f p) (trad_pos_w f' p') /\ 
  typ_fun (trad_pos_w f p) (pos_oper p X) (W_F (pos_to_w1 p) (pos_to_w2 p) Y).
intros X Y f f' p p' eqp ef tyf.
induction eqp; try (destruct IHeqp1; destruct IHeqp2||destruct IHeq_pos);
  simpl; split; intros.
 (* Cst *)
 unfold trad_cst; red; intros.
 unfold sigma_1r_iso.
 apply couple_morph; auto with *.

 unfold trad_cst.
 apply sigma_1r_iso_typ; intros; auto.
 apply cc_prod_intro; intros; auto with *.
 apply empty_ax in H1; contradiction.

 (* Rec *)
 unfold trad_reccall, comp_iso; red; intros.
 apply couple_morph; auto with *.
 apply cc_lam_ext; auto with *.
 red; auto.

 unfold trad_reccall, comp_iso.
 red; intros.
 apply couple_intro_sigma; auto.
  apply singl_intro.

  apply cc_prod_intro; intros; auto with *.

 (* Sum *)
 unfold trad_sum.
 eapply comp_iso_eq_fun.
  apply sum_isomap_typ with (1:=H0) (2:=H2).

  apply sum_isomap_ext; trivial.

  red; intros; apply sum_sigma_iso_morph; trivial.

 assert (pw2m := pos_to_w2_morph').
 apply eq_pos_left in eqp1; apply eq_pos_left in eqp2.
 unfold trad_sum.
 eapply comp_iso_typ.
  apply sum_isomap_typ with (1:=H0) (2:=H2).

  rewrite <- W_F_sum_commut; auto.
  apply sum_sigma_iso_typ; auto.

 (* ConsRecArg *)
 assert (pw2m := pos_to_w2_morph').
 unfold trad_prodcart.
 eapply comp_iso_eq_fun.
  intros x tyx; rewrite sigma_nodep in tyx; revert x tyx.
  apply sigma_isomap_typ with (B':=fun _ => W_F (pos_to_w1 q1) (pos_to_w2 q1) Y);
    auto with *. 
  eassumption.

  intros x x' tyx; rewrite sigma_nodep in tyx; revert x x' tyx.
  apply sigma_isomap_ext; auto with *.
 eapply comp_iso_eq_fun.
  intros x tyx; rewrite <- sigma_nodep in tyx; revert x tyx.
  apply eq_pos_left in eqp1; apply eq_pos_left in eqp2.
  apply prodcart_sigma_iso_typ; auto.

  red; intros; unfold prodcart_sigma_iso.
  rewrite H4; reflexivity.

  apply sigma_isomap_ext; intros.
   do 2 red; intros; apply prodcart_morph;
     (apply cc_prod_ext; [apply pos_to_w2_morph';trivial|red;reflexivity]).
    apply eq_pos_left in eqp1; trivial.
    apply fst_typ in H3; trivial.
    apply fst_morph; trivial.
    apply eq_pos_left in eqp2; trivial.
    apply snd_typ in H3; trivial.
    apply snd_morph; trivial.

   red; trivial.

   apply prodcart_cc_prod_iso_morph; trivial.
   apply sum_morph; apply pos_to_w2_morph; trivial.
    apply fst_typ in H3; trivial.
    apply fst_morph; trivial.
    apply snd_typ in H3; trivial.
    apply snd_morph; trivial.

 assert (pw2m := pos_to_w2_morph').
 apply eq_pos_left in eqp1; apply eq_pos_left in eqp2.
 unfold trad_prodcart.
 eapply comp_iso_typ.
  apply sigma_isomap_typ_prod; [apply H0|apply H2].
 eapply comp_iso_typ.
  apply prodcart_sigma_iso_typ; auto.

  apply sigma_isomap_typ; intros.
  3:red; auto.
   do 2 red; intros; apply prodcart_morph; (apply cc_prod_ext;[|red; reflexivity]).
    apply fst_typ in H3.
    apply fst_morph in H4.
    apply pos_to_w2_morph; trivial.

    apply snd_typ in H3.
    apply snd_morph in H4.
    apply pos_to_w2_morph; trivial.

   do 2 red; intros; apply cc_prod_ext;[|red; reflexivity].
   apply sum_morph; apply pos_to_w2_morph; trivial.
    apply fst_typ in H3; trivial.
    apply fst_morph; trivial.
    apply snd_typ in H3; trivial.
    apply snd_morph; trivial.

   red; intros.
   apply eq_elim with
     (cc_prod (sum (pos_to_w2 p1 (fst x)) (pos_to_w2 q1 (snd x)))
        (sum_case (fun _ => Y) (fun _ => Y))).
    apply cc_prod_ext; auto with *.
    red; intros.
    apply sum_case_ind with (6:=H5); auto with *.
     do 2 red; intros.
     rewrite H7; reflexivity.

     do 2 red; reflexivity.
     do 2 red; reflexivity.
   apply prodcart_cc_prod_iso_typ; trivial.

 (* ConsNonRecArg *)
 red; intros.
 assert (pm : forall x x', x == x' -> eq_pos (p1 x) (p1 x')).
  intros.
  transitivity (p2 x'0); auto with *.
  symmetry; apply H0; auto with *.
 assert (Hrec : forall p p', p \in sigma A (fun x => pos_oper (p1 x) X) ->
   p == p' ->
   trad_pos_w f (p1 (fst p)) (snd p) == trad_pos_w f' (p2 (fst p')) (snd p')).
  intros.
  apply H1; trivial.
   apply fst_typ_sigma in H4; trivial.
   apply fst_morph; trivial.
   apply snd_typ_sigma with (2:=H4); auto with *.
   do 2 red; intros.
   apply pos_oper_morph; auto with *.

   apply snd_morph; trivial.
 unfold trad_sigma, comp_iso, sigma_isomap, sigma_isoassoc.
 repeat (rewrite fst_def||rewrite snd_def).
 apply couple_morph.
  apply couple_morph; apply fst_morph; auto.

  apply snd_morph; auto.

 assert (pm : forall x x', x == x' -> eq_pos (p1 x) (p1 x')).
  intros.
  transitivity (p2 x'); auto.
  symmetry; apply H0; auto with *.
 unfold trad_sigma.
 eapply comp_iso_typ.
  apply sigma_isomap_typ
    with (3:=fun _ h=>h)(B':=fun x => W_F (pos_to_w1 (p1 x)) (pos_to_w2 (p1 x)) Y); intros.
   do 2 red; intros; apply pos_oper_morph; auto with *.

   do 2 red; intros; apply W_F_ext; auto with *.
    apply pos_to_w1_morph; auto with *.
    red; intros; apply pos_to_w2_morph; auto with *.

   apply (H1 x x); auto with *.

  apply sigma_isoassoc_typ.
   do 2 red; intros; apply pos_to_w1_morph; auto with *.
   red; intros; apply cc_prod_ext;[|red;reflexivity].
   apply pos_to_w2_morph; auto with *.

 (* Param *)
 assert (pm : forall x x', x == x' -> eq_pos (p1 x) (p1 x')).
  intros.
  transitivity (p2 x'); auto.
  symmetry; apply H0; auto with *.
 unfold trad_cc_prod.
 eapply comp_iso_eq_fun.
  apply cc_prod_isomap_typ with (4:=fun _ h=>h).
  4:intros; apply (H1 x x); auto with *.
   do 2 red; intros; apply W_F_ext; auto with *.
    apply pos_to_w1_morph; auto.
    red; intros; apply pos_to_w2_morph; auto with *.

   do 2 red; trivial.

   red; intros.
   transitivity (trad_pos_w f' (p2 x') y').
    apply H1; trivial.

    rewrite H3 in H2; rewrite H5 in H4.
    symmetry; apply H1; auto with *.
    revert H4; apply eq_elim; symmetry; apply pos_oper_morph; auto with *.

  apply cc_prod_isomap_ext; intros; auto with *.
   do 2 red; intros; apply pos_oper_morph; auto with *.
   red; trivial.
   apply H1; trivial.
 eapply comp_iso_eq_fun.
  apply cc_prod_sigma_iso_typ.
   do 2 red; intros; apply pos_to_w1_morph; auto.

   red; intros; apply cc_prod_ext;[|red;reflexivity].
   apply pos_to_w2_morph; auto with *.

  red; intros; apply cc_prod_sigma_iso_morph; trivial.

  apply sigma_isomap_ext; auto with *.
   do 2 red; intros; apply cc_prod_ext; auto with *.
   red; intros; apply cc_prod_ext;[|red; reflexivity].
   apply pos_to_w2_morph; auto with *.
   apply cc_app_morph; trivial.

   red; trivial.

   unfold cc_prod_isocurry; intros.
   apply cc_lam_ext; auto with *.
    apply sigma_ext; intros; auto.
    apply pos_to_w2_morph; auto with *.
    apply cc_app_morph; trivial.
    red; intros.
    rewrite H5; rewrite H7; reflexivity.

 assert (pm : forall x x', x == x' -> eq_pos (p1 x) (p1 x')).
  intros.
  transitivity (p2 x'); auto.
  symmetry; apply H0; auto with *.
 unfold trad_cc_prod.
 eapply comp_iso_typ.
  apply cc_prod_isomap_typ
    with (4:=fun a h=>h) (B':=fun x => W_F (pos_to_w1 (p1 x)) (pos_to_w2 (p1 x)) Y).
   do 2 red; intros; apply W_F_ext; auto with *.
    apply pos_to_w1_morph; auto.

    red; intros.
    apply pos_to_w2_morph; auto.

   do 2 red; trivial.

   red; intros.
   transitivity (trad_pos_w f' (p2 x') y').
    apply H1; trivial.

    symmetry; apply H1; auto with *.
    rewrite <- H5; revert H4; apply eq_elim.
    apply pos_oper_morph; auto with *.

   intros.
   apply (H1 x x); auto with *.

 eapply comp_iso_typ.
  apply cc_prod_sigma_iso_typ.
   do 2 red; intros; apply pos_to_w1_morph; auto.

   red; intros; apply cc_prod_ext;[|red; reflexivity].
   apply pos_to_w2_morph; auto.

  apply sigma_isomap_typ.
   do 2 red; intros.
   apply cc_prod_ext; intros; auto with *.
   red; intros.
   apply cc_prod_ext;[|red;reflexivity].
   apply pos_to_w2_morph; auto.
   apply cc_app_morph; trivial.

   do 2 red; intros.
   apply cc_prod_ext; [|red;reflexivity].
   apply sigma_ext; intros; auto with *.
   apply pos_to_w2_morph; auto.
   apply cc_app_morph; trivial.

   red; trivial.

   intros.
   apply cc_prod_isocurry_typ.
    do 2 red; intros.
    apply pos_to_w2_morph; auto with *.
    apply cc_app_morph; auto with *.

    red; reflexivity.
Qed.


Lemma trad_pos_w_morph : Proper ((eq_set==>eq_set)==>eq_pos==>eq_set==>eq_set) trad_pos_w.
do 4 red.
induction 2; simpl; intros.
 (* Cst *)
 unfold trad_cst.
 apply couple_morph; trivial.
 apply cc_lam_ext; auto with *.

 (* Rec *)
 unfold trad_reccall.
 apply comp_iso_morph; trivial.
 red; intros.
 apply comp_iso_morph; trivial.
 2:apply couple_morph; auto with *.
 red; intros.
 apply cc_lam_ext; auto with *.
 red; trivial.

 (* Sum *)
 unfold trad_sum.
 apply comp_iso_morph; trivial.
  apply sum_isomap_morph; auto.
  apply sum_sigma_iso_morph.

 (* ConsRec *)
 unfold trad_prodcart.
 apply comp_iso_morph; trivial.
  apply sigma_isomap_morph; auto.
  red; intros; auto.

  apply comp_iso_morph.
   red; intros.
   unfold prodcart_sigma_iso.
   rewrite H1; reflexivity.

   apply sigma_isomap_morph.
    red; auto.

    do 2 red; intros.
    apply prodcart_cc_prod_iso_morph; trivial.
    apply sum_morph; apply pos_to_w2_morph; trivial.
     apply fst_morph; trivial.
     apply snd_morph; trivial.

 (* ConsNoRec *)
 unfold trad_sigma.
 apply comp_iso_morph; trivial.
  apply sigma_isomap_morph; auto with *.
  red; auto.

  apply sigma_isoassoc_morph.

 (* Param *)
 unfold trad_cc_prod.
 apply comp_iso_morph; trivial.
  apply cc_prod_isomap_morph; auto with *.
  red; auto.

  apply comp_iso_morph; trivial.
   apply cc_prod_sigma_iso_morph; trivial.

   apply sigma_isomap_morph.
    red; auto.

    unfold cc_prod_isocurry.
    do 2 red; intros.
    apply cc_lam_ext.
     apply sigma_morph; trivial.
     red; intros.
     apply pos_to_w2_morph; auto.
     apply cc_app_morph; trivial.

     red; intros.
     rewrite H5; rewrite H7; reflexivity.
Qed.


Lemma trad_pos_w_morph0 : forall X f f' p p',
  eq_pos p p' ->
  eq_fun X f f' ->
  eq_fun (pos_oper p X) (trad_pos_w f p) (trad_pos_w f' p').
intros.
apply trad_pos_w_morph_gen with (Y:=replf X f); trivial.
red; intros.
rewrite replf_ax; eauto with *. 
apply eq_fun_ext in H0; trivial.
Qed.

Lemma trad_pos_w_typ : forall X Y f p,
  eq_pos p p ->
  ext_fun X f ->
  typ_fun f X Y ->
  typ_fun (trad_pos_w f p) (pos_oper p X) (W_F (pos_to_w1 p) (pos_to_w2 p) Y).
intros.
apply trad_pos_w_morph_gen with (1:=H)(2:=H0)(3:=H1).
Qed.
(*
Lemma trad_pos_w_typ :
  forall X Y f p,
  eq_pos p p -> morph1 f -> typ_fun f X Y ->
  typ_fun (trad_pos_w f p) (pos_oper p X) (W_F (pos_to_w1 p) (pos_to_w2 p) Y).
intros X Y f p eqp ef tyf.
assert (posw2m := pos_to_w2_morph').
red.
elim eqp using pos_rect; simpl; intros.
 (* Cst *)
 unfold trad_cst.
 apply sigma_1r_iso_typ; intros; auto.
 apply cc_prod_intro; intros; auto with *.
 apply empty_ax in H1; contradiction.

 (* Rec *)
 unfold trad_reccall, comp_iso.
 apply couple_intro_sigma; auto.
  apply singl_intro.

  apply cc_prod_intro; intros; auto with *.

 (* Sum *)
 unfold trad_sum.
 eapply comp_iso_typ with (3:=H3).
  apply sum_isomap_typ with (1:=H1) (2:=H2).

  rewrite <- W_F_sum_commut; auto.
  apply sum_sigma_iso_typ; auto.

 (* ConsRecArg *)
 unfold trad_prodcart.
 eapply comp_iso_typ with (3:=H3).
  apply sigma_isomap_typ_prod; [eexact H1|eexact H2].
 eapply comp_iso_typ.
  apply prodcart_sigma_iso_typ; auto.

  apply sigma_isomap_typ; intros.
  3:red; auto.
   do 2 red; intros; apply prodcart_morph; (apply cc_prod_ext;[|red; reflexivity]).
    apply fst_morph in H5.
    apply pos_to_w2_morph; trivial.

    apply snd_morph in H5.
    apply pos_to_w2_morph; trivial.

   do 2 red; intros; apply cc_prod_ext;[|red; reflexivity].
   apply sum_morph; apply pos_to_w2_morph; trivial.
    apply fst_morph; trivial.
    apply snd_morph; trivial.

   red; intros.
   apply eq_elim with
     (cc_prod (sum (pos_to_w2 p1 (fst x0)) (pos_to_w2 p2 (snd x0)))
        (sum_case (fun _ => Y) (fun _ => Y))).
    apply cc_prod_ext; auto with *.
    red; intros.
    apply sum_case_ind with (6:=H6); auto with *.
     do 2 red; intros.
     rewrite H8; reflexivity.

     do 2 red; reflexivity.
     do 2 red; reflexivity.
   apply prodcart_cc_prod_iso_typ; trivial.

 (* ConsNonRecArg *)
 unfold trad_sigma.
 eapply comp_iso_typ with (3:=H1); clear x H1.
  apply sigma_isomap_typ
    with (3:=fun _ h=>h)(B':=fun x => W_F (pos_to_w1 (p0 x)) (pos_to_w2 (p0 x)) Y); intros.
   do 2 red; intros; apply pos_oper_morph; auto with *.

   do 2 red; intros; apply W_F_ext; auto with *.
    apply pos_to_w1_morph; auto with *.
    red; intros; apply pos_to_w2_morph; auto with *.

   red; apply (H0 x H1); auto with *.

  apply sigma_isoassoc_typ.
   do 2 red; intros; apply pos_to_w1_morph; auto with *.
   red; intros; apply cc_prod_ext;[|red;reflexivity].
   apply pos_to_w2_morph; auto with *.

 (* Param *)
 unfold trad_cc_prod.
 eapply comp_iso_typ with (3:=H1); clear x H1.
  apply cc_prod_isomap_typ
    with (4:=fun a h=>h) (B':=fun x => W_F (pos_to_w1 (p0 x)) (pos_to_w2 (p0 x)) Y).
   do 2 red; intros; apply W_F_ext; auto with *.
    apply pos_to_w1_morph; auto.

    red; intros.
    apply pos_to_w2_morph; auto.

   do 2 red; trivial.

   red; intros.
   apply trad_pos_w_morph; auto.

   intros.
   red; apply H0; trivial.

 eapply comp_iso_typ.
  apply cc_prod_sigma_iso_typ.
   do 2 red; intros; apply pos_to_w1_morph; auto.

   red; intros; apply cc_prod_ext;[|red; reflexivity].
   apply pos_to_w2_morph; auto.

  apply sigma_isomap_typ.
   do 2 red; intros.
   apply cc_prod_ext; intros; auto with *.
   red; intros.
   apply cc_prod_ext;[|red;reflexivity].
   apply pos_to_w2_morph; auto.
   apply cc_app_morph; trivial.

   do 2 red; intros.
   apply cc_prod_ext; [|red;reflexivity].
   apply sigma_ext; intros; auto with *.
   apply pos_to_w2_morph; auto.
   apply cc_app_morph; trivial.

   red; trivial.

   intros.
   apply cc_prod_isocurry_typ.
    do 2 red; intros.
    apply pos_to_w2_morph; auto with *.
    apply cc_app_morph; auto with *.

    red; reflexivity.
Qed.
*)

Lemma trad_w_iso_fun :
  forall X Y f p,
  eq_pos p p -> iso_fun X Y f ->
  iso_fun (pos_oper p X) (W_F (pos_to_w1 p) (pos_to_w2 p) Y) (trad_pos_w f p).
intros X Y f p eqp isof.
assert (tyf := iso_typ isof).
assert (fm := iso_funm isof).
elim eqp using pos_rect; simpl; intros.
 (* Cst *)
 apply iso_cst.

 (* Rec *)
 apply iso_reccall; trivial.

 (* Sum *)
 apply iso_sum; trivial.
  apply pos_to_w2_morph'; trivial.
  apply pos_to_w2_morph'; trivial.

 (* ConsRecArg *)
 apply iso_prodcart; trivial.
  apply pos_to_w2_morph'; trivial.
  apply pos_to_w2_morph'; trivial.

 (* ConsNonRecArg *)
 apply iso_arg_norec with (B:=fun x => pos_to_w2 (p0 x)); intros.
  do 2 red; intros.
  apply pos_oper_morph; auto with *.

  do 2 red; intros; apply pos_to_w1_morph; auto with *.

  red; intros; apply pos_to_w2_morph; auto with *.

  red; intros.
  revert H3 H4; apply trad_pos_w_morph0; auto with *.

  apply H0; auto with *. 

 (* Param *)
 apply iso_param with (B:=fun x => pos_to_w2 (p0 x)); intros.
  do 2 red; intros.
  apply pos_oper_morph; auto with *.

  do 2 red; intros; apply pos_to_w1_morph; auto with *.

  red; intros; apply pos_to_w2_morph; auto with *.

  red; intros.
  revert H3 H4; apply trad_pos_w_morph0; auto with *.

  apply H0; auto with *. 
Qed.
(*
Lemma trad_w_iso_fun :
  forall X Y f p,
  morph1 f ->
  eq_pos p p -> iso_fun X Y f ->
  iso_fun (pos_oper p X) (W_F (pos_to_w1 p) (pos_to_w2 p) Y) (trad_pos_w f p).
intros X Y f p fm eqp isof.
assert (tyf := iso_typ isof).
elim eqp using pos_rect; simpl; intros.
 (* Cst *)
 apply iso_cst.

 (* Rec *)
 apply iso_reccall; trivial.

 (* Sum *)
 apply iso_sum; trivial.
  apply pos_to_w2_morph'; trivial.
  apply pos_to_w2_morph'; trivial.

 (* ConsRecArg *)
 apply iso_prodcart; trivial.
  apply pos_to_w2_morph'; trivial.
  apply pos_to_w2_morph'; trivial.

 (* ConsNonRecArg *)
 apply iso_arg_norec with (B:=fun x => pos_to_w2 (p0 x)); intros.
  do 2 red; intros.
  apply pos_oper_morph; auto with *.

  do 2 red; intros; apply pos_to_w1_morph; auto with *.

  red; intros; apply pos_to_w2_morph; auto with *.

  red; intros.
  apply trad_pos_w_morph; auto with *.

  apply H0; auto with *. 

 (* Param *)
 apply iso_param with (B:=fun x => pos_to_w2 (p0 x)); intros.
  do 2 red; intros.
  apply pos_oper_morph; auto with *.

  do 2 red; intros; apply pos_to_w1_morph; auto with *.

  red; intros; apply pos_to_w2_morph; auto with *.

  red; intros.
  apply trad_pos_w_morph; auto with *.

  apply H0; auto with *. 
Qed.
*)

Lemma trad_w_iso_id :
  forall X p,
  eq_pos p p ->
  iso_fun (pos_oper p X) (W_F (pos_to_w1 p) (pos_to_w2 p) X)
    (trad_pos_w (fun x => x) p).
intros.
apply trad_w_iso_fun; trivial.
(* do 2 red; auto.*)

 apply id_iso_fun.
Qed.


Section InductiveFixpoint.

  Variable p : positive.
  Hypothesis p_ok : eq_pos p p.

  Let Wpf := pos_oper p.
  Let Wp := W (pos_to_w1 p) (pos_to_w2 p).
  Let Wff := Wf (pos_to_w1 p) (pos_to_w2 p).

  Let Wd := Wdom (pos_to_w1 p) (pos_to_w2 p).

  Let Bext : ext_fun (pos_to_w1 p) (pos_to_w2 p).
apply pos_to_w2_morph'; trivial.
Qed.
  Let Wff_mono : Proper (incl_set ==> incl_set) Wff.
apply Wf_mono; trivial.
Qed.
  Let Wff_typ : forall X, X \incl Wd -> Wff X \incl Wd.
intros.
apply Wf_typ; trivial.
Qed.

  Definition IND_clos_ord := W_ord (pos_to_w1 p) (pos_to_w2 p).
  Definition IND := INDi p IND_clos_ord.


  Let WFf := W_F (pos_to_w1 p) (pos_to_w2 p).
  Let Wp2 := W2 (pos_to_w1 p) (pos_to_w2 p).

  Lemma IND_eq : IND == pos_oper p IND.
pose (isow := TI_iso (pos_oper p) (fun f => trad_pos_w f p) IND_clos_ord).
destruct TI_iso_fun with 
  (F:=pos_oper p) (G:=WFf) (g:=fun f => trad_pos_w f p) (o:=IND_clos_ord) as
 (isof, expTI); intros.
(*  apply stable2_weaker; auto with *.
  apply sp_stable; trivial.*)

  apply sp_mono; trivial.

  apply W_F_mono; trivial.

  do 2 red; intros; apply trad_pos_w_morph; trivial.

  apply trad_pos_w_morph0; trivial.

  apply trad_w_iso_fun; trivial.

  apply W_o_o; trivial.
fold isow in expTI, isof.
apply iso_fun_inj with Wp2 (trad_pos_w isow p).
 generalize isof; apply iso_fun_morph; try reflexivity.
 red; intros.
 rewrite <- expTI.
  apply (iso_funm isof); trivial.
  rewrite <- H0; trivial.

 apply trad_w_iso_fun with (p:=p) in isof; trivial.
 apply iso_change_rhs with (2:=isof).
 symmetry; apply W2_eqn; trivial.

 unfold IND, INDi; red; intros.
 rewrite <- TI_mono_succ; auto with *.
 2:apply sp_mono; trivial.
 2:apply W_o_o; trivial.  
 revert H; apply TI_incl.
  apply sp_mono; trivial.
  apply isOrd_succ; apply W_o_o; trivial.
  apply lt_osucc; apply W_o_o; trivial.
Qed.

  Lemma INDi_IND : forall o,
    isOrd o ->
    INDi p o \incl IND.
induction 1 using isOrd_ind; intros.
unfold INDi.
rewrite TI_eq; auto.
red; intros.
rewrite sup_ax in H2; auto.
destruct H2.
rewrite IND_eq.
revert H3; apply sp_mono; auto.
apply H1; trivial.
Qed.

End InductiveFixpoint.

Require Import ZFgrothendieck.
Section InductiveUniverse.

  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : omega \in U.

  Let Unonmt : empty \in U.
apply G_trans with omega; trivial.
apply zero_omega.
Qed.

  Inductive pos_universe : positive -> Prop :=
    PU_Cst A : A \in U -> pos_universe (P_Cst A)
  | PU_Rec : pos_universe P_Rec
  | PU_Sum p1 p2 : pos_universe p1 -> pos_universe p2 -> pos_universe (P_Sum p1 p2)
  | PU_ConsRec p1 p2 : pos_universe p1 -> pos_universe p2 -> pos_universe (P_ConsRec p1 p2)
  | PU_ConsNoRec A p : A \in U -> (forall x, x \in A -> pos_universe (p x)) ->
       pos_universe (P_ConsNoRec A p)
  | PU_Param A p : A \in U -> (forall x, x \in A -> pos_universe (p x)) ->
       pos_universe (P_Param A p).


  Lemma G_sum X Y : X \in U -> Y \in U -> sum X Y \in U.
unfold sum; intros.
apply G_subset; trivial.
apply G_prodcart; trivial.
 unfold ZFnats.succ, ZFnats.zero.
 assert (empty \in U) by (apply G_trans with omega; auto; apply zero_omega).
 eauto 10 using G_union2, G_singl.

 apply G_union2; trivial.
Qed.


  Lemma pos_univ_oper_ok p X :
    eq_pos p p -> pos_universe p -> X \in U -> pos_oper p X \in U.
intros.
revert H; elim H0; simpl; intros; trivial.
 inversion_clear H5.
 apply G_sum; auto.

 inversion_clear H5.
 apply G_prodcart; auto.

 inversion_clear H4.
 apply G_sigma; auto with *.
 do 2 red; intros; apply pos_oper_morph; auto with *.

 inversion_clear H4.
 apply G_cc_prod; auto with *.
 do 2 red; intros; apply pos_oper_morph; auto with *.
Qed.


  Lemma G_posw1 p : eq_pos p p -> pos_universe p ->
   pos_to_w1 p \in U.
intros p_ok.
elim p_ok using pos_rect; simpl; intros.
 inversion_clear H; trivial.

 apply G_singl; trivial.

 inversion_clear H3.
 apply G_sum; auto.

 inversion_clear H3.
 apply G_prodcart; auto.

 inversion_clear H1.
 apply G_sigma; auto.
 do 2 red; intros; apply pos_to_w1_morph; auto.

 inversion_clear H1.
 apply G_cc_prod; auto.
 do 2 red; intros; apply pos_to_w1_morph; auto.
Qed.

  Lemma G_posw2 p x :
    eq_pos p p ->
    pos_universe p -> x \in pos_to_w1 p -> pos_to_w2 p x \in U.
intros p_ok.
revert x; elim p_ok using pos_rect; simpl; intros.
 apply G_trans with omega; trivial.
 apply zero_omega.

 apply G_singl; trivial.

 inversion_clear H3.
 apply sum_ind with (3:=H4); intros.
  rewrite sum_case_inl0; eauto.
  apply H1; trivial.
  rewrite H7; rewrite dest_sum_inl; trivial.

  rewrite sum_case_inr0; eauto.
  apply H2; trivial.
  rewrite H7; rewrite dest_sum_inr; trivial.

 inversion_clear H3.
 apply G_sum; auto.
  apply fst_typ in H4; auto.
  apply snd_typ in H4; auto.

 inversion_clear H1.
 apply H0.
  apply fst_typ_sigma in H2; trivial.

  apply H4.
  apply fst_typ_sigma in H2; trivial.

  apply snd_typ_sigma with (2:=H2); auto with *.
  do 2 red; intros; apply pos_to_w1_morph; auto.

 inversion_clear H1.
 apply G_sigma; trivial.
  do 2 red; intros; apply pos_to_w2_morph; auto with *.
  apply cc_app_morph; auto with *.

  intros.
  apply H0; auto.
  apply cc_prod_elim with (1:=H2); trivial.
Qed.

  Lemma G_IND p : eq_pos p p -> pos_universe p -> IND p \in U.
intros.
unfold IND, INDi.
apply G_TI; trivial.
 apply pos_oper_morph; trivial.

 apply W_o_o; trivial.
 apply pos_to_w2_morph'; trivial.

 apply G_W_ord; trivial.
  apply pos_to_w2_morph'; trivial.

  apply G_posw1; trivial.

  intros; apply G_posw2; trivial.

 intros; apply pos_univ_oper_ok; trivial.
Qed.

  Lemma G_INDi p o : eq_pos p p -> pos_universe p -> isOrd o -> INDi p o \in U.
intros.
apply G_incl with (IND p); trivial.
 apply G_IND; trivial.

 apply INDi_IND; trivial.
Qed.

End InductiveUniverse.
