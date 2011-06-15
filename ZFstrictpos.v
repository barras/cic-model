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

(* Qu: maybe we can avoid the restriction that the first component
   of a sigma cannot be a recursive argument if we consider that we only need
   parametricity (map) up to isomorphic types. *)

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
   (forall x x', x \in A -> x == x' -> eq_pos (p1 x) (p2 x')) ->
   eq_pos (P_ConsNoRec A p1) (P_ConsNoRec A' p2)
| EP_Param : forall A A' p1 p2,
   A == A' ->
   (forall x x', x \in A -> x == x' -> eq_pos (p1 x) (p2 x')) ->
   eq_pos (P_Param A p1) (P_Param A' p2).

Instance eq_pos_sym : Symmetric eq_pos.
red; induction 1; constructor; auto with *.
 intros.
 rewrite <- H in H2; rewrite H3 in H2; auto with *.

 intros.
 rewrite <- H in H2; rewrite H3 in H2; auto with *.
Qed.

Instance eq_pos_trans : Transitive eq_pos.
red.
intros x y z ep1 ep2; revert z ep2; induction ep1; intros; inversion_clear ep2;
  constructor; intros; eauto with *.
 transitivity A'; trivial.
 transitivity A'; trivial.

 apply H1 with x; auto with *.
 rewrite H in H4; auto.

 transitivity A'; trivial.

 apply H1 with x; auto with *.
 rewrite H in H4; auto.
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
   (forall x x', x \in A -> x == x' -> eq_pos (p x) (p x')) ->
   (forall x, x \in A -> P (p x)) ->
   P (P_ConsNoRec A p)) ->
  (forall A p,
   (forall x x', x \in A -> x == x' -> eq_pos (p x) (p x')) ->
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

Lemma pos_oper_morph :
  Proper (eq_pos ==> eq_set ==> eq_set) pos_oper.
do 2 red; intros.
red.
induction H; simpl; intros; auto with *.
 apply sum_morph; auto.

 apply prodcart_morph; auto.

 apply sigma_morph; auto with *.

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

 apply sigma_morph; auto.

 apply cc_prod_ext; auto.
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

 apply sigma_morph; intros; auto.
 apply H1; trivial.
  apply cc_prod_elim with (1:=H2); trivial.

  apply cc_app_morph; trivial.
Qed.

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

(* -> ind_w *)
Lemma W_F_morph : Proper (eq_set ==> (eq_set ==> eq_set) ==> eq_set ==> eq_set) W_F.
do 4 red; intros.
unfold W_F.
apply sigma_morph; trivial.
intros.
apply cc_prod_ext; auto with *.
red; trivial.
Qed.

Lemma W_F_ext : forall A A' B B' X X',
  A == A' ->
  eq_fun A B B' ->
  X == X' ->
  W_F A B X == W_F A' B' X'.
unfold W_F; intros.
apply sigma_morph; trivial.
intros.
apply cc_prod_ext; auto with *.
red; auto.
Qed.

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
 2:red; reflexivity.
 rewrite sum_case_inl0.
  apply H.
   rewrite H4; rewrite dest_sum_inl; trivial.
   apply dest_sum_morph; trivial.
  exists x0; rewrite <- H2; trivial.

 rewrite sum_case_inr0; eauto.
 apply cc_prod_ext; intros; auto with *.
 2:red; reflexivity.
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
apply sigma_morph; intros; auto with *.
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
 2:apply iso_fun_sum_sigma; trivial.
  apply W_F_sum_commut; trivial.

  do 2 red; intros; apply cc_prod_ext; intros; auto with *.
  red; reflexivity.

  do 2 red; intros; apply cc_prod_ext; intros; auto with *.
  red; reflexivity.
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
assert (m1 : ext_fun A1 (fun x => cc_prod (B1 x) (fun _ => Y))).
 do 2 red; intros; apply cc_prod_ext; intros; auto with *.
 red; reflexivity.
assert (m1' : ext_fun A2 (fun x => cc_prod (B2 x) (fun _ => Y))).
 do 2 red; intros; apply cc_prod_ext; intros; auto with *.
 red; reflexivity.
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
 apply iso_fun_prodcart_sigma; trivial.

 apply sigma_iso_fun_morph.
  do 2 red; intros.
  apply prodcart_morph.
   apply m1.
    apply fst_typ in H3; trivial.
    apply fst_morph; trivial.
   apply m1'.
    apply snd_typ in H3; trivial.
    apply snd_morph; trivial.

  do 2 red; intros.
  apply cc_prod_ext; auto.
  red; reflexivity.

  red; intros.
  apply prodcart_cc_prod_iso_morph; auto with *.

  apply id_iso_fun.

  intros.
  eapply iso_change_rhs.
  2:apply iso_fun_prodcart_cc_prod.
  2:do 2 red; reflexivity.
  2:do 2 red; reflexivity.
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
 red; reflexivity.
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
  red; reflexivity.

  apply sigma_iso_fun_morph; intros.
   do 2 red; intros.
   apply cc_prod_ext; auto with *.
   red; intros.
   apply cc_prod_ext.
   2:red; reflexivity.
   apply H1; auto with *.
    apply cc_prod_elim with (1:=H4); trivial.
    apply cc_app_morph; auto.

   do 2 red; intros.
   apply cc_prod_ext.
   2:red; reflexivity.
   apply sigma_morph; intros; auto with *.
   apply H1; trivial.
    apply cc_prod_elim with (1:=H4); trivial.
    apply cc_app_morph; auto.

   red; intros.
   unfold cc_prod_isocurry.
   apply cc_lam_ext.
    apply sigma_morph; intros; auto with *.
    apply H1; trivial.
     apply cc_prod_elim with (1:=H4); trivial.
     apply cc_app_morph; auto.

    red; intros.
    rewrite H7; rewrite H9; reflexivity.

   apply id_iso_fun.

   eapply iso_change_rhs.
   2:apply cc_prod_curry_iso_fun.
    apply cc_prod_ext.
    2:red; reflexivity.
    apply sigma_morph; intros; auto with *.
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
  eq_pos p p' -> eq_fun X f f' -> typ_fct f X Y ->
  eq_fun (pos_oper p X) (trad_pos_w f p) (trad_pos_w f' p') /\ 
  typ_fct (trad_pos_w f p) (pos_oper p X) (W_F (pos_to_w1 p) (pos_to_w2 p) Y).
intros X Y f f' p p' eqp ef tyf.
induction eqp; try (destruct IHeqp1; destruct IHeqp2||destruct IHeq_pos);
  simpl; split; intros.
 (* Cst *)
 unfold trad_cst; red; intros.
 unfold sigma_1r_iso.
 apply couple_morph; auto with *.

 unfold trad_cst.
 apply sigma_1r_iso_typ; intros.
  do 2 red; intros.
  apply cc_prod_ext; auto with *.
  red; reflexivity.

  apply cc_prod_intro; intros; auto with *.
  apply empty_ax in H1; contradiction.

 (* Rec *)
 unfold trad_reccall, comp_iso; red; intros.
 apply couple_morph; auto with *.
 apply cc_lam_ext; auto with *.
 red; auto.

 unfold trad_reccall, comp_iso.
 red; intros.
 apply couple_intro_sigma.
  do 2 red; intros.
  apply cc_prod_ext; auto with *.
  red; reflexivity.

  apply singl_intro.

  apply cc_prod_intro; intros; auto with *.

 (* Sum *)
 unfold trad_sum.
 eapply comp_iso_eq_fun.
  apply sum_isomap_typ with (1:=H0) (2:=H2).

  apply sum_isomap_morph; trivial.

  red; intros; apply sum_sigma_iso_morph; trivial.

 apply eq_pos_left in eqp1; apply eq_pos_left in eqp2.
 unfold trad_sum.
 eapply comp_iso_typ.
  apply sum_isomap_typ with (1:=H0) (2:=H2).

  rewrite <- W_F_sum_commut.
  2:apply pos_to_w2_morph'; trivial.
  2:apply pos_to_w2_morph'; trivial.
  apply sum_sigma_iso_typ.
   do 2 red; intros; apply cc_prod_ext;[|red; reflexivity].
   apply pos_to_w2_morph'; trivial.

   do 2 red; intros; apply cc_prod_ext;[|red; reflexivity].
   apply pos_to_w2_morph'; trivial.

 (* ConsRecArg *)
 unfold trad_prodcart.
 eapply comp_iso_eq_fun.
  intros x tyx; rewrite sigma_nodep in tyx; revert x tyx.
  apply sigma_isomap_typ with (B':=fun _ => W_F (pos_to_w1 q1) (pos_to_w2 q1) Y);
    auto with *. 
  eassumption.

  intros x x' tyx; rewrite sigma_nodep in tyx; revert x x' tyx.
  apply sigma_isomap_morph; auto with *.
 eapply comp_iso_eq_fun.
  intros x tyx; rewrite <- sigma_nodep in tyx; revert x tyx.
  apply prodcart_sigma_iso_typ.
   do 2 red; intros; apply cc_prod_ext; [|red;reflexivity].
   apply eq_pos_left in eqp1; apply pos_to_w2_morph';trivial.
   do 2 red; intros; apply cc_prod_ext; [|red;reflexivity].
   apply eq_pos_left in eqp2; apply pos_to_w2_morph';trivial.

  red; intros; unfold prodcart_sigma_iso.
  rewrite H4; reflexivity.

  apply sigma_isomap_morph; intros.
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

 apply eq_pos_left in eqp1; apply eq_pos_left in eqp2.
 unfold trad_prodcart.
 eapply comp_iso_typ.
  apply sigma_isomap_typ_prod; [apply H0|apply H2].
 eapply comp_iso_typ.
  apply prodcart_sigma_iso_typ.
   do 2 red; intros; apply cc_prod_ext;[|red; reflexivity].
   apply pos_to_w2_morph; trivial.

   do 2 red; intros; apply cc_prod_ext;[|red; reflexivity].
   apply pos_to_w2_morph; trivial.

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
 assert (pm : forall x x', x \in A -> x == x' -> eq_pos (p1 x) (p1 x')).
  intros.
  transitivity (p2 x'0); auto with *.
  symmetry; apply H0; auto with *.
  rewrite <- H5; trivial.
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

 assert (pm : forall x x', x \in A -> x == x' -> eq_pos (p1 x) (p1 x')).
  intros.
  transitivity (p2 x'); auto.
  symmetry; apply H0; auto with *.
  rewrite <- H3; trivial.
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
 assert (pm : forall x x', x \in A -> x == x' -> eq_pos (p1 x) (p1 x')).
  intros.
  transitivity (p2 x'); auto.
  symmetry; apply H0; auto with *.
  rewrite <- H3; trivial.
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

  apply cc_prod_isomap_morph; intros; auto with *.
   do 2 red; intros; apply pos_oper_morph; auto with *.
   red; trivial.
   apply H1; trivial.
 eapply comp_iso_eq_fun.
  apply cc_prod_sigma_iso_typ.
   do 2 red; intros; apply pos_to_w1_morph; auto.

   red; intros; apply cc_prod_ext;[|red;reflexivity].
   apply pos_to_w2_morph; auto with *.

  red; intros; apply cc_prod_sigma_iso_morph; trivial.

  apply sigma_isomap_morph; auto with *.
   do 2 red; intros; apply cc_prod_ext; auto with *.
   red; intros; apply cc_prod_ext;[|red; reflexivity].
   apply pos_to_w2_morph; auto with *.
    apply cc_prod_elim with (1:=H2); trivial.
    apply cc_app_morph; trivial.

   red; trivial.

   unfold cc_prod_isocurry; intros.
   apply cc_lam_ext; auto with *.
    apply sigma_morph; intros; auto.
    apply pos_to_w2_morph; auto with *.
     apply cc_prod_elim with (1:=H2); trivial.
     apply cc_app_morph; trivial.
    red; intros.
    rewrite H5; rewrite H7; reflexivity.

 assert (pm : forall x x', x \in A -> x == x' -> eq_pos (p1 x) (p1 x')).
  intros.
  transitivity (p2 x'); auto.
  symmetry; apply H0; auto with *.
  rewrite <- H3; trivial.
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
     rewrite <- H3; trivial.

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
    apply cc_prod_elim with (1:=H2); trivial.
    apply cc_app_morph; trivial.

   do 2 red; intros.
   apply cc_prod_ext; [|red;reflexivity].
   apply sigma_morph; intros; auto with *.
   apply pos_to_w2_morph; auto.
    apply cc_prod_elim with (1:=H2); trivial.
    apply cc_app_morph; trivial.

   red; trivial.

   intros.
   apply cc_prod_isocurry_typ.
    do 2 red; intros.
    apply pos_to_w2_morph; auto with *.
     apply cc_prod_elim with (1:=H2); trivial.
     apply cc_app_morph; auto with *.

    red; reflexivity.
Qed.

Lemma trad_pos_w_morph : forall X f f' p p',
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
  typ_fct f X Y ->
  typ_fct (trad_pos_w f p) (pos_oper p X) (W_F (pos_to_w1 p) (pos_to_w2 p) Y).
intros.
apply trad_pos_w_morph_gen with (1:=H)(2:=H0)(3:=H1).
Qed.

Lemma trad_w_iso_fun :
  forall X Y f p,
  eq_pos p p -> iso_fun X Y f ->
  iso_fun (pos_oper p X) (W_F (pos_to_w1 p) (pos_to_w2 p) Y) (trad_pos_w f p).
intros X Y f p eqp isof.
set (p':=p) in eqp at 2.
assert (tyf := iso_typ isof).
assert (fm := iso_funm isof).
induction eqp; simpl; intros.
 (* Cst *)
 apply iso_cst.

 (* Rec *)
 apply iso_reccall; trivial.

 (* Sum *)
 apply eq_pos_left in eqp1.
 apply eq_pos_left in eqp2.
 apply iso_sum; trivial.
  apply pos_to_w2_morph'; trivial.
  apply pos_to_w2_morph'; trivial.

 (* ConsRecArg *)
 apply eq_pos_left in eqp1.
 apply eq_pos_left in eqp2.
 apply iso_prodcart; trivial.
  apply pos_to_w2_morph'; trivial.
  apply pos_to_w2_morph'; trivial.

 (* ConsNonRecArg *)
 assert (pm : forall x x', x \in A -> x == x' -> eq_pos (p1 x) (p1 x')).
  intros.
  transitivity (p2 x'); auto.
  symmetry; apply H0; auto with *.
  rewrite <- H3; trivial.
 apply iso_arg_norec with (B:=fun x => pos_to_w2 (p1 x)); intros.
  do 2 red; intros.
  apply pos_oper_morph; auto with *.

  do 2 red; intros; apply pos_to_w1_morph; auto with *.

  red; intros; apply pos_to_w2_morph; auto with *.

  red; intros.
  apply (trad_pos_w_morph X); auto with *.

  apply (H1 x x); auto with *. 

 (* Param *)
 assert (pm : forall x x', x \in A -> x == x' -> eq_pos (p1 x) (p1 x')).
  intros.
  transitivity (p2 x'); auto with *.
  symmetry; apply H0; auto with *.
  rewrite <- H3; trivial.
 apply iso_param with (B:=fun x => pos_to_w2 (p1 x)); intros.
  do 2 red; intros.
  apply pos_oper_morph; auto with *.

  do 2 red; intros; apply pos_to_w1_morph; auto with *.

  red; intros; apply pos_to_w2_morph; auto with *.

  red; intros.
  apply (trad_pos_w_morph X); auto with *.

  apply (H1 x x); auto with *. 
Qed.

Lemma trad_w_iso_id :
  forall X p,
  eq_pos p p ->
  iso_fun (pos_oper p X) (W_F (pos_to_w1 p) (pos_to_w2 p) X)
    (trad_pos_w (fun x => x) p).
intros.
apply trad_w_iso_fun; trivial.
apply id_iso_fun.
Qed.



(***************************************)
(*
Fixpoint pos_map p f :=
  match p with
  | P_Cst A => (fun x => x)
  | P_Rec => f
  | P_Sum p1 p2 => sum_isomap (pos_map p1 f) (pos_map p2 f)
  | P_ConsRec p1 p2 => sigma_isomap (pos_map p1 f) (fun _ => pos_map p2 f)
  | P_ConsNoRec A p => sigma_isomap (fun x => x) (fun a => pos_map (p a) f)
  | P_Param A p => cc_prod_isomap A (fun x => x) (fun a => pos_map (p a) f)
  end.

  Lemma pos_map_typ : forall p p' X Y f f',
    eq_pos p p' ->
    eq_fun X f f' ->
    typ_fct f X Y ->
    eq_fun (pos_oper p X) (pos_map p f) (pos_map p' f') /\
    typ_fct (pos_map p f) (pos_oper p X) (pos_oper p Y).
intros p p' X Y f f' eqp eqf tyf.
induction eqp; simpl; try (destruct IHeqp1;destruct IHeqp2); split; trivial; intros.
 (* Cst *)
 red; trivial.
 red; trivial.

 (* Sum *)
 apply sum_isomap_morph; trivial.

 apply sum_isomap_typ; trivial.

 (* prodcart *)
 intros x x' tyx; rewrite sigma_nodep in tyx; revert x x' tyx.
 apply sigma_isomap_morph; intros; auto with *.

 do 2 rewrite sigma_nodep.
 apply sigma_isomap_typ; auto with *.

 (* sigma *)
 apply sigma_isomap_morph; intros; auto with *.
  do 2 red; intros; apply pos_oper_morph; auto with *.
  transitivity (p2 x'); auto with *.
  rewrite H3 in H2; symmetry; auto with *.

  red; trivial.

  apply H1; trivial.

 apply sigma_isomap_typ.
  do 2 red; intros; apply pos_oper_morph; auto with *.
  transitivity (p2 x'); auto with *.
  rewrite H3 in H2; symmetry; auto with *.

  do 2 red; intros; apply pos_oper_morph; auto with *.
  transitivity (p2 x'); auto with *.
  rewrite H3 in H2; symmetry; auto with *.

  red; trivial.

  intros; apply (H1 x x); auto with *.

 (* cc_prod *)
 apply cc_prod_isomap_morph; intros; auto with *.
  do 2 red; intros; apply pos_oper_morph; auto with *.
  transitivity (p2 x'); auto with *.
  rewrite H3 in H2; symmetry; auto with *.

  red; trivial.

  apply H1; trivial.

 apply cc_prod_isomap_typ.
  do 2 red; intros; apply pos_oper_morph; auto with *.
  transitivity (p2 x'); auto with *.
  rewrite H3 in H2; symmetry; auto with *.

  do 2 red; trivial.

  red; intros.
  transitivity (pos_map (p2 x') f' y');[|symmetry]; apply H1; auto with *.
   rewrite <- H3; trivial.
   rewrite <- H5; revert H4; apply eq_elim; apply pos_oper_morph; auto with *.
   transitivity (p2 x'); auto with *.
   rewrite H3 in H2; symmetry; auto with *.

  red; trivial.

  intros; apply (H1 x x); auto with *.
Qed.

  Lemma pos_map_iso : forall p X Y f,
    eq_pos p p ->
    iso_fun X Y f ->
    iso_fun (pos_oper p X) (pos_oper p Y) (pos_map p f).
intros p X Y f eqp isof.
set (p':=p) in eqp at 2.
induction eqp; simpl; intros; trivial.
 (* Cst *)
 apply id_iso_fun.

 (* Sum *)
 apply sum_iso_fun_morph; trivial.

 (* prodcart *)
 apply prodcart_iso_fun_morph; trivial.

 (* sigma *)
 assert (pm : forall x x', x \in A -> x == x' -> eq_pos (p1 x) (p1 x')).
  intros.
  transitivity (p2 x'); auto.
  symmetry; apply H0; auto with *.
  rewrite <- H3; trivial.
 apply sigma_iso_fun_morph with (4:=id_iso_fun _); intros.
  do 2 red; intros; apply pos_oper_morph; auto with *.
  do 2 red; intros; apply pos_oper_morph; auto with *.

  red; intros.
  apply pos_map_typ with (1:=pm _ _ H2 H3) (2:=iso_funm isof) (3:=iso_typ isof);
    auto with *.

  eapply iso_change_rhs.
  2:apply (H1 x x); auto with *.
  apply pos_oper_morph; auto with *.

 (* cc_prod *)
 assert (pm : forall x x', x \in A -> x == x' -> eq_pos (p1 x) (p1 x')).
  intros.
  transitivity (p2 x'); auto.
  symmetry; apply H0; auto with *.
  rewrite <- H3; trivial.
 apply cc_prod_iso_fun_morph with (4:=id_iso_fun _); intros.
  do 2 red; intros; apply pos_oper_morph; auto with *.
  do 2 red; intros; apply pos_oper_morph; auto with *.

  red; intros.
  apply pos_map_typ with (1:=pm _ _ H2 H3) (2:=iso_funm isof) (3:=iso_typ isof);
    auto with *.

  apply (H1 x x); auto with *.
Qed.

Lemma pos_map_comp : forall p f g x X,
  x \in pos_oper p X ->
  pos_map p g (pos_map p f x) == pos_map p (comp_iso f g) x.
Admitted.

Lemma pos_map_eta : forall p X x,
  x \in pos_oper p X ->
  x == pos_map p (fun x => x) x.
Admitted.

*)


Section Iso.

  Variable p : positive.
  Hypothesis p_ok : eq_pos p p.

  Let Wpf := pos_oper p.
  Let Wp := W (pos_to_w1 p) (pos_to_w2 p).
(*  Let Ws f a := Wsup (pos_to_w2 p) (trad_pos_w f p a).*)
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

(*
  Lemma Ws0_iso : forall X, X \incl Wd ->
    iso_fun (pos_oper p X) (Wf (pos_to_w1 p) (pos_to_w2 p) X) Ws0.
intros.
assert (Wsinj :
   forall x x', x \in pos_oper p X -> x' \in pos_oper p X -> Ws0 x == Ws0 x' -> x == x').
 intros.
 apply Wsup_inj with (A:=pos_to_w1 p) (X:=X) (Y:=X) in H2; trivial.
  apply (iso_inj (trad_w_iso_id X p p_ok)) in H2; trivial. 

  apply (iso_typ (trad_w_iso_id X p p_ok)); trivial.

  apply (iso_typ (trad_w_iso_id X p p_ok)); trivial.
constructor; intros; auto.
 do 2 red; intros.
 eapply Wsup_morph with (A:=pos_to_w1 p); trivial.
  eapply (iso_typ (trad_w_iso_id X p p_ok)); trivial.

  apply (iso_funm (trad_w_iso_id X p p_ok)); trivial.

 apply Wf_intro; trivial.
 apply (trad_pos_w_morph X X (fun x => x) (fun x => x) p p); auto with *.
 red; trivial.

 apply Wf_elim in H0; trivial.
 destruct H0.
 destruct (iso_surj (trad_w_iso_id X p p_ok)) with x; trivial.
 exists x0; trivial.
 rewrite H1.
 eapply Wsup_morph with (A:=pos_to_w1 p); trivial.
 apply (iso_typ (trad_w_iso_id X p p_ok)); trivial.
Qed.
*)
(*
  Lemma Ws_iso : forall X Y f, Y \incl Wd ->
    iso_fun X Y f ->
    iso_fun (pos_oper p X) (Wff Y) (Ws f).
intros X Y f H isof.
change (Ws f) with (comp_iso (trad_pos_w f p) (Wsup (pos_to_w2 p))).
eapply iso_fun_trans.
 apply trad_w_iso_fun with (2:=isof); trivial.

 constructor; intros.
  apply Wsup_morph; trivial.

  apply Wf_intro; trivial.

  apply Wsup_inj with (2:=H)(3:=H) in H2; trivial.

  apply Wf_elim in H0; trivial.
  destruct H0; eauto with *.
Qed.
*)

  Definition IND_clos_ord := W_ord (pos_to_w1 p) (pos_to_w2 p).
  Definition IND := INDi p IND_clos_ord.

(***************************************)
(*
Require Import ZFfixfuntyp.

Parameter trF : (set -> set) -> set -> set .
Parameter trF_typ : forall X Y x g,
  ext_fun X g ->
  X \incl Wd ->
  (forall x, x \in X -> g x \in Y) ->
  x \in Wff X ->
  trF g x \in pos_oper p Y.
Parameter trF_inj : forall X Y g g' x x',
    X \incl Wd -> Y \incl Wd ->
    x \in Wff X -> x' \in Wff Y ->
    ext_fun X g -> ext_fun Y g' ->
    (forall a a', a \in X -> a' \in Y -> g a == g' a' -> a == a') ->
    trF g x == trF g' x' -> x == x'.
Parameter Gm_prf : forall (x x' : set) (g g' : set -> set),
   x \in Wp->
   eq_fun (fsub Wff Wd x) g g' ->
   x == x' ->
   trF g x == trF g' x'.
Hint Resolve Gm_prf.

  Definition trad := Fix_rec Wff Wd trF.

Require Import ZFrepl.

Instance trad_morph : morph1 trad.
red; red; intros.
unfold trad.
unfold Fix_rec.
apply uchoice_morph_raw; red; intros.
apply Ffix_rel_morph; trivial.
Qed.

  Lemma trad_ok : forall o,
    isOrd o ->
    forall x,
    x \in TI Wff o ->
    trad x \in TI Wpf o.
intros o oo.
apply isOrd_ind with (2:=oo); intros.
unfold trad.
rewrite Fr_eqn with (o:=y); auto.
apply TI_Wf_elim in H2; trivial.
destruct H2 as (o',?,(x',?,?)).
assert (oo' : isOrd o').
 apply isOrd_inv with y; trivial.
apply TI_intro with o'; auto.
 apply Fmono_morph; apply sp_mono; trivial.

 apply trF_typ with (TI Wff o'); auto with *.
  transitivity Wp; [apply Wi_W|apply Wtyp]; trivial.

  rewrite H4.
  rewrite <- TI_mono_succ; auto.
  apply Wsup_typ; trivial.
Qed.


  Lemma trad_inj : forall o,
    isOrd o ->
    forall x y o', x \in TI Wff o ->
    isOrd o' ->
    y \in TI Wff o' ->
    trad x == trad y -> x == y.
intros o oo.
apply isOrd_ind with (2:=oo).
intros o1 ord1 _ Hrec x y o2 xty ord2 yty eqtr.
unfold trad in eqtr.
rewrite Fr_eqn with (o:=o1) in eqtr; auto.
rewrite Fr_eqn with (o:=o2) in eqtr; auto.
apply TI_Wf_elim in xty; trivial.
destruct xty as (o1', ?, (c1,?,?)).
apply TI_Wf_elim in yty; trivial.
destruct yty as (o2', ?, (c2,?,?)).
apply trF_inj with (TI Wff o1') (TI Wff o2') trad trad; auto with *.
 transitivity Wp; [apply Wi_W|apply Wtyp];eauto using isOrd_inv.
 transitivity Wp; [apply Wi_W|apply Wtyp];eauto using isOrd_inv.

 rewrite <- TI_mono_succ; eauto using isOrd_inv.
 rewrite H1; apply Wsup_typ; eauto using isOrd_inv.

 rewrite <- TI_mono_succ; eauto using isOrd_inv.
 rewrite H4; apply Wsup_typ; eauto using isOrd_inv.

 intros.
 apply Hrec with o1' o2'; eauto using isOrd_inv.
Qed.


  Definition trad1 := iso_inv Wp trad.

  Lemma trad_iso : forall o,
    isOrd o ->
    iso_fun (TI Wff o) (TI Wpf o) trad.
intros o oo.
apply isOrd_ind with (2:=oo); intros o'; intros.
constructor; intros; auto with *.
 apply trad_ok; trivial.

 apply trad_inj with (o:=o') (o':=o') in H4; trivial.

 apply TI_elim in H2; auto with *.
 2:apply Fmono_morph; apply sp_mono; trivial.
 destruct H2.
 specialize H1 with (1:=H2).
 assert (iso_fun (Wff (TI Wff x)) (Wpf (TI Wpf x)) (trF (iso_inv (TI Wff x) trad))).
  admit.
 exists (iso_inv (Wff (TI Wff x)) (trF (iso_inv (TI Wff x) trad)) y).
  apply TI_intro with x; auto.
  apply iso_inv_typ with (1:=H4); trivial.

  unfold trad; rewrite Fr_eqn with (o:=o'); fold trad; auto with *.


assert (ty_tr_y : Ws' trad1 y \in TI Wff o').
 apply TI_intro with x; auto with *.
 rewrite <- TI_mono_succ; eauto using isOrd_inv.
 apply Wsup_typ; eauto using isOrd_inv.
 apply (trad_pos_w_morph (TI Wpf x) (TI Wff x) trad1 trad1 _ _ p_ok); trivial.
  red; intros; apply union_morph.
  apply subset_morph; auto with *.
  red; intros.
  rewrite H5; reflexivity.

  red; intros.
  apply H1; trivial.
assert (trad (Ws' trad1 y ) == y).
 unfold trad; rewrite Fr_eqn with (o:=o'); fold trad; auto with *.
 unfold trF.
 transitivity (WFmap trad (WFmap trad1 y)).
  apply WFmap_morph with (TI Wf x); auto with *.
   red; intros; apply trad_morph; trivial.

   rewrite Wsupi_def with (TI Wf x).
    apply WFmap_typ with (TI W_F x); auto with *.
    intros.
    apply H1; trivial.

    apply WFmap_typ with (TI W_F x); auto with *.
    intros.
    apply H1; trivial.

   transitivity W; [apply Wi_W; eauto using isOrd_inv|apply Wtyp].

   apply Wsupi_def with (TI Wf x).
    apply WFmap_typ with (TI W_F x); auto with *.
    intros.
    apply H1; trivial.

    transitivity W; [apply Wi_W; eauto using isOrd_inv|apply Wtyp].

  generalize (WF_eta _ _ H3); intro.
  apply @transitivity with (3:=symmetry H4); auto with *.
  rewrite WFmap_comp with (TI W_F x) (TI Wf x); auto with *.
   apply WFmap_ext; auto with *.
    apply fst_typ_sigma in H3; trivial.

    intros.
    rewrite <- H6.
    apply H1 with x; trivial.
    apply cc_prod_elim with (1:=tys _ _ H3); trivial.

   intros.
   apply H1; trivial.
assert (trad1 y == Wsup (WFmap trad1 y)).
 apply union_subset_singl with (y':=Wsup (WFmap trad1 y));
   intros; auto with *.
  apply Wi_W with o'; trivial.

  unfold W in H5,H6.
  rewrite Ffix_def in H5,H6; auto with *.
  destruct H5; destruct H6.
  rewrite <- H8 in H7; apply trad_inj with (o:=x0) (o':=x1) in H7; trivial. 

rewrite H5; auto.

 exists (
 apply morph_is_ext; 
apply TI_elim in H2; auto with *.
2:apply Fmono_morph; apply sp_mono; trivial.
destruct H2.
assert (ty_tr_y : Ws' trad1 y \in TI Wff o').



  Instance trad1m : morph1 trad1.
do 2 red; intros.
unfold trad1.
apply union_morph.
apply subset_morph.
 reflexivity.

 red; intros.
 rewrite H; reflexivity.
Qed.

  Lemma trad_surj : forall o,
    isOrd o ->
    forall y,
    y \in TI Wpf o ->
    trad1 y \in TI Wff o /\ trad (trad1 y) == y.
intros o oo.
apply isOrd_ind with (2:=oo); intros o'; intros.
apply TI_elim in H2; auto with *.
2:apply Fmono_morph; apply sp_mono; trivial.
destruct H2.
assert (ty_tr_y : Ws' trad1 y \in TI Wff o').
 apply TI_intro with x; auto with *.
 rewrite <- TI_mono_succ; eauto using isOrd_inv.
 apply Wsup_typ; eauto using isOrd_inv.
 apply (trad_pos_w_morph (TI Wpf x) (TI Wff x) trad1 trad1 _ _ p_ok); trivial.
  red; intros; apply union_morph.
  apply subset_morph; auto with *.
  red; intros.
  rewrite H5; reflexivity.

  red; intros.
  apply H1; trivial.
assert (trad (Ws' trad1 y ) == y).
 unfold trad; rewrite Fr_eqn with (o:=o'); fold trad; auto with *.
 unfold trF.
 transitivity (WFmap trad (WFmap trad1 y)).
  apply WFmap_morph with (TI Wf x); auto with *.
   red; intros; apply trad_morph; trivial.

   rewrite Wsupi_def with (TI Wf x).
    apply WFmap_typ with (TI W_F x); auto with *.
    intros.
    apply H1; trivial.

    apply WFmap_typ with (TI W_F x); auto with *.
    intros.
    apply H1; trivial.

   transitivity W; [apply Wi_W; eauto using isOrd_inv|apply Wtyp].

   apply Wsupi_def with (TI Wf x).
    apply WFmap_typ with (TI W_F x); auto with *.
    intros.
    apply H1; trivial.

    transitivity W; [apply Wi_W; eauto using isOrd_inv|apply Wtyp].

  generalize (WF_eta _ _ H3); intro.
  apply @transitivity with (3:=symmetry H4); auto with *.
  rewrite WFmap_comp with (TI W_F x) (TI Wf x); auto with *.
   apply WFmap_ext; auto with *.
    apply fst_typ_sigma in H3; trivial.

    intros.
    rewrite <- H6.
    apply H1 with x; trivial.
    apply cc_prod_elim with (1:=tys _ _ H3); trivial.

   intros.
   apply H1; trivial.
assert (trad1 y == Wsup (WFmap trad1 y)).
 apply union_subset_singl with (y':=Wsup (WFmap trad1 y));
   intros; auto with *.
  apply Wi_W with o'; trivial.

  unfold W in H5,H6.
  rewrite Ffix_def in H5,H6; auto with *.
  destruct H5; destruct H6.
  rewrite <- H8 in H7; apply trad_inj with (o:=x0) (o':=x1) in H7; trivial. 

rewrite H5; auto.



assert (ty_tr_y : Wsup (WFmap trad1 y) \in TI Wf o').
 apply TI_intro with x; auto with *.
 rewrite <- TI_mono_succ; eauto using isOrd_inv.
 apply Wsup_typ; eauto using isOrd_inv.
 apply WFmap_typ with (TI W_F x); auto with *.
 intros.
 apply H1; trivial.
assert (trad (Wsup (WFmap trad1 y)) == y).
 unfold trad; rewrite Fr_eqn with (o:=o'); fold trad; auto with *.
 unfold trF.
 transitivity (WFmap trad (WFmap trad1 y)).
  apply WFmap_morph with (TI Wf x); auto with *.
   red; intros; apply trad_morph; trivial.

   rewrite Wsupi_def with (TI Wf x).
    apply WFmap_typ with (TI W_F x); auto with *.
    intros.
    apply H1; trivial.

    apply WFmap_typ with (TI W_F x); auto with *.
    intros.
    apply H1; trivial.

   transitivity W; [apply Wi_W; eauto using isOrd_inv|apply Wtyp].

   apply Wsupi_def with (TI Wf x).
    apply WFmap_typ with (TI W_F x); auto with *.
    intros.
    apply H1; trivial.

    transitivity W; [apply Wi_W; eauto using isOrd_inv|apply Wtyp].

  generalize (WF_eta _ _ H3); intro.
  apply @transitivity with (3:=symmetry H4); auto with *.
  rewrite WFmap_comp with (TI W_F x) (TI Wf x); auto with *.
   apply WFmap_ext; auto with *.
    apply fst_typ_sigma in H3; trivial.

    intros.
    rewrite <- H6.
    apply H1 with x; trivial.
    apply cc_prod_elim with (1:=tys _ _ H3); trivial.

   intros.
   apply H1; trivial.
assert (trad1 y == Wsup (WFmap trad1 y)).
 apply union_subset_singl with (y':=Wsup (WFmap trad1 y));
   intros; auto with *.
  apply Wi_W with o'; trivial.

  unfold W in H5,H6.
  rewrite Ffix_def in H5,H6; auto with *.
  destruct H5; destruct H6.
  rewrite <- H8 in H7; apply trad_inj with (o:=x0) (o':=x1) in H7; trivial. 

rewrite H5; auto.
Qed.







  Definition Wsupi x :=
     union (subset (W_F Wdom) (fun y => Wsup y == x)).

  Instance Wsupi_morph : morph1 Wsupi.
do 2 red; intros.
unfold Wsupi.
apply union_morph; apply subset_morph; auto with *.
red; intros.
rewrite H; reflexivity.
Qed.

  Lemma Wsupi_def : forall X x,
    x \in W_F X ->
    X \incl Wdom ->
    Wsupi (Wsup x) == x.
unfold Wsupi; intros.
apply union_subset_singl with (y':=x); auto with *.
 revert H; apply W_F_mono; auto.

 intros.
 rewrite <- H4 in H3.
 apply Wsup_inj with (X:=Wdom) (Y:=Wdom) in H3; auto with *.
Qed.

(* translation Wf X --> W_F Y given translation g:X-->Y *)
  Definition trF g x := WFmap g (Wsupi x).

  Lemma trF_decomp : forall X g x y,
    ext_fun X g ->
    x \in W_F X ->
    X \incl Wdom ->
    y == Wsup x ->
    trF g y == WFmap g x.
intros.
unfold trF.
assert (Wsupi y == x).
 rewrite H2.
 apply Wsupi_def with X; auto with *.
apply (WFmap_morph X); trivial.
 rewrite H3; trivial.
Qed.

Lemma Wfsub_intro : forall X x i,
  x \in W_F X ->
  X \incl Wdom ->
  i \in B (fst x) ->
  cc_app (snd x) i \in fsub Wf Wdom (Wsup x).
intros.
apply subset_intro.
 apply H0.
 apply cc_prod_elim with (1:=tys _ _ H); trivial.

 intros.
 apply Wf_elim in H3.
 destruct H3.
 apply Wsup_inj with (X:=X)(Y:=X0) in H4; auto.
 rewrite <- H4 in H3.
 apply cc_prod_elim with (1:=tys _ _ H3); trivial.
Qed. 

Let Gm_prf : forall (x x' : set) (g g' : set -> set),
   x \in W ->
   eq_fun (fsub Wf Wdom x) g g' ->
   x == x' ->
   trF g x == trF g' x'.
intros.
unfold trF.
apply WFmap_ext.
 rewrite W_eqn in H.
 apply Wf_elim in H.
 destruct H.
 rewrite H2.
 rewrite Wsupi_def with W; trivial.
  apply fst_typ_sigma in H; trivial.
  apply Wtyp.

 rewrite H1; reflexivity.

 intros.
 unfold W in H; rewrite Ffix_def in H; auto with *.
 destruct H.
 apply TI_Wf_elim in H4; trivial.
 destruct H4.
 destruct H5.
 assert (Wsupi x == x2).
  rewrite H6; rewrite Wsupi_def with (TI Wf x1); auto with *.
  transitivity W; [apply Wi_W; eauto using isOrd_inv|apply Wtyp].
 assert (cc_app (snd (Wsupi x)) i \in fsub Wf Wdom (Wsup (Wsupi x))).
  apply Wfsub_intro with (TI Wf x1); auto with *.
   rewrite H7; trivial.

   transitivity W; [apply Wi_W; eauto using isOrd_inv|apply Wtyp].
 rewrite (fsub_morph Wf Wdom (Wsup (Wsupi x)) x) in H8.
  apply H0; trivial.
  rewrite H1; rewrite H3; reflexivity.

  transitivity (Wsup x2); auto with *.
  symmetry; apply Wsup_morph with (TI Wf x1); auto with *.
Qed.
Hint Resolve Gm_prf.


Lemma trF_typ : forall X Y x g,
  ext_fun X g ->
  X \incl Wdom ->
  (forall x, x \in X -> g x \in Y) ->
  x \in Wf X ->
  trF g x \in W_F Y.
intros.
apply Wf_elim in H2; destruct H2.
rewrite trF_decomp with (2:=H2) (4:=H3); trivial.
apply WFmap_typ with X; trivial.
Qed.

  Lemma trF_inj : forall X Y g g' x x',
    X \incl Wdom -> Y \incl Wdom ->
    x \in Wf X -> x' \in Wf Y ->
    ext_fun X g -> ext_fun Y g' ->
    (forall a a', a \in X -> a' \in Y -> g a == g' a' -> a == a') ->
    trF g x == trF g' x' -> x == x'.
intros X Y g g' x x' Xi Yi H H0 gm g'm H1 H2.
apply Wf_elim in H; destruct H.
apply Wf_elim in H0; destruct H0.
(*rewrite trF_decomp with (2:=H) (3:=H3) in H2; trivial.
  produces ill-typed proof term rejected at Qed *)
rewrite trF_decomp with (2:=H) (4:=H3) in H2; trivial.
rewrite trF_decomp with (2:=H0) (4:=H4) in H2; trivial.
apply WFmap_inj with (X:=X)(Y:=Y) in H2; trivial.
rewrite H3; rewrite H4; apply Wsup_morph with X; auto with *.
Qed.

  Definition trad := Fix_rec Wf Wdom trF.

Instance trad_morph : morph1 trad.
red; red; intros.
unfold trad.
unfold Fix_rec.
apply uchoice_morph_raw; red; intros.
apply Ffix_rel_morph; trivial.
Qed.


  Lemma trad_ok : forall o,
    isOrd o ->
    forall x,
    x \in TI Wf o ->
    trad x \in TI W_F o.
intros o oo.
apply isOrd_ind with (2:=oo); intros.
unfold trad.
rewrite Fr_eqn with (o:=y); auto.
apply TI_Wf_elim in H2; trivial.
destruct H2 as (o',?,(x',?,?)).
assert (oo' : isOrd o').
 apply isOrd_inv with y; trivial.
apply TI_intro with o'; auto.
 apply Fmono_morph; apply W_F_mono.

 apply trF_typ with (TI Wf o'); auto with *.
  transitivity W; [apply Wi_W|apply Wtyp]; trivial.

  rewrite H4.
  rewrite <- TI_mono_succ; auto.
  apply Wsup_typ; trivial.
Qed.


  Lemma trad_inj : forall o,
    isOrd o ->
    forall x y o', x \in TI Wf o ->
    isOrd o' ->
    y \in TI Wf o' ->
    trad x == trad y -> x == y.
intros o oo.
apply isOrd_ind with (2:=oo).
intros o1 ord1 _ Hrec x y o2 xty ord2 yty eqtr.
unfold trad in eqtr.
rewrite Fr_eqn with (o:=o1) in eqtr; auto.
rewrite Fr_eqn with (o:=o2) in eqtr; auto.
apply TI_Wf_elim in xty; trivial.
destruct xty as (o1', ?, (c1,?,?)).
apply TI_Wf_elim in yty; trivial.
destruct yty as (o2', ?, (c2,?,?)).
apply trF_inj with (TI Wf o1') (TI Wf o2') trad trad; auto with *.
 transitivity W; [apply Wi_W|apply Wtyp];eauto using isOrd_inv.
 transitivity W; [apply Wi_W|apply Wtyp];eauto using isOrd_inv.

 rewrite <- TI_mono_succ; eauto using isOrd_inv.
 rewrite H1; apply Wsup_typ; eauto using isOrd_inv.

 rewrite <- TI_mono_succ; eauto using isOrd_inv.
 rewrite H4; apply Wsup_typ; eauto using isOrd_inv.

 intros.
 apply Hrec with o1' o2'; eauto using isOrd_inv.
Qed.

  Definition trad1 y :=
    union (subset W (fun x => trad x == y)).

  Instance trad1m : morph1 trad1.
do 2 red; intros.
unfold trad1.
apply union_morph.
apply subset_morph.
 reflexivity.

 red; intros.
 rewrite H; reflexivity.
Qed.

  Lemma trad_surj : forall o,
    isOrd o ->
    forall y,
    y \in TI W_F o ->
    trad1 y \in TI Wf o /\ trad (trad1 y) == y.
intros o oo.
apply isOrd_ind with (2:=oo); intros o'; intros.
apply TI_elim in H2; auto with *.
2:apply Fmono_morph; apply W_F_mono.
destruct H2.
assert (ty_tr_y : Wsup (WFmap trad1 y) \in TI Wf o').
 apply TI_intro with x; auto with *.
 rewrite <- TI_mono_succ; eauto using isOrd_inv.
 apply Wsup_typ; eauto using isOrd_inv.
 apply WFmap_typ with (TI W_F x); auto with *.
 intros.
 apply H1; trivial.
assert (trad (Wsup (WFmap trad1 y)) == y).
 unfold trad; rewrite Fr_eqn with (o:=o'); fold trad; auto with *.
 unfold trF.
 transitivity (WFmap trad (WFmap trad1 y)).
  apply WFmap_morph with (TI Wf x); auto with *.
   red; intros; apply trad_morph; trivial.

   rewrite Wsupi_def with (TI Wf x).
    apply WFmap_typ with (TI W_F x); auto with *.
    intros.
    apply H1; trivial.

    apply WFmap_typ with (TI W_F x); auto with *.
    intros.
    apply H1; trivial.

   transitivity W; [apply Wi_W; eauto using isOrd_inv|apply Wtyp].

   apply Wsupi_def with (TI Wf x).
    apply WFmap_typ with (TI W_F x); auto with *.
    intros.
    apply H1; trivial.

    transitivity W; [apply Wi_W; eauto using isOrd_inv|apply Wtyp].

  generalize (WF_eta _ _ H3); intro.
  apply @transitivity with (3:=symmetry H4); auto with *.
  rewrite WFmap_comp with (TI W_F x) (TI Wf x); auto with *.
   apply WFmap_ext; auto with *.
    apply fst_typ_sigma in H3; trivial.

    intros.
    rewrite <- H6.
    apply H1 with x; trivial.
    apply cc_prod_elim with (1:=tys _ _ H3); trivial.

   intros.
   apply H1; trivial.
assert (trad1 y == Wsup (WFmap trad1 y)).
 apply union_subset_singl with (y':=Wsup (WFmap trad1 y));
   intros; auto with *.
  apply Wi_W with o'; trivial.

  unfold W in H5,H6.
  rewrite Ffix_def in H5,H6; auto with *.
  destruct H5; destruct H6.
  rewrite <- H8 in H7; apply trad_inj with (o:=x0) (o':=x1) in H7; trivial. 

rewrite H5; auto.
Qed.








  Definition tro :=
    Fix_rec Wff Wd
      (fun f => iso_inv IND (Ws' (iso_inv Wd f))).

  Lemma tro_eqn : forall o x,
  isOrd o ->
  o \incl IND_clos_ord p ->
  x \in TI Wff o ->
  tro x == iso_inv IND (Ws' (iso_inv Wd tro)) x.
intros.
eapply Fr_eqn; intros; eauto with *.
 apply Wf_mono.
 apply pos_to_w2_morph'; trivial.

 apply Wf_typ; trivial.
 apply pos_to_w2_morph'; trivial.

 unfold iso_inv.
 apply union_morph.
 apply subset_morph; auto with *.
 red; intros.
 rewrite H4.
 assert (forall a b c, a==b -> (a == c <-> b == c)).
  split; intros.
  rewrite <- H6; trivial.
  rewrite H6; trivial.
 apply H6; clear H6.
 eapply Wsup_morph.
  apply pos_to_w2_morph'; trivial.

  eapply trad_pos_w_morph.

iso_typ (trad_w_iso_fun _ _ _ _ p_ok (id_)).
 instantiate (1:=Wd).
 refine (iso_typ (trad_w_iso _ _ _ _ p_ok _) _).
  .

 apply eq_set_morph.
 rewrite H4; reflex
 apply iso_inv_morph.

  Definition tro o x y :=
    forall R,
    (forall o', isOrd o' -> o' \incl o ->
     forall x f, x \in TI (pos_oper p) o' ->
     (forall o''forall x', 

lt o' ox, x \in pos_oper 
    R x y

  Lemma iso_trad :
    iso_fun (TI (pos_oper p) (IND_clos_ord p)) (TI Wff (IND_clos_ord p))
      (fun x => union (subset Wd (fun y => 
        forall R, 
        (forall x f, (forall x', x' < x -> R x' (f x')) ->
         R x (sup f 
        R x y.


  Lemma IND_fix : IND == pos_oper p IND.

  Definition trad := Fix_rec Wff Wd
    (fun f x => 
  Definition tro :=
    TIO (fun o f => Ws' (TI (pos_oper p) o) (TI Wff o) f).

  Definition trF g :=
    iso_inv (Ws


(* translation Wf X --> W_F Y given translation g:X-->Y *)
  Definition trF g x := pos_map p g (iso_inv (pos_oper p ..)Wsupi x).

  Lemma trF_decomp : forall X g x y,
    morph1 g ->
    x \in Wf X ->
    X \incl Wd ->
    y == Ws x ->
    trF g y == pos_map p g x.
intros.
unfold trF.

apply WFmap_morph; trivial.
rewrite H2.
apply Wsupi_def with X; auto with *.
Qed.

Lemma Wfsub_intro : forall X x i,
  x \in W_F X ->
  X \incl Wdom ->
  i \in B (fst x) ->
  cc_app (snd x) i \in fsub Wf Wdom (Wsup x).
intros.
apply subset_intro.
 apply H0.
 apply cc_prod_elim with (1:=tys _ _ H); trivial.

 intros.
 apply Wf_elim in H3.
 destruct H3.
 apply Wsup_inj with (X:=X)(Y:=X0) in H4; auto.
 rewrite <- H4 in H3.
 apply cc_prod_elim with (1:=tys _ _ H3); trivial.
Qed. 

Let Gm_prf : forall (x x' : set) (g g' : set -> set),
   x \in W ->
   eq_fun (fsub Wf Wdom x) g g' ->
   x == x' ->
   trF g x == trF g' x'.
intros.
unfold trF.
apply WFmap_ext.
 rewrite H1; reflexivity.

 intros.
 unfold W in H; rewrite Ffix_def in H; auto with *.
 destruct H.
 apply TI_Wf_elim in H4; trivial.
 destruct H4.
 destruct H5.
 assert (Wsupi x == x2).
  rewrite H6; rewrite Wsupi_def with (TI Wf x1); auto with *.
  transitivity W; [apply Wi_W; eauto using isOrd_inv|apply Wtyp].
 assert (cc_app (snd (Wsupi x)) i \in fsub Wf Wdom (Wsup (Wsupi x))).
  apply Wfsub_intro with (TI Wf x1); auto with *.
   rewrite H7; trivial.

   transitivity W; [apply Wi_W; eauto using isOrd_inv|apply Wtyp].
 rewrite (fsub_morph Wf Wdom (Wsup (Wsupi x)) x) in H8.
  apply H0; trivial.
  rewrite H1; rewrite H3; reflexivity.

  rewrite H7; auto with *.
Qed.
Hint Resolve Gm_prf.


Lemma trF_typ : forall X Y x g,
  morph1 g ->
  X \incl Wdom ->
  (forall x, x \in X -> g x \in Y) ->
  x \in Wf X ->
  trF g x \in W_F Y.
intros.
apply Wf_elim in H2; destruct H2.
rewrite trF_decomp with (2:=H2) (4:=H3); trivial.
apply WFmap_typ with X; trivial.
Qed.

  Lemma trF_inj : forall X Y g g' x x',
    X \incl Wdom -> Y \incl Wdom ->
    x \in Wf X -> x' \in Wf Y ->
    morph1 g -> morph1 g' ->
    (forall a a', a \in X -> a' \in Y -> g a == g' a' -> a == a') ->
    trF g x == trF g' x' -> x == x'.
intros X Y g g' x x' Xi Yi H H0 gm g'm H1 H2.
apply Wf_elim in H; destruct H.
apply Wf_elim in H0; destruct H0.
(*rewrite trF_decomp with (2:=H) (3:=H3) in H2; trivial.
  produces ill-typed proof term rejected at Qed *)
rewrite trF_decomp with (2:=H) (4:=H3) in H2; trivial.
rewrite trF_decomp with (2:=H0) (4:=H4) in H2; trivial.
apply WFmap_inj with (X:=X)(Y:=Y) in H2; trivial.
rewrite H3; rewrite H4; apply Wsup_morph; auto with *.
Qed.

  Definition trad := Fix_rec Wf Wdom trF.

Instance trad_morph : morph1 trad.
red; red; intros.
unfold trad.
unfold Fix_rec.
apply uchoice_morph_raw; red; intros.
apply Ffix_rel_morph; trivial.
Qed.


  Lemma trad_ok : forall o,
    isOrd o ->
    forall x,
    x \in TI Wf o ->
    trad x \in TI W_F o.
intros o oo.
apply isOrd_ind with (2:=oo); intros.
unfold trad.
rewrite Fr_eqn with (o:=y); auto.
apply TI_Wf_elim in H2; trivial.
destruct H2 as (o',?,(x',?,?)).
assert (oo' : isOrd o').
 apply isOrd_inv with y; trivial.
apply TI_intro with o'; auto.
 apply Fmono_morph; apply W_F_mono.

 apply trF_typ with (TI Wf o'); auto with *.
  transitivity W; [apply Wi_W|apply Wtyp]; trivial.

  rewrite H4.
  rewrite <- TI_mono_succ; auto.
  apply Wsup_typ; trivial.
Qed.

forall F : set -> set,
       Proper (incl_set ==> incl_set) F ->
       forall A : set,
       (forall X : set, X \incl A -> F X \incl A) ->
       forall G : (set -> set) -> set -> set,
       (forall (x x' : set) (g g' : set -> set),
        x \in Ffix F A ->
        eq_fun (fsub F A x) g g' -> x == x' -> G g x == G g' x') ->
       forall a o : set,
       isOrd o -> a \in TI F o -> Fix_rec F A G a == G (Fix_rec F A G) a


  Lemma trad_inj : forall o,
    isOrd o ->
    forall x y o', x \in TI Wf o ->
    isOrd o' ->
    y \in TI Wf o' ->
    trad x == trad y -> x == y.
intros o oo.
apply isOrd_ind with (2:=oo).
intros o1 ord1 _ Hrec x y o2 xty ord2 yty eqtr.
unfold trad in eqtr.
rewrite Fr_eqn with (o:=o1) in eqtr; auto.
rewrite Fr_eqn with (o:=o2) in eqtr; auto.
apply TI_Wf_elim in xty; trivial.
destruct xty as (o1', ?, (c1,?,?)).
apply TI_Wf_elim in yty; trivial.
destruct yty as (o2', ?, (c2,?,?)).
apply trF_inj with (TI Wf o1') (TI Wf o2') trad trad; auto with *.
 transitivity W; [apply Wi_W|apply Wtyp];eauto using isOrd_inv.
 transitivity W; [apply Wi_W|apply Wtyp];eauto using isOrd_inv.

 rewrite <- TI_mono_succ; eauto using isOrd_inv.
 rewrite H1; apply Wsup_typ; eauto using isOrd_inv.

 rewrite <- TI_mono_succ; eauto using isOrd_inv.
 rewrite H4; apply Wsup_typ; eauto using isOrd_inv.

 intros.
 apply Hrec with o1' o2'; eauto using isOrd_inv.
Qed.

  Definition trad1 y :=
    union (subset W (fun x => trad x == y)).

  Instance trad1m : morph1 trad1.
do 2 red; intros.
unfold trad1.
apply union_morph.
apply subset_morph.
 reflexivity.

 red; intros.
 rewrite H; reflexivity.
Qed.

  Lemma trad_surj : forall o,
    isOrd o ->
    forall y,
    y \in TI W_F o ->
    trad1 y \in TI Wf o /\ trad (trad1 y) == y.
intros o oo.
apply isOrd_ind with (2:=oo); intros o'; intros.
apply TI_elim in H2; auto with *.
2:apply Fmono_morph; apply W_F_mono.
destruct H2.
assert (ty_tr_y : Wsup (WFmap trad1 y) \in TI Wf o').
 apply TI_intro with x; auto with *.
 rewrite <- TI_mono_succ; eauto using isOrd_inv.
 apply Wsup_typ; eauto using isOrd_inv.
 apply WFmap_typ with (TI W_F x); auto with *.
 intros.
 apply H1; trivial.
assert (trad (Wsup (WFmap trad1 y)) == y).
 unfold trad; rewrite Fr_eqn with (o:=o'); fold trad; auto with *.
 unfold trF.
 rewrite Wsupi_def with (TI Wf x).
  generalize (WF_eta _ _ H3); intro.
  apply @transitivity with (3:=symmetry H4); auto with *.
  rewrite WFmap_comp; auto with *.
  apply WFmap_ext; auto with *.
  intros.
  rewrite <- H6.
  apply H1 with x; trivial.
  apply cc_prod_elim with (1:=tys _ _ H3); trivial.

  apply WFmap_typ with (TI W_F x); auto with *.
  intros.
  apply H1; trivial.

  transitivity W; [apply Wi_W; eauto using isOrd_inv|apply Wtyp].
assert (trad1 y == Wsup (WFmap trad1 y)).
 apply union_subset_singl with (y':=Wsup (WFmap trad1 y));
   intros; auto with *.
  apply Wi_W with o'; trivial.

  unfold W in H5,H6.
  rewrite Ffix_def in H5,H6; auto with *.
  destruct H5; destruct H6.
  rewrite <- H8 in H7; apply trad_inj with (o:=x0) (o':=x1) in H7; trivial. 

rewrite H5; auto.
Qed.

*)
(********************************************)

  Let WFf := W_F (pos_to_w1 p) (pos_to_w2 p).
  Let Wp2 := W2 (pos_to_w1 p) (pos_to_w2 p).

  Lemma IND_eq : IND == pos_oper p IND.
pose (isow := TI_iso (pos_oper p) (fun f => trad_pos_w f p) IND_clos_ord).
destruct TI_iso_fun with 
  (F:=pos_oper p) (G:=WFf) (g:=fun f => trad_pos_w f p) (o:=IND_clos_ord) as
 (isof, expTI); intros.
  apply stable2_weaker; auto with *.
  apply sp_stable; trivial.

  apply sp_mono; trivial.

  apply W_F_mono; trivial.

  apply trad_pos_w_morph; trivial.

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

End Iso.
