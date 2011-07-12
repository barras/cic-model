Require Import ZF ZFpairs ZFsum ZFrelations ZFcoc ZFord.
Import IZF.
Require Import ZFind_basic.
Require Import ZFstrictpos.

(* Inductive family.
   The strategy is to first remove dependencies, reuse the fixpoint
   construction for inductive types, and then checking dependencies
   a posteriori.
 *)

Section InductiveFamily.

(* Inductive specification *)
Inductive dpositive :=
| DP_Cst (A:set)
| DP_EqInst (j:set) (* Instance built by the constructor *)
| DP_Rec (i:set)    (* Recursive call with a specific instance of the family *)
| DP_Sum (p1 p2:dpositive)
| DP_ConsRec (p1 p2:dpositive)
| DP_ConsNoRec (A:set) (p:set->dpositive)
| DP_Param (A:set) (p:set->dpositive).

(* The index type of the family *)

Variable Arg : set.

Inductive eq_dpos : dpositive -> dpositive -> Prop :=
| EDP_Cst : forall A A', A == A' -> eq_dpos (DP_Cst A) (DP_Cst A')
| EDP_EqInst : forall j j', j \in Arg -> j == j' -> eq_dpos (DP_EqInst j) (DP_EqInst j')
| EDP_Rec : forall i i', i \in Arg -> i == i' -> eq_dpos (DP_Rec i) (DP_Rec i')
| EDP_Sum : forall p1 p2 q1 q2,
   eq_dpos p1 p2 -> eq_dpos q1 q2 -> eq_dpos (DP_Sum p1 q1) (DP_Sum p2 q2)
| EDP_ConsRec : forall p1 p2 q1 q2,
   eq_dpos p1 p2 -> eq_dpos q1 q2 -> eq_dpos (DP_ConsRec p1 q1) (DP_ConsRec p2 q2)
| EDP_ConsNoRec : forall A A' p1 p2,
   A == A' ->
   (forall x x', x == x' -> eq_dpos (p1 x) (p2 x')) ->
   eq_dpos (DP_ConsNoRec A p1) (DP_ConsNoRec A' p2)
| EDP_Param : forall A A' p1 p2,
   A == A' ->
   (forall x x', x == x' -> eq_dpos (p1 x) (p2 x')) ->
   eq_dpos (DP_Param A p1) (DP_Param A' p2).

Instance eq_dpos_sym : Symmetric eq_dpos.
red; induction 1; constructor; auto with *.
 rewrite <- H0; trivial. 

 rewrite <- H0; trivial. 
Qed.

Instance eq_dpos_trans : Transitive eq_dpos.
red.
intros x y z ep1 ep2; revert z ep2; induction ep1; intros; inversion_clear ep2;
  constructor; intros; eauto with *.
 transitivity A'; trivial.

 transitivity j'; trivial.

 transitivity i'; trivial.

 transitivity A'; trivial.

 transitivity A'; trivial.
Qed.

Lemma eq_dpos_left : forall p1 p2, eq_dpos p1 p2 -> eq_dpos p1 p1.
intros.
transitivity p2; trivial.
symmetry; trivial.
Qed.

Lemma dpos_rect : forall (P:dpositive->Type),
  (forall A, P (DP_Cst A)) ->
  (forall j, j \in Arg -> P (DP_EqInst j)) ->
  (forall i, i \in Arg -> P (DP_Rec i)) ->
  (forall p1 p2, eq_dpos p1 p1 -> eq_dpos p2 p2 -> P p1 -> P p2 -> P (DP_Sum p1 p2)) ->
  (forall p1 p2, eq_dpos p1 p1 -> eq_dpos p2 p2 -> P p1 -> P p2 -> P (DP_ConsRec p1 p2)) ->
  (forall A p,
   (forall x x', x == x' -> eq_dpos (p x) (p x')) ->
   (forall x, x \in A -> P (p x)) ->
   P (DP_ConsNoRec A p)) ->
  (forall A p,
   (forall x x', x == x' -> eq_dpos (p x) (p x')) ->
   (forall x, x \in A -> P (p x)) ->
   P (DP_Param A p)) ->
  forall p, eq_dpos p p -> P p.
intros.
induction p; trivial.
 apply X0; inversion_clear H; auto.

 apply X1; inversion_clear H; auto.

 assert (eq_dpos p1 p1 /\ eq_dpos p2 p2) by (inversion H; auto with *).
 destruct H0; auto.

 assert (eq_dpos p1 p1 /\ eq_dpos p2 p2) by (inversion H; auto with *).
 destruct H0; auto.

 apply X4; intros.
  inversion_clear H; auto.

  apply X6.
  inversion H; auto with *.

 apply X5; intros.
  inversion_clear H; auto.

  apply X6.
  inversion H; auto with *.
Defined.


Fixpoint dpos_oper p X a :=
  match p with
  | DP_Cst A => A
  | DP_EqInst j => EQ Arg a j
  | DP_Rec i => X i
  | DP_Sum p1 p2 => sum (dpos_oper p1 X a) (dpos_oper p2 X a)
  | DP_ConsRec p1 p2 => prodcart (dpos_oper p1 X a) (dpos_oper p2 X a)
  | DP_ConsNoRec A p => sigma A (fun x => dpos_oper (p x) X a)
  | DP_Param A p => cc_prod A (fun x => dpos_oper (p x) X a)
  end.


Instance dpos_oper_morph : Proper (eq_dpos ==> (eq_set ==> eq_set) ==> eq_set ==> eq_set) dpos_oper.
do 4 red; intros.
induction H; simpl; intros; trivial.
 apply EQ_morph; auto with *.

 apply H0; trivial.

 apply sum_morph; trivial.

 apply prodcart_morph; trivial.

 apply sigma_morph; trivial.

 apply cc_prod_morph; trivial.
Qed.

Lemma dpos_oper_ext : forall p p' X X',
  eq_dpos p p' -> eq_fun Arg X X' -> eq_fun Arg (dpos_oper p X) (dpos_oper p' X').
red; intros.
induction H; simpl; intros; auto with *.
 apply EQ_morph; auto with *.

 apply sum_morph; auto.

 apply prodcart_morph; auto.

 apply sigma_morph; auto with *.

 apply cc_prod_ext; intros; auto.
 red; auto.
Qed.

Lemma dpos_oper_mono p p' :
  eq_dpos p p' ->
  forall X Y, morph1 X -> morph1 Y ->
  (forall a, a \in Arg -> X a \incl Y a) ->
  forall a, a \in Arg -> dpos_oper p X a \incl dpos_oper p' Y a.
intros eqp X Y Xm Ym Xmono a tya.
induction eqp; simpl; intros; auto with *.
 rewrite H; reflexivity.

 rewrite H0; reflexivity.

 rewrite <- H0; auto.

 apply sum_mono; auto.

 apply prodcart_mono; auto.

 apply sigma_mono; auto with *.
  do 2 red; intros.
  apply dpos_oper_morph; auto with *.
  transitivity (p2 x'); auto with *.
  symmetry.
  rewrite H3 in H2; auto with *.

  do 2 red; intros.
  apply dpos_oper_morph; auto with *.
  rewrite <- H in H2.
  transitivity (p1 x); auto with *.
  symmetry; auto with *.

  rewrite H; reflexivity.

 apply cc_prod_covariant; auto with *.
 do 2 red; intros.
 apply dpos_oper_morph; auto with *.
  rewrite <- H in H2.
  transitivity (p1 x); auto with *.
  symmetry; auto with *.
Qed.

(*
Require Import ZFfixfun.
Lemma dpos_oper_mono p p' :
  eq_dpos p p' ->
  forall X Y, morph1 X -> morph1 Y ->
  incl_fam Arg X Y ->
  incl_fam Arg (dpos_oper p X) (dpos_oper p' Y).
intros eqp X Y Xm Ym Xmono a a' tya eqa.
induction eqp; simpl; intros; auto with *.
 rewrite H; reflexivity.

 rewrite H0; rewrite eqa; reflexivity.

 apply sum_mono; auto.

 apply prodcart_mono; auto.

 apply sigma_mono; auto with *.
  do 2 red; intros.
  apply dpos_oper_morph; auto with *.
  transitivity (p2 x'); auto with *.
  symmetry.
  rewrite H3 in H2; auto with *.

  do 2 red; intros.
  apply dpos_oper_morph; auto with *.
  rewrite <- H in H2.
  transitivity (p1 x); auto with *.
  symmetry; auto with *.

  rewrite H; reflexivity.

 apply cc_prod_covariant; auto with *.
 do 2 red; intros.
 apply dpos_oper_morph; auto with *.
  rewrite <- H in H2.
  transitivity (p1 x); auto with *.
  symmetry; auto with *.
Qed.
*)

(* Erasing dependencies *)
Fixpoint tr_pos p :=
  match p with
  | DP_Cst A => P_Cst A
  | DP_EqInst j => P_Cst (singl empty)
  | DP_Rec i => P_Rec
  | DP_Sum p1 p2 => P_Sum (tr_pos p1) (tr_pos p2)
  | DP_ConsRec p1 p2 => P_ConsRec (tr_pos p1) (tr_pos p2)
  | DP_ConsNoRec A p => P_ConsNoRec A (fun x => tr_pos (p x))
  | DP_Param A p => P_Param A (fun x => tr_pos (p x))
  end.

Instance tr_pos_morph : Proper (eq_dpos ==> eq_pos) tr_pos.
do 2 red; intros.
induction H; simpl; intros; constructor; auto with *.
Qed.

(* Checking dependencies *)
  Inductive instance p a : dpositive -> set -> Prop :=
  | I_Cst A : forall x, x \in A -> instance p a (DP_Cst A) x
  | I_EqInst j : forall z, a == j -> z == empty -> instance p a (DP_EqInst j) z
  | I_Rec i : forall x z, instance p i p x -> z == x -> instance p a (DP_Rec i) z
  | I_Sum1 p1 p2 :
     forall x z,
     instance p a p1 x -> 
     z == inl x ->
     instance p a (DP_Sum p1 p2) z
  | I_Sum2 p1 p2 :
     forall y z,
     instance p a p2 y -> 
     z == inr y ->
     instance p a (DP_Sum p1 p2) z
  | I_ConsRec p1 p2 :
     forall x y z,
     instance p a p1 x -> 
     instance p a p2 y -> 
     z == couple x y ->
     instance p a (DP_ConsRec p1 p2) z
  | I_ConsNoRec A p' :
     forall x y z,
     x \in A ->
     instance p a (p' x) y ->
     z == couple x y ->
     instance p a (DP_ConsNoRec A p') z
  | I_Param A p' :
     forall f g,
     morph1 f ->
     (forall x, x \in A -> instance p a (p' x) (f x)) ->
     g == cc_lam A f ->
     instance p a (DP_Param A p') g.

  Instance instance_morph :
    Proper (eq_dpos ==> eq_set ==> eq_dpos ==> eq_set ==> iff) instance.
apply morph_impl_iff4; auto with *.
do 6 red; intros.
revert y H y0 H0 y1 H1 y2 H2.
induction H3; intros.
 inversion_clear H2.
 apply I_Cst; trivial.
 rewrite H3 in H; rewrite H4 in H; trivial.

 inversion_clear H3.
 rewrite H2 in H; rewrite H4 in H0; rewrite H6 in H,H5.
 apply I_EqInst; trivial.

 inversion_clear H2.
 apply I_Rec with z; auto with *.

 inversion_clear H2.
 rewrite H4 in H.
 apply I_Sum1 with x0; auto with *.

 inversion_clear H2.
 rewrite H4 in H.
 apply I_Sum2 with y; auto with *.

 inversion_clear H2.
 rewrite H3 in H.
 apply I_ConsRec with x0 y; auto with *.

 inversion_clear H4.
 rewrite H6 in H; rewrite H5 in H0.
 apply I_ConsNoRec with x0 y; auto with *.

 inversion_clear H5.
 rewrite H6 in H2.
 apply I_Param with f; trivial.
  intros.
  rewrite <- H7 in H5.
  apply H1 with x0; auto with *.

  rewrite H2; apply cc_lam_morph; auto with *.
Qed.

(* The inductive family *)
  Definition DINDi p o a := subset (INDi (tr_pos p) o) (instance p a p).

  Definition DIND p a := subset (IND (tr_pos p)) (instance p a p).

  Instance DINDi_morph : Proper (eq_dpos ==> eq_set ==> eq_set ==> eq_set) DINDi.
do 4 red; intros.
apply subset_morph.
 apply INDi_morph; trivial.
 apply tr_pos_morph; trivial.

 red; intros.
 apply instance_morph; auto with *.
Qed.

(*
  Instance DIND_morph : Proper (eq_dpos ==> eq_set ==> eq_set) DIND.
do 3 red; intros.
apply subset_morph.
 apply INDi_morph; trivial.
  apply tr_pos_morph; trivial.

  admit.

 red; intros.
 apply instance_morph; auto with *.
Qed.
*)

  Variable p : dpositive.
  Hypothesis eqp : eq_dpos p p.
Let eqp' := tr_pos_morph _ _ eqp.

  Lemma DINDi_mono o o' a :
    isOrd o -> isOrd o' -> o \incl o' ->
    DINDi p o a \incl DINDi p o' a.
intros.
red; intros.
unfold DINDi in H2; rewrite subset_ax in H2; destruct H2.
destruct H3.
rewrite H3; apply subset_intro; trivial.
rewrite <- H3; revert H2; apply INDi_mono; trivial.
Qed.

  Lemma DINDi_eq o : isOrd o -> forall a, a \in Arg ->
    DINDi p (osucc o) a == dpos_oper p (DINDi p o) a.
intros oo a tya.
symmetry; apply subset_ext; intros.
 rewrite INDi_succ_eq in H; trivial.
 revert a tya x H H0.
 pattern p at 1 4 5; elim eqp using dpos_rect; simpl; intros; trivial.
  (* Inst *)
  inversion_clear H1.
  rewrite <- H2; rewrite H3; apply refl_typ; trivial.

  (* Rec *)
  inversion_clear H1.
  rewrite H3 in H0 |-*.
  apply subset_intro; trivial.

  (* Sum *)
  inversion H4; clear H4; subst x p1 p3.
   rewrite H9 in H3|-*; apply inl_typ.
   apply H1; trivial.
   apply sum_ind with (3:=H3); intros.
    apply inl_inj in H5; rewrite H5; trivial.
    apply discr_sum in H5; contradiction.

   rewrite H9 in H3|-*; apply inr_typ.
   apply H2; trivial.
   apply sum_ind with (3:=H3); intros.
    symmetry in H5; apply discr_sum in H5; contradiction.
    apply inr_inj in H5; rewrite H5; trivial.

  (* ConsRec *)
  inversion H4; clear H4; subst.
  rewrite H10 in H3|-*; clear x H10.
  apply couple_intro.
   apply H1; trivial.
   apply fst_typ in H3.
   rewrite fst_def in H3; trivial.

   apply H2; trivial.
   apply snd_typ in H3.
   rewrite snd_def in H3; trivial.

  (* ConsNoRec *)
  inversion H2; clear H2; subst.
  rewrite H8.
  apply couple_intro_sigma; trivial.
   do 2 red; intros; apply dpos_oper_morph; auto with *.
   apply DINDi_morph; auto with *.

   apply H0; trivial.
   rewrite <- (snd_def x0 y); rewrite <- H8.
   apply snd_typ_sigma with (2:=H1).
    do 2 red; intros; apply pos_oper_morph; auto with *.
    apply tr_pos_morph; auto.

    symmetry; rewrite H8; apply fst_def.

  (* Param *)
  inversion H2; clear H2; subst.
  rewrite H8 in H1|-*; clear x H8.
  apply cc_prod_intro; intros; auto with *.
   do 2 red; intros; apply dpos_oper_morph; auto with *.
   apply DINDi_morph; auto with *.

   apply H0; auto.
   setoid_replace (f x) with (cc_app (cc_lam A f) x).
    apply cc_prod_elim with (1:=H1); trivial.

    symmetry; apply cc_beta_eq; auto with *.

 (* *)
 rewrite INDi_succ_eq; trivial.
 revert a tya x H.
 pattern p at 1 3; elim eqp using dpos_rect; simpl; intros; trivial.
  (* Inst *)
  destruct EQ_elim with (1:=H0) as (_,(_,eqr)); rewrite eqr; apply singl_intro.

  (* REC *)
  apply subset_elim1 in H0; trivial.

  (* sum *)
  revert H3; apply sum_mono; red; intros; eauto.

  (* prod *)
  revert H3; apply prodcart_mono; red; intros; eauto.

  (* sigma *)
  revert x H1; apply sigma_mono; auto with *.
   do 2 red; intros; apply dpos_oper_morph; auto with *.
   apply DINDi_morph; auto with *.

   do 2 red; intros; apply pos_oper_morph; auto with *.
   apply tr_pos_morph; auto.

   red; intros.
   apply H0 with a; trivial.
    rewrite <- H2; trivial.

    revert H3; apply eq_elim; apply dpos_oper_morph; auto with *.
    apply DINDi_morph; auto with *.

  (* cc_prod *)
  revert H1; apply cc_prod_covariant; auto with *.
   do 2 red; intros; apply pos_oper_morph; auto with *.
   apply tr_pos_morph; auto with *.

   red; intros.
   apply H0 with a; trivial.

 (* *)
 exists x; auto with *.
 revert a tya x H.
 pattern p at 1 4; elim eqp using dpos_rect; simpl; intros.
  (* Cst *)
  constructor; trivial.

  (* Inst *)
  destruct EQ_elim with (1:=H0) as (_,(?,?)).
  constructor; trivial.

  (* Rec *)
  apply subset_elim2 in H0.
  destruct H0.
  constructor 3 with x0; trivial.

  (* sum *)
  apply sum_ind with (3:=H3); intros.
   apply I_Sum1 with x0; auto.

   apply I_Sum2 with y; auto.

  (* prodcart *)
  apply I_ConsRec with (fst x) (snd x).
   apply fst_typ in H3; auto.
   apply snd_typ in H3; auto.
   apply surj_pair with (1:=H3).

  (* sigma *)
  assert (fst x \in A) by (apply fst_typ_sigma in H1; trivial).
  apply I_ConsNoRec with (fst x) (snd x); trivial.
   apply H0; trivial.
   apply snd_typ_sigma with (2:=H1); auto with *.
   do 2 red; intros; apply dpos_oper_morph; auto with *.
   apply DINDi_morph; auto with *.

   apply surj_pair with (1:=subset_elim1 _ _ _ H1).

  (* cc_prod *)
  apply I_Param with (cc_app x); intros.
   apply cc_app_morph; reflexivity.

   apply H0; trivial.
   apply cc_prod_elim with (1:=H1); trivial.

   apply cc_eta_eq with (1:=H1).
Qed.

  Lemma DINDi_eq2 o a : isOrd o -> a \in Arg ->
    DINDi p o a == sup o (fun o' => dpos_oper p (DINDi p o') a).
intros.
apply eq_intro; intros.
unfold DINDi in H1; rewrite subset_ax in H1; destruct H1.
destruct H2.
rewrite H2 in H1|-*; clear z H2.
apply TI_elim in H1; auto with *.
destruct H1.
rewrite sup_ax.
 2:do 2 red; intros; apply dpos_oper_morph; auto with *.
 2:apply DINDi_morph; auto with *.
exists x0; trivial.
rewrite <- DINDi_eq; eauto using isOrd_inv.
apply subset_intro; trivial.
rewrite INDi_succ_eq; eauto using isOrd_inv.

rewrite sup_ax in H1.
 2:do 2 red; intros; apply dpos_oper_morph; auto with *.
 2:apply DINDi_morph; auto with *.
destruct H1.
rewrite <- DINDi_eq in H2; eauto using isOrd_inv.
revert H2; apply DINDi_mono; eauto using isOrd_inv.
red; intros.
apply isOrd_plump with x; eauto using isOrd_inv.
apply olts_le; trivial.
Qed.


  Lemma DIND_eq : forall a, a \in Arg ->
    DIND p a == dpos_oper p (DIND p) a.
intros.
assert (isOrd (IND_clos_ord (tr_pos p))).
 apply ZFind_w.W_o_o.
 apply pos_to_w2_morph'; trivial.
unfold DIND, IND.
fold (DINDi p (IND_clos_ord (tr_pos p))).
rewrite <- DINDi_eq; trivial.
unfold DINDi.
apply subset_morph. 
 rewrite INDi_succ_eq; trivial.
 apply IND_eq; trivial.

 red; reflexivity.
Qed.


  Lemma DINDi_DIND o a :
    isOrd o ->
    a \in Arg ->
    DINDi p o a \incl DIND p a.
intros.
revert a H0.
induction H using isOrd_ind; intros.
rewrite DIND_eq; trivial.
rewrite DINDi_eq2; trivial.
red; intros.
rewrite sup_ax in H3.
 2:do 2 red; intros; apply dpos_oper_morph; auto with *.
 2:apply DINDi_morph; auto with *.
destruct H3.
revert H4; apply dpos_oper_mono; auto with *.
 apply DINDi_morph; auto with *.

 apply DINDi_morph; auto with *.
Qed.

End InductiveFamily.
