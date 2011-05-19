Require Import ZF ZFpairs ZFsum ZFrelations ZFcoc.
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


Fixpoint pos_oper p X :=
  match p with
  | P_Cst A => A
  | P_Rec => X
  | P_Sum p1 p2 => sum (pos_oper p1 X) (pos_oper p2 X)
  | P_ConsRec p1 p2 => prodcart (pos_oper p1 X) (pos_oper p2 X)
  | P_ConsNoRec A p => sigma A (fun x => pos_oper (p x) X)
  | P_Param A p => cc_prod A (fun x => pos_oper (p x) X)
  end.

Inductive eq_pos : positive -> positive -> Prop :=
| EP_Cst : forall A A', A == A' -> eq_pos (P_Cst A) (P_Cst A')
| EP_Rec : eq_pos P_Rec P_Rec
| EP_Sum : forall p1 p2 q1 q2,
   eq_pos p1 p2 -> eq_pos q1 q2 -> eq_pos (P_Sum p1 q1) (P_Sum p2 q2)
| EP_ConsRec : forall p1 p2 q1 q2,
   eq_pos p1 p2 -> eq_pos q1 q2 -> eq_pos (P_ConsRec p1 q1) (P_ConsRec p2 q2)
| EP_ConsNoRec : forall A A' p1 p2,
   A == A' ->
   (forall x x', (*x \in A ->*) x == x' -> eq_pos (p1 x) (p2 x')) ->
   eq_pos (P_ConsNoRec A p1) (P_ConsNoRec A' p2)
| EP_Param : forall A A' p1 p2,
   A == A' ->
   (forall x x', (*x \in A ->*) x == x' -> eq_pos (p1 x) (p2 x')) ->
   eq_pos (P_Param A p1) (P_Param A' p2).

Instance eq_pos_sym : Symmetric eq_pos.
red; induction 1; constructor; auto with *.
Qed.

Instance eq_pos_trans : Transitive eq_pos.
red.
intros x y z ep1 ep2; revert z ep2; induction ep1; intros; inversion_clear ep2;
  constructor; eauto with *.
 transitivity A'; trivial.
 transitivity A'; trivial.
 transitivity A'; trivial.
Qed.

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
induction p; simpl; intros.
 apply cst_stable.

 apply id_stable.

 inversion_clear H.
 apply sum_stable; eauto.

 inversion_clear H.
 apply prodcart_stable; eauto.

 inversion_clear H0.
 clear H1.
 apply sigma_stable; auto.
  do 2 red; reflexivity.

  do 3 red; intros.
  apply pos_oper_morph; auto.

  apply cst_stable.

  intro.
  change (stable (pos_oper (p x))); auto with *.

 inversion_clear H0.
 clear H1.
 apply cc_prod_stable; auto.
  do 3 red; intros.
  apply pos_oper_morph; auto.

  intro.
  change (stable (pos_oper (p x))); auto with *.
Qed.

Require Import ZFind_w.
Require Import ZFind_nat.
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
 apply sum_case_morph; auto.

 apply sum_morph; auto using fst_morph, snd_morph.

 auto using fst_morph, snd_morph.

 apply sigma_morph; intros; auto.
 apply H1; trivial.
 apply cc_app_morph; trivial.
Qed.

(*
Instance pos_to_w2_morph' :
  forall p, eq_pos p p -> morph1 (pos_to_w2 p).
intros; apply pos_to_w2_morph; trivial.
Qed.
*)


Lemma iso_cst : forall A X,
  { f:_ | iso_fun A (W_F A (fun _ => empty) X) f }.
econstructor; intros.
apply iso_fun_sym.
unfold W_F.
eapply iso_fun_trans.
 eapply sigma_iso_fun_morph.
  4:apply id_iso_fun.

  4:intros.
  4:apply cc_prod_iso_fun_0_l.

  do 2 red; reflexivity.
  do 2 red; reflexivity.
  do 3 red; reflexivity.

 eapply sigma_iso_fun_1_r.
  do 2 red; reflexivity.

  intros.
  apply eq_iso_fun; auto with *.
   do 2 red; reflexivity.

   intros.
   apply singl_elim in H0; auto with *.
Defined.

Lemma iso_reccall :
  forall X Y f,
  { g:_ | iso_fun X Y f -> iso_fun X (W_F (singl empty) (fun _ => singl empty) Y) g }.
econstructor; intros.
eapply iso_fun_trans with (1:=H).
apply iso_fun_sym.
unfold W_F.
eapply iso_fun_trans.
 eapply sigma_iso_fun_1_l.
 do 2 red; reflexivity.

 eapply cc_prod_iso_fun_1_l; auto with *.
Defined.

Lemma iso_sum : forall X1 X2 A1 A2 B1 B2 Y f g,
  {h:_|
   morph1 B1 ->
   morph1 B2 ->
   iso_fun X1 (W_F A1 B1 Y) f ->
   iso_fun X2 (W_F A2 B2 Y) g ->
   iso_fun (sum X1 X2) (W_F (sum A1 A2) (sum_case B1 B2) Y) h}.
econstructor; intros bm1 bm2 H H0.
eapply iso_fun_trans.
 eapply sum_iso_fun_morph.
  apply H.
  apply H0.

assert (m1 : morph1 (fun x => cc_prod (B1 x) (fun _ => Y))).
 do 2 red; intros; apply cc_prod_ext; intros; auto with *.
 red; reflexivity.
assert (m1' : morph1 (fun x => cc_prod (B2 x) (fun _ => Y))).
 do 2 red; intros; apply cc_prod_ext; intros; auto with *.
 red; reflexivity.
 eapply iso_fun_trans.
  eapply iso_fun_sum_sigma; trivial.

  apply eq_iso_fun with (f:=fun x => x); intros; auto with *.
   do 2 red; auto.
  apply sigma_morph; auto with *.
  intros.
apply sum_ind with (3:=H1); intros. 
 rewrite H4; rewrite sum_case_inl; trivial.
 apply cc_prod_ext; intros; auto with *.
 2:red; reflexivity.
 rewrite <- H2; rewrite H4; rewrite sum_case_inl; auto with *.

 rewrite H4; rewrite sum_case_inr; trivial.
 apply cc_prod_ext; intros; auto with *.
 2:red; reflexivity.
 rewrite <- H2; rewrite H4; rewrite sum_case_inr; auto with *.
Defined.



Lemma iso_prodcart : forall X1 X2 A1 A2 B1 B2 Y f g,
  {h:_|
   morph1 B1 ->
   morph1 B2 ->
   iso_fun X1 (W_F A1 B1 Y) f ->
   iso_fun X2 (W_F A2 B2 Y) g ->
   iso_fun (prodcart X1 X2)
     (W_F (prodcart A1 A2) (fun i => sum (B1 (fst i)) (B2 (snd i))) Y) h}.
econstructor; intros bm1 bm2 iso1 iso2.
eapply iso_fun_trans.
 eapply prodcart_iso_fun_morph with (1:=iso1) (2:=iso2).
assert (m1 : morph1 (fun x => cc_prod (B1 x) (fun _ => Y))).
 do 2 red; intros; apply cc_prod_ext; intros; auto with *.
 red; reflexivity.
assert (m1' : morph1 (fun x => cc_prod (B2 x) (fun _ => Y))).
 do 2 red; intros; apply cc_prod_ext; intros; auto with *.
 red; reflexivity.
eapply iso_fun_trans.
 apply iso_fun_prodcart_sigma; trivial.

 eapply sigma_iso_fun_morph.
  4:apply id_iso_fun.

  do 2 red; intros.
  apply prodcart_morph.
   apply cc_prod_ext; intros; auto with *.
    rewrite H0; reflexivity.

    red; reflexivity.

   apply cc_prod_ext; intros; auto with *.
    rewrite H0; reflexivity.

    red; reflexivity.

  do 2 red; intros.
  apply cc_prod_ext; intros; auto with *.
   rewrite H0; reflexivity.

  red; reflexivity.

Focus 2.
intros.
eapply iso_fun_trans.
 eapply iso_fun_prodcart_cc_prod; do 2 red; auto with *.

 apply eq_iso_fun with (f:=fun x => x); intros; auto with *.
  do 2 red; auto.
 apply cc_prod_ext; intros; auto with *.
  rewrite H0; reflexivity.

  red; intros.
  apply sum_case_ind with (6:=H1); auto with *.
   do 2 red; intros.
   rewrite H3; reflexivity.

   do 2 red; reflexivity.  

   do 2 red; reflexivity.  

  do 3 red; intros.
  unfold comp_iso.
  apply cc_lam_ext; intros; auto with *.
   rewrite H; reflexivity.

   red; intros.
   apply sum_case_morph; auto.
    apply cc_app_morph; auto with *.
    rewrite H0; reflexivity.

    apply cc_app_morph; auto with *.
    rewrite H0; reflexivity.
Defined.

Lemma W_F_morph : Proper (eq_set ==> (eq_set ==> eq_set) ==> eq_set ==> eq_set) W_F.
do 4 red; intros.
unfold W_F.
apply sigma_morph; trivial.
intros.
apply cc_prod_ext; auto with *.
red; trivial.
Qed.

Lemma iso_arg_norec : forall P X A B Y f,
  {h:_|
   morph1 X -> 
   morph1 A ->
   morph2 B ->
   morph2 f ->
   (forall x, x \in P -> iso_fun (X x) (W_F (A x) (B x) Y) (f x)) ->
   iso_fun (sigma P X)
    (W_F (sigma P A) (fun p => B (fst p) (snd p)) Y) h}.
econstructor; intros.
eapply iso_fun_trans.
 eapply sigma_iso_fun_morph with (4:=id_iso_fun _).
  do 2 red; intros; apply H; trivial.

  3:intros x x' tyx eqx.
  3:generalize (H3 _ tyx); apply iso_fun_morph; auto with *.
  2:trivial.
  2:instantiate (1:=fun x => W_F (A x) (B x) Y).

  do 2 red; intros.
  apply W_F_morph; auto with *.

  simpl; apply W_F_morph; auto with *.

  eapply iso_sigma_sigma; intros.
   do 2 red; intros; apply H0; trivial.

   apply cc_prod_ext; intros.
    apply H1; auto with *.

    red; reflexivity.
Defined.

Lemma iso_param : forall P X A B Y f,
  {h:_|
   morph1 X -> 
   morph1 A ->
   morph2 B ->
   morph2 f ->
   (forall x, x \in P -> iso_fun (X x) (W_F (A x) (B x) Y) (f x)) ->
   iso_fun (cc_prod P X)
    (W_F (cc_prod P A) (fun p => sigma P (fun x => B x (cc_app p x))) Y) h}.
econstructor; intros.
eapply iso_fun_trans.
 eapply cc_prod_iso_fun_morph.
  auto with *.
  2:eexact H2.

  2:apply id_iso_fun.

  2:intros x x' h eqx.
  2:generalize (H3 _ h); apply iso_fun_morph; auto with *.
  2:instantiate (1:=fun x => W_F (A x) (B x) Y).
  do 2 red; intros.
  apply W_F_morph; auto with *.

  simpl; apply W_F_morph; auto with *.

  assert (m1 : morph2 (fun x y => cc_prod (B x y) (fun _ => Y))).
   do 3 red; intros.
   apply cc_prod_ext; eauto with *.
    apply H1; trivial.
    red; reflexivity.
  eapply iso_fun_trans.
   eapply iso_fun_cc_prod_sigma; trivial.

   eapply sigma_iso_fun_morph with (4:=id_iso_fun _); intros.
    do 2 red; intros.
    apply cc_prod_ext; intros; auto with *.
    red; intros.
    apply m1; trivial.
    apply cc_app_morph; trivial.

   do 2 red; intros.
   apply cc_prod_ext.
    apply sigma_morph; auto with *.
    intros.
    apply H1; trivial.
    apply cc_app_morph; trivial.

    red; reflexivity.

   2:eapply iso_fun_trans;[apply cc_prod_curry_iso_fun|apply eq_iso_fun with (f:=fun x=>x)];
     intros; auto with *.
    do 3 red; intros.
    unfold comp_iso, cc_prod_isocurry.
    apply cc_lam_ext; intros.
     apply sigma_morph; intros; auto with *.
     apply H1; trivial.
     apply cc_app_morph; trivial.

     red; intros.   
     rewrite H7; rewrite H5; reflexivity.

    do 2 red; intros; apply H1; trivial.
    apply cc_app_morph; auto with *.

    do 2 red; auto.

    apply cc_prod_ext.
     apply sigma_morph; auto with *.
     intros.
     apply H1; trivial.
     apply cc_app_morph; trivial.

     red; reflexivity.
Defined.

Fixpoint trad_pos_w X Y f p :=
  match p with 
  | P_Cst A => proj1_sig (iso_cst A Y)
  | P_Rec => proj1_sig (iso_reccall X Y f)
  | P_Sum p1 p2 =>
      proj1_sig (iso_sum (pos_oper p1 X) (pos_oper p2 X) (pos_to_w1 p1) (pos_to_w1 p2)
             (pos_to_w2 p1) (pos_to_w2 p2) Y
             (trad_pos_w X Y f p1) (trad_pos_w X Y f p2))
  | P_ConsRec p1 p2 => proj1_sig (iso_prodcart (pos_oper p1 X) (pos_oper p2 X)
             (pos_to_w1 p1) (pos_to_w1 p2) (pos_to_w2 p1) (pos_to_w2 p2) Y
             (trad_pos_w X Y f p1) (trad_pos_w X Y f p2))
  | P_ConsNoRec A p => proj1_sig
     (iso_arg_norec A (fun a => pos_oper (p a) X) (fun a => pos_to_w1 (p a))
             (fun a => pos_to_w2 (p a)) Y (fun a => trad_pos_w X Y f (p a)))
  | P_Param A p => proj1_sig 
     (iso_param A (fun a => pos_oper (p a) X) (fun a => pos_to_w1 (p a))
             (fun a => pos_to_w2 (p a)) Y (fun a => trad_pos_w X Y f (p a)))
  end.

Lemma tpm : forall X Y f, morph1 f -> 
  Proper (eq_pos ==> eq_set ==> eq_set) (trad_pos_w X Y f).
do 3 red.
induction 2; simpl; intros.
 unfold iso_inv.
 apply union_morph; apply subset_morph.
  apply sigma_morph; auto with *.

  red; intros.
  unfold comp_iso, sigma_isomap.
  rewrite H1; reflexivity.

 unfold comp_iso, iso_inv, cc_prod_iso1l.
 apply union_morph; apply subset_morph; auto with *.
 red; intros.
 rewrite H0; reflexivity.

 unfold comp_iso, sum_isomap, sum_sigma_iso.
 apply sum_case_morph.
  red; intros.
  rewrite H1; reflexivity.

  red; intros.
  rewrite H1; reflexivity.

  apply sum_case_morph; trivial.
   red; intros.
   apply inl_morph; auto.

   red; intros.
   apply inr_morph; auto.

 unfold comp_iso, sigma_isomap.
 apply couple_morph.
  repeat rewrite fst_def.
  repeat rewrite snd_def.
  apply couple_morph; apply fst_morph.
   apply IHeq_pos1; apply fst_morph; trivial.
   apply IHeq_pos2; apply snd_morph; trivial.

  apply cc_lam_ext; intros.
   apply sum_morph.
    apply pos_to_w2_morph; trivial.
    repeat rewrite fst_def.
    apply fst_morph; apply IHeq_pos1; apply fst_morph; trivial.

    apply pos_to_w2_morph; trivial.
    repeat rewrite fst_def.
    repeat rewrite snd_def.
    apply fst_morph; apply IHeq_pos2; apply snd_morph; trivial.

   red; intros.
   apply sum_case_morph; trivial.
    red; intros.
    repeat (rewrite fst_def||rewrite snd_def).
    apply cc_app_morph; trivial.
    apply snd_morph; apply IHeq_pos1; apply fst_morph; trivial.
    
    red; intros.
    repeat (rewrite fst_def||rewrite snd_def).
    apply cc_app_morph; trivial.
    apply snd_morph; apply IHeq_pos2; apply snd_morph; trivial.

 unfold comp_iso, sigma_isomap, sigma_isoassoc.
  repeat (rewrite fst_def||rewrite snd_def).
  rewrite H2 with (1:=fst_morph _ _ H3) (2:=snd_morph _ _ H3).
  rewrite H3.
  reflexivity.

 unfold comp_iso, sigma_isomap.
 apply couple_morph.
  unfold cc_prod_sigma_iso.
  rewrite fst_def.
  rewrite fst_def.
  apply cc_lam_ext; intros; auto with *.
  red; intros.
  apply fst_morph; apply cc_app_morph; auto.
  unfold cc_prod_isomap.
  apply cc_lam_ext; intros; auto.
  red; intros.
  apply H2.
   unfold iso_inv; apply union_morph; apply subset_morph; trivial.
   red; intros.
   rewrite H7; reflexivity.

   apply cc_app_morph; trivial.
   unfold iso_inv.
   apply union_morph; apply subset_morph; trivial.
   red; intros.
   rewrite H7; reflexivity.

  unfold cc_prod_isocurry, cc_prod_sigma_iso, sigma_isomap, cc_prod_isocurry.
  apply cc_lam_ext; intros.
   apply sigma_morph; intros; auto with *.
   apply pos_to_w2_morph; auto.
   rewrite fst_def.
   rewrite fst_def.
   apply cc_app_morph; trivial.
   apply cc_lam_ext; intros; auto.
   red; intros.
   apply fst_morph; apply cc_app_morph; auto.
   unfold cc_prod_isomap, iso_inv.
   apply cc_lam_ext; intros; auto.
   red; intros.
   apply H2.
    apply union_morph; apply subset_morph; auto.
    red; intros.
    rewrite H9; reflexivity.

    apply cc_app_morph; trivial.
    apply union_morph; apply subset_morph; auto.
    red; intros.
    rewrite H9; reflexivity.

  red; intros.
  rewrite H5.
  apply cc_app_morph; auto with *.
  rewrite snd_def.
  rewrite snd_def.
  apply cc_app_morph; auto with *.
  apply cc_lam_ext; intros; auto with *.
  red; intros.
  apply snd_morph; apply cc_app_morph; trivial.
  unfold cc_prod_isomap, iso_inv.
  apply cc_lam_ext; intros; auto.
  red; intros.
  apply H2.
   apply union_morph; apply subset_morph; trivial.
   red; intros.
   rewrite H9; reflexivity.

   apply cc_app_morph; trivial.
   apply union_morph; apply subset_morph; trivial.
   red; intros.
   rewrite H9; reflexivity.
Qed.

Lemma trad_w_iso :
  forall X Y f p,
  eq_pos p p -> iso_fun X Y f ->
  iso_fun (pos_oper p X) (W_F (pos_to_w1 p) (pos_to_w2 p) Y) (trad_pos_w X Y f p).
intros.
induction p; simpl.
 apply (proj2_sig (iso_cst A Y)).

 apply (proj2_sig (iso_reccall X Y f)); trivial.

 inversion_clear H.
 apply (proj2_sig
    (iso_sum (pos_oper p1 X) (pos_oper p2 X) (pos_to_w1 p1) (pos_to_w1 p2)
             (pos_to_w2 p1) (pos_to_w2 p2) Y
       (trad_pos_w X Y f p1) (trad_pos_w X Y f p2))); auto.
  apply pos_to_w2_morph; auto with *.
  apply pos_to_w2_morph; auto with *.

 inversion_clear H.
 apply (proj2_sig
    (iso_prodcart (pos_oper p1 X) (pos_oper p2 X) (pos_to_w1 p1) (pos_to_w1 p2)
                  (pos_to_w2 p1) (pos_to_w2 p2) Y
       (trad_pos_w X Y f p1) (trad_pos_w X Y f p2))); auto.
  apply pos_to_w2_morph; auto with *.
  apply pos_to_w2_morph; auto with *.

 inversion_clear H.
 clear H2.
 apply (proj2_sig
   (iso_arg_norec A (fun a => pos_oper (p a) X) (fun a => pos_to_w1 (p a))
             (fun a => pos_to_w2 (p a)) Y (fun a => trad_pos_w X Y f (p a)))); auto with *.
  do 2 red; intros; apply pos_oper_morph; auto with *.
  do 2 red; intros; apply pos_to_w1_morph; auto with *.
  do 2 red; intros; apply pos_to_w2_morph; auto with *.
  do 2 red; intros; apply tpm; auto; apply (iso_funm H0).

 inversion_clear H.
 clear H2.
 apply (proj2_sig
   (iso_param A (fun a => pos_oper (p a) X) (fun a => pos_to_w1 (p a))
             (fun a => pos_to_w2 (p a)) Y (fun a => trad_pos_w X Y f (p a)))); auto with *.
  do 2 red; intros; apply pos_oper_morph; auto with *.
  do 2 red; intros; apply pos_to_w1_morph; auto with *.
  do 2 red; intros; apply pos_to_w2_morph; auto with *.
  do 2 red; intros; apply tpm; auto; apply (iso_funm H0).
Qed.

(*
Fixpoint trad_pos_w1 p :=
  match p with
  | P_Cst A => (fun a => a)
  | P_Rec => (fun _ => empty)
  | P_Sum p1 p2 =>
     sum_case
       (fun a1 => inl (trad_pos_w1 p1 a1))
       (fun a2 => inr (trad_pos_w1 p2 a2))
  | P_ConsRec p1 p2 =>
     (fun c => couple (trad_pos_w1 p1 (fst c)) (trad_pos_w1 p2 (snd c)))
  | P_ConsNoRec X p =>
     (fun c => couple (fst c) (trad_pos_w1 (p (fst c)) (snd c)))
  | P_Param X p =>
     (fun f => cc_lam X (fun x => trad_pos_w1 (p x) (cc_app f x)))
  end.

Instance trad_pos_w1_morph : Proper (eq_pos ==> eq_set ==> eq_set) trad_pos_w1.
Admitted.

Fixpoint trad_pos_w2 f p :=
  match p with
  | P_Cst A => (fun x _ => empty) (* dummy *)
  | P_Rec => (fun x _ => f x)
  | P_Sum p1 p2 =>
     (fun x c => sum_case
       (fun x1 => trad_pos_w2 f p1 x1 c) (fun x2 => trad_pos_w2 f p2 x2 c) x)
  | P_ConsRec p1 p2 =>
     (fun x c => sum_case (trad_pos_w2 f p1 (fst x)) (trad_pos_w2 f p2 (snd x)) c)
  | P_ConsNoRec X p =>
     (fun x c => trad_pos_w2 f (p (fst x)) (snd x) c)
  | P_Param X p =>
     (fun x c => trad_pos_w2 f (p (fst c)) (cc_app x (fst c)) (snd c))
  end.

Instance trad_pos_w2_morph :
  Proper ((eq_set ==> eq_set) ==> eq_pos ==> eq_set ==> eq_set ==> eq_set)
    trad_pos_w2.
Admitted.

Definition trad_pos_w f p x :=
  couple (trad_pos_w1 p x)
    (cc_lam (pos_to_w2 p (trad_pos_w1 p x)) (trad_pos_w2 f p x)).



Lemma trad_w1_typ : forall X p x,
  eq_pos p p ->
  x \in pos_oper p X ->
  trad_pos_w1 p x \in pos_to_w1 p.
induction p; simpl; intros; trivial.
 apply singl_intro.

 inversion_clear H.
 apply sum_case_ind with (6:=H0).
  do 2 red; intros.
  rewrite H; reflexivity.

  do 2 red; intros.
  apply inl_morph; apply trad_pos_w1_morph; auto with *.

  do 2 red; intros.
  apply inr_morph; apply trad_pos_w1_morph; auto with *.

  intros.
  apply inl_typ; auto.

  intros.
  apply inr_typ; auto.

 inversion_clear H.
 apply couple_intro.
  apply fst_typ in H0; auto.
  apply snd_typ in H0; auto.

 inversion_clear H0.
 clear H2.
 apply couple_intro_sigma.
  do 2 red; intros.
  specialize H3 with (1:=H2).
  rewrite H3; reflexivity.

  apply fst_typ_sigma in H1; trivial.

  apply H; auto with *.
  apply snd_typ_sigma with (2:=H1); auto with *.
  do 2 red; intros.
  specialize H3 with (1:=H2).
  apply pos_oper_morph; auto with *.

 inversion_clear H0.
 clear H2.
 apply cc_prod_intro; intros.
  do 2 red; intros.
  apply trad_pos_w1_morph; auto.
  rewrite H2; reflexivity.

  do 2 red; intros.
  apply pos_to_w1_morph; auto.

  apply H; auto with *.
  apply cc_prod_elim with (1:=H1); trivial.
Qed.

Lemma trad_w2_typ : forall X Y f p x i,
  eq_pos p p ->
  morph1 f ->
  (forall x, x \in X -> f x \in Y) ->
  x \in pos_oper p X ->
  i \in pos_to_w2 p (trad_pos_w1 p x) ->
  trad_pos_w2 f p x i \in Y.
intros X Y f p x i eqp mf tyf; revert p eqp x i.
induction p; simpl; intros; auto.
 apply empty_ax in H0; contradiction.

 inversion_clear eqp.
 generalize (pos_to_w2_morph' _ H1); intro m1.
 generalize (pos_to_w2_morph' _ H2); intro m1'.
 assert (m2 : morph1 (fun a => inl (trad_pos_w1 p1 a))).
  do 2 red; intros.
  apply inl_morph; apply trad_pos_w1_morph; auto with *.
 assert (m2' : morph1 (fun a => inr (trad_pos_w1 p2 a))).
  do 2 red; intros.
  apply inr_morph; apply trad_pos_w1_morph; auto with *.
 assert (m3 : morph1 (fun x => trad_pos_w2 f p1 x i)).
  do 2 red; intros.
  apply trad_pos_w2_morph; auto with *.
 assert (m3' : morph1 (fun x => trad_pos_w2 f p2 x i)).
  do 2 red; intros.
  apply trad_pos_w2_morph; auto with *.
 apply sum_ind with (3:=H); intros.
  rewrite H4 in H0|-*.
  rewrite sum_case_inl in H0|-*; auto with *.
  rewrite sum_case_inl in H0; auto.

  rewrite H4 in H0|-*.
  rewrite sum_case_inr in H0|-*; auto with *.
  rewrite sum_case_inr in H0; auto.

 inversion_clear eqp.
 generalize (pos_to_w2_morph' _ H1); intro m1.
 generalize (pos_to_w2_morph' _ H2); intro m1'.
 assert (m2:morph1 (trad_pos_w2 f p1 (fst x))).
  do 2 red; intros.
  apply trad_pos_w2_morph; auto with *.
 assert (m2':morph1 (trad_pos_w2 f p2 (snd x))).
  do 2 red; intros.
  apply trad_pos_w2_morph; auto with *.
 rewrite fst_def in H0.
 rewrite snd_def in H0.
 apply sum_ind with (3:=H0); intros.
  apply fst_typ in H.
  rewrite H4.
  rewrite sum_case_inl; auto with *.

  apply snd_typ in H.
  rewrite H4.
  rewrite sum_case_inr; auto with *.

 inversion_clear eqp.
 clear H2.
 change (Proper (eq_set ==> eq_pos) p) in H3.
 rewrite fst_def in H1.
 rewrite snd_def in H1.
 apply H; auto with *.
 apply snd_typ_sigma with (2:=H0); auto with *.
 do 2 red; intros.
 apply pos_oper_morph; auto with *.

 inversion_clear eqp.
 clear H2.
 apply H; auto with *.
  apply cc_prod_elim with (1:=H0).
  apply fst_typ_sigma in H1; trivial.

  generalize (pos_to_w2_morph _ _ (H3 _ _ (reflexivity (fst i)))); intro m2.
  rewrite (m2 (trad_pos_w1 (p (fst i)) (cc_app x (fst i)))
    (cc_app (cc_lam A (fun x1 => trad_pos_w1 (p x1) (cc_app x x1))) (fst i))).
   eapply snd_typ_sigma with (2:=H1); auto with *.
   do 2 red; intros.
   apply pos_to_w2_morph; auto with *.
   rewrite H4; reflexivity.

   rewrite cc_beta_eq; auto with *.
    do 2 red; intros.
    apply trad_pos_w1_morph; auto with *.
    rewrite H4; reflexivity.

    apply fst_typ_sigma in H1; trivial.
Qed.

(* Proving that the translation of any strictly positive operator to W is
   well-typed. *)
Lemma trad_w_typ : forall p f x X Y,
  eq_pos p p ->
  morph1 f ->
  (forall x, x \in X -> f x \in Y) ->
  x \in pos_oper p X ->
  trad_pos_w f p x \in W_F (pos_to_w1 p) (pos_to_w2 p) Y.
intros.
apply couple_intro_sigma.
 do 2 red; intros.
 apply cc_prod_ext; auto with *.
  apply pos_to_w2_morph; auto with *.
  red; reflexivity.

 apply trad_w1_typ with (2:=H2); trivial.

 apply cc_prod_intro; intros.
  do 2 red; intros.
  apply trad_pos_w2_morph; auto with *.

  do 2 red; reflexivity.

  apply trad_w2_typ with (1:=H) (3:=H1); trivial.
Qed.

(* We now have to show that the translation is an isomorphism *)

Lemma iso_fun_sym_eq : forall X Y f g,
  morph1 g ->
  iso_fun X Y f ->
  (forall y, y \in Y -> g y \in X) ->
  (forall y, y \in Y -> f (g y) == y) ->
  iso_fun Y X g.
constructor; intros; trivial.
 apply H1; trivial.

 apply (iso_funm H0) in H5.
 rewrite H2 in H5; trivial.
 rewrite H2 in H5; trivial.

 exists (f y).
  apply (iso_typ H0); trivial.

  apply (iso_inj H0); trivial.
   apply H1.
   apply (iso_typ H0); trivial.

   rewrite H2; auto with *.
   apply (iso_typ H0); trivial.
Qed.

Lemma sum_case_inl_eq : forall f g x a,
  morph1 f ->
  morph1 g ->
  x == inl a ->
  sum_case f g x == f a.
intros.
rewrite H1.
rewrite sum_case_inl; auto with *.
Qed.

Lemma sum_case_inr_eq : forall f g x a,
  morph1 f ->
  morph1 g ->
  x == inr a ->
  sum_case f g x == g a.
intros.
rewrite H1.
rewrite sum_case_inr; auto with *.
Qed.

Lemma WF_intro : forall a b A B X,
  morph1 b ->
  morph1 B ->
  a \in A ->
  (forall i, i \in B a -> b i \in X) ->
  couple a (cc_lam (B a) b) \in W_F A B X.
intros.
apply couple_intro_sigma; trivial.
 do 2 red; intros; apply cc_prod_ext; auto with *.
 red; reflexivity.

 apply cc_prod_intro; intros; auto with *.
Qed.

Lemma iso_W_F : forall X Y A B f g h,
  morph1 f ->
  morph2 g ->
  (forall a a' b b', a \in A -> a == a' ->
   (forall y y', y \in B a -> y == y' -> b y == b' y') ->
   h a b == h a' b') ->
  morph1 B ->
  (forall x, x \in X -> f x \in A) ->
  (forall x y, x \in X -> y \in B (f x) -> g x y \in Y) ->
  (forall a b, morph1 b -> a \in A ->
   (forall y, y \in B a -> b y \in Y) ->
   h a b \in X) ->
  (forall x, x \in X -> h (f x) (g x) == x) ->
  (forall a b, morph1 b -> a \in A -> (forall y, y \in B a -> b y \in Y) ->
   f (h a b) == a /\ forall y, y \in B a -> g (h a b) y == b y) ->
  iso_fun X (W_F A B Y) (fun x => couple (f x) (cc_lam (B (f x)) (g x))).
intros X Y A B f g h fm gm hm Bm fty gty hty eq1 eq2.
constructor; intros.
 do 2 red; intros.
 apply couple_morph; auto with *.
 apply cc_lam_ext; intros; auto with *.
 red; intros.
 apply gm; auto with *.

 apply WF_intro; auto with *.
 apply gm; reflexivity.

 apply couple_injection in H1; destruct H1.
 rewrite <- (eq1 x); trivial. 
 rewrite <- (eq1 x'); trivial. 
 apply hm; intros; auto.
 generalize (cc_app_morph _ _ H2 _ _ H4).
 rewrite cc_beta_eq; auto with *.
 2:do 2 red; intros; apply gm; auto with *.
 rewrite cc_beta_eq; auto with *.
  do 2 red; intros; apply gm; auto with *.

  rewrite <- H4; rewrite <- H1; trivial.

 assert (f (h (fst y) (cc_app (snd y))) == fst y).
  apply eq2; intros.
   apply cc_app_morph; auto with *.

   apply fst_typ_sigma in H; trivial.

   apply snd_typ_sigma with (y:=fst y) in H; auto with *.
    apply cc_prod_elim with (1:=H); trivial.

    do 2 red; intros.
    apply cc_prod_ext; intros; auto with *.
    red; reflexivity.
 assert (forall i, i \in B (fst y) -> g (h (fst y) (cc_app (snd y))) i == cc_app (snd y) i).
  intros.
  apply eq2; intros; auto.
   apply cc_app_morph; auto with *.

   apply fst_typ_sigma in H; trivial.

   apply snd_typ_sigma with (y:=fst y) in H; auto with *.
    apply cc_prod_elim with (1:=H); trivial.

    do 2 red; intros.
    apply cc_prod_ext; intros; auto with *.
    red; reflexivity.
 exists (h (fst y) (cc_app (snd y))).
  apply hty; intros; auto.
   apply cc_app_morph ;auto with *.

   apply fst_typ_sigma in H; trivial.
   
   apply snd_typ_sigma with (y:=fst y) in H; auto with *.
    apply cc_prod_elim with (1:=H); trivial.

    do 2 red; intros.
    apply cc_prod_ext; intros; auto with *.
    red; reflexivity.

  transitivity (couple (fst y) (cc_lam (B (fst y)) (cc_app (snd y)))).
   apply couple_morph; trivial.
   apply cc_lam_ext; intros; auto.
   red; intros.
   rewrite <- H3.
   rewrite H0 in H2; auto.

   symmetry; apply WF_eta with (2:=H); trivial.
Qed.

Lemma trad_w_iso : forall X Y f p,
  eq_pos p p ->
  iso_fun X Y f ->
  iso_fun (pos_oper p X)
    (W_F (pos_to_w1 p) (pos_to_w2 p) Y) (trad_pos_w f p).
unfold trad_pos_w; intros X Y f p eqp isof; induction p; simpl.
Eval simpl in (proj1_sig (iso_cst A Y)).
 apply (proj2_sig (iso_cst A Y)).
 apply iso_W_F with (h:=fun x _ => x); intros; auto with *.




Lemma trad_w_iso1 : forall X Y f p p',
  eq_pos p p' ->
  iso_fun X Y f ->
  iso_fun (pos_oper p X)
    (W_F (pos_to_w1 p') (pos_to_w2 p') Y) (trad_pos_w f p).
unfold trad_pos_w; intros X Y f p p' eqp isof; induction eqp; simpl.
 apply (proj2_sig (iso_cst _ )).

 apply iso_W_F with (h:=fun x _ => x); intros; auto with *.
  do 2 red; auto.
  do 3 red; reflexivity.
  do 2 red; reflexivity.

  rewrite <- H; trivial.

  apply empty_ax in H1; contradiction.

  rewrite H; trivial.

  split; intros; auto with *.
  apply empty_ax in H3; contradiction.

 apply iso_fun_trans
   with (Y:=Y) (f:=f) (g:=fun y => couple empty (cc_lam (singl empty) (fun _ => y)));
   trivial.
 apply iso_W_F with (B:=fun _ => singl empty) (h:=fun _ g => g empty); intros; auto with *.
  do 2 red; reflexivity.
  do 3 red; auto.
  apply H1; auto with *; apply singl_intro.
  do 2 red; reflexivity.

  apply singl_intro.

  apply H1; apply singl_intro.

  apply singl_elim in H0.
  split; intros; auto with *.
  apply singl_elim in H2.
  apply H; auto with *.

 (* Sum *)
assert (m1:forall y, morph1 (fun x => cc_app (snd x) y)).
 admit.
assert (m2:morph1 (fun x1 => inl (fst x1))).
 do 2 red; intros; apply inl_morph; apply fst_morph; trivial.
assert (m2':morph1 (fun x1 => inr (fst x1))).
 do 2 red; intros; apply inr_morph; apply fst_morph; trivial.
assert (m3: morph1 (pos_to_w2 p2)).
 apply pos_to_w2_morph; auto with *.
 transitivity p1; auto with *.
assert (m3': morph1 (pos_to_w2 q2)).
 apply pos_to_w2_morph; auto with *.
 transitivity q1; auto with *.
assert (m4:forall b, morph1 (fun a1 : set =>
      inl (couple a1 (cc_lam (pos_to_w2 p2 a1) b)))).
 admit.
assert (m4':forall b, morph1 (fun a1 : set =>
      inr (couple a1 (cc_lam (pos_to_w2 q2 a1) b)))).
 admit.
assert (m5:forall x, morph1 (fun a1 : set =>
      inl
        (couple a1
           (cc_lam (pos_to_w2 p2 a1)
              (fun c : set =>
               sum_case (fun x1 : set => cc_app (snd x1) c)
                 (fun x2 : set => cc_app (snd x2) c) x))))).
 admit.
assert (m5':forall x, morph1(fun a2 : set =>
      inr
        (couple a2
           (cc_lam (pos_to_w2 q2 a2)
              (fun c : set =>
               sum_case (fun x1 : set => cc_app (snd x1) c)
                 (fun x2 : set => cc_app (snd x2) c) x))))).
 admit.
 eapply iso_fun_trans_eq with (3:=sum_iso_fun_morph _ _ _ _ _ _ IHeqp1 IHeqp2)
    (g:=fun x => let a := sum_case (fun x1 => inl (fst x1)) (fun x2 => inr (fst x2)) x in
       couple a
        (cc_lam (sum_case (pos_to_w2 p2) (pos_to_w2 q2) a)
           (fun c => sum_case (fun x1 => cc_app (snd x1) c)
                              (fun x2 => cc_app (snd x2) c) x))); intros.
  do 2 red; intros; apply couple_morph; auto with *.
   apply sum_case_morph; auto with *.
    admit.
    admit.

   admit.

  apply couple_morph.
   admit.

   apply cc_lam_ext; intros; auto.
    admit.

    red; intros.
    admit.

  eapply iso_W_F with (B:=sum_case (pos_to_w2 p2) (pos_to_w2 q2))
    (h:=fun a b => sum_case
      (fun a1 => inl (couple a1 (cc_lam (pos_to_w2 p2 a1) b)))
      (fun a2 => inr (couple a2 (cc_lam (pos_to_w2 q2 a2) b))) a).
   apply sum_case_morph; auto with *.

   do 3 red; intros; apply sum_case_morph; auto with *.
    admit.
    admit. 

   intros; apply sum_case_morph; auto with *.
    admit.
    admit.

   apply sum_case_morph; auto with *.

   intros.
   apply sum_case_ind with (6:=H); trivial.
    do 2 red; intros.
    rewrite H0; reflexivity.

    intros.
    apply inl_typ.
    apply fst_typ_sigma in H0; trivial.

    intros.
    apply inr_typ.
    apply fst_typ_sigma in H0; trivial.

   intros.
   apply sum_ind with (3:=H); intros.
    rewrite H2 in H0|-*.
    repeat rewrite sum_case_inl in H0|-*; trivial.
    rewrite sum_case_inl in H0; trivial.
    apply snd_typ_sigma with (y:=fst x0) in H1; auto with *.
     apply cc_prod_elim with (1:=H1); trivial.

     do 2 red; intros; apply cc_prod_ext; auto; intros.
     red; reflexivity.

    rewrite H2 in H0|-*.
    repeat rewrite sum_case_inr in H0|-*; trivial.
    rewrite sum_case_inr in H0; trivial.
    apply snd_typ_sigma with (y:=fst y0) in H1; auto with *.
     apply cc_prod_elim with (1:=H1); trivial.

     do 2 red; intros; apply cc_prod_ext; auto; intros.
     red; reflexivity.

   intros.
   apply sum_ind with (3:=H0); intros.
    rewrite H3.
    rewrite sum_case_inl; trivial.
    apply inl_typ.
    apply WF_intro; intros; auto.
    apply H1.
    rewrite H3; rewrite sum_case_inl; trivial.

    rewrite H3.
    rewrite sum_case_inr; trivial.
    apply inr_typ.
    apply WF_intro; intros; auto with *.
    apply H1.
    rewrite H3; rewrite sum_case_inr; trivial.

   intros.
   apply sum_ind with (3:=H); intros.
    rewrite H1.
    do 2 (rewrite sum_case_inl; trivial).
    apply inl_morph.
    transitivity (WFmap (pos_to_w2 p2) (fun x => x) x0).
    2:symmetry; apply WF_eta with (2:=H0).
    2:apply pos_to_w2_morph; auto with *.
    2:transitivity p1; auto with *.
    apply couple_morph; auto with *.
    apply cc_lam_ext; intros; auto with *.
    red; intros.
    rewrite H1.
    rewrite sum_case_inl; trivial.
    apply cc_app_morph; auto with *.

    rewrite H1.
    do 2 (rewrite sum_case_inr; trivial).
    apply inr_morph.
    transitivity (WFmap (pos_to_w2 q2) (fun x => x) y).
    2:symmetry; apply WF_eta with (2:=H0).
    2:apply pos_to_w2_morph; auto with *.
    2:transitivity q1; auto with *.
    apply couple_morph; auto with *.
    apply cc_lam_ext; intros; auto with *.
    red; intros.
    rewrite H1.
    rewrite sum_case_inr; trivial.
    apply cc_app_morph; auto with *.

   intros.
   split; intros.
    apply sum_ind with (3:=H0); intros.
     rewrite H3.
     rewrite sum_case_inl; trivial.
     rewrite sum_case_inl; trivial.
     rewrite fst_def; reflexivity.

     rewrite H3.
     rewrite sum_case_inr; trivial.
     rewrite sum_case_inr; trivial.
     rewrite fst_def; reflexivity.

    apply sum_ind with (3:=H0); intros.
     rewrite H4.
     rewrite sum_case_inl; trivial.
     rewrite sum_case_inl; trivial.
     rewrite H4 in H2.
     rewrite sum_case_inl in H2; trivial.
     rewrite snd_def.
     rewrite cc_beta_eq; auto with *.
   
     rewrite H4.
     rewrite sum_case_inr; trivial.
     rewrite sum_case_inr; trivial.
     rewrite H4 in H2.
     rewrite sum_case_inr in H2; trivial.
     rewrite snd_def.
     rewrite cc_beta_eq; auto with *.

 (* ConsRec *)
 admit.

 (* Cons_NoRec *)
assert (m1 : Proper (eq_set ==> eq_pos) p1).
 do 2 red; intros.
 transitivity (p2 y).
  apply H0; trivial.
  symmetry; apply H0; reflexivity.
assert (m1' : Proper (eq_set ==> eq_pos) p2).
 do 2 red; intros.
 transitivity (p1 x).
  symmetry; apply H0; reflexivity.
  apply H0; trivial.
assert (e1 : ext_fun A (fun x => pos_oper (p1 x) X)).
 admit.
assert (e2 : ext_fun A (fun x => W_F (pos_to_w1 (p2 x)) (pos_to_w2 (p2 x)) Y)).
 admit.
assert (gm : morph2 (fun x x0 => couple (trad_pos_w1 (p1 x) x0)
            (cc_lam (pos_to_w2 (p1 x) (trad_pos_w1 (p1 x) x0))
               (trad_pos_w2 f (p1 x) x0)))).
 admit.
 eapply iso_fun_trans_eq with
    (3:=sigma_iso_fun_morph _ _ _ _ _ _ e1 e2 gm
       (id_iso_fun A) (fun x x' h ex => H1 x x' ex))
    (g:=fun t => couple (couple (fst t) (fst (snd t)))
         (cc_lam (pos_to_w2 (p2 (fst t)) (fst (snd t))) (cc_app (snd (snd t))))).
  admit.

  intros.
  apply couple_morph.
   apply couple_morph.
    apply fst_def.

    rewrite snd_def.
    apply fst_def.

   change ((eq_set ==> eq_pos)%signature p1 p2) in H0.
   symmetry.
   apply cc_lam_ext; intros; auto with *.
    rewrite fst_def.
    rewrite snd_def.
    rewrite fst_def.
    rewrite snd_def.
    rewrite fst_def.
    apply pos_to_w2_morph; auto with *.

    red; intros.
    rewrite snd_def.
    rewrite snd_def.
    rewrite cc_beta_eq; auto with *.
     generalize (iso_funm isof); intro.
     rewrite H4; reflexivity.

     do 2 red; intros.
     generalize (iso_funm isof); intro.
     rewrite H6; reflexivity.

     rewrite fst_def in H3.
     rewrite snd_def in H3.
     rewrite <- H4; trivial.

  eapply iso_W_F with (B:=fun a => pos_to_w2 (p2 (fst a)) (snd a))
   (h :=fun a b =>
    couple (fst a) (couple (snd a) (cc_lam (pos_to_w2 (p1 (fst a)) (snd a)) b))).

   iso_inv (pos_oper (p (fst a)) X) 
 couple (fst a) (couple (snd a) (cc_lam
    (pos_to_w2 (p (fst a)) (snd a)) b))).
  admit.
  admit.
  admit.
  admit.

  intros.
  apply couple_intro_sigma; trivial.
   admit.

   apply fst_typ_sigma in H0; trivial.

   apply trad_w1_typ with (X:=X).
    apply H1; reflexivity.

    apply snd_typ_sigma with (y:=fst x) in H0; auto with *.
    admit.

  intros.
  apply trad_w2_typ with (X:=X); intros; auto with *.
   apply (iso_funm isof).

   apply (iso_typ isof); trivial.

   apply snd_typ_sigma with (y:=fst x) in H0; auto with *.
   admit.

   rewrite fst_def in H2.
   rewrite snd_def in H2.
   trivial.

  intros.


 eapply iso_fun_trans_eq with (3:=sigma_iso_fun_morph _ _ _ _ _ _ (eq_iso_fun _ _ _ (fun _ _ h => h) (fun _ _ => reflexivity _)) (I (H1 _ _ (reflexivityH0))
    (g:=fun x => let a := sum_case (fun x1 => inl (fst x1)) (fun x2 => inr (fst x2)) x in
       couple a
        (cc_lam (sum_case (pos_to_w2 p1) (pos_to_w2 p2) a)
           (fun c => sum_case (fun x1 => cc_app (snd x1) c)
                              (fun x2 => cc_app (snd x2) c) x))); intros.
  admit.

  apply couple_morph.
   admit.

   apply cc_lam_ext; intros; auto.
    apply sum_case_morph; auto with *.
     apply pos_to_w2_morph; auto with *.
     apply pos_to_w2_morph; auto with *.
     admit.

    red; intros.
    admit.
 admit.
  simpl.


    specialize WF_eta with (1:=pos_to_w2_morph _ _ H) (2:=H2); intro.
    symmetry in H4; apply eq_set_trans with (2:=H4).
 x0).
    rewrite sum_case_inl in H2; trivial.
    apply snd_typ_sigma with (y:=fst x0) in H3; auto with *.
     apply cc_prod_elim with (1:=H3); trivial.

     do 2 red; intros; apply cc_prod_ext; auto; intros.
     red; reflexivity.

    rewrite H4 in H2|-*.
    repeat rewrite sum_case_inr in H2|-*; trivial.
    rewrite sum_case_inr in H2; trivial.
    apply snd_typ_sigma with (y:=fst y0) in H3; auto with *.
     apply cc_prod_elim with (1:=H3); trivial.

     do 2 red; intros; apply cc_prod_ext; auto; intros.
     red; reflexivity.


   apply sum_

   (h:=fun a g => sum_case (fun a1 => trad_pos_w2 f p1 x1

  .

  .

   
Y:=sum (W_F (pos_to_w1 p1) (pos_to_w2 p1) Y)
                               (W_F (pos_to_w1 p2) (pos_to_w2 p2) Y)).

 eapply iso_fun_trans_eq with (Y:=sum (W_F (pos_to_w1 p1) (pos_to_w2 p1) Y)
                               (W_F (pos_to_w1 p2) (pos_to_w2 p2) Y)).

    (f:=sum_case (fun x1 => inl (trad_pos_w p1 x1)) (fun x2 => inl (trad_pos_w p2 x2)))
    (g:=fun x => let a := sum_case (fun x1 => inl (fst x1)) (fun x2 => inr (fst x2)) x in
       couple a
        (cc_lam X (fun c => sum_case
  apply sum_iso_morph; auto.



 unfold W_F.
 apply iso_trans with (1:=iso_sum_sigma _ _ _ _).
 apply sigma_iso_morph_eq; auto with *.
 intros.
 apply eq_iso.
 assert (m1: morph1 (fun x0 => cc_prod (pos_to_w2 p1 x0) (fun _ => Y))).
  do 2 red; intros.
  apply cc_prod_ext.
   apply pos_to_w2_morph; auto with *.
   red; reflexivity.
 assert (m1': morph1 (fun x0 => cc_prod (pos_to_w2 p2 x0) (fun _ => Y))).
  do 2 red; intros.
  apply cc_prod_ext.
   apply pos_to_w2_morph; auto with *.
   red; reflexivity.
 assert (m2:morph1 (pos_to_w2 p1)).
  apply pos_to_w2_morph; auto with *.
 assert (m2':morph1 (pos_to_w2 p2)).
  apply pos_to_w2_morph; auto with *.
 apply sum_ind with (3:=H1); intros.
  rewrite H4.
  rewrite sum_case_inl; trivial.
  apply cc_prod_ext; intros; auto.
   rewrite <- H2; rewrite H4; rewrite sum_case_inl; auto with *.
   red; reflexivity.

  rewrite H4.
  rewrite sum_case_inr; trivial.
  apply cc_prod_ext.
   rewrite <- H2; rewrite H4; rewrite sum_case_inr; auto with *.
   red; reflexivity.

 assert (eq_pos p1 p1 /\ eq_pos p2 p2).
  inversion_clear H; auto.
 clear H; destruct H0.
 apply iso_trans with (prodcart (W_F (pos_to_w1 p1) (pos_to_w2 p1) Y)
   (W_F (pos_to_w1 p2) (pos_to_w2 p2) Y)).
  apply prodcart_iso_morph; auto.
 unfold W_F.
 apply iso_trans with (1:=iso_prodcart_sigma _ _ _ _).
 apply sigma_iso_morph_eq; auto with *.
 intros.
 apply iso_trans with (1:=iso_prodcart_cc_prod _ _ _ _).
 apply eq_iso.
 apply cc_prod_ext; intros.
  apply sum_morph.
   apply pos_to_w2_morph; auto with *.
   rewrite H2; reflexivity.

   apply pos_to_w2_morph; auto with *.
   rewrite H2; reflexivity.

  red; intros.
  apply sum_case_ind with (6:=H3); auto with *.
   do 2 red; intros.
   rewrite H5; reflexivity.

   do 2 red; reflexivity.
   do 2 red; reflexivity.

 assert (forall x x', x \in A -> x == x' -> eq_pos (p x) (p x')).
  inversion_clear H; auto with *.
 clear H.
 apply iso_trans with (sigma A (fun x => W_F (pos_to_w1 (p x)) (pos_to_w2 (p x)) Y)).
  apply sigma_iso_morph_eq; auto with *.
  intros.
  apply iso_trans with (pos_oper (p x') X0).
   apply eq_iso; apply pos_oper_morph; auto with *.

   apply X; trivial.
   rewrite H1 in H; auto with *.

  unfold W_F.
  apply iso_sigma_sigma.

 assert (forall x x', x \in A -> x == x' -> eq_pos (p x) (p x')).
  inversion_clear H; auto with *.
 clear H.
 apply iso_trans with (cc_prod A (fun x => W_F (pos_to_w1 (p x)) (pos_to_w2 (p x)) Y)).
  apply cc_prod_iso_morph_eq; auto with *.
  intros.
  apply iso_trans with (pos_oper (p x') X0).
   apply eq_iso; apply pos_oper_morph; auto with *.

   apply X; trivial.
   rewrite H1 in H; auto with *.

  unfold W_F.
  apply iso_trans with (1:=iso_cc_prod_sigma _ _ _).
  apply sigma_iso_morph_eq; auto with *.
  intros.
  apply iso_trans with (1:=cc_prod_curry _ _ _).
  apply eq_iso.
  apply cc_prod_ext; intros; auto with *.
   apply sigma_morph; intros; auto with *.
   apply pos_to_w2_morph; auto with *.
   rewrite H1; rewrite H3; reflexivity.

   red; reflexivity.



Lemma trad_w_iso : forall p X Y,
  eq_pos p p ->
  iso X Y -> 
  iso (pos_oper p X) (W_F (pos_to_w1 p) (pos_to_w2 p) Y).
induction p; simpl; intros.
 unfold W_F.
 apply iso_sym.
 apply sigma_iso_1_r; intros.
 apply cc_prod_0_l.

 unfold W_F.
 apply iso_trans with Y; trivial.
 apply iso_trans with (sigma (singl empty) (fun _ => Y)).
  apply iso_sym; apply sigma_iso_1_l.

  apply sigma_iso_morph_eq; intros; auto with *.
  apply iso_sym; apply cc_prod_1_l; trivial.

 assert (eq_pos p1 p1 /\ eq_pos p2 p2).
  inversion_clear H; auto.
 clear H; destruct H0.
 apply iso_trans with (sum (W_F (pos_to_w1 p1) (pos_to_w2 p1) Y)
   (W_F (pos_to_w1 p2) (pos_to_w2 p2) Y)).
  apply sum_iso_morph; auto.
 unfold W_F.
 apply iso_trans with (1:=iso_sum_sigma _ _ _ _).
 apply sigma_iso_morph_eq; auto with *.
 intros.
 apply eq_iso.
 assert (m1: morph1 (fun x0 => cc_prod (pos_to_w2 p1 x0) (fun _ => Y))).
  do 2 red; intros.
  apply cc_prod_ext.
   apply pos_to_w2_morph; auto with *.
   red; reflexivity.
 assert (m1': morph1 (fun x0 => cc_prod (pos_to_w2 p2 x0) (fun _ => Y))).
  do 2 red; intros.
  apply cc_prod_ext.
   apply pos_to_w2_morph; auto with *.
   red; reflexivity.
 assert (m2:morph1 (pos_to_w2 p1)).
  apply pos_to_w2_morph; auto with *.
 assert (m2':morph1 (pos_to_w2 p2)).
  apply pos_to_w2_morph; auto with *.
 apply sum_ind with (3:=H1); intros.
  rewrite H4.
  rewrite sum_case_inl; trivial.
  apply cc_prod_ext; intros; auto.
   rewrite <- H2; rewrite H4; rewrite sum_case_inl; auto with *.
   red; reflexivity.

  rewrite H4.
  rewrite sum_case_inr; trivial.
  apply cc_prod_ext.
   rewrite <- H2; rewrite H4; rewrite sum_case_inr; auto with *.
   red; reflexivity.

 assert (eq_pos p1 p1 /\ eq_pos p2 p2).
  inversion_clear H; auto.
 clear H; destruct H0.
 apply iso_trans with (prodcart (W_F (pos_to_w1 p1) (pos_to_w2 p1) Y)
   (W_F (pos_to_w1 p2) (pos_to_w2 p2) Y)).
  apply prodcart_iso_morph; auto.
 unfold W_F.
 apply iso_trans with (1:=iso_prodcart_sigma _ _ _ _).
 apply sigma_iso_morph_eq; auto with *.
 intros.
 apply iso_trans with (1:=iso_prodcart_cc_prod _ _ _ _).
 apply eq_iso.
 apply cc_prod_ext; intros.
  apply sum_morph.
   apply pos_to_w2_morph; auto with *.
   rewrite H2; reflexivity.

   apply pos_to_w2_morph; auto with *.
   rewrite H2; reflexivity.

  red; intros.
  apply sum_case_ind with (6:=H3); auto with *.
   do 2 red; intros.
   rewrite H5; reflexivity.

   do 2 red; reflexivity.
   do 2 red; reflexivity.

 assert (forall x x', x \in A -> x == x' -> eq_pos (p x) (p x')).
  inversion_clear H; auto with *.
 clear H.
 apply iso_trans with (sigma A (fun x => W_F (pos_to_w1 (p x)) (pos_to_w2 (p x)) Y)).
  apply sigma_iso_morph_eq; auto with *.
  intros.
  apply iso_trans with (pos_oper (p x') X0).
   apply eq_iso; apply pos_oper_morph; auto with *.

   apply X; trivial.
   rewrite H1 in H; auto with *.

  unfold W_F.
  apply iso_sigma_sigma.

 assert (forall x x', x \in A -> x == x' -> eq_pos (p x) (p x')).
  inversion_clear H; auto with *.
 clear H.
 apply iso_trans with (cc_prod A (fun x => W_F (pos_to_w1 (p x)) (pos_to_w2 (p x)) Y)).
  apply cc_prod_iso_morph_eq; auto with *.
  intros.
  apply iso_trans with (pos_oper (p x') X0).
   apply eq_iso; apply pos_oper_morph; auto with *.

   apply X; trivial.
   rewrite H1 in H; auto with *.

  unfold W_F.
  apply iso_trans with (1:=iso_cc_prod_sigma _ _ _).
  apply sigma_iso_morph_eq; auto with *.
  intros.
  apply iso_trans with (1:=cc_prod_curry _ _ _).
  apply eq_iso.
  apply cc_prod_ext; intros; auto with *.
   apply sigma_morph; intros; auto with *.
   apply pos_to_w2_morph; auto with *.
   rewrite H1; rewrite H3; reflexivity.

   red; reflexivity.
Qed.
*)