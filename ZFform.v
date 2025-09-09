
Require Import basic ZF ZFpairs ZFsum ZFnats ZFiso ZFcoc.
Require Import ZFord.

(* Encoding first-order formula as natural numbers *)


(* 1+N iso N *)
Definition C1n : set -> set :=
  sum_case (fun _ => zero) succ.
Instance C1n_morph : morph1 C1n.
unfold C1n; do 2 red; intros.
apply sum_case_morph; trivial.
*red; intros; reflexivity.
*apply succ_morph.
Qed. 
Lemma C1n_iso : iso_fun (sum (succ zero) N) N C1n.
split.
*apply C1n_morph.
*red; intros.
 unfold C1n.
 elim H using sum_ind; intros.
 +rewrite sum_case_inl0; [apply zero_typ|eauto].
 +rewrite sum_case_inr0;[|eauto].
  rewrite H1, dest_sum_inr.
  apply succ_typ; trivial.  
*unfold C1n; intros.
 elim H using sum_ind; intros; elim H0 using sum_ind; intros.
 +rewrite H3,H5; apply inl_morph.
  apply le_case in H2; apply le_case in H4.
  destruct H2;[|apply empty_ax in H2; contradiction].
  destruct H4;[|apply empty_ax in H4; contradiction].
  rewrite H2, H4; reflexivity.
 +rewrite sum_case_inl0 in H1;[|eauto].
  rewrite sum_case_inr0 in H1;[|eauto].
  symmetry in H1; apply discr in H1; contradiction.
 +rewrite sum_case_inr0 in H1;[|eauto].
  rewrite sum_case_inl0 in H1;[|eauto].
  apply discr in H1; contradiction.
 +do 2 (rewrite sum_case_inr0 in H1;[|eauto]).
  rewrite H3,H5,!dest_sum_inr in H1.
  apply succ_inj in H1; trivial.
  rewrite H3,H5, H1; reflexivity.
*unfold C1n; intros.
 elim H using N_ind; intros.
 +destruct H2 as (x,?,?); exists x;[trivial|].
  rewrite <-H1; trivial.
 +exists (inl zero).
  apply inl_typ; apply succ_intro1; reflexivity.
  rewrite sum_case_inl0; [reflexivity|exists zero; reflexivity].
 +exists (inr n).
  apply inr_typ; trivial.
  rewrite sum_case_inr0; [|exists n; reflexivity].
  rewrite dest_sum_inr; reflexivity.
Qed.  
Lemma C1n_order : forall n, n ∈ N -> n ∈ C1n (inr n).
unfold C1n; intros.
rewrite sum_case_inr0;[|exists n;reflexivity].
rewrite dest_sum_inr; apply succ_intro1; reflexivity.
Qed.

(* N+N iso N *)
Definition Cnn : set -> set :=
  sum_case (fun n => add n n) (fun n => succ (add n n)).

Lemma addS_l m n : m ∈ N -> n ∈ N -> add (succ m) n == succ (add m n).
intros.
elim H0 using N_ind; intros.
*rewrite <-H2; trivial.
*rewrite !add0; reflexivity.
*rewrite !addS,H2; trivial. 
 reflexivity.
Qed.

Lemma discr_even_odd m n :
  m ∈ N -> n ∈ N ->
  ~ add m m == succ (add n n).
intros mty; revert n; elim mty using N_ind; intros.
*rewrite <-H0; auto.
*rewrite add0.
 intros h; symmetry in h; apply discr in h; trivial. 
*rewrite addS; trivial.
 rewrite addS_l; trivial.
 elim H1 using N_ind; intros.
 +rewrite <-H3; trivial.
 +rewrite add0.
  intro h.
  apply succ_inj in h; auto using zero_typ, succ_typ, add_typ.
  apply discr in h; trivial.
 +rewrite addS; trivial.
  rewrite addS_l; trivial.
  intro h.
  apply succ_inj in h; auto using zero_typ, succ_typ, add_typ.
  apply succ_inj in h; auto using zero_typ, succ_typ, add_typ.
  apply H0 in h; auto.
Qed.

Lemma mult2_inj m n : m ∈ N -> n ∈ N -> add m m == add n n -> m==n.
intros mty; revert n; elim mty using N_ind; intros.
*rewrite <-H0 in H3|-*; auto.
*rewrite add0 in H0.
 revert H0; elim H using N_ind; intros.
 +rewrite <-H1 in H3|-*; auto.
 +reflexivity.
 +rewrite addS in H2; trivial.
  symmetry in H2; apply discr in H2; contradiction.  
*rewrite addS in H2; trivial.
 rewrite addS_l in H2; trivial.
 revert H2; elim H1 using N_ind; intros.
 +rewrite <-H3 in H5|-*; auto.
 +rewrite add0 in H2.
  apply discr in H2; contradiction.
 +rewrite addS in H4; trivial.
  rewrite addS_l in H4; trivial.
  apply succ_inj in H4; auto using zero_typ, succ_typ, add_typ.
  apply succ_inj in H4; auto using zero_typ, succ_typ, add_typ.
  apply succ_morph; auto.
Qed.

Lemma Cnn_iso : iso_fun (sum N N) N Cnn.
unfold Cnn; split; intros.
*do 2 red; intros.
 apply sum_case_morph; trivial.
 +red; intros.
  rewrite H0; reflexivity.
 +red; intros.
  rewrite H0; reflexivity.
*red; intros.
 elim H using sum_ind; intros.
 +rewrite sum_case_inl0;[|eauto].
  apply add_typ; rewrite H1,dest_sum_inl; trivial.
 +rewrite sum_case_inr0;[|eauto].
  apply succ_typ; apply add_typ; rewrite H1,dest_sum_inr; trivial.
*elim H using sum_ind; intros; elim H0 using sum_ind; intros.
 +rewrite !sum_case_inl0 in H1; eauto.
  rewrite H3, H5, !dest_sum_inl in H1.
  rewrite H3,H5; apply inl_morph.
  apply mult2_inj in H1; trivial.
 +rewrite sum_case_inl0,sum_case_inr0 in H1; eauto.
  rewrite H3, H5, dest_sum_inl,dest_sum_inr in H1.
  apply discr_even_odd in H1; trivial; contradiction.  
 +rewrite sum_case_inr0,sum_case_inl0 in H1; eauto.
  rewrite H3, H5, dest_sum_inl,dest_sum_inr in H1.
  symmetry in H1; apply discr_even_odd in H1; trivial; contradiction.  
 +rewrite !sum_case_inr0 in H1; eauto.
  rewrite H3, H5, !dest_sum_inr in H1.
  rewrite H3,H5; apply inr_morph.
  apply mult2_inj; trivial.
  apply succ_inj; auto using add_typ.
*elim H using N_ind; intros.
 +revert H2; apply ex2_morph; intros x; [reflexivity|].
  rewrite H1; reflexivity.
 +exists (inl zero); [apply inl_typ; apply zero_typ|].
  rewrite sum_case_inl; [apply add0|].
  intros ?? h; rewrite h; reflexivity.
 +destruct H1 as (s,tys,eqn).
  elim tys using sum_ind; intros.
  ++exists (inr x); [apply inr_typ; trivial|].
    rewrite sum_case_inl0 in eqn;[|eauto].
    rewrite H2, dest_sum_inl in eqn.
    rewrite sum_case_inr; [rewrite eqn; reflexivity|].
    intros ?? h; rewrite h; reflexivity.
  ++exists (inl (succ y0)); [auto using inl_typ, succ_typ|].
    rewrite sum_case_inr0 in eqn;[|eauto].
    rewrite H2, dest_sum_inr in eqn.
    rewrite <- eqn.
    rewrite sum_case_inl; [|intros ?? h; rewrite h; reflexivity].
    rewrite addS; trivial.
    rewrite addS_l; auto with *.
Qed.

Lemma mult2_incr n : n ∈ N -> n <= add n n.
intros.
elim H using N_ind; intros.
*rewrite <-H1; trivial.
*rewrite add0; apply succ_intro1; reflexivity.
*rewrite addS; trivial.
 rewrite addS_l; trivial.
 red in H1|-*.
 apply lt_mono; auto using succ_typ, add_typ.
 apply succ_intro2; trivial.
Qed.
 
  Lemma Cnn_order : forall n, n ∈ N -> n <= Cnn (inl n) /\ n <= Cnn (inr n).
intros.
unfold Cnn.
rewrite sum_case_inl, sum_case_inr;
  [|intros ?? h;rewrite h; reflexivity|intros ?? h;rewrite h; reflexivity].
split; [apply mult2_incr;trivial|].
apply succ_intro2;apply mult2_incr;trivial.
Qed.

(* NxN iso N *)
Definition Cnxn := NN2N.
Lemma Cnxn_iso : iso_fun (prodcart N N) N Cnxn.
unfold Cnxn.
split.
*apply NN2N_morph.
*apply NN2N_typ.
*apply NN2N_inj.
*intros; destruct NN2N_surj with (1:=H) as (p,(?,?)); exists p; trivial.
 symmetry; trivial.
Qed.

Lemma nat2set_le_intro m n :
  (m <= n)%nat ->
  nat2set m ⊆ nat2set n.
induction 1; [reflexivity|simpl].
rewrite IHle.
red; intros.
apply lt_trans with (2:=H0).
*apply succ_typ; apply nat2set_typ.
*apply succ_intro1; reflexivity.
Qed.
Lemma nat2set_le_intro' m n :
  (m <= n)%nat ->
  nat2set m <= nat2set n.
induction 1; [apply succ_intro1;reflexivity|simpl].
apply le_trans with (2:=IHle).
*apply succ_typ; apply nat2set_typ.
*apply succ_intro2; apply succ_intro1; reflexivity.
Qed.

Require Import Lia.

Lemma nn2n_order n m :
  (n <= nn2n n m /\ m <= nn2n n m)%nat.
unfold nn2n.
unfold nn2n1, nn2n2; simpl.
lia.
Qed.

  Lemma Cnxn_order : forall n m, n ∈ N -> m ∈ N -> n <= Cnxn (couple n m) /\ m <= Cnxn (couple n m).
unfold Cnxn; intros.
destruct (nat2set_reflect n) as (n',?); [trivial|].
destruct (nat2set_reflect m) as (m',?); [trivial|].
rewrite H1,H2.
rewrite NN2N_def.
split; apply nat2set_le_intro'; apply nn2n_order.
Qed.
  
(* f iso A ->N  yields iso  1+A -> N*)
Definition compC1n f :=
  comp_iso (sum_isomap (fun x=>x) f) C1n.
Definition compCnn f g x :=
  Cnn (sum_isomap f g x).
Definition compCnxn f g x :=
  Cnxn (sigma_isomap f (fun _ =>g) x).
Lemma compC1n_iso A f : iso_fun A N f -> iso_fun (sum (succ zero) A) N (compC1n f).
intros.
unfold compC1n.
apply iso_fun_trans with (2:=C1n_iso).
apply sum_iso_fun_morph;[|trivial].
apply id_iso_fun.
Qed.
Lemma compCnn_iso A B f g :
  iso_fun A N f -> iso_fun B N g -> iso_fun (sum A B) N (compCnn f g).
intros.
unfold compCnn.
apply iso_fun_trans with (2:=Cnn_iso).
apply sum_iso_fun_morph;trivial.
Qed.
Lemma compCnxn_iso A B f g :
  iso_fun A N f -> iso_fun B N g -> iso_fun (prodcart A B) N (compCnxn f g).
intros.
unfold compCnxn.
apply iso_fun_trans with (2:=Cnxn_iso).
apply prodcart_iso_fun_morph;trivial.
Qed.

(* Inductive Form :=
     Fbot | Feq (i j:N) | Fin (i j:N)
   | Fand (f1 f2:Form) | For (f1 f2:Form)
 *)

Definition FForm :=
  (sum (succ zero) (* bot *)
     (sum (prodcart N N) (* eq *)
        (sum (prodcart N N) (* in *)
           (sum (prodcart N N) (* and *)
              (sum (prodcart N N) (* or *)
                 (sum (prodcart N N) (* imp *)
                    (sum N (* fa *)
                       N (* ex *)
  ))))))).

Definition mkForm :=
  compC1n (* bot *)
    (compCnn Cnxn (* eq *)
       (compCnn Cnxn (* in *)
          (compCnn Cnxn (* and *)
             (compCnn Cnxn (* or *)
                (compCnn Cnxn (* imp *)
                   (compCnn (fun x => x) (* fa *)
                      (fun x => x) (* ex *)
    )))))).

Lemma mkForm_iso : iso_fun FForm N mkForm.
unfold mkForm.
apply compC1n_iso.
apply compCnn_iso; [apply Cnxn_iso|].
apply compCnn_iso; [apply Cnxn_iso|].
apply compCnn_iso; [apply Cnxn_iso|].
apply compCnn_iso; [apply Cnxn_iso|].
apply compCnn_iso; [apply Cnxn_iso|].
apply compCnn_iso; apply id_iso_fun.
Qed.

Definition Form := N.
Definition Fbot     := mkForm (inl zero).
Definition Feq  i j := mkForm (inr (inl (couple i j))).
Definition Fin  i j := mkForm (inr (inr (inl (couple i j)))).
Definition Fand P Q := mkForm (inr (inr (inr (inl (couple P Q))))).
Definition For  P Q := mkForm (inr (inr (inr (inr (inl (couple P Q)))))).
Definition Fimp P Q := mkForm (inr (inr (inr (inr (inr (inl (couple P Q))))))).
Definition Ffa  P   := mkForm (inr (inr (inr (inr (inr (inr (inl P))))))).
Definition Fex  P   := mkForm (inr (inr (inr (inr (inr (inr (inr P))))))).

Lemma Feq_typ : forall n, n ∈ N -> forall m, m ∈ N -> Feq n m ∈ Form.
intros.
unfold Form, Feq.
apply mkForm_iso.
apply inr_typ; apply inl_typ.
apply couple_intro; trivial.
Qed.
Lemma Fin_typ : forall n, n ∈ N -> forall m, m ∈ N -> Fin n m ∈ Form.
intros.
unfold Form, Fin.
apply mkForm_iso.
apply inr_typ; apply inr_typ; apply inl_typ.
apply couple_intro; trivial.
Qed.
Lemma Fbot_typ : Fbot ∈ Form.
intros.
unfold Form, Fbot.
apply mkForm_iso.
apply inl_typ.
apply succ_intro1; reflexivity.
Qed.
Lemma Fand_typ : forall P Q, P ∈ Form -> Q ∈ Form -> Fand P Q ∈ Form.
intros.
unfold Form, Fand.
apply mkForm_iso.
repeat apply inr_typ; apply inl_typ.
apply couple_intro; trivial.
Qed.
Lemma For_typ : forall P Q, P ∈ Form -> Q ∈ Form -> For P Q ∈ Form.
intros.
unfold Form, For.
apply mkForm_iso.
repeat apply inr_typ; apply inl_typ.
apply couple_intro; trivial.
Qed.
Lemma Fimp_typ : forall P Q, P ∈ Form -> Q ∈ Form -> Fimp P Q ∈ Form.
intros.
unfold Form, Fimp.
apply mkForm_iso.
repeat apply inr_typ; apply inl_typ.
apply couple_intro; trivial.
Qed.
Lemma Ffa_typ : forall P, P ∈ Form -> Ffa P ∈ Form.
intros.
unfold Form, Ffa.
apply mkForm_iso.
repeat apply inr_typ; apply inl_typ; trivial.
Qed.
Lemma Fex_typ : forall P, P ∈ Form -> Fex P ∈ Form.
intros.
unfold Form, Fex.
apply mkForm_iso.
repeat apply inr_typ; trivial.
Qed.

Lemma le_lt_trans : forall m n p, p ∈ N -> m <= n -> n < p -> m < p.
intros.
apply le_case in H0; destruct H0.
*rewrite H0; trivial.
*apply lt_trans with n; trivial.
Qed.


Lemma Fand_sub P Q : P ∈ Form -> Q ∈ Form -> let PQ := Cnxn (couple P Q) in PQ ∈ Fand P Q.
intros.
unfold Fand, mkForm.
intros.
assert (aux := iso_funm Cnn_iso).
assert (ty1 : PQ ∈ N).
{apply Cnxn_iso; apply couple_intro; trivial. }
set (f := compCnn Cnxn (compCnn Cnxn (compCnn (fun x => x) (fun x => x)))).
assert (isof : iso_fun (sum (prodcart N N) (sum (prodcart N N) (sum N N))) N f).
{apply compCnn_iso; [apply Cnxn_iso|].
 apply compCnn_iso; [apply Cnxn_iso|].
 apply compCnn_iso; apply id_iso_fun. }
clearbody f.
assert (isof1 : iso_fun (sum (prodcart N N) (sum (prodcart N N) (sum (prodcart N N) (sum N N)))) N (compCnn Cnxn f)).
{apply compCnn_iso; [apply Cnxn_iso|apply isof]. }
assert (PQ <= compCnn Cnxn f (inl (couple P Q))).
{unfold compCnn.
 rewrite sum_isomap_inl with (2:=reflexivity _).
 *apply Cnn_order; trivial.
 *intros.
  rewrite H1; reflexivity. }
assert (ty2 : compCnn Cnxn f (inl (couple P Q)) ∈ N).
{eapply compCnn_iso; [apply Cnxn_iso|apply isof|].
 apply inl_typ; apply couple_intro; trivial. }
assert (PQ <= compCnn Cnxn (compCnn Cnxn f) (inr (inl (couple P Q)))).
{unfold compCnn at 1.
 rewrite sum_isomap_inr with (2:=reflexivity _).
 *apply le_trans with (compCnn Cnxn f (inl (couple P Q)));[|apply H1|].
  +apply Cnn_iso; apply inr_typ; trivial.
  +apply Cnn_order; trivial.
 *intros.
  apply isof1; trivial. }
unfold compC1n, comp_iso.
rewrite sum_isomap_inr with (2:=reflexivity _).
*eapply le_lt_trans; [| |apply C1n_order].
 +apply C1n_iso.
  apply inr_typ. 
  eapply compCnn_iso; [apply Cnxn_iso| |apply inr_typ].
  ++apply compCnn_iso; [apply Cnxn_iso|].
    apply isof1.
  ++apply inr_typ; apply inl_typ; apply couple_intro; trivial.
 +unfold compCnn at 1, comp_iso.
  rewrite sum_isomap_inr with (2:=reflexivity _).
  apply le_trans with (2:=H2).
  ++apply Cnn_iso; apply inr_typ.
    eapply compCnn_iso; [apply Cnxn_iso|apply isof1 |apply inr_typ].
    apply inl_typ; apply couple_intro; trivial.
  ++apply Cnn_order.  
    eapply compCnn_iso; [apply Cnxn_iso|apply isof1|].
    apply inr_typ; apply inl_typ;apply couple_intro;[apply H|apply H0].
  ++intros.
    eapply compCnn_iso; [apply Cnxn_iso|apply isof1 |trivial].
 +eapply compCnn_iso; [apply Cnxn_iso| |apply inr_typ].
  ++apply compCnn_iso; [apply Cnxn_iso|apply isof1].
  ++apply inr_typ; apply inl_typ; apply couple_intro; trivial.
*intros.
 eapply compCnn_iso; [apply Cnxn_iso| |trivial].
 apply compCnn_iso; [apply Cnxn_iso|apply isof1].
Qed.

Lemma Fand_sub_l P Q : P ∈ Form -> Q ∈ Form -> P ∈ Fand P Q.
intros.
apply le_lt_trans with (Cnxn (couple P Q)).
*apply Fand_typ; trivial.
*apply Cnxn_order; trivial.
*apply Fand_sub; trivial.
Qed.
Lemma Fand_sub_r P Q : P ∈ Form -> Q ∈ Form -> Q ∈ Fand P Q.
intros.
apply le_lt_trans with (Cnxn (couple P Q)).
*apply Fand_typ; trivial.
*apply Cnxn_order; trivial.
*apply Fand_sub; trivial.
Qed.
 
 (* Form: the set of (first-order) formulas. Can be seen as N (or a subset of N) *)
(*Parameter Form : set.
Parameter Feq : set -> set -> set.
Parameter Feq_typ : forall n, n ∈ N -> forall m, m ∈ N -> Feq n m ∈ Form.
Parameter Fin : set -> set -> set.
Parameter Fin_typ : forall n, n ∈ N -> forall m, m ∈ N -> Fin n m ∈ Form.
Parameter Fbot : set.
Parameter Fbot_typ : Fbot ∈ Form.
Parameter Fand For Fimp : set -> set -> set.
Parameter Fand_typ : forall P Q, P ∈ Form -> Q ∈ Form -> Fand P Q ∈ Form.
Parameter For_typ : forall P Q, P ∈ Form -> Q ∈ Form -> For P Q ∈ Form.
Parameter Fimp_typ : forall P Q, P ∈ Form -> Q ∈ Form -> Fimp P Q ∈ Form.
Parameter Ffa Fex : set -> set.
Parameter Ffa_typ : forall P, P ∈ Form -> Ffa P ∈ Form.
Parameter Fex_typ : forall P, P ∈ Form -> Fex P ∈ Form.
*)

Parameter fo_Form_ind :
  forall P:set->Prop,
    Proper (eq_set==>iff) P ->
    (forall i j, i ∈ N -> j ∈ N -> P (Feq i j)) ->
    (forall i j, i ∈ N -> j ∈ N -> P (Fin i j)) ->
    P Fbot ->
    (forall A B, A ∈ Form -> P A -> B ∈ Form -> P B -> P (Fand A B)) ->
    (forall A B, A ∈ Form -> P A -> B ∈ Form -> P B -> P (For A B)) ->
    (forall A B, A ∈ Form -> P A -> B ∈ Form -> P B -> P (Fimp A B)) ->
    (forall A, A ∈ Form -> P A -> P (Ffa A)) ->
    (forall A, A ∈ Form -> P A -> P (Fex A)) ->
    forall A, A ∈ Form -> P A.

Definition Form_case (f1 f2:set->set->set) (f3:set) (f4 f5 f6:set->set->set) (f7 f8:set->set) A :=
  let a := iso_inv FForm mkForm A in
            sum_case (fun _ => f3)
  (fun a => sum_case (fun c => f1 (fst c) (snd c))
  (fun a => sum_case (fun c => f2 (fst c) (snd c))
  (fun a => sum_case (fun c => f4 (fst c) (snd c))
  (fun a => sum_case (fun c => f5 (fst c) (snd c))
  (fun a => sum_case (fun c => f6 (fst c) (snd c))
  (fun a => sum_case (fun c => f7 c)
  (fun a => f8 a) a)a)a)a)a)a)a.

Instance Form_case_morph :
  let E:=eq_set in
  Proper ((E==>E==>E)==>(E==>E==>E)==>E==>
          (E==>E==>E)==>(E==>E==>E)==>(E==>E==>E)==>(E==>E)==>(E==>E)==>E==>E) Form_case.
simpl.
intros f1 f1' e1 f2 f2' e2 f3 f3' e3 f4 f4' e4 f5 f5' e5 f6 f6' e6 f7 f7' e7 f8 f8' e8 A A' e.
apply sum_case_morph; [intros ?? h;apply e3|clear A A' e; intros A A' e|].
apply sum_case_morph; [intros ?? h; apply e1;[apply fst_morph|apply snd_morph];trivial|clear A A' e; intros A A' e|trivial].
apply sum_case_morph; [intros ?? h; apply e2;[apply fst_morph|apply snd_morph];trivial|clear A A' e; intros A A' e|trivial].
apply sum_case_morph; [intros ?? h; apply e4;[apply fst_morph|apply snd_morph];trivial|clear A A' e; intros A A' e|trivial].
apply sum_case_morph; [intros ?? h; apply e5;[apply fst_morph|apply snd_morph];trivial|clear A A' e; intros A A' e|trivial].
apply sum_case_morph; [intros ?? h; apply e6;[apply fst_morph|apply snd_morph];trivial|clear A A' e; intros A A' e|trivial].
apply sum_case_morph; [intros ?? h; apply e7;trivial|clear A A' e; intros A A' e|trivial].
apply e8; trivial.
apply iso_inv_morph;[reflexivity|apply mkForm_iso|trivial].
Qed.


Instance Form_case_morph0 f1 f2 f3 f4 f5 f6 f7 f8 :
  morph1 (Form_case f1 f2 f3 f4 f5 f6 f7 f8).
Admitted.


Existing Instance Form_case_morph0.

(*Parameter Form_case_morph :
  let E:=eq_set in
  Proper ((E==>E==>E)==>(E==>E==>E)==>E==>(E==>E==>E)==>(E==>E==>E)==>(E==>E==>E)==>(E==>E)==>(E==>E)==>E==>E) Form_case.*)

Lemma Form_case_eq : forall f1 f2 f3 f4 f5 f6 f7 f8,
  morph2 f1 ->
  forall i j, i∈N -> j∈N -> Form_case f1 f2 f3 f4 f5 f6 f7 f8 (Feq i j) == f1 i j.
intros.
unfold Form_case, Feq.
set (a := inr (inl (couple i j))).
assert (eqa: iso_inv FForm mkForm (mkForm a) == a).
{apply iso_inv_eq2 with (1:=mkForm_iso).
 apply inr_typ; apply inl_typ; apply couple_intro; trivial. }
rewrite sum_case_inr0;[|eauto].
rewrite sum_case_inl0.
*rewrite eqa; unfold a; rewrite dest_sum_inr,dest_sum_inl,fst_def,snd_def; reflexivity.
*eexists.
 rewrite eqa; unfold a; rewrite dest_sum_inr; reflexivity.
Qed.
Parameter Form_case_in : forall f1 f2 f3 f4 f5 f6 f7 f8,
  forall i j, i∈N -> j∈N -> Form_case f1 f2 f3 f4 f5 f6 f7 f8 (Fin i j) == f2 i j.
Parameter Form_case_bot : forall f1 f2 f3 f4 f5 f6 f7 f8,
  Form_case f1 f2 f3 f4 f5 f6 f7 f8 Fbot == f3.
Parameter Form_case_and : forall f1 f2 f3 f4 f5 f6 f7 f8,
  forall P Q, P∈Form -> Q∈Form -> Form_case f1 f2 f3 f4 f5 f6 f7 f8 (Fand P Q) == f4 P Q.
Parameter Form_case_or : forall f1 f2 f3 f4 f5 f6 f7 f8,
  forall P Q, P∈Form -> Q∈Form -> Form_case f1 f2 f3 f4 f5 f6 f7 f8 (For P Q) == f5 P Q.
Parameter Form_case_imp : forall f1 f2 f3 f4 f5 f6 f7 f8,
  forall P Q, P∈Form -> Q∈Form -> Form_case f1 f2 f3 f4 f5 f6 f7 f8 (Fimp P Q) == f6 P Q.
Parameter Form_case_fa : forall f1 f2 f3 f4 f5 f6 f7 f8,
  forall P, P∈Form -> Form_case f1 f2 f3 f4 f5 f6 f7 f8 (Ffa P) == f7 P.
Parameter Form_case_ex : forall f1 f2 f3 f4 f5 f6 f7 f8,
  forall P, P∈Form -> Form_case f1 f2 f3 f4 f5 f6 f7 f8 (Fex P) == f8 P.


Definition Form_cases P :=
  (exists i, i∈N /\ exists j, j∈N /\ P == Feq i j)
  \/ (exists i, i∈N /\ exists j, j∈N /\ P == Fin i j)
  \/ P==Fbot
  \/ (exists A, A∈Form /\ exists B, B∈Form /\ P == Fand A B)
  \/ (exists A, A∈Form /\ exists B, B∈Form /\ P == For A B)
  \/ (exists A, A∈Form /\ exists B, B∈Form /\ P == Fimp A B)
  \/ (exists A, A∈Form /\ P == Ffa A)
  \/ (exists A, A∈Form /\ P == Fex A).

Lemma Form_case_split : forall P, P ∈ Form -> Form_cases P.
intros.
elim H using fo_Form_ind; intros.
*intros ?? h; unfold Form_cases.
 repeat (apply or_iff_morphism||apply and_iff_morphism||(apply ex_morph;intro));
   try rewrite h; try reflexivity.
*left; exists i;split;[trivial|exists j;split;[trivial|reflexivity]].
*right;left; exists i;split;[trivial|exists j;split;[trivial|reflexivity]].
*do 2 right; left; reflexivity.
*do 3 right;left; exists A;split;[trivial|exists B;split;[trivial|reflexivity]].
*do 4 right;left; exists A;split;[trivial|exists B;split;[trivial|reflexivity]].
*do 5 right;left; exists A;split;[trivial|exists B;split;[trivial|reflexivity]].
*do 6 right;left; exists A;split;[trivial|reflexivity].
*do 7 right; exists A;split;[trivial|reflexivity].
Qed.



Definition subForm : set -> set :=
  Form_case (fun _ _=>empty) (fun _ _=>empty)
    empty (fun P Q => pair P Q) (fun P Q => pair P Q) (fun P Q => pair P Q)
    (fun P => singl P) (fun P => singl P).

Instance subForm_morph : morph1 subForm.
apply Form_case_morph0.
Qed.

Parameter subForm_lt :
  forall P Q, P ∈ Form -> Q ∈ subForm P -> Q ∈ P.


Lemma N_trans x y : x ∈ N -> y ∈ x -> y ∈ N.
intros tyx; revert y; elim tyx using N_ind; intros.
*rewrite <-H0 in H2; auto.
*apply empty_ax in H; contradiction.
*apply le_case in H1; destruct H1;[|auto].
 rewrite H1; trivial. 
Qed.


  Lemma wf_Form P : P ∈ Form -> Acc (fun x y => x ∈subForm y) P.
intros.
cut (forall n, n ∈ N -> n <= P -> Acc (fun x y => x ∈ subForm y) n).
{intros h; apply h; [trivial|].
 apply succ_intro1; reflexivity. }
elim H using N_ind.
*intros.
 rewrite <-H1 in H4; auto.
*constructor; intros.
 apply subForm_lt in H2;[|trivial].
 apply le_case in H1; destruct H1; [|apply empty_ax in H1; contradiction].
rewrite H1 in H2; apply empty_ax in H2; contradiction.
*intros.
 constructor; intros.
 apply subForm_lt in H4;[|trivial].
 apply H1; [apply N_trans with n0; trivial|].
 apply le_case in H3; destruct H3; [rewrite H3 in H4; trivial|].
 apply lt_trans with n0; trivial.
 apply succ_typ; trivial.
Qed.

  
  Lemma subForm_typ x y :
  x ∈ subForm y -> y ∈ Form -> x ∈ Form.
unfold subForm.
intros xsub yty.
revert xsub.
assert (auxm1 : morph2 (fun _ _ =>empty)) by (do 3 red; reflexivity).
destruct (Form_case_split _ yty) as
  [(k&?&k'&?&e)|[(k&?&k'&?&e)|
                  [e|[(A&?&B&?&e)|[(A&?&B&?&e)|[(A&?&B&?&e)|[(A&?&e)|(A&?&e)]]]]]]];
  rewrite e;
  [rewrite Form_case_eq|rewrite Form_case_in|rewrite Form_case_bot|rewrite Form_case_and
  |rewrite Form_case_or|rewrite Form_case_imp|rewrite Form_case_fa|rewrite Form_case_ex];
  trivial; intros.
*apply empty_ax in xsub; contradiction.
*apply empty_ax in xsub; contradiction.
*apply empty_ax in xsub; contradiction.
*apply pair_ax in xsub; destruct xsub as [e'|e']; rewrite e'; trivial.
*apply pair_ax in xsub; destruct xsub as [e'|e']; rewrite e'; trivial.
*apply pair_ax in xsub; destruct xsub as [e'|e']; rewrite e'; trivial.
*apply singl_elim in xsub; rewrite xsub; trivial.
*apply singl_elim in xsub; rewrite xsub; trivial.
Qed.

Lemma clos_subFrom_typ x y :
  ZFrepl.WFRle subForm x y -> y ∈ Form -> x ∈ Form.
induction 1;[|auto].
destruct H as [e|?]; [rewrite e; trivial|apply subForm_typ; trivial].
Qed.






Require Import ZFlist.
(*
Parameter Cons : set -> set -> set.
Parameter Cons_morph : morph2 Cons.
Existing Instance Cons_morph. *)

Parameter Fint_var : set -> set -> set.
Parameter Fint_var_morph : morph2 Fint_var.
Existing Instance Fint_var_morph.
Parameter Fiv_0 : forall x l, Fint_var (Cons x l) zero == x.
Parameter Fiv_S : forall x l k, Fint_var (Cons x l) (succ (nat2set k)) == Fint_var l (nat2set k).



Module UnboundedInterpretation.

  Local Definition Tr_body i f :=
  Form_case (fun i0 j => P2p (Fint_var i i0 == Fint_var i j))
    (fun i0 j => P2p (Fint_var i i0 ∈ Fint_var i j)) empty
    (fun A B => f A i ∩ f B i)
    (fun A B => f A i ∪ f B i)
    (fun A B => P2p (p2P (f A i) -> p2P (f B i)))
    (fun A => P2p (forall x0, p2P (f A (Cons x0 i))))
    (fun A => P2p (exists x0, p2P (f A (Cons x0 i)))).

  Local Lemma auxm1 i : morph2 (fun i0 j => P2p (Fint_var i i0 == Fint_var i j)).
intros ?? h ?? h'; rewrite h,h'; reflexivity.
Qed.
  Local Lemma auxm2 i : morph2 (fun i0 j => P2p (Fint_var i i0 ∈ Fint_var i j)).
intros ?? h ?? h'; rewrite h,h'; reflexivity.
Qed.
Hint Resolve auxm1 auxm2 : core.
  (*    (fun A B => f A i ∩ f B i)
    (fun A B => f A i ∪ f B i)
    (fun A B => P2p (p2P (f A i) -> p2P (f B i)))
    (fun A => P2p (forall x0, p2P (f A (Cons x0 i))))
    (fun A => P2p (exists x0, p2P (f A (Cons x0 i)))).*)

  
  (* We *need* to use the second order WFR here *)
  Definition Fintrec : set -> set -> set :=
    ZFrepl.WFR eq_set subForm (fun Fint P l => Tr_body l Fint P).
  Definition FTr (P:set) (l:set) : Prop := p2P (Fintrec P l).

  Lemma FTr_morph : Proper (eq_set==>eq_set==>iff) FTr.
do 3 red; intros.
apply p2P_morph.
apply ZFrepl.WFR_morph0; trivial.
Qed.

  Lemma Tr_body_wf P :
      P ∈ Form ->
      forall x x' a a' f f',
        ZFrepl.WFRle subForm x P ->
        (forall y y' a a', y ∈ subForm x -> y == y' -> a==a' -> f y a == f' y' a') ->
        x == x' ->
        a == a' ->
        Tr_body a f x == Tr_body a' f' x'.
intros Pty x x' a a' f f' xle eqf eqx eqa.
assert (subfo : x ∈ Form)
  by (apply clos_subFrom_typ with (1:=xle); trivial).
unfold Tr_body.
rewrite <- eqx. 
destruct (Form_case_split _ subfo) as
   [(k&?&k'&?&e)|[(k&?&k'&?&e)|
                   [e|[(A&?&B&?&e)|[(A&?&B&?&e)|[(A&?&B&?&e)|[(A&?&e)|(A&?&e)]]]]]]];
   rewrite e;
   [rewrite !Form_case_eq|rewrite !Form_case_in|rewrite !Form_case_bot|rewrite !Form_case_and
   |rewrite !Form_case_or|rewrite !Form_case_imp|rewrite !Form_case_fa|rewrite !Form_case_ex]; trivial.
*rewrite eqa; reflexivity.
*rewrite eqa; reflexivity.
*reflexivity.
*apply inter2_morph; (apply eqf; [|reflexivity|trivial]);
 unfold subForm; rewrite e,Form_case_and; auto;apply couple_intro; auto.
*apply union2_morph; (apply eqf; [|reflexivity|trivial]);
 unfold subForm; rewrite e,Form_case_or; auto;apply couple_intro; auto.
*apply P2p_morph; apply impl_morph;[|intros]; apply p2P_morph;
   (apply eqf;[|reflexivity|trivial]);
 unfold subForm; rewrite e,Form_case_imp; auto;apply couple_intro; auto.
*apply P2p_morph; apply fa_morph; intro;
 apply p2P_morph; apply eqf; [|reflexivity|rewrite eqa; reflexivity].
 unfold subForm; rewrite e,Form_case_fa; auto; apply singl_intro.
*apply P2p_morph; apply ex_morph; intro;
 apply p2P_morph; apply eqf; [|reflexivity|rewrite eqa; reflexivity].
 unfold subForm; rewrite e,Form_case_ex; auto; apply singl_intro.
Qed.

Lemma FTr_eq : forall i m n,
    m ∈ N -> n ∈ N ->
    FTr (Feq m n) i <-> Fint_var i m == Fint_var i n.
intros.
unfold FTr.
unfold Fintrec.
rewrite ZFrepl.WFR_eqn.
*unfold Tr_body; rewrite Form_case_eq; trivial.
 rewrite P2p2P; reflexivity.
*auto with *.
*auto with *.
*apply Tr_body_wf; trivial.
 apply Feq_typ; trivial.
*apply wf_Form.
 apply Feq_typ; trivial.
Qed.
Lemma FTr_in : forall i m n,
    m ∈ N -> n ∈ N ->
    FTr (Fin m n) i <-> Fint_var i m ∈ Fint_var i n.
intros.
unfold FTr.
unfold Fintrec.
rewrite ZFrepl.WFR_eqn.
*unfold Tr_body; rewrite Form_case_in; trivial.
 rewrite P2p2P; reflexivity.
*auto with *.
*auto with *.
*apply Tr_body_wf; trivial.
 apply Fin_typ; trivial.
*apply wf_Form.
 apply Fin_typ; trivial.
Qed.
Lemma FTr_bot : forall i,
    ~ FTr (Fbot) i.
intros.
unfold FTr.
unfold Fintrec.
rewrite ZFrepl.WFR_eqn.
*unfold Tr_body; rewrite Form_case_bot; trivial.
 apply empty_ax.
*auto with *.
*auto with *.
*apply Tr_body_wf; trivial.
 apply Fbot_typ.
*apply wf_Form.
 apply Fbot_typ.
Qed.
Lemma FTr_and : forall i P Q,
    P ∈ Form ->
    Q ∈ Form ->
    FTr (Fand P Q) i <-> FTr P i /\ FTr Q i.
intros.
unfold FTr.
unfold Fintrec.
rewrite ZFrepl.WFR_eqn.
*unfold Tr_body; rewrite Form_case_and; trivial.
 unfold p2P.
 rewrite inter2_def.
 reflexivity.
*auto with *.
*auto with *.
*apply Tr_body_wf; trivial.
 apply Fand_typ; trivial.
*apply wf_Form.
 apply Fand_typ; trivial.
Qed.
Lemma FTr_or : forall i P Q,
    P ∈ Form ->
    Q ∈ Form ->
    FTr (For P Q) i <-> FTr P i \/ FTr Q i.
intros.
unfold FTr.
unfold Fintrec.
rewrite ZFrepl.WFR_eqn.
*unfold Tr_body; rewrite Form_case_or; trivial.
 unfold p2P.
 rewrite union2_ax.
 reflexivity.
*auto with *.
*auto with *.
*apply Tr_body_wf; trivial.
 apply For_typ; trivial.
*apply wf_Form.
 apply For_typ; trivial.
Qed.
Lemma FTr_imp : forall i P Q,
    P ∈ Form ->
    Q ∈ Form ->
    FTr (Fimp P Q) i <-> (FTr P i -> FTr Q i).
intros.
unfold FTr.
unfold Fintrec.
rewrite ZFrepl.WFR_eqn.
*unfold Tr_body; rewrite Form_case_imp; trivial.
 rewrite P2p2P; reflexivity.
*auto with *.
*auto with *.
*apply Tr_body_wf; trivial.
 apply Fimp_typ; trivial.
*apply wf_Form.
 apply Fimp_typ; trivial.
Qed.

Lemma FTr_fa : forall i P,
    P ∈ Form ->
    FTr (Ffa P) i <-> (forall x:set, FTr P (Cons x i)).
intros.
unfold FTr.
unfold Fintrec.
rewrite ZFrepl.WFR_eqn.
*unfold Tr_body; rewrite Form_case_fa; trivial.
 rewrite P2p2P; reflexivity.
*auto with *.
*auto with *.
*apply Tr_body_wf; trivial.
 apply Ffa_typ; trivial.
*apply wf_Form.
 apply Ffa_typ; trivial.
Qed.
Lemma FTr_ex : forall i P,
    P ∈ Form ->
    FTr (Fex P) i <-> (exists x:set, FTr P (Cons x i)).
intros.
unfold FTr.
unfold Fintrec.
rewrite ZFrepl.WFR_eqn.
*unfold Tr_body; rewrite Form_case_ex; trivial.
 rewrite P2p2P; reflexivity.
*auto with *.
*auto with *.
*apply Tr_body_wf; trivial.
 apply Fex_typ; trivial.
*apply wf_Form.
 apply Fex_typ; trivial.
Qed.

End UnboundedInterpretation.
#[global]Existing Instance UnboundedInterpretation.FTr_morph.

Module BoundedInterpretation.

  Section Bounded.

    Variable M :set.
    Hypothesis ConsM : forall x i, x ∈ M -> i ∈ M -> Cons x i ∈ M.
    
    Definition subForm_M x :=
      prodcart (subForm (fst x)) M.

    Instance subForm_M_morph : morph1 subForm_M.
do 2 red; intros.
unfold subForm_M; rewrite H; reflexivity.
Qed.

      Lemma subForm_M_typ x y :
      x ∈ subForm_M y -> fst y ∈ Form -> fst x ∈ Form.
intros.
apply fst_typ in H.
revert H0; apply subForm_typ; trivial.
Qed.

    Lemma clos_subFrom_M_typ x y :
      ZFrepl.WFRle subForm_M x y -> fst y ∈ Form -> fst x ∈ Form.
induction 1;[|auto].
destruct H as [e|?]; [rewrite e; trivial|apply subForm_M_typ; trivial].
Qed.
    Lemma clos_subFrom_M_typ_snd x y :
      ZFrepl.WFRle subForm_M x y -> snd y ∈ M -> snd x ∈ M.
induction 1;[|auto].
destruct H as [e|H]; [rewrite e; trivial|apply snd_typ in H; trivial].
Qed.
    
    Lemma wf_FormM P x : P ∈ Form -> Acc (fun x y => x ∈subForm_M y) (couple P x).
intros ty.
revert x; elim wf_Form with (1:=ty); intros; constructor; intros.
constructor; intros.
apply Acc_inv with (couple (fst y)(snd y)).
*clear y0 H2.
 apply H0.
 apply fst_typ in H1. 
 rewrite fst_def in H1; trivial.
*rewrite <- surj_pair with (1:=H1); trivial.
Qed.

  Definition Tr_body i f :=
  Form_case (fun i0 j => P2p (Fint_var i i0 == Fint_var i j))
    (fun i0 j => P2p (Fint_var i i0 ∈ Fint_var i j)) empty
    (fun A B => f (couple A i) ∩ f (couple B i))
    (fun A B => f (couple A i) ∪ f (couple B i))
    (fun A B => cc_arr (f (couple A i)) (f (couple B i)))
    (fun A => P2p (forall x0, x0 ∈ M -> p2P (f (couple A (Cons x0 i)))))
    (fun A => P2p (exists x0, x0 ∈ M /\ p2P (f (couple A (Cons x0 i))))).

    Definition Fintrec : set -> set :=
      WFR subForm_M
        (fun Fint Pl => Tr_body (snd Pl) Fint (fst Pl)).
    
    Definition FTr (P:set) (l:set) : Prop := p2P (Fintrec (couple P l)).

    Local Lemma auxm1 i : morph2 (fun i0 j => P2p (Fint_var i i0 == Fint_var i j)).
intros ?? h ?? h'; rewrite h,h'; reflexivity.
Qed.
    Local Lemma auxm2 i : morph2 (fun i0 j => P2p (Fint_var i i0 ∈ Fint_var i j)).
intros ?? h ?? h'; rewrite h,h'; reflexivity.
Qed.
    Hint Resolve auxm1 auxm2 : core.
    
    Lemma Tr_body_wf P i :
      P ∈ Form -> i ∈ M ->
      forall x x' f f',
        ZFrepl.WFRle subForm_M x (couple P i) ->
        (forall y y', y ∈ subForm_M x -> y == y' -> f y == f' y') ->
        x == x' ->
        Tr_body (snd x) f (fst x) == Tr_body (snd x') f' (fst x').
intros Pty ity x x' f f' xle eqf eqx.
assert (subfo : fst x ∈ Form)
  by (apply clos_subFrom_M_typ with (1:=xle); rewrite fst_def;trivial).
assert (subi : snd x ∈ M)
  by (apply clos_subFrom_M_typ_snd with (1:=xle); rewrite snd_def; trivial).
unfold Tr_body.
rewrite <- eqx. 
destruct (Form_case_split _ subfo) as
   [(k&?&k'&?&e)|[(k&?&k'&?&e)|
                   [e|[(A&?&B&?&e)|[(A&?&B&?&e)|[(A&?&B&?&e)|[(A&?&e)|(A&?&e)]]]]]]];
   rewrite e;
   [rewrite !Form_case_eq|rewrite !Form_case_in|rewrite !Form_case_bot|rewrite !Form_case_and
   |rewrite !Form_case_or|rewrite !Form_case_imp|rewrite !Form_case_fa|rewrite !Form_case_ex]; trivial.
*rewrite eqx; reflexivity.
*rewrite eqx; reflexivity.
*reflexivity.
*apply inter2_morph;
    (apply eqf; auto with *; [|rewrite eqx; reflexivity]);
    unfold subForm_M,subForm; rewrite e,Form_case_and; auto;apply couple_intro; auto.
*apply union2_morph;
    (apply eqf; auto with *; [|rewrite eqx; reflexivity]);
    unfold subForm_M,subForm; rewrite e,Form_case_or; auto;apply couple_intro; auto.
*apply cc_arr_morph;
    (apply eqf; auto with *; [|rewrite eqx; reflexivity]);
    unfold subForm_M,subForm; rewrite e,Form_case_imp; auto;apply couple_intro; auto.
*apply P2p_morph; apply fa_morph; intro; apply impl_morph;[reflexivity|intros].
 apply p2P_morph; apply eqf; [|rewrite eqx;reflexivity].
 apply couple_intro; [|apply ConsM]; trivial.
 unfold subForm_M,subForm; rewrite e,Form_case_fa; auto; apply singl_intro.
*apply P2p_morph; apply ex_morph; intro; apply and_iff_morphisml;[reflexivity|intros].
 apply p2P_morph; apply eqf; [|rewrite eqx;reflexivity].
 apply couple_intro; [|apply ConsM]; trivial.
 unfold subForm_M,subForm; rewrite e,Form_case_ex; auto; apply singl_intro.
Qed.
    
Lemma FTr_eq : forall i m n,
    i ∈ M -> m ∈ N -> n ∈ N ->
    FTr (Feq m n) i <-> Fint_var i m == Fint_var i n.
intros.
unfold FTr.
unfold Fintrec.
rewrite WFR_eqn.
*rewrite fst_def.
 unfold Tr_body; rewrite Form_case_eq; trivial.
rewrite snd_def.
 rewrite P2p2P; reflexivity.
*auto with *.
*apply Tr_body_wf;[|trivial].
 apply Feq_typ; trivial.
*apply wf_FormM.
 apply Feq_typ; trivial.
Qed.

Lemma FTr_fa : forall i P,
    i ∈ M ->
    P ∈ Form ->
    FTr (Ffa P) i <-> (forall x, x ∈ M -> FTr P (Cons x i)).
intros.
unfold FTr.
unfold Fintrec.
rewrite WFR_eqn.
*rewrite fst_def.
 unfold Tr_body; rewrite Form_case_fa; trivial.
 rewrite P2p2P; intros.
 apply fa_morph; intros x.
 apply impl_morph; [reflexivity|intro].
 apply p2P_morph.
 apply WFR_morph0.
 rewrite snd_def; reflexivity.
*auto with *.
*apply Tr_body_wf;[|trivial].
 apply Ffa_typ; trivial.
*apply wf_FormM.
 apply Ffa_typ; trivial.
Qed.
  End Bounded.
  
End BoundedInterpretation.



(*Parameter Fint : set -> set -> Prop.*)
Definition Fint i P := UnboundedInterpretation.FTr P i.
Lemma Fint_eq : forall i m n,
  m ∈ N -> n ∈ N ->
  Fint i (Feq m n) <-> Fint_var i m == Fint_var i n.
intros; apply UnboundedInterpretation.FTr_eq; trivial.
Qed.
Lemma Fint_in : forall i m n,
  m ∈ N -> n ∈ N ->
  Fint i (Fin m n) <-> Fint_var i m ∈ Fint_var i n.
intros; apply UnboundedInterpretation.FTr_in; trivial.
Qed.
Lemma Fint_bot : forall i, ~ Fint i Fbot.
apply UnboundedInterpretation.FTr_bot.
Qed.
Lemma Fint_and : forall i P Q,
  P ∈ Form -> Q ∈ Form ->
  Fint i (Fand P Q) <-> (Fint i P /\ Fint i Q).
intros; apply UnboundedInterpretation.FTr_and; trivial.
Qed.
Lemma Fint_or : forall i P Q,
  P ∈ Form -> Q ∈ Form ->
  Fint i (For P Q) <-> (Fint i P \/ Fint i Q).
intros; apply UnboundedInterpretation.FTr_or; trivial.
Qed.
Lemma Fint_imp : forall i P Q,
  P ∈ Form -> Q ∈ Form ->
  Fint i (Fimp P Q) <-> (Fint i P -> Fint i Q).
intros; apply UnboundedInterpretation.FTr_imp; trivial.
Qed.
Lemma Fint_fa : forall i P,
  P ∈ Form ->
  Fint i (Ffa P) <-> (forall x:set, Fint (Cons x i) P).
intros; apply UnboundedInterpretation.FTr_fa; trivial.
Qed.
Lemma Fint_ex : forall i P,
  P ∈ Form ->
  Fint i (Fex P) <-> (exists x:set, Fint (Cons x i) P).
intros; apply UnboundedInterpretation.FTr_ex; trivial.
Qed.

#[global]Instance Fint_morph : Proper (eq_set==>eq_set==>iff) Fint.
do 3 red; intros; apply UnboundedInterpretation.FTr_morph; trivial.
Qed.


Require Import ZFfo.

Lemma fo_Fint u v :
  fo_in u ->
  fo_in v ->
  fo_form (fun i => Fint (u i) (v i)).
Admitted.


(* Predicate fo_form stands for predicates that can be represented by
   a formula *)
Lemma fo_form_ex P :
  fo_form P ->
  exists A, A ∈ Form /\ forall vs l, (forall k, Fint_var l (nat2set k) == vs k) ->
                                     P vs <-> Fint l A.
induction 1.
*destruct IHfo_form as (Q & Qty & Qdef); exists Q;split;[trivial|intros].
 rewrite <-H; auto.
*destruct H as (k,?). 
 destruct H0 as (k',?). 
 subst  x y.
 exists (Feq (nat2set k) (nat2set k')); split.
  apply Feq_typ; apply nat2set_typ. 
 intros. 
 rewrite Fint_eq;[|apply nat2set_typ|apply nat2set_typ].
 rewrite !H; reflexivity.
*destruct H as (k,?). 
 destruct H0 as (k',?). 
 subst  x y.
 exists (Fin (nat2set k) (nat2set k')); split.
  apply Fin_typ; apply nat2set_typ. 
 intros. 
 rewrite Fint_in;[|apply nat2set_typ|apply nat2set_typ].
 rewrite !H; reflexivity.
*exists (Fimp Fbot Fbot); split;[apply Fimp_typ; apply Fbot_typ|]. 
 intros.  
 rewrite Fint_imp;[|apply Fbot_typ|apply Fbot_typ].
 split; intros; trivial.
*exists Fbot; split; [apply Fbot_typ|intros].
 split; intros; [contradiction|].
 apply Fint_bot in H0; trivial.
*destruct IHfo_form1 as (A'&?&?).
 destruct IHfo_form2 as (B'&?&?).
 exists (Fand A' B'); split; [apply Fand_typ; trivial|intros].
 rewrite Fint_and; trivial.
 apply and_iff_morphism; auto.
*destruct IHfo_form1 as (A'&?&?).
 destruct IHfo_form2 as (B'&?&?).
 exists (For A' B'); split; [apply For_typ; trivial|intros].
 rewrite Fint_or; trivial.
 apply or_iff_morphism; auto.
*destruct IHfo_form1 as (A'&?&?).
 destruct IHfo_form2 as (B'&?&?).
 exists (Fimp A' B'); split; [apply Fimp_typ; trivial|intros].
 rewrite Fint_imp; trivial.
 apply impl_morph; auto.
*destruct IHfo_form as (B'&?&?).
 exists (Ffa B'); split; [apply Ffa_typ; trivial|intros].
 rewrite Fint_fa; trivial.
 apply fa_morph; intros x.
 rewrite <-H1 with (vs:=icons x vs).
 +unfold bind; simpl.
  reflexivity.
 +destruct k; simpl.
  apply Fiv_0.
  rewrite Fiv_S; trivial.
*destruct IHfo_form as (B'&?&?).
 exists (Fex B'); split; [apply Fex_typ; trivial|intros].
 rewrite Fint_ex; trivial.
 apply ex_morph; intros x.
 rewrite <-H1 with (vs:=icons x vs).
 +reflexivity.
 +destruct k; simpl.
  apply Fiv_0.
  rewrite Fiv_S; trivial.
Qed.

