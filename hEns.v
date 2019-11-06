Require Import ZFskol.
Require Import Sublogic.
Require Import paths hott.
Import TrSubThms.

Require Import EnsZ.

(** In this file, we give an attempt to build a model of IZF
   in Coq + prop-truncation + predicate-extensionality
 *)
Axiom fun_ext : type_fun_ext.
Axiom univ : set_univ.
Axiom univ_comp : set_univ_comp univ.

Axiom pred_ext : type_predicate_ext.

(*Instance pred_ext : type_predicate_ext.
red; intros.
apply fun_ext; intros x.
apply univ with
  (fun p => tr_elim (H0 x) (proj1 (H1 x) (tr_i p)))
  (fun q => tr_elim (H x) (proj2 (H1 x) (tr_i q))).
 apply isSet_prop; trivial.
 split; intros.
  apply H.
  apply H0.
Qed.
*)

(* Equality of families *)

Definition eq_fam {X X':Ti}{Y} (f:X->Y) (f':X'->Y) :=
  (forall i, #exists j, f i = f' j) /\
  (forall j, #exists i, f i = f' j).

Lemma eq_fam_refl {X Y f} : @eq_fam X X Y f f.
split; intros.
 apply tr_i; exists i; trivial.
 apply tr_i; exists j; trivial.
Qed.
  
Lemma eq_fam_sym {X X' Y f f'} : @eq_fam X X' Y f f' -> eq_fam f' f.
destruct 1; split; intros.
 generalize (H0 i); apply TrMono.
 intros (j,?); exists j; auto.

 generalize (H j); apply TrMono.
 intros (i,?); exists i; auto.
Qed.

Lemma eq_fam_trans {X1 X2 X3 Y} {f1:X1->Y}{f2:X2->Y}{f3:X3->Y} :
  eq_fam f1 f2 -> eq_fam f2 f3 -> eq_fam f1 f3.
intros (e12,e21) (e23,e32).
split.
 intros i1.
 elim (e12 i1) using tr_ind_tr; intros (i2,ef12).
 elim (e23 i2) using tr_ind_tr; intros (i3,ef23).
 apply tr_i; exists i3; transitivity (f2 i2); trivial.

 intros i3.
 elim (e32 i3) using tr_ind_tr; intros (i2,ef32).
 elim (e21 i2) using tr_ind_tr; intros (i1,ef21).
 apply tr_i; exists i1; transitivity (f2 i2); trivial.
Qed.

Lemma eq_fam_comp {X X' Y Y'} (f:Y->Y'){g:X->Y}{g':X'->Y}:
  eq_fam g g' -> eq_fam (fun i => f (g i)) (fun i => f (g' i)).
destruct 1; split; intros.
 Tdestruct (H i) as (j,?). 
 Texists j; f_equal; trivial.

 Tdestruct (H0 j) as (i,?). 
 Texists i; f_equal; trivial.
Qed.

(*Hint Resolve tr_prop isProp_forall isProp_conj.*)

Definition eq_fam_set {Y} (p q:{X:Ti & X->Y}) :=
  eq_fam (projT2 p) (projT2 q).
Instance isRel_eq_fam {Y} : isRel (@eq_fam_set Y).
split.
 unfold eq_fam_set, eq_fam; auto with *.

 split; red; intros.
  split; intros.
   Texists i; trivial.
   Texists j; trivial.

 apply eq_fam_sym; trivial.

 destruct H; destruct H0.
 split; intros.
  Tdestruct (H i) as (j,?).
  Tdestruct (H0 j) as (k,?).
  rewrite <- H3 in H4.
  Texists k; auto.

  Tdestruct (H2 j) as (i,?).
  Tdestruct (H1 i) as (k,?).
  rewrite H3 in H4.
  Texists k; auto.
Qed.

Section Ker. (** 1- Using univalence (truncated at set level) *)
Import Quo1. (* Need a copy of quo at another universe level... univ poly needed! *)
(* Quo is used at level Tj, Quo1 at level Ti *)


Variable Y:Tj.
Hypothesis Ys : isSet Y.

(* The index function of a set, unique up to equivalence...
   obtained by identifying indices that yield the same set. *)

Definition ker (X:Ti) (f:X->Y) : Ti :=
  quo X (fun x y => f x = f y).


Instance isRel_ker {X:Ti}(f:X->Y): isRel (fun x y => f x = f y).
split; intros.
 red; intros; apply Ys.
split; red; intros; eauto.
transitivity (f y); trivial.
Qed.

Definition ker_i {X:Ti}(f:X->Y) (x:X) : ker X f :=
  quo_i (isRel_ker _) x.

Definition ker_map (X:Ti) (f:X->Y) (i:ker X f) : Y.
elim i using (quo_ind_set_nodep _ Ys) with (h:=f).
trivial.
Defined.

Definition ker_set (X:Ti) (f:X->Y) : {X:Ti & X->Y} :=
  existT (fun X:Ti=>X->Y) (ker X f) (ker_map X f).

(** Unicity of ker up to isomorphism *)

Definition ker_f0 {X X':Ti} {f:X->Y} {f':X'->Y} :
  eq_fam f f' ->
  X -> ker X' f'.
assert (Hr := isRel_ker f).
assert (Hr' := isRel_ker f').
assert (Hs := isSet_quo X' (fun x0 y0 : X' => f' x0 = f' y0) Hr').
pose (f1:= fun i (x : {x : X' | f i = f' x}) => ker_i f' (proj1_sig x)).
assert (inv1 : forall i x y, f1 i x = f1 i y).
 intros.
 apply quo_i_eq.
 transitivity (f i).
  symmetry; apply (proj2_sig x).
  apply (proj2_sig y).
intros eqf x.
exact (tr_ind_set_nodep _ _ Hs _ (inv1 x) (proj1 tr_ex_sig (proj1 eqf x))).
Defined.

Definition ker_f {X X':Ti} {f:X->Y} {f':X'->Y} :
  eq_fam f f' -> ker X f -> ker X' f'.
assert (Hr := isRel_ker f).
assert (Hr' := isRel_ker f').
assert (Hs := isSet_quo X' (fun x0 y0 : X' => f' x0 = f' y0) Hr').
intros eqf k.
eapply quo_ind_set_nodep with (1:=Hr) (2:=Hs) (h:=ker_f0 eqf) (4:=k).
intros.
unfold ker_f0; intros.
apply tr_ind_set_nodep_ind.
 red; intros; apply isSet_quo; auto with *. 
intros (x',?).
apply tr_ind_set_nodep_ind.
 red; intros; apply isSet_quo; auto with *. 
intros (y',?).
apply quo_i_eq; simpl.
rewrite <- e, <- e0; trivial.
Defined.

Lemma ker_f_eq {X X':Ti} {f:X->Y} {f':X'->Y} (eqf:eq_fam f f') i j :
  f i = f' j -> ker_f eqf (ker_i f i) = ker_i f' j.
intros.
unfold ker_f, ker_i, quo_ind_set_nodep.
rewrite quo_ind_set_eq.
unfold ker_f0.
apply tr_ind_set_nodep_ind.
 red; intros; apply isSet_quo; auto with *. 
intros (j',?); simpl.
apply quo_i_eq.
rewrite <- H, <- e; trivial.
Qed.

Lemma ker_f_id {X X':Ti} {f:X->Y} {f':X'->Y} (eqf:eq_fam f f')(eqf':eq_fam f' f) x :
  ker_f eqf' (ker_f eqf x) = x.
elim x using (quo_ind _).
 red; intros; apply isSet_quo; auto with *.
intros i.
fold (ker_i f i).
elim (proj1 tr_ex_sig (proj1 eqf i)) using tr_ind.
 red; intros; apply isSet_quo; auto with *.
intros (j,?).
rewrite ker_f_eq with (j0:=j); trivial.
apply ker_f_eq; auto.
Qed.

Definition ker_map_def (X:Ti) (f:X->Y) (i:ker X f) :
  tr{i':X & ker_i _ i' = i /\ f i' = ker_map X f i}.
elim i using (quo_ind _).
 intros; apply tr_prop.
intros x.
apply tr_i; exists x.
split;[reflexivity|].
unfold ker_map, quo_ind_set_nodep.
rewrite quo_ind_set_eq.
reflexivity.
Qed.

Lemma eq_fam_ker (X:Ti) (f:X->Y) :
  eq_fam f (ker_map X f).
split; intros.
 apply tr_i; exists (ker_i f i). 
 unfold ker_i, ker_map, quo_ind_set_nodep.
 rewrite quo_ind_set_eq; trivial.

 apply tr_ind_tr with (2:=ker_map_def X f j).
 intros (i,(?,?)).
 apply tr_i; exists i; trivial.
Qed.


Definition fam := Quo.quo {X:Ti&X->Y} eq_fam_set.

Lemma fams : isSet fam.
apply Quo.isSet_quo.
apply isRel_eq_fam.
Qed.

Definition isDecomp (a:fam) (q:{X:Ti & X->Y}) : Prop :=
  isSet (projT1 q) /\
  (forall x x', projT2 q x = projT2 q x' -> x=x') /\
  a = Quo.quo_i _ q.

Lemma isProp_isDecomp a q :
  isProp (isDecomp a q).
red; intros.
assert (Xs := proj1 x).
revert x y; apply isProp_conj.
 apply isProp_forall; intros.
 apply isProp_forall; intros.
 apply isProp_forall; intros.
 apply isProp_forall; intros.
 red; intros; apply is_prop_uip.
 red; intros; apply Xs.
apply isProp_conj.
 apply isProp_forall; intros.
 apply isProp_forall; intros.
 apply isProp_forall; intros.
 red; intros; apply Xs.

 red; intros; apply fams.
Qed.

Definition decomp_fam (a:fam) :=
  { s:{X:Ti & X->Y} | isDecomp a s }.

Lemma decomp_ker X f :
  isDecomp (Quo.quo_i _ (existT (fun X:Ti=>X->Y) X f)) (ker_set X f).
split;[|split]; simpl.
 (* ker is a set *)
 apply isSet_quo; auto with *.

 (* ker_map is injective *)
 intros.
 apply tr_ind_nodep with (3:=ker_map_def X f x).
  red; intros; apply isSet_quo; auto with *.
 intros (i,(?,?)).
 apply tr_ind_nodep with (3:=ker_map_def X f x').
  red; intros; apply isSet_quo; auto with *.
 intros (i',(?,?)).
 rewrite <-H1,<-H3 in H.
 rewrite <-H0,<-H2; apply quo_i_eq; trivial.

 (* (X,f) and ker_set X f are equal families *)
 apply Quo.quo_i_eq.
 apply eq_fam_ker.
Qed.

Definition decomp_tr (a:fam) : tr(decomp_fam a).
pattern a.
elim a using (Quo.quo_ind _); auto with *.
intros (X,f); apply tr_i.
exists (ker_set X f).
apply decomp_ker.
Defined.


Lemma isDecomp_eqv a q q' :
  isDecomp a q ->
  isDecomp a q' ->
  let (X,f) := q in let (X',g) := q' in
  { E:eqv X X' | forall i:X', f (eg E i) = g i }.
destruct q as (X,f); destruct q' as (X',g);
  intros (Xs&finj&eqa) (X's&ginj&eqa'); simpl in *.
rewrite eqa in eqa'.
apply Quo.quo_i_eq in eqa'.
assert (forall i:X, {j:X' | f i = g j}).
 intros.
 apply descr.
  red; intros; apply Ys.
  intros.
  rewrite H in H0; apply ginj in H0; trivial.

  apply (proj1 tr_ex_sig).
  apply eqa'.

assert (forall j:X', {i:X| f i = g j}).
 intros.
 apply descr.
  red; intros; apply Ys.
  intros.
  rewrite <-H0 in H; apply finj in H; trivial.

  apply (proj1 tr_ex_sig).
  apply eqa'.
pose (ff :=fun i => proj1_sig (X0 i)).
pose (gg := fun j => proj1_sig (X1 j)).
assert (eggff : forall i, gg (ff i) = i).
  intros.
  unfold ff, gg.
  destruct (X0 i); simpl.
  destruct (X1 x); simpl.
  rewrite <- e in e0; apply finj in e0; auto.
assert (effgg : forall j, ff (gg j) = j).
  intros.
  unfold ff, gg.
  destruct (X1 j); simpl.
  destruct (X0 x); simpl.
  rewrite e0 in e; apply ginj in e; auto.
exists (mkE ff gg eggff effgg); simpl.
unfold gg; intros.
destruct (X1 i); simpl; trivial.
Qed.

(** We need univalence at set level (in universe Ti) from now on... *)

Lemma isDecomp_uniq a q q' :
  isDecomp a q ->
  isDecomp a q' ->
  q=q'.
intros.
destruct q as (X,f); destruct q' as (X',g).
destruct (isDecomp_eqv _ _ _ H H0) as (E,Ef); simpl in *.
apply @sigT_eq_intro with (e:=univ _ _ _ _ (proj1 H) (conj (egf E) (efg E))); simpl.
red.
rewrite transport_dom.
apply fun_ext.
intros j.
rewrite <- Ef.
f_equal.
apply transport_r2l with (P:=fun X=>X).
assert (aux:=univ_comp); red in aux; rewrite aux; clear aux.
symmetry; apply (efg E).
Qed.

Lemma isProp_decomp a :
  isProp (decomp_fam a).
red; intros (q,?) (q',?).
apply sig_intro; simpl.
 intros; apply isProp_isDecomp.
 apply isDecomp_uniq with a; trivial.
Qed.

Definition decomp (a:fam) : decomp_fam a.
elim (decomp_tr a) using tr_ind_nodep; trivial.
apply isProp_decomp.  
Defined.

Lemma decomp_eq X (f:X->Y) :
  proj1_sig (decomp (Quo.quo_i _ (existT(fun X=>X->Y) X f))) =
  ker_set X f.
unfold decomp.
unfold decomp_tr.
rewrite Quo.quo_ind_eq.
rewrite tr_ind_nodep_eq; simpl.
reflexivity.
Qed.

End Ker.



(******************************************************************************)
(** * The type of intensional sets *)

Module Z := Zermelo TrSubThms.
Import Z.

  Notation eq_iset := Z.eq_set.

  Lemma isProp_eq_iset x y : isProp (eq_iset x y).
revert x y; intros (X,f) (Y,g); simpl.
apply isProp_conj.
 apply isProp_forall; intros i.
 apply tr_prop.

 apply isProp_forall; intros i.
 apply tr_prop.
Qed.

  Lemma isProp_in_set x y : isProp (Z.in_set x y).
apply tr_prop.
Qed.

Hint Resolve isProp_eq_iset isProp_in_set.
  
  Instance isRel_eq_iset : isRel eq_iset.
split.
 apply isProp_eq_iset.  

 split; auto with *.
Qed.


Module SetsQuo <: WfSetTheory TrSubThms.

  Definition isup (c:{X:Ti & X->iset}) : iset := Z.isup (projT1 c) (projT2 c).

  Definition unsup (x:iset) := let (X,f) := x in existT (fun X:Ti=>X->iset) X f.

  (* The type of extensional sets *)
  Definition set := quo iset eq_iset.

  Lemma isSet_set : isSet set.
apply isSet_quo; auto with *.
Qed.


  Definition mks (x:iset) : set := quo_i _ x.
  
  Definition unfold_set (x:set) : fam set.
pose (f:= fun x:iset => quo_i _ (existT (fun X:Ti=>X->set)
                               (projT1 (unsup x))
                               (fun i => mks (projT2 (unsup x) i)))).
apply quo_ind_set_nodep with (h:=f) (4:=x); auto with *.
 apply fams.

 intros.
 unfold f.
 apply quo_i_eq.
 red; simpl.
 destruct x0 as (x0); destruct y as (y); simpl in *.
 destruct r as (xy,yx).
 split; intros.
  Tdestruct (xy i) as (j,?).
  Texists j.
  apply quo_i_eq; trivial.

  Tdestruct (yx j) as (i,?).
  Texists i.
  apply quo_i_eq; trivial.
Defined.

Lemma unfold_set_eq X f :
  unfold_set (quo_i _ (Z.isup X f)) =
  quo_i _ (existT(fun X:Ti=>X->set) X (fun i => mks (f i))).
unfold unfold_set.
unfold quo_ind_set_nodep.
rewrite quo_ind_set_eq.
simpl.
reflexivity.
Qed.


Definition Ker (a:set) : Ti :=
  projT1 (proj1_sig (decomp _ isSet_set (unfold_set a))).
Definition Kerf (a:set) : Ker a -> set :=
  projT2 (proj1_sig (decomp _ isSet_set (unfold_set a))).


  (* Equality *)
  Definition eq_set (x y:set) := x=y.

Lemma eq_set_intro x y :
  eq_fam (Kerf x) (Kerf y) ->
  x = y.
elim x using (quo_ind _).
 intros; apply isProp_forall.
 red; intros; apply isSet_set.
intros (X,f).
elim y using (quo_ind _).
 intros; apply isProp_forall.
 red; intros; apply isSet_set.
intros (Y,g).
unfold Kerf, Ker.
rewrite !unfold_set_eq.
rewrite !decomp_eq.  
simpl.
intros (xy,yx).
apply quo_i_eq.
simpl.
destruct (eq_fam_ker _ isSet_set X (fun i => mks(f i))) as (e1,e2).
destruct (eq_fam_ker _ isSet_set Y (fun i => mks(g i))) as (f1,f2).
split; intros.
 specialize xy with (ker_i _ isSet_set (fun i => mks(f i)) i). 
 elim xy using (tr_ind_tr _).
 clear xy; intros (j,?).
 elim (f2 j) using tr_ind_tr.
 intros (i',?); apply tr_i; exists i'.
 rewrite <- H in H0.
 unfold ker_map, ker_i, Quo1.quo_ind_set_nodep in H0.
 rewrite Quo1.quo_ind_set_eq in H0.
 apply quo_i_eq in H0; symmetry; trivial.

 elim (f1 j) using tr_ind_tr.
 intros (k,?).
 elim (yx k) using tr_ind_tr.
 intros (k',?).
 elim (e2 k') using tr_ind_tr.
 intros (i,?); apply tr_i; exists i.
 rewrite H0,<-H in H1.
 apply quo_i_eq in H1; trivial.
Qed.


  (* Membership *)
  Definition in_set (x y:set) : Prop :=
    tr{j:Ker y & x = Kerf y j}.
  Notation "x ∈ y" := (in_set x y).

  Lemma in_iset_ax z (X:Ti) f :
      z ∈ mks (Z.isup X f) <->
      tr{i:X| z = mks (f i)}.
unfold in_set.
unfold Ker, Kerf.
rewrite unfold_set_eq.
rewrite decomp_eq.
simpl.
destruct (eq_fam_ker _ isSet_set X (fun i => mks (f i))) as (e1,e2).
split; intros.
 elim H using tr_ind_tr; clear H.
 intros (k,?).
 elim (e2 k) using tr_ind_tr.
 intros (i,?).
 apply tr_i; exists i; rewrite H; trivial.

 elim H using tr_ind_tr; clear H.
 intros (i,?). 
 elim (e1 i) using tr_ind_tr.
 intros (j,?).
 rewrite H in e.
 apply tr_i; exists j; trivial.
Qed. 

  Lemma eq_set_ax a b : a = b <-> (forall x, x ∈ a <-> x ∈ b).
split; [intros; subst a; reflexivity|].
intros.
apply eq_set_intro.
split; intros.
 destruct H with (Kerf a i).
 elim H0 using tr_ind_tr.
  intros (j,?); Texists j; trivial.

  apply tr_i; exists i; trivial.

 destruct H with (Kerf b j).
 elim H1 using tr_ind_tr.
  intros (i,?); Texists i; auto.

  apply tr_i; exists j; trivial.
Qed.

  Lemma in_reg a a' b : a = a' -> a ∈ b -> a' ∈ b.
intros; subst a'; trivial.
Qed.

  (* Well-foundation *)
(*
  Lemma isProp_Acc A R (x:A) : isProp (Acc R x).
red; revert x; fix Hrec 2; intros x (a1) (a2).
f_equal.
apply fun_ext; intros y.
apply fun_ext; intros r.
apply Hrec.
Qed.

  Lemma acc_in_set (x:set) : Acc in_set x.
elim x using (quo_ind _).
 intros; apply isProp_Acc.    
clear x; intros x.
revert x; fix acc 1; intros ((X,f)).
assert (Hrec := fun i => acc (f i)); clear acc.
constructor; intros.
apply in_iset_ax in H.
elim H using tr_ind_nodep.
 apply isProp_Acc.
intros (i,?); subst y; trivial.
Qed.
*)

  Lemma wf_ax_iset (P:set->Type) :
    (forall x, isProp (P x)) ->
    (forall x, (forall y, in_set y x -> P y) -> P x) ->
    forall x:iset, P (quo_i _ x).
intros Pp Hrec.
fix acc 1.
intros (X,f); simpl.
apply Hrec; intros.
rewrite in_iset_ax in H.
elim H using tr_ind;[auto|].
clear H.
intros (i,?); subst y.
apply acc.
Qed.

  Lemma wf_ax :
  forall (P:set->Prop),
  (forall x, (forall y, in_set y x -> #P y) -> #P x) -> forall x, #P x.
intros.
apply quo_ind with (Rr:=isRel_eq_iset) (x:=x).
 intros; apply tr_prop.

 intros.
 apply wf_ax_iset; auto with *.
Qed.

  (** from set to iset *)

  Inductive set_cano (x:set) : iset -> Prop :=
  | ISC_sup f :
      (forall i, set_cano (Kerf x i) (f i)) ->
      set_cano x (Z.isup (Ker x) f).


  Lemma set_cano_ok x y : set_cano x y -> x = mks y.
induction 1.
clear H.
apply eq_set_ax; intros z.
rewrite in_iset_ax.
split; apply tr_map.
 intros (i,?); exists i.
 rewrite <- H0; trivial.
 
 intros (i,?); exists i.
 rewrite H0; trivial.
Qed.

  Lemma set2iset_cano (x:set) : isContr {y|set_cano x y}.
elim x using (quo_ind _).
 intros; apply (isProp_isContr _).
clear x; intros x.
pattern (quo_i _ x).
elim x using wf_ax_iset.
 intros; apply (isProp_isContr _).
clear x; intros x Hrec.
red in Hrec.
assert (kin: forall i, in_set (Kerf x i) x).
 red; intros.
 apply tr_i; exists i; trivial.
assert (Hreck := fun i => Hrec _ (kin i)).
clear kin Hrec.
pose (y:=isup(existT(fun X=>X->iset)(Ker x)(fun i => proj1_sig(projT1(Hreck i))))).
pose (yc:=ISC_sup _ _ (fun i => proj2_sig(projT1(Hreck i)))).
exists (exist (set_cano x) y yc).
intros (z,zc).
destruct zc.
unfold yc.
pose (h := fun (f_Hf:{f:Ker x->iset|forall i, set_cano (Kerf x i) (f i)}) =>
             exist (set_cano x)
                   (Z.isup (Ker x) (proj1_sig f_Hf))
                   (ISC_sup x (proj1_sig f_Hf) (proj2_sig f_Hf))).
change (h (exist (fun f => forall i, set_cano (Kerf x i)(f i)) f s) =
        h (exist (fun f => forall i, set_cano (Kerf x i)(f i))
                 (fun i => proj1_sig(projT1(Hreck i))) (fun i => proj2_sig(projT1(Hreck i))))).
apply f_equal with (f:=h).
apply sig_eq
 with (e:=fun_ext_singl
            (fun i => f_equal (fun x => proj1_sig x)
                        (projT2 (Hreck i) (exist (set_cano (Kerf x i)) (f i) (s i))))); simpl.
unfold eqD.
rewrite transport_rng.
apply fun_ext; intros i.
rewrite transport_app.
rewrite fun_ext_eqv2.
exact (sig_proj2(projT2 (Hreck i) (exist (set_cano(Kerf x i)) (f i) (s i)))).
Qed.

Definition set2iset (x:set) : iset :=
  proj1_sig (proj1_sig (set2iset_cano x)).

Definition set2iset_ok x : x = mks (set2iset x).
apply set_cano_ok.
apply (proj2_sig (proj1_sig (set2iset_cano x))).
Qed.
Print Assumptions set2iset_ok. (* set univalence (+ fun_ext) + truncation *)

Definition sup (X:Ti) (f:X->set) : set :=
  mks (Z.isup X (fun i => set2iset (f i))).

Lemma in_set_ax a X f :
  a ∈ sup X f <-> #exists i:X, a = f i.
unfold sup.
rewrite in_iset_ax.
split; intros.
 elim H using tr_ind_tr; clear H.
 intros (i,e).
 rewrite <- set2iset_ok in e.
 apply tr_i; exists i; trivial.

 elim H using tr_ind_tr; clear H.
 intros (i,e).
 apply tr_i; exists i; trivial.
 rewrite <- set2iset_ok; trivial.
Qed.

Lemma eq_set_iset a :
  Z.eq_set a (set2iset (mks a)).
assert (mks a = mks (set2iset (mks a))).
 rewrite <- set2iset_ok; trivial.
apply quo_i_eq in H; trivial.
Qed. 

Lemma sup_eqv X f :
  mks (Z.isup X f) = sup X (fun i => mks (f i)).
unfold sup.
apply quo_i_eq.
apply Z.eq_set_ax.
split; apply tr_map; simpl; intros (j,?); exists j.
 rewrite H; apply eq_set_iset.
 rewrite H; symmetry; apply eq_set_iset.
Qed.

Lemma in_set_eqv z a :
  in_set (mks z) (mks a) <-> Z.in_set z a.
destruct a as (X,f).
rewrite sup_eqv.
rewrite in_set_ax.
split; apply tr_map; intros (i,?); exists i.
 apply quo_i_eq in H; trivial.

 apply quo_i_eq; trivial.
Qed.

(** Definite choice: uch_single P = {x} if P holds only for x *)

Definition uch_single (P:set->Prop) : set :=
  sup (tr{z|#P z} /\ isProp{z| #P z})
      (fun c => let (w,p) := c in proj1_sig (tr_elim p w)).

Lemma uch_single_ax P z :
  isProp {x:set|#P x} ->
  (in_set z (uch_single P) <-> #P z).
intros Hp.
unfold uch_single; rewrite in_set_ax.
split; intros.
 elim H using tr_ind_tr; clear H.
 intros ((w,Hp'),?); simpl.
 destruct (tr_elim Hp' w); simpl in *.
 subst z; trivial.

 apply tr_i; exists (conj (tr_i (exist (fun z=>tr(P z)) z H)) Hp).
 destruct (tr_elim Hp (tr_i (exist (fun z=>tr(P z)) z H))); simpl.
 assert (aux := Hp (exist (fun z=>tr(P z)) z H) (exist (fun z=>tr(P z)) x t)).
 apply f_equal with (f:=fun x=>proj1_sig x) in aux; simpl in aux.
 trivial. 
Qed.

  Lemma uch_single_mono P Q :
  (forall x, P x <-> Q x) ->
  forall z, z ∈ uch_single P -> z ∈ uch_single Q.
intros.
assert (tr_iff : forall x, tr (P x) <-> tr (Q x)).
 split; intros h; elim h using tr_ind_tr; intro; apply tr_i; apply H; trivial.
assert (isProp {z|tr(P z)}).
 unfold uch_single in H0.
 rewrite in_set_ax in H0.
 elim H0 using tr_ind.
  intros; apply isProp_isProp.
 intros ((?,?),_); trivial.
assert (isProp {z|tr(Q z)}).
 red; intros.
 apply sig_intro; auto with *.
 destruct x as (x,?); destruct y as (y,?); simpl.
 assert (aux := H1 (exist (fun z=>tr(P z)) x (proj2 (tr_iff _) t)) (exist (fun z=>tr(P z)) y (proj2 (tr_iff _) t0))).
 apply f_equal with (f:=fun x=>proj1_sig x) in aux; simpl in aux.
 trivial.
rewrite uch_single_ax in H0; trivial.
rewrite uch_single_ax; trivial.
elim H0 using tr_ind_tr; clear H0; intros.
apply tr_i; apply H; trivial.
Qed.


End SetsQuo.


Import SetsQuo.

Module ZF <: IZF_R_sig TrSubThms.

  Include Z.
  Infix "∈" := Z.in_set.
  Infix "==" := Z.eq_set.

  Definition repl (a:set) (R:set->set->Prop) : set :=
    Z.replf (subset a (fun x => exists w, R x w))
            (fun x => union(set2iset(SetsQuo.uch_single (fun w => R x (set2iset w))))).

  Lemma repl_ax a (R:set->set->Prop) :
    (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x ∈ a -> R x y -> R x y' -> y == y') ->
    forall x, x ∈ repl a R <-> #exists2 y, y ∈ a & R y x.
intros Rm Runiq z.
unfold repl.
pose (P x y := R x (set2iset y)).
assert (Hp : forall x, x ∈ a -> isProp {z|#R x (set2iset z)}).
 intros x tyx (w,Rw) (w',Rw').
 apply sig_intro; simpl; auto with *.
 rewrite (set2iset_ok w), (set2iset_ok w').
 apply quo_i_eq.
 elim Rw using tr_ind; auto.
 clear Rw; intros Rw.
 elim Rw' using tr_ind; auto.
 clear Rw'; intros Rw'.
 apply Runiq with x; auto.
assert (Hext : forall x y, x ∈ a -> R x y ->
                            y == union (set2iset (uch_single (fun w => R x (set2iset w))))).
 intros; apply eq_set_ax; intros z'.
 rewrite union_ax.
 split; intros.  
  Texists y; trivial.
  apply in_set_eqv.
  rewrite <- set2iset_ok.
  apply uch_single_ax; auto.
  apply tr_i.
  apply Rm with x y; auto with *.
  apply eq_set_iset.

  elim H1 using tr_ind; auto.
  clear H1; intros (b, ?,?).
  apply in_set_eqv in H2.
  rewrite <- set2iset_ok in H2.
  apply uch_single_ax in H2; auto.
  elim H2 using tr_ind; auto.
  clear H2; intros.
  assert (y==b).
   rewrite (eq_set_iset b).
   apply Runiq with x; auto.
  eapply eq_set_ax;[apply H2|apply H1].
rewrite replf_ax.
split; intros.
 elim H using tr_ind_tr; clear H; intros.
 destruct H as (y,?,?).
 apply subset_ax in H.
 destruct H as (?,?).
 elim H1 using tr_ind_tr; clear H1; intros.
 destruct H1 as (y',?,(w,?)).
 assert (z == w).
  rewrite H0.
  symmetry; apply Hext; trivial.
  apply Rm with y' w; auto with *.
  apply in_reg with y; auto.
 Texists y; trivial.
 apply Rm with y' w; auto with *.
 apply in_reg with y; auto.

 elim H using tr_ind_tr; clear H; intros.
 destruct H as (y,?,?).
 apply tr_i; exists y; auto.
 apply subset_ax.
 split; trivial. 
 Texists y; auto with *.
 exists z; trivial.

 intros.
 replace (uch_single (fun w => R z0 (set2iset w))) with
         (uch_single (fun w => R z' (set2iset w))); auto with *.
 apply subset_ax in H; destruct H as (?,_).
 assert (forall w, R z' (set2iset w) <-> R z0 (set2iset w)).
  split; apply Rm; auto with *.
  apply in_reg with z0; auto. 
 apply SetsQuo.eq_set_ax; intros z1.
 split; apply uch_single_mono; trivial.
 symmetry; auto.
Qed.
 
Lemma repl_mono a a' :
    (forall z, z ∈ a -> z ∈ a') ->
    forall (R R':set->set->Prop),
    (forall x x', x==x' -> forall y y', y==y' -> (R x y <-> R' x' y')) ->
    forall z, z ∈ repl a R -> z ∈ repl a' R'.
unfold repl.
intros incl R R' Req z tyz.
rewrite replf_ax in tyz|-*.
 revert tyz; apply tr_map; intros (y,?,?); exists y.
  apply subset_ax in H; destruct H.
  apply subset_ax; split; auto.
  revert H1; apply tr_map; intros (z',?,(w,?)); exists z'; auto.
  exists w; auto with *.
  revert H2; apply Req; auto with *.

  replace (uch_single (fun w => R' y (set2iset w))) with
          (uch_single (fun w => R y (set2iset w))); auto with *.
  apply SetsQuo.eq_set_ax; intros z1.
  split; apply uch_single_mono; auto with *.
  symmetry; apply Req; auto with *.

 intros.
 replace (uch_single (fun w => R z0 (set2iset w))) with
         (uch_single (fun w => R z' (set2iset w))); auto with *.
 apply SetsQuo.eq_set_ax; intros z1.
 split; apply uch_single_mono; intros.
  transitivity (R' z' (set2iset x)); auto with *.
  symmetry; auto with *.
  transitivity (R' z' (set2iset x)); auto with *.
  symmetry; auto with *.

 intros.
 replace (uch_single (fun w => R' z0 (set2iset w))) with
         (uch_single (fun w => R' z' (set2iset w))); auto with *.
 apply SetsQuo.eq_set_ax; intros z1.
 split; apply uch_single_mono; intros.
  transitivity (R z' (set2iset x)); auto with *.
  symmetry; auto with *.
  transitivity (R z' (set2iset x)); auto with *.
  symmetry; auto with *.
Qed.

End ZF.

Section TestZF.
Import ZF.
Definition test_zf :=
  (eq_set_ax,wf_ax,pair_ax,power_ax,infinity_ax1,infinity_ax2,union_ax,repl_ax,repl_mono).
Print Assumptions test_zf. (* set univalence + resized prop-truncation *)
End TestZF.


(** * The type of sets defined as a HIT *)

Module SetsHit <: IZF_R_sig TrSubThms.
    
(** We assume we can build an type "set" equivalent
    to the quotiented indexed families of sets *)
Parameter set : Type.
Parameter set_def : eqv set (fam set). (* missing: well-foundation *)
Definition unfold_set := ef set_def.
Definition fold_set := eg set_def.
Lemma fold_unfold_eq x : fold_set (unfold_set x) = x.
apply (egf set_def).
Qed.
Lemma unfold_fold_eq x : unfold_set (fold_set x) = x.
apply (efg set_def).
Qed.

Lemma isSet_set : isSet set.
apply isSet_by_eqv with (2:=set_def).
apply isSet_quo; auto with *.
Qed.

Definition sup (X:Ti) (f:X->set) : set :=
  fold_set (quo_i _ (existT (fun X=>X->set) X f)).

Lemma eq_fam_def {X X' f f'}:
  eq_fam f f' <-> sup X f = sup X' f'.
Proof.
unfold sup.
split.
 intros.
 apply f_equal with (f:=fold_set).
 apply (proj2 (quo_i_eq _)).
 exact H.

 intros.
 apply f_equal with (f:=unfold_set) in H.
 rewrite !unfold_fold_eq in H.
 apply quo_i_eq in H.
 exact H.
Defined.

Definition set_ind_prop (P:set->Type) (Pp : forall x, isProp(P x))
    (h: forall (X:Ti) (f:X->set), P (sup X f)) (x:set) : P x :=
  transport P (fold_unfold_eq x)
  (quo_ind (X:={X:Ti&X->set}) isRel_eq_fam
              (fun x => P (fold_set x)) (fun _ => Pp _)
              (fun p:{X:Ti&X->set} => match p with existT X f => h X f end)
              (unfold_set x)).

Definition set_comp (P:set->Type) (h:forall X f, P (sup X f)) :=
 forall X X' f f' (r : eq_fam f f'), eqD P ((let (h,_) := eq_fam_def in h) r) (h X f) (h X' f').


Definition unf_set_comp (P:set->Type) (h:forall X f, P (sup X f)) :=
 forall (x y : {X : Ti & X -> set}) (r : eq_fam_set x y),
 eqD (fun x0 : quo {X : Ti & X -> set} eq_fam_set => P (fold_set x0))
          (proj2 (quo_i_eq isRel_eq_fam) r)
           (let (X, f) as p0 return (P (fold_set (quo_i _ p0))) := x in h X f)
           (let (X, f) as p0 return (P (fold_set (quo_i _ p0))) := y in h X f).

Lemma mk_comp P (h:forall X f, P (sup X f)) :
  set_comp P h ->
  unf_set_comp P h.
unfold set_comp, unf_set_comp.
intros.
red.
rewrite <- transport_f_equal with (P:=P) (f:=fold_set).
destruct x as (X,f); destruct y as (X',f').
red in r; simpl in r.
unfold eq_fam_def in H; simpl in H.
exact (H _ _ _ _ r).
Qed.

Definition set_ind (P:set->Type) (Ps : forall x, isSet(P x))
    (h: forall (X:Ti) (f:X->set), P (sup X f)) (hcomp:set_comp P h) (x:set) : P x :=
  transport P (fold_unfold_eq x)
  (quo_ind_set {X:Ti&X->set} eq_fam_set isRel_eq_fam
              (fun x => P (fold_set x)) (fun _ => Ps _)
              (fun p:{X:Ti&X->set} => match p with existT X f => h X f end)
              (mk_comp _ _ hcomp) (unfold_set x)).

Lemma set_ind_eq P Ps h hcomp X f :
  set_ind P Ps h hcomp (sup X f) = h X f.
unfold set_ind, sup.
set (q := quo_i _ (existT (fun X:Type=>X->set) X f)) in *.
replace (fold_unfold_eq (fold_set q)) with (f_equal fold_set (eq_sym(eq_sym(unfold_fold_eq q)))).  
2:apply isSet_set.
rewrite transport_f_equal.
case (eq_sym (unfold_fold_eq q)); simpl.
unfold q.
rewrite quo_ind_set_eq; reflexivity.
Qed.

Definition set_comp_nodep (P:Type) (h:forall X:Ti,(X->set)->P) :=
 forall X X' f f' (r : eq_fam f f'), h X f = h X' f'.

Lemma set_comp_nodep_intro {P h} (c:set_comp_nodep P h) :
  set_comp (fun _ => P) h.
red; intros.
red in c.
rewrite <- (c _ _ _ _ r).
apply transport_cst.
Defined.
Definition set_ind_nodep (P:Type) (Ps : isSet P)
           (h: forall (X:Ti) (f:X->set), P) (hcomp:set_comp_nodep P h) (x:set) : P :=
  set_ind (fun _ => P) (fun _ => Ps) h (set_comp_nodep_intro hcomp) x.

Definition eq_set := @eq set.


Definition in_set (x y:set) : Prop :=
  #exists X:Ti, exists2 f:X->set, y = sup X f & exists j:X, x = f j.

Lemma isProp_in_set x y : isProp (in_set x y).
apply tr_prop.
Qed.

Hint Resolve isProp_in_set.

Lemma in_set_ax X f x :
  in_set x (sup X f) <-> #exists i:X, x = f i.
split; intros.
 Tdestruct H as (X',(f',eqf,(j,?))).
 apply eq_fam_def in eqf.
 Tdestruct (proj2 eqf j) as (i,?).
 rewrite <- H0 in H.
 Texists i; trivial.

 elim H using tr_ind; auto.
 intros (i,?).
 Texists X; eauto.
Qed.

Lemma eq_set_ax x y :
  x = y <-> (forall z, in_set z x <-> in_set z y).
split; intros.
 subst y; auto with *.

 revert H.
 elim x using set_ind_prop.
  intros; apply isProp_forall; red; intros; apply isSet_set.
 intros X f.
 elim y using set_ind_prop.
  intros; apply isProp_forall; red; intros; apply isSet_set.
 intros X' f'.
 intro.
 apply eq_fam_def.
 split; intros.
  apply in_set_ax.
  apply H.   
  apply in_set_ax.
  Texists i; trivial.

  destruct (H (f' j)).
  apply in_set_ax in H1.
   Tdestruct H1 as (i,?).
   Texists i; auto.

   apply in_set_ax.
   Texists j; trivial.
Qed.   

Lemma in_reg : forall x x' y,
  x = x' -> in_set x y -> in_set x' y.
intros; subst x'; trivial.
Qed.

  Lemma wf_ax :
  forall (P:set->Prop),
  (forall x, (forall y, in_set y x -> #P y) -> #P x) -> forall x, #P x.
Admitted.

(** Empty set *)
Definition empty :=
  sup False (False_rect _).

Lemma empty_ax : forall x, in_set x empty -> #False.
intros.
apply in_set_ax in H.
elim H using tr_ind_tr; auto.
intros ([ ],_).
Qed.

(** Pairing *)

Definition pair (a b:set) : set :=
  sup bool (fun z => if z then a else b).

Lemma pair_ax a b z :
  in_set z (pair a b) <-> #(z=a \/ z=b).
unfold pair; rewrite in_set_ax.
split; apply TrMono; intros.
 destruct H as ([|],?); auto.

 destruct H; [exists true|exists false]; trivial.
Qed.

(** Subset *)

Definition subset_fam (X:Ti) (f:X->set) (P:set->Prop) :=
  sup {i:X | tr (P (f i))} (fun i => f (proj1_sig i)).

Lemma subset_fam_ext {P P':set->Prop} {X X' f f'} :
  @eq_fam X X' _ f f' ->
  (forall z, tr (P z) <-> tr (P' z)) ->
  subset_fam X f P = subset_fam X' f' P'.
intros (ff',f'f) eqP.
unfold subset_fam.
apply eq_fam_def.
split; intros.
 destruct i as (i,?); simpl.
 Tdestruct (ff' i) as (j,?).
 rewrite H in t.
 apply eqP in t.
 Texists (exist (fun i => tr (P' (f' i))) j t); simpl; trivial.

 destruct j as (j,?); simpl.
 Tdestruct (f'f j) as (i,?).
 rewrite <- H in t.
 apply eqP in t.
 Texists (exist (fun i => tr (P (f i))) i t); simpl; trivial.
Qed.

Lemma subset_fam_comp P :
  set_comp_nodep set (fun X f => subset_fam X f P).
red; intros.
apply subset_fam_ext; trivial.
reflexivity.
Qed.

Definition subset (a:set) (P:set->Prop) : set :=
  set_ind_nodep set isSet_set
    (fun X f => subset_fam X f P) (subset_fam_comp P) a.

Lemma subset_fam_ax X f P z :
  in_set z (subset_fam X f P) <-> (in_set z (sup X f) /\ #P z).
unfold subset_fam; do 2 rewrite in_set_ax.
split; intros.
 Tdestruct H as ((i,?),?); simpl in *; subst z.
 split; trivial.
 Texists i; trivial.

 destruct H as (H,H'); elim H using tr_ind_tr.
 clear H; intros (i,eqz); subst z.
 Texists (exist (fun i => tr (P (f i))) i H'); trivial.
Qed.

Lemma subset_ax0 a P z :
  in_set z (subset a P) <-> (in_set z a /\ #P z).
unfold subset.
elim a using set_ind_prop; auto with *.
intros.
unfold set_ind_nodep; rewrite set_ind_eq.
apply subset_fam_ax.
Qed.
Lemma subset_ax a P z :
  in_set z (subset a P) <-> (in_set z a /\ #exists2 z', z=z' & P z').
rewrite subset_ax0.
apply and_iff_morphism; auto with *.
split; apply TrMono; intros; auto.
 exists z; trivial.

 destruct H as (z',?,?); subst z'; trivial.
Qed.

(** Powerset *)

Definition power_fam (X:Ti) (f:X->set) :=
  sup (X->Prop)
   (fun P => subset_fam X f (fun y => exists2 i, y = f i & P i)).

Lemma power_fam_comp :
  set_comp_nodep set (fun X f => power_fam X f).
red; intros; unfold power_fam.
apply eq_fam_def.
split; intros.
 Texists (fun j => exists2 k, f k = f' j & i k).
 apply subset_fam_ext; trivial.
 split; intros.
  Tdestruct H as (k,?,?). 
  subst z.
  Tdestruct (proj1 r k) as (j,?). 
  Texists j; trivial.
  exists k; trivial.

  Tdestruct H as (k,?,(j,?,?)). 
  subst z.
  Texists j; auto.

 Texists (fun i => exists2 k, f i = f' k & j k).
 apply subset_fam_ext; trivial.
 split; intros.
  Tdestruct H as (k,?,(i,?,?)). 
  subst z.
  Texists i; auto.

  Tdestruct H as (k,?,?). 
  subst z.
  Tdestruct (proj2 r k) as (i,?). 
  Texists i; auto.
  exists k; trivial.
Qed.

Definition power (a:set) : set :=
  set_ind_nodep set isSet_set
    (fun X f => power_fam X f) power_fam_comp a.

Lemma power_ax a z :
  in_set z (power a) <-> forall x, in_set x z -> in_set x a.
elim a using set_ind_prop; auto with *.
intros.
unfold power, set_ind_nodep; rewrite set_ind_eq.
unfold power_fam; rewrite in_set_ax.
split; intros.
 rewrite in_set_ax.
 Tdestruct H as (P,?); subst z.
 rewrite subset_fam_ax in H0.
 destruct H0.
 Tdestruct H0 as (i,?,_).
 Texists i; trivial. 

 Texists (fun i => in_set (f i) z).
 revert H; elim z using set_ind_prop.
  intros; apply isProp_forall; intros.
  red; intros; apply isSet_set.
 intros X' f' ?. 
 apply eq_fam_def.
 split; intros.
  assert (in_set (f' i) (sup X' f')). 
   apply in_set_ax; Texists i; trivial.
  specialize H with (1:=H0).
  apply in_set_ax in H.
  Tdestruct H as (j,?).
  assert (tr (exists2 i':X, f j = f i' & in_set (f i') (sup X' f'))). 
   Texists j; trivial.
   rewrite <- H; trivial.
  Texists (exist (fun i =>  tr(exists2 i', f i = f i' & _)) j H1); trivial.

  destruct j as (i,?); simpl.
  Tdestruct t as (i',?,?).
  apply in_set_ax in H1.
  Tdestruct H1 as (j,?).
  Texists j.
  rewrite H0; auto.
Qed.


(** Union *)

Definition Ker (a:set) : Ti :=
  projT1 (proj1_sig (decomp _ isSet_set (unfold_set a))).
Definition Kerf (a:set) : Ker a -> set :=
  projT2 (proj1_sig (decomp _ isSet_set (unfold_set a))).

Lemma Kerf_ax x y :
  in_set x y <-> #exists i, x = Kerf y i.
unfold in_set.
unfold Ker,Kerf.
destruct (decomp _ isSet_set (unfold_set y)) as ((X,f),(?,(?,eqy))); simpl in *.
apply f_equal with (f:=fold_set) in eqy.
rewrite fold_unfold_eq in eqy.
subst y.
split; intros.
 elim H using tr_ind_tr; intros (Y,(g,?,(j,?))).
 apply eq_fam_def in H0.
 destruct H0 as (_,?).
 Tdestruct (H0 j) as (i',?).
 Texists i'.
 subst x; auto.

 Tdestruct H as (i',?).
 Texists X.
 exists f; trivial.
 exists i'; trivial.
Qed.

Lemma Kerf_in x i : in_set (Kerf x i) x.
apply Kerf_ax.
Texists i; trivial.
Qed.

Definition union_fam (X:Ti) (Y:X->Ti) (f:forall x,Y x->set) : set :=
  sup { x:X & Y x } (fun p => f (projT1 p) (projT2 p)).

Definition union (a:set) : set :=
  union_fam (Ker a) (fun x => Ker (Kerf a x)) (fun x y => Kerf (Kerf a x) y).

Lemma union_ax a z :
  in_set z (union a) <-> #exists2 y, in_set z y & in_set y a.
unfold union, union_fam.
rewrite in_set_ax.
split; intros.
 elim H using (tr_ind_tr _); intros ((i,j),eqz); simpl in eqz.
 Texists (Kerf a i).
  rewrite eqz; apply Kerf_in.
  apply Kerf_in.

 elim H using (tr_ind_tr _); intros (y,?,?).
 apply Kerf_ax in H1.
 elim H1 using (tr_ind_tr _); intros (i,?).   
 subst y.
 apply Kerf_ax in H0.
 elim H0 using (tr_ind_tr _); intros (j,?).   
 Texists (existT (fun i =>Ker(Kerf a i)) i j).
 trivial.
Qed.
Print Assumptions union_ax.
Print Assumptions power_ax.

(** Infinity *)

Fixpoint num n :=
  match n with
      0 => empty
    | S n => let x := num n in union (pair x (pair x x))
  end.
Definition infinite := sup _ num.
Lemma infinity_ax1 : in_set empty infinite.
apply in_set_ax.
Texists 0; trivial.
Qed.

Lemma infinity_ax2 x :
  in_set x infinite ->
  in_set (union (pair x (pair x x))) infinite.
intros.
apply in_set_ax; apply in_set_ax in H.
Tdestruct H as (n,?).
subst x.
Texists (S n); trivial.
Qed.


Definition replf_fam (X:Ti) (f:X->set) (F:set->set) : set :=
  sup X (fun i => F (f i)).

Lemma replf_fam_ext {F F':set->set} {X X' f f'} :
  @eq_fam X X' _ f f' ->
  (forall z, F z = F' z) ->
  replf_fam X f F = replf_fam X' f' F'.
intros (ff',f'f) eqF.
unfold replf_fam.
apply eq_fam_def.
split; intros.
 Tdestruct (ff' i) as (j,?).
 rewrite H.
 Texists j; auto.

 Tdestruct (f'f j) as (i,?).
 rewrite <- H.
 Texists i; auto.
Qed.

Lemma replf_fam_comp F :
  set_comp_nodep set (fun X f => replf_fam X f F).
red; intros; apply replf_fam_ext; auto.
Qed.

Definition replf (a:set) (F:set->set) : set :=
  set_ind_nodep set isSet_set
    (fun X f => replf_fam X f F) (replf_fam_comp F) a.

Lemma replf_ax a F z :
  in_set z (replf a F) <-> #exists2 x, in_set x a & z = F x.
elim a using set_ind_prop; auto with *.
intros.
unfold replf, set_ind_nodep; rewrite set_ind_eq.
unfold replf_fam; rewrite in_set_ax.
split.
 apply TrMono; intros.
 destruct H as (i,?); subst z.
 exists (f i); trivial.
 apply in_set_ax.
 Texists i; trivial.

 intros H; Tdestruct H as (x,?,?); subst z.
 apply in_set_ax in H.
 Tdestruct H as (i,?); subst x.
 Texists i; trivial.
Qed.

Lemma in_set_sup (X:Ti) (f:X->set) (i:X) : in_set (f i) (sup X f).
apply in_set_ax.  
Texists i; reflexivity.
Defined.
Lemma in_set1 (X:Ti) (f:X->set) (i:X) : {x|in_set x (sup X f)}.
exists (f i).
apply in_set_sup.
Defined.

Definition repl1_fam (X:Ti) (f:X->set) (F:{x:set|in_set x (sup X f)}->set) : set :=
  sup X (fun i => F (in_set1 X f i)).

Lemma repl1_fam_ext {X X' f f'} {F:_->set} {F':_->set}:
  @eq_fam X X' _ f f' ->
  (forall z z', proj1_sig z = proj1_sig z' -> F z = F' z') ->
  repl1_fam X f F = repl1_fam X' f' F'.
intros (ff',f'f) eqF.
unfold repl1_fam.
apply eq_fam_def.
split; intros.
 Tdestruct (ff' i) as (j,?).
 Texists j.
 apply eqF; simpl; trivial.

 Tdestruct (f'f j) as (i,?).
 Texists i; auto.
Qed.

  
Lemma repl1_fam_comp :
  set_comp (fun a=>({x:set|in_set x a}->set)->set) (repl1_fam).
red; intros.
red.
set (h := (let (h,_) := eq_fam_def in h) r).
apply fun_ext; intros F.
transitivity (repl1_fam X f (transport (fun a => {x:set|in_set x a}->set) (eq_sym h) F)).
 destruct h; simpl; reflexivity.

 apply repl1_fam_ext; auto.
 intros.
 transitivity (F (transport (fun a => {x|in_set x a}) h z)).
  destruct h; simpl; reflexivity.

  apply f_equal with (f:=F).
  apply sig_intro; auto.
  revert z' H.
  destruct h; simpl.
  trivial.
Qed.

Definition repl1 (a:set) (F:{x|in_set x a}->set) : set :=
  set_ind (fun a => ({x|in_set x a}->set)->set) (fun _ => isSet_forall (fun _ => isSet_set))
    (fun X f F => repl1_fam X f F) (repl1_fam_comp) a F.

Lemma repl1_ax a F z :
  in_set z (repl1 a F) <-> #exists x, z = F x.
revert F; elim a using set_ind_prop; auto with *.
intros.
unfold repl1; rewrite set_ind_eq.
unfold repl1_fam; rewrite in_set_ax.
split.
 apply TrMono; intros.
 destruct H as (i,?); subst z.
 exists (in_set1 X f i); trivial.

 intros H; Tdestruct H as ((x,?),?); simpl; subst z.
 assert (H:=i); apply in_set_ax in H.
 Tdestruct H as (i',?); subst x.
 Texists i'; trivial.
 f_equal.
 apply sig_intro; simpl; auto.
Qed.

Definition uch_pred (P:set->Prop) :=
  (forall y, isProp (P y)) /\
  (forall y y', P y -> P y' -> y=y') /\
  #exists y, P y.
Definition repl_rel (R:set->set->Prop) :=
  forall x, uch_pred (R x).

Lemma isProp_uch P : isProp (uch_pred P).
apply isProp_conj; auto.
 apply isProp_forall; intros; apply isProp_isProp.
apply isProp_conj; auto with *.
apply isProp_forall; intros.
apply isProp_forall; intros.
apply isProp_forall; intros.
apply isProp_forall; intros.
red; intros; apply isSet_set.
Qed.

Definition uch (P:set->Prop) (Puc:uch_pred P) : set :=
  proj1_sig (descr (proj1 Puc) (proj1(proj2 Puc))
                   (proj1 tr_ex_sig (proj2(proj2 Puc)))).

Definition repl0 (a:set) (R:set->set->Prop) (Rr:repl_rel R) :=
  replf a (fun x => uch (R x) (Rr x)).

Lemma sub_uch a R (x:{x|in_set x (subset a (fun x => uch_pred (R x)))}) :
  uch_pred (R (proj1_sig x)).
destruct x; simpl in *.
apply subset_ax0 in i.
destruct i as (_,h).
apply tr_elim; trivial.
apply isProp_uch.
Qed.

Definition repl (a:set) (R:set->set->Prop) :=
  let R x y := # R x y in
  repl1 (subset a (fun x => uch_pred (R x)))
        (fun x => uch (R (proj1_sig x)) (sub_uch a R x)).

Lemma repl_ax0 a (R:set->set->Prop) x :
 in_set x (repl a R) <-> #exists2 y, in_set y a & R y x /\ forall x', R y x' -> x=x'.
intros.
unfold repl.
rewrite repl1_ax.
split; intros.
 Tdestruct H as ((z,?),?); simpl in *.
 assert (h:=i); apply subset_ax0 in h.
 destruct h.
 Tdestruct H1 as (?,(?,?)).
 Tdestruct H3 as (y,?).
 elim H3 using tr_ind_tr; intros.
 Texists z; trivial.
 split.
  replace x with y; trivial.
  subst x.
  symmetry; apply descr_eq; trivial.

  intros; subst x.
  apply descr_eq; trivial.
  apply tr_i; trivial.

 Tdestruct H as (y, ?, (?,?)).
 assert (in_set y (subset a (fun x => uch_pred (fun z => #R x z)))).
  apply subset_ax0.
  split; trivial.
  apply tr_i; split; intros; auto with *.
  split; intros.
   elim H2 using tr_ind; intros.
    red; intros; apply isSet_set.
   elim H3 using tr_ind; intros.
    red; intros; apply isSet_set.
   transitivity x; eauto.
   symmetry; eauto.

   Texists x; trivial.
   apply tr_i; trivial.
 Texists (exist (fun x => in_set x _) y H2); simpl.
 symmetry; apply descr_eq; trivial.
 apply tr_i; trivial.
Qed.

Lemma repl_ax: forall a (R:set->set->Prop),
    (forall x x' y y', in_set x a -> x = x' -> y = y' -> R x y -> R x' y') ->
    (forall x y y', in_set x a -> R x y -> R x y' -> y = y') ->
    forall x, in_set x (repl a R) <-> #exists2 y, in_set y a & R y x.
intros.
rewrite repl_ax0; trivial.  
split; apply TrMono; intros.
 destruct H1 as (y,?,(?,?)); eauto.

 destruct H1 as (y,?,?).
 exists y; trivial.
 split; trivial.
 eauto.
Qed.
Print Assumptions repl_ax.

Lemma repl_mono: forall a a',
    (forall z, in_set z a -> in_set z a') ->
    forall (R R':set->set->Prop),
    (forall x x', x=x' -> forall y y', y=y' -> (R x y <-> R' x' y')) ->
    forall z, in_set z (repl a R) -> in_set z (repl a' R').
intros.
apply repl_ax0 in H1.
elim H1 using tr_ind; auto.
clear H1; intros (y,?,(?,?)).
apply repl_ax0.
Texists y; auto.
split.
 apply (H0 y y eq_refl z z eq_refl); trivial.

 intros.
 apply H3.
 apply (H0 y y eq_refl x' x' eq_refl); trivial.
Qed.

End SetsHit.

Section TestHIT.
Import SetsHit.
Definition test :=
  (eq_set_ax,wf_ax,pair_ax,power_ax,infinity_ax1,infinity_ax2,union_ax,repl_ax,repl_mono).
Print Assumptions test.
End TestHIT.


(** Construction of ZF axioms directly on the quotiented type *)

Module SetsQuoEnd <: IZF_R_sig TrSubThms.

Include SetsQuo.

(** Empty set *)

Definition empty := sup False (fun abs => False_rect _ abs).

Lemma empty_ax x : x ∈ empty -> #False.
intros.
apply in_set_ax in H.
elim H using tr_ind_tr.
intros ([],_).
Qed.

(** Pair *)

Definition pair (a b:set) :=
  sup bool (fun c => if c then a else b).

Lemma pair_ax a b x : x ∈ pair a b <-> #(x = a \/ x = b).
unfold pair; rewrite in_set_ax.
split; intros H; elim H using tr_ind_tr; clear H; intros H; apply tr_i.
 destruct H as ([|],?); auto.

 destruct H;[exists true|exists false]; trivial.
Qed.

(** Union *)

Definition union (a:set) :=
  sup {i:Ker a & Ker (Kerf a i)}
      (fun c => Kerf (Kerf a (projT1 c)) (projT2 c)).

Lemma union_ax a x : x ∈ union a <-> #exists2 y, x ∈ y & y ∈ a.
unfold union; rewrite in_set_ax.
split; intros.  
 elim H using tr_ind_tr; clear H; intros ((i,j),?); simpl in *.
 apply tr_i; exists (Kerf a i).
  rewrite H; apply tr_i; exists j; trivial.

  apply tr_i; exists i; trivial.

 elim H using tr_ind_tr; clear H; intros (y,?,?).
 elim H using tr_ind_tr; clear H; intros (j,?).
 elim H0 using tr_ind_tr; clear H0; intros (i,?).
 subst y.
 apply tr_i; exists (existT (fun i => Ker(Kerf a i)) i j); simpl; trivial.
Qed.

(** Subset *)

Definition subset (a:set) (P:set -> Prop) :=
  sup {i:Ker a|P (Kerf a i)}
      (fun i => Kerf a (proj1_sig i)).

Lemma subset_ax a P x :
    x ∈ subset a P <-> (x ∈ a /\ #exists2 x', x=x' & P x').
unfold subset; rewrite in_set_ax.
split; intros.
 elim H using tr_ind.
  intros; apply isProp_conj; auto with *.
  apply tr_prop.
 clear H; intros ((i,Hp),?); simpl in *.
 split.
  rewrite H; apply tr_i; exists i; trivial. 

  apply tr_i; exists (Kerf a i); auto.

 destruct H.
 elim H0 using tr_ind_tr; clear H0.  
 intros (x',?,?); subst x'.
 elim H using tr_ind_tr; clear H.
 intros (i,?).
 rewrite e in H1.
 apply tr_i; exists (exist (fun i => P(Kerf a i)) i H1); trivial.
Qed.

(** Infinity *)

Fixpoint num (n:nat) :=
  match n with
  | 0 => empty
  | S k => let ks := num k in union (pair ks (pair ks ks))
  end.

Definition infinite := sup nat num.

Lemma infinity_ax1: empty ∈ infinite.
apply in_set_ax.
apply tr_i; exists 0; trivial.
Qed.

Lemma infinity_ax2 x :
  x ∈ infinite -> union (pair x (pair x x)) ∈ infinite.
intros.
apply in_set_ax in H.
apply in_set_ax.  
elim H using tr_ind_tr; clear H.
intros (n,?).
apply tr_i; exists (S n); simpl.
subst x; trivial.
Qed.

(** Powerset *)

Definition power (a:set) :=
  sup (Ker a->Prop) (fun P => subset a (fun z => exists2 i, P i & z = Kerf a i)).

Lemma power_ax a x : x ∈ power a <-> (forall y, y ∈ x -> y ∈ a).
unfold power; rewrite in_set_ax.
split; intros.
 elim H using tr_ind_tr; clear H.
 intros (P,?).
 subst x.
 apply subset_ax in H0.
 destruct H0; trivial.

 apply tr_i; exists (fun i:Ker a => Kerf a i ∈ x).
 apply eq_set_ax.
 intros z.
 rewrite subset_ax.
 split; intros.
  split; auto.
  elim H with (1:=H0) using tr_ind_tr.
  intros (i,?).
  apply tr_i; exists z; trivial.
  exists i; auto.
  rewrite <- e; trivial.

  destruct H0.
  elim H1 using tr_ind_tr; clear H1.
  intros (x',?,(i,?,?)); subst x'.
  elim H2 using tr_ind_tr; clear H2.
  intros (j,?).
  apply tr_i; exists j.
  rewrite <- e; trivial.
Qed.

(** Replacement *)

Definition uch (P:set->Prop) : set := union (uch_single P).

Lemma uch_eq (P:set->Prop) x :
  isProp {z | tr(P z)} ->
  P x ->
  uch P = x.
unfold uch; intros.
apply eq_set_ax; intros z.
rewrite union_ax.
split; intros.
 elim H1 using tr_ind_tr; clear H1.
 intros (y,?,?).
 rewrite uch_single_ax in H2; trivial.
 assert (aux := H (exist (fun z=>tr(P z)) x (tr_i H0)) (exist (fun z=>tr(P z)) y H2)).
 apply f_equal with (f:=fun x=>proj1_sig x) in aux; simpl in aux.
 rewrite <- aux in H1; trivial.

 apply tr_i; exists x; trivial.
 apply uch_single_ax; trivial.
 apply tr_i; trivial.
Qed. 


Lemma uch_ext P Q :
  (forall x, P x <-> Q x) ->
  uch P = uch Q.
intros.
unfold uch.
apply eq_set_ax; intros z.
rewrite !union_ax.
split; intros.
 elim H0 using tr_ind_tr; clear H0.
 intros (y,?,?).
 apply tr_i; exists y; trivial.
 revert H1; apply uch_single_mono; trivial.
 
 elim H0 using tr_ind_tr; clear H0.
 intros (y,?,?).
 apply tr_i; exists y; trivial.
 revert H1; apply uch_single_mono; trivial.
 symmetry; trivial.
Qed.

Definition repl (a:set) (R:set->set->Prop) :=
  sup {i:Ker a|tr{z|#R(Kerf a i) z} /\ isProp{z| #R (Kerf a i) z}}
      (fun i => uch (R (Kerf a (proj1_sig i)))).


Lemma repl_mono a a' :
    (forall z, z ∈ a -> z ∈ a') ->
    forall (R R':set->set->Prop),
    (forall x x', x=x' -> forall y y', y=y' -> (R x y <-> R' x' y')) ->
    forall z, z ∈ repl a R -> z ∈ repl a' R'.
intros.
apply in_set_ax in H1.
apply in_set_ax.
elim H1 using tr_ind_tr; clear H1.
intros ((i,(?,?)),?); simpl in *.
elim (H (Kerf a i)) using tr_ind_tr.
2:apply tr_i; exists i; trivial.
intros (j,?).
assert (tr {z|tr(R'(Kerf a' j)z)}/\isProp{z|tr(R'(Kerf a' j)z)}).
 split.
  elim t using tr_ind_tr; clear t.
  intros (w,?).
  apply tr_i; exists w.
  elim t using tr_ind_tr; clear t; intros.
  apply tr_i.
  apply (H0 _ _ e w w eq_refl); trivial.

  red; intros.
  apply sig_intro; auto with *.
  destruct x as (x,?); destruct y as (y,?); simpl.
  assert (tr (R (Kerf a i) x)).
   revert t0; apply tr_map.
   apply H0; auto.
  assert (tr (R (Kerf a i) y)).
   revert t1; apply tr_map.
   apply H0; auto.
  assert (aux := i0 (exist (fun z=>tr(R(Kerf a i)z)) x H2) (exist (fun z=>tr(R(Kerf a i)z)) y H3)).
  apply f_equal with (f:=fun x=>proj1_sig x) in aux; simpl in aux.
  trivial.
apply tr_i; exists (exist (fun _=>_ /\ _) j H2); simpl.
rewrite H1.
apply uch_ext.
intros; apply H0; auto.
Qed.


 Lemma repl_ax a (R:set->set->Prop) :
  (forall x x' y y', x ∈ a -> x = x' -> y = y' -> R x y -> R x' y') ->
  (forall x y y', x ∈ a -> R x y -> R x y' -> y = y') ->
  forall x, x ∈ repl a R <-> #exists2 y, y ∈ a & R y x.
intros _ Huniq x.
unfold repl; rewrite in_set_ax.  
split; intros.
 elim H using tr_ind_tr; clear H.
 intros ((i,(Hex,Hp)),?); simpl in *.
 elim Hex using tr_ind_tr; clear Hex.
 intros (z,?).
 elim t using tr_ind_tr; clear t; intros.
 apply tr_i; exists (Kerf a i).
  apply tr_i; exists i; trivial. 

  replace x with z; trivial.
  rewrite H.
  symmetry; apply uch_eq; trivial.

 elim H using tr_ind_tr; clear H.
 intros (y,?,?).
 elim H using tr_ind_tr; clear H.
 intros (i,?).
 subst y.
 assert (tr{z|tr(R (Kerf a i) z)} /\ isProp {z | tr (R (Kerf a i) z)}).
  split.
   apply tr_i; exists x; apply tr_i; trivial.

   apply isProp_sig; auto with *.
   intros.
   elim H using tr_ind.
    red; intros; apply isSet_set.
   clear H; intros.
   elim H1 using tr_ind.
    red; intros; apply isSet_set.
   clear H1; intros.
   apply Huniq with (Kerf a i); trivial.
   apply tr_i; exists i; trivial.
 apply tr_i; exists (exist (fun _ => _/\_) i H); simpl.
 symmetry; apply uch_eq; trivial.
 destruct H; trivial.
Qed.

End SetsQuoEnd.

Section TestQuo2.
Import SetsQuoEnd.
Definition test_quo2 :=
  (eq_set_ax,wf_ax,pair_ax,power_ax,infinity_ax1,infinity_ax2,union_ax,repl_ax).
Print Assumptions test_quo2. (* set univalence + resized prop-truncation *)
End TestQuo2.

