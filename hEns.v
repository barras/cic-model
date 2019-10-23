Require Import ZFskol.
Require Import Sublogic.
Require Import paths hott.
Import TrSubThms.

(* The level of indices *)
Definition Ti := Type.


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
eapply univ with (fst (X x)) (snd (X x)).
admit.
admit.
(* apply isSet_prop; trivial.

 split; intros.
  apply H.
  apply H0.*)
Qed.
*)

(* Equality of families *)

Definition eq_fam {X X':Ti}{Y} (f:X->Y) (f':X'->Y) :=
  (forall i, #exists j, f i = f' j) /\
  (forall j, #exists i, f i = f' j).

Lemma eq_fam_sym {X X' Y f f'} : @eq_fam X X' Y f f' -> eq_fam f' f.
destruct 1; split; intros.
 generalize (H0 i); apply TrMono.
 intros (j,?); exists j; auto.

 generalize (H j); apply TrMono.
 intros (i,?); exists i; auto.
Qed.

Lemma eq_fam_comp {X X' Y Y'} (f:Y->Y'){g:X->Y}{g':X'->Y}:
  eq_fam g g' -> eq_fam (fun i => f (g i)) (fun i => f (g' i)).
destruct 1; split; intros.
 Tdestruct (H i) as (j,?). 
 Texists j; f_equal; trivial.

 Tdestruct (H0 j) as (i,?). 
 Texists i; f_equal; trivial.
Qed.

Hint Resolve tr_prop isProp_forall isProp_conj.

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

Variable Y:Type.
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

Definition ker_i {X}(f:X->Y) (x:X) : ker X f :=
  quo_i (isRel_ker _) x.

(** Unicity of ker up to isomorphism *)

Definition ker_f {X X':Ti} {f:X->Y} {f':X'->Y} :
  eq_fam f f' -> ker X f -> ker X' f'.
intros eqf k.
assert (Hr := isRel_ker f).
assert (Hr' := isRel_ker f').
assert (Hs := isSet_quo X' (fun x0 y0 : X' => f' x0 = f' y0) Hr').
pose (f1:= fun i (x : {x : X' | f i = f' x}) => ker_i f' (proj1_sig x)).
assert (inv1 : forall i x y, f1 i x = f1 i y).
 intros.
 apply quo_i_eq.
 rewrite <- (proj2_sig x).
 rewrite <- (proj2_sig y).
 reflexivity.
pose (f2 := fun x:X =>
               tr_ind_set_nodep _ _ Hs _ (inv1 x) (proj1 tr_ex_sig (proj1 eqf x))).
assert (inv2: forall x y:X, f x = f y -> f2 x = f2 y).
 unfold f2; intros.
 apply tr_ind_set_nodep_ind.
  red; intros; apply isSet_quo; auto with *. 
 intros (x',?).
 apply tr_ind_set_nodep_ind.
  red; intros; apply isSet_quo; auto with *. 
 intros (y',?).
 apply quo_i_eq; simpl.
 rewrite <- e, <- e0; trivial.
eapply quo_ind_set_nodep with (1:=Hr) (2:=Hs) (h:=f2) (4:=k).
intros.
unfold f2; intros.
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

Definition ker_map (X:Ti) (f:X->Y) (i:ker X f) :
  {x:Y|tr{i':X & ker_i _ i' = i /\ f i' = x }}.
elim i using (quo_ind _).
 clear i; intros i (j,?)(j',?).
 apply sig_intro; auto with *.
 simpl.
 elim t using tr_ind_nodep; intros.
  red; intros; apply Ys.
 destruct X0 as (i',(?,?)).
 elim t0 using tr_ind_nodep; intros.
  red; intros; apply Ys.
 destruct X0 as (i'',(?,?)).
 rewrite <-H1 in H.
 apply quo_i_eq in H.
 rewrite H in H0; rewrite H0 in H2; trivial.

 intros.
 exists (f x).
 apply tr_i; exists x; auto.
Defined.
(*Definition ker_map (X:Ti) (f:X->Y) (i:ker X f) :
  {x:Y|#exists2 i':X, ker_i _ i' = i &f i' = x }.
elim i using (quo_ind _).
 clear i; intros i (j,?)(j',?).
 apply sig_intro; auto with *.
 simpl.
 elim t using tr_ind; intros.
  red; intros; apply Ys.
 destruct x as (i',?).
 elim t0 using tr_ind; intros.
  red; intros; apply Ys.
 destruct x as (i'',?).
 rewrite <-H1 in H.
 apply quo_i_eq in H.
 rewrite H in H0; rewrite H0 in H2; trivial.

 intros.
 exists (f x).
 Texists x; auto.
Defined.*)

(*
Lemma ker_comp : set_comp_nodep Type ker.
red; intros.
assert (r' := eq_fam_sym r).
apply univ with (ker_f r) (ker_f r').
 apply isSet_quo; auto with *.
 apply isSet_quo; auto with *.
split; intros.
 apply ker_f_id. 
 apply ker_f_id. 
Qed.
 *)

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

Definition decomp_tr (a:fam) : tr(decomp_fam a).
pattern a.
elim a using (Quo.quo_ind _); auto.
intros (X,f); apply tr_i.
 exists (existT (fun X=>X->Y) (ker X f)
                (fun i => proj1_sig (ker_map X f i))); simpl.
 split;[|split]; simpl.
  apply isSet_quo; auto with *.

  intros.
  destruct (ker_map X f x); simpl in *.
  destruct (ker_map X f x'); simpl in *.
  elim t using tr_ind_nodep; intros.
   red; intros; apply isSet_quo; auto with *.
  destruct X0 as (i,(?,?)).
  elim t0 using tr_ind_nodep; intros.
   red; intros; apply isSet_quo; auto with *.
  destruct X0 as (i',(?,?)).
  rewrite <-H1,<-H3 in H.
  rewrite <-H0,<-H2; apply quo_i_eq; trivial.

  apply Quo.quo_i_eq.
  split; simpl; intros.
   apply tr_i; exists (ker_i f i).
   destruct (ker_map X f (ker_i f i)) as (x,?); simpl.
   elim t using tr_ind_nodep; intros.
    red; intros; apply Ys.
   destruct X0 as (i',(?,?)).
   apply quo_i_eq in H.
   rewrite <- H; trivial.
   
   elim j using (quo_ind _); auto with *.
   intros i.
   fold (ker_i f i).
   apply tr_i; exists i.
   destruct (ker_map X f (ker_i f i)) as (x,?); simpl.
   elim t using tr_ind_nodep; intros.
    red; intros; apply Ys.
   destruct X0 as (i',(?,?)).
   apply quo_i_eq in H.
   rewrite <- H; trivial.
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
  existT (fun X => X->Y) (ker X f) (fun i => proj1_sig (ker_map X f i)).
unfold decomp.
unfold decomp_tr.
rewrite Quo.quo_ind_eq.
rewrite tr_ind_nodep_eq; simpl.
reflexivity.
Qed.

End Ker.


(** * The type of sets *)

Module SetsHit <: IZF_R_sig TrSubThms.
  
  
(** We assume we can build an type "set" equivalent
    to the quotiented indexed families of sets *)
Parameter set : Type.
Parameter set_def : eqv set (fam set).
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
elim H using tr_ind; auto.
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

 destruct H as (H,H'); elim H using tr_ind; auto.
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
apply isProp_conj; auto.
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
 elim H3 using tr_ind; auto; intros.
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
  apply tr_i; split; intros; auto.
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

Import SetsHit.
Definition test :=
  (eq_set_ax,wf_ax,pair_ax,power_ax,infinity_ax1,infinity_ax2,union_ax,repl_ax).
Print Assumptions test.



(******************************************************************************)
(** * The type of intensional sets *)

Module SetsQuo <: IZF_R_sig TrSubThms.

  Inductive iset :=
    isup (_:{X:Ti & X->iset}).

  Definition unsup (x:iset) := let (x) := x in x.

  Fixpoint eq_iset (x y:iset) :=
    let (x):=x in
    let (y):=y in
    (forall i, #exists j, eq_iset (projT2 x i) (projT2 y j)) /\
    (forall j, #exists i, eq_iset (projT2 x i) (projT2 y j)).

  Instance eq_iset_refl : Reflexive eq_iset.
red; fix rfl 1.
intros (x); simpl.
split; intros.
 Texists i; apply rfl.
 Texists j; apply rfl.
Qed.

  Instance eq_iset_sym : Symmetric eq_iset.
red; fix sym 1.
intros (x) (y); simpl.
destruct 1; split; intros.
 Tdestruct (H0 i) as (j,?).
 Texists j. 
 apply sym; assumption.

 Tdestruct (H j) as (i,?).
 Texists i. 
 apply sym; assumption.
Qed.

Instance eq_iset_trans : Transitive eq_iset.
red; fix trans 1.
intros (x) (y) (z) (xy,yx) (yz,zy); simpl.
split; intros.
 Tdestruct (xy i) as (j,?).
 Tdestruct (yz j) as (k,?).
 Texists k.
 apply trans with (projT2 y j); assumption.

 Tdestruct (zy j) as (k,?).
 Tdestruct (yx k) as (i,?).
 Texists i.
 apply trans with (projT2 y k); assumption.
Qed.

  Lemma isProp_eq_iset x y : isProp (eq_iset x y).
revert x y; intros (x) (y); simpl.
apply isProp_conj.
 apply isProp_forall; intros i.
 apply tr_prop.

 apply isProp_forall; intros i.
 apply tr_prop.
Qed.

  Instance isRel_eq_iset : isRel eq_iset.
split.
 apply isProp_eq_iset.  

 split; auto with *.
Qed.

(* Trying to prove that iset is a set:
  Lemma isup_inj x y : isup x = isup y -> x=y.
  apply f_equal with (f:=unsup).
  Defined.

Definition sigT_eq A B (x y:@sigT A B) :=
  { e1 : projT1 x = projT1 y & eqD B e1 (projT2 x) (projT2 y) }.    
Lemma sigT_eq_to A B (x y:@sigT A B) (e:x=y) : sigT_eq _ _ x y.
destruct e.     
exists eq_refl.
reflexivity.
Defined.
Lemma sigT_eq_from A B (x y:@sigT A B) (e:sigT_eq _ _ x y) : x=y.
destruct x as (x1,x2); destruct y as (y1,y2).
destruct e as (e1,e2); simpl in *.
revert e2; destruct e1.
destruct 1.
reflexivity.
Defined.

  Lemma s0s : isSet iset.
red.
fix s0s 1.  
intros (x) (y) p q.
 replace p with (f_equal isup (isup_inj _ _ p)).
 replace q with (f_equal isup (isup_inj _ _ q)).
  f_equal.
  pose (e1:= sigT_eq_to _ _ _ _ (isup_inj x y p)).
  pose (e2:= sigT_eq_to _ _ _ _ (isup_inj x y q)).
Lemma sigT_eq_from_to A B (x y:@sigT A B) (p:x=y) :
  p = sigT_eq_from _ _ _ _ (sigT_eq_to _ _ _ _ p).    
destruct p.
destruct x.
reflexivity.  
Qed.
  rewrite sigT_eq_from_to with (p:=isup_inj _ _ p).
  rewrite sigT_eq_from_to with (p:=isup_inj _ _ q).
  f_equal.
assert (tmp : projT1 (sigT_eq_to Ti (fun X : Ti => X -> iset) x y (isup_inj x y p)) =
projT1 (sigT_eq_to Ti (fun X : Ti => X -> iset) x y (isup_inj x y q))).
 unfold isup_inj.
 unfold sigT_eq_to.
 
eapply exT_eq.
Show Existentials.

  with (e:=f_equal (fun x=>projT1 x) eq_refl).
  admit.

  unfold isup_inj.
Lemma f_equal_comp A B C (f:B->C)(g:A->B) x y (e:x=y) :
  f_equal f (f_equal g e) = f_equal (fun x => f (g x)) e.    
destruct e; reflexivity.
Defined.
  transitivity (f_equal (fun x => isup (unsup x)) q).
  apply f_equal_comp with (f:=isup) (g:=unsup) (e:=q).
Lemma f_equal_id A f (x y:A) (e:x=y) :
  (forall x, f x = x) ->
  f_equal f e = e.

  destruct q.
  rewrite f_equal_comp with (f:=isup) (g:=unsup) (e:=q).
*)
  
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
  unfold_set (quo_i _ (isup (existT(fun X:Ti=>X->iset) X f))) =
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

(*
Lemma ker_ax :
  tr{i:X | z = mks (f i)} <-> tr{k:ker _ 
*)
Definition in_set (x y:set) : Prop :=
  tr{j:Ker y & x = Kerf y j}.
Notation "x ∈ y" := (in_set x y).

Lemma in_iset_ax z (X:Ti) f :
      z ∈ mks (isup (existT (fun X=>X->iset) X f)) <->
      tr{i:X| z = mks (f i)}.
unfold in_set.
unfold Ker, Kerf.
rewrite unfold_set_eq.
rewrite decomp_eq.
simpl.
split; intros.
 elim H using (tr_ind_tr _); clear H.
 intros (k,?).
 destruct ker_map with (Ys:=isSet_set) (i:=k); simpl in e.
 elim t using (tr_ind_tr _); clear t.
 intros (i,(?,?)).
 rewrite <- H0 in e.
 apply tr_i; exists i; trivial.

 elim H using (tr_ind_tr _); clear H.
 intros (i,?). 
 pose (k := ker_i _ isSet_set (fun i => mks (f i)) i).
 apply tr_i; exists k.
 destruct ker_map with (Ys:=isSet_set) (i:=k); simpl.
 elim t using tr_ind.
  red; intros; apply isSet_set.
 clear t.
 intros (j,(?,?)).
 apply Quo1.quo_i_eq in H.
 rewrite e,<-H; auto.
Qed. 


Lemma wf_ax_iset (P:set->Type) :
    (forall x, isProp (P x)) ->
    (forall x, (forall y, in_set y x -> P y) -> P x) ->
    forall x:iset, P (quo_i _ x).
intros Pp Hrec.
fix acc 1.
intros ((X,f)); simpl.
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
 apply wf_ax_iset; trivial.
Qed.

(** from set to iset *)

Inductive set_cano (x:set) : iset -> Prop :=
  | ISC_sup f :
      (forall i, set_cano (Kerf x i) (f i)) ->
      set_cano x (isup (existT (fun X=>X->iset) (Ker x) f)).


Lemma set2iset_cano (x:set) : isContr {y|set_cano x y}.
elim x using (quo_ind _).
 intros; apply (isProp_isContr _).
clear x; intros x.
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
pose (h := fun (f_Hf:{f:Ker x->iset|forall i, set_cano (Kerf x i) (f i)}) => exist (set_cano x) (isup (existT (fun X => X->iset)(Ker x) (proj1_sig f_Hf))) (ISC_sup x (proj1_sig f_Hf) (proj2_sig f_Hf))).
change (h (exist (fun f => forall i, set_cano (Kerf x i)(f i)) f s) =
        h (exist (fun f => forall i, set_cano (Kerf x i)(f i)) (fun i => proj1_sig(projT1(Hreck i))) (fun i => proj2_sig(projT1(Hreck i))))).
apply f_equal with (f:=h).
apply sig_eq with (e:=fun_ext_singl (f:=f) (g:=fun i => proj1_sig (projT1 (Hreck i)))
                               (fun i => f_equal (fun x => proj1_sig x) (projT2 (Hreck i) (exist (set_cano (Kerf x i)) (f i) (s i))))); simpl.
unfold eqD.
rewrite transport_rng.
apply fun_ext; intros i.
assert (aux:=sig_proj2(projT2 (Hreck i) (exist (set_cano(Kerf x i)) (f i) (s i)))).
red in aux.
rewrite <- aux.
rewrite transport_app.
apply f_equal with (f:=fun e => transport (set_cano (Kerf x i)) e (s i)).
(*assert (iss : isSet iset).
admit.
apply iss.
*)
rewrite fun_ext_eqv2.
reflexivity.
Qed.

Lemma set_cano_ok x y :
  set_cano x y -> x = mks y.
induction 1; intros.
revert f H H0.
elim x using (quo_ind _).
 intros; apply isProp_forall.
 intros; apply isProp_forall.
 intros; apply isProp_forall.
 intros.
 red; intros; apply isSet_quo; auto with *.
clear x; intros ((X,f),e).
intros.

(*
Lemma eq_iset_ker :
  eq_iset (
Lemma eq_iset_intro X Y f g :
  eq_fam f g ->
  eq_iset (isup (existT (fun X=>X->iset) X f)) (isup (existT (fun X=>X->iset) Y g)).
unfold eq_fam.
simpl.  *)
apply quo_i_eq.
simpl.
clear H.
revert e H0. 
unfold Kerf, Ker.
replace (proj1_sig
           (decomp _ isSet_set
              (unfold_set (quo_i isRel_eq_iset (isup (existT(fun X:Ti=>X->iset) X f)))))) with
  (existT (fun X=>X->set) (ker _ X (fun i=>mks (f i)))
                          (fun i => proj1_sig (ker_map _ isSet_set X _ i))); simpl.
2:rewrite unfold_set_eq.
2:rewrite decomp_eq; reflexivity.
split; intros.
 pose (k := ker_i _ isSet_set (fun i => mks (f i)) i).
 apply tr_i; exists k.
 specialize H0 with k.
 destruct (ker_map _ isSet_set _ (fun i => mks (f i)) k); simpl in H0.
 elim t using tr_ind.
  intros; apply isProp_eq_iset.
 intros (i',(?,?)).
 rewrite H0 in H1.
 apply quo_i_eq in H1.
 apply Quo1.quo_i_eq in H.
 apply quo_i_eq in H.
 transitivity (f i'); auto.
 symmetry; trivial.

 specialize H0 with j.
 destruct (ker_map _ isSet_set _ (fun i => mks (f i)) j) as (y,?); simpl in *.
 elim t using (tr_ind_tr _).
 clear t.
 intros (i,(?,?)).
 Texists i.
 rewrite H0 in H1.
 apply quo_i_eq in H1; trivial.
Qed.

Definition set2iset (x:set) : iset :=
  proj1_sig (proj1_sig (set2iset_cano x)).

Definition set2iset_ok x : x = mks (set2iset x).
apply set_cano_ok.
apply (proj2_sig (proj1_sig (set2iset_cano x))).
Qed.
Print Assumptions set2iset_ok. (* set univalence (+ fun_ext) + truncation *)

Lemma eq_set_intro x y :
  eq_fam (Kerf x) (Kerf y) ->
  x = y.
rewrite (set2iset_ok x).
rewrite (set2iset_ok y).
destruct (set2iset x) as ((X,f)).
destruct (set2iset y) as ((Y,g)).
unfold Kerf, Ker.
rewrite !unfold_set_eq.
rewrite !decomp_eq.  
simpl.
intros (xy,yx).
apply quo_i_eq.
simpl.
split; intros.
 specialize xy with (ker_i _ isSet_set (fun i => mks(f i)) i). 
 elim xy using (tr_ind_tr _).
 clear xy; intros (j,?).
 destruct (ker_map _ isSet_set _ (fun i => mks(g i)) j) as (z,?).
 simpl in *.
 elim t using (tr_ind_tr _).
 clear t.
 intros (j',(?,?)).
 destruct (ker_map _ isSet_set _ (fun i => mks(f i)) (ker_i _ isSet_set _ i)) as (z',?).
 simpl in *.
 elim t using tr_ind_tr.
 clear t.
 intros (i',(?,?)).
 Texists j'.
 rewrite <-H3,<-H1 in H.
 apply Quo1.quo_i_eq in H2.
 rewrite H2 in H.
 apply quo_i_eq in H; trivial.

 specialize yx with (ker_i _ isSet_set (fun i => mks(g i)) j). 
 elim yx using tr_ind_tr.
 clear yx; intros (i,?).
 destruct (ker_map _ isSet_set _ (fun i => mks(f i)) i) as (z,?).
 simpl in *.
 elim t using tr_ind_tr.
 clear t.
 intros (i',(?,?)).
 destruct (ker_map _ isSet_set _ (fun i => mks(g i)) (ker_i _ isSet_set _ j)) as (z',?).
 simpl in *.
 elim t using tr_ind_tr.
 clear t.
 intros (j',(?,?)).
 Texists i'.
 rewrite <-H3,<-H1 in H.
 apply Quo1.quo_i_eq in H2.
 rewrite H2 in H.
 apply quo_i_eq in H; trivial.
Qed.


Definition sup (X:Ti) (f:X->set) : set :=
  mks (isup (existT (fun X=>X->iset) X (fun i => set2iset (f i)))).


(** Equality and Membership *)

Definition eq_set (x y:set) := x=y.

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
  intros; apply isProp_conj; auto.
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

Definition uch_single (P:set->Prop) : set :=
  sup (tr{z|#P z} /\ isProp{z| #P z})
      (fun c => let (w,p) := c in proj1_sig (tr_ind_nodep p (fun w=>w) w)).
Lemma uch_single_ax P z :
  isProp {x:set|#P x} ->
  (in_set z (uch_single P) <-> #P z).
intros Hp.
unfold uch_single; rewrite in_set_ax.
split; intros.
 elim H using tr_ind_tr; clear H.
 intros ((w,Hp'),?); simpl.
 destruct (tr_ind_nodep Hp' (fun w => w) w); simpl in *.
 subst z; trivial.

 apply tr_i; exists (conj (tr_i (exist (fun z=>tr(P z)) z H)) Hp).
 destruct (tr_ind_nodep Hp (fun w => w) (tr_i (exist (fun z=>tr(P z)) z H))); simpl.
 assert (aux := Hp (exist (fun z=>tr(P z)) z H) (exist (fun z=>tr(P z)) x t)).
 apply f_equal with (f:=fun x=>proj1_sig x) in aux; simpl in aux.
 trivial. 
Qed.

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
 apply sig_intro; auto.
 destruct x as (x,?); destruct y as (y,?); simpl.
 assert (aux := H1 (exist (fun z=>tr(P z)) x (proj2 (tr_iff _) t)) (exist (fun z=>tr(P z)) y (proj2 (tr_iff _) t0))).
 apply f_equal with (f:=fun x=>proj1_sig x) in aux; simpl in aux.
 trivial.
rewrite uch_single_ax in H0; trivial.
rewrite uch_single_ax; trivial.
elim H0 using tr_ind_tr; clear H0; intros.
apply tr_i; apply H; trivial.
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
  apply sig_intro; auto.
  destruct x as (x,?); destruct y as (y,?); simpl.
  assert (tr (R (Kerf a i) x)).
   elim t0 using tr_ind_tr; clear t0; intros.
   apply tr_i; apply (H0 _ _ e x x eq_refl); trivial.
  assert (tr (R (Kerf a i) y)).
   elim t1 using tr_ind_tr; clear t1; intros.
   apply tr_i; apply (H0 _ _ e y y eq_refl); trivial.
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

   apply isProp_sig; auto.
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

End SetsQuo.

Import SetsQuo.
Definition test_quo :=
  (eq_set_ax,wf_ax,pair_ax,power_ax,infinity_ax1,infinity_ax2,union_ax,repl_ax).
Print Assumptions test_quo. (* set univalence + resized prop-truncation *)


(******************************************************************************)
(** * The type of sets *)
Module S <: Zermelo_sig TrSubThms.

(* The level of indexes *)
Definition Ti := Type.

Inductive set_ : Type :=
  sup (X:Ti) (f:X->set_).
Definition set := set_.

Definition idx (x:set) := let (X,_) := x in X.
Definition elts (x:set) : idx x -> set :=
  match x return idx x -> set with
  | sup X f => f
  end.

Fixpoint eq_set (x y:set) {struct x} :=
  (forall i, #exists j, eq_set (elts x i) (elts y j)) /\
  (forall j, #exists i, eq_set (elts x i) (elts y j)).

Lemma isProp_eq_set x y : isProp (eq_set x y).
destruct x; simpl; intros.
apply isProp_conj.
 apply isProp_forall; intros i; apply tr_prop.
 apply isProp_forall; intros i; apply tr_prop.
Qed.

Lemma eq_set_refl : forall x, eq_set x x.
induction x; simpl.
split; intros; apply tr_i.
 exists i; trivial.
 exists j; trivial.
Qed.

Lemma eq_set_sym : forall x y, eq_set x y -> eq_set y x.
induction x; destruct y; simpl; intros.
destruct H0.
split; intros.
 elim (H1 i) using tr_ind_tr; intros (?,?).
 apply tr_i.
 exists x; auto.

 elim (H0 j) using tr_ind_tr; intros (?,?).
 apply tr_i; exists x; auto.
Qed.

Lemma eq_set_trans : forall x y z,
  eq_set x y -> eq_set y z -> eq_set x z.
induction x; destruct y; destruct z; simpl; intros.
destruct H0.
destruct H1.
split; intros.
 elim (H0 i) using tr_ind_tr; intros (?,?).
 elim (H1 x) using tr_ind_tr; intros (?,?).
 apply tr_i; exists x0; eauto.

 elim (H3 j) using tr_ind_tr; intros (?,?).
 elim (H2 x) using tr_ind_tr; intros (?,?).
 apply tr_i; exists x0; eauto.
Qed.


Lemma eq_set_def : forall x y,
  (forall i, #exists j, eq_set (elts x i) (elts y j)) ->
  (forall j, #exists i, eq_set (elts x i) (elts y j)) ->
  eq_set x y.
destruct x; simpl; auto.
Qed.

Definition in_set x y :=
  #exists j, eq_set x (elts y j).


Lemma in_set_ind P x y :
  isProp P ->
  (forall j, eq_set x (elts y j) -> P) ->
  in_set x y -> P.
intros.
apply (proj1 tr_ex_sig) in H0.
elim H0 using tr_ind; auto.  
destruct 1; intros; eauto.
Qed.

Lemma isProp_in_set x y : isProp (in_set x y).
apply tr_prop.
Qed.

  Definition incl_set x y := forall z, in_set z x -> in_set z y.

Lemma isProp_incl_set x y : isProp (incl_set x y).
apply isProp_forall; intros.
apply isProp_forall; intros.
auto.
apply tr_prop.
Qed.
Hint Resolve isProp_eq_set isProp_incl_set isProp_in_set tr_prop.


Lemma eq_elim0 x y i :
  eq_set x y ->
  in_set (elts x i) y.
destruct x; simpl; intros.
destruct H.
red; auto.
Qed.

Lemma eq_set_ax : forall x y,
  eq_set x y <-> (forall z, in_set z x <-> in_set z y).
unfold in_set; split; intros.
 split; intros h; Tdestruct h.
  elim (eq_elim0 x y x0) using in_set_ind; intros; auto.
  Texists j; apply eq_set_trans with (elts x x0); trivial.

  apply eq_set_sym in H.
  elim (eq_elim0 y x x0) using in_set_ind; intros; auto.
  Texists j; apply eq_set_trans with (elts y x0); trivial.

  apply eq_set_def; intros.
   apply H.
   Texists i; apply eq_set_refl.

   destruct (H (elts y j)).
   elim H1 using in_set_ind; intros; auto.
    Texists j0; apply eq_set_sym; trivial.

    Texists j; apply eq_set_refl.
Qed.

Definition elts' (x:set) (i:idx x) : {y|in_set y x}.
exists (elts x i).
abstract (apply tr_i; exists i; apply eq_set_refl).
Defined.

Lemma in_reg : forall x x' y,
  eq_set x x' -> in_set x y -> in_set x' y.
intros.
elim H0 using in_set_ind; intros; auto.
apply tr_i; exists j.
apply eq_set_trans with x; trivial.
apply eq_set_sym; trivial.
Qed.

Lemma eq_intro : forall x y,
  (forall z, in_set z x -> in_set z y) ->
  (forall z, in_set z y -> in_set z x) ->
  eq_set x y.
intros.
rewrite eq_set_ax.
split; intros; eauto.
Qed.

Lemma eq_elim : forall x y y',
  in_set x y ->
  eq_set y y' ->
  in_set x y'.
intros.
rewrite eq_set_ax in H0.
destruct (H0 x); auto.
Qed.

  Lemma wf_ax :
  forall (P:set->Prop),
  (forall x, (forall y, in_set y x -> #P y) -> #P x) -> forall x, #P x.
intros P H x.
cut (forall x', eq_set x x' -> #P x');[auto using eq_set_refl|].
induction x; intros.
apply H; intros.
assert (in_set y (sup X f)).
 apply eq_elim with x'; trivial.
 apply eq_set_sym; trivial.
clear H1 H2.
elim H3 using in_set_ind; intros; auto.
apply eq_set_sym in H1; eauto.
Qed.

Definition empty :=
  sup False (fun x => match x with end).

Lemma empty_ax : forall x, in_set x empty -> #False.
intros.
elim H using in_set_ind; intros; auto.
contradiction.
Qed.

Definition singl x := sup unit (fun _ => x).

Definition pair_spec (a b:set->Prop) (x:set) : Prop :=
  forall z, in_set z x <-> #(a z \/ b z).

Definition pair x y :=
  sup bool (fun b => if b then x else y).

Lemma pair_spec_intro a b :
  pair_spec (fun a' => eq_set a' a) (fun b' => eq_set b' b) (pair a b).
intros z.
unfold pair; simpl.
split; intros.
 elim H using in_set_ind; intros; auto.
 apply tr_i.
 destruct j; auto.

 elim H using tr_ind; intros; auto.
 destruct x.
  apply tr_i; exists true; trivial.
  apply tr_i; exists false; trivial.
Qed.

Lemma pair_ax : forall a b z,
  in_set z (pair a b) <-> #(eq_set z a \/ eq_set z b).
Proof pair_spec_intro.


Lemma pair_morph :
  forall a a', eq_set a a' -> forall b b', eq_set b b' ->
  eq_set (pair a b) (pair a' b').
unfold pair.
simpl; intros.
split; intros.
 apply tr_i; exists i; destruct i; trivial.
 apply tr_i; exists j; destruct j; trivial.
Qed.

Definition subset_spec (x:set) (P:set->Prop) (y:set) :=
  forall z,
  in_set z y <->
  in_set z x /\ # (exists2 z', eq_set z z' & P z').

Definition subset (x:set) (P:set->Prop) :=
  sup {a|exists2 x', eq_set (elts x a) x' & P x'}
    (fun y => elts x (proj1_sig y)).

Lemma subset_ax : forall x P, subset_spec x P (subset x P).
red.
unfold subset; simpl.
split; intros.
 elim H using in_set_ind; simpl; intros; auto.
 clear H; destruct j as (j,?); simpl in H0.
 split.
  apply tr_i; exists j; trivial.

  destruct e.
  apply tr_i; exists x0; trivial.
  apply eq_set_trans with (elts x j); trivial.

 destruct H.
 elim H using in_set_ind; auto.
 clear H; intros.
 elim H0 using tr_ind; intros; auto.
 destruct x0.
 assert (exists2 x', eq_set (elts x j) x' & P x').
  exists x0; trivial.
  apply eq_set_trans with z; trivial.
  apply eq_set_sym; trivial.
 apply tr_i; exists
  (@exist _ (fun a=>exists2 x',eq_set (elts x a) x' & P x')
    j H3); simpl; trivial.
Qed.

Definition power (x:set) :=
  sup (idx x->Prop)
   (fun P => subset x (fun y => exists2 i, eq_set y (elts x i) & P i)).

Lemma power_ax : forall x z,
  in_set z (power x) <->
  (forall y, in_set y z -> in_set y x).
unfold power; simpl; intros.
split; intros.
 elim H using in_set_ind; intros; auto.
 simpl in *.
 specialize eq_elim with (1:=H0)(2:=H1); intro.
 apply (proj1 (proj1 (subset_ax _ _ _) H2)).

 apply tr_i; exists (fun i => in_set (elts x i) z); simpl.
 apply eq_intro; intros.
  apply (fun x P z => proj2 (subset_ax x P z)).
  split; auto.
  elim H with z0 using in_set_ind; trivial; intros.
  Texists z0.
   apply eq_set_refl.

   exists j; trivial.
   apply in_reg with z0; trivial.

  elim (proj2 (proj1 (subset_ax _ _ _) H0)) using tr_ind; intros; auto.
  destruct x0 as (z', ?, (i,?,?)).
  apply in_reg with (elts x i); trivial.
  apply eq_set_sym; apply eq_set_trans with z'; trivial.
Qed.

Lemma power_morph : forall x y,
  eq_set x y -> eq_set (power x) (power y).
intros.
apply eq_intro; intros.
 rewrite power_ax in H0|-*; intros.
 apply eq_elim with x; auto.

 apply eq_set_sym in H.
 rewrite power_ax in H0|-*; intros.
 apply eq_elim with y; auto.
Qed.

  
 Definition union (x:set) :=
  sup {i:idx x & idx (elts x i)}
    (fun p => elts (elts x (projS1 p)) (projS2 p)).

Lemma union_ax : forall a z,
  in_set z (union a) <-> #exists2 b, in_set z b & in_set b a.
unfold in_set at 1, union; simpl; intros.
split; intros.
 Tdestruct H.
 Texists (elts a (projT1 x)).
  Texists (projT2 x); trivial.
  Texists (projT1 x); apply eq_set_refl.

 Tdestruct H.
 Tdestruct H0.
 assert (in_set z (elts a x0)).
  apply eq_elim with x; trivial.
 Tdestruct H1.
 Texists (existT (fun i=>idx(elts a i)) x0 x1); simpl.
 trivial.
Qed.

Lemma union_morph :
  forall a a', eq_set a a' -> eq_set (union a) (union a').
intros.
apply eq_set_ax; intros z.
rewrite union_ax.
rewrite union_ax.
split; intros h; Tdestruct h as (b,?,?); Texists b; trivial.
 apply eq_elim with a; trivial.
 apply eq_elim with a'; trivial.
 apply eq_set_sym; trivial.
Qed.


Fixpoint num (n:nat) : set :=
  match n with
  | 0 => empty
  | S k => union (pair (num k) (pair (num k) (num k)))
  end.

Definition infinite := sup _ num.

Lemma infinity_ax1 : in_set empty infinite.
 Texists 0.
 unfold elts, infinite, num.
 apply eq_set_refl.
Qed.

Lemma infinity_ax2 : forall x, in_set x infinite ->
  in_set (union (pair x (pair x x))) infinite.
intros.
elim H using in_set_ind; intros; auto.
Texists (S j).
simpl elts.
apply union_morph.
apply pair_morph; trivial.
apply pair_morph; trivial.
Qed.

Definition replf (x:set) (F:set->set) :=
  sup _ (fun i => F (elts x i)).

Lemma replf_ax : forall x F z,
  (forall z z', in_set z x ->
   eq_set z z' -> eq_set (F z) (F z')) ->
  (in_set z (replf x F) <->
   #exists2 y, in_set y x & eq_set z (F y)).
unfold replf; simpl; intros.
split; intros.
 elim H0 using in_set_ind; intros; auto.
 simpl in *.
 Texists (elts x j); trivial.
 Texists j; apply eq_set_refl.

 elim H0 using tr_ind; intros; auto.
 destruct x0 as (x',?,?).
 elim H1 using in_set_ind; intros; auto.
 Texists j; simpl.
 apply eq_set_trans with (F x'); trivial.
 apply eq_set_sym.
 apply H.
  Texists j; apply eq_set_refl.
  apply eq_set_sym; trivial.
Qed.

End S.


(** * The type of sets as a HIT *)
(*
Module hS <: IZF_R_sig TrSubThms.

(* The level of indexes *)
Definition Ti := Type.

Inductive set_ : Type :=
  sup (X:Ti) (f:X->set_).
Definition set := set_.

Parameter eq_fam : forall {A} (X X':Ti), (X->A) -> (X'->A) -> Type.
Parameter map_eq_fam : forall {A B X X' f f'} (h:A->B),
  eq_fam X X' f f' -> eq_fam X X' (fun x => h (f x)) (fun x => h (f' x)).

Lemma set_ext {X X':Ti} {f f'} :
  eq_fam X X' f f' ->
  sup X f = sup X' f'.
Admitted.

Lemma isSet_set : isSet set.
Admitted.

Lemma set_elim :
  forall (P:set->Type)
  (Pp:forall x, isSet (P x))
  (h:forall (X:Ti) f, (forall (i:X), P (f i)) -> P (sup X f)),
  (forall (X X':Ti) f f' (Hf:forall i,P (f i)) (Hf':forall i, P (f' i))
          (e:eq_fam X X' (fun i => existT P (f i) (Hf i))
                        (fun i => existT P (f' i) (Hf' i))),
     eqD P (set_ext (map_eq_fam (@projT1 _ _) e)) (h X f Hf) (h X' f' Hf')) ->
  forall x, P x.
intros P Pp h _.
fix 1.
destruct x.
apply h.
intros; apply set_elim.
Defined.

Lemma set_elim_nodep :
  forall (P:Type)
  (Pp:isSet P)
  (h:forall (X:Ti), (X->set) -> (X->P) -> P),
  (forall (X X':Ti) f f' Hf Hf'
     (e:eq_fam X X' f f')(eP:eq_fam X X' Hf Hf'), h X f Hf = h X' f' Hf') ->
  set->P.
intros.
apply set_elim with (P:=fun _ => P) (h:=h); trivial.
intros.
red.
match goal with |- transport _ ?e _ = _ => set (eqn := e) end.
simpl in eqn.
clearbody eqn.
Scheme eq_indd := Induction for eq Sort Prop.
apply eq_indd with (P:=fun x (e:sup X0 f=x) =>
        transport (fun _ => P) e (h X0 f Hf) = h X' f' Hf').
simpl.
apply H.
apply (map_eq_fam (@projT1 _ _) e).
admit.
Qed.


Definition eq_set := @eq set.

(*
Definition idx (x:set) := let (X,_) := x in X.
Definition elts (x:set) : idx x -> set :=
  match x return idx x -> set with
  | sup X f => f
  end.

Fixpoint eq_set (x y:set) {struct x} :=
  (forall i, #exists j, eq_set (elts x i) (elts y j)) /\
  (forall j, #exists i, eq_set (elts x i) (elts y j)).

Lemma isProp_eq_set x y : isProp (eq_set x y).
destruct x; simpl; intros.
apply isProp_conj.
 apply isProp_forall; intros i; apply tr_prop.
 apply isProp_forall; intros i; apply tr_prop.
Qed.

Lemma eq_set_refl : forall x, eq_set x x.
induction x; simpl.
split; intros; apply tr_i.
 exists i; trivial.
 exists j; trivial.
Qed.

Lemma eq_set_sym : forall x y, eq_set x y -> eq_set y x.
induction x; destruct y; simpl; intros.
destruct H0.
split; intros.
 elim (H1 i) using tr_ind_tr; intros (?,?).
 apply tr_i.
 exists x; auto.

 elim (H0 j) using tr_ind_tr; intros (?,?).
 apply tr_i; exists x; auto.
Qed.

Lemma eq_set_trans : forall x y z,
  eq_set x y -> eq_set y z -> eq_set x z.
induction x; destruct y; destruct z; simpl; intros.
destruct H0.
destruct H1.
split; intros.
 elim (H0 i) using tr_ind_tr; intros (?,?).
 elim (H1 x) using tr_ind_tr; intros (?,?).
 apply tr_i; exists x0; eauto.

 elim (H3 j) using tr_ind_tr; intros (?,?).
 elim (H2 x) using tr_ind_tr; intros (?,?).
 apply tr_i; exists x0; eauto.
Qed.


Lemma eq_set_def : forall x y,
  (forall i, #exists j, eq_set (elts x i) (elts y j)) ->
  (forall j, #exists i, eq_set (elts x i) (elts y j)) ->
  eq_set x y.
destruct x; simpl; auto.
Qed.
 *)

Definition in_set (x y:set) : Prop.
apply  set_elim_nodep with (h:=fun X f _ => #exists j, eq_set x (f j))(3:=y).
admit.
intros.

apply (@pred_ext unit) with 
#exists j, eq_set x (elts y j).


Lemma in_set_ind P x y :
  isProp P ->
  (forall j, eq_set x (elts y j) -> P) ->
  in_set x y -> P.
intros.
apply (proj1 tr_ex_sig) in H0.
elim H0 using tr_ind; auto.  
destruct 1; intros; eauto.
Qed.

Lemma isProp_in_set x y : isProp (in_set x y).
apply tr_prop.
Qed.

  Definition incl_set x y := forall z, in_set z x -> in_set z y.

Lemma isProp_incl_set x y : isProp (incl_set x y).
apply isProp_forall; intros.
apply isProp_forall; intros.
auto.
apply tr_prop.
Qed.
Hint Resolve isProp_eq_set isProp_incl_set isProp_in_set tr_prop.


Lemma eq_elim0 x y i :
  eq_set x y ->
  in_set (elts x i) y.
destruct x; simpl; intros.
destruct H.
red; auto.
Qed.

Lemma eq_set_ax : forall x y,
  eq_set x y <-> (forall z, in_set z x <-> in_set z y).
unfold in_set; split; intros.
 split; intros h; Tdestruct h.
  elim (eq_elim0 x y x0) using in_set_ind; intros; auto.
  Texists j; apply eq_set_trans with (elts x x0); trivial.

  apply eq_set_sym in H.
  elim (eq_elim0 y x x0) using in_set_ind; intros; auto.
  Texists j; apply eq_set_trans with (elts y x0); trivial.

  apply eq_set_def; intros.
   apply H.
   Texists i; apply eq_set_refl.

   destruct (H (elts y j)).
   elim H1 using in_set_ind; intros; auto.
    Texists j0; apply eq_set_sym; trivial.

    Texists j; apply eq_set_refl.
Qed.

Definition elts' (x:set) (i:idx x) : {y|in_set y x}.
exists (elts x i).
abstract (apply tr_i; exists i; apply eq_set_refl).
Defined.

Lemma in_reg : forall x x' y,
  eq_set x x' -> in_set x y -> in_set x' y.
intros.
elim H0 using in_set_ind; intros; auto.
apply tr_i; exists j.
apply eq_set_trans with x; trivial.
apply eq_set_sym; trivial.
Qed.

Lemma eq_intro : forall x y,
  (forall z, in_set z x -> in_set z y) ->
  (forall z, in_set z y -> in_set z x) ->
  eq_set x y.
intros.
rewrite eq_set_ax.
split; intros; eauto.
Qed.

Lemma eq_elim : forall x y y',
  in_set x y ->
  eq_set y y' ->
  in_set x y'.
intros.
rewrite eq_set_ax in H0.
destruct (H0 x); auto.
Qed.


  Lemma wf_ax :
  forall (P:set->Prop),
  (forall x, isProp (P x)) ->
  (forall x, (forall y, in_set y x -> P y) -> P x) -> forall x, P x.
intros P Pp H x.
cut (forall x', eq_set x x' -> P x');[auto using eq_set_refl|].
induction x; intros.
apply H; intros.
assert (in_set y (sup X f)).
 apply eq_elim with x'; trivial.
 apply eq_set_sym; trivial.
clear H1 H2.
elim H3 using in_set_ind; intros; auto.
apply eq_set_sym in H1; eauto.
Qed.


Definition empty :=
  sup False (fun x => match x with end).

Lemma empty_ax : forall x, ~ in_set x empty.
red; intros.
elim H using in_set_ind; intros.
 apply isProp_False.
contradiction.
Qed.

Definition singl x := sup unit (fun _ => x).

Definition pair_spec (a b:set->Prop) (x:set) : Prop :=
  forall z, in_set z x <-> #(a z \/ b z).

Definition pair x y :=
  sup bool (fun b => if b then x else y).

Lemma pair_spec_intro a b :
  pair_spec (fun a' => eq_set a' a) (fun b' => eq_set b' b) (pair a b).
intros z.
unfold pair; simpl.
split; intros.
 elim H using in_set_ind; intros; auto.
 apply tr_i.
 destruct j; auto.

 elim H using tr_ind; intros; auto.
 destruct x.
  apply tr_i; exists true; trivial.
  apply tr_i; exists false; trivial.
Qed.

Lemma pair_ax : forall a b z,
  in_set z (pair a b) <-> #(eq_set z a \/ eq_set z b).
Proof pair_spec_intro.


Lemma pair_morph :
  forall a a', eq_set a a' -> forall b b', eq_set b b' ->
  eq_set (pair a b) (pair a' b').
unfold pair.
simpl; intros.
split; intros.
 apply tr_i; exists i; destruct i; trivial.
 apply tr_i; exists j; destruct j; trivial.
Qed.

Definition subset_spec (x:set) (P:set->Prop) (y:set) :=
  forall z,
  in_set z y <->
  in_set z x /\ # (exists2 z', eq_set z z' & P z').

Definition subset (x:set) (P:set->Prop) :=
  sup {a|exists2 x', eq_set (elts x a) x' & P x'}
    (fun y => elts x (proj1_sig y)).

Lemma subset_ax : forall x P, subset_spec x P (subset x P).
red.
unfold subset; simpl.
split; intros.
 elim H using in_set_ind; simpl; intros; auto.
 clear H; destruct j as (j,?); simpl in H0.
 split.
  apply tr_i; exists j; trivial.

  destruct e.
  apply tr_i; exists x0; trivial.
  apply eq_set_trans with (elts x j); trivial.

 destruct H.
 elim H using in_set_ind; auto.
 clear H; intros.
 elim H0 using tr_ind; intros; auto.
 destruct x0.
 assert (exists2 x', eq_set (elts x j) x' & P x').
  exists x0; trivial.
  apply eq_set_trans with z; trivial.
  apply eq_set_sym; trivial.
 apply tr_i; exists
  (@exist _ (fun a=>exists2 x',eq_set (elts x a) x' & P x')
    j H3); simpl; trivial.
Qed.

Definition power (x:set) :=
  sup (idx x->Prop)
   (fun P => subset x (fun y => exists2 i, eq_set y (elts x i) & P i)).

Lemma power_ax : forall x z,
  in_set z (power x) <->
  (forall y, in_set y z -> in_set y x).
unfold power; simpl; intros.
split; intros.
 elim H using in_set_ind; intros; auto.
 simpl in *.
 specialize eq_elim with (1:=H0)(2:=H1); intro.
 apply (proj1 (proj1 (subset_ax _ _ _) H2)).

 apply tr_i; exists (fun i => in_set (elts x i) z); simpl.
 apply eq_intro; intros.
  apply (fun x P z => proj2 (subset_ax x P z)).
  split; auto.
  elim H with z0 using in_set_ind; trivial; intros.
  Texists z0.
   apply eq_set_refl.

   exists j; trivial.
   apply in_reg with z0; trivial.

  elim (proj2 (proj1 (subset_ax _ _ _) H0)) using tr_ind; intros; auto.
  destruct x0 as (z', ?, (i,?,?)).
  apply in_reg with (elts x i); trivial.
  apply eq_set_sym; apply eq_set_trans with z'; trivial.
Qed.

Lemma power_morph : forall x y,
  eq_set x y -> eq_set (power x) (power y).
intros.
apply eq_intro; intros.
 rewrite power_ax in H0|-*; intros.
 apply eq_elim with x; auto.

 apply eq_set_sym in H.
 rewrite power_ax in H0|-*; intros.
 apply eq_elim with y; auto.
Qed.

  
 Definition union (x:set) :=
  sup {i:idx x & idx (elts x i)}
    (fun p => elts (elts x (projS1 p)) (projS2 p)).

Lemma union_ax : forall a z,
  in_set z (union a) <-> #exists2 b, in_set z b & in_set b a.
unfold in_set at 1, union; simpl; intros.
split; intros.
 Tdestruct H.
 Texists (elts a (projT1 x)).
  Texists (projT2 x); trivial.
  Texists (projT1 x); apply eq_set_refl.

 Tdestruct H.
 Tdestruct H0.
 assert (in_set z (elts a x0)).
  apply eq_elim with x; trivial.
 Tdestruct H1.
 Texists (existT (fun i=>idx(elts a i)) x0 x1); simpl.
 trivial.
Qed.

Lemma union_morph :
  forall a a', eq_set a a' -> eq_set (union a) (union a').
intros.
apply eq_set_ax; intros z.
rewrite union_ax.
rewrite union_ax.
split; intros h; Tdestruct h as (b,?,?); Texists b; trivial.
 apply eq_elim with a; trivial.
 apply eq_elim with a'; trivial.
 apply eq_set_sym; trivial.
Qed.


Fixpoint num (n:nat) : set :=
  match n with
  | 0 => empty
  | S k => union (pair (num k) (pair (num k) (num k)))
  end.

Definition infinity := sup _ num.

Lemma infty_ax1 : in_set empty infinity.
 Texists 0.
 unfold elts, infinity, num.
 apply eq_set_refl.
Qed.

Lemma infty_ax2 : forall x, in_set x infinity ->
  in_set (union (pair x (pair x x))) infinity.
intros.
elim H using in_set_ind; intros; auto.
Texists (S j).
simpl elts.
apply union_morph.
apply pair_morph; trivial.
apply pair_morph; trivial.
Qed.

Definition replf (x:set) (F:set->set) :=
  sup _ (fun i => F (elts x i)).

Lemma replf_ax : forall x F z,
  (forall z z', in_set z x ->
   eq_set z z' -> eq_set (F z) (F z')) ->
  (in_set z (replf x F) <->
   #exists2 y, in_set y x & eq_set z (F y)).
unfold replf; simpl; intros.
split; intros.
 elim H0 using in_set_ind; intros; auto.
 simpl in *.
 Texists (elts x j); trivial.
 Texists j; apply eq_set_refl.

 elim H0 using tr_ind; intros; auto.
 destruct x0 as (x',?,?).
 elim H1 using in_set_ind; intros; auto.
 Texists j; simpl.
 apply eq_set_trans with (F x'); trivial.
 apply eq_set_sym.
 apply H.
  Texists j; apply eq_set_refl.
  apply eq_set_sym; trivial.
Qed.

End hS.

 *)

Hint Resolve S.isProp_eq_set S.isProp_incl_set S.isProp_in_set.

Module IZF_R <: IZF_R_sig TrSubThms.
(*Module IZF_R <: IZF_R_Ex_sig CoqSublogicThms.*)

Definition set := quo S.set S.eq_set.
Definition eq_set := @eq set.

(*Parameter sup :*)

Instance isRel_eqset : isRel S.eq_set.
split; intros; auto.
split; red; intros.
 apply S.eq_set_refl.

 apply S.eq_set_sym; trivial.  

 apply S.eq_set_trans with y; trivial.  
Qed.

Lemma isSet_set : isSet set.
apply isSet_quo; auto with *.
Qed.

Lemma isProp_eq x y : isProp (eq_set x y).
red; intros; apply isSet_set.
Qed.
Global Hint Resolve isProp_eq.

Definition qset_set (q:set) (x:S.set) : Prop :=
  q = quo_i _ x.

(*Lemma qset_set_eq (x:S.set) :
  qset_set (quo_i _ x) = S.eq_set x.
unfold qset_set.
apply pred_ext; intros; auto.
apply quo_i_eq.
Qed.
*)
(*
Definition is_set (P:set->Prop) := tr (isClass eq_set P).
Definition mk_qset (P:set->Prop) (Ps:is_set P) : qset :=
  exist is_set P Ps.
*)

Definition in_set (x y:set) :=
  tr { x' | x = quo_i _ x' /\ tr{ y' | y = quo_i _ y' /\ S.in_set x' y'}}.

Lemma isProp_in x y : isProp (in_set x y).
apply tr_prop.
Qed.
Global Hint Resolve isProp_in.

Lemma in_set_ind P x y :
  isProp P ->
  (forall x' y', x = quo_i _ x' -> y = quo_i _ y' -> S.in_set x' y' -> P) ->
  in_set x y -> P.
intros.
elim H0 using tr_ind; auto.
clear H0.
destruct 1 as (x', (?,?)).
elim H1 using tr_ind; auto.
clear H1.
destruct 1 as (y',(?,?)).
eauto.
Qed.

Lemma in_set_eqv x y :
  in_set (quo_i _ x) (quo_i _ y) <-> S.in_set x y.
split; intros.
 elim H using in_set_ind; intros; auto.
 apply quo_i_eq in H0.
 apply quo_i_eq in H1.
 apply S.eq_elim with y'; trivial.
  apply S.in_reg with x'; trivial.
  apply S.eq_set_sym; trivial.
  apply S.eq_set_sym; trivial.

 apply tr_i; exists x; split; trivial.
 apply tr_i; exists y; split; trivial.
Qed.


Lemma eq_set_ax : forall x y,
  eq_set x y <-> (forall z, in_set z x <-> in_set z y).
unfold eq_set.
split; intros.
 subst y; auto with *.

 revert H.
 elim x using (quo_ind _); auto.
 clear x; intros x.
 elim y using (quo_ind _); auto.
 clear y; intros y.
 intros.
 apply quo_i_eq.
 apply S.eq_set_ax; intros.
 do 2 rewrite <- in_set_eqv.
 apply H.
Qed.

Lemma in_reg : forall x x' y,
  eq_set x x' -> in_set x y -> in_set x' y.
unfold eq_set; intros; subst; trivial.
Qed.

(* Set induction *)
(*
Lemma isProp_Acc X (R:X->X->Prop) x : isProp (Acc R x).
red; revert x; fix 2.
intros x a a'.
destruct a; destruct a'.
assert (Hrec := fun y r => isProp_Acc y (a y r)).
clear isProp_Acc.
f_equal.
apply isProp_forall; intros y.
apply isProp_forall; intros r.
red; intros.
 transitivity (a y r); auto.
Qed.
  
Lemma Acc_in_set : forall x, Acc in_set x.
cut (forall x y, eq_set x y -> Acc in_set y).
 intros.
 apply H with x; apply eq_set_refl.
induction x; intros.
constructor; intros.
specialize eq_elim with (1:=H1)(2:=eq_set_sym _ _ H0); intro.
clear y H0 H1.
elim H2 using tr_ind; intros.
 apply isProp_Acc.
destruct x; simpl in *.
apply H with x.
apply eq_set_sym; trivial.
Qed.


Lemma wf_rec :
  forall P : set -> Type,
  (forall x, (forall y, in_set y x -> P y) -> P x) -> forall x, P x.
intros.
elim (Acc_in_set x); intros.
apply X; apply X0.
Defined.
*)

(*
  Lemma wf_ax0 :
  forall (P:set->Prop),
  (forall x, isProp (P x)) ->
  (forall x, (forall y, in_set y x -> P y) -> P x) -> forall x, P x.
intros P Pp H x.
elim x using (quo_ind _); auto.
clear x; intros x.
elim x using S.wf_ax; auto.
intros y Hy.
apply H.
intros z.
elim z using (quo_ind _); auto.
clear z; intros z ?.
apply in_set_eqv in H0.
auto.
Qed.
 *)

  Lemma wf_ax :
  forall (P:set->Prop),
  (forall x, (forall y, in_set y x -> #(P y)) -> #(P x)) -> forall x, #(P x).
intros P H x.
elim x using (quo_ind _); auto.
clear x; intros x.
elim x using S.wf_ax with (P:=fun x=>P(quo_i _ x)); auto.
intros y Hy.
apply H.
intros z.
elim z using (quo_ind _); auto.
clear z; intros z ?.
apply in_set_eqv in H0.
auto.
Qed.

(* *)

Definition empty := quo_i _ S.empty.

(*Lemma empty_ax0 : forall x, ~ in_set x empty.
red; intros.
elim H using in_set_ind; auto.
 apply isProp_False.
intros x' y' _ mtdef inmt.
apply quo_i_eq in mtdef.
apply S.eq_elim with (2:=S.eq_set_sym _ _ mtdef) in inmt.
apply S.empty_ax in inmt; trivial.
Qed.*)

Lemma empty_ax : forall x, in_set x empty -> #False.
intros.
elim H using in_set_ind; auto.
intros x' y' _ mtdef inmt.
apply quo_i_eq in mtdef.
apply S.eq_elim with (2:=S.eq_set_sym _ _ mtdef) in inmt.
apply S.empty_ax in inmt; trivial.
Qed.

Definition pair (a b:set) : set.
pose (h := fun a b => quo_i _ (S.pair a b)).
assert (forall a x y, S.eq_set x y -> h a x = h a y).
 intros.
 unfold h.
 apply quo_i_eq.
 apply S.pair_morph; trivial.
 reflexivity.
pose (qh := fun a => quo_ind_set_nodep _ isSet_set (h a) (H a) b).
apply quo_ind_set_nodep with (1:=_) (h0:=qh) (4:=a).
 exact isSet_set.
intros.
unfold qh.
elim b using (quo_ind _).
 red; intros.
 apply isSet_set.
intros.
unfold quo_ind_set_nodep.
rewrite quo_ind_set_eq.
rewrite quo_ind_set_eq.
unfold h.
apply quo_i_eq.
apply S.pair_morph; trivial.
apply S.eq_set_refl.
Defined.

Lemma pair_eq a b:
  pair (quo_i _ a) (quo_i _ b) = quo_i _ (S.pair a b).
unfold pair.
unfold quo_ind_set_nodep.
eapply transitivity.
match goal with
    |- context[quo_ind_set ?X ?R ?Rr ?P ?Ps ?h ?hcomp (quo_i ?Rr ?x)] =>
  apply (quo_ind_set_eq X R Rr P Ps h hcomp x)
end.
match goal with
    |- context[quo_ind_set ?X ?R ?Rr ?P ?Ps ?h ?hcomp (quo_i ?Rr ?x)] =>
  apply (quo_ind_set_eq X R Rr P Ps h hcomp x)
end.
Qed.

Lemma pair_ax : forall a b z,
  in_set z (pair a b) <-> #(z=a \/ z=b).
intros.
elim a using (quo_ind _); auto with *.
clear a; intros a.
elim b using (quo_ind _); auto with *.
clear b; intros b.
elim z using (quo_ind _); auto with *.
clear z; intros z.
rewrite pair_eq.
rewrite in_set_eqv.
rewrite S.pair_ax.
split; apply TrMono; (destruct 1;[left|right]); try apply quo_i_eq; trivial.
 apply quo_i_eq in H; trivial.
 apply quo_i_eq in H; trivial.
Qed.
Print Assumptions pair_ax.

Definition union (a:set) : set.
pose (h := fun a => quo_i _ (S.union a)).
apply quo_ind_set_nodep with (1:=_) (h0:=h) (4:=a).
 exact isSet_set.
unfold h; intros.
apply quo_i_eq.
apply S.union_morph; trivial.
Defined.

Lemma union_eq a:
  union (quo_i _ a) = quo_i _ (S.union a).
unfold union.
unfold quo_ind_set_nodep.
rewrite quo_ind_set_eq.
reflexivity.
Qed.

Lemma union_ax : forall a z,
  in_set z (union a) <-> #exists2 b, in_set z b & in_set b a.
intros.
elim a using (quo_ind _); auto with *.
clear a; intros a.
elim z using (quo_ind _); auto with *.
clear z; intros z.
rewrite union_eq.
rewrite in_set_eqv.
rewrite S.union_ax.
split.
 apply TrMono.
 destruct 1 as (b,?,?); exists (quo_i _ b).
  apply in_set_eqv; trivial.
  apply in_set_eqv; trivial.

 intros h.
 Tdestruct h as (b,?,?).
 revert H H0.
 elim b using (quo_ind _); auto.
 clear b; intros b ? ?.
 Texists b.
  apply in_set_eqv; trivial.
  apply in_set_eqv; trivial.
Qed.

Definition subset (a:set) (P:set->Prop) : set.
pose (P' z := P (quo_i _ z)).
pose (h := fun a => quo_i _ (S.subset a P')).
apply quo_ind_set_nodep with (1:=_) (h0:=h) (4:=a).
 exact isSet_set.
intros.
unfold h.
apply quo_i_eq.
assert (aux := S.subset_ax).
red in aux.
apply S.eq_set_ax; intros z.
do 2 rewrite aux.
apply and_iff_morphism; auto with *.
split; intros.
 apply S.eq_elim with x; trivial.
 apply S.eq_elim with y; trivial.
 apply S.eq_set_sym; trivial.
Defined.

Lemma subset_eq a P:
  subset (quo_i _ a) P = quo_i _ (S.subset a (fun z => P (quo_i _ z))).
unfold subset.
unfold quo_ind_set_nodep.
rewrite quo_ind_set_eq.
reflexivity.
Qed.

Lemma subset_ax x P z :
  in_set z (subset x P) <->
  in_set z x /\ # (exists2 z', eq_set z z' & P z').
elim x using (quo_ind _); auto with *.
clear x; intros x.
elim z using (quo_ind _); auto with *.
clear z; intros z.
rewrite subset_eq.
rewrite in_set_eqv.
rewrite in_set_eqv.
assert (aux := S.subset_ax).
red in aux.
rewrite aux.
apply and_iff_morphism; auto with *.
split.
 apply TrMono.
 destruct 1 as (b,?,?); exists (quo_i _ b); trivial.
 apply quo_i_eq; trivial.

 intros h.
 Tdestruct h as (b,?,?).
 revert H H0.
 elim b using (quo_ind _); auto.
 clear b; intros b ? ?.
 apply quo_i_eq in H.
 Texists b; trivial.
Qed.

Definition infinite := quo_i _ S.infinite.

Lemma infinity_ax1 : in_set empty infinite.
apply in_set_eqv.
apply S.infinity_ax1.
Qed.

Lemma infinity_ax2 : forall x, in_set x infinite ->
  in_set (union (pair x (pair x x))) infinite.
intros x.
elim x using (quo_ind _); auto.
clear x; intros x tyx.
apply in_set_eqv in tyx.
rewrite !pair_eq, union_eq.
apply in_set_eqv.
apply S.infinity_ax2; trivial.
Qed.

Definition power (a:set) : set.
pose (h := fun a => quo_i _ (S.power a)).
apply quo_ind_set_nodep with (1:=_) (h0:=h) (4:=a).
 exact isSet_set.
unfold h; intros.
apply quo_i_eq.
apply S.power_morph; trivial.
Defined.

Lemma power_eq a:
  power (quo_i _ a) = quo_i _ (S.power a).
unfold power.
unfold quo_ind_set_nodep.
rewrite quo_ind_set_eq.
reflexivity.
Qed.

Lemma power_ax : forall x z,
  in_set z (power x) <->
  (forall y, in_set y z -> in_set y x).
intros.
elim x using (quo_ind _); auto with *.
clear x; intros x.
elim z using (quo_ind _); auto with *.
clear z; intros z.
rewrite power_eq.
rewrite in_set_eqv.
rewrite S.power_ax.
split.
 intros h y.
 elim y using (quo_ind _); auto.
 intros.
 apply in_set_eqv.
 apply in_set_eqv in H.
 auto.

 intros h y ?.
 apply in_set_eqv.
 apply in_set_eqv in H.
 auto.
Qed.


(*Definition repl (a:set) (R:set->set->Prop) : set.
elim a using (quo_ind _); auto.
clear a; intros a.
quo_i _ (S.replf a (fun x => S.uchoice*)
(*
Definition replf (x:set) (F:set->set) : set.
@quo_i

  assert (tr (S.set->S.set)).

  sup _ (fun i => F (elts x i)).

Lemma replf_ax : forall x F z,
  (forall z z', in_set z x ->
   eq_set z z' -> eq_set (F z) (F z')) ->
  (in_set z (replf x F) <->
   #exists2 y, in_set y x & eq_set z (F y)).
unfold replf; simpl; intros.
split; intros.
 elim H0 using in_set_ind; intros; auto.
 simpl in *.
 Texists (elts x j); trivial.
 Texists j; apply eq_set_refl.

 elim H0 using tr_ind; intros; auto.
 destruct x0 as (x',?,?).
 elim H1 using in_set_ind; intros; auto.
 Texists j; simpl.
 apply eq_set_trans with (F x'); trivial.
 apply eq_set_sym.
 apply H.
  Texists j; apply eq_set_refl.
  apply eq_set_sym; trivial.
Qed.

*)



Parameter repl : set -> (set -> set -> Prop) -> set.

Lemma repl_ax:
    forall a (R:set->set->Prop),
    (forall x x' y y', in_set x a ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x y y', in_set x a -> R x y -> R x y' -> eq_set y y') ->
    forall z, in_set z (repl a R) <->
     #(exists2 y, in_set y a & R y z).
Admitted.

Lemma repl_mono a a' :
 (forall z, in_set z a -> in_set z a') ->
 forall R R' : set -> set -> Prop,
 (forall x x', eq_set x x' ->
  forall y y', eq_set y y' -> (R x y <-> R' x' y')) ->
 forall z,
 in_set z (repl a R) ->
 in_set z (repl a' R').
Admitted.


(*Definition uch (P:set->Prop) : set :=
  quo_i _ (S.sup (tr{x|#P x} /\ isProp {x|#P x})
                 (fun c => let (w,p) := c in proj1_sig (tr_ind_nodep p (fun w => w) w))).

Lemma uch_ax P z :
  isProp {x:set|#P x} ->
  (in_set z (uch P) <-> #P z).
intros Hp.
unfold uch.
split; intros.
 elim H using tr_ind_tr; clear H.
 intros (z',(?,?)).
 elim H0 using tr_ind_tr; clear H0.
 intros (y',(?,?)).
 apply quo_i_eq in H0.
 apply S.eq_elim with (2:=symmetry H0) in H1.
 red in H1; simpl in H1.
 clear H0.
 elim H1 using tr_ind_tr; clear H1.
 intros (j,?).
 destruct j.
 destruct (tr_ind_nodep i (fun w => w) t); simpl in H0.
(* elim t using tr_ind_tr; clear t.
 intros (x',?).*)
 apply (quo_i_eq _) in H0.
 subst z; rewrite H0.
 apply tr_i; trivial.

 elim H using tr_ind_tr; clear H.
 elim z using (quo_ind _); auto.
 intros z' pz'.
 assert (Hp': isProp {x'|#P(quo_i _ x')}).
  red; intros (x,px) (y,py).


  intros z'.
 apply tr_i; exists z'; split; trivial.
 apply tr_i; eexists; split; [reflexivity|].
 red; simpl.
 exists 
 red.
 replace (quo_i _ z') with 


 Definition uch (P:set->Prop) : set :=
  quo_i _ (S.sup (tr{x|P (quo_i _ x)} /\ isProp {x|P (quo_i _ x)})
                 (fun c => let (w,p) := c in proj1_sig (tr_ind_nodep p (fun w => w) w))).

Lemma uch_ax P z :
  isProp {x:set|#P x} ->
  (in_set z (uch P) <-> #P z).
intros Hp.
unfold uch.
split; intros.
 elim H using tr_ind_tr; clear H.
 intros (z',(?,?)).
 elim H0 using tr_ind_tr; clear H0.
 intros (y',(?,?)).
 apply quo_i_eq in H0.
 apply S.eq_elim with (2:=symmetry H0) in H1.
 red in H1; simpl in H1.
 clear H0.
 elim H1 using tr_ind_tr; clear H1.
 intros (j,?).
 destruct j.
 destruct (tr_ind_nodep i (fun w => w) t); simpl in H0.
(* elim t using tr_ind_tr; clear t.
 intros (x',?).*)
 apply (quo_i_eq _) in H0.
 subst z; rewrite H0.
 apply tr_i; trivial.

 elim H using tr_ind_tr; clear H.
 elim z using (quo_ind _); auto.
 intros z' pz'.
 assert (Hp': isProp {x'|#P(quo_i _ x')}).
  red; intros (x,px) (y,py).


  intros z'.
 apply tr_i; exists z'; split; trivial.
 apply tr_i; eexists; split; [reflexivity|].
 red; simpl.
 exists 
 red.
 replace (quo_i _ z') with 
 

 simpl in H1.
 unfold uch; rewrite in_set_ax.
split; intros.
 elim H using tr_ind_tr; clear H.
 intros ((w,Hp'),?); simpl.
 destruct (tr_ind_nodep Hp' (fun w => w) w); simpl in *.
 subst z; trivial.

 apply tr_i; exists (conj (tr_i (exist (fun z=>tr(P z)) z H)) Hp).
 destruct (tr_ind_nodep Hp (fun w => w) (tr_i (exist (fun z=>tr(P z)) z H))); simpl.
 assert (aux := Hp (exist (fun z=>tr(P z)) z H) (exist (fun z=>tr(P z)) x t)).
 apply f_equal with (f:=fun x=>proj1_sig x) in aux; simpl in aux.
 trivial. 
Qed.

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


Lemma uchoice :
  forall (P:set->Prop),
  (forall q, isProp (P q)) ->
  (#exists x, P x) ->
  (forall y y', P y -> P y' -> y = y') ->
  set.
intros P Pp Pex Puniq.
clear Pp Pex Puniq.
apply (fun Hp Hu Hex => proj1_sig (descr (P:=fun x => (#P x) /\ isProp {x|P x}) Hp Hu Hex)).
 intros; apply isProp_conj; auto.
 apply isProp_isProp.

 intros a a' (?,?) (?,_).
 elim H using tr_ind.
  red; intros; apply isSet_set.
 clear H; intros H.
 elim H1 using tr_ind.
  red; intros; apply isSet_set.
 clear H1; intros H1.
 assert (aux := H0 (exist (fun z=>P z) a H) (exist (fun z=>P z) a' H1)).
 apply f_equal with (f:=fun x=>proj1_sig x) in aux; simpl in aux.
 trivial.

 

 
apply (proj1 (@tr_ex_sig _ P)) in Pex; trivial.
exact (proj1_sig (descr Pp Puniq Pex)).  
Defined.
Lemma uchoice :
  forall (P:set->Prop),
  (forall q, isProp (P q)) ->
  (#exists x, P x) ->
  (forall y y', P y -> P y' -> y = y') ->
  set.
intros P Pp Pex Puniq.
apply (proj1 (@tr_ex_sig _ P)) in Pex; trivial.
exact (proj1_sig (descr Pp Puniq Pex)).  
Defined.

Lemma uchoice_ext : forall (P:set->Prop) x
  (Pp : forall q, isProp (P q))
  (w:#exists x, P x )
  (uniq:forall y y', P y -> P y' -> y = y'),
  P x -> uchoice P Pp w uniq = x.
intros.
unfold uchoice.
apply descr_eq; trivial.
Qed.
Print Assumptions uchoice_ext.

*)

End IZF_R.
Import IZF_R.


(*
  Lemma qrepl_ax:
    forall a (R:qset->qset->Prop),
    (forall x y y', in_qset x a -> R x y -> R x y' -> y = y') ->
    exists b, forall x, in_qset x b <->
     (exists2 y, in_qset y a & R y x).
  intros.
  


(* Fixpoint *)
Fixpoint wfrec (F:(set->set)->set->set) (x:set) : set :=
  F (fun y => union (sup {i:idx x|eq_set (elts x i) y}
               (fun i => wfrec F (elts x (proj1_sig i))))) x.
Section FixRec.
Hypothesis F : (set->set)->set->set.
Hypothesis Fext : forall x x' f f',
  (forall y y', in_set y x -> eq_set y y' -> eq_set (f y) (f' y')) ->
  eq_set x x' ->
  eq_set (F f x) (F f' x').

Instance wfrecm : Proper (eq_set==>eq_set) (wfrec F).
do 2 red.
induction x; destruct y; intros.
simpl wfrec.
apply Fext; trivial.
simpl in H0; destruct H0.
intros.
apply union_morph.
simpl.
split; intros.
 clear H2; destruct i as (i,?); simpl.
 destruct (H0 i) as (j,?).
 assert (eq_set (f0 j) y').
  apply eq_set_trans with y; trivial.
  apply eq_set_trans with (f i); trivial.
  apply eq_set_sym; trivial.
 exists (exist _ j H4); simpl.
 apply H; trivial.

 destruct H2 as (i,?H2); simpl in i,H2.
 destruct j as (j,?).
 exists (exist _ i (eq_set_sym _ _ H2)); simpl.
 apply H.
 apply eq_set_sym.
 apply eq_set_trans with y; trivial. 
 apply eq_set_trans with y'; trivial.
 apply eq_set_sym; trivial.
Qed.

Lemma wfrec_eqn x :
  eq_set (wfrec F x) (F (wfrec F) x).
destruct x; simpl.
apply Fext.
2:apply eq_set_refl.
intros.
rewrite eq_set_ax.
intros z.
rewrite union_ax.
split; intros.
 destruct H1 as (b,?,?).
 destruct H2 as ((j,e),?).
 simpl in H2.
 apply eq_elim with b; trivial.
 apply eq_set_trans with (1:=H2).
 apply wfrecm.
 apply eq_set_trans with y; trivial.

 destruct H as (i,H).
 simpl in i,H.
 apply eq_set_sym in H0.
 exists (wfrec F (f i)).
  apply eq_elim with (1:=H1).
  apply wfrecm.
  apply eq_set_trans with y; trivial.

  apply eq_set_sym in H.
  exists (exist _ i H).
  simpl.
  apply eq_set_refl.
Qed.
End FixRec.



(* We only use the following instance of unique choice for
   replacement: *)
Definition ttrepl :=
  forall a:set, unique_choice {x|in_set x a} set eq_set.

(* We show it is a consequence of [choice]. *)
Lemma ttrepl_axiom : ttrepl.
red; red; intros; apply choice_axiom; trivial.
Qed.

Lemma repl_ax:
    forall a (R:set->set->Prop),
    (forall x x' y y', in_set x a ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x y y', in_set x a -> R x y -> R x y' -> eq_set y y') ->
    exists b, forall x, in_set x b <->
     (exists2 y, in_set y a & R y x).
intros.
elim (ttrepl_axiom (subset a (fun x=>exists y, R x y))
        (fun p y => R (proj1_sig p) y)); intros.
pose (a' := {x|in_set x (subset a (fun x => exists y, R x y))}).
fold a' in x,H1.
exists (repl1 _ x).
intros.
elim (repl1_ax _ x x0); intros.
 fold a' in H2,H3|-.
 split; intros.
  elim H2; trivial; intros.
  exists (proj1_sig x1).
   apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig x1))).

   apply H with (4:=H1 x1).
    apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig x1))).
    apply eq_set_refl.
    apply eq_set_sym; trivial.

  apply H3.
  destruct H4.
  assert (in_set x1 (subset a (fun x => exists y, R x y))).
   apply (proj2 (subset_ax a (fun x => exists y, R x y) x1)).
   split; trivial.
   exists x1.
    apply eq_set_refl.
    exists x0; trivial.
  pose (x' := exist _ x1 H6 : a').
  exists x'.
  apply H0 with x1; trivial.
  apply (H1 x').

 apply H0 with (proj1_sig z); trivial.
  apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig z))).
  apply H with (proj1_sig z') (x z'); trivial.
   apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig z'))).
   apply eq_set_sym; trivial.
   apply eq_set_refl.

(* side conditions *)
 elim (proj2 (proj1 (subset_ax _ _ _) (proj2_sig x))); intros. 
 destruct H2.
 exists x1; apply H with (4:=H2).
  apply in_reg with (proj1_sig x); trivial.
  apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig x))).

  apply eq_set_sym; trivial.

  apply eq_set_refl.

 assert (in_set (proj1_sig x) a).
  apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig x))).
 split; intros.
  apply H0 with (proj1_sig x); trivial.

  revert H1; apply H; trivial.
  apply eq_set_refl.
Qed.

(* Attempt to prove that choice is necessary for replacement, by deriving
   choice from replacement. Works only for relations that are morphisms for
   set equality... *)
Lemma ttrepl_needed_for_repl :
  forall a:set,
  let A := {x|in_set x a} in
  let eqA (x y:A) := eq_set (proj1_sig x) (proj1_sig y) in
  let B := set in
  let eqB := eq_set in
  forall (R:A->B->Prop),
  Proper (eqA==>eqB==>iff) R ->
  (forall x:A, exists y:B, R x y) ->
  (forall x y y', R x y -> R x y' -> eqB y y') ->
  exists f:A->B, forall x:A, R x (f x).
intros a A eqA B eqB R Rext Rex Runiq.
destruct repl_ax with
  (a:=a) (R:=fun x y => exists h:in_set x a, R (exist _ x h) y).
 intros.
 destruct H2.
 exists (in_reg _ _ _ H0 x0).
 revert H2; apply Rext; apply eq_set_sym; assumption.

 intros x y y' _ (h,Rxy) (h',Rxy').
 apply Runiq with (1:=Rxy).
 revert Rxy'; apply Rext.
  apply eq_set_refl.
  apply eq_set_refl.

 exists (fun y => union (subset x (fun z => R y z))).
 intro.
 destruct Rex with x0.
 apply Rext with (3:=H0);[apply eq_set_refl|].
 apply eq_set_sym.
 apply eq_set_ax; split; intros.
  rewrite union_ax; exists x1; trivial.
  rewrite subset_ax.
  split.
   apply H.
   exists (proj1_sig x0); [apply proj2_sig|].
   exists (proj2_sig x0).
   destruct x0; trivial.

   exists x1; trivial; apply eq_set_refl.

  rewrite union_ax in H1; destruct H1.
  rewrite subset_ax in H2; destruct H2.
  destruct H3.
  apply eq_elim with x2; trivial.
  apply eq_set_trans with (1:=H3).
  apply Runiq with (1:=H4); trivial.
Qed.
 *)

Notation "x ∈ y" := (in_set x y).
Notation "x == y" := (eq_set x y).

(* Deriving the existentially quantified sets *)

Lemma empty_ex: #exists empty, forall x, x ∈ empty -> #False.
apply tr_i.
exists empty.
exact empty_ax.
Qed.

Lemma pair_ex: forall a b, #exists c, forall x, x ∈ c <-> #(x == a \/ x == b).
intros.
apply tr_i.
exists (pair a b).
apply pair_ax.
Qed.

Lemma union_ex: forall a, #exists b,
    forall x, x ∈ b <-> #(exists2 y, x ∈ y & y ∈ a).
intros.
apply tr_i.
exists (union a).
apply union_ax.
Qed.

Lemma subset_ex : forall x P, #exists b,
  forall z, z ∈ b <->
  (z ∈ x /\ #exists2 z', z == z' & P z').
intros.
apply tr_i.
exists (subset x P).
apply subset_ax.
Qed.

Lemma power_ex: forall a, #exists b,
     forall x, x ∈ b <-> (forall y, y ∈ x -> y ∈ a).
intros.
apply tr_i.
exists (power a).
apply power_ax.
Qed.

Lemma repl_ex: forall a (R:set->set->Prop),
    (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x ∈ a -> R x y -> R x y' -> y == y') ->
    #exists b, forall x, x ∈ b <-> #(exists2 y, y ∈ a & R y x).
intros.
apply tr_i.
exists (repl a R).
apply repl_ax; trivial.
Qed.

(* Collection *)
(*Section Collection.

Section FromTTColl.

(* TTColl is a consequence of choice *)
Lemma ttcoll :
  forall (A:Ti) (R:A->set->Prop),
  (forall x:A, exists y:set, R x y) ->
  exists X:Ti, exists f : X->set,
    forall x:A, exists i:X, R x (f i).
intros.
destruct (choice_axiom A set R) as (f,Hf); trivial.
(* X is A because choice "chooses" just one y for each x *)
exists A; exists f; eauto.
Qed.

Lemma ttcoll' :
  forall (A:Ti) R,
  (forall x:A, exists y:set, R x y) ->
  exists B, forall x:A, exists2 y, y ∈ B & R x y.
intros.
destruct ttcoll with (1:=H) as (X,(f,Hf)).
exists (sup X f).
intro.
destruct Hf with x.
exists (f x0); trivial.
exists x0; apply eq_set_refl.
Qed.

Lemma coll_ax_ttcoll : forall A (R:set->set->Prop), 
    (forall x x' y y', in_set x A ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x, in_set x A -> exists y, R x y) ->
    exists B, forall x, in_set x A -> exists2 y, in_set y B & R x y.
intros.
destruct (ttcoll (idx A) (fun i y => R (elts A i) y)) as (X,(f,Hf)).
 intro i.
 apply H0.
 exists i; apply eq_set_refl.

 exists (sup X f); intros.
 destruct H1 as (i,?).
 destruct (Hf i) as (j,?).
 exists (f j).
  exists j; apply eq_set_refl.

  revert H2; apply H.
   exists i; apply eq_set_refl.
   apply eq_set_sym; assumption.
   apply eq_set_refl.
Qed.

(* Proving collection requires the specialized version of ttcoll *)
Lemma ttcoll'' : forall A (R:set->set->Prop),
  (forall x x' y y', in_set x A ->
   eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
  (forall x, x ∈ A -> exists y:set, R x y) ->
  exists f : {x|x∈ A} -> {X:Ti & X->set},
    forall x, exists i:projT1 (f x), R (proj1_sig x) (projT2 (f x) i).
intros.
destruct (coll_ax_ttcoll A R H H0) as (B,HB).
exists (fun _ => let (X,f) := B in existT (fun X => X->set) X f).
destruct B; simpl.
destruct x; simpl; intros.
destruct HB with x; trivial.
destruct H1.
exists x1.
apply H with (4:=H2); auto with *.
apply eq_set_refl.
Qed.

End FromTTColl.

Section FromChoice.

Lemma coll_ax_choice : forall A (R:set->set->Prop), 
    (forall x x' y y', in_set x A ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x, in_set x A -> exists y, R x y) ->
    exists B, forall x, in_set x A -> exists y, in_set y B /\ R x y.
intros.
elim (choice_axiom {x|x ∈ A} set (fun p y => R (proj1_sig p) y)); trivial; intros.
 exists (repl1 A x).
 intros.
 destruct H2.
 exists (x (elts' _ x1)); split.
  exists x1; apply eq_set_refl.

  apply H with (proj1_sig (elts' _ x1)) (x (elts' _ x1)); trivial.
   apply (proj2_sig (elts' _ x1)).
   apply eq_set_sym; trivial.
   apply eq_set_refl.

 apply H0.
 apply (proj2_sig x).
Qed.

End FromChoice.

End Collection.
*)

(* Infinity *)

Lemma infinity_ex: #exists2 infinite,
    #(exists2 empty, (forall x, x ∈ empty -> #False) & empty ∈ infinite) &
    (forall x, x ∈ infinite ->
     #exists2 y, (forall z, z ∈ y <-> #(z == x \/ z ∈ x)) &
       y ∈ infinite).
Texists infinite.
 Texists empty.
  exact empty_ax.
  exact infinity_ax1.

 intros.
 Texists (union (pair x (pair x x))); intros.
  rewrite union_ax.
  split; intros.
   Tdestruct H0.
   rewrite pair_ax in H1; Tdestruct H1.
    subst x; Tright; trivial.

    subst x0.
    rewrite pair_ax in H0; Tdestruct H0; apply tr_i; auto.

   Tdestruct H0.
    red in H0; subst z.
    Texists (pair x x).
     rewrite pair_ax; apply tr_i; auto.
     rewrite pair_ax; apply tr_i; auto.

    Texists x; trivial.
    rewrite pair_ax; Tleft; trivial.

  apply infinity_ax2; trivial.
Qed.

