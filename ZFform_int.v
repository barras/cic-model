
Require Import ZF ZFfo ZFform.
Require Import ZFpairs ZFrelations ZFnats ZFwf ZFord ZFlist.
Require Import ZFrank ZFgrothendieck.

Lemma wfax x : isWf x.
apply wf_ax; apply isWf_intro.
Qed.

(* More properties about VN universes *)

Lemma fo_VNlim_compl A :
  fo_in A ->
  fo_in (fun i => VNlim_compl (A i)).
Admitted.

Definition VN_ord (X:set) := subset X isOrd.

Instance VN_ord_morph : morph1 VN_ord.
intros ?? h; unfold VN_ord; apply subset_morph; trivial.
red; intros; reflexivity.
Qed.

Require Import ZFrank.

Lemma VN_ord_ax o : isOrd o -> VN_ord (VN o) == o.
intros.
apply eq_set_ax; split; intros.
*apply subset_ax in H0; destruct H0 as (?,(x',eqx,xo)).
 rewrite <-eqx in xo; clear x' eqx.
 apply VN_ord_inv; auto.
*assert (xo : isOrd x) by (apply isOrd_inv with o; auto).
 apply subset_intro;[|trivial].
 apply VN_incl with (VN x); auto.
 apply VN_intro; auto.
 apply VN_mono; auto.
Qed.


Lemma limOrd_VNlim X : isVNlim X -> limitOrd (VN_ord X).
intros (o,(lo,eqX)).
rewrite eqX.
rewrite VN_ord_ax; auto.
Qed.


Lemma repl_morph I I' R R' :
  I == I' ->
  (forall x x' y y', x ∈ I -> x==x' -> y==y' -> R x y <-> R' x' y') ->
  (forall x y y', x ∈ I -> R x y -> R x y' -> y==y') ->
  repl I R == repl I' R'.
intros.
apply eq_set_ax; intros z.
rewrite !repl_ax; trivial; intros.
*rewrite !ex_ex2.
 apply ex_morph; intros x.
 apply and_iff_morphisml; [rewrite H; reflexivity|auto with *].
*rewrite <-H in H2.
 cut (R x y).
 +apply H0; auto with *.
 +revert H5; apply H0; auto with *.
*rewrite <-H in H2.
 apply H1 with x; trivial.
 +revert H3; apply H0; auto with *.
 +revert H4; apply H0; auto with *.
*cut (R' x y).
 +rewrite H3 in H2.
  apply H0; auto with *.
 +revert H5; apply H0; auto with *.
Qed.

(*************************************)

Definition repls Mi :=
  sup Mi (fun I => sup Form (fun Rf => replf (List Mi) (fun vs =>
     cond_set (forall x y y', x ∈ I -> Fint (Cons x (Cons y vs)) Rf -> 
                             Fint (Cons x (Cons y' vs)) Rf -> y==y')
       (repl I (fun x y => Fint (Cons x (Cons y vs)) Rf))))).

Instance repls_morph : morph1 repls.
unfold repls; do 2 red; intros.
apply sup_morph;[trivial|].
red; intros.
apply sup_morph;[reflexivity|].
red; intros.
apply replf_morph;[rewrite H;reflexivity|].
red; intros.
apply cond_set_morph.
*apply fa_morph; intros x3.
 apply fa_morph; intros y0.
 apply fa_morph; intros y'.
 apply impl_morph; [rewrite H1; reflexivity|intros].
rewrite H5,H3; reflexivity.
*apply ZFrepl.repl_morph_raw;[trivial|].
do 2 red; intros.
rewrite H3,H5,H6,H7; reflexivity.
Qed.


Module OneUniv.
(* Building one single universe *)

Definition Ustage M k :=
  natrec (VNlim_compl M) (fun _ Mi => VNlim_compl (Mi ∪ repls Mi)) k.

Instance repls_auxm : morph2 (fun _ Mi => VNlim_compl (Mi ∪ repls Mi)).
do 3 red; intros.
rewrite H0; reflexivity.
Qed.

Hint Resolve repls_auxm : core.

Instance Ustage_morph : morph2 Ustage.
do 3 red; intros.
apply natrec_morph; trivial.
*rewrite H; reflexivity.
*apply repls_auxm.
Qed.

Lemma Ustage_0 M : Ustage M zero == VNlim_compl M.
unfold Ustage; apply natrec_0.
Qed.
Lemma Ustage_S M k : k ∈ N -> Ustage M (succ k) == VNlim_compl (Ustage M k ∪ repls (Ustage M k)).
unfold Ustage; apply natrec_S; auto.
Qed.


(*Lemma isWf_Ustage M k : isWf M -> k ∈ N -> isWf (Ustage M k).
intros wfM tyk.
elim tyk using N_ind; intros.
  *)
  
(* Uses wf axiom *)
Lemma VNlim_Ustage M k : k ∈ N -> isVNlim (Ustage M k).
intros tyk.
elim tyk using N_ind; intros.
+rewrite <-H0; trivial.
+rewrite Ustage_0.
 apply VNlim_compl_ok; trivial.
 apply wfax.
+rewrite Ustage_S; trivial.
 apply VNlim_compl_ok.  
 apply wfax.
Qed.

Hint Resolve VNlim_Ustage : core.

Lemma Ustage_mono M k k' : k ∈ N -> k' ∈ N -> k <= k' -> Ustage M k ⊆ Ustage M k'.
intros.
elim H1 using Nle_ind; intros; trivial.
*do 2 red; intros.
rewrite H2; reflexivity.
*reflexivity.
*rewrite H3, Ustage_S; trivial.
 transitivity (Ustage M n ∪ repls (Ustage M n)).
 +intro; apply union2_intro1.
 +apply VNlim_ext.
  apply wfax.
Qed.

(*
Lemma Ustage_mono_base M M' k :
  k ∈ N -> VNlim_compl M ∈ M' -> Ustage M k ∈ Ustage M' k.
intros tyk; revert M M'; elim tyk using N_ind.
*admit.
*intros.
 rewrite !Ustage_0.  
 apply VNlim_ext; trivial.
*intros.
 do 2 (rewrite Ustage_S; [|trivial]).
 specialize H0 with (1:=H1).
 
 ; trivial.
 *)

Definition U' M := sup N (Ustage M).
 
  Lemma U'_def M z : z ∈ U' M <-> exists k, k∈N /\ z ∈ Ustage M k.
unfold U'.
rewrite sup_ax.
*rewrite ex_ex2; reflexivity.
*do 2 red; intros.
 rewrite H0; reflexivity.
Qed.

  Lemma U'_ext M : isWf M -> M ⊆ U' M.
intros wfM z tyz.
rewrite U'_def.
exists zero;split;[apply zero_typ|].
rewrite Ustage_0.
apply VNlim_ext; trivial.
Qed.

Lemma U'_VNlim M : isVNlim (U' M).
unfold U'.
apply VNlim_sup.
*do 2 red; intros.
 rewrite H0; reflexivity.
*intros.
 apply VNlim_Ustage; trivial.
*intros.
 fold (Ustage M (succ k)).
 fold (Ustage M k).
 apply Ustage_mono; auto using succ_typ.
 apply succ_intro2; apply succ_intro1; reflexivity.
Qed.

(*
Lemma U'_func M : (exists A, A ∈ U' M) -> N ∈ U' M. 
intros (A,wit).
*)

Lemma Ustage_List M l :
  (exists A, A ∈ U' M) ->
  l ∈ List (U' M) ->
  exists2 k, k ∈ N & l∈Ustage M k /\ l ∈ List (Ustage M k).
intros (A,wit) tyl.
rewrite U'_def in wit.
destruct wit as (k0 & tyk0 & wit).
destruct (VNlim_Ustage M k0) as (o & lo & Ust_eq); [trivial|].
elim tyl using List_ind; intros.
*intros ?? h; apply ex2_morph; intro k; try rewrite h; reflexivity.
*exists k0; [trivial|].
 split; [|apply Nil_typ].
 rewrite Ust_eq in wit|-*.
 apply VN_incl with A; auto.
*destruct H1 as (k,tyk,(Ul',tyl')).
 rewrite U'_def in H.
 destruct H as (k',(tyk',tyx)).
 exists (max k k'); [apply max_typ; trivial|].
 split.
 **destruct (VNlim_Ustage M (max k k')) as (ok & lok & Ustk_eq); [auto|].
   rewrite Ustk_eq.
   apply VNlim_couple;[trivial|revert tyx |revert Ul'];
     rewrite <-Ustk_eq; apply Ustage_mono; auto.
 **apply Cons_typ;[revert tyx|revert tyl';apply List_mono]; apply Ustage_mono; auto.
Qed. 
(*  
  Lemma U'_List M : (exists A, A ∈ U' M) -> List (U' M) ⊆ U' M. 
intros (A,nonmt) l tyl.
destruct (U'_VNlim M) as (o,(lo,Ueq)).
rewrite Ueq in nonmt,tyl|-*.
clear Ueq.
elim tyl using List_ind.
*intros ?? h; rewrite h; reflexivity.
*apply VN_incl with A; auto.
*intros x l' tyx tyl' Hrec.
 Transparent couple.
 apply VNlim_pair; [trivial| |]; (apply VNlim_pair; [trivial| |]); trivial.
Qed.
*)

Lemma U'_repl_raw M I Rf l :
  I ∈ U' M -> l ∈ List (U' M) ->
  fo_form Rf ->
  let R x y := Rf (*(fun _=>True)*) (icons x (icons y (fun k => Fint_var l (nat2set k)))) in
  (forall x y , x ∈ I -> R x y -> y ∈ U' M) -> 
  (forall x y y', x ∈ I -> R x y -> R x y' -> y==y') ->
  repl I R ∈ U' M.
intros tyI tyl foR R Rty Runiq.
destruct (U'_VNlim M) as (o,(limo,Udef)).
assert (oo:isOrd o) by apply limo.
destruct fo_form_ex with (1:=foR) as (P,(Pty,Pdef)).
destruct Ustage_List with (2:=tyl) as (k',tyk',(Ul,tyl')); [eauto|].
 clear tyl.
 rewrite U'_def in tyI|-*.
 destruct tyI as (k&tyk&tyI).
 assert (tyI' : I ∈ Ustage M (max k k')).
 {revert tyI; apply Ustage_mono; auto. }
 assert (tyl : l ∈ List (Ustage M (max k k'))).
 {revert tyl'; apply List_mono; apply Ustage_mono; auto. } 
 clear tyl'.
 exists (succ (max k k')); split; [auto using succ_typ,max_typ|].
 rewrite Ustage_S; auto.
 apply VNlim_ext; [apply wfax|].
 apply union2_intro2.
 unfold repls.
 rewrite sup_ax.
 2:{do 2 red; intros.
    apply sup_morph; [reflexivity|red; intros].
    apply replf_morph; [reflexivity|red; intros].
    apply cond_set_morph2.
    *apply fa_morph; intros x2.
     apply fa_morph; intros y.
     apply fa_morph; intros y'.
     rewrite H0,H2,H4; reflexivity.
    *intros uniq.
     apply repl_morph;[trivial| |].
     +intros.
      rewrite H6,H7,H4,H2; reflexivity.
     +intros.
      apply uniq with x2; trivial. }
 exists I; [trivial|].
 rewrite sup_ax.
 2:{do 2 red; intros.
    apply replf_morph; [reflexivity|red; intros].
    apply cond_set_morph2.
    *apply fa_morph; intros x2.
     apply fa_morph; intros y.
     apply fa_morph; intros y'.
     rewrite H0,H2; reflexivity.
    *intros uniq.
     apply repl_morph;[reflexivity| |].
     +intros.
      rewrite H5,H4,H2,H0; reflexivity.
     +intros.
      apply uniq with x1; trivial. }
 exists P; [trivial|].
 rewrite replf_ax.
 2:{do 2 red; intros.
    apply cond_set_morph2.
    *apply fa_morph; intros x2.
     apply fa_morph; intros y.
     apply fa_morph; intros y'.
     rewrite H0; reflexivity.
    *intros uniq.
     apply repl_morph;[reflexivity| |].
     +intros.
      rewrite H3,H2,H0; reflexivity.
     +intros.
      apply uniq with x0; trivial. }
 exists l; [trivial|]. 
 rewrite cond_set_ok.
 +apply repl_morph; [reflexivity| |auto].
  intros.
  apply Pdef.
  destruct k0 as [|[|i]]; simpl.
  ++rewrite Fiv_0; symmetry; trivial.
  ++rewrite Fiv_S with (k:=0); simpl.
    rewrite Fiv_0; symmetry; trivial.
  ++rewrite Fiv_S with (k:=S i); simpl.
    rewrite Fiv_S; reflexivity.
 +intros.
  apply Runiq with x; trivial.  
  **unfold R; rewrite Pdef with (l:=Cons x (Cons y l)); trivial.
    destruct k0 as [|[|i]]; simpl.
    ++rewrite Fiv_0; reflexivity.
    ++rewrite Fiv_S with (k:=0); simpl.
      rewrite Fiv_0; reflexivity.
    ++rewrite Fiv_S with (k:=S i); simpl.
      rewrite Fiv_S; reflexivity.
  **unfold R; rewrite Pdef with (l:=Cons x (Cons y' l)); trivial.
    destruct k0 as [|[|i]]; simpl.
    ++rewrite Fiv_0; reflexivity.
    ++rewrite Fiv_S with (k:=0); simpl.
      rewrite Fiv_0; reflexivity.
    ++rewrite Fiv_S with (k:=S i); simpl.
      rewrite Fiv_S; reflexivity.
Qed.

  Lemma U'_repl_ex M I Rf l :
  I ∈ U' M -> l ∈ List (U' M) ->
  fo_form Rf ->
  let R x y := Rf (*(fun _=>True)*) (icons x (icons y (fun k => Fint_var l (nat2set k)))) in
  (forall x y , x ∈ I -> R x y -> y ∈ U' M) -> 
  (forall x y y', x ∈ I -> R x y -> R x y' -> y==y') ->
  exists b, b∈U' M /\ forall z, z ∈ b <-> exists x, x ∈ I /\ R x z.
intros tyI tyl foR R Rty Runiq.
exists (repl I R); split.
*apply U'_repl_raw; trivial.
*intros.
 rewrite repl_ax.
 +rewrite ex_ex2.
  reflexivity.
 +intros.
  assert (Rm : Proper (eq_set==>eq_set==>iff) R).
  {unfold R; do 3 red; intros.
   apply fo_form_param with (1:=foR); red; [intros].
   destruct a as [|[|?]]; simpl; trivial.
   reflexivity. }
  revert H2; apply iff_impl; apply Rm; trivial.
 +intros.
  apply Runiq with x; trivial.
Qed.

Lemma U'_repl M I R :
  I ∈ U' M -> 
  (forall x y , x ∈ I -> R x y -> y ∈ U' M) -> 
  (forall x y y', x ∈ I -> R x y -> R x y' -> y==y') ->
  (exists Rfo l, fo_form Rfo /\ l ∈ List (U' M) /\
                   let vs := fun k => Fint_var l (nat2set k) in
                   forall x y, x ∈ I ->
                                R x y <-> Rfo (icons x (icons y vs))) ->
  repl I R ∈ U' M.
intros tyI U_R Runiq (A & vs & foR & tyl & eqR).
set (R' :=fun x y=>A(icons x (icons y (fun k=>Fint_var vs (nat2set k))))).
assert (R'uniq : forall x y y', x ∈ I -> R' x y -> R' x y' -> y==y').
{unfold R'; intros.
 rewrite <- eqR in H0,H1; trivial.
 eauto. }
apply in_reg with (repl I (fun x y=>A(icons x (icons y (fun k=>Fint_var vs (nat2set k)))))).
*apply repl_morph; [reflexivity| |trivial]. 
 intros; transitivity (R' x' y').
 +apply fo_form_param with (1:=foR); intros [|[|k]]; simpl; trivial.
  reflexivity.
 +symmetry; apply eqR.
  rewrite <-H0; trivial.
*apply U'_repl_raw; trivial.
 intros.
 rewrite <-eqR in H0; eauto.
Qed.

End OneUniv.


(********************)

Module UnivHierarchy.

Definition mrepls B Mi :=
  sup Mi (fun I => sup Form (fun Rf => replf (List B) (fun vs =>
     cond_set ((forall x y y', x ∈ I -> Fint (Cons x (Cons y vs)) Rf -> 
                               Fint (Cons x (Cons y' vs)) Rf -> y==y') /\
                 (forall x y, x ∈ I -> Fint (Cons x (Cons y vs)) Rf -> y ∈ Mi))
       (repl I (fun x y => Fint (Cons x (Cons y vs)) Rf))))).

Instance mrepls_morph : morph2 mrepls.
Admitted.

(* Building a hierarchy of universes *)
  Section S.
    Variable M0:set.

(* We start with a sequence of Zermelo univs *)
Definition Uinit := natrec (VNlim_compl M0) (fun _ Mi => VNlim_compl (singl Mi)).
Definition Ubase := sup N Uinit.

Instance Uinit_auxm : morph2 (fun _ Mi => VNlim_compl (singl Mi)).
do 3 red; intros.
rewrite H0; reflexivity.
Qed.
    
Instance Uinit_morph : morph1 Uinit.
Admitted.

Definition Unext M :=
  let B := sup N M in
  natrec (VNlim_compl (B ∪ mrepls B (M zero)))
    (fun k Mi => VNlim_compl (singl Mi ∪ M (succ k) ∪ mrepls B (M (succ k)))).

Instance unext_auxm M :
  morph1 M ->
  morph2 (fun k Mi => VNlim_compl ((singl Mi ∪ M (succ k)) ∪ mrepls (sup N M) (M (succ k)))).
Admitted.
Hint Resolve unext_auxm : core.

Instance Unext_morph : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) Unext.
Admitted.


    
(* B limit VN-universe*)
Definition Ustage :=
  natrec (cc_lam N Uinit) (fun _ Mi => cc_lam N (Unext (cc_app Mi))).

Instance mstage_auxm M : ext_fun N M ->
                       morph2 (fun k Mi => VNlim_compl (Mi ∪ mrepls (sup N M) (M (succ k)))).
Admitted.
(*(fun k Mi => VNlim_compl (Mi ∪ mrepls B Mi)).
do 3 red; intros.
rewrite H0; reflexivity.
Qed.
*)
Hint Resolve mstage_auxm : core.

Instance Ustage_morph : morph1 Ustage.
Admitted.
(*do 3 red; intros.
apply natrec_morph; trivial.
*rewrite H; reflexivity.
*apply repls_auxm.
Qed.*)

Lemma Ustage_0 j : j ∈ N -> cc_app (Ustage zero) j == Uinit j.
intros; unfold Ustage; rewrite natrec_0, cc_beta_eq; auto with *.
Qed.
Lemma Ustage_S k j : k ∈ N -> j ∈ N ->
                     cc_app (Ustage (succ k)) j == Unext (cc_app (Ustage k)) j.
intros; unfold Ustage; rewrite natrec_S,cc_beta_eq; auto.
*reflexivity.
*intros ??? h; apply Unext_morph;[apply cc_app_morph;reflexivity|trivial].
*do 3 red; intros.
 apply cc_lam_ext; [reflexivity|red; intros].
 apply Unext_morph; trivial.
 apply cc_app_morph; trivial.
Qed.
(*Lemma Ustage_0 : Ustage zero == cc_lam N Uinit.
unfold Ustage; apply natrec_0.
Qed.
Lemma Ustage_S k : k ∈ N -> Ustage (succ k) == cc_lam N (Unext (cc_app (Ustage k))).
unfold Ustage; apply natrec_S; auto.
do 3 red; intros.
apply cc_lam_ext; [reflexivity|red; intros].
apply Unext_morph; trivial.
apply cc_app_morph; trivial.
Qed.*)

Lemma VNlim_Ustage k j : k ∈ N -> j ∈ N -> isVNlim (cc_app (Ustage k) j).
intros tyk tyj.
revert j tyj; elim tyk using N_ind; intros.
*rewrite <-H0; auto.
*rewrite Ustage_0;[|trivial].
 elim tyj using N_ind; intros.
 +rewrite <-H0; trivial.
 +unfold Uinit; rewrite natrec_0.
  apply VNlim_compl_ok.  
  apply wfax.
 +unfold Uinit; rewrite natrec_S; auto with *.
  apply VNlim_compl_ok.  
  apply wfax.
*rewrite Ustage_S; trivial.
 elim tyj using N_ind; intros.
 +revert H3; apply isVNlim_morph; apply Unext_morph; [|symmetry;trivial].
  apply cc_app_morph; reflexivity.
 +unfold Unext; rewrite natrec_0.
  apply VNlim_compl_ok.  
  apply wfax.
 +unfold Unext; rewrite natrec_S; trivial.
  2:apply unext_auxm; auto with *.
  apply VNlim_compl_ok.  
  apply wfax.
Qed.
(*
 Lemma VNlim_Ustage M k : k ∈ N -> isVNlim (Ustage M k).
intros.
elim H using N_ind; intros.
+rewrite <-H1; trivial.
+rewrite Ustage_0.
 apply VNlim_compl_ok.  
+rewrite Ustage_S; trivial.
 apply VNlim_compl_ok.  
Qed.
*)
Hint Resolve VNlim_Ustage : core.

(*
Lemma Ustage_mono_base M M' k :
  k ∈ N -> VNlim_compl M ∈ M' -> Ustage M k ∈ Ustage M' k.
intros tyk; revert M M'; elim tyk using N_ind.
*admit.
*intros.
 rewrite !Ustage_0.  
 apply VNlim_ext; trivial.
*intros.
 do 2 (rewrite Ustage_S; [|trivial]).
 specialize H0 with (1:=H1).
 
 ; trivial.
 *)

Definition Uj j := sup N (fun k => cc_app (Ustage k) j).

Instance Uj_morph : morph1 Uj.
Admitted.

Lemma Uj_def j z : z ∈ Uj j <-> exists k, k∈N /\ z ∈ cc_app (Ustage k) j.
unfold Uj.
rewrite sup_ax.
*rewrite ex_ex2; reflexivity.
*do 2 red; intros.
 rewrite H0; reflexivity.
Qed.

Definition U := sup N Uj.
 
Lemma U_def z : z ∈ U <-> exists j, j∈N /\ z ∈ Uj j.
unfold U.
rewrite sup_ax.
*rewrite ex_ex2; reflexivity.
*do 2 red; intros.
 rewrite H0; reflexivity.
Qed.

  Lemma U_ext : M0 ⊆ U.
intros z tyz.
rewrite U_def.
exists zero;split;[apply zero_typ|].
rewrite Uj_def.
exists zero;split;[apply zero_typ|].
rewrite Ustage_0; [|apply zero_typ].
unfold Uinit; rewrite natrec_0.
apply VNlim_ext; trivial.
apply wfax.
Qed.

Lemma Unext_in M j : morph1 M -> j ∈ N -> Unext M j ∈ Unext M (succ j).
intros Mm tyj.
unfold Unext at 2; rewrite natrec_S; auto with *.
fold (Unext M).
apply VNlim_ext; [apply wfax|].
apply union2_intro1.
apply union2_intro1.
apply singl_intro.
Qed.

Lemma Unext_ext M j : morph1 M -> j ∈ N -> Unext M j ⊆ Unext M (succ j).
intros Mm tyj z tyz.
assert (isVNlim (Unext M (succ j))).
{unfold Unext; rewrite natrec_S; auto with *.
 apply VNlim_compl_ok.
 apply wfax. }
destruct H as (o,(lo,e)).
rewrite e; apply VN_trans with (2:=tyz).
rewrite <-e; apply Unext_in; trivial.
Qed.


Lemma Urow_in k j : k ∈ N -> j ∈ N -> cc_app (Ustage k) j ∈ cc_app (Ustage k) (succ j).
intros tyk tyj.
elim tyk using N_ind; intros.
*rewrite <- H0; trivial.
*rewrite !Ustage_0; auto using succ_typ.
 unfold Uinit; rewrite natrec_S; auto with *.
 apply VNlim_ext; [apply wfax|].
 apply singl_intro.
*rewrite !Ustage_S; auto using succ_typ.
 apply Unext_in; auto with *.
Qed.

Lemma Urow_ext k j : k ∈ N -> j ∈ N -> cc_app (Ustage k) j ⊆ cc_app (Ustage k) (succ j).
red; intros.
destruct VNlim_Ustage with (1:=H)(2:=succ_typ _ H0) as (o,(lo,e)).
rewrite e; apply VN_trans with (2:=H1).
rewrite <-e; apply Urow_in; trivial.
Qed.


Lemma Unext_ext_sup M j : morph1 M -> j ∈ N -> sup N M ⊆ Unext M j.
intros Mm tyj.
elim tyj using N_ind; intros.
*revert H1; apply iff_impl; apply incl_set_morph; [apply sup_morph; [|red]; auto with *|].
 apply natrec_morph;[reflexivity| |trivial].
 do 2 red; intros.
 apply mstage_auxm; auto with *.
 rewrite H1,H2; reflexivity.
*unfold Unext; rewrite natrec_0.
 eapply transitivity; [|apply VNlim_ext;apply wfax].
 intro;apply union2_intro1.
*rewrite H0.
apply Unext_ext; trivial.
Qed.
Lemma Unext_repl M j : morph1 M -> j ∈ N -> mrepls (sup N M) (M j) ⊆ Unext M j.
intros Mm tyj.
elim tyj using N_ind; intros.
*rewrite <-H0; trivial.
*unfold Unext; rewrite natrec_0.
 eapply transitivity; [|apply VNlim_ext; apply wfax].
 intro;apply union2_intro2.
*unfold Unext; rewrite natrec_S; auto.
 eapply transitivity; [|apply VNlim_ext; apply wfax].
 intro; apply union2_intro2.
Qed.

Lemma Ustage_mono k k' j : j ∈ N -> k ∈ N -> k' ∈ N -> k <= k' ->
                           cc_app (Ustage k) j ⊆ cc_app (Ustage k') j.
intros.
elim H2 using Nle_ind; intros; trivial.
*do 2 red; intros.
 rewrite H3; reflexivity.
*reflexivity.
*rewrite H4, Ustage_S; trivial.
 rewrite <- Unext_ext_sup; auto with *.
 apply sup_incl; auto with *.
 intros ??? h; rewrite h; reflexivity.
Qed.


Lemma Uj_VNlim j : j ∈ N -> isVNlim (Uj j).
unfold U.
intros.
apply VNlim_sup.
*do 2 red; intros.
 rewrite H1; reflexivity.
*intros.
 apply VNlim_Ustage; trivial.
*intros.
 rewrite Ustage_S; trivial.
 rewrite <- Unext_ext_sup;[|apply cc_app_morph;reflexivity|trivial].
 apply sup_incl; [|trivial].
 intros ??? h; apply cc_app_morph; auto with *.
Qed.

Lemma U_VNlim : isVNlim U.
apply VNlim_sup.
*auto with *.
*intros.
 apply Uj_VNlim; trivial.
*unfold Uj.
 intros j tyj z.
 rewrite !sup_ax.
 +intros (k,tyk,tyz); exists k; [trivial|].
  apply Urow_ext; trivial.
 +intros ??? h; rewrite h; reflexivity.
 +intros ??? h; rewrite h; reflexivity.
Qed.  

Lemma Ustage_List l :
  (exists A, A ∈ U) ->
  l ∈ List U ->
  exists2 k, k ∈ N & l∈sup N (cc_app(Ustage k)) /\ l ∈ List (sup N (cc_app(Ustage k))).
Admitted.
(*intros (A,wit) tyl.
rewrite U'_def in wit.
destruct wit as (k0 & tyk0 & wit).
destruct (VNlim_Ustage M k0) as (o & lo & Ust_eq); [trivial|].
elim tyl using List_ind; intros.
*intros ?? h; apply ex2_morph; intro k; try rewrite h; reflexivity.
*exists k0; [trivial|].
 split; [|apply Nil_typ].
 rewrite Ust_eq in wit|-*.
 apply VN_incl with A; auto.
*destruct H1 as (k,tyk,(Ul',tyl')).
 rewrite U'_def in H.
 destruct H as (k',(tyk',tyx)).
 exists (max k k'); [apply max_typ; trivial|].
 split.
 **destruct (VNlim_Ustage M (max k k')) as (ok & lok & Ustk_eq); [auto|].
   rewrite Ustk_eq.
   apply VNlim_couple;[trivial|revert tyx |revert Ul'];
     rewrite <-Ustk_eq; apply Ustage_mono; auto.
 **apply Cons_typ;[revert tyx|revert tyl';apply List_mono]; apply Ustage_mono; auto.
Qed. 
*)

(******* Not working....
Lemma Uj_repl_raw I Rf l j :
  j ∈ N ->
  I ∈ Uj j -> l ∈ List U ->
  fo_form Rf ->
  let R x y := Rf (icons x (icons y (fun k => Fint_var l (nat2set k)))) in
  (forall x y , x ∈ I -> R x y -> y ∈ Uj j) -> 
  (forall x y y', x ∈ I -> R x y -> R x y' -> y==y') ->
  repl I R ∈ Uj j.
intros tyj tyI tyl foR R Rty Runiq.
destruct Uj_VNlim with (1:=tyj) as (o,(limo,Udef)).
assert (oo:isOrd o) by apply limo.
destruct fo_form_ex with (1:=foR) as (P,(Pty,Pdef)).
destruct Ustage_List with (2:=tyl) as (k',tyk',(Ul,tyl'));
  [exists I; rewrite U_def; exists j; auto|].
clear tyl.
rewrite Uj_def in tyI|-*.
destruct tyI as (k&tyk&tyI).
assert (tyI' : I ∈ cc_app (Ustage (max k k')) j).
{revert tyI; apply Ustage_mono; auto. }
(* assert (tyl : l ∈ List (Ustage M (max k k'))).
   {revert tyl'; apply List_mono; apply Ustage_mono; auto. } 
 clear tyl'. *)
exists (succ (max k k')); split; [auto using succ_typ,max_typ|].
rewrite Ustage_S; auto.
 apply VNlim_ext.
 apply union2_intro2.

 unfold repls.
 rewrite sup_ax.
 2:{do 2 red; intros.
    apply sup_morph; [reflexivity|red; intros].
    apply replf_morph; [reflexivity|red; intros].
    apply cond_set_morph2.
    *apply fa_morph; intros x2.
     apply fa_morph; intros y.
     apply fa_morph; intros y'.
     rewrite H0,H2,H4; reflexivity.
    *intros uniq.
     apply repl_morph;[trivial| |].
     +intros.
      rewrite H6,H7,H4,H2; reflexivity.
     +intros.
      apply uniq with x2; trivial. }
 exists I; [trivial|].
 rewrite sup_ax.
 2:{do 2 red; intros.
    apply replf_morph; [reflexivity|red; intros].
    apply cond_set_morph2.
    *apply fa_morph; intros x2.
     apply fa_morph; intros y.
     apply fa_morph; intros y'.
     rewrite H0,H2; reflexivity.
    *intros uniq.
     apply repl_morph;[reflexivity| |].
     +intros.
      rewrite H5,H4,H2,H0; reflexivity.
     +intros.
      apply uniq with x1; trivial. }
 exists P; [trivial|].
 rewrite replf_ax.
 2:{do 2 red; intros.
    apply cond_set_morph2.
    *apply fa_morph; intros x2.
     apply fa_morph; intros y.
     apply fa_morph; intros y'.
     rewrite H0; reflexivity.
    *intros uniq.
     apply repl_morph;[reflexivity| |].
     +intros.
      rewrite H3,H2,H0; reflexivity.
     +intros.
      apply uniq with x0; trivial. }
 exists l; [trivial|]. 
 rewrite cond_set_ok.
 +apply repl_morph; [reflexivity| |auto].
  intros.
  apply Pdef.
  destruct k0 as [|[|i]]; simpl.
  ++rewrite Fiv_0; symmetry; trivial.
  ++rewrite Fiv_S with (k:=0); simpl.
    rewrite Fiv_0; symmetry; trivial.
  ++rewrite Fiv_S with (k:=S i); simpl.
    rewrite Fiv_S; reflexivity.
 +intros.
  apply Runiq with x; trivial.  
  **unfold R; rewrite Pdef with (l:=Cons x (Cons y l)); trivial.
    destruct k0 as [|[|i]]; simpl.
    ++rewrite Fiv_0; reflexivity.
    ++rewrite Fiv_S with (k:=0); simpl.
      rewrite Fiv_0; reflexivity.
    ++rewrite Fiv_S with (k:=S i); simpl.
      rewrite Fiv_S; reflexivity.
  **unfold R; rewrite Pdef with (l:=Cons x (Cons y' l)); trivial.
    destruct k0 as [|[|i]]; simpl.
    ++rewrite Fiv_0; reflexivity.
    ++rewrite Fiv_S with (k:=0); simpl.
      rewrite Fiv_0; reflexivity.
    ++rewrite Fiv_S with (k:=S i); simpl.
      rewrite Fiv_S; reflexivity.
Qed.


Lemma U_repl_raw I Rf l :
  I ∈ U -> l ∈ List U ->
  fo_form Rf ->
  let R x y := Rf (icons x (icons y (fun k => Fint_var l (nat2set k)))) in
  (forall x y , x ∈ I -> R x y -> y ∈ U) -> 
  (forall x y y', x ∈ I -> R x y -> R x y' -> y==y') ->
  repl I R ∈ U.
intros tyI tyl foR R Rty Runiq.
destruct U_VNlim as (o,(limo,Udef)).
assert (oo:isOrd o) by apply limo.
destruct fo_form_ex with (1:=foR) as (P,(Pty,Pdef)).
destruct Ustage_List with (2:=tyl) as (k',tyk',(Ul,tyl')); [eauto|].
 clear tyl.
 rewrite U_def in tyI|-*.
 destruct tyI as (k&tyk&tyI).
 assert (tyI' : I ∈ Ustage M (max k k')).
 {revert tyI; apply Ustage_mono; auto. }
 assert (tyl : l ∈ List (Ustage M (max k k'))).
 {revert tyl'; apply List_mono; apply Ustage_mono; auto. } 
 clear tyl'.
 exists (succ (max k k')); split; [auto using succ_typ,max_typ|].
 rewrite Ustage_S; auto.
 apply VNlim_ext.
 apply union2_intro2.

 unfold repls.
 rewrite sup_ax.
 2:{do 2 red; intros.
    apply sup_morph; [reflexivity|red; intros].
    apply replf_morph; [reflexivity|red; intros].
    apply cond_set_morph2.
    *apply fa_morph; intros x2.
     apply fa_morph; intros y.
     apply fa_morph; intros y'.
     rewrite H0,H2,H4; reflexivity.
    *intros uniq.
     apply repl_morph;[trivial| |].
     +intros.
      rewrite H6,H7,H4,H2; reflexivity.
     +intros.
      apply uniq with x2; trivial. }
 exists I; [trivial|].
 rewrite sup_ax.
 2:{do 2 red; intros.
    apply replf_morph; [reflexivity|red; intros].
    apply cond_set_morph2.
    *apply fa_morph; intros x2.
     apply fa_morph; intros y.
     apply fa_morph; intros y'.
     rewrite H0,H2; reflexivity.
    *intros uniq.
     apply repl_morph;[reflexivity| |].
     +intros.
      rewrite H5,H4,H2,H0; reflexivity.
     +intros.
      apply uniq with x1; trivial. }
 exists P; [trivial|].
 rewrite replf_ax.
 2:{do 2 red; intros.
    apply cond_set_morph2.
    *apply fa_morph; intros x2.
     apply fa_morph; intros y.
     apply fa_morph; intros y'.
     rewrite H0; reflexivity.
    *intros uniq.
     apply repl_morph;[reflexivity| |].
     +intros.
      rewrite H3,H2,H0; reflexivity.
     +intros.
      apply uniq with x0; trivial. }
 exists l; [trivial|]. 
 rewrite cond_set_ok.
 +apply repl_morph; [reflexivity| |auto].
  intros.
  apply Pdef.
  destruct k0 as [|[|i]]; simpl.
  ++rewrite Fiv_0; symmetry; trivial.
  ++rewrite Fiv_S with (k:=0); simpl.
    rewrite Fiv_0; symmetry; trivial.
  ++rewrite Fiv_S with (k:=S i); simpl.
    rewrite Fiv_S; reflexivity.
 +intros.
  apply Runiq with x; trivial.  
  **unfold R; rewrite Pdef with (l:=Cons x (Cons y l)); trivial.
    destruct k0 as [|[|i]]; simpl.
    ++rewrite Fiv_0; reflexivity.
    ++rewrite Fiv_S with (k:=0); simpl.
      rewrite Fiv_0; reflexivity.
    ++rewrite Fiv_S with (k:=S i); simpl.
      rewrite Fiv_S; reflexivity.
  **unfold R; rewrite Pdef with (l:=Cons x (Cons y' l)); trivial.
    destruct k0 as [|[|i]]; simpl.
    ++rewrite Fiv_0; reflexivity.
    ++rewrite Fiv_S with (k:=0); simpl.
      rewrite Fiv_0; reflexivity.
    ++rewrite Fiv_S with (k:=S i); simpl.
      rewrite Fiv_S; reflexivity.
Qed.

  Lemma U'_repl_ex M I Rf l :
  I ∈ U' M -> l ∈ List (U' M) ->
  fo_form Rf ->
  let R x y := Rf (*(fun _=>True)*) (icons x (icons y (fun k => Fint_var l (nat2set k)))) in
  (forall x y , x ∈ I -> R x y -> y ∈ U' M) -> 
  (forall x y y', x ∈ I -> R x y -> R x y' -> y==y') ->
  exists b, b∈U' M /\ forall z, z ∈ b <-> exists x, x ∈ I /\ R x z.
intros tyI tyl foR R Rty Runiq.
exists (repl I R); split.
*apply U'_repl_raw; trivial.
*intros.
 rewrite repl_ax.
 +rewrite ex_ex2.
  reflexivity.
 +intros.
  assert (Rm : Proper (eq_set==>eq_set==>iff) R).
  {unfold R; do 3 red; intros.
   apply fo_form_param with (1:=foR); red; [intros].
   destruct a as [|[|?]]; simpl; trivial.
   reflexivity. }
  revert H2; apply iff_impl; apply Rm; trivial.
 +intros.
  apply Runiq with x; trivial.
Qed.

Lemma U'_repl M I R :
  I ∈ U' M -> 
  (forall x y , x ∈ I -> R x y -> y ∈ U' M) -> 
  (forall x y y', x ∈ I -> R x y -> R x y' -> y==y') ->
  (exists Rfo l, fo_form Rfo /\ l ∈ List (U' M) /\
                   let vs := fun k => Fint_var l (nat2set k) in
                   forall x y, x ∈ I ->
                                R x y <-> Rfo (icons x (icons y vs))) ->
  repl I R ∈ U' M.
intros tyI U_R Runiq (A & vs & foR & tyl & eqR).
set (R' :=fun x y=>A(icons x (icons y (fun k=>Fint_var vs (nat2set k))))).
assert (R'uniq : forall x y y', x ∈ I -> R' x y -> R' x y' -> y==y').
{unfold R'; intros.
 rewrite <- eqR in H0,H1; trivial.
 eauto. }
apply in_reg with (repl I (fun x y=>A(icons x (icons y (fun k=>Fint_var vs (nat2set k)))))).
*apply repl_morph; [reflexivity| |trivial]. 
 intros; transitivity (R' x' y').
 +apply fo_form_param with (1:=foR); intros [|[|k]]; simpl; trivial.
  reflexivity.
 +symmetry; apply eqR.
  rewrite <-H0; trivial.
*apply U'_repl_raw; trivial.
 intros.
 rewrite <-eqR in H0; eauto.
Qed.
*)

End S.
End UnivHierarchy.
 

(**)

Opaque WFR.
Opaque Fint.
Opaque N.

Lemma fo_U' A :
  fo_in A ->
  fo_in (fun i => OneUniv.U' (A i)).
intros foA.
unfold OneUniv.U', w_iter.
repeat fo_set; [apply fo_N|apply fo_in_eq].
apply fo_natrec;[| |fo_trivial].
*apply fo_VNlim_compl.
 apply fo_form_ren with (1:=foA)(f:=lft S).
*apply fo_VNlim_compl.
 repeat fo_set; try fo_trivial.
 apply fo_in_eq; repeat fo_set; [apply fo_N|].
 apply fo_in_eq; repeat fo_set; [apply fo_List; fo_trivial|].
 apply fo_in_eq; apply fo_repl_cond;[fo_trivial|].
 apply fo_Fint;[|fo_trivial].
 apply fo_couple;[fo_trivial|].
 apply fo_couple;fo_trivial.
Qed.
  

Require Import ModelCC.

Import BuildModel T J R.

Module FO.

  (* Interpretation *)

Definition fo_int (t:term) :=
  fo_in (int t).


Lemma int_ref n : fo_int (Ref n).
do 2 red; simpl.
atom.
Qed.

Lemma int_props : fo_int prop.
red.
simpl.  
apply fo_power.
apply fo_pair; apply fo_empty.
Qed.

Lemma int_app M N :
  fo_int M ->
  fo_int N ->
  fo_int (App M N).
intros foM foN.
red; simpl.
unfold int; simpl.
apply fo_cc_app; trivial.
Qed.

Lemma int_abs M N :
  fo_int M ->
  fo_int N ->
  fo_int (Abs M N).
intros foM foN.
red; simpl.
unfold int; simpl.
apply fo_cc_lam; trivial.
unfold bind; simpl.
red in foN.
apply FO_ext with (2:=foN); intros vs.
apply in_set_morph; [reflexivity|].
apply int_morph; [reflexivity|].
intros [|k]; simpl; reflexivity.
Qed.

Lemma int_prod M N :
  fo_int M ->
  fo_int N ->
  fo_int (Prod M N).
intros foM foN.
red; simpl.
unfold int; simpl.
apply fo_cc_prod; trivial.
unfold bind; simpl.
red in foN.
apply FO_ext with (2:=foN); intros vs.
apply in_set_morph; [reflexivity|].
apply int_morph; [reflexivity|].
intros [|k]; simpl; reflexivity.
Qed.


Import OneUniv. (* U' *)

Parameter ecc : nat -> set.
Parameter ecc0 : ecc 0 == U' (singl N).
Parameter eccS : forall k, ecc (S k) == U' (singl (ecc k)).
Parameter type : nat->term.
Parameter type_nk : forall k, type k <> kind.
Parameter type_def : forall k, int (type k) = fun _ => ecc k.


Lemma int_type n :
  fo_int (type n).
red; rewrite type_def.
induction n.
*eapply FO_ext with (fun i => i 0 ∈ U' (singl N)).
 {intros; rewrite ecc0; reflexivity. }
 change (fo_in (fun _ => U'(singl N))).
 apply fo_U'.
 apply fo_pair; apply fo_N.
*eapply FO_ext with (fun i => i 0 ∈ U' (singl (ecc n))).
 {intros; rewrite eccS; reflexivity. }
 change (fo_in (fun _ => U'(singl (ecc n)))).
 apply fo_U'.
 apply fo_pair; apply IHn.
Qed.

Parameter term_fo : forall T : term, fo_int T.

(*Lemma U'_replf M A F :
    ext_fun A F ->
    A ∈ U' M ->
    (forall x, x ∈ A -> F x ∈ U' M) ->
    replf A F ∈ U' M.
intros.
unfold replf.
apply U'_repl; trivial.
*intros.
 rewrite H3; auto.  
*intros.
 rewrite H3,H4. 
 apply H; auto with *.
*
fo_form (fun  *)
 Transparent cc_lam.
(*Lemma U'_cc_lam M A F :
    ext_fun A F ->
    A ∈ U' M ->
    (forall x, x ∈ A -> F x ∈ U' M) ->
    cc_lam A F ∈ U' M.
intros.
unfold cc_lam.

apply G_sup; intros; trivial.
 do 2 red; intros; apply replf_morph; auto.
 red; intros; apply couple_morph; trivial.
apply G_replf; intros; auto.
 do 2 red; intros; apply couple_morph; auto with *.

 apply G_couple; trivial.
  apply G_trans with A; trivial.

  apply G_trans with (F x); auto.
Qed.
*)

Lemma ecc_prod2 : forall n T U,
  T ∈ ecc n ->
  (forall x, x ∈ T -> U x ∈ ecc n) ->
  cc_prod T U ∈ ecc n.
Admitted.

(* TODO

Lemma typ_replf : forall e n T U,
  typ e T (type n) ->
  typ (T :: e) U (type n) ->
  forall i, val_ok e i -> replf (int T i) (fun x => int U (V.cons x i)) ∈ ecc n.
(*red; intros.
apply in_int_el.*)
simpl; intros.
(*rewrite type_def.*)
apply ecc_prod2.
*red in H; specialize H with (1:=H1).
 apply in_int_not_kind in H.
 2:apply type_nk.
 rewrite type_def in H; trivial.
*assert (fo_in (bind (fun x i=>int U (V.cons x i)))).


 Lemma typ_prod2 : forall e n T U,
  typ e T (type n) ->
  typ (T :: e) U (type n) ->
  typ e (Prod T U) (type n).
red; intros.
apply in_int_el.
simpl.
rewrite type_def.
apply ecc_prod2.
*red in H; specialize H with (1:=H1).
 apply in_int_not_kind in H.
 2:apply type_nk.
 rewrite type_def in H; trivial.
*assert (fo_in (bind (fun x i=>int U (V.cons x i)))).
 

 H.

typ e T (type n) ->
  typ (T :: e) U (type n) ->
  typ e (Prod T U) (type n).


  Lemma typ_Type : forall e n, typ e (type n) (type (S n)).
red; intros; simpl.
apply (ecc_in2 (S n)).
Qed.


Lemma typ_prod_
 

Definition typ' e M T :=
  typ e M T /\ fo_int 
*)
End FO.
