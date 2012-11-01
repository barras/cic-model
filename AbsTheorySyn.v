Require Import List.
Require Import Omega.

(******************************************************************************************)
(******************************************************************************************)
(*This file gives the syntax model of the theory*)
(******************************************************************************************)
(******************************************************************************************)



(******************************************************************************************)
(*This model describes the abstract signature of the theory,*)
(*and defines some operations on the signature*)
(******************************************************************************************)
Module Type TheorySig.

(*The set of first-order terms*)
Parameter foterm : Set.

(*Lift is the recocation of free variables*)
Parameter lift_trm_rec : foterm -> nat -> nat -> foterm.
Definition lift_trm t n := lift_trm_rec t n 0.

Axiom lift_trm0 : forall t, lift_trm t 0 = t.
Axiom lift_trm_split : forall t n k, 
  lift_trm_rec t (S n) k = lift_trm_rec (lift_trm_rec t n k) 1 k.

(*Substitute term*)
Parameter subst_trm_rec : foterm -> foterm -> nat -> foterm.
Definition subst_trm M N := subst_trm_rec M N 0.

(*Free variables are calculated due to need of definition of well-typed terms*)
(*fv_trm_rec list all free variables in a term with a binder k*)
(*The free variables are used for indexes in a context in which the term is well typed*)
(*So, the free variables are subtracted by the binder k*)
Parameter fv_trm_rec : foterm -> (*k*)nat -> list nat.
Definition fv_trm t := fv_trm_rec t 0.

Axiom in_S_fv_trm : forall t n k,
  In (S n) (fv_trm_rec t k) <->
  In n (fv_trm_rec t (S k)).

Axiom in_fv_trm_lift : forall t n k k' k'',
  In n (fv_trm_rec (lift_trm_rec t k' k'') (k+k'+k'')) <->
  In n (fv_trm_rec t (k+k'')).

Axiom in_fv_trm_subst_split : forall t n N k k',
  In n (fv_trm_rec (subst_trm_rec t N k') (k+k')) ->
  In n (fv_trm_rec N k) \/ In (S n) (fv_trm_rec t (k+k')).

Axiom in_fv_trm_subst : forall t n N k k',
  In (S n) (fv_trm_rec t (k+k')) ->
  In n (fv_trm_rec (subst_trm_rec t N k') (k+k')).

End TheorySig.


(******************************************************************************************)
(*This model defines the first-order language on top of signatures*)
(*Actually shows possible logic formulas*)
(******************************************************************************************)
Module FoLang (M : TheorySig).

Export M.

(*Fist order foformula*)
Inductive foformula :=
| eq_fotrm : foterm -> foterm -> foformula
| TF   : foformula
| BF   : foformula
| neg : foformula -> foformula
| conj : foformula -> foformula -> foformula
| disj : foformula -> foformula -> foformula
| implf : foformula -> foformula -> foformula
| fall : foformula -> foformula
| exst : foformula -> foformula.

(*Relication of the free variables of formula*)
Fixpoint lift_fml_rec f n k:=
  match f with
    | eq_fotrm x y => eq_fotrm (lift_trm_rec x n k) (lift_trm_rec y n k)
    | TF => TF
    | BF => BF
    | neg f' => neg (lift_fml_rec f' n k)
    | conj A B => conj (lift_fml_rec A n k) (lift_fml_rec B n k)
    | disj A B => disj (lift_fml_rec A n k) (lift_fml_rec B n k)
    | implf A B => implf (lift_fml_rec A n k) (lift_fml_rec B n k)
    | fall A => fall (lift_fml_rec A n (S k))
    | exst A => exst (lift_fml_rec A n (S k))
  end.

Definition lift_fml t n := lift_fml_rec t n 0.

Lemma lift_fml_split : forall f n k, 
  lift_fml_rec f (S n) k = lift_fml_rec (lift_fml_rec f n k) 1 k.
induction f; trivial; unfold lift_fml in *; simpl; intros.
 rewrite lift_trm_split with (t:=f).
 rewrite lift_trm_split with (t:=f0); trivial.

 rewrite IHf; trivial.

 rewrite IHf1, IHf2; trivial.
 
 rewrite IHf1, IHf2; trivial.

 rewrite IHf1, IHf2; trivial.

 rewrite IHf; trivial.

 rewrite IHf; trivial.
Qed.

(*Substitution of formular*)
Fixpoint subst_fml_rec f N n :=
  match f with
    | eq_fotrm x y => eq_fotrm (subst_trm_rec x N n) (subst_trm_rec y N n)
    | TF => TF
    | BF => BF
    | neg f => neg (subst_fml_rec f N n)
    | conj f1 f2 => conj (subst_fml_rec f1 N n) (subst_fml_rec f2 N n)
    | disj f1 f2 => disj (subst_fml_rec f1 N n) (subst_fml_rec f2 N n)
    | implf f1 f2 => implf (subst_fml_rec f1 N n) (subst_fml_rec f2 N n)
    | fall f => fall (subst_fml_rec f N (S n))
    | exst f => exst (subst_fml_rec f N (S n))
  end.

Definition subst_fml f N := subst_fml_rec f N 0.

(*Free variables of the formula : enjoy the same idea with the definiton on foterm*)
Fixpoint fv_fml_rec f k : list nat :=
  match f with
    | eq_fotrm t1 t2 => (fv_trm_rec t1 k) ++ (fv_trm_rec t2 k)
    | TF => nil
    | BF => nil
    | neg f0 => fv_fml_rec f0 k
    | conj f1 f2 => (fv_fml_rec f1 k) ++ (fv_fml_rec f2 k)
    | disj f1 f2 => (fv_fml_rec f1 k) ++ (fv_fml_rec f2 k)
    | implf f1 f2 => (fv_fml_rec f1 k) ++ (fv_fml_rec f2 k)
    | fall f0 => (fv_fml_rec f0 (S k))
    | exst f0 => (fv_fml_rec f0 (S k))
  end.

Definition fv_fml f := fv_fml_rec f 0.

Lemma in_S_fv_fml : forall f n k, 
  In (S n) (fv_fml_rec f k) <-> In n (fv_fml_rec f (S k)).
induction f; simpl; try reflexivity; trivial; intros; do 2 rewrite in_app_iff.
 do 2 rewrite in_S_fv_trm; reflexivity.

 rewrite IHf1, IHf2; reflexivity.

 rewrite IHf1, IHf2; reflexivity.

 rewrite IHf1, IHf2; reflexivity.
Qed.

Lemma in_fv_fml_lift : forall f n k k' k'',
  In n (fv_fml_rec (lift_fml_rec f k' k'') (k+k'+k'')) <->
  In n (fv_fml_rec f (k+k'')).
induction f; simpl; intros; try reflexivity; trivial.
 do 2 rewrite in_app_iff. do 2 rewrite in_fv_trm_lift; reflexivity.

 do 2 rewrite in_app_iff. rewrite IHf1, IHf2; reflexivity.

 do 2 rewrite in_app_iff. rewrite IHf1, IHf2; reflexivity.

 do 2 rewrite in_app_iff. rewrite IHf1, IHf2; reflexivity.

 replace (S (k + k'+ k'')) with (k + k' + S k'') by omega.
 replace (S (k + k'')) with (k + S k'') by omega. apply IHf; trivial.

 replace (S (k + k'+ k'')) with (k + k' + S k'') by omega.
 replace (S (k + k'')) with (k + S k'') by omega. apply IHf; trivial.
Qed.

Lemma in_fv_fml_subst_split : forall g n N k k',
  In n (fv_fml_rec (subst_fml_rec g N k') (k+k')) -> 
  In n (fv_trm_rec N k) \/ In (S n) (fv_fml_rec g (k+k')).
induction g; simpl; intros; try contradiction; trivial.
 rewrite in_app_iff in H |- *.
 destruct H as [H|H]; apply in_fv_trm_subst_split in H.
  destruct H; [left|right; left]; trivial.
  
  destruct H; [left|right; right]; trivial.

 apply IHg in H; trivial.
 
 rewrite in_app_iff in H |- *. destruct H as [H|H]; [apply IHg1 in H|apply IHg2 in H].
  destruct H; [left|right; left]; trivial.

  destruct H; [left|right; right]; trivial.

 rewrite in_app_iff in H |- *. destruct H as [H|H]; [apply IHg1 in H|apply IHg2 in H].
  destruct H; [left|right; left]; trivial.

  destruct H; [left|right; right]; trivial.

 rewrite in_app_iff in H |- *. destruct H as [H|H]; [apply IHg1 in H|apply IHg2 in H].
  destruct H; [left|right; left]; trivial.

  destruct H; [left|right; right]; trivial.

 replace (S (k + k')) with (k + S k') in H |- * by omega. apply IHg in H; trivial.

 replace (S (k + k')) with (k + S k') in H |- * by omega. apply IHg in H; trivial.
Qed.

Lemma in_fv_fml_subst : forall f n N k k',
  In (S n) (fv_fml_rec f (k+k')) ->
  In n (fv_fml_rec (subst_fml_rec f N k') (k+k')).
induction f; simpl; intros; trivial.
 rewrite in_app_iff in H |- *.
 destruct H; [left|right]; apply in_fv_trm_subst; trivial.

 apply IHf; trivial.

 rewrite in_app_iff in H |- *.
 destruct H; [left; apply IHf1|right; apply IHf2]; trivial.

 rewrite in_app_iff in H |- *.
 destruct H; [left; apply IHf1|right; apply IHf2]; trivial.

 rewrite in_app_iff in H |- *.
 destruct H; [left; apply IHf1|right; apply IHf2]; trivial.

 replace (S (k + k')) with (k + S k') in H |- * by omega. apply IHf; trivial.

 replace (S (k + k')) with (k + S k') in H |- * by omega. apply IHf; trivial.
Qed.

(*Context is a list of foterm or formula*)
(*In the list, None stands for foterm,*)
(*and Some formula stands for the certain formular*)
Definition HYP := list (option foformula).

(*An well-typed term is the term with all free variables typed foterm*)
Definition wf_trm (hyp : HYP) t := 
  forall n, In n (fv_trm t) -> nth_error hyp n = Some None.

(*An well-typed first order formula should contain merely free variables typed foterm*)
Definition wf_fml (hyp : HYP) f := 
  forall n, In n (fv_fml f) -> nth_error hyp n = Some None.

Lemma wf_weakening : forall hyp t f',
  wf_fml (t :: hyp) (lift_fml f' 1) ->
  wf_fml hyp f'.
intros; red in H |- *; intros. specialize H with (n:= S n).
unfold fv_fml in H, H0. rewrite in_S_fv_fml in H.
unfold lift_fml in H. replace 1 with (0+1+0) in H by omega.
rewrite in_fv_fml_lift in H. simpl in H. apply H in H0; trivial.
Qed.

End FoLang.

(******************************************************************************************)
(*Theory axioms defines how valid fomula origns*)
(******************************************************************************************)
Module Type TheoryAx (M : TheorySig).

Include FoLang M.

(*Theory Axioms*)
Parameter ax_syn : HYP -> foformula -> Prop.
Axiom ax_wf : forall hyp f, ax_syn hyp f -> wf_fml hyp f.

End TheoryAx.

(******************************************************************************************)
(*Derivition rules defines how valid fomulas can be derived from the axioms*)
(******************************************************************************************)
Module FoDeriv (M1 : TheorySig) (M2 : TheoryAx M1).

Import M1 M2.

Inductive deriv : HYP -> foformula -> Prop :=
| hyp_judge : forall f hyp n, 
  nth_error hyp n = Some (Some f) ->
  wf_fml hyp (lift_fml f (S n)) ->
  deriv hyp (lift_fml f (S n))
| ax_intro : forall f hyp, ax_syn hyp f -> deriv hyp f
| true_intro : forall hyp, deriv hyp TF
| false_elim : forall hyp f, deriv hyp BF -> wf_fml hyp f -> deriv hyp f
| neg_intro : forall hyp f, deriv hyp (implf f BF) -> deriv hyp (neg f)
| neg_elim : forall hyp f, deriv hyp (neg f) -> deriv hyp (implf f BF)
| conj_intro : forall hyp f1 f2, 
  deriv hyp f1 -> deriv hyp f2 -> deriv hyp (conj f1 f2)
| conj_elim1 : forall hyp f1 f2,
  deriv hyp (conj f1 f2) -> deriv hyp f1
| conj_elim2 : forall hyp f1 f2,
  deriv hyp (conj f1 f2) -> deriv hyp f2
| disj_intro1 : forall hyp f1 f2, 
  deriv hyp f1 -> wf_fml hyp f2 -> deriv hyp (disj f1 f2)
| disj_intro2 : forall hyp f1 f2, 
  wf_fml hyp f1 ->
  deriv hyp f2 -> deriv hyp (disj f1 f2)
| disj_elim : forall hyp f1 f2 f3,
  deriv hyp (disj f1 f2) -> deriv (Some f1::hyp) (lift_fml f3 1) -> 
  deriv (Some f2::hyp) (lift_fml f3 1) -> deriv hyp f3
| impl_intro : forall hyp f1 f2,
  wf_fml hyp f1 ->
  deriv ((Some f1)::hyp) (lift_fml f2 1) -> deriv hyp (implf f1 f2)
| impl_elim : forall hyp f1 f2,
  deriv hyp (implf f1 f2) -> deriv hyp f1 -> deriv hyp f2
| fall_intro : forall hyp f,
  deriv (None::hyp) f -> deriv hyp (fall f)
| fall_elim : forall hyp f u, 
  wf_trm hyp u -> deriv hyp (fall f) -> deriv hyp (subst_fml f u)
| exst_intro : forall hyp f N, wf_trm hyp N -> 
  deriv hyp (subst_fml f N) -> deriv hyp (exst f)
| exst_elim : forall hyp f f1, 
  deriv hyp (exst f) -> 
  deriv (Some f::None::hyp) (lift_fml f1 2) -> deriv hyp f1.

Lemma deriv_well_typed : forall hyp f, deriv hyp f -> wf_fml hyp f.
induction 1; trivial.
 apply ax_wf; trivial.

 red; simpl; intros; contradiction.

 red in IHderiv |- *. unfold fv_fml in IHderiv |- *. simpl in IHderiv |- *.
 intros; apply IHderiv. rewrite app_nil_r; trivial.

 red in IHderiv |- *. unfold fv_fml in IHderiv |- *. simpl in IHderiv |- *.
 intros; apply IHderiv. rewrite app_nil_r in H0; trivial.

 red in IHderiv1, IHderiv2 |- *. unfold fv_fml in IHderiv1, IHderiv2 |- *.
 simpl; intros. apply in_app_iff in H1. 
 destruct H1; [apply IHderiv1|apply IHderiv2]; trivial.

 red in IHderiv |- *. unfold fv_fml in IHderiv |- *. simpl in IHderiv.
 intros; apply IHderiv. rewrite in_app_iff; left; trivial.

 red in IHderiv |- *. unfold fv_fml in IHderiv |- *. simpl in IHderiv.
 intros; apply IHderiv. rewrite in_app_iff; right; trivial.

 red in IHderiv, H0 |- *. unfold fv_fml in IHderiv, H0 |- *.
 simpl; intros. apply in_app_iff in H1. 
 destruct H1; [apply IHderiv|apply H0]; trivial.

 red in IHderiv, H |- *. unfold fv_fml in IHderiv, H |- *.
 simpl; intros. apply in_app_iff in H1. 
 destruct H1; [apply H|apply IHderiv]; trivial.

 apply wf_weakening in IHderiv2; trivial.

 apply wf_weakening in IHderiv.
 red in IHderiv, H |- *. unfold fv_fml in IHderiv, H |- *. simpl; intros.
 rewrite in_app_iff in H1. destruct H1; [apply H in H1|apply IHderiv in H1]; trivial.

 red in IHderiv1 |- *. unfold fv_fml in IHderiv1 |- *. intros; apply IHderiv1.
 simpl; rewrite in_app_iff; right; trivial.

 red in IHderiv |- *. unfold fv_fml in IHderiv |- *. simpl; intros.
 rewrite <- in_S_fv_fml in H0. apply IHderiv in H0. simpl in H0; trivial.

 red in IHderiv |- *. unfold fv_fml in IHderiv |- *. simpl; intros.
 simpl in IHderiv. unfold subst_fml in H1.
 replace 0 with (0+0) in H1 by omega. apply in_fv_fml_subst_split in H1.
 destruct H1; [apply H in H1
   |rewrite in_S_fv_fml in H1; simpl in H1; apply IHderiv in H1]; trivial.

 red in IHderiv |- *. unfold fv_fml in IHderiv |- *. simpl in IHderiv |- *.
 intros; apply IHderiv. rewrite <- in_S_fv_fml in H1.
 unfold subst_fml. replace 0 with (0+0) in H1 |- * by omega.
 apply in_fv_fml_subst; trivial.
  
 unfold lift_fml in IHderiv2. rewrite lift_fml_split in IHderiv2.
 fold (lift_fml f1 1) in IHderiv2. fold (lift_fml (lift_fml f1 1) 1) in IHderiv2.
 apply wf_weakening in IHderiv2. apply wf_weakening in IHderiv2; trivial.
Qed. 

End FoDeriv.


(******************************************************************************************)
(*This model defines the first-order theory with 4 parts :*)
(*1. The abstract signature of the theory*)
(*2. The first-order language defined above*)
(*3. The axioms defined abstractly*)
(*3. Derivation rules*)
(******************************************************************************************)

Module Type TheorySyn.

(*Signature of the theory*)
Declare Module sig : TheorySig.
Export sig.
(*Check foterm.*)

(*First order language is included when defining abstract axioms*)
Declare Module ax : TheoryAx sig.
Export ax.
(*Print foformula.*)
(*Check ax_syn.*)

(*Derivation rules are included now*)
Include FoDeriv sig ax.
(*Print deriv.*)

End TheorySyn.

