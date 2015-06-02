
(** A theory of dependent inductive families (here W-types) as a subset
    of a W-type *)

Require Import ZF ZFpairs ZFrelations ZFord ZFstable ZFind_w ZFfixfun.

Section DependentW.

(** Parameters of W-types *)
Variable A : set.
Variable B : set -> set.
Hypothesis Bm : morph1 B.
Let Bext : ext_fun A B.
apply morph_is_ext; trivial.
Qed.

(** Index type *)
Variable Arg : set.

(** Constraints on the subterms *)
Hypothesis f : set -> set -> set.
Hypothesis fm : morph2 f.
Hypothesis ftyp : forall x i,
  x ∈ A -> i ∈ B x -> f x i ∈ Arg.

(** Instance introduced by the constructors *)
Hypothesis g : set -> set -> Prop.
Hypothesis gm : Proper (eq_set==>eq_set==>iff) g.

(** The intended type operator:

    [Inductive Wd : Arg->Type := C (x:A) (_:forall i:B x, Wd(f x i)) : Wd(g x).

    is encoded as

    [Inductive Wd' (a:Arg) : Type := C' (x:A) (_:g x=a) (_:forall i:B x, Wd(f x i)).
 *)
Definition W_Fd (X:set->set) (a:set) :=
  Σ x ∈ subset A (fun x => g x a), Π i ∈ B x, X (f x i).

Instance W_Fd_morph :
  Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) W_Fd.
do 3 red; intros.
apply sigma_ext; intros.
 apply subset_morph; auto with *.
 red; intros.
 rewrite H0; reflexivity.

 apply subset_elim1 in H1.
 apply cc_prod_ext; auto with *.
 red; intros.
 apply H.
 apply fm; auto.
Qed.

Lemma W_Fd_mono : mono_fam Arg W_Fd.
do 2 red; intros.
apply sigma_mono.
 do 2 red; intros.
 apply subset_elim1 in H3.
 apply cc_prod_ext; auto with *.
 red; intros.
 apply H; apply fm; auto.

 do 2 red; intros.
 apply subset_elim1 in H3.
 apply cc_prod_ext; auto with *.
 red; intros.
 apply H0; apply fm; auto.

 red; intros.
 rewrite subset_ax in H3|-*; destruct H3 as (?,(z',?,?)).
 split; trivial.
 exists z'; trivial.

 intros.
 apply subset_elim1 in H3.
 apply cc_prod_covariant; auto with *.
  do 2 red; intros.
  apply H0; apply fm; auto with *.

  intros.
  rewrite <- H4; apply H1; auto.
Qed.
Hint Resolve W_Fd_mono.

Lemma W_Fd_incl_W_F X Y :
  ext_fun Arg X ->
  (forall a, a ∈ Arg -> X a ⊆ Y) ->
  forall a, a ∈ Arg -> W_Fd X a ⊆ W_F A B Y.
intros.
apply sigma_mono.
 do 2 red; intros.
 apply subset_elim1 in H2.
 apply cc_prod_ext; auto with *.
 red; intros.
 apply H; auto.
 apply fm; trivial.

 do 2 red; intros; apply cc_arr_morph; auto with *.

 red; intros.
 apply subset_elim1 in H2; trivial.

 intros.
 apply subset_elim1 in H2.
 unfold cc_arr; apply cc_prod_covariant; auto with *.
Qed.
(*
Lemma W_Fd_def X Y :
  ext_fun Arg X ->
  (forall a, a ∈ Arg -> X a ⊆ Y) ->
  forall a, a ∈ Arg ->
  W_Fd X a == subset (W_F A B Y) (fun w => 
        g (fst w) == a /\
        forall i, i ∈ B (fst w) -> cc_app (snd w) i ∈ X (f (fst w) i)).
intros.
apply incl_eq.
 red; intros.
 rewrite subset_ax.
 split.
  revert H2; apply W_Fd_incl_W_F; trivial.

  exists z; auto with *.
  assert (fst z ∈ A).
   apply fst_typ_sigma in H2.
   apply subset_elim1 in H2; trivial.
  split; intros.
   apply fst_typ_sigma in H2.
   rewrite subset_ax in H2; destruct H2 as (_,(a',?,?)).
   rewrite H2; trivial.

   apply snd_typ_sigma with (y:=fst z) in H2; auto with *.
    apply cc_prod_elim with (1:=H2); trivial.

    do 2 red; intros.
    apply subset_elim1 in H5.
    apply cc_prod_ext; auto with *.
    red; intros; auto.
    apply H; auto with *.
    apply fm; trivial.

 red; intros.
 rewrite subset_ax in H2; destruct H2 as (?,(z',?,(?,?))).
 apply W_F_elim in H2; trivial.
 destruct H2 as (?,(?,?)).
 rewrite H7; apply couple_intro_sigma.
  do 2 red; intros.
  apply subset_elim1 in H8.
  apply cc_prod_ext; auto with *.
  red; intros.
  apply H; auto with *.
  apply fm; trivial.

  apply subset_intro; trivial.
  rewrite H3; trivial.

  apply cc_prod_intro; intros.
   do 2 red; intros; apply cc_app_morph; auto with *.

   do 2 red; intros.
   apply H; auto with *.
   apply fm; auto with *.

   assert (x ∈ B (fst z')).
    revert H8; apply eq_elim; apply Bext; trivial.
    apply fst_morph; trivial.
   specialize H5 with (1:=H9).
   revert H5; apply in_set_morph.
    rewrite H3; reflexivity.

    apply H; auto.
    rewrite H3; reflexivity.
Qed.
*)
(** Predicate characterizing the elements of the W-type that respect the
    index constraints *)
Inductive instance a w : Prop :=
  | I_node :
      fst w ∈ A ->
      g (fst w) a ->
      (forall i, i ∈ B (fst w) -> instance (f (fst w) i) (cc_app (snd w) i)) ->
      instance a w.

Instance inst_m : Proper (eq_set ==> eq_set ==> iff) instance.
apply morph_impl_iff2; auto with *.
do 4 red; intros.
revert y H y0 H0.
induction H1; constructor; intros.
 rewrite <- H4; trivial.

 rewrite <- H3; rewrite <- H4; trivial.

 apply H2 with i.
  rewrite (Bext _ _ H (fst_morph _ _ H4)); trivial.

  rewrite H4; reflexivity.

  rewrite H4; reflexivity.
Qed.

Lemma inst_inv o :
  isOrd o ->
  forall a, a ∈ Arg ->
  subset (TI (W_F A B) o) (instance a) == TIF Arg W_Fd o a.
induction 1 using isOrd_ind; intros.
rewrite TIF_eq; auto with *.
apply eq_set_ax; intros z.
rewrite subset_ax.
rewrite TI_eq; auto with *.
2:apply W_F_morph; trivial.
rewrite sup_ax.
 rewrite sup_ax.
  split; intros.
   destruct H3 as ((o',?,?),(z',?,?)).
   exists o'; trivial.
   apply W_F_elim in H4; trivial.
   destruct H4 as (?,(?,?)).
   rewrite H8.
   apply couple_intro_sigma.
    do 2 red; intros.
    apply subset_elim1 in H9.
    apply cc_prod_ext; auto with *.
    red; intros; apply TIF_morph; auto with *.
    apply fm; trivial.

    destruct H6 as (?,?,_).
    rewrite <- H5 in H9.
    apply subset_intro; trivial.

    apply cc_prod_intro; intros.
     do 2 red; intros; apply cc_app_morph; auto with *.

     do 2 red; intros.
     apply TIF_morph; auto with *.
     apply fm; auto with *.

     rewrite <- H1; auto.
     apply subset_intro; auto.
     rewrite <- H5 in H6.
     destruct H6 as (_,_,?); auto.

   destruct H3 as (o',?,?).
   split.
    exists o'; trivial.
    revert H4; apply W_Fd_incl_W_F; trivial.
     do 2 red; intros; apply TIF_morph; auto with *.

     intros.
     rewrite <- H1; auto.
     red; intros.
     apply subset_elim1 in H5; trivial.

     exists z; auto with *.
     assert (fst z ∈ A).
      apply fst_typ_sigma in H4.
      apply subset_elim1 in H4; trivial.
     constructor; intros; trivial.
      apply fst_typ_sigma in H4.
      rewrite subset_ax in H4.
      destruct H4 as (?,(x',?,?)).
      rewrite H6; trivial.

      apply snd_typ_sigma with (y:=fst z) in H4; auto with *.
       apply cc_prod_elim with (2:=H6) in H4.
       rewrite <- H1 in H4; auto.
       rewrite subset_ax in H4; destruct H4 as (_,(w',?,?)).
       rewrite H4; trivial.

       do 2 red; intros.
       apply subset_elim1 in H7.
       apply cc_prod_ext; auto.
       red; intros; apply TIF_morph; auto with *.
       apply fm; auto.

  do 2 red; intros.
  apply W_Fd_morph; auto with *.
  red; intros; apply TIF_morph; auto.

 do 2 red; intros.
 apply W_F_morph; auto with *.
 apply TI_morph; auto.
Qed.

(** Fixpoint of the W_Fd operator *)
Definition Wd := TIF Arg W_Fd (W_ord A B).

Lemma Wd_eqn : forall a, a ∈ Arg -> Wd a == W_Fd Wd a.
intros.
apply incl_eq.
 unfold Wd; rewrite <- TIF_mono_succ; auto with *.
 apply TIF_incl; auto with *.
  apply isOrd_succ.
  apply W_o_o; trivial.

  apply lt_osucc; apply W_o_o; trivial.

 apply W_o_o; trivial.

 red; intros.
 unfold Wd; rewrite <- inst_inv; trivial.
 2:apply W_o_o; trivial.
 apply subset_intro.
  change (z ∈ W A B).
  rewrite W_eqn; trivial.
  revert H0; apply W_Fd_incl_W_F; intros; auto.
   do 2 red; intros.
   apply TIF_morph; auto with *.

   red; intros.
   unfold Wd in H1.
   rewrite <- inst_inv in H1; auto.
   2:apply W_o_o; trivial.
   apply subset_elim1 in H1; trivial.
   
  unfold Wd in H0; rewrite <- TIF_mono_succ in H0; auto.
   rewrite <- inst_inv in H0; auto.
   2:apply isOrd_succ; apply W_o_o; trivial.
   rewrite subset_ax in H0; destruct H0 as (_,(?,?,?)).
   rewrite H0; trivial.

   apply W_Fd_morph.

   apply W_o_o; trivial.
Qed.

(*

(** Predicate characterizing the elements of the W-type that respect the
    index constraints *)
Inductive instance a w : Prop :=
| I_node :
    g (fst w) == a ->
    (forall i, i ∈ B (fst w) -> instance (f (fst w) i) (cc_app (snd w) i)) ->
    instance a w.

(** The intended type operator *)
Definition W_Fd (X:set->set) (a:set) :=
  subset (W_F A B (sup Arg X)) (instance a).

Instance W_Fd_morph :
  Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) W_Fd.
do 3 red; intros.
apply subset_morph.
 apply W_F_morph; auto with *.
 apply sup_morph; auto with *.
 red; auto.

 red; intros.
 split; destruct 1; split; intros; auto.
  rewrite <- H0; trivial.
  rewrite H0; trivial.
Qed.

Lemma W_Fd_mono : mono_fam Arg W_Fd.
unfold W_Fd; do 3 red; intros.
rewrite subset_ax in H3|-*.
destruct H3; split; trivial.
revert H3; apply W_F_mono; auto with *.
red; intros.
rewrite sup_ax in H3|-*; auto with *.
destruct H3 as (a',?,?); exists a'; trivial.
revert H5; apply H1; trivial.
Qed.
Hint Resolve W_Fd_mono.

Lemma inst_inv o :
  isOrd o ->
  forall a, a ∈ Arg ->
  subset (TI (W_F A B) o) (instance a) == TIF Arg W_Fd o a.
induction 1 using isOrd_ind; intros.
rewrite TIF_eq; auto with *.
apply eq_set_ax; intros z.
rewrite subset_ax.
rewrite TI_eq; auto with *.
2:apply W_F_morph; trivial.
rewrite sup_ax.
 rewrite sup_ax.
  split; intros.
   destruct H3 as ((o',?,?),(z',?,?)).
   exists o'; trivial.
   rewrite H5; apply subset_intro; trivial.
   apply W_F_elim in H4; trivial.
   destruct H4 as (?,(?,?)).
   rewrite <- H5; rewrite H8.
   apply W_F_intro; intros; auto with *.
    do 2 red; intros; apply cc_app_morph; auto with *.
   rewrite sup_ax.
    destruct H6.
    exists (f (fst z') i).
     rewrite <- H5; auto.
    rewrite <- H1; auto.
    2:rewrite <- H5; auto.
    rewrite H5; apply subset_intro.
     rewrite <- H5; auto.

     apply H10.
     revert H9; apply eq_elim; apply Bext; auto.
     apply fst_morph; trivial.

    do 2 red; intros; apply TIF_morph; auto with *.

   destruct H3 as (o',?,?).
   unfold W_Fd at 1 in H4; rewrite subset_ax in H4.
   destruct H4 as (?,(z',?,?)).
   split.
    exists o'; trivial.
    revert H4; apply W_F_mono; auto with *.
    red; intros w ?.
    rewrite sup_ax in H4.
     destruct H4 as (a',?,?).
     rewrite <- H1 in H7; trivial.
     apply subset_elim1 in H7; trivial.

     do 2 red; intros; apply TIF_morph; auto with *.

    exists z'; trivial.

  do 2 red; intros; apply W_Fd_morph; auto with *.
  red; intros; apply TIF_morph; auto with *.

 do 2 red; intros; apply W_F_morph; trivial.
 apply TI_morph; trivial.
Qed.

(** Fixpoint of the W_Fd operator *)
Definition Wd := TIF Arg W_Fd (W_ord A B).

Lemma Wd_eqn : forall a, a ∈ Arg -> Wd a == W_Fd Wd a.
intros.
apply incl_eq.
 unfold Wd; rewrite <- TIF_mono_succ; auto with *.
 apply TIF_incl; auto with *.
  apply isOrd_succ.
  apply W_o_o; trivial.

  apply lt_osucc; apply W_o_o; trivial.

 apply W_o_o; trivial.

 red; intros.
 unfold W_Fd in H0.
 rewrite subset_ax in H0; destruct H0 as (?,(z',?,?)).
 unfold Wd; rewrite <- inst_inv; trivial.
 2:apply W_o_o; trivial.
 rewrite H1; apply subset_intro; trivial.
 rewrite <- H1.
 change (z ∈ W A B).
 rewrite W_eqn; trivial.
 revert H0; apply W_F_mono; auto with *.
 red; intros.
 rewrite sup_ax in H0.
  destruct H0 as (a',?,?).
  unfold Wd in H3; rewrite <- inst_inv in H3; trivial.
  2:apply W_o_o; trivial.
  apply subset_elim1 in H3; trivial.

 do 2 red; intros.
 apply TIF_morph; auto with *.
Qed.
*)

End DependentW.