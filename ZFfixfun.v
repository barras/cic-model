(** Construction of a function (a.k.a a family of sets) over a fixed domain by
    transfinite iteration. No fixpoint theorem here.
 *)

Require Import ZF ZFrelations ZFnats ZFord.
    
(** Order on families *)
Definition incl_fam A X Y :=
  forall a, a ∈ A -> X a ⊆ Y a.

Instance incl_fam_trans : forall A, Transitive (incl_fam A).
red; red; intros.
transitivity (y a); auto with *.
Qed.

(** Monotonicity *)
Definition mono_fam A F :=
  forall X Y, morph1 X -> morph1 Y -> incl_fam A X Y -> incl_fam A (F X) (F Y).

Section IterMonotone.

  Variable A : set.
  Variable F : (set -> set) -> set -> set.
  Variable Fm : Proper ((eq_set==>eq_set) ==> eq_set ==> eq_set) F.

  (** Definition of the TIF iterator *)
  Let F' f o := cc_lam A (fun a => sup o (fun o' => F (cc_app (f o')) a)).

  Let F'm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) F'.
do 3 red; intros.
unfold F'.
apply cc_lam_ext; intros; auto with *.
red; intros.
apply sup_morph; trivial.
red; intros.
apply Fm; trivial.
red; intros.
apply cc_app_morph; auto with *.
Qed.

  Let F'ext : forall o f f', isOrd o -> eq_fun o f f' -> F' f o == F' f' o.
intros.
unfold F'.
apply cc_lam_ext; intros; auto with *.
red; intros.
apply sup_morph; auto with *.
red; intros.
apply Fm; trivial.
red; intros.
apply cc_app_morph; auto with *.
Qed.

  Definition TIF o := cc_app (TR F' o).

  Instance TIF_morph : morph2 TIF.
unfold TIF; do 3 red; intros.
apply cc_app_morph; trivial.
apply TR_morph0; auto with *.
Qed.

  Let m2: forall a a' o o', a ∈ A -> a == a' -> isOrd o -> o == o' ->
    F (TIF o) a == F (TIF o') a'.
intros.
apply Fm; auto with *.
apply TIF_morph; auto with *.
Qed.

  Lemma TIF_eq : forall o a,
    isOrd o ->
    a ∈ A ->
    TIF o a == sup o (fun o' => F (TIF o') a).
intros.
unfold TIF.
rewrite TR_eqn; intros; auto.
unfold F' at 1; rewrite cc_beta_eq; auto with *.
do 2 red; intros.
apply sup_morph; auto with *.
red; intros.
apply m2; trivial.
apply isOrd_inv with o; trivial.
Qed.

  Lemma TIF_intro : forall o o' a x,
    isOrd o ->
    lt o' o ->
    a ∈ A ->
    x ∈ F (TIF o') a ->
    x ∈ TIF o a.
intros.
rewrite TIF_eq; trivial.
rewrite sup_ax; auto.
 exists o'; trivial.

 do 2 red; intros; apply m2; auto with *.
 apply isOrd_inv with o; trivial.
Qed.

  Lemma TIF_elim : forall o x a,
    isOrd o ->
    a ∈ A ->
    x ∈ TIF o a ->
    exists2 o', lt o' o & x ∈ F (TIF o') a.
intros.
rewrite TIF_eq in H1; trivial.
rewrite sup_ax in H1; auto.
do 2 red; intros; apply m2; auto with *.
apply isOrd_inv with o; trivial.
Qed.

  (** Monotonicity of TIF *)
  Lemma TIF_mono : forall a, a ∈ A -> increasing (fun o => TIF o a).
do 2 red; intros.
apply TIF_elim in H3; intros; auto with *.
destruct H3.
apply TIF_intro with x0; auto with *.
apply H2 in H3; trivial.
Qed.

  Lemma TIF_incl : forall o, isOrd o ->
    forall o', lt o' o ->
    forall a, a ∈ A -> 
    TIF o' a ⊆ TIF o a.
intros.
apply TIF_mono; trivial; auto.
apply isOrd_inv with o; trivial.
Qed.


  
  Variable Fmono : mono_fam A F.

(*  Lemma FFmono_ext: forall X Y, morph1 X -> morph1 Y -> eq_fun A X Y -> eq_fun A (F X) (F Y).
red; intros.
rewrite <- H3; clear x' H3.
apply incl_eq.
 apply Fmono; trivial.
 red; red; intros.
 revert H4; apply eq_elim; auto with *.

 apply Fmono; trivial.
 red; red; intros.
 revert H4; apply eq_elim; symmetry; apply H1; auto with *.
Qed.
Hint Resolve FFmono_ext.
*)

  Lemma TIF_mono_succ : forall o a,
    isOrd o ->
    a ∈ A ->
    TIF (osucc o) a == F (TIF o) a.
intros.
assert (Fext : ext_fun (osucc o) (fun o' => F (TIF o') a)).
 do 2 red; intros; apply m2; auto with *.
 apply isOrd_inv with (osucc o); auto.
rewrite TIF_eq; auto.
apply eq_intro; intros.
 rewrite sup_ax in H1; trivial.
 destruct H1.
 revert H2; apply Fmono; auto with *.
  apply TIF_morph; auto with *.
  apply TIF_morph; auto with *.
 red; intros.
 apply TIF_mono; trivial.
  apply isOrd_inv with (osucc o); auto.
  apply olts_le; trivial.

 rewrite sup_ax; trivial.
 exists o; trivial.
 apply lt_osucc; trivial.
Qed.

  Lemma TIF_mono_eq : forall o a,
    isOrd o ->
    a ∈ A ->
    TIF o a == sup o (fun o' => TIF (osucc o') a).
intros.
rewrite TIF_eq; auto.
apply sup_morph; auto with *.
red; intros.
rewrite <- TIF_mono_succ; trivial.
 apply TIF_morph; auto with *.
 rewrite H2; reflexivity.

 apply isOrd_inv with o; trivial.
Qed.

  (** Property related to fixpoints: any post-fixpoint [fx] contains all stages *)
  Lemma TIF_pre_fix : forall fx o,
     morph1 fx ->
     isOrd o ->
     incl_fam A (F fx) fx ->
     incl_fam A (TIF o) fx.
intros.
induction H0 using isOrd_ind; intros.
red; intros.
transitivity (F fx a); auto with *.
red; intros.
elim TIF_elim with (3:=H5); intros; auto with *.
revert H7; apply Fmono; auto with *.
apply TIF_morph; auto with *.
Qed.


End IterMonotone.


Local Notation E := eq_set (only parsing).
  
Instance TIF_morph_gen : Proper (E==>((E==>E)==>E==>E)==>E==>E==>E) TIF.
do 5 red; intros.
unfold TIF.
apply cc_app_morph; trivial.
apply TR_morph; trivial.
do 3 red; intros.
apply cc_lam_ext; trivial.
red; intros.
apply sup_morph; trivial.
red; intros.
apply H0; trivial.
red; intros.
apply cc_app_morph; auto.
Qed.

