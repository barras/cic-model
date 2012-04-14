(** Set theory without infinity axiom: hereditarily finite sets *)

Require Export Setoid Morphisms.
Require Import List.
Require Import Bool.

Lemma in_map_inv : forall (A B:Set) (f:A->B) x l,
  In x (map f l) -> exists2 y, In y l & x = f y.
Proof.
induction l; simpl in |- *; intros.
 elim H.
 destruct H.
  exists a; auto.
  elim IHl; intros; trivial.
    exists x0; auto.
Qed.

(*****************)

Inductive hf : Set := HF (elts : list hf).

Definition hf_elts (x:hf) := let (lx) := x in lx.

Lemma hf_elts_ext : forall x, HF (hf_elts x) = x.
destruct x; reflexivity.
Qed.

Lemma hf_ind2 : forall P : hf -> Prop,
  (forall l, (forall x, In x l -> P x) -> P (HF l)) ->
  forall x, P x.
Proof.
intros P Pnode.
fix hf_ind 1.
destruct x.
apply Pnode.
induction elts; simpl in |- *; intros.
 elim H.

 destruct H.
  elim H.
    apply hf_ind.
  apply IHelts; trivial.
Qed.

(*****************)

Definition forall_elt P x :=
  fold_right (fun y b => P y && b) true (hf_elts x).

Definition exists_elt P x :=
  negb (forall_elt (fun x => negb (P x)) x).

Lemma forall_elt_case :
  forall P x,
  forall_elt P x = true /\ (forall y, In y (hf_elts x) -> P y = true) \/
  forall_elt P x = false /\ (exists2 y, In y (hf_elts x) & P y = false).
Proof.
unfold forall_elt in |- *.
destruct x as (lx); simpl.
induction lx; simpl in |- *; intros.
 left.
   split; trivial.
   destruct 1.
 elimtype (P a = true \/ P a = false); intros.
   rewrite H; simpl in |- *.
    elim IHlx; intros.
   left.
     destruct H0; split; trivial.
     destruct 1; auto.
     elim H2; auto.
   right.
     destruct H0.
     split; auto.
     destruct H1.
     exists x; auto.
   rewrite H; simpl in |- *.
    right.
    split; auto.
    exists a; auto.
  destruct (P a); auto.
Qed.

Lemma forall_elt_true_intro :
  forall P x,
  (forall y, In y (hf_elts x) -> P y = true) ->
  forall_elt P x = true.
intros.
elim forall_elt_case with P x; intros.
 destruct H0; trivial.
 destruct H0.
   destruct H1.
    rewrite (H _ H1) in H2;  discriminate.
Qed.

Lemma forall_elt_false_intro :
  forall P y x,
  In y (hf_elts x) ->
  P y = false ->
  forall_elt P x = false.
intros.
elim forall_elt_case with P x; intros.
 destruct H1.
    rewrite (H2 _ H) in H0;  discriminate.
 destruct H1; trivial.
Qed.

Lemma forall_elt_true_elim :
  forall P y x,
  forall_elt P x = true ->
  In y (hf_elts x) ->
  P y = true.
intros.
elim forall_elt_case with P x; intros.
 destruct H1; auto.
 destruct H1.
    rewrite H1 in H;  discriminate.
Qed.

Lemma forall_elt_false_elim :
  forall P x,
  forall_elt P x = false ->
  exists2 y, In y (hf_elts x) & P y = false.
intros.
elim forall_elt_case with P x; intros.
 destruct H0.
    rewrite H0 in H;  discriminate.
 destruct H0; trivial.
Qed.

Lemma exists_elt_true_intro :
  forall P y x,
  In y (hf_elts x) ->
  P y = true ->
  exists_elt P x = true.
intros.
unfold exists_elt in |- *.
 rewrite forall_elt_false_intro with (fun x => negb (P x)) y x; trivial.
 rewrite H0; trivial.
Qed.

Lemma exists_elt_true_elim :
  forall P x,
  exists_elt P x = true ->
  exists2 y, In y (hf_elts x) & P y = true.
intros.
elim forall_elt_false_elim with (fun x => negb (P x)) x; intros.
 exists x0; trivial.
    rewrite <- (negb_elim (P x0)).
    rewrite H1; trivial.
 fold (negb true) in |- *.
   apply negb_sym; trivial.
   symmetry  in |- *; trivial.
Qed.

(** Equality *)

Fixpoint eq_hf (x y: hf) {struct x} : bool :=
  forall_elt (fun x1 => exists_elt (fun y1 => eq_hf x1 y1) y) x &&
  forall_elt (fun y1 => exists_elt (fun x1 => eq_hf x1 y1) x) y.

Definition Eq_hf x y := eq_hf x y = true.


Lemma eq_hf_intro :
  forall x y,
  (forall x', In x' (hf_elts x) ->
   exists2 y', In y' (hf_elts y) & Eq_hf x' y') ->
  (forall y', In y' (hf_elts y) ->
   exists2 x', In x' (hf_elts x) & Eq_hf x' y') ->
  Eq_hf x y.
Proof.
unfold Eq_hf.
destruct x as (lx); simpl; intros.
apply andb_true_intro; split; apply forall_elt_true_intro; intros.
 elim H with (1 := H1); intros.
   apply exists_elt_true_intro with x; auto.
 elim H0 with (1 := H1); intros.
   apply exists_elt_true_intro with x; auto.
Qed.

Lemma eq_hf_elim1 :
  forall x' x y,
  Eq_hf x y ->
  In x' (hf_elts x) ->
  exists2 y', In y' (hf_elts y) & Eq_hf x' y'.
Proof.
unfold Eq_hf.
destruct x as (lx); simpl in |- *; intros.
elim andb_prop with (1 := H); clear H; intros.
specialize forall_elt_true_elim with (1 := H) (2 := H0); intros.
apply exists_elt_true_elim with (P := fun y' => eq_hf x' y').
trivial.
Qed.

Lemma eq_hf_elim2 :
  forall y' x y,
  Eq_hf x y ->
  In y' (hf_elts y) ->
  exists2 x', In x' (hf_elts x) & Eq_hf x' y'.
Proof.
unfold Eq_hf.
destruct x as (lx); destruct y as (ly); simpl in |- *; intros.
elim andb_prop with (1 := H); clear H; intros.
specialize forall_elt_true_elim with (1 := H1) (2 := H0); intros.
change lx with (hf_elts (HF lx)).
apply exists_elt_true_elim with (P := fun x1 => eq_hf x1 y').
trivial.
Qed.

Instance eq_hf_refl : Reflexive Eq_hf.
red; intro.
elim x using hf_ind2; intros.
apply eq_hf_intro; intros.
 exists x'; auto.
 exists y'; auto.
Qed.

Instance eq_hf_sym : Symmetric Eq_hf.
red; intros x.
elim x using hf_ind2; destruct y; intros.
apply eq_hf_intro; intros.
 elim eq_hf_elim2 with (1 := H0) (2 := H1); intros.
   exists x0; auto.
 elim eq_hf_elim1 with (1 := H0) (2 := H1); intros.
   exists x0; auto.
Qed.

Instance eq_hf_trans : Transitive Eq_hf.
red; intros x.
elim x using hf_ind2; destruct y; destruct z; intros.
apply eq_hf_intro; intros.
 elim eq_hf_elim1 with (1 := H0) (2 := H2); intros.
   elim eq_hf_elim1 with (1 := H1) (2 := H3); intros.
   exists x1;  eauto.
 elim eq_hf_elim2 with (1 := H1) (2 := H2); intros.
   elim eq_hf_elim2 with (1 := H0) (2 := H3); intros.
   exists x1;  eauto.
Qed.

Instance eq_hf_equiv : Equivalence Eq_hf. (* why is it needed? *)
constructor; auto with *.
Qed.

Instance eq_hf_morph : Proper (Eq_hf ==> Eq_hf ==> @eq bool) eq_hf.
repeat red; intros.
apply bool_1.
fold (Eq_hf x x0) (Eq_hf y y0).
rewrite H; rewrite H0; reflexivity.
Qed.

(** Membership *)

Definition in_hf (x y: hf) : bool := exists_elt (fun y1 => eq_hf x y1) y.

Definition In_hf x y := in_hf x y = true.

Lemma in_hf_intro : forall x x' y,
  Eq_hf x x' ->
  In x' (hf_elts y) ->
  In_hf x y.
intros.
unfold In_hf, in_hf.
apply exists_elt_true_intro with x'; auto.
Qed.

Lemma in_hf_elim : forall x y,
  In_hf x y ->
  exists2 x', In x' (hf_elts y) & Eq_hf x x'.
unfold In_hf, in_hf.
intros.
apply exists_elt_true_elim with (1:=H).
Qed.


Lemma in_hf_reg_l: forall a a' b,
  Eq_hf a a' -> In_hf a b -> In_hf a' b.
intros.
elim in_hf_elim with (1:=H0); intros.
apply in_hf_intro with x; trivial.
transitivity a; trivial; symmetry; trivial.
Qed.

Lemma in_hf_reg_r :
  forall a x y,
  Eq_hf x y ->
  In_hf a x ->
  In_hf a y.
intros.
elim in_hf_elim with (1:=H0); intros.
elim eq_hf_elim1 with (1:=H) (2:=H1); intros.
apply in_hf_intro with x1; trivial.
transitivity x0; trivial.
Qed.


Instance In_hf_morph : Proper (Eq_hf ==> Eq_hf ==> iff) In_hf.
split; intros.
 apply in_hf_reg_l with x; trivial.
 apply in_hf_reg_r with x0; trivial.

 symmetry in H, H0.
 apply in_hf_reg_l with y; trivial.
 apply in_hf_reg_r with y0; trivial.
Qed.

Instance in_hf_morph : Proper (Eq_hf ==> Eq_hf ==> @eq _) in_hf.
repeat red; intros.
apply bool_1.
fold (In_hf x x0) (In_hf y y0).
rewrite H; rewrite H0; reflexivity.
Qed.


Lemma In_hf_head : forall x y l,
  Eq_hf x y ->
  In_hf x (HF (y::l)).
intros.
apply in_hf_intro with y; simpl; auto.
Qed.

Lemma In_hf_tail : forall x y l,
  In_hf x (HF l) ->
  In_hf x (HF (y::l)).
intros.
elim in_hf_elim with (1:=H); intros.
apply in_hf_intro with x0; simpl; auto.
Qed.

Lemma In_hf_elim : forall x y l,
  In_hf x (HF (y::l)) ->
  Eq_hf x y \/ In_hf x (HF l).
Proof.
intros.
elim in_hf_elim with (1:=H); simpl; intros.
destruct H0.
 subst x0; auto.
 right; apply in_hf_intro with x0; trivial.
Qed.

Lemma In_app_left : forall x l1 l2,
  In_hf x (HF l1) ->
  In_hf x (HF (l1 ++ l2)).
Proof.
induction l1; simpl; intros.
 inversion H.

 elim In_hf_elim with (1:=H); intros.
  apply In_hf_head; trivial.
  apply In_hf_tail; auto.
Qed.

Lemma In_app_right : forall x l1 l2,
  In_hf x (HF l2) ->
  In_hf x (HF (l1 ++ l2)).
Proof.
induction l1; simpl; intros; auto.
 apply In_hf_tail; auto.
Qed.

Lemma In_app_elim : forall x l1 l2,
  In_hf x (HF (l1 ++ l2)) ->
  In_hf x (HF l1) \/ In_hf x (HF l2).
induction l1; simpl; intros; auto.
elim In_hf_elim with (1:=H); intros.
 left.
 apply In_hf_head; trivial.

 elim IHl1 with (1:=H0); intros; auto.
 left.
 apply In_hf_tail; trivial.
Qed.

Definition incl_hf x y :=
  forall_elt (fun x1 => in_hf x1 y) x.

Definition Incl_hf x y := forall a, In_hf a x -> In_hf a y.

Instance incl_hf_morph : Proper (Eq_hf ==> Eq_hf ==> iff) Incl_hf.
unfold Incl_hf; split; intros.
 rewrite <- H0; rewrite <- H in H2; auto.
 rewrite H0; rewrite H in H2; auto.
Qed.

Lemma incl_hf_sound : forall x y,
  incl_hf x y = true -> Incl_hf x y.
unfold incl_hf, Incl_hf.
intros.
elim in_hf_elim with (1:=H0); intros.
specialize forall_elt_true_elim with (1:=H) (2:=H1); intros.
apply in_hf_reg_l with x0; trivial.
symmetry; trivial.
Qed.

Lemma incl_hf_complete :  forall x y,
  Incl_hf x y -> incl_hf x y = true.
unfold incl_hf, Incl_hf; intros.
apply forall_elt_true_intro; intros.
apply H.
apply in_hf_intro with y0; trivial; reflexivity.
Qed.

Lemma Eq_hf_intro : forall x y,
  Incl_hf x y -> Incl_hf y x -> Eq_hf x y.
intros.
apply eq_hf_intro; intros.
 apply in_hf_elim.
 apply H.
 apply in_hf_intro with x'; trivial; reflexivity.

 elim (in_hf_elim y' x); intros.
  exists x0; trivial; symmetry; trivial.

  apply H0.
  apply in_hf_intro with y'; trivial; reflexivity.
Qed.


Lemma Eq_hf_cons : forall x1 x2 l1 l2,
  Eq_hf x1 x2 ->
  Eq_hf (HF l1) (HF l2) ->
  Eq_hf (HF (x1::l1)) (HF (x2::l2)).
Proof.
intros.
apply Eq_hf_intro; red; simpl in |- *; intros.
 elim In_hf_elim with (1:=H1); intros.
  apply In_hf_head; transitivity x1; trivial.
  apply In_hf_tail; apply in_hf_reg_r with (HF l1); trivial.

 elim In_hf_elim with (1:=H1); intros.
  apply In_hf_head; transitivity x2; trivial.
  symmetry; trivial.

  apply In_hf_tail; apply in_hf_reg_r with (HF l2); trivial.
  symmetry; trivial.
Qed.

Lemma Eq_hf_split : forall l1 l1' l2 l2',
  Eq_hf (HF l1) (HF l1') ->
  Eq_hf (HF l2) (HF l2') ->
  Eq_hf (HF(l1++l2)) (HF(l1'++l2')).
intros.
apply Eq_hf_intro; red; intros.
 elim In_app_elim with (1:=H1); intros.
  apply In_app_left.
  apply in_hf_reg_r with (HF l1); auto.

  apply In_app_right.
  apply in_hf_reg_r with (HF l2); auto.

 elim In_app_elim with (1:=H1); intros.
  apply In_app_left.
  apply in_hf_reg_r with (HF l1'); auto.
  symmetry; auto.

  apply In_app_right.
  apply in_hf_reg_r with (HF l2'); auto.
  symmetry; auto.
Qed.


Lemma hf_size_ind : forall (P:hf->Type) x,
  P (HF nil) ->
  (forall x' y,
   In_hf x' x ->
   Incl_hf y x ->
   P y -> P (HF(x'::hf_elts y))) ->
  P x.
Proof.
destruct x as (x).
intro Pnil.
elim x; intros; trivial.
change l with (hf_elts (HF l)).
apply  X0.
 apply In_hf_head; reflexivity.

 red; intros; apply In_hf_tail; trivial.

 apply X; intros.
 apply X0; trivial.
  apply In_hf_tail; trivial.
  red; intros; apply In_hf_tail; auto.
Qed.



(** Cancelling redundancies *)

Lemma cancel_repeat : forall a l,
  In_hf a (HF l) -> Eq_hf (HF(a::l)) (HF l).
intros.
apply Eq_hf_intro; red; intros.
 elim In_hf_elim with (1:=H0); intros; auto.
 rewrite H1; trivial.

 apply In_hf_tail; trivial.
Qed.

Definition cons_hf x l := if in_hf x (HF l) then l else x :: l.

Lemma cons_hf_cons :
  forall x l, Eq_hf (HF(cons_hf x l)) (HF(cons x l)).
unfold cons_hf.
intros.
case_eq (in_hf x (HF l)); intro.
 symmetry; apply cancel_repeat; trivial.
 reflexivity.
Qed.

Lemma In_hf_head_hf : forall x y l,
  Eq_hf x y ->
  In_hf x (HF (cons_hf y l)).
Proof.
intros.
rewrite cons_hf_cons.
apply In_hf_head; trivial.
Qed.

Lemma In_hf_tail_hf : forall x y l,
  In_hf x (HF l) ->
  In_hf x (HF (cons_hf y l)).
Proof.
intros.
rewrite cons_hf_cons.
apply In_hf_tail; trivial.
Qed.

Lemma In_hf_elim_hf : forall x y l,
  In_hf x (HF (cons_hf y l)) ->
  Eq_hf x y \/ In_hf x (HF l).
intros.
rewrite cons_hf_cons in H.
apply In_hf_elim; trivial.
Qed.


Lemma Eq_hf_cons_hf : forall x1 x2 l1 l2,
  Eq_hf x1 x2 ->
  Eq_hf (HF l1) (HF l2) ->
  Eq_hf (HF (cons_hf x1 l1)) (HF (cons_hf x2 l2)).
Proof.
intros.
do 2 rewrite cons_hf_cons.
apply Eq_hf_cons; trivial.
Qed.


Fixpoint app_hf (l1 l2:list hf) {struct l1} : list hf :=
  match l1 with 
    nil => l2
  | cons x l' => cons_hf x (app_hf l' l2)
  end.

Lemma In_app_hf_left : forall x l1 l2,
  In_hf x (HF l1) ->
  In_hf x (HF (app_hf l1 l2)).
Proof.
induction l1; simpl; intros.
 inversion H.

 elim In_hf_elim with (1:=H); intros.
  apply In_hf_head_hf; trivial.
  apply In_hf_tail_hf; auto.
Qed.

Lemma In_app_hf_right : forall x l1 l2,
  In_hf x (HF l2) ->
  In_hf x (HF (app_hf l1 l2)).
Proof.
induction l1; simpl; intros; auto.
 apply In_hf_tail_hf; auto.
Qed.

Lemma In_app_hf_elim : forall x l1 l2,
  In_hf x (HF (app_hf l1 l2)) ->
  In_hf x (HF l1) \/ In_hf x (HF l2).
induction l1; simpl; intros; auto.
elim In_hf_elim_hf with (1:=H); intros.
 left.
 apply In_hf_head; trivial.

 elim IHl1 with (1:=H0); intros; auto.
 left.
 apply In_hf_tail; trivial.
Qed.


Definition fold_set (X:Type) (f:hf->X->X) (x:hf) (acc:X) : X :=
  let fix F (l:list hf) : X :=
    match l with
      nil => acc
    | cons x l' => if in_hf x (HF l') then F l' else f x (F l')
    end in
  F (hf_elts x).


Lemma fold_set_unfold : forall X f x l acc,
  fold_set X f (HF(x::l)) acc =
  if in_hf x (HF l) then fold_set X f (HF l) acc
  else f x (fold_set X f (HF l) acc).
reflexivity.
Qed.

Lemma fold_set_ind : forall X (P:hf->X->Prop) f x acc,
  P (HF nil) acc ->
  (forall x' y acc, In_hf x' x -> In_hf x' y -> P y acc ->
   P (HF(x'::hf_elts y)) acc) ->
  (forall x' y acc, In_hf x' x -> ~ In_hf x' y -> P y acc ->
   P (HF(x'::hf_elts y)) (f x' acc)) ->
  P x (fold_set X f x acc).
Proof.
destruct x.
induction elts; simpl; intros; auto.
rewrite fold_set_unfold.
case_eq (in_hf a (HF elts)); intro.
 change elts with (hf_elts (HF elts)).
 apply H0; trivial.
  apply In_hf_head; reflexivity.

  simpl in IHelts; apply (IHelts acc); intros; trivial.
   apply H0; trivial.
   apply In_hf_tail; trivial.

   apply H1; trivial.
   apply In_hf_tail; trivial.

 change elts with (hf_elts (HF elts)).
 apply H1; trivial.
  apply In_hf_head; reflexivity.

  unfold In_hf; rewrite H2; discriminate.

  simpl in IHelts; apply (IHelts acc); intros; trivial.
   apply H0; trivial.
   apply In_hf_tail; trivial.

   apply H1; trivial.
   apply In_hf_tail; trivial.
Qed.

Fixpoint canonical (x:hf) : hf :=
  HF (fold_set _ (fun y cl => canonical y :: cl) x nil).

Lemma canonical_correct : forall x, Eq_hf (canonical x) x.
Proof.
intro.
elim x using hf_ind2; intros.
unfold canonical in |- *; fold canonical in |- *.
induction l; simpl in |- *; intros.
 compute; reflexivity.

 rewrite fold_set_unfold.
 case_eq (in_hf a (HF l)); intro.
  apply eq_hf_trans with (HF l); auto with *.
  symmetry; apply cancel_repeat; trivial.

  apply Eq_hf_cons; auto with *.
Qed.

Hint Resolve In_hf_head In_hf_head_hf In_hf_head_hf In_hf_tail_hf.

(** Notations *)

Notation "{ l }" := (HF l) (at level 0, l at level 99).

Notation EMPTY := {nil}.
Notation ONE := {EMPTY::nil}.
Notation TWO := {EMPTY::ONE::nil}.

Infix ":::" := cons_hf (at level 60, right associativity).
Infix "+++" := app_hf (at level 60, right associativity).

(* *)
Notation "x ∈ y" := (In_hf x y) (at level 60).
Notation "x == y" := (Eq_hf x y) (at level 70).

Notation morph1 := (Proper (Eq_hf ==> Eq_hf)).
Notation morph2 := (Proper (Eq_hf ==> Eq_hf ==> Eq_hf)).
Notation morph3 := (Proper (Eq_hf ==> Eq_hf ==> Eq_hf ==> Eq_hf)).

(** Set theoretical operators *)

Definition empty := HF nil.
Definition singl x := HF (x:::nil).
Definition pair x y := HF (x:::y:::nil).

Definition union (x:hf) :=
  HF (fold_set _ (fun y l => hf_elts y+++l) x nil).

Definition power (x:hf) :=
  HF (fold_set _
          (fun y pow p => pow p ++ pow (y::p)) x
           (fun p => HF (rev p) :: nil) nil).

Definition subset (x:hf) (P:hf->bool) :=
  HF (fold_set _ (fun y l => if P y then y :: l else l) x nil).

Definition repl (x:hf) (f:hf->hf) :=
  HF (map f (hf_elts x)).


Instance singl_morph : morph1 singl.
Proof.
unfold singl in |- *; do 2 red; intros.
apply Eq_hf_cons_hf; trivial.
reflexivity.
Qed.

Instance pair_morph : morph2 pair.
Proof.
unfold pair in |- *; do 3 red; intros.
repeat apply Eq_hf_cons_hf; trivial.
reflexivity.
Qed.

Definition eq_hf_fun (x:hf) (f1 f2:hf->hf) :=
  forall y1 y2, y1 ∈ x -> y1 == y2 -> f1 y1 == f2 y2.

Lemma eq_hf_fun_sym : forall x f1 f2,
  eq_hf_fun x f1 f2 -> eq_hf_fun x f2 f1.
Proof.
unfold eq_hf_fun in |- *; intros.
symmetry  in |- *.
apply H.
 apply in_hf_reg_l with y1; trivial.
 symmetry  in |- *; trivial.
Qed.

Lemma eq_hf_fun_trans : forall x f1 f2 f3,
   eq_hf_fun x f1 f2 -> eq_hf_fun x f2 f3 -> eq_hf_fun x f1 f3.
Proof.
unfold eq_hf_fun in |- *; intros.
transitivity (f2 y1); auto.
apply H; trivial.
reflexivity.
Qed.

Lemma eq_hf_fun_left : forall x f1 f2,
  eq_hf_fun x f1 f2 -> eq_hf_fun x f1 f1.
Proof.
unfold eq_hf_fun in |- *; intros.
transitivity (f2 y2); auto.
symmetry  in |- *.
apply H.
 apply in_hf_reg_l with y1; trivial.
 reflexivity.
Qed.

Definition hf_pred_morph x P :=
  forall y1 y2, y1 ∈ x -> y1 == y2 -> P y1 = true -> P y2 = true.

Definition eq_hf_pred (x:hf) (f1 f2:hf->bool) :=
  forall y1 y2, y1 ∈ x -> y1 == y2 -> f1 y1 = f2 y2.

(* *)

Lemma empty_elim : forall x, ~ x ∈ empty.
compute in |- *; intros;  discriminate.
Qed.

Lemma empty_ext : forall a, (forall x, ~ x ∈ a) -> a == empty.
intros.
apply Eq_hf_intro; red; intros.
 elim H with a0; trivial.
 elim empty_elim with a0; trivial.
Qed.

Lemma singl_intro : forall x y, x == y -> x ∈ singl y.
unfold singl in |- *; auto.
Qed.

Lemma singl_elim : forall x a, x ∈ singl a -> x == a.
unfold singl in |- *; intros.
elim In_hf_elim_hf with (1 := H); intros; auto.
discriminate H0.
Qed.

Lemma singl_ext :
  forall y x,
  x ∈ y ->
  (forall z, z ∈ y -> z == x) ->
  y == singl x.
Proof.
intros; apply Eq_hf_intro; red; intros.
 apply singl_intro; auto.
 apply in_hf_reg_l with x; trivial.
  symmetry  in |- *; apply singl_elim; trivial.
Qed.


Lemma pair_elim : forall x a b,
  x ∈ pair a b -> x == a \/ x == b.
intros.
unfold pair in H.
elim In_hf_elim_hf with (1 := H); intros; auto.
right.
elim In_hf_elim_hf with (1 := H0); intros; auto.
 discriminate H1.
Qed.

Lemma pair_intro1 : forall x a b, x == a -> x ∈ pair a b.
Proof.
unfold pair;auto.
Qed.

Lemma pair_intro2 : forall x a b, x == b -> x ∈ pair a b.
Proof.
unfold pair;auto.
Qed.


Lemma union_intro : forall x y z, x ∈ y -> y ∈ z -> x ∈ union z.
Proof.
intros x y z H.
unfold union.
pattern z, (fold_set _ (fun y0 l => hf_elts y0 +++ l) z nil).
apply fold_set_ind; intros.
 discriminate.

 apply H2.
 rewrite cancel_repeat in H3; auto.

 elim In_hf_elim with (1:=H3); intros.
  apply In_app_hf_left.
  rewrite hf_elts_ext.
  rewrite <- H4; trivial.

  apply In_app_hf_right.
  rewrite hf_elts_ext in H4.
  auto.
Qed.

Lemma union_elim : forall x z, x ∈ union z -> exists2 y, x ∈ y & y ∈ z.
unfold union.
intros x z.
pattern z, (fold_set _ (fun y l => hf_elts y +++ l) z nil).
apply fold_set_ind; intros.
 discriminate.

 destruct H1; trivial.
 exists x0; trivial.
 rewrite cancel_repeat; auto.

 elim In_app_hf_elim with (1:=H2); intros.
  rewrite hf_elts_ext in H3.
  exists x'; trivial.
  apply In_hf_head; reflexivity.

  elim H1 with (1:=H3); intros.
  exists x0; trivial.
  apply In_hf_tail.
  rewrite hf_elts_ext; trivial.
Qed.

Lemma union_ext :
  forall u z,
  (forall x y, x ∈ y -> y ∈ z -> x ∈ u) ->
  (forall x, x ∈ u -> exists2 y, x ∈ y & y ∈ z) ->
  u == union z.
intros.
apply Eq_hf_intro; red; intros.
 elim H0 with (1:=H1); intros.
 apply union_intro with x; trivial.

 elim union_elim with (1:=H1); intros.
 eauto.
Qed.

Instance union_morph : morph1 union.
do 2 red; intros.
apply union_ext; intros.
 apply union_intro with y0; trivial.
 rewrite H; trivial.

 elim union_elim with (1 := H0); intros.
 exists x1; trivial.
 rewrite <- H; trivial.
Qed.


Lemma union_singl : forall x, union (singl x) == x.
intros.
symmetry; apply union_ext; intros.
 apply singl_elim in H0.
 rewrite <- H0; trivial.

 exists x; trivial.
 apply singl_intro; reflexivity.
Qed.


(** power properties *)

Lemma power_intro :
  forall x y, Incl_hf x y -> x ∈ power y.
unfold power.
set (g := fun y0 (pow:list hf ->list hf) p => pow p ++ pow (y0 :: p)).
set (h := fun p => HF(rev p) :: nil).
intros x y.
assert (forall x l, Incl_hf (HF (rev l)) x ->
 Incl_hf x (HF(rev l ++ hf_elts y)) ->
 x ∈ HF(fold_set _ g y h l)).
clear x.
pattern y, (fold_set _ g y h).
apply fold_set_ind; intros.
 unfold h; simpl.
 apply In_hf_head.
 apply Eq_hf_intro; trivial.
 red; intros.
 elim In_app_elim with (1:=H0 _ H1); intros; auto.
 elim empty_elim with a; trivial.

 apply H1; trivial.
 red; intros.
 elim In_app_elim with (1:=H3 _ H4); intros.
  apply In_app_left; trivial.

  apply In_app_right.
  rewrite hf_elts_ext in H5.
  elim In_hf_elim with (1:=H5); intros; trivial.
  rewrite H6; trivial.

 unfold g; simpl.
 case_eq (in_hf x' x); intros.
  apply In_app_right.
  apply H1.
   red; simpl; intros.
   elim In_app_elim with (1:=H5); intros; auto.
   elim In_hf_elim with (1:=H6); simpl; intros.
    rewrite H7; trivial.
    elim empty_elim with a; trivial.

  simpl.
  rewrite app_ass; simpl.
  trivial.

 apply In_app_left.
 apply H1; trivial.
 red; intros.
 elim In_app_elim with (1:=H3 _ H5); simpl; intros.
  apply In_app_left; trivial.

  apply In_app_right.
  elim In_hf_elim with (1:=H6); intros; auto.
  rewrite H7 in H5; unfold In_hf in H5; rewrite H5 in H4; discriminate.  

intro; apply H; simpl.
 red; intros.
 elim empty_elim with a; trivial.

 rewrite hf_elts_ext; trivial.
Qed.


Lemma power_elim : forall x y z, x ∈ power y -> z ∈ x -> z ∈ y.
unfold power.
set (g := fun y0 (pow:list hf ->list hf) p => pow p ++ pow (y0 :: p)).
set (h := fun p => HF(rev p) :: nil).
intros x y.
assert (forall l,
 x ∈ HF(fold_set _ g y h l) ->
 forall z, z ∈ x -> ~ z ∈ (HF(rev l)) -> z ∈ y).
 pattern y, (fold_set _ g y h).
 apply fold_set_ind; intros.
  unfold h in H.
  elim H1.
  apply in_hf_reg_r with (2:=H0).
  apply singl_elim.
  assumption.

 apply In_hf_tail.
 rewrite hf_elts_ext.
 eauto.

 unfold g in H2.
 elim In_app_elim with (1:=H2);intros.
  apply In_hf_tail; rewrite hf_elts_ext.
  apply H1 with l; trivial.

  case_eq (eq_hf z x'); intro.
   apply In_hf_head; trivial.

   apply In_hf_tail; rewrite hf_elts_ext.
   apply H1 with (1:=H5); trivial.
   simpl; red; intros; apply H4.
   elim In_app_elim with (1:=H7); intros; trivial.
   replace (eq_hf z x') with true in H6; try discriminate.
   symmetry; apply singl_elim.
   assumption.

intros.
apply H with (l:=@nil hf); trivial.
red; intros; discriminate.
Qed.

Lemma power_ext :
  forall p a,
  (forall x, (forall y, y ∈ x -> y ∈ a) -> x ∈ p) ->
  (forall x y, x ∈ p -> y ∈ x -> y ∈ a) ->
  p == power a.
intros.
apply Eq_hf_intro; red; intros.
 apply power_intro; red; intros; eauto.

 apply H; intros.
 eapply power_elim; eauto.
Qed.

Lemma power_morph : morph1 power.
do 2 red; intros.
apply power_ext; intros.
 apply power_intro.
 rewrite H; trivial.

 rewrite <- H.
 apply power_elim with (1 := H0); trivial.
Qed.


Lemma subset_intro_gen : forall a (P:hf->bool) x,
  x ∈ a -> (forall x', x==x' -> P x' = true) -> x ∈ subset a P.
unfold subset.
intros a P x in_a in_P; revert in_a.
set (g := fun y l => if P y then y :: l else l).
pattern a, (fold_set _ g a nil).
apply fold_set_ind; simpl; intros; auto.
 apply H1; trivial.
 rewrite cancel_repeat in in_a; auto.

 unfold g.
 elim In_hf_elim with (1:=in_a);intros.
  rewrite in_P; trivial.
  apply In_hf_head; trivial.

  destruct (P x'); auto.
  apply In_hf_tail; auto.
Qed.

Lemma subset_intro : forall a (P:hf->bool) x,
  hf_pred_morph a P ->
  x ∈ a -> P x = true -> x ∈ subset a P.
intros.
apply subset_intro_gen; trivial.
intros.
red in H.
apply H with (2:=H2); trivial.
Qed.

Lemma subset_elim1 : forall a (P:hf->bool) x, x ∈ subset a P -> x ∈ a.
unfold subset.
intros a P x.
set (g := fun y l => if P y then y :: l else l).
pattern a, (fold_set _ g a nil).
apply fold_set_ind; simpl; intros; auto.

rewrite cancel_repeat; auto.

unfold g in H2.
destruct (P x').
 elim In_hf_elim with (1:=H2); intros.
  apply In_hf_head; trivial.
  apply In_hf_tail; auto.

 apply In_hf_tail; auto.
Qed.

Lemma subset_elim2_gen : forall a (P:hf->bool) x,
  x ∈ subset a P ->
  exists2 x', x==x' & P x' = true.
unfold subset.
intros a P x.
set (g := fun y l => if P y then y :: l else l).
pattern a, (fold_set _ g a nil).
apply fold_set_ind; simpl; intros; auto.
 discriminate.

 unfold g in H2.
 case_eq (P x'); intro.
  rewrite H3 in H2.
  elim In_hf_elim with (1:=H2); intros; auto.
  exists x'; trivial.

  rewrite H3 in H2; auto.
Qed.

Lemma subset_elim2 : forall a (P:hf->bool) x,
  hf_pred_morph a P ->
  x ∈ subset a P ->
  P x = true.
unfold subset.
intros a P x Pmorph.
set (g := fun y l => if P y then y :: l else l).
pattern a, (fold_set _ g a nil).
apply fold_set_ind; simpl; intros; auto.
 discriminate.

 unfold g in H2.
 case_eq (P x'); intro.
  rewrite H3 in H2.
  elim In_hf_elim with (1:=H2); intros; auto.
  apply Pmorph with x'; auto.
  symmetry; trivial.

  rewrite H3 in H2; auto.
Qed.

Lemma subset_ext :
  forall s a (P:hf->bool),
  hf_pred_morph a P ->
  (forall x, x ∈ a -> P x = true -> x ∈ s) ->
  (forall x, x ∈ s -> x ∈ a) ->
  (forall x, x ∈ s -> P x = true) ->
  s == subset a P.
intros.
apply Eq_hf_intro; red; intros.
 apply subset_intro; auto.

 apply H0.
  apply subset_elim1 with (1:=H3); trivial.
  apply subset_elim2 with (2:=H3); trivial.
Qed.

Lemma subset_morph_ext : forall x1 x2 y1 y2,
  x1 == x2 -> eq_hf_pred x1 y1 y2 -> subset x1 y1 == subset x2 y2.
intros.
assert (hf_pred_morph x1 y1).
 red; intros.
 red in H0.
 rewrite H0 with y3 y3; trivial.
  rewrite <- H0 with y0 y3; trivial.
  apply in_hf_reg_l with y0; auto.
  reflexivity.
assert (hf_pred_morph x2 y2).
 red; intros.
 red in H0.
 rewrite <- H0 with y0 y3; trivial.
  rewrite H0 with y0 y0; trivial.
   apply in_hf_reg_r with x2; auto.
   symmetry; trivial.
   reflexivity.
  apply in_hf_reg_r with x2; auto.
  symmetry; trivial.
apply subset_ext; intros; trivial.
 apply subset_intro; trivial.
  apply in_hf_reg_r with x2; auto.
  symmetry; trivial.

  rewrite H0 with x x; trivial.
   apply in_hf_reg_r with x2; auto.
   symmetry; trivial.

   reflexivity.

 apply in_hf_reg_r with x1; auto.
 apply subset_elim1 with (1:=H3).

 rewrite <- H0 with x x.
  apply subset_elim2 with (2:=H3); trivial.

  apply subset_elim1 with (1:=H3).

  reflexivity.
Qed.

Lemma subset_empty1 : forall P, subset empty P == empty.
intros.
apply empty_ext; red; intros.
apply subset_elim1 in H.
elim empty_elim with x; trivial.
Qed.

Lemma subset_singl : forall x a (P:hf->bool),
  x ∈ a ->
  P x = true ->
  (forall x', x' ∈ a -> (x==x' <-> P x' = true)) ->
  subset a P == singl x.
intros.
apply singl_ext; intros.
 apply subset_intro_gen; trivial; intros.
 apply -> H1; trivial.
 rewrite <- H2; trivial.

 elim subset_elim2_gen with (1:=H2); intros.
 transitivity x0; trivial.
 symmetry; apply <- H1; trivial.
 rewrite <- H3.
 apply subset_elim1 in H2; trivial.
Qed.


(** replacement properties *)

Lemma repl_intro : forall a f y x,
  eq_hf_fun a f f ->
  y ∈ a -> x == f y -> x ∈ repl a f.
Proof.
unfold repl.
intros a f y x.
destruct a as (a); simpl.
elim a; simpl; intros.
 elim empty_elim with y; trivial.

 elim In_hf_elim with (1:=H1); intros.
  apply In_hf_head.
  rewrite H2; auto.

  apply In_hf_tail.
  apply H; trivial.
  red; intros; apply H0; trivial.
  apply In_hf_tail; trivial.
Qed.

Lemma repl_elim : forall a f x,
  eq_hf_fun a f f ->
  x ∈ repl a f -> exists2 y, y ∈ a & x == f y.
Proof.
unfold repl.
intros a f x.
destruct a as (a); elim a; simpl; intros.
 elim empty_elim with x; trivial.

 elim In_hf_elim with (1:=H1); intros.
  exists a0; trivial.
  apply In_hf_head; reflexivity.

  elim H with (2:=H2); intros.
   exists x0; trivial.
   apply In_hf_tail; trivial.

   red; intros; apply H0; trivial.
   apply In_hf_tail; trivial.
Qed.

Lemma repl_ext : forall x a f,
  eq_hf_fun a f f ->
  (forall y, y ∈ a -> f y ∈ x) ->
  (forall y, y ∈ x -> exists2 z, z ∈ a & y == f z) ->  
  x == repl a f.
intros.
apply Eq_hf_intro; red; intros.
 elim H1 with (1:=H2); intros.
 apply repl_intro with x0 ;trivial.

 elim repl_elim with (2:=H2); intros; trivial.
 apply in_hf_reg_l with (f x0); auto.
 symmetry; trivial.
Qed.


Lemma repl_morph :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_hf_fun x1 f1 f2 ->
  repl x1 f1 == repl x2 f2.
unfold eq_hf_fun, repl.
intros.
apply eq_hf_intro; simpl; intros.
 elim in_map_inv with (1 := H1); intros.
   elim eq_hf_elim1 with (1 := H) (2 := H2); intros.
   exists (f2 x0).
  apply in_map; trivial.
   rewrite H3.
    apply H0; auto.
    apply in_hf_intro with x; trivial; reflexivity.
 elim in_map_inv with (1 := H1); intros.
   elim eq_hf_elim2 with (1 := H) (2 := H2); intros.
   exists (f1 x0).
  apply in_map; trivial.
   rewrite H3.
    apply H0; auto.
    apply in_hf_intro with x0; trivial; reflexivity.
Qed.

(** bool *)
Definition hf_false := empty.
Definition hf_true := singl hf_false.
Definition hf_bool := pair hf_false hf_true.

(** couples *)
Definition couple x y := pair (singl x) (pair x y).
Definition fst p := union (subset (union p) (fun x => in_hf (singl x) p)).
Definition snd p :=
  union (subset (union p) (fun y => eq_hf (pair (fst p) y) (union p))).


Lemma union_couple_eq : forall a b, union (couple a b) == pair a b. 
Proof.
intros; unfold couple in |- *; symmetry  in |- *.
apply union_ext; intros.
 elim pair_elim with (1 := H0); intro y_eq;  rewrite y_eq in H; trivial.
 apply pair_intro1.
 apply singl_elim; trivial.

 elim pair_elim with (1 := H); intro.
  exists (singl a).
   apply singl_intro; auto.
   apply pair_intro1; reflexivity.

  exists (pair a b).
   apply pair_intro2; trivial.
   apply pair_intro2; reflexivity.
Qed.

Instance couple_morph : morph2 couple.
unfold couple; do 3 red; intros.
rewrite H; rewrite H0; reflexivity.
Qed.

Instance fst_morph : morph1 fst.
unfold fst; do 2 red; intros.
apply union_morph.
apply subset_morph_ext.
 apply union_morph; trivial.

 red in |- *; intros.
 rewrite H; rewrite H1; trivial.
Qed.

Lemma fst_def : forall x y, fst (couple x y) == x.
unfold fst.
intros.
assert (hf_pred_morph (union (couple x y))
         (fun x0 => in_hf (singl x0) (couple x y))).
 red; intros.
 change (singl y2 ∈ couple x y).
 rewrite <- H0; trivial.
symmetry.
apply union_ext; intros.
 apply in_hf_reg_r with y0; trivial.
 specialize subset_elim2 with (1:=H) (2:=H1); clear H1; intro.
 unfold couple in H1.
 elim pair_elim with (1:=H1); clear H1; intros.
  apply singl_elim.
  apply in_hf_reg_r with (singl y0); auto.
  apply singl_intro; reflexivity.

  symmetry; apply singl_elim.
  apply in_hf_reg_r with (pair x y).
   symmetry; trivial.
   apply pair_intro1; reflexivity.

 exists x; trivial.
 apply subset_intro; trivial.
  apply union_intro with (singl x).
   apply singl_intro; reflexivity.
   unfold couple; apply pair_intro1; reflexivity.

  unfold couple; apply pair_intro1; reflexivity.
Qed.

Instance snd_morph : morph1 snd.
unfold snd; do 2 red; intros.
apply union_morph.
apply subset_morph_ext.
 apply union_morph; trivial.

 red in |- *; intros.
 rewrite H; rewrite H1; trivial.
Qed.

Lemma snd_def : forall x y, snd (couple x y) == y.
intros; unfold snd in |- *.
assert (hf_pred_morph (union (couple x y))
    (fun y0 => eq_hf (pair (fst (couple x y)) y0) (union (couple x y)))).
 red; intros.
 change (pair (fst (couple x y)) y2 == union (couple x y)).
 rewrite <- H0; trivial.
transitivity (union (singl y)).
 apply union_morph.
   apply singl_ext; intros.
  apply subset_intro; trivial.
    rewrite union_couple_eq.
    apply pair_intro2; reflexivity.

    rewrite fst_def.
    apply eq_hf_sym.
    apply union_couple_eq.

  specialize subset_elim2 with (1 := H) (2:=H0); intro.
  generalize H1.
  rewrite fst_def.
  clear H0; intro.
  rewrite union_couple_eq in H0.
  elim pair_elim with z x y; intros; trivial.
   rewrite H2 in H0 |- *; clear H2.
   symmetry.
   elim pair_elim with y x x; intros; trivial.
   apply in_hf_reg_r with (pair x y).
    symmetry; trivial.
    apply pair_intro2; reflexivity.

  apply in_hf_reg_r with (pair x z); trivial.
  apply pair_intro2; reflexivity.

 symmetry; apply union_ext; intros.
  apply in_hf_reg_r with y0; trivial.
  apply singl_elim; trivial.

  exists y; trivial.
  apply singl_intro; reflexivity.
Qed.

Lemma snd_ext : forall p x y,
 p == couple x y ->
 y == snd p.
intros.
rewrite H; rewrite snd_def; reflexivity.
Qed.

(* example *)

(*
Definition hf_negb :=
 lam hf_bool (fun b => if eq_hf b hf_true then hf_false else hf_true).

Eval compute in (eq_hf hf_true (app hf_negb hf_false)).
Eval compute in (eq_hf hf_false (app hf_negb hf_true)).
Eval compute in
 (eq_hf hf_negb {couple hf_true hf_false:::couple hf_false hf_true ::: nil}).
*)

(** regularity *)

Lemma raw_choose_elt : forall x, {y | In y (hf_elts x)}+{x==empty}.
intros ([|h l]); simpl; [right;compute;reflexivity|left;exists h; auto].
Qed.

Lemma choose_elt : forall x, {y | y ∈ x}+{x==empty}.
intros ([|h l]); [right;compute;reflexivity|left;exists h].
apply in_hf_intro with h; simpl; auto; reflexivity.
Qed.

Lemma regularity_ax: forall a a0, a0 ∈ a ->
    exists2 b, b ∈ a & ~(exists2 c, c ∈ a & c ∈ b).
induction a0 using hf_ind2; intros.
set (a0 := HF l) in *.
pose (A := subset a0 (fun y => in_hf y a)).
destruct (choose_elt A).
 destruct s.
 subst A.
 specialize subset_elim1 with (1:=i); intro.
 apply in_hf_elim in H1.
 destruct H1.
 rewrite H2 in i; clear H2 x.
 assert (x0 ∈ a).
  apply subset_elim2 with (2:=i).
  red; intros.
  rewrite H3 in H4; trivial.
 eauto.

 exists a0; trivial.
 red; destruct 1.
 assert (x ∈ A).
  apply subset_intro; trivial.
  red; intros.
  rewrite H4 in H5; trivial.
 rewrite e in H3; elim empty_elim with (1:=H3).
Qed.
