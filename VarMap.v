
Require Import Setoid Morphisms.
Require Import Omega.

Module Type Eqv.
  Parameter Inline t : Type.
  Parameter Inline eq : t -> t -> Prop.
  Parameter eq_equiv : Equivalence eq.
  Existing Instance eq_equiv.
End Eqv.

Module Make (X:Eqv).
  Import X.

Definition map := nat -> t.
Definition eq_map : relation map := (pointwise_relation nat eq).

Definition nil (x:t) : map := fun _ => x.

Definition cons (x:t) (i:map) : map :=
  fun k => match k with
  | 0 => x
  | S n => i n
  end.
Definition shift (n:nat) (i:map) : map := fun k => i (n+k).

Definition lams n (f:map -> map) (i:map) : map :=
  fun k => if le_gt_dec n k then f (shift n i) (k-n) else i k.

Instance cons_morph : Proper (eq ==> eq_map ==> eq_map) cons.
do 5 red; intros.
destruct a; simpl; trivial.
Qed.
Instance cons_morph' :
  Proper (eq ==> eq_map ==> @Logic.eq _ ==> eq) cons.
do 4 red; intros.
subst y1; destruct x1; simpl; trivial.
Qed.

Instance shift_morph : Proper (@Logic.eq _ ==> eq_map ==> eq_map) shift.
do 5 red; intros.
subst y.
unfold shift; apply H0.
Qed.

Instance lams_morph :
  Proper (@Logic.eq _ ==> (eq_map ==> eq_map) ==> eq_map ==> eq_map) lams.
do 6 red; intros.
subst y.
unfold lams.
destruct (le_gt_dec x a); eauto.
apply H0.
rewrite H1.
reflexivity.
Qed.

Lemma cons_ext (x:t) i i' :
  eq x (i' 0) ->
  eq_map i (shift 1 i') ->
  eq_map (cons x i) i'.
do 2 red; intros.
destruct a; simpl; auto.
apply H0.
Qed.

Lemma shift0 i : eq_map (shift 0 i) i.
do 2 red; reflexivity.
Qed.

Lemma shift_split m n i :
  eq_map (shift (m+n) i) (shift n (shift m i)).
intros k.
unfold shift; simpl.
rewrite plus_assoc; reflexivity.
Qed.

Lemma shiftS_split n i :
  eq_map (shift (S n) i) (shift n (shift 1 i)).
do 2 red; unfold shift; intros.
replace (1+(n+a)) with (1+n+a); simpl; auto with *.
Qed.

Lemma shift_cons x i :
  eq_map (shift 1 (cons x i)) i.
do 2 red; intros.
reflexivity.
Qed.

Lemma shiftS_cons n x i :
  eq_map (shift (S n) (cons x i)) (shift n i).
rewrite shiftS_split.
rewrite shift_cons.
reflexivity.
Qed.

Lemma lams_split k k' f i :
  Proper (eq_map ==> eq_map) f -> 
  eq_map (lams (k+k') f i) (lams k (lams k' f) i).
intros fm n; unfold lams; simpl.
destruct (le_gt_dec k n).
 destruct (le_gt_dec k' (n-k)); destruct (le_gt_dec (k+k') n); try (exfalso; omega).
  replace (n-k-k') with (n-(k+k')) by omega.
  apply fm.
  rewrite shift_split; reflexivity.

  unfold shift; simpl.
  replace (k+(n-k)) with n by omega; reflexivity.

 destruct (le_gt_dec (k+k') n).
  exfalso; omega.
 reflexivity.
Qed.

Lemma lams_bv m f i k :
  k < m -> eq (lams m f i k) (i k).
unfold lams; intros.
destruct (le_gt_dec m k).
 apply False_ind; omega.
 reflexivity.
Qed.

Lemma lams_shift : forall m f i,
  eq_map (shift m (lams m f i)) (f (shift m i)).
unfold lams, shift; do 2 red; intros.
destruct (le_gt_dec m (m+a)).
 replace (m+a-m) with a by omega.
 reflexivity.
apply False_ind; omega.
Qed.

Lemma lams0 f i : eq_map (lams 0 f i) (f i).
intros.
rewrite <- (shift0 (lams 0 f i)).
rewrite lams_shift.
reflexivity.
Qed.


Lemma shift_lams k f i :
  eq_map (shift 1 (lams (S k) f i)) (lams k f (shift 1 i)).
do 2 red; unfold lams, shift; simpl; intros.
destruct (le_gt_dec k a); simpl; reflexivity.
Qed.

Lemma cons_lams k f i x :
  Proper (eq_map ==> eq_map) f ->
  eq_map (cons x (lams k f i)) (lams (S k) f (cons x i)).
intros.
apply cons_ext; simpl.
 rewrite lams_bv; unfold cons; simpl; auto with *.

 rewrite shift_lams.
 rewrite shift_cons; reflexivity.
Qed.

End Make.

