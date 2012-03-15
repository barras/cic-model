
Require Export ZF.

(* natural numbers *)

Definition zero := empty.
Definition succ n := union2 n (singl n).

Instance succ_morph : morph1 succ.
Proof.
unfold succ; do 2 red; intros; rewrite H; reflexivity.
Qed.

Definition pred := union.

Instance pred_morph : morph1 pred.
exact union_morph.
Qed.

Lemma discr : forall k, ~ succ k == zero.
Proof.
red; intros.
elim (empty_ax k).
rewrite <- H.
unfold succ.
apply union2_intro2.
apply singl_intro.
Qed.

Definition lt := in_set.
Definition le m n := lt m (succ n).

Instance lt_morph : Proper (eq_set ==> eq_set ==> iff) lt.
exact in_set_morph.
Qed.

Instance le_morph : Proper (eq_set ==> eq_set ==> iff) le.
Proof.
unfold le; do 3 red; intros; rewrite H; rewrite H0; reflexivity.
Qed.


Lemma le_case : forall m n, le m n -> m == n \/ lt m n.
Proof.
unfold le, lt, succ in |- *; intros.
elim union2_elim with (1 := H); intros; auto.
left.
apply singl_elim; trivial.
Qed.

Lemma succ_intro1 : forall x n, x == n -> lt x (succ n).
red; intros.
unfold succ.
apply union2_intro2.
apply singl_intro_eq.
trivial.
Qed.

Lemma succ_intro2 : forall x n, lt x n -> lt x (succ n).
red; intros.
unfold succ.
apply union2_intro1.
trivial.
Qed.

Lemma lt_is_le : forall x y, lt x y -> le x y.
Proof succ_intro2.

Lemma le_refl : forall n, le n n.
intros.
apply succ_intro1; reflexivity.
Qed.
Hint Resolve lt_is_le le_refl.


(* building the set of natural numbers *)

Definition is_nat n : Prop :=
  forall nat:set,
  zero \in nat ->
  (forall k, k \in nat -> succ k \in nat) ->
  n \in nat.

Lemma is_nat_zero : is_nat zero.
Proof.
red in |- *; intros; auto.
Qed.

Lemma is_nat_succ : forall n, is_nat n -> is_nat (succ n).
Proof.
unfold is_nat in |- *; intros.
apply H1.
apply H; auto.
Qed.

Definition N := subset infinite is_nat.

Lemma zero_typ: zero \in N.
Proof.
unfold N in |- *.
apply subset_intro.
 unfold zero in |- *; apply infinity_ax1.
 exact is_nat_zero.
Qed.

Lemma succ_typ: forall n, n \in N -> succ n \in N.
Proof.
unfold N; intros.
apply subset_intro.
 unfold succ, union2, singl; apply infinity_ax2;
  apply subset_elim1 with is_nat; trivial.
 apply is_nat_succ.
  elim subset_elim2 with (1:=H); intros; trivial.
  unfold is_nat.
  intros; rewrite H0.
  auto.
Qed.

Lemma N_ind : forall (P: set->Prop),
  (forall n n', n \in N -> n == n' -> P n -> P n') ->
  P zero ->
  (forall n, n \in N -> P n -> P (succ n)) ->
  forall n, n \in N -> P n.
Proof.
intros.
assert (n \in subset N P).
 unfold N in H2.
 elim subset_elim2 with (1 := H2); intros.
 rewrite H3.
 red in H4; apply H4; intros; auto.
  apply subset_intro; trivial.
  apply zero_typ.

  apply subset_intro.
   apply succ_typ.
   apply subset_elim1 with (1 := H5).

   apply H1.
    apply subset_elim1 with (1 := H5).

    elim subset_elim2 with (1 := H5); intros.
    apply H with x0; auto.
    rewrite <- H6.
    apply subset_elim1 with (1 := H5).
    symmetry; trivial.

 elim subset_elim2 with (1 := H3); intros.
 apply H with x; auto.
 rewrite <- H4; trivial.
 symmetry; trivial.
Qed.


Lemma lt_trans : forall m n p, p \in N -> lt m n -> lt n p -> lt m p.
Proof.
intros m n p ty_p.
unfold lt in |- *.
elim ty_p using N_ind; intros.
 rewrite <- H0 in H3|-*; auto.
 elim empty_ax with (1 := H0).
 elim le_case with (1 := H2); intros.
   rewrite <- H3; trivial.
    unfold succ in |- *.
    apply union2_intro1; trivial.
  unfold succ in |- *.
    apply union2_intro1; auto.
Qed.

Lemma pred_succ_eq : forall n, n \in N -> pred (succ n) == n.
Proof.
unfold pred, succ in |- *; intros.
apply eq_intro; intros.
 elim union_elim with (1 := H0); intros.
   elim union2_elim with (1 := H2); intros.
  apply lt_trans with x; trivial.
   rewrite (singl_elim _ _ H3) in H1.
    trivial.
 apply union_intro with n; trivial.
   apply union2_intro2.
   apply singl_intro.
Qed.

Lemma pred_typ : forall n, n \in N -> pred n \in N.
Proof.
intros.
elim H using N_ind; intros.
 rewrite <- H1; trivial.

 unfold pred, zero in |- *.
 rewrite union_empty_eq.
 exact zero_typ.

 rewrite pred_succ_eq; trivial.
Qed.

Lemma succ_inj : forall m n, m \in N -> n \in N -> succ m == succ n -> m == n.
Proof.
intros.
 rewrite <- (pred_succ_eq _ H).
 rewrite <- (pred_succ_eq _ H0).
 rewrite H1; reflexivity.
Qed.

(* max *)

Definition max := union2.

Instance max_morph : morph2 max.
exact union2_morph.
Qed.

Lemma lt_0_succ : forall n, n \in N -> lt zero (succ n).
intros.
elim H using N_ind; intros.
 rewrite <- H1; trivial.

 apply succ_intro1; reflexivity.

 apply lt_trans with (succ n0); trivial.
  apply succ_typ; apply succ_typ; trivial.
  apply succ_intro1; reflexivity.
Qed.

Lemma lt_mono : forall m n, m \in N -> n \in N -> 
  lt m n -> lt (succ m) (succ n).
intros m n Hm Hn.
elim Hn using N_ind; intros. rewrite H0 in H1; auto.
 elim empty_ax with m; trivial.
 elim le_case with (1:=H1); intros.
  rewrite H2; apply succ_intro1; reflexivity.
  apply succ_intro2; auto.
Qed.


Lemma le_total : forall m, m \in N -> forall n, n \in N ->
  lt m n \/ m == n \/ lt n m.
intros m Hm.
elim Hm using N_ind; intros. rewrite <- H0; auto.
 elim H using N_ind; intros. rewrite <- H1; auto.
  right; left; reflexivity.

  left.
  apply lt_0_succ; trivial.

 elim H1 using N_ind; intros. rewrite <- H3; auto.
  right;right.
  apply lt_0_succ; trivial.

  elim H0 with n1; intros; auto.
   left.
   apply lt_mono; trivial.

   right.
   destruct H4.
    left; rewrite H4; reflexivity.

    right.
    apply lt_mono; trivial.
Qed.

Lemma max_sym : forall m n, max m n == max n m.
unfold max; intros.
apply union2_commut.
Qed.


Lemma max_eq : forall m n, m == n -> max m n == m.
unfold max; intros.
rewrite H.
apply eq_intro; intros.
 elim union2_elim with (1:=H0); auto.
 apply union2_intro1; trivial.
Qed.

Lemma max_lt : forall m n, n \in N -> lt m n -> max m n == n.
intros m n H.
generalize m; clear m.
elim H using N_ind; intros.
 unfold max; rewrite <- H1 in H3|-*; auto.

 elim empty_ax with m; trivial.

 elim le_case with (1:=H2); intros.
  unfold max; rewrite H3.
  apply eq_intro; intros.
   elim union2_elim with (1:=H4); intros; auto.
   apply succ_intro2; trivial.

   apply union2_intro2; trivial.

 unfold max.
 apply eq_intro; intros.
  elim union2_elim with (1:=H4); intros; auto.
  rewrite <- (H1 _ H3).
  apply succ_intro2.
  apply union2_intro1; trivial.

  apply union2_intro2; trivial.
Qed.


Lemma max_typ : forall m n, m \in N -> n \in N -> max m n \in N.
intros.
elim le_total with m n; trivial; intros.
 rewrite (max_lt m n); trivial.

 destruct H1.
  rewrite H1; rewrite max_eq; trivial; reflexivity.

  rewrite (max_sym m n).
  rewrite (max_lt n m); trivial.
Qed.



(* nat -> set *)
Fixpoint nat2set (n:nat) : set :=
  match n with
  | 0 => zero
  | S k => succ (nat2set k)
  end.

Lemma nat2set_typ : forall n, nat2set n \in N.
induction n; simpl.
 apply zero_typ.
 apply succ_typ; trivial.
Qed.

Lemma nat2set_inj : forall n m, nat2set n == nat2set m -> n = m.
induction n; destruct m; simpl; intros; trivial.
 elim (discr (nat2set m)); symmetry; trivial.

 elim (discr (nat2set n)); trivial.

 replace m with n; auto.
 apply IHn.
 apply succ_inj; trivial; apply nat2set_typ.
Qed.

Lemma nat2set_reflect : forall x, x \in N -> exists n, x == nat2set n.
intros.
elim H using N_ind; intros.
 destruct H2.
 exists x0.
 rewrite <- H1; trivial.

 exists 0; reflexivity.

 destruct H1.
 exists (S x0); rewrite H1; reflexivity.
Qed.
