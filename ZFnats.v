
Require Export ZF.

(** Natural numbers *)

Definition zero := empty.
Definition succ n := n ∪ singl n.

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
Infix "<" := lt.
Infix "<=" := le.

Instance lt_morph : Proper (eq_set ==> eq_set ==> iff) lt.
exact in_set_morph.
Qed.

Instance le_morph : Proper (eq_set ==> eq_set ==> iff) le.
Proof.
unfold le; do 3 red; intros; rewrite H; rewrite H0; reflexivity.
Qed.


Lemma le_case : forall m n, m <= n -> m == n \/ m < n.
Proof.
unfold le, lt, succ in |- *; intros.
elim union2_elim with (1 := H); intros; auto.
left.
apply singl_elim; trivial.
Qed.

Lemma succ_intro1 : forall x n, x == n -> x < succ n.
red; intros.
unfold succ.
apply union2_intro2.
apply singl_intro_eq.
trivial.
Qed.

Lemma succ_intro2 : forall x n, x < n -> x < succ n.
red; intros.
unfold succ.
apply union2_intro1.
trivial.
Qed.

Lemma lt_is_le : forall x y, x < y -> x <= y.
Proof succ_intro2.

Lemma le_refl : forall n, n <= n.
intros.
apply succ_intro1; reflexivity.
Qed.
Hint Resolve lt_is_le le_refl.


(* building the set of natural numbers *)

Definition is_nat n : Prop :=
  forall nat:set,
  zero ∈ nat ->
  (forall k, k ∈ nat -> succ k ∈ nat) ->
  n ∈ nat.

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

Lemma zero_typ: zero ∈ N.
Proof.
unfold N in |- *.
apply subset_intro.
 unfold zero in |- *; apply infinity_ax1.
 exact is_nat_zero.
Qed.

Lemma succ_typ: forall n, n ∈ N -> succ n ∈ N.
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
  (forall n n', n ∈ N -> n == n' -> P n -> P n') ->
  P zero ->
  (forall n, n ∈ N -> P n -> P (succ n)) ->
  forall n, n ∈ N -> P n.
Proof.
intros.
assert (n ∈ subset N P).
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


Lemma lt_trans : forall m n p, p ∈ N -> m < n -> n < p -> m < p.
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

Lemma pred_succ_eq : forall n, n ∈ N -> pred (succ n) == n.
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

Lemma pred_typ : forall n, n ∈ N -> pred n ∈ N.
Proof.
intros.
elim H using N_ind; intros.
 rewrite <- H1; trivial.

 unfold pred, zero in |- *.
 rewrite union_empty_eq.
 exact zero_typ.

 rewrite pred_succ_eq; trivial.
Qed.

Lemma succ_inj : forall m n, m ∈ N -> n ∈ N -> succ m == succ n -> m == n.
Proof.
intros.
 rewrite <- (pred_succ_eq _ H).
 rewrite <- (pred_succ_eq _ H0).
 rewrite H1; reflexivity.
Qed.

(** max *)

Definition max := union2.

Instance max_morph : morph2 max.
exact union2_morph.
Qed.

Lemma lt_0_succ : forall n, n ∈ N -> zero < succ n.
intros.
elim H using N_ind; intros.
 rewrite <- H1; trivial.

 apply succ_intro1; reflexivity.

 apply lt_trans with (succ n0); trivial.
  apply succ_typ; apply succ_typ; trivial.
  apply succ_intro1; reflexivity.
Qed.

Lemma lt_mono : forall m n, m ∈ N -> n ∈ N -> 
  m < n -> succ m < succ n.
intros m n Hm Hn.
elim Hn using N_ind; intros. rewrite H0 in H1; auto.
 elim empty_ax with m; trivial.
 elim le_case with (1:=H1); intros.
  rewrite H2; apply succ_intro1; reflexivity.
  apply succ_intro2; auto.
Qed.


Lemma le_total : forall m, m ∈ N -> forall n, n ∈ N ->
  m < n \/ m == n \/ n < m.
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

Lemma max_lt : forall m n, n ∈ N -> m < n -> max m n == n.
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


Lemma max_typ : forall m n, m ∈ N -> n ∈ N -> max m n ∈ N.
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

Lemma nat2set_typ : forall n, nat2set n ∈ N.
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

Lemma nat2set_reflect : forall x, x ∈ N -> exists n, x == nat2set n.
intros.
elim H using N_ind; intros.
 destruct H2.
 exists x0.
 rewrite <- H1; trivial.

 exists 0; reflexivity.

 destruct H1.
 exists (S x0); rewrite H1; reflexivity.
Qed.

(** Recursor (as in G""odel's T) *)

Definition NREC f g n y :=
  forall P,
  Proper (eq_set ==> eq_set ==> iff) P -> 
  P zero f -> (forall m x, m ∈ N -> P m x -> P (succ m) (g m x)) -> P n y.

Lemma NREC_inv : forall f g n y,
  morph2 g ->
  NREC f g n y ->
  NREC f g n y /\
  (n == zero -> y == f) /\
  (forall m, m ∈ N -> n == succ m -> exists2 z, NREC f g m z & y == g m z).
intros f g n y gm h; pattern n, y; apply h.
 do 3 red; intros.
 apply and_iff_morphism.
  split; red; intros.
   rewrite <- H; rewrite <- H0; apply H1; trivial. 
   rewrite H; rewrite H0; apply H1; trivial. 
  apply and_iff_morphism.
   rewrite H; rewrite H0; reflexivity.

   apply fa_morph; intro m.
   rewrite H.
   apply fa_morph; intros _.
   apply fa_morph; intros _.
   apply ex2_morph.
    red; reflexivity.

    red; intros.
    rewrite H0; reflexivity.

 split; [|split]; intros.
  red; auto.

  reflexivity.

  symmetry in H0; apply discr in H0; contradiction.

 intros ? ? ? (?,(?,?)).
 split; [|split]; intros.
  red; intros.
  apply H5; trivial; apply H0; auto.

  apply discr in H3; contradiction.

  apply succ_inj in H4; trivial.
  exists x.
   red; intros.
   rewrite <- H4; apply H0; auto.

   rewrite H4; reflexivity.
Qed.

Require Import ZFrepl.

Lemma NREC_choice_0 : forall f g, uchoice_pred (NREC f g zero).
split; [|split]; intros.
 unfold NREC in *; intros.
 rewrite <- H.
 apply H0; auto.

 exists f.
 red; auto.

 cut (zero==zero); auto with *.
 pattern zero at 2, x; apply H; intros.
  do 3 red; intros.
  rewrite H1; rewrite H2; reflexivity.

  revert H1; pattern zero at 2, x'; apply H0; intros.
   do 3 red; intros.
   rewrite H1; rewrite H2; reflexivity.

   reflexivity.

   symmetry in H3; apply discr in H3; contradiction.

  symmetry in H3; apply discr in H3; contradiction.
Qed.

Lemma NREC_choice : forall f g n,
  n ∈ N ->
  morph2 g ->
  uchoice_pred (NREC f g n).
intros f g n H gm.
split; intros.
 unfold NREC; intros.
 rewrite <- H0.
 apply H1; auto.

 split; intros.
  elim H using N_ind; intros.
   destruct H2.
   exists x; red; intros.
   rewrite <- H1.
   apply H2; auto.

   exists f; red; auto.

   destruct H1.
   exists (g n0 x); red; intros.
   apply H4; trivial.
   apply H1; auto.

  revert x x' H0 H1.
  elim H using N_ind; intros.
   apply H2.
    red; intros; rewrite H1; apply H3; trivial.
    red; intros; rewrite H1; apply H4; trivial.

   apply NREC_inv in H0; trivial; apply NREC_inv in H1; trivial;
   destruct H0 as (_,(?,_)); destruct H1 as (_,(?,_)).
   rewrite H0; auto with *.
   rewrite H1; auto with *.

   apply NREC_inv in H2; trivial; apply NREC_inv in H3; trivial;
   destruct H2 as (_,(_,?)); destruct H3 as (_,(_,?)).
   destruct (H2 n0); auto with *.
   destruct (H3 n0); auto with *.
   rewrite H5; rewrite H7.
   apply gm; auto with *.
Qed.

(** Recursor at the level of sets *)

Definition natrec f g n := uchoice (NREC f g n).

Global Instance natrec_morph' :
  Proper (eq ==> eq ==> eq_set ==> eq_set) natrec.
do 4 red; intros.
subst y y0.
unfold natrec.
apply uchoice_morph_raw.
red; intros.
unfold NREC.
apply fa_morph; intros P.
apply fa_morph; intros Pm.
rewrite H1; rewrite H; reflexivity.
Qed.

Instance natrec_morph :
  Proper (eq_set ==> (eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) natrec.
do 4 red; intros.
unfold natrec, NREC.
apply uchoice_morph_raw.
red; intros.
apply fa_morph; intro P.
apply fa_morph; intro Pm.
rewrite H.
apply fa_morph; intros _.
split; intros.
 rewrite <- H1; rewrite <- H2; apply H3; intros.
 setoid_replace (x0 m x3) with (y0 m x3); auto.
 apply H0; reflexivity.

 rewrite H1; rewrite H2; apply H3; intros.
 setoid_replace (y0 m x3) with (x0 m x3); auto.
 symmetry; apply H0; reflexivity.
Qed.

Lemma natrec_def : forall f g n,
  morph2 g -> n ∈ N -> NREC f g n (natrec f g n).
intros.
unfold natrec; apply uchoice_def.
apply NREC_choice; trivial.
Qed.


Lemma natrec_0 : forall f g, natrec f g zero == f.
unfold natrec; intros.
symmetry; apply uchoice_ext; trivial.
 apply NREC_choice_0.

 red; auto.
Qed.

Lemma natrec_S : forall f g n, morph2 g -> n ∈ N ->
   natrec f g (succ n) == g n (natrec f g n).
intros.
elim H0 using N_ind; intros.
 rewrite <- H2; trivial.

 symmetry; apply uchoice_ext.
  apply NREC_choice; trivial.
  apply succ_typ; apply zero_typ.
 red; intros.
 apply H3.
  apply zero_typ.

  rewrite natrec_0; auto.

 unfold natrec at 1; symmetry; apply uchoice_ext; auto.
  apply NREC_choice; trivial.
  do 2 apply succ_typ; trivial.

  red; intros.
  apply H5.
   apply succ_typ; trivial.
  rewrite H2.
  apply H5; trivial.
  revert P H3 H4 H5; change (NREC f g n0 (natrec f g n0)).
  unfold natrec; apply uchoice_def.
  apply NREC_choice; trivial.
Qed.

Lemma natrec_typ P f g n :
  morph1 P ->
  morph2 g ->
  n ∈ N ->
  f ∈ P zero ->
  (forall k h, k ∈ N -> h ∈ P k -> g k h ∈ P (succ k)) ->
  natrec f g n ∈ P n.
intros.
elim H1 using N_ind; intros.
 rewrite <- H5; trivial.

 rewrite natrec_0; trivial.

 rewrite natrec_S; auto.
Qed.
