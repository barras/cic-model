
Require Export ZF ZFwfr.

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

Lemma le_trans m n p :
  p ∈ N -> le m n -> le n p -> le m p.
intros.
apply le_case in H0; destruct H0.
 rewrite H0; trivial.

 apply lt_is_le.
 apply le_case in H1; destruct H1.
 rewrite <-H1; trivial.

 apply lt_trans with n; trivial.
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

(** max *)

Definition max := union2.

Instance max_morph : morph2 max.
exact union2_morph.
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

Lemma max_le_l n m : n ∈ N -> m ∈ N -> le n (max n m).
intros.
destruct le_total with n m as [?|[?|?]]; trivial.
 rewrite max_lt; trivial.
 apply lt_is_le; trivial.

 rewrite max_eq; trivial.

 rewrite max_sym,max_lt; trivial.
Qed.

Lemma max_le_r n m : n ∈ N -> m ∈ N -> le m (max n m).
intros.
rewrite max_sym; apply max_le_l; trivial.
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
Hint Resolve max_le_l max_le_r max_typ.

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

 (** * Well-foundation results *)

Require Import ZFwf.

Lemma isWf_succ : forall n, isWf n -> isWf (succ n).
intros.
apply isWf_intro; intros.
elim le_case with (1:=H0); clear H0; intros.
 apply isWf_ext with n; trivial.
 symmetry; trivial.

 apply isWf_inv with n; trivial.
Qed.

Lemma isWf_N : isWf N.
apply isWf_intro; intros.
elim H using N_ind; intros.
 apply isWf_ext with n; trivial.
 apply isWf_zero.
 apply isWf_succ; trivial.
Qed.

(** Recursor *)
Lemma N_trans x y : x ∈ y -> y ∈ N -> x ∈ N.
 intros.
 revert H; elim H0 using N_ind; intros. 
  rewrite <- H1 in H3; auto.

  apply empty_ax in H; contradiction.
  apply union2_elim in H2; destruct H2; auto.
  apply singl_elim in H2.
  rewrite H2; trivial.
Qed.

(** Recursor (as in G""odel's T) *)

Section Natrec.

Let natrec_body f g (F:set->set) n :=
  cond_set (n==zero) f ∪
  cond_set (exists2 k, k ∈ N & n==succ k) (g (pred n) (F (pred n))).

Local Instance natrec_body_morph :
  Proper (eq_set==>(eq_set==>eq_set==>eq_set)==>
                (eq_set==>eq_set)==>eq_set==>eq_set) natrec_body.
do 5 red; intros.
apply union2_morph.
 rewrite H,H2; reflexivity.

 apply cond_set_morph; auto with *.
  apply ex2_morph; auto with *.
  red; intros.
  rewrite H2; reflexivity.

  apply H0.
   rewrite H2; reflexivity.

   apply H1.
   rewrite H2; reflexivity.
Qed.

Lemma natrec_body_ext f g x F F' :
   morph2 g ->
   (forall y y', y ∈ N /\ y ∈ x -> y == y' -> F y == F' y') ->
   natrec_body f g F x == natrec_body f g F' x.
intros gm Feq.
apply union2_morph; auto with *.
apply cond_set_morph2; auto with *.
intros (k,tyk,eqx).
apply gm; auto with *.
apply Feq; auto with *.
rewrite eqx.
rewrite pred_succ_eq; auto.
split; trivial.
apply succ_intro1.
reflexivity.
Qed.

Lemma natrec_body0 f g F n :
  n==zero -> natrec_body f g F n == f.
unfold natrec_body.
intros eqn.
rewrite cond_set_ok; auto with *.
rewrite cond_set_mt.
 apply union2_mt_r.

 intros (k,_,e).
 rewrite e in eqn; apply discr in eqn; trivial.
Qed.

Local Instance Rmorph : Proper (eq_set==>eq_set==>iff) (fun n m => n∈N /\ n<m).
do 3 red; intros.
rewrite H,H0; reflexivity.
Qed.

Definition natrec (f:set) (g:set->set->set) (n:set) : set :=
  WFR (fun n m => n ∈ N /\ n < m) (natrec_body f g) n.

Global Instance natrec_morph :
  Proper (eq_set ==> (eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) natrec.
do 4 red; intros.
apply WFR_morph; auto with *.
 do 2 red; intros.
 rewrite H2,H3; reflexivity.

 do 2 red; intros.
 apply natrec_body_morph; trivial.
Qed.

Global Instance natrec_morph_gen2 f g : morph1 (natrec f g).
apply WFR_morph_gen2.
red; red; reflexivity.
Qed.

Lemma N_acc n :
  n ∈ N -> Acc (fun n m => n∈N /\ n<m) n.
intros ntyp.
assert (forall m, m ∈ N -> m <= n -> Acc (fun n m=>n∈N/\n<m) m); eauto.
apply N_ind with (4:=ntyp); intros.
 rewrite <- H0 in H3.
 generalize (H1 _ H2 H3).
 apply iff_impl; apply wf_morph with (eqA:=eq_set); auto with *.
 apply Rmorph.

 constructor; destruct 1.
 red in H0.
 apply le_case in H0; destruct H0.
  rewrite H0 in H2; apply empty_ax in H2; contradiction.
  apply empty_ax in H0; contradiction.

 constructor; destruct 1.
 assert (y <= n0); auto.
  apply le_case in H2; destruct H2.
   rewrite H2 in H4; trivial.
   apply lt_trans with m; trivial.
   apply succ_typ; trivial.
Qed.

Lemma natrec_0 f g :
  natrec f g zero == f.
unfold natrec; rewrite WFR_eqn_norec.
 apply natrec_body0; auto with *.

 red; destruct 1.
 apply empty_ax in H0; contradiction.

 intros.
 rewrite natrec_body0; auto with *.
 rewrite natrec_body0; auto with *.
Qed.

Lemma natrec_0_eq f g n :
  morph2 g ->
  n == zero ->
  natrec f g n == f.
intros.
rewrite H0.
apply natrec_0.
Qed.

Lemma natrec_S_eq f g n k :
  morph2 g ->
  k ∈ N ->
  n == succ k ->
  natrec f g n == g k (natrec f g k).
intros.
unfold natrec.
rewrite WFR_eqn.
 unfold natrec_body at 1.
 rewrite cond_set_mt.
 rewrite cond_set_ok.
 rewrite union2_mt_l.
 apply pred_morph in H1; rewrite pred_succ_eq in H1; trivial.
 apply H; trivial.
 apply WFR_morph0; trivial.

 exists k; auto with *.

 rewrite H1; apply discr.

 apply Rmorph.

 apply natrec_body_morph; auto with *.
 
 intros.
 apply natrec_body_ext; trivial.

 constructor; intros.
 destruct H2.
 apply N_acc; trivial.
Qed.

Lemma natrec_S f g n :
  morph2 g ->
  n ∈ N ->
  natrec f g (succ n) == g n (natrec f g n).
intros; apply natrec_S_eq; auto with *.
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
 rewrite <- H5.
 trivial.

 rewrite natrec_0; trivial.
 rewrite natrec_S; auto.
Qed.

End Natrec.
 (*
Lemma natrec_ext f f' g g' :
  f == f' ->
  (forall n n', n ∈ N -> n==n' -> forall x x', x==x' -> g n x == g' n' x') ->
  (eq_set==>eq_set)%signature (natrec f g) (natrec f' g').
red; intros.
unfold natrec.
apply ZFwf.WellFoundedRecursion2.WFR_morph; trivial.
 clear; do 2 red; intros.
 rewrite H,H0; reflexivity.

 do 2 red; intros.
 apply union2_morph.
  rewrite H,H3; reflexivity.

  apply cond_set_morph2.
   apply ex2_morph.  
    reflexivity.
    red; intros.
    rewrite H3; reflexivity.

   intros (k,tyk,eqx1).
   apply H0.
    rewrite eqx1,pred_succ_eq; trivial.
    rewrite H3; reflexivity.
    apply H2; rewrite H3; reflexivity.
Qed.
*)

(** Addition *)

Definition add m n := natrec m (fun _ => succ) n.

Instance add_morph : morph2 add.
do 3 red; intros.
apply WFR_morph_gen2; auto with *.
red; red; intros.
rewrite H; reflexivity.
Qed.

Lemma add0 n : add n zero == n.
  apply natrec_0; do 3 red; intros; apply succ_morph; trivial.
Qed.
  
Lemma addS : forall m n, m ∈ N -> add n (succ m) == succ (add n m).
intros.
apply natrec_S; trivial.
do 3 red; intros; apply succ_morph; trivial.  
Qed.

Lemma add1 n : add n (succ zero) == succ n.
intros; rewrite addS; trivial.
 rewrite add0; reflexivity.  

 apply zero_typ.
Qed.

Lemma add_typ m n :
  m ∈ N -> n ∈ N -> add m n ∈ N.
intros.
apply natrec_typ with (P:=fun _=>N); auto with *.
 do 2 red; reflexivity.
 do 3 red; intros; apply succ_morph; trivial.  
intros; apply succ_typ; trivial.
Qed.
