Require Import Classical.
Require Import ZFnats.
Import IZF.

Definition isOrd x :=
  forall P : set -> Prop,
  (forall y,
   (forall a b, a \in b -> b \in y -> a \in y) ->
   (forall z, z \in y -> P z)-> P y) -> P x.

Lemma isOrd_intro x :
  (forall a b, a \in b -> b \in x -> a \in x) ->
  (forall y, y \in x -> isOrd y) ->
  isOrd x.
red; intros.
apply H1; trivial.
intros.
red in H0.
apply H0; trivial.
Qed.

Lemma isOrd_elim x :
  isOrd x ->
  (forall a b, a \in b -> b \in x -> a \in x) /\
  (forall y, y \in x -> isOrd y).
intro xo; apply xo; intros.
split; intros; eauto.
apply H0 in H1.
destruct H1.
apply isOrd_intro; intros; eauto.
Qed.


Lemma isOrd_inv x y :
  isOrd x -> lt y x -> isOrd y.
intros.
apply isOrd_elim in H; destruct H; eauto.
Qed.

Lemma isOrd_trans x y z :
  isOrd x -> lt z y -> lt y x -> lt z x.
intros xo.
unfold lt.
apply isOrd_elim in xo; destruct xo; eauto.
Qed.

Lemma isOrd_ext : forall x y, x == y -> isOrd x -> isOrd y.
intros.
apply isOrd_elim in H0; destruct H0.
apply isOrd_intro; intros.
 rewrite <- H in H3|-*; eauto.

 rewrite <- H in H2; auto.
Qed.

Instance isOrd_morph : Proper (eq_set ==> iff) isOrd.
apply morph_impl_iff1; auto with *.
exact isOrd_ext.
Qed.

Lemma isOrd_ind : forall x (P:set->Prop),
  (forall y, isOrd y -> y \incl x ->
   (forall z, lt z y -> P z) -> P y) ->
  isOrd x -> P x.
intros.
cut (isOrd x /\ (x \incl x -> P x)).
 destruct 1 as (_,?); auto with *.
pattern x at -3.
apply H0; intros.
assert (isOrd y).
 apply isOrd_intro; intros; eauto.
 apply H2; trivial.
split; intros; trivial.
apply H; intros; trivial.
destruct H2 with (1:=H5) as (_,?).
apply H6.
red; intros.
apply H4.
apply isOrd_trans with z; auto.
Qed.

Lemma isOrd_le : forall x y,
  isOrd x -> le y x -> isOrd y.
intros.
apply le_case in H0; destruct H0.
 rewrite H0; trivial.

 apply isOrd_inv with x; trivial.
Qed.

Lemma isOrd_zero : isOrd zero.
apply isOrd_intro; intros.
 elim empty_ax with b; trivial.
 elim empty_ax with y; trivial.
Qed.

Lemma isOrd_succ : forall n, isOrd n -> isOrd (succ n).
intros.
apply isOrd_intro; intros.
 apply succ_intro2.
 elim le_case with (1:=H1); clear H1; intros.
  rewrite <- H1; trivial.

  apply isOrd_trans with b; trivial.

 elim le_case with (1:=H0); clear H0; intros.
  apply isOrd_ext with n; trivial.
  symmetry; trivial.

  apply isOrd_inv with n; trivial.
Qed.


Lemma le_lt_trans : forall x y z, isOrd z -> le x y -> lt y z -> lt x z.
intros.
apply le_case in H0; destruct H0.
 rewrite H0; trivial.
 apply isOrd_trans with y; trivial.
Qed.

Lemma lt_le_trans : forall x y z, isOrd z -> lt x y -> le y z -> lt x z.
intros.
apply le_case in H1; destruct H1.
 rewrite <- H1; trivial.
 apply isOrd_trans with y; trivial.
Qed.

Lemma lt_antirefl : forall x, isOrd x -> ~ lt x x.
induction 1 using isOrd_ind; intros.
red; intros; apply H1 with y; trivial.
Qed.

Lemma isOrd_eq : forall o, isOrd o -> o == sup o succ.
intros.
apply eq_intro; intros.
 rewrite sup_ax.
 2:do 2 red; intros; apply succ_morph; trivial.
 exists z; trivial.
 apply le_refl.

 rewrite sup_ax in H0.
 2:do 2 red; intros; apply succ_morph; trivial.
 destruct H0.
 apply le_lt_trans with x; trivial.
Qed.

Lemma ord_le_incl : forall x y, isOrd x -> isOrd y -> le x y -> x \incl y.
red; intros.
apply lt_le_trans with x; auto.
Qed.

Module ClassicOrdinal.

Axiom EM : forall A, A \/ ~A.

Lemma ord_tricho : forall x y,
  isOrd x -> isOrd y -> lt x y \/ x == y \/ lt y x.
intros x y xord; revert y.
apply isOrd_ind with (2:=xord).
clear xord; intros x0 xord _ Hrec y yord; clear x; rename x0 into x.
apply isOrd_ind with (2:=yord).
clear yord; intros y0 yord _ Hrecy; clear y; rename y0 into y.
destruct (EM (exists2 x1, lt x1 x & forall y1, lt y1 y -> lt y1 x1)).
 right; right.
 destruct H.
 destruct (Hrec x0 H y yord).
  elim (@lt_antirefl x0); auto.
  apply isOrd_inv with y; trivial.
 destruct H1.
  rewrite <- H1; trivial.

  apply isOrd_trans with x0; trivial.

destruct (EM (exists2 y1, lt y1 y & forall x1, lt x1 x -> lt x1 y1)).
 left.
 destruct H0.
 destruct (Hrecy x0 H0).
  apply isOrd_trans with x0; trivial.
 destruct H2.
  rewrite H2; trivial.

  elim (@lt_antirefl x0); auto.
  apply isOrd_inv with x; trivial.

 assert (forall x1, lt x1 x -> exists2 y1, lt y1 y & le x1 y1).
  intros.
  destruct (EM (exists2 y1, lt y1 y & le x1 y1)); trivial.
  elim H.
  exists x1; trivial.
  intros.
  destruct (Hrec _ H1 y1).
   apply isOrd_inv with y; trivial.

   elim H2.
   exists y1; trivial.
   apply lt_is_le; trivial.

   destruct H4; trivial.
   elim H2.
   exists y1; trivial.
   rewrite <- H4; apply le_refl.
 assert (forall y1, lt y1 y -> exists2 x1, lt x1 x &  le y1 x1).
  intros.
  destruct (EM (exists2 x1, lt x1 x & le y1 x1)); trivial.
  elim H0.
  exists y1; trivial.
  intros.
  destruct (Hrec _ H4 y1); trivial.
   apply isOrd_inv with y; trivial.

   elim H3.
   exists x1; trivial.
   destruct H5; auto with *.
   rewrite <- H5; apply le_refl.
 right; left.
 apply eq_intro; intros.
  destruct H1 with (1:=H3).
  apply le_lt_trans with x0; trivial.

  destruct H2 with (1:=H3).
  apply le_lt_trans with x0; trivial.
Qed.

Lemma ord_total : forall x y,
  isOrd x -> isOrd y -> le x y \/ lt y x.
intros.
destruct (ord_tricho _ _ H H0); auto.
destruct H1; auto.
left; rewrite H1.
apply le_refl.
Qed.

Lemma ord_incl_le : forall x y, isOrd x -> isOrd y -> x \incl y -> le x y. 
intros.
destruct (ord_total x y); trivial.
apply H1 in H2.
apply lt_antirefl in H2; trivial.
contradiction.
Qed.

End ClassicOrdinal.

Definition increasing F :=
  forall x y, isOrd x -> isOrd y -> y \incl x -> F y \incl F x.

Lemma increasing_le : forall F x y,
  increasing F -> isOrd x -> le y x -> F y \incl F x.
unfold increasing; intros.
assert (isOrd y).
 apply isOrd_inv with (succ x); trivial.
 apply isOrd_succ; trivial.
apply H; trivial.
apply ord_le_incl; trivial.
Qed.

Lemma isOrd_N : isOrd N.
apply isOrd_intro; intros.
 generalize a H; clear a H.
 elim H0 using N_ind; intros.
  rewrite <- H1 in H3; auto.

  elim empty_ax with a; trivial.
  elim le_case with (1:=H2); clear H2; intros; auto.
  rewrite H2; trivial.

 elim H using N_ind; intros.
  apply isOrd_ext with n; trivial.
  apply isOrd_zero.
  apply isOrd_succ; trivial.
Qed.

Lemma natOrd : forall n, n \in N -> isOrd n.
intros.
apply isOrd_inv with N; trivial.
apply isOrd_N.
Qed.

Hint Resolve natOrd isOrd_N.


Definition succOrd o := exists2 o', isOrd o' & o == succ o'.

(* Limit ordinals *)

Definition limitOrd o := isOrd o /\ union o == o.
Definition limitOrd' o := isOrd o /\ (forall x, lt x o -> lt (succ x) o).

Lemma limit_equiv : forall o, limitOrd' o -> limitOrd o.
destruct 1; split; trivial.
apply eq_intro; intros.
 apply union_elim in H1; destruct H1.
 apply isOrd_trans with x; trivial.

 apply union_intro with (succ z).
  apply le_refl.
  apply H0; trivial.
Qed.

Lemma N_limit_ord : limitOrd' N.
split; intros.
 apply isOrd_N.
 apply succ_typ; trivial.
Qed.

Lemma limit_is_ord : forall o, limitOrd o -> isOrd o.
destruct 1; trivial.
Qed.
Hint Resolve limit_is_ord.
Lemma limit'_is_ord : forall o, limitOrd' o -> isOrd o.
destruct 1; trivial.
Qed.
Hint Resolve limit'_is_ord.

Lemma discr_lim_succ : forall o, limitOrd o -> succOrd o -> False.
destruct 1; destruct 1.
assert (x == o).
 rewrite <- H0; rewrite H2.
 apply eq_intro; intros.
  apply union_intro with x; trivial.
  apply succ_intro1; reflexivity.

  rewrite union_ax in H3; destruct H3.
  apply le_case in H4; destruct H4.
   rewrite <- H4; trivial.
   apply isOrd_trans with x0; trivial.
elim lt_antirefl with x; trivial.
generalize (succ_intro1 x x); intros.
rewrite <- H2 in H4; rewrite <- H3 in H4.
apply H4; reflexivity.
Qed.

(*****************************************************************************)


Lemma isOrd_union2 : forall x y,
  isOrd x ->
  isOrd y ->
  isOrd (union2 x y).
intros.
apply isOrd_intro; intros.
 apply union2_elim in H2; destruct H2.
  apply union2_intro1.
  apply isOrd_trans with b; trivial.

  apply union2_intro2.
  apply isOrd_trans with b; trivial.

 apply union2_elim in H1; destruct H1.
  apply isOrd_inv with x; trivial.
  apply isOrd_inv with y; trivial.
Qed.

Lemma ord1_union : forall a P Q,
  union2 (subset a P) (subset a Q) ==
  subset a (fun x => P x\/Q x).
intros.
apply eq_intro; intros.
 apply union2_elim in H; destruct H.
  rewrite subset_ax in H; destruct H.
  destruct H0.
  rewrite H0 in H|-*.
  apply subset_intro; auto.

  rewrite subset_ax in H; destruct H.
  destruct H0.
  rewrite H0 in H|-*.
  apply subset_intro; auto.

 rewrite subset_ax in H; destruct H.
 destruct H0.
 rewrite H0 in H|-*; clear H0 z.
 destruct H1.
  apply union2_intro1.
  apply subset_intro; trivial.

  apply union2_intro2.
  apply subset_intro; trivial.
Qed.

Lemma isOrd_union2_lub : forall o x y,
  isOrd o ->
  lt x o ->
  lt y o ->
  lt (union2 x y) o.
intros.
assert (uord : isOrd (union2 x y)).
 apply isOrd_union2.
  apply isOrd_inv with o; trivial.
  apply isOrd_inv with o; trivial.
destruct (ClassicOrdinal.ord_total o (union2 x y)); trivial.
assert (o \incl union2 x y).
 apply ord_le_incl; trivial.
assert (isOrd x).
 apply isOrd_inv with o; trivial.
assert (isOrd y).
 apply isOrd_inv with o; trivial.
apply H3 in H0.
apply H3 in H1.
apply union2_elim in H0.
apply union2_elim in H1.
destruct H0.
 elim (lt_antirefl x); trivial.
destruct H1.
 elim (lt_antirefl x); trivial.
 apply isOrd_trans with y; trivial.
elim (lt_antirefl y); trivial.
Qed.


(* least ordinal... *)

Definition least_ord o (P:set->Prop) :=
  union (subset o (fun y => P y /\ forall x, isOrd x -> P x -> le y x)).

Lemma least_ord_morph : forall o o' (P P':set->Prop),
  isOrd o -> o == o' ->
  (forall x x', isOrd x -> x == x' -> (P x <-> P' x')) ->
  least_ord o P == least_ord o' P'.
unfold least_ord; intros.
apply union_morph.
apply subset_morph; auto.
red; intros.
split; destruct 1; split; intros.
 rewrite <- (H1 x x); trivial; try reflexivity.
 apply isOrd_inv with o; trivial.

 rewrite <- (H1 x0 x0) in H6; auto; try reflexivity.

 rewrite (H1 x x); trivial; try reflexivity.
 apply isOrd_inv with o; trivial.

 rewrite (H1 x0 x0) in H6; auto; try reflexivity.
Qed.

Lemma least_ord1 : forall o (P:set->Prop),
  (forall x x', isOrd x -> x == x' -> P x -> P x') ->
  isOrd o ->
  forall x,
  lt x o ->
  P x ->
  P (least_ord o P) /\ isOrd (least_ord o P) /\ le (least_ord o P) x /\
  forall y, lt y (least_ord o P) -> ~ P y.
induction 2 using isOrd_ind; intros.
Import ClassicOrdinal.
elim (EM (exists2 z, lt z x & P z)); intro.
 destruct H5.
 assert (least_ord y P == least_ord x P).
  apply eq_intro; intros.
   apply union_elim in H7; destruct H7.
   rewrite subset_ax in H8; destruct H8.
   destruct H9.
   destruct H10.
   rewrite H9 in H7,H8|-;clear H9 x1.
   apply union_intro with x2; auto.
   apply subset_intro; auto.
   apply H11 in H6.
   2:apply isOrd_inv with x; trivial; apply isOrd_inv with y; trivial.
   apply le_lt_trans with x0; trivial.
   apply isOrd_inv with y; trivial.

   apply union_elim in H7; destruct H7.
   specialize subset_elim2 with (1:=H8); intro.
   apply subset_elim1 in H8.
   destruct H9.
   rewrite H9 in H7,H8|-; clear H9 x1.
   destruct H10.
   assert (isOrd x2).
    apply isOrd_inv with x; trivial.
    apply isOrd_inv with y; trivial.
   apply union_intro with x2; trivial.
   apply subset_intro; auto.
   apply isOrd_trans with x; trivial.
 destruct H2 with x x0; auto.
 destruct H9.
 destruct H10.
 split.
  apply H with (least_ord x P); trivial.
  symmetry; trivial.

  rewrite H7; split; trivial.
  split; intros.
   apply lt_is_le; apply le_lt_trans with x0; trivial.
   apply isOrd_inv with y; trivial.

   rewrite H7 in H12; auto.

 assert (least_ord y P == x).
  apply eq_intro; intros.
   apply union_elim in H6; destruct H6.
   apply subset_elim2 in H7.
   destruct H7.
   destruct H8.
   rewrite H7 in H6; clear H7 x0.
   assert (le x1 x).
    apply H9; trivial.
    apply isOrd_inv with y; trivial.
   apply le_case in H7; destruct H7.
    rewrite <- H7; trivial.
    elim H5; exists x1; trivial.

   unfold least_ord.
   apply union_intro with x; trivial.
   apply subset_intro; trivial.
   split; trivial; intros.
   elim (ord_total x x0); intros; trivial.
    elim H5.
    exists x0; trivial.

    apply isOrd_inv with y; auto.
 split.
  symmetry in H6.
  apply H with x; auto.
  apply isOrd_inv with y; auto.

  rewrite H6; split; auto.
   apply isOrd_inv with y; auto.

   split; auto.
   red; intros; apply H5.
   exists y0; trivial.
   rewrite H6 in H7; trivial.
Qed.

(********************************************************************)

Require Import ZFrepl.

Section LimOrd.

  Variable f : nat -> set.
  Variable ford : forall n, isOrd (f n).

  Definition ord_sup :=
    union (repl N (fun x y => exists2 n, x == nat2set n & f n == y)).

  Lemma repl_sup : 
    repl_rel N (fun x y => exists2 n, x == nat2set n & f n == y).
split; intros.
 destruct H2.
 exists x0.
  rewrite <- H0; trivial.
  rewrite <- H1; trivial.

 destruct H0.
 destruct H1.
 rewrite <- H2; rewrite <- H3.
 replace x1 with x0; try reflexivity.
 apply nat2set_inj.
 rewrite <- H0; trivial.
Qed.

  Lemma isOrd_sup_intro : forall n, f n \incl ord_sup.
unfold ord_sup.
red; intros.
apply union_intro with (f n); trivial.
apply repl_intro with (nat2set n).
 exact repl_sup.

 apply nat2set_typ.

 exists n; reflexivity.
Qed.

  Lemma isOrd_sup_elim : forall x, lt x ord_sup -> exists n, lt x (f n).
unfold ord_sup; intros.
elim union_elim with (1:=H); clear H; intros.
elim repl_elim with (1:=repl_sup) (2:=H0); intros.
destruct H2.
exists x2.
rewrite H3; trivial.
Qed.

  Lemma isOrd_sup : isOrd ord_sup.
apply isOrd_intro; intros.
 elim isOrd_sup_elim with (1:=H0); intros.
 apply isOrd_sup_intro with x.
 apply isOrd_trans with b; trivial.

 elim isOrd_sup_elim with (1:=H); intros.
 apply isOrd_inv with (f x); trivial.
Qed.

End LimOrd.

Section LimOrdRel.

  Variable R : nat -> set -> Prop.
  Variable Rmorph : forall n x x', isOrd x -> x == x' -> R n x -> R n x'.
  Variable Rtot : forall n, exists x, R n x.
  Variable Rfun : forall n x x',
    isOrd x -> isOrd x' -> R n x -> R n x' -> x == x'.
  Variable Rord : forall n x, R n x -> isOrd x.

  Definition sup_rel :=
    union (repl N (fun x y => exists2 n, x == nat2set n & R n y)).

  Lemma repl_sup_rel : 
    repl_rel N (fun x y => exists2 n, x == nat2set n & R n y).
split; intros.
 destruct H2.
 exists x0.
  rewrite <- H0; trivial.
  apply Rmorph with y; eauto.

 destruct H0.
 destruct H1.
 apply Rfun with x0; trivial; eauto.
 replace x0 with x1; trivial.
 apply nat2set_inj.
 rewrite <- H1; trivial.
Qed.

  Lemma isOrd_sup_rel_intro2 : forall n y, R n y -> y \incl sup_rel.
unfold sup_rel.
red; intros.
apply union_intro with y; trivial.
apply repl_intro with (nat2set n).
 exact repl_sup_rel.

 apply nat2set_typ.

 exists n; trivial; reflexivity.
Qed.

  Lemma isOrd_sup_rel_intro : forall n,
    exists2 y, R n y & y \incl sup_rel.
intros.
elim (Rtot n); intros.
exists x; trivial.
apply isOrd_sup_rel_intro2 with n; trivial.
Qed.


  Lemma isOrd_sup_rel_elim :
    forall x, lt x sup_rel -> exists n, exists2 y, R n y & lt x y.
unfold sup_rel; intros.
elim union_elim with (1:=H); clear H; intros.
elim repl_elim with (1:=repl_sup_rel) (2:=H0); intros.
destruct H2.
exists x2.
exists x0; trivial.
Qed.

  Lemma isOrd_sup_rel : isOrd sup_rel.
apply isOrd_intro; intros.
 elim isOrd_sup_rel_elim with (1:=H0); intros.
 destruct H1.
 apply (isOrd_sup_rel_intro2 x x0); trivial.
 apply isOrd_trans with b; eauto.

 elim isOrd_sup_rel_elim with (1:=H); intros.
 destruct H0.
 apply isOrd_inv with x0; eauto.
Qed.

End LimOrdRel.

Section TransfiniteRecursion.

  Variable F : (set -> set) -> set -> set.
  Hypothesis Fmorph : forall o o' f f',
    o == o' -> eq_fun o f f' -> F f o == F f' o'.

  Definition TR_rel o y :=
    forall P,
    Proper (eq_set ==> eq_set ==> iff) P ->
    (forall o' f, ext_fun o' f ->
     (forall n, lt n o' -> P n (f n)) ->
     P o' (F f o')) ->
    P o y.

  Instance TR_rel_morph : Proper (eq_set ==> eq_set ==> iff) TR_rel.
do 3 red; unfold TR_rel; split; intros.
 rewrite <- H; rewrite <- H0; apply H1; auto.

 rewrite H; rewrite H0; apply H1; auto.
Qed.

  Lemma TR_rel_intro : forall x f,
    ext_fun x f ->
    (forall y, y \in x -> TR_rel y (f y)) ->
    TR_rel x (F f x).
red; intros.
apply H2; trivial; intros.
apply H0; trivial.
Qed.

  Lemma TR_rel_inv : forall x y,
    TR_rel x y ->
    exists2 f,
      ext_fun x f /\ (forall y, y \in x -> TR_rel y (f y)) &
      y == F f x.
intros.
apply (@proj2 (TR_rel x y)).
apply H; intros.
 do 3 red; intros.
 rewrite <- H0; rewrite <- H1.
 split; destruct 1 as (Htr,(f,(fm,eqf),eqF)); split; trivial; exists f; trivial.
  split; intros.
   do 2 red; intros.
   rewrite <- H0 in H2; auto.
   rewrite <- H0 in H2; auto.
  rewrite <- H1; rewrite eqF; apply Fmorph; intros; auto.
  split; intros.
   do 2 red; intros.
   rewrite H0 in H2; auto.
   rewrite H0 in H2; auto.
  symmetry in H0; rewrite H1; rewrite eqF; apply Fmorph; intros; auto.
assert (TR_relsub := fun n h => proj1 (H1 n h)); clear H1.
split.
 apply TR_rel_intro; trivial.

 exists f; auto with *.
Qed.


  Lemma TR_rel_fun :
    forall x y, TR_rel x y -> forall y', TR_rel x y' -> y == y'.
intros x y H.
apply H; intros.
 do 3 red; intros.
 split; intros.
  rewrite <- H1; rewrite <- H0 in H3; auto.
  rewrite H1; rewrite H0 in H3; auto.
apply TR_rel_inv in H2; destruct H2.
destruct H2.
rewrite H3; clear y' H3.
apply Fmorph; intros.
 reflexivity.
red; intros.
apply H1; trivial.
rewrite H5 in H3|-*; auto.
Qed.

  Lemma TR_rel_repl_rel :
    forall x, repl_rel x TR_rel.
split; intros.
 rewrite <- H0; rewrite <- H1; trivial.

 apply TR_rel_fun with x0; trivial.
Qed.

  Lemma TR_rel_def : forall o, isOrd o -> exists y, TR_rel o y.
induction 1 using isOrd_ind; intros.
assert (forall z, lt z y -> uchoice_pred (fun y => TR_rel z y)).
 intros.
 specialize H1 with (1:=H2).
 destruct H1.
 split; intros.
  rewrite <- H3; trivial.
 split; intros.
  exists x; trivial.
 apply TR_rel_fun with z; trivial.
exists (F (fun z => uchoice (fun y => TR_rel z y)) y).
apply TR_rel_intro; intros.
 do 2 red; intros.
 apply uchoice_morph; intros; auto.
 rewrite H4; reflexivity.
apply uchoice_def; auto.
Qed.

  Lemma TR_rel_choice_pred : forall o, isOrd o ->
    uchoice_pred (fun y => TR_rel o y).
split; intros.
 rewrite <- H0; trivial.
split; intros.
 apply TR_rel_def; trivial.
apply TR_rel_fun with o; trivial.
Qed.

  Definition TR o := uchoice (fun y => TR_rel o y).

  Lemma TR_morph : forall x x', isOrd x -> x == x' -> TR x == TR x'.
intros.
unfold TR.
apply uchoice_morph.
 apply TR_rel_choice_pred; trivial.

 intros.
 apply TR_rel_morph; auto with *.
Qed.
 
  Lemma TR_eqn : forall o, isOrd o -> TR o == F TR o.
unfold TR; intros.
specialize TR_rel_choice_pred with (1:=H); intro.
apply uchoice_def in H0.
apply TR_rel_inv in H0.
destruct H0.
destruct H0.
rewrite H1.
apply Fmorph; intros; auto with *.
red; intros.
apply TR_rel_fun with x'.
 rewrite <- H4; auto.

 apply uchoice_def.
 apply TR_rel_choice_pred.
 rewrite <- H4; apply isOrd_inv with o; trivial.
Qed.

  Lemma TR_ind : forall o (P:set->set->Prop),
    (forall x x', isOrd x -> x \incl o -> x == x' ->
     forall y y', y == y' -> P x y -> P x' y') ->
    isOrd o ->
    (forall y, isOrd y -> y \incl o ->
     (forall x, lt x y -> P x (TR x)) ->
     P y (F TR y)) ->
    P o (TR o).
induction 2 using isOrd_ind; intros.
apply H with y (F TR y); auto with *.
 symmetry; apply TR_eqn; trivial.
apply H3; trivial; intros.
 reflexivity.
apply H2; trivial; intros.
apply H3; trivial.
red; intros.
apply H6 in H8.
apply isOrd_trans with x; trivial.
Qed.

  Lemma TR_typ : forall n X,
    morph1 X ->
    isOrd n ->
    (forall y f, isOrd y -> y \incl n ->
     (forall z, lt z y -> f z \in X z) -> F f y \in X y) ->
    TR n \in X n.
intros n X Xm is_ord.
apply TR_ind with (o:=n); intros; trivial.
 rewrite <- H2; rewrite <- H1; apply H3; intros.
 rewrite H1 in H6; auto.
apply H2; intros; auto with *.
apply H1; trivial; intros.
apply H2; auto.
red; intros.
apply H5 in H7.
apply isOrd_trans with z; trivial.
Qed.

End TransfiniteRecursion.


(* Specialized version where the case of limit ordinals is union *)
Section TransfiniteIteration.

  Variable F : set -> set.
  Hypothesis Fmorph : Proper (eq_set ==> eq_set) F.

Let G f o := sup o (fun o' => F (f o')).

Lemma Gmorph : forall o o' f f',
    o == o' -> eq_fun o f f' -> G f o == G f' o'.
unfold G; intros.
apply sup_morph; trivial.
red; auto.
Qed.
Hint Resolve Gmorph.

  Definition TI := TR G.

  Lemma TI_morph : forall x x', isOrd x -> x == x' -> TI x == TI x'.
unfold TI; intros.
apply TR_morph; auto with *.
Qed.

  Lemma TI_fun_ext : forall x, isOrd x -> ext_fun x (fun y => F (TI y)).
do 2 red; intros.
apply Fmorph.
apply TI_morph; trivial.
apply isOrd_inv with x; trivial.
Qed.
Hint Resolve TI_fun_ext.

  Lemma TI_eq : forall o,
    isOrd o ->
    TI o == sup o (fun o' => F (TI o')).
intros.
unfold TI.
apply TR_eqn; auto.
Qed.

  Lemma TI_intro : forall o o' x,
    isOrd o ->
    lt o' o ->
    x \in F (TI o') ->
    x \in TI o.
intros.
rewrite TI_eq; trivial.
rewrite sup_ax; auto.
exists o'; trivial.
Qed.

  Lemma TI_elim : forall o x,
    isOrd o ->
    x \in TI o ->
    exists2 o', lt o' o & x \in F (TI o').
intros.
rewrite TI_eq in H0; trivial.
rewrite sup_ax in H0; auto.
Qed.

  Lemma TI_initial : TI zero == empty.
apply empty_ext; red; intros.
apply TI_elim in H.
 destruct H.
 elim empty_ax with (1:=H).

 apply isOrd_zero.
Qed.

  Lemma TI_typ : forall n X,
    (forall a, a \in X -> F a \in X) ->
    isOrd n ->
    (forall m G, le m n ->
     ext_fun m G ->
     (forall x, lt x m -> G x \in X) -> sup m G \in X) ->
    TI n \in X.
induction 2 using isOrd_ind; intros.
rewrite TI_eq; trivial.
apply H3 with (G:=fun o => F (TI o)); intros; auto.
apply H.
apply H2; trivial; intros.
apply H3; auto.
apply lt_is_le.
apply le_lt_trans with x; trivial.
Qed.

End TransfiniteIteration.
Hint Resolve TI_fun_ext.
