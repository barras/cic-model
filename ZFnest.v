Require Import ZF ZFpairs ZFsum ZFrelations ZFcoc ZFord ZFfix.
Import IZF.

Require Import ZFstable.
Require Import ZFiso ZFfixrec.
Require Import ZFind_w ZFspos.
Require Import ZFlist.

Section TRF.

Hypothesis F:(set->set->set)->set->set->set.
Hypothesis Fext : forall o o' f f' x x',
  isOrd o ->
  (forall o' o'' x x', o' \in o -> o'==o'' -> x==x' -> f o' x == f' o'' x') ->
  o == o' ->
  x == x' ->
  F f o x == F f' o' x'.

  Definition TR_rel o x y :=
    isOrd o /\
    forall (P:set->set->set->Prop),
    Proper (eq_set ==> eq_set==>eq_set ==> iff) P ->
    (forall o' f x, isOrd o' -> morph2 f ->
     (forall n x, n \in o' -> P n x (f n x)) ->
     P o' x (F f o' x)) ->
    P o x y.

  Instance TR_rel_morph : Proper (eq_set ==> eq_set ==> eq_set ==> iff) TR_rel.
apply morph_impl_iff3; auto with *.
do 5 red; unfold TR_rel; intros.
destruct H2 as (xo,Hrec); split; intros.
 rewrite <- H; auto.

 cut (P x x0 x1).
  do 4 red in H2.
  apply -> H2; trivial.
 apply Hrec; auto.
Qed.

  Lemma TR_rel_intro : forall o x f,
    isOrd o ->
    morph2 f ->
    (forall o' x, o' \in o -> TR_rel o' x (f o' x)) ->
    TR_rel o x (F f o x).
red; intros.
split; intros; auto.
apply H3; trivial; intros.
apply H1; trivial.
Qed.

  Lemma TR_rel_inv : forall o x y,
    TR_rel o x y -> TR_rel o x y /\
    exists2 f,
      morph2 f /\ (forall o' x, o' \in o -> TR_rel o' x (f o' x)) &
      y == F f o x.
intros o x y H.
destruct H as (H,H0).
apply H0; intros.
 apply morph_impl_iff3; auto with *.
 do 5 red; intros.
 destruct H4; split.
  revert H4; apply TR_rel_morph; auto with *.
 destruct H5 as (f,(fm,eqf),eqF); exists f; [split|]; trivial.
  intros.
  rewrite <- H1 in H5; auto.

  rewrite <- H3; rewrite eqF.
  apply Fext; trivial.
   apply H4.
   intros; apply fm; auto.
split; [split;trivial|].
 apply TR_rel_intro; intros; trivial.
 apply H3; trivial.

 exists f; auto with *.
 split; intros; auto.
 apply H3; auto.
Qed.


  Lemma TR_rel_fun : forall o x y,
    TR_rel o x y -> forall y', TR_rel o x y' -> y == y'.
intros o x y (xo,H).
apply H; intros.
 apply morph_impl_iff3; auto with *.
 do 5 red; intros.
 rewrite <- H2; rewrite <- H0 in H4; rewrite <- H1 in H4; auto.
apply TR_rel_inv in H3; destruct H3.
destruct H4.
destruct H4.
rewrite H5.
apply Fext; auto with *.
intros.
apply H2; trivial.
rewrite <- H8; rewrite H9; auto.
Qed.

Require Import ZFrepl.

  Lemma TR_rel_repl_rel :
    forall o, repl_rel o (TR_rel o).
split; intros.
 rewrite <- H0; rewrite <- H1; trivial.

 apply TR_rel_fun with o x; trivial.
Qed.

  Lemma TR_rel_ex : forall o, isOrd o -> forall x, exists y, TR_rel o x y.
induction 1 using isOrd_ind; intros.
assert (forall x z, z \in y -> uchoice_pred (fun y => TR_rel z x y)).
 intros.
 destruct H1 with z x0; trivial.
 split; intros.
  rewrite <- H4; trivial.
 split; intros.
  exists x1; trivial.
 apply TR_rel_fun with z x0; trivial.
exists (F (fun z x => uchoice (fun y => TR_rel z x y)) y x).
apply TR_rel_intro; intros; trivial.
 do 3 red; intros.
 apply uchoice_morph_raw; red; intros.
 apply TR_rel_morph; trivial.
apply uchoice_def; auto.
Qed.

  Lemma TR_rel_choice_pred : forall o x, isOrd o ->
    uchoice_pred (fun y => TR_rel o x y).
split; intros.
 rewrite <- H0; trivial.
split; intros.
 apply TR_rel_ex; trivial.
apply TR_rel_fun with o x; trivial.
Qed.

  Definition TR o x := uchoice (fun y => TR_rel o x y).

Instance TR_morph : morph2 TR.
do 3 red; intros.
unfold TR.
apply uchoice_morph_raw; red; intros.
apply TR_rel_morph; trivial.
Qed.

  Lemma TR_rel_i o x : isOrd o ->
    TR_rel o x (TR o x).
intros.
specialize TR_rel_choice_pred with (1:=H) (x:=x); intro.
apply uchoice_def in H0; trivial.
Qed.

  Lemma TR_rel_iff o x y : isOrd o ->
    (TR_rel o x y <-> TR o x == y).
split; intros.
 apply TR_rel_fun with (2:=H0).
 apply TR_rel_i; trivial.

 rewrite <- H0.
 apply TR_rel_i; trivial.
Qed.

  Lemma TR_eqn0 : forall o x, isOrd o ->
     TR o x == F TR o x.
intros.
rewrite <- TR_rel_iff; trivial.
apply TR_rel_intro; trivial with *.
intros.
apply TR_rel_i; eauto using isOrd_inv.
Qed.

End TRF.

Existing Instance TR_morph.

Section TR_irrel.

Variable F : (set->set->set)->set->set->set.

Variable T : set -> set.
Variable Tcont : forall o z, isOrd o ->
  (z \in T o <-> exists2 o', o' \in o & z \in T (osucc o')).

Hypothesis Fext : forall o o' f f' x x',
  isOrd o ->
  (forall o' o'' x x', o' \in o -> o'==o'' -> x==x' -> f o' x == f' o'' x') ->
  o == o' ->
  x == x' ->
  F f o x == F f' o' x'.

Hypothesis Firr : forall o o' f f' x x',
  morph2 f ->
  morph2 f' ->
  isOrd o ->
  isOrd o' ->
  (forall o1 o1' x x',
   o1 \in o -> o1' \in o' -> o1 \incl o1' -> x \in T o1 -> x==x' ->
   f o1 x == f' o1' x') ->
  o \incl o' ->
  x \in T o ->
  x == x' ->
  F f o x == F f' o' x'.

Lemma TR_irrel : forall o o' x,
  isOrd o ->
  isOrd o' ->
  o' \incl o ->
  x \in T o' ->
  TR F o x == TR F o' x.
intros.
revert o H H1 x H2; elim H0 using isOrd_ind; intros.
rewrite Tcont in H5; trivial; destruct H5. 
rewrite TR_eqn0; auto with *.
rewrite TR_eqn0; auto with *.
symmetry; apply Firr; intros; auto with *.
 symmetry.
 rewrite <- H11.
 eauto using isOrd_inv.

 rewrite Tcont; eauto.
Qed.

End TR_irrel.


Section TRirr.

Variable F : (set->set)->set->set.
Hypothesis Fm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) F.
Variable T : set -> set.
Variable Tcont : forall o z, isOrd o ->
  (z \in T o <-> exists2 o', o' \in o & z \in T (osucc o')).
Hypothesis Fext : forall o f f',
  isOrd o ->
  eq_fun (T o) f f' ->
  eq_fun (T (osucc o)) (F f) (F f').

Lemma Tmono o o': isOrd o -> isOrd o' -> o \incl o' -> T o \incl T o'.
red; intros.
rewrite Tcont in H2; auto.
destruct H2.
rewrite Tcont; trivial.
exists x; auto.
Qed.

(*
Definition iter f o x :=
  let fx := replf o (fun o' => F (f o') x) in
  union (subset fx (fun y =>
    exists2 o', o' \in o &
    forall o'', isOrd o'' -> o' \incl o'' -> o'' \in o ->
    F (f o'') x == y)).

Lemma ef o x f :
  morph2 f ->
  ext_fun o (fun o' => F (f o') x).
do 2 red; intros.
apply Fm; auto with *.
Qed.
Hint Resolve ef.

Lemma iter_def : forall o o' x f,
  isOrd o ->
  o' \in o ->
  x \in T (osucc o') ->
  morph2 f ->
  (forall x x' o o', isOrd o -> isOrd o' -> x \in T o -> x == x' -> o \incl o' ->
  f o x == f o' x')->
  iter f o x == F (f o') x.
intros o o' x f oo o'o xty fm firr.
assert (os : forall x, x \in o -> isOrd x) by eauto using isOrd_inv.
unfold iter.
apply eq_intro; intros.
 rewrite union_ax in H; destruct H.
 rewrite subset_ax in H0; destruct H0.
 destruct H1.
 rewrite H1 in H,H0; clear x0 H1.
 rewrite replf_ax in H0; auto.
 destruct H0.
 destruct H2.
 revert H; apply eq_elim.
 transitivity (F (f (osup2 o' x2)) x).
  symmetry; apply H3; trivial.
   apply isOrd_osup2; auto.
   apply osup2_incl2; auto.
   apply osup2_lt; auto.

  apply Fext with (o:=o'); auto with *; trivial.
  red; intros.
  symmetry; apply firr; auto with *.
   apply isOrd_osup2; auto.

   rewrite <- H4; trivial.

   apply osup2_incl1; auto.

 apply union_intro with (F (f o') x); trivial.
 apply subset_intro.
  rewrite replf_ax; auto.
  exists o'; auto with *.

  exists o'; trivial; intros.
  symmetry; apply (Fext o'); auto with *.
  red; intros.
  apply firr; auto with *.
Qed.

Let iter_ok :
   forall (o o' : set) (f f' : set -> set -> set) (x x' : set),
   (forall o' o'' x x' : set,
    o' \in o -> o' == o'' -> x == x' -> f o' x == f' o'' x') ->
   o == o' -> x == x' -> iter f o x == iter f' o' x'.
intros.
unfold iter.
apply union_morph.
apply subset_morph.
 apply replf_morph; auto.
 red; intros.
 apply Fm; auto.
 red; intros; apply H; auto.

 red; intros.
 apply ex2_morph; red; intros.
  rewrite H0; reflexivity.

  apply fa_morph; intros.
  apply fa_morph; intros.
  apply fa_morph; intros.
  rewrite <- H0.
  apply fa_morph; intros.
  assert (F (f x1) x == F (f' x1) x').
   apply Fm; auto.
   red; intros; apply H; auto with *.
  rewrite H3; reflexivity.
Qed.

Lemma iter_ext o o' f f' x x' :
   morph2 f ->
   morph2 f' ->
   isOrd o ->
   isOrd o' ->
   (forall o'2 o'' x2 x'1 : set,
    o'2 \in o ->
    o'' \in o' ->
    o'2 \incl o'' ->
    x2 \in T o'2 ->
    x2 == x'1 -> f o'2 x2 == f' o'' x'1) ->
   o \incl o' ->
   x \in T o ->
   x == x' -> iter f o x == iter f' o' x'.
intros fm fm'; intros.
unfold iter; apply eq_intro; intros.
 rewrite union_ax in H5; destruct H5.
 rewrite subset_ax in H6; destruct H6.
 destruct H7.
 rewrite H7 in H5,H6; clear x0 H7.
 rewrite replf_ax in H6; auto.
 destruct H6.
 destruct H8.
 apply union_intro with x1; trivial.
 assert (os : forall x, x \in o -> isOrd x) by eauto using isOrd_inv.
 assert (os' : forall x, x \in o' -> isOrd x) by eauto using isOrd_inv.
 rewrite Tcont in H3; trivial.
 destruct H3.
 assert (forall z, osup2 x2 x3 \incl z -> z \in o' -> F (f x0) x == F (f' z) x').
  intros.
  transitivity (F (f (osup2 x2 x3)) x).
   symmetry; rewrite <- H7; apply H9; auto.
    apply isOrd_osup2; auto.
    apply osup2_incl1; auto.
    apply osup2_lt; auto.
 
   apply Fext with x3; auto with *.
   red; intros.
   apply H1; auto with *.
    apply osup2_lt; auto.
    revert H13; apply Tmono; auto with *.
     apply isOrd_osup2; auto.
     apply osup2_incl2; auto.
 apply subset_intro.
  rewrite replf_ax; auto.
  exists (osup2 x2 x3); auto.
   apply osup2_lt; auto.
  rewrite H7; apply H11; auto with *.
  apply osup2_lt; auto.

  exists (osup2 x2 x3); auto.
   apply osup2_lt; auto.
  intros.
  rewrite H7; symmetry.
  apply H11; auto.

 rewrite union_ax in H5; destruct H5.
 rewrite subset_ax in H6; destruct H6.
 destruct H7.
 rewrite H7 in H5,H6; clear x0 H7.
 rewrite replf_ax in H6; auto.
 destruct H6.
 destruct H8.
 apply union_intro with x1; trivial.
 assert (os : forall x, x \in o' -> isOrd x) by eauto using isOrd_inv.
 rewrite Tcont in H3; trivial.
 destruct H3.
 assert (forall z, x3 \incl z -> z \in o -> F (f z) x == F (f' x0) x').
  intros.
  transitivity (F (f' (osup2 x2 z0)) x').
   apply Fext with x3; auto with *.
   red; intros.
   apply H1; auto with *.
    apply osup2_lt; auto.
    apply osup2_incl2; auto.

    revert H13; apply Tmono; auto with *.

   rewrite <- H7; apply H9; auto.
    apply isOrd_osup2; auto.
    apply osup2_incl1; auto.
    apply osup2_lt; auto.

 apply subset_intro.
  rewrite replf_ax; auto.
  exists x3; trivial.
  symmetry; rewrite H7.
  auto with *.

  exists x3; intros; auto.
  rewrite H7.
  auto with *.
Qed.


Lemma TR_irr : forall o o' x,
  isOrd o ->
  o' \in o ->
  x \in T (osucc o') ->
  TR iter o x == F (TR iter o') x.
intros.
rewrite TR_eqn0; auto with *.
apply iter_def with (3:=H1); trivial.
 apply TR_morph.
intros.
rewrite <- H5.
symmetry; apply TR_irrel with T; auto with *.
apply iter_ext.
Qed.
*)







(* Limit of a sequence of functions by retaining values that do not
   change after some iteration stage *)
Definition dom_fun (f:set->set->set) (o:set) (x:set) (o':set) :=
  forall o'', o' \incl o'' -> o'' \in o -> f o'' x == f o' x.
Definition sup_fun (f:set->set->set) (o:set) (x:set) :=
  sup (subset o (dom_fun f o x)) (fun o' => f o' x).

Definition iter (F:(set->set)->set->set) f o x := F (sup_fun f o) x.

(*
Section TRDom.

Variable F : (set->set)->set->set.
Variable T : set -> set.
Variable Tcont : forall o z, isOrd o ->
  (z \in T o <-> exists2 o', o' \in o & z \in T (osucc o')).
*)

Definition TRF := TR(iter F).

Lemma iter_def : forall o o' x f,
  isOrd o ->
  o' \in o ->
  x \in T (osucc o') ->
  morph2 f ->
  (forall x x' o o', isOrd o -> isOrd o' ->
   x \in T o -> x == x' -> o \incl o' ->
   f o x == f o' x')->
  iter F f o x == F (f o') x.
intros o o' x f oo o'o xty fm firr.
assert (os : forall x, x \in o -> isOrd x) by eauto using isOrd_inv.
unfold iter.
red in Fext; apply Fext with o'; auto with *.
red; intros.
unfold sup_fun.
rewrite eq_set_ax; intro z.
rewrite sup_ax.
2:do 2 red; intros; apply fm; auto with *.
split; intros.
 destruct H1.
 rewrite subset_ax in H1; destruct H1.
 destruct H3.
 red in H4.
 revert H2; apply eq_elim.
 rewrite H3 in H1|-*.
 transitivity (f (osup2 x2 o') x0).
  symmetry; apply H4; auto.
   apply osup2_incl1; auto.

   apply osup2_lt; auto.

 symmetry; apply firr; auto with *.
  apply isOrd_osup2; auto.

  rewrite <- H0; trivial.

  apply osup2_incl2; auto.

 exists o'.
 2:rewrite H0; trivial.
 apply subset_intro; trivial.
 red; intros.
 symmetry; apply firr; auto with *.
Qed.


Let iter_ok : forall o o' f f' x x',
   isOrd o ->
   (forall o' o'' x x' : set,
    o' \in o -> o' == o'' -> x == x' -> f o' x == f' o'' x') ->
   o == o' -> x == x' -> iter F f o x == iter F f' o' x'.
intros.
unfold iter.
apply Fm; trivial.
red; intros.
unfold sup_fun.
apply sup_morph.
 apply subset_morph; trivial.
 red; intros.
 unfold dom_fun.
 apply fa_morph; intro.
 rewrite H1.
 apply fa_morph; intro.
 apply fa_morph; intro.
 rewrite (H0 x2 x2 x0 y); auto with *.
  2:rewrite H1; trivial.
 rewrite (H0 x1 x1 x0 y); auto with *.

 red; intros.
 apply subset_elim1 in H4; auto.
Qed.

Lemma iter_ext o o' f f' x x' :
   morph2 f ->
   morph2 f' ->
   isOrd o ->
   isOrd o' ->
   (forall o'2 o'' x2 x'1 : set,
    o'2 \in o ->
    o'' \in o' ->
    o'2 \incl o'' ->
    x2 \in T o'2 ->
    x2 == x'1 -> f o'2 x2 == f' o'' x'1) ->
   o \incl o' ->
   x \in T o ->
   x == x' -> iter F f o x == iter F f' o' x'.
intros fm fm'; intros.
assert (os : forall x, x \in o -> isOrd x) by eauto using isOrd_inv.
assert (os' : forall x, x \in o' -> isOrd x) by eauto using isOrd_inv.
unfold iter.
rewrite Tcont in H3; trivial; destruct H3 as (ox,oxlt,tyx).
apply (Fext ox); auto.
clear x x' tyx H4.
intros x x' tyx eqx.
unfold sup_fun.
apply eq_set_ax; intros z.
rewrite sup_ax.
2:do 2 red; intros; apply fm; auto with *.
rewrite sup_ax.
2:do 2 red; intros; apply fm'; auto with *.
split; destruct 1 as (od,ins,zin).
 rewrite subset_ax in ins; destruct ins as (odlt,(od',e,odom)).
 rewrite e in odlt, zin; clear od e; rename od' into od.
 assert (forall z, osup2 ox od \incl z -> z \in o' -> f od x == f' z x').
  intros.
  transitivity (f (osup2 ox od) x).
   red in odom.
   symmetry; apply odom; auto.
    apply osup2_incl2; auto.
    apply osup2_lt; auto.
 
   apply H1; auto with *.
    apply osup2_lt; auto.

    revert tyx; apply Tmono; auto with *.
     apply isOrd_osup2; auto.
     apply osup2_incl1; auto.
 exists (osup2 ox od).
  apply subset_intro; auto.
   apply osup2_lt; auto.

   red; intros.
   transitivity (f (osup2 ox od) x').
    symmetry; apply H1; auto with *.
     apply osup2_lt; auto.

     rewrite <- eqx; revert tyx; apply Tmono; auto.
      apply isOrd_osup2; auto.
      apply osup2_incl1; auto.

    apply H1; auto with *.
     apply osup2_lt; auto.
     apply osup2_lt; auto.

     rewrite <- eqx; revert tyx; apply Tmono; auto.
      apply isOrd_osup2; auto.
      apply osup2_incl1; auto.

   rewrite <- H3; auto with *.
   apply osup2_lt; auto.

 rewrite subset_ax in ins; destruct ins as (odlt,(od',e,odom)).
 rewrite e in odlt, zin; clear od e; rename od' into od.
 assert (forall z, ox \incl z -> z \in o -> f z x == f' od x').
  intros.
  transitivity (f' (osup2 od z0) x').
   apply H1; auto with *.
    apply osup2_lt; auto.
    apply osup2_incl2; auto.

    revert tyx; apply Tmono; auto with *.

   red in odom.
   apply odom; auto.
    apply osup2_incl1; auto.
    apply osup2_lt; auto.
 exists ox.
  apply subset_intro; trivial.
  red; intros.
  transitivity (f' o'' x').
   apply H1; auto with *.
   revert tyx; apply Tmono; auto.

   symmetry; apply H1; auto with *.

  rewrite H3; auto with *.
Qed.

Lemma TRF_indep : forall o o' x,
  isOrd o ->
  o' \in o ->
  x \in T (osucc o') ->
  TRF o x == F (TRF o') x.
intros.
unfold TRF. 
rewrite TR_eqn0; auto with *.
apply iter_def with (3:=H1); trivial.
 apply TR_morph.
intros.
rewrite <- H5.
symmetry; apply TR_irrel with T; auto with *.
apply iter_ext.
Qed.

End TRirr.



(* --> ZFfix *)
Lemma TI_op_mono o o' f f' :
  morph1 f ->
  morph1 f' -> 
  (incl_set ==> incl_set)%signature f f' ->
  isOrd o ->
  o == o' ->
  TI f o \incl TI f' o'.
intros.
rewrite <- H3.
clear o' H3.
elim H2 using isOrd_ind; intros.
red; intros.
apply TI_elim in H6; trivial.
destruct H6.
apply TI_intro with x; trivial.
revert H7; apply H1; auto.
Qed.

Section NestedInductive.

  Variable F : set -> set -> set.
  Hypothesis Fmono : Proper (incl_set==>incl_set==>incl_set) F.

  Instance Fmono_morph2 : morph2 F.
Admitted.


  Let Fnest_mono X : Proper (incl_set ==> incl_set) (fun Y => F X Y).
do 2 red; intros; apply Fmono; auto with *.
Qed.

  Let Fnest_morph X : morph1 (fun Y => F X Y).
apply Fmono_morph; trivial.
Qed.

(** F(X,Y): Y is the nested type with (uniform) parameter X *)

(* F(X,Y) iso { x:A | B x -> X & C x -> Y } *)
Hypothesis A : set.
Hypothesis B : set -> set.
Hypothesis C : set -> set.
Hypothesis Bm : morph1 B.
Hypothesis Cm : morph1 C.
Hypothesis Fdef : forall X Y,
  F X Y == sigma A (fun x => prodcart (cc_arr (B x) X) (cc_arr (C x) Y)). 

Let ACm : morph1 (W_F A C).
do 2 red; intros.
apply W_F_ext; auto with *.
red; auto with *.
Qed.

(* F X Y  (iso)  { x:A(Y) & B(Y,x) -> X }
                 { x:A'(X) & B'(X,x) -> Y
*)

Lemma F_elim x X Y :
  x \in F X Y ->
  fst x \in A /\
  (forall b, b \in B (fst x) -> cc_app (fst (snd x)) b \in X) /\
  (forall i, i \in C (fst x) -> cc_app (snd (snd x)) i \in Y) /\
  x == (couple (fst x)
       (couple (cc_lam (B (fst x)) (cc_app (fst (snd x))))
               (cc_lam (C (fst x)) (cc_app (snd (snd x)))))).
intros.
rewrite Fdef in H.
assert (ty1 := fst_typ_sigma _ _ _ H).
assert (eq1 := surj_pair _ _ _ (subset_elim1 _ _ _ H)).
apply snd_typ_sigma with (y:=fst x) in H; auto with *.
 split; trivial.
 assert (ty2 := fst_typ _ _ _ H).
 assert (eq2 := surj_pair _ _ _ H).
 apply snd_typ in H.
 split; [|split]; intros.
  apply cc_arr_elim with (1:=ty2); trivial.

  apply cc_arr_elim with (1:=H); trivial.

  transitivity (couple (fst x) (snd x)); auto with *.
  apply couple_morph; auto with *.
  rewrite eq2; apply couple_morph; auto with *.
   rewrite cc_eta_eq with (1:=ty2).
   apply cc_lam_ext; auto with *.
   red; intros.
   rewrite fst_def.
   rewrite <- H1.
   rewrite cc_beta_eq; auto with *.
   do 2 red; intros; apply cc_app_morph; auto with *.

   rewrite cc_eta_eq with (1:=H).
   apply cc_lam_ext; auto with *.
   red; intros.
   rewrite snd_def.
   rewrite <- H1.
   rewrite cc_beta_eq; auto with *.
   do 2 red; intros; apply cc_app_morph; auto with *.

 do 2 red; intros.
 rewrite <- H1; reflexivity.
Qed.
  
Lemma F_intro a fb fc X Y :
  ext_fun (B a) fb ->
  ext_fun (C a) fc -> 
  a \in A ->
  (forall b, b \in B a -> fb b \in X) ->
  (forall i, i \in C a -> fc i \in Y) ->
  couple a (couple (cc_lam (B a) fb) (cc_lam (C a) fc)) \in F X Y.
intros.
rewrite Fdef.
apply couple_intro_sigma; trivial.
 do 2 red; intros.
 rewrite <- H5; reflexivity.
apply couple_intro; apply cc_arr_intro; intros; auto with *.
Qed.



Let A'i := TI (W_F A C).

Let B'0 := List (union2 (sup A C) (sup A B)).

(* B_ok x' b means that b is an element of B'0 that is
   correctly indexed by x':A' *)
Inductive B_ok (x':set) (b:set) : Prop :=
| Bnil l :
   l \in B (fst x') ->
   b == Cons l Nil ->
   B_ok x' b
| Bcons i b' :
   i \in C (fst x') ->
   B_ok (cc_app (snd x') i) b' ->
   b == Cons i b' ->
   B_ok x' b.

Let B' x' := subset B'0 (B_ok x').

Instance B'm : morph1 B'.
do 2 red; intros.
apply subset_morph; auto with *.
assert (Proper (eq_set ==> eq_set ==> impl) B_ok).
 do 4 red; intros.
 revert y0 y1 H0 H1; elim H2; intros.
  rewrite H3 in H0; rewrite H4 in H1; apply Bnil with l; trivial.
  rewrite H5 in H0; rewrite H6 in H4; apply Bcons with i b'; trivial.
  apply H3; auto with *.
  rewrite H5; reflexivity.
split; apply H0; auto with *.
Qed.

Lemma B'notmt x' z : z \in B' x' -> ~ z == Nil.
red; intros.
rewrite H0 in H; clear z H0.
unfold B' in H; rewrite subset_ax in H; destruct H.
destruct H0.
destruct H1.
 rewrite H2 in H0; apply discr_mt_pair in H0; trivial.
 rewrite H3 in H0; apply discr_mt_pair in H0; trivial.
Qed.


Lemma fst_A'i o x' :
  isOrd o -> x' \in A'i o -> fst x' \in A.
intros.
apply TI_elim in H0; trivial.
destruct H0.
apply fst_typ_sigma in H1; trivial.
Qed.

Lemma B'nil o x' l :
  isOrd o ->
  x' \in A'i o ->
  l \in B (fst x') ->
  Cons l Nil \in B' x'.
intros.
apply subset_intro.
 apply Cons_typ;[|apply Nil_typ].
 apply union2_intro2.
 rewrite sup_ax; auto with *.
 exists (fst x'); trivial.
 apply fst_A'i with o; trivial.

 apply Bnil with l; auto with *.
Qed.

Lemma B'cons o x' i b' :
  isOrd o ->
  x' \in A'i o ->
  i \in C (fst x') ->
  b' \in B' (cc_app (snd x') i) ->
  Cons i b' \in B' x'.
intros.
apply subset_intro.
 apply Cons_typ.
  apply union2_intro1.
  rewrite sup_ax; auto with *.
  exists (fst x'); trivial.
  apply fst_A'i with o; trivial.

  apply subset_elim1 in H2; trivial.

 apply subset_elim2 in H2; destruct H2.
 apply Bcons with i x; auto with *.
 rewrite H2; reflexivity.
Qed.

Lemma B'_ind : forall (P:set->set->Prop),
  (forall x' b l,
   l \in B (fst x') ->
   b == Cons l Nil -> P x' b) ->
  (forall x' b i b',
   i \in C (fst x') ->
   b' \in B' (cc_app (snd x') i) ->
   P (cc_app (snd x') i) b' ->
   b == Cons i b' ->
   P x' b) ->
  forall x' z,
  z \in B' x' ->
  P x' z.
intros.
unfold B' in H1; rewrite subset_ax in H1; destruct H1.
destruct H2.
revert z H1 H2; induction H3; intros.
 rewrite <- H4 in H2; eauto with *.

 rewrite <- H5 in H2.
 assert (b' \in B'0).
  revert H2; apply List_ind with (4:=H4); intros.
   do 2 red; intros.
   rewrite H2; reflexivity.

   apply discr_mt_pair in H2; contradiction.

   apply couple_injection in H8; destruct H8.
   rewrite <- H9; trivial.
 apply H0 with i b'; auto with *.
 apply subset_intro; trivial.
Qed.

Lemma B'_eqn o x' z :
  isOrd o ->
  x' \in A'i o -> 
  (z \in B' x' <->
   (exists2 l, l \in B (fst x') & z == Cons l Nil) \/
   (exists2 i, i \in C (fst x') & exists2 b', b' \in B' (cc_app (snd x') i) & z == Cons i b')).
split; intros.
 apply B'_ind with (3:=H1); intros.
  left; exists l; trivial.

  right ;exists i; trivial; exists b'; trivial.

 destruct H1 as [(l,?,?)|(i,?,(b',?,?))].
  rewrite H2; apply B'nil with o; trivial.
  rewrite H3; apply B'cons with o; trivial.
Qed.


Parameter B'case : (set -> set) -> (set->set->set) -> set -> set.

Lemma B'case_ext a' f g :
  (forall l l', l \in B (fst a') -> l == l' -> f l == f l') ->
  (forall i i' b b', i \in C (fst a') -> i==i' -> b \in B' (cc_app (snd a') i) -> b==b' ->
   g i b == g i' b') ->
  ext_fun (B' a') (B'case f g).
Admitted.

Instance B'case_morph : Proper ((eq_set==>eq_set)==>(eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) B'case.
Admitted.

Parameter B'case_typ : forall P f g o x' b,
  isOrd o ->
  x' \in A'i o ->
  b \in B' x' ->
  (forall l, l \in B (fst x') -> f l \in P) ->
  (forall i b', i \in C (fst x') -> b' \in B' (cc_app (snd x') i) -> g i b' \in P) ->
  B'case f g b \in P.

Parameter B'case_nil : forall f g l,
  B'case f g (Cons l Nil) == f l.

Parameter B'case_cons : forall f g i b',
  B'case f g (Cons i b') == g i b'.

Parameter B'case_nil' : forall x f g l,
  x == Cons l Nil ->
  B'case f g x == f l.

Parameter B'case_cons' : forall x f g i b',
  x == Cons i b' ->
  B'case f g x == g i b'.

(** Isomorphism *)

(*
Let fcm :
  a \in A ->
  ext_fun  fc
  ext_fun (C a) (fun i => fst (f (cc_app (snd (snd x)) i)))
*)

(* TI F_X o -> A'i (osucc o) *)
Let a'of a fc :=
  couple a (cc_lam (C a) (fun i => fst (fc i))).

Let a'of_typ o a fc X :
  isOrd o ->
  a \in A ->
  typ_fun fc (C a) (W_F (A'i o) B' X) ->
  a'of a fc \in A'i(osucc o).
unfold a'of; intros.
unfold A'i; rewrite TI_mono_succ; auto with *.
2:apply W_F_mono; auto with *.
apply W_F_intro; intros; auto with *.
 admit.

 apply H1 in H2.
 apply fst_typ_sigma in H2; trivial.
Qed.

Definition g f t (* f:Y->WF(A',B',X), t:F X Y *) := (* W_F(A'+,B',X) *)
  let a := fst t in (*A*)
  let fb := cc_app (fst (snd t)) in (* B a -> X *)
  let fc := cc_app (snd (snd t)) in (* C a -> Y *)
  let a' := couple a (cc_lam (C a) (fun i => fst (f (fc i)))) in
  let fb' := (* B' a' -> X *)
    B'case (fun l (* B a *) => fb l)
           (fun i b' => cc_app (snd (f (fc i))) b') in
  couple (a'of a (fun i => f(fc i))) (cc_lam (B' (a'of a (fun i =>f(fc i)))) fb').


Lemma gext f X Y :
  ext_fun Y f ->
  ext_fun (F X Y) (g f).
do 2 red; intros.
unfold g.
apply couple_morph.
Admitted.

Lemma gext' f f' X Y :
  eq_fun Y f f' ->
  eq_fun (F X Y) (g f) (g f').
Admitted.


Instance gm :  Proper ((eq_set==>eq_set)==>eq_set==>eq_set) g.
do 3 red; intros.
assert (fm := fst_morph _ _ H0).
assert (cmorph := fun x x' e y y' e' =>
  couple_morph x x' e y y' (e' e)).
apply cmorph; intros.
 apply couple_morph; auto.
 apply cc_lam_morph; auto.
 red; intros.
 apply fst_morph; apply H.
 rewrite H0; rewrite H1; reflexivity.

 apply cc_lam_morph; auto.
  apply B'm; auto.

  red; intros.
  apply B'case_morph; trivial.
   red; intros.
   rewrite H0 ;rewrite H2; reflexivity.

   do 2 red; intros.
   apply cc_app_morph; auto with *.
   apply snd_morph; apply H.
   rewrite H0; rewrite H2; reflexivity.
Qed.
(*
Lemma ext_gfo o f x :
  ext_fun o (fun o' => g (f o') x).
Admitted.
Hint Resolve ext_gfo.

Definition iter (F:(set->set)->set->set) Fsub o x :=
  let fx := replf o (fun o' => F (Fsub o') x) in
  union (subset fx (fun y =>
    exists2 o', o' \in o &
    forall o'', isOrd o'' -> o' \incl o'' -> o'' \in o ->
    F (Fsub o'') x == y)).

Lemma iter_def : forall o o' x f X,
isOrd o ->
o' \in o ->
x \in F X (TI(fun Y=>F X Y) o') ->
(forall x x' o o', isOrd o -> isOrd o' -> x \in TI(fun Y=>F X Y) o -> x == x' ->o \incl o' ->
  f o x == f o' x')->
iter g f o x == g (f o') x.
intros o o' x f X oo o'o xty firr.
assert (os : forall x, x \in o -> isOrd x) by eauto using isOrd_inv.
unfold iter.
apply eq_intro; intros.
 rewrite union_ax in H; destruct H.
 rewrite subset_ax in H0; destruct H0.
 destruct H1.
 rewrite H1 in H,H0; clear x0 H1.
 rewrite replf_ax in H0; auto.
 destruct H0.
 destruct H2.
 revert H; apply eq_elim.
 transitivity (g (f (osup2 o' x2)) x).
  symmetry; apply H3; trivial.
   apply isOrd_osup2; auto.
   apply osup2_incl2; auto.
   apply osup2_lt; auto.

  apply gext' with (X:=X)(Y:=TI(fun Y=>F X Y)o'); auto with *.
  red; intros.
  symmetry; apply firr; auto with *.
   apply isOrd_osup2; auto.

   rewrite <- H4; revert H; apply TI_mono; auto with *.

   apply osup2_incl1; auto.

 apply union_intro with (g (f o') x); trivial.
 apply subset_intro.
  rewrite replf_ax; auto.
  exists o'; auto with *.

  exists o'; trivial; intros.
  symmetry; apply gext' with (X:=X)(Y:=TI(fun Y=>F X Y) o'); auto with *.
  red; intros.
  apply firr; auto with *.
Qed.

Let iter_ok :
   forall (o o' : set) (f f' : set -> set -> set) (x x' : set),
   (forall o' o'' x x' : set,
    o' \in o -> o' == o'' -> x == x' -> f o' x == f' o'' x') ->
   o == o' -> x == x' -> iter g f o x == iter g f' o' x'.
intros.
unfold iter.
apply union_morph.
apply subset_morph.
 apply replf_morph; auto.
 red; intros.
 apply gm; auto.
 red; intros; apply H; auto.

 red; intros.
 apply ex2_morph; red; intros.
  rewrite H0; reflexivity.

  apply fa_morph; intros.
  apply fa_morph; intros.
  apply fa_morph; intros.
  rewrite <- H0.
  apply fa_morph; intros.
  assert (g (f x1) x == g (f' x1) x').
   apply gm; auto.
   red; intros; apply H; auto with *.
  rewrite H3; reflexivity.
Qed.

Lemma iter_ext X o o' f f' x x' :
   isOrd o ->
   isOrd o' ->
   (forall o'2 o'' x2 x'1 : set,
    o'2 \in o ->
    o'' \in o' ->
    o'2 \incl o'' ->
    x2 \in TI (fun Y : set => F X Y) o'2 ->
    x2 == x'1 -> f o'2 x2 == f' o'' x'1) ->
   o \incl o' ->
   x \in TI (fun Y : set => F X Y) o ->
   x == x' -> iter g f o x == iter g f' o' x'.
intros.
unfold iter; apply eq_intro; intros.
 rewrite union_ax in H5; destruct H5.
 rewrite subset_ax in H6; destruct H6.
 destruct H7.
 rewrite H7 in H5,H6; clear x0 H7.
 rewrite replf_ax in H6; auto.
 destruct H6.
 destruct H8.
 apply union_intro with x1; trivial.
 assert (os : forall x, x \in o -> isOrd x) by eauto using isOrd_inv.
 assert (os' : forall x, x \in o' -> isOrd x) by eauto using isOrd_inv.
 apply TI_elim in H3;auto.
 destruct H3.
 assert (forall z, osup2 x2 x3 \incl z -> z \in o' -> g (f x0) x == g (f' z) x').
  intros.
  transitivity (g (f (osup2 x2 x3)) x).
   symmetry; rewrite <- H7; apply H9; auto.
    apply isOrd_osup2; auto.
    apply osup2_incl1; auto.
    apply osup2_lt; auto.
 
   apply gext' with (X:=X)(Y:=TI(fun Y=>F X Y) x3); auto with *.
   red; intros.
   apply H1; auto with *.
    apply osup2_lt; auto.

    revert H13; apply TI_mono; auto with *.
     apply isOrd_osup2; auto.
     apply osup2_incl2; auto.
 apply subset_intro.
  rewrite replf_ax; auto.
  exists (osup2 x2 x3); auto.
   apply osup2_lt; auto.
  rewrite H7; apply H11; auto with *.
  apply osup2_lt; auto.

  exists (osup2 x2 x3); auto.
   apply osup2_lt; auto.
  intros.
  rewrite H7; symmetry.
  apply H11; auto.

 rewrite union_ax in H5; destruct H5.
 rewrite subset_ax in H6; destruct H6.
 destruct H7.
 rewrite H7 in H5,H6; clear x0 H7.
 rewrite replf_ax in H6; auto.
 destruct H6.
 destruct H8.
 apply union_intro with x1; trivial.
 assert (os : forall x, x \in o' -> isOrd x) by eauto using isOrd_inv.
 apply TI_elim in H3;auto.
 destruct H3.
 assert (forall z, x3 \incl z -> z \in o -> g (f z) x == g (f' x0) x').
  intros.
  transitivity (g (f' (osup2 x2 z0)) x').
   apply gext' with (X:=X)(Y:=TI(fun Y=>F X Y) x3); auto with *.
   red; intros.
   apply H1; auto with *.
    apply osup2_lt; auto.
    apply osup2_incl2; auto.

    revert H13; apply TI_mono; auto with *.

   rewrite <- H7; apply H9; auto.
    apply isOrd_osup2; auto.
    apply osup2_incl1; auto.
    apply osup2_lt; auto.

 apply subset_intro.
  rewrite replf_ax; auto.
  exists x3; trivial.
  symmetry; rewrite H7.
  auto with *.

  exists x3; intros; auto.
  rewrite H7.
  auto with *.
Qed.



Lemma TR_indep : forall X o o' x,
  isOrd o ->
  o' \in o ->
  x \in F X (TI(fun Y=>F X Y) o') ->
  TR (iter g) o x == g (TR (iter g) o') x.
intros.
rewrite TR_eqn0; auto with *.
apply iter_def with (3:=H1); trivial.
intros.
rewrite <- H5.
symmetry; apply TR_indep0 with (TI (fun Y => F X Y)); auto with *.
 intros.
 rewrite TI_mono_eq; auto.
 rewrite sup_ax; auto with *.
 do 2 red; intros; apply TI_morph; apply osucc_morph; trivial.

 apply iter_ext.
Qed.
*)

Hint Resolve W_F_mono.


Lemma  ecase1 : forall Y Z a g x f,
  iso_fun Y Z f ->
  typ_fun (cc_app (snd (snd x))) (C a) Y ->
  ext_fun (B' (a'of a g))
     (B'case (fun l => cc_app (fst (snd x)) l)
        (fun i b' => cc_app (snd (f (cc_app (snd (snd x)) i))) b')).
intros.
apply B'case_ext; intros.
 rewrite H2; reflexivity.

 apply cc_app_morph; auto with *.
 apply snd_morph.
 unfold a'of in H1; rewrite fst_def in H1.
 apply (iso_funm H); auto.
 rewrite H2; reflexivity.
Qed.



Lemma giso Y X f o:
  isOrd o ->
  iso_fun Y (W_F (A'i o) B' X) f ->
  iso_fun (F X Y) (W_F (W_F A C (A'i o)) B' X) (g f).
intros.
assert (ec1 := fun a g x => ecase1 _ _ a g x _ H0).
assert (essf1 : forall x,
  typ_fun (cc_app (snd (snd x))) (C (fst x)) Y ->
  ext_fun (C (fst x)) (fun i => fst (f (cc_app (snd (snd x)) i)))).
 do 2 red; intros.
 apply fst_morph; apply (iso_funm H0); auto.
 rewrite H3; reflexivity.
constructor; intros.
 apply gext; trivial.
 apply iso_funm in H0; trivial.

 red; intros.
 apply F_elim in H1; destruct H1 as (ty1,(ty2,(ty3,et1))).
 unfold g.
 apply W_F_intro; intros; auto with *.
  unfold A'i; rewrite <- TI_mono_succ; auto with *.
  apply a'of_typ with X; auto.
  apply iso_typ in H0; red in H0; red; auto.
(*
  apply W_F_intro; intros; auto with *.
   admit.
(* ext_fun (C (fst x)) (fun i : set => fst (f (cc_app (snd (snd x)) i)))*)

   apply iso_typ in H0.
   apply ty3 in H1.
   apply H0 in H1.
   apply fst_typ_sigma in H1; trivial.
*)
   apply B'case_typ with (o:=osucc o) (3:=H1); intros; auto.
apply a'of_typ with X; trivial.
apply iso_typ in H0; red in H0; red; auto.
(* apply ty3 in H2.
     apply (iso_typ H0) in H2.
     apply fst_typ_sigma in H2; trivial.

    rewrite fst_def in H2; auto.

    unfold A'i; rewrite TI_mono_succ; auto with *.
    2:apply W_F_mono; auto with *.
    apply W_F_intro; intros; auto with *.
     admit.

     apply ty3 in H2.
     apply (iso_typ H0) in H2.
     apply fst_typ_sigma in H2; trivial.
*)
    unfold a'of in H2; rewrite fst_def in H2; auto.

    unfold a'of in H2,H3.
    rewrite fst_def in H2.
    rewrite snd_def in H3.
    rewrite cc_beta_eq in H3; auto with *.
     apply ty3 in H2.
     apply (iso_typ H0) in H2.
     apply W_F_elim in H2; auto with *.
     destruct H2 as (_,(?,_)); auto.

 (* injectivity *)
 unfold g in H3.
 apply F_elim in H1; destruct H1 as (ty1,(ty2,(ty3,et))).
 apply F_elim in H2; destruct H2 as (ty1',(ty2',(ty3',et'))).
 destruct WFi_inv with (1:=H3); clear H3; intros; auto with *.
  apply B'm; trivial.
 destruct WFi_inv with (1:=H1); clear H1; intros; auto with *.
 rewrite et; rewrite et'.
 apply couple_morph; trivial.
 apply couple_morph; apply cc_lam_ext; auto.
 red; intros.
 red in H4.
 generalize (H2 (Cons x0 Nil) (Cons x'0 Nil)).
 rewrite B'case_nil.
 rewrite B'case_nil.
 intros h; apply h.
  apply B'nil with (osucc o); auto.
apply a'of_typ with X; auto.
red; apply iso_typ in H0; auto.
(*    unfold A'i; rewrite TI_mono_succ; auto with *.
    2:apply W_F_mono; auto with *.
    apply W_F_intro; intros; auto with *.
     admit.

     apply ty3 in H8.
     apply (iso_typ H0) in H8.
     apply fst_typ_sigma in H8; trivial.
*)
    unfold a'of; rewrite fst_def; trivial.

   rewrite H5; reflexivity.

  red; intros.
  rewrite <- H5; clear x'0 H5.
  assert (H4' := H4 _ _ H1 (reflexivity _)).
  assert (tyf := ty3); assert (tyf' := ty3').
  specialize tyf with (1:=H1).
  rewrite H3 in H1; specialize tyf' with (1:=H1).
  apply (iso_inj H0); auto.
  apply (iso_typ H0) in tyf.
  apply (iso_typ H0) in tyf'.
  rewrite WF_eta with (2:=tyf); auto with *.
  rewrite WF_eta with (2:=tyf'); auto with *.
  unfold WFmap.
  apply couple_morph; trivial.
  apply cc_lam_ext.
   apply B'm; trivial.

   red; intros.
   red in H2.
   generalize (H2 (Cons x0 x1) (Cons x0 x'0)).
   rewrite B'case_cons.
   rewrite B'case_cons.
   intros h; apply h.
    apply B'cons with (osucc o); auto.
apply a'of_typ with X; trivial.
red; apply iso_typ in H0; auto.
(*     unfold A'i; rewrite TI_mono_succ; auto with *.
     2:apply W_F_mono; auto with *.
     apply W_F_intro; intros; auto with *.
      admit.

      apply ty3 in H9.
      apply (iso_typ H0) in H9.
      apply fst_typ_sigma in H9; trivial.
*)
     unfold a'of; rewrite fst_def; trivial.
     rewrite H3; trivial.

     unfold a'of; rewrite snd_def.
     rewrite cc_beta_eq; auto with *.
     rewrite H3; trivial.

    rewrite H6; reflexivity.

 (* surj *)
 apply W_F_elim in H1; auto with *.
 destruct H1 as (tya',(tyb',et)).
 destruct W_F_elim with (2:=tya') as (tya,(tyf,et')); auto with *.
 pose (fb' :=  fun i => couple (cc_app (snd (fst y)) i)
   (cc_lam (B' (cc_app (snd (fst y)) i))
      (fun b' : set => cc_app (snd y) (Cons i b')))).
 assert (fb'ty : forall i, i \in C (fst (fst y)) -> fb' i \in W_F (A'i o) B' X).
  intros; unfold fb'.
  apply W_F_intro; intros; auto with *.
   do 2 red; intros.
   rewrite H3; reflexivity.

   apply tyb'.
   apply B'cons with (osucc o); auto.
   unfold A'i; rewrite TI_mono_succ; auto with *.
 exists
 (let a' := fst y in
  let b' := snd y in
  let x := fst a' in
  let fb b := cc_app b' (Cons b Nil) in
  let fc i := iso_inv Y f (fb' i) in
  couple x (couple (cc_lam (B x) fb) (cc_lam (C x) fc))).
  apply F_intro; intros; auto.
   admit. (* cc_app *)
   admit. (* iso_inv *)

   apply tyb'.
   apply B'nil with (osucc o); auto.
   unfold A'i; rewrite TI_mono_succ; auto with *.

   apply (iso_inv_typ H0).
   apply fb'ty; trivial.

  rewrite et.
  apply couple_morph.
   rewrite et'; apply couple_morph.
    simpl.
    rewrite fst_def; reflexivity.

    symmetry; apply cc_lam_ext; simpl; intros.
     rewrite fst_def; reflexivity.

     red; intros.
     rewrite H2 in H1.
     transitivity (fst (f (iso_inv Y f (fb' x')))).
      rewrite iso_inv_eq with (1:=H0); auto.
      unfold fb'; rewrite fst_def.
      rewrite H2; reflexivity.

      apply fst_morph.
      apply (iso_funm H0).
       apply (iso_inv_typ H0); auto.

       rewrite snd_def.
       rewrite snd_def.
       rewrite cc_beta_eq; auto with *.
       admit. (* iso_inv *)

   symmetry; apply cc_lam_ext.
    simpl.
    apply B'm.
    transitivity (couple (fst (fst y))
                  (cc_lam (C (fst (fst y))) (cc_app (snd (fst y))))); auto with *.
     apply couple_morph.
      rewrite fst_def; auto with *.

      symmetry; apply cc_lam_ext.
       rewrite fst_def; reflexivity.

       red; intros.
       rewrite fst_def in H1.
   transitivity (fst (f (iso_inv Y f (fb' x)))).
      apply fst_morph.
      symmetry; apply (iso_funm H0).
       apply (iso_inv_typ H0); auto.

       rewrite snd_def.
       rewrite snd_def.
       rewrite cc_beta_eq; auto with *.
       admit. (* iso_inv *)

      rewrite iso_inv_eq with (1:=H0); auto.
      unfold fb'; rewrite fst_def.
      rewrite H2; reflexivity.

    red; intros.
    specialize tyb' with (1:=H1).
    rewrite H2 in H1|-*.
    rewrite B'_eqn with (o:=osucc o) in H1; auto.
     destruct H1 as [(l,?,eqx')|(i,?,(b',?,eqx'))].
      rewrite B'case_nil' with (l:=l); [|rewrite eqx';reflexivity].
      rewrite snd_def.
      rewrite fst_def.
      rewrite eqx'.
      rewrite cc_beta_eq; auto with *.
      admit.

      rewrite B'case_cons' with (1:=eqx').
    transitivity
       (cc_app (snd (f (iso_inv Y f (fb' i)))) b').
      rewrite iso_inv_eq with (1:=H0); auto.
      unfold fb'; rewrite snd_def.
      rewrite eqx'.
      rewrite cc_beta_eq; auto with *.
      admit.

      apply cc_app_morph; auto with *.
      apply snd_morph.
      apply (iso_funm H0).
       apply (iso_inv_typ H0); auto.

       rewrite snd_def.
       rewrite snd_def.
       rewrite cc_beta_eq; auto with *.
       admit. (* iso_inv *)

    unfold A'i; rewrite TI_mono_succ; auto with *.
Qed.

Lemma TRF_indep_g : forall X o o' x,
  isOrd o ->
  o' \in o ->
  x \in F X (TI(fun Y=>F X Y) o') ->
  TRF g o x == g (TRF g o') x.
intros.
rewrite <- TI_mono_succ in H1; eauto using isOrd_inv.
rewrite TRF_indep with (6:=H1); auto with *.
 intros; rewrite TI_mono_eq; auto with *.
 rewrite sup_ax; auto with *.
 do 2 red; intros; apply TI_morph; auto with *.
 apply osucc_morph; trivial.

 red; intros.
 rewrite TI_mono_succ in H4; auto with *.
 revert H4 H5; apply gext'; trivial.
Qed.

Lemma giso_it X o:
  isOrd o ->
  iso_fun (TI(fun Y=>F X Y)o) (W_F (A'i o) B' X) (TRF g o).
intros.
elim H using isOrd_ind; intros.
constructor; intros.
 do 2 red; intros.
 apply TR_morph; auto with *.

 red; intros.
 assert (yo := isOrd_inv y).
 apply TI_elim in H3; auto with *.
 destruct H3.
 rewrite TRF_indep_g with (3:=H4); auto with *.
 specialize H2 with (1:=H3).
 apply giso in H2; eauto using isOrd_inv.
 apply (iso_typ H2) in H4.
 apply W_F_elim in H4; auto with *.
 destruct H4 as (?,(?,?)).
 rewrite H6; apply W_F_intro; auto with *.
  do 2 red; intros; apply cc_app_morph; auto with *.
 apply TI_intro with x0; auto with *.

 apply TI_elim in H3; auto.
 destruct H3.
 apply TI_elim in H4; auto.
 destruct H4.
 destruct (isOrd_dir _ H0 x0 x1); trivial.
 destruct H9.
 specialize H2 with (1:=H8).
 apply giso in H2; eauto using isOrd_inv.
 assert (x \in F X (TI (fun Y=>F X Y) x2)).
  revert H6; apply Fmono; auto with *.
  apply TI_mono; eauto using isOrd_inv.
 assert (x' \in F X (TI (fun Y=>F X Y) x2)).
  revert H7; apply Fmono; auto with *.
  apply TI_mono; eauto using isOrd_inv.
 clear H6 H7.
 rewrite TRF_indep_g with (3:=H11) in H5; auto.
 rewrite TRF_indep_g with (3:=H12) in H5; auto.
 apply (iso_inj H2) in H5; trivial.

 apply W_F_elim in H3; auto with *.
 destruct H3 as (?,(?,?)).
 apply TI_elim in H3; auto with *.
 destruct H3.
 specialize H2 with (1:=H3).
 apply giso in H2; eauto using isOrd_inv.
 destruct (iso_surj H2) with y0.
  rewrite H5; apply W_F_intro; auto with *.
  do 2 red; intros; apply cc_app_morph; auto with *.
 rewrite <- TRF_indep_g with (2:=H3)(3:=H7) in H8; auto.
 exists x0; trivial.
 apply TI_intro with x; trivial.
Qed.


Definition nest_pos (o:set) : positive :=
  mkPositive (fun X => TI (fun Y => F X Y) o) (A'i o) B' (TR (iter g) o).

Lemma isPos_nest o :
  isOrd o ->
  isPositive (nest_pos o).
constructor.
 do 2 red; intros.
 simpl.
 apply TI_op_mono; auto with *; apply Fmono_morph;
   do 2 red; intros; apply Fmono; auto with *.

 do 2 red; intros; simpl.
 apply B'm; trivial.

 simpl; intros.
 apply giso_it; trivial.
Qed.



(* Reverse order! *)
(*
Definition g f t (* W_F A' B' X*) := (* N X *)
  let a' := fst t in
  let b' := snd t in
  let x := fst a' in
  let fb b := cc_app b' (Cons b Nil) in
  let fc i :=
    f  (couple (cc_app (snd a') i) (cc_lam (B'(cc_app(snd a') i)) (fun b'' =>
         cc_app b' (Cons i b'')))) in
  couple x (couple (cc_lam (B x) fb) (cc_lam (C x) fc)).

Lemma giso X f o:
  isOrd o ->
  iso_fun (W_F (A'i o) B' X) (TI (fun Y=>F X Y) o) f ->
  iso_fun (W_F (W_F A C (A'i o)) B' X) (F X (TI (fun Y=>F X Y) o)) (g f).
constructor; intros.
 admit.

 red; intros.
 rewrite Fdef.
 unfold g.
 assert (ftyp:=iso_typ H0).
 red in ftyp.
 assert (fst (fst x) \in A).
  apply fst_typ_sigma in H1.
  apply fst_typ_sigma in H1; trivial.
 apply couple_intro_sigma; trivial.
  admit.
 apply couple_intro.
  apply cc_arr_intro; intros.
   admit.
  assert (h := H1).
  apply snd_typ_sigma with (y:=fst x) in h; auto with *.
  2:admit.
  apply cc_arr_elim with (1:=h).
  apply B'nil with (osucc o); auto.
  unfold A'i; rewrite TI_mono_succ; auto.
  2:apply W_F_mono; auto with *.
  apply fst_typ_sigma in H1; trivial.

  apply cc_arr_intro; intros.
   admit.
 apply ftyp.
 assert (cc_app (snd (fst x)) x0 \in (A'i o)).
  apply fst_typ_sigma in H1.
  apply snd_typ_sigma with (y:=fst (fst x)) in H1; auto with *.
  apply cc_arr_elim with (1:=H1); trivial.
 apply couple_intro_sigma; trivial.
  admit.
 apply cc_arr_intro; intros.
  admit.
 assert (h := H1).
 apply snd_typ_sigma with (y:=fst x) in h; auto with *.
 2:admit.
 apply cc_arr_elim with (1:=h).
 apply B'cons with (osucc o); auto.
 unfold A'i; rewrite TI_mono_succ; auto.
 2:apply W_F_mono; auto with *.
 apply fst_typ_sigma in H1; trivial.

 unfold g in H3.
 apply couple_injection in H3; destruct H3.
 apply couple_injection in H4; destruct H4.
 apply cc_lam_inj in H4; destruct H4.
 apply cc_lam_inj in H5; destruct H5.
 rewrite WF_eta with (2:=H1). 2:admit.
 rewrite WF_eta with (2:=H2). 2:admit.
 unfold WFmap.
 assert (eqf : fst x == fst x').
  admit.
 apply couple_morph; trivial.
 apply cc_lam_ext; intros.
  admit.

  red; intros.
  rewrite <- H9.
  rewrite B'_eqn with (o:=osucc o) in H8; auto.
   destruct H8 as [(l,?,eqx0)|(i,?,(b',?,eqx0))]; rewrite eqx0.
    apply H6; auto with *.

    red in H7.
    assert (r : i==i) by reflexivity.
    specialize H7 with (1:=H8) (2:=r).
    apply (iso_inj H0) in H7.
    2:admit.
    2:admit.
    apply couple_injection in H7; destruct H7 as (_,?).
    apply cc_lam_inj in H7; destruct H7.
    apply H11; auto with *.

   unfold A'i; rewrite TI_mono_succ; auto.
   2:apply W_F_mono; auto with *.
   apply fst_typ_sigma in H1; trivial.

 rewrite Fdef in H1.
 generalize (surj_pair _ _ _ (subset_elim1 _ _ _ H1)); intro.
 assert (fy_typ := fst_typ_sigma _ _ _ H1).
 apply snd_typ_sigma with (y:=fst y) in H1; auto with *.
 2:admit.
 rewrite (surj_pair _ _ _ H1) in H2.
 assert (fsy_typ := fst_typ _ _ _ H1).
 apply snd_typ in H1.
 assert (invtyp := iso_typ (iso_fun_sym H0)).
 pose (a' := couple (fst y)
            (cc_lam (C (fst y)) (fun i => 
              fst (iso_inv (W_F (A'i o) B' X) f (cc_app (snd (snd y)) i))))).
 assert (a'typ : a' \in A'i (osucc o)).
  unfold A'i; rewrite TI_mono_succ; auto with *.
  2:apply W_F_mono; auto with *.
  apply couple_intro_sigma; trivial.
   admit.

   apply cc_arr_intro; intros.
    admit.
   apply cc_arr_elim with (2:=H3) in H1.
   apply invtyp in H1.
   apply fst_typ_sigma in H1; trivial.   
 exists
  (couple a'
    (cc_lam (B' a')
      (B'case (fun l => cc_app (fst (snd y)) l)
              (fun i b' => cc_app (snd (iso_inv (W_F (A'i o) B' X) f (cc_app (snd (snd y)) i))) b')))).
  apply couple_intro_sigma; trivial.
   admit.

   unfold A'i; rewrite <- TI_mono_succ; auto with *.
   apply W_F_mono; auto with *.

   apply cc_arr_intro; intros.
    admit.
   apply B'case_typ with a'; intros; trivial.
    admit.

    apply cc_arr_elim with (1:=fsy_typ); trivial.
    unfold a' in H4; rewrite fst_def in H4; trivial.

    unfold a' in H4; rewrite fst_def in H4.
    apply cc_arr_elim with (2:=H4) in H1.
    apply invtyp in H1.
    apply snd_typ_sigma with (y:=fst (iso_inv (W_F (A'i o) B' X) f (cc_app (snd (snd y)) i))) in H1; auto with *.
    2:admit.
    apply cc_arr_elim with (1:=H1).
    revert H5; apply eq_elim; apply B'm.
    unfold a'; rewrite snd_def.
    rewrite cc_beta_eq; auto with *.
    admit.

  transitivity (couple (fst y) (couple (fst (snd y)) (snd (snd y)))); [|auto with *].
  unfold g; apply couple_morph.
   rewrite fst_def.
   unfold a'; rewrite fst_def; reflexivity.

   apply couple_morph.
    transitivity (cc_lam (B (fst y)) (fun b => cc_app (fst (snd y)) b)).
    2:symmetry; apply cc_eta_eq with (1:=fsy_typ).
    symmetry; apply cc_lam_ext; [|red; intros].
     apply Bm.
     rewrite fst_def.
     unfold a'; rewrite fst_def; auto with *.

     rewrite snd_def.
     rewrite cc_beta_eq.
     2:admit.
      rewrite B'case_nil.
      rewrite <- H4; auto with *.

      apply B'nil with (osucc o); auto.
      unfold a'; rewrite fst_def; trivial.
      rewrite <- H4; trivial.

assert (fm : morph1 f).
 admit.
    transitivity (cc_lam (C (fst y)) (fun i => cc_app (snd (snd y)) i)).
    2:symmetry; apply cc_eta_eq with (1:=H1).
    symmetry; apply cc_lam_ext; [|red; intros].
     unfold a'; do 2 rewrite fst_def; reflexivity.

     transitivity (f (iso_inv (W_F (A'i o) B' X) f (cc_app (snd (snd y)) x'))).
      rewrite iso_inv_eq with (1:=H0).
       rewrite H4; reflexivity.

       apply cc_arr_elim with (1:=H1); trivial.
       rewrite <- H4; trivial.

      apply fm.
      rewrite H4 in H3.
      assert (h:=H1); apply cc_arr_elim with (2:=H3) in h.
      apply invtyp in h.
      generalize (surj_pair _ _ _ (subset_elim1 _ _ _ h)); intro.
      rewrite H5; apply couple_morph.
       rewrite fst_def.
       unfold a'; rewrite snd_def.
       rewrite cc_beta_eq; auto with *.
       admit.

       apply snd_typ_sigma with
        (y:=fst (iso_inv (W_F (A'i o) B' X) f (cc_app (snd (snd y)) x')))in h; auto with *.
       2:admit.
       rewrite (cc_eta_eq _ _ _ h).
       apply cc_lam_ext; [|red;intros].
        apply B'm.
        rewrite fst_def.
        unfold a'; rewrite snd_def.
        rewrite cc_beta_eq; auto with *.
        admit.

        rewrite snd_def.
        rewrite cc_beta_eq; auto with *.
         2:admit.
         rewrite B'case_cons.
         rewrite <- H7; reflexivity.

         apply B'cons with (osucc o); auto.
          unfold a'; rewrite fst_def; trivial.

          rewrite <- H7; revert H6; apply eq_elim.
          apply B'm.
          unfold a'; rewrite snd_def.
          rewrite cc_beta_eq; auto with *.
          admit.
Qed.

Lemma nest_recursor X o :
    isOrd o ->
    recursor o (fun o' => W_F (A'i o') B' X)
      (fun o f => iso_fun (W_F (A'i o) B' X) (TI (fun Y =>  F X Y) o) (cc_app f))
      (fun o f => cc_lam (W_F (A'i (osucc o)) B' X) (g (cc_app f))).
constructor; intros.
 admit.

 unfold W_F.
apply eq_intro; intros.
 assert (h := fst_typ_sigma _ _ _ H1).
 apply TI_elim in h; auto with *.
 2:admit.
 destruct h.
 rewrite sup_ax;[|admit].
 exists x; trivial.
 rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ H1)).
 apply couple_intro_sigma.
  admit.

  unfold A'i; rewrite TI_mono_succ; auto with *.
   apply W_F_mono; auto with *.
   apply isOrd_inv with o0; trivial.

   apply snd_typ_sigma with (y:=fst z) in H1; auto with *.
   admit.

 rewrite sup_ax in H1;[|admit].
 destruct H1.
 rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ H2)).
 apply couple_intro_sigma.
  admit.

  apply fst_typ_sigma in H2.
  revert H2; apply TI_mono; eauto using isOrd_inv.
   apply W_F_mono; auto with *.
   red; intros.
   apply le_lt_trans with x; trivial.

  apply snd_typ_sigma with (y:=fst z) in H2; auto with *.
  admit.

 (* Q m *)
 admit.

 (* Q cont *)
 constructor; intros.
  admit.

  admit.

  admit. (* directed ord! *)

  apply TI_elim in H4; auto with *.
  2:admit.
  destruct H4.
  rewrite <- TI_mono_succ in H5; auto with *.
   2:do 2 red; intros; apply Fmono; auto with *.
   2:apply isOrd_inv with o0; trivial.
  destruct (iso_surj (H3 _ H4)) with y; trivial.
  exists x0; trivial.
  admit.

 (* body m *)
 admit.

 (* body typ *)
 split.
  apply ZFfunext.is_cc_fun_lam.
  admit.

  apply giso in H3; trivial.
  revert H3; apply iso_fun_morph.
   admit.

   rewrite TI_mono_succ; auto with *.
   do 2 red; intros.
   apply Fmono; auto with *.

   red; intros.
   rewrite <- H4.
   rewrite cc_beta_eq; auto with *.
    admit.

    clear x' H4; revert x H3.
    admit.

 (* body irrel *)
 do 2 red; intros.
 rewrite cc_beta_eq; auto.
  2:admit.
 rewrite cc_beta_eq; auto with *.
  2:admit.
  unfold g.
  apply couple_morph; auto with *.
  apply couple_morph; auto with *.
  apply cc_lam_ext; [|red; intros]; auto with *.
  red in H4.
  rewrite <- H4.
   apply cc_app_morph; auto with *.
   apply couple_morph.
    rewrite H7; reflexivity.
    apply cc_lam_ext.
     apply B'm; rewrite H7; reflexivity.
     red; intros.
     rewrite H7; rewrite H9; reflexivity.

   rewrite H7 in H6.
   apply couple_intro_sigma.
    admit.

    apply fst_typ_sigma in H5.
    unfold A'i in H5; rewrite TI_mono_succ in H5; auto with *.
    2:apply W_F_mono; auto with *.
    2:apply H2.
    apply snd_typ_sigma with (y:=fst (fst x)) in H5; auto with *.
    apply cc_arr_elim with (1:=H5); trivial.

    apply cc_arr_intro; intros.
     admit.
    assert (h:=H5).
    apply snd_typ_sigma with (y:=fst x) in H5; auto with *.
    2:admit.
    apply cc_arr_elim with (1:=H5).
    apply B'cons with (osucc o0); trivial.
     apply isOrd_succ; apply H2.

     apply fst_typ_sigma in h; trivial.

 admit.
Qed.

Lemma giso_it X o:
  isOrd o ->
  iso_fun (W_F (A'i o) B' X) (TI (fun Y=>F X Y) o)
    (cc_app (REC (fun o f => cc_lam (W_F (A'i (osucc o)) B' X)  (g (cc_app f))) o)).
intro.
apply REC_typing with (1:=H) (2:=nest_recursor X o H); intro.
Qed.

Parameter X_:set.
Definition nest_pos (o:set) : positive :=
mkPositive (fun X => TI (fun Y => F X Y) o) (A'i o) B'
  (iso_inv (W_F (A'i o) B' X_) (cc_app (REC (fun o f => cc_lam (W_F (A'i (osucc o)) B' X_)  (g (cc_app f))) o))).

Lemma isPos_nest o :
  isOrd o ->
  isPositive (nest_pos o).
constructor.
 do 2 red; intros.
 simpl.
 apply TI_op_mono; auto with *; apply Fmono_morph;
   do 2 red; intros; apply Fmono; auto with *.

 do 2 red; intros; simpl.
 apply B'm; trivial.

 simpl; intros.
 replace X_ with X.
 2:admit.
 apply iso_fun_sym.
 apply giso_it; trivial.
Qed.


Fixpoint iso' (a':A') : (B' a' -> X) -> N X :=
  match a' return (B' a' -> X)->N X with CA' x f => fun b' =>
  let fb (b:B x) := b' (B'nil (CA' x f) b) in
  let fc (i:C x) :=
    iso' (f i) (fun b'':B'(f i) => b' (B'cons (CA' x f) i b'')) in
  CN _ (mkF _ _ x fb fc)
  end.



  Hypothesis ord : set.
  Hypothesis oord : isOrd ord.

(* X -> \mu Y. F(X,Y) *)
Definition pos_nest_op X := TI (fun Y => F X Y) ord.

  (* ord is beyond the closure ordinal of Y -> F(X,Y) *)
  Hypothesis ord_clos : forall X, pos_nest_op X == F X (pos_nest_op X).

(*
is pos_nest_op X a W-type ?

nest X = {x':A' | B'(x') -> X }
F X (nest X) = { x:A | B(x) -> X & C(x) -> nest X}
             = { x:A | B(x) -> X & { f:C(x) -> A' | (i:C x)-> B'(f i) -> X }
             = { x:A | { f:C(x)->A' | B(x) -> X & {i:C x|B'(f i)} -> X } }
  = { {x:A; f:C x-> A'} | (B(x) + {i:C x|B'(f i)}) -> X }

A' = { x:A; C(x) ->A' }
B'(x,f) = B x + {i:C x & B'(f i)}  <-- param non-uniforme!
B'(_) = sup A B + (sup A C * B')

Ex: tree, list  F(T,L) = 1+T*L
 list T =  \mu L.F(T,L) = 1+T*\mu L.F(T,L)
 Ft T = 1+T*list T
 A=bool B=(0|1) C=(0|1)
 A' = 1 + A'
 B' = (0|1 + B' o snd)
 A' = nat
 B'(0) = 0
 B'(S k) = 1+B'(k)
 Ft T = {n:nat; n -> T }

F X (nest X) = { x:A(X) ; B(X,x) -> nest X }
  =  {x:A(X) ; f:B(X,x) -> A' ; {i:B(X,x);B'(f i)}->X}
  = { {x:A(X); f:B(_,x) -> A' ; 


*)



Definition g f  t (* A * B->X * C->TI F o *) :=
                     let trec i (* C(fst t) *):= f (cc_app (snd (snd t)) i) in
                     let x' (*A'*):=
                         couple (fst t) (cc_lam (C (fst t)) (fun i => fst(trec i))) in
                     let f' (* B'->X*) b' :=
B'case (fun l (* B x' *) => cc_app (fst (snd t)) l)
      (fun i b'' => cc_app (snd (trec i)) b'') b' in
                     couple x' (cc_lam (B' x') f').


Definition nest_iso := TI_iso pos_nest_op g.


(*
Definition pos_nest F o :=
  mkPositive (pos_nest_op F o)
    (TI (fun Y => w1 (F Y))) (fun x => TI (fun Y => w2 (F Y) x))
    (fun c => TI_iso (fun Y => pos_oper (F Y) X)
       (fun f => 

list A = {n:N & n -> A }
list A = W1 * W2->A
1+A*list A = 1 + A*W1 * W2osnd -> A
   = (1+W1) * (0|1+W2) -> A
W1=1+W1
W2(n) = 0|1+W2(n-1)


\mu X.1+AX = \mu X. 1+A * (0|1 -> X) 
List B ->f A


pos_oper (F Y)  empty (fun _=>empty) (fun _=>empty).

Lemma isPos_nest F o :
  Proper (eq_set==>eqpos) F ->
  isOrd o ->
  (* Parameter occurs positively if the constructors of nested type (Y) *)
  (forall Y, isPositive (F Y)) ->
  (* The nested operator is monotonic *)
  (forall X, Proper (incl_set ==> incl_set) (fun Y => pos_oper (F Y) X)) ->
  isPositive (pos_nest F o).
unfold pos_nest, pos_nest_op; intros Fm oo FposParam FmonoNested.
split; simpl; intros.
 do 3 red; intros.
 admit.

 red; intros.
 assert (Fpos' := fun Y => pos_stable (F Y) (FposParam Y)).
 red in Fpos'.
 transitivity (TI (fun Y => inter (replf X (fun x => pos_oper (F Y) x))) o).
(* 
TI (Y -> F Y X) o =
U(o'<o) F (TI F_X o') X =
U(o'<o)  w1(TI F_X o') * (w2(TI F_X o') -> X)
(if w1,w2 cont)
w1(

*)

red; intros.
apply TI_stable in H.

*)
*)
End NestedInductive.
