Require Import ZF ZFpairs ZFnats ZFord ZFfix.

Section Limit.

(* Building the limit of a sequnce of sets *)
Variable o : set.
Variable F : set -> set.
Hypothesis oord : isOrd o.
Hypothesis Fm : ext_fun o F.

Definition lim :=
  subset (sup o F) (fun z => exists2 o', o' \in o & forall w, o' \incl w -> w \in o -> z \in F w).

Lemma lim_def z :
  z \in lim <-> exists2 o', o' \in o &forall w, o' \incl w -> w \in o -> z \in F w.
intros.
unfold lim.
rewrite subset_ax.
rewrite sup_ax; auto with *.
split; intro.
 destruct H as (_,(z',eqz,(o',o'lt,zin))).
 exists o'; intros; trivial.
 rewrite eqz; auto.

 destruct H as (o',o'lt,zin).
 split; eauto with *.
 exists z; eauto with *.
Qed.

Lemma lim_cst o' :
  o' \in o ->
  (forall w, o' \incl w -> w \in o -> F w == F o') ->
  lim == F o'.
intros o'lt fcst.
apply eq_set_ax; intros z.
assert (os := fun y => isOrd_inv o y oord).
rewrite lim_def; trivial.
split; intros.
 destruct H as (w,w'o,zin).
 rewrite <- (fcst (osup2 o' w)).
  apply zin.
   apply osup2_incl2; auto.
   apply osup2_lt; auto.

  apply osup2_incl1; auto.
  apply osup2_lt; auto.

 exists o'; intros; trivial.
 rewrite fcst; auto.
Qed.

End Limit.

Lemma lim_oucc o F :
  isOrd o ->
  ext_fun (osucc o) F ->
  lim (osucc o) F == F o.
intros.
apply lim_cst; auto with *; intros.
 apply lt_osucc; trivial.

 apply H0; auto.
 apply olts_le in H2; trivial.
 apply incl_eq; trivial.
Qed.

Lemma lim_ext :
  forall o o', isOrd o -> o == o' -> forall f f', eq_fun o f f' -> lim o f == lim o' f'.
intros; unfold lim.
apply subset_morph.
 apply sup_morph; auto with *.

 red; intros.
 split; destruct 1 as (w',?,?); exists w'; intros.
  rewrite <- H0; trivial.

  rewrite <- H0 in H6.
  rewrite <- (H1 _ _ H6 (reflexivity w)); auto.

  rewrite H0; trivial.

  rewrite (H1 _ _ H6 (reflexivity w)); auto.
  rewrite H0 in H6; auto.
Qed.

Instance lim_morph : Proper (eq_set==>(eq_set==>eq_set)==>eq_set) lim.
do 3 red; intros; unfold lim.
apply subset_morph.
 apply sup_morph; auto with *.
 red; intros; apply H0; trivial.

 red; intros.
 apply ex2_morph; red; intros.
  rewrite H; reflexivity.

  apply fa_morph; intro w.
  rewrite H; rewrite (H0 _ _ (reflexivity w)); reflexivity.
Qed.

Section LimitMono.

Variable F:set->set.
Variable o : set.
Hypothesis oord : isOrd o.
Hypothesis Fmono : increasing F.

Let os := fun y => isOrd_inv _ y oord.

Let Fext : ext_fun o F.
do 2 red; intros.
apply incl_eq; apply Fmono; auto.
 rewrite <- H0; auto.
 rewrite H0; reflexivity.
 rewrite <- H0; auto.
 rewrite H0; reflexivity.
Qed.

Lemma lim_def_mono : lim o F == sup o F.
apply eq_set_ax; intros z.
rewrite lim_def; auto with *.
rewrite sup_ax; trivial.
split; destruct 1.
 exists x; auto with *.

 exists x; intros; trivial.
 revert H0; apply Fmono; auto.
Qed.

Lemma lim_mono z :
  z \in lim o F <-> exists2 o', o' \in o & z \in F o'.
rewrite lim_def_mono; rewrite sup_ax; auto with *.
Qed.

End LimitMono.

Section LimitTI.

Variable F : set->set.
Hypothesis Fm : Proper (incl_set==>incl_set) F.

Lemma TIlim o :
  isOrd o ->
  TI F o == lim o (fun o' => F(TI F o')).
intros oo.
rewrite TI_eq; auto using Fmono_morph.
rewrite lim_def_mono; auto with *.
red; intros.
apply Fm; apply TI_mono; trivial.
Qed.

End LimitTI.
(*
Section TRF.

Hypothesis F:(set->set->set)->set->set->set.
Hypothesis Fext : forall o o' f f' x x',
  isOrd o ->
  (forall o' o'' x x', o' \in o -> o'==o'' -> x==x' -> f o' x == f' o'' x') ->
  o == o' ->
  x == x' ->
  F f o x == F f' o' x'.

  Definition TR_set 

  Definition TR_rel o x y :=
    isOrd o /\
    forall P,
    (forall o' f x, isOrd o' -> o' \incl o -> morph2 f ->
     x \in X -> (forall n x , n \in o'
     (forall n x, n \in o' -> couple n (couple x (f n x)) \in P) ->
     couple o' (couple x (F f o' x)) \in P) ->
    couple o (couple x y) \in P.

  Instance TR_rel_morph : Proper (eq_set ==> eq_set ==> eq_set ==> iff) TR_rel.
apply morph_impl_iff3; auto with *.
do 5 red; unfold TR_rel; intros.
destruct H2 as (xo,Hrec); split; intros.
 rewrite <- H; auto.

 rewrite <- H; rewrite <- H0; rewrite <- H1; apply Hrec; auto.
Qed.

  Lemma TR_rel_intro : forall o x f,
    isOrd o ->
    morph2 f ->
    (forall o' x, o' \in o -> TR_rel o' x (f o' x)) ->
    TR_rel o x (F f o x).
red; intros.
split; intros; auto.
apply H2; trivial; intros.
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

Global Instance TR_morph : morph2 TR.
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
*)

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

Global Instance TR_morph : morph2 TR.
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


Let G f o x := F (fun x => lim o (fun o' => f o' x)) x.
Definition TRF := TR G.

Let Gext : forall o o' f f' x x',
  isOrd o ->
  (forall o' o'' x x', o' \in o -> o'==o'' -> x==x' -> f o' x == f' o'' x') ->
  o == o' ->
  x == x' ->
  G f o x == G f' o' x'.
unfold G; intros.
apply Fm; trivial.
red; intros.
apply lim_ext; trivial.
red; intros; auto.
Qed.

Let Girr : forall o o' f f' x x',
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
  G f o x == G f' o' x'.
unfold G; intros.
assert (os := fun y => isOrd_inv _ y H1).
rewrite Tcont in H5; trivial.
destruct H5 as (w,?,?).
apply Fext with w; auto.
red; intros.
rewrite lim_cst with (o':=w); auto.
 rewrite lim_cst with (o':=w); auto.
  apply H3; auto with *.

  do 2 red; intros.
  apply H0; auto with *.

  intros.
  transitivity (f w x0).
   symmetry; apply H3; auto with *.

   apply H3; auto with *.

 do 2 red; intros.
 apply H; auto with *.

 intros.
 transitivity (f' w0 x'0).
  apply H3; auto with *.
  revert H8; apply Tmono; auto.

  symmetry; apply H3; auto with *.
Qed.


Lemma TRF_indep : forall o o' x,
  isOrd o ->
  o' \in o ->
  x \in T (osucc o') ->
  TRF o x == F (TRF o') x.
intros.
assert (os := fun y => isOrd_inv _ y H).
unfold TRF. 
rewrite TR_eqn0; auto with *.
unfold G at 1.
apply (Fext o'); auto with *.
red; intros.
rewrite <- H3.
rewrite lim_cst with (o':=o'); auto with *.
 do 2 red; intros.
 apply TR_morph; auto with *.

 intros.
 apply TR_irrel with (T:=T); auto with *.
Qed.

End TRirr.


(*


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




(* Limit of a sequence of functions by retaining values that do not
   change after some iteration stage *)
Definition dom_fun (f:set->set->set) (o:set) (x:set) (o':set) :=
  forall o'', o' \incl o'' -> o'' \in o -> f o'' x == f o' x.
Definition sup_fun (f:set->set->set) (o:set) (x:set) :=
  sup (subset o (dom_fun f o x)) (fun o' => f o' x).


Lemma dom_fun_sup f o x o1 o2 :
  isOrd o ->
  o1 \in o ->
  o2 \in o ->
  dom_fun f o x o1 ->
  dom_fun f o x o2 ->
  dom_fun f o x (osup2 o1 o2).
unfold dom_fun; intros.
assert (os := isOrd_inv o).
Admitted.

Lemma sup_fun_ok f o x o' :
  isOrd o ->
  o' \in o ->
  morph2 f -> (* ext_fun o (fun o' -> f o' x) *)
  dom_fun f o x o' ->
  sup_fun f o x == f o' x.
intros oo o'lt fm dm.
assert (os := fun y => isOrd_inv o y oo).
unfold sup_fun.
rewrite eq_set_ax; intro z.
rewrite sup_ax.
2:do 2 red; intros; apply fm; auto with *.
split; intros.
 destruct H.
 rewrite subset_ax in H; destruct H.
 destruct H1.
 revert H0; apply eq_elim.
 rewrite H1 in H|-*;clear x0 H1.
 transitivity (f (osup2 x1 o') x).
  symmetry; apply H2.
   apply osup2_incl1; auto.
   apply osup2_lt; auto.

  apply dm.
   apply osup2_incl2; auto.
   apply osup2_lt; auto.

 exists o'; trivial.
 apply subset_intro; trivial.
Qed.


Definition TRF := TR(fun f o x => F (sup_fun f o) x).

Lemma TRF_indep : forall o o' x,
  isOrd o ->
  o' \in o ->
  dom_fun TRF o x o' ->
  TRF o x == F (TRF o') x.
intros.
unfold TRF. 
rewrite TR_eqn0; auto with *.
red in H1.
fold TRF.


Lemma dom_intro o o' x :
  isOrd o ->
  o' \in o ->
  x \in T o' -> dom_fun TRF o x o'.
intros oo; revert o' x.
elim oo using isOrd_ind; intros; auto.
unfold dom_fun in *.
intros.


 apply F

rewrite TR_eqn0; auto with *.
apply iter_def with (3:=H1); trivial.
 apply TR_morph.
intros.
rewrite <- H5.
symmetry; apply TR_irrel with T; auto with *.
apply iter_ext.
Qed.



Lemma iter_def : forall o f,
  isOrd o ->
  morph2 f ->
  (forall x o', x \in T o' -> dom_fun f o x o') ->
  forall o', o' \in o ->
  eq_fun (T o') (sup_fun f o) (f o').
red; intros o f oo fm dm o' o'lt x x' tyx eqx.
rewrite <- eqx.
apply sup_fun_ok; auto.
Qed.


Definition iter (F:(set->set)->set->set) f o x := F (sup_fun f o) x.


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

*)