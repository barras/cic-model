Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFtarski ZFstable.
Require Import ZFgrothendieck.
Require Import ZFlist.
Import ZFrepl.

(** In this file we develop the theory of W-types as a type of trees encoded
    as a relation from paths to labels.
 *)

Module Type Wsized.

Parameter Wf : set -> (set -> set) -> set -> set.
Parameter Wf_morph_gen :
  Proper (eq_set==>(eq_set==>eq_set)==>eq_set==>eq_set) Wf.
Existing Instance Wf_morph_gen.
Parameter Wf_mono : forall A B,
  morph1 B -> Proper (incl_set ==> incl_set) (Wf A B).
Parameter Wf_ext : forall A A' B B' X X',
  A == A' ->
  eq_fun A B B' ->
  X == X' ->
  Wf A B X == Wf A' B' X'.
Parameter Wsup : set -> set -> set.
Parameter Wsup_morph : morph2 Wsup.
Parameter Wf_intro : forall A B,
       morph1 B ->
       forall X x f, x ∈ A -> f ∈ (Π _ ∈ B x, X) -> Wsup x f ∈ Wf A B X.

Parameter wsubterms : set -> (set->set) -> set -> set.
Parameter wsubterms_morph :
  Proper (eq_set==>(eq_set==>eq_set)==>eq_set==>eq_set) wsubterms.
Existing Instance wsubterms_morph.
Parameter wsubterms_ext : forall A A' B B' X X',
  A == A' ->
  eq_fun A B B' ->
  X == X' ->
  wsubterms A B X == wsubterms A' B' X'.

Parameter W : set -> (set->set) -> set.
Parameter W_morph : Proper (eq_set==>(eq_set==>eq_set)==>eq_set) W.
Existing Instance W_morph.
Parameter W_ext : forall A A' B B',
  A == A' ->
  eq_fun A B B' ->
  W A B == W A' B'.
Parameter Wf_stable : forall A B, morph1 B ->
  stable_class (fun X => X ⊆ W A B) (Wf A B).
Parameter W_eqn : forall A B, morph1 B -> W A B == Wf A B (W A B).
Parameter wsubterms_incl_W : forall A B,
  morph1 B -> forall X, wsubterms A B X ⊆ W A B.
Parameter wsubterms_trans : forall A B,
  morph1 B ->
  forall X,
  wsubterms A B X ⊆ Wf A B (wsubterms A B X).
Parameter wsubterms_compl : forall A B,
   morph1 B -> forall X, X ∩ W A B ⊆ wsubterms A B X.
Parameter wsubterms_proj : forall A B,
       morph1 B ->
       forall X, X ⊆ W A B -> X ⊆ Wf A B X -> wsubterms A B X == X.
Parameter G_W'
     : forall A B,
       morph1 B ->
       forall U,
       grot_univ U ->
       ZFord.omega ∈ U ->
       A ∈ U -> (forall a : set, a ∈ A -> B a ∈ U) -> W A B ∈ U.

(*Require Import ZFwpaths.*)
(*Parameter Wf_elim : forall A B,
       morph1 B ->
       forall a X,
       a ∈ Wf A B X ->
       exists2 x, x ∈ A &
       exists2 f, f ∈ (Π _ ∈ B x, X) & a == Wsup x f.
*)
(*Parameter Wfst : set -> set.
Parameter Wfst_morph : morph1 Wfst.
Parameter Wsnd_fun : set -> set.
Parameter Wsnd_fun_morph : morph1 Wsnd_fun.
Parameter Wfst_typ_gen : forall A B,
  morph1 B ->
  forall X w,
  w ∈ Wf A B X ->
  Wfst w ∈ A.
Parameter Wsnd_typ_gen : forall A B,
  morph1 B ->
  forall X w i,
  X ⊆ W(*dom*) A B ->
  w ∈ Wf A B X ->
  i ∈ B (Wfst w) ->
  Wsnd w i ∈ X.
Parameter Wfst_def : forall x f, Wfst (Wsup x f) == x.
Parameter Wsnd_fun_def : forall A B Y x f,
  f ∈ (Π _ ∈ Y, W A B) -> Wsnd_fun (Wsup x f) == f.
*)

Parameter Wcase : (set -> set -> set) -> set -> set.
Parameter Wcase_morph_gen : Proper ((eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) Wcase.
Existing Instance Wcase_morph_gen.
Parameter Wcase_ext : forall A A' B B' X X' h h' c c',
  morph1 B ->
  morph1 B' ->
  X ⊆ W A B ->
  X' ⊆ W A' B' ->
  (forall x x' f f', x ∈ A -> x' ∈ A' -> x == x' ->
   f ∈ (Π _ ∈ B x, X) -> f' ∈ (Π _ ∈ B' x', X') ->
   f == f' -> h x f == h' x' f') ->
  c ∈ Wf A B X ->
  c' ∈ Wf A' B' X' ->
  c == c' ->
  Wcase h c == Wcase h' c'.

Parameter Wcase_typ : forall (A : set) (B : set -> set),
       morph1 B ->
       forall (X : set) (Q : set -> set) (h : set -> set -> set) (w : set),
       morph1 Q ->
       X ⊆ W A B ->
       (forall x f : set, x ∈ A -> f ∈ (Π _ ∈ B x, X) -> h x f ∈ Q (Wsup x f)) ->
       w ∈ Wf A B X -> Wcase h w ∈ Q w.

Parameter Wcase_eqn : forall A B,
       morph1 B -> forall h x f,
       morph2 h -> f ∈ (Π _ ∈ B x, W A B) -> Wcase h (Wsup x f) == h x f.

Parameter WSREC'
     : set ->
       (set -> set) ->
       (set -> Prop) ->
       set -> (set -> set -> set) -> (set -> set -> set -> set) -> set -> set.
Parameter WSREC'_morph_gen
     : Proper
         (eq_set ==>
          (eq_set ==> eq_set) ==>
          (eq_set ==> iff) ==>
          eq_set ==>
          (eq_set ==> eq_set ==> eq_set) ==>
          (eq_set ==> eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set)
         WSREC'.
Existing Instance WSREC'_morph_gen.
Parameter WSREC'_ext : forall A A' B B' K K' O O' U U' F F',
       A == A' ->
       eq_fun A B B' ->
       eq_pred (power (W A B)) K K' ->
       O ⊆ W A B ->
       O == O' ->
       (forall X,
        K X -> forall w w', w ∈ W A B -> w == w' -> U X w == U' X w') ->
       (forall X recf x,
        K X ->
        recf ∈ (Π w ∈ X, U X w) -> x ∈ Wf A B X -> F X recf x == F' X recf x) ->
       eq_fun (W A B) (WSREC' A B K O U F) (WSREC' A' B' K' O' U' F').
Parameter WSREC_typ' : forall A B,
       morph1 B ->
       forall K : set -> Prop,
       Proper (eq_set ==> iff) K ->
       (forall X,
        (exists z0, z0 ∈ X) ->
        (forall z, z ∈ X -> K z) -> K (inter X)) ->
       (forall I X,
        ext_fun I X -> (forall i, i ∈ I -> K (X i)) -> K (sup I X)) ->
       (forall X, K X -> X ⊆ W A B) ->
       K (W A B) ->
       (forall X, K X -> K (Wf A B X)) ->
       (forall X, K X -> X ⊆ Wf A B X) ->
       forall O,
       K O ->
       forall P,
       morph2 P ->
       (forall X Y x,
        K Y ->
        (forall w, w ∈ X ->
         exists2 w', w' ∈ Y & forall X, K X -> w' ∈ Wf A B X -> w ∈ X) ->
        P (Wf A B X) x ⊆ P Y x) ->
       forall F,
       Proper (eq_set ==> eq_set ==> eq_set ==> eq_set) F ->
       (forall X x recf,
        X ⊆ O ->
        K X ->
        x ∈ Wf A B X ->
        recf ∈ (Π w ∈ X, P X w) -> F X recf x ∈ P (Wf A B X) x) ->
       (forall X X' recf recf',
        X ⊆ O ->
        K X ->
        X' ⊆ O ->
        K X' ->
        recf ∈ (Π w ∈ X, P X w) ->
        recf' ∈ (Π w ∈ X', P X' w) ->
        (forall x, x ∈ X -> x ∈ X' -> cc_app recf x == cc_app recf' x) ->
        forall x,
        x ∈ Wf A B X -> x ∈ Wf A B X' -> F X recf x == F X' recf' x) ->
       forall w, w ∈ O -> WSREC' A B K O P F w ∈ P O w.
Parameter WSREC_eqn' : forall A B,
       morph1 B ->
       forall K : set -> Prop,
       Proper (eq_set ==> iff) K ->
       (forall X,
        (exists z0, z0 ∈ X) ->
        (forall z, z ∈ X -> K z) -> K (inter X)) ->
       (forall I X,
        ext_fun I X -> (forall i, i ∈ I -> K (X i)) -> K (sup I X)) ->
       (forall X, K X -> X ⊆ W A B) ->
       K (W A B) ->
       (forall X, K X -> K (Wf A B X)) ->
       (forall X, K X -> X ⊆ Wf A B X) ->
       forall O,
       K O ->
       forall P,
       morph2 P ->
       (forall X Y x,
        K Y ->
        (forall w, w ∈ X ->
         exists2 w', w' ∈ Y & forall X, K X -> w' ∈ Wf A B X -> w ∈ X) ->
        P (Wf A B X) x ⊆ P Y x) ->
       forall F,
       Proper (eq_set ==> eq_set ==> eq_set ==> eq_set) F ->
       (forall X x recf,
        X ⊆ O ->
        K X ->
        x ∈ Wf A B X ->
        recf ∈ (Π w ∈ X, P X w) -> F X recf x ∈ P (Wf A B X) x) ->
       (forall X X' recf recf',
        X ⊆ O ->
        K X ->
        X' ⊆ O ->
        K X' ->
        recf ∈ (Π w ∈ X, P X w) ->
        recf' ∈ (Π w ∈ X', P X' w) ->
        (forall x, x ∈ X -> x ∈ X' -> cc_app recf x == cc_app recf' x) ->
        forall x,
        x ∈ Wf A B X -> x ∈ Wf A B X' -> F X recf x == F X' recf' x) ->
       (* concl: *)
       forall w,
       w ∈ O ->
       WSREC' A B K O P F w == F O (λ w0 ∈ O, WSREC' A B K O P F w0) w.
(*Parameter WSREC' : set ->
       (set -> set) ->
       (set -> set) -> (set -> set -> set -> set) -> set -> set.
Parameter WSREC'_morph_gen :
  Proper (eq_set==>(eq_set==>eq_set)==>(eq_set==>eq_set)==>(eq_set==>eq_set==>eq_set==>eq_set)==>eq_set==>eq_set)
  WSREC'.
Existing Instance WSREC'_morph_gen.
Parameter WSREC'_ext : forall A A' B B' U U' F F',
  A == A' ->
  eq_fun A B B' ->
  eq_fun (W A B) U U' ->
  (forall X recf x, X ⊆ W A B -> X ⊆ Wf A B X -> recf ∈ (Π w ∈ X, U w) -> x ∈ Wf A B X ->
   F X recf x == F' X recf x) ->
  eq_fun (W A B) (WSREC' A B U F) (WSREC' A' B' U' F').

Parameter WSREC_typ' :
       forall (A : set) (B : set -> set),
       morph1 B ->
       forall P : set -> set,
       morph1 P ->
       forall F : set -> set -> set -> set,
       Proper (eq_set ==> eq_set ==> eq_set ==> eq_set) F ->
       (forall X x recf : set,
        X ⊆ W A B ->
        X ⊆ Wf A B X ->
        x ∈ Wf A B X -> recf ∈ (Π w ∈ X, P w) -> F X recf x ∈ P x) ->
       (forall X X' recf recf' : set,
        X ⊆ W A B ->
        X ⊆ Wf A B X ->
        X' ⊆ W A B ->
        X' ⊆ Wf A B X' ->
        recf ∈ (Π w ∈ X, P w) ->
        recf' ∈ (Π w ∈ X', P w) ->
        (forall x : set, x ∈ X -> x ∈ X' -> cc_app recf x == cc_app recf' x) ->
        forall x : set,
        x ∈ Wf A B X -> x ∈ Wf A B X' -> F X recf x == F X' recf' x) ->
       forall w : set, w ∈ W A B -> WSREC' A B P F w ∈ P w.

Parameter WSREC_eqn' :
       forall (A : set) (B : set -> set),
       morph1 B ->
       forall P : set -> set,
       morph1 P ->
       forall F : set -> set -> set -> set,
       Proper (eq_set ==> eq_set ==> eq_set ==> eq_set) F ->
       (forall X x recf : set,
        X ⊆ W A B ->
        X ⊆ Wf A B X ->
        x ∈ Wf A B X -> recf ∈ (Π w ∈ X, P w) -> F X recf x ∈ P x) ->
       (forall X X' recf recf' : set,
        X ⊆ W A B ->
        X ⊆ Wf A B X ->
        X' ⊆ W A B ->
        X' ⊆ Wf A B X' ->
        recf ∈ (Π w ∈ X, P w) ->
        recf' ∈ (Π w ∈ X', P w) ->
        (forall x, x ∈ X -> x ∈ X' -> cc_app recf x == cc_app recf' x) ->
        forall x,
        x ∈ Wf A B X -> x ∈ Wf A B X' -> F X recf x == F X' recf' x) ->
       forall w,
       w ∈ W A B ->
       WSREC' A B P F w == F (W A B) (λ w0 ∈ W A B, WSREC' A B P F w0) w.
*)
End Wsized.

Module Wpaths <: Wsized.

Section W_theory.

(** * Definition and properties of the W-type operator *)

Variable A : set.
Variable B : set -> set.
Hypothesis Bm : morph1 B.

(** * Encoding W-types as sets of path in a tree *)


(** The construction domain and the constructor *)
Definition Wdom := rel (List (sup A B)) A.

Definition Wsup x f :=
   singl (couple Nil x) ∪
   replf (subset f (fun z => z == couple (fst z) (couple (fst (snd z)) (snd (snd z)))))
     (fun z => couple (Cons (fst z) (fst (snd z))) (snd (snd z))).

Global Instance Wsup_morph : morph2 Wsup.
do 3 red; intros.
unfold Wsup.
apply union2_morph.
 rewrite H; reflexivity.

 apply replf_morph_raw.
  apply subset_morph; trivial.
  red; intros; reflexivity.

  red; intros.
  rewrite H1; reflexivity.
Qed.

Lemma Wsup_def x f p :
  (p ∈ Wsup x f <->
   p == couple Nil x \/
   exists i l y, couple i (couple l y) ∈ f /\ p == couple (Cons i l) y).
unfold Wsup.
rewrite union2_ax.
rewrite replf_ax.
apply or_iff_morphism.
 split; intros.
  apply singl_elim in H; trivial.
  rewrite H; apply singl_intro.

 split; intros.
  destruct H as (z,z_in_f,eqp).
  rewrite subset_ax in z_in_f.
  destruct z_in_f as (z_in_f,(z',eqz,etaz)).
  rewrite <- eqz in etaz; clear z' eqz.
  rewrite etaz in z_in_f.
  do 3 econstructor; split; [exact z_in_f|trivial].

  destruct H as (i&l&y&in_f&etap).
  exists (couple i (couple l y)).
   apply subset_intro; trivial.
   rewrite snd_def, !fst_def, snd_def.
   reflexivity.

   rewrite snd_def, !fst_def, snd_def.
   trivial.

 do 2 red; intros.
 rewrite H0; reflexivity.
Qed.

Lemma Wsup_hd_prop a x f :
  couple Nil a ∈ Wsup x f <-> a == x.
rewrite Wsup_def.
split; intros.
 destruct H as [eqc|(i&l&y&_&eqc)].
  apply couple_injection in eqc; destruct eqc; trivial.

  apply couple_injection in eqc; destruct eqc as (eqc,_).
  apply discr_mt_pair in eqc; contradiction.

 left; rewrite H; reflexivity.
Qed.

Lemma Wsup_tl_prop i l a x f :
  couple (Cons i l) a ∈ Wsup x f <-> couple l a ∈ cc_app f i.
rewrite Wsup_def.
rewrite <- couple_in_app.
split; intros.
 destruct H as [eqc|(i'&l'&y&in_f&eqc)].
  apply couple_injection in eqc; destruct eqc as (eqc,_).
  symmetry in eqc.
  apply discr_mt_pair in eqc; contradiction.

  apply couple_injection in eqc; destruct eqc as (eqc,eqa).
  apply couple_injection in eqc; destruct eqc as (eqi,eql).
  rewrite eqi,eql,eqa; auto.

 right.
 exists i; exists l; exists a; auto with *.
Qed.

Lemma Wsup_typ_gen x f :
  x ∈ A ->
  f ∈ (Π i ∈ B x, Wdom) ->
  Wsup x f ∈ Wdom.
intros.
assert (tyf := cc_prod_is_cc_fun _ _ _ H0).
apply power_intro; intros.
rewrite Wsup_def in H1; trivial.
destruct H1 as [eqz|(i&l&y&in_f&eqz)]; rewrite eqz.
 apply couple_intro; trivial.
 apply Nil_typ.

 destruct tyf with (1:=in_f) as (_,tyi).
 rewrite fst_def in tyi.
 specialize cc_prod_elim with (1:=H0) (2:=tyi); intros tyapp.
 rewrite couple_in_app in in_f.
 apply power_elim with (2:=in_f) in tyapp.
 apply couple_intro.
  apply Cons_typ.
   rewrite sup_ax; eauto with *.
   apply fst_typ in tyapp; rewrite fst_def in tyapp; trivial.

  apply snd_typ in tyapp; rewrite snd_def in tyapp; trivial.
Qed.

Definition Wfst w :=
  snd (union (subset w (fun p => exists x, p == couple Nil x))).

Global Instance Wfst_morph : morph1 Wfst.
do 2 red; intros.
unfold Wfst.
apply snd_morph; apply union_morph.
apply subset_morph; trivial.
red; intros.
reflexivity.
Qed.

Definition Wsnd_fun w :=
   replf (subset w (fun z => exists i l x, z == couple (Cons i l) x))
     (fun z => couple (fst (fst z)) (couple (snd (fst z)) (snd z))).

Global Instance Wsnd_fun_morph : morph1 Wsnd_fun.
do 2 red; intros.
unfold Wsnd_fun.
apply replf_morph_raw.
 apply subset_morph; auto with *.
red; intros.
rewrite H0; reflexivity.
Qed.

Definition Wsnd w i := cc_app (Wsnd_fun w) i.

Global Instance Wsnd_morph : morph2 Wsnd.
do 3 red; intros.
apply cc_app_morph; trivial.
apply Wsnd_fun_morph; trivial.
Qed.


Lemma Wfst_def x f :
  Wfst (Wsup x f) == x.
unfold Wfst.
rewrite union_subset_singl with (y:=couple Nil x)(y':=couple Nil x); auto with *.
 apply snd_def.

 rewrite Wsup_hd_prop; reflexivity.

 exists x; reflexivity.

 intros y y' tyy tyy' (x1,eqy) (x2,eqy').
 rewrite eqy in tyy|-*.
 rewrite eqy' in tyy'|-*.
 rewrite Wsup_hd_prop in tyy.
 rewrite Wsup_hd_prop in tyy'.
 rewrite tyy,tyy'; reflexivity.
Qed.

Lemma Wsnd_fun_def_raw x f :
  Wsnd_fun (Wsup x f) ==
  subset f (fun z => z == couple (fst z) (couple (fst (snd z)) (snd (snd z)))).
unfold Wsnd_fun.
symmetry; apply replf_ext; intros.
 do 2 red; intros.
 rewrite H0; reflexivity.

 apply subset_intro.
  apply subset_ax in H.
  destruct H as (?,(x',?,(i,(l,(y,?))))).
  rewrite <- H0 in H1; clear H0 x'.
  rewrite H1 in H|-*; clear H1 x0.
  rewrite !fst_def, !snd_def.
  apply Wsup_def in H.
  destruct H as [?|(i',(l',(y',(?,?))))].  
   apply couple_injection in H; destruct H as (abs,_).
   apply couple_mt_discr in abs; contradiction.

   apply couple_injection in H0; destruct H0 as (?,?).
   apply couple_injection in H0; destruct H0 as (?,?).
   rewrite H0,H2,H1; trivial.

  rewrite !fst_def, !snd_def, !fst_def.
  reflexivity.

 apply subset_ax in H.
 destruct H as (?,(x',?,?)).
 rewrite <- H0 in H1; clear H0 x'.
 exists (couple (couple (fst y) (fst (snd y))) (snd (snd y))).
  apply subset_intro.
   apply Wsup_def; right.
   exists (fst y); exists (fst (snd y)); exists (snd (snd y)).
   split;[|reflexivity].
   rewrite <- H1; trivial.

   exists (fst y); exists (fst (snd y)); exists (snd (snd y)).
   reflexivity.

  rewrite !fst_def, !snd_def.
  trivial.
Qed.
 
Lemma Wsnd_fun_def_dom Y x f :
  f ∈ (Π i ∈ Y, Wdom) ->
  Wsnd_fun (Wsup x f) == f.
intros tyf.
rewrite Wsnd_fun_def_raw.
symmetry; apply subset_ext; intros; trivial.
exists x0; auto with *.
destruct (cc_prod_is_cc_fun _ _ _ tyf _ H) as (eqx,tyx).
apply transitivity with (1:=eqx).
apply couple_morph;[reflexivity|].
rewrite eqx in H.
rewrite couple_in_app in H.
specialize cc_prod_elim with (1:=tyf) (2:=tyx); intros tyapp.
apply power_elim with (2:=H) in tyapp.
apply surj_pair in tyapp; trivial.
Qed.


Lemma Wsnd_def x f i :
  cc_app f i ∈ Wdom ->
  Wsnd (Wsup x f) i == cc_app f i.
intros tyf.
unfold Wsnd; rewrite Wsnd_fun_def_raw.
apply eq_set_ax; split; intros.
 apply couple_in_app in H.
 apply subset_ax in H; destruct H as (?,_).
 apply couple_in_app; trivial.

 apply couple_in_app. 
 apply subset_intro.
  apply couple_in_app; trivial.

  rewrite fst_def, snd_def.
  apply couple_morph;[reflexivity|].
  apply power_elim with (2:=H) in tyf.
  apply surj_pair in tyf; trivial.
Qed.

Lemma Wsup_inj x x' f f' :
  x ∈ A ->
  x' ∈ A ->
  (forall i, i ∈ B x -> cc_app f i ∈ Wdom) ->
  (forall i, i ∈ B x' -> cc_app f' i ∈ Wdom) ->
  Wsup x f == Wsup x' f' -> x == x' /\ (forall i, i ∈ B x -> cc_app f i == cc_app f' i).
intros tyx tyx' tyf tyf' eqw.
assert (eqx : x==x').
 rewrite <- (Wfst_def x f).
 rewrite <- (Wfst_def x' f').
 rewrite eqw; reflexivity.
split; intros; trivial.
rewrite <- (Wsnd_def x f i); auto.
rewrite eqx in H.
rewrite <- (Wsnd_def x' f' i); auto.
rewrite eqw; reflexivity.
Qed.


Definition Wcase (h:set->set->set) w := h (Wfst w) (Wsnd_fun w).

Lemma Wcase_eqn_dom h x f :
  morph2 h ->
  f ∈ (Π i ∈ B x, Wdom) ->
  Wcase h (Wsup x f) == h x f.
intros hm tyf.
unfold Wcase.
apply hm.
 apply Wfst_def.

 apply Wsnd_fun_def_dom with (1:=tyf).
Qed.

(** The type operator on the construction domain *)
Definition Wf X :=
  sup A (fun x => replf (Π _ ∈ B x, X) (fun f => Wsup x f)). 

Hint Resolve Wsup_morph.

Lemma Wf_intro X x f :
  x ∈ A ->
  f ∈ cc_prod (B x) (fun _ => X) ->
  Wsup x f ∈ Wf X.
intros.
unfold Wf.
rewrite sup_ax.
 exists x; trivial.
 rewrite replf_ax; auto with *.
  exists f; auto with *.

  do 2 red; intros; apply Wsup_morph; auto with *.

 do 2 red; intros.
 apply replf_morph_raw.
  apply cc_prod_morph; auto with *.
  red; intros; reflexivity.

  red; intros; apply Wsup_morph; trivial.
Qed.

Lemma Wf_elim : forall a X,
  a ∈ Wf X ->
  exists2 x, x ∈ A & exists2 f, f ∈ Π i ∈ B x, X & a == Wsup x f.
intros.
unfold Wf in H.
rewrite sup_ax in H.
 destruct H as (x,tyx,tya).
 rewrite replf_ax in tya.
  destruct tya as (f,tyf,eqa).
  exists x; trivial.
  exists f; trivial.

  do 2 red; intros; apply Wsup_morph; auto with *.

 do 2 red; intros.
 apply replf_morph_raw.
  apply cc_prod_morph; auto with *.
  red; intros; reflexivity.

  red; intros; apply Wsup_morph; trivial.
Qed.

Lemma Wf_elim' X x f :
  x ∈ A ->
  (forall i, i ∈ B x -> cc_app f i ∈ Wdom) ->
  X ⊆ Wdom ->
  Wsup x f ∈ Wf X ->
  forall i, i ∈ B x -> cc_app f i ∈ X.
intros tyx tyf Xincl tyw.
apply Wf_elim in tyw.
destruct tyw as (x',tyx',(f',tyf',eqw)).
apply Wsup_inj in eqw; intros; auto.
trivial.
 destruct eqw as (eqx,eqf).
 rewrite eqf; trivial.
 apply cc_prod_elim with (1:=tyf').
 rewrite <- eqx; trivial.

 apply Xincl.
 apply cc_prod_elim with (1:=tyf'); trivial.
Qed.

Instance Wf_mono : Proper (incl_set ==> incl_set) Wf.
intros X Y inclXY a tya.
apply Wf_elim in tya; destruct tya as (x,tyx,(f,tyf,eqz)); rewrite eqz.
apply Wf_intro; trivial.
revert tyf; apply cc_prod_covariant; auto with *.
Qed.

Instance Wf_morph : morph1 Wf.
apply Fmono_morph; auto with *.
Qed.
Hint Resolve Wf_mono Wf_morph.

Lemma Wf_typ X :
  X ⊆ Wdom -> Wf X ⊆ Wdom.
red; intros.
apply Wf_elim in H0; destruct H0 as (x,tyx,(f,tyf,eqz)); rewrite eqz.
apply Wsup_typ_gen; trivial.
revert tyf; apply cc_prod_covariant; auto with *.
(*intros.
apply H.
apply cc_prod_elim with (1:=tyf); trivial.*)
Qed.
Hint Resolve Wf_typ.

Lemma Wfst_typ_gen X w :
  w ∈ Wf X ->
  Wfst w ∈ A.
intros tyw.
apply Wf_elim in tyw; trivial.
destruct tyw as (x,tyx,(f,tyf,eqw)).
rewrite eqw,Wfst_def; trivial.
Qed.

Lemma Wsnd_fun_typ_gen X w :
  X ⊆ Wdom ->
  w ∈ Wf X ->
  Wsnd_fun w ∈ Π _ ∈ B (Wfst w), X.
intros XinclW tyw.
apply Wf_elim in tyw; trivial.
destruct tyw as (x,tyx,(f,tyf,eqw)).
apply in_reg with f.
 rewrite eqw, Wsnd_fun_def_dom.
 reflexivity.
 eapply cc_prod_covariant;[|reflexivity|intros; apply XinclW|].
  do 2 red; reflexivity.
  exact tyf.
apply eq_elim with (2:=tyf).
apply cc_prod_ext.
 rewrite eqw,Wfst_def; reflexivity.
 red; reflexivity.
Qed.

Lemma Wsnd_typ_gen X w i :
  X ⊆ Wdom ->
  w ∈ Wf X ->
  i ∈ B (Wfst w) ->
  Wsnd w i ∈ X.
intros.
apply Wsnd_fun_typ_gen in H0; trivial.
apply cc_prod_elim with (1:=H0); trivial.
Qed.

Lemma Wcase_typ_dom X Q h w :
  morph1 Q ->
  X ⊆ Wdom ->
  (forall x f, x ∈ A -> f ∈ (Π i ∈ B x, X) -> h x f ∈ Q (Wsup x f)) ->
  w ∈ Wf X ->
  Wcase h w ∈ Q w.
intros Qm tyX tyh tyw.
apply Wf_elim in tyw.
destruct tyw as (x,tyx,(f,tyf,eqw)).
assert (eq1 : Wfst w == x).
 rewrite eqw, Wfst_def; reflexivity.
assert (eq2 : Wsnd_fun w == f).
 rewrite eqw.
 eapply cc_prod_covariant in tyf.
  apply Wsnd_fun_def_dom with (1:=tyf).
   auto with *.
   reflexivity.
   trivial.
unfold Wcase.
eapply eq_elim.
2:apply tyh.
 apply Qm.
 symmetry; apply transitivity with (1:=eqw).
 apply Wsup_morph; auto with *.

 rewrite eq1; trivial.

 rewrite eq2.
 revert tyf; apply eq_elim.
 apply cc_prod_ext; auto with *.
 red; reflexivity.
Qed.

Require Import ZFstable.

Lemma Wf_stable0 (K:set->Prop) :
  (forall X, K X -> X ⊆ Wdom) ->
 stable_class K Wf.
red; intros Kdef X Xty z H.
assert (forall a, a ∈ X -> z ∈ Wf a).
 intros.
 apply inter_elim with (1:=H).
 rewrite replf_ax.
 2:red;red;intros;apply Wf_morph; trivial.
 exists a; auto with *.
destruct inter_wit with (2:=H); auto.
assert (tyz := H0 _ H1).
apply Wf_elim in tyz.
destruct tyz as (x',tyx,(f,tyf,eqz)).
rewrite eqz.
apply Wf_intro; trivial.
rewrite cc_eta_eq with (1:=tyf).
apply cc_prod_intro; intros.
 intros ? ? ? h; rewrite h; reflexivity.
 do 2 red; reflexivity.
apply inter_intro; eauto.
intros.
specialize H0 with (1:=H3).
apply Wf_elim in H0.
destruct H0 as (x'',tyx',(f',tyf',eqz')).
rewrite eqz in eqz'.
apply Wsup_inj in eqz'; trivial; intros.
 destruct eqz' as (eqx,eqf).
 rewrite eqf; trivial.
 apply cc_prod_elim with (1:=tyf').
 rewrite <- eqx; trivial.

 apply (Kdef x); auto.
 apply cc_prod_elim with (1:=tyf); trivial.

 apply (Kdef y); auto.
 apply cc_prod_elim with (1:=tyf'); trivial.
Qed.

(*
Lemma Wf_stable : stable_class (fun X : set => X ⊆ Ffix Wf Wdom) Wf.
apply Wf_stable0.
intros.
rewrite H; apply Ffix_inA.
Qed.
*)

(* Using the impredicative construction of the fixpoint of a monotonic
   operator (Tarski), we get the type W. *)
Definition W := FIX incl_set inter Wdom (power Wdom) Wf.

Lemma W_lfp : is_lfp incl_set Wf W. 
apply knaster_tarski; auto with *.
Qed.

Lemma W_eqn : W == Wf W.
symmetry; apply W_lfp.
Qed.

Lemma W_least X : Wf X ⊆ X -> W ⊆ X.
apply W_lfp.
Qed.

Lemma W_typ : W ⊆ Wdom.
apply lfp_typ; auto with *.
Qed.

Lemma Wf_stable : stable_class (fun X => X ⊆ W) Wf.
apply Wf_stable0.
intros; transitivity W; trivial.
apply W_typ.
Qed.

Lemma W_ind : forall (P:set->Prop),
  Proper (eq_set ==> iff) P ->
  (forall x f, x ∈ A -> f ∈ (Π i ∈ B x, W) ->
   (forall i, i ∈ B x -> P (cc_app f i)) ->
   P (Wsup x f)) ->
  forall a, a ∈ W -> P a.
intros.
cut (W ⊆ subset W P).
 intros inclW; apply inclW in H1.
 apply subset_elim2 in H1; destruct H1 as (a',eqa,?).
 rewrite eqa; trivial.
clear a H1.
(*apply FIX_ind; auto with *.
fold W; intros.
trivial.
*)
apply lower_bound; auto with *.
unfold M'.
assert (inclDom : subset W P ⊆ Wdom).
 red; intros.
 apply W_typ.
 apply subset_elim1 in H1; trivial.
apply subset_intro.
 apply subset_intro; trivial.
 apply power_intro; trivial.
red.
red; intros.
apply Wf_elim in H1.
destruct H1 as (x,tyx,(f,tyf,eqz)).
rewrite eqz.
apply subset_intro.
 rewrite W_eqn.
 apply Wf_intro; trivial.
 revert tyf; apply cc_prod_covariant; auto with *.
 red; intros.
 apply subset_elim1 in H2; trivial.

 apply H0; trivial.
  revert tyf; apply cc_prod_covariant; auto with *.
  red; intros.
  apply subset_elim1 in H2; trivial.

  intros.
  specialize cc_prod_elim with (1:=tyf) (2:=H1); intros tyfi.
  apply subset_elim2 in tyfi; destruct tyfi as (w',tyw',?).
  rewrite tyw'; trivial.
Qed.

Lemma Wfst_typ w :
  w ∈ W ->
  Wfst w ∈ A.
intros tyw.
rewrite W_eqn in tyw; trivial.
apply Wfst_typ_gen in tyw; trivial.
Qed.

Lemma Wsnd_fun_typ w :
  w ∈ W ->
  Wsnd_fun w ∈ Π _ ∈ B (Wfst w), W.
intros tyw.
rewrite W_eqn in tyw.
apply Wsnd_fun_typ_gen with (2:=tyw).
apply W_typ.
Qed.

Lemma Wsnd_fun_def Y x f :
  f ∈ (Π i ∈ Y, W) ->
  Wsnd_fun (Wsup x f) == f.
intros.
apply Wsnd_fun_def_dom with (Y:=Y); trivial.
revert H; apply cc_prod_covariant; auto with *.
intros.
apply W_typ.
Qed.
(*
Lemma Wsnd_typ w i :
  w ∈ W ->
  i ∈ B (Wfst w) ->
  Wsnd w i ∈ W.
intros tyw tyi.
apply Wsnd_fun_typ in tyw.
apply cc_prod_elim with (1:=tyw); trivial.
Qed.
*)
Lemma Wcase_typ X Q h w :
  morph1 Q ->
  X ⊆ W ->
  (forall x f, x ∈ A -> f ∈ (Π i ∈ B x, X) -> h x f ∈ Q (Wsup x f)) ->
  w ∈ Wf X ->
  Wcase h w ∈ Q w.
intros.
apply Wcase_typ_dom with X; trivial.
transitivity W; trivial.
apply W_typ.
Qed.

Lemma Wcase_eqn h x f :
  morph2 h ->
  f ∈ (Π i ∈ B x, W) ->
  Wcase h (Wsup x f) == h x f.
intros.
apply Wcase_eqn_dom; trivial.
revert H0; apply cc_prod_covariant; auto with *.
intros.
apply W_typ.
Qed.


(** The primitive recursor *)

Section PrimRecursor.

Variable P : set -> set.
Hypothesis Pm : morph1 P.

Variable F : set -> set -> set -> set.
Hypothesis Fm : Proper (eq_set==>eq_set==>eq_set==>eq_set) F.
Hypothesis f_typ : forall x f recf,
  x ∈ A ->
  f ∈ (Π i ∈ B x, W) ->
  recf ∈ (Π i ∈ B x, P (cc_app f i)) -> 
  F x f recf ∈ P (Wsup x f).

(**)

Definition Wrec_rel w y :=
  forall Q, Proper (eq_set==>eq_set==>iff) Q ->
  (forall x f recf,
   x ∈ A ->
   f ∈ (Π i ∈ B x, W) ->
   recf ∈ (Π i ∈ B x, P (cc_app f i)) ->
   (forall i, i ∈ B x -> Q (cc_app f i) (cc_app recf i)) -> 
   Q (Wsup x f) (F x f recf)) -> 
  Q w y.

Instance Wrec_rel_morph : Proper (eq_set==>eq_set==>iff) Wrec_rel.
do 3 red; intros.
apply fa_morph; intros Q.
apply fa_morph; intros Qm.
apply fa_morph; intros.
apply Qm; trivial.
Qed.

Lemma Wrec_rel_intro x f recf :
  x ∈ A ->
  f ∈ (Π i ∈ B x, W) ->
  recf ∈ (Π i ∈ B x, P (cc_app f i)) ->
  (forall i, i ∈ B x -> Wrec_rel (cc_app f i) (cc_app recf i)) ->
  Wrec_rel (Wsup x f) (F x f recf).
red; intros.
apply H4; trivial.
intros.
apply H2; trivial.
Qed.

Lemma Wrec_rel_elim w y :
  w ∈ W ->
  Wrec_rel w y ->
  exists2 x, x ∈ A &
  exists2 f, f ∈ (Π i ∈ B x, W) /\ w == Wsup x f &
  exists2 recf,
   recf ∈ (Π i ∈ B x, P (cc_app f i)) &
   y == F x f recf /\
  (forall i, i ∈ B x -> Wrec_rel (cc_app f i) (cc_app recf i)).
intros tyw inv.
apply proj2 with (A:=Wrec_rel w y).
pattern w, y.
apply inv; intros.
 do 3 red; intros.
 apply and_iff_morphism.
  rewrite H,H0; reflexivity.
 apply ex2_morph; intros x'; auto with *.
 apply ex2_morph; intros f'; auto with *.
  rewrite H; reflexivity.
 apply ex2_morph; intros recf; auto with *.
 rewrite H0; reflexivity.

 split.
 apply Wrec_rel_intro; trivial.
 intros.
 apply H2; trivial.

 exists x; trivial.
 exists f; auto with *.
 exists recf; trivial.
 split; auto with *.
 intros.
 apply H2.
 trivial.
Qed.

Lemma Wrec_rel_elim' x f y :
  x ∈ A ->
  f ∈ (Π i ∈ B x, W) ->
  Wrec_rel (Wsup x f) y ->
  exists2 recf,
   recf ∈ (Π i ∈ B x, P (cc_app f i)) &
   y == F x f recf /\
  (forall i, i ∈ B x -> Wrec_rel (cc_app f i) (cc_app recf i)).
intros.
assert (tyw : Wsup x f ∈ W).
 rewrite W_eqn; apply Wf_intro; trivial.
apply Wrec_rel_elim in H1; trivial.
destruct H1 as (x',tyx',(f',(tyf',eqw),(recf,tyrecf,(eqf,?)))).
apply Wsup_inj in eqw; trivial.
 destruct eqw.
 exists recf.
 revert tyrecf; apply eq_elim.
 apply cc_prod_ext; auto with *.
 red; intros.
 rewrite <- H5.
 rewrite <- H2 in H4.
 rewrite H3; auto with *.

 split.
  rewrite eqf.
  apply Fm; auto with *.
  rewrite cc_eta_eq with (1:=H0).
  rewrite cc_eta_eq with (1:=tyf').
  apply cc_lam_ext; auto with *.
  red; intros.
  rewrite <- H5.
  rewrite <- H2 in H4.
  rewrite H3; auto with *.

  intros.
  rewrite H3; auto with *.
  rewrite H2 in H4; auto.

    intros. 
    apply W_typ.
    apply cc_prod_elim with (1:=H0); trivial.

    intros. 
    apply W_typ.
    apply cc_prod_elim with (1:=tyf'); trivial.
Qed.

Lemma Wrec_ex w :
  w ∈ W ->
  exists2 y, y ∈ P w & Wrec_rel w y /\ (forall y', Wrec_rel w y' -> y==y').
intros tyw.
pattern w; apply W_ind; intros; trivial.
 do 2 red; intros.
 apply ex2_morph; intros y'.
  rewrite H; reflexivity.
 apply and_iff_morphism.
  rewrite H; reflexivity.
 apply fa_morph; intros y''.
 rewrite H; reflexivity.

 pose (recf := λ i ∈ B x, union (subset (P (cc_app f i)) (Wrec_rel (cc_app f i)))).
 assert (tyrecf : recf ∈ Π i ∈ B x, P (cc_app f i)).
  apply cc_prod_intro; intros.
   do 2 red; intros.
   apply union_morph; apply subset_morph.
    rewrite H3; reflexivity.
   red; intros.
   rewrite H3; reflexivity.

   intros ? ? ? h; rewrite h; reflexivity.

   destruct H1 with (1:=H2).
   destruct H4.
   rewrite union_subset_singl with (y:=x1)(y':=x1); auto with *.
   intros.
   rewrite <- H5 with (1:=H8).
   rewrite <- H5 with (1:=H9).
   reflexivity.
 exists (F x f recf).
  apply f_typ; trivial.
 split; intros.
  apply Wrec_rel_intro; intros; trivial.
  destruct H1 with (1:=H2).
  destruct H4.
  unfold recf; rewrite cc_beta_eq; trivial.
   rewrite union_subset_singl with (y:=x0)(y':=x0); intros; auto with *.
   rewrite <- H5 with (1:=H8).
   rewrite <- H5 with (1:=H9).
   reflexivity.

   do 2 red; intros.
   apply union_morph; apply subset_morph.
    rewrite H7; reflexivity.
   red; intros.
   rewrite H7; reflexivity.

   apply Wrec_rel_elim' in H2; trivial.
   destruct H2 as (recf',tyrecf',(eqy,?)).
   rewrite eqy.
   apply Fm; auto with *.
   rewrite cc_eta_eq with (1:=tyrecf').
   apply cc_lam_ext; auto with *.
   red; intros.
   rewrite <- H4; auto.
   apply union_subset_singl with (y':=cc_app recf' x0); intros; auto with *.
    apply cc_prod_elim with (1:=tyrecf'); trivial.

    destruct H1 with (1:=H3); intros.
    destruct H10.
    rewrite <- H11 with (1:=H7).
    rewrite <- H11 with (1:=H8).
    reflexivity.
Qed.

Definition WREC w := union (subset (P w) (Wrec_rel w)).

Lemma WREC_ok w :
  w ∈ W ->
  Wrec_rel w (WREC w).
intros.
destruct Wrec_ex with (1:=H).
destruct H1.
unfold WREC.
rewrite union_subset_singl with (y:=x)(y':=x); auto with *.
intros.
rewrite <- H2 with (1:=H5).
rewrite <- H2 with (1:=H6).
reflexivity.
Qed.

Lemma WREC_typ w :
  w ∈ W -> 
  WREC w ∈ P w.
intros tyw.
destruct Wrec_ex with (1:=tyw) as (y,tyy,(ydef,?)).
unfold WREC.
rewrite union_subset_singl with (y:=y)(y':=y); intros; auto with *.
rewrite <- H with (1:=H2).
rewrite <- H with (1:=H3).
reflexivity.
Qed.

Lemma WREC_eqn x f :
  x ∈ A ->
  f ∈ (Π i ∈ B x, W) ->
  WREC (Wsup x f) == F x f (λ i ∈ B x, WREC (cc_app f i)).
intros tya tyf.
assert (Wrec_rel (Wsup x f) (WREC (Wsup x f))).  
 apply WREC_ok.
 rewrite W_eqn; apply Wf_intro; auto.
apply Wrec_rel_elim' in H; trivial.
destruct H as (recf,tyrecf,(eqf,?)).
rewrite eqf.
apply Fm; auto with *.
rewrite cc_eta_eq with (1:=tyrecf).
apply cc_lam_ext; auto with *.
red; intros.
rewrite H1 in H0|-*.
symmetry.
apply union_subset_singl with (y':=cc_app recf x'); auto with *.
 apply cc_prod_elim with (1:=tyrecf); trivial.

 intros.
 destruct Wrec_ex with (w:=cc_app f x').
  apply cc_prod_elim with (1:=tyf); trivial.
 destruct H7.
 rewrite <- H8 with (1:=H4).
 rewrite <- H8 with (1:=H5).
 reflexivity.
Qed.

End PrimRecursor.

(** The recursor (size-based style), but only allowing recursive calls
    on direct subterms *)

Section Recursor.

Variable P : set -> set.
Hypothesis Pm : morph1 P.

Variable F : set -> set -> set.
Hypothesis Fm : Proper (eq_set==>eq_set==>eq_set) F.
Hypothesis f_typ : forall X x recf,
  X ⊆ W ->
  x ∈ Wf X ->
  recf ∈ (Π w ∈ X, P w) ->
  F recf x ∈ P x.
Hypothesis Firr : forall X recf recf',
  X ⊆ W ->
  (forall x, x ∈ X -> cc_app recf x == cc_app recf' x) ->
  forall x, x ∈ Wf X -> F recf x == F recf' x.

Definition Wsrec_rel w y :=
  forall Q, Proper (eq_set==>eq_set==>iff) Q ->
  (forall X x recf,
   X ⊆ W ->
   x ∈ Wf X ->
   recf ∈ (Π w ∈ X, P w) ->
   (forall w, w ∈ X -> Q w (cc_app recf w)) -> 
   Q x (F recf x)) -> 
  Q w y.

Instance Wsrec_rel_morph : Proper (eq_set==>eq_set==>iff) Wsrec_rel.
do 3 red; intros.
apply fa_morph; intros Q.
apply fa_morph; intros Qm.
apply fa_morph; intros.
apply Qm; trivial.
Qed.

Lemma Wsrec_rel_intro X x recf :
  X ⊆ W ->
  x ∈ Wf X ->
  recf ∈ (Π w ∈ X, P w) ->
  (forall w, w ∈ X -> Wsrec_rel w (cc_app recf w)) -> 
  Wsrec_rel x (F recf x).
red; intros.
apply H4 with X; trivial.
intros.
apply H2; trivial.
Qed.

Lemma Wsrec_rel_elim w y :
  w ∈ W ->
  Wsrec_rel w y ->
  exists2 X, X ⊆ W /\ w ∈ Wf X &
  exists2 recf, recf ∈ (Π w ∈ X, P w) &
    y == F recf w /\
    (forall w, w ∈ X -> Wsrec_rel w (cc_app recf w)).
intros tyw inv.
apply proj2 with (A:=Wsrec_rel w y).
pattern w, y.
apply inv; intros.
 do 3 red; intros.
 apply and_iff_morphism.
  rewrite H,H0; reflexivity.
 apply ex2_morph; intros X; auto with *.
  rewrite H; reflexivity.
 apply ex2_morph; intros recf'; auto with *.
  rewrite H,H0; reflexivity.

 split.
  apply Wsrec_rel_intro with X; trivial.
  intros.
  apply H2; trivial.

  exists X; auto.
  exists recf; trivial.
  split; auto with *.
  intros.
  apply H2.
  trivial.
Qed.


Lemma Wsrec_rel_elim' x f y :
  x ∈ A ->
  f ∈ (Π i ∈ B x, W) ->
  Wsrec_rel (Wsup x f) y ->
  exists2 X, X ⊆ W /\ f ∈ (Π i ∈ B x, X) &
  exists2 recf, recf ∈ (Π w ∈ X, P w) &
    y == F recf (Wsup x f) /\
   (forall w, w ∈ X -> Wsrec_rel w (cc_app recf w)).
intros.
assert (tyw : Wsup x f ∈ W).
 rewrite W_eqn; apply Wf_intro; trivial.
apply Wsrec_rel_elim in H1; trivial.
destruct H1 as (X,(XinclW,tyw'),(recf,tyrecf,(eqy,?))).
apply Wf_elim in tyw'; destruct tyw' as (x',tyx',(f',tyf',eqw)).
apply Wsup_inj in eqw; trivial.
 destruct eqw as (eqx,eqf).
 exists X. 
  split; trivial.
  rewrite cc_eta_eq with (1:=H0).
  apply cc_prod_intro; intros; auto with *.
   do 2 red; intros; apply cc_app_morph; auto with *.
  rewrite eqf; trivial.
  apply cc_prod_elim with (1:=tyf').
  rewrite <-eqx; trivial.
 exists recf; auto.

 intros.
 apply W_typ.
 apply cc_prod_elim with (1:=H0); trivial.

 intros.
 apply W_typ.
 apply XinclW.
 apply cc_prod_elim with (1:=tyf'); trivial.
Qed.

Lemma Wsrec_ex w :
  w ∈ W ->
  exists2 y, y ∈ P w & Wsrec_rel w y /\ (forall y', Wsrec_rel w y' -> y==y').
intros tyw.
pattern w; apply W_ind; intros; trivial.
 do 2 red; intros.
 apply ex2_morph; intros y'.
  rewrite H; reflexivity.
 apply and_iff_morphism.
  rewrite H; reflexivity.
 apply fa_morph; intros y''.
 rewrite H; reflexivity.

 pose (X := replf (B x) (cc_app f)).
 assert (Xdef : forall z, z ∈ X <-> exists2 i, i ∈ B x & z == cc_app f i).
  intros.
  subst X; rewrite replf_ax; auto with *.
  do 2 red; intros; apply cc_app_morph; auto with *.
 assert (XinclW : X ⊆ W).
  red; intros.
  rewrite Xdef in H2.
  destruct H2 as (i,tyi,eqz); rewrite eqz.
  apply cc_prod_elim with (1:=H0); trivial.
 pose (recf := λ w ∈ X, union (subset (P w) (Wsrec_rel w))).
 assert (tyf : f ∈ Π _ ∈ B x, X).
  rewrite cc_eta_eq with (1:=H0).
  apply cc_prod_intro; intros; auto with *.
   do 2 red; intros; apply cc_app_morph; auto with *.
  rewrite Xdef; eauto with *.
 assert (tyrecf : recf ∈ Π w ∈ X, P w).
  apply cc_prod_intro; intros.
   do 2 red; intros.
   apply union_morph; apply subset_morph.
    rewrite H3; reflexivity.
   red; intros.
   rewrite H3; reflexivity.

   intros ? ? ? h; rewrite h; reflexivity.

   rewrite Xdef in H2.
   destruct H2 as (i,tyi,eqx0).
   destruct H1 with (1:=tyi).
   destruct H3.
   rewrite <- eqx0 in H2,H3.
   rewrite union_subset_singl with (y:=x1)(y':=x1); auto with *.
   intros.
   rewrite eqx0 in H7,H8.
   rewrite <- H4 with (1:=H7).
   rewrite <- H4 with (1:=H8).
   reflexivity.
 exists (F recf (Wsup x f)).
  apply f_typ with X; trivial.
  apply Wf_intro; trivial.
 split; intros.
  apply Wsrec_rel_intro with (X:=X); intros; trivial.
   apply Wf_intro; trivial.
  rewrite Xdef in H2; destruct H2 as (i,tyi,eqz).
  destruct H1 with (1:=tyi).
  destruct H3.
  unfold recf; rewrite cc_beta_eq; trivial.
   rewrite <- eqz in H2,H3.
   rewrite union_subset_singl with (y:=x0)(y':=x0); intros; auto with *.
   rewrite eqz in H7,H8.
   rewrite <- H4 with (1:=H7).
   rewrite <- H4 with (1:=H8).
   reflexivity.

   do 2 red; intros.
   apply union_morph; apply subset_morph.
    rewrite H6; reflexivity.
   red; intros.
   rewrite H6; reflexivity.

   rewrite Xdef; eauto.

  apply Wsrec_rel_elim' in H2; trivial.
   destruct H2 as (X',(X'inclW,tyf'),(recf',tyrecf',(eqy,?))).
   rewrite eqy.
   apply Firr with X; trivial.
    intros.
    assert (x0 ∈ X').
     rewrite Xdef in H3; destruct H3 as (i,tyi,eqz).
     rewrite eqz.
     apply cc_prod_elim with (1:=tyf'); trivial.
    unfold recf; rewrite cc_beta_eq; trivial.
     apply union_subset_singl with (y':=cc_app recf' x0); intros; auto with *.
      apply cc_prod_elim with (1:=tyrecf'); trivial.

      rewrite Xdef in H3; destruct H3 as (i,tyi,eqx0).
      destruct H1 with (1:=tyi); intros.
      destruct H9.
      rewrite eqx0 in H7,H8.
      rewrite <- H10 with (1:=H7).
      rewrite <- H10 with (1:=H8).
      reflexivity.

     do 2 red; intros.
     apply union_morph; apply subset_morph.
      rewrite H6; reflexivity.
     red; intros.
     rewrite H6; reflexivity.

    apply Wf_intro; trivial.
Qed.

Definition WSREC w := union (subset (P w) (Wsrec_rel w)).

Lemma WSREC_ok w :
  w ∈ W ->
  Wsrec_rel w (WSREC w).
intros.
destruct Wsrec_ex with (1:=H).
destruct H1.
unfold WSREC.
rewrite union_subset_singl with (y:=x)(y':=x); auto with *.
intros.
rewrite <- H2 with (1:=H5).
rewrite <- H2 with (1:=H6).
reflexivity.
Qed.

Lemma WSREC_eqn x f :
  x ∈ A ->
  f ∈ (Π i ∈ B x, W) ->
  WSREC (Wsup x f) == F (λ w ∈ W, WSREC w) (Wsup x f).
intros tya tyf.
assert (Wsrec_rel (Wsup x f) (WSREC (Wsup x f))).  
 apply WSREC_ok.
 rewrite W_eqn; apply Wf_intro; auto.
apply Wsrec_rel_elim' in H; trivial.
destruct H as (X,(XinclW,tyf'),(recf,tyrecf,(eqf,?))).
rewrite eqf.
apply Firr with X; auto with *.
2:apply Wf_intro; trivial.
intros.
rewrite cc_beta_eq; auto.
 symmetry.
 apply union_subset_singl with (y':=cc_app recf x0); auto with *.
  apply cc_prod_elim with (1:=tyrecf); trivial.

  intros.
  destruct Wsrec_ex with (w:=x0); auto.
  destruct H6.
  rewrite <- H7 with (1:=H3).
  rewrite <- H7 with (1:=H4).
  reflexivity.

 do 2 red; intros.
     apply union_morph; apply subset_morph.
      rewrite H2; reflexivity.
     red; intros.
     rewrite H2; reflexivity.
Qed.

End Recursor.

(** The recursor (size-based style), but allowing recursive calls
    on transitive subterms *)

(** First a theory of subterms *)
Definition wsubterms X :=
  inter (subset (power W) (fun Y => Y ⊆ Wf Y /\ X ∩ W ⊆ Y)).

Lemma wsubterms_incl_W X : wsubterms X ⊆ W.
unfold wsubterms.
red; intros.
apply inter_elim with (1:=H).
apply subset_intro.
 apply power_intro; auto.
split.
 rewrite <- W_eqn; reflexivity.
 apply inter2_incl2.
Qed.

Lemma wsubterms_trans X : wsubterms X ⊆ Wf (wsubterms X).
red; intros.
assert (zw := wsubterms_incl_W _ _ H).
rewrite W_eqn in zw.
apply Wf_elim in zw.
destruct zw as (x,tyx,(f,tyf,eqz)).
rewrite eqz; apply Wf_intro; trivial.
rewrite cc_eta_eq with (1:=tyf).
apply cc_prod_intro; intros.
 do 2 red; intros; apply cc_app_morph; auto with *.
 auto with *.

apply inter_intro; intros.
assert (z ∈ y).
 apply inter_elim with (1:=H); trivial.
rewrite subset_ax in H1.
destruct H1 as (yinclW,(y',eqy,(transy,incly))).
rewrite <- eqy in transy,incly.
apply transy in H2.
rewrite eqz in H2.
apply Wf_elim in H2.
destruct H2 as (x',tyx',(f',tyf',eqw)).
apply Wsup_inj in eqw; trivial.
 destruct eqw as (eqx,eqf).
 rewrite eqf; trivial.
 apply cc_prod_elim with (1:=tyf').
 rewrite <- eqx; trivial.

 intros.
 apply W_typ.
 apply cc_prod_elim with (1:=tyf); trivial.

 intros.
 apply W_typ.
 apply power_elim with (1:=yinclW).
 apply cc_prod_elim with (1:=tyf'); trivial.

exists W; apply subset_intro.
 apply power_intro; auto.
split.
 rewrite <- W_eqn; reflexivity.
 apply inter2_incl2.
Qed.

Lemma wsubterms_compl X : X ∩ W ⊆ wsubterms X.
red; intros.
apply inter_intro.
 intros.
rewrite subset_ax in H0.
destruct H0 as (yinclW,(y',eqy,(transy,incly))).
rewrite <- eqy in transy,incly.
auto.

exists W; apply subset_intro.
 apply power_intro; auto.
split.
 rewrite <- W_eqn; reflexivity.
 apply inter2_incl2.
Qed.

Lemma wsubterms_proj X : X ⊆ W -> X ⊆ Wf X -> wsubterms X == X.
intros XinclW Xtrans.
apply incl_eq.
 red; intros.
 apply inter_elim with (1:=H). 
 apply subset_intro.
  apply power_intro; auto with *.

  split; trivial.
  apply inter2_incl1.

 transitivity (X ∩ W).
  apply inter2_incl; auto with *.
  apply wsubterms_compl.
Qed.

(*
Definition fsub w :=
  subset W (fun w' => forall X, X ⊆ W -> X ⊆ Wf X -> w ∈ Wf X -> w' ∈ X).

Instance fsub_morph : morph1 fsub.
do 2 red; intros.
unfold fsub.
apply subset_morph; auto with *.
red; intros.
apply fa_morph; intros X.
rewrite H; reflexivity.
Qed.

Lemma fsub_elim X x y :
  X ⊆ W ->
  X ⊆ Wf X ->
  y ∈ Wf X ->
  x ∈ fsub y ->
  x ∈ X.
intros XinclW Xtrans tyy xsub.
unfold fsub in xsub; rewrite subset_ax in xsub.
destruct xsub as (tyx,(x',eqx,subt)).
rewrite eqx; eauto.
Qed.

Lemma fsub_inv : forall x y,
  x ∈ W ->
  y ∈ fsub x ->
  y ∈ W.
intros.
apply subset_elim1 in H0; trivial.
Qed.

Lemma fsub_intro x f i :
  x ∈ A ->
  f ∈ (Π i ∈ B x, W) ->
  i ∈ B x ->
  cc_app f i ∈ fsub (Wsup x f).
intros; unfold fsub.
apply subset_intro; intros.
 apply cc_prod_elim with (1:=H0); trivial.

 apply Wf_elim in H4.
 destruct H4 as (x',tyx',(f',tyf',eqw)).
 apply Wsup_inj in eqw; trivial.
  destruct eqw as (eqx,eqf).
  rewrite eqf; trivial.
  apply cc_prod_elim with (1:=tyf').
  rewrite <- eqx; trivial.

  intros.
  apply W_typ.
  apply cc_prod_elim with (1:=H0); trivial.

  intros.
  apply W_typ.
  apply H2.
  apply cc_prod_elim with (1:=tyf'); trivial.
Qed.

Lemma fsub_intro' x f w i :
  x ∈ A ->
  f ∈ (Π i ∈ B x, W) ->
  Wsup x f ∈ fsub w ->
  i ∈ B x ->
  cc_app f i ∈ fsub w.
intros; unfold fsub.
apply subset_intro; intros.
 apply cc_prod_elim with (1:=H0); trivial.

 specialize fsub_elim with (1:=H3)(2:=H4)(3:=H5)(4:=H1); intros.
 apply H4 in H6.
 apply Wf_elim in H6.
 destruct H6 as (x',tyx',(f',tyf',eqw)).
 apply Wsup_inj in eqw; trivial.
  destruct eqw as (eqx,eqf).
  rewrite eqf; trivial.
  apply cc_prod_elim with (1:=tyf').
  rewrite <- eqx; trivial.

  intros.
  apply W_typ.
  apply cc_prod_elim with (1:=H0); trivial.

  intros.
  apply W_typ.
  apply H3.
  apply cc_prod_elim with (1:=tyf'); trivial.
Qed.

Lemma fsub_trans w :
  w ∈ W ->
  fsub w ⊆ Wf (fsub w).
intros tyw w' subw.
assert (tyw' := fsub_inv _ _ tyw subw).
rewrite W_eqn in tyw'.
apply Wf_elim in tyw'.
destruct tyw' as (x,tyx,(f,tyf,eqw)).
rewrite eqw; apply Wf_intro; trivial.
rewrite cc_eta_eq with (1:=tyf).
apply cc_prod_intro; intros.
 do 2 red; intros; apply cc_app_morph; auto with *.
 auto with *.
apply fsub_intro' with x; trivial.
rewrite <- eqw; trivial.
Qed.


Lemma fsub_elim' w x f :
  x ∈ A ->
  f ∈ (Π i ∈ B x, W) ->
  w ∈ fsub (Wsup x f) ->
  exists2 i, i ∈ B x & cc_app f i == w \/ w ∈ fsub (cc_app f i).
intros.
pose (X := sup (B x) (fun i => singl (cc_app f i) ∪ fsub (cc_app f i))).
assert (Xdef : forall z, z ∈ X <->
         exists2 i, i ∈ B x & cc_app f i == z \/ z ∈ fsub (cc_app f i)).
 intros.
 unfold X; rewrite sup_ax.
 apply ex2_morph; red; intros; auto with *.
 rewrite union2_ax.
 apply or_iff_morphism.
  split; intros.
   apply singl_elim in H2; auto with *.
   rewrite <- H2; apply singl_intro.
  reflexivity.

 do 2 red; intros.
 rewrite H3; reflexivity.
assert (XinclW : X ⊆ W).
 red; intros.
 rewrite Xdef in H2.
 destruct H2 as (i,tyi,tyz).
 destruct tyz.
  rewrite <- H2; apply cc_prod_elim with (1:=H0); trivial.

  apply fsub_inv with (2:=H2).
  apply cc_prod_elim with (1:=H0); trivial.
rewrite <- Xdef.
eapply fsub_elim with (Wsup x f); trivial.
 red; intros.
 assert (tyz := XinclW _ H2).
 rewrite W_eqn in tyz; apply Wf_elim in tyz.
 destruct tyz as (x',tyx',(f',tyf',eqz)).
 rewrite eqz; apply Wf_intro; trivial.
 rewrite cc_eta_eq with (1:=tyf').
 apply cc_prod_intro; intros.
  do 2 red; intros; apply cc_app_morph; auto with *.
  auto with *.
 rewrite Xdef in H2.
 destruct H2 as (i,tyi,tyz).
 rewrite Xdef.
 exists i; trivial.
 right.
 destruct tyz.
  rewrite H2.
  rewrite eqz.
  apply fsub_intro; trivial.

  apply fsub_intro' with x'; trivial.
  rewrite <- eqz; trivial.

 apply Wf_intro; trivial.
 rewrite cc_eta_eq with (1:=H0).
 apply cc_prod_intro; intros.
  do 2 red; intros; apply cc_app_morph; auto with *.
  auto with *.
 rewrite Xdef.
 exists x0; auto with *.
Qed.

*)

Variable K : set -> Prop.
Hypothesis Km : Proper (eq_set==>iff) K.

Hypothesis Kinter : forall X,
  (exists z0, z0 ∈ X) ->
  (forall z, z ∈ X -> K z) ->
  K (inter X).

Hypothesis Ksup : forall I X,
  ext_fun I X ->
  (forall i, i ∈ I -> K (X i)) ->
  K (sup I X).

Hypothesis KW : forall X, K X -> X ⊆ W.
Hypothesis KWtop : K W.

Hypothesis Kintro : forall X,
  K X -> K (Wf X).
Hypothesis Ktrans : forall X,
  K X -> X ⊆ Wf X.

(* TODO
Hypothesis Kstage : forall w w',
   (forall X, K X -> w ∈ Wf X -> w' ∈ Wf X) ->
   forall X, K X -> w ∈ X -> w' ∈ X.
*)


Definition fsub w :=
  inter (subset (power W) (fun Z => K Z /\ w ∈ Wf Z)).

Instance fsub_morph : morph1 fsub.
do 2 red; intros.
unfold fsub.
apply inter_morph.
apply subset_morph; auto with *.
red; intros.
rewrite H; reflexivity.
Qed.

Lemma fsub_intro w w' :
  w ∈ W ->
  (forall X, K X -> w ∈ Wf X -> w' ∈ X) ->
  w' ∈ fsub w.
intros.
apply inter_intro; intros.
 apply subset_ax in H1.
 destruct H1 as (_,(y',eqy,(Ky,wy))).
 rewrite <- eqy in wy,Ky; auto.

 exists W.
 apply subset_intro.
  apply power_intro; trivial.
  split; trivial.
  rewrite <- W_eqn; trivial.
Qed.

Lemma fsub_elim X x y :
  K X ->
  y ∈ Wf X ->
  x ∈ fsub y ->
  x ∈ X.
intros KX tyy xsub.
apply inter_elim with (1:=xsub).
apply subset_intro; auto.
apply power_intro; apply KW; trivial.
Qed.

Lemma Kfsub w :
  w ∈ W ->
  K (fsub w).
intros tyw.
apply Kinter.
 exists W.
 apply subset_intro; auto.
  apply power_intro; trivial.

  split; trivial.
  rewrite <- W_eqn; trivial.

 intros.
 apply subset_elim2 in H.
 destruct H as (z',eqz,(?,_)).
 rewrite eqz; trivial.
Qed.


Definition fsub' w :=
  inter (subset (power W) (fun Z => K Z /\ w ∈ Z)).

Instance fsub'_morph : morph1 fsub'.
do 2 red; intros.
unfold fsub'.
apply inter_morph.
apply subset_morph; auto with *.
red; intros.
rewrite H; reflexivity.
Qed.

Lemma fsub'_intro w w' :
  w ∈ W ->
  (forall X, K X -> w ∈ X -> w' ∈ X) ->
  w' ∈ fsub' w.
intros.
apply inter_intro; intros.
 apply subset_ax in H1.
 destruct H1 as (_,(y',eqy,(Ky,wy))).
 rewrite <- eqy in wy,Ky; auto.

 exists W.
 apply subset_intro; auto.
 apply power_intro; trivial.
Qed.

Lemma fsub'_elim X x y :
  K X ->
  y ∈ X ->
  x ∈ fsub' y ->
  x ∈ X.
intros KX tyy xsub.
apply inter_elim with (1:=xsub).
apply subset_intro; auto.
apply power_intro; apply KW; trivial.
Qed.

Lemma Kfsub' w :
  w ∈ W ->
  K (fsub' w).
intros tyw.
apply Kinter.
 exists W.
 apply subset_intro; auto.
 apply power_intro; trivial.

 intros.
 apply subset_elim2 in H.
 destruct H as (z',eqz,(?,_)).
 rewrite eqz; trivial.
Qed.



(*
Variable Kstage : forall X x,
  K X ->
  x ∈ X -> Wf (fsub x) ⊆ X.
*)
(*Definition fsub' w := singl w ∪ fsub w.*)

(* TODO 
Lemma Kstage' : forall X x,
  K X ->
  x ∈ X -> Wf (fsub x) ⊆ X.
red; intros.
apply Kstage with (w:=x); trivial.
(* apply KW with X; trivial.*)

 intros.
 revert H1; apply Wf_mono.
 red; intros.
 apply fsub_elim with (3:=H1); trivial.
Qed.
*)

(*
Lemma fsubterms_inv X w :
  X ⊆ W ->
  w ∈ fsubterms X ->
  exists2 x, x ∈ X & w ∈ fsub' x.
*)
Lemma fsub_elim' w x f :
  x ∈ A ->
  f ∈ (Π i ∈ B x, W) ->
  w ∈ fsub (Wsup x f) ->
  exists2 i, i ∈ B x & w ∈ fsub' (cc_app f i).
intros tyx tyf tyw.
(*pose (X:=fsubterms (replf (B x) (fun i => cc_app f i))).
assert (w ∈ X).
apply fsubterms_intro.
 admit.

 intros.
 apply fsub_elim with (3:=tyw); trivial.
  apply Wf_intro; trivial.
  rewrite cc_eta_eq with (1:=tyf).
  apply cc_prod_intro; intros; auto.
   admit.

   apply H0.
   rewrite replf_ax.
   2:admit.
   exists x0; auto with *.

*)
pose (X := sup (B x) (fun i => fsub' (cc_app f i))).
assert (w ∈ X).
 apply fsub_elim with (3:=tyw). 
  apply Ksup.
   intros i i' tyi eqi; rewrite eqi; reflexivity.

   intros.
   apply Kfsub'.
   apply cc_prod_elim with (1:=tyf); trivial.

  apply Wf_intro; trivial.
  rewrite cc_eta_eq with (1:=tyf).
  apply cc_prod_intro; intros; auto.
   intros ? ? ? ?; apply cc_app_morph; trivial; reflexivity.

   unfold X; rewrite sup_ax.
   2:intros i i' tyi eqi; rewrite eqi; reflexivity.
   exists x0; trivial.
   apply fsub'_intro; trivial.
   apply cc_prod_elim with (1:=tyf); trivial.

unfold X in H; rewrite sup_ax in H; trivial.
intros i i' tyi eqi; rewrite eqi; reflexivity.
Qed.


Section TransitiveRecursor.


Variable O : set.
Hypothesis KO : K O.

Variable P : set -> set -> set.
Hypothesis Pm : morph2 P.
Hypothesis Pmono : forall X Y x,
  K Y ->
  (forall w, w ∈ X -> exists2 w', w' ∈ Y &(* w ∈ fsub w') ->*)
   forall X, K X -> w' ∈ Wf X -> w ∈ X) ->
  P (Wf X) x ⊆ P Y x.

Variable F : set -> set -> set -> set.
Hypothesis Fm : Proper (eq_set==>eq_set==>eq_set==>eq_set) F.
Hypothesis f_typ : forall X x recf,
  X ⊆ O ->
  K X ->
  x ∈ Wf X ->
  recf ∈ (Π w ∈ X, P X w) ->
  F X recf x ∈ P (Wf X) x.
Hypothesis Firr : forall X X' recf recf',
  X ⊆ O ->
  K X ->
  X' ⊆ O ->
  K X' ->
  recf ∈ (Π w ∈ X, P X w) ->
  recf' ∈ (Π w ∈ X', P X' w) ->
  (forall x, x ∈ X -> x ∈ X' -> cc_app recf x == cc_app recf' x) ->
  forall x, x ∈ Wf X -> x ∈ Wf X' -> F X recf x == F X' recf' x.

Definition Wsrec_rel' w y :=
  forall Q, Proper (eq_set==>eq_set==>iff) Q ->
  (forall X x recf,
   X ⊆ O ->
   K X ->
   x ∈ Wf X ->
   recf ∈ (Π w ∈ X, P X w) (*is_cc_fun X recf*) ->
   (forall w, w ∈ X -> Q w (cc_app recf w)) -> 
   Q x (F X recf x)) -> 
  Q w y.

Instance Wsrec_rel_morph' : Proper (eq_set==>eq_set==>iff) Wsrec_rel'.
do 3 red; intros.
apply fa_morph; intros Q.
apply fa_morph; intros Qm.
apply fa_morph; intros.
apply Qm; trivial.
Qed.

Lemma Wsrec_rel_intro' X x recf :
  X ⊆ O ->
  K X ->
  x ∈ Wf X ->
  recf ∈ (Π w ∈ X, P X w) (*is_cc_fun X recf*) ->
  (forall w, w ∈ X -> Wsrec_rel' w (cc_app recf w)) -> 
  Wsrec_rel' x (F X recf x).
red; intros.
apply H5; trivial.
intros.
apply H3; trivial.
Qed.

Lemma Wsrec'_rel_elim w y :
  w ∈ O ->
  Wsrec_rel' w y ->
  exists2 X, X ⊆ O /\ K X /\ w ∈ Wf X &
  exists2 recf, recf ∈ Π w ∈ X, P X w (*is_cc_fun X recf*) &
    y == F X recf w /\
    (forall w, w ∈ X -> Wsrec_rel' w (cc_app recf w)).
intros tyw inv.
apply proj2 with (A:=Wsrec_rel' w y).
pattern w, y.
apply inv; intros.
 do 3 red; intros.
 apply and_iff_morphism.
  rewrite H,H0; reflexivity.
 apply ex2_morph; intros X; auto with *.
  rewrite H; reflexivity.
 apply ex2_morph; intros recf'; auto with *.
  rewrite H,H0; reflexivity.

 split.
  apply Wsrec_rel_intro'; trivial.
  intros.
  apply H3; trivial.

  exists X; auto.
  exists recf; trivial.
  split; auto with *.
  intros.
  apply H3.
  trivial.
Qed.
(*
Lemma Wsrec_ex' w :
  w ∈ O ->
  forall w', w' ∈ fsub' w ->
  exists2 y, Wsrec_rel' w' y & (forall y', Wsrec_rel' w' y' -> y==y').
intros tyw.
assert (forall X, X ⊆ O -> K X ->
   w ∈ X ->
   forall w', w' ∈ fsub' w ->
   exists2 y, Wsrec_rel' w' y & (forall y', Wsrec_rel' w' y' -> y == y')).
2:apply H with (X:=O); auto with *.
apply KW in tyw; trivial.
pattern w; apply W_ind; intros; trivial.
 intros w1 w2 eqw.
 apply fa_morph; intros X.
 apply fa_morph; intros _.
 apply fa_morph; intros _.
 apply impl_morph.
  rewrite eqw; reflexivity.
 intros _.
 apply fa_morph; intros w'.
 rewrite eqw; reflexivity.

 set (Y := fsub (Wsup x f)) in *.
 set (REC := fun w => uchoice (Wsrec_rel' w)).
 assert (wsm : ext_fun Y REC).
  intros w1 w2 _ eqw.
  apply uchoice_morph_raw.
  apply Wsrec_rel_morph'; trivial.
 assert (KY : K Y).
  apply Kfsub.
  apply KW with (X:=X); trivial.

 assert (YinclX : Wf Y ⊆ X).
(*red; intros.
unfold Y in H6.
rewrite fsub_eq in H6.*)
(*apply Wf_stable0 with (K:=fun Y => Y ⊆ Wdom) in H6.*)
admit. (*  apply Kstage; trivial.*)
 assert (YinclO : Y ⊆ O).
  transitivity X; trivial.
  transitivity (Wf Y); trivial.
  apply Ktrans; trivial.
 assert (tyf : f ∈ Π _ ∈ B x, Y).
  rewrite cc_eta_eq with (1:=H0).
  apply cc_prod_intro; intros; auto with *.
   do 2 red; intros; apply cc_app_morph; auto with *.
  apply fsub_intro; auto.
   rewrite W_eqn; apply Wf_intro; trivial.

   intros Z ? ?.
   apply Wf_elim' with (x:=x); trivial.
    intros; apply W_typ.
    apply cc_prod_elim with (1:=H0); trivial.

    transitivity W;[|apply W_typ].
    apply KW; trivial.

 assert (tyw' : w' ∈ Wf Y).
  apply fsub'_elim with (3:=H5); auto.
(*   apply Kintro; trivial.*)

   apply Wf_intro; trivial.

 pose (recf := λ w ∈ Y, REC w).

 assert (tyHrec : forall  x0, x0 ∈ Y ->
    Wsrec_rel' x0 (REC x0) /\
    forall y, Wsrec_rel' x0 y -> REC x0 == y).
  intros x0 tyx0.
  apply fsub_elim' in tyx0; trivial.
  destruct tyx0 as (i,tyi,sbt).
  destruct H1 with (1:=tyi) (X:=Y) (5:=sbt); trivial.
   apply cc_prod_elim with (1:=tyf); trivial.
  assert (eqrec : REC x0 == x1).
   symmetry; apply uchoice_ext; trivial.
   split; intros.
    rewrite <- H8; trivial.
   split; intros.
    exists x1; trivial.
   rewrite <- H7 with (1:=H8).
   rewrite <- H7 with (1:=H9).
   reflexivity.
  rewrite eqrec.
  split; trivial.
  intros; rewrite eqrec; auto.
 assert (tyrecf : is_cc_fun Y recf).
  apply is_cc_fun_lam; trivial.
 exists (F Y recf w'); intros.
   apply Wsrec_rel_intro'; intros; trivial.
   unfold recf; rewrite cc_beta_eq; trivial.
   destruct tyHrec with (1:=H6) as (?,_); trivial.

   apply Wsrec'_rel_elim in H6; auto.
   destruct H6 as (X',(XinclO',(KX',tyw'')),(recf',tyrecf',(eqy,?))).
   rewrite eqy.
   apply Firr; trivial.
    apply cc_prod_intro; intros; auto with *.
     intros ????; apply Pm; auto with *.

   intros.
   unfold recf; rewrite cc_beta_eq; trivial.
   destruct tyHrec with (1:=H7) as (_,(_,?)); auto.
Qed.
*)

Lemma Wsrec_ex' w :
  w ∈ O ->
  forall w', w' ∈ fsub' w ->
  uchoice_pred (Wsrec_rel' w') /\
  uchoice (Wsrec_rel' w') ∈ P O w'.
intros tyw.
assert (forall X, X ⊆ O -> K X ->
   w ∈ X ->
   forall w', w' ∈ fsub' w ->
   uchoice_pred (Wsrec_rel' w') /\ uchoice (Wsrec_rel' w') ∈ P X w').
2:apply H; auto with *.
apply KW in tyw; trivial.
pattern w; apply W_ind; intros; trivial.
 intros w1 w2 eqw.
 apply fa_morph; intros X.
 apply fa_morph; intros _.
 apply fa_morph; intros _.
 apply impl_morph.
  rewrite eqw; reflexivity.
 intros _.
 apply fa_morph; intros w'.
 rewrite eqw; reflexivity.

 set (Y := fsub (Wsup x f)) in *.
 set (REC := fun w => uchoice (Wsrec_rel' w)).
 assert (wsm : ext_fun Y REC).
  intros w1 w2 _ eqw.
  apply uchoice_morph_raw.
  apply Wsrec_rel_morph'; trivial.
 assert (KY : K Y).
  apply Kfsub.
  apply KW with (X:=X); trivial.

(* assert (YinclX : Wf Y ⊆ X).
(*red; intros.
unfold Y in H6.
rewrite fsub_eq in H6.*)
(*apply Wf_stable0 with (K:=fun Y => Y ⊆ Wdom) in H6.*)
admit.*) (*  apply Kstage'; trivial.*)
 assert (YinclO : Y ⊆ O).
  transitivity X; trivial.
  red; intros.
  apply fsub_elim with (3:=H6); trivial.
  apply Ktrans; trivial.
 assert (tyf : f ∈ Π _ ∈ B x, Y).
  rewrite cc_eta_eq with (1:=H0).
  apply cc_prod_intro; intros; auto with *.
   do 2 red; intros; apply cc_app_morph; auto with *.
  apply fsub_intro; auto.
   rewrite W_eqn; apply Wf_intro; trivial.

   intros Z ? ?.
   apply Wf_elim' with (x:=x); trivial.
    intros; apply W_typ.
    apply cc_prod_elim with (1:=H0); trivial.

    transitivity W;[|apply W_typ].
    apply KW; trivial.

 assert (tyw' : w' ∈ Wf Y).
  apply fsub'_elim with (3:=H5); auto.
(*   apply Kintro; trivial.*)

   apply Wf_intro; trivial.

 pose (recf := λ w ∈ Y, REC w).

 assert (tyHrec : forall  x0, x0 ∈ Y ->
    uchoice_pred (Wsrec_rel' x0) /\ REC x0 ∈ P Y x0).
  intros x0 tyx0.
  apply fsub_elim' in tyx0; trivial.
  destruct tyx0 as (i,tyi,sbt).
  apply H1 with (i:=i); trivial.
  apply cc_prod_elim with (1:=tyf); trivial.
(*

 /\ Wsrec_rel' x0 (REC x0) /\
    forall y, Wsrec_rel' x0 y -> REC x0 == y).
  destruct H1 with (1:=tyi) (X:=Y) (5:=sbt) as (chm&(y,(Hy,tyy))&uniq); trivial.
   apply cc_prod_elim with (1:=tyf); trivial.
  assert (eqrec : REC x0 == y).
   symmetry; apply uchoice_ext.
   split; trivial.
    admit.
   split.
    exists y; trivial.

  destruct H1 with (1:=tyi) (X:=Y) (5:=sbt) as (_&(y,(Hy,tyy))&uniq); trivial.
   apply cc_prod_elim with (1:=tyf); trivial.
  assert (eqrec : REC x0 == y).
   symmetry; apply uchoice_ext.

   unfold REC; rewrite union_subset_singl with (y:=x1)(y':=x1); intros; auto with *.
    apply Pmono with Y; trivial.    
     transitivity (Wf Y); trivial.   
     apply Ktrans; trivial.

    rewrite <- H8 with (1:=H11).
    rewrite <- H8 with (1:=H12).
    reflexivity.
  rewrite eqrec.
  split; [|split]; trivial.
  intros; rewrite eqrec; auto.*)
 assert (tyrecf : recf ∈ Π w ∈ Y, P Y w).
  apply cc_prod_intro; intros; auto.
   intros ? ? ? h; rewrite h; reflexivity.
  destruct tyHrec with (1:=H6); trivial.
 assert (uch : uchoice_pred (Wsrec_rel' w')).
  split; [intros; rewrite <- H6; trivial|split;intros].
   exists (F Y recf w').
   apply Wsrec_rel_intro'; intros; trivial.
(*    apply is_cc_fun_lam; trivial.*)
   unfold recf; rewrite cc_beta_eq; trivial.
   apply uchoice_def.
   apply tyHrec; trivial.

   apply Wsrec'_rel_elim in H6; auto.
   destruct H6 as (X',(XinclO',(KX',tyw'')),(recf',tyrecf',(eqy,?))).
   rewrite eqy.
   apply Wsrec'_rel_elim in H7; auto.
   destruct H7 as (X'',(XinclO'',(KX'',tyw''')),(recf'',tyrecf'',(eqy',?))).
   rewrite eqy'.
   clear x0 x' eqy eqy'.
transitivity (F Y recf w').
   apply Firr; trivial.
   intros.
   unfold recf; rewrite cc_beta_eq; auto with *.
   apply uchoice_ext; auto.
   apply tyHrec; trivial.    

   apply Firr; trivial.
   symmetry; unfold recf; rewrite cc_beta_eq; auto with *.
   apply uchoice_ext; auto.
   apply tyHrec; trivial.    
apply fsub'_elim with (3:=H5); auto.
apply fsub'_elim with (3:=H5); auto.
 split; trivial.
apply in_reg with (F Y recf w').
apply uchoice_ext; trivial.
apply Wsrec_rel_intro'; auto.
   intros.
   unfold recf; rewrite cc_beta_eq; auto with *.
   apply uchoice_def.
   apply tyHrec; trivial.    
apply Pmono with Y; auto.
intros.
assert (w0 ∈ sup X fsub).
apply fsub_elim with (3:=H6); auto.
 apply Ksup.
 do 2 red; intros; apply fsub_morph; trivial.
 intros.
 apply Kfsub; auto.
 apply KW with (X:=X); trivial.

 apply Wf_intro; trivial.
 revert tyf; apply cc_prod_covariant; auto with *.
 intros.
 red; intros.
 rewrite sup_ax; auto with *.
 exists (Wsup x f); auto.
rewrite sup_ax in H7; auto with *.
destruct H7.
exists x0; trivial.
intros.
apply fsub_elim with (3:=H8); trivial.
Qed.

Definition WSREC' w := uchoice (Wsrec_rel' w).

Instance WSREC'_morph : morph1 WSREC'.
do 2 red; intros.
apply uchoice_morph_raw.
apply Wsrec_rel_morph'; trivial.
Qed.

Definition Wsrec_ex2 w tyw :=
  Wsrec_ex' w tyw w (fsub'_intro _ _ (KW _ KO _ tyw) (fun X KX tyw => tyw)).
(*
Lemma Wsrec_ex2 w :
  w ∈ O ->
  exists2 y, y ∈ P O w & Wsrec_rel' w y /\ (forall y', Wsrec_rel' w y' -> y==y').
*)

Lemma WSREC_ok' w :
  w ∈ O ->
  Wsrec_rel' w (WSREC' w).
intros.
unfold WSREC'; apply uchoice_def; apply Wsrec_ex2; trivial.
Qed.

Lemma WSREC_typ' w :
  w ∈ O -> 
  WSREC' w ∈ P O w.
intros tyw.
apply Wsrec_ex2 with (1:=tyw).
Qed.

Lemma WSREC_eqn' w :
  w ∈ O ->
  WSREC' w == F O (λ w ∈ O, WSREC' w) w.
intros tyw.
assert (Wsrec_rel' w (WSREC' w)).  
 apply WSREC_ok'; trivial.
apply Wsrec'_rel_elim in H; trivial.
destruct H as (X,(XinclW,(KX,tyw')),(recf,tyrecf,(eqf,tyf))).
rewrite eqf.
apply Firr; auto with *.
 apply cc_prod_intro; intros.
  do 2 red; intros.
  apply WSREC'_morph; trivial.

  do 2 red; intros; apply Pm; auto with *.

  apply WSREC_typ'; trivial.

 intros.
 rewrite cc_beta_eq; auto.
  apply uchoice_ext; auto.
  apply Wsrec_ex2 with (w:=x); auto.

  do 2 red; intros.
  apply WSREC'_morph; trivial.

 revert tyw'; apply Wf_mono; trivial.
Qed.


Lemma WSREC_eqn2' X x f :
  x ∈ A ->
  f ∈ (Π i ∈ B x, X) ->
  Wf X ⊆ O ->
  WSREC' (Wsup x f) == F O (λ w ∈ O, WSREC' w) (Wsup x f).
intros tya tyf inclO.
apply WSREC_eqn'.
apply inclO.
apply Wf_intro; auto.
Qed.

(*
Lemma W_bound_ind (P:set->Prop) O :
  O ⊆ W ->
  O ⊆ Wf O ->
  Proper (eq_set ==> iff) P ->
  (forall x f, x ∈ A -> f ∈ (Π i ∈ B x, W) ->
   Wsup x f ∈ O ->
   (forall i, i ∈ B x -> P (cc_app f i)) ->
   P (Wsup x f)) ->
  forall a, a ∈ O -> P a.
intros.
generalize H3; apply H in H3.
apply W_ind with (3:=H3).
 admit.

 intros.
 apply H2; trivial.
 intros.
 apply H6; trivial.
 apply H0 in H7.
 apply Wf_elim' with (i:=i) in H7; trivial.
  intros.
  apply W_typ.
  apply cc_prod_elim with (1:=H5); trivial.

  transitivity W; trivial.
  apply W_typ.
Qed.

Lemma W_fsub_ind_raw P O :
  Proper (eq_set ==> eq_set ==> iff) P ->
  K O ->
  (forall X w, X ⊆ O -> K X -> w ∈ X ->
   (forall w', w' ∈ fsub w -> P (fsub w) w') ->
   P X w) ->
  forall a, a ∈ O -> forall X a', X ⊆ O -> K X -> a' ∈ X -> a' ∈ fsub' a -> P X a'.
intros Pm KO Hstep a tya.
generalize tya; apply KW with (1:=KO) in tya.
apply W_ind with (3:=tya).
 do 2 red; intros.
 apply impl_morph.
  rewrite H; reflexivity.
 intros; apply fa_morph; intros X; apply fa_morph; intros a'.
 rewrite H; reflexivity.

 intros x f tyx tyf Hrec tyw X a' Xincl KX tya' a'sub.
 assert (tyww : Wsup x f ∈ W).
  rewrite W_eqn; apply Wf_intro; trivial.
 
 apply Hstep; trivial.
 intros w' w'sub.
 assert (w'sub' : w' ∈ fsub (Wsup x f)).
  apply fsub_elim with (3:=w'sub).
   apply Kfsub; trivial.
  apply fsub'_elim with (3:=a'sub); trivial.
   apply Kintro; apply Kfsub; trivial.
  apply Wf_intro; trivial.
   rewrite cc_eta_eq with (1:=tyf).
   apply cc_prod_intro; intros.
    intros ? ? ? ?; apply cc_app_morph; auto with *.
    auto with *.
   apply fsub_intro; trivial.
   intros.
   apply Wf_elim' with (i:=x0) in H1; trivial.
    intros; apply W_typ; apply cc_prod_elim with (1:=tyf); trivial.
    transitivity W;[|apply W_typ].
    apply KW; trivial.
 apply fsub_elim' in w'sub'; trivial.
 destruct w'sub' as (i,tyi,tyw').
 apply Hrec with (i:=i); trivial.
  apply Ktrans in tyw; trivial.
  apply Wf_elim' with (i:=i) in tyw; trivial.
   intros; apply W_typ; apply cc_prod_elim with (1:=tyf); trivial.
   transitivity W;[|apply W_typ].
   apply KW; trivial.

  red; intros.
  apply fsub_elim with (3:=H); trivial.
  apply Ktrans; auto.

  apply Kfsub.
  apply KW with (X:=O); auto.
Qed.

Lemma W_fsub_ind P O :
  Proper (eq_set ==> eq_set ==> iff) P ->
  K O ->
  (forall X w, X ⊆ O -> K X -> w ∈ X ->
   (forall w', w' ∈ fsub w -> P (fsub w) w') ->
   P X w) ->
  forall a, a ∈ O -> P O a.
intros.
apply W_fsub_ind_raw with (O:=O) (a:=a); auto with *.
apply fsub'_intro; auto.
apply KW with (X:=O); trivial.
Qed.
*)
(*
Lemma W_fsub_ind_raw (P:set->Prop) O :
  Proper (eq_set ==> iff) P ->
  K O ->
  (forall w, w ∈ O ->
   (forall w', w' ∈ fsub w -> P w') ->
   P w) ->
  forall a, a ∈ O -> forall a', a' ∈ fsub' a -> P a'.
intros Pm KO Hstep a tya.
generalize tya; apply KW with (1:=KO) in tya.
apply W_ind with (3:=tya).
 do 2 red; intros.
 apply impl_morph.
  rewrite H; reflexivity.
 intros; apply fa_morph; intros a'.
 rewrite H; reflexivity.

 intros x f tyx tyf Hrec tyw a' a'sub.
 assert (tyww : Wsup x f ∈ W).
  rewrite W_eqn; apply Wf_intro; trivial.
  
 apply Hstep; trivial.
  apply fsub'_elim with (3:=a'sub); trivial.
 intros w' w'sub.
 assert (w'sub' : w' ∈ fsub (Wsup x f)).
  apply fsub_elim with (3:=w'sub).
   apply Kfsub; trivial.
  apply fsub'_elim with (3:=a'sub); trivial.
   apply Kintro; apply Kfsub; trivial.
  apply Wf_intro; trivial.
   rewrite cc_eta_eq with (1:=tyf).
   apply cc_prod_intro; intros.
    intros ? ? ? ?; apply cc_app_morph; auto with *.
    auto with *.
   apply fsub_intro; trivial.
   intros.
   apply Wf_elim' with (i:=x0) in H1; trivial.
    intros; apply W_typ; apply cc_prod_elim with (1:=tyf); trivial.
    transitivity W;[|apply W_typ].
    apply KW; trivial.
 apply fsub_elim' in w'sub'; trivial.
 destruct w'sub' as (i,tyi,tyw').
 apply Hrec with (i:=i); trivial.
 apply Ktrans in tyw; trivial.
 apply Wf_elim' with (i:=i) in tyw; trivial.
  intros; apply W_typ; apply cc_prod_elim with (1:=tyf); trivial.
  transitivity W;[|apply W_typ].
  apply KW; trivial.
Qed.

Lemma W_fsub_ind (P:set->Prop) O :
  K O ->
  Proper (eq_set ==> iff) P ->
  (forall w, w ∈ O ->
   (forall w', w' ∈ fsub w -> P w') ->
   P w) ->
  forall a, a ∈ O -> P a.
intros.
apply W_fsub_ind_raw with (O:=O) (a:=a); trivial.
apply fsub'_intro; auto.
apply KW with (X:=O); trivial.
Qed.
*)


(* Attempt 1: P depends on the "stage" set

Section TransitiveRecursor.


Variable O : set.
Hypothesis KO : K O.

Variable P : set -> set -> set.
Hypothesis Pm : morph2 P.
Hypothesis Pmono : forall X Y x,
  X ⊆ Y ->
  P X x ⊆ P Y x.
(*Lemma Kstage' : forall X x,
  K X ->
  x ∈ X -> Wf (fsub x) ⊆ X.
*)
Hypothesis Pmono' : forall X Y x,
  K X ->
  x ∈ X ->
  X ⊆ Y ->
  P (Wf (fsub x)) x ⊆ P Y x.


Variable F : set -> set -> set -> set.
Hypothesis Fm : Proper (eq_set==>eq_set==>eq_set==>eq_set) F.
Hypothesis f_typ : forall X x recf,
  X ⊆ O ->
  K X ->
  x ∈ Wf X ->
  x ∈ O ->
  recf ∈ (Π w ∈ X, P X w) ->
  F X recf x ∈ P (Wf X ∩ O) x.
Hypothesis Firr : forall X X' recf recf',
  X ⊆ O ->
  K X ->
  X' ⊆ O ->
  K X' ->
  recf ∈ (Π w ∈ X, P X w) ->
  recf' ∈ (Π w ∈ X', P X' w) ->
  (forall x, x ∈ X -> x ∈ X' -> cc_app recf x == cc_app recf' x) ->
  forall x, x ∈ Wf X -> x ∈ Wf X' -> F X recf x == F X' recf' x.

Definition Wsrec_rel' w y :=
  forall Q, Proper (eq_set==>eq_set==>iff) Q ->
  (forall X x recf,
   X ⊆ O ->
   K X ->
   x ∈ Wf X ->
   recf ∈ (Π w ∈ X, P X w) ->
   (forall w, w ∈ X -> Q w (cc_app recf w)) -> 
   Q x (F X recf x)) -> 
  Q w y.

Instance Wsrec_rel_morph' : Proper (eq_set==>eq_set==>iff) Wsrec_rel'.
do 3 red; intros.
apply fa_morph; intros Q.
apply fa_morph; intros Qm.
apply fa_morph; intros.
apply Qm; trivial.
Qed.

Lemma Wsrec_rel_intro' X x recf :
  X ⊆ O ->
  K X ->
  x ∈ Wf X ->
  recf ∈ (Π w ∈ X, P X w) ->
  (forall w, w ∈ X -> Wsrec_rel' w (cc_app recf w)) -> 
  Wsrec_rel' x (F X recf x).
red; intros.
apply H5; trivial.
intros.
apply H3; trivial.
Qed.

Lemma Wsrec'_rel_elim w y :
  w ∈ O ->
  Wsrec_rel' w y ->
  exists2 X, X ⊆ O /\ K X /\ w ∈ Wf X &
  exists2 recf, recf ∈ (Π w ∈ X, P X w) &
    y == F X recf w /\ y ∈ P (Wf X ∩ O) w /\
    (forall w, w ∈ X -> Wsrec_rel' w (cc_app recf w)).
intros tyw inv.
apply proj2 with (A:=Wsrec_rel' w y).
pattern w, y.
apply inv; intros.
 do 3 red; intros.
 apply and_iff_morphism.
  rewrite H,H0; reflexivity.
 apply ex2_morph; intros X; auto with *.
  rewrite H; reflexivity.
 apply ex2_morph; intros recf'; auto with *.
  rewrite H,H0; reflexivity.

 split.
  apply Wsrec_rel_intro'; trivial.
  intros.
  apply H3; trivial.

  exists X; auto.
  exists recf; trivial.
  split; auto with *.
  split.
   apply f_typ; trivial.
admit.
  intros.
  apply H3.
  trivial.
Qed.

Lemma Wsrec_ex' w :
  w ∈ O ->
  exists2 y, y ∈ P O w & Wsrec_rel' w y /\ (forall y', Wsrec_rel' w y' -> y==y').
intros tyw; pattern O, w.
apply W_fsub_ind; trivial.
 admit.

 clear w tyw; intros X w Xincl KX tyw Hrec.
 set (Y := fsub w) in *.
 set (REC := fun w => union (subset (P Y w) (Wsrec_rel' w))).
 assert (wsm : ext_fun Y REC).
  intros w1 w2 _ eqw.
  apply union_morph; apply subset_morph.
   rewrite eqw; reflexivity.
  intros y tyy.
  rewrite eqw; reflexivity.
 assert (KY : K Y).
  apply Kfsub.
  apply KW with (X:=O); auto.
 assert (YinclX : Y ⊆ X).
  red; intros.
  apply fsub_elim with (3:=H); trivial.
  apply Ktrans; trivial.
 assert (tywY : w ∈ Wf Y).
(*  apply fsub'_elim with (3:=H5); auto. (* Kintro *)*)
admit.
 assert (Hrec' : forall  x0, x0 ∈ Y ->
    REC x0 ∈ P Y x0 /\ Wsrec_rel' x0 (REC x0) /\
    forall y, Wsrec_rel' x0 y -> REC x0 == y).
  intros w' tyw'.
  destruct Hrec with (1:=tyw') as (y,tyy,(Hy,uniq)).
  assert (eqrec : REC w' == y).
   unfold REC; rewrite union_subset_singl with (y:=y)(y':=y); intros; auto with *.
   rewrite <- uniq with (1:=H1).
   rewrite <- uniq with (1:=H2).
   reflexivity.
  rewrite eqrec.
  split; [|split]; trivial.
  intros; rewrite eqrec; auto.
 clear Hrec.
 pose (recf := λ w ∈ Y, REC w).
 assert (tyrecf : recf ∈ Π w ∈ Y, P Y w).
  apply cc_prod_intro; intros; auto.
   intros ? ? ? h; rewrite h; reflexivity.
  destruct Hrec' with (1:=H); trivial.
 exists (F Y recf w).
(*  apply Pmono' with X; trivial.*)
  apply Pmono with (Wf Y ∩ O); trivial.
   apply inter2_incl2.
  apply f_typ; trivial.
admit.
admit.

  split; intros.
   apply Wsrec_rel_intro'; intros; trivial.
admit.
admit.
   unfold recf; rewrite cc_beta_eq; trivial.
   destruct Hrec' with (1:=H) as (_,(?,_)); trivial.

   apply Wsrec'_rel_elim in H; auto.
   destruct H as (X',(XinclO',(KX',tyw'')),(recf',tyrecf',(eqy,(tyy,?)))).
   rewrite eqy.
   apply Firr; trivial.
admit.
   intros.
   unfold recf; rewrite cc_beta_eq; trivial.
   destruct tyHrec with (1:=H7) as (_,(_,?)); auto.

red; intros.
apply inter2_def in H6; destruct H6.

admit. (* Wf Y ⊆ X *)
  apply f_typ; trivial.

  split; intros.

Lemma Wsrec_ex' w X :
  w ∈ X ->
  X ⊆ O ->
  K X ->
  forall w', w' ∈ fsub' w ->
  exists2 y, y ∈ P X w' &
    Wsrec_rel' w' y /\ (forall y', Wsrec_rel' w' y' -> y == y').


Lemma Wsrec_ex' w :
  w ∈ O ->
  forall w', w' ∈ fsub' w ->
  exists2 y, y ∈ P O w' & Wsrec_rel' w' y /\ (forall y', Wsrec_rel' w' y' -> y==y').
intros tyw.
assert (forall X, X ⊆ O -> K X ->
   w ∈ X ->
   forall w', w' ∈ fsub' w ->
   exists2 y, y ∈ P X w' &
     Wsrec_rel' w' y /\ (forall y', Wsrec_rel' w' y' -> y == y')).
2:apply H; auto with *.
apply KW in tyw; trivial.
pattern w; apply W_ind; intros; trivial.
 intros w1 w2 eqw.
 apply fa_morph; intros X.
 apply fa_morph; intros _.
 apply fa_morph; intros _.
 apply impl_morph.
  rewrite eqw; reflexivity.
 intros _.
 apply fa_morph; intros w'.
 rewrite eqw; reflexivity.

 set (Y := fsub (Wsup x f)) in *.
 set (REC := fun w => union (subset (P X w) (Wsrec_rel' w))).
 assert (wsm : ext_fun Y REC).
  intros w1 w2 _ eqw.
  apply union_morph; apply subset_morph.
   rewrite eqw; reflexivity.
  intros y tyy.
  rewrite eqw; reflexivity.
 assert (KY : K Y).
  apply Kfsub.
  apply KW with (X:=X); trivial.

(* assert (YinclX : Wf Y ⊆ X).
(*red; intros.
unfold Y in H6.
rewrite fsub_eq in H6.*)
(*apply Wf_stable0 with (K:=fun Y => Y ⊆ Wdom) in H6.*)
  apply Kstage'; trivial.*)
 assert (YinclX : Y ⊆ X).
  red; intros.
  apply fsub_elim with (3:=H6); trivial.
  apply Ktrans; trivial.
 assert (YinclO : Y ⊆ O).
  transitivity X; trivial.
(*  transitivity (Wf Y); trivial.
  apply Ktrans; trivial.*)
 assert (tyf : f ∈ Π _ ∈ B x, Y).
  rewrite cc_eta_eq with (1:=H0).
  apply cc_prod_intro; intros; auto with *.
   do 2 red; intros; apply cc_app_morph; auto with *.
  apply fsub_intro; auto.
   rewrite W_eqn; apply Wf_intro; trivial.

   intros Z ? ?.
   apply Wf_elim' with (x:=x); trivial.
    intros; apply W_typ.
    apply cc_prod_elim with (1:=H0); trivial.

    transitivity W;[|apply W_typ].
    apply KW; trivial.

 assert (tyw' : w' ∈ Wf Y).
  apply fsub'_elim with (3:=H5); auto. (* Kintro *)
admit.
  apply Wf_intro; trivial.
 assert (tyw'O : w' ∈ O).
  apply fsub'_elim with (3:=H5); auto.

 pose (recf := λ w ∈ Y, REC w).

 assert (tyHrec : forall  x0, x0 ∈ Y ->
    REC x0 ∈ P Y x0 /\ Wsrec_rel' x0 (REC x0) /\
    forall y, Wsrec_rel' x0 y -> REC x0 == y).
  intros x0 tyx0.
  apply fsub_elim' in tyx0; trivial.
  destruct tyx0 as (i,tyi,sbt).
  destruct H1 with (1:=tyi) (X:=Y) (5:=sbt); trivial.
   apply cc_prod_elim with (1:=tyf); trivial.
  destruct H7.
  assert (eqrec : REC x0 == x1).
   unfold REC; rewrite union_subset_singl with (y:=x1)(y':=x1); intros; auto with *.
    apply Pmono with Y; trivial.    

    rewrite <- H8 with (1:=H11).
    rewrite <- H8 with (1:=H12).
    reflexivity.
  rewrite eqrec.
  split; [|split]; trivial.
  intros; rewrite eqrec; auto.
 assert (tyrecf : recf ∈ Π w ∈ Y, P Y w).
  apply cc_prod_intro; intros; auto.
   intros ? ? ? h; rewrite h; reflexivity.
  destruct tyHrec with (1:=H6); trivial.
 exists (F Y recf w').
(*  apply Pmono' with X; trivial.*)
  apply Pmono with (Wf Y ∩ O); trivial.
red; intros.
apply inter2_def in H6; destruct H6.

admit. (* Wf Y ⊆ X *)
  apply f_typ; trivial.

  split; intros.
   apply Wsrec_rel_intro'; intros; trivial.
   unfold recf; rewrite cc_beta_eq; trivial.
   destruct tyHrec with (1:=H6) as (_,(?,_)); trivial.

   apply Wsrec'_rel_elim in H6; auto.
   destruct H6 as (X',(XinclO',(KX',tyw'')),(recf',tyrecf',(eqy,(tyy,?)))).
   rewrite eqy.
   apply Firr; trivial.
   intros.
   unfold recf; rewrite cc_beta_eq; trivial.
   destruct tyHrec with (1:=H7) as (_,(_,?)); auto.
Qed.
*)
(*
Definition WSREC' w := union (subset (P O w) (Wsrec_rel' w)).

Instance WSREC'_morph : morph1 WSREC'.
do 2 red; intros.
apply union_morph; apply subset_morph.
 rewrite H; reflexivity.
red; intros.
rewrite H; reflexivity.
Qed.

Lemma Wsrec_ex2 w :
  w ∈ O ->
  exists2 y, y ∈ P O w & Wsrec_rel' w y /\ (forall y', Wsrec_rel' w y' -> y==y').
intros.
apply Wsrec_ex' with (1:=H); auto with *.
apply fsub'_intro_gen; trivial.
apply KW with (X:=O); trivial.
Qed.

Lemma WSREC_ok' w :
  w ∈ O ->
  Wsrec_rel' w (WSREC' w).
intros.
destruct Wsrec_ex2 with (1:=H).
destruct H1.
unfold WSREC'.
rewrite union_subset_singl with (y:=x)(y':=x); auto with *.
intros.
rewrite <- H2 with (1:=H5).
rewrite <- H2 with (1:=H6).
reflexivity.
Qed.

Lemma WSREC_typ' w :
  w ∈ O -> 
  WSREC' w ∈ P O w.
intros tyw.
destruct Wsrec_ex2 with (1:=tyw) as (y,tyy,(ydef,?)).
unfold WSREC'.
rewrite union_subset_singl with (y:=y)(y':=y); intros; auto with *.
rewrite <- H with (1:=H2).
rewrite <- H with (1:=H3).
reflexivity.
Qed.

Lemma WSREC_eqn' w :
  w ∈ O ->
  WSREC' w == F O (λ w ∈ O, WSREC' w) w.
intros tyw.
assert (Wsrec_rel' w (WSREC' w)).  
 apply WSREC_ok'; trivial.
apply Wsrec'_rel_elim in H; trivial.
destruct H as (X,(XinclW,(Xtrans,tyf')),(recf,tyrecf,(eqf,(tyf,?)))).
rewrite eqf.
apply Firr; auto with *.
 apply cc_prod_intro; intros.
  do 2 red; intros.
  apply WSREC'_morph; trivial.

  do 2 red; intros; apply Pm; auto with *.

  apply WSREC_typ'; trivial.

 intros.
 rewrite cc_beta_eq; auto.
  symmetry.
  apply union_subset_singl with (y':=cc_app recf x); auto with *.
   apply Pmono with X; trivial.
   apply cc_prod_elim with (1:=tyrecf); trivial.

   intros.
   destruct Wsrec_ex2 with (w:=x); auto.
   destruct H7.
   rewrite <- H8 with (1:=H4).
   rewrite <- H8 with (1:=H5).
   reflexivity.

  do 2 red; intros.
  apply WSREC'_morph; trivial.

 revert tyf'; apply Wf_mono; trivial.
Qed.


Lemma WSREC_eqn2' X x f :
  x ∈ A ->
  f ∈ (Π i ∈ B x, X) ->
  Wf X ⊆ O ->
  WSREC' (Wsup x f) == F O (λ w ∈ O, WSREC' w) (Wsup x f).
intros tya tyf inclO.
apply WSREC_eqn'.
apply inclO.
apply Wf_intro; auto.
Qed.

End TransitiveRecursor.
*)

(* Attempt 2: P depends on the "stage" set

Section TransitiveRecursor.

Variable O : set.
Hypothesis OinclW : O ⊆ W.
Hypothesis Otrans : O ⊆ Wf O.

Lemma stable_pair K F X Y :
  Proper (eq_set ==> iff) K ->
  morph1 F ->
  stable_class K F ->
  K X ->
  K Y ->
  F X ∩ F Y ⊆ F (X ∩ Y).
intros Km Fm stb kx ky.
unfold inter2.
setoid_replace (pair (F X) (F Y)) with (replf (pair X Y) F).
 apply stb; intros.
 apply pair_elim in H; destruct H; rewrite H; trivial.

 apply eq_set_ax; intros z.
 rewrite pair_ax.
 rewrite replf_ax; auto.
 split; intros.
  destruct H; [exists X|exists Y]; auto.

  destruct H.
  apply pair_elim in H; destruct H; rewrite H in H0; auto.
Qed.

Lemma inter_trans X :
  X ⊆ W ->
  X ⊆ Wf X ->
  X ∩ O ⊆ Wf (X ∩ O).
intros.
transitivity (Wf X ∩ Wf O).
apply inter2_incl.
 transitivity X; trivial.
 apply inter2_incl1.

 transitivity O; trivial.
 apply inter2_incl2.

 apply stable_pair with (K:=fun X => X ⊆ Wdom); auto with *.
  do 2 red; intros.
  rewrite H1; reflexivity.

  apply Wf_stable0; auto.

  transitivity W; trivial.
  apply W_typ.

  transitivity W; trivial.
  apply W_typ.
Qed.



Variable P : set -> set -> set.
Hypothesis Pm : morph2 P.

Variable F : set -> set -> set -> set.
Hypothesis Fm : Proper (eq_set==>eq_set==>eq_set==>eq_set) F.
Hypothesis f_typ : forall X x recf,
  X ⊆ O ->
  X ⊆ Wf X -> (* allow indirect subterms *)
  x ∈ Wf X ->
  x ∈ O ->
  recf ∈ (Π w ∈ X, P X w) ->
  F X recf x ∈ P (Wf X) x.
Hypothesis Firr : forall X X' recf recf',
  X ⊆ O ->
  X ⊆ Wf X -> (* allow indirect subterms *)
  X' ⊆ O ->
  X' ⊆ Wf X' -> (* allow indirect subterms *)
  recf ∈ (Π w ∈ X, P X w) ->
  recf' ∈ (Π w ∈ X', P X' w) ->
  (forall x, x ∈ X -> x ∈ X' -> cc_app recf x == cc_app recf' x) ->
  forall x, x ∈ Wf X -> x ∈ Wf X' -> x ∈ O -> F X recf x == F X' recf' x.

Definition Wsrec_rel' w y :=
  forall Q, Proper (eq_set==>eq_set==>iff) Q ->
  (forall X x recf,
   X ⊆ O ->
   X ⊆ Wf X ->
   x ∈ Wf X ->
   x ∈ O ->
   recf ∈ (Π w ∈ X, P X w) ->
   (forall w, w ∈ X -> Q w (cc_app recf w)) -> 
   Q x (F X recf x)) -> 
  Q w y.

Instance Wsrec_rel_morph' : Proper (eq_set==>eq_set==>iff) Wsrec_rel'.
do 3 red; intros.
apply fa_morph; intros Q.
apply fa_morph; intros Qm.
apply fa_morph; intros.
apply Qm; trivial.
Qed.

Lemma Wsrec_rel_intro' X x recf :
  X ⊆ O ->
  X ⊆ Wf X ->
  x ∈ Wf X ->
  x ∈ O ->
  recf ∈ (Π w ∈ X, P X w) ->
  (forall w, w ∈ X -> Wsrec_rel' w (cc_app recf w)) -> 
  Wsrec_rel' x (F X recf x).
red; intros.
apply H6; trivial.
intros.
apply H4; trivial.
Qed.

Lemma Wsrec'_rel_elim w y :
  w ∈ O ->
  Wsrec_rel' w y ->
  exists2 X, X ⊆ O /\ X ⊆ Wf X /\ w ∈ Wf X &
  exists2 recf, recf ∈ (Π w ∈ X, P X w) &
    y == F X recf w /\
    (forall w, w ∈ X -> Wsrec_rel' w (cc_app recf w)).
intros tyw inv.
apply proj2 with (A:=Wsrec_rel' w y).
pattern w, y.
apply inv; intros.
 do 3 red; intros.
 apply and_iff_morphism.
  rewrite H,H0; reflexivity.
 apply ex2_morph; intros X; auto with *.
  rewrite H; reflexivity.
 apply ex2_morph; intros recf'; auto with *.
  rewrite H,H0; reflexivity.

 split.
  apply Wsrec_rel_intro'; trivial.
  intros.
  apply H4; trivial.

  exists X; auto.
  exists recf; trivial.
  split; auto with *.
  intros.
  apply H4.
  trivial.
Qed.

(*
Lemma Wsrec'_rel_elim' x f y :
  x ∈ A ->
  f ∈ (Π i ∈ B x, O) ->
  Wsrec_rel' (Wsup x f) y ->
  exists2 X, X ⊆ O /\ X ⊆ Wf X /\ f ∈ (Π i ∈ B x, X) &
  exists2 recf, recf ∈ (Π w ∈ X, P X w) &
    y == F X recf (Wsup x f) /\
   (forall w, w ∈ X -> Wsrec_rel' w (cc_app recf w)).
intros.
assert (tyw : Wsup x f ∈ Wf O).
 (*rewrite W_eqn;*) apply Wf_intro; trivial.
apply Wsrec'_rel_elim in H1; trivial.
 revert H0; appl
destruct H1 as (X,(XinclW,(Xtrans,tyw')),(recf,tyrecf,(eqy,?))).
apply Wf_elim in tyw'; destruct tyw' as (x',tyx',(f',tyf',eqw)).
apply Wsup_inj in eqw; trivial.
 destruct eqw as (eqx,eqf).
 exists X. 
  split; trivial.
  split; trivial.
  rewrite cc_eta_eq with (1:=H0).
  apply cc_prod_intro; intros; auto with *.
   do 2 red; intros; apply cc_app_morph; auto with *.
  rewrite eqf; trivial.
  apply cc_prod_elim with (1:=tyf').
  rewrite <-eqx; trivial.
 exists recf; auto.

 intros.
 apply W_typ.
 apply cc_prod_elim with (1:=H0); trivial.

 intros.
 apply W_typ.
 apply XinclW.
 apply cc_prod_elim with (1:=tyf'); trivial.
Qed.
*)

Lemma Wsrec_ex' w :
  w ∈ O ->
  forall w', w==w' \/ w' ∈ fsub w ->
  exists2 y, y ∈ P O w' & Wsrec_rel' w' y /\ (forall y', Wsrec_rel' w' y' -> y==y').
intros tyw.
assert (forall X, X ⊆ O -> X ⊆ Wf X ->
   w ∈ X ->
   forall w' : set,
   w == w' \/ w' ∈ fsub w ->
   exists2 y : set,
     y ∈ P X w' &
     Wsrec_rel' w' y /\ (forall y' : set, Wsrec_rel' w' y' -> y == y')).
2:apply H; auto with *.
apply OinclW in tyw.
pattern w; apply W_ind; intros; trivial.
 admit. (* OK*)

 set (Y := fsub (Wsup x f)) in *.
(*assert (YinclX : Y ⊆ X).
red; intros.
apply fsub_elim' in H6.


 assert (XinclW : Y ⊆ O).
  red; intros.
apply Wf_elim in H6.
destruct H6 as (x',tyx',(f',tyf',eqz)).
destruct H5
admit. (*  apply subset_elim1 in H3; trivial.*)
*)
 assert (YinclX : Y ⊆ X).
red; intros.
apply subset_elim2 in H6.
destruct H6 as (z',eqz,Hz).
rewrite eqz; apply Hz; trivial.
 transitivity O; trivial.
 apply H3; trivial.
 assert (XinclW : Y ⊆ O).
  transitivity X; trivial.
 assert (Xtrans : Y ⊆ Wf Y).
  apply fsub_trans.
  rewrite W_eqn; apply Wf_intro; trivial.

 pose (recf := λ w ∈ Y, union (subset (P X w) (Wsrec_rel' w))).
(* pose (recf := λ w ∈ Y, union (subset (P Y w) (Wsrec_rel' w))).*)
 assert (tyf : f ∈ Π _ ∈ B x, Y).
  rewrite cc_eta_eq with (1:=H0).
  apply cc_prod_intro; intros; auto with *.
   do 2 red; intros; apply cc_app_morph; auto with *.
  apply fsub_intro; auto.
 assert (tyrecf : recf ∈ Π w ∈ Y, P Y w).
  apply cc_prod_intro; intros.
admit. (*   do 2 red; intros.
   apply union_morph; apply subset_morph.
    rewrite H4; reflexivity.
   red; intros.
   rewrite H4; reflexivity.*)

admit. (*   intros ? ? ? h; rewrite h; reflexivity.*)

   apply fsub_elim' in H6; trivial.
   destruct H6 as (i,tyi,sbt).
   destruct H1 with (1:=tyi) (X:=Y) (5:=sbt); trivial.
apply cc_prod_elim with (1:=tyf); trivial.
(*    apply XinclW; apply cc_prod_elim with (1:=tyf); trivial.*)
   destruct H7.
   rewrite union_subset_singl with (y:=x1)(y':=x1); auto with *.
admit. (* Y ⊆ X *)
   intros.
   rewrite <- H8 with (1:=H11).
   rewrite <- H8 with (1:=H12).
   reflexivity.
 assert (tyw' : w' ∈ Wf Y).
  destruct H5 as [eqw|eqw].
   rewrite <- eqw; apply Wf_intro; trivial.

   apply Xtrans; trivial.
 destruct H5 as [eqw|eqw].
  exists (F Y recf w').
   assert (P (Wf Y) w' ⊆ P X w').
admit. (* Wf Y ⊆ X ??? *)
   apply H5.
   apply f_typ; trivial.
admit. (*   transitivity (Wf Y); trivial.*)
  split; intros.
  apply Wsrec_rel_intro'; intros; trivial.
  assert (tyw0' := H5).
  apply fsub_elim' in H5; trivial.
  destruct H5 as (i,tyi,eqz).
  destruct H1 with (1:=tyi) (X:=Y) (5:=eqz); trivial.
transitivity (Wf Y); trivial.
apply cc_prod_elim with (1:=tyf); trivial.
  destruct H6.
  unfold recf; rewrite cc_beta_eq; trivial.
   rewrite union_subset_singl with (y:=x0)(y':=x0); intros; auto with *.
admit.
   rewrite <- H7 with (1:=H10).
   rewrite <- H7 with (1:=H11).
   reflexivity.
admit.

  apply Wsrec'_rel_elim in H5; auto.
  destruct H5 as (X',(X'inclW,(X'trans,tyf')),(recf',tyrecf',(eqy,?))).
  rewrite eqy.
  apply Firr; trivial.
transitivity (Wf Y); trivial.
transitivity (Wf X'); trivial.
   intros.
(*   assert (x0 ∈ X').
    apply fsub_elim with (y:=w'); trivial.
    rewrite <- H2; trivial.*)
   unfold recf; rewrite cc_beta_eq; trivial.
    apply union_subset_singl with (y':=cc_app recf' x0); intros; auto with *.
apply cc_prod_elim with (1:=tyrecf'); trivial.

assert (X' ⊆ Y).
 red; intros.

(*     apply cc_prod_elim with (1:=tyrecf'); trivial.*) admit.

     assert (tyx0 := H6).
     apply fsub_elim' in H6; trivial.
     destruct H6 as (i,tyi,eqx0).
     destruct H1 with (1:=tyi) (X:=Y) (5:=eqx0); intros; trivial.
transitivity (Wf Y); trivial.
destruct eqx0.
 rewrite H6; trivial.
apply cc_prod_elim with (1:=tyf); trivial.

     destruct H12.
     rewrite <- H13 with (1:=H10).
     rewrite <- H13 with (1:=H11).
     reflexivity.

admit. (*
    do 2 red; intros.
    apply union_morph; apply subset_morph.
     rewrite H7; reflexivity.
    red; intros.
    rewrite H7; reflexivity.

   rewrite W_eqn; trivial.
   revert tyw'; apply Wf_mono; trivial.
*)

  apply fsub_elim' in eqw; trivial.
  destruct eqw as (i,tyi,sbt).
  apply H1 with (1:=tyi) (5:=sbt); trivial.

apply H3 in H4.
apply Wf_elim in H4; destruct H4 as (x',tyx',(f',tyf',eqw)).
apply Wsup_inj in eqw; trivial.
destruct eqw as (eqx,eqf).
rewrite eqf; trivial.
apply cc_prod_elim with (1:=tyf'); trivial.
rewrite <- eqx; trivial.

intros.
apply W_typ.
apply OinclW.
apply XinclW.
apply Xtrans.
apply cc_prod_elim with (1:=tyf); trivial.

intros.
apply W_typ.
apply OinclW.
apply H2.
apply cc_prod_elim with (1:=tyf'); trivial.
Qed.

transitivity W;[|apply W_typ].
assert (Y ⊆ X).
 red; intros.
 apply

apply cc_prod_elim with (1:=tyf); trivial.





intros tyw.
generalize tyw; apply OinclW in tyw.
pattern w; apply W_ind; intros; trivial.
 do 2 red; intros.
 apply impl_morph; intros.
  rewrite H; reflexivity.
 apply fa_morph; intros w'.
 apply impl_morph; intros.
  rewrite H; reflexivity.
 reflexivity.

 set (X := fsub (Wsup x f)) in *.
 assert (XinclW : X ⊆ O).
  red; intros.
admit. (*  apply subset_elim1 in H3; trivial.*)
 assert (Xtrans : X ⊆ Wf X).
  apply fsub_trans.
  rewrite W_eqn; apply Wf_intro; trivial.
 pose (recf := λ w ∈ X, union (subset (P X w) (Wsrec_rel' w))).
 assert (tyf : f ∈ Π _ ∈ B x, X).
  rewrite cc_eta_eq with (1:=H0).
  apply cc_prod_intro; intros; auto with *.
   do 2 red; intros; apply cc_app_morph; auto with *.
  apply fsub_intro; auto.
 assert (tyrecf : recf ∈ Π w ∈ X, P X w).
admit.
(*  apply cc_prod_intro; intros.
   do 2 red; intros.
   apply union_morph; apply subset_morph.
    rewrite H4; reflexivity.
   red; intros.
   rewrite H4; reflexivity.

   intros ? ? ? h; rewrite h; reflexivity.

   apply fsub_elim' in H3; trivial.
   destruct H3 as (i,tyi,sbt).
   destruct H1 with (1:=tyi) (3:=sbt).
    apply XinclW; apply cc_prod_elim with (1:=tyf); trivial.
   destruct H4.
   rewrite union_subset_singl with (y:=x1)(y':=x1); auto with *.
   intros.
   rewrite <- H5 with (1:=H8).
   rewrite <- H5 with (1:=H9).
   reflexivity.
*)
 assert (tyw' : w' ∈ Wf X).
  destruct H2 as [eqw|eqw].
   rewrite <- eqw; apply Wf_intro; trivial.

   apply Xtrans.
   eapply fsub_elim with (y:=Wsup x f); trivial.
transitivity O; trivial.
   apply Wf_intro; trivial.

 destruct H2.
  exists (F X recf w').
admit. (* P mono *)
(*   apply f_typ; trivial.*)
  split; intros.
  apply Wsrec_rel_intro' with (X:=X); intros; trivial.
  assert (tyw0' := H3).
  apply fsub_elim' in H3; trivial.
  destruct H3 as (i,tyi,eqz).
  destruct H1 with (1:=tyi) (3:=eqz).
apply XinclW.
apply cc_prod_elim with (1:=tyf); trivial.
  destruct H4.
  unfold recf; rewrite cc_beta_eq; trivial.
   rewrite union_subset_singl with (y:=x0)(y':=x0); intros; auto with *.
   rewrite <- H5 with (1:=H8).
   rewrite <- H5 with (1:=H9).
   reflexivity.

   do 2 red; intros.
   apply union_morph; apply subset_morph.
    rewrite H7; reflexivity.
   red; intros.
   rewrite H7; reflexivity.

  apply Wsrec'_rel_elim in H3; trivial.
   destruct H3 as (X',(X'inclW,(X'trans,tyf')),(recf',tyrecf',(eqy,?))).
   rewrite eqy.
   apply Firr; trivial.
   intros.
(*   assert (x0 ∈ X').
    apply fsub_elim with (y:=w'); trivial.
    rewrite <- H2; trivial.*)
   unfold recf; rewrite cc_beta_eq; trivial.
    apply union_subset_singl with (y':=cc_app recf' x0); intros; auto with *.
     apply cc_prod_elim with (1:=tyrecf'); trivial.

     assert (tyx0 := H4).
     apply fsub_elim' in H4; trivial.
     destruct H4 as (i,tyi,eqx0).
     destruct H1 with (1:=tyi) (2:=eqx0); intros.
     destruct H10.
     rewrite <- H11 with (1:=H8).
     rewrite <- H11 with (1:=H9).
     reflexivity.

    do 2 red; intros.
    apply union_morph; apply subset_morph.
     rewrite H7; reflexivity.
    red; intros.
    rewrite H7; reflexivity.

   rewrite W_eqn; trivial.
   revert tyw'; apply Wf_mono; trivial.

  apply fsub_elim' in H2; trivial.
  destruct H2 as (i,tyi,sbt).
  apply H1 with (1:=tyi) (2:=sbt).
Qed.


*)
End TransitiveRecursor.

(*********)
(* version OK (previous) 
Section TransitiveRecursor.

Variable P : set -> set.
Hypothesis Pm : morph1 P.

Variable F : set -> set -> set -> set.
Hypothesis Fm : Proper (eq_set==>eq_set==>eq_set==>eq_set) F.
Hypothesis f_typ : forall X x recf,
  X ⊆ W ->
  X ⊆ Wf X -> (* allow indirect subterms *)
  x ∈ Wf X ->
  recf ∈ (Π w ∈ X, P w) ->
  F X recf x ∈ P x.
Hypothesis Firr : forall X X' recf recf',
  X ⊆ W ->
  X ⊆ Wf X -> (* allow indirect subterms *)
  X' ⊆ W ->
  X' ⊆ Wf X' -> (* allow indirect subterms *)
  recf ∈ (Π w ∈ X, P w) ->
  recf' ∈ (Π w ∈ X', P w) ->
  (forall x, x ∈ X -> x ∈ X' -> cc_app recf x == cc_app recf' x) ->
  forall x, x ∈ Wf X -> x ∈ Wf X' -> F X recf x == F X' recf' x.

Definition Wsrec_rel' w y :=
  forall Q, Proper (eq_set==>eq_set==>iff) Q ->
  (forall X x recf,
   X ⊆ W ->
   X ⊆ Wf X ->
   x ∈ Wf X ->
   recf ∈ (Π w ∈ X, P w) ->
   (forall w, w ∈ X -> Q w (cc_app recf w)) -> 
   Q x (F X recf x)) -> 
  Q w y.

Instance Wsrec_rel_morph' : Proper (eq_set==>eq_set==>iff) Wsrec_rel'.
do 3 red; intros.
apply fa_morph; intros Q.
apply fa_morph; intros Qm.
apply fa_morph; intros.
apply Qm; trivial.
Qed.

Lemma Wsrec_rel_intro' X x recf :
  X ⊆ W ->
  X ⊆ Wf X ->
  x ∈ Wf X ->
  recf ∈ (Π w ∈ X, P w) ->
  (forall w, w ∈ X -> Wsrec_rel' w (cc_app recf w)) -> 
  Wsrec_rel' x (F X recf x).
red; intros.
apply H5; trivial.
intros.
apply H3; trivial.
Qed.

Lemma Wsrec'_rel_elim w y :
  w ∈ W ->
  Wsrec_rel' w y ->
  exists2 X, X ⊆ W /\ X ⊆ Wf X /\ w ∈ Wf X &
  exists2 recf, recf ∈ (Π w ∈ X, P w) &
    y == F X recf w /\
    (forall w, w ∈ X -> Wsrec_rel' w (cc_app recf w)).
intros tyw inv.
apply proj2 with (A:=Wsrec_rel' w y).
pattern w, y.
apply inv; intros.
 do 3 red; intros.
 apply and_iff_morphism.
  rewrite H,H0; reflexivity.
 apply ex2_morph; intros X; auto with *.
  rewrite H; reflexivity.
 apply ex2_morph; intros recf'; auto with *.
  rewrite H,H0; reflexivity.

 split.
  apply Wsrec_rel_intro'; trivial.
  intros.
  apply H3; trivial.

  exists X; auto.
  exists recf; trivial.
  split; auto with *.
  intros.
  apply H3.
  trivial.
Qed.


Lemma Wsrec'_rel_elim' x f y :
  x ∈ A ->
  f ∈ (Π i ∈ B x, W) ->
  Wsrec_rel' (Wsup x f) y ->
  exists2 X, X ⊆ W /\ X ⊆ Wf X /\ f ∈ (Π i ∈ B x, X) &
  exists2 recf, recf ∈ (Π w ∈ X, P w) &
    y == F X recf (Wsup x f) /\
   (forall w, w ∈ X -> Wsrec_rel' w (cc_app recf w)).
intros.
assert (tyw : Wsup x f ∈ W).
 rewrite W_eqn; apply Wf_intro; trivial.
apply Wsrec'_rel_elim in H1; trivial.
destruct H1 as (X,(XinclW,(Xtrans,tyw')),(recf,tyrecf,(eqy,?))).
apply Wf_elim in tyw'; destruct tyw' as (x',tyx',(f',tyf',eqw)).
apply Wsup_inj in eqw; trivial.
 destruct eqw as (eqx,eqf).
 exists X. 
  split; trivial.
  split; trivial.
  rewrite cc_eta_eq with (1:=H0).
  apply cc_prod_intro; intros; auto with *.
   do 2 red; intros; apply cc_app_morph; auto with *.
  rewrite eqf; trivial.
  apply cc_prod_elim with (1:=tyf').
  rewrite <-eqx; trivial.
 exists recf; auto.

 intros.
 apply W_typ.
 apply cc_prod_elim with (1:=H0); trivial.

 intros.
 apply W_typ.
 apply XinclW.
 apply cc_prod_elim with (1:=tyf'); trivial.
Qed.

Lemma fsub_trans w :
  w ∈ W ->
  fsub w ⊆ Wf (fsub w).
Admitted.

Lemma Wsrec_ex' w :
  w ∈ W ->
  forall w', w==w' \/ w' ∈ fsub w ->
  exists2 y, y ∈ P w' & Wsrec_rel' w' y /\ (forall y', Wsrec_rel' w' y' -> y==y').
intros tyw.
pattern w; apply W_ind; intros; trivial.
 do 2 red; intros.
 apply fa_morph; intros w'.
 apply impl_morph; intros.
  rewrite H; reflexivity.
 reflexivity.

 set (X := fsub (Wsup x f)) in *.
assert (tywW : Wsup x f ∈ W).
rewrite W_eqn; apply Wf_intro; trivial.

 assert (XinclW : X ⊆ W).
apply KW.
apply Kfsub; trivial.
(*  red; intros.
  apply subset_elim1 in H3; trivial.*)
 assert (Xtrans : X ⊆ Wf X).
red; intros.
apply fsub_elim with (3:=H3).
apply Kintro; trivial.
apply Kfsub; trivial.
apply Wf_intro; trivial.
rewrite cc_eta_eq with (1:=H0).
apply cc_prod_intro; intros; auto with *.
 do 2 red; intros; apply cc_app_morph; auto with *.
apply Ktrans.
 apply Kfsub; trivial. 
apply fsub_intro; auto.
intros.
eapply Wf_elim' with (4:=H6); auto.
 intros; apply W_typ.
 apply cc_prod_elim with (1:=H0); trivial.
transitivity W;[|apply W_typ].
apply KW; trivial.
(*
  apply fsub_trans.
  rewrite W_eqn; apply Wf_intro; trivial.*)
 pose (recf := λ w ∈ X, union (subset (P w) (Wsrec_rel' w))).
 assert (tyf : f ∈ Π _ ∈ B x, X).
  rewrite cc_eta_eq with (1:=H0).
  apply cc_prod_intro; intros; auto with *.
   do 2 red; intros; apply cc_app_morph; auto with *.
  apply fsub_intro; auto.
intros.
eapply Wf_elim' with (4:=H5); auto.
 intros; apply W_typ.
 apply cc_prod_elim with (1:=H0); trivial.
transitivity W;[|apply W_typ].
apply KW; trivial.
 assert (tyrecf : recf ∈ Π w ∈ X, P w).
  apply cc_prod_intro; intros.
   do 2 red; intros.
   apply union_morph; apply subset_morph.
    rewrite H4; reflexivity.
   red; intros.
   rewrite H4; reflexivity.

   intros ? ? ? h; rewrite h; reflexivity.

   apply fsub_elim' in H3; trivial.
   destruct H3 as (i,tyi,sbt).
   destruct H1 with (1:=tyi) (w':=x0)(*(2:=sbt)*).
admit.
   destruct H4.
   rewrite union_subset_singl with (y:=x1)(y':=x1); auto with *.
   intros.
   rewrite <- H5 with (1:=H8).
   rewrite <- H5 with (1:=H9).
   reflexivity.

 assert (tyw' : w' ∈ Wf X).
  destruct H2 as [eqw|eqw].
   rewrite <- eqw; apply Wf_intro; trivial.

   apply Xtrans.
   eapply fsub_elim with (y:=Wsup x f); trivial.
apply Kfsub.
rewrite W_eqn; apply Wf_intro; trivial.
   apply Wf_intro; trivial.

 destruct H2.
  exists (F X recf w').
   apply f_typ; trivial.
  split; intros.
  apply Wsrec_rel_intro' with (X:=X); intros; trivial.
  assert (tyw0 := H3).
  apply fsub_elim' in H3; trivial.
  destruct H3 as (i,tyi,eqz).
  destruct H1 with (1:=tyi) (w':=w0)(*(2:=eqz)*).
admit.
  destruct H4.
  unfold recf; rewrite cc_beta_eq; trivial.
   rewrite union_subset_singl with (y:=x0)(y':=x0); intros; auto with *.
   rewrite <- H5 with (1:=H8).
   rewrite <- H5 with (1:=H9).
   reflexivity.

   do 2 red; intros.
   apply union_morph; apply subset_morph.
    rewrite H7; reflexivity.
   red; intros.
   rewrite H7; reflexivity.

  apply Wsrec'_rel_elim in H3; trivial.
   destruct H3 as (X',(X'inclW,(X'trans,tyf')),(recf',tyrecf',(eqy,?))).
   rewrite eqy.
   apply Firr; trivial.
   intros.
(*   assert (x0 ∈ X').
    apply fsub_elim with (y:=w'); trivial.
    rewrite <- H2; trivial.*)
   unfold recf; rewrite cc_beta_eq; trivial.
    apply union_subset_singl with (y':=cc_app recf' x0); intros; auto with *.
     apply cc_prod_elim with (1:=tyrecf'); trivial.

     assert (tyx0 := H4).
     apply fsub_elim' in H4; trivial.
     destruct H4 as (i,tyi,eqx0).
     destruct H1 with (1:=tyi) (w':=x0)(*(2:=eqx0)*); intros.
admit.
     destruct H10.
     rewrite <- H11 with (1:=H8).
     rewrite <- H11 with (1:=H9).
     reflexivity.

    do 2 red; intros.
    apply union_morph; apply subset_morph.
     rewrite H7; reflexivity.
    red; intros.
    rewrite H7; reflexivity.

   rewrite W_eqn; trivial.
   revert tyw'; apply Wf_mono; trivial.

  apply fsub_elim' in H2; trivial.
  destruct H2 as (i,tyi,sbt).
  apply H1 with (1:=tyi) (2:=sbt).
Qed.

Definition WSREC' w := union (subset (P w) (Wsrec_rel' w)).

Instance WSREC'_morph : morph1 WSREC'.
do 2 red; intros.
apply union_morph; apply subset_morph.
 rewrite H; reflexivity.
red; intros.
rewrite H; reflexivity.
Qed.

Lemma Wsrec_ex2 w :
  w ∈ W ->
  exists2 y, y ∈ P w & Wsrec_rel' w y /\ (forall y', Wsrec_rel' w y' -> y==y').
intros.
apply Wsrec_ex' with (1:=H); auto with *.
Qed.

Lemma WSREC_ok' w :
  w ∈ W ->
  Wsrec_rel' w (WSREC' w).
intros.
destruct Wsrec_ex2 with (1:=H).
destruct H1.
unfold WSREC'.
rewrite union_subset_singl with (y:=x)(y':=x); auto with *.
intros.
rewrite <- H2 with (1:=H5).
rewrite <- H2 with (1:=H6).
reflexivity.
Qed.

Lemma WSREC_typ' w :
  w ∈ W -> 
  WSREC' w ∈ P w.
intros tyw.
destruct Wsrec_ex2 with (1:=tyw) as (y,tyy,(ydef,?)).
unfold WSREC'.
rewrite union_subset_singl with (y:=y)(y':=y); intros; auto with *.
rewrite <- H with (1:=H2).
rewrite <- H with (1:=H3).
reflexivity.
Qed.

Lemma WSREC_eqn' w :
  w ∈ W ->
  WSREC' w == F W (λ w ∈ W, WSREC' w) w.
intros tyw.
assert (Wsrec_rel' w (WSREC' w)).  
 apply WSREC_ok'; trivial.
apply Wsrec'_rel_elim in H; trivial.
destruct H as (X,(XinclW,(Xtrans,tyf')),(recf,tyrecf,(eqf,?))).
rewrite eqf.
apply Firr; auto with *.
 rewrite <- W_eqn; reflexivity.

 apply cc_prod_intro; intros.
  do 2 red; intros.
  apply WSREC'_morph; trivial.

  do 2 red; intros; apply Pm; trivial.

  apply WSREC_typ'; trivial.

 intros.
 rewrite cc_beta_eq; auto.
  symmetry.
  apply union_subset_singl with (y':=cc_app recf x); auto with *.
   apply cc_prod_elim with (1:=tyrecf); trivial.

   intros.
   destruct Wsrec_ex2 with (w:=x); auto.
   destruct H7.
   rewrite <- H8 with (1:=H4).
   rewrite <- H8 with (1:=H5).
   reflexivity.

  do 2 red; intros.
  apply WSREC'_morph; trivial.

 rewrite <- W_eqn; trivial.
Qed.


Lemma WSREC_eqn2' x f :
  x ∈ A ->
  f ∈ (Π i ∈ B x, W) ->
  WSREC' (Wsup x f) == F W (λ w ∈ W, WSREC' w) (Wsup x f).
intros tya tyf.
apply WSREC_eqn'.
rewrite W_eqn; apply Wf_intro; auto.
Qed.

End TransitiveRecursor.
*)
 (** * Universe facts: when A and B belong to a given (infinite) universe, then so does W(A,B). *)

Section W_Univ.

(* Universe facts *)
  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : ZFord.omega ∈ U.  

  Hypothesis aU : A ∈ U.
  Hypothesis bU : forall a, a ∈ A -> B a ∈ U.

  Lemma G_Wdom : Wdom ∈ U.
unfold Wdom.
apply G_rel; trivial.
apply G_List; trivial.
apply G_sup; trivial.
apply morph_is_ext; trivial.
Qed.

  Lemma G_W' : W ∈ U.
apply G_incl with Wdom; trivial.
 apply G_Wdom.

 apply W_typ.
Qed.

End W_Univ.

End W_theory.

Instance Wf_morph_gen :
  Proper (eq_set==>(eq_set==>eq_set)==>eq_set==>eq_set) Wf.
do 4 red; intros.
unfold Wf.
apply sup_morph; trivial.
red; intros.
apply replf_morph_raw.
 apply cc_prod_ext; auto with *.
 red; intros; trivial.

 red; intros.
 apply Wsup_morph; trivial.
Qed.

Lemma Wf_ext A A' B B' X X' :
  A == A' ->
  eq_fun A B B' ->
  X == X' ->
  Wf A B X == Wf A' B' X'.
intros; unfold Wf.
apply sup_morph; auto with *.
red; intros.
apply replf_morph_raw.
 apply cc_prod_ext; auto with *.

 red; trivial.

 red; intros.
 apply Wsup_morph; trivial.
Qed.


Lemma Wdom_ext A A' B B' :
  A == A' ->
  eq_fun A B B' ->
  Wdom A B == Wdom A' B'.
intros; unfold Wdom.
apply rel_morph; trivial.
apply ZFlist.List_morph.
apply sup_morph; auto with *.
Qed.
 

Instance Wdom_morph : Proper (eq_set==>(eq_set==>eq_set)==>eq_set) Wdom.
do 3 red; intros.
apply Wdom_ext; trivial.
red; intros; apply H0; trivial.
Qed.

Lemma Wcase_ext A A' B B' X X' h h' c c' :
  morph1 B ->
  morph1 B' ->
  X ⊆ W A B ->
  X' ⊆ W A' B' ->
  (forall x x' f f', x ∈ A -> x' ∈ A' -> x == x' ->
   f ∈ (Π _ ∈ B x, X) -> f' ∈ (Π _ ∈ B' x', X') ->
   f == f' -> h x f == h' x' f') ->
  c ∈ Wf A B X ->
  c' ∈ Wf A' B' X' ->
  c == c' ->
  Wcase h c == Wcase h' c'.
unfold Wcase; intros.
apply H3.
 apply Wfst_typ_gen with (B:=B) (X:=X); trivial.
 apply Wfst_typ_gen with (B:=B') (X:=X'); trivial.
 apply Wfst_morph; trivial.
 apply Wsnd_fun_typ_gen with (A:=A); trivial.
  transitivity (W A B);[trivial|apply W_typ; trivial].
 apply Wsnd_fun_typ_gen with (A:=A'); trivial.
  transitivity (W A' B');[trivial|apply W_typ; trivial].
 apply Wsnd_fun_morph; trivial.
Qed.

Instance Wcase_morph_gen :
  Proper ((eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) Wcase.
do 3 red; intros.
unfold Wcase.
apply H.
 apply Wfst_morph; trivial.

 apply Wsnd_fun_morph; trivial.
Qed.

Lemma W_ext A A' B B' :
  A == A' ->
  eq_fun A B B' ->
  W A B == W A' B'.
unfold W; intros.
apply FIX_morph_gen.
 apply incl_set_morph.

 apply inter_morph.

 apply Wdom_ext; trivial.

 apply power_morph.
 apply Wdom_ext; trivial.

 red; intros.
 apply Wf_ext; trivial.
Qed.

Instance W_morph : Proper (eq_set==>(eq_set==>eq_set)==>eq_set) W.
do 3 red; intros.
unfold W.
 unfold FIX.
apply inter_morph.
unfold M'.
apply subset_morph.
 apply subset_morph.
  apply power_morph.
  apply Wdom_morph; trivial.
 red; intros.
 apply incl_set_morph; auto with *.
 apply Wdom_morph; auto with *.
red; intros.
unfold post_fix.
apply incl_set_morph; auto with *.
apply Wf_morph_gen; auto with *.
Qed.

Instance WREC_morph_gen :
  Proper (eq_set==>(eq_set==>eq_set)==>(eq_set==>eq_set)==>(eq_set==>eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) WREC.
do 6 red; intros.
unfold WREC.
apply union_morph.
apply subset_morph.
 auto.
red; intros.
unfold Wrec_rel.
apply fa_morph; intros Q.
apply fa_morph; intros Qm.
apply impl_morph; intros.
 apply fa_morph; intros.
 apply fa_morph; intros.
 apply fa_morph; intros.
 apply impl_morph; intros.
  rewrite H; reflexivity.
 apply impl_morph; intros.
  apply in_set_morph; auto with *.
  apply cc_prod_morph; auto with *.
  red; intros.
  apply W_morph; trivial.
 apply impl_morph; intros.
  apply in_set_morph; auto with *.
  apply cc_prod_morph; auto with *.
  red; intros.
  apply H1.
  rewrite H7; reflexivity.
 apply impl_morph; intros.
  apply fa_morph; intros.
  apply impl_morph; intros.
   apply in_set_morph; auto with *.
  reflexivity.
 apply Qm; auto with *.
 apply H2; auto with *.

 apply Qm; auto with *.
Qed.

Instance WSREC_morph_gen :
  Proper (eq_set==>(eq_set==>eq_set)==>(eq_set==>eq_set)==>(eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) WSREC.
do 6 red; intros.
unfold WSREC.
apply union_morph.
apply subset_morph.
 auto.
red; intros.
unfold Wsrec_rel.
apply fa_morph; intros Q.
apply fa_morph; intros Qm.
apply impl_morph; intros.
 apply fa_morph; intros X.
 apply fa_morph; intros w.
 apply fa_morph; intros recf.
 apply impl_morph; intros.
  apply incl_set_morph; auto with *.
  apply W_morph; trivial.
 apply impl_morph; intros.
  rewrite (Wf_morph_gen _ _ H _ _ H0 _ _ (reflexivity X)); reflexivity.
 apply impl_morph; intros.
  apply in_set_morph; auto with *.
  apply cc_prod_morph; auto with *.
 apply impl_morph; intros.
  reflexivity.
 apply Qm; auto with *.
 apply H2; auto with *.

 apply Qm; auto with *.
Qed.

Instance WSREC'_morph_gen :
  Proper (eq_set==>(eq_set==>eq_set)==>(eq_set==>iff)==>eq_set==>(eq_set==>eq_set==>eq_set)==>(eq_set==>eq_set==>eq_set==>eq_set)==>eq_set==>eq_set)
  WSREC'.
do 8 red; intros.
unfold WSREC'.
apply uchoice_morph_raw.
red; intros.
unfold Wsrec_rel'.
apply fa_morph; intros Q.
apply fa_morph; intros Qm.
apply impl_morph; intros.
 apply fa_morph; intros X.
 apply fa_morph; intros w.
 apply fa_morph; intros recf.
 apply impl_morph; intros.
  apply incl_set_morph; auto with *.
 apply impl_morph; intros; auto with *.
 apply impl_morph; intros; auto with *.
  apply in_set_morph; auto with *.
  apply Wf_morph_gen; auto with *.
 apply impl_morph; intros; auto with *.
  apply in_set_morph; auto with *.
  apply cc_prod_morph; auto with *.
 apply impl_morph; intros; auto with *.
 apply Qm; auto with *.
 apply H4; auto with *.

 apply Qm; auto with *.
Qed.
(*
Instance WSREC'_morph_gen :
  Proper (eq_set==>(eq_set==>eq_set)==>(eq_set==>eq_set)==>(eq_set==>eq_set==>eq_set==>eq_set)==>eq_set==>eq_set)
  WSREC'.
do 6 red; intros.
unfold WSREC'.
apply union_morph.
apply subset_morph.
 auto.
red; intros.
unfold Wsrec_rel'.
apply fa_morph; intros Q.
apply fa_morph; intros Qm.
apply impl_morph; intros.
 apply fa_morph; intros X.
 apply fa_morph; intros w.
 apply fa_morph; intros recf.
 apply impl_morph; intros.
  apply incl_set_morph; auto with *.
  apply W_morph; trivial.
 apply impl_morph; intros.
  apply incl_set_morph; auto with *.
  apply Wf_morph_gen; auto with *.
 apply impl_morph; intros.
  apply in_set_morph; auto with *.
  apply Wf_morph_gen; auto with *.
 apply impl_morph; intros.
  apply in_set_morph; auto with *.
  apply cc_prod_morph; auto with *.
 apply impl_morph; intros.
  reflexivity.
 apply Qm; auto with *.
 apply H2; auto with *.

 apply Qm; auto with *.
Qed.
*)
Lemma wsubterms_ext A A' B B' X X' :
  A == A' ->
  eq_fun A B B' ->
  X == X' ->
  wsubterms A B X == wsubterms A' B' X'.
intros.
unfold wsubterms.
apply inter_morph.
apply subset_morph.
 apply power_morph.
 apply W_ext; trivial.

 red; intros.
 apply and_iff_morphism.
  apply incl_set_morph; auto with *.
  apply Wf_ext; auto with *.

  apply incl_set_morph; auto with *.
  apply inter2_morph; trivial.
  apply W_ext; auto with *.
Qed.

Instance wsubterms_morph :
  Proper (eq_set==>(eq_set==>eq_set)==>eq_set==>eq_set) wsubterms.
do 4 red; intros.
unfold wsubterms.
apply inter_morph.
apply subset_morph.
 apply power_morph.
 apply W_morph; trivial.

 red; intros.
 rewrite (W_morph _ _ H _ _ H0).
 rewrite (Wf_morph_gen _ _ H _ _ H0 _ _ (reflexivity _)).
 rewrite H1; reflexivity.
Qed.


Lemma WSREC'_ext A A' B B' K K' O O' U U' F F' :
  A == A' ->
  eq_fun A B B' ->
  eq_pred (power (W A B)) K K' ->
  O ⊆ W A B ->
  O == O' ->
  (forall X, K X -> forall w w', w ∈ W A B -> w==w' -> U X w == U' X w') ->
  (forall X recf x, K X -> recf ∈ (Π w ∈ X, U X w) -> x ∈ Wf A B X ->
   F X recf x == F' X recf x) ->
  eq_fun (W A B) (WSREC' A B K O U F) (WSREC' A' B' K' O' U' F').
red; intros.
unfold WSREC'.
apply uchoice_morph_raw.
red; intros.
unfold Wsrec_rel'.
apply fa_morph; intros Q.
apply fa_morph; intros Qm.
apply impl_morph; intros.
 apply fa_morph; intros X.
 apply fa_morph; intros w.
 apply fa_morph; intros recf.
 apply impl_morph; intros.
  apply incl_set_morph; auto with *.
 apply impl_morph; intros.
  apply H1.
  apply power_intro; auto.
 apply impl_morph; intros.
  apply in_set_morph; auto with *.
  apply Wf_ext; auto with *.
 apply impl_morph; intros.
  apply in_set_morph; auto with *.
  apply cc_prod_ext; auto with *.
  red; intros; auto with *.
 apply impl_morph; intros; auto with *.
 apply Qm; auto with *.

 apply Qm; auto with *.
Qed.

End Wpaths.

