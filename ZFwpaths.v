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

Class subtermClass A B (K:set->Prop) :=
  { Kinter : forall X,
      (exists z0, z0 ∈ X) ->
      (forall z, z ∈ X -> K z) ->
      K (inter X);
    Ksup : forall I X,
      ext_fun I X ->
      (forall i, i ∈ I -> K (X i)) ->
      K (sup I X);
    KW : forall X, K X -> X ⊆ W A B;
    KWtop : K (W A B);
    Kintro : forall X, K X -> K (Wf A B X);
    Ktrans : forall X, K X -> X ⊆ Wf A B X }.
(*Module Type SubtermClass.
  Parameter K : set -> (set->set) -> set -> Prop.
  Parameter Km : forall A B, Proper (eq_set==>iff) (K A B).

  Parameter Kinter : forall A B X,
    (exists z0, z0 ∈ X) ->
    (forall z, z ∈ X -> K A B z) ->
    K A B(inter X).
  Parameter Ksup : forall A B I X,
    ext_fun I X ->
    (forall i, i ∈ I -> K A B (X i)) ->
    K A B (sup I X).

  Parameter KW : forall A B X, K A B X -> X ⊆ (W A B).
  Parameter KWtop : forall A B, K A B (W A B).

  Parameter Kintro : forall A B X,
    K A B X -> K A B (Wf A B X).
  Parameter Ktrans : forall A B X,
    K A B X -> X ⊆ Wf A B X.
  Hint Resolve KW KWtop Kintro Ktrans.
End SubtermClass.*)

(*Module Type WRecursor (Sub:SubtermClass).
Import Sub.*)
Parameter WSREC' : set -> (set -> set) -> (set->Prop) -> (set -> set -> set -> set) -> set -> set.
Parameter WSREC'_morph_gen
     : Proper
         (eq_set ==> (eq_set ==> eq_set) ==> (eq_set==>iff) ==>
          (eq_set ==> eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set)
         WSREC'.
Existing Instance WSREC'_morph_gen.
(*Parameter WSREC'_ext : forall A A' B B' O O' U U' F F',
       A == A' ->
       eq_fun A B B' ->
       O ⊆ W A B ->
       O == O' ->
       (forall X,
        K A B X -> forall w w', w ∈ W A B -> w == w' -> U X w == U' X w') ->
       (forall X recf x,
        K A B X ->
        recf ∈ (Π w ∈ X, U X w) -> x ∈ Wf A B X -> F X recf x == F' X recf x) ->
       eq_fun (W A B) (WSREC' A B F) (WSREC' A' B' F').*)
Parameter WSREC_typ' : forall A B,
       morph1 B ->
       forall K, Proper (eq_set==>iff) K -> subtermClass A B K ->
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
(*       (forall X X' recf recf',
        X ⊆ O ->
        K X ->
        X' ⊆ O ->
        K X' ->
        recf ∈ (Π w ∈ X, P X w) ->
        recf' ∈ (Π w ∈ X', P X' w) ->
        (forall x, x ∈ X -> x ∈ X' -> cc_app recf x == cc_app recf' x) ->
        forall x,
        x ∈ Wf A B X -> x ∈ Wf A B X' -> F X recf x == F X' recf' x) ->*)
       forall w, w ∈ O -> WSREC' A B K F w ∈ P O w.
Parameter WSREC_eqn' : forall A B,
       morph1 B ->
       forall K, Proper (eq_set==>iff) K -> subtermClass A B K ->
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
       WSREC' A B K F w == F O (λ w0 ∈ O, WSREC' A B K F w0) w.
(*End WRecursor.
Declare Module MakeRec (Sub:SubtermClass) : WRecursor.*)

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

Lemma Wsup_mono x x' f f' :
  x == x' ->
  is_cc_fun (B x) f ->
  (forall i, i ∈ B x -> cc_app f i ⊆ cc_app f' i) ->
  Wsup x f ⊆ Wsup x' f'.
intros eqx tyf lef; rewrite <- eqx; clear x' eqx.
intros z; rewrite !Wsup_def.
destruct 1; auto.
right.
destruct H as (i&l&y&isp&eqz).
exists i; exists l; exists y; split; trivial.
assert (i ∈ B x).
 apply tyf in isp.
 destruct isp as (_,ity). 
 rewrite fst_def in ity; trivial.
rewrite couple_in_app in isp|-*.
apply lef; trivial.
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
(*
Definition Wsnd_fun w :=
   replf (subset w (fun z => exists i l x, fst z == couple (Cons i l) x))
     (fun z => couple (fst (fst z)) (couple (snd (fst z)) (snd z))).
*)





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

Lemma mt_not_in_Wf X : ~ empty ∈ Wf X.
intro.
apply Wf_elim in H.
destruct H as (x,_,(f,_,?)).
apply empty_ax with (x:=couple Nil x).
rewrite H; apply Wsup_def; auto with *.
Qed.

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
apply W_least.
assert (subset W P ⊆ W).
 intro; apply subset_elim1.
assert (Wf (subset W P) ⊆ W).
 transitivity (Wf W).
  apply Wf_mono; trivial.
  rewrite <- W_eqn; reflexivity. 
intros z tyz.
apply subset_intro; auto.
apply Wf_elim in tyz; destruct tyz as (x,tyx,(f,tyf,eqz)).
rewrite eqz.
apply H0; trivial.
 revert tyf; apply cc_prod_covariant; auto with *.

 intros.
 apply cc_prod_elim with (2:=H4) in tyf.
 apply subset_elim2 in tyf; destruct tyf as (y,?,?).
 rewrite H5; trivial.
(*clear a H1. (* proof using FIX_ind *)
apply FIX_ind; auto with *.
fold W; intros.
red; intros.
apply subset_intro.
 rewrite W_eqn.
 revert H3; apply Wf_mono; trivial.

 apply Wf_mono in H2.
 apply H2 in H3.
 apply Wf_elim in H3; destruct H3 as (x,?,(y,?,?)).
 rewrite H5; apply H0; trivial.
 revert H4; apply cc_prod_covariant; auto with *.
 intros.
 intros z'; apply subset_elim1.
 intros.
 apply cc_prod_elim with (2:=H6) in H4.
 apply subset_elim2 in H4; destruct H4 as (y',?,?).
 rewrite H4; trivial.
*)
(*apply lower_bound; auto with *.
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
 *)
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

(** Adding bottom (for SN) *)
Lemma mt_Wdom : empty ∈ Wdom.
apply power_intro; intros.
apply empty_ax in H; contradiction.
Qed.
Hint Resolve mt_Wdom.

Require Import ZFcoc.
Definition Wfbot X := Wf (cc_bot X).

Instance Wfbot_mono : Proper (incl_set ==> incl_set) Wfbot.
unfold Wfbot; do 2 red; intros.
rewrite H; reflexivity.
Qed.

Lemma Wfbot_typ X : X ⊆ Wdom -> Wfbot X ⊆ Wdom.
intros.
apply Wf_typ.
red; intros.
apply cc_bot_ax in H0; destruct H0; auto.
rewrite H0; auto.
Qed.

Hint Resolve Wfbot_mono Wfbot_typ.

Definition Wbot := FIX incl_set inter Wdom (power Wdom) Wfbot.

Lemma Wbot_lfp : is_lfp incl_set Wfbot Wbot. 
apply knaster_tarski; auto with *.
Qed.

Lemma Wbot_eqn : Wbot == Wfbot Wbot.
symmetry; apply Wbot_lfp.
Qed.

Lemma Wbot_least X : Wfbot X ⊆ X -> Wbot ⊆ X.
apply Wbot_lfp.
Qed.

Lemma Wbot_typ : Wbot ⊆ Wdom.
apply lfp_typ; auto with *.
Qed.
Lemma Wbot_typ' : cc_bot Wbot ⊆ Wdom.
red; intros.
apply cc_bot_ax in H; destruct H.
 rewrite H; trivial.
 apply Wbot_typ; trivial.
Qed.
Lemma Wbot_ind : forall (P:set->Prop),
  Proper (eq_set ==> iff) P ->
  (forall x f, x ∈ A -> f ∈ (Π i ∈ B x, cc_bot Wbot) ->
   (forall i, i ∈ B x -> cc_app f i == empty \/ P (cc_app f i)) ->
   P (Wsup x f)) ->
  forall a, a ∈ Wbot -> P a.
intros.
cut (Wbot ⊆ subset Wbot P).
 intros inclW; apply inclW in H1.
 apply subset_elim2 in H1; destruct H1 as (a',eqa,?).
 rewrite eqa; trivial.
apply Wbot_least.
assert (subset Wbot P ⊆ Wbot).
 intro; apply subset_elim1.
assert (Wf (cc_bot (subset Wbot P)) ⊆ Wbot).
 transitivity (Wfbot Wbot).
  apply Wf_mono; trivial.
  apply cc_bot_mono; trivial.
  rewrite <- Wbot_eqn; reflexivity. 
intros z tyz.
apply subset_intro; auto.
apply Wf_elim in tyz; destruct tyz as (x,tyx,(f,tyf,eqz)).
rewrite eqz.
apply H0; trivial.
 revert tyf; apply cc_prod_covariant; auto with *.
 intros; apply cc_bot_mono; auto.
 
 intros.
 apply cc_prod_elim with (2:=H4) in tyf.
 apply cc_bot_ax in tyf; destruct tyf; auto.
 apply subset_elim2 in H5; destruct H5 as (y,?,?).
 rewrite <- H5 in H6; auto.
Qed. 
 
Lemma Wfbot_stable : stable_class (fun X => X ⊆ cc_bot Wbot) Wfbot.
eapply compose_stable_class with (F:=Wf) (K1:=fun X => X⊆cc_bot Wbot); auto with *.
 do 2 red; intros.
 rewrite H; reflexivity.

 apply Wf_stable0; intros.
 rewrite H.
 apply Wbot_typ'; trivial.

 red; intros.
 red; intros.
 destruct inter_wit with (2:=H0); auto with *.
 assert (forall x, x ∈ X -> z ∈ cc_bot x).
  intros.
  apply inter_elim with (1:=H0).
  apply replf_ax; auto with *.
  exists x0; auto with *.
 assert (zcase:=H2 _ H1).
 apply cc_bot_ax in zcase; destruct zcase.
  rewrite H3; auto.
 specialize H with (1:=H1).
 apply H in H3. 
 apply cc_bot_ax in H3; destruct H3.
  rewrite H3; auto.
 apply cc_bot_intro. 
 apply inter_intro;[|eauto].
 intros. 
 apply H2 in H4.
 apply cc_bot_ax in H4; destruct H4; trivial.
 rewrite H4 in H3; rewrite Wbot_eqn in H3.
 apply mt_not_in_Wf in H3; contradiction.

 red; intros.
 apply cc_bot_ax in H0; destruct H0; auto.
 rewrite H0; auto.
Qed.

Lemma Wfst_typ_bot w : w ∈ Wbot -> Wfst w ∈ A.
intros.
apply Wfst_typ_gen with (X:=cc_bot Wbot).
rewrite Wbot_eqn in H; trivial.
Qed.

Lemma Wsnd_typ_bot w i :
  w ∈ Wbot ->
  i ∈ B (Wfst w) ->
  Wsnd w i ∈ cc_bot Wbot.
intros.  
apply Wsnd_typ_gen; trivial.
 apply Wbot_typ'.
 rewrite Wbot_eqn in H; trivial.
Qed.


(** Coinductive *)

(* Co-Iteration of Wf *)
Require Import ZFord ZFcofix.

Definition COWi := COTI Wdom Wf.

(* Proving the fixpoint is reached at omega *)

Definition co_ord := omega.
Lemma co_ordo : isOrd co_ord. 
trivial.
Qed.

Definition COW := COWi co_ord.

Lemma COWi_closure : COW ⊆ Wf COW.
red; intros.
assert (z ∈ Wf Wdom).
 assert (z ∈ Wf (COWi zero)).
  apply COTI_elim with (3:=H); auto.
 unfold COWi in H0; rewrite COTI_initial in H0; auto.
apply Wf_elim in H0; destruct H0 as (a,tya,(f,tyf,eqz)).
rewrite eqz.
apply Wf_intro; trivial. 
rewrite cc_eta_eq with (1:=tyf).
apply cc_prod_intro; intros; auto with *.
 do 2 red; intros; apply cc_app_morph; auto with *.
apply COTI_intro; auto.
 apply cc_prod_elim with (1:=tyf); trivial.

 intros.
 assert (oo':isOrd o') by eauto using isOrd_inv.
 rewrite <- COTI_mono_succ; auto.
 2:apply Wf_typ; reflexivity.
 assert (z ∈ Wf (COWi (osucc o'))).
  apply COTI_elim with (3:=H); auto.
 rewrite eqz in H2.
 apply Wf_elim' with (x:=a); trivial.
  intros; apply cc_prod_elim with (1:=tyf); trivial.

  apply COTI_bound; auto.
Qed.

Lemma COW_typ : COW ⊆ Wdom.
apply COTI_bound; trivial.
Qed.
Lemma COW_eqn : COW == Wf COW.
apply incl_eq.
 apply COWi_closure.

 unfold COW,COWi.
 rewrite <- COTI_mono_succ; auto.
 2:apply Wf_typ; reflexivity.
 apply COTI_incl; auto.
Qed.
Lemma COW_gfp X : X ⊆ Wdom -> X ⊆ Wf X -> X ⊆ COW.
intros.
apply COTI_post_fix; auto.
Qed.

(* We do not need more properties about COW beyond this point *)
Opaque COW.
(*
Parameter COW : set.
Parameter COW_typ : COW ⊆ Wdom.
Parameter COW_eqn : COW == Wf COW.
Parameter COW_gfp : forall X, X ⊆ Wdom -> X ⊆ Wf X -> X ⊆ COW.
 *)
(* greatest fixpoint of Wf reached at a known ordinal *)
Opaque co_ord.
(*
Parameter co_ord : set.
Parameter co_ordo : isOrd co_ord. 
Parameter COWi_closure : COWi co_ord ⊆ Wf (COWi co_ord).*)
Hint Resolve co_ordo.

Lemma COW_Wf1 : COW ⊆ Wf Wdom.
rewrite COW_eqn; apply Wf_mono; trivial.
apply COW_typ.  
Qed.
Hint Resolve COW_typ COW_eqn COW_Wf1.

Lemma COW_COWi o : isOrd o -> COW ⊆ COWi o.
intros; apply COTI_post_fix; auto with *.
rewrite <- COW_eqn; reflexivity.
Qed.

(* We rediscover after the fact that COW is the iteration at omega *)
Lemma COW_def : COW == COWi co_ord.
apply incl_eq.
 apply COW_COWi; trivial.

 apply COW_gfp.
  apply COTI_bound; auto.
  apply COWi_closure.
Qed.

(* Co-recursion... *)


(* Specific properties related to building corecusrion by
   transifinite iteration *)
Lemma Wsup_incl_hd_inv x x' f f' :
  Wsup x f ⊆ Wsup x' f' -> x==x'.
intros.
assert (couple Nil x ∈ Wsup x' f').
 apply H.
 apply Wsup_def; auto with *.
apply Wsup_hd_prop in H0; trivial.
Qed.

Lemma Wsnd_def_raw0 i w z :
  z ∈ Wsnd w i <-> z == couple (fst z) (snd z) /\ couple (Cons i (fst z)) (snd z) ∈ w.
unfold Wsnd, Wsnd_fun; intros.
rewrite <- couple_in_app.
rewrite replf_ax.
2:do 2 red; intros; rewrite H0; reflexivity.
split; intros.
 destruct H as (t,?,?).
 apply subset_ax in H; destruct H as (?,(t',eqt',(i0&l0&x0&eqt))).
 rewrite eqt',eqt,!fst_def,!snd_def in H0.
 rewrite eqt',eqt in H. 
 apply couple_injection in H0; destruct H0.
 rewrite H0, H1, fst_def, snd_def.
 split; auto with *.

 destruct H.
 exists (couple (Cons i (fst z)) (snd z)).
  apply subset_intro; trivial.
  exists i; exists (fst z); exists (snd z); reflexivity. 

  rewrite H, !fst_def, !snd_def; reflexivity.
Qed.

Lemma Wsnd_def_raw i p x w :
  couple p x ∈ Wsnd w i <-> couple (Cons i p) x ∈ w.
rewrite Wsnd_def_raw0, fst_def, snd_def.
split; auto with *.
destruct 1; trivial.
Qed.

Lemma Wsnd_mono w1 w2 x :
  w1 ⊆ w2 ->
  Wsnd w1 x ⊆ Wsnd w2 x.
unfold Wsnd, Wsnd_fun; intros.
red; intros.  
rewrite <- couple_in_app in H0|-*.
revert H0; apply replf_mono_raw.
 intros z0.
 rewrite subset_ax.
 rewrite subset_ax.
 destruct 1; auto.

 red; intros.
 rewrite H0; reflexivity.
Qed.


Definition directed I X f :=
  forall x y, x ∈ I -> y ∈ I ->
  exists2 z, z ∈ I & f z ∈ X /\ f x ⊆ f z /\ f y ⊆ f z.

Lemma directed_covariant I X Y f :
  X ⊆ Y ->
  directed I X f ->
  directed I Y f.
unfold directed; intros.
destruct H0 with x y as (z,?,(?&?&?)); eauto.
Qed.

Lemma Wsnd_directed I X f x :
   X ⊆ Wdom ->
   (forall i, i ∈ I -> f i ∈ Wf X -> x ∈ B (Wfst (f i))) ->
   directed I (Wf X) f ->
   directed I X (fun i => Wsnd (f i) x).
intros Xty tyx.
unfold directed; intros.
destruct H with (1:=H0)(2:=H1) as (z,tyz,(tyfz&lex&ley)).
exists z; trivial.
split.
 apply Wsnd_typ_gen; auto.
split.
 apply Wsnd_mono; auto.
 apply Wsnd_mono; auto.
Qed.


  
  Lemma Wsup_sup_new I X f :
  ext_fun I f ->
  X ⊆ Wdom ->
  (exists2 i, i∈I & forall j, j ∈ I -> f i ⊆ f j) ->
  typ_fun f I (Wf X) ->
  exists2 a0, a0 ∈ A &
  sup I f == Wsup a0 (λ i ∈ B a0, sup I (fun x => Wsnd (f x) i)).
intros fext Xty (i0,wit,fdir) fty.
red in fty.
assert (eqsm : forall A, ext_fun A (fun i1 => sup I (fun x => Wsnd (f x) i1))).
 do 2 red; intros.
 apply sup_morph; auto with *.
 red; intros.
 apply Wsnd_morph; auto.
assert (sfm : forall i, ext_fun I (fun x => Wsnd (f x) i)).
 do 2 red; intros.
 apply Wsnd_morph; auto with *.
assert (tyf0 := fty _ wit).
apply Wf_elim in tyf0; destruct tyf0 as (a0,tya0,(f0,tyf0,eqf0)).
exists a0; trivial.
apply eq_set_ax; intros z.
 rewrite sup_ax; trivial.
 split; intros. 
  destruct H as (y,tyy,tyz).
  specialize fty with (1:=tyy).
  specialize fdir with (1:=tyy).
  apply Wf_elim in fty; destruct fty as (a1,_,(f1,tyf1,eqf1)).
  rewrite eqf0,eqf1 in fdir.
  apply Wsup_incl_hd_inv in fdir.
  rewrite eqf1 in tyz.
  revert tyz; apply Wsup_mono; auto with *.
   apply cc_prod_is_cc_fun in tyf1; trivial.

   intros.
   rewrite cc_beta_eq; auto.
   2:rewrite fdir; trivial.
   rewrite <- (Wsnd_def a1 f1 i),<-eqf1.
    apply sup_incl with (1:=sfm i); trivial.
    apply Xty; apply cc_prod_elim with (1:=tyf1); trivial.

 apply Wsup_def in H.
 destruct H as [?|(i&l&y&?&eqz)].
  exists i0; trivial.
  rewrite H,eqf0.
  apply Wsup_def; auto with *.

  apply cc_lam_def in H; trivial.
  destruct H as (x,tyx,(y',tyy',eqq)).
  apply couple_injection in eqq; destruct eqq.
  rewrite <- H0 in tyy'.
  apply sup_ax in tyy'; trivial.
  destruct tyy' as (y'',?,?).
  exists y''; trivial.
  rewrite eqz.
  apply Wsnd_def_raw.
  rewrite H; trivial.
Qed.

Lemma Wsup_sup_raw I X f a0 :
  ext_fun I f ->
  X ⊆ Wdom ->
  (exists i, i∈I) ->
  (forall i, i∈I -> exists2 j, j ∈ I &
                    exists2 g, g ∈ (Π _∈B a0,X) & f i ⊆ f j /\ f j == Wsup a0 g) ->
  sup I f == Wsup a0 (λ i ∈ B a0, sup I (fun x => Wsnd (f x) i)).
intros fext Xty (i0,wit) fdir.
assert (eqsm : forall A, ext_fun A (fun i1 => sup I (fun x => Wsnd (f x) i1))).
 do 2 red; intros.
 apply sup_morph; auto with *.
 red; intros.
 apply Wsnd_morph; auto.
assert (sfm : forall i, ext_fun I (fun x => Wsnd (f x) i)).
 do 2 red; intros.
 apply Wsnd_morph; auto with *.
apply eq_set_ax; intros z.
 rewrite sup_ax; trivial.
 split; intros. 
  destruct H as (y,tyy,tyz).
  destruct fdir with (1:=tyy) as (y',tyy',(f1,tyf1,(ley,le0))).
  rewrite le0 in ley.
  red in ley; specialize ley with (1:=tyz).
  revert ley; apply Wsup_mono; auto with *.
   apply cc_prod_is_cc_fun in tyf1; trivial.
  intros.
  rewrite cc_beta_eq; auto.
  rewrite <- (Wsnd_def a0 f1 i),<-le0.
   apply sup_incl with (1:=sfm _); trivial.
   apply Xty;apply cc_prod_elim with (1:=tyf1); trivial.
   
(*

  apply Wsup_def in ley.
  destruct ley as [?|(i&l&a'&tyi&eqz)];[auto|].
  right; exists i; exists l; exists a'; split; trivial.
  apply cc_lam_def; trivial.
  exists i; trivial.
   apply tyf1 in tyi.
   destruct tyi as (_,tyi).
   rewrite fst_def in tyi; trivial.

   exists (couple l a'); auto with *.
   apply sup_ax; trivial.
   exists y; trivial.
   rewrite eqz in tyz.  
   apply Wsnd_def_raw; trivial.
*)
 rewrite Wsup_def in H.
 destruct H as [?|(i&l&y&?&eqz)].
  destruct fdir with (1:=wit) as (i,tyi,(f0,tyf0,(lei,le0))).
  exists i; trivial.
  rewrite H,le0.
  apply Wsup_def; auto with *.

  apply cc_lam_def in H; trivial.
  destruct H as (x,tyx,(y',tyy',eqq)).
  apply couple_injection in eqq; destruct eqq.
  rewrite <- H0 in tyy'.
  apply sup_ax in tyy'; trivial.
  destruct tyy' as (y'',?,?).
  exists y''; trivial.
  rewrite eqz.
  apply Wsnd_def_raw.
  rewrite H; trivial.
Qed.


Definition complete o X :=
  forall f, ext_fun o f->
  directed o X f ->
  sup o f ∈ X.

Instance complete_morph : Proper (eq_set==>eq_set==>iff) complete.
do 3 red; intros.
apply fa_morph; intros f.
apply impl_morph; intros.
 apply fa_morph; intros a.
 apply fa_morph; intros a'.
 rewrite H; reflexivity.

 apply impl_morph; intros.
  apply fa_morph; intros x1.
  apply fa_morph; intros y1.
  apply impl_morph; [rewrite H;reflexivity|intros].
  apply impl_morph; [rewrite H;reflexivity|intros].
  apply ex2_morph; red; intros.
   rewrite H; reflexivity.
   rewrite H0; reflexivity.

  apply in_set_morph; trivial. 
  apply sup_morph; trivial.
Qed.

(*Lemma infb_complete I J F :
  ext_fun J F ->
  (forall j, j ∈ J -> F j ⊆ Wdom) ->
  (forall j, j ∈ J -> complete I (F j)) ->
  complete I (infb Wdom J F).
intros Fext Fty Fcl.
red; intros.
apply infb_ax; intros; trivial.
split.
 apply power_intro; intros.
 apply sup_ax in H1; trivial.
 destruct H1 as (y,tyy,tyz).
 destruct H0 with y y as (y',tyy',(tyfy'&ley'&_)); trivial.
 apply infb_ax in tyfy'; trivial.
 apply ley' in tyz.
 apply power_elim with (2:=tyz).
 apply tyfy'.

 intros.
 apply Fcl; trivial.
 red; intros.
 destruct H0 with x0 y as (z,zty,(tyfz&le1&le2)); trivial.
 exists z; trivial.
 split; auto.
 apply infb_ax in tyfz; trivial.
 apply tyfz; trivial.
Qed.
*)
(*
Lemma Wsup_sup I X f :
  ext_fun I f ->
  X ⊆ Wdom ->
  (exists i, i∈I) ->
  directed I (Wf X) f ->
  exists2 a, a ∈ A &
  exists2 g, is_cc_fun (B a) g &
  sup I f == Wsup a g /\
  forall x, x ∈ B a -> cc_app g x == sup I (fun i => Wsnd (f i) x).
intros fext Xty (i0,wit0) dir.
red in dir.
destruct dir with (1:=wit0)(2:=wit0) as (i,wit,(tyfi&lei&_)).
clear wit0 lei.
apply Wf_elim in tyfi.
destruct tyfi as (a0,tya0,(f0,tyf0,eqf0)).
exists a0; trivial.
apply cc_prod_is_cc_fun in tyf0.
econstructor;[|split;[apply Wsup_sup_raw with (X:=X); eauto|]].
 apply is_cc_fun_lam. admit.

admit.

intros.
rewrite cc_beta_eq; auto with *.
admit.
(*
apply Wsup_sup_raw with (X:=X); eauto.
intros.
destruct dir with (1:=wit)(2:=H) as (z,tyz,(tyfz&le0&le1)).
rewrite eqf0 in le0.
apply Wf_elim in tyfz.
destruct tyfz as (a,tya,(f1,tyf1,eqfz)).
rewrite eqfz in le0.
apply Wsup_incl_hd_inv in le0.
apply cc_prod_is_cc_fun in tyf1.
rewrite <- le0 in tyf1,eqfz.
exists z; trivial.
exists f1; auto.*)
Qed.

 Lemma Wf_complete I X :
  (exists i, i ∈ I) ->
  X ⊆ Wdom -> complete I X -> complete I (Wf X).
intros Iwit tyX Xcl.
red; intros f fext fdir.  
destruct Wsup_sup with (4:=fdir) as (a,tya,(g,tyg,(eqf,?))); trivial. 
rewrite eqf; apply Wf_intro; trivial.
rewrite cc_eta_eq' with (1:=tyg).
apply cc_prod_intro; intros; auto.
 admit.
apply Xcl; auto.
apply Wsnd_directed; trivial.
intros.
red in fdir.
apply Wf_elim in H1; destruct H1 as (a1,_,(f1,_,eqf1)).
assert (f i ⊆ sup I f); auto.
rewrite eqf, eqf1 in H1.
apply Wsup_incl_hd_inv in H1.
rewrite eqf1,Wfst_def,H1; trivial.
Qed.
*)
  
  Lemma Wsup_sup I X f :
  ext_fun I f ->
  X ⊆ Wdom ->
  (exists i, i∈I) ->
  directed I (Wf X) f ->
  exists2 a0, a0 ∈ A & sup I f == Wsup a0 (λ i ∈ B a0, sup I (fun x => Wsnd (f x) i)).
intros fext Xty (i0,wit0) dir.
red in dir.
destruct dir with (1:=wit0)(2:=wit0) as (i,wit,(tyfi&lei&_)).
clear wit0 lei.
apply Wf_elim in tyfi.
destruct tyfi as (a0,tya0,(f0,_,eqf0)).
exists a0; trivial.
apply Wsup_sup_raw with (X:=X); eauto.
intros.
destruct dir with (1:=wit)(2:=H) as (z,tyz,(tyfz&le0&le1)).
rewrite eqf0 in le0.
apply Wf_elim in tyfz.
destruct tyfz as (a,tya,(f1,tyf1,eqfz)).
rewrite eqfz in le0.
apply Wsup_incl_hd_inv in le0.
rewrite <-le0 in eqfz.
exists z; trivial.
exists f1; auto.
revert tyf1; apply eq_incl; apply cc_prod_ext; auto with *.
do 2 red; reflexivity.
Qed.

  Lemma Wf_complete I X :
  (exists i, i ∈ I) ->
  X ⊆ Wdom -> complete I X -> complete I (Wf X).
intros Iwit tyX Xcl.
red; intros f fext fdir.  
assert (eqsm : forall A, ext_fun A (fun i1 => sup I (fun x => Wsnd (f x) i1))).
 do 2 red; intros.
 apply sup_morph; auto with *.
 red; intros.
 apply Wsnd_morph; auto.
assert (sfm : forall i, ext_fun I (fun x => Wsnd (f x) i)).
 do 2 red; intros.
 apply Wsnd_morph; auto with *.
destruct Wsup_sup with (4:=fdir) as (a,tya,eqf); trivial. 
rewrite eqf; apply Wf_intro; trivial.
apply cc_prod_intro; intros; auto.
apply Xcl; auto.
apply Wsnd_directed; trivial.
intros.
red in fdir.
apply Wf_elim in H1; destruct H1 as (a1,_,(f1,_,eqf1)).
assert (f i ⊆ sup I f); auto.
rewrite eqf, eqf1 in H1.
apply Wsup_incl_hd_inv in H1.
rewrite eqf1,Wfst_def,H1; trivial.
Qed.

  
  Lemma power_sup_closed a I f :
    ext_fun I f ->
    (forall i, i ∈ I -> exists2 j, j ∈ I & f j ∈ power a /\ f i ⊆ f j) ->
    sup I f ∈ power a.
intros fext tyf; apply power_intro; intros.
apply sup_ax in H; trivial.
destruct H as (?,?,tyz).
destruct tyf with (1:=H) as (j,tyj,(tyfj,leij)).
apply power_elim with (f j); auto.
Qed.
    
  Lemma Wdom_sup_closed I f :
    ext_fun I f ->
    directed I Wdom f ->
    sup I f ∈ Wdom.
intros; apply  power_sup_closed; trivial; intros.
red in H0.
destruct H0 with i i as (z,tyz,(tyfz&le&_)); eauto.
Qed.

Lemma COWi_complete I o : (exists i, i ∈ I) -> isOrd o -> complete I (COWi o).
intros wit oo; elim oo using isOrd_ind; intros.
assert (aux := fun o => isOrd_inv _ o H).
intros f fext fdir.
apply COTI_intro; intros; auto.
 apply Wdom_sup_closed; trivial.
 revert fdir; apply directed_covariant.
 apply COTI_bound; auto.

 apply Wf_complete; auto.
  apply COTI_bound; auto.

  revert fdir; apply directed_covariant.
  rewrite <- COTI_mono_succ; auto.
   apply COTI_mono; auto.
   apply olts_le; apply lt_osucc_compat; trivial.

   apply Wf_typ; reflexivity.
Qed.

Lemma Wf_dir o o' f :
  ext_fun o f ->
  increasing f ->
  isOrd o ->
  o' ∈ o ->
  (forall o'', o' ⊆ o'' -> o'' ∈ o -> f o'' ∈ Wf (COWi o')) ->
  directed o (Wf (COWi o')) f.
intros fext fmono oo lto Hrec.
assert (aux := isOrd_inv).
red; intros.
set (z := o' ⊔ (x ⊔ y)).
assert (z ∈ o).
 apply osup2_lt; trivial.
 apply osup2_lt; trivial.
exists z; trivial.
split.
 apply Hrec; trivial.
 apply osup2_incl1; eauto.
split; apply fmono; eauto.
 unfold z; rewrite <- osup2_incl2; eauto.
 apply osup2_incl1; eauto.

 unfold z; rewrite <- osup2_incl2; eauto.
 apply osup2_incl2; eauto.
Qed.


Lemma COWi_sup_intro f o o' :
  ext_fun o f ->
  increasing f ->
  isOrd o ->
  o' ∈ o ->
  (forall o'', o' ⊆ o'' -> o'' ∈ o -> f o'' ∈ Wf (COWi o')) ->
  sup o f ∈ Wf (COWi o').
intros fext fmono oo lto Hrec.
assert (aux := isOrd_inv).
assert (oo':isOrd o') by eauto.
apply Wf_complete; eauto.
 apply COTI_bound; auto.

 apply COWi_complete; eauto.
 apply Wf_dir; trivial.
Qed.


(*  Lemma Wsup_incl_inv x x' f f' :
  Wsup x f ⊆ Wsup x' f' -> x==x' /\ (f ∈ (Π _∈B x,Wdom) -> f ⊆ f').
intros.
assert (couple Nil x ∈ Wsup x' f').
 apply H.
 apply Wsup_def; auto with *.
split.
 apply Wsup_hd_prop in H0; trivial.

 red; intros.
 assert (z == couple (fst z) (couple (fst (snd z)) (snd (snd z)))).
  rewrite cc_eta_eq with (1:=H1) in H2.
  apply cc_lam_def in H2.
  2:do 2 red; intros; apply cc_app_morph; auto with *.
  destruct H2 as (i,tyi,(y,tyy,eqz)).  
  rewrite eqz,fst_def, snd_def.
  assert (y ∈ prodcart (List (sup A B)) A).
   apply power_elim with (2:=tyy).
   apply cc_prod_elim with (1:=H1); trivial.
  apply surj_pair in H2.
  apply couple_in_app in tyy.
  rewrite <- H2; reflexivity.
 assert (couple (Cons (fst z) (fst (snd z))) (snd (snd z)) ∈ Wsup x' f'). 
  apply H.
  apply Wsup_def.
  right. 
  exists (fst z); exists (fst (snd z)); exists (snd (snd z)); split; auto with *.
  rewrite <- H3; trivial.
 apply Wsup_tl_prop in H4.
 apply couple_in_app in H4.
 rewrite H3; trivial.
Qed.*)
(*
Lemma Wsup_cont o f x :
  ext_fun o f ->
  sup o (fun o' => Wsup x (f o')) ⊆ Wsup x (sup o f).
red; intros.
apply sup_ax in H0.
 destruct H0 as (o',?,?).
 apply Wsup_def.
 apply Wsup_def in H1.
 destruct H1; auto.
 right.
 destruct H1 as (i&l&y&?&?).
 exists i;exists l;exists y; split; trivial.
 apply sup_ax; eauto.

 do 2 red; intros.
 apply Wsup_morph; auto with *.
Qed. 


Lemma Wsup_cont_rev o f x o' :
  o' ∈ o ->
  Wsup x (sup o f) ⊆ sup o (fun o' => Wsup x (f o')).
intros o_ne.
red; intros.
apply Wsup_def in H.
destruct H.
 apply sup_ax. admit.
 exists o'; trivial.
 apply Wsup_def; auto.

 destruct H as (i&l&y&?&?). 
 apply sup_ax in H. 2:admit.
 destruct H.
 apply sup_ax.
  admit.
 exists x0; trivial.
 apply Wsup_def.
 right.
 eauto.
Qed.
*)

Lemma pre_incl_eq X w1 w2 :
  X ⊆ Wdom ->
  X ⊆ Wf X ->
  w1 ∈ X ->
  w2 ∈ X ->
  w1 ⊆ w2 ->
  w2 == w1.
intros Xty Xcl cw1 cw2 incl12.
apply incl_eq; trivial.
red; intros.
assert (tyz : exists2 p, p ∈ List (sup A B) & exists2 a, a ∈ A & z == couple p a).
 specialize power_elim with (1:=Xty _ cw2) (2:=H); intros.
 exists (fst z);[apply fst_typ in H0; trivial|].
 exists (snd z);[apply snd_typ in H0; trivial|].
 apply surj_pair with (1:=H0).
destruct tyz as (p,typ,(a,tya,eqz)).
assert (forall a w1 w2, a ∈ A -> w1 ⊆ w2 -> w1 ∈ X -> w2 ∈ X ->
                        couple p a ∈ w2 -> couple p a ∈ w1).
 clear z eqz incl12 cw1 cw2 H w1 w2 a tya.
 elim typ using List_ind; intros.
  do 2 red; intros.
  apply fa_morph; intros a.
  apply fa_morph; intros w1.
  apply fa_morph; intros w2.
  rewrite H; reflexivity.

  apply Xcl in H1; apply Wf_elim in H1; destruct H1 as (a1,_,(f1,_,eqw1)).
  apply Xcl in H2; apply Wf_elim in H2; destruct H2 as (a2,_,(f2,_,eqw2)).
  rewrite eqw1 in H0|-*; rewrite eqw2 in H0,H3; clear eqw1 eqw2.
  apply Wsup_incl_hd_inv in H0.
  apply Wsup_hd_prop in H3; apply Wsup_hd_prop.
  rewrite H0; trivial.

  assert (tyw2 :=H5).
  apply Xcl in H4; apply Wf_elim in H4; destruct H4 as (a1,_,(f1,tyf1,eqw1)).
  apply Xcl in H5; apply Wf_elim in H5; destruct H5 as (a2,_,(f2,tyf2,eqw2)).
  rewrite eqw1 in H3|-*; rewrite eqw2 in H3,H6,tyw2; clear eqw1 eqw2.
  assert (same_x := H3); apply Wsup_incl_hd_inv in same_x.
  apply Wsup_tl_prop in H6; apply Wsup_tl_prop.
  assert (tyx2 : x ∈ B a2).
   apply couple_in_app in H6.
   apply cc_prod_is_cc_fun in tyf2.
   apply tyf2 in H6.
   destruct H6 as (_,tyx).
   rewrite fst_def in tyx; trivial.
  assert (tyx1 : x ∈ B a1).
   rewrite same_x; trivial.
  revert H6; apply H1; auto.
   apply Wsnd_mono with (x:=x) in H3; auto.
   rewrite !Wsnd_def in H3; auto.
    apply Xty; apply cc_prod_elim with (1:=tyf2); trivial.
    apply Xty; apply cc_prod_elim with (1:=tyf1); trivial.
   apply cc_prod_elim with (1:=tyf1); trivial.
   apply cc_prod_elim with (1:=tyf2); trivial.
revert H; rewrite eqz; apply H0; trivial.
Qed.


(* Simple co-recursion *)
Section SimpleCorecursion.

Hypothesis F:set->set.
Hypothesis Fm:morph1 F.
(*Existing Instance Fm.*)
Hypothesis Fty :
  forall X w, COW ⊆ Wf X -> Wf X ⊆ X ->
            w ∈ X -> F w ∈ Wf X.
(*Hint Resolve Fm.*)
Require Import ZFfix.

Lemma TI_WF_dom o :
  isOrd o ->
  TI F o ∈ Wdom.
induction 1 using isOrd_ind; intros.
rewrite TI_eq; auto with *.
apply power_intro.
intros.
apply sup_ax in H2. 2:do 2 red; intros; apply Fm; apply TI_morph; trivial.
destruct H2.
apply power_elim with (2:=H3).
apply Wf_typ with (X:=Wdom); auto with *.
Qed.

Lemma FTI_typ o w :
  isOrd o ->
  w ∈ COWi o ->
  F w ∈ Wf (COWi o).
intros.
apply Fty; trivial.
 rewrite COW_eqn; apply Wf_mono; apply COW_COWi; trivial.

 unfold COWi; rewrite <- COTI_mono_succ; auto with *.
 apply COTI_incl; auto.
Qed.

Definition productive X F :=
  forall w w0,
  w0 ∈ X -> (* w0 = observation *)
  w ∈ X -> w0 ⊆ w -> (* obs of w0 are the same in w *)
  F w0 ⊆ F w. (* F w0 can be observed both in F w *)
  
Hypothesis Fprod : productive Wdom F.
(*  forall X, X ⊆ Wdom -> COW ⊆ Wf X -> Wf X ⊆ X -> (* = K X *)
  productive X F.*)


Definition K X :=
  COW ⊆ X /\ X ⊆ Wdom /\ Wf X ⊆ X.
Definition K' X :=
  COW ⊆ X /\ X ⊆ Wdom /\ X ⊆ Wf X.

Definition Fcfx X := subset X (fun w => F w ⊆ w).

Lemma Fcxf_cofix w :
  w ∈ Fcfx COW ->
  w ∈ COW /\ w == F w.
intros.
apply subset_ax' in H. 2:admit.
destruct H.
split; trivial.
apply pre_incl_eq with (X:=COW); auto.
 rewrite <-COW_eqn; reflexivity.

 rewrite COW_eqn; apply Fty; auto.
  rewrite <-COW_eqn; reflexivity.
  rewrite <-COW_eqn; reflexivity.
Qed.


(*


      Lemma Fcxf_cofix X w :
  X ⊆ Wdom ->
  X ⊆ Wf X ->
  w ∈ Fcfx X ->
  w ∈ X /\ w == F w.
intros.
apply subset_ax' in H1. 2:admit.
destruct H1.
split; trivial.
apply pre_incl_eq with (X:=Wf X); auto.
apply Fty.
apply subset
*)

(*
Lemma WfFcfx X : Fcfx X ⊆ Wf (Fcfx X).
red; intros.
apply subset_ax' in H. 2:admit.
destruct H.
assert (F z ∈ Wf Wdom).
 apply Fty; auto.
  apply Wf_typ; reflexivity.
  admit. (* X ⊆ Wdom *)
apply Wf_elim in H1; destruct H1 as (a,tya,(f,tyf,eqfz)).
assert (z ∈ Wf X) by admit. (* X ⊆ Wf X *)
apply Wf_elim in H1; destruct H1 as (a',tya',(f',tyf',eqz)).
rewrite eqz; apply Wf_intro; trivial.
rewrite cc_eta_eq with (1:=tyf').
apply cc_prod_intro; auto. admit.
intros.
apply subset_intro.
 apply cc_prod_elim with (1:=tyf'); trivial.

 apply Wsnd_mono with (x:=x) in H0.
 rewrite eqfz,Wsnd_def in H0.
 rewrite eqz, Wsnd_def in H0.
 rewrite <- H0.
 
 rewrite <-(Wsnd_def a' f' x).

 rewrite 

  Lemma WfFcfx X : Wf (Fcfx X) ⊆ Fcfx X.
red; intros.
apply subset_intro.
admit. (* Wf X ⊆ X *)

assert (F z ∈ Wf Wdom).
admit.
apply Wf_elim in H; destruct H as (a,tya,(f,tyf,eqz)).
apply Wf_elim in H0; destruct H0 as (a',tya',(f',tyf',eqfz)).
rewrite eqfz,eqz.
assert (a'==a).
 admit.
apply Wsup_mono; trivial.
 apply cc_prod_is_cc_fun in tyf'; trivial.

 intros.
 rewrite H in H0.
 specialize cc_prod_elim with (1:=tyf) (2:=H0); intros.
 apply subset_ax' in H1. 2:admit.
 destruct H1.
 
 
 
apply Fty.
assert (F z ∈ Wf (Wf (Fcfx X))).
apply Fty; trivial.

Wdom).

*)
(*
Definition cfx := infb Wdom (subset (power Wdom) (fun X => X ⊆ Wf X)) Fcfx.
 *)
(*
Lemma cfx_clos : cfx ⊆ Wf cfx.
red; intros.
apply infb_ax in H. 2:admit.
destruct H.
assert (forall X, X ⊆ Wdom -> X ⊆ Wf X -> z ∈ X /\ F z ⊆ z).
 admit.

 apply H1.
apply Wf_typ.
apply infb_bound.

apply 

Admitted.
*)
(*Lemma cfx_typ : cfx ⊆ COW.
apply COW_gfp.
 apply infb_bound.
 apply cfx_clos.
Qed.
 
Definition COREC' :=
  infb empty (subset Wdom (fun w => forall X, K' X -> w ∈ X -> F w ⊆ w))
       (fun w => w).


Lemma COREC'_typ X :
  X ⊆ Wdom ->
  
  *)

         
Lemma FTI_mono : increasing (fun o => F (TI F o)).
red; intros.
apply Fprod.
 apply TI_WF_dom; trivial.

 apply TI_WF_dom; trivial.

 apply TI_mono; trivial.
Qed.

Lemma TI_WF_step o : isOrd o ->
  TI F o ⊆ F (TI F o).
red; intros.
apply TI_elim in H0; trivial.
destruct H0 as (o',?,?).
revert H1; apply FTI_mono; eauto using isOrd_inv.
Qed.

Lemma TI_WF_typ_gen o o' : isOrd o -> isOrd o' -> o' ⊆ o -> TI F o ∈ COWi o'.
intros oo; revert o'; elim oo using isOrd_ind; intros.
apply COTI_intro; auto.
 apply TI_WF_dom; trivial.

 intros o''; intros.
 assert (oo'':isOrd o'') by eauto using isOrd_inv.
 assert (eqC: Wf (COWi o'') == COWi (osucc o'')).
  symmetry; apply COTI_mono_succ; auto.
  apply Wf_typ; reflexivity.
 rewrite TI_eq; auto.
 apply COWi_sup_intro; auto.
  apply FTI_mono.

  intros.
  apply FTI_typ; auto.
Qed.

Lemma TI_WF_typ o : isOrd o -> TI F o ∈ COWi o.
intros; apply TI_WF_typ_gen; auto with *.
Qed.


Definition COREC := TI F co_ord.

Lemma COREC_typ : COREC ∈ COW.
rewrite COW_def.
apply TI_WF_typ; trivial.
Qed.

Lemma COREC_eqn : COREC == F COREC.  
symmetry.
apply pre_incl_eq with (X:=COWi co_ord); auto.
 apply COWi_closure.

 rewrite <- COW_def.
 apply COREC_typ.

 rewrite <- COW_def, COW_eqn, COW_def.
 apply FTI_typ; trivial.
 apply COREC_typ.

 apply TI_WF_step; trivial.
Qed.


Lemma corec_typ w :
  w ∈ Wdom ->
  w == F w ->
  w ∈ COW.
intros.
rewrite COW_def.
elim co_ordo using isOrd_ind; intros.
apply COTI_intro; intros; auto.
rewrite H0.
apply FTI_typ; eauto using isOrd_inv.
Qed.

Lemma COREC_unique w :
  w ∈ Wdom ->
  w == F w ->
  w == COREC.
intros.
apply pre_incl_eq with (X:=COW); auto.
 rewrite <- COW_eqn; reflexivity.

 apply COREC_typ.

 apply corec_typ; trivial.

 unfold COREC.
 elim co_ordo using isOrd_ind; intros.
 red; intros.
 elim TI_elim with (3:=H4); intros; auto with *.
 rewrite H0; revert H6; apply Fprod; auto.
 apply TI_WF_dom; eauto using isOrd_inv.
Qed.

Let test := (COREC_typ,COREC_eqn,COREC_unique).
Print Assumptions test.


(* Productive functions : includes constructors *)

 
Lemma productive_id X : productive X (fun w => w).
  red; trivial.
Qed.

Lemma productive_comp X Y F0 G :
  (forall w, w ∈ X -> F0 w ∈ Y) ->
  productive X F0 ->
  productive Y G ->
  productive X (fun x => G (F0 x)).
unfold productive; auto.
Qed.

Lemma productive_cst X w : productive X (fun _ => w).
red; reflexivity.
Qed.

Lemma productive_cstr X x f :
  (forall w, w ∈ X -> is_cc_fun (B x) (f w)) ->
  (forall i, i ∈ B x -> productive X (fun w => cc_app (f w) i)) ->
  productive X (fun w => Wsup x (f w)).
unfold productive; intros fty fprod; intros.
apply Wsup_mono; auto with *.
Qed.

End SimpleCorecursion.

(* Indexed-corec *)

Require Import ZFfixfun.

Parameter I:set.
Parameter F:(set->set)->set->set.
Parameter Fm:Proper((eq_set==>eq_set)==>eq_set==>eq_set) F.
Existing Instance Fm.
Parameter Fty :
  forall X f, COW ⊆ Wf X -> Wf X ⊆ X ->
  morph1 f ->
  typ_fun f I X ->
  typ_fun (F f) I (Wf X).
Hint Resolve Fm.

Definition iproductive I X F :=
  forall w w0,
  morph1 w -> morph1 w0 ->
  typ_fun w0 I X -> (* w0 = observation *)
  typ_fun w I X ->
  incl_fam I w0 w -> (* obs of w0 are the same in w *)
  incl_fam I (F w0) (F w). (* F w0 can be observed both in F w *)
  
Parameter Fprod : iproductive I Wdom F.

Lemma TIF_WF_dom o :
  isOrd o ->
  typ_fun (TIF I F o) I Wdom.
intros oo; induction oo using isOrd_ind; red; intros.
rewrite TIF_eq; auto with *.
apply power_intro.
intros.
apply sup_ax in H2. 2:do 2 red; intros; apply Fm; auto with *; apply TIF_morph; trivial.
 destruct H2.
 apply power_elim with (2:=H3).
 apply Wf_typ with (X:=Wdom); auto with *.
 apply Fty with (X:=Wdom); auto with *.
 apply TIF_morph; reflexivity.
Qed.

Lemma FTIF_typ o w (wm:morph1 w) :
  isOrd o ->
  typ_fun w I (COWi o) ->
  typ_fun (F w) I (Wf (COWi o)).
intros.
apply Fty; trivial.
 rewrite COW_eqn; apply Wf_mono; apply COW_COWi; trivial.

 unfold COWi; rewrite <- COTI_mono_succ; auto with *.
 apply COTI_incl; auto.
Qed.


Lemma FTIF_mono a : a ∈ I -> increasing (fun o => F (TIF I F o) a).
red; intros.
apply Fprod; auto.
 apply TIF_morph; auto with *.
 apply TIF_morph; auto with *.

 apply TIF_WF_dom; trivial.

 apply TIF_WF_dom; trivial.

 red; intros.
 apply TIF_mono; trivial.
Qed.

Lemma TIF_WF_step o : isOrd o ->
  incl_fam I (TIF I F o) (F (TIF I F o)).
do 2 red; intros.
apply TIF_elim in H1; trivial.
destruct H1 as (o',?,?).
revert H2; apply FTIF_mono; eauto using isOrd_inv.
Qed.

Lemma TIF_WF_typ_gen o o' : isOrd o -> isOrd o' -> o' ⊆ o -> typ_fun (TIF I F o) I (COWi o').
intros oo; revert o'; elim oo using isOrd_ind; red; intros.
apply COTI_intro; auto.
 apply TIF_WF_dom; trivial.

 intros o''; intros.
 assert (oo'':isOrd o'') by eauto using isOrd_inv.
 assert (eqC: Wf (COWi o'') == COWi (osucc o'')).
  symmetry; apply COTI_mono_succ; auto.
  apply Wf_typ; reflexivity.
 rewrite TIF_eq; auto.
 apply COWi_sup_intro; auto.
  do 2 red; intros.
  apply Fm; auto with *.
  apply TIF_morph; trivial.
  
  apply FTIF_mono; trivial.

  intros.
  apply FTIF_typ; auto.
  apply TIF_morph; auto with *.
Qed.

Lemma TIF_WF_typ o : isOrd o -> typ_fun (TIF I F o) I (COWi o).
intros; apply TIF_WF_typ_gen; auto with *.
Qed.


Definition ICOREC := TIF I F co_ord.

Instance ICOREC_morph : morph1 ICOREC.
apply TIF_morph; reflexivity.
Qed.


Lemma ICOREC_typ : typ_fun ICOREC I COW.
red; intros.
rewrite COW_def.
apply TIF_WF_typ; trivial.
Qed.

Lemma ICOREC_eqn : eq_fun I ICOREC (F ICOREC).
red; intros.
symmetry.
apply pre_incl_eq with (X:=COWi co_ord); auto.
 apply COWi_closure.

 rewrite <- COW_def.
 apply ICOREC_typ; trivial.

 rewrite <- COW_def, COW_eqn, COW_def.
 apply FTIF_typ; auto with *.
  apply ICOREC_typ.
  rewrite <- H0; trivial.

 rewrite H0.
 apply TIF_WF_step; trivial.
 rewrite <- H0; trivial.
Qed.


Lemma icorec_typ w :
  morph1 w ->
  typ_fun w I Wdom ->
  eq_fun I w (F w) ->
  typ_fun w I COW.
intros wm; intros.
rewrite COW_def.
elim co_ordo using isOrd_ind; intros.
red; intros.
apply COTI_intro; intros; auto.
red in H0; rewrite H0;[|trivial|reflexivity].
apply FTIF_typ; eauto using isOrd_inv.
Qed.

Lemma ICOREC_unique w :
  morph1 w ->
  typ_fun w I Wdom ->
  eq_fun I w (F w) ->
  eq_fun I w ICOREC.
intros wm; intros.
red; intros.
rewrite <- H2.
clear x' H2.
apply pre_incl_eq with (X:=COW); auto.
 rewrite <- COW_eqn; reflexivity.

 apply ICOREC_typ; trivial.

 apply icorec_typ; trivial.

 unfold ICOREC.
 revert x H1; elim co_ordo using isOrd_ind; intros.
 red; intros.
 elim TIF_elim with (4:=H5); intros; auto with *.
 red in H0; rewrite H0; [|trivial|reflexivity].
 revert H7; apply Fprod; auto.
  apply TIF_morph; reflexivity.

  apply TIF_WF_dom; eauto using isOrd_inv.

  red; intros; apply H3; trivial.
Qed.

Let itest := (ICOREC_typ,ICOREC_eqn,COREC_unique).
Print Assumptions itest.

(* *)


(* Counter-example: well-typed cofix, but not productive... 
CoInductive strm := Cs (_:nat) (_:strm).
Definition hd (s:strm) := let (n,_) := s in n.
Definition tl (s:strm) := let (_,s') := s in s'.
(*Definition s := cofix s := Cs (S (hd s)) s.*)
Lemma nos s : s = Cs (S (hd s)) s -> False.
intros.
apply f_equal with (f:=hd) in H.
simpl in H.
apply Plus.succ_plus_discr with (m:=0) in H; trivial.
Qed.
*)


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

Class subtermClass (K:set->Prop) :=
  { Kinter : forall X,
      (exists z0, z0 ∈ X) ->
      (forall z, z ∈ X -> K z) ->
      K (inter X);
    Ksup : forall I X,
      ext_fun I X ->
      (forall i, i ∈ I -> K (X i)) ->
      K (sup I X);
    KW : forall X, K X -> X ⊆ W;
    KWtop : K W;
    Kintro : forall X, K X -> K (Wf X);
    Ktrans : forall X, K X -> X ⊆ Wf X }.
(* TODO
Hypothesis Kstage : forall w w',
   (forall X, K X -> w ∈ Wf X -> w' ∈ Wf X) ->
   forall X, K X -> w ∈ X -> w' ∈ X.
*)

Variable K : set -> Prop.
Hypothesis Km : Proper (eq_set==>iff) K.
Hypothesis Ksc : subtermClass K.

Hint Resolve KW KWtop Kintro Ktrans.
Let KW' := KW. 

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
  split; auto.
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

Lemma fsub_Wf_intro w :
   w ∈ W ->
   w ∈ Wf (fsub w).
intros.
rewrite W_eqn in H.
apply Wf_elim in H.
destruct H as (x,tyx,(f,tyf,eqw)).
rewrite eqw; apply Wf_intro; trivial.
rewrite cc_eta_eq with (1:=tyf).
apply cc_prod_intro; auto.
 do 2 red; intros; apply cc_app_morph; auto with *.
intros.
apply fsub_intro.
 rewrite W_eqn; apply Wf_intro; trivial.

 intros.
 apply Wf_elim' with (4:=H1); auto.
 intros; apply W_typ; apply cc_prod_elim with (1:=tyf); trivial.
 rewrite <-W_typ; auto.
 Qed.

Lemma fsub'fsub w0 w1 :
  w0 ∈ W ->
  w1 ∈ fsub' w0 ->
  w1 ∈ Wf (fsub w0).
intros.   
apply fsub'_elim with (3:=H0).
 apply Kintro.
 apply Kfsub; trivial.

 apply fsub_Wf_intro; trivial.
Qed.

Lemma fsub_fsub'_trans w0 w1 w2 :
  w0 ∈ W ->
  w1 ∈ fsub' w0 ->
  w2 ∈ fsub w1 ->
  w2 ∈ fsub w0.
intros.  
apply fsub_elim with (3:=H1).
 apply Kfsub; trivial.

 apply fsub'fsub; trivial.
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

(*Require Import ZFlimit.*)


Let R w w' := w ∈ fsub w'.
Let Rm : Proper (eq_set==>eq_set==>iff) R.
unfold R; do 3 red; intros.
rewrite H,H0; reflexivity.
Qed.

Let G f w :=
  F (fsub w) (cc_lam (fsub w) f) w.
Let Gm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) G.
unfold G; do 3 red; intros.
apply Fm; trivial.
 apply fsub_morph; trivial.

 apply cc_lam_ext.
  apply fsub_morph; trivial.

  red; intros;auto.
Qed.  
Hint Resolve Rm Gm.

Let Gext x f f' :
   Acc R x ->
   (forall y y', R y x -> y == y' -> f y == f' y') ->
   G f x == G f' x.
intros.
unfold G.
apply Fm; auto with *.
apply cc_lam_ext; auto with *.
Qed.

     
Definition WSREC' := WFR R G.

Global Instance WSREC'_morph0 : morph1 WSREC'.
apply WFR_morph0.
Qed.


Lemma Wacc w :
  w ∈ W ->
  forall w', w' ∈ fsub' w ->
  Acc R w'.
intros tyw.
elim tyw using W_ind; intros.
 do 2 red; intros.
 apply fa_morph; intros w'.
 rewrite H; reflexivity.

 constructor; intros.
 red in H3.
 assert (y ∈ fsub (Wsup x f)).
  apply fsub_fsub'_trans with w'; trivial.
  rewrite W_eqn; apply Wf_intro; trivial.
 destruct fsub_elim' with (3:=H4) as (i,tyi,?); eauto.
Qed.

Let Oacc w :
  w ∈ O ->
  Acc R w.
intros.
apply KW' in H; trivial.  
apply Wacc with w; trivial.
apply fsub'_intro; auto.
Qed.
Hint Resolve Gext Oacc.

Lemma WSREC_eqn0' w :
  w ∈ O ->
  WSREC' w == F (fsub w) (λ w ∈ fsub w, WSREC' w) w.
intros; unfold WSREC' at 1.
apply WFR_eqn; auto.
Qed.

Lemma Pmono' x y :
  y ∈ W ->
  x ∈ fsub y ->    
  P (Wf (fsub x)) x ⊆ P (fsub y) x.
intros.
apply Pmono.
 apply Kfsub; auto.

 intros.
 exists x; trivial.
 intros.
 apply fsub_elim with (3:=H1); trivial.
Qed.


  Lemma WSREC_typ0' w :
  w ∈ O ->
  WSREC' w ∈ P (Wf (fsub w)) w.
intros; unfold WSREC'.
generalize H; eapply WFR_ind with (x:=w); intros; auto.
 do 3 red; intros.
 rewrite H0,H1; reflexivity.
apply f_typ.
 red; intros.
 apply fsub_elim with (3:=H3); auto.
 apply Ktrans; auto.

 apply Kfsub; auto.
 apply KW' in H2; trivial.

 apply fsub_Wf_intro; auto.
 apply KW' in H2; trivial.

 apply cc_prod_intro; intros.
  do 2 red; intros; apply WSREC'_morph0; trivial.
  do 2 red; intros; apply Pm; auto with *.
 apply Pmono'; trivial.
  apply KW' in H2; trivial.

  apply H1; trivial.
  apply (Ktrans _ KO) in H2; trivial.
  apply fsub_elim with (3:=H3); trivial.
Qed.

Lemma WSREC_typ' w :
  w ∈ O -> 
  WSREC' w ∈ P O w.
intros tyw.
eapply Pmono; auto.
2:apply WSREC_typ0'; trivial.
intros; exists w; trivial.
intros.
apply fsub_elim with (3:=H); trivial.
Qed.

Lemma WSREC_eqn' w :
  w ∈ O ->
  WSREC' w == F O (λ w ∈ O, WSREC' w) w.
intros.
rewrite WSREC_eqn0'; trivial.
assert (wO : w ∈ Wf O).
 apply Ktrans; trivial.
apply Firr; auto with *.
 red; intros.
 apply fsub_elim with (3:=H0); trivial.

 apply Kfsub; auto.
 apply KW with (X:=O); trivial. 

 apply cc_prod_intro.
  do 2 red; intros; apply WSREC'_morph0; trivial.
  do 2 red; intros; apply Pm; auto with *.
 intros.
 apply Pmono'; trivial.
  apply KW' in H; trivial.
 apply WSREC_typ0'; trivial.
 apply fsub_elim with (3:=H0); trivial.

 apply cc_prod_intro.
  do 2 red; intros; apply WSREC'_morph0; trivial.
  do 2 red; intros; apply Pm; auto with *.
 intros.
 eapply Pmono; trivial.
 2:apply WSREC_typ0'; trivial.
 intros.
 exists x; trivial.
 intros. 
 apply fsub_elim with (3:=H1); trivial.

 intros.
 rewrite cc_beta_eq; trivial.
  rewrite cc_beta_eq; trivial.
   reflexivity.

   do 2 red; intros; apply WSREC'_morph0; trivial.
  do 2 red; intros; apply WSREC'_morph0; trivial.

 apply fsub_Wf_intro.
 apply KW with (X:=O); trivial. 
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

Local Notation E := eq_set (only parsing).

Instance Wf_morph_gen :
  Proper (E==>(E==>E)==>E==>E) Wf.
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
 

Instance Wdom_morph : Proper (E==>(E==>E)==>E) Wdom.
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
  Proper ((E==>E==>E)==>E==>E) Wcase.
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

Instance W_morph : Proper (E==>(E==>E)==>E) W.
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
  Proper (E==>(E==>E)==>(E==>E)==>(E==>E==>E==>E)==>E==>E) WREC.
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
  Proper (E==>(E==>E)==>(E==>E)==>(E==>E==>E)==>E==>E) WSREC.
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

Lemma fsub_ext A A' B B' K K' :
  A==A' ->
  eq_fun A B B' ->
  (forall X, X ⊆ W A B -> (K X <-> K' X)) ->
  (E==>E)%signature (fsub A B K) (fsub A' B' K').
red; intros; unfold fsub.
apply inter_morph; apply subset_morph.
 apply power_morph; apply W_ext; trivial.

 red; intros.
 rewrite power_ax in H3.
 apply and_iff_morphism; auto with *.
 apply in_set_morph; trivial.
 apply Wf_ext; auto with *.
Qed.
Instance fsub_morph_gen :
  Proper (E==>(E==>E)==>(E==>iff)==>E==>E) fsub.
do 5 red; intros; unfold fsub.
apply inter_morph; apply subset_morph.
 apply power_morph; apply W_morph; trivial.

 red; intros.
 apply and_iff_morphism; auto with *.
 apply in_set_morph; trivial.
 apply Wf_morph_gen; auto with *.
Qed.

Instance WSREC'_morph_gen :
  Proper (E==>(E==>E)==>(E==>iff)==>(E==>E==>E==>E)==>E==>E)
  WSREC'.
do 6 red; intros.
unfold WSREC'.
apply WFR_morph; trivial.
 do 2 red; intros.
 apply in_set_morph; trivial.
 apply fsub_morph_gen; trivial.

 do 2 red; intros.
 apply H2; trivial.
  apply fsub_morph_gen; trivial.

  apply cc_lam_ext.
   apply fsub_morph_gen; trivial.

   red; intros; auto.
Qed.

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
  Proper (E==>(E==>E)==>E==>E) wsubterms.
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

(*Lemma WSREC'_ext A A' B B' K K' F F' U :
  A == A' ->
  eq_fun A B B' ->
  (forall X, X ⊆ W A B -> (K X <-> K' X)) ->
(*  O ⊆ W A B ->
  O == O' ->
  (forall X, K X -> forall w w', w ∈ W A B -> w==w' -> U X w == U' X w') ->*)
  (forall X X' recf recf' x, K X -> X==X' -> recf ∈ (Π w ∈ X, W A B) -> recf==recf' -> x ∈ Wf A B X ->
   F X recf x == F' X' recf' x) ->
  eq_fun (W A B) (WSREC' A B K F) (WSREC' A' B' K' F').
red; intros.
apply uchoice_morph_raw.
red; intros.
unfold WFR_rel.
apply fa_morph; intros P.
apply fa_morph; intros Pm.
apply impl_morph; intros.
2:apply Pm; trivial.
apply fa_morph; intros w.
apply fa_morph; intros f.
apply fa_morph; intros fm.
apply impl_morph; intros.
 apply star_rel_gen_morph; auto with *.
 intros w1 w2.
 apply in_set_morph; auto with *.
 apply fsub_ext; auto with *.
apply impl_morph; intros.
 apply fa_morph; intros z.
 apply impl_morph; auto with *.
 apply in_set_morph; auto with *.
 apply fsub_ext; auto with *.
apply Pm; auto with *.
apply H2.
 admit.

 apply fsub_ext; auto with *.

 apply cc_prod_intro.
  do 2 red; intros.
  rewrite H9; reflexivity. 

  do 2 red; intros.
  admit.

  intros.
  
  apply cond_set_morph.
   apply in_set_morph; auto with *.
   apply fsub_ext; auto with *.
   
  
 admit.
 admit.

 

 apply fsub
       _ext; auto with *.

  apply cc_prod_intro; intros.
   do 2 red; intros.
   rewrite H7; reflexivity.
   admit. (* Um *)



   apply Kfsub; auto.
 rewrite (fsub_morph_gen _ _ H _ _ (fun _ _ h => H0 _ _ reflexivity).
apply fa_morph; intros P.
apply fa_morph; intros P.


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
*)
End Wpaths.

