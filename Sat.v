Require Import Lambda.

(** A somehow abstract interface to work with reducibility candidates
    or saturated sets.
 *)

Set Implicit Arguments.

(** * Theory of saturated sets *)

Module Type SAT.
  (** The type of "saturated sets" and basic relations: equality and membership *)
  Parameter SAT : Type.
  Parameter eqSAT : SAT -> SAT -> Prop.
  Parameter inSAT : term -> SAT -> Prop.
  Parameter eqSAT_def : forall X Y,
    eqSAT X Y <-> (forall t, inSAT t X <-> inSAT t Y).
  Definition inclSAT A B := forall t, inSAT t A -> inSAT t B.

  Parameter inSAT_morph : Proper ((@eq term) ==> eqSAT ==> iff) inSAT.

  (** Essential properties of saturated sets :
      - they are sets of SN terms
      - they are closed by head expansion
   *)
  Parameter sat_sn : forall t S, inSAT t S -> sn t.
  Parameter inSAT_red : forall S u m,
    inSAT (App (Abs m) u) S ->
    inSAT (subst u m) S.
  Parameter inSAT_exp : forall S u m,
    boccur 0 m = true \/ sn u ->
    inSAT (subst u m) S ->
    inSAT (App (Abs m) u) S.

  (** A term that belongs to all saturated sets (e.g. variables) *)
  Parameter daimon : term.
  Parameter varSAT : forall S, inSAT daimon S.

  (** Closure properties are preserved by head contexts *)
  Parameter inSAT_context : forall u u' v,
    (forall S, inSAT u S -> inSAT u' S) ->
    forall S, inSAT (App u v) S -> inSAT (App u' v) S.

  (** The set of strongly normalizing terms *)
  Parameter snSAT : SAT.
  Parameter snSAT_intro : forall t, sn t -> inSAT t snSAT.

  (** Non-depenent products *)
  Parameter prodSAT : SAT -> SAT -> SAT.
  Parameter prodSAT_morph : Proper (eqSAT ==> eqSAT ==> eqSAT) prodSAT.
  Parameter prodSAT_intro : forall A B m,
    (forall v, inSAT v A -> inSAT (subst v m) B) ->
    inSAT (Abs m) (prodSAT A B).
  Parameter prodSAT_elim : forall A B u v,
    inSAT u (prodSAT A B) ->
    inSAT v A ->
    inSAT (App u v) B.

  (** Intersection *)
  Parameter interSAT : forall A:Type, (A -> SAT) -> SAT.
  Parameter interSAT_morph : forall A A' (F:A->SAT) (G:A'->SAT),
    indexed_relation eqSAT F G ->
    eqSAT (interSAT F) (interSAT G).
  Parameter interSAT_intro_gen : forall A F u,
    sn u ->
    (forall x:A, inSAT u (F x)) ->
    inSAT u (interSAT F).
  Parameter interSAT_elim : forall A F u,
    inSAT u (interSAT F) ->
    forall x:A, inSAT u (F x).

  Existing Instance inSAT_morph.
  Existing Instance prodSAT_morph.

End SAT.

(** * Instantiating this signature with Girard's reducibility candidates *)

Require Import Can.

Module SatSet <: SAT.

  Definition SAT := {P:term->Prop|is_cand P}.
  Definition inSAT t (S:SAT) := proj1_sig S t.
  Definition eqSAT X Y := forall t, inSAT t X <-> inSAT t Y.
  Lemma eqSAT_def : forall X Y,
    eqSAT X Y <-> (forall t, inSAT t X <-> inSAT t Y).
reflexivity.
Qed.

  Instance inSAT_morph : Proper ((@eq term) ==> eqSAT ==> iff) inSAT.
do 3 red; intros; unfold inSAT.
rewrite H.
exact (H0 y).
Qed.

  Definition inclSAT A B := forall t, inSAT t A -> inSAT t B.

  Lemma eqSAT_incl X Y : eqSAT X Y -> inclSAT X Y.
intros h t; apply h.
Qed.

  Lemma inclSAT_eq X Y :
    inclSAT X Y -> inclSAT Y X -> eqSAT X Y.
split; auto.
Qed.
  
  Global Instance inclSAT_ord : PreOrder inclSAT.
split; red; intros.
 red; trivial.

 red; intros; auto.
Qed.

  Global Instance eqSAT_equiv : Equivalence eqSAT.
split; red; intros.
 rewrite eqSAT_def; reflexivity.
 rewrite eqSAT_def in H|-*; symmetry; trivial.
 rewrite eqSAT_def in H,H0|-*; intros;
   transitivity (inSAT t y); trivial.
Qed.


  Lemma sat_sn : forall t S, inSAT t S -> sn t.
destruct S; simpl; intros.
apply (incl_sn _ i); trivial.
Qed.

  Definition daimon := Ref 0.

  Lemma varSAT : forall S, inSAT daimon S.
destruct S; simpl; intros.
apply var_in_cand with (1:=i).
Qed.

  Lemma inSAT_red : forall S u m,
    inSAT (App (Abs m) u) S ->
    inSAT (subst u m) S.
destruct S; simpl; intros.
apply clos_red with (X:=x) (t:=App(Abs m) u); auto with *.
Qed.

  Lemma inSAT_exp : forall S u m,
    boccur 0 m = true \/ sn u ->
    inSAT (subst u m) S ->
    inSAT (App (Abs m) u) S.
destruct S; simpl; intros.
apply cand_sat with (X:=x); trivial.
Qed.

  Lemma inSAT_context : forall u u' v,
    (forall S, inSAT u S -> inSAT u' S) ->
    forall S, inSAT (App u v) S -> inSAT (App u' v) S.
destruct S; simpl; intros.
apply cand_context with (X:=x) (u:=u); trivial; intros.
apply (H (exist _ X H1)); trivial.
Qed.



  Definition snSAT : SAT := exist _ sn cand_sn.

  Lemma snSAT_intro : forall t, sn t -> inSAT t snSAT.
do 3 red; trivial.
Qed.

  Global Opaque snSAT.
  
  Definition prodSAT (X Y:SAT) : SAT.
(*begin show*)
exists (Arr (proj1_sig X) (proj1_sig Y)).
(*end show*)
apply is_cand_Arr; apply proj2_sig.
Defined.

  Lemma prodSAT_intro': forall A B m,
    (forall v, inSAT v A -> inSAT (App m v) B) ->
    inSAT m (prodSAT A B).
simpl; intros.
red; intros.
apply H; trivial.
Qed.

  Lemma prodSAT_elim : forall A B u v,
    inSAT u (prodSAT A B) ->
    inSAT v A ->
    inSAT (App u v) B.
intros (A,A_can) (B,B_can) u v u_in v_in; simpl in *.
red in u_in.
auto.
Qed.

  Global Opaque prodSAT.
  
  Lemma prodSAT_intro : forall A B m,
    (forall v, inSAT v A -> inSAT (subst v m) B) ->
    inSAT (Abs m) (prodSAT A B).
intros.
apply prodSAT_intro'; intros.
apply inSAT_exp; auto.
apply sat_sn in H0; auto.
Qed.

  Instance prodSAT_mono : Proper (inclSAT --> inclSAT ++> inclSAT) prodSAT.
do 4 red; intros.
apply prodSAT_intro'.
intros u satu.
apply H0.
apply prodSAT_elim with (1:=H1); auto.
Qed.

  Instance prodSAT_morph : Proper (eqSAT ==> eqSAT ==> eqSAT) prodSAT.
do 3 red; intros.
apply inclSAT_eq.
 apply prodSAT_mono.
  apply eqSAT_incl; symmetry; trivial.
  apply eqSAT_incl; trivial.

 apply prodSAT_mono.
  apply eqSAT_incl; trivial.
  apply eqSAT_incl; symmetry; trivial.
Qed.

  Definition interSAT (A:Type) (F:A -> SAT) : SAT :=
    exist _ (Inter A (fun x => proj1_sig (F x)))
      (is_can_Inter _ _ (fun x => proj2_sig (F x))).

  Lemma interSAT_intro_gen A F u :
    sn u ->
    (forall x:A, inSAT u (F x)) ->
    inSAT u (interSAT F).
split; trivial.
Qed.

  Lemma interSAT_elim : forall A F u,
    inSAT u (interSAT F) ->
    forall x:A, inSAT u (F x).
unfold inSAT, interSAT, Inter; simpl; intros.
destruct H; trivial.
Qed.
  Global Opaque interSAT.

  Lemma interSAT_intro' : forall A (P:A->Prop) F t,
      sn t ->
      (forall x, P x -> inSAT t (F x)) ->
      inSAT t (interSAT (fun p:sig P => F (proj1_sig p))).
intros.
apply interSAT_intro_gen; auto.
destruct x; simpl; auto.
Qed.

  Lemma interSAT_mono A (F G:A->SAT):
    (forall x, inclSAT (F x) (G x)) ->
    inclSAT (interSAT F) (interSAT G).
red; intros.
apply interSAT_intro_gen; intros.
 apply sat_sn in H0; trivial.
apply H.
apply interSAT_elim with (1:=H0).
Qed.

  Lemma interSAT_morph A A' (F:A->SAT) (G:A'->SAT) :
    indexed_relation eqSAT F G ->
    eqSAT (interSAT F) (interSAT G).
intros (eqv1,eqv2).
split; intros.
 apply interSAT_intro_gen; intros.
  apply sat_sn in H; trivial.
 destruct eqv2 with x as (x',?).
 rewrite <- H0.
 apply interSAT_elim with (1:=H); trivial. 

 apply interSAT_intro_gen; intros.
  apply sat_sn in H; trivial.
 destruct eqv1 with x as (x',?).
 rewrite H0.
 apply interSAT_elim with (1:=H); trivial. 
Qed.

  Lemma interSAT_intro : forall A F u,
    A ->
    (forall x:A, inSAT u (F x)) ->
    inSAT u (interSAT F).
intros.
apply interSAT_intro_gen; trivial.
eapply sat_sn.
apply (H X).
Qed.


Lemma incl_interSAT_l A (F:A->SAT) x :
  inclSAT (interSAT F) (F x).
red; intros.
apply interSAT_elim with (1:=H).
Qed.

Lemma interSAT_ax : forall A F u,
    A ->
    ((forall x:A, inSAT u (F x)) <->
     inSAT u (interSAT F)).
split; intros.
 apply interSAT_intro; auto.
 apply interSAT_elim; trivial.
Qed.

End SatSet.

Export SatSet.

Global Opaque inSAT.

(** Derived facts *)

  Instance inclSAT_morph : Proper (eqSAT==>eqSAT==>iff) inclSAT.
apply morph_impl_iff2; auto with *.
do 5 red; intros.
 rewrite <- H0; rewrite <- H in H2; auto. 
Qed.

Lemma interSAT_mono_subset :
  forall A (P Q:A->Prop) (F:sig P->SAT) (G:sig Q->SAT),
  (forall x, Q x -> P x) ->
  (forall x Px Qx,
   inclSAT (F (exist P x Px)) (G (exist Q x Qx))) ->
  inclSAT (interSAT F) (interSAT G).
red; intros.
split.
 apply sat_sn in H1; trivial.
intros (x,Qx).
change (inSAT t (G (exist Q x Qx))).
apply H0 with (Px:=H _ Qx).
apply interSAT_elim with (1:=H1).
Qed.

Lemma interSAT_morph_subset :
  forall A (P Q:A->Prop) (F:sig P->SAT) (G:sig Q->SAT),
  (forall x, P x <-> Q x) ->
  (forall x Px Qx,
   eqSAT (F (exist P x Px)) (G (exist Q x Qx))) ->
  eqSAT (interSAT F) (interSAT G).
intros.
apply interSAT_morph; red; split; intros.
 destruct x; simpl.
 exists (exist Q x (proj1 (H x) p)); auto.

 destruct y; simpl.
 exists (exist P x (proj2 (H x) q)); auto.
Qed.

  Definition neuSAT := interSAT(fun S=>S).

  Lemma neuSAT_def u :
    inSAT u neuSAT <-> forall S, inSAT u S.
split; intros; trivial.
apply interSAT_elim with (1:=H).
Qed.

  Lemma neuSAT_ext S :
    inclSAT S neuSAT -> 
    eqSAT S neuSAT.
split; intros; auto.
apply neuSAT_def; trivial.
Qed.

  Lemma neuSAT_inf S :
    inclSAT neuSAT S.
red; intros.
rewrite neuSAT_def in H; trivial.
Qed.


(** If t belongs to all reducibility candidates, then it has a free variable *)
  Lemma neutral_not_closed :
  forall t, (forall S, inSAT t S) -> exists k, occur k t.
intros.
assert (neu := H (exist _ _ neutral_is_cand : SAT)).
simpl in neu.
destruct neu as (_,(u,?,(nfu,neuu))).
destruct nf_neutral_open with (1:=nfu) (2:=neuu) as (k,occ).
exists k.
apply red_closed with u; auto.
Qed.

 
  Lemma KSAT_intro : forall A t m,
    sn t ->
    inSAT m A ->
    inSAT (App2 K m t) A.
intros.
apply prodSAT_elim with snSAT.
2:apply snSAT_intro; trivial.
apply prodSAT_elim with A; trivial.
apply prodSAT_intro; intros.
unfold subst; simpl subst_rec.
apply prodSAT_intro; intros.
unfold subst; rewrite simpl_subst; trivial.
rewrite lift0; trivial.
Qed.


Lemma KSAT_def : forall A t m,
    (inSAT m A /\ sn t) <->
    inSAT (App2 K m t) A.
split; intros.
 destruct H; apply KSAT_intro; trivial.

 split.
  unfold K in H.
  eapply inSAT_context in H.
  2:intros S; apply inSAT_red.
  unfold subst in H; simpl in H.
  apply inSAT_red in H.
  unfold subst in H; rewrite simpl_subst in H; auto with *.
  rewrite lift0 in H; trivial.

  apply sat_sn in H.
  apply subterm_sn with (1:=H).
  constructor.
Qed.


  Lemma SAT_daimon1 : forall S u,
    sn u ->
    inSAT (App daimon u) S.
intros.
apply prodSAT_elim with snSAT; auto.
apply varSAT.
Qed.

  Lemma omega_sn_when_A_is_A_to_B A B :
    let delta := Abs (App (Ref 0) (Ref 0)) in
    eqSAT A (prodSAT A B) -> inSAT (App delta delta) B.
intros.
assert (inSAT delta A).
 rewrite H.
 apply prodSAT_intro; intros.
 unfold subst; simpl.
 rewrite lift0.
 apply prodSAT_elim with A; trivial.
 rewrite <- H; trivial.
apply prodSAT_elim with A; trivial.
rewrite <- H; trivial.
Qed.

(** Dealing with type dependencies *)

Definition depSAT A (P:A->Prop) F :=
  interSAT (fun x:sig P => F (proj1_sig x)).

Lemma depSAT_elim A (P:A->Prop) F t x :
  inSAT t (depSAT P F) ->
  P x ->
  inSAT t (F x).
intros.
apply interSAT_elim with (x:=exist P x H0) in H.
trivial.
Qed.

Lemma depSAT_elim' A (P:A->Prop) F t :
  inSAT t (depSAT P F) -> id (forall x, P x -> inSAT t (F x)).
red; intros.
apply depSAT_elim with (1:=H) (2:=H0).
Qed.

Lemma depSAT_intro A (P:A->Prop) F t :
  sn t ->
  (forall x, P x -> inSAT t (F x)) ->
  inSAT t (depSAT P F).
split; trivial.
intros (x,?); simpl.
apply (H0 x); trivial.
Qed.

Lemma depSAT_intro' A (P:A->Prop) F t :
  (exists x, P x) ->
  (forall x, P x -> inSAT t (F x)) ->
  inSAT t (depSAT P F).
split; trivial.
 destruct H as (x,px).
 apply H0 in px; apply sat_sn in px; trivial.

 intros (x,?); simpl.
 apply (H0 x); trivial.
Qed.

(** Conditional saturated set *)

Definition condSAT (P:Prop) (S:SAT) : SAT :=
  depSAT (fun C => P -> inclSAT S C) (fun C => C).

Lemma condSAT_ext (P Q:Prop) S S':
  (P -> Q) ->
  (P -> Q -> inclSAT S S') ->
  inclSAT (condSAT P S) (condSAT Q S').
unfold condSAT, depSAT; red; intros.
apply interSAT_intro.
 econstructor; reflexivity.
intros (C,?); simpl.
assert (rmk : P -> inclSAT S C).
 intros.
 transitivity S'; auto.
apply interSAT_elim with (1:=H1)(x:=exist (fun _=>_) C rmk). 
Qed.

Lemma condSAT_morph_gen (P P':Prop) S S' :
  (P<->P') ->
  (P->eqSAT S S') ->
  eqSAT (condSAT P S) (condSAT P' S').
intros.
apply interSAT_morph_subset; simpl; intros; auto with *.
apply impl_morph; trivial.
split; intros.
 red; intros.
 rewrite <- H0 in H3; auto.

 red ;intros.
 rewrite H0 in H3; auto.
Qed.

Instance condSAT_mono :
  Proper (impl ==> inclSAT ==> inclSAT) condSAT.
unfold condSAT, depSAT; do 4 red; intros.
apply interSAT_intro.
 econstructor; reflexivity.
intros (C,?); simpl.
assert (rmk : x -> inclSAT x0 C).
 intros.
 transitivity y0; auto.
apply interSAT_elim with (1:=H1)(x:=exist (fun _=>_) C rmk). 
Qed.

Instance condSAT_morph : Proper (iff==>eqSAT==>eqSAT) condSAT.
do 3 red; intros.
apply condSAT_morph_gen; auto with *.
Qed.

Lemma condSAT_ok (P:Prop) S : P -> eqSAT (condSAT P S) S.
split; intros.
 unfold condSAT in H0.
 apply (depSAT_elim S H0); auto with *.

 apply depSAT_intro; intros.
  apply sat_sn in H0; trivial.
  apply H1; trivial.
Qed.

Lemma condSAT_neutral P C S :
  ~ P -> inclSAT (condSAT P C) S.
red; intros.
unfold condSAT in H0.
eapply depSAT_elim' in H0; red in H0.
apply H0; intros; contradiction.
Qed.

Lemma condSAT_smaller P S :
  inclSAT (condSAT P S) S.
red; intros.
unfold condSAT in H.
apply (depSAT_elim S H); auto with *.
Qed.


(** Dependent product *)

Definition piSAT0 A (P:A->Prop) (F G:A->SAT) :=
  depSAT P (fun x => prodSAT (F x) (G x)).

Lemma piSAT0_morph : forall A (P P':A->Prop) F F' G G',
  pointwise_relation A iff P P' ->
  (forall x, P x -> P' x -> eqSAT (F x) (F' x)) ->
  (forall x, P x -> P' x -> eqSAT (G x) (G' x)) ->
  eqSAT (piSAT0 P F G) (piSAT0 P' F' G').
unfold piSAT0; intros.
apply interSAT_morph_subset; simpl; intros; auto with *.
apply prodSAT_morph; auto with *.
Qed.

Lemma piSAT0_intro : forall A (P:A->Prop) (F G:A->SAT) t,
  sn t -> (* if A is empty *)
  (forall x u, P x -> inSAT u (F x) -> inSAT (App t u) (G x)) ->
  inSAT t (piSAT0 P F G).
unfold piSAT0; intros.
apply depSAT_intro; trivial.
intros.
apply prodSAT_intro'; auto.
Qed.

Lemma piSAT0_intro' A0 (P:A0->Prop) (F G:A0->SAT) t :
  (forall x u, P x -> inSAT u (F x) -> inSAT (App t u) (G x)) ->
  (exists w, P w) ->
  inSAT t (piSAT0 P F G).
intros.
apply piSAT0_intro; trivial.
destruct H0 as (w,?).
apply subterm_sn with (App t (Ref 0)); auto.
apply sat_sn with (G w).
apply H; trivial.
apply varSAT.
Qed.


Lemma piSAT0_elim : forall A (P:A->Prop) (F G:A->SAT) x t u,
  inSAT t (piSAT0 P F G) ->
  P x ->
  inSAT u (F x) ->
  inSAT (App t u) (G x).
intros.
apply interSAT_elim with (x:=exist _ x H0) in H.
apply prodSAT_elim with (2:=H1); trivial.
Qed.

Lemma piSAT0_elim' A (P:A->Prop) (F G:A->SAT) t :
  inSAT t (piSAT0 P F G) ->
  id (forall x u, P x -> inSAT u (F x) -> inSAT (App t u) (G x)).
red; intros.
apply piSAT0_elim with (1:=H)(2:=H0)(3:=H1).
Qed.

Lemma piSAT0_mono X X' (A:X->Prop) (A':X'->Prop) B B' C C' (f:X'->X):
  (forall x, A' x -> A (f x)) ->
  (forall x, A' x -> inclSAT (B' x) (B (f x))) ->
  (forall x, A' x -> inclSAT (C (f x)) (C' x)) ->
  inclSAT (piSAT0 A B C) (piSAT0 A' B' C').
red; intros.
apply piSAT0_intro.
 apply sat_sn in H2; trivial.
intros.
apply H1; trivial.
 apply piSAT0_elim' in H2; red in H2.
apply H2; auto.
apply H0; trivial.
Qed.
Global Opaque piSAT0.
