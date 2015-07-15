Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFtarski.
Require Import ZFgrothendieck.
Require Import ZFlist.
Import ZFrepl.

(** In this file we develop the theory of W-types as a type of trees encoded
    as a relation from paths to labels.
 *)

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
   sup (B x)
     (fun y => replf (subset (cc_app f y) (fun p => p == couple (fst p) (snd p)))
                     (fun p => couple (Cons y (fst p)) (snd p))).

Instance Wsup_morph : morph2 Wsup.
do 3 red; intros.
unfold Wsup.
apply union2_morph.
 rewrite H; reflexivity.

 apply sup_morph.
  rewrite H; reflexivity.

  red; intros.
  apply replf_morph_raw; auto.
   apply subset_morph.
    rewrite H0; rewrite H2; reflexivity.
   red; intros.
   reflexivity.

   red; intros.
   rewrite H2; rewrite H3; reflexivity.
Qed.

Lemma wext1 : forall i y,
  ext_fun y (fun p => couple (Cons i (fst p)) (snd p)).
do 2 red; intros.
rewrite H0; reflexivity.
Qed.

Lemma wext2 : forall X g,
  ext_fun X (fun y =>
     replf (subset (cc_app g y) (fun p => p == couple (fst p) (snd p)))
           (fun p => couple (Cons y (fst p)) (snd p))).
do 2 red; intros.
apply replf_morph_raw; auto.
 apply subset_morph.
  rewrite H0; reflexivity.
 red; intros.
 reflexivity.

 red; intros.
 rewrite H0; rewrite H1; reflexivity.
Qed.
Hint Resolve wext1 wext2.

Lemma Wsup_def x f p :
  (p ∈ Wsup x f <->
   p == couple Nil x \/
   exists2 i, i ∈ B x &
   exists l y, couple l y ∈ cc_app f i /\ p == couple (Cons i l) y).
unfold Wsup.
split; intros.
 apply union2_elim in H; destruct H;[left|right].
  apply singl_elim in H; trivial.

  rewrite sup_ax in H; auto.
  destruct H as (i,?,?); exists i; trivial.
  rewrite replf_ax in H0; trivial.
  destruct H0 as (p',tyx,eqp).
  rewrite subset_ax in tyx.
  destruct tyx as (?,(p'',?,?)).
  rewrite <- H1 in H2; clear H1 p''.
  rewrite H2 in H0.
  exists (fst p'); exists (snd p'); split; trivial.

 destruct H as [eqp|(i,?,(l&y&?&eqp))]; rewrite eqp; clear eqp.  
  apply union2_intro1.
  apply singl_intro.

  apply union2_intro2.
  rewrite sup_ax; auto.
  exists i; trivial.
  rewrite replf_ax; trivial.
  exists (couple l y).
   apply subset_intro; trivial.
   rewrite fst_def, snd_def; reflexivity.

   rewrite fst_def, snd_def; reflexivity.
Qed.

Lemma Wsup_hd_prop a x f :
  couple Nil a ∈ Wsup x f <-> a == x.
rewrite Wsup_def.
split; intros.
 destruct H as [eqc|(i,tyi,(l&y&?&eqc))].
  apply couple_injection in eqc; destruct eqc; trivial.

  apply couple_injection in eqc; destruct eqc as (eqc,_).
  apply discr_mt_pair in eqc; contradiction.

 left; rewrite H; reflexivity.
Qed.

Lemma Wsup_tl_prop i l a x f :
  couple (Cons i l) a ∈ Wsup x f <-> i ∈ B x /\ couple l a ∈ cc_app f i.
rewrite Wsup_def.
split; intros.
 destruct H as [eqc|(i',tyi,(l'&y&?&eqc))].
  apply couple_injection in eqc; destruct eqc as (eqc,_).
  symmetry in eqc.
  apply discr_mt_pair in eqc; contradiction.

  apply couple_injection in eqc; destruct eqc as (eqc,eqa).
  apply couple_injection in eqc; destruct eqc as (eqi,eql).
  rewrite eqi,eql,eqa; auto.

 right.
 destruct H.
 exists i; trivial.
 exists l; exists a; auto with *.
Qed.


Lemma Wsup_inj x x' f f' :
  x ∈ A ->
  x' ∈ A ->
  (forall i, i ∈ B x -> cc_app f i ∈ Wdom) ->
  (forall i, i ∈ B x' -> cc_app f' i ∈ Wdom) ->
  Wsup x f == Wsup x' f' -> x == x' /\ (forall i, i ∈ B x -> cc_app f i == cc_app f' i).
intros tyx tyx' tyf tyf' eqw.
assert (eqh1 := Wsup_hd_prop x x f).
assert (eqh2 := Wsup_hd_prop x x' f').
rewrite <- eqw in eqh2.
rewrite eqh1 in eqh2.
apply and_split.
 apply eqh2; reflexivity.
clear eqh1 eqh2.
intros eqx i tyi.
apply eq_set_ax; intros z.
assert (eqt1 := Wsup_tl_prop i (fst z) (snd z) x f).
assert (eqt2 := Wsup_tl_prop i (fst z) (snd z) x' f').
rewrite <- eqw in eqt2.
rewrite eqt1 in eqt2.
specialize tyf with (1:=tyi).
assert (tyi' := tyi).
rewrite eqx in tyi'.
specialize tyf' with (1:=tyi').
split; intros.
 apply power_elim with (2:=H) in tyf.
 rewrite surj_pair with (1:=tyf).
 apply eqt2.
 split; trivial.
 rewrite <- surj_pair with (1:=tyf); trivial.

 apply power_elim with (2:=H) in tyf'.
 rewrite surj_pair with (1:=tyf').
 apply eqt2.
 split; trivial.
 rewrite <- surj_pair with (1:=tyf'); trivial.
Qed.

Lemma Wsup_typ_gen x f :
  x ∈ A ->
  (forall i, i ∈ B x -> cc_app f i ∈ Wdom) ->
  Wsup x f ∈ Wdom.
intros.
apply power_intro; intros.
rewrite Wsup_def in H1; trivial.
destruct H1 as [eqz|(i,tyi,(l&y&ty&eqz))]; rewrite eqz.
 apply couple_intro; trivial.
 apply Nil_typ.

 specialize H0 with (1:=tyi).
 apply power_elim with (2:=ty) in H0. 
 apply couple_intro.
  apply Cons_typ.
  rewrite sup_ax; eauto with *.

  apply fst_typ in H0; rewrite fst_def in H0; trivial.

  apply snd_typ in H0; rewrite snd_def in H0; trivial.
Qed.

(** The type operator on the construction domain *)
Definition Wf X :=
  sup A (fun x => replf (cc_prod (B x) (fun _ => X)) (fun f => Wsup x f)). 

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
intros.
apply H.
apply cc_prod_elim with (1:=tyf); trivial.
Qed.
Hint Resolve Wf_typ.


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

Section TransitiveRecursor.

Variable P : set -> set.
Hypothesis Pm : morph1 P.

Variable F : set -> set -> set.
Hypothesis Fm : Proper (eq_set==>eq_set==>eq_set) F.
Hypothesis f_typ : forall X x recf,
  X ⊆ W ->
  X ⊆ Wf X -> (* allow indirect subterms *)
  x ∈ Wf X ->
  recf ∈ (Π w ∈ X, P w) ->
  F recf x ∈ P x.
Hypothesis Firr : forall X recf recf',
  X ⊆ W ->
  X ⊆ Wf X -> (* allow indirect subterms *)
  (forall x, x ∈ X -> cc_app recf x == cc_app recf' x) ->
  forall x, x ∈ Wf X -> F recf x == F recf' x.

Definition Wsrec_rel' w y :=
  forall Q, Proper (eq_set==>eq_set==>iff) Q ->
  (forall X x recf,
   X ⊆ W ->
   X ⊆ Wf X ->
   x ∈ Wf X ->
   recf ∈ (Π w ∈ X, P w) ->
   (forall w, w ∈ X -> Q w (cc_app recf w)) -> 
   Q x (F recf x)) -> 
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
  Wsrec_rel' x (F recf x).
red; intros.
apply H5 with X; trivial.
intros.
apply H3; trivial.
Qed.

Lemma Wsrec'_rel_elim w y :
  w ∈ W ->
  Wsrec_rel' w y ->
  exists2 X, X ⊆ W /\ X ⊆ Wf X /\ w ∈ Wf X &
  exists2 recf, recf ∈ (Π w ∈ X, P w) &
    y == F recf w /\
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
  apply Wsrec_rel_intro' with X; trivial.
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
    y == F recf (Wsup x f) /\
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
 assert (XinclW : X ⊆ W).
  red; intros.
  apply subset_elim1 in H3; trivial.
 assert (Xtrans : X ⊆ Wf X).
  apply fsub_trans.
  rewrite W_eqn; apply Wf_intro; trivial.
 pose (recf := λ w ∈ X, union (subset (P w) (Wsrec_rel' w))).
 assert (tyf : f ∈ Π _ ∈ B x, X).
  rewrite cc_eta_eq with (1:=H0).
  apply cc_prod_intro; intros; auto with *.
   do 2 red; intros; apply cc_app_morph; auto with *.
  apply fsub_intro; auto.
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
   destruct H1 with (1:=tyi) (2:=sbt).
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
   apply Wf_intro; trivial.

 destruct H2.
  exists (F recf w').
   apply f_typ with X; trivial.
  split; intros.
  apply Wsrec_rel_intro' with (X:=X); intros; trivial.
  assert (tyw0 := H3).
  apply fsub_elim' in H3; trivial.
  destruct H3 as (i,tyi,eqz).
  destruct H1 with (1:=tyi) (2:=eqz).
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
   apply Firr with X; trivial.
   intros.
   assert (x0 ∈ X').
    apply fsub_elim with (y:=w'); trivial.
    rewrite <- H2; trivial.
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

Definition WSREC' w := union (subset (P w) (Wsrec_rel' w)).

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

Lemma WSREC_eqn' x f :
  x ∈ A ->
  f ∈ (Π i ∈ B x, W) ->
  WSREC' (Wsup x f) == F (λ w ∈ W, WSREC' w) (Wsup x f).
intros tya tyf.
assert (Wsrec_rel' (Wsup x f) (WSREC' (Wsup x f))).  
 apply WSREC_ok'.
 rewrite W_eqn; apply Wf_intro; auto.
apply Wsrec'_rel_elim' in H; trivial.
destruct H as (X,(XinclW,(Xtrans,tyf')),(recf,tyrecf,(eqf,?))).
rewrite eqf.
apply Firr with X; auto with *.
2:apply Wf_intro; trivial.
intros.
rewrite cc_beta_eq; auto.
 symmetry.
 apply union_subset_singl with (y':=cc_app recf x0); auto with *.
  apply cc_prod_elim with (1:=tyrecf); trivial.

  intros.
  destruct Wsrec_ex2 with (w:=x0); auto.
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

End TransitiveRecursor.

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

Instance Wsup_morph_gen : Proper ((eq_set==>eq_set)==>eq_set==>eq_set==>eq_set) Wsup.
do 4 red; intros.
unfold Wsup.
apply union2_morph.
 rewrite H0; reflexivity.

 apply sup_morph.
 apply H; rewrite H0; reflexivity.
 red; intros.
 apply replf_morph_raw.
  apply subset_morph.
  rewrite H1,H3; reflexivity.
  red; intros.
  reflexivity.
 red; intros.
 rewrite H3,H4; reflexivity.
Qed.

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
 apply Wsup_morph_gen; trivial.
Qed.

Instance Wdom_morph : Proper (eq_set==>(eq_set==>eq_set)==>eq_set) Wdom.
do 3 red; intros.
unfold Wdom.
apply rel_morph; trivial.
apply List_morph.
apply sup_morph; trivial.
red; intros.
auto.
Qed.

Lemma W_morph : Proper (eq_set==>(eq_set==>eq_set)==>eq_set) W.
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


Lemma WREC_morph_gen :
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
 rewrite H0.
 apply Qm; auto with *.
 apply H2; auto with *.

 apply Qm; auto with *.
Qed.

Lemma WSREC_morph_gen :
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

Lemma WSREC'_morph_gen :
  Proper (eq_set==>(eq_set==>eq_set)==>(eq_set==>eq_set)==>(eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) WSREC'.
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
