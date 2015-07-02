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

Section Recursor.

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

End Recursor.

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
