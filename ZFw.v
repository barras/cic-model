Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFtarski ZFstable.
Require Import ZFgrothendieck.
Require Import ZFcoc.
Require Import ZFord ZFcofix.
Require Import ZFfix.
Require Import ZFfixfun.
Require ZFwdom.

Existing Instance ZFwdom.Wf_mono.
Existing Instance ZFwdom.Wfbot_mono.

Section W.

(* The first parameter of W-types (aka the payload) *)
Variable A : set.
(* The subterm index type *)
Variable B : set -> set.
Hypothesis Bm : morph1 B.

Notation Wdom := (ZFwdom.Wdom A B).
Notation Wf := (ZFwdom.Wf A B).
Notation Wsup := ZFwdom.Wsup.
Notation Wfst := ZFwdom.Wfst.
Notation Wsnd_fun := ZFwdom.Wsnd_fun.

(*******************************************************************************************)
(** * Definition and properties of the W-type operator *)

Section ImpredicativeFixpoint.

  Import ZFtarski.

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
  apply ZFwdom.Wf_mono; trivial.
  rewrite <- W_eqn; reflexivity. 
intros z tyz.
apply subset_intro; auto.
apply ZFwdom.Wf_elim in tyz; [|trivial]; destruct tyz as (x,tyx,(f,tyf,eqz)).
rewrite eqz.
apply H0; trivial.
 revert tyf; apply cc_prod_covariant; auto with *.

 intros.
 apply cc_prod_elim with (2:=H4) in tyf.
 apply subset_elim2 in tyf; destruct tyf as (y,?,?).
 rewrite H5; trivial.
Qed.

Lemma Wfst_typ w :
  w ∈ W ->
  Wfst w ∈ A.
intros tyw.
rewrite W_eqn in tyw; trivial.
apply ZFwdom.Wfst_typ_gen in tyw; trivial.
Qed.

Lemma Wsnd_fun_typ w :
  w ∈ W ->
  Wsnd_fun w ∈ Π __ ∈ B (Wfst w), W.
intros tyw.
rewrite W_eqn in tyw.
apply ZFwdom.Wsnd_fun_typ_gen with (3:=tyw); trivial.
apply W_typ.
Qed.

Lemma Wsnd_fun_def Y x f :
  f ∈ (Π i ∈ Y, W) ->
  Wsnd_fun (Wsup x f) == f.
intros.
apply ZFwdom.Wsnd_fun_def_dom with (A:=A)(B:=B)(Y:=Y); trivial.
revert H; apply cc_prod_covariant; auto with *.
intros.
apply W_typ.
Qed.

(** Adding bottom (for SN) *)
Lemma mt_Wdom : empty ∈ Wdom.
apply power_intro; intros.
apply empty_ax in H; contradiction.
Qed.
Hint Resolve mt_Wdom : core.

Definition Wfbot X := Wf (cc_bot X).

Instance Wfbot_mono : Proper (incl_set ==> incl_set) Wfbot.
unfold Wfbot; do 2 red; intros.
rewrite H; reflexivity.
Qed.

Lemma Wfbot_typ X : X ⊆ Wdom -> Wfbot X ⊆ Wdom.
intros.
apply ZFwdom.Wf_typ; trivial.
red; intros.
apply cc_bot_ax in H0; destruct H0; auto.
rewrite H0; auto.
Qed.

Hint Resolve Wfbot_mono Wfbot_typ : core.

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
  apply ZFwdom.Wf_mono; trivial.
  apply cc_bot_mono; trivial.
  rewrite <- Wbot_eqn; reflexivity. 
intros z tyz.
apply subset_intro; auto.
apply ZFwdom.Wf_elim in tyz; [|trivial];
  destruct tyz as (x,tyx,(f,tyf,eqz)).
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
  
Lemma Wfst_typ_bot w : w ∈ Wbot -> Wfst w ∈ A.
intros.
apply ZFwdom.Wfst_typ_gen with (B:=B)(X:=cc_bot Wbot); trivial.
rewrite Wbot_eqn in H; trivial.
Qed.

Lemma Wsnd_typ_bot w i :
  w ∈ Wbot ->
  i ∈ B (Wfst w) ->
  ZFwdom.Wsnd w i ∈ cc_bot Wbot.
intros.  
apply ZFwdom.Wsnd_typ_gen with (A:=A)(B:=B); trivial.
 apply Wbot_typ'.
 rewrite Wbot_eqn in H; trivial.
Qed.

End ImpredicativeFixpoint.

(*******************************************************************************************)
Section FixpointByIteration.
  
(* Relating W with the iteration of a monotonic operator. We show there exists an ordinal
   for which the sequence reaches the fixpoint W.
   We introduce notion of subterm as an auxiliary tool to defining the recursor. *)

  Lemma Wf_stable : stable_class (fun X => X ⊆ W) Wf.
apply ZFwdom.Wf_stable_gen; trivial.
intros; transitivity W; trivial.
apply W_typ.
Qed.

  Lemma Wf_stable_stages : stable_class (fun X : set => X ⊆ Fstages Wf Wdom) Wf.
apply ZFwdom.Wf_stable_gen; trivial.
intros.
rewrite H.
apply Fstages_inA.
Qed.
Hint Resolve Wf_stable_stages : core.

  Definition W_ord := clos_ord Wf Wdom.

  Lemma W_ord_o : isOrd W_ord.
apply clos_ord_o; auto.
Qed.
Hint Resolve W_ord_o : core.

  Lemma W_ord_clos : closure_ordinal Wf W_ord.
apply closure_ordinal_bounded; auto.
Qed.

Definition Wi := TI Wf.

Lemma Wi_typ o : isOrd o -> Wi o ⊆ Wdom.
intros oo.
apply TI_pre_fix; auto.
apply ZFwdom.Wf_typ; [trivial| reflexivity].
Qed.

Lemma Wi_W o : isOrd o -> Wi o ⊆ W.
intros.
apply TI_pre_fix; auto with *.
rewrite <- W_eqn; reflexivity.
Qed.
  
  Lemma W_post : W ⊆ Wi W_ord.
apply W_least.
rewrite <- TI_mono_succ; auto.
apply W_ord_clos; auto.
Qed.

  Lemma W_clos : W == Wi W_ord.
apply incl_eq.
 red; intros; apply W_post; trivial.

 apply Wi_W; trivial.
Qed.

(** With bottom *)

Lemma Wfbot_stable : stable_class (fun X => X ⊆ Wfbot Wdom) Wfbot.
apply ZFwdom.Wfbot_stable_gen; trivial.
split.
+rewrite H; apply Wfbot_typ; reflexivity.
+intros.
 apply H in H0.
 right; intro eqz; rewrite eqz in H0.
 apply ZFwdom.mt_not_in_Wf in H0; trivial.
Qed.

Hint Resolve Wfbot_mono Wfbot_typ : core.
Lemma Wfbot_stable_stages : stable_class (fun X : set => X ⊆ Fstages Wfbot Wdom) Wfbot.
apply ZFwdom.Wfbot_stable_gen; trivial.
split.
+rewrite H; apply Fstages_inA.
+intros.
 apply H in H0.
 right; intro eqz.
 apply Fstages_def in H0; auto.
 destruct H0 as (o,oo,mt).
 apply ZFwdom.mt_not_in_Wfbot in mt; auto with *.
Qed.
Hint Resolve Wfbot_stable_stages : core.

  Definition Wbot_ord := clos_ord Wfbot Wdom.

  Lemma Wbot_ord_o : isOrd Wbot_ord.
apply clos_ord_o; auto.
Qed.
  Hint Resolve Wbot_ord_o : core.

  Lemma Wbot_ord_clos : closure_ordinal Wfbot Wbot_ord.
apply closure_ordinal_bounded; auto with *.
Qed.

  Definition Wbi := TI Wfbot.

Lemma Wbi_typ o : isOrd o -> Wbi o ⊆ Wdom.
intros oo.
apply TI_pre_fix; auto with *.
Qed.

Lemma Wbi_Wbot o : isOrd o -> Wbi o ⊆ Wbot.
intros.
apply TI_pre_fix; auto with *.
rewrite <- Wbot_eqn; reflexivity.
Qed.
  
  Lemma Wbot_post : Wbot ⊆ Wbi Wbot_ord.
apply Wbot_least.
rewrite <- TI_mono_succ; auto.
apply Wbot_ord_clos; auto.
Qed.

  Lemma Wbot_clos : Wbot == Wbi Wbot_ord.
apply incl_eq.
 red; intros; apply Wbot_post; trivial.

 apply Wbi_Wbot; trivial.
Qed.

  
End FixpointByIteration.



(*******************************************************************************************)
(* Universe facts *)

Section W_Univ.

  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : ZFord.omega ∈ U.  

  Hypothesis aU : A ∈ U.
  Hypothesis bU : forall a, a ∈ A -> B a ∈ U.

  Let Gdom : Wdom ∈ U.
apply ZFwdom.G_Wdom; trivial.
Qed.

  Lemma G_W : W ∈ U.
apply G_incl with Wdom; trivial.
apply W_typ.
Qed.

  Lemma G_Wi o : isOrd o -> Wi o ∈ U.
intros oo.
apply G_incl with Wdom; trivial.
apply Wi_typ; trivial.
Qed.

End W_Univ.


(*******************************************************************************************)
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
 rewrite W_eqn; apply ZFwdom.Wf_intro; trivial.
apply Wrec_rel_elim in H1; trivial.
destruct H1 as (x',tyx',(f',(tyf',eqw),(recf,tyrecf,(eqf,?)))).
apply ZFwdom.Wsup_inj with (A:=A)(B:=B) in eqw; trivial.
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
 rewrite W_eqn; apply ZFwdom.Wf_intro; auto.
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


(*******************************************************************************************)
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
apply ZFwdom.Wf_elim in zw;[|trivial].
destruct zw as (x,tyx,(f,tyf,eqz)).
rewrite eqz; apply ZFwdom.Wf_intro; trivial.
rewrite cc_eta_eq with (1:=tyf).
apply cc_prod_intro; intros.
 do 2 red; intros; apply cc_app_morph; auto with *.
 auto with *.

apply inter_intro; intros.
+assert (z ∈ y).
 {apply inter_elim with (1:=H); trivial. }
 rewrite subset_ax in H1.
 destruct H1 as (yinclW,(y',eqy,(transy,incly))).
 rewrite <- eqy in transy,incly.
 apply transy in H2.
 rewrite eqz in H2.
 apply ZFwdom.Wf_elim in H2; [|trivial].
 destruct H2 as (x',tyx',(f',tyf',eqw)).
 apply ZFwdom.Wsup_inj with (A:=A)(B:=B) in eqw; trivial.
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

+exists W; apply subset_intro.
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

Instance subsets_subtermClass : subtermClass (fun X => X ⊆ Wf X /\ X ⊆ W).
split; intros.
+split.
 {red; intros.
  apply Wf_stable.  
  *apply H0; trivial.
  *apply inter_intro.
   intros.
   rewrite replf_ax in H2; auto.
   destruct H2 as (x,?,?).   
   rewrite H3.
   apply H0; trivial.
   apply inter_elim with (1:=H1); trivial.

   apply inter_non_empty in H1.
   destruct H1 as (w,?,?); exists (Wf w).
   rewrite replf_ax; auto.
   exists w; auto with *. }
 {red; intros.
  destruct inter_non_empty with (1:=H1) as (w,?,?).
  apply (H0 w); trivial. }
+split.
 {apply sup_lub; intros; trivial.
  destruct (H0 y) as (h,_); trivial.
  rewrite h.
  apply ZFwdom.Wf_mono; auto. }
 {apply sup_lub; intros; trivial.
  apply (H0 y); trivial. }
+apply H.
+split;[|reflexivity].
 rewrite <- W_eqn; reflexivity.
+destruct H; split.
 apply ZFwdom.Wf_mono; auto.
 rewrite W_eqn; apply ZFwdom.Wf_mono; auto.
+apply H.
Qed.

(*
Instance Wi_subtermClass : subtermClass (fun X => exists2 o, isOrd o & X==Wi o).
split; intros.
+destruct H as (w,tyw).
 destruct H0 with (1:=tyw) as (o,oo,eqz).
 exists (inter (replf X (fun x => inter (subset (osucc o) (fun o' => x == Wi o'))))).
  apply isOrd_inter; intros.
  rewrite replf_ax in H;[|admit].
  destruct H as (x,tyx,eqy).
  rewrite eqy.
  apply isOrd_inter; intros.
  apply subset_elim1 in H.
  apply isOrd_inv with (osucc o); auto.

  apply incl_eq.
  admit.
  admit.  
+admit.
+destruct H as (o,oo,eqX); rewrite eqX.
 apply Wi_W; trivial.
+apply H.
+split;[|reflexivity].
 rewrite <- W_eqn; reflexivity.
+destruct H; split.
 apply Wf_mono; auto.
 rewrite W_eqn; apply Wf_mono; auto.
+apply H.
Qed.
*)

Variable K : set -> Prop.
Hypothesis Km : Proper (eq_set==>iff) K.
Hypothesis Ksc : subtermClass K.

Hint Resolve KW Ktrans : core.
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
  split; [apply KWtop|].
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

  split; [apply KWtop|].
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
 split ;trivial.
 apply KWtop.
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

 split ;trivial.
 apply KWtop.
 
 intros.
 apply subset_elim2 in H.
 destruct H as (z',eqz,(?,_)).
 rewrite eqz; trivial.
Qed.

Lemma fsub_elim' w x f :
  x ∈ A ->
  f ∈ (Π i ∈ B x, W) ->
  w ∈ fsub (Wsup x f) ->
  exists2 i, i ∈ B x & w ∈ fsub' (cc_app f i).
intros tyx tyf tyw.
pose (X := sup (B x) (fun i => fsub' (cc_app f i))).
assert (w ∈ X).
 apply fsub_elim with (3:=tyw). 
  apply Ksup.
   intros i i' tyi eqi; rewrite eqi; reflexivity.

   intros.
   apply Kfsub'.
   apply cc_prod_elim with (1:=tyf); trivial.

  apply ZFwdom.Wf_intro; trivial.
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
apply ZFwdom.Wf_elim in H; [|trivial].
destruct H as (x,tyx,(f,tyf,eqw)).
rewrite eqw; apply ZFwdom.Wf_intro; trivial.
rewrite cc_eta_eq with (1:=tyf).
apply cc_prod_intro; auto.
 do 2 red; intros; apply cc_app_morph; auto with *.
intros.
apply fsub_intro.
 rewrite W_eqn; apply ZFwdom.Wf_intro; trivial.

 intros.
 apply ZFwdom.Wf_elim' with (5:=H1); auto.
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


(*******************************************************************************************)
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
 rewrite W_eqn; apply ZFwdom.Wf_intro; trivial.
apply Wsrec_rel_elim in H1; trivial.
destruct H1 as (X,(XinclW,tyw'),(recf,tyrecf,(eqy,?))).
apply ZFwdom.Wf_elim in tyw'; [|trivial];
  destruct tyw' as (x',tyx',(f',tyf',eqw)).
apply ZFwdom.Wsup_inj with (A:=A)(B:=B) in eqw; trivial.
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
 assert (tyf : f ∈ Π __ ∈ B x, X).
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
  apply ZFwdom.Wf_intro; trivial.
 split; intros.
  apply Wsrec_rel_intro with (X:=X); intros; trivial.
   apply ZFwdom.Wf_intro; trivial.
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

    apply ZFwdom.Wf_intro; trivial.
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
 rewrite W_eqn; apply ZFwdom.Wf_intro; auto.
apply Wsrec_rel_elim' in H; trivial.
destruct H as (X,(XinclW,tyf'),(recf,tyrecf,(eqf,?))).
rewrite eqf.
apply Firr with X; auto with *.
2:apply ZFwdom.Wf_intro; trivial.
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

(*******************************************************************************************)
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
Hint Resolve Rm Gm : core.

Let Gext x x' f f' :
  x==x' ->
  (forall y y', R y x -> y == y' -> f y == f' y') ->
  G f x == G f' x'.
intros.
unfold G.
apply Fm; [rewrite H;reflexivity| |trivial].
apply cc_lam_ext; auto with *.
rewrite H; reflexivity.
Qed.

     
Definition WSREC' := WFR fsub G.

Global Instance WSREC'_morph0 : morph1 WSREC'.
apply WFR_morph0; auto with *.
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
  rewrite W_eqn; apply ZFwdom.Wf_intro; trivial.
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
Hint Resolve Gext Oacc : core.

Lemma WSREC_eqn0' w :
  w ∈ O ->
  WSREC' w == F (fsub w) (λ w ∈ fsub w, WSREC' w) w.
intros; unfold WSREC' at 1.
apply WFR_eqn; auto with *.
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
generalize H; eapply WFR_ind with (xx:=w); intros; auto with *.
*do 3 red; intros.
 rewrite H0,H1; reflexivity.
*apply f_typ.
 +red; intros.
  apply fsub_elim with (3:=H3); auto.
  apply Ktrans; auto.

 +apply Kfsub; auto.
  apply KW' in H2; trivial.

 +apply fsub_Wf_intro; auto.
  apply KW' in H2; trivial.

 +apply cc_prod_intro; intros.
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
apply ZFwdom.Wf_intro; auto.
Qed.

End TransitiveRecursor.

End W.

#[global]Hint Resolve W_ord_o : core.
#[global]Hint Resolve Wbot_ord_o : core.


Local Notation E := eq_set (only parsing).

Lemma W_ext A A' B B' :
  A == A' ->
  eq_fun A B B' ->
  W A B == W A' B'.
unfold W; intros.
apply FIX_morph_gen.
 apply incl_set_morph.

 apply inter_morph.

 apply ZFwdom.Wdom_ext; trivial.

 apply power_morph.
 apply ZFwdom.Wdom_ext; trivial.

 red; intros.
 apply ZFwdom.Wf_ext; trivial.
Qed.

Instance W_morph : Proper (E==>(E==>E)==>E) W.
do 3 red; intros.
unfold W.
unfold FIX.
apply inter_morph.
apply subset_morph.
 apply subset_morph.
  apply power_morph.
  apply ZFwdom.Wdom_morph; trivial.
 red; intros.
 apply incl_set_morph; auto with *.
 apply ZFwdom.Wdom_morph; auto with *.
red; intros.
unfold post_fix.
apply incl_set_morph; auto with *.
apply ZFwdom.Wf_morph_gen; auto with *.
Qed.

Lemma W_ord_morph : Proper (E==>(E==>E)==>E) W_ord.
do 3 red; intros.
unfold W_ord.  
apply clos_ord_morph.
 red; intros.
 apply ZFwdom.Wf_morph_gen; trivial.

 apply ZFwdom.Wdom_morph; trivial.
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
  rewrite (ZFwdom.Wf_morph_gen _ _ H _ _ H0 _ _ (reflexivity X)); reflexivity.
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
 apply ZFwdom.Wf_ext; auto with *.
Qed.
Instance fsub_morph_gen :
  Proper (E==>(E==>E)==>(E==>iff)==>E==>E) fsub.
do 5 red; intros; unfold fsub.
apply inter_morph; apply subset_morph.
 apply power_morph; apply W_morph; trivial.

 red; intros.
 apply and_iff_morphism; auto with *.
 apply in_set_morph; trivial.
 apply ZFwdom.Wf_morph_gen; auto with *.
Qed.

Instance WSREC'_morph_gen :
  Proper (E==>(E==>E)==>(E==>iff)==>(E==>E==>E==>E)==>E==>E)
  WSREC'.
do 6 red; intros.
unfold WSREC'.
apply WFR_morph; trivial.
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
  apply ZFwdom.Wf_ext; auto with *.

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
 rewrite (ZFwdom.Wf_morph_gen _ _ H _ _ H0 _ _ (reflexivity _)).
 rewrite H1; reflexivity.
Qed.
