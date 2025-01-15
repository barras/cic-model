Require Import Setoid Compare_dec Wf_nat.
Require Import Lambda.
Require Import ZF ZFpairs ZFnats ZFord ZFgrothendieck.
Require Import ZFfix.
Require Import Sat.

(** * The set of lambda-terms with constants *)

Module Lam.
Section LambdaTerms.

  (** Set of constants *)
  Variable A : set.

  Definition LAMf (X:set) :=
    prodcart (singl zero) N ∪
    prodcart (singl (succ zero)) A ∪
    (prodcart (singl (succ (succ zero))) (prodcart X X) ∪
     prodcart (singl (succ (succ (succ zero)))) X).

Instance LAMf_mono : Proper (incl_set ==> incl_set) LAMf.
do 2 red; intros.
unfold LAMf.
do 2 apply union2_mono; apply prodcart_mono; auto with *.
apply prodcart_mono; trivial.
Qed.

Instance LAMf_morph : Proper (eq_set ==> eq_set) LAMf.
apply Fmono_morph; apply LAMf_mono.
Qed.

  Hint Resolve LAMf_mono LAMf_morph : core.
  
  Definition Var n := couple zero n.
  Definition Cst x := couple (succ zero) x.
  Definition App a b := couple (succ (succ zero)) (couple a b).
  Definition Abs a := couple (succ (succ (succ zero))) a.

  Lemma LAMf_ind : forall X (P : set -> Prop),
    Proper (eq_set ==> iff) P ->
    (forall n, n ∈ N -> P (Var n)) ->
    (forall x, x ∈ A -> P (Cst x)) ->
    (forall a b, a ∈ X -> b ∈ X -> P (App a b)) ->
    (forall a, a ∈ X -> P (Abs a)) ->
    forall a, a ∈ LAMf X -> P a.
unfold LAMf; intros.
apply union2_elim in H4; destruct H4 as [H4|H4];
 apply union2_elim in H4; destruct H4.
  rewrite surj_pair with (1:=H4).
  rewrite (singl_elim _ _ (fst_typ _ _ _ H4)).
  apply H0.
  apply snd_typ in H4; trivial.

  rewrite surj_pair with (1:=H4).
  rewrite (singl_elim _ _ (fst_typ _ _ _ H4)).
  apply H1.
  apply snd_typ in H4; trivial.

  rewrite surj_pair with (1:=H4).
  rewrite (singl_elim _ _ (fst_typ _ _ _ H4)).
  apply snd_typ in H4.
  rewrite surj_pair with (1:=H4).
  apply H2.
   apply fst_typ in H4; trivial.
   apply snd_typ in H4; trivial.

  rewrite surj_pair with (1:=H4).
  rewrite (singl_elim _ _ (fst_typ _ _ _ H4)).
  apply H3.
  apply snd_typ in H4; trivial.
Qed.

  Lemma Var_typ : forall X n,
    n ∈ N -> Var n ∈ LAMf X.
intros.
unfold Var, LAMf.
apply union2_intro1; apply union2_intro1.
apply couple_intro;[apply singl_intro|trivial].
Qed.

  Lemma Cst_typ : forall X x,
    x ∈ A -> Cst x ∈ LAMf X.
intros.
unfold Cst, LAMf.
apply union2_intro1; apply union2_intro2.
apply couple_intro;[apply singl_intro|trivial].
Qed.

  Lemma App_typ : forall X a b,
    a ∈ X -> b ∈ X -> App a b ∈ LAMf X.
intros.
unfold App, LAMf.
apply union2_intro2; apply union2_intro1.
apply couple_intro;[apply singl_intro|trivial].
apply couple_intro; trivial.
Qed.

  Lemma Abs_typ : forall X a,
    a ∈ X -> Abs a ∈ LAMf X.
intros.
unfold Abs, LAMf.
apply union2_intro2; apply union2_intro2.
apply couple_intro;[apply singl_intro|trivial].
Qed.


  Definition Lambda := TI LAMf omega.

  Lemma Lambda_eqn : Lambda == LAMf Lambda.
apply eq_intro; intros.
*unfold Lambda.
 rewrite <- TI_mono_succ; auto.
 revert H; apply TI_incl; auto.
*elim H using LAMf_ind; intros.
 +do 2 red; intros.
  rewrite H0; reflexivity.
 +apply TI_intro with (osucc zero); auto.
  apply Var_typ; trivial.
 +apply TI_intro with (osucc zero); auto.
  apply Cst_typ; trivial.
 +apply TI_elim in H0; auto.
  destruct H0 as (o1,tyo1,tya).  
  assert (oo1 : isOrd o1) by eauto using isOrd_inv.
  apply TI_elim in H1; auto.
  destruct H1 as (o2,tyo2,tyb).  
  assert (oo2 : isOrd o2) by eauto using isOrd_inv.
  assert (oo : isOrd(osucc (o1 ⊔ o2))) by auto using isOrd_osup2.
  rewrite <- TI_mono_succ in tya,tyb; eauto using isOrd_inv.
  apply TI_intro with (osucc (o1 ⊔ o2)); auto.
   apply osucc_omega.
   apply osup2_lt; trivial.
  apply App_typ; trivial.
  revert tya; apply TI_mono; auto with *.
  apply osucc_mono; auto using isOrd_osup2, osup2_incl1.
  revert tyb; apply TI_mono; auto with *.
  apply osucc_mono; auto using isOrd_osup2, osup2_incl2.
 +apply TI_elim in H0; auto.
  destruct H0 as (o,tyo,tyl).  
  apply TI_intro with (osucc o); auto.
  apply Abs_typ; trivial.
  rewrite TI_mono_succ; auto.
  apply isOrd_inv with omega; trivial.  
Qed.

  Lemma Lambda_ind : forall P : set -> Prop,
    Proper (eq_set ==> iff) P ->
    (forall n, n ∈ N -> P (Var n)) ->
    (forall x, x ∈ A -> P (Cst x)) ->
    (forall a b, a ∈ Lambda -> b ∈ Lambda -> P a -> P b -> P (App a b)) ->
    (forall a, a ∈ Lambda -> P a -> P (Abs a)) ->
    forall a, a ∈ Lambda -> P a.
intros.
revert a H4.
unfold Lambda.
elim isOrd_omega using isOrd_ind; intros.
apply TI_elim in H7; auto.
destruct H7 as (o,oo,tya).
elim tya using LAMf_ind; intros; auto.
*apply H2; eauto.
 revert H7; apply TI_incl; auto.
 revert H8; apply TI_incl; auto.
*apply H3; eauto.
 revert H7; apply TI_incl; auto.
Qed.

  Lemma Var_typ0 : forall n,
    n ∈ N -> Var n ∈ Lambda.
intros.
rewrite Lambda_eqn; apply Var_typ; trivial.
Qed.

  Lemma Cst_typ0 : forall x,
    x ∈ A -> Cst x ∈ Lambda.
intros.
rewrite Lambda_eqn; apply Cst_typ; trivial.
Qed.

  Lemma App_typ0 : forall a b,
    a ∈ Lambda -> b ∈ Lambda -> App a b ∈ Lambda.
intros.
rewrite Lambda_eqn; apply App_typ; trivial.
Qed.

  Lemma Abs_typ0 : forall a,
    a ∈ Lambda -> Abs a ∈ Lambda.
intros.
rewrite Lambda_eqn; apply Abs_typ; trivial.
Qed.

End LambdaTerms.
End Lam.

Import Lam.
Import Lambda.

(** * Pure lambda-terms: no constants *) 
Definition CCLam := Lambda zero.

Fixpoint iLAM (t:term) :=
  match t with
  | Ref n => Lam.Var (nat2set n)
  | Abs M => Lam.Abs (iLAM M)
  | App u v => Lam.App (iLAM u) (iLAM v)
  end.

Lemma iLAM_typ : forall t, iLAM t ∈ CCLam.
  unfold CCLam; induction t; try destruct s; simpl;
  repeat
  (apply Var_typ0 || apply Cst_typ0 || apply App_typ0 || apply Abs_typ0 ||
   (apply succ_intro1; reflexivity) || apply succ_intro2 || apply nat2set_typ);
 trivial.
Qed. 

Ltac inj_pre H :=
  unfold Var, Cst, Lam.App, Lam.Abs in H;
  change (succ (succ (succ zero))) with (nat2set 3) in H;
  change (succ (succ zero)) with (nat2set 2) in H;
  change (succ zero) with (nat2set 1) in H;
  change zero with (nat2set 0) in H.

Ltac inj_lam H :=
  (apply nat2set_inj in H; try discriminate H) ||
  (apply couple_injection in H;
   let H2 := fresh "H" in
   destruct H as (H,H2); inj_lam H; inj_lam H2) ||
  idtac.

Ltac injl H := inj_pre H; inj_lam H.

Lemma iLAM_inj : forall t u,
  iLAM t == iLAM u -> t=u.
fix IH 1.
destruct t; destruct u; simpl;
  intro H; trivial; injl H.
 rewrite H0; trivial.

 rewrite (IH _ _ H0); trivial.

 rewrite (IH _ _ H0); rewrite (IH _ _ H1); trivial.
Qed.

(** Embedding saturated sets in a set *)
Definition iSAT S :=
  subset CCLam (fun x => exists2 t, inSAT t S & x == iLAM t).

Instance iSAT_morph : Proper (eqSAT ==> eq_set) iSAT.
do 2 red; intros.
rewrite eqSAT_def in H.
unfold iSAT.
apply subset_ext; intros.
 apply subset_intro; trivial.
 destruct H1.
 exists x1; trivial.
 rewrite H; trivial.

 apply subset_elim1 in H0; trivial.

 apply subset_elim2 in H0.
 destruct H0.
 destruct H1.
 exists x1; trivial.
 exists x2; trivial.
 rewrite <- H; trivial.
Qed.

Definition complSAT (P:term->Prop) :=
  interSAT (fun p:{S|forall t, sn t -> P t -> inSAT t S} => proj1_sig p).

Definition sSAT x :=
  complSAT (fun t => iLAM t ∈ x).

Instance sSAT_morph : Proper (eq_set ==> eqSAT) sSAT.
do 2 red; intros.
unfold sSAT, complSAT.
apply interSAT_morph_subset; simpl; intros.
 split; intros.
  rewrite <- H in H2; auto.
  rewrite H in H2; auto.

 reflexivity.
Qed.

Lemma iSAT_id : forall S, eqSAT (sSAT (iSAT S)) S.
intros.
rewrite eqSAT_def.
unfold sSAT, complSAT.
intros.
rewrite <- interSAT_ax.
split; intros.
 assert (forall t, sn t -> iLAM t ∈ iSAT S -> inSAT t S).
  intros.
  unfold iSAT in H1.
  rewrite subset_ax in H1.
  destruct H1 as (_,(x,eq_x,(u,inS,eq_u))).
  rewrite eq_u in eq_x; apply iLAM_inj in eq_x.
  rewrite eq_x; trivial.
 exact (H (exist _ S H0)). 

 destruct x; simpl.
 apply i.
  apply sat_sn in H; trivial.

  unfold iSAT.
  apply subset_intro.
   apply iLAM_typ.

   exists t; trivial; reflexivity.

 exists snSAT; intros.
 apply snSAT_intro; trivial.
Qed.

Lemma sSAT_mt : eqSAT (sSAT empty) neuSAT.
unfold sSAT,complSAT.
apply neuSAT_ext.
red; intros.
assert (h : forall t, sn t -> iLAM t ∈ empty -> inSAT t neuSAT).
 intros.
 apply empty_ax in H1; contradiction.
assert (H' := fun h => interSAT_elim H (exist _ neuSAT h));
   clear H; simpl in H'.
auto.
Qed.


Definition SATset :=
  subset (power CCLam) (fun S => iSAT(sSAT S)==S).

Definition replSAT F :=
  replf (power CCLam) (fun P => F (sSAT P)).

Lemma replSAT_ax : forall f z,
  Proper (eqSAT ==> eq_set) f ->
  (z ∈ replSAT f <-> exists A, z == f A).
unfold replSAT.
intros.
rewrite replf_ax.
 split; intros.
  destruct H0 as (y,isSet,img).
  exists (sSAT y); trivial.

  destruct H0 as (S,eqz).
  exists (iSAT S).
   apply power_intro; intros.
   unfold iSAT in H0.
   apply subset_elim1 in H0; trivial.

   rewrite iSAT_id; trivial.

 do 2 red; intros.
 rewrite <- H1; reflexivity.
Qed.

Lemma G_CCLam U :
  grot_univ U ->
  omega ∈ U ->
  CCLam ∈ U.
intros.
assert (U_singl := G_singl _ H).
assert (U_N : ZFnats.N ∈ U).
 apply G_N; trivial.
assert (U_0 : ZFnats.zero ∈ U).
 apply G_inf_nontriv; trivial.
assert (U_succ : forall n, n ∈ U -> ZFnats.succ n ∈ U).
 intros.
 apply G_union2; auto.
unfold CCLam.
unfold Lam.Lambda.
apply G_TI; trivial.
 do 2 red; intros.
 unfold Lam.LAMf.
 rewrite H1; reflexivity.

 intros.
 unfold Lam.LAMf.
 auto 20 using G_union2, G_prodcart.
Qed.
Hint Resolve G_CCLam : core.
