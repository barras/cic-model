Require Import LambdaI.
Require Import ZF ZFpairs ZFnats ZFord ZFlambda.
Import IZF.
Require Import SatI.
Require Import Setoid Compare_dec Wf_nat.


Import Lam.
Import LambdaI.

Definition CCLam := Lambda (succ N).

Fixpoint iLAM (t:term) :=
  match t with
  | Ref n => Lam.Var (nat2set n)
  | Abs M => Lam.Abs (iLAM M)
  | App u v => Lam.App (iLAM u) (iLAM v)
  | Int n => Lam.Cst (nat2set n)
  | Ifn c f => Lam.App (Lam.App (Lam.Cst N) (iLAM c)) (iLAM f)
  end.

Lemma iLAM_typ : forall t, iLAM t \in CCLam.
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

 revert H0; destruct t1; simpl; intro H0; injl H0.
 revert H2; destruct t1_1; simpl; intro H2; injl H2.
 generalize (nat2set_typ n); rewrite H4; intro.
 clear IH; admit. (* N \in N absurd *)

 rewrite H0; trivial.

 revert H0; destruct u1; simpl; intro H0; injl H0.
 revert H2; destruct u1_1; simpl; intro H2; injl H2.
 generalize (nat2set_typ n); rewrite <- H4; intro.
 clear IH; admit. (* N \in N absurd *)

 rewrite (IH _ _ H3); rewrite (IH _ _ H1); trivial.
Qed.


Lemma interSAT_ax : forall A F u,
    A ->
    ((forall x:A, inSAT u (F x)) <->
     inSAT u (interSAT F)).
split; intros.
 apply interSAT_intro; auto.
 apply interSAT_elim; trivial.
Qed.


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
  complSAT (fun t => iLAM t \in x).

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
 assert (forall t, sn t -> iLAM t \in iSAT S -> inSAT t S).
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


Definition replSAT F :=
  repl (power CCLam) (fun P y => y == F (sSAT P)).

Lemma replSAT_ax : forall f z,
  Proper (eqSAT ==> eq_set) f ->
  (z \in replSAT f <-> exists A, z == f A).
unfold replSAT.
intros.
rewrite repl_ax.
 split; intros.
  destruct H0 as (y,isSet,(z',eq_z,img)).
  rewrite <- eq_z in img; exists (sSAT y); trivial.

  destruct H0.
  exists (iSAT x).
   apply power_intro; intros.
   unfold iSAT in H1.
   apply subset_elim1 in H1; trivial.

   exists z; try reflexivity.
   rewrite iSAT_id; trivial.

 intros.
 rewrite H1; rewrite H2.
 rewrite H3; reflexivity.
Qed.


 