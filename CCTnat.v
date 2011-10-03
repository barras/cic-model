Require Import Models.
Require Import GenModel.
Require Import ModelZF.
Require Import ZFnats.
Require Import ZFcoc.
Require Import ZF.
Require Import ZFrepl.
Import IZF.

Module BuildModel := GenModel.MakeModel(CCM).
Import BuildModel.
Import T.
Import J.
Import CCM.

Definition T : term.
left; exists (fun _ => N); do 2 red; reflexivity.
Defined.

Definition Zero : term.
left; exists (fun _ => zero); do 2 red; reflexivity.
Defined.

Lemma typ_0 : forall e, typ e Zero T.
do 2 red; simpl; intros e i H; apply zero_typ.
Qed.

Definition Succ : term -> term.
intro n; left; exists (fun i => succ (int n i)). 
do 2 red; intros. rewrite H; reflexivity. 
Defined.

Lemma typ_S : forall e t, typ e t T -> typ e (Succ t) T.
do 2 red; simpl; intros. apply succ_typ.
apply H; apply H0.
Qed.

(*Definition Succ : term.
left; exists (fun _ => lam N succ). 
do 2 red; intros. reflexivity. 
Defined.

Lemma typ_S : forall e t, typ e t T ->
  typ e Succ (Prod T (lift 1 T)).
do 2 red; simpl; intros. apply prod_intro.
 repeat red; intros. rewrite H2. reflexivity.
 
 repeat red; reflexivity.

 apply succ_typ.
Qed.*)


Definition NREC f g n y :=
  forall P, 
  Proper (eq_set ==> eq_set ==> iff) P ->
  P zero f -> (forall m t, P m t -> P (succ m) (g m t)) -> P n y.

Instance NREC_morph : 
  Proper (eq_set ==> (eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set ==> iff) NREC.
repeat red; split; intros.
 unfold NREC; intros. 
 rewrite <- H1; rewrite <- H2; apply H3; auto.
  rewrite H; auto.

  repeat red in H0. 
  intros m t; rewrite (H0 _ _ (reflexivity m) _ _ (reflexivity t)).
  apply H6.

 unfold NREC; intros.
 rewrite H1, H2. apply H3; auto.
 rewrite <- H; auto.
 
 repeat red in H0.
 intros m t; rewrite <- (H0 _ _ (reflexivity m) _ _ (reflexivity t)).
 apply H6.
Qed.

Lemma NREC_inv : forall f g n y,
  n \in N ->
  morph2 g ->
  NREC f g n y ->
  n \in N /\
  NREC f g n y /\
  (n == zero -> y == f) /\
  (forall m, m \in N -> n == succ m -> exists2 z, NREC f g m z & y == g m z).
intros. pattern n, y. apply H1. 
 do 3 red; intros.
 apply and_iff_morphism.
  rewrite H2; reflexivity.
  
  apply and_iff_morphism.
   rewrite H2; rewrite H3; reflexivity.

   apply and_iff_morphism.
    rewrite H3; rewrite H2; reflexivity.

    apply fa_morph; intros. rewrite H2. 
    apply fa_morph; intros. apply fa_morph; intros. 
    apply ex2_morph; red.
     reflexivity.
   
     intros. rewrite H3. reflexivity.

 split; try split; try split; intros.
  apply zero_typ.  

  red; intro; auto.

  reflexivity.

  symmetry in H3; apply discr in H3; contradiction.

 intros; split; try split; try split; intros; destruct H2.
  apply succ_typ; auto.
  
  destruct H3. red; intros. apply H7. apply H3; auto.

  apply discr in H3; contradiction.

  apply succ_inj in H4; auto. exists t; rewrite <- H4.
   destruct H5; assumption.

   reflexivity.
Qed.
   
  
Lemma NREC_choice : forall f g n,
  n \in N ->
  morph2 g ->
  uchoice_pred (NREC f g n).
Proof.
split;try split; intros.
 unfold NREC; intros; rewrite <- H1; apply H2; auto.

 elim H using N_ind; intros.
  destruct H3. exists x.
  unfold NREC; intros; rewrite <- H2; apply H3; auto.

  exists f. unfold NREC; auto.
  
  destruct H2. exists (g n0 x). 
  red; intros. apply H5. apply H2; auto.

 revert x x' H1 H2. elim H using N_ind; intros.
  apply H3.
   red; intros; rewrite H2; apply H4; auto.
   
   red; intros; rewrite H2; apply H5; auto.
   
   apply (NREC_inv _ _ _ _ zero_typ) in H1; trivial.
   apply (NREC_inv _ _ _ _ zero_typ) in H2; trivial.
   destruct H1 as (?, (?, (?, ?))). rewrite (H4 (reflexivity zero)).
   destruct H2 as (?, (?, (?, ?))). rewrite (H7 (reflexivity zero)).
   reflexivity.
   
   apply (NREC_inv _ _ _ _ (succ_typ _ H1)) in H3; trivial.
   apply (NREC_inv _ _ _ _ (succ_typ _ H1)) in H4; trivial.
   destruct H3 as (?, (?, (?, ?))). 
   destruct (H7 n0 H1 (reflexivity (succ n0))). rewrite H9. 
   destruct H4 as (?, (?, (?, ?))). 
   destruct (H12 n0 H1 (reflexivity (succ n0))). rewrite H14.
   apply H0. reflexivity. auto.
Qed.

Lemma uchoice_NREC_0 : forall f g, uchoice_pred (NREC f g zero).
split; try split; intros.
 unfold NREC; intros. rewrite <- H. apply H0; auto.
 
 exists f. unfold NREC; intros; auto.

 cut (zero == zero); try reflexivity.
  pattern zero at 2, x'; apply H0; intros.
   repeat red; intros. rewrite H1. rewrite H2. auto.

   revert H1; pattern zero at 2, x; apply H; intros.
    repeat red; intros. rewrite H1, H2. auto.

    reflexivity.

    symmetry in H2. apply discr in H2; contradiction.

    symmetry in H2. apply discr in H2; contradiction.
Qed.

  

Definition NATREC f g n := uchoice (NREC f g n).

Instance NATREC_morph : 
  Proper (eq_set ==> (eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) NATREC.
repeat red; intros. unfold NATREC, NREC; intros. 
apply uchoice_morph_raw; repeat red; intros.
apply fa_morph; intros. 
apply fa_morph; intros. rewrite H.
apply fa_morph; intros. split; intros.
 rewrite <- H2. rewrite <- H1. apply H3. intros. 
 setoid_replace (x0 m t) with (y0 m t). 
  auto. 
  apply H0; reflexivity.

 rewrite H2. rewrite H1. apply H3. intros.
 setoid_replace (y0 m t) with (x0 m t).
  auto.
  symmetry. apply H0; reflexivity.
Qed.

Lemma NATREC_0 : forall f g, NATREC f g zero == f.
unfold NATREC; intros.
symmetry. apply uchoice_ext. 
 apply uchoice_NREC_0.
 
 unfold NREC; intros; auto.
Qed.

Lemma NATREC_Succ : forall f g n, morph2 g -> n \in N ->
  NATREC f g (succ n) == g n (NATREC f g n).
intros. elim H0 using N_ind; intros.
 rewrite <- H2; auto.
 
 rewrite NATREC_0. unfold NATREC. symmetry. apply uchoice_ext.
 apply NREC_choice. 
  apply succ_typ; apply zero_typ.
  assumption.

  unfold NREC; intros. apply H3; assumption.

 rewrite H2. unfold NATREC at 1. symmetry. apply uchoice_ext.
  apply NREC_choice; trivial. repeat apply succ_typ; auto.
  
  repeat red; intros. apply H5. apply H5.
  revert P H3 H4 H5. change (NREC f g n0 (NATREC f g n0)).
  unfold NATREC; apply uchoice_def. apply NREC_choice; auto.
Qed.

Definition NatRec (f g n:term) : term.
left; exists (fun i => NATREC (int f i) 
  (fun m t => app (app (int g i) m) t) (int n i)).
repeat red; intros. apply NATREC_morph. 
 rewrite H; reflexivity.
 
 repeat red; intros. rewrite H, H0, H1. reflexivity.

 rewrite H; reflexivity.
Defined.
   

Lemma typ_Nrect : forall e n f g P,
  typ e n T ->
  typ e P (Prod T kind) -> 
  typ e f (App P Zero) ->
  typ e g (Prod T (Prod (App (lift 1 P) (Ref 0))
              (App (lift 2 P) ( Succ (Ref 1))))) ->
  typ e (NatRec f g n) (App P n).
do 2 red. simpl. intros.
red in H; specialize H with (1:=H3).
red in H0; specialize H0 with (1:=H3).
red in H1; specialize H1 with (1:=H3).
red in H2; specialize H2 with (1:=H3).
simpl in *.
replace (fun k0 : nat => i k0) with i in *; trivial.
set (c := int n i) in *; clearbody c.
set (f0 := int f i) in *; clearbody f0.
set (fS := int g i) in *; clearbody fS.

elim H using N_ind; intros. 
 revert H6. apply in_set_morph.
  apply NATREC_morph.
   reflexivity.
   do 2 red; intros. rewrite H7. rewrite H6. reflexivity.
   symmetry; assumption.
  rewrite H5; reflexivity.

 rewrite NATREC_0. apply H1.
 
 rewrite NATREC_Succ; auto.
  refine (let H6 := prod_elim _ _ _ _ _ H2 H4 in _).
   red; intros. apply prod_ext.
    apply app_ext; try assumption.
     apply int_morph; try reflexivity.
      do 2 red; intros. rewrite H7; reflexivity.
   
    red; intros. apply app_ext.
     apply int_morph; try reflexivity.
      do 2 red; intros. apply V.cons_morph; try assumption.
       do 2 red; intros. rewrite H7; reflexivity.

     rewrite H7; reflexivity.

  simpl in H6. clear H2. 
  replace (fun k : nat => V.cons n0 i k) with (V.cons n0 i) in *; trivial.
  refine (let H7 := prod_elim _ _ _ _ _ H6 _ in _).
   do 2 red; intros. apply app_ext; try reflexivity.
    apply int_morph; try reflexivity.
     do 2 red; intros. rewrite H7; reflexivity.
   
   rewrite simpl_int_lift1. apply H5.

  simpl in H7. revert H7. apply in_set_morph; try reflexivity.
  set (fS' := fun n y :set => app (app fS n) y) in |-*.
   apply app_ext; try reflexivity.
    replace (fun k : nat => V.cons (NATREC f0 fS' n0) (V.cons n0 i) k) 
    with (V.cons (NATREC f0 fS' n0) (V.cons n0 i)); trivial.
    rewrite simpl_int_lift. symmetry; apply simpl_int_lift1.

  do 3 red; intros. rewrite H6, H7; reflexivity.
Qed. 

Definition Add : term -> term -> term.
intros m n; left; exists (fun i => NATREC (int m i) (fun _ => succ) (int n i)).
do 2 red; intros. apply NATREC_morph; try rewrite H; try reflexivity.
 do 2 red; intros. rewrite H1; reflexivity.
Defined.

Lemma typ_Add : forall e m n, typ e m T -> typ e n T -> 
  typ e (Add m n) T.
Proof.
do 2 red; simpl; intros.
replace (fun k : nat => i k) with i; trivial.
do 2 red in H0; simpl in H0; specialize H0 with (1:=H1).
do 2 red in H; simpl in H; specialize H with (1:=H1).
elim H0 using N_ind; intros.
 revert H4; apply in_set_morph; try reflexivity.
  apply NATREC_morph; try reflexivity; try symmetry; trivial.
   do 2 red; intros; rewrite H5; reflexivity.
   
 rewrite NATREC_0; trivial.

 rewrite NATREC_Succ; trivial.
  apply succ_typ; trivial.
    
  do 3 red; intros. rewrite H5; reflexivity.
Qed.

(*Definition Add : term.
left; exists (fun i => lam N (fun m => lam N (fun n => NATREC m (fun _ => succ) n))).
do 2 red; intros. apply lam_ext; try reflexivity.
 do 2 red; intros. apply lam_ext; try reflexivity.
  do 2 red; intros. apply NATREC_morph; trivial.
   do 2 red; intros. rewrite H5; reflexivity.
Defined.

Lemma typ_Add : forall e, typ e Add (Prod T (Prod (lift 1 T) (lift 2 T))).
Proof.
do 2 red; simpl; intros.
apply prod_intro.
 do 2 red; intros; apply lam_ext; try reflexivity.
  do 2 red; intros. apply NATREC_morph; trivial.
   do 2 red; intros. rewrite H5; reflexivity.

 do 2 red; intros; try reflexivity.

 intros. apply prod_intro.
  do 2 red; intros; try reflexivity.
   apply NATREC_morph; try reflexivity; trivial.
    do 2 red; intros; rewrite H4; reflexivity.

  do 2 red; intros; reflexivity.

  intros. elim H1 using N_ind; intros.
   revert H4; apply in_set_morph; try reflexivity.
    apply NATREC_morph; try reflexivity; try symmetry; trivial.
     do 2 red; intros; rewrite H5; reflexivity.
   
   rewrite NATREC_0; trivial.

   rewrite NATREC_Succ; trivial.
    apply succ_typ; trivial.
    
    do 3 red; intros. rewrite H5; reflexivity.

Qed.*)
   

(*Inductive is_clsd_foterm : term -> Prop := 
| const : is_clsd_foterm Zero  
| suc : forall x, is_clsd_foterm x -> is_clsd_foterm (App Succ x).

Lemma clsd_foterm_typ : forall t e, is_clsd_foterm t -> typ e t T.
Proof.
induction 1 as [|t H IH]; do 2 red; simpl; intros i He.
 apply zero_typ.
 
 do 2 red in IH; specialize IH with (1 := He); simpl in *.
 rewrite beta_eq.
  apply succ_typ; apply IH.

  do 2 red; intros. rewrite H1; reflexivity.

  apply IH.
Qed.*)

Inductive is_foterm : term -> Prop :=
| T_var : forall n, is_foterm n
| T_0   : is_foterm Zero
| T_S   : forall n, is_foterm n -> is_foterm (Succ n)
| T_Add : forall m n, is_foterm m -> is_foterm n -> is_foterm (Add m n).

Lemma foterm_typ : forall t e, is_foterm t -> (forall n, typ e n T) -> typ e t T.
Proof.
induction 1 as [ | |t H IH | u v  H1 IH1 H2 IH2]; do 2 red; simpl; intros.
 apply H. apply H0.

 apply zero_typ.

 specialize IH with (1:=H0). 
 do 2 red in IH; specialize IH with (1 := H1); simpl in *.
 apply succ_typ; apply IH.
  
 specialize IH1 with (1:=H).
 specialize IH2 with (1:=H).
 refine (let Hta := typ_Add in _); clearbody Hta.
 specialize Hta with (1:=IH1) (2:=IH2).
 do 2 red in Hta; simpl in Hta; specialize Hta with (1:=H0).
 apply Hta.
Qed.

Lemma discr_term : forall n, ~ eq_term Zero (Add n (Succ Zero)).
red; intros. red in H; simpl in H; red in H.
refine (let v := (fun _ => empty) : val in _); clearbody v. 
assert (eq_val v v); try reflexivity. 
 specialize H with (1:=H0). rewrite NATREC_Succ in H.
  rewrite NATREC_0 in H. symmetry in H; apply discr in H; trivial.

 do 3 red; intros. rewrite H2; reflexivity.

 apply zero_typ.
Qed.

Lemma Succ_inj : forall x y, x <> None -> y <> None ->
 (forall v, int x v \in N /\ int y v \in N) -> 
  eq_term (Succ x) (Succ y) -> eq_term x y.
intros x y HxN HyN H HSucc; destruct x; destruct y; simpl; trivial.
 repeat red in HSucc; repeat red; simpl in *; intros.
 destruct H with (v:=x) as (HNx, _).
 destruct H with (v:=y) as (_, HNy).
 specialize HSucc with (1 := H0); apply succ_inj.
  apply HNx.
  apply HNy.
  apply HSucc.

 elim HyN; reflexivity.
 
 elim HxN; reflexivity.
Qed.

Lemma eq_props_2 : props == succ (succ zero).
unfold props; unfold ZFcoc.props. 
replace prf_trm with empty; trivial.
replace zero with empty; trivial. unfold succ.
assert (union2 empty (singl empty) == singl empty).
 apply eq_intro; intros.
  apply union2_elim in H; destruct H; trivial.
   apply empty_ax in H; contradiction.

   apply union2_intro2; trivial.
rewrite H. 
assert (union2 (singl empty) (singl (singl empty)) == pair empty (singl empty)).
 apply eq_intro; intros.
  apply union2_elim in H0; destruct H0; apply singl_elim in H0; 
   rewrite pair_ax; [left | right]; trivial.
  
 apply pair_elim in H0; destruct H0.
  apply union2_intro1; apply singl_intro_eq; apply H0.

  apply union2_intro2; apply singl_intro_eq; apply H0.
rewrite H0. clear H H0.
symmetry; apply power_ext; intros.
 admit.

 apply pair_elim in H; destruct H; rewrite H in H0; trivial.
  apply empty_ax in H0; contradiction.
Qed.
 
 
 
   
   
   

   
 
Lemma Add_0 : forall n, n <> None -> eq_term (Add n Zero) n.
destruct n; simpl; intros.
 do 2 red; intros; rewrite NATREC_0.
 replace (fun k : nat => x k) with x; trivial.
 destruct s; simpl; rewrite H0; reflexivity.

 apply H; reflexivity.
Qed.

Lemma Add_ass : forall x y, x <> None -> y <> None -> (forall i, int y i \in N) ->
 eq_term (Add (Add x y) (Succ Zero)) (Add x (Add y (Succ Zero))).
simpl; red; intros. 
replace (fun k : nat => x0 k) with x0; trivial.
replace (fun k : nat => y0 k) with y0; trivial.
assert (morph2 (fun _ : set => succ)).
 do 3 red; intros. rewrite H4; reflexivity.
assert (zero \in N). apply zero_typ.
rewrite (NATREC_Succ _ _ _ H3 H4). rewrite NATREC_0.
rewrite (NATREC_Succ _ _ _ H3 H4). rewrite NATREC_0. 
rewrite (NATREC_Succ _ _ _ H3 (H1 y0)).
do 3 red in H3. apply (H3 zero zero (reflexivity zero)).
apply NATREC_morph.
 rewrite H2; reflexivity.

 do 2 red; intros. rewrite H6; reflexivity.

 rewrite H2; reflexivity.
Qed.

Lemma foformula : forall P n, is_foterm n ->
  (forall k i, int k i \in N) ->
  P Zero ->
  (forall m, P m -> P (Succ m)) -> 
  P n. 



 















