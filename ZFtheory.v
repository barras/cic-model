Require Export ZFrepl.
Require Export ZFnats.
Require Export ZFind_basic.


Definition NREC f g n y :=
  forall P, 
  Proper (eq_set ==> eq_set ==> iff) P ->
  P zero f -> (forall m t, P m t -> P (succ m) (g m t)) -> P n y.

Instance NREC_morph : 
  Proper (eq_set ==> (eq_set ==> eq_set ==> eq_set) ==> 
    eq_set ==> eq_set ==> iff) NREC.
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
 intros m t; 
   rewrite <- (H0 _ _ (reflexivity m) _ _ (reflexivity t)).
 apply H6.
Qed.

Lemma NREC_inv : forall f g n y,
  n ∈ N ->
  morph2 g ->
  NREC f g n y ->
  n ∈ N /\
  NREC f g n y /\
  (n == zero -> y == f) /\
  (forall m, m ∈ N -> n == succ m -> 
    exists2 z, NREC f g m z & y == g m z).
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
  n ∈ N ->
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
  Proper (eq_set ==> (eq_set ==> eq_set ==> eq_set) ==> 
    eq_set ==> eq_set) NATREC.
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

Lemma NATREC_Succ : forall f g n, morph2 g -> n ∈ N ->
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

Lemma NATREC_typ : forall x y, x ∈ N -> y ∈ N ->
  NATREC x (fun _ => succ) y ∈ N.
intros. assert (morph2 (fun _ => succ)).
 do 2 red; intros _ _ _ x1 x2 HEQ; rewrite HEQ; reflexivity.
elim H0 using N_ind; intros.
 rewrite <- (NATREC_morph _ _ (reflexivity x) _ _ H1 _ _ H3);
   trivial.

 rewrite NATREC_0; trivial.

 rewrite NATREC_Succ; trivial.
  apply succ_typ; trivial.
Qed.

Lemma EQ_discr : forall x, EQ N zero (succ x) == empty.
intros; apply eq_set_ax; split; intros.
 apply EQ_elim in H. destruct H as (_, (H, _)).
 symmetry in H; apply discr in H; contradiction.

 apply empty_ax in H; contradiction.
Qed.

Lemma EQ_succ_inj : forall x y x0, 
  x ∈ N -> y ∈ N ->
  x0 ∈ (EQ N (succ x) (succ y)) ->
  empty ∈ (EQ N x y).
intros x y x0 HxN HyN H. apply EQ_elim in H. 
destruct H as (_, (H1, _)). 
apply succ_inj in H1; trivial.
rewrite H1. apply refl_typ; trivial.
Qed.

Lemma EQ_add_0 : forall x, x ∈ N ->
  EQ N x (NATREC x (fun _ => succ) (zero)) == singl empty.
intros x HxN. rewrite NATREC_0. apply eq_set_ax; split; intros.
 apply EQ_elim in H. destruct H as (_, (_, H0)); 
 rewrite H0; apply singl_intro.

 apply singl_elim in H; rewrite H; apply refl_typ; trivial.
Qed.

Lemma EQ_add_succ : forall x y, x ∈ N -> y ∈ N ->
  EQ N (NATREC (NATREC x (fun _ => succ) y) 
         (fun _ => succ ) (succ zero))
       (NATREC x (fun _ => succ) 
         (NATREC y (fun _ => succ) (succ zero)))  == singl empty.
intros x y HxN HyN. apply eq_set_ax; split; intros.
 apply EQ_elim in H. destruct H as (_, (_, H1)); 
 rewrite H1; apply singl_intro.

 assert (morph2 (fun _ : set => succ)).
  do 2 red; intros _ _ _ x1 x2 Heq; rewrite Heq; reflexivity.
 unfold EQ; rewrite cond_set_ax. split; trivial. split.
  apply NATREC_typ; trivial. 
   apply NATREC_typ; trivial.

   apply succ_typ; apply zero_typ.
  
 rewrite (NATREC_Succ (NATREC x (fun _ : set => succ) y)
  (fun _ : set => succ) _ H0 zero_typ). rewrite NATREC_0.
 rewrite (NATREC_morph _ _ (reflexivity x) _ _ H0 _ _ 
   (NATREC_Succ _ _ _ H0 zero_typ)).
 rewrite NATREC_0. rewrite (NATREC_Succ _ _ _ H0 HyN).
 reflexivity.
Qed.


  

   
   





  
  
   
      
















