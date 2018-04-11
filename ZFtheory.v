Require Export ZFrepl.
Require Export ZFnats.
Require Export ZFind_basic.


Lemma natrec_typ : forall x y, x ∈ N -> y ∈ N ->
  natrec x (fun _ => succ) y ∈ N.
intros. assert (morph2 (fun _ => succ)).
 do 2 red; intros _ _ _ x1 x2 HEQ; rewrite HEQ; reflexivity.
elim H0 using N_ind; intros.
 rewrite <- (natrec_morph _ _ (reflexivity x) _ _ H1 _ _ H3);
   trivial.

 rewrite natrec_0; trivial.

 rewrite natrec_S; trivial.
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
  EQ N x (natrec x (fun _ => succ) (zero)) == singl empty.
intros x HxN. rewrite natrec_0. apply eq_set_ax; split; intros.
 apply EQ_elim in H. destruct H as (_, (_, H0)); 
 rewrite H0; apply singl_intro.

 apply singl_elim in H; rewrite H; apply refl_typ; trivial.
Qed.

Lemma EQ_add_succ : forall x y, x ∈ N -> y ∈ N ->
  EQ N (natrec (natrec x (fun _ => succ) y) 
         (fun _ => succ ) (succ zero))
       (natrec x (fun _ => succ) 
         (natrec y (fun _ => succ) (succ zero)))  == singl empty.
intros x y HxN HyN. apply eq_set_ax; split; intros.
 apply EQ_elim in H. destruct H as (_, (_, H1)); 
 rewrite H1; apply singl_intro.

 assert (morph2 (fun _ : set => succ)).
  do 2 red; intros _ _ _ x1 x2 Heq; rewrite Heq; reflexivity.
 unfold EQ; rewrite cond_set_ax. split; trivial. split.
  apply natrec_typ; trivial. 
   apply natrec_typ; trivial.

   apply succ_typ; apply zero_typ.
  
 rewrite (natrec_S (natrec x (fun _ : set => succ) y)
  (fun _ : set => succ) _ H0 zero_typ). rewrite natrec_0.
 rewrite (natrec_morph _ _ (reflexivity x) _ _ H0 _ _ 
   (natrec_S _ _ _ H0 zero_typ)).
 rewrite natrec_0. rewrite (natrec_S _ _ _ H0 HyN).
 reflexivity.
Qed.


  

   
   





  
  
   
      
















