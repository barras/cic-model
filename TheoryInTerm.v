Require Export GenModel.
Require Export ZFcoc.
Require Export ZFtheory. 
Require Export ModelZF.
Require Export List.
Require Export FOTheory.
Import IZF.

Module BuildModel := GenModel.MakeModel(CCM).
Import BuildModel.
Import T J R.
Import CCM.

Definition prf_term : term.
left; exists (fun _ => empty); do 2 red; reflexivity.
Defined.

(*Presburger signature and typing*)

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
  set (fS' := fun n y => app (app fS n) y) in |-*.
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

(*Presburger Axioms*)

Lemma discr_term : forall e n i, val_ok e i ->
  ~ eq_typ e Zero (Add n (Succ Zero)).
red; intros. red in H0; simpl in *.
specialize H0 with (1 := H).
 rewrite NATREC_Succ in H0. rewrite NATREC_0 in H0.
 symmetry in H0; apply discr in H0. trivial.

 do 3 red; intros. rewrite H2; reflexivity.

 apply zero_typ.
Qed.

Lemma Succ_inj : forall e x y, typ e x T -> typ e y T ->
 eq_typ e (Add x (Succ Zero)) (Add y (Succ Zero)) ->
 eq_typ e x y.
red; intros. red in H, H0, H1; simpl in *.
specialize H with (1:=H2).
specialize H0 with (1:=H2).
specialize H1 with (1:=H2).
assert (morph2 (fun _ => succ)).
 do 3 red; intros x0 y0 H3 x1 y1 H4; rewrite H4; reflexivity.
do 2 rewrite NATREC_Succ in H1; try apply zero_typ; try apply H3.
do 2 rewrite NATREC_0 in H1.
apply succ_inj; trivial.
Qed.
 
Lemma Add_0 : forall e n, typ e n T -> eq_typ e (Add n Zero) n.
destruct n; red; intros; simpl; rewrite NATREC_0; reflexivity.
Qed.

Lemma Add_ass : forall e x y, typ e y T ->
 eq_typ e (Add (Add x y) (Succ Zero)) (Add x (Add y (Succ Zero))).
assert (morph2 (fun _ => succ)).
 do 3 red; intros x y H0 x1 y1 H1; rewrite H1; reflexivity.
do 2 red; intros; simpl.
replace (fun k : nat => i k) with i; trivial.
do 2 rewrite (NATREC_Succ _ _ _ H zero_typ); try zero_typ; try apply H.
do 2 rewrite NATREC_0. red in H0; simpl in H0; specialize H0 with (1:=H1).
rewrite (NATREC_Succ _ _ _ H H0). reflexivity.
Qed.


(*First order theory signature and Introduction*)

Lemma lift_Somen : forall A n k, A <> None -> lift_rec n k A <> None.
intros; destruct A.
 destruct s. simpl. red. intros. discriminate.

 elim H. trivial.
Qed.

Lemma lift_Some1 : forall A, A <> None -> lift 1 A <> None.
unfold lift. intros. apply lift_Somen. trivial.
Qed.

Lemma subst_Some : forall t a, t <> None -> subst a t <> None.
unfold subst; intros; destruct t; intro.
 destruct s; simpl in H0. discriminate.

 elim H; trivial.
Qed. 

Lemma proof_irr : forall P p e, P <> None -> 
  typ e p P ->
  typ e P prop -> 
  forall i, val_ok e i -> int p i == prf_trm.
intros.
do 2 red in H0; simpl in H0; specialize H0 with (1:=H2).
do 2 red in H1; simpl in H1; specialize H1 with (1:=H2).
destruct P. 2 : elim H; trivial.
 unfold props in H1. unfold ZFcoc.props in H1.
 rewrite power_ax in H1. specialize H1 with (1:=H0).
 apply singl_elim; trivial.
Qed.

Lemma lift_prop : forall n, eq_term (lift n prop) prop.
simpl; red; reflexivity.
Qed.

Lemma lift_split : forall n t,
 eq_term (lift (S n) t) (lift 1 (lift n t)).
red; intros. destruct t. 
 destruct s; simpl. do 2 red; simpl; intros.
 repeat rewrite V.lams0. rewrite <- V.shift_split. 
 replace (fun k : nat => x0 k) with x0; trivial.
 replace (fun k : nat => y k) with y; trivial. 
 rewrite H; reflexivity.

 simpl; trivial.
Qed.

Definition predicate : (list foterm -> Prop) -> list foterm -> term.
intros P l; left.
exists (fun i => subset (singl empty) (fun _ => P l /\ predicate_stable P)).
do 2 red; intros. apply subset_morph; try reflexivity.
Defined.

Lemma predicate_typ : forall e P l, typ e (predicate P l) prop.
do 2 red; simpl; intros. unfold props. unfold ZFcoc.props.
rewrite power_ax; intros.
rewrite subset_ax in H0.
destruct H0. trivial.
Qed.

Lemma predicate_intro : forall P e l, predicate_stable P ->
  P l -> typ e prf_term (predicate P l).
do 2 red; simpl; intros. apply subset_intro.
 apply singl_intro; trivial.
 
 split; trivial.
Qed.

Definition False_symb : term.
left. exists (fun _ => empty).
do 3 red; reflexivity.
Defined.

Lemma False_symb_intro : ~exists t, typ nil t False_symb.
red; intros H. destruct H; do 2 red in H; simpl in H.
refine (let i:= (fun _ => empty) : val in _); clearbody i.
assert (val_ok nil i). 
 unfold val_ok; intros n t Herror. 
 destruct n; simpl in Herror; discriminate.
specialize H with (1:=H0). apply empty_ax in H; trivial.
Qed.

Lemma False_symb_elim : forall e P, (exists t, typ e t False_symb) ->
  (exists t', typ e t' P).
intros. destruct H. exists x. do 2 red; simpl; intros.
do 2 red in H; simpl in H; specialize H with (1:=H0).
elim empty_ax with (1:=H).
Qed.

Definition True_symb : term.
left. exists (fun _ => singl empty).
do 3 red; reflexivity.
Defined.

Lemma True_symb_intro : exists t, typ nil t True_symb.
exists False_symb; do 2 red; simpl; intros.
apply singl_intro.
Qed.

Definition Conj : term -> term ->term.
intros a b; left. 
exists (fun i => let A := int a i in let B := int b i in
  subset (union2 A B) (fun x => x \in A /\ x \in B)).
do 3 red; intros. apply subset_morph.
 rewrite H; reflexivity.

 split; intros. 
  rewrite <- H; trivial.

  rewrite H; trivial.
Defined.

Lemma Conj_intro : forall e A B t, A <> None -> B <> None ->
  typ e t A /\ typ e t B -> typ e t (Conj A B).
intros e A B t HSA HSB H.
destruct H as (HA, HB); do 2 red; simpl; intros.
 do 2 red in HA, HB; simpl in *.
 specialize HA with (1:=H).
 specialize HB with (1:=H).
 apply subset_intro. 
  destruct A; simpl in *.
   apply union2_intro1; trivial.
   
   elim HSA; reflexivity.

  destruct A; destruct B; simpl in *. 
   split; trivial.

   destruct HSB; reflexivity.

   destruct HSA; reflexivity.

   destruct HSA; reflexivity.
Qed.

Lemma Conj_elim : forall e A B t, A <> None -> B <> None ->
  typ e t (Conj A B) -> typ e t A /\ typ e t B.
intros e A B t HSA HSB; intro H.
 do 2 red in H; simpl in H; split; 
 do 2 red; intros i HE; specialize H with (1:=HE).
  destruct A; simpl in *; trivial.
  apply subset_elim2 in H. destruct H as (x', H0, (H1, _)).
  rewrite H0; trivial.

  destruct B; simpl in *; trivial.
  apply subset_elim2 in H. destruct H as (x', H0, (_, H1)).
  rewrite H0; trivial.
Qed.

Definition Disj : term -> term -> term.
intros x y; left. exists (fun i => union2 (int x i)(int y i)).
do 3 red; intros. rewrite H; reflexivity.
Defined.

Lemma Disj_intro : forall e t A B,  A <> None -> B <> None ->
  typ e t A \/ typ e t B -> typ e t (Disj A B).
intros e t A B HSA HSB H.
 do 2 red; simpl; intros. destruct H; do 2 red in H; 
 specialize H with (1:=H0); destruct A; destruct B; simpl in H.
  apply union2_intro1; trivial.

  destruct HSA; trivial.

  destruct HSB; trivial.

  destruct HSA; trivial.

  destruct HSA; trivial.

  apply union2_intro2; trivial.
  
  destruct HSB; trivial.

  destruct HSA; trivial.

  destruct HSA; trivial.
Qed.

Lemma Disj_elim : forall e t t1 t2 A B C, C <> None -> 
  typ e C prop ->
  typ e A prop ->
  typ e B prop ->
  typ e t (Disj A B) ->
  typ (A::e) t1 (lift 1 C) ->
  typ (B::e) t2 (lift 1 C) ->
  typ e prf_term C.
do 2 red; simpl; intros e t t1 t2 A B C HSC HCP HAP HBP H H1 H2 i HE.
do 2 red in H; simpl in H; specialize H with (1:=HE).
generalize (lift_Some1 _ HSC); intros HSClift1.
apply union2_elim in H; destruct H.
 apply weakening with (A:=A) in HCP. rewrite lift_prop in HCP.
 generalize (proof_irr _ _ _ HSClift1 H1 HCP); intros.
 generalize (vcons_add_var _ _ _ _ HE H); intros.
 do 2 red in H1. specialize H1 with (1:=H3). specialize H0 with (1:=H3).
 case_eq (lift 1 C); intros. rewrite H4 in H1; rewrite <- H4 in H1.
  rewrite H0 in H1; rewrite simpl_int_lift1 in H1.
  case_eq C; intros. 
   rewrite <- H5. exact H1.

   elim HSC; trivial.

  elim HSClift1; trivial.

 apply weakening with (A:=B) in HCP. rewrite lift_prop in HCP.
 generalize (proof_irr _ _ _ HSClift1 H2 HCP); intros.
 generalize (vcons_add_var _ _ _ _ HE H); intros.
 do 2 red in H2. specialize H2 with (1:=H3). specialize H0 with (1:=H3).
 case_eq (lift 1 C); intros. rewrite H4 in H2; rewrite <- H4 in H2.
  rewrite H0 in H2; rewrite simpl_int_lift1 in H2.
  case_eq C; intros. 
   rewrite <- H5. exact H2.

   elim HSC; trivial.

  elim HSClift1; trivial.
Qed.

Definition Impl : term -> term -> term.
intros x y; left.
exists (fun i => prod (int x i) (fun _ => int y i)).
do 3 red; intros. apply prod_ext.
 rewrite H; reflexivity.

 red; intros. rewrite H; reflexivity.
Defined.


Lemma Impl_intro : forall e b A B, A <> None -> B <> None -> 
  typ (A::e) b (lift 1 B) -> typ e (Abs A b) (Impl A B).
do 2 red; simpl; intros. apply prod_intro; intros.
 do 2 red; intros. rewrite H4; reflexivity.

 do 2 red; intros; reflexivity. 

 do 2 red in H1; simpl in H1.
 assert (val_ok (A::e) (V.cons x i)).
  apply vcons_add_var0; trivial.
   red. destruct A.
    apply H3.
    elim H; reflexivity.
 specialize H1 with (1:=H4).
 generalize lift_Some1; intros. specialize H5 with (1:=H0). 
 case_eq (lift 1 B); intros. 
  rewrite H6 in H1.
  rewrite <- H6  in H1. rewrite simpl_int_lift1 in H1.
  apply H1.
 
  rewrite H6 in H5. elim H5; trivial.
Qed.

Lemma Impl_elim : forall e t u A B, 
  A <> None -> B <> None ->
  typ e t (Impl A B) ->
  typ e u A ->
  typ e (App t u) B.
do 2 red; simpl; intros.
do 2 red in H1; simpl in H1; specialize H1 with (1:=H3).
do 2 red in H2; simpl in H2; specialize H2 with (1:=H3).
replace (fun k : nat => i k) with i in *; trivial.
destruct A.
 destruct B.
  apply prod_elim with (2:=H1); trivial.
   do 2 red; intros; reflexivity.

  elim H0; trivial.

 elim H; trivial.
Qed.


Definition Neg t := Impl t False_symb.

Lemma Neg_intro : forall na A e,
  typ e na (Impl A False_symb) ->
  typ e na (Neg A).
intros; unfold Neg; trivial.
Qed.

Lemma Neg_elim : forall na A e,
  typ e na (Neg A) ->
  typ e na (Impl A False_symb).
intros; unfold Neg; trivial.
Qed.
  
Definition Fall : term -> term.
intros t; left.
exists (fun i => prod N (fun z => int t (V.cons z i))).
do 3 red; intros. apply prod_ext; try rewrite H; try reflexivity.
 do 2 red; intros. rewrite H; rewrite H1; reflexivity.
Defined.


Lemma Fall_intro : forall e t B, B <> None ->
  typ (T::e) t B -> 
  typ e (Abs T t) (Fall B).
do 2 red; intros; simpl. apply prod_intro.
 do 2 red; intros. rewrite H3; reflexivity.

 do 2 red; intros. rewrite H3; reflexivity.

 intros.
 replace (fun k : nat => i k) with i; trivial.
 do 2 red in H0. destruct B.
  apply H0. apply vcons_add_var0; trivial.

  elim H; reflexivity.
Qed.

Lemma Fall_elim : forall e t u B, B <> None ->
  typ e t (Fall B) -> 
  typ e u T ->
  typ e (App t u) (subst u B).
do 2 red; simpl; intros.
do 2 red in H0; simpl in H0; intros; specialize H0 with (1:=H2).
do 2 red in H1; simpl in H1; intros; specialize H1 with (1:=H2).
generalize (subst_Some _ u H); intros.
case_eq (subst u B); intros.
 rewrite <- H4. rewrite int_subst_eq. apply prod_elim with (2:=H0); trivial.
  do 2 red; intros. rewrite H6; reflexivity.
  
 elim H3; trivial.
Qed.
 
Definition Exst : term -> term.
intro t; left.
exists (fun i => union (replf N (fun n => int t (V.cons n i)))).
do 3 red; intros. apply union_morph. apply replf_morph; try reflexivity.
 red; intros. rewrite H1; rewrite H. reflexivity.
Defined.


Lemma Exst_intro : forall e t p a, 
  t <> None ->
  typ e a T -> 
  typ e p (subst a t) ->
  typ e p (Exst t).
do 2 red; simpl; intros.
do 2 red in H0. specialize H0 with (1:=H2). simpl in H0.
do 2 red in H1. specialize H1 with (1:=H2). 
generalize subst_Some; intros. specialize H3 with (a:=a) (1:=H).
case_eq (subst a t); intros.
 rewrite H4 in H1. rewrite <- H4 in H1.
 rewrite int_subst_eq in H1.
 apply union_intro with (y:= int t (V.cons (int a i) i)); trivial.
  apply replf_intro with (2:=H0); try reflexivity.
   do 2 red; intros. rewrite H6; reflexivity.

 elim H3; trivial.
Qed.

Lemma strength : forall e t A, A <> None -> 
  typ (T::e) (lift 1 t) (lift 1 A) ->
  typ e t A.
do 2 red; simpl; intros.
generalize (vcons_add_var _ T _ zero H1 zero_typ); intros.
do 2 red in H0; simpl in H0; specialize H0 with (1:=H2).
generalize (lift_Some1 _ H); intros.
case_eq (lift 1 A); intros. 
 rewrite H4 in H0. rewrite <- H4 in H0.
 case_eq A; intros.
  rewrite <- H5. do 2 rewrite simpl_int_lift1 in H0. trivial.

  elim H; trivial.

 elim H3; trivial.
Qed.
 
Lemma Exst_elim : forall e t1 t2 A C, 
  C <> None ->
  typ e C prop -> 
  typ e t1 (Exst A) ->
  typ (A::T::e) t2 (lift 2 C) ->
  typ e prf_term C.
do 2 red; intros.
do 2 red in H1; simpl in H1; specialize H1 with (1:=H3).
apply weakening with (A:=T) in H0.
apply weakening with (A:=A) in H0.
do 2 rewrite <- lift_split in H0. rewrite lift_prop in H0.
generalize (lift_Somen _ 2 0 H); intro Hlift; fold (lift 2 C) in Hlift.
apply union_elim in H1; destruct H1.
apply replf_elim in H4. 2 : do 2 red; intros u v _ Ht; rewrite Ht; reflexivity.
destruct H4. rewrite H5 in H1.
assert (N == int T i). simpl; reflexivity. rewrite H6 in H4.
generalize (vcons_add_var _ _ _ _ H3 H4); intros.
generalize (vcons_add_var _ _ _ _ H7 H1); intros.
generalize (proof_irr _ _ _ Hlift H2 H0 _ H8); intros.
do 2 red in H2; simpl in H2; specialize H2 with (1:=H8).
case_eq (lift 2 C); intros.
 rewrite H10 in H2; rewrite <- H10 in H2.
 rewrite lift_split in H2.
 do 2 rewrite simpl_int_lift1 in H2.
 rewrite H9 in H2.
 case_eq C; intros.
  rewrite <- H11; trivial.
 
  elim H; trivial.

 elim Hlift; trivial.
Qed.


  

 


      
















