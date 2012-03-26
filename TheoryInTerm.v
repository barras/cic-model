Require Export ZFtheory. 
Require Export GenModel.
Require Export ZFcoc.
Require Export ModelZF.
Require Export List.

Module BuildModel := GenModel.MakeModel(CCM).
Import BuildModel.
Import T J R.
Import CCM.
Import ZFind_basic.
Import ZFnats.


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
              (App (lift 2 P) (Succ (Ref 1))))) ->
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
  replace (fun k : nat => V.cons n0 i k) with (V.cons n0 i) in *; 
    trivial.
  refine (let H7 := prod_elim _ _ _ _ _ H6 _ in _).
   do 2 red; intros. apply app_ext; try reflexivity.
    apply int_morph; try reflexivity.
     do 2 red; intros. rewrite H7; reflexivity.
   
   rewrite simpl_int_lift1. apply H5.

  simpl in H7. revert H7. apply in_set_morph; try reflexivity.
  set (fS' := fun n y => app (app fS n) y) in |-*.
   apply app_ext; try reflexivity.
    replace (fun k : nat => V.cons (NATREC f0 fS' n0) 
                                       (V.cons n0 i) k) 
    with (V.cons (NATREC f0 fS' n0) (V.cons n0 i)); trivial.
    rewrite simpl_int_lift. symmetry; apply simpl_int_lift1.

  do 3 red; intros. rewrite H6, H7; reflexivity.
Qed. 

Definition Add : term -> term -> term.
intros m n; left; 
exists (fun i => NATREC (int m i) (fun _ => succ) (int n i)).
do 2 red; intros. 
apply NATREC_morph; try rewrite H; try reflexivity.
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

Definition ind_schema_term : term.
left; exists (fun i => NATREC (i 2) (fun n x => app (app (i 1) n) x) (i 0)).
do 2 red; intros.
apply NATREC_morph; try apply H.
 do 2 red; intros; simpl. apply app_ext; trivial.
  apply app_ext; trivial.
Defined.

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
do 2 rewrite (NATREC_Succ _ _ _ H zero_typ); 
try zero_typ; try apply H.
do 2 rewrite NATREC_0. 
red in H0; simpl in H0; specialize H0 with (1:=H1).
rewrite (NATREC_Succ _ _ _ H H0). reflexivity.
Qed.


(*First order theory signature and Introduction*)

Lemma lift_Somen : forall A n k, A <> None -> 
  lift_rec n k A <> None.
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

Definition EQ_trm : term -> term -> term.
intros x y; left.
exists (fun i => EQ N (int x i) (int y i)).
do 2 red; intros. unfold EQ. 
apply cond_set_morph; try rewrite H; reflexivity.
Defined.

Lemma EQ_trm_typ : forall e x y, typ e (EQ_trm x y) prop.
do 2 red; simpl; intros. unfold props. unfold ZFcoc.props.
rewrite power_ax; intros. 
unfold EQ in H0. unfold cond_set in H0.
rewrite subset_ax in H0.
destruct H0. trivial.
Qed.

Lemma EQ_trm_eq_typ : forall e x y t, typ e t (EQ_trm x y) ->
  eq_typ e x y.
do 2 red; simpl; intros.
do 2 red in H; simpl in H; specialize H with (1:=H0).
replace (fun k : nat => i k) with i in H; trivial.
apply EQ_elim in H. destruct H as (_, (H, _)); trivial.
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

Lemma False_symb_elim : forall e P, 
  (exists t, typ e t False_symb) ->
  (exists t', typ e t' P).
intros. destruct H. exists x. do 2 red; simpl; intros.
do 2 red in H; simpl in H; specialize H with (1:=H0).
elim empty_ax with (1:=H).
Qed.

Definition True_symb : term.
left. exists (fun _ => singl empty).
do 3 red; reflexivity.
Defined.

Lemma True_symb_intro : forall e, exists t, typ e t True_symb.
exists False_symb; do 2 red; simpl; intros.
apply singl_intro.
Qed.

Definition Conj : term -> term ->term.
intros a b; left. 
exists (fun i => let A := int a i in let B := int b i in
  subset (A ∪ B) (fun x => x ∈ A /\ x ∈ B)).
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
intros x y; left. exists (fun i => int x i ∪ int y i).
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
  typ e t (Disj A B) ->
  typ (A::e) t1 (lift 1 C) ->
  typ (B::e) t2 (lift 1 C) ->
  typ e prf_term C.
do 2 red; simpl; intros e t t1 t2 A B C HSC HCP H H1 H2 i HE.
do 2 red in H; simpl in H; specialize H with (1:=HE).
generalize (lift_Some1 _ HSC); intros HSClift1.
apply union2_elim in H; destruct H.
 apply weakening with (A:=A) in HCP. rewrite lift_prop in HCP.
 generalize (proof_irr _ _ _ HSClift1 H1 HCP); intros.
 generalize (vcons_add_var _ _ _ _ HE H); intros.
 do 2 red in H1. 
 specialize H1 with (1:=H3). specialize H0 with (1:=H3).
 case_eq (lift 1 C); intros. 
  rewrite H4 in H1; rewrite <- H4 in H1.
  rewrite H0 in H1; rewrite simpl_int_lift1 in H1.
  case_eq C; intros. 
   rewrite <- H5. exact H1.

   elim HSC; trivial.

  elim HSClift1; trivial.

 apply weakening with (A:=B) in HCP. rewrite lift_prop in HCP.
 generalize (proof_irr _ _ _ HSClift1 H2 HCP); intros.
 generalize (vcons_add_var _ _ _ _ HE H); intros.
 do 2 red in H2. specialize H2 with (1:=H3). 
 specialize H0 with (1:=H3).
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
 rewrite <- H4. rewrite int_subst_eq. 
 apply prod_elim with (2:=H0); trivial.
  do 2 red; intros. rewrite H6; reflexivity.
  
 elim H3; trivial.
Qed.
 
Definition Exst : term -> term.
intro t; left.
exists (fun i => union (replf N (fun n => int t (V.cons n i)))).
do 3 red; intros. apply union_morph. 
apply replf_morph; try reflexivity.
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
generalize (lift_Somen _ 2 0 H); intro Hlift; 
fold (lift 2 C) in Hlift.
apply union_elim in H1; destruct H1.
apply replf_elim in H4. 2 : do 2 red; 
intros u v _ Ht; rewrite Ht; reflexivity.
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

Lemma P_ax_intro1 : forall e, exists t,
  typ e t (Fall (Neg (EQ_trm Zero (Add (Ref 0) (Succ Zero))))).
exists (Abs T 
  (Abs (EQ_trm Zero (Add (Ref 0) (Succ Zero))) prf_term)).
apply Fall_intro.
 intro; simpl in H; discriminate.

 apply Neg_intro. apply Impl_intro.
  intro; simpl in H; discriminate.

  intro; simpl in H; discriminate.

  do 2 red; simpl; intros. unfold val_ok in H.
  assert (nth_error (EQ_trm Zero (Add (Ref 0) (Succ Zero))::T::e) 
    0 = value (EQ_trm Zero (Add (Ref 0) (Succ Zero)))); trivial.
  specialize H with (1:=H0). clear H0. red in H; simpl in H.
  rewrite NATREC_Succ in H.
   rewrite EQ_discr in H. apply empty_ax in H; contradiction.

   do 2 red; intros _ _ _ x1 x2 H1; rewrite H1; reflexivity.

   apply zero_typ.
Qed.

Lemma P_ax_intro2 : forall e, exists t, 
  typ e t (Fall (Fall (Impl
  (EQ_trm (Add (Ref 0) (Succ Zero)) (Add (Ref 1) (Succ Zero)))
  (EQ_trm (Ref 0) (Ref 1))))).
refine (let P1 := (EQ_trm (Add (Ref 0) (Succ Zero)) 
  (Add (Ref 1) (Succ Zero))) in _).
assert (P1 = (EQ_trm (Add (Ref 0) (Succ Zero)) 
  (Add (Ref 1) (Succ Zero)))); auto.
refine (let P2 := (EQ_trm (Ref 0) (Ref 1)) in _).
assert (P2 = (EQ_trm (Ref 0) (Ref 1))); auto.
rewrite <- H. rewrite <- H0. clearbody P1 P2.
exists (Abs T (Abs T (Abs P1 prf_term))).
apply Fall_intro.
 intro; simpl; discriminate.

 apply Fall_intro.
  intro; simpl; discriminate.

  apply Impl_intro. 
   rewrite H; intro; simpl; discriminate.

   rewrite H0; intro; simpl; discriminate.

   do 2 red; intros.
   refine (let i':= V.shift 1 i in _).
   assert (i' = (V.shift 1 i)); auto.
   assert (eq_val i (V.cons (i 0) i')).
    symmetry. apply V.cons_ext; try reflexivity.
   case_eq (lift 1 P2); intros.
    rewrite <- H4. unfold val_ok in H1.
    assert (nth_error (P1::T::T::e) 0 = Some P1); trivial.
    assert (nth_error (P1::T::T::e) 1 = Some T) as H1T; trivial.
    assert (nth_error (P1::T::T::e) 2 = Some T) as H2T; trivial.
    generalize (H1 _ _ H5); intro H0P.
    generalize (H1 _ _ H1T); intro H1N.
    generalize (H1 _ _ H2T); intro H2N.
    assert (forall n, eq_term (lift n T) T) as HlT.
     red; simpl; red; intros; reflexivity.
    rewrite HlT in H1N, H2N. red in H1N, H2N.
    simpl in H1N, H2N. red in H0P; simpl in H0P.
    case_eq (lift 1 P1); intros.
     rewrite H6 in H0P. rewrite <- H6 in H0P.
     simpl. rewrite H3. rewrite simpl_int_lift1.
     rewrite H3 in H0P at 2. rewrite simpl_int_lift1 in H0P.
     rewrite H in H0P; simpl in H0P. rewrite H0; simpl.
     assert (morph2 (fun _ : set => succ)).
      do 3 red; intros. rewrite H8; reflexivity.
     do 2 rewrite (NATREC_Succ _ _ _ H7 zero_typ) in H0P.
     do 2 rewrite NATREC_0 in H0P. simpl in H0P.
     apply EQ_succ_inj with (x0 := i 0); trivial.
    
     rewrite H in H6; simpl in H6; discriminate.

    rewrite H0 in H4; simpl in H4; discriminate.
Qed.

Lemma P_ax_intro3 : forall e , exists t, 
  typ e t (Fall (EQ_trm (Ref 0) (Add (Ref 0) Zero))). 
exists (Abs T prf_term). apply Fall_intro.
 intro; simpl in H; discriminate.

 do 2 red; simpl; intros. rewrite EQ_add_0.
  apply singl_intro.

  unfold val_ok in H. assert (nth_error (T::e) 0 = Some T); trivial.
  specialize H with (1:=H0). red in H; simpl in H. trivial.
Qed.

Lemma P_ax_intro4 : forall e, exists t, 
  typ e t (Fall(Fall (EQ_trm (Add (Add (Ref 0) (Ref 1)) (Succ Zero)) 
                   (Add (Ref 0) (Add (Ref 1) (Succ Zero)))))).
exists (Abs T (Abs T (prf_term))).
apply Fall_intro.
 intro; simpl in H; discriminate.

 apply Fall_intro.
  intro; simpl in H; discriminate.

  do 2 red; intros; simpl. unfold val_ok in H.
  assert (nth_error (T::T::e) 0 = Some T); trivial.
  assert (nth_error (T::T::e) 1 = Some T); trivial.
  rewrite EQ_add_succ.
   apply singl_intro.

   generalize (H _ _ H0); intro H2; simpl in H2; trivial.

   generalize (H _ _ H1); intro H2; simpl in H2; trivial.
Qed.

Lemma P_ax_intro5 : forall e P, P <> None ->
  exists t, typ e t (Impl (subst Zero P)
    (Impl (Fall (Impl P
      (subst (Add (Ref 0) (Succ Zero)) (lift_rec 1 1 P))))
    (Fall P))).
intros e P HNP.
exists (Abs (subst Zero P) (Abs (Fall (Impl (lift_rec 1 1 P)
  ((lift_rec 1 1 (subst (Add (Ref 0) (Succ Zero)) (lift_rec 1 1 P)))))) 
    (Abs T ind_schema_term))).
assert (forall i, eq_val (V.cons (i 0) (V.shift 1 i)) i) as Hcons.
 intros; apply V.cons_ext; reflexivity.
apply Impl_intro.
 apply subst_Some; trivial.
 
 intro; simpl in *; discriminate.
 
 assert (forall x y z, 
   eq_term (lift 1 (Impl (Fall (Impl x y)) z)) 
   (Impl (Fall (Impl (lift_rec 1 1 x)
     (lift_rec 1 1 y))) (lift 1 z))) as Hrewrite.
  red; simpl; red; intros. 
   apply prod_ext.
    apply prod_ext; try reflexivity.
     do 2 red; intros. apply prod_ext; [ | red; intros];
     rewrite int_lift_rec_eq; apply int_morph; try reflexivity;
     rewrite V.cons_lams; [rewrite H, H1 | do 2 red; intros; rewrite H2 
     | rewrite H, H1 | do 2 red; intros xx xy HP; rewrite HP]; reflexivity.

    do 2 red; intros. rewrite H. rewrite V.lams0.
    rewrite <- (Hcons y0). rewrite simpl_int_lift1. reflexivity.

 rewrite Hrewrite. apply Impl_intro.
  intro; simpl in H; discriminate.

  apply lift_Some1. intro; simpl in H; discriminate.

  rewrite <- lift_split.
  assert (forall t n, eq_term (lift n (Fall t)) 
    (Fall (lift_rec n 1 t))) as Hliftin.
   red; simpl; red; intros. apply prod_ext; try reflexivity.
    do 2 red; intros. rewrite int_lift_rec_eq.
    rewrite H1. rewrite H. rewrite V.cons_lams; try reflexivity.
     do 2 red; intros. rewrite H2; reflexivity.
  rewrite Hliftin. apply Fall_intro.
   apply lift_Somen; trivial.

   do 2 red; intros i Hhyp.
   unfold val_ok in Hhyp.
   assert (nth_error (T :: (Fall (Impl (lift_rec 1 1 P)
     (lift_rec 1 1 (subst (Add (Ref 0) (Succ Zero))
     (lift_rec 1 1 P))))) :: (subst Zero P) :: e) 0 =
     value T) as Hind; trivial.
   assert (nth_error (T :: (Fall (Impl (lift_rec 1 1 P)
     (lift_rec 1 1 (subst (Add (Ref 0) (Succ Zero))
     (lift_rec 1 1 P))))) :: (subst Zero P) :: e) 1 =
     value (Fall (Impl (lift_rec 1 1 P)
     (lift_rec 1 1 (subst (Add (Ref 0) (Succ Zero))
     (lift_rec 1 1 P)))))) as Hsucc; trivial.
   assert (nth_error (T :: (Fall (Impl (lift_rec 1 1 P)
     (lift_rec 1 1 (subst (Add (Ref 0) (Succ Zero))
     (lift_rec 1 1 P))))) :: (subst Zero P) :: e) 2 =
     value (subst Zero P)) as Hzero; trivial.
   generalize (Hhyp _ _ Hind); clear Hind; intro Hind; simpl in Hind.
   generalize (Hhyp _ _ Hsucc); clear Hsucc; intro Hsucc; simpl in Hsucc.
   generalize (Hhyp _ _ Hzero); clear Hzero; intro Hzero.
     simpl in Hzero. red in Hzero.
   clear Hrewrite Hhyp Hliftin.

   assert (forall i, eq_val (V.shift 2 (V.shift 1 i)) (V.shift 3 i)) as Hsplit.
    do 2 red; intros i0 a; unfold V.shift; 
    setoid_replace (1 + (2 + a)) with (3 + a) by omega; reflexivity.
   case_eq (lift 3 (subst Zero P)); intros.
    2 : apply lift_Somen in H; [contradiction | apply subst_Some; trivial].

    rewrite H in Hzero; rewrite <- H in Hzero; clear s H.
    rewrite <- (Hcons i) in Hzero at 2. rewrite simpl_int_lift in Hzero.
    rewrite <- (Hcons (V.shift 1 i)) in Hzero. 
    rewrite simpl_int_lift in Hzero. rewrite <- V.shift_split in Hzero.
    rewrite <- (Hcons (V.shift 2 i)) in Hzero. 
    rewrite simpl_int_lift1 in Hzero. rewrite (Hsplit i) in Hzero.
    rewrite int_subst_eq in Hzero; simpl in Hzero.

   assert (forall z i, int (lift_rec 1 1 P) (fun k : nat =>
      V.cons z (V.lams 0 (V.shift 2) (fun k0 : nat => i k0)) k) == 
    int P (V.cons z (V.shift 3 i))) as Haux1.
    intros. replace ((fun k : nat => V.cons z (V.lams 0 (V.shift 2) (fun k0 => 
        i0 k0)) k)) with (V.cons z (V.lams 0 (V.shift 2) i0)); trivial. 
      rewrite int_lift_rec_eq.
      rewrite <- V.cons_lams.
       2 : do 2 red; intros x y H1; rewrite H1; reflexivity.

       do 2 rewrite V.lams0. rewrite (Hsplit i0); reflexivity.
   assert (prod N (fun z : X => prod (int (lift_rec 1 1 P)
    (fun k : nat => V.cons z (V.lams 0 (V.shift 2) (fun k0 : nat => i k0)) k))
     (fun _ : X => int (lift_rec 1 1 (subst (Add (Ref 0) (Succ Zero)) 
      (lift_rec 1 1 P))) (fun k : nat =>
        V.cons z (V.lams 0 (V.shift 2) (fun k0 : nat => i k0)) k))) ==
    prod N (fun z : X => prod (int P (V.cons z (V.shift 3 i))) 
      (fun _ : X => int P (V.cons (succ z) (V.shift 3 i))))) as Haux2.
    apply prod_ext; try reflexivity.
     do 2 red; intros. apply prod_ext.
      rewrite <- H0. apply Haux1.

      do 2 red. intros. rewrite Haux1 in H1.
      replace  (fun k : nat => V.cons y1 (V.lams 0 (V.shift 2) (fun k0 : nat 
        => i k0)) k) with (V.cons y1 (V.lams 0 (V.shift 2) i)); trivial.
      rewrite int_lift_rec_eq. rewrite int_subst_eq.
      rewrite int_lift_rec_eq. rewrite <- V.cons_lams; simpl.
       2 : do 2 red; intros x y H3; rewrite H3; reflexivity.

       rewrite NATREC_Succ. 
        2 : do 3 red; intros _ _ _ m0 n0 Hmn; rewrite Hmn; reflexivity.

        2: apply zero_typ.

       rewrite NATREC_0. rewrite <- H0. rewrite <- V.cons_lams.
        2 : do 2 red; intros m0 n0 Hmn; rewrite Hmn; reflexivity.

        apply int_morph; try reflexivity.
         do 2 red; intros. apply V.cons_morph. 
          rewrite V.lams_bv; try omega.
          rewrite V.lams0. unfold V.cons. reflexivity.

          rewrite V.lams0. 
          replace ((fun k : nat => V.cons y1 (V.lams 0 (V.shift 1) 
          (V.lams 0 (V.shift 2) i)) k)) with (V.cons y1 (V.lams 0 (V.shift 1) 
          (V.lams 0 (V.shift 2) i))); trivial.
          rewrite V.shift_cons. rewrite V.lams0. apply V.shift_split.
    rewrite Haux2 in Hsucc. clear Haux1 Haux2.
         
   case_eq (lift_rec 2 1 P); intros.
    2 : apply lift_Somen in H; [contradiction | trivial].

    rewrite <- H; clear H. simpl. rewrite int_lift_rec_eq.
    rewrite <- (Hcons i) at 3. rewrite <- V.cons_lams.
     2 : do 2 red; intros x y H; rewrite H; reflexivity.
     
     rewrite V.lams0. 
     replace (fun k : nat => V.shift 1 i k) with (V.shift 1 i); trivial.
     rewrite (Hsplit i). elim Hind using N_ind.
      intros. rewrite NATREC_morph.
       rewrite <- H0. apply H1.
     
       reflexivity.

       do 2 red; intros. apply app_ext; trivial.
        apply app_ext; try reflexivity; trivial.

       symmetry; trivial.

     rewrite NATREC_0; trivial.

     intros. rewrite NATREC_Succ; trivial.
      generalize prod_elim; intro Haux.
      specialize Haux with (2:=Hsucc) (3:=H). simpl in Haux.
      assert (eq_fun N
        (fun z : X =>
          prod (int P (V.cons z (V.shift 3 i)))
          (fun _ : X => int P (V.cons (succ z) (V.shift 3 i))))
        (fun z : X =>
          prod (int P (V.cons z (V.shift 3 i)))
          (fun _ : X => int P (V.cons (succ z) (V.shift 3 i))))) as H'.
      red; intros. apply prod_ext; [|do 2 red; intros]; rewrite H2; reflexivity.
      specialize Haux with (1:=H') (2:=Hsucc) (3:=H). clear H' Hsucc.
      generalize prod_elim; intro Haux1.
      assert ( eq_fun (int P (V.cons n (V.shift 3 i)))
        (fun _ : X => int P (V.cons (succ n) (V.shift 3 i)))
        (fun _ : X => int P (V.cons (succ n) (V.shift 3 i)))) as H'.
      red; intros; try reflexivity.
      specialize Haux1 with (1:=H') (2:=Haux) (3:=H0). clear H'. apply Haux1.
    
      do 3 red; intros. apply app_ext; trivial.
       apply app_ext; try reflexivity; trivial.
Qed.


