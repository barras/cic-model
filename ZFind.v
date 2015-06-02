
Require Import ZF ZFpairs ZFrelations ZFord ZFstable ZFfixfun.

Require ZFind_wnup.
Module W0 := ZFind_wnup.

Section InductiveFamilies.

  (** This file models inductive types of the form [[
  Parameter (m:Type) (Arg A:m->Type) (B:forall i:m, A i -> Type)
            (g:forall (i:m) (x:A i), Arg i -> Prop)
            (j:forall (i:m) (x:A i), B i x -> m)
            (f:forall (i:m) (x:A i) (b:B i x), Arg (j i x b)).
  Inductive W (i:m) (a:Arg i) : Type :=
    W_intro (x:A i) (y:forall b:B i x, W (j i x b) (f i x b))
    (_:g i x a) : W i a.
]] *)
  
  (* inductive index and parameter *)
  Variable m : set.
  (* family index for each inductive *)
  Variable Arg : set -> set.
  (* payload (a.k.a. constructor) *)
  Variable A : set -> set.
  (* subterm index *)
  Variable B : set -> set -> set.
  (* family index populated by a constructor *)
  Variable g : set -> set -> set -> Prop.
  (* inductive index and parameter of a subterm *)
  Variable j : set -> set -> set -> set.
  (* family index of a subterm *)
  Variable f : set -> set -> set -> set.

  Hypothesis Argm : morph1 Arg.
  Hypothesis Am : morph1 A.
  Hypothesis Bm : morph2 B.
  Hypothesis jm : Proper (eq_set==>eq_set==>eq_set==>eq_set) j.
  Hypothesis fm : Proper (eq_set==>eq_set==>eq_set==>eq_set) f.
  Hypothesis gm : Proper (eq_set==>eq_set==>eq_set==>iff) g.

  Hypothesis jtyp : forall i x y,
    i ∈ m ->
    x ∈ A i ->
    y ∈ B i x ->
    j i x y ∈ m.
  
  Hypothesis ftyp : forall i x y,
    i ∈ m ->
    x ∈ A i ->
    y ∈ B i x ->
    f i x y ∈ Arg (j i x y).

  Definition Arg' := Σ i ∈ m, Arg i.
  Definition A' a := subset (A (fst a)) (fun x => g (fst a) x (snd a)).
  Definition B' a x := B (fst a) x.
  Definition f' a x y := couple (j (fst a) x y) (f (fst a) x y).

Instance A'm : morph1 A'.
  do 2 red; intros.
  unfold A'.
  apply subset_morph.
   rewrite H; reflexivity.  

   red; intros.
   rewrite H; reflexivity.
Qed.

Instance B'm : morph2 B'.
  do 3 red; intros.
  unfold B'.
  rewrite H; rewrite H0; reflexivity.
Qed.

Instance f'm : Proper (eq_set ==> eq_set ==> eq_set ==> eq_set) f'.
do 4 red; intros; unfold f'.
rewrite H; rewrite H0; rewrite H1.
reflexivity.
Qed.

Lemma f'typ a x y :
  a ∈ Arg' -> x ∈ A' a -> y ∈ B' a x -> f' a x y ∈ Arg'.
Proof.
  unfold Arg', A', B', f'.
  intros.
  apply subset_elim1 in H0.
  apply fst_typ_sigma in H; trivial.
  apply couple_intro_sigma.  
   do 2 red; intros; apply Argm; trivial.

   apply jtyp; trivial.

   apply ftyp; trivial.
Qed.
Hint Resolve A'm B'm f'm f'typ.
  
  Definition W ia := W0.WW Arg' A' B' f' ia.

  Instance W_morph : morph1 W.
do 2 red; intros.
unfold W, W0.WW.
apply W0.W_morph_all.
5:reflexivity.
4:apply W0.extln_morph.
 unfold W0.Arg'.
 apply TIF_morph_gen; trivial.
 reflexivity.
 2:reflexivity.
 do 2 red; intros. 
 apply union2_morph.
 reflexivity.
 apply sigma_morph.
 apply A'm; trivial.
 red; intros.
 apply sigma_morph.
 apply B'm; trivial.
 red; intros.
 apply H0.
 apply f'm; trivial.

 red; intros.
 unfold W0.A''.
 apply A'm.
 apply W0.Dec_morph; trivial.

 do 2 red; intros.
 apply B'm; trivial.
 apply W0.Dec_morph; trivial.
Qed.

  Lemma W_eqn ia : ia ∈ (Σ i ∈ m, Arg i) -> W ia == W0.W_Fd A' B' f' W ia.
intros.
apply W0.WW_eqn; trivial.
apply f'typ.
  Qed.
  
  Lemma W_intro i a x y :
    i ∈ m ->
    a ∈ Arg i ->
    x ∈ A i ->
    y ∈ (Π b ∈ B i x, W (couple (j i x b) (f i x b))) ->
    g i x a ->
    couple x y ∈ W (couple i a).
intros.
rewrite W_eqn.
apply couple_intro_sigma.
 do 2 red; intros.
 apply cc_prod_ext.
  apply B'm; trivial.
  reflexivity.

  red; intros.
  apply W_morph.
  apply f'm; trivial.
  reflexivity.

unfold A'.
apply subset_intro.
 rewrite fst_def; trivial.
 rewrite fst_def; rewrite snd_def; trivial.

 unfold B', f'.
 revert H2; apply eq_elim.
 apply cc_prod_ext. 
  rewrite fst_def.
  reflexivity.

  red; intros.
  rewrite fst_def.  
  rewrite H4.
  reflexivity.

apply couple_intro_sigma; trivial.
do 2 red; intros.
auto.
Qed.

  Require Import ZFfixrec.

  Section Recursor.

    Hypothesis F : set -> set -> set -> set -> set -> set.
    Hypothesis Fm : Proper (eq_set==>eq_set==>eq_set==>eq_set==>eq_set==>eq_set) F.
    Hypothesis P : set -> set -> set.
    Hypothesis Pm : morph2 P.
    
    Hypothesis Ftyp : forall i a x y recy,
      i ∈ m ->
      a ∈ Arg i ->
      x ∈ A i ->
      y ∈ (Π b ∈ B i x, W (couple (j i x b) (f i x b))) ->
      g i x a ->
      recy ∈ (Π b ∈ B i x, P (couple (j i x b) (f i x b)) (cc_app y b)) ->
      F i a x y recy ∈ P (couple i a) (couple x y).

(* W a ==  W0.Wi (W0.Arg' Arg' A' B' f' a) (W0.A'' A' f' a) 
     (W0.B'' B' f' a) W0.extln
     (W0.W_ord (W0.Arg' Arg' A' B' f' a) (W0.A'' A' f' a) (W0.B'' B' f' a))
*)
    Definition Wi o ia :=
      W0.Wi (W0.Arg' Arg' A' B' f' ia) (W0.A'' A' f' ia) 
            (W0.B'' B' f' ia) W0.extln o ia.
    
    Definition W_ord ia :=
      W0.W_ord (W0.Arg' Arg' A' B' f' ia) (W0.A'' A' f' ia) (W0.B'' B' f' ia).

    Lemma W_o_o : forall i a, i ∈ m -> a ∈ Arg i -> isOrd (W_ord (couple i a)).
intros.
unfold W_ord.
apply W0.W_o_o.      
apply W0.B''_morph.
apply B'm.
Qed.

    Let WF o fct :=
      λ p ∈ (Σ ia ∈ Arg', Wi o ia),
      F (fst (fst p)) (snd (fst p)) (fst (snd p)) (snd (snd p))
        (λ b ∈ B (fst (fst p)) (fst (snd p)),
         cc_app fct
                (couple (couple (j (fst (fst p)) (fst (snd p)) b)
                                (f (fst (fst p)) (fst (snd p)) b))
                        (cc_app (snd (snd p)) b))).
    
    Definition W_REC i a w :=
      cc_app (REC WF (W_ord (couple i a))) (couple (couple i a) w).
(* forall ord : set,
       isOrd ord ->
       forall (T : set -> set) (Q : set -> set -> Prop)
         (F : set -> set -> set),
       recursor ord T Q F ->
       REC F ord == (λ x ∈ T ord, cc_app (F ord (REC F ord)) x)*)

    Let Q o f :=
      forall p, p ∈ (Σ ia ∈ Arg', Wi o ia) -> cc_app f p ∈ P (fst p) (snd p).
    
    Lemma recur o : isOrd o -> recursor o (fun o => Σ ia ∈ Arg', Wi o ia) Q WF.
    Admitted.
    
    Lemma W_REC_typ i a w :
      i ∈ m ->
      a ∈ Arg i ->
      w ∈ W (couple i a) ->
      W_REC i a w ∈ P (couple i a) w.
intros.
unfold W_REC.
assert (REC WF (W_ord (couple i a)) ∈ Π p ∈ (Σ ia ∈ Arg', W ia), P (fst p) (snd p)).
(*apply REC_typ with (X:=fun o => Π p ∈ (Σ ia ∈ Arg', Wi o ia), P (fst p) (snd p)).
*)
admit.
assert (couple (couple i a) w ∈ Σ ia ∈ Arg', W ia).
 apply couple_intro_sigma; trivial.
 do 2 red; intros.
 apply W_morph; trivial.

 apply couple_intro_sigma; auto.
specialize cc_prod_elim with (1:=H2) (2:=H3).
rewrite fst_def; rewrite snd_def.
trivial.

                                                 
Lemma W_REC_eqn i a x y :
  i ∈ m ->
  a ∈ Arg i ->
  x ∈ A i ->
  y ∈ (Π i ∈ B i x, W (couple (j i x y) (f i x y))) ->
  W_REC i a (couple x y) ==
  F i a x y (λ b ∈ B i x, W_REC (j i x b) (f i x b) (cc_app y b)).
intros.
unfold W_REC at 1.
rewrite REC_eqn with (1:=W_o_o _ _ H H0) (2:= recur _ (W_o_o _ _ H H0)).  
rewrite cc_beta_eq.
 unfold WF.
 rewrite cc_beta_eq.

 apply Fm.
 rewrite fst_def,fst_def; reflexivity.
 rewrite fst_def,snd_def; reflexivity.
 rewrite snd_def,fst_def; reflexivity.
 rewrite snd_def,snd_def; reflexivity.
 apply cc_lam_ext.
  rewrite snd_def,!fst_def; reflexivity.
 red; intros.
 unfold W_REC.
 unfold WF.
 apply cc_app_morph.
 admit.
 apply couple_morph.
  rewrite !fst_def, !snd_def, !fst_def.
  rewrite H4; reflexivity.
  apply cc_app_morph; trivial.  
  rewrite !snd_def; reflexivity.
admit.

apply couple_intro_sigma.
admit.
apply couple_intro_sigma; auto.
assert (couple x y ∈ W (couple i a)).
unfold W.
2:unfold Wi,W_ord.
unfold W0.WW.
unfold W0.W.
reflexivity. 

 ass apply REC_typ with .
unfold W_REC.
unfold W in H0.
unfold W0.WW in H0.
unfold W0.W in H0.
unfold W0.Wi in H0.
assert (tmp := W0.W0.WPREC_typ).

W_rect
     : forall P : forall (i : m) (a : Arg i), W i a -> Type,
       (forall (i : m) (a : Arg i) (x : A i)
          (y : forall b : B i x, W (j i x b) (f i x b)),
        (forall b : B i x, P (j i x b) (f i x b) (y b)) ->
        forall g : g i x a, P i a (W_intro i a x y g)) ->
       forall (i : m) (a : Arg i) (w : W i a), P i a w


                                                 Let WF := fun X => sup m (fun i => W0.W_Fd

                                       W0.W0.WPREC = 
fun (A : set) (B : set -> set) (F : set -> set -> set -> set) =>
W0.W0.W_REC A B
  (fun f : set =>
   λ w ∈ W0.W0.W A B,
   F (fst w) (snd w) (λ i ∈ B (fst w), cc_app f (cc_app (snd w) i)))
     : set -> (set -> set) -> (set -> set -> set -> set) -> set
                        
  Definition W_REC :=
    W0.W0.WREC (fun o fct => λ w ∈ TI W_F (osucc o), F (fst w) (snd w) (λ i ∈ B (fst w), cc_app fct (cc_app (snd w) i))).


    WREC (fun o fct => λ w ∈ TI W_F (osucc o), cc_app (F fct) w) W_ord.
  Definition WPREC : set :=
    W_REC (fun f =>
             λ w ∈ W, F (fst w) (snd w) (λ i ∈ B (fst w), cc_app f (cc_app (snd w) i))).
  


                  
  Definition WPREC F w :=
    cc_app (W0.W0.WPREC F) w.

  Lemma WPREC_
  
  Require Import ZFgrothendieck.
  Section UniverseFacts.

    Variable U : set.
    Hypothesis Ugrot : grot_univ U.
    Hypothesis Uinf : omega ∈ U.

    Hypothesis Atyp : forall i, i ∈ m -> A i ∈ U.
    Hypothesis Btyp : forall i x, i ∈ m -> x ∈ A i -> B i x ∈ U.

    Lemma W_typ i a : i ∈ m -> a ∈ Arg i -> W (couple i a) ∈ U.
    Proof.
      intros ityp atyp.
      assert (iatyp : couple i a ∈ Arg').
        apply couple_intro_sigma; auto.
      apply W0.G_WW; trivial.
      apply f'typ.

      intros.
      apply G_subset; trivial.
      apply Atyp.
      apply fst_typ_sigma in H; trivial.

      intros.
      apply Btyp; trivial.
      apply fst_typ_sigma in H; trivial.
      apply subset_elim1 in H0; trivial.
    Qed.

  End UniverseFacts.

End InductiveFamilies.

Section Test.
Let x := (W_eqn, W_typ).
Print Assumptions x.
End Test.
