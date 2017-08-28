
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
  
  Definition Wi o ia := W0.Wi Arg' A' B' f' o ia.

  Instance Wi_morph : morph2 Wi.
do 3 red; intros.
apply W0.Wi_morph_all; trivial.
 reflexivity.
 apply A'm.
 apply B'm.
 apply f'm.
Qed.

    Lemma Wi_succ o a : isOrd o -> a ∈ Arg' -> Wi (osucc o) a == W0.W_Fd A' B' f' (Wi o) a. 
unfold Wi, W0.Wi.
intros.
apply TIF_mono_succ; trivial.
 apply W0.W_Fd_morph; auto.

 apply W0.W_Fd_mono; auto.
Qed.

  Lemma Wi_mono o o' ia : isOrd o -> isOrd o' -> o ⊆ o' -> ia ∈ Arg' -> Wi o ia ⊆ Wi o' ia.
unfold Wi, W0.Wi.
intros.
apply TIF_mono; trivial.
 apply W0.W_Fd_morph; auto.

 apply W0.W_Fd_mono; auto.
Qed.

  (** The fixpoint *)
  Definition W ia := W0.W Arg' A' B' f' ia.

  Instance W_morph : morph1 W.
do 2 red; intros.
apply W0.W_morph_all; trivial.
 reflexivity.
 apply A'm.
 apply B'm.
 apply f'm.
Qed.

  Lemma W_post o ia : isOrd o -> ia ∈ Arg' -> Wi o ia ⊆ W ia.
intros.
apply W0.W_post; auto.
Qed.

  (** Closure ordinal of the whole family. May escape the universe of
      A and B. *)
  Definition W_ord := W0.W_ord Arg' A' B'.

  Lemma W_o_o : isOrd W_ord.
apply W0.W_o_o; auto.
Qed.

  Lemma W_def ia : ia ∈ Arg' -> W ia == Wi W_ord ia.
reflexivity.
Qed.

  Lemma W_eqn ia : ia ∈ (Σ i ∈ m, Arg i) -> W ia == W0.W_Fd A' B' f' W ia.
intros.
apply W0.W_eqn; trivial.
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

    Lemma wim1 o : ext_fun Arg' (fun ia : set => Wi o ia).
do 2 red; intros.
apply Wi_morph; auto with *.
Qed.
Hint Resolve wim1.

    Let WF o fct :=
      λ p ∈ (Σ ia ∈ Arg', Wi (osucc o) ia),
      F (fst (fst p)) (snd (fst p)) (fst (snd p)) (snd (snd p))
        (λ b ∈ B (fst (fst p)) (fst (snd p)),
         cc_app fct
                (couple (couple (j (fst (fst p)) (fst (snd p)) b)
                                (f (fst (fst p)) (fst (snd p)) b))
                        (cc_app (snd (snd p)) b))).

    Let WFm1 : Proper (eq_set ==> eq_set ==> eq_set) (fun fct p =>
 F (fst (fst p)) (snd (fst p)) (fst (snd p)) (snd (snd p))
        (λ b ∈ B (fst (fst p)) (fst (snd p)),
         cc_app fct
                (couple (couple (j (fst (fst p)) (fst (snd p)) b)
                                (f (fst (fst p)) (fst (snd p)) b))
                        (cc_app (snd (snd p)) b)))).
do 3 red; intros.
apply Fm.
 rewrite H0; reflexivity.
 rewrite H0; reflexivity.
 rewrite H0; reflexivity.
 rewrite H0; reflexivity.
apply cc_lam_ext.
 rewrite H0; reflexivity.
red; intros.
apply cc_app_morph; trivial.
apply couple_morph.
 apply couple_morph.
  apply jm; trivial.
   rewrite H0; reflexivity.
   rewrite H0; reflexivity.
  apply fm; trivial.
   rewrite H0; reflexivity.
   rewrite H0; reflexivity.
 apply cc_app_morph; trivial.
 rewrite H0; reflexivity.
Qed.

    Let WFm : morph2 WF.
do 3 red; intros.
unfold WF.
apply cc_lam_ext.
 apply sigma_morph; auto with *.
 red; intros.
 rewrite H,H1; reflexivity.
red; intros.
apply WFm1; trivial.
Qed.
    
    Definition W_REC i a w :=
      cc_app (REC WF W_ord ) (couple (couple i a) w).

    Let Q o f :=
      forall p, p ∈ (Σ ia ∈ Arg', Wi o ia) -> cc_app f p ∈ P (fst p) (snd p).
    

Let wi_elim x o :
  isOrd o ->
  x ∈ (Σ ia ∈ Arg', Wi o ia) ->
  x == couple (couple (fst (fst x)) (snd (fst x))) (snd x) /\
  fst (fst x) ∈ m /\
  snd (fst x) ∈ Arg (fst (fst x)) /\
  snd x ∈ Wi o (fst x).
intros.
destruct sigma_elim with (2:=H0) as (x_eta & x1ty & x2ty); auto.
destruct sigma_elim with (2:=x1ty) as (x1_eta & mty & ity); auto.
split; auto.
rewrite <- x1_eta; trivial.
Qed.

Let succ_elim0 x o :
  isOrd o ->
  x ∈ (Σ ia ∈ Arg', Wi (osucc o) ia) ->
  x == couple (couple (fst (fst x)) (snd (fst x))) (couple (fst (snd x)) (snd (snd x))) /\
  fst (fst x) ∈ m /\
  snd (fst x) ∈ Arg (fst (fst x)) /\
  fst (snd x) ∈ A' (fst x) /\
  snd (snd x) ∈ (Π i ∈ B' (fst x) (fst (snd x)), Wi o (f' (fst x) (fst (snd x)) i)).
intros.
destruct wi_elim with (2:=H0) as (x_eta & mty & ity & wty); auto.
rewrite Wi_succ in wty; trivial.
destruct sigma_elim with (2:=wty) as (w_eta & aty & bty); auto.
 do 2 red; intros.
 apply cc_prod_morph.
  rewrite H2; reflexivity.
  red; intros.
  rewrite H2,H3; reflexivity.
split.
 rewrite <- w_eta; trivial.
split; trivial.
split; trivial.
split; trivial.
rewrite x_eta,fst_def.
apply couple_intro_sigma; auto.
Qed.

Let succ_elim x o :
  isOrd o ->
  x ∈ (Σ ia ∈ Arg', Wi (osucc o) ia) ->
  x == couple (couple (fst (fst x)) (snd (fst x))) (couple (fst (snd x)) (snd (snd x))) /\
  fst (fst x) ∈ m /\
  snd (fst x) ∈ Arg (fst (fst x)) /\
  fst (snd x) ∈ A' (fst x) /\
  (forall i, i ∈ B' (fst x) (fst (snd x)) -> cc_app (snd (snd x)) i ∈ Wi o (f' (fst x) (fst (snd x)) i)).
intros.
apply succ_elim0 in H0; trivial.
destruct H0 as (x_eta & mty & ity & aty & bty); auto.
split; trivial.
split; trivial.
split; trivial.
split; trivial.
intros.
apply cc_prod_elim with (1:=bty); trivial.
Qed.

  Lemma Ftyp' o fct x :
    isOrd o ->
    Q o fct ->
    x ∈ (Σ ia ∈ Arg', Wi (osucc o) ia) ->
    F (fst (fst x)) (snd (fst x)) (fst (snd x)) (snd (snd x))
     (λ b ∈ B (fst (fst x)) (fst (snd x)),
      cc_app fct
        (couple
           (couple (j (fst (fst x)) (fst (snd x)) b)
              (f (fst (fst x)) (fst (snd x)) b)) (cc_app (snd (snd x)) b)))
    ∈ P (fst x) (snd x).
intros.
apply succ_elim0 in H1; trivial.
destruct H1 as (x_eta & mty & ity & aty & bty).
apply eq_elim with (P (couple (fst (fst x)) (snd (fst x))) (couple (fst (snd x)) (snd (snd x)))).
 apply Pm.
  rewrite x_eta,!fst_def,snd_def.
  reflexivity.

  rewrite x_eta,!snd_def, fst_def.
  reflexivity.
apply Ftyp; trivial.
 apply subset_elim1 in aty; trivial.

 unfold B' in bty.
 generalize bty; apply cc_prod_covariant.
  do 2 red; intros; apply W_morph.
  rewrite H2; reflexivity.

  reflexivity.

  intros.
  apply W_post; trivial.
  apply couple_intro_sigma; auto.
   apply jtyp; trivial.
   apply subset_elim1 in aty; trivial.

   apply ftyp; trivial.
   apply subset_elim1 in aty; trivial.

 apply subset_elim2 in aty.
 destruct aty as (z, eqz, inst).
 rewrite <- eqz in inst.
 trivial.

 apply cc_prod_intro.
  do 2 red; intros.
  rewrite H2; reflexivity.

  do 2 red; intros.
  rewrite H2; reflexivity.
 intros.
 red in H0.
 generalize (H0 (couple (couple (j (fst (fst x)) (fst (snd x)) x0)
          (f (fst (fst x)) (fst (snd x)) x0)) (cc_app (snd (snd x)) x0))).
 rewrite fst_def.
 rewrite snd_def.
 intro.
 apply H2.
 apply couple_intro_sigma; auto.
  apply couple_intro_sigma; auto.
   apply jtyp; trivial.
   apply subset_elim1 in aty; trivial.

   apply ftyp; trivial.
   apply subset_elim1 in aty; trivial.

  generalize (cc_prod_elim _ _ _ _ bty H1).
  apply eq_elim; apply Wi_morph; auto with *.
  reflexivity.
Qed.

    Lemma recur o : isOrd o -> recursor o (fun o => Σ ia ∈ Arg', Wi o ia) Q WF.
intros.
split; intros.
 do 2 red; intros; apply sigma_morph; auto with *.
 red; intros; apply Wi_morph; auto.

 rewrite <- ZFcont.sigma_cont.
  apply sigma_ext; auto with *.
  intros.
  unfold Wi,W0.Wi; rewrite TIF_eq; trivial.
   apply sup_morph; auto with *.
   red; intros.
   rewrite TIF_mono_succ.
    apply W0.W_Fd_morph; auto with *.
    red; intros; apply TIF_morph; trivial.

    apply W0.W_Fd_morph; auto.
    apply W0.W_Fd_mono; auto.

    rewrite <- H4; trivial.
    apply isOrd_inv with o0; auto.

    rewrite <- H2; trivial.

   apply W0.W_Fd_morph; auto.
   apply W0.W_Fd_mono; auto.

  do 3 red; intros.
  rewrite H1,H2; reflexivity.

 red in H4|-*; intros.
 red in H3.
 rewrite <- H3.
 apply H4.
 revert H5; apply eq_elim; apply sigma_morph; auto with *.
 red; intros.
 apply Wi_morph; auto with *.
 revert H5; apply eq_elim; apply sigma_morph; auto with *.
 red; intros.
 apply Wi_morph; auto with *.

 red; intros.
 red in H3.
 assert (pfst := fst_typ_sigma _ _ _ H4).
 assert (psnd : snd p ∈ Wi o0 (fst p)).
  apply snd_typ_sigma with (3:=reflexivity _) in H4; auto.
 unfold Wi, W0.Wi in psnd.
 apply TIF_elim in psnd; auto.
 destruct psnd as (o',?,?).
 apply H3 with o'; trivial.
 rewrite surj_pair with (1:=subset_elim1 _ _ _  H4).
 apply couple_intro_sigma; auto.
 rewrite Wi_succ; auto.
 apply isOrd_inv with o0; auto.
  apply W0.W_Fd_morph; auto.
  apply W0.W_Fd_mono; auto.

 apply WFm.  

 split.
  apply is_cc_fun_lam.
  do 2 red; intros.
  apply WFm1; auto with *.

  red; intros.
  unfold WF.
  rewrite cc_beta_eq; trivial.
   apply Ftyp' with o0; trivial.

   do 2 red; intros.
   apply WFm1; auto with *.

 red; red; intros.
 unfold WF.
 destruct H2; destruct H3.
 rewrite cc_beta_eq; trivial.
 rewrite cc_beta_eq; trivial.
  apply succ_elim in H5; trivial.
  destruct H5 as (x_eta & mty & ity & aty & bty).
  apply Fm; auto with *.
  apply cc_lam_ext; auto with *.
  red; intros.
  rewrite <- H8.
  apply H4.
   apply couple_intro_sigma; auto.
    apply couple_intro_sigma; auto.
     apply jtyp; auto.
     apply subset_elim1 in aty; trivial.
     apply ftyp; auto.
     apply subset_elim1 in aty; trivial.

    apply bty; trivial.

 do 2 red; intros.
 apply WFm1; auto with *.

 revert H5; apply sigma_mono; auto with *.
 intros.
 rewrite <- H8.
 clearbody Q. (* See BZ#5156. *)
 apply TIF_mono; auto with *.
  apply W0.W_Fd_morph; auto.
  apply W0.W_Fd_mono; auto.
  apply osucc_mono; auto.

 do 2 red; intros.
 apply WFm1; auto with *.
Qed.

    Lemma W_REC_typ i a w :
      i ∈ m ->
      a ∈ Arg i ->
      w ∈ W (couple i a) ->
      W_REC i a w ∈ P (couple i a) w.
intros.
unfold W_REC.
pose (X:=fun o => Π p ∈ (Σ ia ∈ Arg', Wi o ia), P (fst p) (snd p)).
specialize REC_typing with (1:=W_o_o) (2:= recur _ W_o_o).  
unfold Q.
intro.
generalize (H2 (couple (couple i a) w)).
 rewrite fst_def, snd_def; intros.
apply H3.
apply couple_intro_sigma; auto.
 apply couple_intro_sigma; auto.
(*
 rewrite W_def in H1; trivial.
 apply couple_intro_sigma; auto.*)
Qed.
                                                 
Lemma W_REC_eqn i a x y :
  i ∈ m ->
  a ∈ Arg i ->
  x ∈ A i ->
  y ∈ (Π b ∈ B i x, W (couple (j i x b) (f i x b))) ->
  g i x a ->
  W_REC i a (couple x y) ==
  F i a x y (λ b ∈ B i x, W_REC (j i x b) (f i x b) (cc_app y b)).
intros.
assert (tyw : couple (couple i a) (couple x y) ∈ (Σ ia ∈ Arg', Wi W_ord ia)).
 apply couple_intro_sigma; trivial.
  apply couple_intro_sigma; auto.

  apply W_intro; try assumption.
unfold W_REC at 1.
rewrite REC_eqn with (1:=W_o_o) (2:= recur _ W_o_o).  
rewrite cc_beta_eq; trivial.
 unfold WF at 1.
 rewrite cc_beta_eq.

 apply Fm.
 rewrite fst_def,fst_def; reflexivity.
 rewrite fst_def,snd_def; reflexivity.
 rewrite snd_def,fst_def; reflexivity.
 rewrite snd_def,snd_def; reflexivity.
 apply cc_lam_ext.
  rewrite snd_def,!fst_def; reflexivity.
 red; intros.
 rewrite !snd_def,!fst_def.
 rewrite H5.
 reflexivity.

do 2 red; intros.
apply Fm.
 rewrite H5; reflexivity.
 rewrite H5; reflexivity.
 rewrite H5; reflexivity.
 rewrite H5; reflexivity.
apply cc_lam_ext.
 rewrite H5; reflexivity.
red; intros.
apply cc_app_morph.
 reflexivity.
 rewrite H5,H7.
 reflexivity.

revert tyw; apply sigma_mono; auto.
 reflexivity.

 intros.
 unfold Wi,W0.Wi.
 rewrite <- H5.
 apply TIF_incl; trivial.
  apply W0.W_Fd_morph; auto.
  apply W0.W_Fd_mono; auto.

  apply isOrd_succ.
  apply W_o_o.

  apply lt_osucc.
  apply W_o_o.

do 2 red; intros.
rewrite H5; reflexivity.
Qed.

  End Recursor.

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
      apply W0.G_W_big; trivial.
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
Let x := (W_eqn, W_typ, W_REC_typ, W_REC_eqn).
Print Assumptions x.
End Test.
