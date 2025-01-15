Require Import Inverse_Image.
Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFord.
Require Import ZFgrothendieck.
Require Import ZFlist ZFfixfun.

Section EncodeBigParameter.

Variable A : set.
Variable B : set -> set.
Variable f : set -> set -> set.
Hypothesis Bm : morph1 B.
Hypothesis fm : morph2 f.
Hypothesis ftyp : forall a b,
  a ∈ A ->
  b ∈ B a ->
  f a b ∈ A.

(** Encoding big parameters as (small) paths from a fixed parameter [a].
    First, the type operator. *)
Let L X a := singl empty ∪ Σ b ∈ B a, X (f a b).

Instance Lmorph : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) L.
do 3 red; intros.
apply union2_morph;[reflexivity|].
apply sigma_morph; auto.
red; intros.
apply H; apply fm; trivial.
Qed.
Hint Resolve Lmorph : core.

Lemma L_intro1 X a : empty ∈ L X a.
apply union2_intro1.
apply singl_intro.
Qed.

Lemma L_intro2 a b q X :
  morph1 X ->
  a ∈ A ->
  b ∈ B a ->
  q ∈ X (f a b) ->
  couple b q ∈ L X a.
unfold L; intros.
apply union2_intro2.
apply couple_intro_sigma; trivial.
do 2 red; intros; apply H; apply fm; auto with *.
Qed.

Definition L_match q f g :=
  if_prop (exists b q', q == couple b q') (g (fst q) (snd q)) f.

Lemma Lmatch_aux_morph :
  Proper (eq_set ==> iff) (fun x => exists b q', x == couple b q').
do 2 red; intros.
apply ex_morph; intros b.  
apply ex_morph; intros q'.  
rewrite H; reflexivity.
Qed.

Lemma L_match_mt l f0 g :
  l==empty ->
  L_match l f0 g == f0.
intros; unfold L_match.
apply if_right; trivial.
intros (x,(q,eql)).
rewrite eql in H; apply couple_mt_discr in H; trivial.
Qed.

Lemma L_match_cons l f0 g b q :
  Proper (eq_set==>eq_set==>eq_set) g ->
  l==couple b q ->
  L_match l f0 g == g b q.
intros; unfold L_match.
rewrite if_left.
 rewrite H0,!snd_def,!fst_def; reflexivity.

 exists b;exists q; trivial.
Qed.

Lemma L_elim a q X :
  morph1 X ->
  a ∈ A ->
  q ∈ L X a ->
  q == empty \/
  exists2 b, b ∈ B a &
  exists2 q', q' ∈ X (f a b) &
  q == couple b q'.
intros.
destruct union2_elim with (1:=H1);[left|right].
 apply singl_elim in H2; trivial.

 clear H1.
 apply sigma_elim in H2. 
 2:do 2 red; intros; apply H; apply fm; auto with *.
 destruct H2 as (eqq & tyb & tyq).
 eauto.
Qed.

Lemma Lmono : mono_fam A L.
do 3 red; intros.
destruct L_elim with (3:=H3) as [znil|(b,bty,(q,qty,zcons))]; trivial.
 rewrite znil; apply L_intro1.

 rewrite zcons; apply L_intro2; trivial.
 revert qty; apply H1.
 apply ftyp; auto.
Qed.
Hint Resolve Lmono : core.

(** The fixpoint: paths
    Aenc a == 1 + { b : B a ; l : Aenc (f a b) } *)
Definition Aenc : set -> set := TIF A L omega.

Instance Aenc_morph : morph1 Aenc.
apply TIF_morph; reflexivity.
Qed.

Lemma Aenc_ind P :
  Proper (eq_set ==> eq_set ==> iff) P ->
  (forall a, a ∈ A -> P a empty) ->
  (forall a b q,
   a ∈ A ->
   b ∈ B a ->
   q ∈ Aenc (f a b) ->
   P (f a b) q ->
   P a (couple b q)) ->
  forall a q,
  a ∈ A -> 
  q ∈ Aenc a ->
  P a q.
unfold Aenc; intros.
revert a q H2 H3; elim isOrd_omega using isOrd_ind; intros.
rename y into o.
apply TIF_elim in H6; trivial.
destruct H6 as (o',?,?); trivial.
destruct L_elim with (3:=H7) as [qnil|(b,bty,(q',q'ty,qcons))]; trivial.
 apply TIF_morph; reflexivity.

 rewrite qnil; auto.

 rewrite qcons.
 apply H1; trivial.
  revert q'ty; apply TIF_mono; auto.
  apply isOrd_inv with o; trivial.

  apply H4 with o'; trivial.
  apply ftyp; trivial.
Qed.

Lemma Aenc_eqn a :
  a ∈ A ->
  Aenc a == L Aenc a.
intros.
apply eq_intro; intros.
 apply Aenc_ind with (5:=H0); intros; trivial.
  apply morph_impl_iff2; auto with *.
  do 4 red; intros.
  rewrite <- H2; rewrite <- H1; trivial.

  apply L_intro1.

  apply L_intro2; trivial with *.

 destruct L_elim with (3:=H0) as [qnil|(b,bty,(q,qty,qcons))];
   trivial with *.
  apply TIF_intro with (osucc zero); auto with *.
  rewrite qnil; apply L_intro1.

  apply TIF_elim in qty; auto.
  destruct qty as (o,oo,qty).
  apply TIF_intro with (osucc o); auto.
  rewrite qcons; apply L_intro2; auto.
   apply TIF_morph; reflexivity.

   rewrite TIF_mono_succ; auto.
   eauto using isOrd_inv.
Qed.

Lemma Aenc_intro1 a :
  a ∈ A ->
  empty ∈ Aenc a.
intros.
rewrite Aenc_eqn; trivial.
apply L_intro1.
Qed.

Lemma Aenc_intro2 a b q :
  a ∈ A ->
  b ∈ B a ->
  q ∈ Aenc (f a b) ->
  couple b q ∈ Aenc a.
intros.
rewrite Aenc_eqn; trivial.
apply L_intro2; trivial with *.
Qed.

(** Auxiliary result to build recursive function over an Arg' *)

Definition Aenc_sub q := cond_set (isCouple q) (singl (snd q)).
Definition Aenc_lt q q' := q ∈ Aenc_sub q'.
Definition Aenc_acc q := Acc Aenc_lt q.

Instance Aenc_sub_morph : morph1 Aenc_sub.
do 2 red; intros.
unfold Aenc_sub.
rewrite H; reflexivity.
Qed.

Lemma Aenc_sub_def q q' : q' ∈ Aenc_sub q <-> exists b, q == couple b q'.
unfold Aenc_sub.
rewrite cond_set_ax.
split; intros.
*destruct H.
 exists (fst q). 
 apply singl_elim in H.
 rewrite H.
 assumption.
*destruct H as (b,eqq). 
 rewrite eqq.
 unfold isCouple.
 rewrite fst_def, snd_def.
 split;[|reflexivity].
 apply singl_intro. 
Qed.

Instance Aenc_ltm : Proper (eq_set ==> eq_set ==> iff) Aenc_lt.
do 3 red; intros.
unfold Aenc_lt.
apply in_set_morph; trivial.
apply Aenc_sub_morph; trivial.
Qed.

Instance Aenc_accm : Proper (eq_set ==> iff) Aenc_acc.
do 2 red; intros.
apply wf_morph with (eqA := eq_set); auto with *.
apply Aenc_ltm.
Qed.

Lemma Aenc_wf a q : a ∈ A -> q ∈ Aenc a -> Aenc_acc q.
intros.
pattern a, q; apply Aenc_ind with (a:=a) (q:=q); trivial.
 do 3 red; intros.
 apply Aenc_accm; trivial.

 intros; constructor; intros.
 apply Aenc_sub_def in H2.
 destruct H2 as (b,h).
 symmetry in h; apply couple_mt_discr in h; contradiction.

 intros.
 constructor; intros.
 apply Aenc_sub_def in H5.
 destruct H5 as (b',h).
 apply couple_injection in h; destruct h as (_,h).
 rewrite <- h; trivial.
Qed.

Hint Resolve Aenc_accm Aenc_wf : core.

Section DecodePath.
  
Let F Frec q a :=
    L_match q
            (*q=[]:*)a
            (*q=[x:y:q']:*)(fun b q' => Frec q' (f a b)).

  Definition Dec a(**∈A*) q(**∈Aenc a*) : set(*∈ A*) :=
    ZFrepl.WFR eq_set Aenc_sub F q a.


  Let Fm : Proper ((eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set ==> eq_set) F.
unfold F; do 4 red; intros.
apply if_prop_morph; trivial.
*apply Lmatch_aux_morph; trivial.
*apply H; rewrite H0; [reflexivity|].
 rewrite H1; reflexivity.
Qed.
    
  Let Fext q q' a a' g g' :
    (forall q' q'' b b' : set, Aenc_lt q' q -> q' == q'' -> b == b' -> g q' b == g' q'' b') ->
    q == q' ->
    a == a' ->
    F g q a == F g' q' a'.
unfold F; intros.
apply union2_morph; apply cond_set_morph2; intros; auto with *.
*apply Lmatch_aux_morph; trivial.
*apply H; [|apply snd_morph;trivial|rewrite H0,H1; reflexivity].
 apply Aenc_sub_def.
 destruct H2 as (b & q'' & e).
 exists b.
 rewrite e, snd_def; reflexivity.
*apply impl_morph; [|reflexivity].
 apply Lmatch_aux_morph; trivial.
Qed.

  Hint Resolve Fm Fext : core.
  

  Global Instance Dec_morph : morph2 Dec.
do 3 red; intros.
apply ZFrepl.WFR_morph; auto with *.
apply Aenc_sub_morph.
Qed.

  Lemma Dec_mt a : a ∈ A -> Dec a empty == a.
unfold Dec; intros.
rewrite ZFrepl.WFR_eqn; auto with *.
*unfold F; apply L_match_mt; reflexivity.
*constructor; intros.
 apply Aenc_sub_def in H0. 
 destruct H0 as (b,abs).
 symmetry in abs; apply couple_mt_discr in abs; contradiction.
Qed.


Lemma Dec_cons a b q :
  a ∈ A ->
  b ∈ B a ->
  q ∈ Aenc (f a b) ->
  Dec a (couple b q) == Dec (f a b) q.
intros.
unfold Dec at 1.
rewrite ZFrepl.WFR_eqn; auto with *.
*unfold F; rewrite L_match_cons with (b:=b) (q:=q); [| |reflexivity].
 +apply Dec_morph; auto with *.
 +clear -fm; do 3 red; intros.
  apply ZFrepl.WFR_morph0; auto with *.
  rewrite H; reflexivity.
*apply Aenc_wf with a; trivial.
 apply Aenc_intro2; trivial.
Qed.
End DecodePath.


Lemma Dec_typ a q :
  a ∈ A ->
  q ∈ Aenc a ->
  Dec a q ∈ A.
intros.
apply Aenc_ind with (5:=H0); intros; auto with *.
 do 3 red; intros.
 rewrite H1; rewrite H2; reflexivity.

 rewrite Dec_mt; auto.

 rewrite Dec_cons; auto.
Qed.

(** Extending a path *)

Section ExtendPath.

  Let F b g q :=
    L_match q
             (*q=[]:*)(couple b empty)
             (*q=[x:y:q']:*)(fun b' q' => couple b' (g q')).

  Let Fm : Proper (eq_set==>(eq_set ==> eq_set) ==> eq_set ==> eq_set) F.
unfold F; do 4 red; intros.
apply if_prop_morph; auto with *.
 apply ex_morph; intros b'.
 apply ex_morph; intros q'.
 rewrite H1; reflexivity.

 apply couple_morph; [rewrite H1;reflexivity|].
 apply H0; rewrite H1; reflexivity.

 rewrite H; reflexivity.
Qed.

  Let Fext b b' x x' g g' :
    b == b' ->
    (forall y y', Aenc_lt y x -> y==y' -> g y == g' y') ->
    x == x' ->
    F b g x == F b' g' x'.
unfold F; intros.
apply union2_morph; apply cond_set_morph2; intros; auto with *.
*apply Lmatch_aux_morph; trivial.
*apply couple_morph; [rewrite H1; reflexivity|].
 apply H0; [|rewrite H1; reflexivity].
 apply Aenc_sub_def.
 destruct H2 as (b1,(q1,h)).
 exists b1.
 apply transitivity with (1:=h).
 rewrite h,!snd_def; reflexivity.
*apply impl_morph;[|reflexivity].
 apply Lmatch_aux_morph; trivial.
*rewrite H; reflexivity.
Qed. 
  
  Definition extln q a : set := WFR Aenc_sub (F a) q.

Global Instance extln_morph : Proper (eq_set==>eq_set==>eq_set) extln.
do 3 red; intros.
apply WFR_morph; auto with *.
apply Aenc_sub_morph.
Qed.

Lemma extln_cons a b q b' :
  a ∈ A ->
  b ∈ B a ->
  q ∈ Aenc (f a b) ->
  b' ∈ B (Dec (f a b) q) ->
  extln (couple b q) b' == couple b (extln q b').
intros.
unfold extln at 1.
rewrite WFR_eqn; auto with *.
*apply L_match_cons with (b:=b) (q:=q); auto with *.
 do 3 red; intros.
 apply couple_morph; [trivial|].
 apply WFR_morph; auto with *.
 apply Aenc_sub_morph.
*apply Aenc_wf with a; trivial.
 apply Aenc_intro2; trivial.
Qed.

Lemma extln_nil a b :
  a ∈ A ->
  b ∈ B a ->
  extln empty b == couple b empty.
intros.
unfold extln at 1.
rewrite WFR_eqn; auto with *.
*apply L_match_mt; auto with *.
*apply Aenc_wf with a; trivial.
 eapply Aenc_intro1; trivial.
Qed.

End ExtendPath.

Lemma extln_typ a q b :
  a ∈ A ->
  q ∈ Aenc a ->
  b ∈ B (Dec a q) ->
  extln q b ∈ Aenc a.
intros aty qty; revert b; apply Aenc_ind with (5:=qty); trivial; intros.
 do 3 red; intros.
 apply fa_morph; intros b1.
 rewrite H,H0; reflexivity.

 rewrite Dec_mt in H0; trivial.
 rewrite extln_nil with (a:=a0); trivial.
 apply Aenc_intro2; auto.
 apply Aenc_intro1; trivial.
 apply ftyp; auto.

 rewrite Dec_cons in H3; auto.
 rewrite extln_cons with (a:=a0); auto.
 apply Aenc_intro2; auto.
Qed.

Lemma Dec_extln a p b :
  a ∈ A ->
  p ∈ Aenc a ->
  b ∈ B (Dec a p) ->
  Dec a (extln p b) == f (Dec a p) b.
intros.
revert b H1.
apply Aenc_ind with (4:=H) (5:=H0). 
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
  rewrite <- H1,<- H2 in H4|-*.
  auto.

 intros.
 rewrite Dec_mt in H2|-*; trivial.
 rewrite extln_nil; eauto.
 rewrite Dec_cons; trivial.
  apply Dec_mt; auto.
  apply Aenc_intro1; auto.

 intros.
 rewrite Dec_cons in H5|-*; trivial.
 rewrite extln_cons with (a:=a0); auto.
 rewrite Dec_cons; auto.
 apply extln_typ; auto.
Qed.

Section UniverseFacts.
  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : omega ∈ U.  

  (** We don't assume A is in U... *)
  Hypothesis BU : forall a, a ∈ A -> B a ∈ U.

  (* ... but [Aenc a] is in U *)
  Lemma G_Aenc : forall a, a ∈ A -> Aenc a ∈ U.
unfold Aenc.
elim isOrd_omega using isOrd_ind; intros.
rewrite TIF_eq; auto.
apply G_sup; trivial.
*do 2 red; intros.
 apply Lmorph; [|reflexivity].
 apply TIF_morph; trivial.
*apply G_incl with omega; trivial.
*unfold L; intros.
 apply G_union2; trivial.
  apply G_singl; trivial.
  apply G_trans with omega; auto.

  apply G_sigma; auto.
  do 2 red; intros.
  apply TIF_morph; auto with *.
  apply fm; auto with *.
Qed.

End UniverseFacts.
  
End EncodeBigParameter.

(*Existing Instance Aenc_ltm.*)

Instance Aenc_morph_gen :
  Proper (eq_set==>(eq_set==>eq_set)==>(eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) Aenc.
do 5 red; intros.
unfold Aenc.
apply TIF_morph_gen; auto with *.
do 2 red; intros.
apply union2_morph; [reflexivity|].
apply sigma_morph; [auto|].
red; intros.
apply H3; apply H1; trivial.
Qed.

Instance Dec_morph_gen :
  Proper ((eq_set==>eq_set==>eq_set)==>eq_set==>eq_set==>eq_set) Dec.
assert (m1 := Aenc_ltm).
do 4 red; intros.
unfold Dec.
apply ZFrepl.WFR_morph; auto with *.
*red; intros.
 apply Aenc_sub_morph; trivial.

*do 3 red; intros.
 apply if_prop_morph; trivial.
  apply ex_morph; intros b'.
  apply ex_morph; intros q'.
  rewrite H3; reflexivity.

  apply H2.
   rewrite H3; reflexivity.
   apply H; trivial.
   rewrite H3; reflexivity.
Qed.
