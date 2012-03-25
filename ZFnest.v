Require Import ZF.
Require Import ZFstable ZFpairs ZFsum ZFrelations ZFcoc ZFord ZFfix ZFlimit.
Require Import ZFiso ZFfixrec.
Require Import ZFind_w ZFspos.
Require Import ZFlist.

(* --> ZFfix *)
Lemma TI_op_mono o o' f f' :
  morph1 f ->
  morph1 f' -> 
  (incl_set ==> incl_set)%signature f f' ->
  isOrd o ->
  o == o' ->
  TI f o \incl TI f' o'.
intros.
rewrite <- H3.
clear o' H3.
elim H2 using isOrd_ind; intros.
red; intros.
apply TI_elim in H6; trivial.
destruct H6.
apply TI_intro with x; trivial.
revert H7; apply H1; auto.
Qed.

Section NestedInductive.

  Variable F : set -> set -> set.
  Hypothesis Fmono : Proper (incl_set==>incl_set==>incl_set) F.

  Instance Fmono_morph2 : morph2 F.
do 3 red; intros; apply incl_eq.
 apply Fmono.
  rewrite H; reflexivity.
  rewrite H0; reflexivity.
 apply Fmono.
  rewrite H; reflexivity.
  rewrite H0; reflexivity.
Qed.

  Let Fnest_mono X : Proper (incl_set ==> incl_set) (fun Y => F X Y).
do 2 red; intros; apply Fmono; auto with *.
Qed.

  Let Fnest_morph X : morph1 (fun Y => F X Y).
apply Fmono_morph; trivial.
Qed.

(** F(X,Y): Y is the nested type with (uniform) parameter X *)

(* F(X,Y) iso { x:A | B x -> X & C x -> Y } *)
Hypothesis A : set.
Hypothesis B : set -> set.
Hypothesis C : set -> set.
Hypothesis Bm : morph1 B.
Hypothesis Cm : morph1 C.
Hypothesis Fdef : forall X Y,
  F X Y == sigma A (fun x => prodcart (cc_arr (B x) X) (cc_arr (C x) Y)). 

Let ACm : morph1 (W_F A C).
do 2 red; intros.
apply W_F_ext; auto with *.
red; auto with *.
Qed.
(*
is pos_nest_op X a W-type ?

nest X = {x':A' | B'(x') -> X }
F X (nest X) = { x:A | B(x) -> X & C(x) -> nest X}
             = { x:A | B(x) -> X & { f:C(x) -> A' | (i:C x)-> B'(f i) -> X }
             = { x:A | { f:C(x)->A' | B(x) -> X & {i:C x|B'(f i)} -> X } }
  = { {x:A; f:C x-> A'} | (B(x) + {i:C x|B'(f i)}) -> X }

A' = { x:A; C(x) ->A' }
B'(x,f) = B x + {i:C x & B'(f i)}  <-- param non-uniforme!
B'(_) = sup A B + (sup A C * B')

Ex: tree, list  F(T,L) = 1+T*L
 list T =  \mu L.F(T,L) = 1+T*\mu L.F(T,L)
 Ft T = 1+T*list T
 A=bool B=(0|1) C=(0|1)
 A' = 1 + A'
 B' = (0|1 + B' o snd)
 A' = nat
 B'(0) = 0
 B'(S k) = 1+B'(k)
 Ft T = {n:nat; n -> T }

F X (nest X) = { x:A(X) ; B(X,x) -> nest X }
  =  {x:A(X) ; f:B(X,x) -> A' ; {i:B(X,x);B'(f i)}->X}
  = { {x:A(X); f:B(_,x) -> A' ; 



list A = {n:N & n -> A }
list A = W1 * W2->A
1+A*list A = 1 + A*W1 * W2osnd -> A
   = (1+W1) * (0|1+W2) -> A
W1=1+W1
W2(n) = 0|1+W2(n-1)
*)

(* F X Y  (iso)  { x:A(Y) & B(Y,x) -> X }
                 { x:A'(X) & B'(X,x) -> Y
*)

Lemma F_elim x X Y :
  x \in F X Y ->
  fst x \in A /\
  (forall b, b \in B (fst x) -> cc_app (fst (snd x)) b \in X) /\
  (forall i, i \in C (fst x) -> cc_app (snd (snd x)) i \in Y) /\
  x == (couple (fst x)
       (couple (cc_lam (B (fst x)) (cc_app (fst (snd x))))
               (cc_lam (C (fst x)) (cc_app (snd (snd x)))))).
intros.
rewrite Fdef in H.
assert (ty1 := fst_typ_sigma _ _ _ H).
assert (eq1 := surj_pair _ _ _ (subset_elim1 _ _ _ H)).
apply snd_typ_sigma with (y:=fst x) in H; auto with *.
 split; trivial.
 assert (ty2 := fst_typ _ _ _ H).
 assert (eq2 := surj_pair _ _ _ H).
 apply snd_typ in H.
 split; [|split]; intros.
  apply cc_arr_elim with (1:=ty2); trivial.

  apply cc_arr_elim with (1:=H); trivial.

  transitivity (couple (fst x) (snd x)); auto with *.
  apply couple_morph; auto with *.
  rewrite eq2; apply couple_morph; auto with *.
   rewrite cc_eta_eq with (1:=ty2).
   apply cc_lam_ext; auto with *.
   red; intros.
   rewrite fst_def.
   rewrite <- H1.
   rewrite cc_beta_eq; auto with *.
   do 2 red; intros; apply cc_app_morph; auto with *.

   rewrite cc_eta_eq with (1:=H).
   apply cc_lam_ext; auto with *.
   red; intros.
   rewrite snd_def.
   rewrite <- H1.
   rewrite cc_beta_eq; auto with *.
   do 2 red; intros; apply cc_app_morph; auto with *.

 do 2 red; intros.
 rewrite <- H1; reflexivity.
Qed.
  
Lemma F_intro a fb fc X Y :
  ext_fun (B a) fb ->
  ext_fun (C a) fc -> 
  a \in A ->
  (forall b, b \in B a -> fb b \in X) ->
  (forall i, i \in C a -> fc i \in Y) ->
  couple a (couple (cc_lam (B a) fb) (cc_lam (C a) fc)) \in F X Y.
intros.
rewrite Fdef.
apply couple_intro_sigma; trivial.
 do 2 red; intros.
 rewrite <- H5; reflexivity.
apply couple_intro; apply cc_arr_intro; intros; auto with *.
Qed.



Let A'i := TI (W_F A C).

Lemma fst_A'i o x' :
  isOrd o -> x' \in A'i o -> fst x' \in A.
intros.
apply TI_elim in H0; trivial.
destruct H0.
apply fst_typ_sigma in H1; trivial.
Qed.

Let B'0 := List (union2 (sup A C) (sup A B)).

(* B_ok x' b means that b is an element of B'0 that is
   correctly indexed by x':A' *)
Inductive B_ok (x':set) (b:set) : Prop :=
| Bnil l :
   l \in B (fst x') ->
   b == Cons l Nil ->
   B_ok x' b
| Bcons i b' :
   i \in C (fst x') ->
   B_ok (cc_app (snd x') i) b' ->
   b == Cons i b' ->
   B_ok x' b.

Let B' x' := subset B'0 (B_ok x').

Instance B'm : morph1 B'.
do 2 red; intros.
apply subset_morph; auto with *.
assert (Proper (eq_set ==> eq_set ==> impl) B_ok).
 do 4 red; intros.
 revert y0 y1 H0 H1; elim H2; intros.
  rewrite H3 in H0; rewrite H4 in H1; apply Bnil with l; trivial.
  rewrite H5 in H0; rewrite H6 in H4; apply Bcons with i b'; trivial.
  apply H3; auto with *.
  rewrite H5; reflexivity.
split; apply H0; auto with *.
Qed.

Lemma B'notmt x' z : z \in B' x' -> ~ z == Nil.
red; intros.
rewrite H0 in H; clear z H0.
unfold B' in H; rewrite subset_ax in H; destruct H.
destruct H0.
destruct H1.
 rewrite H2 in H0; apply discr_mt_pair in H0; trivial.
 rewrite H3 in H0; apply discr_mt_pair in H0; trivial.
Qed.
(*
Lemma B'nil X x' l :
  x' \in W_F A C X ->
  l \in B (fst x') ->
  Cons l Nil \in B' x'.
intros.
apply subset_intro.
 apply Cons_typ;[|apply Nil_typ].
 apply union2_intro2.
 rewrite sup_ax; auto with *.
 exists (fst x'); trivial.
 apply fst_typ_sigma in H; trivial.

 apply Bnil with l; auto with *.
Qed.

Lemma B'cons X x' i b' :
  x' \in W_F A C X ->
  i \in C (fst x') ->
  b' \in B' (cc_app (snd x') i) ->
  Cons i b' \in B' x'.
intros.
apply subset_intro.
 apply Cons_typ.
  apply union2_intro1.
  rewrite sup_ax; auto with *.
  exists (fst x'); trivial.
  apply fst_typ_sigma in H; trivial.

  apply subset_elim1 in H1; trivial.

 apply subset_elim2 in H1; destruct H1.
 apply Bcons with i x; auto with *.
 rewrite H1; reflexivity.
Qed.
*)

Lemma B'nil o x' l :
  isOrd o ->
  x' \in A'i o ->
  l \in B (fst x') ->
  Cons l Nil \in B' x'.
intros.
apply subset_intro.
 apply Cons_typ;[|apply Nil_typ].
 apply union2_intro2.
 rewrite sup_ax; auto with *.
 exists (fst x'); trivial.
 apply fst_A'i with o; trivial.

 apply Bnil with l; auto with *.
Qed.

Lemma B'cons o x' i b' :
  isOrd o ->
  x' \in A'i o ->
  i \in C (fst x') ->
  b' \in B' (cc_app (snd x') i) ->
  Cons i b' \in B' x'.
intros.
apply subset_intro.
 apply Cons_typ.
  apply union2_intro1.
  rewrite sup_ax; auto with *.
  exists (fst x'); trivial.
  apply fst_A'i with o; trivial.

  apply subset_elim1 in H2; trivial.

 apply subset_elim2 in H2; destruct H2.
 apply Bcons with i x; auto with *.
 rewrite H2; reflexivity.
Qed.

Lemma B'_elim x' z :
  z \in B' x' ->
  (exists2 l, l \in B (fst x') & z == Cons l Nil) \/
  (exists2 i, i \in C (fst x') & exists2 b', b' \in B' (cc_app (snd x') i) & z == Cons i b').
unfold B'.
intros.
rewrite subset_ax in H.
destruct H as (zb,(z',eqz, zok)).
destruct zok.
 left; exists l; trivial.
 rewrite eqz; trivial.

 right; exists i; trivial; exists b'.
  apply subset_intro; auto.
  unfold B'0 in zb.
  rewrite List_eqn in zb.
  revert H0; rewrite <- eqz.
  apply LISTf_ind with (4:=zb); intros.
   do 2 red; intros.
   rewrite H0; reflexivity.

   apply discr_mt_pair in H0; contradiction.

   apply couple_injection in H2; destruct H2 as (_,H2); rewrite <- H2; trivial.

  rewrite eqz; trivial.
Qed.

Lemma B'_ind : forall (P:set->set->Prop),
  (forall x' b l,
   l \in B (fst x') ->
   b == Cons l Nil -> P x' b) ->
  (forall x' b i b',
   i \in C (fst x') ->
   b' \in B' (cc_app (snd x') i) ->
   P (cc_app (snd x') i) b' ->
   b == Cons i b' ->
   P x' b) ->
  forall x' z,
  z \in B' x' ->
  P x' z.
intros.
unfold B' in H1; rewrite subset_ax in H1; destruct H1.
destruct H2.
revert z H1 H2; induction H3; intros.
 rewrite <- H4 in H2; eauto with *.

 rewrite <- H5 in H2.
 assert (b' \in B'0).
  revert H2; apply List_ind with (4:=H4); intros.
   do 2 red; intros.
   rewrite H2; reflexivity.

   apply discr_mt_pair in H2; contradiction.

   apply couple_injection in H8; destruct H8.
   rewrite <- H9; trivial.
 apply H0 with i b'; auto with *.
 apply subset_intro; trivial.
Qed.

Lemma B'_eqn o x' z :
  isOrd o ->
  x' \in A'i o -> 
  (z \in B' x' <->
   (exists2 l, l \in B (fst x') & z == Cons l Nil) \/
   (exists2 i, i \in C (fst x') & exists2 b', b' \in B' (cc_app (snd x') i) & z == Cons i b')).
split; intros.
 apply B'_ind with (3:=H1); intros.
  left; exists l; trivial.

  right ;exists i; trivial; exists b'; trivial.

 destruct H1 as [(l,?,?)|(i,?,(b',?,?))].
  rewrite H2; apply B'nil with o; trivial.
  rewrite H3; apply B'cons with o; trivial.
Qed.

Lemma B'cases x b :
  b \in B' x ->
  (b == Cons (fst b) Nil /\ fst b \in B (fst x) /\
   forall f g, LIST_case (snd b) f g == f) \/
  (b == Cons (fst b) (snd b) /\ fst b \in C (fst x) /\ snd b \in B'(cc_app (snd x) (fst b)) /\
   forall f g, LIST_case (snd b) f g == g).
intros.
apply B'_elim in H; destruct H as [(l,?,?)|(i,?,(b',?,?))].
 left; split; [|split]; intros.
  rewrite H0; rewrite fst_def; reflexivity.

  rewrite H0; rewrite fst_def; trivial.

  rewrite H0; rewrite snd_def; apply LIST_case_Nil.

 right; split;[|split;[|split]]; intros.
  rewrite H1; rewrite fst_def; rewrite snd_def; reflexivity.

  rewrite H1; rewrite fst_def; trivial.

  rewrite H1; rewrite fst_def; rewrite snd_def; trivial.

  rewrite H1; rewrite snd_def.
  apply B'_elim in H0; destruct H0 as [(l,?,eqb)|(i',?,(b'',?,eqb))]; rewrite eqb; apply LIST_case_Cons.
Qed.


Definition B'case_typ x b f g X :
  b \in B' x ->
  (fst b \in B(fst x) -> f \in X) ->
  (fst b \in C(fst x) -> snd b \in B'(cc_app(snd x)(fst b)) -> g \in X) ->
  LIST_case (snd b) f g \in X.
intros.
apply B'cases in H; destruct H as [(?,(?,eqc))|(?,(?,(?,eqc)))]; rewrite eqc; auto.
Qed.
(*
Parameter B'case : (set -> set) -> (set->set->set) -> set -> set.

Lemma B'case_ext a' f g :
  (forall l l', l \in B (fst a') -> l == l' -> f l == f l') ->
  (forall i i' b b', i \in C (fst a') -> i==i' -> b \in B' (cc_app (snd a') i) -> b==b' ->
   g i b == g i' b') ->
  ext_fun (B' a') (B'case f g).
Admitted.

Instance B'case_morph : Proper ((eq_set==>eq_set)==>(eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) B'case.
Admitted.

Parameter B'case_typ : forall P f g o x' b,
  isOrd o ->
  x' \in A'i o ->
  b \in B' x' ->
  (forall l, l \in B (fst x') -> f l \in P) ->
  (forall i b', i \in C (fst x') -> b' \in B' (cc_app (snd x') i) -> g i b' \in P) ->
  B'case f g b \in P.

Parameter B'case_nil : forall f g l,
  B'case f g (Cons l Nil) == f l.

Parameter B'case_cons : forall f g i b',
  B'case f g (Cons i b') == g i b'.

Parameter B'case_nil' : forall x f g l,
  x == Cons l Nil ->
  B'case f g x == f l.

Parameter B'case_cons' : forall x f g i b',
  x == Cons i b' ->
  B'case f g x == g i b'.
*)
(** Isomorphism *)

(*
Let fcm :
  a \in A ->
  ext_fun  fc
  ext_fun (C a) (fun i => fst (f (cc_app (snd (snd x)) i)))
*)

(* TI F_X o -> A'i (osucc o) *)
Let a'of a fc :=
  couple a (cc_lam (C a) (fun i => fst (fc i))).

Let a'of_typ o a fc X :
  ext_fun (C a) fc ->
  isOrd o ->
  a \in A ->
  typ_fun fc (C a) (W_F (A'i o) B' X) ->
  a'of a fc \in A'i(osucc o).
unfold a'of; intros.
unfold A'i; rewrite TI_mono_succ; auto with *.
2:apply W_F_mono; auto with *.
apply W_F_intro; intros; auto with *.
 do 2 red; intros; apply fst_morph; auto.

 apply H2 in H3.
 apply fst_typ_sigma in H3; trivial.
Qed.

Definition g f t (* f:Y->WF(A',B',X), t:F X Y *) := (* W_F(A'+,B',X) *)
  let a := fst t in (*A*)
  let fb := cc_app (fst (snd t)) in (* B a -> X *)
  let fc := cc_app (snd (snd t)) in (* C a -> Y *)
  let a' := couple a (cc_lam (C a) (fun i => fst (f (fc i)))) in
  let fb' b := (* B' a' -> X *)
    LIST_case (snd b) (fb (fst b)) (* fst b : B a *)
                      (cc_app (snd (f (fc (fst b)))) (snd b)) in
  couple (a'of a (fun i => f(fc i))) (cc_lam (B' (a'of a (fun i =>f(fc i)))) fb').


Lemma ecase1 : forall Y Z a g x f,
  iso_fun Y Z f ->
  typ_fun (cc_app (snd (snd x))) (C a) Y ->
  ext_fun (B' (a'of a g))
     (fun b => LIST_case (snd b) (cc_app (fst (snd x)) (fst b))
        (cc_app (snd (f (cc_app (snd (snd x)) (fst b)))) (snd b))).
do 2 red; intros.
rewrite <- (snd_morph _ _ H2).
apply B'cases in H1; destruct H1 as [(?,(?,eqc))|(?,(?,(?,eqc)))]; do 2 rewrite eqc.
 rewrite H2; reflexivity.

 apply cc_app_morph; auto with *.
 apply snd_morph.
 apply (iso_funm H).
  unfold a'of in H3; rewrite fst_def in H3; auto.

  rewrite H2; reflexivity.
Qed.

Lemma gext f f' X Y :
  eq_fun Y f f' ->
  eq_fun (F X Y) (g f) (g f').
red; intros.
assert (cmorph := fun x x' e y y' e' =>
  couple_morph x x' e y y' (e' e)).
unfold g.
apply F_elim in H0; destruct H0 as (ty1,(ty2,(ty3,eqx))).
apply cmorph; intros.
 apply couple_morph.
  apply fst_morph; trivial.

  apply cc_lam_ext.
   rewrite H1; reflexivity.

   red; intros.
   apply fst_morph.
   apply H; auto.
   rewrite H1; rewrite H2; reflexivity.

 apply cc_lam_ext.
  apply B'm; trivial.

  red; intros.
  rewrite <- (snd_morph _ _ H2).
  apply B'cases in H0; destruct H0 as [(?,(?,eqc))|(?,(?,(?,eqc)))]; do 2 rewrite eqc.
   rewrite H1; rewrite H2; reflexivity.

   apply cc_app_morph; auto with *.
   apply snd_morph.
   apply H; auto.
   2:rewrite H1; rewrite H2; reflexivity.
   unfold a'of in H3; rewrite fst_def in H3; auto.
Qed.

Instance gm :  Proper ((eq_set==>eq_set)==>eq_set==>eq_set) g.
do 3 red; intros.
assert (fm := fst_morph _ _ H0).
assert (cmorph := fun x x' e y y' e' =>
  couple_morph x x' e y y' (e' e)).
apply cmorph; intros.
 apply couple_morph; auto.
 apply cc_lam_morph; auto.
 red; intros.
 apply fst_morph; apply H.
 rewrite H0; rewrite H1; reflexivity.

 apply cc_lam_morph; auto.
  apply B'm; auto.

  red; intros.
  apply LIST_case_morph.
   apply snd_morph; trivial.

   rewrite H0 ;rewrite H1; reflexivity.

   apply cc_app_morph.
   2:apply snd_morph; trivial.
   apply snd_morph; apply H.
   rewrite H0 ;rewrite H1; reflexivity.
Qed.

Hint Resolve W_F_mono.


Lemma giso Y X f o:
  isOrd o ->
  iso_fun Y (W_F (A'i o) B' X) f ->
  iso_fun (F X Y) (W_F (W_F A C (A'i o)) B' X) (g f).
intros.
assert (ec1 := fun a g x => ecase1 _ _ a g x _ H0).
assert (essf1 : forall x,
  typ_fun (cc_app (snd (snd x))) (C (fst x)) Y ->
  ext_fun (C (fst x)) (fun i => fst (f (cc_app (snd (snd x)) i)))).
 do 2 red; intros.
 apply fst_morph; apply (iso_funm H0); auto.
 rewrite H3; reflexivity.
constructor; intros.
 apply gext; auto.
 apply (iso_funm H0).

 red; intros.
 apply F_elim in H1; destruct H1 as (ty1,(ty2,(ty3,et1))).
 unfold g.
 assert (tya' : a'of (fst x) (fun i => f (cc_app (snd (snd x)) i)) \in TI (W_F A C) (osucc o)).
  apply a'of_typ with X; auto.
   do 2 red; intros; apply (iso_funm H0); auto.
   rewrite H2; reflexivity.

   apply iso_typ in H0; red in H0; red; auto.
 apply W_F_intro; intros; auto with *.
  unfold A'i; rewrite <- TI_mono_succ; auto with *.

  apply B'case_typ with (1:=H1); intros.
   unfold a'of in H2; rewrite fst_def in H2; auto.

   unfold a'of in H2,H3.
   rewrite fst_def in H2.
   rewrite snd_def in H3.
   rewrite cc_beta_eq in H3; auto with *.
   apply ty3 in H2.
   apply (iso_typ H0) in H2.
   apply W_F_elim in H2; auto with *.
   destruct H2 as (_,(?,_)); auto.

 (* injectivity *)
 unfold g in H3.
 apply F_elim in H1; destruct H1 as (ty1,(ty2,(ty3,et))).
 apply F_elim in H2; destruct H2 as (ty1',(ty2',(ty3',et'))).
 destruct WFi_inv with (1:=H3); clear H3; intros; auto with *.
  apply B'm; trivial.
 destruct WFi_inv with (1:=H1); clear H1; intros; auto with *.
 rewrite et; rewrite et'.
 assert (tya' : a'of (fst x) (fun i => f (cc_app (snd (snd x)) i)) \in TI (W_F A C) (osucc o)).
  apply a'of_typ with X; auto.
   do 2 red; intros; apply (iso_funm H0); auto.
   rewrite H5; reflexivity.

   apply iso_typ in H0; red in H0; red; auto.
 apply couple_morph; trivial.
 apply couple_morph; apply cc_lam_ext; auto.
  red; intros.
  red in H4.
  generalize (H2 (Cons x0 Nil) (Cons x'0 Nil)).
  do 2 rewrite snd_def; do 2 rewrite LIST_case_Nil.
  do 2 rewrite fst_def.
  intros h; apply h.
   apply B'nil with (osucc o); auto.
   unfold a'of; rewrite fst_def; trivial.

   rewrite H5; reflexivity.

  red; intros.
  rewrite <- H5; clear x'0 H5.
  assert (H4' := H4 _ _ H1 (reflexivity _)).
  assert (tyf := ty3); assert (tyf' := ty3').
  specialize tyf with (1:=H1).
  rewrite H3 in H1; specialize tyf' with (1:=H1).
  apply (iso_inj H0); auto.
  apply (iso_typ H0) in tyf.
  apply (iso_typ H0) in tyf'.
  rewrite WF_eta with (2:=tyf); auto with *.
  rewrite WF_eta with (2:=tyf'); auto with *.
  unfold WFmap.
  apply couple_morph; trivial.
  apply cc_lam_ext.
   apply B'm; trivial.

   red; intros.
   red in H2.
   rewrite <- H6; clear x'0 H6.
   assert (case_Cons : forall f g, LIST_case x1 f g == g).
    intros; apply B'_elim in H5; destruct H5 as [(l,?,eqx)|(i,?,(b',?,eqx))];
      rewrite eqx; apply LIST_case_Cons.
   assert (f (cc_app (snd (snd x)) (fst (Cons x0 x1))) == f (cc_app (snd(snd x)) x0)).
    symmetry; apply (iso_funm H0); auto.
     apply ty3.
     rewrite H3; trivial.

     rewrite fst_def; reflexivity.
   assert (f (cc_app (snd (snd x')) (fst (Cons x0 x1))) == f (cc_app (snd(snd x')) x0)).
    symmetry; apply (iso_funm H0); auto.
    rewrite fst_def; reflexivity.
   rewrite <- H6; rewrite <- H7.
   generalize (H2 (Cons x0 x1) (Cons x0 x1)).
   rewrite snd_def; do 2 rewrite case_Cons.
   intros h; apply h; auto with *.
   apply B'cons with (osucc o); auto.
    unfold a'of; rewrite fst_def; trivial.
    rewrite H3; trivial.

    unfold a'of; rewrite snd_def.
    rewrite cc_beta_eq; auto with *.
    rewrite H3; trivial.

 (* surj *)
 apply W_F_elim in H1; auto with *.
 destruct H1 as (tya',(tyb',et)).
 destruct W_F_elim with (2:=tya') as (tya,(tyf,et')); auto with *.
 pose (fb' :=  fun i => couple (cc_app (snd (fst y)) i)
   (cc_lam (B' (cc_app (snd (fst y)) i))
      (fun b' : set => cc_app (snd y) (Cons i b')))).
 assert (fb'ty : forall i, i \in C (fst (fst y)) -> fb' i \in W_F (A'i o) B' X).
  intros; unfold fb'.
  apply W_F_intro; intros; auto with *.
   do 2 red; intros.
   rewrite H3; reflexivity.

   apply tyb'.
   apply B'cons with (osucc o); auto.
   unfold A'i; rewrite TI_mono_succ; auto with *.
 assert (invm : ext_fun (C (fst (fst y))) (fun i : set => iso_inv Y f (fb' i))).
  do 2 red; intros.
  apply iso_inv_ext; auto with *.
   apply (iso_funm H0).

   unfold fb'; apply WFi_ext with (A:=A'i o); auto with *.
    rewrite H2; reflexivity.

    red; intros.
    rewrite <- H5; rewrite H2; reflexivity.
 exists
 (let a' := fst y in
  let b' := snd y in
  let x := fst a' in
  let fb b := cc_app b' (Cons b Nil) in
  let fc i := iso_inv Y f (fb' i) in
  couple x (couple (cc_lam (B x) fb) (cc_lam (C x) fc))).

  apply F_intro; intros; auto.
   do 2 red; intros; apply cc_app_morph; auto with *.
   rewrite H2; reflexivity.

   apply tyb'.
   apply B'nil with (osucc o); auto.
   unfold A'i; rewrite TI_mono_succ; auto with *.

   apply (iso_inv_typ H0).
   apply fb'ty; trivial.

  rewrite et.
  apply couple_morph.
   rewrite et'; apply couple_morph.
    simpl.
    rewrite fst_def; reflexivity.

    symmetry; apply cc_lam_ext; simpl; intros.
     rewrite fst_def; reflexivity.

     red; intros.
     rewrite H2 in H1.
     transitivity (fst (f (iso_inv Y f (fb' x')))).
      rewrite iso_inv_eq with (1:=H0); auto.
      unfold fb'; rewrite fst_def.
      rewrite H2; reflexivity.

      apply fst_morph.
      apply (iso_funm H0).
       apply (iso_inv_typ H0); auto.

       rewrite snd_def.
       rewrite snd_def.
       rewrite cc_beta_eq; auto with *.

   symmetry; apply cc_lam_ext.
    simpl.
    apply B'm.
    transitivity (couple (fst (fst y))
                  (cc_lam (C (fst (fst y))) (cc_app (snd (fst y))))); auto with *.
     apply couple_morph.
      rewrite fst_def; auto with *.

      symmetry; apply cc_lam_ext.
       rewrite fst_def; reflexivity.

       red; intros.
       rewrite fst_def in H1.
   transitivity (fst (f (iso_inv Y f (fb' x)))).
      apply fst_morph.
      symmetry; apply (iso_funm H0).
       apply (iso_inv_typ H0); auto.

       rewrite snd_def.
       rewrite snd_def.
       rewrite cc_beta_eq; auto with *.

      rewrite iso_inv_eq with (1:=H0); auto.
      unfold fb'; rewrite fst_def.
      rewrite H2; reflexivity.

    red; intros.
    specialize tyb' with (1:=H1).
    rewrite H2 in tyb',H1|-*; clear x tyb' H2.    
    apply B'cases in H1; destruct H1 as [(?,(?,eqc))|(?,(?,(?,eqc)))]; rewrite eqc.
     rewrite snd_def.
     rewrite fst_def.
     rewrite cc_beta_eq; auto with *.
     apply cc_app_morph; auto with *.
     do 2 red; intros.
     rewrite H4; reflexivity.

     transitivity
       (cc_app (snd (f (iso_inv Y f (fb' (fst x'))))) (snd x')).
      rewrite iso_inv_eq with (1:=H0); auto.
      unfold fb'; rewrite snd_def.
      rewrite cc_beta_eq; auto with *.
       apply cc_app_morph; auto with *.

       do 2 red; intros.
       rewrite H5; reflexivity.

      apply cc_app_morph; auto with *.
      apply snd_morph.
      apply (iso_funm H0).
       apply (iso_inv_typ H0); auto.

       rewrite snd_def.
       rewrite snd_def.
       rewrite cc_beta_eq; auto with *.
Qed.

Lemma TRF_indep_g : forall X o o' x,
  isOrd o ->
  o' \in o ->
  x \in F X (TI(fun Y=>F X Y) o') ->
  TRF g o x == g (TRF g o') x.
intros.
rewrite <- TI_mono_succ in H1; eauto using isOrd_inv.
rewrite TRF_indep with (6:=H1); auto with *.
 intros; rewrite TI_mono_eq; auto with *.
 rewrite sup_ax; auto with *.
 do 2 red; intros; apply TI_morph; auto with *.
 apply osucc_morph; trivial.

 red; intros.
 rewrite TI_mono_succ in H4; auto with *.
 revert H4 H5; apply gext; trivial.
Qed.

Lemma giso_it X o:
  isOrd o ->
  iso_fun (TI(fun Y=>F X Y)o) (W_F (A'i o) B' X) (TRF g o).
intros.
elim H using isOrd_ind; intros.
constructor; intros.
 do 2 red; intros.
 apply TRF_morph; auto with *.

 red; intros.
 assert (yo := isOrd_inv y).
 apply TI_elim in H3; auto with *.
 destruct H3.
 rewrite TRF_indep_g with (3:=H4); auto with *.
 specialize H2 with (1:=H3).
 apply giso in H2; eauto using isOrd_inv.
 apply (iso_typ H2) in H4.
 apply W_F_elim in H4; auto with *.
 destruct H4 as (?,(?,?)).
 rewrite H6; apply W_F_intro; auto with *.
  do 2 red; intros; apply cc_app_morph; auto with *.
 apply TI_intro with x0; auto with *.

 apply TI_elim in H3; auto.
 destruct H3.
 apply TI_elim in H4; auto.
 destruct H4.
 destruct (isOrd_dir _ H0 x0 x1); trivial.
 destruct H9.
 specialize H2 with (1:=H8).
 apply giso in H2; eauto using isOrd_inv.
 assert (x \in F X (TI (fun Y=>F X Y) x2)).
  revert H6; apply Fmono; auto with *.
  apply TI_mono; eauto using isOrd_inv.
 assert (x' \in F X (TI (fun Y=>F X Y) x2)).
  revert H7; apply Fmono; auto with *.
  apply TI_mono; eauto using isOrd_inv.
 clear H6 H7.
 rewrite TRF_indep_g with (3:=H11) in H5; auto.
 rewrite TRF_indep_g with (3:=H12) in H5; auto.
 apply (iso_inj H2) in H5; trivial.

 apply W_F_elim in H3; auto with *.
 destruct H3 as (?,(?,?)).
 apply TI_elim in H3; auto with *.
 destruct H3.
 specialize H2 with (1:=H3).
 apply giso in H2; eauto using isOrd_inv.
 destruct (iso_surj H2) with y0.
  rewrite H5; apply W_F_intro; auto with *.
  do 2 red; intros; apply cc_app_morph; auto with *.
 rewrite <- TRF_indep_g with (2:=H3)(3:=H7) in H8; auto.
 exists x0; trivial.
 apply TI_intro with x; trivial.
Qed.


Definition nest_pos (o:set) : positive :=
  mkPositive (fun X => TI (fun Y => F X Y) o) (A'i o) B' (TRF g o).

Lemma isPos_nest o :
  isOrd o ->
  isPositive (nest_pos o).
constructor.
 do 2 red; intros.
 simpl.
 apply TI_op_mono; auto with *; apply Fmono_morph;
   do 2 red; intros; apply Fmono; auto with *.

 do 2 red; intros; simpl.
 apply B'm; trivial.

 simpl; intros.
 apply giso_it; trivial.
Qed.
(*Print Assumptions isPos_nest.*)



(* Reverse order! *)
(*
Definition g f t (* W_F A' B' X*) := (* N X *)
  let a' := fst t in
  let b' := snd t in
  let x := fst a' in
  let fb b := cc_app b' (Cons b Nil) in
  let fc i :=
    f  (couple (cc_app (snd a') i) (cc_lam (B'(cc_app(snd a') i)) (fun b'' =>
         cc_app b' (Cons i b'')))) in
  couple x (couple (cc_lam (B x) fb) (cc_lam (C x) fc)).

Lemma giso X f o:
  isOrd o ->
  iso_fun (W_F (A'i o) B' X) (TI (fun Y=>F X Y) o) f ->
  iso_fun (W_F (W_F A C (A'i o)) B' X) (F X (TI (fun Y=>F X Y) o)) (g f).
*)

End NestedInductive.

(*
Lemma W_F_inj :
  (forall X, iso_fun (W_F A B X) (W_F A' B' X) f) ->
  let f1 := fun a => fst(f (*X=1*) (couple a (cc_lam (B a) (fun _ => empty)))) in
  iso_fun A A' () /\
  (forall X x, a \in A -> iso_fun (cc_arr (B x) X) (cc_arr (B' (f1 x)) X) (fun
)).
*)
(*
Section VariableSeparation.

Variable F : set -> set -> set.
Hypothesis Fmono : Proper (incl_set==>incl_set==>incl_set) F.

(* W-type in X *)
Variable A : set -> set.
Variable B : set -> set -> set.
Variable fX : set -> set -> set.

Let pX Y := mkPositive (fun X => F X Y) (A Y) (B Y) (fX Y).

Hypothesis FposX : forall Y, isPositive (pX Y).

(* W-type in Y *)
Variable A' : set -> set.
Variable B' : set -> set -> set.
Variable fY : set -> set -> set.

Let pY X := mkPositive (fun Y => F X Y) (A' X) (B' X) (fY X).

Hypothesis FposY : forall X, isPositive (pY X).

(* 
F(X,Y) = A(Y) * (B(Y)->X) = A'(X) * (B'(X)->Y)
F(X,1) = A(1) * (B(1)->X) = A'(X)
-->
F(X,Y) = A(1) * (B(1)->X) * (B'(1)->Y) ?
 *)

Definition A0 := A (singl empty).
Definition B0 := B (singl empty).


Definition iso1 X p :=
  couple p (cc_lam (B' X p) (fun _ => empty)).

Lemma iso_fun1 X :
  iso_fun (A' X) (W_F (A' X) (B' X) (singl empty)) (iso1 X).
constructor; intros.
 admit.

 red; intros.
 unfold iso1.
 apply W_F_intro; intros; auto with *.
  do 2 red; intros; apply (w2m (pY X)); auto with *.
  apply singl_intro.

 apply couple_injection in H1; destruct H1; trivial.

 apply W_F_elim in H.
 2:apply (w2m (pY X)); trivial.
 destruct H as (?,(?,?)).
 exists (fst y); trivial.
 unfold iso1.
 apply (@transitivity) with (3:=symmetry H1); auto with *.
 apply couple_morph; auto with *.
 apply cc_lam_ext; auto with *.
 red; intros.
 rewrite <- H3; symmetry; apply singl_elim; auto.
Qed.

Definition iso2 X Y :=
  comp_iso (iso_inv (F X Y) (wf (pY X))) (wf (pX Y)).

Lemma iso_fun2 X Y :
  iso_fun (W_F (A' X) (B' X) Y) (W_F (A Y) (B Y) X) (iso2 X Y).
eapply iso_fun_trans.
 apply (iso_fun_sym (w_iso _ (FposY X) Y)).
 apply (w_iso _ (FposX Y) X).
Qed.



Lemma if1 X :
  {f:_ | iso_fun (A' X) (W_F A0 B0 X) f }.
econstructor.
eapply iso_fun_trans.
 apply iso_fun1.

 apply iso_fun2.
Defined.

(* coe :  A0 --> A' (singl empty) *)
Definition coe i := iso_inv (A' (singl empty)) (proj1_sig (if1(singl empty)))
   (couple i (cc_lam (B0 i) (fun _ => empty))).
Definition C0 i := B' (singl empty) (coe i).

(*
Lemma iso_fun1 : forall X,
  iso_fun (A' X) (W_F (A (singl empty)) (B (singl empty)) X)
*)

Lemma Fdef : forall X Y,
  {f:_|
  iso_fun (F X Y) (sigma A0 (fun x => prodcart (cc_arr (B0 x) X) (cc_arr (C0 x) Y))) f}. 
intros.
econstructor.
eapply iso_fun_trans.
 apply (w_iso _ (FposY X)).
 simpl.
eapply iso_fun_trans.
 unfold W_F.
 apply sigma_iso_fun_morph with (4:=proj2_sig (if1 X)).
Focus 5.
eapply iso_fun_trans.
 apply iso_fun_sym.
 apply iso_sigma_sigma.
Focus 3.
 apply eq_iso_fun.
  apply sigma_ext;[reflexivity|].
  intros.
  rewrite sigma_nodep.
  apply sigma_ext; intros.
   apply cc_arr_morph; auto with *.
   apply (w2m _ (FposX (singl empty))); trivial.

assert (C0m : ext_fun A0 C0) by admit.
   rewrite <- (C0m _ _ H H0).
   apply cc_arr_morph.
    reflexivity.
    reflexivity.
 instantiate (1:=fun x=>x); reflexivity.
Unfocus.
Focus 4.
simpl; intros.
unfold C0.
Show Existentials.
(*
[X : set
 Y : set
 x : set |- set -> set] 
iso_fun (B X x -> Y) (B' (singl empty) (coe (fst x')) -> Y1) ?
*)

apply eq_iso_fun with (f:=fun x=>x); auto with *.
apply cc_arr_morph; auto with *.
unfold C0.
generalize (w2m _ (FposY (singl empty))).
simpl.
Abort.

End VariableSeparation.
*)