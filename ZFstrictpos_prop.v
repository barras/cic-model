Require Import ZF ZFpairs ZFsum ZFrelations ZFcoc ZFord ZFfix.
Import IZF.

Require Import ZFstable.

(* Same as ZFstrictpos, but for inductive definitions in Prop *)

Inductive positive :=
| P_Cst (A:set)
| P_Rec
| P_Sum (p1 p2:positive)
| P_ConsRec (p1 p2:positive)
| P_ConsNoRec (A:set) (p:set->positive)
| P_Param (A:set) (p:set->positive).


Inductive eq_pos : positive -> positive -> Prop :=
| EP_Cst : forall A A', A == A' -> eq_pos (P_Cst A) (P_Cst A')
| EP_Rec : eq_pos P_Rec P_Rec
| EP_Sum : forall p1 p2 q1 q2,
   eq_pos p1 p2 -> eq_pos q1 q2 -> eq_pos (P_Sum p1 q1) (P_Sum p2 q2)
| EP_ConsRec : forall p1 p2 q1 q2,
   eq_pos p1 p2 -> eq_pos q1 q2 -> eq_pos (P_ConsRec p1 q1) (P_ConsRec p2 q2)
| EP_ConsNoRec : forall A A' p1 p2,
   A == A' ->
   (forall x x', x == x' -> eq_pos (p1 x) (p2 x')) ->
   eq_pos (P_ConsNoRec A p1) (P_ConsNoRec A' p2)
| EP_Param : forall A A' p1 p2,
   A == A' ->
   (forall x x', x == x' -> eq_pos (p1 x) (p2 x')) ->
   eq_pos (P_Param A p1) (P_Param A' p2).

Instance eq_pos_sym : Symmetric eq_pos.
red; induction 1; constructor; auto with *.
Qed.

Instance eq_pos_trans : Transitive eq_pos.
red.
intros x y z ep1 ep2; revert z ep2; induction ep1; intros; inversion_clear ep2;
  constructor; intros; eauto with *.
 transitivity A'; trivial.
 transitivity A'; trivial.

 transitivity A'; trivial.
Qed.

Lemma eq_pos_left : forall p1 p2, eq_pos p1 p2 -> eq_pos p1 p1.
intros.
transitivity p2; trivial.
symmetry; trivial.
Qed.

Lemma pos_rect : forall (P:positive->Type),
  (forall A, P (P_Cst A)) ->
  P P_Rec ->
  (forall p1 p2, eq_pos p1 p1 -> eq_pos p2 p2 -> P p1 -> P p2 -> P (P_Sum p1 p2)) ->
  (forall p1 p2, eq_pos p1 p1 -> eq_pos p2 p2 -> P p1 -> P p2 -> P (P_ConsRec p1 p2)) ->
  (forall A p,
   (forall x x', x == x' -> eq_pos (p x) (p x')) ->
   (forall x, x \in A -> P (p x)) ->
   P (P_ConsNoRec A p)) ->
  (forall A p,
   (forall x x', x == x' -> eq_pos (p x) (p x')) ->
   (forall x, x \in A -> P (p x)) ->
   P (P_Param A p)) ->
  forall p, eq_pos p p -> P p.
intros.
induction p; trivial.
 assert (eq_pos p1 p1 /\ eq_pos p2 p2) by (inversion H; auto with *).
 destruct H0; auto.

 assert (eq_pos p1 p1 /\ eq_pos p2 p2) by (inversion H; auto with *).
 destruct H0; auto.

 apply X3; intros.
  inversion_clear H; auto.

  apply X5.
  inversion H; auto with *.

 apply X4; intros.
  inversion_clear H; auto.

  apply X5.
  inversion H; auto with *.
Defined.


Lemma union2_mono : Proper (incl_set ==> incl_set ==> incl_set) union2.
do 4 red; intros.
apply union2_elim in H1; destruct H1; [apply union2_intro1|apply union2_intro2]; auto.
Qed.

Lemma inter2_mono : Proper (incl_set ==> incl_set ==> incl_set) inter2.
do 4 red; intros.
rewrite inter2_def in H1|-*; destruct H1; auto.
Qed.

Lemma sup_mono A A' F F' :
  ext_fun A F ->
  ext_fun A' F' ->
  A \incl A' ->
  (forall x, x \in A -> F x \incl F' x) ->
  sup A F \incl sup A' F'.
intros eF eF' inclA inclF z tyz.
rewrite sup_ax in tyz|-*; trivial.
destruct tyz as (x,?,?).
exists x; auto.
revert H0; apply inclF; trivial.
Qed.

Fixpoint pos_oper p X : Prop :=
  match p with
  | P_Cst A => exists w, w \in A
  | P_Rec => X
  | P_Sum p1 p2 => pos_oper p1 X \/ pos_oper p2 X
  | P_ConsRec p1 p2 => pos_oper p1 X /\ pos_oper p2 X
  | P_ConsNoRec A p => exists2 x, x \in A & pos_oper (p x) X
  | P_Param A p => forall x, x \in A -> pos_oper (p x) X
  end.

Let eqfcst : forall X Y, eq_fun X (fun _ => Y) (fun _ => Y).
red; reflexivity.
Qed.
Hint Resolve eqfcst.

Lemma pos_oper_morph :
  Proper (eq_pos ==> iff ==> iff) pos_oper.
do 2 red; intros.
red.
induction H; simpl; intros; auto with *.
 apply ex_morph; intro w.
 rewrite H; reflexivity.

 apply or_iff_morphism; auto.

 apply and_iff_morphism; auto.

 apply ex2_morph; intro w; auto with *.
 rewrite H; reflexivity.

 apply fa_morph; intro w.
 apply impl_morph; auto with *. 
 rewrite H; reflexivity.
Qed.

Lemma pos_oper_mono :
  Proper (eq_pos ==> impl ==> impl) pos_oper.
do 2 red; intros.
do 2 red.
induction H; simpl; intros; auto with *.
 revert H1; apply iff_impl.
 apply ex_morph; intro w.
 rewrite H; reflexivity.

 destruct H2; eauto.

 destruct H2; eauto.

 destruct H3 as (w,?,?).
 exists w.
  rewrite <- H; trivial.

  apply H1 with w x; auto with *.

 rewrite <- H in H4.
 apply H1 with x0 x; auto with *.
Qed.

Definition pos_oper' p a := P2p (pos_oper p (p2P a)).

Lemma sp_mono : Proper (eq_pos ==> incl_set ==> incl_set) pos_oper'.
unfold pos_oper', P2p, p2P.
do 4 red; intros.
rewrite cond_set_ax in H1|-*.
destruct H1; split; trivial.
revert H2; apply pos_oper_mono; trivial.
red; auto.
Qed.

Lemma sp_morph : Proper (eq_pos ==> eq_set ==> eq_set) pos_oper'.
do 3 red; intros.
unfold pos_oper'.
apply cond_set_morph; auto with *.
apply pos_oper_morph; trivial.
apply in_set_morph; auto with *.
Qed.

Lemma sp_morph0 : forall p, eq_pos p p -> morph1 (pos_oper' p).
intros; apply sp_morph; trivial.
Qed.

Hint Resolve sp_morph0.

Section InductiveProp.

Definition INDi p o := TI (pos_oper' p) o.

Definition IND p := P2p (forall X, (pos_oper p X -> X) -> X).

  Instance INDi_morph : Proper (eq_pos ==> eq_set ==> eq_set) INDi.
do 3 red; intros.
unfold INDi.
apply TR_morph; trivial.
do 2 red; intros.
apply sup_morph; trivial.
red; intros.
apply sp_morph; auto.
Qed.

  Variable p : positive.
  Hypothesis p_ok : eq_pos p p.

  Lemma INDi_succ_eq : forall o,
    isOrd o -> INDi p (osucc o) == pos_oper' p (INDi p o).
unfold INDi; intros.
apply TI_mono_succ; auto with *.
apply sp_mono; trivial.
Qed.

(*
  Lemma INDi_stable : stable_ord (INDi p).
unfold INDi; intros.
apply TI_stable.
 apply pos_oper_mono; trivial.

 apply sp_stable; trivial.
Qed.
*)

  Lemma INDi_mono : forall o o',
    isOrd o -> isOrd o' -> o \incl o' -> INDi p o \incl INDi p o'.
intros.
apply TI_mono; auto with *.
apply sp_mono; trivial.
Qed.

  Lemma IND_post : pos_oper' p (IND p) \incl IND p.
unfold IND, pos_oper'; red; intros.
unfold P2p in H at 1|-*.
rewrite cond_set_ax in H|-*.
destruct H; split; trivial.
intros.
apply H1.
revert H0; apply pos_oper_mono; trivial.
red; intros.
rewrite P2p2P in H0.
apply H0; trivial.
Qed.

  Lemma IND_pre : IND p \incl pos_oper' p (IND p).
red; intros.
unfold IND, P2p in H.
rewrite cond_set_ax in H.
destruct H.
apply H0; intro.
unfold pos_oper', P2p.
rewrite cond_set_ax.
split; trivial.
revert H1; apply pos_oper_mono; trivial.
red; intro.
apply IND_post in H1; trivial.
unfold p2P; apply singl_elim in H; rewrite <- H; trivial.
Qed.

  Lemma IND_eq : pos_oper' p (IND p) == IND p.
apply incl_eq.
 apply IND_post.
 apply IND_pre.
Qed.

  Lemma INDi_IND :
    forall o,
    isOrd o ->
    INDi p o \incl IND p.
induction 1 using isOrd_ind; intros.
unfold INDi.
rewrite TI_eq; auto.
red; intros.
rewrite sup_ax in H2; auto.
destruct H2.
apply IND_post; trivial.
revert H3; apply sp_mono; auto.
apply H1; trivial.
Qed.

  Lemma IND_typ : IND p \in props.
unfold IND.
apply P2p_typ.
Qed.

  Lemma INDi_typ o : isOrd o -> INDi p o \in props.
intros.
unfold props.
apply power_intro; intros.
apply INDi_IND in H0; trivial.
apply power_elim with (1:=IND_typ).
trivial.
Qed.

  Definition IND' p :=
    P2p (exists2 o, isOrd o & p2P (INDi p o)).

  Lemma IND'_def z : z \in IND' p <-> exists2 o, isOrd o & z \in INDi p o.
split; intros.
 unfold IND', P2p in H.
 rewrite cond_set_ax in H; destruct H.
 destruct H0.
 exists x; trivial.
 apply singl_elim in H; rewrite H; trivial.

 destruct H.
 unfold IND', P2p.
 rewrite cond_set_ax; trivial.
 assert (z == prf_trm).
  apply power_elim with (1:=INDi_typ _ H) in H0.
  apply singl_elim in H0; trivial.
 rewrite H1 in H0|-*.
 split; eauto.
 apply singl_intro.
Qed.

  Lemma INDi_IND' o : isOrd o -> INDi p o \incl IND' p.
red; intros.
rewrite IND'_def; eauto.
Qed.

  Lemma IND'_IND : IND' p \incl IND p.
red; intros.
rewrite IND'_def in H; destruct H.
revert H0; apply INDi_IND; trivial.
Qed.

  Lemma IND'_post : pos_oper' p (IND' p) \incl IND' p.
red; intros.
unfold pos_oper', P2p in H.
unfold IND', P2p.
rewrite cond_set_ax in H|-*.
destruct H; split; trivial.
 unfold IND' in H0.
cut (exists2 o, isOrd o & pos_oper p (p2P (INDi p o))).
 destruct 1.
 exists (osucc x); auto.
 unfold p2P, INDi; rewrite TI_mono_succ; auto.
 2:apply sp_mono; trivial.
 unfold pos_oper' at 1.
 unfold P2p; rewrite cond_set_ax.
 split; trivial.
 apply singl_intro.

 revert H0.
 pattern p at 1 3.
 elim p; simpl; intros.
  exists empty; auto.

  rewrite P2p2P in H0; trivial.

  destruct H2.
   destruct H0; eauto.
   destruct H1; eauto.

  destruct H2.
  destruct H0; trivial.
  destruct H1; trivial.
  exists (osup2 x x0).
   apply isOrd_osup2; trivial.

   split.
    revert H4; apply pos_oper_mono.
     admit.
    red; unfold p2P.
    apply INDi_mono; trivial.
     apply isOrd_osup2; trivial.
     apply osup2_incl1; auto.

    revert H5; apply pos_oper_mono.
     admit.
    red; unfold p2P.
    apply INDi_mono; trivial.
     apply isOrd_osup2; trivial.
     apply osup2_incl2; auto.

  destruct H1.
  destruct H0 with x; eauto.

  assert (forall x, x \in A -> exists2 o, isOrd o & pos_oper (p0 x) (p2P (INDi p o))).
   eauto.
  admit.
Qed.



Parameter Pb : nat -> Prop.

Inductive I (I':Prop) : Prop :=
  Ii (n:nat) (_:(exists2 k, k < n & Pb k)->I') (_:exists2 k, k <= n & Pb k).


Lemma L1 : I False <-> Pb 0.
split; intros.
 destruct H; trivial.
 destruct H0.
 destruct x; trivial.
 destruct n.
  inversion H0.
 
 des
 destruct H; exists 
 destruct n; trivial.
 admit.


((exists k < n -> Pb k) -> X) ->
 (exists k < S n -> Pb k) -> I X 

 exists 0; trivial.
 intros.
 destruct H0.
 inversion H0.
Qed.

I : Prop -> Prop
I False <-> Pb 0
I (Pb 0) <-> Pb 0 \/ Pb 1

I X = (exists k < n, Pb k -> X) /\ P n


Inductive I (I':Prop): Prop :=
  C0 (_:Pb 0)
| C1 (_:Pb 1) (_:Pb 0 -> I').

Lemma L1 : I False <-> Pb 0.
split; intros.
 destruct H; trivial.
 contradiction.

 constructor 1; trivial.
Qed.

Lemma L2 : I (I False) <-> Pb 0 \/ Pb 1.
split ;intros.
 destruct H; auto.
 rewrite L1 in H0; auto.

destruct H.
 constructor 1; trivial.

 constructor 2; trivial.

Fixpoint pos_ord p :=
  match p with
  | P_Cst _ => (fun _ _ => empty)
  | P_Rec => (fun _ o => o)
  | P_Sum p1 p2 => 
     (fun i g =>
       sum_case i
         (fun i1 => pos_ord p1 i1 (g (inl i1)))
         (fun i2 => pos_ord p2 i2 (g (inr i2))))
  | P_ConsRec p1 p2 =>
     (fun i g => osup2 (pos_ord p1 (fst i) 


   intros.

auto.
    red; intro.


; auto.

 destruct H2.
 destruct H0; eauto.

 destruct H1.
 specialize H0 with (1:=H2).
 eauto.



trivial.
eauto.
 destruct H1; trivial.
 
 exists (osup2 x x0).
  apply isOrd_osup2; trivial.

  revert 
unfold p2P.

  unfold INDi in H4,H5|-*.

Definition fsub a := forall P, a \in pos_oper p P -> b \in P.

(* TODO: find an ordinal o such that IND = INDi o ... *)
