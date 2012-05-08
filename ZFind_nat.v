Require Import ZF ZFsum ZFfix ZFnats ZFrelations ZFord ZFcard (*ZFstable*) ZFcont.
Require Import ZFind_basic.
Import ZFrepl.

Section Nat_theory.

(***************************************************************************)
(* Natural numbers *)

Section TypeConstructor.

  Definition NATf X := sum UNIT X.

  Lemma sum_ext_natf : forall A, ext_fun A NATf.
do 2 red; intros.
unfold NATf.
rewrite H0; reflexivity.
Qed.

  Instance NATf_mono : Proper (incl_set ==> incl_set) NATf.
do 2 red; intros.
unfold NATf.
apply sum_mono; trivial.
red; trivial.
Qed.
Hint Resolve NATf_mono Fmono_morph.
  Instance NATf_morph : Proper (eq_set ==> eq_set) NATf.
apply Fmono_morph; trivial.
Qed.


Definition ZERO := inl zero.
Definition SUCC x := inr x.

  Lemma NATf_discr : forall n, ~ ZERO == SUCC n.
red; intros.
apply discr_sum in H; trivial.
Qed.

  Lemma SUCC_inj : forall n m, SUCC n == SUCC m -> n == m.
unfold SUCC.
apply inr_inj.
Qed.

  Lemma ZERO_typ_gen : forall X, ZERO ∈ sum UNIT X.
unfold ZERO; intros.
apply inl_typ.
apply unit_typ.
Qed.

  Lemma SUCC_typ_gen : forall x X, x ∈ X -> SUCC x ∈ sum UNIT X.
unfold SUCC; intros.
apply inr_typ; trivial.
Qed.

  Lemma NATf_case : forall X (P:Prop) x,
    (x == ZERO -> P) ->
    (forall n, n ∈ X -> x == SUCC n -> P) ->
    x ∈ NATf X -> P.
intros.
unfold NATf in H.
apply sum_ind with (3:=H1); intros.
 apply H.
 apply unit_elim in H2.
 rewrite H2 in H3; trivial.

 apply H0 with y; trivial.
Qed.

  Lemma SUCC_inv_typ_gen : forall X x,
    SUCC x ∈ NATf X -> x ∈ X.
intros.
apply NATf_case with (3:=H); intros.
 symmetry in H0; apply NATf_discr in H0; contradiction.

 apply SUCC_inj in H1; rewrite H1; trivial.
Qed.
(*
Lemma NATf_stable : stable NATf.
unfold NATf.
apply sum_stable.
 red; red; reflexivity.
 red; red; auto.

 apply cst_stable.
 apply id_stable.
Qed.

Lemma NATf_stable2 : stable2 NATf.
Proof stable2_weaker _ NATf_morph NATf_stable.
*)
End TypeConstructor.

Hint Resolve NATf_mono Fmono_morph.

Section IterationNat.

  Definition NATi := TI NATf.

  Instance NATi_morph : morph1 NATi.
unfold NATi; intros.
apply TI_morph; auto.
Qed.

  Lemma NATfun_ext : forall x, ext_fun x (fun n => NATf (NATi n)).
do 2 red; intros.
apply NATf_morph.
apply NATi_morph; trivial.
Qed.
Hint Resolve NATfun_ext.

(*
Lemma NATi_stable : stable_ord NATi.
apply TI_stable; auto.
apply NATf_stable.
Qed.

Lemma NATi_stable2 : stable2_ord NATi.
unfold NATi.
apply TI_stable2; auto.
apply NATf_stable2.
Qed.

Lemma NATfun_stable : stable_ord (fun n => NATf (NATi n)).
apply compose_stable with (F:=NATf) (G:=NATi); auto with *.
 apply NATf_stable.
 apply NATi_stable.
Qed.

Lemma NATfun_stable2 : stable2_ord (fun n => NATf (NATi n)).
red; red; intros.
apply NATf_stable2 in H1.
revert H1; apply NATf_mono.
apply NATi_stable2; trivial.
Qed.
*)

Lemma ZEROi_typ : forall o,
  isOrd o -> ZERO ∈ NATi (osucc o).
intros.
apply TI_intro with o; auto.
apply ZERO_typ_gen.
Qed.

Lemma SUCCi_typ : forall o n,
  isOrd o ->
  n ∈ NATi o ->
  SUCC n ∈ NATi (osucc o).
intros.
apply TI_intro with o; auto.
apply SUCC_typ_gen; trivial.
Qed.

Lemma SUCCi_inv_typ : forall o n,
  isOrd o ->
  SUCC n ∈ NATi (osucc o) ->
  n ∈ NATi o.
intros.
apply TI_elim in H0; auto.
destruct H0.
apply SUCC_inv_typ_gen in H1.
revert H1; apply TI_mono; trivial.
 apply isOrd_inv with (osucc o); auto.

 apply olts_le in H0; trivial.
Qed.

(* Case analysis *)

Section CaseAnalysis.

  (* Case scheme *)

  Lemma NATi_case : forall (P:set->Prop) o n,
    isOrd o ->
    (forall x x', x ∈ NATi o -> x == x' -> P x -> P x') ->
    P ZERO ->
    (forall m o', lt o' o -> m ∈ NATi o' -> P (SUCC m)) ->    
    n ∈ NATi o -> P n.
intros.
apply TI_elim in H3; auto.
destruct H3.
apply NATf_case with (3:=H4); intros.
 apply H0 with ZERO; trivial.
  apply TI_intro with x; auto.
  apply ZERO_typ_gen.

  symmetry; trivial.

 apply H0 with (SUCC n0); eauto.
 2:symmetry; trivial.
 apply TI_intro with x; auto.
 apply SUCC_typ_gen; auto.
Qed.

  (* Pattern-matching *)

  Variable fZ : set.
  Variable fS : set -> set.

  Definition NATCASE (n:set) :=
    cond_set (n==ZERO) fZ ∪
    cond_set (exists k,n==SUCC k) (fS (dest_sum n)).

Instance NATCASE_m1 : morph1 fS -> morph1 NATCASE.
do 2 red; intros.
unfold NATCASE.
apply union2_morph; apply cond_set_morph; auto with *.
 rewrite H0; reflexivity.

 apply ex_morph; red; intros.
 rewrite H0; reflexivity.

 rewrite H0; reflexivity.
Qed.


Lemma NATCASE_ZERO : NATCASE ZERO == fZ.
unfold NATCASE.
apply eq_set_ax; intros z.
rewrite union2_ax; do 2 rewrite cond_set_ax.
intuition.
destruct H1.
apply NATf_discr in H0; contradiction.
Qed.


Lemma NATCASE_SUCC : forall n,
  (forall x, x == n -> fS x == fS n) ->
  NATCASE (SUCC n) == fS n.
unfold NATCASE; intros.
apply eq_set_ax; intros z.
rewrite union2_ax; do 2 rewrite cond_set_ax.
split; intros.
 destruct H0 as [(_,?)|(?,(k,?))].
  symmetry in H0; apply NATf_discr in H0; contradiction.

  apply SUCC_inj in H1.
  rewrite H in H0; auto.
  apply dest_sum_inr.

 right; split.
  rewrite H; auto.
  apply dest_sum_inr.

  exists n; reflexivity.
Qed.

Lemma NATCASE_mt :
  NATCASE empty == empty.
unfold NATCASE.
apply empty_ext; red; intros.
rewrite union2_ax in H; do 2 rewrite cond_set_ax in H.
destruct H as [(_,?)|(_,(k,?))].
 (* ~ empty == ZERO *)
 unfold ZERO, inl, ZFpairs.couple in H.
 apply empty_ax with (singl zero).
 rewrite H.
 auto.

 (* ~ empty == SUCC _ *)
 unfold SUCC, inr, ZFpairs.couple in H.
 apply empty_ax with (singl (succ zero)).
 rewrite H.
 auto.
Qed.

Lemma NATCASE_typ :
  forall (P:set->set) o,
  morph1 P ->
  morph1 fS ->
  isOrd o ->
  fZ ∈ P ZERO ->
  (forall n, n ∈ NATi o -> fS n ∈ P (SUCC n)) ->
  forall n,
  n ∈ NATi (osucc o) ->
  NATCASE n ∈ P n.
intros.
pattern n; apply NATi_case with (o:=osucc o); intros; auto.
 rewrite <- H6; trivial.

 rewrite NATCASE_ZERO; trivial.

 rewrite NATCASE_SUCC; auto.
 apply H3.
 revert H6; apply TI_mono; auto.
  eauto using isOrd_inv.

  apply olts_le; trivial.
Qed.

End CaseAnalysis.

Lemma NATCASE_morph_gen : forall fZ fZ' fS fS' c c',
  c == c' ->
  fZ == fZ' ->
  (forall x x', c == SUCC x -> x == x' -> fS x == fS' x') ->
  NATCASE fZ fS c == NATCASE fZ' fS' c'.
unfold NATCASE; intros.
apply union2_morph; apply cond_set_morph2; intros; auto with *.
 rewrite H; reflexivity.

 apply ex_morph; red; intros.
 rewrite H; reflexivity.

 destruct H2.
 apply H1.
  rewrite H2; rewrite dest_sum_inr; reflexivity.

  rewrite H; reflexivity.
Qed.

Instance NATCASE_morph : Proper
  (eq_set ==> (eq_set ==> eq_set) ==> eq_set ==> eq_set) NATCASE.
do 4 red; intros.
apply NATCASE_morph_gen; auto.
Qed.

(* Fixpoints *)

Require Import ZFfunext ZFfixrec.

Section Recursor.

  Lemma NATi_fix :
    forall (P:set->Prop) o,
    isOrd o ->
    (forall i, isOrd i -> i ⊆ o ->
     (forall i' m, lt i' i -> m ∈ NATi i' -> P m) ->
     forall n, n ∈ NATi i -> P n) ->
    forall n, n ∈ NATi o -> P n.
intros P o is_ord Prec.
induction is_ord using isOrd_ind; intros; eauto.
Qed.


(* Recursor *)

  Notation prod := cc_prod.

  Variable ord : set.
  Hypothesis oord : isOrd ord.

  Variable F : set -> set -> set.
  Hypothesis Fm : morph2 F.

  Variable U : set -> set -> set.
  Hypothesis Umono : forall o o' x x',
    isOrd o' -> o' ⊆ ord -> isOrd o -> o ⊆ o' ->
    x ∈ NATi o -> x == x' ->
    U o x ⊆ U o' x'.

  Let Ty o := prod (NATi o) (U o).
  Hypothesis Ftyp : forall o f, isOrd o -> o ⊆ ord ->
    f ∈ Ty o -> F o f ∈ Ty (osucc o).

  Let Q o f := forall x, x ∈ NATi o -> cc_app f x ∈ U o x.

  Definition NAT_ord_irrel :=
    forall o o' f g,
    isOrd o' -> o' ⊆ ord -> isOrd o -> o ⊆ o' ->
    f ∈ Ty o -> g ∈ Ty o' ->
    fcompat (NATi o) f g ->
    fcompat (NATi (osucc o)) (F o f) (F o' g).

  Hypothesis Firrel : NAT_ord_irrel.

  Definition NATREC := REC F.

Lemma Umorph : forall o o', isOrd o' -> o' ⊆ ord -> o == o' ->
    forall x x', x ∈ NATi o -> x == x' -> U o x == U o' x'. 
intros.
apply incl_eq.
 apply Umono; auto.
  rewrite H1; trivial.
  rewrite H1; reflexivity.

 apply Umono; auto.
  rewrite H1; trivial.
  rewrite H1; trivial.
  rewrite H1; reflexivity.
  rewrite <- H3; rewrite <- H1; trivial.
  symmetry; trivial.
Qed.

Lemma Uext : forall o, isOrd o -> o ⊆ ord -> ext_fun (NATi o) (U o).
red; red; intros.
apply Umorph; auto with *.
Qed.


  Lemma NATREC_typing : forall o f, isOrd o -> o ⊆ ord -> 
    is_cc_fun (NATi o) f -> Q o f -> f ∈ Ty o.
intros.
rewrite cc_eta_eq' with (1:=H1).
apply cc_prod_intro; intros; auto.
 do 2 red; intros.
 rewrite H4; reflexivity.

 apply Uext; trivial.
Qed.


Lemma NATi_cont : forall o,
   isOrd o -> NATi o == sup o (fun o' => NATi (osucc o')).
intros.
unfold NATi; rewrite TI_eq; auto.
apply sup_morph; auto with *.
red; intros.
rewrite <- TI_mono_succ; eauto using isOrd_inv.
apply TI_morph; apply osucc_morph; trivial.
Qed.

Let Qm :
   forall o o',
   isOrd o ->
   o ⊆ ord ->
   o == o' -> forall f f', fcompat (NATi o) f f' -> Q o f -> Q o' f'.
intros.
unfold Q in H3|-*; intros.
rewrite <- H1 in H4.
specialize H3 with (1:=H4).
red in H2; rewrite <- H2; trivial.
revert H3; apply Umono; auto with *.
 rewrite <- H1; trivial.
 rewrite <- H1; trivial.
 rewrite <- H1; reflexivity.
Qed.

Let Qcont : forall o f : set,
 isOrd o ->
 o ⊆ ord ->
 is_cc_fun (NATi o) f ->
 (forall o' : set, o' ∈ o -> Q (osucc o') f) -> Q o f.
intros.
red; intros.
apply TI_elim in H3; auto.
destruct H3.
rewrite <- TI_mono_succ in H4; eauto using isOrd_inv.
generalize (H2 _ H3 _ H4).
apply Umono; eauto using isOrd_inv with *.
red; intros.
apply isOrd_plump with x0; eauto using isOrd_inv.
apply olts_le in H5; trivial.
Qed.

Let Qtyp : forall o f,
 isOrd o ->
 o ⊆ ord ->
 is_cc_fun (NATi o) f ->
 Q o f -> is_cc_fun (NATi (osucc o)) (F o f) /\ Q (osucc o) (F o f).
intros.
assert (F o f ∈ Ty (osucc o)).
 apply Ftyp; trivial.
 apply NATREC_typing; trivial.
split.
 apply cc_prod_is_cc_fun in H3; trivial.

 red; intros.
 apply cc_prod_elim with (1:=H3); trivial.
Qed.

  Lemma Firrel_NAT : stage_irrelevance ord NATi Q F.
red; red; intros.
destruct H1 as (oo,(ofun,oty)); destruct H2 as (o'o,(o'fun,o'ty)).
apply Firrel; trivial.
 apply NATREC_typing; trivial. 
 transitivity o'; trivial.

 apply NATREC_typing; trivial. 
Qed.
Hint Resolve Firrel_NAT.

  Lemma NAT_recursor : recursor ord NATi Q F.
constructor; trivial.
 apply TI_morph.

 apply NATi_cont.
Qed.

 Hint Resolve NAT_recursor.

  (* Main properties of NATREC: typing and equation *)
  Lemma NATREC_wt : NATREC ord ∈ Ty ord.
intros.
refine ((fun h => NATREC_typing
          ord (NATREC ord) oord (reflexivity _) (proj1 h) (proj2 h)) _).
apply REC_wt with (T:=NATi) (Q:=Q); auto.
Qed.

  Lemma NATREC_ord_irrel o o' x:
    isOrd o ->
    isOrd o' ->
    o ⊆ o' ->
    o' ⊆ ord ->
    x ∈ NATi o ->
    cc_app (NATREC o) x == cc_app (NATREC o') x.
intros.
apply REC_ord_irrel with (2:=NAT_recursor); auto with *.
Qed.


  Lemma NATREC_ext G :
    is_cc_fun (NATi ord) G ->
    (forall o', o' ∈ ord ->
     NATREC o' == cc_lam (NATi o') (cc_app G) ->
     fcompat (NATi (osucc o')) G (F o' (cc_lam (NATi o') (cc_app G)))) ->
    NATREC ord == G.
intros.
apply REC_ext with (T:=NATi) (Q:=Q); auto.
Qed.

  Lemma NATREC_expand : forall n,
    n ∈ NATi ord -> cc_app (NATREC ord) n == cc_app (F ord (NATREC ord)) n.
intros.
apply REC_expand with (T:=NATi) (Q:=Q); auto.
Qed.

  Lemma NATREC_eqn :
    NATREC ord == cc_lam (NATi ord) (cc_app (F ord (NATREC ord))).
apply REC_eqn with (Q:=Q); auto with *.
Qed.

End Recursor.


Instance NATREC_morph :
  Proper ((eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) NATREC.
do 3 red; intros.
unfold NATREC, REC.
apply TR_morph; trivial; intros.
do 2 red; intros.
apply sup_morph; intros; auto.
red; intros.
apply H; auto.
Qed.

Section NatFixpoint.

(** NAT : the least fixpoint (using continuity) *)

  Definition NAT := NATi omega.

  Lemma NAT_continuous : forall F,
    ext_fun omega F ->
    NATf (sup omega F) == sup omega (fun n => NATf (F n)).
intros.
unfold NATf.
rewrite <- sum_cont; auto.
rewrite <- cst_cont.
 reflexivity.

 exists zero; apply zero_omega.
Qed.

  Lemma NAT_eq : NAT == NATf NAT.
unfold NAT, NATi.
apply eq_intro; intros.
 rewrite <- TI_mono_succ; auto.
 apply TI_incl with omega; auto.

 unfold NATf in H at 1.
 rewrite TI_eq in H; auto.
 rewrite (cst_cont UNIT omega) in H; auto.
 2:exists zero; auto.
 rewrite sum_cont in H; auto.
 rewrite sup_ax in H.
 2:do 2 red; intros; apply NATf_morph; eapply NATfun_ext; eauto.
 destruct H.
 rewrite <- TI_mono_succ in H0; auto.
 apply TI_intro with (osucc x); auto.
 apply isOrd_inv with omega; trivial.
Qed.

  Lemma NATi_NAT : forall o,
    isOrd o ->
    NATi o ⊆ NAT.
induction 1 using isOrd_ind; intros.
unfold NATi.
rewrite TI_eq; auto.
red; intros.
rewrite sup_ax in H2; auto.
destruct H2.
rewrite NAT_eq.
apply NATf_mono with (NATi x); auto.
Qed.

  Lemma ZERO_typ : ZERO ∈ NAT.
rewrite NAT_eq.
apply ZERO_typ_gen.
Qed.

  Lemma SUCC_typ : forall n, n ∈ NAT -> SUCC n ∈ NAT.
intros.
rewrite NAT_eq.
apply SUCC_typ_gen; trivial.
Qed.

  Lemma NAT_fix :
    forall (P:set->Prop),
    (forall o, isOrd o ->
     (forall o' m, lt o' o -> m ∈ NATi o' -> P m) ->
     forall n, n ∈ NATi o -> P n) ->
    forall n, n ∈ NAT -> P n.
intros.
apply NATi_fix with (P:=P) (o:=omega); intros; auto.
apply H with i; trivial.
Qed.

  Lemma NAT_ind : forall (P:set->Prop),
    (forall x x', x ∈ NAT -> x == x' -> P x -> P x') ->
    P ZERO ->
    (forall n, n ∈ NAT -> P n -> P (SUCC n)) ->    
    forall n, n ∈ NAT -> P n.
intros.
elim H2 using NAT_fix; intros.
elim H5 using NATi_case; trivial; intros.
 apply H with x; trivial.
 apply NATi_NAT with o; trivial.

 apply H1; eauto.
 apply NATi_NAT with o'; trivial.
 apply isOrd_inv with o; trivial.
Qed.

  Fixpoint nat2NAT (n:nat) : set :=
    match n with
    | 0 => ZERO
    | S k => SUCC (nat2NAT k)
    end.

  Lemma nat2NAT_reflect : forall x,
    x ∈ NAT -> exists n, x == nat2NAT n.
intros.
elim H using NAT_ind; intros.
 destruct H2.
 exists x1.
 rewrite <- H1; rewrite H2; reflexivity.

 exists 0; reflexivity.

 destruct H1.
 exists (S x0); unfold SUCC; rewrite H1; reflexivity.
Qed.

End NatFixpoint.

End IterationNat.

(**)
Hint Resolve NATfun_ext.

Section NatConvergence.

(** Convergence (using closure property of ordinal) *)

Require Import ZFrank.

  Variable o : set.
  Hypothesis limo : limitOrd o.
  Hypothesis diro : isDir o.

  Let oo : isOrd o.
Proof proj1 limo.

  Let zer : forall x, x ∈ VN o -> zero ∈ VN o.
intros.
apply VN_incl with x; auto.
red; intros.
elim empty_ax with z; trivial.
Qed.

  Let suc : forall x, x ∈ VN o -> succ x ∈ VN o.
unfold succ.
intros.
apply VN_union; trivial.
apply VNlim_pair; auto.
apply VNlim_pair; auto.
Qed.

  Lemma NATf_size_gen :
    forall X, X ∈ VN o -> NATf X ∈ VN o.
intros.
unfold NATf.
unfold sum.
assert (zero ∈ VN o).
 apply VN_incl with X; trivial.
 red; intros.
 apply empty_ax in H0; contradiction.
assert (forall Y Z, Y ∈ VN o -> Z ∈ VN o -> ZFpairs.prodcart Y Z ∈ VN o).
 intros.
 unfold ZFpairs.prodcart.
 apply VN_subset; trivial.
 apply VNlim_power; trivial.
 apply VNlim_power; trivial.
 apply VN_union; trivial.
 apply VNlim_pair; trivial.
apply VN_union; trivial.
apply VNlim_pair; trivial.
 apply H1; eauto.
 apply VNlim_pair; trivial.

 apply H1; auto.
 apply VNlim_pair; trivial.
  apply VN_union; trivial.
  apply VNlim_pair; trivial.
  apply VNlim_pair; trivial.

  apply VN_union; trivial.
  apply VNlim_pair; trivial.
  apply VNlim_pair; trivial.
Qed.

  Hypothesis zer_o : zero ∈ VN o.

  Lemma NATf_size_gen_le : forall X,
    X ⊆ VN o -> NATf X ⊆ VN o.
red; intros.
apply NATf_case with (3:=H0); intros.
 rewrite H1.
 unfold ZERO, inl.
 unfold ZFpairs.couple.
 apply VNlim_pair; trivial.
  apply VNlim_pair; trivial.
  apply VNlim_pair; trivial.

 rewrite H2; unfold SUCC.
 unfold inr.
 unfold ZFpairs.couple.
 apply VNlim_pair; trivial.
  apply VNlim_pair; auto.

  apply VNlim_pair; auto.
Qed.

End NatConvergence.

  (* Showing that omega is the closing ordinal for NAT *)

  Lemma NAT_incl_omega : NAT ⊆ VN omega.
apply TI_pre_fix; auto.
apply NATf_size_gen_le; auto with *.
apply VN_intro; trivial.
apply zero_omega.
Qed.

  Lemma NAT_typ : forall o, isOrd o -> lt omega o -> NAT ∈ VN o.
intros.
rewrite VN_def; trivial.
exists omega; trivial.
apply NAT_incl_omega.
Qed.

End Nat_theory.

Hint Resolve NATf_mono Fmono_morph NATfun_ext.

(*******************************************************************************)
(** ** Applications *)

Module Example.
(** Abel's counter-example: *)

Definition U o := cc_arr (cc_arr NAT (NATi (osucc o))) NAT.

Definition shift f := cc_lam NAT (fun n =>
  NATCASE ZERO (fun m => m) (cc_app f (SUCC n))).

Lemma shift_typ : forall o f,
  isOrd o ->
  f ∈ cc_arr NAT (NATi (osucc (osucc o))) ->
  shift f ∈ cc_arr NAT (NATi (osucc o)).
intros.
unfold shift.
apply cc_arr_intro; intros.
 admit.
apply NATCASE_typ with (o:=osucc o)(P:=fun _=> NATi (osucc o)); auto.
 do 2 red; reflexivity.
 do 2 red; trivial.

 unfold NATi; rewrite TI_mono_succ; auto.
 apply ZERO_typ_gen.

 apply cc_arr_elim with (1:=H0).
 apply SUCC_typ; trivial.
Qed.

Definition loopF o loop :=
  cc_lam (NATi (osucc o)) (fun _ =>
  cc_lam (cc_arr NAT (NATi (osucc (osucc o)))) (fun f =>
  NATCASE
    ZERO
    (fun n =>
     NATCASE
       ZERO
       (fun m => cc_app (cc_app loop m) (shift f))
       n)
    (cc_app f ZERO))).

Lemma loopF_typ : forall o lp,
  isOrd o ->
  lp ∈ cc_arr (NATi o) (U o) ->
  loopF o lp ∈ cc_arr (NATi (osucc o)) (U (osucc o)).
unfold loopF, U; intros.
apply cc_arr_intro;[| intros y ?].
 do 2 red; reflexivity.
apply cc_arr_intro;[|intros f ?].
 admit.
apply NATCASE_typ with (o:=osucc o) (P:=fun _ => NAT); auto.
 do 2 red; reflexivity.
 admit.

 apply ZERO_typ.

 intros.
 apply NATCASE_typ with (o:=o) (P:=fun _=>NAT); auto.
  do 2 red; reflexivity.
  admit.

  apply ZERO_typ.

  intros.
  apply cc_arr_elim with (cc_arr NAT (NATi (osucc o))).
   apply cc_arr_elim with (NATi o); trivial.

   apply shift_typ; trivial.

 apply cc_arr_elim with NAT; trivial.
 apply ZERO_typ.
Qed.

 (* loopF satisfies the stability criterion, but the fixpoint cannot be accepted *)

 Lemma sfp : forall o, isOrd o ->
   NAT_ord_irrel o loopF (fun o' x => U o').
intros eps oeps o o' f f' o'o o'eps oo ole tyf tyf' eqf x tyx.
unfold loopF.
rewrite cc_beta_eq; auto.
rewrite cc_beta_eq; auto.
 apply cc_lam_ext.
  admit. (* not provable (we're assuming we can have with multiple recursive arguments) *) 

  red; intros.
  apply NATCASE_morph_gen; intros; auto with *.
   rewrite H0; auto with *.
  apply NATCASE_morph_gen; intros; auto with *.
  apply cc_app_morph.
   rewrite <- H4.
   apply eqf.
   apply SUCCi_inv_typ; trivial.
   rewrite <- H3.
   apply SUCCi_inv_typ; auto.
   rewrite <- H1.
   apply cc_arr_elim with (1:=H).
   apply ZERO_typ.

   unfold shift.
   apply cc_lam_ext; auto with *.
   red; intros.
   apply NATCASE_morph; auto with *.
    red; intros; auto.

    rewrite H0; rewrite H6; reflexivity.

 revert tyx; apply TI_mono; auto with *.
 red; intros.
 apply ole_lts; eauto using isOrd_inv.
 apply olts_le in H.
 transitivity o; trivial.
Qed.

End Example.
