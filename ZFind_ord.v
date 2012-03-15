Require Import ZF ZFsum ZFfix ZFnats ZFrelations ZFord ZFcard ZFcont.
Require Import ZFstable ZFrank ZFgrothendieck ZFinaccessible.
Require Import ZFind_basic ZFind_nat.
Import ZFrepl.

Section Ord_theory.

(***************************************************************************)
(* Ordinals *)

  Definition ORDf X := sum UNIT (func NAT X).

  Lemma sum_ext_ordf : forall A, ext_fun A ORDf.
do 2 red; intros.
unfold ORDf.
rewrite H0; reflexivity.
Qed.

  Instance ORDf_mono : Proper (incl_set ==> incl_set) ORDf.
do 2 red; intros.
unfold ORDf.
apply sum_mono; trivial.
red; trivial.
apply func_mono; trivial.
reflexivity.
Qed.
Hint Resolve ORDf_mono.
  Instance ORDf_morph : Proper (eq_set ==> eq_set) ORDf.
apply Fmono_morph; trivial.
Qed.

  Definition LIM f := inr f.

  Lemma LIM_typ_gen : forall x X, x \in func NAT X -> LIM x \in sum UNIT (func NAT X).
unfold LIM; intros.
apply inr_typ; trivial.
Qed.

  Lemma ORDf_case : forall X (P:Prop) x,
    (x == ZERO -> P) ->
    (forall f, f \in func NAT X -> x == LIM f -> P) ->
    x \in ORDf X -> P.
intros.
unfold ORDf in H.
apply sum_ind with (3:=H1); intros.
 apply H.
 apply unit_elim in H2.
 rewrite H2 in H3; trivial.

 apply H0 with y; trivial.
Qed.

Lemma ORDf_stable : stable ORDf.
unfold ORDf.
apply sum_stable.
 red; red; reflexivity.
 red; red; intros.
 rewrite H; reflexivity.

 apply cst_stable.
 apply func_stable.
Qed.

Lemma ORDf_stable2 : stable2 ORDf.
Proof stable2_weaker _ ORDf_morph ORDf_stable.


Section IterationOrd.

  Definition ORDi := TI ORDf.

  Instance ORDi_morph : morph1 ORDi.
unfold ORDi; do 2 red; intros.
apply TI_morph; trivial.
Qed.

  Lemma ORDi_stable : stable_ord ORDi.
unfold ORDi.
apply TI_stable; auto.
apply ORDf_stable.
Qed.

  Lemma ORDi_stable2 : stable2_ord ORDi.
unfold ORDi.
apply TI_stable2; auto.
apply ORDf_stable2.
Qed.

  Lemma ORDfun_ext : forall x, ext_fun x (fun n => ORDf (ORDi n)).
do 2 red; intros.
apply ORDf_morph.
apply ORDi_morph; trivial.
Qed.
Hint Resolve ORDfun_ext.

  Lemma ORDfun_stable : stable_ord (fun n => ORDf (ORDi n)).
apply compose_stable with (F:=ORDf) (G:=ORDi); auto with *.
 apply ORDf_stable.
 apply ORDi_stable.
Qed.

  Lemma ORDfun_stable2 : stable2_ord (fun n => ORDf (ORDi n)).
red; red; intros.
apply ORDf_stable2 in H1.
revert H1; apply ORDf_mono.
apply ORDi_stable2; trivial.
Qed.

  Lemma ORDi_case : forall (P:set->Prop) o n,
    isOrd o ->
    (forall x x', x \in ORDi o -> x == x' -> P x -> P x') ->
    P ZERO ->
    (forall f o', lt o' o -> f \in func NAT (ORDi o') -> P (LIM f)) ->    
    n \in ORDi o -> P n.
intros.
apply TI_elim in H3; auto.
destruct H3.
apply ORDf_case with (3:=H4); intros.
 apply H0 with ZERO; trivial.
  apply TI_intro with x; auto.
  apply ZERO_typ_gen.

  symmetry; trivial.

 apply H0 with (LIM f); eauto.
 2:symmetry; trivial.
 apply TI_intro with x; auto.
 apply LIM_typ_gen; auto.
Qed.

  Lemma ORDi_fix :
    forall (P:set->Prop) o,
    isOrd o ->
    (forall i, isOrd i -> i \incl o ->
     (forall i' m, lt i' i -> m \in ORDi i' -> P m) ->
     forall n, n \in ORDi i -> P n) ->
    forall n, n \in ORDi o -> P n.
intros P o is_ord Prec.
induction is_ord using isOrd_ind; intros; eauto.
Qed.

End IterationOrd.

Hint Resolve ORDfun_ext.

Require Import ZFind_w.
Definition ORDf_clos :=
  let A := NATf (NATf empty) in
  let B x := NATCASE empty (fun _ => NAT) x in
  W_ord A B.

Instance Bm : morph1 (fun x => NATCASE empty (fun _ => NAT) x).
do 2 red; intros.
apply NATCASE_morph; auto with *.
red; intros; auto with *.
Qed.

Lemma ordOc : isOrd ORDf_clos.
apply W_o_o; auto with *.
Qed.
Hint Resolve ordOc.

(*
  Lemma ORDf_cont0 : forall F,
    stable_ord F ->
    increasing F ->
    ORDf (sup ORDf_clos F) \incl sup ORDf_clos (fun A => ORDf (F A)).
unfold ORDf.
intros.
rewrite <- sum_cont; auto.
rewrite <- cst_cont; eauto.
2:admit.
apply sum_mono; auto with *.
red; intros.

apply func_cont_gen; auto. (* uses boundo *)
*)

Section OrdConvergence.

(*
  Let o := hartog_succ NAT.

Lemma boundo :
    forall F,
    ext_fun NAT F -> 
    (forall n, n \in NAT -> lt (F n) o) ->
    lt (sup NAT F) o.
intros.
apply hartog_bound; trivial.
Qed.

Lemma zer_h : zero \in o.
unfold o, hartog_succ.
rewrite sup_ax.
2:admit.
exists empty.
 apply subset_intro.
  unfold rel; apply power_intro; intros.
  elim empty_ax with z; trivial.

  constructor; intros.
  red in H.
  elim empty_ax with (1:=H).

 unfold order_type.
 rewrite sup_ax.
 2:apply ot_ext; reflexivity.
 exists ZERO.
  apply ZERO_typ.

  unfold osucc; apply subset_intro; auto.
  apply power_intro; intros.
  elim empty_ax with z; trivial.
Qed.

Lemma limo : limitOrd o.
split.
 apply isOrd_hartog.
intros.
unfold o, hartog_succ in *.
rewrite sup_ax in H|-*.
2:admit.
2:admit.
destruct H as (R,woR,otR).
Require Import ZFpairs.
pose (R' :=
   union2
    (replf R (fun p => couple (SUCC (fst p)) (SUCC (snd p)))) (* shift R *)
    (replf NAT (fun n => couple (SUCC n) ZERO))). (* put 0 above all elements of R *)
assert (Rax: forall y z, rel_app R' y z <->
  exists2 y', y == SUCC y' /\ y' \in NAT &
  (exists2 z', z==SUCC z' & rel_app R y' z') \/ z == ZERO).
 split; intros.
  apply union2_elim in H; destruct H.
   rewrite replf_ax in H.
   2:admit.
   destruct H.
   apply couple_injection in H0; destruct H0.
   exists (fst x0).
    split; trivial.
    apply fst_typ with NAT.
    apply power_elim with R; trivial.
    apply subset_elim1 in woR; trivial.
   left.
   exists (snd x0); trivial.
   red; rewrite <- (@surj_pair x0 NAT NAT); trivial.
   apply power_elim with R; trivial.
   apply subset_elim1 in woR; trivial.

   rewrite replf_ax in H.
   2:admit.
   destruct H.
   apply couple_injection in H0; destruct H0.
   exists x0; auto.

  destruct H as (y',(?,?),[(z',?,?)|?]).
   apply union2_intro1.
   apply replf_intro with (couple y' z'); auto.
    admit.
    rewrite fst_def; rewrite snd_def.
    rewrite H; rewrite H1; reflexivity.

   apply union2_intro2.
   apply replf_intro with y'; auto.
    admit.
    rewrite H; rewrite H1; reflexivity.
assert (R' \in wo NAT).
 apply subset_intro.
Lemma union2_rel : forall A B r1 r2,
  r1 \in rel A B -> r2 \in rel A B -> union2 r1 r2 \in rel A B.
intros.
apply power_intro; intros.
apply union2_elim in H1; destruct H1.
 apply power_elim with r1; trivial.
 apply power_elim with r2; trivial.
Qed.
  (* REL *)
  apply union2_rel.
   apply power_intro; intros.
   rewrite replf_ax in H.
   2:admit.
   destruct H.
   rewrite H0.
   apply couple_intro.
    apply SUCC_typ.
    apply fst_typ with NAT.
    apply power_elim with R; trivial.
    apply subset_elim1 in woR; trivial.

    apply SUCC_typ.
    apply snd_typ with NAT.
    apply power_elim with R; trivial.
    apply subset_elim1 in woR; trivial.

   apply power_intro; intros.
   rewrite replf_ax in H.
   2:admit.
   destruct H.
   rewrite H0.
   apply couple_intro.
    apply SUCC_typ; trivial.
    apply ZERO_typ.

 (* WO *)
 red; intros.
 assert (forall n y, y == SUCC n -> Acc (rel_app R') y). 
  intro n.
  induction (wo_def2 _ _ woR n).
  constructor; intros.
  rewrite Rax in H2; destruct H2 as (y',(?,?),[(z',?,?)|?]).
   apply H0 with y'; trivial.
   rewrite H1 in H4; apply SUCC_inj in H4; rewrite H4; trivial.

   rewrite H4 in H1; apply NATf_discr in H1; contradiction.
 constructor; intros.
 rewrite Rax in H0; destruct H0 as (y',(?,?),_).
 apply H with y'; trivial.

exists R'; trivial.
 apply wo_def2 in H.
 (* OT *)
 unfold order_type in otR|-*.
 rewrite sup_ax in otR|-*.
 2:admit.
 2:admit.
 exists ZERO; [apply ZERO_typ|].
 apply lt_osucc_compat.
  apply order_type_assign_ord with NAT R' ZERO.
  apply uchoice_def.
  apply order_type_assign_uchoice; trivial.

  rewrite order_type_assign_rel_inv'; trivial.
  rewrite sup_ax.
  2:admit.
  destruct otR.
  exists (SUCC x0).
   apply subset_intro.
    apply SUCC_typ; trivial.

    rewrite Rax.
    exists x0; auto with *.

   assert (forall n, n \in NAT -> forall x,
     order_type_assign_rel NAT R n x -> order_type_assign_rel NAT R' (SUCC n) x).
    intros.
    apply H3; intros.
     admit.

     red; intros.
     setoid_replace (sup x' (fun y => osucc (f y))) with
       (sup (subset NAT (fun y => rel_app R' y (SUCC x2)))
         (fun y => osucc (f (pred y)))).
admit.
admit.
   generalize (uchoice_def _ (order_type_assign_uchoice NAT _ x0 (wo_def2 _ _ woR))); intro.
   apply H2 in H3; trivial. 
   rewrite <- (uchoice_ext _ (uchoice (order_type_assign_rel NAT R x0))
       (order_type_assign_uchoice NAT _ (SUCC x0) H)); trivial.
Qed.

  Lemma nato : lt omega o.
pose (NtoO := fun n m => exists2 n', n == nat2NAT n' &
      m == (fix F n := match n with 0 => zero | S k => osucc (F k) end) n').
assert (forall n, n \in NAT -> uchoice_pred (NtoO n)).
 admit.
setoid_replace omega with (sup NAT (fun n => uchoice (NtoO n))).
 apply boundo.
  admit.

  intros.
  apply nat2NAT_reflect in H0.
  destruct H0.
  revert n H0.
  induction x; simpl; intros.
   admit.
   admit.

apply sup_ext.
 admit.

 intros.
 admit.

 intros.
 unfold omega in H0.
 unfold ord_sup in H0.
 apply union_elim in H0; destruct H0.
 apply repl_elim in H1.
 2:admit.
 destruct H1.
 destruct H2.
 exists (nat2NAT x1).
  elim x1; simpl.
   apply ZERO_typ.
   intros.
   apply SUCC_typ; trivial.

  admit.
Qed.
*)

  Variable o : set.
Hypothesis zer_o : zero \in o.
  Hypothesis limo : limitOrd o.
(*  Hypothesis nato : lt omega o.*)
  Hypothesis boundo :
    forall F,
    ext_fun NAT F -> 
    (forall n, n \in NAT -> lt (F n) o) ->
    lt (osup NAT F) o.

  Let oo : isOrd o.
Proof proj1 limo.

  Lemma diro : isDir o.
red; intros.
pose (P n z := n == ZERO /\ z == x \/ ~ n == ZERO /\ z == y).
assert (eP : ext_fun NAT (fun n => uchoice (P n))).
 red; red ;intros.
 apply uchoice_morph_raw.
 red ;intros.
 unfold P.
 rewrite H2; rewrite H3.
 reflexivity.
assert (forall n, n \in NAT -> uchoice_pred (P n)).
 split; intros.
  revert H3; unfold P; rewrite H2; trivial.

  split; intros.
   apply NATi_case with (5:=H1); auto with *.
    intros.
    destruct H4.
    exists x1.
    revert H4; unfold P; rewrite H3; trivial.

    exists x; left; auto with *.

    intros.
    exists y; right; split; auto with *.
    red; intros.
    symmetry in H4; apply NATf_discr in H4; contradiction.

   destruct H2 as [(e1,r1)|(e1,r1)];
   destruct H3 as [(e2,r2)|(e2,r2)];
   rewrite r1; rewrite r2; try reflexivity.
   elim e2; trivial.
   elim e1; trivial.

exists (osup NAT (fun n => uchoice (P n))).
 apply boundo; trivial.
  intros.
  assert (P n (uchoice (P n))).
   apply uchoice_def; auto.
  destruct H3 as [(_,e)|(_,e)]; rewrite e; trivial.

 split.
  assert (t0 := ZERO_typ).
  assert (P ZERO (uchoice (P ZERO))).
   apply uchoice_def; auto.
  destruct H2 as [(_,e)|(d,_)].
   red; intros.
   apply osup_intro with (x:=ZERO); trivial.
   rewrite e; trivial.

   elim d; reflexivity.

  red; intros.
  assert (t1 : SUCC ZERO \in NAT).
   apply SUCC_typ; apply ZERO_typ.
  apply osup_intro with (x:=SUCC ZERO); trivial.
  assert (P (SUCC ZERO) (uchoice (P (SUCC ZERO)))).
   apply uchoice_def; auto.
  destruct H3 as [(d,_)|(_,e)].
   symmetry in d; apply NATf_discr in d; contradiction.

   rewrite e; trivial.
Qed.
Hint Resolve diro.

  Let zer : zero \in VN o.
intros.
apply VN_intro; auto.
Qed.

  Let suc : forall x, x \in VN o -> succ x \in VN o.
unfold succ.
intros.
apply VN_union; trivial.
apply VNlim_pair; auto.
apply VNlim_pair; auto.
Qed.

  Let NATo : NAT \in VN o.
apply NAT_typ; trivial.
admit. (* this is the real hyp. *)
Qed.

  Lemma ORDf_size_gen :
    forall X, X \in VN o -> ORDf X \in VN o.
intros.
unfold ORDf.
unfold sum.
apply VN_subset; trivial.
unfold ZFpairs.prodcart.
apply VN_subset; trivial.
apply VNlim_power; trivial.
apply VNlim_power; trivial.
apply VN_union; trivial.
apply VNlim_pair; auto.
apply VN_union; trivial.
apply VNlim_pair; trivial.
 unfold UNIT; auto.
unfold func.
apply VN_subset; trivial.
unfold rel.
apply VNlim_power; trivial.
unfold ZFpairs.prodcart.
apply VN_subset; trivial.
apply VNlim_power; trivial.
apply VNlim_power; trivial.
apply VN_union; trivial.
apply VNlim_pair; trivial.
Qed.

  Lemma ORDf_size_gen_le : forall X,
    X \incl VN o -> ORDf X \incl VN o.
red; intros.
apply ORDf_case with (3:=H0); intros.
 rewrite H1.
 unfold ZERO, inl.
 unfold ZFpairs.couple.
 apply VNlim_pair; trivial.
  apply VNlim_pair; trivial.
  apply VNlim_pair; trivial.

 rewrite H2; unfold LIM.
 unfold inr.
 unfold ZFpairs.couple.
 apply VNlim_pair; trivial.
  apply VNlim_pair; auto.

Import ZFrelations.
  apply VNlim_pair; auto.
  pose (F n := inter (subset o (fun x => ZFpairs.couple  n (app f n) \in VN x))).
  assert (eS : ext_fun (func NAT o) (fun f0 => sup NAT (app f0))).
   red; red; intros.
   apply sup_morph; auto with *.
   red; intros.
   apply app_morph; trivial.
  assert (eF : ext_fun NAT F).
   red; red; intros.
   apply inter_morph.
   apply subset_morph; auto with *.
   red; intros.
   rewrite H4; reflexivity.
  assert (pF : forall n, n \in NAT -> lt (F n) o /\ ZFpairs.couple n (app f n) \in VN (F n)). 
   intros.
   assert (app f n \in X).
    apply app_typ with NAT; auto.
   generalize (H _ H4); intros.
   rewrite VN_def in H5; auto.
   destruct H5.
   assert (n \in VN o).
    apply VN_trans with NAT; trivial.
   rewrite VN_def in H7; auto.
   destruct H7.
   destruct (diro x (osucc x0)); auto.
    apply limo; trivial.
   destruct H10.
   assert (o1 : isOrd x1).
    apply isOrd_inv with o; trivial.



   assert (ZFpairs.couple n (app f n) \in VN (osucc (osucc (osucc x1)))).
    assert (n \in VN (osucc x1)).
     apply VN_incl with (VN x0); auto.
     apply VN_mono; auto.
     apply oles_lt in H11; trivial.
      apply isOrd_trans with x1; auto. 

      apply isOrd_inv with o; auto.
    apply VNsucc_pair; auto.
     apply VNsucc_pair; auto.

     apply VNsucc_pair; auto.
     apply VN_incl with (VN x); auto.
     apply VN_mono; auto.
     apply ole_lts; auto.
     apply isOrd_inv with o; trivial.
   split.
    apply isOrd_plump with (osucc (osucc (osucc x1))); trivial.
     apply isOrd_inter; intros.
     apply subset_elim1 in H13; eauto using isOrd_inv.

     red; intros.
     apply inter_elim with (1:=H13).
     apply subset_intro; auto.
     repeat apply limo; trivial.

     repeat apply limo; trivial.

     apply VN_stable; intros.
      apply subset_elim1 in H13.
      apply isOrd_inv with o; trivial.

      apply inter_intro.
       intros.
       rewrite replf_ax in H13.
       2:red; red; intros; apply VN_morph; trivial.
       destruct H13.
       rewrite H14.
       apply subset_elim2 in H13; destruct H13.
       rewrite H13; trivial.

       exists (VN (osucc(osucc(osucc x1)))); intros.
       rewrite replf_ax.   
       2:red; red; intros; apply VN_morph; trivial.
       exists (osucc(osucc(osucc x1))); auto with *.
       apply subset_intro; trivial.
       repeat apply limo; trivial.
  assert (lt (osup NAT F) o).
   apply boundo; auto.
   intros; apply pF; trivial.
(*   apply isOrd_plump with (4:=bound); auto.
    apply isOrd_supf; intros; auto.
    apply isOrd_inv with o; trivial.
    apply pF; trivial.

    red; intros.
    rewrite sup_ax; trivial.
    exists (lam NAT F).
     apply lam_is_func; auto.
     intros; apply pF; auto.

     apply eq_elim with (2:=H3).
     apply sup_morph; auto with *.
     red; intros.
     rewrite beta_eq; auto.
     rewrite <- H5; trivial.*)
  specialize func_eta with (1:=H1); intros.
  rewrite H4.
  unfold lam.
  apply VN_incl with (VN (osup NAT F)); auto.
   assert (eSS : ext_fun NAT (fun x : set => singl (ZFpairs.couple x (app f x)))).
    red; red; intros.
    rewrite H6; reflexivity.
   setoid_replace (replf NAT (fun x => ZFpairs.couple x (app f x)))
     with (sup NAT (fun x => singl (ZFpairs.couple x (app f x)))).
    red; intros.
    rewrite sup_ax in H5; trivial.
    destruct H5.
    apply singl_elim in H6.
    rewrite H6.
    apply VN_mono_le with (o:=F x); auto.
     apply isOrd_inv with o; auto.
     apply pF; trivial.

     apply isOrd_osup; trivial; intros.
     apply isOrd_inv with o; auto.
     apply pF; trivial.

     apply osup_intro; trivial.

     apply pF; trivial.
    assert (ext_fun NAT (fun x : set => ZFpairs.couple x (app f x))).
     red; red; intros.
     rewrite H6; reflexivity.
    apply eq_intro; intros.
     rewrite replf_ax in H6; auto.
     rewrite sup_ax; auto.
     destruct H6.
     exists x; trivial.
     rewrite H7; apply singl_intro.

     rewrite replf_ax; auto.
     rewrite sup_ax in H6; auto.
     destruct H6.
     exists x; trivial.
     apply singl_elim in H7; trivial.

 apply VN_mono; auto.
Qed.

  Lemma ORDi_incl_o : ORDi o \incl VN o.
apply TI_pre_fix; auto.
apply ORDf_size_gen_le; auto with *.
Qed.

  Lemma ORDi_typ : forall mu, isOrd mu -> lt o mu -> ORDi o \in VN mu.
intros.
rewrite VN_def; trivial.
exists o; trivial.
apply ORDi_incl_o.
Qed.


  Lemma ORDf_cont : forall F,
    stable_ord F ->
    increasing F ->
    ORDf (sup o F) \incl sup o (fun A => ORDf (F A)).
unfold ORDf.
intros.
rewrite <- sum_cont; auto.
rewrite <- cst_cont.
2:exists zero; trivial.
apply sum_mono; auto with *.
apply func_cont_gen; auto. (* uses boundo *)
Qed.

(* least fixpoint reached at ordinal o *)
  Lemma ORDo_pre : ORDf (ORDi o) \incl ORDi o.
red; intros.
assert (ORDi o \incl sup o ORDi).
 red; intros.
 apply TI_elim in H0; auto.
 destruct H0.
 rewrite sup_ax; auto.
  exists (osucc x); auto.
   apply limo; trivial.

   unfold ORDi; rewrite TI_mono_succ; auto.
   apply isOrd_inv with o; auto.

  red; red; intros; apply ORDi_morph; trivial.
assert (z \in ORDf (sup o ORDi)).
 revert H; apply ORDf_mono; auto with *.
apply ORDf_cont in H1.
 rewrite sup_ax in H1; auto.
 destruct H1.
 apply TI_intro with x; auto.

 apply ORDi_stable.

 apply TI_mono; trivial.
Qed.

  Lemma ORDo_fix : ORDi o == ORDf (ORDi o).
apply eq_intro; intros.
 rewrite <- TI_mono_succ; auto.
 apply TI_incl with o; auto.

 apply ORDo_pre; trivial.
Qed.

  Lemma ORDi_ORD : forall x,
    isOrd x ->
    ORDi x \incl ORDi o.
induction 1 using isOrd_ind; intros.
unfold ORDi at 1.
rewrite TI_eq; auto.
red; intros.
rewrite sup_ax in H2; auto.
destruct H2.
rewrite ORDo_fix.
apply ORDf_mono with (ORDi x0); auto.
Qed.


End OrdConvergence.


Section OrdFixpoint.

Require Import ZFgrothendieck ZFinaccessible.

  Variable U : set.
  Hypothesis Ug : grot_univ U.
  Hypothesis Uw : omega \in U.

  Notation mu := (grot_ord U).

  Let mu_ord : isOrd mu.
auto.
Qed.

  Let mu_lim : limitOrd mu.
split; trivial.
apply G_limit; trivial.
Qed.

  Let mu_reg : VN_regular mu.
apply VN_regular_weaker.
apply G_regular; trivial.
Qed.

Section FirstAttempt.
(* We can already build the fixpoint (at iteration mu), but we cannot
   prove we stay within the universe U *)
(*
  Let mu_dir : isDir mu.
apply isDir_regular; trivial.
 apply G_limit; trivial.

 apply G_regular; trivial.
Qed.
*)
  Let mu_omega : lt omega mu.
apply grot_ord_inv; trivial.
Qed.

  Lemma NATf_size_mu : forall X, X \in VN mu -> NATf X \in VN mu.
apply NATf_size_gen; trivial.
Qed.

  Lemma NAT_in_mu : NAT \in VN mu.
apply NAT_typ; trivial.
Qed.

  Definition ORD := ORDi mu.

  Lemma ORD_eq : ORD == ORDf ORD.
apply ORDo_fix; trivial.
 apply isOrd_trans with omega; trivial.
intros.
apply VN_reg_ord; trivial.
apply NAT_in_mu.
Qed.

  Lemma ORD_weak_typ : ORD \incl VN mu.
apply ORDi_incl_o; trivial.
 apply isOrd_trans with omega; trivial.
intros.
apply VN_reg_ord; trivial.
apply NAT_in_mu.
Qed.
End FirstAttempt.


(*****)
(* Building a bound to the cardinal of NAT, following ZFind_w *)
Require Import ZFlist.

Definition Ndom := subset (power (List NAT)) (fun X => Nil \in X).

Require Import ZFcoc.

Definition Nsup x :=
  union2 (singl Nil)
   (sup (fst x) (fun y =>
      replf (cc_app (snd x) y) (fun p => Cons y p))).

Definition N_F X := sigma (power NAT) (fun Y => cc_arr Y X).

Lemma Nsup_morph : forall X, ext_fun (N_F X) Nsup.
Admitted.
(*
do 2 red; intros.
unfold Wsup.
apply union2_morph.
 rewrite H0; reflexivity.

 apply sup_morph.
  apply Bext.
   apply fst_typ_sigma in H; trivial.
   apply fst_morph; trivial.

  red; intros.
  apply replf_morph_raw; auto.
   rewrite H0; rewrite H2; reflexivity.

   red; intros.
   rewrite H2; rewrite H3; reflexivity.
Qed.
*)
Lemma wext1 : forall i y,
  ext_fun y (fun p => Cons i p).
Admitted.

Lemma wext2 : forall X g,
  ext_fun X (fun y => replf (cc_app g y) (fun p => Cons y p)).
Admitted.
(*
do 2 red; intros.
apply replf_morph_raw; auto.
 rewrite H0; reflexivity.

 red; intros.
 rewrite H0; rewrite H1; reflexivity.
Qed.*)
Hint Resolve wext1 wext2.

Lemma Nsup_def :
  forall x p,
  (p \in Nsup x <->
   p == Nil \/
   exists2 i, i \in fst x &
   exists2 q, q \in cc_app (snd x) i & p == Cons i q).
intros x p; intros.
unfold Nsup.
split; intros.
 apply union2_elim in H; destruct H;[left|right].
  apply singl_elim in H; trivial.

  rewrite sup_ax in H; auto.
  destruct H as (i,?,?); exists i; trivial.
  rewrite replf_ax in H0; trivial.

 destruct H as [eqp|(i,?,(q,?,eqp))]; rewrite eqp; clear eqp.  
  apply union2_intro1.
  apply singl_intro.

  apply union2_intro2.
  rewrite sup_ax; auto.
  exists i; trivial.
  rewrite replf_ax; trivial.
  exists q; auto with *.
Qed.

Lemma Nsup_hd_prop : forall x, Nil \in Nsup x.
intros.
unfold Nsup.
apply union2_intro1.
apply singl_intro.
Qed.

Lemma Nsup_tl_prop : forall X i l x,
  x \in N_F X ->
  X \incl Ndom ->
  (Cons i l \in Nsup x <-> i \in fst x /\ l \in cc_app (snd x) i).
intros X i l x H inclX.
assert (tyx : fst x \in power NAT).
 apply fst_typ_sigma in H; trivial.
split; intros.
 apply union2_elim in H0; destruct H0.
  apply singl_elim in H0.
  symmetry in H0.
  apply discr_mt_pair in H0; contradiction.

  rewrite sup_ax in H0; auto.
  destruct H0.
  rewrite replf_ax in H1; trivial.
  destruct H1.
  apply couple_injection in H2; destruct H2.
  rewrite H2.
  split; trivial.
  rewrite H3; trivial.

 destruct H0.
 unfold Wsup.
 apply union2_intro2.
 rewrite sup_ax; auto.
 exists i; trivial.
 rewrite replf_ax; trivial.
 exists l; auto with *.
Qed.

Lemma Nsup_inj : forall X Y x x',
  X \incl Ndom ->
  Y \incl Ndom ->
  x \in N_F X ->
  x' \in N_F Y ->
  Nsup x == Nsup x' -> x == x'.
Admitted.
(*intros X Y x x' tyf tyf' H H0 H1.
assert (fst x == fst x').
  assert (forall i l, i \in fst x /\ l \in cc_app (snd x) i <->
                      i \in fst x' /\ l \in cc_app (snd x') i).
   intros.
   rewrite <- Nsup_tl_prop with (1:=H); trivial.
   rewrite H1.
   apply Nsup_tl_prop with (1:=H0); trivial.
 generalize (Nsup_tl_prop x); intro.
 generalize (Nsup_hd_prop x'); intro.
 apply H3.
 rewrite <- H1.
 apply H2.
 reflexivity.
assert (snd x == snd x').
 specialize cc_eta_eq with (1:=tys _ _ H); intros.
 specialize cc_eta_eq with (1:=tys _ _ H0); intros.
 rewrite H3; rewrite H4.
 apply cc_lam_ext.
  apply Bext; trivial.
  apply fst_typ_sigma in H; trivial.

  red; intros.
  assert (x'0 \in B (fst x')).
   revert H5; apply in_set_morph; auto with *.
   apply Bext; auto with *.
   apply fst_typ_sigma in H0; trivial.
  assert (cc_app (snd x) x0 \incl prodcart (List (sup A B)) A).
   red; intros.
   apply power_elim with (2:=H8).
   apply tyf.
   apply cc_prod_elim with (1:=tys _ _ H); trivial.
  assert (cc_app (snd x') x'0 \incl prodcart (List (sup A B)) A).
   red; intros.
   apply power_elim with (2:=H9); trivial.
   apply tyf'.
   apply cc_prod_elim with (1:=tys _ _ H0); trivial.
  generalize (fun z l => Wsup_tl_prop _ x0 l z _ H tyf); intros.
  generalize (fun z l => Wsup_tl_prop _ x'0 l z _ H0 tyf'); intros.
  apply eq_intro; intros.
   generalize (surj_pair _ _ _ (H8 _ H12)); intro.
   rewrite H13.
   apply H11.
   rewrite <- H6; rewrite <- H1.
   apply <- H10.
   rewrite <- H13; auto.

   generalize (surj_pair _ _ _ (H9 _ H12)); intro.
   rewrite H13.
   apply H10.
   rewrite H1; rewrite H6.
   apply <- H11.
   rewrite <- H13; auto.
apply subset_elim1 in H.
apply subset_elim1 in H0.
rewrite (surj_pair _ _ _ H).
rewrite (surj_pair _ _ _ H0).
rewrite H2; rewrite H3; reflexivity.
Qed.
*)

Lemma nextarr1 : forall X, ext_fun (power NAT) (fun Y => cc_arr Y X).
do 2 red; intros; apply cc_arr_morph; auto with *.
Qed.
Hint Resolve nextarr1.

Lemma Nsup_typ_gen : forall X x,
  X \incl Ndom ->
  x \in N_F X ->
  Nsup x \in Ndom.
intros.
apply subset_intro.
2:apply Nsup_hd_prop.
apply power_intro; intros.
rewrite Nsup_def in H1; trivial.
destruct H1 as [eqz|(i,?,(q,?,eqz))]; rewrite eqz; clear z eqz.
 apply Nil_typ.

 apply Cons_typ.
  apply power_elim with (2:=H1).
  apply fst_typ_sigma in H0; trivial.

  apply power_elim with (2:=H2).
  apply snd_typ_sigma with (y:=fst x) in H0; auto with *.
  apply cc_arr_elim with (2:=H1) in H0.
  apply H in H0.
  apply subset_elim1 in H0; trivial.
Qed.

(* The type operator on the construction domain *)
Definition Nf X := replf (N_F X) Nsup.

Hint Resolve Nsup_morph.

Lemma Nf_intro : forall x X,
  x \in N_F X ->
  Nsup x \in Nf X.
intros.
unfold Nf.
rewrite replf_ax; trivial.
exists x; auto with *.
Qed.

Lemma Nf_elim : forall a X,
  a \in Nf X ->
  exists2 x, x \in N_F X &
  a == Nsup x.
intros.
unfold Nf in H.
rewrite replf_ax in H; trivial.
Qed.

Lemma Nf_mono : Proper (incl_set ==> incl_set) Nf.
do 3 red; intros.
apply Nf_elim in H0; destruct H0 as (f,?,?).
rewrite H1; apply Nf_intro; trivial.
clear H1; revert f H0.
admit.
(*apply N_F_mono; trivial.*)
Qed.
Hint Resolve Nf_mono Fmono_morph.

Lemma Nf_typ : forall X,
  X \incl Ndom -> Nf X \incl Ndom.
red; intros.
apply Nf_elim in H0; destruct H0 as (x,?,?).
rewrite H1.
apply Nsup_typ_gen with X; auto with *.
Qed.
Hint Resolve Nf_typ.

(*
Lemma Wf_stable : forall X,
  X \incl power Wdom ->
  inter (replf X Wf) \incl Wf (inter X).
red; intros X Xty z H.
unfold Wf.
assert (forall a, a \in X -> z \in Wf a).
 intros.
 apply inter_elim with (1:=H).
 rewrite replf_ax.
 2:red;red;intros;apply Fmono_morph; trivial.
 exists a; auto with *.
rewrite replf_ax; auto.
destruct inter_wit with (2:=H).
 apply Fmono_morph; trivial.
assert (z \in Wf x); auto.
apply Wf_elim in H2.
destruct H2.
exists x0; auto.
apply W_F_stable.
apply inter_intro.
 intros.
 rewrite replf_ax in H4.
 2:red;red;intros;apply Fmono_morph; auto.
 2:apply W_F_mono.
 destruct H4.
 rewrite H5; clear y H5.
 specialize H0 with (1:=H4).
 apply Wf_elim in H0; destruct H0.
 rewrite H3 in H5; apply Wsup_inj with (X:=x) (Y:=x1)in H5; trivial.
  rewrite H5; trivial.

  red; intros; apply power_elim with (1:=Xty _ H1); trivial.

  red; intros; apply power_elim with (1:=Xty _ H4); trivial.

 exists (W_F x).
 rewrite replf_ax.
 2:red;red;intros;apply Fmono_morph;auto.
 2:apply W_F_mono.
 exists x; auto with *.
Qed.
*)
(*Hint Resolve Wf_stable.*)

(* The fixpoint *)

Definition NF := Ffix Nf Ndom.

Lemma NFtyp : NF \incl Ndom.
apply Ffix_inA.
Qed.

Lemma Ni_NF : forall o, isOrd o -> TI Nf o \incl NF.
apply TI_Ffix; auto.
Qed.

Lemma TI_Nf_elim : forall a o,
  isOrd o ->
  a \in TI Nf o ->
  exists2 o', lt o' o &
  exists2 x, x \in N_F (TI Nf o') &
  a == Nsup x.
intros.
apply TI_elim in H0; trivial.
2:apply Fmono_morph; trivial.
destruct H0.
apply Nf_elim in H1.
eauto.
Qed.

Lemma Nsup_typ : forall o x,
  isOrd o ->
  x \in N_F (TI Nf o) ->
  Nsup x \in TI Nf (osucc o).
intros.
rewrite TI_mono_succ; auto.
apply Nf_intro; trivial.
Qed.

Lemma NF_ind : forall (P:set->Prop),
  Proper (eq_set ==> iff) P ->
  (forall o' x, isOrd o' -> x \in N_F (TI Nf o') ->
   (forall i, i \in fst x -> P (cc_app (snd x) i)) ->
   P (Nsup x)) ->
  forall a, a \in NF -> P a.
intros.
unfold NF in H1; rewrite Ffix_def in H1; auto.
destruct H1.
revert a H2.
apply isOrd_ind with (2:=H1); intros.
apply TI_Nf_elim in H5; trivial.
destruct H5 as (o',?,(x',?,?)).
rewrite H7; clear a H7.
apply H0 with o'; trivial.
 apply isOrd_inv with y; trivial.

 intros.
 apply H4 with o'; trivial.
 apply snd_typ_sigma with (y:=fst x') in H6; auto with *.
 apply cc_prod_elim with (1:=H6); trivial.
Qed.

(* Inverse of Nsup *)
Definition Nfst x :=
  replf (subset x (fun l => exists i, exists l', l == Cons i l')) fst.

Definition Nsnd x :=
  cc_lam (Nfst x) (fun i => replf (subset x (fun l => exists l', l == Cons i l')) snd).

Definition Nsupi x := couple (Nfst x) (Nsnd x).

Lemma Nfst_inv X x:
  X \incl Ndom ->
  x \in N_F X ->
  Nfst (Nsup x) == fst x.
intros.
unfold Nfst.
apply eq_intro; intros.
 rewrite replf_ax in H1; auto.
 2:admit.
 destruct H1 as (y,?,?).
 rewrite subset_ax in H1; destruct H1.
 destruct H3 as (y',?,(i,(l',?))).
 rewrite H4 in H3; rewrite H3 in H1,H2; rewrite H2; clear H4 H3 H2.
 unfold Cons; rewrite fst_def.
 apply Nsup_tl_prop with (1:=H0) in H1; auto.
 destruct H1; trivial.

 rewrite replf_ax.
 2:admit.
 exists (Cons z Nil). 
 2:unfold Cons; rewrite fst_def; reflexivity.
 apply subset_intro.
  rewrite Nsup_tl_prop with (X:=X); trivial.
  split; trivial.
  apply snd_typ_sigma with (y:=fst x) in H0; auto with *.
  apply cc_arr_elim with (2:=H1) in H0.
  apply H in H0.
  apply subset_elim2 in H0.
  destruct H0.
  rewrite H0; trivial.

  exists z; exists Nil; reflexivity.
Qed.

Lemma Nsnd_inv X x:
  X \incl Ndom ->
  x \in N_F X ->
  Nsnd (Nsup x) == snd x.
intros.
unfold Nsnd.
assert (fx_ty := H0); apply fst_typ_sigma in fx_ty.
assert (sx_ty :=H0); apply snd_typ_sigma with (y:=fst x) in sx_ty; auto with *.
rewrite cc_eta_eq with (1:=sx_ty).
symmetry; apply cc_lam_ext.
 symmetry; apply Nfst_inv with (2:=H0); trivial.
red; intros.
apply eq_intro; intros.
 rewrite replf_ax.
 2:admit.
 exists (Cons x0 z).
 2:unfold Cons; rewrite snd_def; reflexivity.
 apply subset_intro.
 2:exists z; rewrite H2; reflexivity.
 rewrite Nsup_tl_prop with (1:=H0); auto.

 rewrite replf_ax in H3.
 2:admit.
 destruct H3.
 rewrite H4.
 rewrite subset_ax in H3; destruct H3.
 destruct H5.
 destruct H6.
 rewrite H6 in H5; rewrite H5 in H3|-*; clear H4 H5 H6.
 unfold Cons; rewrite snd_def.
 rewrite Nsup_tl_prop with (1:=H0) in H3; trivial.
 rewrite H2; destruct H3; trivial.
Qed.

Lemma Nsup_inv X x:
  X \incl Ndom ->
  x \in N_F X ->
  Nsupi (Nsup x) == x.
intros.
unfold Nsupi.
rewrite Nfst_inv with (2:=H0); trivial.
rewrite Nsnd_inv with (2:=H0); trivial.
symmetry; apply surj_pair with (1:=subset_elim1 _ _ _ H0).
Qed.

Lemma Nsupi_ty X x :
  X \incl Ndom ->
  x \in Nf X ->
  Nsupi x \in N_F X.
intros.
destruct Nf_elim with (1:=H0); trivial.
Admitted.

(* The closure ordinal of W *)
  Definition N_ord := Ffix_ord Nf Ndom.

(*
  Lemma N_ord_bound : bound_ord NAT N_ord.
red; intros.
unfold N_ord.
unfold Ffix_ord.
pose (G:= fun n => subset NF (fun x => Fix_rec Nf Ndom (F_a Nf Ndom) x == F n)).
pose (G' := replf (cc_prod NAT G) (fun f => Nsup (couple NAT f))).
*)

  Lemma W_o_o : isOrd N_ord.
apply Ffix_o_o; auto.
Qed.
Hint Resolve W_o_o.

(*
  Lemma NF_post : forall a,
   a \in NF ->
   a \in TI Nf N_ord.
apply Ffix_post; eauto.
intros.
apply Wf_stable.
Qed.

  Lemma W_eqn : W == Wf W.
apply Ffix_eqn; eauto.
apply Wf_stable.
Qed.
*)

End OrdFixpoint.


Section OrdUniverse.

  (* The universe where we build the inductive type *)
  Variable U : set.
  Hypothesis has_cstr : forall X, X \in U -> sum UNIT (func NAT X) \in U.
  Hypothesis has_empty : empty \in U.
  Variable mu : set.
  Hypothesis mu_ord : isOrd mu.
  Hypothesis mu_clos : forall x F,
    le x mu ->
    ext_fun x F ->
    (forall n, n \in x -> F n \in U) -> sup x F \in U.

  Lemma ORDi_pre_typ : forall n, lt n mu -> ORDi n \in U.
intros.
assert (isOrd n).
 apply isOrd_inv with mu; auto.
revert H.
induction H0 using isOrd_ind; intros.
unfold ORDi; rewrite TI_eq; auto.
apply mu_clos; intros; auto.
apply has_cstr; apply H1; trivial.
apply isOrd_trans with y; trivial.
Qed.

  Lemma ORD_typ : ORDi mu \in U.
unfold ORDi.
rewrite TI_eq; auto.
apply mu_clos; intros; auto.
apply has_cstr.
apply ORDi_pre_typ; trivial.
Qed.

End OrdUniverse.

End Ord_theory.
