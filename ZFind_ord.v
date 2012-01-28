Require Import ZF ZFsum ZFfix ZFnats ZFrelations ZFord ZFcard ZFcont.
Require Import ZFstable ZFrank ZFgrothendieck ZFinaccessible.
Require Import ZFind_basic ZFind_nat.
Import IZF ZFrepl.

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

(*
Lemma no_nat_cof :
  forall F,
  ext_fun NAT F ->
  (forall n, n \in NAT -> lt (F n) mu) ->
  (forall o, lt o mu -> exists2 n, n \in NAT & lt o (F n)) -> (* sup NAT F == mu *)
  False.
intros.
assert (mu \incl sup NAT F).
 red; intros.
 destruct H1 with z; trivial.
 rewrite sup_ax; trivial.
 exists x; trivial.
apply (lt_antirefl mu); trivial.
apply isOrd_plump with (sup NAT F); trivial.
apply VN_reg_ord; auto.
apply NAT_in_mu.
Qed.
*)

Lemma mu_omega : omega \in mu.
Admitted.
Hint Resolve mu_omega.

Lemma no_nat_cof :
  forall F,
  ext_fun NAT F ->
  (forall n, n \in NAT -> lt (F n) mu) ->
  exists2 o, lt o mu & lt (osup NAT F) o.
intros.
exists (osucc (osup NAT F)).
 apply mu_lim.
 apply VN_reg_ord; auto.
 apply NAT_in_mu.

 apply lt_osucc.
 apply isOrd_osup; trivial; intros.
 apply isOrd_inv with mu; auto.
Qed.


  Definition bound_ord_mu A o :=
    forall F, ext_fun A F ->
    (forall n, n \in A -> lt (F n) mu) ->
    lt (osup A F) o.

  Lemma bound_ord_mu_inter : forall A a,
    (exists w, w \in a) ->
    (forall x, x \in a -> bound_ord_mu A x) ->
    bound_ord_mu A (inter a).
red; intros.
apply inter_intro; trivial; intros.
red in H0.
apply H0; trivial.
Qed.

  Lemma mu_bound : forall A, A \in VN mu -> bound_ord_mu A mu.
red; intros.
apply VN_reg_ord; auto; intros.

Qed.

  Definition nat_bound :=
    inter (subset (osucc mu) (bound_ord_mu NAT)).

  Lemma nb_bound : bound_ord_mu

(*
Lemma L :
   ~~ exists2 o, limitOrd o &
      lt omega o /\ lt o mu /\
      lt (sup (func NAT o) (fun f => sup NAT (app f))) o.
red; intros.
assert (forall o, limitOrd o -> lt omega o -> lt o mu ->
~ lt (sup (func NAT o) (fun f => sup NAT (app f))) o).
 red; intros.
 apply H; exists o; auto.
clear H.
*)

(* TODO: build the closure ordinal *)
  Definition closes_ord o :=
    limitOrd o /\ lt omega o /\ bound_ord NAT o.

  Lemma mu_closes_ord : closes_ord mu.
split;[|split]; intros; trivial.
 apply grot_ord_inv; trivial.

 red; intros.
 apply VN_reg_ord; trivial.
 apply NAT_in_mu.
Qed.

  Definition clos_ord :=
    inter (subset (osucc mu) closes_ord).

Lemma isOrd_clos_ord : isOrd clos_ord.
apply isOrd_inter; intros.
apply subset_elim2 in H; destruct H.
rewrite H.
destruct H0 as ((?,_),_); trivial.
Qed.

Lemma limitOrd_clos_ord : limitOrd clos_ord.
split; intros.
 apply isOrd_clos_ord.

 apply inter_intro; intros.
  specialize inter_elim with (1:=H)(2:=H0); intro.
  apply subset_elim2 in H0; destruct H0.
  rewrite H0 in H1|-*.
  destruct H2.
  apply H2; trivial.

  exists mu.
  apply subset_intro.
   apply lt_osucc; trivial.

   apply mu_closes_ord.
Qed.

Lemma omega_in_clos_ord : lt omega clos_ord.
apply inter_intro; intros.
 apply subset_elim2 in H; destruct H.
 rewrite H; destruct H0 as (_,(?,_)); trivial.

 exists mu.
  apply subset_intro.
   apply lt_osucc; trivial.

   apply mu_closes_ord.
Qed.

Lemma bound_clos_ord : bound_ord NAT clos_ord.
red; intros.
apply inter_intro; intros.
 rewrite subset_ax in H1; destruct H1.
 destruct H2.
 rewrite H2 in H1|-*; clear y H2.
 generalize (proj2 (proj2 H3)); intro.
 apply H2; trivial.
 intros.
 apply inter_elim with (subset (osucc mu) closes_ord).
  apply H0; trivial.

  apply subset_intro; trivial.

 exists mu.
  apply subset_intro.
   apply lt_osucc; trivial.

   apply mu_closes_ord.
Qed.

Lemma clos_ord_closes : closes_ord clos_ord.
split;[|split].
 apply limitOrd_clos_ord.

 apply omega_in_clos_ord.

 apply bound_clos_ord.
Qed.

Lemma co_mu : clos_ord \incl mu.
red; intros.
apply inter_elim with (1:=H).
apply subset_intro.
 apply lt_osucc; trivial.

 apply mu_closes_ord.
Qed.

(*
Lemma clos_ord_step :
  closes_ord (sup (func NAT clos_ord) (fun f => sup NAT (app f))).
split;[|split].
 split.
  admit.

  intros.
  rewrite sup_ax in H|-*.
  2:admit.
  2:admit.
  destruct H.
  exists (lam NAT (fun n => osucc (app x0 n))).
   apply lam_is_func; auto; intros.
    admit.

    apply limitOrd_clos_ord.
    apply app_typ with NAT; auto.

   rewrite sup_ax in H0|-*.
   2:admit.
   2:admit.
   destruct H0.
   exists x1; trivial.
   rewrite beta_eq; auto.
   2:admit.
   apply lt_osucc_compat; auto.
   apply isOrd_inv with clos_ord.
    apply isOrd_clos_ord.

    apply app_typ with NAT; trivial.

 admit.

 red; intros.
 rewrite sup_ax.
 2:admit.
 exists (lam NAT (fun _ => osucc (sup NAT F))).
  apply lam_is_func; intros.
   admit.

   apply limitOrd_clos_ord.
   apply bound_clos_ord; trivial.
   intros.
   apply H0 in H2.
   rewrite sup_ax in H2.
   2:admit.
   destruct H2.
   rewrite sup_ax in H3.
   2:admit.
   destruct H3.
   apply isOrd_trans with (app x0 x1); trivial.
    apply isOrd_clos_ord.

    apply app_typ with NAT; trivial.

  rewrite sup_ax.
  2:admit.
  exists ZERO.
   apply ZERO_typ.

   rewrite beta_eq.
   apply lt_osucc.
   apply isOrd_supf; intros; trivial.
   2:admit.
   admit.

   apply ZERO_typ.
Qed.

  Lemma co_incl :
    clos_ord \incl (sup (func NAT clos_ord) (fun f => sup NAT (app f))).
red; intros.
rewrite sup_ax.
2:admit.
exists (lam NAT (fun _ => osucc z)).
 apply lam_is_func; intros.
  red; red; auto with *.

  apply limitOrd_clos_ord; trivial.

 rewrite sup_ax.
 2:admit.
 exists ZERO.
  apply ZERO_typ.

  rewrite beta_eq.
   apply lt_osucc.
   apply isOrd_inv with clos_ord; trivial.
   apply isOrd_clos_ord.

   red; red ;auto with *.

   apply ZERO_typ.
Qed.

red; intros.
apply inter_elim with (1:=H).
apply subset_intro.
 apply ole_lts; auto.
  admit.

  red; intros.
  rewrite sup_ax in H0.
  2:admit.
  destruct H0.
  rewrite sup_ax in H1.
  2:admit.
  destruct H1.
  apply isOrd_trans with (app x x0); trivial.
  apply co_mu.
  apply app_typ with NAT; trivial.

 apply clos_ord_step.
Qed.
*)

  Lemma nmu : ~ mu \incl clos_ord.
red; intros.
assert (forall o, lt o mu -> 
exists2 F, ext_fun NAT F &
(forall n, n \in NAT -> lt (F n) clos_ord) /\
lt o (sup NAT F)).
 intros.
 apply H in H0.
 exists (fun _ => osucc o).
  red; red; reflexivity.

  split; intros.
   apply limitOrd_clos_ord; trivial.

   rewrite sup_ax.
   2:admit.
   exists ZERO.
    apply ZERO_typ.

    apply lt_osucc.
    apply isOrd_inv with clos_ord; trivial.
    apply isOrd_clos_ord.

   red; red ;auto with *.

   apply ZERO_typ.
Qed.


 generalize (co_incl _ H0); intros.
 rewrite sup_ax in H1.
 2:admit.
 destruct H1.
 rewrite sup_ax in H2.
 2:admit.
destruct H2.
exists (app x).
 red; red; intros; apply app_morph; auto with *.

 split; intros.
  apply app_typ with NAT; trivial.

  rewrite sup_ax.
  2:admit.
  exists x0; trivial.


specialize co_inclapply 

(*
  Definition clos_ord_exp o :=
    exists2 F,
      ext_fun NAT F /\ (forall n, n \in NAT -> lt (F n) mu) &
      o \incl sup NAT F.
*)

  Lemma clos_ord_induc :
    exists2 F,
      ext_fun NAT F /\ (forall n, n \in NAT -> lt (F n) mu) &
      clos_ord \incl osup NAT F.
(*
destruct clos_ord_step as (?,(?,?)).
assert (clos_ord \incl sup (func NAT clos_ord) (fun f => sup NAT (app f))).
 red; intros.
 unfold clos_ord in H.
 apply inter_elim with (1:=H).
 apply subset_intro.
  apply isOrd_trans with mu; auto.
  apply VN_reg_ord; auto.
   admit.
.   admit.
   intros.
   apply VN_reg_ord; auto.
    admit.
    apply NAT_in_mu.
    intros.
    admit.

  apply clos_ord_step.

  exists (fun n => sup (func NAT clos_ord) (fun f => app f n)).

destruct clos_ord_step as (?,(?,?)).
*)
Admitted.
(*
  Lemma clos_ord_induc :
    exists2 F,
      ext_fun NAT F /\ (forall n, n \in NAT -> lt (F n) clos_ord) &
      clos_ord == sup NAT F.
Admitted.
*)
  Lemma clos_ord_lt_mu : lt clos_ord mu.
destruct clos_ord_induc as (?,(?,?)).
apply isOrd_plump with (osup NAT x); auto.
 apply isOrd_clos_ord.
apply VN_reg_ord; auto.
apply NAT_in_mu.
(*
 intros.
 apply H0 in H2.
 apply inter_elim with (1:=H2).
  apply subset_intro.
   apply lt_osucc; trivial.

   apply mu_closes_ord.
*)
Qed.


  Lemma ORD_clos :
    exists2 o, limitOrd o &
      lt omega o /\ lt o mu /\
      lt (sup (func NAT o) (fun f => sup NAT (app f))) o.
Admitted.


(* card(X) = card(A->X) if card(X) >= card(2^card(A)) *)

  Definition NATfb o := osup (func NAT o) (fun f => osup NAT (app f)).

  Instance NATfb_morph : morph1 NATfb.
unfold NATfb.
do 2 red; intros.
apply osup_morph; auto with *.
 rewrite H; reflexivity.
red; intros.
apply osup_morph; auto with *.
red; intros; apply app_morph; trivial.
Qed.

  Lemma ext1 : forall A, ext_fun A (fun f => osup NAT (app f)).
red; red; intros.
apply osup_morph; auto with *.
red; intros.
rewrite H0,H2; reflexivity.
Qed.
Hint Resolve ext1.

  Lemma NATfb_ord : forall o, isOrd o -> isOrd (NATfb o).
unfold NATfb; intros.
apply isOrd_osup; trivial; intros.
apply isOrd_osup; intros.
 red; red; intros.
 rewrite H2; reflexivity.

 apply isOrd_inv with o; trivial.
 apply app_typ with NAT; trivial.
Qed.

  Lemma NATfb_mono : increasing NATfb.
unfold NATfb.
red; intros.
apply osup_lub; intros.
 do 2 red; intros; apply osup_morph; auto with *.
 red; intros; apply app_morph; trivial.

 apply isOrd_osup; intros; auto. 
 apply isOrd_osup; intros; auto.
  do 2 red; intros; apply app_morph; auto with *.

  apply isOrd_inv with x; trivial.
  apply app_typ with (1:=H2); trivial.

 apply osup_intro with (f:=fun x => osup NAT (app x)) (x:=x0).
  do 2 red; intros; apply osup_morph; auto with *.
  red; intros; apply app_morph; trivial.

  apply func_narrow with (1:=H2); intros. (* covariant *)
  apply H1.
  apply app_typ with (1:=H2); trivial.
Qed.

  Lemma plw_ord : forall o, isOrd o -> isOrd (plus_w o).
intros.
apply isOrd_iter_w; auto.
 red; intros; apply isOrd_trans with o; auto.

 intros.
 red; intros.
 apply le_lt_trans with x; auto.
 apply ole_lts; auto.
Qed.

  Lemma plw_lim : forall o, isOrd o -> limitOrd (plus_w o).
split.
 apply plw_ord; trivial.
intros.
apply isOrd_sup_elim in H0.
destruct H0.
apply isOrd_sup_intro with (S x0); simpl.
apply lt_osucc_compat; trivial.
clear H0; revert o H.
elim x0; simpl; intros; auto.
Qed.

  Lemma plw_lt : forall o, isOrd o -> lt o (plus_w o).
intros.
apply isOrd_sup_intro with 1; simpl.
apply lt_osucc; trivial.
Qed.



  (* We look for a fixpoint of this: *)
  Definition ORDb o := (* == NATfb o + w *)
    TI (fun x => union2 (osucc x) (NATfb o)) omega.
(*
  Instance ORDb_morph : morph1 ORDb.
unfold ORDb.
do 2 red; intros.
apply osucc_morph; apply sup_morph; auto with *.
 rewrite H; reflexivity.
red; intros.
apply sup_morph; auto with *.
red; intros; apply app_morph; trivial.
Qed.

  Lemma ORDb_ord : forall o, isOrd o -> isOrd (ORDb o).
unfold ORDb; intros.
apply isOrd_succ.
apply isOrd_supf; trivial; intros.
apply isOrd_supf; intros.
 red; red; intros.
 rewrite H2; reflexivity.

 apply isOrd_inv with o; trivial.
 apply app_typ with NAT; trivial.
Qed.

  Lemma ORDb_mono : increasing ORDb.
unfold ORDb.
red; red; intros.
apply ole_lts.
 apply isOrd_inv with (2:=H2).
 apply ORDb_ord; trivial.

 apply olts_le in H2.
 rewrite H2.
 clear z H2.
 red; intros.
rewrite sup_ax in H2|-*; trivial.
 destruct H2.
 exists x0; trivial.
 apply func_narrow with y; trivial.
 intros.
 apply H1.
 apply app_typ with NAT; trivial.
Qed.

  Definition l := TI ORDb mu.

  Lemma l_ord : isOrd l.
unfold l.
induction mu_ord using isOrd_ind; intros.
rewrite TI_eq; auto with *.
apply isOrd_supf; auto.
 red; red; intros.
 rewrite H2; reflexivity.

 intros.
 apply ORDb_ord; auto. 
Qed.

  Lemma l_succ : forall x, isOrd x -> x \incl (ORDb x).
red; intros.
unfold ORDb.
apply ole_lts; trivial.
 admit.
red; intros.
rewrite sup_ax; auto.
exists (lam NAT (fun _ => z)).
 apply lam_is_func; intros; auto.

 rewrite sup_ax.
 2:red;red;intros; apply app_morph;auto with *.
 exists ZERO.
  apply ZERO_typ.

  rewrite beta_eq; auto.
  apply ZERO_typ.
Qed.

  Lemma l_succ : forall x, isOrd x -> lt x (ORDb x).
intros.
apply ole_lts; trivial.
red; intros.
apply isOrd_trans with x; trivial.
 admit.
rewrite sup_ax; auto.
exists (lam NAT (fun _ => )).

  Lemma l_lim : limitOrd l.
split.
 apply l_ord.
intros.
apply TI_elim in H; auto with *.
destruct H.
apply TI_intro with (osucc x0); auto with *.
 apply mu_lim; trivial.
apply lt_osucc_compat.
 admit.
rewrite sup_ax; auto.
exists (lam NAT (fun _ => osucc x)).
 apply lam_is_func; auto.
 intros.

  Lemma ORDb_fix : forall x, isOrd x ->
    ORDb x == x -> 
  lt (sup (func NAT x) (fun f : set => sup NAT (app f))) x.
intros.
apply oles_lt.
 apply isOrd_supf; trivial; intros.
 apply isOrd_supf; intros.
  red; red; intros.
  rewrite H3; reflexivity.

  apply isOrd_inv with x; trivial.
  apply app_typ with NAT; trivial.
change (ORDb x \incl x).
Qed.
*)

 Lemma bound : forall o,
   lt o mu ->
   ORDb (osucc (osucc (osucc (osucc o)))) \incl
    osucc (osucc (osucc (osucc o))).
unfold ORDb.
red; intros.
assert (oo : isOrd o) by eauto using isOrd_inv.
assert (isOrd z).
 apply isOrd_inv with (2:=H0).
 apply ORDb_ord; auto.
apply olts_le in H0.
apply ole_lts; auto.
red; intros.
apply H0 in H2.
rewrite sup_ax in H2; auto.
destruct H2.
rewrite sup_ax in H3; auto.
2:admit.
destruct H3.
specialize app_typ with (1:=H2) (2:=H3); intros.
apply olts_le in H5.
auto.
Qed.

  Lemma ORD_clos0 :
    exists2 o, limitOrd o /\ isDir o &
      lt omega o /\ lt o mu /\
      lt (sup (func NAT o) (fun f : set => sup NAT (app f))) o.
exists (

 Lemma bound_lt : forall o,
   isOrd o ->
   exists2 l, lt l mu & ORDb l == l.
intros.




  Lemma ORDi_typfun : forall o X, isOrd o ->
    X \in VN o -> ORDf X \in VN (ORDb o).
intros.
rewrite VN_def; auto.
unfold Ffun.
 exists (sup (func NAT o) (fun f => sup NAT (app f))).
  apply lt_osucc.
  admit.

  red; intros.
  assert (z \in func NAT X).
   admit. (* todo: treat zero *)
  assert (func NAT o \in VN (osucc (osucc (osucc (osucc (osucc o)))))).
   apply VN_func; auto.
    admit.
    apply VN_intro; auto.
    apply lt_osucc; auto.
  assert (z \in VN (sup NAT (app z))).

osucc (osucc (osucc (osucc o)))).

unfold VN, Ffun.
rewrite TI_mono_succ; auto.
 rewrite power_ax; intros.
 


(* ORD : the least fixpoint *)
(*
  Hypothesis mu : set.
  Hypothesis mu_strong : VN_inaccessible_rel mu.
  (* mu is a cardinal bigger than those of the types of our universe *)
  Hypothesis NAT_in_mu : NAT \in VN mu.
(*  Hypothesis NAT_in_mu : lt_card NAT mu.*)

  Let mu_regular : VN_regular mu.
destruct mu_strong as (_,mu_reg); trivial.
Qed.
  Let mu_ord : isOrd mu.
destruct mu_strong as ((muo,_),_); trivial.
Qed.
  Let mu_lim : forall o, lt o mu -> lt (osucc o) mu.
destruct mu_strong as ((_,lim),_); trivial.
Qed.

  Definition ORD := ORDi mu.

  Lemma ORD_eq : ORD == ORDf ORD.
unfold ORD, ORDi.
apply eq_intro; intros.
 rewrite <- TI_mono_succ; auto.
 apply TI_incl with mu; auto.

 unfold ORDf in H at 1.
 rewrite TI_eq in H; auto.
 rewrite func_cont in H; auto.
  assert (exists w, w \in mu).
   rewrite VN_def in NAT_in_mu; trivial.
   destruct NAT_in_mu.
   exists x; trivial.
  destruct H0 as (w, wmu).
  rewrite (cst_cont UNIT mu w) in H; auto.
   rewrite sum_cont in H; auto.
   rewrite sup_ax in H.
   2:do 2 red; intros; apply ORDf_morph; eapply ORDfun_ext; eauto.
   destruct H.
   rewrite <- TI_mono_succ in H0; auto.
    apply TI_intro with (osucc x); auto.
    apply isOrd_inv with mu; trivial.

  apply ORDfun_stable.

  red; intros.
  apply ORDf_mono.
  apply TI_mono; auto.
Qed.

  Lemma ORDi_ORD : forall o,
    isOrd o ->
    ORDi o \incl ORD.
induction 1 using isOrd_ind; intros.
unfold ORDi.
rewrite TI_eq; auto.
red; intros.
rewrite sup_ax in H2; auto.
destruct H2.
rewrite ORD_eq.
apply ORDf_mono with (ORDi x); auto.
Qed.



Section OrdUniverse.

  (* The universe where we build the inductive type *)
  Variable U : set.
  Hypothesis has_cstr : forall X, X \in U -> sum UNIT (func NAT X) \in U.
  Hypothesis has_empty : empty \in U.
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

  Lemma ORD_typ : ORD \in U.
unfold ORD, ORDi.
rewrite TI_eq; auto.
apply mu_clos; intros; auto.
apply has_cstr.
apply ORDi_pre_typ; trivial.
Qed.

End OrdUniverse.
*)
End OrdFixpoint.

End Ord_theory.
