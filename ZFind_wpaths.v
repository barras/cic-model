Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFord ZFfix ZFstable.
Require Import ZFgrothendieck.

(** Abstract model of W and COW *)

Parameter A : set.
Parameter B : set -> set.
Parameter Bm : morph1 B.
Existing Instance Bm.

Parameter Wsup : set -> set -> set.
Parameter Wsup_morph : morph2 Wsup.
Parameter Wfst : set -> set.
Parameter Wfst_morph : morph1 Wfst.
Parameter Wfst_def : forall x f, Wfst (Wsup x f) == x.
Parameter Wsnd : set -> set -> set.
Parameter Wsnd_morph : morph2 Wsnd.

Parameter Wdom : set.

Parameter Wsnd_def : forall x f i,
  cc_app f i ∈ Wdom ->
  Wsnd (Wsup x f) i == cc_app f i.

Parameter Wf : set -> set.
Parameter Wf_intro :
  forall X x f, x ∈ A -> f ∈ (Π _ ∈ B x, X) -> Wsup x f ∈ Wf X.
Parameter Wf_elim : forall a X,
  a ∈ Wf X ->
  exists2 x, x ∈ A & exists2 f, f ∈ Π i ∈ B x, X & a == Wsup x f.

Parameter Wf_typ : forall X, X ⊆ Wdom -> Wf X ⊆ Wdom.

Parameter Wsup_incl_hd_inv : forall x x' f f',
  Wsup x f ⊆ Wsup x' f' -> x==x'.
Parameter Wsnd_mono : forall w1 w2 x,
  w1 ⊆ w2 ->
  Wsnd w1 x ⊆ Wsnd w2 x.
Parameter Wsup_mono : forall x x' f f',
  x == x' ->
  is_cc_fun (B x) f ->
  (forall i, i ∈ B x -> cc_app f i ⊆ cc_app f' i) ->
  Wsup x f ⊆ Wsup x' f'.

Parameter Wsup_sup : forall I X f,
  ext_fun I f ->
  X ⊆ Wdom ->
  (exists2 i, i∈I & forall j, j ∈ I -> f i ⊆ f j) ->
  typ_fun f I (Wf X) ->
  exists2 a0, a0 ∈ A &
  sup I f == Wsup a0 (λ i ∈ B a0, sup I (fun x => Wsnd (f x) i)).

Parameter Wdom_sup_closed : forall I f,
  ext_fun I f ->
  (forall i, i ∈ I -> f i ∈ Wdom) ->
  sup I f ∈ Wdom.
         
(* extensionality w.r.t. observations *)
Parameter pre_incl_eq : forall X w1 w2,
  X ⊆ Wdom ->
  X ⊆ Wf X ->
  w1 ∈ X ->
  w2 ∈ X ->
  w1 ⊆ w2 ->
  w2 == w1.


(** Derived facts *)

Instance Wf_mono : Proper (incl_set ==> incl_set) Wf.
intros X Y inclXY a tya.
apply Wf_elim in tya; destruct tya as (x,tyx,(f,tyf,eqz)); rewrite eqz.
apply Wf_intro; trivial.
revert tyf; apply cc_prod_covariant; auto with *.
Qed.
Instance Wf_morph : morph1 Wf := Fmono_morph _ Wf_mono.

Hint Resolve Wf_mono Wf_morph.
Hint Resolve Wf_typ.

Lemma Wsup_inj : forall x x' f f',
  x ∈ A ->
  x' ∈ A ->
  (forall i, i ∈ B x -> cc_app f i ∈ Wdom) ->
  (forall i, i ∈ B x' -> cc_app f' i ∈ Wdom) ->
  Wsup x f == Wsup x' f' -> x == x' /\ (forall i, i ∈ B x -> cc_app f i == cc_app f' i).
intros.
specialize eq_incl with (1:=H3); intro.
symmetry in H3; apply eq_incl in H3.
split; intros.
 apply Wsup_incl_hd_inv in H4; trivial.

 apply incl_eq.
 apply Wsnd_mono with (x:=i) in H4.
  rewrite Wsnd_def in H4; auto.
  rewrite Wsnd_def in H4; auto.
  apply H2.
  apply Wsup_incl_hd_inv in H3; rewrite H3; trivial.

 apply Wsnd_mono with (x:=i) in H3.
  rewrite Wsnd_def in H3; auto.
  rewrite Wsnd_def in H3; auto.
  apply H2.
  apply Wsup_incl_hd_inv in H4; rewrite <- H4; trivial.
Qed.

Lemma Wf_elim' X x f :
  x ∈ A ->
  (forall i, i ∈ B x -> cc_app f i ∈ Wdom) ->
  X ⊆ Wdom ->
  Wsup x f ∈ Wf X ->
  forall i, i ∈ B x -> cc_app f i ∈ X.
intros tyx tyf Xincl tyw.
apply Wf_elim in tyw.
destruct tyw as (x',tyx',(f',tyf',eqw)).
apply Wsup_inj in eqw; intros; auto.
trivial.
 destruct eqw as (eqx,eqf).
 rewrite eqf; trivial.
 apply cc_prod_elim with (1:=tyf').
 rewrite <- eqx; trivial.

 apply Xincl.
 apply cc_prod_elim with (1:=tyf'); trivial.
Qed.

Lemma Wfst_typ_gen X w :
  w ∈ Wf X ->
  Wfst w ∈ A.
intros tyw.
apply Wf_elim in tyw; trivial.
destruct tyw as (x,tyx,(f,tyf,eqw)).
rewrite eqw,Wfst_def; trivial.
Qed.

Lemma Wsnd_typ_gen X w i :
  X ⊆ Wdom ->
  w ∈ Wf X ->
  i ∈ B (Wfst w) ->
  Wsnd w i ∈ X.
intros.
apply Wf_elim in H0; destruct H0 as (x,tyx,(f,tyf,eqw)).
rewrite eqw,Wfst_def in H1.
rewrite eqw,Wsnd_def.
 apply cc_prod_elim with (1:=tyf); trivial.
 apply H; apply cc_prod_elim with (1:=tyf); trivial.
Qed.

Lemma Wf_stable0 (K:set->Prop) :
  (forall X, K X -> X ⊆ Wdom) ->
 stable_class K Wf.
red; intros Kdef X Xty z H.
assert (forall a, a ∈ X -> z ∈ Wf a).
 intros.
 apply inter_elim with (1:=H).
 rewrite replf_ax.
 2:red;red;intros;apply Wf_morph; trivial.
 exists a; auto with *.
destruct inter_wit with (2:=H); auto.
assert (tyz := H0 _ H1).
apply Wf_elim in tyz.
destruct tyz as (x',tyx,(f,tyf,eqz)).
rewrite eqz.
apply Wf_intro; trivial.
rewrite cc_eta_eq with (1:=tyf).
apply cc_prod_intro; intros.
 intros ? ? ? h; rewrite h; reflexivity.
 do 2 red; reflexivity.
apply inter_intro; eauto.
intros.
specialize H0 with (1:=H3).
apply Wf_elim in H0.
destruct H0 as (x'',tyx',(f',tyf',eqz')).
rewrite eqz in eqz'.
apply Wsup_inj in eqz'; trivial; intros.
 destruct eqz' as (eqx,eqf).
 rewrite eqf; trivial.
 apply cc_prod_elim with (1:=tyf').
 rewrite <- eqx; trivial.

 apply (Kdef x); auto.
 apply cc_prod_elim with (1:=tyf); trivial.

 apply (Kdef y); auto.
 apply cc_prod_elim with (1:=tyf'); trivial.
Qed.

(** Inductive type least fixpoint of Wf *)
Require Import ZFtarski.

Definition W := FIX incl_set inter Wdom (power Wdom) Wf.

Lemma W_lfp : is_lfp incl_set Wf W. 
apply knaster_tarski; auto with *.
Qed.

Lemma W_eqn : W == Wf W.
symmetry; apply W_lfp.
Qed.

Lemma W_least X : Wf X ⊆ X -> W ⊆ X.
apply W_lfp.
Qed.

Lemma W_typ : W ⊆ Wdom.
apply lfp_typ; auto with *.
Qed.

Lemma Wf_stable : stable_class (fun X => X ⊆ W) Wf.
apply Wf_stable0.
intros; transitivity W; trivial.
apply W_typ.
Qed.

Lemma W_ind : forall (P:set->Prop),
  Proper (eq_set ==> iff) P ->
  (forall x f, x ∈ A -> f ∈ (Π i ∈ B x, W) ->
   (forall i, i ∈ B x -> P (cc_app f i)) ->
   P (Wsup x f)) ->
  forall a, a ∈ W -> P a.
intros.
cut (W ⊆ subset W P).
 intros inclW; apply inclW in H1.
 apply subset_elim2 in H1; destruct H1 as (a',eqa,?).
 rewrite eqa; trivial.
apply W_least.
assert (subset W P ⊆ W).
 intro; apply subset_elim1.
assert (Wf (subset W P) ⊆ W).
 transitivity (Wf W).
  apply Wf_mono; trivial.
  rewrite <- W_eqn; reflexivity. 
intros z tyz.
apply subset_intro; auto.
apply Wf_elim in tyz; destruct tyz as (x,tyx,(f,tyf,eqz)).
rewrite eqz.
apply H0; trivial.
 revert tyf; apply cc_prod_covariant; auto with *.

 intros.
 apply cc_prod_elim with (2:=H4) in tyf.
 apply subset_elim2 in tyf; destruct tyf as (y,?,?).
 rewrite H5; trivial.
Qed.

(** Coinductive *)
(* Co-Iteration of Wf *)
Require Import ZFord ZFcofix.

Definition COWi := COTI Wdom Wf.

(* Proving the fixpoint is reached at omega *)

Definition co_ord := omega.
Lemma co_ordo : isOrd co_ord. 
trivial.
Qed.

Definition COW := COWi co_ord.

Lemma COWi_closure : COW ⊆ Wf COW.
red; intros.
assert (z ∈ Wf Wdom).
 assert (z ∈ Wf (COWi zero)).
  apply COTI_elim with (3:=H); auto.
 unfold COWi in H0; rewrite COTI_initial in H0; auto.
apply Wf_elim in H0; destruct H0 as (a,tya,(f,tyf,eqz)).
rewrite eqz.
apply Wf_intro; trivial. 
rewrite cc_eta_eq with (1:=tyf).
apply cc_prod_intro; intros; auto with *.
 do 2 red; intros; apply cc_app_morph; auto with *.
apply COTI_intro; auto.
 apply cc_prod_elim with (1:=tyf); trivial.

 intros.
 assert (oo':isOrd o') by eauto using isOrd_inv.
 rewrite <- COTI_mono_succ; auto.
 2:apply Wf_typ; reflexivity.
 assert (z ∈ Wf (COWi (osucc o'))).
  apply COTI_elim with (3:=H); auto.
 rewrite eqz in H2.
 apply Wf_elim' with (x:=a); trivial.
  intros; apply cc_prod_elim with (1:=tyf); trivial.

  apply COTI_bound; auto.
Qed.

Lemma COW_typ : COW ⊆ Wdom.
apply COTI_bound; trivial.
Qed.
Lemma COW_eqn : COW == Wf COW.
apply incl_eq.
 apply COWi_closure.

 unfold COW,COWi.
 rewrite <- COTI_mono_succ; auto.
 2:apply Wf_typ; reflexivity.
 apply COTI_incl; auto.
Qed.
Lemma COW_gfp X : X ⊆ Wdom -> X ⊆ Wf X -> X ⊆ COW.
intros.
apply COTI_post_fix; auto.
Qed.

(* We do not need more properties about COW beyond this point *)
Opaque COW.
(*
Parameter COW : set.
Parameter COW_typ : COW ⊆ Wdom.
Parameter COW_eqn : COW == Wf COW.
Parameter COW_gfp : forall X, X ⊆ Wdom -> X ⊆ Wf X -> X ⊆ COW.
 *)
(* greatest fixpoint of Wf reached at a known ordinal *)
Opaque co_ord.
(*
Parameter co_ord : set.
Parameter co_ordo : isOrd co_ord. 
Parameter COWi_closure : COWi co_ord ⊆ Wf (COWi co_ord).*)
Hint Resolve co_ordo.

Lemma COW_Wf1 : COW ⊆ Wf Wdom.
rewrite COW_eqn; apply Wf_mono; trivial.
apply COW_typ.  
Qed.
Hint Resolve COW_typ COW_eqn COW_Wf1.

Lemma COW_COWi o : isOrd o -> COW ⊆ COWi o.
intros; apply COTI_post_fix; auto with *.
rewrite <- COW_eqn; reflexivity.
Qed.

(* We rediscover after the fact that COW is the iteration at omega *)
Lemma COW_def : COW == COWi co_ord.
apply incl_eq.
 apply COW_COWi; trivial.

 apply COW_gfp.
  apply COTI_bound; auto.
  apply COWi_closure.
Qed.

(* Co-recursion... *)
(*
  Lemma Wsup_sup I X f :
  ext_fun I f ->
  X ⊆ Wdom ->
  (exists i, i∈I) ->
  directed I (Wf X) f ->
  exists2 a0, a0 ∈ A & sup I f == Wsup a0 (λ i ∈ B a0, sup I (fun x => Wsnd (f x) i)).
intros fext Xty (i0,wit0) dir.
red in dir.
destruct dir with (1:=wit0)(2:=wit0) as (i,wit,(tyfi&lei&_)).
pose (I' := subset I (fun j => f j ∈ Wdom)).
assert (tyi' : i ∈ I').
 apply subset_intro; trivial.
 apply Wf_typ with X; trivial.
assert (fext' : ext_fun I' f). admit.
assert (eqsf : sup I f == sup I' f).
 apply eq_set_ax; intros z.
 rewrite sup_ax; trivial.
 rewrite sup_ax; trivial.
 split; destruct 1 as (j,?,?); intros.
 destruct dir with j j as (z',?,(?&?&?)); trivial.
 exists z'; auto.
 apply subset_intro; trivial. 
 apply Wf_typ with X; trivial. 

 apply subset_elim1 in H; eauto.
clear wit0 lei.
apply Wf_elim in tyfi.
destruct tyfi as (a0,tya0,(f0,_,eqf0)).
exists a0; trivial.
rewrite eqsf.
rewrite Wsup_sup_raw with (a0:=a0)(X:=X); eauto.
 apply Wsup_morph;[reflexivity|].
 apply cc_lam_ext; intros; auto with *.
 red; intros.
 assert (fext2 : forall x, ext_fun I (fun i => Wsnd (f i) x)). admit.
 assert (fext2' : forall x, ext_fun I' (fun i => Wsnd (f i) x)). admit.
 apply eq_set_ax; intros z.
 rewrite sup_ax; trivial.
 rewrite sup_ax; trivial.
 split; destruct 1 as (j,?,?); intros.
  rewrite H0 in H2.
  apply subset_elim1 in H1; eauto.

  destruct dir with j j as (z',?,(?&?&?)); trivial.
  exists z'; auto.
   apply subset_intro; trivial. 
   apply Wf_typ with X; trivial. 

  revert H2; rewrite <- H0; apply Wsnd_mono; trivial.

 intros.
apply subset_elim1 in  apply subset_ax in H; destruct H.
 destruct H0.
 rewrite H0 in H.

destruct dir with (1:=wit)(2:=H) as (z,tyz,(tyfz&le0&le1)).
rewrite eqf0 in le0.
apply Wf_elim in tyfz.
destruct tyfz as (a,tya,(f1,tyf1,eqfz)).
rewrite eqfz in le0.
apply Wsup_incl_hd_inv in le0.
apply cc_prod_is_cc_fun in tyf1.
rewrite <- le0 in tyf1,eqfz.
exists z; trivial.
exists f1; auto.
 destruct 

 exists 

  apply subset_elim1 in H; eauto.
 apply incl_eq.
  
 

 
 
intros.
destruct dir with (1:=wit)(2:=H) as (z,tyz,(tyfz&le0&le1)).
rewrite eqf0 in le0.
apply Wf_elim in tyfz.
destruct tyfz as (a,tya,(f1,tyf1,eqfz)).
rewrite eqfz in le0.
apply Wsup_incl_hd_inv in le0.
apply cc_prod_is_cc_fun in tyf1.
rewrite <- le0 in tyf1,eqfz.
exists z; trivial.
exists f1; auto.
Qed.

*)

Definition complete I X :=
  forall f,
  ext_fun I f ->
  typ_fun f I X ->
  (exists2 i0, i0 ∈ I & forall i, i ∈ I -> f i0 ⊆ f i) -> 
  sup I f ∈ X.

Lemma Wf_complete I X :
  X ⊆ Wdom -> complete I X -> complete I (Wf X).
intros tyX Xcl.
red; intros f fext fty (i0,tyi0,fdir).  
assert (eqsm : forall A, ext_fun A (fun i1 => sup I (fun x => Wsnd (f x) i1))).
 do 2 red; intros.
 apply sup_morph; auto with *.
 red; intros.
 apply Wsnd_morph; auto.
assert (sfm : forall i, ext_fun I (fun x => Wsnd (f x) i)).
 do 2 red; intros.
 apply Wsnd_morph; auto with *.
destruct Wsup_sup with I X f as (a0,tya0,eqsup); eauto.
rewrite eqsup.
apply Wf_intro; trivial.
apply cc_prod_intro; auto.
intros.
apply Xcl; trivial.
 red; intros.
 apply Wsnd_typ_gen; auto.
 assert (lesup : f x0 ⊆ sup I f) by auto.
 rewrite eqsup in lesup.
 apply fty in H0.
 apply Wf_elim in H0; destruct H0 as (a1,tya1,(f1,tyf1,eqf1)).
 rewrite eqf1 in lesup|-*.
 rewrite Wfst_def.
 apply Wsup_incl_hd_inv in lesup.
 rewrite lesup; trivial.

 exists i0; trivial.
 intros; apply Wsnd_mono; auto.
Qed.

Lemma COWi_complete I o : isOrd o -> complete I (COWi o).
intros oo; revert I; elim oo using isOrd_ind; intros.
assert (aux := fun o => isOrd_inv _ o H).
intros f fext fty fdir.
red in fty.
apply COTI_intro; intros; auto.
 apply Wdom_sup_closed; trivial.
 intros.
 apply fty in H2.
 revert H2; apply COTI_bound; auto.

 eapply Wf_complete; auto.
  apply COTI_bound; auto.

  red; intros.
  apply fty in H3.
  rewrite <- COTI_mono_succ; auto.
   revert H3; apply COTI_mono; auto.
   apply olts_le; apply lt_osucc_compat; trivial.

   apply Wf_typ; reflexivity.
Qed.

Lemma COWi_sup_intro f o o' :
  ext_fun o f ->
  increasing f ->
  isOrd o ->
  o' ∈ o ->
  (forall o'', o' ⊆ o'' -> o'' ∈ o -> f o'' ∈ Wf (COWi o')) ->
  sup o f ∈ Wf (COWi o').
intros fext fmono oo lto Hrec.
assert (aux := isOrd_inv).
assert (oo':isOrd o') by eauto.
pose (I := subset o (fun o'' => o' ⊆ o'')).
assert (fext' : ext_fun I f).
 do 2 red; intros.
 apply subset_elim1 in H; auto.
assert (sup o f == sup I f).
 apply eq_set_ax; intros z.
 rewrite sup_ax; trivial.
 rewrite sup_ax; trivial.
 split; destruct 1; intros.
  exists (o' ⊔ x).
   apply subset_intro.
    apply osup2_lt; trivial.
    apply osup2_incl1; eauto.

   revert H0; apply fmono; eauto.
    apply isOrd_osup2; eauto.
    apply osup2_incl2; eauto.

  apply subset_elim1 in H;eauto.
rewrite H.
eapply Wf_complete; eauto.
 apply COTI_bound; auto.

 apply COWi_complete; eauto.

 red; intros.
 apply subset_ax' in H0; auto with *.
  destruct H0; auto.

  apply incl_set_morph; reflexivity.

 exists o'.
  apply subset_intro; auto with *.

  intros.
  apply subset_ax' in H0; auto with *.
   destruct H0; auto.
   apply fmono; eauto.

   apply incl_set_morph; reflexivity.
Qed.


(* Simple co-recursion *)
Section SimpleCorecursion.

Hypothesis F:set->set.
Hypothesis Fm:morph1 F.
(*Existing Instance Fm.*)
Hypothesis Fty :
  forall X w, COW ⊆ Wf X -> Wf X ⊆ X ->
            w ∈ X -> F w ∈ Wf X.
(*Hint Resolve Fm.*)
Require Import ZFfix.

Lemma TI_WF_dom o :
  isOrd o ->
  TI F o ∈ Wdom.
induction 1 using isOrd_ind; intros.
rewrite TI_eq; auto with *.
apply Wdom_sup_closed; auto.
intros.
apply Wf_typ with (X:=Wdom); auto with *. 
Qed.

Lemma FTI_typ o w :
  isOrd o ->
  w ∈ COWi o ->
  F w ∈ Wf (COWi o).
intros.
apply Fty; trivial.
 rewrite COW_eqn; apply Wf_mono; apply COW_COWi; trivial.

 unfold COWi; rewrite <- COTI_mono_succ; auto with *.
 apply COTI_incl; auto.
Qed.

Definition productive X F :=
  forall w w0,
  w0 ∈ X -> (* w0 = observation *)
  w ∈ X -> w0 ⊆ w -> (* obs of w0 are the same in w *)
  F w0 ⊆ F w. (* F w0 can be observed both in F w *)
  
Hypothesis Fprod : productive Wdom F.
(*  forall X, X ⊆ Wdom -> COW ⊆ Wf X -> Wf X ⊆ X -> (* = K X *)
  productive X F.*)

Lemma FTI_mono : increasing (fun o => F (TI F o)).
red; intros.
apply Fprod.
 apply TI_WF_dom; trivial.

 apply TI_WF_dom; trivial.

 apply TI_mono; trivial.
Qed.

Lemma TI_WF_step o : isOrd o ->
  TI F o ⊆ F (TI F o).
red; intros.
apply TI_elim in H0; trivial.
destruct H0 as (o',?,?).
revert H1; apply FTI_mono; eauto using isOrd_inv.
Qed.

Lemma TI_WF_typ o : isOrd o -> TI F o ∈ COWi o.
intros oo; elim oo using isOrd_ind; intros.
apply COTI_intro; auto.
 apply TI_WF_dom; trivial.

 intros o'; intros.
 assert (oo':isOrd o') by eauto using isOrd_inv.
 rewrite TI_eq; auto.
 apply COWi_sup_intro; auto.
  apply FTI_mono.

  intros.
  assert (eqC: Wf (COWi o') == COWi (osucc o')).
   symmetry; apply COTI_mono_succ; auto.
   apply Wf_typ; reflexivity.
  apply Fty; auto.
   rewrite eqC; apply COW_COWi; auto.
   rewrite eqC; apply COTI_incl; auto.

   specialize H1 with (1:=H4); revert H1.
   apply COTI_mono; eauto using isOrd_inv.
Qed.

Definition COREC := TI F co_ord.

Lemma COREC_typ : COREC ∈ COW.
rewrite COW_def.
apply TI_WF_typ; trivial.
Qed.

Lemma COREC_eqn : COREC == F COREC.  
symmetry.
apply pre_incl_eq with (X:=COWi co_ord); auto.
 apply COWi_closure.

 rewrite <- COW_def.
 apply COREC_typ.

 rewrite <- COW_def, COW_eqn, COW_def.
 apply FTI_typ; trivial.
 apply COREC_typ.

 apply TI_WF_step; trivial.
Qed.


Lemma corec_typ w :
  w ∈ Wdom ->
  w == F w ->
  w ∈ COW.
intros.
rewrite COW_def.
elim co_ordo using isOrd_ind; intros.
apply COTI_intro; intros; auto.
rewrite H0.
apply FTI_typ; eauto using isOrd_inv.
Qed.

Lemma COREC_unique w :
  w ∈ Wdom ->
  w == F w ->
  w == COREC.
intros.
apply pre_incl_eq with (X:=COW); auto.
 rewrite <- COW_eqn; reflexivity.

 apply COREC_typ.

 apply corec_typ; trivial.

 unfold COREC.
 elim co_ordo using isOrd_ind; intros.
 red; intros.
 elim TI_elim with (3:=H4); intros; auto with *.
 rewrite H0; revert H6; apply Fprod; auto.
 apply TI_WF_dom; eauto using isOrd_inv.
Qed.

End SimpleCorecursion.

Let test := (COREC_typ,COREC_eqn,COREC_unique).
Print Assumptions test.


(* Productive functions : includes constructors *)

 
Lemma productive_id X : productive X (fun w => w).
  red; trivial.
Qed.

Lemma productive_comp X Y F0 G :
  (forall w, w ∈ X -> F0 w ∈ Y) ->
  productive X F0 ->
  productive Y G ->
  productive X (fun x => G (F0 x)).
unfold productive; auto.
Qed.

Lemma productive_cst X w : productive X (fun _ => w).
red; reflexivity.
Qed.



Lemma productive_cstr X x f :
  (forall w, w ∈ X -> is_cc_fun (B x) (f w)) ->
  (forall i, i ∈ B x -> productive X (fun w => cc_app (f w) i)) ->
  productive X (fun w => Wsup x (f w)).
unfold productive; intros fty fprod; intros.
apply Wsup_mono; auto with *.
Qed.

(* Indexed-corec *)

Require Import ZFfixfun.

Parameter I:set.
Parameter F:(set->set)->set->set.
Parameter Fm:Proper((eq_set==>eq_set)==>eq_set==>eq_set) F.
Existing Instance Fm.
Parameter Fty :
  forall X f, COW ⊆ Wf X -> Wf X ⊆ X ->
  morph1 f ->
  typ_fun f I X ->
  typ_fun (F f) I (Wf X).
Hint Resolve Fm.

Definition iproductive I X F :=
  forall w w0,
  morph1 w -> morph1 w0 ->
  typ_fun w0 I X -> (* w0 = observation *)
  typ_fun w I X ->
  incl_fam I w0 w -> (* obs of w0 are the same in w *)
  incl_fam I (F w0) (F w). (* F w0 can be observed both in F w *)
  
Parameter Fprod : iproductive I Wdom F.

Lemma TIF_WF_dom o :
  isOrd o ->
  typ_fun (TIF I F o) I Wdom.
intros oo; induction oo using isOrd_ind; red; intros.
rewrite TIF_eq; auto with *.
 apply Wdom_sup_closed.
  do 2 red; intros; apply Fm; auto with *.
  apply TIF_morph; trivial.

 intros.
 apply Wf_typ with (X:=Wdom); auto with *.
 apply Fty; auto.
  apply Wf_typ with (X:=Wdom); auto with *.
  apply TIF_morph; reflexivity.
Qed.

Lemma FTIF_typ o w (wm:morph1 w) :
  isOrd o ->
  typ_fun w I (COWi o) ->
  typ_fun (F w) I (Wf (COWi o)).
intros.
apply Fty; trivial.
 rewrite COW_eqn; apply Wf_mono; apply COW_COWi; trivial.

 unfold COWi; rewrite <- COTI_mono_succ; auto with *.
 apply COTI_incl; auto.
Qed.


Lemma FTIF_mono a : a ∈ I -> increasing (fun o => F (TIF I F o) a).
red; intros.
apply Fprod; auto.
 apply TIF_morph; auto with *.
 apply TIF_morph; auto with *.

 apply TIF_WF_dom; trivial.

 apply TIF_WF_dom; trivial.

 red; intros.
 apply TIF_mono; trivial.
Qed.

Lemma TIF_WF_step o : isOrd o ->
  incl_fam I (TIF I F o) (F (TIF I F o)).
do 2 red; intros.
apply TIF_elim in H1; trivial.
destruct H1 as (o',?,?).
revert H2; apply FTIF_mono; eauto using isOrd_inv.
Qed.

Lemma TIF_WF_typ o : isOrd o -> typ_fun (TIF I F o) I (COWi o).
intros oo; elim oo using isOrd_ind; red; intros.
apply COTI_intro; auto.
 apply TIF_WF_dom; trivial.

 intros o'; intros.
 assert (oo':isOrd o') by eauto using isOrd_inv.
 rewrite TIF_eq; auto.
 apply COWi_sup_intro; auto.
  do 2 red; intros.
  apply Fm; auto with *.
  apply TIF_morph; trivial.

  apply FTIF_mono; trivial.

  intros.
  assert (eqC: Wf (COWi o') == COWi (osucc o')).
   symmetry; apply COTI_mono_succ; auto.
   apply Wf_typ; reflexivity.
  apply Fty; auto.
   rewrite eqC; apply COW_COWi; auto.
   rewrite eqC; apply COTI_incl; auto.
   apply TIF_morph; reflexivity.

   red; intros.
   red in H1.
   specialize H1 with (1:=H5) (2:=H6); revert H1.
   apply COTI_mono; eauto using isOrd_inv.
Qed.

Definition ICOREC := TIF I F co_ord.

Instance ICOREC_morph : morph1 ICOREC.
apply TIF_morph; reflexivity.
Qed.


Lemma ICOREC_typ : typ_fun ICOREC I COW.
red; intros.
rewrite COW_def.
apply TIF_WF_typ; trivial.
Qed.

Lemma ICOREC_eqn : eq_fun I ICOREC (F ICOREC).
red; intros.
symmetry.
apply pre_incl_eq with (X:=COWi co_ord); auto.
 apply COWi_closure.

 rewrite <- COW_def.
 apply ICOREC_typ; trivial.

 rewrite <- COW_def, COW_eqn, COW_def.
 apply FTIF_typ; auto with *.
  apply ICOREC_typ.
  rewrite <- H0; trivial.

 rewrite H0.
 apply TIF_WF_step; trivial.
 rewrite <- H0; trivial.
Qed.


Lemma icorec_typ w :
  morph1 w ->
  typ_fun w I Wdom ->
  eq_fun I w (F w) ->
  typ_fun w I COW.
intros wm; intros.
rewrite COW_def.
elim co_ordo using isOrd_ind; intros.
red; intros.
apply COTI_intro; intros; auto.
red in H0; rewrite H0;[|trivial|reflexivity].
apply FTIF_typ; eauto using isOrd_inv.
Qed.

Lemma ICOREC_unique w :
  morph1 w ->
  typ_fun w I Wdom ->
  eq_fun I w (F w) ->
  eq_fun I w ICOREC.
intros wm; intros.
red; intros.
rewrite <- H2.
clear x' H2.
apply pre_incl_eq with (X:=COW); auto.
 rewrite <- COW_eqn; reflexivity.

 apply ICOREC_typ; trivial.

 apply icorec_typ; trivial.

 unfold ICOREC.
 revert x H1; elim co_ordo using isOrd_ind; intros.
 red; intros.
 elim TIF_elim with (4:=H5); intros; auto with *.
 red in H0; rewrite H0; [|trivial|reflexivity].
 revert H7; apply Fprod; auto.
  apply TIF_morph; reflexivity.

  apply TIF_WF_dom; eauto using isOrd_inv.

  red; intros; apply H3; trivial.
Qed.

Definition itest := (ICOREC_typ,ICOREC_eqn,COREC_unique).
Print Assumptions itest.
