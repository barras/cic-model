
Require Import ZF ZFpairs ZFnats ZFrank ZFreflect ZFform.
Require Import ZFlist.
Existing Instance UnboundedInterpretation.FTr_morph.

(******************************************************)
(* Using second-order WFR, we can build an interpretation function
   for *all* first-order formulae, hence we can build universes
   closed by *first-order* replacement *)

(* More on first-order formulae *)
(*
Lemma fo_down P :
  fo_form P -> ZFfo.fo_form (P (fun _=>True)).
induction 1; try (constructor; auto).
*apply ZFfo.FO_ext with (2:=IHfo_form); trivial.
*unfold ZFfo.bind, bind in *.
 apply ZFfo.FO_ext with (2:=IHfo_form); split; auto.
*unfold ZFfo.bind, bind in *.
 apply ZFfo.FO_ext with (2:=IHfo_form); split; [|destruct 1]; auto.
Qed.

Lemma fo_lift P :
  ZFfo.fo_form P ->
  exists2 P', fo_form P' & forall vs, P vs <-> P' (fun _=>True) vs.
induction 1.
*destruct IHfo_form as (A',?,?).
 exists A'; trivial; intros.
 rewrite <- H2; symmetry; auto.
*exists (fun _ i => x i == y i); [|reflexivity].
 constructor; trivial.
*exists (fun _ i => x i ∈ y i); [|reflexivity].
 constructor; trivial.
*exists (fun _ _ => True); [constructor|reflexivity].
*exists (fun _ _ => False); [constructor|reflexivity].
*destruct IHfo_form1 as (A',?,Aeq); destruct IHfo_form2 as (B',?,Beq).
 exists (fun K i => A' K i /\ B' K i); [constructor;trivial|intros].
 rewrite Aeq, Beq; reflexivity.
*destruct IHfo_form1 as (A',?,Aeq); destruct IHfo_form2 as (B',?,Beq).
 exists (fun K i => A' K i \/ B' K i); [constructor;trivial|intros].
 rewrite Aeq, Beq; reflexivity.
*destruct IHfo_form1 as (A',?,Aeq); destruct IHfo_form2 as (B',?,Beq).
 exists (fun K i => A' K i -> B' K i); [constructor;trivial|intros].
 rewrite Aeq, Beq; reflexivity.
*destruct IHfo_form as (B',?,Beq).
 exists (fun K i => forall x, K x -> B' K (icons x i)); [constructor;trivial|intros].
 +apply FO_ext with (2:=H0); intros.
  unfold bind. 
  apply fo_form_param with (1:=H0); [reflexivity|].
  intros [|k]; simpl; reflexivity.
 +apply fa_morph; intros x.
  rewrite <- Beq.
  unfold ZFfo.bind; simpl.
  split; auto.
*destruct IHfo_form as (B',?,Beq).
 exists (fun K i => exists x, K x /\ B' K (icons x i)); [constructor;trivial|intros].
 +apply FO_ext with (2:=H0); intros.
  unfold bind. 
  apply fo_form_param with (1:=H0); [reflexivity|].
  intros [|k]; simpl; reflexivity.
 +apply ex_morph; intros x.
  rewrite <- Beq.
  unfold ZFfo.bind; simpl.
  split; [|destruct 1]; auto.
Qed.
 *)
Require Import ZFfo.
(*
Ltac atom :=
  constructor; eexists; reflexivity.

Lemma fvi k : fvar (fun fv => fv k).
  exists k; reflexivity.
Qed.

Ltac fo_trivial :=
  first[apply FO_eq; apply fvi
       |apply FO_in; apply fvi
       |apply FO_T
       |apply FO_F].

(* Dup of ZFfo for fo_form defined in ZFreflect *)
Definition fo_in (t:(set->Prop)->fvs->set) :=
  fo_form (fun K i => i 0 ∈ t K (fun k => i (S k))).
Definition fo_eq (t:(set->Prop)->fvs->set) :=
  fo_form (fun K i => i 0 == t K (fun k => i (S k))).

Lemma fo_in_eq t :
  fo_in t ->
  fo_eq t.
intros.
apply FO_ext with (fun K i => forall z, K z -> z ∈ i 0 <-> z ∈ t K (fun k => i (S k))).
{intros; rewrite eq_set_ax.
 ; reflexivity. }
constructor; constructor; constructor; try fo_trivial.
apply fo_form_ren with (f:=lft S)(1:=H).
apply fo_form_ren with (f:=lft S)(1:=H).
Qed.
Lemma fo_eq_in t :
  fo_eq t ->
  fo_in t.
intros.
apply FO_ext with (fun i => exists z, z == t (fun k=>i(S k)) /\ i 0 ∈ z).
{split; intros.
 destruct H0 as (?&?&?).
 revert H1; apply eq_elim; trivial.
 exists (t (fun k => vs(S k))); split; [reflexivity|trivial]. }
constructor; constructor.
apply fo_form_ren with (f:=lft S)(1:=H).
fo_trivial.
Qed.

Lemma fo_in_proj k :
  fo_in (fun i => i k).
fo_trivial.
Qed.
Lemma fo_eq_proj k :
  fo_eq (fun i => i k).
fo_trivial.
Qed.

Lemma fo_in_in u v :
  fo_in u ->
  fo_in v ->
  fo_form (fun i => u i ∈ v i).
intros.
apply FO_ext with (fun i => exists z, z ∈ v i /\ z == u i).
{intros; rewrite in_set_def; reflexivity. }
constructor; constructor; trivial.
apply fo_in_eq; trivial.
Qed.
Lemma fo_eq_eq u v :
  fo_eq u ->
  fo_eq v ->
  fo_form (fun i => u i == v i).
intros.
apply FO_ext with (fun i => exists z, z == u i /\ z == v i).
{split; intros.
 destruct H1 as (?&?&?).
 rewrite <-H1; trivial.
 exists (u vs);split;[reflexivity|trivial]. }
constructor; constructor; trivial.
Qed.
*)
(*
Lemma fo_form_ex P :
  fo_form P ->
  exists A, A ∈ Form /\ forall vs l, (forall k, Fint_var l (nat2set k) == vs k) ->
                                     P (fun _=>True) vs <-> Fint l A.
induction 1.
*destruct IHfo_form as (Q & Qty & Qdef); exists Q;split;[trivial|intros].
 rewrite <-H; auto.
*destruct H as (k,?). 
 destruct H0 as (k',?). 
 subst  x y.
 exists (Feq (nat2set k) (nat2set k')); split.
  apply Feq_typ; apply nat2set_typ. 
 intros. 
 rewrite Fint_eq;[|apply nat2set_typ|apply nat2set_typ].
 rewrite !H; reflexivity.
*destruct H as (k,?). 
 destruct H0 as (k',?). 
 subst  x y.
 exists (Fin (nat2set k) (nat2set k')); split.
  apply Fin_typ; apply nat2set_typ. 
 intros. 
 rewrite Fint_in;[|apply nat2set_typ|apply nat2set_typ].
 rewrite !H; reflexivity.
*exists (Fimp Fbot Fbot); split;[apply Fimp_typ; apply Fbot_typ|]. 
 intros.  
 rewrite Fint_imp;[|apply Fbot_typ|apply Fbot_typ].
 split; intros; trivial.
*exists Fbot; split; [apply Fbot_typ|intros].
 split; intros; [contradiction|].
 apply Fint_bot in H0; trivial.
*destruct IHfo_form1 as (A'&?&?).
 destruct IHfo_form2 as (B'&?&?).
 exists (Fand A' B'); split; [apply Fand_typ; trivial|intros].
 rewrite Fint_and; trivial.
 apply and_iff_morphism; auto.
*destruct IHfo_form1 as (A'&?&?).
 destruct IHfo_form2 as (B'&?&?).
 exists (For A' B'); split; [apply For_typ; trivial|intros].
 rewrite Fint_or; trivial.
 apply or_iff_morphism; auto.
*destruct IHfo_form1 as (A'&?&?).
 destruct IHfo_form2 as (B'&?&?).
 exists (Fimp A' B'); split; [apply Fimp_typ; trivial|intros].
 rewrite Fint_imp; trivial.
 apply impl_morph; auto.
*destruct IHfo_form as (B'&?&?).
 exists (Ffa B'); split; [apply Ffa_typ; trivial|intros].
 rewrite Fint_fa; trivial.
 apply fa_morph; intros x.
 rewrite <-H1 with (vs:=icons x vs).
 +unfold bind; simpl.
  split; auto.
 +destruct k; simpl.
  apply Fiv_0.
  rewrite Fiv_S; trivial.
*destruct IHfo_form as (B'&?&?).
 exists (Fex B'); split; [apply Fex_typ; trivial|intros].
 rewrite Fint_ex; trivial.
 apply ex_morph; intros x.
 rewrite <-H1 with (vs:=icons x vs).
 +unfold bind; simpl.
  split; [destruct 1|]; auto.
 +destruct k; simpl.
  apply Fiv_0.
  rewrite Fiv_S; trivial.
Qed.
*)

Definition u_repl (*(K:set->Prop)*) (i:fvs) b :=
  let a := i 0 in
  let Rf := i 1 in
  let l := i 2 in
  let R x z := UnboundedInterpretation.FTr Rf (Cons x (Cons z l)) in
  Rf ∈ Form /\ (*->
  exists b,*) (*K b /\*) forall z, (*K z ->*) z ∈ b <->
      (exists x, (*K x /\*) x ∈ a /\ R x z /\ forall z', (*K z' ->*) R x z' -> z==z').

(* U is a Zermelo universe closed by replacement *)
Definition U M := refl_set VNlim_compl (u_repl::nil) M.


Lemma u_repl_comp P x vs vs' :
  In P (u_repl :: nil) -> eqfvs 3 vs vs' -> P vs x <-> P vs' x.
simpl; intros [e|[ ]] evs; subst P.
assert (e0 : vs 0 == vs' 0) by (apply evs; auto with arith).
assert (e1 : vs 1 == vs' 1) by (apply evs; auto with arith).
assert (e2 : vs 2 == vs' 2) by (apply evs; auto with arith).
clear evs.
unfold u_repl.
apply and_iff_morphism; [rewrite e1; reflexivity|].
apply fa_morph; intro z. 
apply iff_morph; [reflexivity|intros].
apply ex_morph; intro y. 
apply and_iff_morphism; [rewrite e0; reflexivity|].
apply and_iff_morphism.
*rewrite e1,e2; reflexivity.
*apply fa_morph; intros z'. 
 rewrite e1,e2; reflexivity.
Qed.
Hint Resolve u_repl_comp : core.
Hint Resolve zero_typ succ_typ : core.

Instance auxm : morph2 (fun _ Mi => rstep VNlim_compl (u_repl :: nil) Mi).
do 3 red; intros.
apply rstep_morph with (n:=3); auto with *.
Qed.

Hint Resolve auxm : core.

Lemma U_VNlim M : isVNlim (U M).
unfold U.
rewrite refl_set_alt_def with (compl:=VNlim_compl) (Pl:=u_repl::nil) (n:=3)(M0:=M); auto with *.
*apply VNlim_sup.
 +do 2 red; intros.
  apply rstep_morph with (n:=3); auto with *.
  apply refl_fin_morph with (n:=3); auto with *.
 +unfold rstep.
  intros; apply VNlim_compl_ok.
  apply wf_ax; apply ZFwf.isWf_intro; trivial.
 +intros.
  unfold refl_fin.
  rewrite <-natrec_S with (g:=fun _ Mi=>rstep VNlim_compl (u_repl::nil) Mi)(n:=k); auto with *.
  rewrite <-natrec_S
    with (g:=fun _ Mi=>rstep VNlim_compl (u_repl::nil) Mi)(n:=succ k); auto with *.
  intro; apply refl_fin_mono with (n:=3); auto with *.
   intros; apply VNlim_ext; apply wf_ax; apply ZFwf.isWf_intro.
   apply succ_intro2.  
   apply succ_intro1; reflexivity.
*intros; apply VNlim_ext; apply wf_ax; apply ZFwf.isWf_intro.
Qed.
 
Require Import ZFord ZFrank ZFgrothendieck.

Lemma U_repl M I Rf l :
  I ∈ U M -> l ∈ U M ->
  ZFfo.fo_form Rf ->
  let R x y := Rf (icons x (icons y (fun k => Fint_var l (nat2set k)))) in
  (forall x y , x ∈ I -> R x y -> y ∈ U M) -> 
  exists b, b∈U M /\ forall z, z ∈ b <->
                                 exists x, x ∈ I /\ R x z /\ forall z', R x z' -> z==z'.
intros tyI tyl foR R Rty.
destruct (U_VNlim M) as (o,(limo,Udef)).
assert (oo:isOrd o) by apply limo.
destruct ZFform.fo_form_ex with (1:=foR) as (P,(Pty,Pdef)).
destruct refl_set_model with (compl:=VNlim_compl) (Pl:=u_repl::nil) (n:=3)(M0:=M)
 (vs:=icons I (icons P (fun _=> l)))(P:=u_repl) as (b,(bty,bdef)); auto with *.
*intros; apply VNlim_ext. apply wf_ax; apply ZFwf.isWf_intro.
*fold (U M).
 destruct k as [|[|k]]; simpl; trivial.   
 rewrite Udef.
 elim Pty using N_ind; intros.
 +rewrite <-H0; trivial.
 +rewrite Udef in tyI.
  apply VN_incl with I; trivial.
 +apply VN_union.
  apply VNlim_pair;trivial.
  apply VNlim_pair;trivial.
*exists (repl I (fun x y => R x y /\ forall y', R x y' -> y==y')).
 red; simpl; intros.
 split; [trivial|].
 intros.
 rewrite repl_ax.
 +rewrite ex_ex2.
  apply ex_morph; intros x.
  unfold Fint in Pdef.
  apply and_iff_morphisml; [reflexivity|intros ? _].
  apply and_iff_morphism.
  ++apply Pdef.
    destruct k as [|[|k]]; simpl.
    apply Fiv_0.
    rewrite Fiv_S with (k:=0);apply Fiv_0.    
    rewrite Fiv_S with (k:=S k); simpl.
    rewrite Fiv_S; reflexivity.
  ++apply fa_morph; intros z'.
    apply impl_morph;[|reflexivity].
    apply Pdef.
    destruct k as [|[|k]]; simpl.
    apply Fiv_0.
    rewrite Fiv_S with (k:=0);apply Fiv_0.    
    rewrite Fiv_S with (k:=S k); simpl.
    rewrite Fiv_S; reflexivity.
 +intros.      
  revert H2; apply iff_impl.
  apply and_iff_morphism; [|apply fa_morph; intros y'0].
  ++apply ZFfo.fo_form_param in foR.
    apply foR; red.
    destruct a as [|[|?]]; simpl; auto with *.
  ++apply impl_morph;[|rewrite H1;reflexivity].      
    apply ZFfo.fo_form_param in foR.
    apply foR; red.
    destruct a as [|[|?]]; simpl; auto with *.
 +intros.
  destruct H0; destruct H1; auto.
*destruct bdef as (_,bdef); simpl in bdef.
  fold (U M) in bty.
  exists b; split; [trivial|intros].
  rewrite bdef.
  apply ex_morph; intros x; simpl.
  ++apply and_iff_morphisml; [reflexivity|intros ? _].
    apply and_iff_morphism.
    **symmetry; apply Pdef.
      destruct k as [|[|k]]; simpl.
      apply Fiv_0.
      rewrite Fiv_S with (k:=0);apply Fiv_0.    
      rewrite Fiv_S with (k:=S k); simpl.
      rewrite Fiv_S; reflexivity.
    **apply fa_morph; intros z'.
      apply impl_morph;[|reflexivity].
      symmetry; apply Pdef.
      destruct k as [|[|k]]; simpl.
      apply Fiv_0.
      rewrite Fiv_S with (k:=0);apply Fiv_0.    
      rewrite Fiv_S with (k:=S k); simpl.
      rewrite Fiv_S; reflexivity.
Qed.

(*

Lemma U_repl M I Rf l :
  I ∈ U M -> l ∈ U M ->
  fo_form Rf ->
  let R x y := Rf (fun _=>True) (icons x (icons y (fun k => Fint_var l (nat2set k)))) in
  (forall x y , x ∈ I -> R x y -> y ∈ U M) -> 
  exists b, b∈U M /\ forall z, z ∈ b <->
                                 exists x, x ∈ I /\ R x z /\ forall z', R x z' -> z==z'.
intros tyI tyl foR R Rty.
destruct (U_VNlim M) as (o,(limo,Udef)).
assert (oo:isOrd o) by apply limo.
destruct fo_form_ex with (1:=foR) as (P,(Pty,Pdef)).

destruct refl_set_model with (compl:=VNlim_compl) (Pl:=u_repl::nil) (n:=3)(M0:=M)
 (vs:=icons I (icons P (fun _=> l)))(P:=u_repl) as (b,(bty,bdef)); auto with *.
*intros; apply VNlim_ext. apply wf_ax; apply ZFwf.isWf_intro.
*fold (U M).
 destruct k as [|[|k]]; simpl; trivial.   
 rewrite Udef.
 elim Pty using N_ind; intros.
 +rewrite <-H0; trivial.
 +rewrite Udef in tyI.
  apply VN_incl with I; trivial.
 +apply VN_union.
  apply VNlim_pair;trivial.
  apply VNlim_pair;trivial.
*exists (repl I (fun x y => R x y /\ forall y', R x y' -> y==y')).
 red; simpl; intros.
 split; [trivial|].
 intros.
 rewrite repl_ax.
 +rewrite ex_ex2.
  apply ex_morph; intros x.
  unfold Fint in Pdef.
  apply and_iff_morphisml; [reflexivity|intros ? _].
  apply and_iff_morphism.
  ++apply Pdef.
    destruct k as [|[|k]]; simpl.
    apply Fiv_0.
    rewrite Fiv_S with (k:=0);apply Fiv_0.    
    rewrite Fiv_S with (k:=S k); simpl.
    rewrite Fiv_S; reflexivity.
  ++apply fa_morph; intros z'.
    apply impl_morph;[|reflexivity].
    apply Pdef.
    destruct k as [|[|k]]; simpl.
    apply Fiv_0.
    rewrite Fiv_S with (k:=0);apply Fiv_0.    
    rewrite Fiv_S with (k:=S k); simpl.
    rewrite Fiv_S; reflexivity.
 +intros.      
  revert H2; apply iff_impl.
  apply and_iff_morphism; [|apply fa_morph; intros y'0].
  ++apply fo_form_param with (1:=foR); red; [reflexivity|].
    destruct a as [|[|?]]; simpl; auto with *.
  ++apply impl_morph;[|rewrite H1;reflexivity].      
    apply fo_form_param with (1:=foR); red; [reflexivity|].
    destruct a as [|[|?]]; simpl; auto with *.
 +intros.
  destruct H0; destruct H1; auto.
*destruct bdef as (_,bdef); simpl in bdef.
  fold (U M) in bty.
  exists b; split; [trivial|intros].
  rewrite bdef.
  apply ex_morph; intros x; simpl.
  ++apply and_iff_morphisml; [reflexivity|intros ? _].
    apply and_iff_morphism.
    **symmetry; apply Pdef.
      destruct k as [|[|k]]; simpl.
      apply Fiv_0.
      rewrite Fiv_S with (k:=0);apply Fiv_0.    
      rewrite Fiv_S with (k:=S k); simpl.
      rewrite Fiv_S; reflexivity.
    **apply fa_morph; intros z'.
      apply impl_morph;[|reflexivity].
      symmetry; apply Pdef.
      destruct k as [|[|k]]; simpl.
      apply Fiv_0.
      rewrite Fiv_S with (k:=0);apply Fiv_0.    
      rewrite Fiv_S with (k:=S k); simpl.
      rewrite Fiv_S; reflexivity.
Qed.
*)
Print Assumptions U_repl.
Print Assumptions refl_set_model  .

Module ClosedRel.
(* only works for R closed.... *)
Definition fo_rel (R:set->set->Prop) (vs:fvs) :=
  R (vs 0) (vs 1).

Record fo_grot_univ (U:set) : Prop := {
  G_trans : forall x y, y ∈ x -> x ∈ U -> y ∈ U;
  G_pair : forall x y, x ∈ U -> y ∈ U -> pair x y ∈ U;
  G_power : forall x, x ∈ U -> power x ∈ U;
  G_union : forall x, x ∈ U -> union x ∈ U;
  G_repl_hidden : forall I R, ZFfo.fo_form (fo_rel R) -> ZFrepl.repl_rel I R -> I ∈ U ->
                (forall x y, x ∈ I -> R x y -> y ∈ U) ->
                repl I R ∈ U }.

Instance fo_grot_univ_morph : Proper (eq_set==>iff) fo_grot_univ.
apply morph_impl_iff1; auto with *.
do 3 red; intros.
destruct H0 as (Gtr,G2,Gpow,Gun,Grepl).
split; intros.
*rewrite <- H in H1|-*; eauto.
*rewrite <- H in H0,H1|-*; auto.
*rewrite <- H in H0|-*; auto.
*rewrite <- H in H0|-*; auto.
*rewrite <- H in H2|-*.
 apply Grepl; intros; auto.
 rewrite H; eauto.
Qed.

 Lemma GU M : fo_grot_univ (U M).
destruct (U_VNlim M) as (o,(limo,?)).
assert (oo:isOrd o) by apply limo.
rewrite H.
split; intros.
*apply VN_trans with x; auto.
*apply VNlim_pair; auto.
*apply VNlim_power; auto.
*apply VN_union; auto.
*destruct U_repl with (M:=M)(l:=I)(Rf:=fo_rel R)(I:=I); auto.
 +rewrite H; trivial.
 +rewrite H; trivial.
 +intros.
  rewrite H; apply H3 with x; trivial.
 +destruct H4.
  rewrite <-H.
  setoid_replace (repl I R) with x; trivial.
  apply eq_set_ax; intros z.
  rewrite H5.  
  rewrite repl_ax; try apply H1.
  rewrite <- ex_ex2.
  apply ex2_morph'; [reflexivity|intros w wty].
  unfold fo_rel; simpl.
  split;[split;trivial|destruct 1; trivial].
  intros.
  revert H6 H7; apply H1; trivial.
Qed.
Print Assumptions GU.

End ClosedRel.


Definition fo_rel (R:set->set->set->Prop) :=
  bind (fun x =>
          bind (fun y i =>
                  exists2 l, (forall k, i k == Fint_var l (nat2set k)) & R l x y)).

Record fo_grot_univ (U:set) : Prop := {
  G_trans : forall x y, y ∈ x -> x ∈ U -> y ∈ U;
  G_pair : forall x y, x ∈ U -> y ∈ U -> pair x y ∈ U;
  G_power : forall x, x ∈ U -> power x ∈ U;
  G_union : forall x, x ∈ U -> union x ∈ U;
  G_repl_hidden : forall I R l,
                  l ∈ U ->
                  ZFfo.fo_form (fo_rel R)-> ZFrepl.repl_rel I (R l) -> I ∈ U ->
                (forall x y, x ∈ I -> R l x y -> y ∈ U) ->
                repl I (R l) ∈ U }.

Instance fo_grot_univ_morph : Proper (eq_set==>iff) fo_grot_univ.
apply morph_impl_iff1; auto with *.
do 3 red; intros.
destruct H0 as (Gtr,G2,Gpow,Gun,Grepl).
split; intros.
*rewrite <- H in H1|-*; eauto.
*rewrite <- H in H0,H1|-*; auto.
*rewrite <- H in H0|-*; auto.
*rewrite <- H in H0|-*; auto.
*rewrite <- H in H3|-*.
 apply Grepl; intros; auto.
 rewrite H; eauto.
 rewrite H; eauto.
Qed.

 Lemma GU M : fo_grot_univ (U M).
destruct (U_VNlim M) as (o,(limo,?)).
assert (oo:isOrd o) by apply limo.
rewrite H.
split; intros.
*apply VN_trans with x; auto.
*apply VNlim_pair; auto.
*apply VNlim_power; auto.
*apply VN_union; auto.
*rewrite <-H in H0, H3.
 destruct U_repl with (M:=M)(l:=l)(Rf:=fo_rel R)(I:=I); auto.
 +intros.
  rewrite H; apply H4 with x; trivial.
unfold fo_rel, bind in H6; simpl in H6.
destruct H6.
admit.
 +destruct H5.
  rewrite <-H.
  setoid_replace (repl I (R l)) with x; trivial.
  apply eq_set_ax; intros z.
  rewrite H6.  
  rewrite repl_ax; try apply H2.
  rewrite <- ex_ex2.
  apply ex2_morph'; [reflexivity|intros w wty].
  unfold fo_rel, bind; simpl.
  split;[split;trivial|destruct 1; trivial].
  intros.
  revert H6 H7; apply H1; trivial.
Qed.
Print Assumptions GU.

Require Import ZFsum.
Require Import ZFrelations.

Definition fo_fun (f:set->set) :=
  ZFfo.fo_form (fo_rel (fun x y => y == f x)).

Section FoGrothendieckUniverse.

Variable U : set.
Hypothesis grot : fo_grot_univ U.

Lemma G_incl : forall x y, x ∈ U -> y ⊆ x -> y ∈ U.
intros.
apply G_trans with (power x); trivial.
 rewrite power_ax; auto.

 apply G_power; trivial.
Qed.

Lemma G_subset : forall x P, x ∈ U -> subset x P ∈ U.
intros.
apply G_incl with x; trivial.
red; intros.
apply subset_elim1 in H0; trivial.
Qed.

Lemma G_singl : forall x, x ∈ U -> singl x ∈ U.
unfold singl; intros; apply G_pair; auto.
Qed.


Lemma fo_fun_morph f : fo_fun f -> morph1 f.
do 2 red; intros.
apply ZFfo.fo_form_param in H.
do 2 red in H.
unfold fo_rel in H.
rewrite (H (icons y (icons (f x) (fun _ => empty)))
           (icons x (icons (f x) (fun _ => empty)))); simpl.
*reflexivity.
*intros [|k]; simpl;[symmetry; trivial|reflexivity].
Qed.
Hint Resolve fo_fun_morph : core.

Lemma G_replf : forall A F,
  fo_fun F ->
  A ∈ U ->
  (forall x, x ∈ A -> F x ∈ U) ->
  replf A F ∈ U.
intros.
rewrite ZFrepl.replf_def; [|auto].
apply G_repl_hidden; intros; auto.
*apply ZFrepl.repl_rel_fun; auto.
*rewrite H3; auto.
Qed.

Lemma G_union2 : forall x y, x ∈ U -> y ∈ U -> x ∪ y ∈ U.
intros.
unfold union2.
apply G_union; trivial.
apply G_pair; trivial.
Qed.

Lemma G_sup A B :
  fo_fun B ->
  A ∈ U ->
  (forall x, x ∈ A -> B x ∈ U) ->
  sup A B ∈ U.
intros.
apply G_union; trivial.
apply G_replf; trivial.
Qed.

Lemma G_nat x : x ∈ U -> ZFnats.N ⊆ U.
red; intros.
elim H0 using ZFnats.N_ind; intros.
 rewrite <- H2; trivial.

 apply G_incl with x; trivial.

 apply G_union2; trivial.
 apply G_singl; trivial.
Qed.

Local Transparent prodcart sigma couple.

Lemma G_prodcart : forall A B, A ∈ U -> B ∈ U -> prodcart A B ∈ U.
intros.
unfold prodcart.
apply G_subset; intros; trivial.
apply G_power; trivial.
apply G_power; trivial.
apply G_union2; trivial.
Qed.

  Lemma G_sigma A B :
    fo_fun B ->
    A ∈ U ->
    (forall x, x ∈ A -> B x ∈ U) ->
    sigma A B ∈ U.
intros.
apply G_subset; trivial.
apply G_prodcart; trivial.
apply G_sup; trivial.
Qed.

Lemma G_couple : forall x y, x ∈ U -> y ∈ U -> couple x y ∈ U.
intros.
unfold couple.
apply G_pair; trivial.
 apply G_singl; trivial.

 apply G_pair; trivial.
Qed.

Opaque prodcart sigma couple.


Lemma G_sum X Y : X ∈ U -> Y ∈ U -> sum X Y ∈ U.
unfold sum; intros.
apply G_union2; apply G_prodcart; trivial.
 apply G_singl; apply G_nat with X; trivial.

 apply G_singl; apply G_nat with X; trivial.
 apply ZFnats.succ_typ;  apply ZFnats.zero_typ.
Qed.

Lemma G_sumcase A B f g a :
  morph1 f ->
  morph1 g ->
  a ∈ sum A B ->
  (forall a, a ∈ A -> f a ∈ U) ->
  (forall a, a ∈ B -> g a ∈ U) ->
  sum_case f g a ∈ U.
intros.
apply sum_case_ind with (6:=H1); intros; auto.
apply morph_impl_iff1; auto with *.
do 3 red; intros.
rewrite <- H4; trivial.
Qed.

Lemma G_rel : forall A B, A ∈ U -> B ∈ U -> rel A B ∈ U.
intros.
unfold rel.
apply G_power; trivial.
apply G_prodcart; trivial.
Qed.

Local Transparent dep_func func cc_prod lam app cc_lam cc_app.
Lemma G_func : forall A B, A ∈ U -> B ∈ U -> func A B ∈ U.
intros.
unfold func.
apply G_subset; intros; trivial.
apply G_rel; trivial.
Qed.

Lemma G_dep_func : forall X Y,
  fo_fun Y ->
  X ∈ U ->
  (forall x, x ∈ X -> Y x ∈ U) ->
  dep_func X Y ∈ U.
intros.
unfold dep_func.
apply G_subset; intros; trivial.
apply G_func; trivial.
unfold dep_image.
apply G_union; trivial.
apply G_replf; trivial.
Qed.

Lemma G_app f x :
  f ∈ U -> x ∈ U -> app f x ∈ U.
unfold app; intros.
apply G_union; trivial.
apply G_subset.
unfold rel_image.
apply G_subset.
apply G_union; trivial.
apply G_union; trivial.
Qed.

Lemma fo_fun_eq F :
  fo_fun F <-> fo_eq (fun i => F (i 0)).
unfold fo_fun, fo_rel, fo_eq.
split; intro; apply fo_form_ren with (f:= icons 1 (icons 0 id)) in H; trivial.
Qed. 
 
Lemma G_cc_lam A F :
    fo_fun F ->
    A ∈ U ->
    (forall x, x ∈ A -> F x ∈ U) ->
    cc_lam A F ∈ U.
intros.
unfold cc_lam.
apply G_sup; intros; trivial.
{apply fo_eq_eq; [fo_trivial|].
 apply fo_in_eq.
 apply fo_replf.
 *apply fo_eq_in; trivial.
  apply fo_fun_eq; trivial.
 *apply fo_in_eq.
  apply fo_couple; fo_trivial. }
apply G_replf; intros; auto.
*apply fo_fun_eq.
 apply fo_in_eq.
 apply fo_couple.
 red; unfold fo_rel.
  .
 apply fo_couple.
  do 2 red; intros; apply couple_morph; auto with *.

 apply G_couple; trivial.
  apply G_trans with A; trivial.

  apply G_trans with (F x); auto.
Qed.

  Lemma G_cc_app f x :
    f ∈ U -> x ∈ U -> cc_app f x ∈ U.
unfold cc_app; intros.
unfold rel_image.
apply G_subset.
apply G_union; trivial.
apply G_union; trivial.
apply G_subset; trivial.
Qed.

  Lemma G_cc_prod A B :
    ext_fun A B ->
    A ∈ U ->
    (forall x, x ∈ A -> B x ∈ U) ->
    cc_prod A B ∈ U.
intros.
unfold cc_prod.
apply G_replf; auto with *.
 apply G_dep_func; intros; auto with *.

 intros.
 apply G_cc_lam; intros; auto.
  do 2 red; intros; apply app_morph; auto with *.

  apply G_app.
   apply G_trans with (dep_func A B); trivial.
   apply G_dep_func; trivial.

   apply G_trans with A; trivial.
Qed.
Opaque dep_func func cc_prod lam app cc_lam cc_app.
