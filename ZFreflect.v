Require Import ZF.
  
Definition icons {A} (x : A) (f : nat -> A) (k : nat) :=
  match k with
  | 0 => x
  | S k0 => f k0
  end.

Definition fvs := nat->set.

Definition eqfvs k (vs vs':fvs) :=
  forall i, (i<k)%nat -> vs i == vs' i.

Definition reflect M P :=
  forall vs:fvs, (forall k, vs k ∈ M) -> (P (fun _ => True) vs <-> P (fun x=>x∈M) vs).

 Instance reflect_morph : Proper (eq_set==>(pointwise_relation set iff ==> pointwise_relation fvs iff)==>iff) reflect.
do 3 red; intros.
unfold reflect.
apply fa_morph; intros vs.
apply impl_morph.
*apply fa_morph; intros k.
 rewrite H; reflexivity.
*intros.
 apply iff_morph. 
 +apply H0; reflexivity.
 +apply H0.
 red; intros.
 rewrite H; reflexivity.
Qed.

Definition fvar (f : fvs->set) : Prop :=
  exists k, f = (fun vs => vs k).

Definition bind (A:set->(set->Prop)->fvs->Prop) : (set->Prop) -> fvs -> Prop :=
  fun K vs => A (vs 0) K (fun k => vs (S k)).

Inductive fo_form : ((set->Prop)->fvs->Prop) -> Prop :=
| FO_ext A B : (forall K vs, (A K vs<->B K vs)) -> fo_form A -> fo_form B
| FO_eq x y  : fvar x -> fvar y -> fo_form (fun K vs => x vs == y vs)
| FO_in x y  : fvar x -> fvar y -> fo_form (fun K vs => x vs ∈ y vs)
| FO_T       : fo_form (fun K vs => True)
| FO_F       : fo_form (fun K vs => False)
| FO_and A B : fo_form A -> fo_form B -> fo_form (fun K vs => A K vs/\B K vs)
| FO_or A B  : fo_form A -> fo_form B -> fo_form (fun K vs => A K vs\/B K vs)
| FO_imp A B : fo_form A -> fo_form B -> fo_form (fun K vs => A K vs->B K vs)
| FO_fa B    : fo_form (bind B) ->
               fo_form (fun K vs => forall x:set, K x -> B x K vs)
| FO_ex B    : fo_form (bind B) ->
               fo_form (fun K vs => exists x:set, K x /\ B x K vs).
(*Inductive fo_form (K:set->Prop) (vars : fvs) : Prop -> Prop :=
| FO_ext A B : (A<->B) -> fo_form K vars A -> fo_form K vars B
| FO_eq x y  : is_var x vars -> is_var y vars -> fo_form K vars (x == y)
| FO_in x y  : is_var x vars -> is_var y vars -> fo_form K vars (x ∈ y)
| FO_T       : fo_form K vars True
| FO_F       : fo_form K vars False
| FO_and A B : fo_form K vars A -> fo_form K vars B -> fo_form K vars (A/\B)
| FO_or A B  : fo_form K vars A -> fo_form K vars B -> fo_form K vars (A\/B)
| FO_imp A B : fo_form K vars A -> fo_form K vars B -> fo_form K vars (A->B)
| FO_fa B    : (forall x, fo_form K (push_var x vars) (B x)) ->
               fo_form K vars (forall x:set, K x -> B x)
| FO_ex B    : (forall x, fo_form K (push_var x vars) (B x)) ->
               fo_form K vars (exists x:set, K x /\ B x).*)

Lemma fo_form_param (P : (set -> Prop) -> fvs -> Prop) :
       fo_form P ->
       Proper (pointwise_relation set iff ==>
               pointwise_relation nat eq_set ==> iff)
         P.
Proof.
intros fo Q Q' eqQ fv fv' eqfv; revert (*Q Q' eqQ*) fv fv' eqfv.
induction fo; intros.
*rewrite <- (H Q), <- (H Q'); auto.
*destruct H; destruct H0; subst x y.
 rewrite (eqfv x0), (eqfv x1); reflexivity.
*destruct H; destruct H0; subst x y.
 rewrite (eqfv x0), (eqfv x1); reflexivity.
*reflexivity.
*reflexivity.
*apply and_iff_morphism; auto.
*apply or_iff_morphism; auto.
*apply impl_morph; auto.
*apply fa_morph; intros x.
 apply impl_morph; [trivial| intros].
 unfold bind in IHfo.
 apply IHfo with (fv:=icons x fv) (fv':=icons x fv'). 
 intros [|n]; simpl; auto with *.
*apply ex_morph; intros x.
 apply and_iff_morphism; [trivial|].
 unfold bind in IHfo.
 apply IHfo with (fv:=icons x fv) (fv':=icons x fv'). 
 intros [|n]; simpl; auto with *.
Qed.

Definition fclos k P :=
  forall (K:set->Prop) (vs vs':fvs), eqfvs k vs vs' -> (P K vs <-> P K vs').

Lemma compacity P : fo_form P -> exists k, fclos k P.
intro fo; unfold fclos; induction fo.
*destruct IHfo as (k,?); exists k; intros.
 do 2 rewrite <-H; auto.
*destruct H as (k,?); destruct H0 as (k',?); subst x y.
 exists (S(Peano.max k k')); intros.
 rewrite <-(H k);[|auto with arith].
 rewrite <-(H k');[|auto with arith].
 reflexivity.
*destruct H as (k,?); destruct H0 as (k',?); subst x y.
 exists (S(Peano.max k k')); intros.
 rewrite <-(H k);[|auto with arith].
 rewrite <-(H k');[|auto with arith].
 reflexivity.
*exists 0; reflexivity.
*exists 0; reflexivity.
*destruct IHfo1 as (k,?).
 destruct IHfo2 as (k',?).
 exists (S(Peano.max k k')); intros.
 rewrite <-H with (vs:=vs)(vs':=vs').
 rewrite <-H0 with (vs:=vs)(vs':=vs');[reflexivity|].
 red; intros; apply H1; rewrite H2; auto with arith.
 red; intros; apply H1; rewrite H2; auto with arith.
*destruct IHfo1 as (k,?).
 destruct IHfo2 as (k',?).
 exists (S(Peano.max k k')); intros.
 rewrite <-H with (vs:=vs)(vs':=vs').
 rewrite <-H0 with (vs:=vs)(vs':=vs');[reflexivity|].
 red; intros; apply H1; rewrite H2; auto with arith.
 red; intros; apply H1; rewrite H2; auto with arith.
*destruct IHfo1 as (k,?).
 destruct IHfo2 as (k',?).
 exists (S(Peano.max k k')); intros.
 rewrite <-H with (vs:=vs)(vs':=vs').
 rewrite <-H0 with (vs:=vs)(vs':=vs');[reflexivity|].
 red; intros; apply H1; rewrite H2; auto with arith.
 red; intros; apply H1; rewrite H2; auto with arith.
*destruct IHfo as (k,?).
 exists k; intros. (* not optimal *) 
 apply fa_morph; intro x.
 apply impl_morph; [reflexivity|intros].
 apply (H K (icons x vs) (icons x vs')).
 red; intros; destruct i; simpl; [reflexivity|apply H0;auto with arith].
*destruct IHfo as (k,?).
 exists k; intros. (* not optimal *) 
 apply ex_morph; intro x.
 apply and_iff_morphism; [reflexivity|intros].
 apply (H K (icons x vs) (icons x vs')).
 red; intros; destruct i; simpl; [reflexivity|apply H0;auto with arith].
Qed.

Inductive fo_wit : ((set->Prop)->fvs->Prop) ->
                   list(fvs->set->Prop) ->list(fvs->set->Prop) -> Prop :=
| FW_ext A B Q nQ : (forall K vs, (A K vs<->B K vs)) -> fo_wit A Q nQ -> fo_wit B Q nQ
| FW_eq x y      : fvar x -> fvar y -> fo_wit (fun K vs => x vs == y vs) nil nil
| FW_in x y      : fvar x -> fvar y -> fo_wit (fun K vs => x vs ∈ y vs) nil nil
| FW_T           : fo_wit (fun K vs => True) nil nil
| FW_F           : fo_wit (fun K vs => False) nil nil
| FW_and A B P nP Q nQ : fo_wit A P nP -> fo_wit B Q nQ ->
                         fo_wit (fun K vs => A K vs/\B K vs) (P++Q) (nP++nQ)
| FW_or A B P nP Q nQ  : fo_wit A P nP -> fo_wit B Q nQ ->
                         fo_wit (fun K vs => A K vs\/B K vs) (P++Q) (nP++nQ)
| FW_imp A B P nP Q nQ : fo_wit A P nP -> fo_wit B Q nQ ->
                         fo_wit (fun K vs => A K vs->B K vs) (P++Q) (nP++nQ)
| FW_fa B Q nQ         : fo_wit (bind B) Q nQ ->
                         fo_wit (fun K vs => forall x:set, K x -> B x K vs)
                           Q ((fun vs x => B x (fun _=>True) vs)::nQ)
| FW_ex B Q nQ         : fo_wit (bind B) Q nQ ->
                         fo_wit (fun K vs => exists x:set, K x /\ B x K vs)
                           ((fun vs x => B x (fun _=>True) vs)::Q) nQ.


Lemma fo_wit_form A P nP : fo_wit A P nP -> fo_form A.
induction 1; try constructor; eauto.
apply FO_ext with A; auto.
Qed.

Lemma fo_wit_ex_cond_form A P nP :
  fo_wit A P nP ->
  forall Q, In Q P ->
            exists2 Q', fo_form Q' &
                        Q=fun vs x => Q' (fun _=>True) (icons x vs).
induction 1; simpl; intros; try contradiction; auto.
*rewrite in_app_iff in H1; destruct H1; auto.
*rewrite in_app_iff in H1; destruct H1; auto.
*rewrite in_app_iff in H1; destruct H1; auto.
*destruct H0;[|auto].
 exists (bind B).
  apply fo_wit_form with (1:=H).
  unfold bind; simpl; auto.
Qed.

Lemma fo_wit_fa_cond_form A P nP :
  fo_wit A P nP ->
  forall Q, In Q nP ->
            exists2 Q', fo_form Q' &
                        Q=fun vs x => Q' (fun _=>True) (icons x vs).
induction 1; simpl; intros; try contradiction; auto.
*rewrite in_app_iff in H1; destruct H1; auto.
*rewrite in_app_iff in H1; destruct H1; auto.
*rewrite in_app_iff in H1; destruct H1; auto.
*destruct H0;[|auto].
 exists (bind B).
  apply fo_wit_form with (1:=H).
  unfold bind; simpl; auto.
Qed.

Lemma fo_wit_ex_cond_morph A P nP K :
  fo_wit A P nP ->
  forall Q : fvs -> set -> Prop,
  In Q P ->
  Proper (eq_set ==> iff) (Q K).
Proof.
intros fo Q inQ.
destruct fo_wit_ex_cond_form with (1:=fo)(2:=inQ) as (B,foB,?); subst Q.
do 2 red; intros.
apply fo_form_param with (1:=foB); [red; reflexivity|intros [|n]; simpl; auto with *].
Qed.

Lemma fo_wit_fa_cond_morph A P nP K :
  fo_wit A P nP ->
  forall Q : fvs -> set -> Prop,
  In Q nP ->
  Proper (eq_set ==> iff) (Q K).
Proof.
intros fo Q inQ.
destruct fo_wit_fa_cond_form with (1:=fo)(2:=inQ) as (B,foB,?); subst Q.
do 2 red; intros.
apply fo_form_param with (1:=foB); [red; reflexivity|intros [|n]; simpl; auto with *].
Qed.

Lemma fo_form_ex_wit A : fo_form A -> exists P nP, fo_wit A P nP.
induction 1.
*destruct IHfo_form as (P&nP&?); exists P; exists nP.
 apply FW_ext with A; trivial.
*eexists; eexists; constructor; trivial.
*eexists; eexists; constructor; trivial.
*eexists; eexists; constructor; trivial.
*eexists; eexists; constructor; trivial.
*destruct IHfo_form1 as (P&nP&?).
 destruct IHfo_form2 as (Q&nQ&?).
 eexists; eexists; constructor; eassumption.
*destruct IHfo_form1 as (P&nP&?).
 destruct IHfo_form2 as (Q&nQ&?).
 eexists; eexists; constructor; eassumption.
*destruct IHfo_form1 as (P&nP&?).
 destruct IHfo_form2 as (Q&nQ&?).
 eexists; eexists; constructor; eassumption.
*destruct IHfo_form as (P&nP&?).
 eexists; eexists; constructor; eassumption.
*destruct IHfo_form as (P&nP&?).
 eexists; eexists; constructor; eassumption.
Qed.

Lemma compacity_wit P Q nQ :
  fo_wit P Q nQ ->
  exists n,
    (forall A x vs vs', In A Q -> eqfvs n vs vs' -> A vs x <-> A vs' x) /\
    (forall A x vs vs', In A nQ -> eqfvs n vs vs' -> A vs x <-> A vs' x).
induction 1; simpl; auto; try (exists 0; split; intros; contradiction).
*destruct IHfo_wit1 as (n,(?,?)).
 destruct IHfo_wit2 as (n',(?,?)).
 exists (Peano.max n n'); split; intros; rewrite in_app_iff in H5; destruct H5; auto.
 +apply H1; auto.
  red; intros; apply H6; eauto with arith.
 +apply H3; auto.
  red; intros; apply H6; eauto with arith.
 +apply H2; auto.
  red; intros; apply H6; eauto with arith.
 +apply H4; auto.
  red; intros; apply H6; eauto with arith.
*destruct IHfo_wit1 as (n,(?,?)).
 destruct IHfo_wit2 as (n',(?,?)).
 exists (Peano.max n n'); split; intros; rewrite in_app_iff in H5; destruct H5; auto.
 +apply H1; auto.
  red; intros; apply H6; eauto with arith.
 +apply H3; auto.
  red; intros; apply H6; eauto with arith.
 +apply H2; auto.
  red; intros; apply H6; eauto with arith.
 +apply H4; auto.
  red; intros; apply H6; eauto with arith.
*destruct IHfo_wit1 as (n,(?,?)).
 destruct IHfo_wit2 as (n',(?,?)).
 exists (Peano.max n n'); split; intros; rewrite in_app_iff in H5; destruct H5; auto.
 +apply H1; auto.
  red; intros; apply H6; eauto with arith.
 +apply H3; auto.
  red; intros; apply H6; eauto with arith.
 +apply H2; auto.
  red; intros; apply H6; eauto with arith.
 +apply H4; auto.
  red; intros; apply H6; eauto with arith.
*destruct IHfo_wit as (n,(?,?)).
 apply fo_wit_form in H.
 apply compacity in H.
 destruct H as (n',?).
 exists (Peano.max n n'); split; intros; [|destruct H2].
 +apply H0; auto.
  red; intros; apply H3; eauto with arith.
 +subst A.
  apply (H (fun _=>True) (icons x vs)(icons x vs')).
  red; intros.
  destruct i; simpl; [reflexivity|].
  apply H3; eauto with arith.
 +apply H1; auto.
  red; intros; apply H3; eauto with arith.
*destruct IHfo_wit as (n,(?,?)).
 apply fo_wit_form in H.
 apply compacity in H.
 destruct H as (n',?).
 exists (Peano.max n n'); split; intros; [destruct H2|].
 +subst A.
  apply (H (fun _=>True) (icons x vs)(icons x vs')).
  red; intros.
  destruct i; simpl; [reflexivity|].
  apply H3; eauto with arith.
 +apply H0; auto.
  red; intros; apply H3; eauto with arith.
 +apply H1; auto.
  red; intros; apply H3; eauto with arith.
Qed.

Lemma reflect_conditions M P Q nQ :
  fo_wit P Q nQ ->
  (forall C (vs:fvs), In C Q -> (forall k, vs k ∈ M) ->
                      (exists x, C vs x) -> exists x', x' ∈ M /\ C vs x') ->
  (forall C (vs:fvs), In C nQ -> (forall k, vs k ∈ M) ->
                      (forall x, x ∈ M -> C vs x) -> forall x, C vs x) ->
  reflect M P.
intros foP wit nwit; revert wit nwit.
red; induction foP; intros; try reflexivity.
*do 2 rewrite <- H; auto.
*apply and_iff_morphism; auto.
 +apply IHfoP1; trivial.
  ++intros; apply wit; [rewrite in_app_iff; auto|trivial|eauto].
  ++intros; apply nwit;[rewrite in_app_iff; auto|trivial|trivial].
 +apply IHfoP2; trivial.
  ++intros; apply wit; [rewrite in_app_iff; auto|trivial|eauto].
  ++intros; apply nwit;[rewrite in_app_iff; auto|trivial|trivial].
*apply or_iff_morphism; auto.
 +apply IHfoP1; trivial.
  ++intros; apply wit; [rewrite in_app_iff; auto|trivial|eauto].
  ++intros; apply nwit;[rewrite in_app_iff; auto|trivial|trivial].
 +apply IHfoP2; trivial.
  ++intros; apply wit; [rewrite in_app_iff; auto|trivial|eauto].
  ++intros; apply nwit;[rewrite in_app_iff; auto|trivial|trivial].
*apply impl_morph; intros; auto.
 +apply IHfoP1; trivial.
  ++intros; apply wit; [rewrite in_app_iff; auto|trivial|eauto].
  ++intros; apply nwit;[rewrite in_app_iff; auto|trivial|trivial].
 +apply IHfoP2; trivial.
  ++intros; apply wit; [rewrite in_app_iff; auto|trivial|eauto].
  ++intros; apply nwit;[rewrite in_app_iff; auto|trivial|trivial].
*split; intros.
 +unfold bind in IHfoP.
  rewrite <- IHfoP with (vs:=icons x vs).
  ++apply H0; trivial.
  ++auto.
  ++intros; apply nwit;[simpl;right; auto|trivial|trivial].
  ++destruct k; simpl; auto.
 +eapply nwit with (C:=fun vs0 x0 => B x0 (fun _=>True) vs0)(x:=x)(vs:=vs); [simpl;auto|trivial|].
  intros x' ?.
  unfold bind in IHfoP.
  apply IHfoP with (vs:=icons x' vs).
  ++auto.
  ++intros; apply nwit;[simpl;right; auto|trivial|trivial].
  ++destruct k; simpl; auto.
  ++apply H0; trivial.
*split; intros.
 +destruct H0 as (x&_&Bx).
  destruct wit with (C:=fun vs0 x0 => B x0 (fun _=>True) vs0)(vs:=vs)
    as (x'&?&?); [simpl;auto|trivial|eauto|].
  exists x'; split;[trivial|].
  unfold bind in IHfoP.
  revert H1; apply IHfoP with (vs:=icons x' vs).
  ++intros; eapply wit;[simpl;right;trivial|trivial|eassumption].
  ++auto.
  ++destruct k; simpl; auto.
 +unfold bind in IHfoP.
  destruct H0 as (x&tyx&Bx).
  exists x; split;[trivial|].
  rewrite IHfoP with (vs:=icons x vs).
  ++unfold icons; simpl; auto.
  ++intros; apply wit;[simpl;right;trivial|eauto|trivial].
  ++auto.
  ++destruct k; simpl; auto.
Qed.

(*Require Import ZFcoll.*)

Require Import ZFnats ZFord ZFrank ZFwfr.

Definition rk := WFR (fun x=>x) (fun f x => osup x (fun x' => osucc (f x'))).

Instance rk_morph : morph1 rk.
intros ?? h.
apply WFR_morph; auto with *.
*intros ?? h'; trivial.  
*intros ?? h' ?? h''.
 apply osup_morph;[trivial|].
 intros ??? h'''.
 apply osucc_morph; auto.
Qed.

Lemma rk_def X : Acc in_set X -> rk X == osup X (fun x => osucc (rk x)).
intros acc; unfold rk; rewrite WFR_eqn; auto with *.
intros.
apply osup_morph;[trivial|].
intros ??? h.
apply osucc_morph; auto.
Qed.

Lemma rk_isOrd X : Acc in_set X -> isOrd (rk X).
induction 1; intros.
rewrite rk_def; [|constructor;trivial].
apply isOrd_osup; auto.
intros ??? h.
rewrite h; reflexivity.
Qed.

Lemma VN_rk_ext X : Acc in_set X -> X ⊆ VN (rk X).
intros wfX z inX.
revert z inX; induction wfX; intros.
apply Acc_intro in H.
rewrite VN_def;[|apply rk_isOrd;trivial].
exists (rk z); auto.
*rewrite rk_def with (X:=x);[|trivial].
 apply osup_intro with (x:=z); trivial.
 +intros ??? h; rewrite h; reflexivity.
 +apply lt_osucc; apply rk_isOrd.
  apply Acc_inv with x; trivial.
*red; auto.
Qed.


Definition lst_rk_prop (P : set -> Prop) (C : set) :=
  exists2 o,
    isOrd o &
    C == VN o /\
    (exists2 x, x ∈ VN o & P x) /\
    (forall x o',
     isOrd o' ->
     x ∈ VN o' -> P x -> o ⊆ o').

Parameter NNPP: forall P:Prop, ~~P->P.

Lemma EM (P : Prop) : P \/ ~ P.
Proof.
apply NNPP; intro nor; apply nor.
right; intros p.
apply nor; left; trivial.
Qed.

Lemma isOrd_ord_dec x y :
  isOrd x -> isOrd y -> x ∈ y \/ y ⊆ x.
Proof.
intros xo yo.
revert x xo; elim yo using isOrd_ind.  
intros y_ yo_ _ Hy x xo; clear y yo; rename y_ into y, yo_ into yo.
apply NNPP; intro.
apply H; right; intros z ?.
assert (exists w, in_set w x /\ ~ in_set w z).
{apply NNPP; intro.
 apply H; left.
 apply isOrd_plump with z; trivial.
 intros z' ?; apply NNPP; intro.
 apply H1; exists z'; auto. }
destruct H1 as (w & ? & ?).
assert (wo : isOrd w) by eauto using isOrd_inv.
destruct Hy with (1:=H0) (2:=wo);[contradiction|].
apply isOrd_plump with w; eauto using isOrd_inv.
Qed.

Lemma wo (P : set -> Prop) :
  (exists2 o, isOrd o & P o) ->
  exists2 o, isOrd o &
   P o /\
   (forall o', isOrd o' -> P o' -> o ⊆ o').
Proof.
intros (o, oo, Po).
revert Po; elim oo using isOrd_ind;
  intros y yo _ Hrec Po; clear o oo; rename y into o, yo into oo.
destruct (EM (exists2 z, z ∈ o & P z)) as [(z,ltz,wit)|nowit]; [eauto|].
exists o; [trivial|split;[trivial|intros]].
destruct (isOrd_ord_dec o' o); trivial.
elim nowit; exists o'; trivial.
Qed.

Lemma lst_rk_prop_uch (P : set -> Prop) (w : set) :
  P w -> ZFrepl.uchoice_pred (lst_rk_prop P).
Proof.
intros wit.
assert (wfw : Acc in_set w).
{apply wf_ax; constructor; trivial. }
assert (rko : isOrd (rk w)) by (apply rk_isOrd; trivial).
split;[|split].
*intros x x' e; apply iff_impl.
 apply ex2_morph; intros o; [reflexivity|].
 apply and_iff_morphism; [rewrite e; reflexivity|].
 reflexivity.
*assert (witVN : exists2 o, isOrd o & exists2 x, x ∈ VN o & P x).
 {exists (osucc (rk w)); [auto|].
  exists w; [|trivial].
  apply VN_incl with (VN (rk w)); auto.
  *apply VN_rk_ext; trivial.
  *apply VN_mono; auto. }
 destruct wo with (1:=witVN) as (o, oo, (Po, olst)).
 exists (VN o).
 exists o; [trivial|split;[reflexivity|split;[trivial|]]].
 eauto.
*intros x x' (o, oo, (eqx, ((y,yo,Py),olst))) (o', oo', (eqx',((y',yo',Py'),olst'))).
 rewrite eqx,eqx'; apply VN_morph.
 apply incl_eq; eauto.
Qed.

Definition lst_rk (P:set->Prop) := ZFrepl.uchoice (lst_rk_prop P).

Instance lst_rk_morph : Proper (pointwise_relation set iff==>eq_set) lst_rk.
Proof.
do 2 red; intros.
apply ZFrepl.uchoice_morph_raw.
red; intros.
apply ex2_morph; [reflexivity|intros o].
apply and_iff_morphism; [rewrite H0; reflexivity|].
apply and_iff_morphism.
*apply ex2_morph; [reflexivity|intro x1].
 apply H; reflexivity.
*apply fa_morph; intros x1.
 apply fa_morph; intros o'.
 apply fa_morph; intros _. 
 apply fa_morph; intros _. 
 apply impl_morph; [|reflexivity].
 apply H; reflexivity.
Qed.

Lemma lst_rk_def P :
    (exists x, P x) ->
    exists x, x ∈ lst_rk P /\ P x.
Proof.
intros (w,wit).
assert (wfw : Acc in_set w).
{apply wf_ax; constructor; trivial. }
destruct ZFrepl.uchoice_def with (1:=lst_rk_prop_uch P w wit)
  as (o,oo,(eq_lst_rk&(y,yo,Py)&_)).
exists y; split; [|trivial].
unfold lst_rk.
rewrite eq_lst_rk; trivial.
Qed.

Require Import ZFrelations.

  Definition set2fvs (f:set) (n:nat) : set :=
    ZFrelations.app f (nat2set n).

Lemma lt_antirefl n : n ∈ N -> ~ n < n.
Proof.
intros tyn; elim tyn using N_ind; [intros; rewrite <-H0;trivial| |].
*apply empty_ax.
*clear n tyn; intros n tyn antin.
 intro srefl; apply antin.
 apply le_case in srefl; destruct srefl as [eqs|inn].
 +apply eq_elim with (1:=eqs).
  apply succ_intro1; reflexivity.
 +apply lt_trans with (1:=tyn)(3:=inn).
  apply succ_intro1; reflexivity.
Qed.

(*subset (func N a) (fun f => forall k:nat, ZFrelations.app f*)
(*Definition lift_set2nat n f := supnat (fun k => cond_set (nat2set k == n) (f k)).

Lemma lift_set2nat_def n x f : nat2set n == x -> lift_set2nat x f == f n.
Proof.
unfold lift_set2nat.
intros eqx.
rewrite eq_set_ax; intros z.
rewrite supnat_def.
split; intros.
*destruct H as (k,?).
 rewrite cond_set_ax in H.
 destruct H.
 rewrite <-eqx in H0.
 apply nat2set_inj in H0; subst k; trivial.
*exists n. 
 rewrite cond_set_ok; auto with *.
Qed.
 *)
Require Import Lia.
Lemma set2fvs_surj n vs a :
  (forall k, vs k ∈ a) ->
  exists2 f, f ∈ func N a & (*pointwise_relation nat eq_set*)eqfvs n vs (set2fvs f).
Proof.
intros vs_typ.
induction n.
*exists (lam N (fun _ => vs 0)).
 +apply lam_is_func; auto with *.
 +intros i abs; inversion abs.
*destruct IHn as (f, tyf, eqf).
 assert (aux : ext_fun N
            (fun k => if_prop (eq_set k (nat2set n)) (vs n) (app f k))).
 {do 2 red; intros.
  rewrite H0; reflexivity. }
 exists (lam N (fun k => if_prop (eq_set k (nat2set n)) (vs n) (app f k))).
 +apply lam_is_func; [auto with *|].
  intros m tym.
  assert (dec : m == nat2set n \/ ~ m == nat2set n).
  {destruct le_total with (1:=tym) (2:=nat2set_typ n) as [ltm|[e|ltm]];
      [right|left;trivial|right]; intro eqm; rewrite eqm in ltm;
      (apply lt_antirefl in ltm; [trivial|apply nat2set_typ]). }
  destruct dec as [e|neq]; [rewrite if_left|rewrite if_right]; auto.
  apply app_typ with (1:=tyf); trivial.
 +intros i len.
  unfold set2fvs.
  rewrite beta_eq; [|auto with *|apply nat2set_typ].
  assert (cases: i = n \/ (i<n)%nat) by (inversion_clear len; auto).
  destruct cases as [e|ltn]; [subst n|]; [rewrite if_left|rewrite if_right]; auto with *.
  intros eqn; apply nat2set_inj in eqn; subst i.
  lia.
Qed.

Definition supfvs a (F:fvs -> set) :=
  sup (func N a) (fun f => F (set2fvs f)).

Lemma supfvs_def a n F z :
  Proper ((*pointwise_relation nat eq_set*)eqfvs n ==> eq_set) F ->
  z ∈ supfvs a F <-> exists2 vs:fvs, (forall k, vs k ∈ a) & z ∈ F vs.
Proof.
intros Fm.
unfold supfvs; rewrite sup_ax.
*split; intros.
 +destruct H as (f,fty,?).
  exists (set2fvs f); [|trivial].
  intros; unfold set2fvs.
  apply app_typ with N; [trivial|].
  apply nat2set_typ.
 +destruct H as (vs,?,?).
  destruct set2fvs_surj with (1:=H)(n:=n) as (f,?,?).
  exists f; trivial.
  rewrite <- H2; trivial.
*intros ??? h.
 apply Fm; red; intros.
 unfold set2fvs.
 rewrite h; reflexivity.
Qed.



Section GenReflCompl.

  Variable compl : set -> set.
  Hypothesis complm : morph1 compl.
  Hypothesis compl_ext : forall X, X ⊆ compl X.

(*  Hypothesis compl_union : forall X Y, compl X ∪ compl Y ⊆ compl (X∪Y).*)

Section Formula.

  Variable Pl:list(fvs -> set -> Prop).
  Variable n : nat.
  Hypothesis Plc :
    forall P x vs vs', In P Pl -> eqfvs n vs vs' -> P vs x <-> P vs' x.
  
  Definition rstep (M0:set) :=
    compl (List.fold_right (fun P Mi => Mi ∪ supfvs M0 (fun vs =>lst_rk (P vs))) M0 Pl).

  Instance rstep_morph : morph1 rstep.
Proof.
do 2 red; intros; unfold rstep.
apply complm.
induction Pl; simpl; [trivial|intros].
simpl in Plc.
apply union2_morph; [auto|].
apply sup_morph; [rewrite H; reflexivity|].
red; intros.
apply lst_rk_morph.
red; intros.
apply Plc with (P:=a); auto.
red; intros.
unfold set2fvs.
rewrite H1; reflexivity.
Qed.
    
  Lemma rstep_def M z :
    (z ∈ M \/
       exists2 P, In P Pl &
       exists2 vs:fvs, (forall k, vs k ∈ M) & z ∈ lst_rk (P vs)) ->
    z ∈ rstep M.
Proof.
intros; apply compl_ext.
induction Pl; simpl in *.
*destruct H as [?|(P,[ ],_)]; trivial.
*intros.
 rewrite union2_ax.
 destruct H as [inM|(P,[eqP|inPl],?)]; [auto| |eauto 10].
 subst P; right.
 rewrite supfvs_def with (n:=n); trivial.
 intros ?? h.
 apply lst_rk_morph.
 intros ?; apply Plc; auto.
Qed.

  Variable M0 : set.
  
  Definition refl_fin : set->set :=
    ZFnats.natrec M0 (fun _ Mi => rstep Mi).

  Instance refl_fin_morph : morph1 refl_fin.
Proof.
do 2 red; intros.
apply natrec_morph; [reflexivity| |trivial].
do 2 red; intros.
apply rstep_morph; trivial.
Qed.
  
  Lemma refl_fin_mono m m' z :
    m ∈ N -> m' ∈ N -> m<=m' -> z ∈ refl_fin m -> z ∈ refl_fin m'.
Proof.
intros tym tym' lem tyz.
elim lem using Nle_ind; trivial.
*do 2 red; intros.
(* apply impl_morph; [reflexivity|intros _].*)
 rewrite H; reflexivity.
*intros.
 unfold refl_fin; rewrite natrec_S;[|do 3 red; intros;apply rstep_morph; trivial|trivial].
 apply rstep_def; left; trivial.
Qed.

  Definition refl_set : set := sup N refl_fin.

  Lemma refl_set_def x :
    x ∈ refl_set <-> exists2 m, m ∈ N & x ∈ refl_fin m.
Proof.
unfold refl_set; rewrite sup_ax; auto with *.
Qed.

  Lemma refl_set_ext : M0 ⊆ refl_set.
Proof.
red; intros.
rewrite refl_set_def; exists zero; [apply zero_typ|].
unfold refl_fin; rewrite natrec_0; trivial.
Qed.

  Lemma refl_set_alt_def : refl_set == sup N (fun k => rstep (refl_fin k)).
Proof.
apply eq_set_ax; intros z.
rewrite refl_set_def, sup_ax.
*split; intros (m,tym,tyz).
 +exists m; trivial.
  apply refl_fin_mono with (m':=succ m) in tyz;
    [|trivial|apply succ_typ; trivial
    |apply succ_intro2; apply succ_intro1; reflexivity].
  unfold refl_fin in tyz; rewrite natrec_S in tyz; auto.
  do 3 red; intros; apply rstep_morph; trivial.
 +exists (succ m); [apply succ_typ; trivial|].
  unfold refl_fin; rewrite natrec_S; auto.
  do 3 red; intros; apply rstep_morph; trivial.
*do 2 red; intros. 
 rewrite H0; reflexivity.
Qed.

  Variable vs : fvs.
  Hypothesis inM : forall k, vs k ∈ refl_set.

  Lemma compacity_finite :
    exists2 m, m ∈ N & (forall k, (k <= n)%nat -> vs k ∈ refl_fin m).
Proof.
cut (forall n', (n'<=n)%nat ->
     exists2 m, m ∈ N & forall k, (k<=n')%nat -> vs k ∈ refl_fin m); [auto with arith|].
induction n'; intros.
*specialize inM with 0.
 rewrite refl_set_def in inM.
 destruct inM as (m,tym,ty0).  
 exists m; trivial.
 intros.
 assert (k=0) by lia.
 subst k; trivial.
*specialize inM with (S n').
 rewrite refl_set_def in inM.
 destruct inM as (mn,tymn,tySn').  
 destruct IHn' as (m,tym,?); auto with arith.
 exists (max m mn); [apply max_typ; trivial|intros].
 apply PeanoNat.Nat.lt_eq_cases in H1; destruct H1; [|subst k].
 +apply refl_fin_mono with m; auto with arith.
 +revert tySn'; apply refl_fin_mono; auto with arith.
Qed.

Lemma compacity_finite_ext :
  exists2 m, m ∈ N &
  exists2 vs', eqfvs n vs vs' & forall k, vs' k ∈ refl_fin m. 
destruct compacity_finite as (m,tym,?).
exists m; trivial.
exists (fun k => if le_gt_dec k n then vs k else vs 0).
*red; intros.
 destruct (le_gt_dec i n); [reflexivity|].
 elim (PeanoNat.Nat.lt_irrefl n).
 apply PeanoNat.Nat.lt_trans with i; trivial.
*intros.
 destruct (le_gt_dec k n); auto with arith.
Qed.

  Lemma refl_set_model P :
    In P Pl ->
    (exists x, P vs x) -> exists x', x' ∈ refl_set /\ P vs x'.
intros inPl wit.
destruct compacity_finite_ext as (m,tym,(vs',evs,?)).
assert (ex' : exists x, P vs' x).
{destruct wit as (x,?); exists x.
 rewrite <- Plc with (1:=inPl) (2:=evs); trivial. }
destruct lst_rk_def with (1:=ex')as (x'&?&?).
exists x'; split; [|rewrite Plc with (1:=inPl)(2:=evs); trivial].
apply refl_set_def; exists (succ m); [apply succ_typ; trivial|simpl].
unfold refl_fin; rewrite natrec_S; auto.
2:do 3 red; intros; apply rstep_morph; trivial.
apply rstep_def; right.
exists P; trivial.
exists vs'; auto.
Qed.

End Formula.


  Lemma refl_wit_compact P Q nQ :
    fo_wit P Q nQ ->
    let Q' := Q++List.map(fun nA vs x => ~nA vs x)nQ in
    exists n,
    forall A x vs vs',
      In A Q' -> eqfvs n vs vs' -> A vs x <-> A vs' x.
intros fwP Q'.
destruct compacity_wit with (1:=fwP) as (n,(compactQ,compactnQ)).
exists n; unfold Q'; intros.
apply in_app_iff in H; destruct H; [auto|]. 
apply in_map_iff in H.
destruct H as (A',(eqA,?)); subst A.
apply impl_morph;[|reflexivity].
apply compactnQ; trivial.
Qed.
  
  Lemma reflection_principle_wit M0 P Q nQ :
    fo_wit P Q nQ ->
    let Q' := Q++List.map(fun nA vs x => ~nA vs x)nQ in
    reflect (refl_set Q' M0) P.
intros fwP Q'.
destruct refl_wit_compact with (1:=fwP) as (n,compactQ').
apply reflect_conditions with (1:=fwP); intros.
*apply refl_set_model with (n:=n); auto.
 apply in_app_iff; auto.
*apply NNPP; intros nC.
 destruct refl_set_model with (n:=n)(P:=fun vs x=>~C vs x)(2:=H0) as (x',(?,?));
   [auto| |eauto|auto].
 apply in_app_iff; right.
 apply in_map with (1:=H)(f:=fun nA vs x=>~nA vs x).
Qed.

         
End GenReflCompl.


Section GenReflComplSequence.

  Hypothesis
    (compl : set -> set)
    (complmono : Proper (incl_set ==> incl_set) compl)
    (compl_ext : forall X, X ⊆ compl X).

  Let complm : Proper (eq_set ==> eq_set) compl :=
    Fmono_morph compl complmono.

  Hypothesis
    (K : set -> Prop)
    (Km : Proper (eq_set ==> iff) K)
    (Kcompl : forall X, K (compl X))
    (Ksup : forall f : set -> set,
          ext_fun N f ->
          (forall k, k ∈ N -> K (f k)) ->
          (forall k, k ∈ N -> f k ⊆ f (succ k)) ->
          K (sup N f)).

Section WithFoWit.
    
  Hypothesis
    (P : (set->Prop)->fvs->Prop)
    (Q nQ : list (fvs -> set -> Prop))
    (fwP : fo_wit P Q nQ).

  Let Q' := Q ++ map (fun (nA : fvs -> set -> Prop) vs x => ~ nA vs x) nQ.

  Definition refl_step := refl_set compl Q'.

  Lemma fold_right_incl : forall A f f' a a' (l:list A),
      a ⊆ a' ->
      (forall x b b', In x l -> b ⊆ b' -> f x b ⊆ f' x b') ->
      fold_right f a l ⊆ fold_right f' a' l.
induction l; simpl; intros; auto.
Qed.
  
  Lemma Krefl_step M0 : M0 ⊆ refl_step M0 /\ K (refl_step M0).
Proof.
destruct refl_wit_compact with (1:=fwP) as (n, compactQ').
fold Q' in compactQ'.
split.
*apply refl_set_ext with (n:=n); trivial.
*unfold refl_step.
 rewrite refl_set_alt_def with (n:=n); auto.
 apply Ksup; intros.
 +do 2 red; intros.
  apply rstep_morph with (n:=n); auto with *.
  apply refl_fin_morph with (n:=n); auto with *.
 +apply Kcompl.
 +apply complmono.
  apply fold_right_incl; intros.
  {intro z; apply refl_fin_mono with (n:=n); auto.
   +apply succ_typ; trivial.
   +apply succ_intro2; apply succ_intro1; reflexivity. }
  {apply union2_mono; [auto|].
   intros z; rewrite !supfvs_def with (n:=n).
   +intros (vs,rfl,tyz).
    exists vs; trivial.
    intros.
    generalize (rfl k0).
    apply refl_fin_mono with (n:=n); auto.
    ++apply succ_typ; trivial.
    ++apply succ_intro2; apply succ_intro1; reflexivity.
   +do 2 red; intros.
    apply lst_rk_morph.
    intros z'; apply compactQ'; trivial.
   +do 2 red; intros.
    apply lst_rk_morph.
    intros z'; apply compactQ'; trivial. }
Qed.

  Definition refl_N_seq M0 k :=
    natrec M0 (fun _ M => refl_step (singl M)) k.

  Instance refl_step_morph : morph1 refl_step.
do 2 red; intros.
apply sup_morph; [reflexivity|].
red; intros.
unfold refl_fin.
apply natrec_morph; [rewrite H;reflexivity| |trivial].
do 2 red; intros.
destruct refl_wit_compact with (1:=fwP) as (n, compactQ').
eapply rstep_morph with (n:=n); trivial.
Qed.
  
  Instance refl_N_seq_morph : morph2 refl_N_seq.
Proof.
do 3 red; intros.
apply natrec_morph; trivial.
do 2 red; intros.
rewrite H2; reflexivity.
Qed.

  Lemma refl_N_seq_0 M0 : refl_N_seq M0 zero == M0.
Proof.
unfold refl_N_seq.
apply natrec_0.  
Qed.

  Lemma refl_N_seq_S M0 k :
    k ∈ N ->
    refl_N_seq M0 k ∈ refl_N_seq M0 (succ k).
intros tyk.
unfold refl_N_seq.
rewrite natrec_S; auto with *.
*apply Krefl_step.
 apply singl_intro. 
*do 3 red; intros.
 rewrite H0; reflexivity.
Qed.

  Lemma Krefl_N_seq M0 k :
    k ∈ N -> K (refl_N_seq M0 (succ k)).
intros tyk.
unfold refl_N_seq.
rewrite natrec_S; auto with *.
2:intros ??? ?? h; rewrite h; reflexivity.
apply Krefl_step.
Qed.

  
  Lemma refl_N_seq_refl M0 k :
    k ∈ N ->
    reflect (refl_N_seq M0 (succ k)) P.
intros tyk.
destruct refl_wit_compact with (1:=fwP) as (n, compactQ').
unfold refl_N_seq.
eapply (fun h => reflect_morph _ _ h P P).
*apply natrec_S;[|trivial].
 intros ??? ?? h; rewrite h; reflexivity.
*apply fo_wit_form in fwP.
 apply fo_form_param in fwP.
 do 2 red; intros.
 apply fwP; trivial.
 reflexivity.
*apply reflection_principle_wit; auto.
Qed.
  
End WithFoWit.

  Lemma reflection_principle_gen P M0 :
    fo_form P ->
    exists2 M, M0⊆M /\ K M & reflect M P.
intros foP.
destruct fo_form_ex_wit with (1:=foP) as (Q&nQ&fwP).
destruct refl_wit_compact with (1:=fwP) as (n,compactQ').
exists (refl_set compl (Q++List.map(fun nA vs x => ~nA vs x)nQ) M0);[split;intros|].
*apply refl_set_ext with (n:=n); auto with *.
*set (Q':=Q++ map (fun nA vs x0 => ~ nA vs x0) nQ) in *.
 apply Krefl_step with (1:=fwP).
*apply reflection_principle_wit with (3:=fwP); auto.
Qed.

  Lemma reflection_principle_sequence P M0 :
    fo_form P ->
    exists F : set -> set,
      Proper (eq_set ==> eq_set) F /\
      M0 ∈ F zero /\
      (forall k, k ∈ N -> F k ∈ F (succ k)) /\
      (forall k, k ∈ N -> K (F k)) /\
      (forall k, k ∈ N -> reflect (F k) P).
intros foP.
destruct fo_form_ex_wit with (1:=foP) as (Q&nQ&fwP).
destruct refl_wit_compact with (1:=fwP) as (n,compactQ').
exists (fun k => refl_N_seq Q nQ M0 (succ k)). 
split;[|split;[|split;[|split]]]; intros.
*do 2 red; intros.
 apply refl_N_seq_morph with (1:=fwP); [reflexivity|].
 rewrite H; reflexivity.
*apply in_reg with (1:=refl_N_seq_0 Q nQ M0).
 apply refl_N_seq_S with (1:=fwP).
 apply zero_typ.
*apply refl_N_seq_S with (1:=fwP).
 apply succ_typ; trivial.
*apply Krefl_N_seq with (1:=fwP); trivial.
*apply refl_N_seq_refl with (1:=fwP); trivial.
Qed.

End GenReflComplSequence.

  Lemma reflection_principle M0 P :
    fo_form P ->
    exists2 M, M0⊆M & reflect M P.
intros foP.
destruct fo_form_ex_wit with (1:=foP) as (Q&nQ&fwP).
destruct refl_wit_compact with (1:=fwP) as (n,compactQ').
exists (refl_set (fun x=>x) (Q++List.map(fun nA vs x => ~nA vs x)nQ) M0).
*apply refl_set_ext with (n:=n); auto with *.
*apply reflection_principle_wit with (3:=fwP); auto with *.
Qed.

(* Transitive sets *)
Import ZFwf.FirstOrder.

Lemma wfax x : Acc in_set x.
apply wf_ax; intros; constructor; auto.
Qed.
Hint Resolve wfax : core.

Definition trans (K : set -> Prop) := forall x y, K x -> in_set y x -> K y.

Instance trans_morph : Proper (pointwise_relation set iff ==> iff) trans.
do 2 red; intros.
unfold trans.
apply fa_morph; intros x0.
apply fa_morph; intros y0.
apply impl_morph; [trivial|intros].
apply fa_morph; intros; auto.
Qed.

Definition plump (K : set -> Prop) := forall x y, K x -> y ⊆ x -> K y.

Instance plump_morph : Proper (pointwise_relation set iff ==> iff) plump.
do 2 red; intros.
unfold plump.
apply fa_morph; intros x0.
apply fa_morph; intros y0.
apply impl_morph; [trivial|intros].
apply fa_morph; intros; auto.
Qed.


Lemma trClos_ext X : X ⊆ trClos X.
red; intros.
apply trClos_intro2 with X; auto. 
Qed.
Hint Resolve trClos_ext : core.

  Lemma reflection_principle_trans M0 P :
    fo_form P ->
    exists2 M, M0⊆M /\ (forall x y, x ∈ M -> y ∈ x -> y ∈ M) & reflect M P.
intros foP.
apply reflection_principle_gen with
  (compl:=fun x => sup x trClos)(K:=fun M => trans (fun x=>x ∈ M)); auto with *.
*intros x x' inclx z.
 rewrite !sup_ax; auto with *.
 intros (y,?,?); exists y; auto. 
*intros X z tyz.
 rewrite sup_ax; auto with *.
 exists z; trivial.
 apply trClos_intro1; trivial.
*do 2 red; intros.
 apply trans_morph; intros z.
 rewrite H; reflexivity.
*red; intros.
 rewrite sup_ax in H|-*; auto with *.
 destruct H as (y',?,?).
 exists y'; trivial.
 apply trClos_intro2 with x; trivial.
*intros f extf trf fmono; red; intros.
 rewrite sup_ax in H|-*; auto with *.
 destruct H as (n,tyn,?).
 exists n; trivial.
 red in trf.
 apply trf with (x:=x); auto.
Qed.

Require Import ZFord.

Lemma VN_def x : VN x == sup x (fun y => power (VN y)).
apply WFR_eqn; [auto with *| |trivial].
intros.
clear H.
apply sup_morph; trivial.
red; intros.
apply power_morph; auto.
Qed.

(*Existing Instance VN_morph : morph1 VN.*)

Lemma VN_in_def x z : z ∈ VN x <-> exists2 y, y ∈ x & z ⊆  VN y.
rewrite VN_def, sup_ax; [|intros ??? h; rewrite h; reflexivity].
apply ex2_morph; [reflexivity|intro y].
rewrite power_ax; reflexivity.
Qed.

Instance VN_mono : Proper (incl_set ==> incl_set) VN.
do 2 red; intros.
intros z.
rewrite !VN_def.
assert (morph1 (fun y => power (VN y))) by (intros ?? h; rewrite h; reflexivity).
rewrite !sup_ax; auto.
intros(w,?,?); exists w; auto.
Qed.

Lemma VN_ext x : x ⊆ VN x.
pattern x; apply wf_ax; clear x; red; intros.
apply VN_in_def.
exists z; auto.
Qed.

Lemma VN_plump x : plump (fun y => y ∈ VN x).
red; intros.
rewrite VN_in_def in H|-*.
destruct H as (w,?,?).
exists w; auto.
transitivity x0; trivial.
Qed.

Lemma VN_trans' x : trans (fun y => y ∈ VN x).
red; pattern x; apply wf_ax; clear x; intros.
rewrite VN_in_def in H0|-*.
destruct H0 as (w,?,?).
exists w; trivial.
red; intros.
apply H with y; auto.
Qed.

Local Lemma auxm : forall a, ext_fun a (fun x0 => osucc (rk x0)).
intros ???? h; rewrite h; reflexivity.
Qed.
Hint Resolve auxm : core.

Instance rk_mono : Proper (incl_set ==> incl_set) rk.
do 2 red; intros.
rewrite !rk_def; trivial.
apply osup_lub; intros; auto.
*apply isOrd_osup; auto.
 intros; apply isOrd_succ.
 apply rk_isOrd; trivial.
*red; intros; apply osup_intro with x0; auto.
Qed. 

Lemma next_limOrd_mono o o' :
  isOrd o -> isOrd o' -> o ⊆ o' -> next_limOrd o ⊆ next_limOrd o'.
intros.
apply next_limOrd_lub; [trivial|apply limOrd_next_limOrd; trivial|].
apply isOrd_plump with o'; trivial;[apply limOrd_next_limOrd; trivial|].
apply next_limOrd_intro1; trivial.
Qed.

Lemma rk_VN o : isOrd o -> rk (VN o) == o.
intros oo; elim oo using isOrd_ind; intros.
clear H0 o oo.  
rewrite rk_def; auto.
apply incl_eq.
*apply osup_lub; intros; auto.
 rewrite VN_in_def in H0.
 destruct H0 as (z,?,?).
 transitivity (osucc (rk (VN z))).
 +apply osucc_mono; auto using rk_isOrd.
  apply rk_mono; auto.
 +rewrite H1; trivial.
  red; intros.
  apply isOrd_plump with z; auto.
   apply isOrd_inv with (osucc z); auto.
   apply isOrd_succ; auto.
   apply isOrd_inv with y; trivial.
   apply olts_le; trivial.
*red; intros.
 assert (isOrd z) by eauto using isOrd_inv.
 apply osup_intro with (VN z); auto.
 +apply VN_compl; auto.
  apply VN_ext; trivial.
 +rewrite H1; trivial.
  apply lt_osucc; auto.
Qed. 

Lemma rk_strict_mono x y : x ∈ y -> rk x ∈ rk y.
rewrite (rk_def y); [|trivial].
intros; apply osup_intro with x; auto.
apply lt_osucc.
apply rk_isOrd; trivial.
Qed.

Lemma VN_ord_incl o o' : isOrd o -> isOrd o' -> o' ∈  VN o -> o' ∈ o.
intros oo oo' invn.
revert o' oo' invn; elim oo using isOrd_ind; intros.
clear o oo H0.
apply VN_in_def in invn.
destruct invn as (o,?,?).
apply isOrd_plump with o; auto.
red; intros.
apply H1; eauto using isOrd_inv.
Qed.

Instance limitOrd_morph : Proper (eq_set ==> iff) limitOrd.
do 2 red; intros.
apply and_iff_morphism; [rewrite H; reflexivity|].
apply fa_morph; intros x'.
rewrite H; reflexivity.
Qed.

Lemma N_ind' (P : set -> Prop) :
  (forall k, k == zero -> P k) ->
  (forall n k, n ∈ N -> P n -> k == succ n -> P k) ->
  forall n, n ∈ N -> P n.
intros.
assert (n ∈ subset N (fun k => forall k', k'==k -> P k')).
{apply subset_elim2 in H1.
 destruct H1 as (n',?,?).
 rewrite H1; clear n H1.
 apply H2; intros.
 *apply subset_intro; [apply zero_typ|trivial].
 *apply subset_ax in H1.
  destruct H1 as (tyk, (k', ?,?)).
  apply subset_intro; [apply succ_typ; trivial|].
intros; apply H0 with k; auto. }
apply subset_elim2 in H2.
destruct H2 as (n',?,?).
auto.
Qed.

Lemma Nle_ind' m (P : set -> Prop) :
  (forall m', m == m' -> P m') ->
  (forall n sn', n ∈ N -> P n -> succ n == sn' -> P sn') ->
  forall n, m ∈ N -> n ∈ N -> le m n -> P n.
intros Hm HS n tym tyn Hle.
revert m tym Hm Hle; elim tyn using N_ind'; intros.
*revert Hm Hle; elim tym using N_ind'; intros.
 +apply Hm. 
  rewrite H; trivial.
 +rewrite H in Hle.
  apply le_case in Hle.
  destruct Hle as [abs|abs];[|apply empty_ax in abs;contradiction].  
  rewrite H2 in abs; apply discr in abs; contradiction.
*apply le_case in Hle; destruct Hle; [auto|].
 apply HS with n0; auto with *.
 rewrite H1 in H2.
 apply H0 with m; auto.
Qed.

Definition isVNlim X := exists o, limitOrd o /\ X == VN o.
 
Instance isVNlim_morph : Proper (eq_set ==> iff) isVNlim.
unfold isVNlim.
do 2 red; intros.
apply ex_morph; intros o.
apply and_iff_morphism; [reflexivity|].
rewrite H; reflexivity.
Qed.

Definition VNlim_compl X := VN (next_limOrd (rk X)).

Instance VNlim_compl_mono : Proper (incl_set ==> incl_set) VNlim_compl.
do 2 red; intros.
apply VN_mono.
apply next_limOrd_mono; auto using rk_isOrd.
apply rk_mono; trivial.
Qed.


Lemma VNlim_ext X : X ⊆ VNlim_compl X.
red; intros.
unfold VNlim_compl.
assert (isOrd (rk X)) by (auto using rk_isOrd).
apply VN_mono with (rk X).
*red; intros.
 apply isOrd_trans with (rk X); auto.
 apply limOrd_next_limOrd; auto.
 apply next_limOrd_intro1; trivial.
*apply VN_rk_ext; trivial.
Qed.

Lemma VNlim_compl_ok X : isVNlim (VNlim_compl X).
exists (next_limOrd (rk X)); split;[|reflexivity].
apply limOrd_next_limOrd; auto.
apply rk_isOrd; trivial.
Qed.

Lemma VNlim_sup (f : set -> set) :
  ext_fun N f ->
  (forall k, k ∈ N -> isVNlim (f k)) ->
  (forall k, k ∈ N -> f k ⊆ f (succ k)) ->
  isVNlim (sup N f).
intros fext Kf fmono.
pose (frk := fun k => subset (f k) isOrd).
assert (frkext : ext_fun N frk).
{do 2 red; intros.
 apply subset_morph; [auto|].
 red; reflexivity. }
assert (Kf' : forall k, k ∈ N -> limitOrd (frk k) /\ f k == VN (frk k)).
{intros k tyk.
 destruct Kf with (1:=tyk) as (o & lo & eqf).
 assert (frk k == o).
 {apply eq_set_ax; split; intros.
  *apply subset_ax in H.
   destruct H as (?,(x',eqx, xo)).
   rewrite <- eqx in xo.
   eapply VN_ord_incl; [apply lo|trivial|].
   rewrite <- eqf; trivial.
  *apply subset_intro;[|eauto using isOrd_inv].
   rewrite eqf.
   apply VN_ext; trivial. }
 rewrite H; auto. }
assert (limfo : forall k, k ∈ N -> limitOrd (frk k)).
{intros; apply Kf'; trivial. }
assert (feq : forall k, k ∈ N -> f k == VN (frk k)).
{intros; apply Kf'; trivial. }
assert (lims : limitOrd (sup N frk)).
{split.
 {apply isOrd_supf; intros; trivial.
 *apply limfo; trivial.
 *exists (max x y); [apply max_typ; trivial|].
  assert (fmono_le : forall x y, x ∈ N -> y ∈ N -> x <= y -> f x ⊆ f y).
  {intros.
   elim H3 using Nle_ind'; trivial; intros.
   *rewrite (fext x0 m'); trivial.
    reflexivity.
   *rewrite <- (fext (succ n) sn'); trivial;[|apply succ_typ; trivial].
    rewrite <- fmono; trivial. } 
  split; red; intros.
  +apply subset_ax in H1.
   destruct H1 as (?,(z',?,?)).
   rewrite <- H2 in H3.
   apply subset_intro;[|trivial].
   revert H1; apply fmono_le; auto.
  +apply subset_ax in H1.
   destruct H1 as (?,(z',?,?)).
   rewrite <- H2 in H3.
   apply subset_intro;[|trivial].
   revert H1; apply fmono_le; auto. }
 {intros.
  rewrite sup_ax in H|-*; trivial.
  destruct H as (k,?,?).
  exists k; trivial.
  apply limfo; trivial. }}
exists (sup N frk); split; [trivial|].
apply eq_set_ax; intros x.
rewrite sup_ax; [|trivial].
split; intros.
*destruct H as (k,?,?).
 apply VN_mono_le with (frk k); auto.
 rewrite <- feq; auto.
*rewrite VN_in_def in H.
 destruct H as (y,?,?).
 rewrite sup_ax in H; [|trivial].
 destruct H as (k,?,?).
 exists k; trivial.
 rewrite feq; auto.
 apply VN_incl with (VN y); auto.
 apply ZFrank.VN_mono; auto.
Qed.
