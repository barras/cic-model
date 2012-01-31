
Require Export Lambda.
Hint Unfold iff: core.

(* Girard's reducibility candidates: up to system F *)

  Definition CR := term -> Prop.

  (* Weak candidates *)
  Record weak_cand (X : CR) : Prop := 
    {wk_sn  : forall t, X t -> sn t;
     wk_red : forall t u, X t -> red t u -> X u;
     wk_wit : exists w, X w}.

  Definition weak_chain t : CR := fun u => red t u.

Lemma weakest_cands :
  forall t, sn t -> weak_cand (weak_chain t).
unfold weak_chain.
split; intros.
 eauto using sn_red_sn.

 transitivity t0; trivial.

 eauto using refl_red.
Qed.


  (* The exact definition of is_cand is not used outside this module. *)
  Record is_cand (X : CR) : Prop := 
    {incl_sn : forall t, X t -> sn t;
     clos_red : forall t u, X t -> red t u -> X u;
     clos_exp : forall t, neutral t -> (forall u, red1 t u -> X u) -> X t}. 

  Instance is_cand_morph : Proper (pointwise_relation _ iff ==> iff) is_cand.
Proof.
do 2 red; intros.
split; destruct 1; split; intros.
 rewrite <- H in H0; auto.

 rewrite <- H in H0 |-*; eauto.

 rewrite <- H; apply clos_exp0; intros; trivial.
 rewrite H; auto.

 rewrite H in H0; auto.

 rewrite H in H0 |-*; eauto.

 rewrite H; apply clos_exp0; intros; trivial.
 rewrite <- H; auto.
Qed.


  Lemma cand_sn : is_cand sn.
constructor; intros; auto with coc.

apply sn_red_sn with t; auto with coc.

red in |- *; apply Acc_intro; auto with coc.
Qed.

  Hint Resolve  incl_sn cand_sn: coc.

  Lemma var_in_cand : forall n X, is_cand X -> X (Ref n).
intros.
apply (clos_exp X); auto with coc.
 exact I.

 intros.
 inversion H0.
Qed.

  Lemma weaker_cand : forall X, is_cand X -> weak_cand X.
intros.
case H; split; trivial.
exists (Ref 0).
apply (var_in_cand _ X); trivial.
Qed.

  Lemma sat1_in_cand : forall n X u,
    is_cand X -> sn u -> X (App (Ref n) u).
induction 2; intros.
apply (clos_exp X); trivial.
 exact I.
intros.
inversion_clear H2; auto.
inversion H3.
Qed.

  Lemma cand_sat :
   forall X, is_cand X ->
   forall u, sn u ->
   forall m, X (subst u m) ->
   X (App (Abs m) u).
Proof.
(* induction on (sn u) *)
simple induction 2.
clear u H0; intros u _ IHu; unfold transp in *.
(* induction on (sn m) *)
intros m m_in_X.
generalize m_in_X.
cut (sn m). 
2: apply sn_subst with u; apply (incl_sn _ H); trivial.
simple induction 1.
clear m m_in_X H0; intros m _ IHm m_in_X; unfold transp in *.
(* by case on the reduction *)
apply (clos_exp _ H). exact I.
intros x red_redex.
inversion_clear red_redex; [idtac|inversion_clear H0|idtac].
(* head-reduction *)
trivial.
(* reduction in body *)
apply IHm; trivial.
apply clos_red with (subst u m); trivial.
unfold subst; auto with coc.
(* reduction in arg *)
apply IHu; auto with coc.
apply clos_red with (subst u m); trivial.
unfold subst; auto with coc.
Qed.


  (* equality on CR *)

  Definition eq_cand (X Y:CR) := forall t : term, X t <-> Y t.

  Hint Unfold eq_cand: coc.

  Lemma eq_cand_incl : forall t X Y, eq_cand X Y -> X t -> Y t.
Proof.
intros.
elim H with t; auto with coc.
Qed.

(* Completion: work in progress *)

Section Completion.

  Variable P : term -> Prop.

  Definition compl : CR :=
    fun t => forall C, is_cand C -> (forall u, sn u -> P u -> C u) -> C t.

  Lemma is_can_compl : is_cand compl.
split.
 intros.
 apply (H sn); auto.
 apply cand_sn.

 red; intros.
 apply (clos_red C) with t; auto.
 apply (H C); trivial.

 red; intros.
 apply (clos_exp C); trivial; intros.
 apply H0; trivial.
Qed.

  Lemma compl_intro : forall t, sn t -> P t -> compl t.
red; intros; auto.
Qed.

  Lemma compl_elim : forall t,
    compl t ->
    (exists2 u, conv t u & compl u /\ P u) \/
    (forall C, is_cand C -> C t).
intros.
apply (@proj2 (sn t)).
apply H; intros.
 split; intros.
  destruct H0; trivial.

  destruct H0.
  split.
   apply sn_red_sn with t0; trivial.

   destruct H2.
    left.
    destruct H2.
    exists x; trivial.
    apply trans_conv_conv with t0; auto.
    apply red_sym_conv; trivial.

    right; intros.
    apply (clos_red C) with t0; trivial.
    apply (H2 C); trivial.

  split.
   constructor; intros.
   destruct (H1 y); auto.

   assert ((exists u, red1 t0 u) \/ normal t0).
    admit.
   destruct H2.
    destruct H2.
    destruct (H1 x); auto.
    destruct H4.
     left.
     destruct H4.
     exists x0; trivial.
     apply trans_conv_conv with x; trivial.
     apply red_conv; auto with coc.

     right; intros.
     admit. (*?*)

    right; intros.
    apply (clos_exp C); trivial; intros.
    elim H2 with u; trivial.

 split; trivial.
 left.
 exists u.
  constructor.

  split; trivial.
  red; auto.
Qed.


End Completion.

  Lemma eq_can_compl : forall X Y,
    eq_cand X Y -> eq_cand (compl X) (compl Y).
unfold eq_cand; simpl; split; intros.
 red; intros.
 apply (H0 C); trivial; intros.
 rewrite H in H4; auto.

 red; intros.
 apply (H0 C); trivial; intros.
 rewrite <- H in H4; auto.
Qed.

(* Intersection of candidates *)

  Definition Inter (X:Type) (F:X->CR) t :=
    sn t /\ forall x, F x t.

  Lemma eq_can_Inter :
    forall X Y (F:X->term->Prop) (G:Y->term->Prop),
    (forall x, exists y, eq_cand (F x) (G y)) /\
    (forall y, exists x, eq_cand (F x) (G y)) ->
    eq_cand (Inter _ F) (Inter _ G).
unfold eq_cand, Inter; intros.
destruct H.
split; intros.
 destruct H1; split; trivial; intros.
 destruct (H0 x).
 rewrite <- H3; trivial.

 destruct H1; split; trivial; intros.
 destruct (H x).
 rewrite H3; trivial.
Qed.

  Lemma is_can_Inter :
    forall X F, (forall x:X, is_cand (F x)) -> is_cand (Inter X F).
unfold Inter; intros.
constructor.
 destruct 1; trivial.

 intros.
 destruct H0.
 split; intros.
  apply sn_red_sn with t; trivial.

  apply (clos_red _ (H x)) with t; auto.

 split; intros.
  constructor; intros.
  destruct (H1 y); trivial.

  apply (clos_exp _ (H x)); intros; trivial.
  destruct (H1 u); trivial.
Qed.  

  Lemma is_can_Inter' :
    forall X F, (forall x:X, is_cand (fun t => sn t /\ F x t)) -> is_cand (Inter X F).
unfold Inter; intros.
constructor.
 destruct 1; trivial.

 intros.
 destruct H0.
 split; intros.
  apply sn_red_sn with t; trivial.

  apply (clos_red _ (H x)) with t; auto.

 split; intros.
  constructor; intros.
  destruct (H1 y); trivial.

  apply (clos_exp _ (H x)); intros; trivial.
  destruct (H1 u); auto.
Qed.  

  Lemma is_can_weak : forall X,
    is_cand X -> is_cand (fun t => sn t /\ X t).
intros.
generalize H.
apply is_cand_morph; red; intros.
split; intros.
 apply H0.

 split; trivial.
 apply (incl_sn X); trivial.
Qed.

  Definition InterSubset (X:Type) (P:X->Prop) (f:X->CR) :=
    Inter {x|P x} (fun x => f (proj1_sig x)).

  Definition Neutral := InterSubset _ is_cand (fun C => C).

  Lemma is_cand_neutral : is_cand Neutral.
Admitted.


(* Explicit definition of the CR of neutral terms *)
  Definition Neu : CR := fun t =>
    sn t /\ exists2 u, red t u & nf u /\ neutral u.

Lemma neutral_is_cand : is_cand Neu.
split; intros.
 destruct H; trivial.

 destruct H.
 destruct H1.
 split.
  apply sn_red_sn with t; auto with coc.

  exists x; trivial.
  destruct H2.
  elim confluence with (1:=H1) (2:=H0); intros.
  replace x with x0; trivial.
  revert H2; elim H4; trivial; intros.
  rewrite H6 in H7; trivial.
  elim nf_norm with (2:=H7); trivial.

 assert (sn t).
  constructor; intros.
  destruct (H0 y); auto.
 split; trivial.
 destruct (red1_dec t).
  destruct s.
  specialize H0 with (1:=r).
  destruct H0.
  destruct H2.
  exists x0; trivial.
  transitivity x; auto with coc.

  exists t; auto with *.
Qed.

(* Interpreting non dependent products *)

  Definition Arr (X Y:CR) : CR :=
    fun t => forall u, X u -> Y (App t u).

  Lemma eq_can_Arr :
   forall X1 Y1 X2 Y2,
   eq_cand X1 X2 -> eq_cand Y1 Y2 -> eq_cand (Arr X1 Y1) (Arr X2 Y2).
unfold eq_cand, Arr; split; intros.
 rewrite <- H0; rewrite <- H in H2; auto.
 rewrite H0; rewrite H in H2; auto.
Qed.

  Lemma weak_cand_Arr : forall (X Y:CR),
    weak_cand X ->
    is_cand Y ->
    is_cand (Arr X Y).
unfold Arr in |- *; intros X Y Hne Y_cand.
constructor.
 intros t app_in_can.
 destruct (wk_wit _ Hne) as (w,?).
 apply subterm_sn with (App t w); auto with coc.
 apply (incl_sn Y); auto with coc.

 intros.
 apply (clos_red Y) with (App t u0); auto with coc.

 intros t t_neutr clos_exp_t u u_in_X.
 apply (clos_exp Y); auto with coc.
  exact I.

  generalize u_in_X.
  assert (u_sn: sn u).
   apply (wk_sn X); auto with coc.
  clear u_in_X.
  elim u_sn.
  intros v _ v_Hrec v_in_X w red_w.
  revert t_neutr.
  inversion_clear red_w; intros; auto with coc.
   destruct t_neutr.

   apply (clos_exp Y); intros; auto with coc.
    exact I.

    apply v_Hrec with N2; auto with coc.
    apply (wk_red X) with v; auto with coc.
Qed.

  Lemma weak_Abs_sound_Arr :
   forall (X Y:CR) m,
   (forall t, X t -> sn t) ->
   is_cand Y ->
   (forall n, X n -> Y (subst n m)) ->
   Arr X Y (Abs m).
unfold Arr in |- *; intros.
apply (clos_exp Y); intros; auto with coc.
 exact I.

 apply clos_red with (App (Abs m) u); auto with coc.
 apply (cand_sat Y); auto with coc.
Qed.


  Lemma is_cand_Arr :
   forall X Y, is_cand X -> is_cand Y -> is_cand (Arr X Y).
intros.
apply weak_cand_Arr; trivial.
apply weaker_cand; trivial.
Qed.

  Lemma Abs_sound_Arr :
   forall X Y m,
   is_cand X ->
   is_cand Y ->
   (forall n, X n -> Y (subst n m)) ->
   Arr X Y (Abs m).
unfold Arr in |- *; intros.
apply (clos_exp Y); intros; auto with coc.
 exact I.

 apply clos_red with (App (Abs m) u); auto with coc.
 apply (cand_sat Y); auto with coc.
 apply (incl_sn X); auto with coc.
Qed.


(* Interpreting non dependent products *)

  Definition Pi (X:CR) (Y:term->CR) : CR :=
    fun t => forall u u', conv u' u -> X u -> X u' -> Y u' (App t u).

  Lemma eq_can_Pi :
   forall X1 X2 (Y1 Y2:term->CR),
   eq_cand X1 X2 ->
   (forall u, eq_cand (Y1 u) (Y2 u)) ->
   eq_cand (Pi X1 Y1) (Pi X2 Y2).
unfold eq_cand, Pi; split; intros.
 rewrite <- H0; rewrite <- H in H3,H4; auto.
 rewrite H0; rewrite H in H3,H4; auto.
Qed.

  Lemma is_cand_Pi : forall X (Y:term->CR),
   is_cand X ->
   (forall u, is_cand (Y u)) ->
   is_cand (Pi X Y).
unfold Pi in |- *; intros X Y X_can Y_can.
constructor.
 intros t app_in_can.
 apply subterm_sn with (App t (Ref 0)); auto with coc.
 apply (incl_sn (Y (Ref 0))); auto with coc.
 apply app_in_can; auto with coc.
  apply var_in_cand with (X:=X); auto with coc.
  apply var_in_cand with (X:=X); auto with coc.

 intros.
 apply (clos_red (Y u')) with (App t u0); auto with coc.

 intros t t_neutr clos_exp_t u u' redu u_in_X u'_in_X.
 apply (clos_exp (Y u')); auto with coc.
  exact I.

  assert (u_sn: sn u).
   apply (incl_sn X); auto with coc.
  revert u' redu u_in_X u'_in_X.
  elim u_sn.
  intros v _ v_Hrec u' redu v_in_X u'_in_X w red_w.
  revert t_neutr.
  inversion_clear red_w; intros; auto with coc.
   destruct t_neutr.

   apply (clos_exp (Y u')); intros; auto with coc.
    exact I.

    apply v_Hrec with N2; eauto with coc.
    apply (clos_red X) with v; auto with coc.
Qed.

  Lemma Abs_sound_Pi :
   forall X Y m,
   is_cand X ->
   (forall u, is_cand (Y u)) ->
   (forall n n', X n -> X n' -> conv n' n -> Y n' (subst n m)) ->
   Pi X Y (Abs m).
unfold Pi in |- *; intros.
apply (clos_exp (Y u')); intros; auto with coc.
 exact I.

 apply clos_red with (App (Abs m) u); auto with coc.
 apply (cand_sat (Y u')); auto with coc.
 apply (incl_sn X); auto with coc.
Qed.


  (* Union of 2 candidates of reducibility *)

  Definition Union (X Y:CR) : CR := compl (fun t => X t \/ Y t).

  Lemma eq_can_union : forall X Y X' Y',
    eq_cand X X' -> eq_cand Y Y' ->
    eq_cand (Union X Y) (Union X' Y').
unfold Union; intros.
apply eq_can_compl.
red; intros.
red in H, H0.
rewrite H; rewrite H0; reflexivity.
Qed.

  Lemma is_cand_union : forall X Y, is_cand (Union X Y).
unfold Union; intros.
apply is_can_compl.
Qed.

 Lemma is_cand_union1 : forall (X Y:CR) t,
   is_cand X -> X t -> Union X Y t.
red; red; intros.
apply H2; auto.
apply (incl_sn X); trivial.
Qed.

 Lemma is_cand_union2 : forall (X Y:CR) t,
   is_cand Y -> Y t -> Union X Y t.
red; red; intros.
apply H2; auto.
apply (incl_sn Y); trivial.
Qed.


(******************************************************************************)

  Lemma cand_context : forall u u' v,
    (forall X, is_cand X -> X u -> X u') ->
    forall X, is_cand X -> X (App u v) -> X (App u' v).
intros.
assert (sn v).
 apply subterm_sn with (App u v); auto.
 apply (incl_sn X); trivial.
assert (Arr (weak_chain v) X u').
 apply H.
  apply weak_cand_Arr; trivial.
  apply weakest_cands; trivial.

  red; intros. 
  apply (clos_red X) with (App u v); auto with *.
red in H3.
apply H3; auto with *.
Qed.

  Lemma cand_sat1 :
   forall X, is_cand X ->
   forall u v, sn u ->
   forall m, X (App (subst u m) v) ->
   X (App2 (Abs m) u v).
intros.
apply cand_context with (X:=X) (u:=subst u m); intros; auto.
apply cand_sat with (X:=X0); trivial.
Qed.

  Lemma cand_sat2 :
   forall X, is_cand X ->
   forall u v w, sn u ->
   forall m, X (App2 (subst u m) v w) ->
   X (App (App2 (Abs m) u v) w).
intros.
apply cand_context with (X:=X) (u:=App (subst u m) v); intros; auto.
apply cand_sat1 with (X:=X0); trivial.
Qed.

  Lemma cand_sat3 :
   forall X, is_cand X ->
   forall u v w x, sn u ->
   forall m, X (App2 (App (subst u m) v) w x) ->
   X (App2 (App2 (Abs m) u v) w x).
intros.
apply cand_context with (X:=X) (u:=App2 (subst u m) v w); intros; auto.
apply cand_sat2 with (X:=X0); trivial.
Qed.
