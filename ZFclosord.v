Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFord ZFfix ZFstable.
Require Import ZFlist.
Import ZFrepl.

Section W_theory.

Variable A : set.

Definition path := List A.

Definition tree := power path.

Definition node f :=
  union2 (singl Nil) (sup A (fun x => replf (f x) (Cons x))).

Lemma text1 X x : ext_fun X (Cons x).
do 2 red; intros; apply couple_morph; auto with *.
Qed.
Lemma text2 f : ext_fun A f -> ext_fun A (fun x => replf (f x) (Cons x)).
do 2 red; intros; apply replf_morph; auto with *.
red; intros; apply couple_morph; trivial.
Qed.
Hint Resolve text1 text2.

Lemma node_def : forall f p,
  ext_fun A f ->
  (p \in node f <->
   p == Nil \/ exists2 i, i \in A & exists2 p', p' \in f i & p == Cons i p').
intros; unfold node.
split; intros.
 apply union2_elim in H0; destruct H0; [left|right].
  apply singl_elim in H0; trivial.

  rewrite sup_ax in H0; auto; destruct H0.
  exists x; trivial.
  rewrite replf_ax in H1; trivial.

 destruct H0; [apply union2_intro1|apply union2_intro2].
  rewrite H0; apply singl_intro.

  destruct H0 as (i,tyi,(p',infi,eqp)).
  rewrite sup_ax; auto.
  exists i; trivial.
  rewrite replf_ax; eauto.
Qed.

Lemma node_tl f i p :
  ext_fun A f ->
  i \in A ->
  (Cons i p \in node f <-> p \in f i).
intros.
rewrite node_def; trivial.
split; intros; eauto with *.
destruct H1 as [abs|(i',tyi,(p',typ',eqp))].
 symmetry in abs; apply discr_mt_pair in abs; contradiction.

 apply couple_injection in eqp; destruct eqp.
 rewrite H2; rewrite (H _ _ H0 H1); trivial.
Qed.

Lemma node_mono f f':
  ext_fun A f -> 
  ext_fun A f' ->
  (forall i, i \in A -> f i \incl f' i) ->
  node f \incl node f'.
red; intros.
rewrite node_def in H2|-*; trivial.
destruct H2;[left;trivial|right].
destruct H2 as (i,tyi,(p,typ,eqp)).
exists i; trivial.
exists p; auto.
apply H1; trivial.
Qed.

Lemma node_morph f f' :
  eq_fun A f f' -> node f == node f'.
intros.
assert (e1 := eq_fun_ext _ _ _ H).
assert (e2 := eq_fun_ext _ _ _ (symmetry H)).
apply incl_eq; apply node_mono; trivial; intros.
 rewrite <- (H _ _ H0 (reflexivity _)); reflexivity. 
 rewrite <- (H _ _ H0 (reflexivity _)); reflexivity. 
Qed.

Lemma node_inv_mono f f' :
  ext_fun A f ->
  ext_fun A f' ->
  node f \incl node f' ->
  forall i, i \in A -> f i \incl f' i.
red; intros.
rewrite <- node_tl in H3; trivial.
apply H1 in H3.
rewrite node_tl in H3; trivial.
Qed.

Lemma node_inj f f' :
  ext_fun A f ->
  ext_fun A f' ->
  node f == node f' ->
  eq_fun A f f'.
red; intros.
apply incl_eq.
 rewrite <- (H0 _ _ H2 H3).
 apply node_inv_mono; trivial.
 rewrite H1; reflexivity.

 rewrite <- (H0 _ _ H2 H3).
 apply node_inv_mono; trivial.
 rewrite H1; reflexivity.
Qed.

Lemma node_typ f :
  ext_fun A f ->
  typ_fun f A tree ->
  node f \in tree.
intros.
apply power_intro; intros.
rewrite node_def in H1; trivial.
destruct H1 as [hd|(i,tyi,(p,typ,eqp))].
 rewrite hd; apply Nil_typ.

 rewrite eqp; apply Cons_typ; auto.
 apply power_elim with (2:=typ); auto.
Qed.

Lemma text3 X : ext_fun (cc_arr A X) (fun f => node (cc_app f)).
do 2 red; intros.
apply node_morph.
red; intros; apply cc_app_morph; auto with *.
Qed.
Lemma text4 X f : ext_fun X (cc_app f).
do 2 red; intros; apply cc_app_morph; auto with *.
Qed.
Hint Resolve text3 text4.

(* X a set of trees *)
Definition nodeF X := replf (cc_arr A X) (fun f => node (cc_app f)).

Lemma nodeF_def X t :
  t \in nodeF X <-> exists2 f, f \in cc_arr A X & t == node (cc_app f).
unfold nodeF.
rewrite replf_ax; auto with *.
Qed.

Instance nodeF_mono : Proper (incl_set ==> incl_set) nodeF.
do 3 red; intros.
rewrite nodeF_def in H0 |- *.
destruct H0.
exists x0; auto.
revert H0; apply cc_prod_covariant; auto with *.
Qed.

Instance nodeF_morph : morph1 nodeF.
Proof Fmono_morph _ nodeF_mono.

Lemma nodeF_typ X : X \incl tree -> nodeF X \incl tree.
unfold nodeF; red; intros.
rewrite replf_ax in H0; trivial.
destruct H0.
rewrite H1.
apply node_typ; trivial.
red; intros.
apply H.
apply cc_arr_elim with (1:=H0); trivial.
Qed.

Definition trees := Ffix nodeF tree.










(***************************************************************************)

(* No! *)
Definition node x f :=
  sup ts (fun t => replf t (Cons x)).

Lemma node_def : forall x ts p,
  p \in node x ts <-> exists2 t, t \in ts & exists2 p', p' \in t & p == Cons x p'.

Lemma node_inj : forall x x' t t', node x t == node x' t' -> x == x' /\ t == t'.

(* Prefix order on paths *)
Definition leP := exists2 x, x \in A & p2 == Cons x p1.
Definition leT t p1 p2 := (p1 \in t /\ p2 \in t) /\ leP t1 t2.
Lemma leT_node : forall x ts t p1 p2,
  t \in ts ->
  leT t p1 p2 ->
  leT (node x ts) (Cons x p1) (Cons x p2).

Lemma node_typ :
  x \in A -> ts \incl tree -> node x t \in tree

Definition nodeF ts := sup A (fun x => replf ts (node x)).

Lemma nodeF_typ : forall ts,
  ts \incl tree -> nodeF ts \incl tree.

Lemma nodeF_mono : Proper (incl_set ==> incl_set) nodeF.

Lemma nodeF_stable : forall X Y,
  X \incl tree ->
  Y \incl tree ->
  nodeF (inter2 X Y) == inter2 (nodeF X) (nodeF Y).

Definition trees := Ffix tree nodeF.





 sup ts (fun t => replf A (fun 

Definition wftree t := well_founded (leT t).

Definition trees := subset (power tree) wftree.

Lemma node_typ_wf :
  x \in A -> ts \in tress -> wftree (node x t)

Lemma wft_constr :


Variable F : set -> set.
Hypothesis Fmono : Proper (incl_set ==> incl_set) F.
Hypothesis Fstab : stable F.

Let Fm : morph1 F.
apply Fmono_morph; trivial.
Qed.

Variable Fdom : set -> set.
Hypothesis Fdm : morph1 Fdom.
Hypothesis Fds : forall X x, x \in F X -> Fdom x \incl A.

Variable Fsub : set -> set -> set.
Hypothesis Fsm : morph2 Fsub.
Hypothesis Fstyp : forall X x i, x \in F X -> i \in Fdom x -> Fsub x i \in X.

(* The construction domain and the constructor *)
Definition Wdom := power (List A).

Definition Wsup x :=
  union2 (singl Nil) 
    (sup (Fdom x) (fun i => replf (Fsub x i) (fun p => Cons i p))).

Instance Wsup_morph : Proper (eq_set ==> eq_set) Wsup.
do 2 red; intros.
unfold Wsup.
apply union2_morph; auto with *.
apply sup_morph; auto with *.
red; intros.
apply replf_morph_raw; auto.
 apply Fsm; trivial.

 red; intros.
 apply couple_morph; trivial.
Qed.

Lemma wext1 : forall i y,
  ext_fun y (fun p => Cons i p).
do 2 red; intros.
rewrite H0; reflexivity.
Qed.

Lemma wext2 : forall X f,
  ext_fun X (fun y =>
     replf (Fsub f y) (fun p => Cons y p)).
do 2 red; intros.
apply replf_morph_raw; auto.
 rewrite H0; reflexivity.

 red; intros.
 rewrite H0; rewrite H1; reflexivity.
Qed.
Hint Resolve wext1 wext2.

Lemma Wsup_def :
  forall x p,
  (p \in Wsup x <->
   p == Nil \/
   exists2 i, i \in Fdom x &
   exists2 q, q \in Fsub x i &
   p == Cons i q).
intros.
unfold Wsup.
split; intros.
 apply union2_elim in H; destruct H;[left|right].
  apply singl_elim in H; trivial.

  rewrite sup_ax in H; trivial.
  destruct H as (i,?,?); exists i; trivial.
  rewrite replf_ax in H0; trivial.

 destruct H as [eqp|(i,?,(q,?,eqp))]; rewrite eqp; clear eqp.  
  apply union2_intro1.
  apply singl_intro.

  apply union2_intro2.
  rewrite sup_ax; trivial.
  exists i; trivial.
  rewrite replf_ax; trivial.
  exists q; auto with *.
Qed.

Lemma Wsup_hd_prop : forall x, Nil \in Wsup x.
intros.
unfold Wsup.
apply union2_intro1.
apply singl_intro.
Qed.

Lemma Wsup_tl_prop : forall i l x,
  x \in F Wdom ->
  (Cons i l \in Wsup x <-> i \in Fdom x /\ l \in Fsub x i).
intros.
split; intros.
 apply union2_elim in H0; destruct H0.
  apply singl_elim in H0.
  symmetry in H0.
  apply discr_mt_pair in H0; contradiction.

  rewrite sup_ax in H0; trivial.
  destruct H0.
  rewrite replf_ax in H1; trivial.
  destruct H1.
  apply couple_injection in H2; destruct H2.
  rewrite H2; split; trivial.
  rewrite H3; trivial.

 destruct H0.
 unfold Wsup.
 apply union2_intro2.
 rewrite sup_ax; trivial.
 exists i; trivial.
 rewrite replf_ax; trivial.
 exists l; auto with *.
Qed.
(*
Lemma Wsup_inj : forall x x',
  x \in F Wdom ->
  x' \in F Wdom ->
  Wsup x == Wsup x' -> x == x'.
intros.
assert (fst x == fst x').
 generalize (Wsup_hd_prop (fst x) x); intro.
 generalize (Wsup_hd_prop (fst x) x'); intro.
 apply H3.
 rewrite <- H1.
 apply H2.
 reflexivity.
assert (snd x == snd x').
 specialize cc_eta_eq with (1:=tys _ _ H); intros.
 specialize cc_eta_eq with (1:=tys _ _ H0); intros.
 rewrite H3; rewrite H4.
 apply cc_lam_ext.
  apply Bmorph; trivial.

  red; intros.
  assert (x'0 \in A (fst x')).
   rewrite <- H6; rewrite <- H2; trivial.
  assert (cc_app (snd x) x0 \incl prodcart (List (sup A A)) A).
   red; intros.
   apply power_elim with (2:=H8).
   apply cc_prod_elim with (1:=tys _ _ H); trivial.
  assert (cc_app (snd x') x'0 \incl prodcart (List (sup A A)) A).
   red; intros.
   apply power_elim with (2:=H9); trivial.
   apply cc_prod_elim with (1:=tys _ _ H0); trivial.
  generalize (fun z l => Wsup_tl_prop x0 l z _ H); intros.
  generalize (fun z l => Wsup_tl_prop x'0 l z _ H0); intros.
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
Lemma Wsup_typ_gen : forall x,
  x \in F Wdom ->
  Wsup x \in Wdom.
intros.
apply power_intro; intros.
rewrite Wsup_def in H0.
destruct H0 as [eqz|(i,?,(q,?,eqz))]; rewrite eqz; clear z eqz.
 apply Nil_typ.

 assert (q \in List A).
  apply power_elim with (2:=H1); auto.
 apply Cons_typ; auto.
 revert H0; apply (Fds Wdom); trivial.
Qed.

(* The type operator on the construction domain *)
Definition Wf X := replf (F X) Wsup.

Lemma wfext1 : forall X, ext_fun (F X) Wsup.
do 2 red; intros.
rewrite H0; reflexivity.
Qed.
Hint Resolve wfext1.

Lemma Wf_intro : forall x X,
  x \in F X ->
  Wsup x \in Wf X.
intros.
unfold Wf.
rewrite replf_ax; trivial.
exists x; auto with *.
Qed.

Lemma Wf_elim : forall a X,
  a \in Wf X ->
  exists2 x, x \in F X &
  a == Wsup x.
intros.
unfold Wf in H.
rewrite replf_ax in H; trivial.
Qed.

Lemma Wf_mono : Proper (incl_set ==> incl_set) Wf.
do 3 red; intros.
apply Wf_elim in H0; destruct H0 as (f,?,?).
rewrite H1; apply Wf_intro; trivial.
clear H1; revert f H0.
apply Fmono; trivial.
Qed.
Hint Resolve Wf_mono Fmono_morph.

Lemma Wf_typ : forall X,
  X \incl Wdom -> Wf X \incl Wdom.
red; intros.
apply Wf_elim in H0; destruct H0 as (x,?,?).
rewrite H1.
apply Wsup_typ_gen; trivial.
clear H1; revert x H0.
apply Fmono; trivial.
Qed.
Hint Resolve Wf_typ.

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
rewrite replf_ax.
2:red;red;intros;apply Wsup_morph; trivial.
destruct inter_wit with (2:=H).
 apply Fmono_morph; trivial.
assert (z \in Wf x); auto.
apply Wf_elim in H2.
destruct H2.
exists x0; auto.
apply Fstab.
apply inter_intro.
 intros.
 rewrite replf_ax in H4.
 2:apply morph_is_ext; trivial.
 destruct H4.
 rewrite H5; clear y H5.
 specialize H0 with (1:=H4).
 apply Wf_elim in H0; destruct H0.
 admit.
(* rewrite H3 in H5; apply Wsup_inj in H5.
  rewrite H5; trivial.

  revert H2; apply W_F_mono.
  red; intros; apply power_elim with (1:=Xty _ H1); trivial.

  revert H0; apply W_F_mono.
  red; intros; apply power_elim with (1:=Xty _ H4); trivial.
*)
 exists (F x).
 rewrite replf_ax.
 2:apply morph_is_ext; trivial.
 exists x; auto with *.
Qed.
Hint Resolve Wf_stable.

(* The fixpoint *)

Definition W := Ffix Wf Wdom.

Lemma Wtyp : W \incl Wdom.
apply Ffix_inA.
Qed.

Lemma Wi_W : forall o, isOrd o -> TI Wf o \incl W.
apply TI_Ffix; auto.
Qed.

Lemma TI_Wf_elim : forall a o,
  isOrd o ->
  a \in TI Wf o ->
  exists2 o', lt o' o &
  exists2 x, x \in F (TI Wf o') &
  a == Wsup x.
intros.
apply TI_elim in H0; trivial.
2:apply Fmono_morph; trivial.
destruct H0.
apply Wf_elim in H1.
eauto.
Qed.

Lemma Wsup_typ : forall o x,
  isOrd o ->
  x \in F (TI Wf o) ->
  Wsup x \in TI Wf (osucc o).
intros.
rewrite TI_mono_succ; auto.
apply Wf_intro; trivial.
Qed.
(*
Lemma W_ind : forall (P:set->Prop),
  Proper (eq_set ==> iff) P ->
  (forall o' x, isOrd o' -> x \in W_F (TI Wf o') ->
   (forall i, i \in A (fst x) -> P (cc_app (snd x) i)) -> P (Wsup x)) ->
  forall a, a \in W -> P a.
intros.
unfold W in H1; rewrite Ffix_def in H1; auto.
destruct H1.
revert a H2.
apply isOrd_ind with (2:=H1); intros.
apply TI_Wf_elim in H5; trivial.
destruct H5 as (o',?,(x',?,?)).
rewrite H7; clear a H7.
apply H0 with o'; trivial.
 apply isOrd_inv with y; trivial.

 intros.
 apply H4 with o'; trivial.
 apply cc_prod_elim with (1:=tys _ _ H6); trivial.
Qed.
*)
(* The closure ordinal of W *)
  Definition W_ord := Ffix_ord Wf Wdom.

  Lemma W_o_o : isOrd W_ord.
apply Ffix_o_o; auto.
Qed.
Hint Resolve W_o_o.

  Lemma W_post : forall a,
   a \in W ->
   a \in TI Wf W_ord.
apply Ffix_post; eauto.
Qed.

  Lemma W_eqn : W == Wf W.
apply Ffix_eqn; eauto.
Qed.




  Lemma Fix_reached : TI F (osucc W_ord) \incl TI F W_ord.

(*
Parameter hd : set -> set.
Parameter tl : set -> set -> set.
Parameter hd_eq : forall x, hd (Wsup x) == fst x.

Parameter Wf_eta : forall X x,
  X \incl Wdom ->
  x \in Wf X ->
  x == Wsup (couple (hd x) (cc_lam (A (hd x)) (tl x))).

  Definition trad := Fix_rec Wf Wdom
    (fun g x => couple (hd x)
       (cc_lam (A (hd x)) (fun i => g (tl x i)))).

  Lemma trad_ok : forall o,
    isOrd o ->
    forall x,
    x \in TI Wf o ->
    trad x \in TI W_F o.
intros o oo.
apply isOrd_ind with (2:=oo); intros.
unfold trad.
rewrite Fr_eqn with (o:=y); auto.
2:admit.
apply TI_Wf_elim in H2; trivial.
destruct H2 as (o',?,(x',?,?)).
apply TI_intro with o'; auto.
 apply Fmono_morph; apply W_F_mono.

 assert (x \in Wf (TI Wf o')).
  rewrite <- TI_mono_succ; auto.
  2:apply isOrd_inv with y; trivial.
  rewrite H4; apply Wsup_typ; trivial.
  apply isOrd_inv with y; trivial.
 apply Wf_eta in H5.
 2:admit.
 apply couple_intro_sigma.
  admit.

  admit.

  apply cc_prod_intro; intros.
   admit.
   admit.
  apply H1; trivial.
  admit.
Qed.

  Lemma trad_inj : forall o,
    isOrd o ->
    forall x y, x \in TI Wf o ->
    y \in TI Wf o ->
    trad x == trad y -> x == y.
intros o oo.
apply isOrd_ind with (2:=oo); intros.
unfold trad in H4.
rewrite Fr_eqn with (o:=y) in H4; auto.
2:admit.
rewrite Fr_eqn with (o:=y) in H4; auto.
2:admit.
apply couple_injection in H4; destruct H4.
rewrite (Wf_eta (TI Wf y)).
2:admit.
2:admit.
rewrite (Wf_eta (TI Wf y) y0).
2:admit.
2:admit.
apply Wsup_morph.
apply couple_morph; trivial.
apply cc_lam_ext; intros.
 apply Amorph; trivial.

 red; intros.
 generalize (cc_app_morph _ _ H5 _ _ H7).
 rewrite cc_beta_eq; trivial.
 2:admit.
 rewrite cc_beta_eq; trivial.
 2:admit.
 2:rewrite <- H7; rewrite <- H4; trivial.
 apply H1 with (z:=y).
  admit.
  admit.
  admit.
Qed.
*)

End W_theory.
