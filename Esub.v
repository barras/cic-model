Require Import GenLemmas.

Import SN_CC_Real.
Import ZF SN SN_CC_Model.

Definition esub_i := {f : val->val | Proper (eq_val ==> eq_val) f}.

Definition esub_j := {f : Lc.intt -> Lc.intt | 
  Proper (Lc.eq_intt ==> Lc.eq_intt) f /\
  (forall j k, Lc.eq_intt (f (fun n : nat => Lc.lift_rec 1 (j n) k))
  (fun n : nat => Lc.lift_rec 1 (f j n) k)) /\
  (forall j k u, Lc.eq_intt (f (fun n : nat => Lc.subst_rec u (j n) k))
     (fun n : nat => Lc.subst_rec u (f j n) k))}.

Definition eq_esub_i es es':= 
  forall i i', eq_val i i' -> eq_val (es i) (es' i').

Definition eq_esub_j es es' :=
  forall j j', Lc.eq_intt j j' -> Lc.eq_intt (es j) (es' j').

Definition esub_conv_i (f : esub_i) (es : val) := proj1_sig f es.

Definition esub_conv_j (f : esub_j) (es : Lc.intt) : Lc.intt := 
  proj1_sig f es.

Instance esub_conv_i_morph : 
  Proper (eq ==> eq_val ==> eq_val) esub_conv_i.
do 4 red; simpl; intros. subst y.
destruct x; simpl. rewrite H0; reflexivity.
Qed.

Instance esub_conv_j_morph : 
 Proper (eq ==> Lc.eq_intt ==> Lc.eq_intt) esub_conv_j.
do 5 red; simpl; intros. subst y.
destruct x as (f, (H, (Hl, Hs))); simpl. apply H; trivial.
Qed.

Definition app_esub : esub_i -> esub_j -> term -> term.
intros es_i es_j t; left.
exists (fun i => int t (esub_conv_i es_i i)) (fun j => tm t (esub_conv_j es_j j)).
do 4 red; intros. apply int_morph; try reflexivity.
 apply esub_conv_i_morph; trivial.

do 2 red; intros. apply tm_morph; try reflexivity.
 apply esub_conv_j_morph; trivial.

destruct es_j as (f, (H, (Hl, Hs))); simpl.
red; intros. rewrite Hl.
destruct t; [destruct i; simpl; apply itm_lift0|]; trivial.

destruct es_j as (f, (H, (Hl, Hs))); simpl.
red; intros. rewrite Hs.
destruct t; [destruct i; simpl; apply itm_subst0|]; trivial.
Defined.

Definition id_sub_i : esub_i.
exists (fun f => f). do 2 red; trivial.
Defined.

Definition id_sub_j : esub_j.
exists (fun f => (fun _ => Lc.K)). 
split; [do 4 red|split; do 2 red; intros]; trivial.
Defined.

Definition sub_cons_i : term -> esub_i -> esub_i.
intros t es.
exists (fun i => V.cons (int t i) (esub_conv_i es i)).
do 2 red; intros. apply V.cons_morph; 
  [rewrite H; reflexivity| apply esub_conv_i_morph; trivial].
Defined.

Definition sub_cons_j : term -> esub_j -> esub_j.
intros t es.
exists (fun j => I.cons (tm t j) (esub_conv_j es j)).
split; [|split]; intros.
 do 4 red; intros; rewrite H; trivial.

 do 2 red; intros. destruct es as (f, (H, (Hl, Hs))); simpl. rewrite Hl. 
 destruct t; [destruct i; simpl; rewrite itm_lift0|]; destruct a; simpl; trivial.

 do 2 red; intros. destruct es as (f, (H, (Hl, Hs))); simpl. rewrite Hs. 
 destruct t; [destruct i; simpl; rewrite itm_subst0|]; destruct a; simpl; trivial.
Defined.

Definition typ_esub env1 es_i es_j env2 := 
  forall i j, val_ok env1 i j -> 
    val_ok env2 (esub_conv_i es_i i) (esub_conv_j es_j j).

Lemma esub_typ_id : forall env, typ_esub env id_sub_i id_sub_j nil.
do 2 red; intros. destruct n; simpl in H0; discriminate.
Qed.

Lemma esub_typ_cons : forall env1 env2 s s' t A,
  A <> kind ->
  typ_esub env1 s s' env2 ->
  typ env1 t (app_esub s s' A) ->
  typ_esub env1 (sub_cons_i t s) (sub_cons_j t s') (A::env2).
red; intros; simpl.
apply vcons_add_var; [apply H0| |]; trivial.
 apply red_typ with (1:=H2) in H1; [|discriminate].
 destruct H1 as (_, H1). simpl int in H1; trivial.
Qed.

Lemma explicit_sub_typ : forall env1 env2 s s' t A, 
  A <> kind ->
  typ_esub env1 s s' env2 ->
  typ env2 t A -> 
  typ env1 (app_esub s s' t) (app_esub s s' A).
red; intros.
apply H0 in H2.
apply H1 in H2.
apply in_int_not_kind in H2; trivial.
apply in_int_intro; [discriminate|discriminate|].
simpl int; simpl tm in H2 |- *; trivial.
Qed.

Lemma explicit_sub_eq_typ : forall env1 env2 s s' x y,
  x <> kind ->
  y <> kind ->
  typ_esub env1 s s' env2 ->
  eq_typ env2 x y ->
  eq_typ env1 (app_esub s s' x) (app_esub s s' y).
red; intros. 
apply H1 in H3. 
apply H2 in H3; simpl; trivial.
Qed.