Require Import CCTnat.

Import BuildModel.
Import CCM.
Import IZF.
Import T J.

Definition esub := {f : val->val | Proper (eq_val ==> eq_val) f}.

Definition eq_esub es es':= 
  forall i i', eq_val i i' -> eq_val (es i) (es' i).

Definition esub_conv (f : esub) (es : val) := proj1_sig f es.

Instance esub_conv_morph : Proper (eq ==> eq_val ==> eq_val) esub_conv.
do 4 red; simpl; intros. subst y.
destruct x; simpl. rewrite H0; reflexivity.
Qed.

Definition app_esub : esub -> term -> term.
intros es t. left. 
exists (fun i => int t (esub_conv es i)).
do 3 red; intros. apply int_morph; try reflexivity.
 apply esub_conv_morph; trivial.
Defined.

Definition id_sub : esub.
exists (fun f => f). do 2 red; trivial.
Defined.

Definition sub_cons : term -> esub -> esub.
intros t es.
exists (fun i => V.cons (int t i) (esub_conv es i)).
do 2 red; intros. apply V.cons_morph; 
  [rewrite H; reflexivity| apply esub_conv_morph; trivial].
Defined.

Definition typ_esub env1 es env2 := forall i, 
  val_ok env1 i -> val_ok env2 (esub_conv es i).

Lemma esub_typ_id : forall env, typ_esub env id_sub nil.
do 2 red; intros. destruct n; simpl in H0; discriminate.
Qed.

Lemma esub_typ_cons : forall env1 env2 s t A,
  typ_esub env1 s env2 ->
  typ env1 t (app_esub s A) ->
  typ_esub env1 (sub_cons t s) (A::env2).
red; intros. simpl. 
apply vcons_add_var; [apply H | apply H0]; trivial.
Qed.

Lemma embedding' : forall env1 env2 s t A, A <> None ->
  typ_esub env1 s env2 ->
  typ env2 t A -> 
  typ env1 (app_esub s t) (app_esub s A).
do 2 red; simpl; intros.
red in H0; specialize H0 with (1:=H2).
do 2 red in H1. specialize H1 with (1:=H0).
destruct A; trivial.
 elim H; trivial.
Qed.

Lemma EQ_trm_esub : forall x y s, 
  eq_term (app_esub s (EQ_trm x y)) (EQ_trm (app_esub s x) (app_esub s y)).
red; simpl; red; intros. 
replace (fun k : nat => esub_conv s x0 k) with (esub_conv s x0); trivial.
replace (esub_conv s (fun k : nat => y0 k)) with (esub_conv s y0); trivial.
apply ZFind_basic.EQ_morph; [|rewrite H|rewrite H]; reflexivity.
Qed.

Definition eq_fosub n' e s s' := forall n, n < n' ->
  eq_typ e (app_esub s (Ref n)) (app_esub s' (Ref n)) /\
  typ e (app_esub s (Ref n)) T /\ typ e (app_esub s' (Ref n)) T.

Fixpoint max_var_rec (t:foterm) max_v :=
  match t with
    | Var n => Peano.max max_v n
    | Cst_0 => max_v
    | Cst_1 => max_v
    | Df_Add m n => Peano.max (max_var_rec m max_v) (max_var_rec n max_v) 
  end.

Definition max_var t := max_var_rec t 0.

Fixpoint const_env n := 
  match n with
    | 0 => T :: nil
    | S m => T :: (const_env m)
  end.

Lemma succ_max_distr : forall n m, S (Peano.max n m) = Peano.max (S n) (S m).
induction n; destruct m; simpl; reflexivity.
Qed.

Lemma max_split1 : forall x y z, z < x -> z < Peano.max x y.
induction x; simpl; intros.
 apply False_ind; omega.

 destruct y; trivial.
  destruct z; try omega.
   assert (z < x) by omega. specialize IHx with (1:=H0) (y:=y). omega.
Qed.

Lemma max_split2 : forall x y z, z < y -> z < Peano.max x y.
induction x; simpl; intros; trivial.
 destruct y; trivial.
  apply False_ind; omega.
 
  destruct z; try omega.
   assert (z < y) by omega. specialize IHx with (1:=H0). omega.
Qed.

Lemma max_comb : forall x y z, z < Peano.max x y -> z < x \/ z < y.
induction x; simpl; intros.
 right; trivial.

 destruct y.
  left; trivial.

  destruct z.
   left; omega.

   assert (z < Peano.max x y) by omega.
   specialize IHx with (1:=H0). destruct IHx; [left | right]; omega.
Qed.

Lemma const_env_spec : forall m n t, 
  nth_error (const_env n) m = value t ->
  m <= n /\ t = T.
induction m; destruct n; simpl; intros.
 injection H; intros; split; [|subst t]; trivial.

 injection H; intros; split; [omega |subst t]; trivial.

 destruct m; simpl in H; discriminate.

 specialize IHm with (1:=H). destruct IHm.
 split; [omega | trivial].
Qed.

Lemma impl_and_split : forall A B C, (A -> B /\ C) -> ((A -> B)/\(A->C)).
split; intros H1; specialize H with (1:=H1); destruct H; trivial.
Qed.

Lemma embedding : forall e t1 t2 s s',
  eq_typ (const_env (Peano.max (max_var t1) (max_var t2)))
  (int_fotrm t1) (int_fotrm t2) ->
  eq_fosub (S (Peano.max (max_var t1) (max_var t2))) e s s' ->
  eq_typ e (app_esub s (int_fotrm t1)) (app_esub s' (int_fotrm t2)).
do 2 red; simpl; intros.
do 2 red in H; simpl.
unfold eq_fosub in H0.
assert (val_ok (const_env (Peano.max (max_var t1) (max_var t2))) (esub_conv s i)).
 unfold val_ok. do 2 red; intros. apply const_env_spec in H2.
 destruct H2; subst T; simpl.
 assert (n < S (Peano.max (max_var t1) (max_var t2))) by omega.
 specialize H0 with (1:=H3); destruct H0 as (Heqtyp, (Htyps, Htyps')).
 do 2 red in Htyps; simpl in Htyps; specialize Htyps with (1:=H1). apply Htyps.

specialize H with (1:=H2). rewrite H.
replace (fun k : nat => i k) with i; trivial. clear H H2.

induction t2; simpl; try reflexivity.
 specialize H0 with (n0:=n). destruct H0.
  rewrite succ_max_distr. apply max_split2. unfold max_var; simpl; omega.
  do 2 red in H; simpl in H; apply H; trivial.

 apply NATREC_morph.
  apply IHt2_1. intros. apply H0.
  rewrite succ_max_distr. rewrite succ_max_distr in H. 
  apply max_comb in H. destruct H.
   apply max_split1; trivial.

   apply max_split2. unfold max_var; simpl.
   rewrite succ_max_distr. apply max_split1. trivial.

  do 2 red; intros. rewrite H2; reflexivity.

  apply IHt2_2. intros. apply H0.
  rewrite succ_max_distr. rewrite succ_max_distr in H. 
  apply max_comb in H. destruct H.
   apply max_split1; trivial.

   apply max_split2. unfold max_var; simpl.
   rewrite succ_max_distr. apply max_split2. trivial.
Qed.




  