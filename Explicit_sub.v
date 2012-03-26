Require Export TheoryInTerm.

Import BuildModel.
Import CCM.
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

Lemma explicit_sub : forall env1 env2 s t A, A <> None ->
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

Definition eq_fosub n' e s s' := forall n, (n < n')%nat ->
  eq_typ e (app_esub s (Ref n)) (app_esub s' (Ref n)) /\
  typ e (app_esub s (Ref n)) T /\ typ e (app_esub s' (Ref n)) T.
