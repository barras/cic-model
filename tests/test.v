(* Acc is a prop *)

Parameter dfunext : forall A B (f g:forall x:A,B x),
  (forall x, f x = g x) -> f = g.

Lemma Acc_prop A (R:A->A->Prop) x (h h':Acc R x) : h=h'. 
revert x h h'.
fix 2.
intros.
destruct h.
destruct h'.
f_equal.
apply dfunext; intros y.
apply dfunext; intros r.
apply Acc_prop.
Defined.




Require Import Lambda.

Parameter neutral : term->Prop.
Parameter neutral_red : forall m m',
  neutral m -> red m m' -> neutral m'.
Parameter neutral_not_abs : forall m,
  ~ neutral (Abs m).
Parameter neutral_var : forall n, neutral (Ref n).
Parameter neutral_app : forall m n,
  neutral m -> sn n -> neutral (App m n).
Parameter neutral_sn : forall m, neutral m -> sn m.


Inductive max_dup : term -> nat -> Prop :=
| max_dup_var m : max_dup (Ref m) 1
| max_dup_app m n k1 k2 :
    neutral m ->
    max_dup m k1 ->
    max_dup n k2 ->
    max_dup (App m n) (k1+k2)
| max_dup_abs m k :
    max_dup m k ->
    max_dup (Abs m) k
| max_dup_step m n k1 k2 k3 :
    max_dup (subst n m) k1 ->
    max_dup m k2 ->
    max_dup n k3 ->
    max_dup (App (Abs m) n) (k1+k2+k3).

Lemma redp_dup_decr m n k :
  max_dup m k ->
  redpar m n ->
  exists2 k', k' <= k & max_dup n k'.
intro.
revert n; induction H; intros.
 inversion_clear H.
 exists 1; auto with *.
 constructor.

 inversion H2.
  subst m; apply neutral_not_abs in H; contradiction.

  destruct IHmax_dup1 with (1:=H5).
  destruct IHmax_dup2 with (1:=H7).
  exists (x+x0).
   omega.
  constructor; trivial.
  apply neutral_red with m; auto with *.
  apply rp2.
  apply t_step; trivial.

 inversion_clear H0.
 destruct IHmax_dup with (1:=H1).
 exists x; trivial.
 constructor; trivial.

 inversion H2.
  destruct IHmax_dup1 with (subst n' m').
   apply rp_subst; trivial.
  exists x; trivial.
  omega.

  inversion_clear H5.
  destruct IHmax_dup1 with (subst n' m'0).
   apply rp_subst; trivial.
  destruct IHmax_dup2 with (1:=H8).
  destruct IHmax_dup3 with (1:=H7).
  exists (x+x0+x1).  
   omega.
  apply max_dup_step; trivial.
Qed.


Lemma sn_subterm_ind (P:term->Prop) :
  (forall n, P (Ref n)) ->
  (forall m n, sn m -> P m -> sn n -> P n -> P (App m n)) ->
  (forall m, sn m -> P m -> P (Abs m)) ->
  (forall m m', sn m -> red1 m m' -> P m' -> P m) ->
  forall t, sn t -> P t.
Admitted.


Lemma sn_neutral_dec m :
  sn m -> neutral m \/ exists m', red m (Abs m').
Admitted.
(*induction 1; intros.
revert H0.
assert (sn x).
 constructor; trivial.
clear H; revert H0.
induction x; intros.
 left; apply neutral_var.

 right; exists x; auto with *.

 destruct x1.
  left; apply neutral_app.
   apply neutral_var.
   apply subterm_sn with (App (Ref n) x2); trivial.

  destruct H1 with (subst x2 x1).
   constructor.

   left; admit.

   destruct H.
   right; exists x.
   admit.

  destruct IHx1.
   apply subterm_sn with (1:=H0).
   constructor.

   intros.




   trivial.

*)

Lemma sn_ex_dup m :
  sn m -> exists k, max_dup m k.
induction 1 using sn_subterm_ind.
 exists 1; constructor.

 destruct sn_neutral_dec with (1:=H).
  destruct IHsn1.
  destruct IHsn2.
  exists (x+x0); constructor; trivial.

  destruct H1.
  destruct IHsn1.
  destruct IHsn2.
  assert (exists k, max_dup (Abs x) k).
   revert x0 H2; elim H1; intros; auto.
    exists x0; trivial.

    destruct H4 with (1:=H6).
    destruct redp_dup_decr with (1:=H7) (n:=N).
     admit.
    exists x3; trivial.
  destruct H4.
  inversion_clear H4.
  exists (

    


induction 1.
assert (forall m' k, clos_refl_trans _ subterm m' x -> exists k, max_dup m' k).
intros.
revert H0.
induction H1; intros.
 inversion H0.
  


Require Import List.

Inductive repl : term -> list term -> term -> Prop :=
| repl_app m m' n n' l1 l2 :
    repl m l1 m' ->
    repl n l2 n' ->
    repl (App m n) (l1++l2) (App m' n')
| repl_abs m l m' :
    repl m l m' ->
    repl (Abs m) l (Abs m')
| repl_var n m :
    repl (Ref n) (m::nil) m.



Lemma sn_subst_neu : forall m n,
  sn m -> neutral n -> sn (subst n m).
Admitted.

Lemma sn_app_neu : forall m n,
  sn m -> neutral n -> sn (App m n).
intros.
revert n H0.
induction H; intros.
unfold transp in H0.
assert (snn := neutral_sn _ H1).
revert H1; elim snn; intros.
constructor; intros.
red in H4.
inversion H4.
 apply sn_subst_neu; trivial.
 apply sn_abs_inv with x; auto.
 constructor; trivial.

 apply H0; auto.

 apply H2; trivial.
 apply neutral_red with x0; auto with *.
Qed.
