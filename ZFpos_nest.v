Require Import ZF.
Require Import ZFpairs ZFrelations ZFord ZFfix ZFlimit ZFiso.
Require Import ZFnest ZFspos.

(* Simply nested inductive *)

Section NestedInductive.

  Variable Fop : set -> set -> set.
  Hypothesis Fop_mono : Proper (incl_set==>incl_set==>incl_set) Fop.

(** F(X,Y): Y is the nested type with (uniform) parameter X *)

(* F(X,Y) iso { x:A | B x -> X & C x -> Y } *)
Hypothesis A : set.
Hypothesis B : set -> set.
Hypothesis C : set -> set.
Hypothesis Bm : morph1 B.
Hypothesis Cm : morph1 C.
Hypothesis h : set -> set.
Hypothesis hm : morph1 h.
Hypothesis hiso : forall X Y, iso_fun (Fop X Y) (F A B C X Y) h.

Definition nest_pos (o:set) : positive :=
  mkPositive (fun X => TI (fun Y => Fop X Y) o) (A'i A C o) (B' A B C) (nest_trad A B C h o).

Lemma isPos_nest o :
  isOrd o ->
  isPositive (nest_pos o).
constructor.
 do 2 red; intros.
 simpl.
 apply TI_op_mono; auto with *; apply Fmono_morph;
   do 2 red; intros; apply Fop_mono; auto with *.

 do 2 red; intros; simpl.
 apply B'm; trivial.

 simpl; intros.
 apply nest_iso_it; trivial.
 intros; apply Fop_mono.
 reflexivity.
Qed.

End NestedInductive.

Print Assumptions isPos_nest.



(* Reverse order! *)
(*
Definition g f t (* W_F A' B' X*) := (* N X *)
  let a' := fst t in
  let b' := snd t in
  let x := fst a' in
  let fb b := cc_app b' (Cons b Nil) in
  let fc i :=
    f  (couple (cc_app (snd a') i) (cc_lam (B'(cc_app(snd a') i)) (fun b'' =>
         cc_app b' (Cons i b'')))) in
  couple x (couple (cc_lam (B x) fb) (cc_lam (C x) fc)).

Lemma giso X f o:
  isOrd o ->
  iso_fun (W_F (A'i o) B' X) (TI (fun Y=>F X Y) o) f ->
  iso_fun (W_F (W_F A C (A'i o)) B' X) (F X (TI (fun Y=>F X Y) o)) (g f).
*)

End NestedInductive.

(*
Lemma W_F_inj :
  (forall X, iso_fun (W_F A B X) (W_F A' B' X) f) ->
  let f1 := fun a => fst(f (*X=1*) (couple a (cc_lam (B a) (fun _ => empty)))) in
  iso_fun A A' () /\
  (forall X x, a ∈ A -> iso_fun (cc_arr (B x) X) (cc_arr (B' (f1 x)) X) (fun
)).
*)
(*
Section VariableSeparation.

Variable F : set -> set -> set.
Hypothesis Fmono : Proper (incl_set==>incl_set==>incl_set) F.

(* W-type in X *)
Variable A : set -> set.
Variable B : set -> set -> set.
Variable fX : set -> set -> set.

Let pX Y := mkPositive (fun X => F X Y) (A Y) (B Y) (fX Y).

Hypothesis FposX : forall Y, isPositive (pX Y).

(* W-type in Y *)
Variable A' : set -> set.
Variable B' : set -> set -> set.
Variable fY : set -> set -> set.

Let pY X := mkPositive (fun Y => F X Y) (A' X) (B' X) (fY X).

Hypothesis FposY : forall X, isPositive (pY X).

(* 
F(X,Y) = A(Y) * (B(Y)->X) = A'(X) * (B'(X)->Y)
F(X,1) = A(1) * (B(1)->X) = A'(X)
-->
F(X,Y) = A(1) * (B(1)->X) * (B'(1)->Y) ?
 *)

Definition A0 := A (singl empty).
Definition B0 := B (singl empty).


Definition iso1 X p :=
  couple p (cc_lam (B' X p) (fun _ => empty)).

Lemma iso_fun1 X :
  iso_fun (A' X) (W_F (A' X) (B' X) (singl empty)) (iso1 X).
constructor; intros.
 admit.

 red; intros.
 unfold iso1.
 apply W_F_intro; intros; auto with *.
  do 2 red; intros; apply (w2m (pY X)); auto with *.
  apply singl_intro.

 apply couple_injection in H1; destruct H1; trivial.

 apply W_F_elim in H.
 2:apply (w2m (pY X)); trivial.
 destruct H as (?,(?,?)).
 exists (fst y); trivial.
 unfold iso1.
 apply (@transitivity) with (3:=symmetry H1); auto with *.
 apply couple_morph; auto with *.
 apply cc_lam_ext; auto with *.
 red; intros.
 rewrite <- H3; symmetry; apply singl_elim; auto.
Qed.

Definition iso2 X Y :=
  comp_iso (iso_inv (F X Y) (wf (pY X))) (wf (pX Y)).

Lemma iso_fun2 X Y :
  iso_fun (W_F (A' X) (B' X) Y) (W_F (A Y) (B Y) X) (iso2 X Y).
eapply iso_fun_trans.
 apply (iso_fun_sym (w_iso _ (FposY X) Y)).
 apply (w_iso _ (FposX Y) X).
Qed.



Lemma if1 X :
  {f:_ | iso_fun (A' X) (W_F A0 B0 X) f }.
econstructor.
eapply iso_fun_trans.
 apply iso_fun1.

 apply iso_fun2.
Defined.

(* coe :  A0 --> A' (singl empty) *)
Definition coe i := iso_inv (A' (singl empty)) (proj1_sig (if1(singl empty)))
   (couple i (cc_lam (B0 i) (fun _ => empty))).
Definition C0 i := B' (singl empty) (coe i).

(*
Lemma iso_fun1 : forall X,
  iso_fun (A' X) (W_F (A (singl empty)) (B (singl empty)) X)
*)

Lemma Fdef : forall X Y,
  {f:_|
  iso_fun (F X Y) (sigma A0 (fun x => prodcart (cc_arr (B0 x) X) (cc_arr (C0 x) Y))) f}. 
intros.
econstructor.
eapply iso_fun_trans.
 apply (w_iso _ (FposY X)).
 simpl.
eapply iso_fun_trans.
 unfold W_F.
 apply sigma_iso_fun_morph with (4:=proj2_sig (if1 X)).
Focus 5.
eapply iso_fun_trans.
 apply iso_fun_sym.
 apply iso_sigma_sigma.
Focus 3.
 apply eq_iso_fun.
  apply sigma_ext;[reflexivity|].
  intros.
  rewrite sigma_nodep.
  apply sigma_ext; intros.
   apply cc_arr_morph; auto with *.
   apply (w2m _ (FposX (singl empty))); trivial.

assert (C0m : ext_fun A0 C0) by admit.
   rewrite <- (C0m _ _ H H0).
   apply cc_arr_morph.
    reflexivity.
    reflexivity.
 instantiate (1:=fun x=>x); reflexivity.
Unfocus.
Focus 4.
simpl; intros.
unfold C0.
Show Existentials.
(*
[X : set
 Y : set
 x : set |- set -> set] 
iso_fun (B X x -> Y) (B' (singl empty) (coe (fst x')) -> Y1) ?
*)

apply eq_iso_fun with (f:=fun x=>x); auto with *.
apply cc_arr_morph; auto with *.
unfold C0.
generalize (w2m _ (FposY (singl empty))).
simpl.
Abort.

End VariableSeparation.
*)