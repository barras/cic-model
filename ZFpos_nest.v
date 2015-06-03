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


