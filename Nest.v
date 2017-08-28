Require Export CoqCompat.
(** Showing a nested inductive type operator is isomorphic to
    a W-type.
*)
Set Implicit Arguments.

Parameter A: Type.
Parameter B: A->Type.
Parameter C: A->Type.

(** Binary type operator: X is the parameter of the nested type (and
    the outer inductive type); Y is the nested inductive type.
    It is assumed to be equivalent to a mixed W-type:
   F(X,Y) = \Sigma x:A. (B x -> X) * (C x -> Y)
*)
Record F X Y := mkF { fa : A ; fb : B fa -> X ; fc : C fa -> Y }.
Implicit Arguments mkF [X Y].

(** The nested inductive type *)
Inductive N (X:Type) :=
 CN : F X (N X) -> N X.

(** The container of the inductive type *)
Inductive I :=
 CI : N I -> I.

(** The label of the container: a tree following the structure
   of N, labelled with A. *)
Inductive A' :=
 CA' : forall x:A, (C x -> A') -> A'.
Implicit Arguments CA' [ ].
Definition fst' (x':A') : A := let (a,_) := x' in a.
Definition snd' (x':A') : C (fst' x') -> A' :=
  match x' with CA' _ f => f end.

(** The arity of the container: it is an inductive family with a
   non-uniform parameter.
   It is the set of paths of the tree (of type A'), every node
   has subterms indexed following B. *)
Inductive B' (x':A') :=
| B'nil : B (fst' x') -> B' x'
| B'cons (i:C (fst' x')) (b':B'(snd' x' i)) : B' x'.

(*
Definition g f t (* TI F_X o *) := (* W_F (A'i o) B' X *)
  let a := fst t in (*A*)
  let fb := cc_app (fst (snd t)) in (* B a -> X *)
  let fc := cc_app (snd (snd t)) in (* C a -> Y *)
  let a' := couple a (cc_lam (C a) (fun i => fst (f (fc i)))) in
  let fb' := (* B' a' -> X *)
    B'case (fun l (* B a *) => fb l)
           (fun i b' => cc_app (snd (f (fc i))) b') in
  couple (a'of a (fun i => f(fc i))) (cc_lam (B' (a'of a (fun i =>f(fc i)))) fb').
*)

Parameter X:Type.

(** The equivalent W-type *)
Record W_F X := mkWF { fA' : A' ; fB' : B' fA' -> X }.
Implicit Arguments mkWF [X].

Definition iso_step (Y:Type) (f:Y-> W_F X) (n:F X Y) : W_F X :=
  let x' := CA' (fa n) (fun i => fA' (f (fc n i))) in
  let f' (b:B' x') :=
   match b return X with
   | B'nil l => fb n l
   | B'cons i b' => fB' (f (fc n i)) b'
   end in
  mkWF x' f'.


(** Iso: N --> W-type *)
Fixpoint iso (n:N X) : W_F X :=
  let (nF) := n in iso_step iso nF.


(** For the reverse iso, it is necessary to split the W-type
    in a couple of a A' and a function B'->X
*)
Definition iso'_step Y (f:forall a',(B' a'->X)->Y) (a':A') (fb':B' a' -> X) : F X Y :=
  let x := fst' a' in
  let fb (b:B x) : X := fb' (B'nil _ b) in
  let fc (i:C x) : Y :=
    f (snd' a' i) (fun b'':B'(snd' a' i)=> fb' (B'cons _ i b'')) in
  mkF x fb fc.
Implicit Arguments iso'_step [Y].

Fixpoint iso' (a':A') (fb':B' a' -> X) : N X :=
  CN (iso'_step iso' a' fb').
Implicit Arguments iso' [ ].

Definition iso'' (w:W_F X) : N X := iso' (fA' w) (fB' w).


(* Mixing with inductive types in Prop *)
(*
Inductive Box (T:Type) : Prop := box (x:T).

Inductive NST : Set :=
  CST : Box {X:Type & X->NST} -> NST.
*)
(*
 - { }
 - { 0 }
 - prop
 -
*)