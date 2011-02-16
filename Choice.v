
Definition choice A B :=
  forall (R:A->B->Prop),
  (forall x:A, exists y:B, R x y) ->
  exists f:A->B, forall x:A, R x (f x).

Axiom choice_axiom : forall A B, choice A B.

Definition unique_choice A B (E:B->B->Prop) :=
  forall (R:A->B->Prop),
  (forall x:A, exists y:B, R x y) ->
  (forall x y y', R x y -> R x y' -> E y y') ->
  exists f:A->B, forall x:A, R x (f x).