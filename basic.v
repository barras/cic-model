Require Export Coq.Program.Basics.
Require Export Setoid Morphisms Morphisms_Prop.
Export ProperNotations.

Lemma impl_morph A A' B B' :
  (A <-> A') ->
  (A -> (B <-> B')) ->
  ((A -> B) <-> (A' -> B')).
split; intros.
 rewrite <- H in H2.
 rewrite <- H0; auto.

 rewrite H0; auto.
 rewrite H in H2; auto.
Qed.

Lemma fa_mono : forall A (B B':A->Prop),
  (forall x, impl (B x) (B' x)) -> impl (forall x, B x) (forall x, B' x).
unfold impl; intros; auto.
Qed.

Lemma fa_morph : forall A (B B':A->Prop),
  (forall x, B x <-> B' x) -> ((forall x, B x) <-> (forall x, B' x)).
split; intros.
 rewrite <- H; trivial.
 rewrite H; trivial.
Qed.

(*Instance ex_mono : forall A,
  Proper (pointwise_relation A impl ==> impl) (@ex A).
do 3 red; intros.
destruct H0.
exists x0.
apply H; trivial.
Qed.*)

Instance ex_morph : forall A,
  Proper (pointwise_relation A iff ==> iff) (@ex A).
do 2 red; intros.
split; intros.
 destruct H0.
 exists x0.
 destruct (H x0); auto.

 destruct H0.
 exists x0.
 destruct (H x0); auto.
Qed.

Instance ex2_mono : forall A,
  Proper (pointwise_relation A impl ==> pointwise_relation A impl ==> impl) (@ex2 A).
do 4 red; intros.
destruct H1.
exists x1.
 apply H; trivial.
 apply H0; trivial.
Qed.

Instance ex2_morph : forall A,
  Proper (pointwise_relation A iff ==> pointwise_relation A iff ==> iff) (@ex2 A).
do 2 red; intros.
split; intros.
 destruct H1.
 exists x1.
  destruct (H x1); auto.
  destruct (H0 x1); auto.

 destruct H1.
 exists x1.
  destruct (H x1); auto.
  destruct (H0 x1); auto.
Qed.

Lemma iff_morph : Proper (iff ==> iff ==> iff) iff.
auto with *.
Qed.

Lemma iff_impl : forall A B, iff A B -> impl A B.
destruct 1; auto.
Qed.

(* Should be in stdlib ? *)

Lemma morph_impl_iff1 : forall A (R:A->A->Prop) f,
  Symmetric R ->
  Proper (R ==> impl) f ->
  Proper (R ==> iff) f.
split; intros.
 rewrite <- H1; trivial.
 rewrite H1; trivial.
Qed.

Lemma morph_impl_iff2 : forall A (R:A->A->Prop) B (S:B->B->Prop) f,
  Symmetric R ->
  Symmetric S ->
  Proper (R ==> S ==> impl) f ->
  Proper (R ==> S ==> iff) f.
split; intros.
 apply H1 with x x0; trivial.

 apply H1 with y y0; trivial; symmetry; trivial.
Qed.

Lemma morph_impl_iff3 : forall A B C R S T f,
  @Symmetric A R ->
  @Symmetric B S ->
  @Symmetric C T ->
  Proper (R ==> S ==> T ==> impl) f ->
  Proper (R ==> S ==> T ==> iff) f.
split; intros.
 apply H2 with x x0 x1; trivial.

 apply H2 with y y0 y1; trivial; symmetry; trivial.
Qed.

Lemma morph_impl_iff4 : forall A B C D R S T U f,
  @Symmetric A R ->
  @Symmetric B S ->
  @Symmetric C T ->
  @Symmetric D U ->
  Proper (R ==> S ==> T ==> U ==> impl) f ->
  Proper (R ==> S ==> T ==> U ==> iff) f.
split; intros.
 apply H3 with x x0 x1 x2; trivial.

 apply H3 with y y0 y1 y2; trivial; symmetry; trivial.
Qed.

(* Pb: this is not proved automatically:*)
Goal forall A (eqA:A->A->Prop) P F f g ,
  Equivalence eqA ->
  (*Proper (eqA ==> impl) P ->*)
  Proper (eqA ==> iff) P ->
  Proper (eqA ==> eqA) F ->
  eqA f g ->
  (P (F f) <-> P (F g)).
intros. rewrite H2. reflexivity.
Qed.
(*rewrite H2. fails
red; rewrite H2.  succeeds
*)
