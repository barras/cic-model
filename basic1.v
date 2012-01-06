Require Import Omega.

Lemma succ_max_distr : forall n m, S (max n m) = max (S n) (S m).
induction n; destruct m; simpl; reflexivity.
Qed.

Lemma max_split1 : forall x y z, z < x -> z < max x y.
induction x; simpl; intros.
 apply False_ind; omega.

 destruct y; trivial.
  destruct z; try omega.
   assert (z < x) by omega. specialize IHx with (1:=H0) (y:=y). omega.
Qed.

Lemma max_split2 : forall x y z, z < y -> z < max x y.
induction x; simpl; intros; trivial.
 destruct y; trivial.
  apply False_ind; omega.
 
  destruct z; try omega.
   assert (z < y) by omega. specialize IHx with (1:=H0). omega.
Qed.

Lemma max_comb : forall x y z, z < max x y -> z < x \/ z < y.
induction x; simpl; intros.
 right; trivial.

 destruct y.
  left; trivial.

  destruct z.
   left; omega.

   assert (z < max x y) by omega.
   specialize IHx with (1:=H0). destruct IHx; [left | right]; omega.
Qed.