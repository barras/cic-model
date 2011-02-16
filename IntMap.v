Set Implicit Arguments.

Require Export Compare_dec.

Section Map.

  Variable A : Type.

  Definition eq_map (m1 m2:nat->A) : Prop := forall i, m1 i = m2 i.

  Lemma refl_eq_map : forall m, eq_map m m.
Proof.
red; reflexivity.
Qed.

  Lemma sym_eq_map : forall m1 m2, eq_map m1 m2 -> eq_map m2 m1.
Proof.
unfold eq_map; auto.
Qed.

  Lemma trans_eq_map :
    forall m1 m2 m3, eq_map m1 m2 -> eq_map m2 m3 -> eq_map m1 m3.
Proof.
unfold eq_map; intros; transitivity (m2 i); trivial.
Qed.


  Definition cons_map (x:A) (m:nat->A) (n:nat) : A :=
    match n with
    | O => x
    | (S k) => m k
   end.

  Lemma cons_map_ext : forall x y m1 m2,
    x = y ->
    eq_map m1 m2 ->
    eq_map (cons_map x m1) (cons_map y m2).
Proof.
unfold eq_map; destruct i; simpl; intros; auto.
Qed.

  Definition ins_map (n:nat) (x:A) (m:nat->A) (i:nat) : A :=
     match lt_eq_lt_dec n i with
     | inleft (left _) (* i>n *) => m (pred i)
     | inleft (right _) (* i=n *) => x
     | inright _ (* i<n *) => m i
    end.

  Definition del_map (n k:nat) (m:nat->A) (i:nat) : A :=
    match le_gt_dec k i with
    | left _ => m (plus n i)
    | right_ => m i
   end.

  Lemma del_cons_map :
    forall x n k m,
    eq_map (del_map n (S k) (cons_map x m)) (cons_map x (del_map n k m)). 
Proof.
red; intros.
unfold del_map, cons_map, ins_map.
destruct i; simpl ; auto; intros.
rewrite <- plus_n_Sm.
case (le_gt_dec k i); simpl; trivial.
Qed.

  Lemma del_cons_map2 :
    forall n x m,
    eq_map (del_map (S n) 0 (cons_map x m)) (del_map n 0 m).
Proof.
red;intros.
unfold del_map, cons_map, ins_map.
simpl.
trivial.
Qed.

  Lemma ins_cons_map :
    forall x y k m,
    eq_map (ins_map (S k) y (cons_map x m)) (cons_map x (ins_map k y m)).
Proof.
red;intros.
unfold cons_map, ins_map.
destruct i; auto.
simpl; generalize (lt_eq_lt_dec k i); intros [[H|H]|H]; simpl; trivial.
destruct i; trivial.
inversion H.
Qed.

End Map.

  Hint Resolve refl_eq_map cons_map_ext.
  Hint Immediate sym_eq_map.
