

Require ZFord ZFordcl.
Import ZFnats.
Import IZF.

Lemma isOrd_eqv1 : forall x,
  ZFord.isOrd x -> ZFordcl.isOrd x.
intros.
apply ZFord.isOrd_ind with (2:=H); intros.
apply ZFordcl.isOrd_intro; intros; auto.
apply ZFord.isOrd_trans with b; trivial.
Qed.

Lemma isOrd_equiv : forall x,
  ZFord.isOrd x <-> ZFordcl.isOrd x.
split; intros.
 apply isOrd_eqv1; trivial.

 apply ZFordcl.isOrd_ind; trivial; intros.
  rewrite <- H2; auto.

  apply ZFord.isOrd_intro; intros; auto.
  apply ZFordcl.ClassicOrdinal.ord_incl_le in H4.
   apply le_case in H4.
   destruct H4.
    rewrite H4; trivial.

    apply ZFordcl.isOrd_trans with b; trivial.

   apply isOrd_eqv1; trivial.

   apply ZFordcl.isOrd_inv with y; trivial.
Qed.

Lemma succ_equiv : forall x,
  ZFord.isOrd x -> succ x == ZFord.osucc x.
intros.
apply eq_intro; intros.
 apply le_case in H0; destruct H0.
  rewrite H0; apply ZFord.lt_osucc; trivial.

  apply ZFord.ole_lts.
   apply ZFord.isOrd_inv with x; trivial.

   red; intros.
   apply ZFord.isOrd_trans with z; trivial.

 assert (ZFordcl.isOrd z).
  apply isOrd_eqv1.
  apply ZFord.isOrd_inv with (ZFord.osucc x); auto with *.
 apply ZFord.olts_le in H0.
 apply ZFordcl.ClassicOrdinal.ord_incl_le in H0; trivial.
 apply isOrd_eqv1; trivial.
Qed.

(* Directed set (finite union) *)
Lemma isOrd_dir : forall o, ZFordcl.isOrd o -> ZFord.isDir o.
red; intros.
exists (union2 x y).
 apply ZFordcl.isOrd_union2_lub; trivial.

 split; red; auto using union2_intro1, union2_intro2.
Qed.

Lemma N_omega : N == ZFord.omega.
apply eq_intro; intros.
 elim H using N_ind; intros.
  rewrite <- H1; trivial.

  apply ZFord.zero_omega.

  rewrite succ_equiv.
   apply ZFord.osucc_omega; trivial.

   apply ZFord.isOrd_inv with N; trivial.
   rewrite isOrd_equiv; auto.

 apply ZFord.isOrd_sup_elim in H.
 destruct H.
 apply ZFordcl.isOrd_trans with  (2:=H); auto.
 clear H z.
 induction x; simpl.
  apply zero_typ.

  rewrite <- succ_equiv.
   apply succ_typ; trivial.

   induction x; simpl; auto.
Qed.

Hint Resolve isOrd_eqv1.
