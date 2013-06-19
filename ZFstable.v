
Require Export ZF.

(** Stable functions *)

Definition stable_class (P:set->Prop) (F:set->set) :=
  forall X, (forall x, x∈X -> P x) -> inter (replf X F) ⊆ F (inter X).

Lemma cst_stable_class A K : stable_class K (fun _ => A).
red; red; intros.
apply inter_elim with (1:=H0) (y:=A).
destruct inter_wit with (2:=H0).
 red; red; reflexivity.
rewrite replf_ax; auto.
exists x; auto with *.
Qed.

Lemma id_stable_class K : stable_class K (fun x => x).
red; red; intros.
destruct inter_wit with (2:=H0).
 red; red; auto.
apply inter_intro; eauto.
intros.
apply inter_elim with (1:=H0).
rewrite replf_ax.
2:red; red; auto.
exists y;auto with *.
Qed.

Lemma compose_stable_class K1 K2 F G :
  Proper (eq_set ==> iff) K1 ->
  Proper (incl_set ==> incl_set) F ->
  morph1 G ->
  stable_class K1 F ->
  stable_class K2 G ->
  (forall x, K2 x -> K1 (G x)) ->
  stable_class K2 (fun o => F (G o)).
intros K1m Fm Gm Fs Gs Gty.
red; intros.
transitivity (F (inter (replf X G))).
 red; intros.
 apply Fs.
  intros.
  rewrite replf_ax in H1; auto with *.
  destruct H1.
  rewrite H2; auto.

  rewrite compose_replf; trivial.
   red; red; intros; apply Gm; trivial.

   apply Fmono_morph in Fm.
   red; red; intros; apply Fm; trivial.

 apply Fm.
 apply Gs; trivial.
Qed.

Lemma power_stable K : stable_class K power.
red; red; intros.
apply power_intro; intros.
destruct inter_non_empty with (1:=H0).
rewrite replf_ax in H2.
2:red;red;intros;apply power_morph; trivial.
destruct H2.
apply inter_intro; eauto.
clear H3 H4 H2 x0 x.
intros.
assert (z ∈ power y).
 apply inter_elim with (1:=H0).
 rewrite replf_ax.
 2:red;red;intros;apply power_morph; trivial.
 exists y; auto with *.
rewrite power_ax in H3; auto.
Qed.

Definition stable := stable_class (fun _ => True).
