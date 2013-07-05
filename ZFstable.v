
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

Lemma union2_stable_disjoint K F G :
  morph1 F ->
  morph1 G ->
  stable_class K F ->
  stable_class K G ->
  (forall X Y z, K X -> K Y -> z ∈ F X -> z ∈ G Y -> False) ->
  stable_class K (fun X => F X ∪ G X).
intros Fm Gm Fs Gs disj.
intros X KX z zty.
destruct inter_wit with (2:=zty) as (w,winX).
 do 2 red; intros.
 rewrite H; reflexivity.
assert (forall x, x ∈ X -> z ∈ F x ∪ G x).
 intros.
 apply inter_elim with (1:=zty).
 rewrite replf_ax.
  exists x; auto with *.

  red; red; intros.
  rewrite H1; reflexivity.
clear zty.
assert (z ∈ F w ∪ G w) by auto.
apply union2_elim in H0; destruct H0.
 apply union2_intro1.
 apply Fs; auto.
 apply inter_intro.
  intros.
  rewrite replf_ax in H1.
  2:red;red;intros;apply Fm; trivial.
  destruct H1.
  rewrite H2; clear H2 y.
  assert (z ∈ F x ∪ G x) by auto.
  apply union2_elim in H2; destruct H2; trivial.
  elim disj with (3:=H0) (4:=H2); auto.

  exists (F w).
  rewrite replf_ax.
  2:red;red;intros;apply Fm;trivial.
  exists w; auto with *.

 apply union2_intro2.
 apply Gs; auto.
 apply inter_intro.
  intros.
  rewrite replf_ax in H1.
  2:red;red;intros;apply Gm; trivial.
  destruct H1.
  rewrite H2; clear H2 y.
  assert (z ∈ F x ∪ G x) by auto.
  apply union2_elim in H2; destruct H2; trivial.
  elim disj with (3:=H2) (4:=H0); auto.

  exists (G w).
  rewrite replf_ax.
  2:red;red;intros;apply Gm;trivial.
  exists w; auto with *.
Qed.


Definition stable := stable_class (fun _ => True).
