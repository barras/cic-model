Require Import ZFpairs ZFrelations.

(** Extending domains with a set [bot] of "bottom values" *)

Lemma cc_prod_ext_bot bot U V f :
  ext_fun (bot ∪ U) V ->
  (forall x, x ∈ bot -> empty ∈ V x) ->
  (forall x, x ∈ bot -> ~ x ∈ U) ->
  f ∈ (Π x ∈ U, V x) ->
  f ∈ (Π x ∈ bot ∪ U, V x).
intros Vm Vmt Udiscr tyf.
assert (feq : f == cc_lam (bot ∪ U) (cc_app f)).
 apply cc_prod_is_cc_fun in tyf.
 apply eq_set_ax; intros z.
 rewrite cc_lam_def.
 2:do 2 red; intros; apply cc_app_morph; auto with *.
 split; intros.
  destruct (tyf _ H).
  exists (fst z); [apply union2_intro2; trivial|].
  exists (snd z); trivial.
  rewrite <- couple_in_app.
  rewrite H0 in H; trivial.

  destruct H as (x,xty,(y,yty,eqc)).
  rewrite eqc.
  rewrite couple_in_app; trivial.
rewrite feq; apply cc_prod_intro; trivial.
 do 2 red; intros; apply cc_app_morph; auto with *.

 intros.
 apply union2_ax in H; destruct H.
  rewrite cc_app_outside_domain; auto.
  apply cc_prod_is_cc_fun in tyf; eexact tyf.

 apply cc_prod_elim with (1:=tyf); trivial.
Qed.

Definition squ bot f :=
  subset f (fun c => ~ fst c ∈ bot).
Instance squ_morph : morph2 squ.
do 3 red; intros.
apply subset_morph; trivial.
red; intros.
rewrite H; reflexivity.
Qed.

Lemma squ_ax bot f z :
  z ∈ squ bot f <-> z ∈ f /\ ~ fst z ∈ bot.
unfold squ; rewrite subset_ax.
apply and_iff_morphism; auto with *.
split; intros.
 destruct H.
 rewrite H; trivial.

 exists z; auto with *.
Qed.

Lemma squ_eq bot A B f :
  (forall x, x ∈ bot -> ~ x ∈ A) ->
  f ∈ cc_prod (bot ∪ A) B ->
  squ bot f == cc_lam A (cc_app f).
intros.
apply eq_set_ax; intros z.
rewrite squ_ax.
rewrite cc_lam_def.
2:do 2 red; intros; apply cc_app_morph; auto with *.
split; intros.
 destruct H1.
 destruct cc_prod_is_cc_fun with (1:=H0)(2:=H1).
 apply union2_elim in H4; destruct H4.
  contradiction.
 exists (fst z); trivial.
 exists (snd z); trivial.
 rewrite <- couple_in_app.
 rewrite H3 in H1; trivial.

 destruct H1 as (x,xty,(y,yty,eqc)).
 rewrite <- couple_in_app in yty.
 rewrite eqc; split; trivial.
 rewrite fst_def; intro h; apply H in h; auto.
Qed.

Lemma squ_typ bot A B f :
  ext_fun (bot ∪ A) B ->
  (forall x, x ∈ bot -> ~ x ∈ A) ->
  f ∈ (Π x ∈ bot ∪ A, B x) ->
  squ bot f ∈ (Π x ∈ A, B x).
intros.
rewrite squ_eq with (2:=H1); trivial.
apply cc_prod_intro; intros.
 do 2 red; intros; apply cc_app_morph; auto with *.

 do 2 red; intros; apply H; trivial.
 apply union2_intro2; trivial.

 apply cc_prod_elim with (1:=H1).
 apply union2_intro2; trivial.
Qed.

Lemma squ_nmt bot f x :
  ~ x ∈ bot -> cc_app (squ bot f) x == cc_app f x.
intros Hnmt.
apply eq_set_ax; intros z.
rewrite <- couple_in_app.
rewrite squ_ax, fst_def.
rewrite couple_in_app.
split;[destruct 1; trivial|auto].
Qed.
