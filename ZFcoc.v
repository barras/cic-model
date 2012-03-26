
Require Export basic ZF ZFpairs ZFrelations ZFstable.
Require Import ZFgrothendieck.

(** * Impredicativity of props *)

Definition prf_trm := empty.
Definition props := power (singl prf_trm).

Lemma cc_impredicative_prod : forall dom F,
  (forall x, x ∈ dom -> F x ∈ props) ->
  cc_prod dom F ∈ props.
Proof.
unfold props in |- *; intros.
apply power_intro; intros.
apply singl_intro_eq.
unfold prf_trm in |- *.
unfold cc_prod in H0.
elim replf_elim with (2 := H0); clear H0; intros; auto.
rewrite H1; clear H1 z.
apply cc_impredicative_lam.
 do 2 red; intros; apply app_morph; trivial; reflexivity.
intros.
specialize dep_func_elim with (1 := H0) (2 := H1); intro.
specialize H with (1 := H1).
specialize power_elim with (1 := H) (2 := H2); intro.
apply singl_elim; trivial.
Qed.

(** * mapping (meta-level) propositions to props back and forth *)

Definition P2p (P:Prop) := cond_set P (singl prf_trm).
Definition p2P p := prf_trm ∈ p.

Instance P2p_morph : Proper (iff ==> eq_set) P2p.
do 2 red; intros; unfold P2p.
apply cond_set_morph; auto with *.
Qed.

Instance p2P_morph : Proper (eq_set ==> iff) p2P.
do 2 red; intros; apply in_set_morph; auto with *.
Qed.

Lemma P2p_typ : forall P, P2p P ∈ props.
unfold P2p; intros.
apply power_intro; intros.
rewrite cond_set_ax in H; destruct H; trivial.
Qed.

Lemma P2p2P : forall P, p2P (P2p P) <-> P.
unfold P2p, p2P; intros.
rewrite cond_set_ax.
split; intros.
 destruct H; trivial.

 split; trivial; apply singl_intro.
Qed.

Lemma p2P2p : forall p, p ∈ props -> P2p (p2P p) == p.
unfold p2P, P2p; intros.
apply eq_intro; intros.
 rewrite cond_set_ax in H0; destruct H0.
 apply singl_elim in H0.
 rewrite H0; trivial.

 rewrite cond_set_ax; split.
  apply power_elim with (1:=H); trivial.

  apply in_reg with z; trivial.
  apply singl_elim.
  apply power_elim with (1:=H); trivial.
Qed.

Lemma P2p_forall A (B:set->Prop) :
   (forall x x', x ∈ A -> x == x' -> (B x <-> B x')) ->
   P2p (forall x, x ∈ A -> B x) == cc_prod A (fun x => P2p (B x)).
intros.
unfold P2p.
apply eq_intro; intros.
 rewrite cond_set_ax in H0; destruct H0.
 apply singl_elim in H0.
 rewrite H0.
 unfold prf_trm; rewrite <- (cc_impredicative_lam A (fun _ => prf_trm)); auto with *.
 2:intros; reflexivity.
 apply cc_prod_intro; intros; auto with *.
  do 2 red; intros.
  apply cond_set_morph; auto with *.

  rewrite cond_set_ax; split; auto; apply singl_intro.

 rewrite cond_set_ax.
 split.
  rewrite cc_eta_eq with (1:=H0).
  rewrite cc_impredicative_lam.
   apply singl_intro.

   do 2 red; intros.
   apply cc_app_morph; auto with *.

   intros.
   specialize cc_prod_elim with (1:=H0) (2:=H1); intro.
   rewrite cond_set_ax in H2; destruct H2.
   apply singl_elim in H2; trivial.

  intros.
  specialize cc_prod_elim with (1:=H0) (2:=H1); intro.
  rewrite cond_set_ax in H2; destruct H2; trivial.
Qed.

Lemma cc_prod_forall A B :
   ext_fun A B ->
   (forall x, x ∈ A -> B x ∈ props) ->
   cc_prod A B == P2p (forall x, x ∈ A -> p2P (B x)).
intros.
rewrite P2p_forall.
 apply cc_prod_ext; auto with *.
 red; intros.
 rewrite p2P2p; auto.
 apply H0; rewrite <- H2; trivial.

 intros.
 apply in_set_morph; auto with *.
Qed.

Lemma cc_arr_imp A B :
   B ∈ props ->
   cc_arr A B == P2p ((exists x, x ∈ A) -> p2P B).
intros; unfold cc_arr; rewrite cc_prod_forall; intros; auto.
apply P2p_morph.
split; intros; eauto with *.
destruct H1; eauto.
Qed.

(** * Classical propositions: we also have a model for classical logic *)

Definition cl_props := subset props (fun P => ~~p2P P -> p2P P).

Lemma cc_cl_impredicative_prod : forall dom F,
  ext_fun dom F ->
  (forall x, x ∈ dom -> F x ∈ cl_props) ->
  cc_prod dom F ∈ cl_props.
Proof.
intros dom F eF H.
rewrite cc_prod_forall; intros; trivial.
 apply subset_intro; intros.
  apply P2p_typ.

  rewrite P2p2P in H0|-*; intros.
  specialize H with (1:=H1).
  apply subset_elim2 in H; destruct H.
  rewrite H; apply H2.
  intro nx; apply H0; intro h; apply nx.
  rewrite <- H; auto.

 specialize H with (1:=H0); apply subset_elim1 in H; trivial.
Qed.

Lemma cl_props_classical P :
  P ∈ cl_props ->
  cc_arr (cc_arr P empty) empty ⊆ P.
red; intros.
unfold cl_props in H; rewrite subset_ax in H.
destruct H as (Pty,(P',eqP,clP)).
unfold p2P in clP.
rewrite <- eqP in clP; clear P' eqP.
assert (z == empty).
 assert (cc_arr (cc_arr P empty) empty ∈ props).
  apply cc_impredicative_prod; intros.
  apply power_intro; intros.
  apply empty_ax in H1; contradiction.
 specialize power_elim with (1:=H) (2:=H0); intro.
 apply singl_elim in H1; trivial.
rewrite H; apply clP.
intro nP.
assert (cc_lam P (fun x => x) ∈ cc_arr P empty).
 apply cc_arr_intro; auto with *.
  do 2 red; auto.

  intros.
  elim nP.
  specialize power_elim with (1:=Pty) (2:=H1); intro.
  apply singl_elim in H2; rewrite H2 in H1; trivial.
specialize cc_arr_elim with (1:=H0) (2:=H1); intro.
apply empty_ax in H2; contradiction.
Qed.


(** Auxiliary stuff for strong normalization proof: every type
   contains the empty set. 
 *)

(* The operator that adds the empty set to a type. *)
Definition cc_dec x := singl empty ∪ x.

Instance cc_dec_morph : morph1 cc_dec.
unfold cc_dec; do 2 red; intros.
rewrite H; reflexivity.
Qed.

Lemma cc_dec_ax : forall x z,
  z ∈ cc_dec x <-> z == empty \/ z ∈ x.
unfold cc_dec; intros.
split; intros.
 apply union2_elim in H; destruct H; auto.
 apply singl_elim in H; auto.

 destruct H.
  apply union2_intro1; rewrite H; apply singl_intro.

  apply union2_intro2; trivial.
Qed.


Lemma cc_dec_prop :
    forall P, P ∈ cc_dec props -> cc_dec P ∈ props.
intros.
rewrite cc_dec_ax in H.
apply power_intro; intros.
rewrite cc_dec_ax in H0.
destruct H0;[rewrite H0;apply singl_intro|].
destruct H; [rewrite H in H0; apply empty_ax in H0;contradiction|].
apply power_elim with (1:=H); trivial.
Qed.


Lemma cc_dec_cl_prop :
    forall P, P ∈ cc_dec cl_props -> cc_dec P ∈ cl_props.
intros.
apply subset_intro.
apply cc_dec_prop.
rewrite cc_dec_ax in H|-*; destruct H; auto.
apply subset_elim1 in H; auto.

intros _.
red; rewrite cc_dec_ax; left; reflexivity.
Qed.


(** #<a name="EquivTTColl"/># *)
(** * Correspondance between ZF universes and (Coq + TTColl) universes *)

Section Universe.

 (* A grothendieck universe... *)
  Hypothesis U : set.
  Hypothesis Ugrot : grot_univ U.

(*
Section Equiv_TTRepl.

  Hypothesis cc_set : set.
  Hypothesis cc_eq_set : set -> set -> Prop.
  Hypothesis cc_eq_set_morph : Proper (eq_set==>eq_set==>iff) cc_eq_set.
  Hypothesis cc_set_incl_U : cc_set ⊆ U.

Lemma cc_ttrepl A R :
  Proper (eq_set ==> eq_set ==> iff) R ->
  (* A : Ti *)
  A ∈ U ->
  (* type of R + existence assumption *)
  (forall x, x ∈ A -> exists2 y, y ∈ cc_set & R x y) ->
  (forall x y y', x ∈ A -> R x y -> (R x y' <-> cc_eq_set y y')) ->
  (* exists f:A->set, *)
  exists2 f, f ∈ cc_arr A cc_set &
    (* forall x:A, R x (f i) *)
    forall x, x ∈ A -> R x (cc_app f x).

(forall x in A, exists y ∈ A, exists g:y->cc_set, R x (cc_sup y g))

R' x y := (z ∈ y <-> R x z)  (y = ens de cc_set -> ⊆ U)

End Equiv_TTRepl.
*)

Section Equiv_ZF_CIC_TTColl.

(** We assume now that U is a *ZF* universe (not just IZF),
   so it is closed by collection. *)

  Hypothesis coll_axU : forall A (R:set->set->Prop), 
    A ∈ U ->
    (forall x x' y y', in_set x A ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    exists2 B, B ∈ U & forall x, in_set x A -> (exists2 y, y ∈ U & R x y) ->
       exists2 y, in_set y B & y ∈ U /\ R x y.

  (** The inductive type of sets (cf Ens.set) and its elimination rule *)
  Hypothesis cc_set : set.

Section SetInU.

  (** Here we assume the elimination rule of the Ens.set inductive type *)
  Hypothesis cc_set_ind :
    forall P : set -> Prop,
    (forall y X f, morph1 f ->
     (* y ∈ sigma X:U. U->Ens.set *)
     y == couple X (cc_lam X f) ->
     X ∈ U ->
     (forall x, x ∈ X -> f x ∈ cc_set) ->
     (* induction hypothesis *)
     (forall x, x ∈ X -> P (f x)) ->
     P y) ->
    forall x, x ∈ cc_set -> P x.

(* Sets formed by indexes in U belong to U: *)
Lemma cc_set_incl_U : cc_set ⊆ U.
red; intros.
apply cc_set_ind with (2:=H); intros.
rewrite H1; clear H1 y.
apply G_couple; trivial.
apply G_cc_lam; auto.
Qed.

End SetInU.

  (** All we need to know about cc_set is that it's included in U, so the ttcoll
     axiom is really an instance of collection for universe U. *)
  Hypothesis cc_set_incl_U : cc_set ⊆ U.

(** We prove that the model will validate TTColl (Ens.ttcoll).
   This formulation heavily uses the reification of propositions of the model
   as Coq's Prop elements. *)
Lemma cc_ttcoll A R :
  Proper (eq_set ==> eq_set ==> iff) R ->
  (* A : Ti *)
  A ∈ U ->
  (* type of R + existence assumption *)
  (forall x, x ∈ A -> exists2 y, y ∈ cc_set & R x y) ->
  (* exists X:Ti, *)
  exists2 X, X ∈ U &
    (* exists f:X->set, *)
    exists2 f, f ∈ cc_arr X cc_set &
    (* forall x:A, exists i:X, R x (f i) *)
    forall x, x ∈ A -> exists2 i, i ∈ X & R x (cc_app f i).
intros.
destruct coll_axU with (A:=A) (R:=fun x y => y ∈ cc_set /\ R x y) as (B,HB);
  trivial.
 intros.
 rewrite <- H3; rewrite <- H4; trivial.

 pose (B':= B ∩ cc_set).
 exists B'.
  apply G_incl with B; trivial.
  apply inter2_incl1.
 exists (cc_lam B' (fun x => x)).
  apply cc_arr_intro; intros.
   do 2 red; intros; trivial.
   revert H3; apply inter2_incl2.
 intros.
 destruct H2 with (1:=H3) as (y,yB,(yU,(ys,yR))).
  destruct H1 with (1:=H3).
  exists x0; auto.

  exists y.
   unfold B'; rewrite inter2_def; auto.

   rewrite cc_beta_eq; trivial.
    do 2 red; auto.

    unfold B'; rewrite inter2_def; auto.
Qed.

End Equiv_ZF_CIC_TTColl.

End Universe.
