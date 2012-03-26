
Require Import Bool List.
Require Import HFcoc.
Require Import Models GenModelSyntax.

Module HF_Coc_Model <: CC_Model.

Definition X := hf.
Definition inX := In_hf.
Definition eqX := Eq_hf.
Definition eqX_equiv : Equivalence Eq_hf.
split.
 apply eq_hf_refl.
 apply eq_hf_sym.
 apply eq_hf_trans.
Qed.

Notation "x ∈ y" := (inX x y).
Notation "x == y" := (eqX x y).

Lemma in_ext: Proper (eqX ==> eqX ==> iff) inX.
Proof In_hf_morph.

Definition props := props.
Definition app := cc_app.
Definition lam := cc_lam.
Definition prod := cc_prod.

Definition eq_fun (x:X) (f1 f2:X->X) :=
  forall y1 y2, y1 ∈ x -> y1 == y2 -> f1 y1 == f2 y2.

Lemma lam_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  lam x1 f1 == lam x2 f2.
Proof cc_lam_ext.

Lemma app_ext: Proper (eqX ==> eqX ==> eqX) app.
Proof cc_app_morph.

Lemma prod_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  prod x1 f1 == prod x2 f2.
Proof cc_prod_ext.

Lemma prod_intro : forall dom f F,
  eq_fun dom f f ->
  eq_fun dom F F ->
  (forall x, x ∈ dom -> f x ∈ F x) ->
  lam dom f ∈ prod dom F.
Proof cc_prod_intro.

Lemma prod_elim : forall dom f x F,
  eq_fun dom F F ->
  f ∈ prod dom F ->
  x ∈ dom ->
  app f x ∈ F x.
Proof cc_prod_elim.

Lemma impredicative_prod : forall dom F,
  eq_fun dom F F ->
  (forall x, x ∈ dom -> F x ∈ props) ->
  prod dom F ∈ props.
Proof cc_impredicative_prod.

Lemma beta_eq:
  forall dom F x,
  eq_fun dom F F ->
  x ∈ dom ->
  app (lam dom F) x == F x.
Proof cc_beta_eq.

End HF_Coc_Model.

Module Soundness := GenModelSyntax.MakeModel(HF_Coc_Model).

Import Soundness.
Import T.

Fixpoint forall_int_env (e:Env.env) (f:(nat->hf)->bool) {struct e} : bool :=
  match e with
    nil => f (fun _ => empty)
  | T::e' => forall_int_env e'
      (fun i_f => forall_elt (fun x => f (V.cons x i_f)) (int (int_trm T) i_f))
  end.

Definition valid_context (e:Env.env) : bool :=
  negb (forall_int_env e (fun _ => false)).

(*
  Lemma valid_context_ok : forall e,
    valid_context e = true -> forall M M', ~ eq_typ e M M' FALSE.
*)

Require Import Term TypeJudge.

Definition int_clos T := int (int_trm T) vnil.

  Lemma cc_consistency : forall M M', ~ eq_typ nil M M' FALSE.
apply non_provability.
 intros.
 Time compute.
 discriminate.
Qed.


(* Properties not validated by the model *)
Eval vm_compute in (int_clos FALSE). (*consistency *)

(* Properties validated by the model *)
Eval vm_compute in (int_clos TRUE).
Eval vm_compute in (int_clos INAT). (* NAT is inhabited *)
Eval vm_compute in (int_clos EM). (* excluded-middle *)
Eval vm_compute in (int_clos PI). (* proof-irrelevance *)
Eval vm_compute in (int_clos (EXT prop prop)). (* extensionality of funs of Prop -> Prop *)

