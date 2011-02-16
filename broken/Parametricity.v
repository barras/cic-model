
Require Import Arith.
Require Export Compare_dec.
Require Export Relations.

Hint Resolve t_step rt_step rt_refl: core.
Hint Unfold transp: core.

Inductive ty :=
| Tvar (v:nat)
| Tarr (a b:ty)
| Tall (_:ty).

Inductive term : Set :=
| Ref : nat -> term
| Abs : term -> term
| App : term -> term -> term.


(* Model *)

Parameter D : Type.
Parameter Dapp : D -> D -> D.
Parameter Dlam : (D -> D) -> D.

(* Beware: only for *continuous* f... *)
Parameter Dbeta : forall f x, Dapp (Dlam f) x = f x.

(* Model construction *)

Require Import VarMap.
Require Export Setoid Morphisms List.

(* Term semantics *)
Module Deq.
  Definition t := D.
  Definition eq := @eq D.
  Definition eq_equiv : Equivalence eq := eq_equivalence.
  Existing Instance eq_equiv.
End Deq.
Module DM := VarMap.Make(Deq).

Definition trm := DM.map -> D.

Definition ref n : trm := fun j => j n.
Definition app (u v:trm) : trm :=
  fun j => Dapp (u j) (v j).
Definition abs (b:trm) : trm :=
  fun j => Dlam (fun x => b (DM.cons x j)).
Definition lift n (t:trm) : trm :=
  fun j => t (DM.shift n j).
Definition sub (arg body: trm) : trm :=
  fun i => body (DM.cons (arg i) i).

Axiom ext : forall A B (f g:A->B), (forall x, f x = g x) -> f = g.
Axiom prop_ext : forall A B:Prop, (A <-> B) -> A = B.

Module CommonSemantics.

Parameter U : Type.
Parameter Uarr : U -> U -> U.
Parameter Uinter : (U -> U) -> U.

Parameter Del : U -> D -> Prop.
Parameter Dapp_ty : forall t1 t2 f x,
  Del (Uarr t1 t2) f -> Del t1 x -> Del t2 (Dapp f x).
Parameter Dlam_ty : forall t1 t2 f,
 (forall x, Del t1 x -> Del t2 (f x)) -> Del (Uarr t1 t2) (Dlam f).

Parameter Uinter_def : forall F v, (forall x, Del (F x) v) <-> Del (Uinter F) v.

Module Ueq.
  Definition t := U.
  Definition eq := @eq U.
  Definition eq_equiv : Equivalence eq := eq_equivalence.
  Existing Instance eq_equiv.
End Ueq.
Module UM := VarMap.Make(Ueq).

Definition sty := UM.map -> U.

Definition tvar n : sty := fun i => i n.
Definition tarr (t1 t2: sty) : sty :=
  fun i => Uarr (t1 i) (t2 i).
Definition tall (t:sty) : sty :=
  fun i => Uinter (fun x => t (UM.cons x i)).
Definition tlift n (t:sty) : sty :=
  fun i => t (UM.shift n i).
Definition tsub (arg body: sty) : sty :=
  fun i => body (UM.cons (arg i) i).

Definition val_ok (e:list sty) i j :=
  forall n ty, nth_error e n = value ty ->
  Del (ty i) (j n).

Lemma val_ok_cons : forall e i j x ty,
  val_ok e i j ->
  Del (ty i) x ->
  val_ok (ty::e) i (DM.cons x j).
red; intros.
destruct n as [|n]; simpl in *.
 injection H1; clear H1; intros; subst ty0.
 trivial.

 apply H; trivial.
Qed.

Lemma val_ok_thin : forall e i j x,
  val_ok e i j ->
  val_ok (map (tlift 1) e) (UM.cons x i) j.
unfold val_ok; intros.
assert (exists2 t, nth_error e n = value t & ty0 = tlift 1 t).
 clear i j x H.
 revert e H0; induction n; destruct e; simpl; intros; try discriminate.
  injection H0; exists s; auto.

  specialize IHn with (1:=H0).
  destruct IHn.
  exists x; trivial.
destruct H1.
rewrite H2.
unfold tlift.
replace (UM.shift 1 (UM.cons x i)) with i; auto.
apply ext; intro.
reflexivity.
Qed.


Definition sjudge (e:list sty) (M:trm) (T:sty) :=
  forall i j, val_ok e i j -> Del (T i) (M j).

Lemma ty_ref : forall (e:list sty) n ty,
  nth_error e n = value ty ->
  sjudge e (ref n) ty.
red; intros.
apply H0; trivial.
Qed.

Lemma ty_app : forall e u v t1 t2,
  sjudge e u (tarr t1 t2) ->
  sjudge e v t1 ->
  sjudge e (app u v) t2.
unfold sjudge; intros.
apply Dapp_ty with (t1 i); auto.
apply H; trivial.
Qed.

Lemma ty_abs : forall e m ty1 ty2,
  sjudge (ty1::e) m ty2 -> 
  sjudge e (abs m) (tarr ty1 ty2).
unfold sjudge; intros.
apply Dlam_ty; intros.
apply H with (j:=DM.cons x j).
apply val_ok_cons; trivial.
Qed.

Lemma ty_gen : forall e m t,
  sjudge (List.map (tlift 1) e) m t ->
  sjudge e m (tall t).
unfold sjudge; intros.
unfold tall.
rewrite <- Uinter_def; intros.
apply H.
apply val_ok_thin; trivial.
Qed.

Lemma ty_spec : forall e m u ty,
  sjudge e m (tall u) ->
  sjudge e m (tsub ty u).
unfold sjudge; intros.
specialize H with (1:=H0).
unfold tall in H.
rewrite <- Uinter_def in H.
unfold tsub; trivial.
Qed.

End CommonSemantics.

Module RelSemantics.


  Definition R := D -> D -> Prop.
  Definition Rel (r:R) : D -> D -> Prop := r.

  Definition Rarr (t1 t2:R) : R :=
    fun f f' => forall x x', Rel t1 x x' -> Rel t2 (Dapp f x) (Dapp f' x').

  Definition Rall (t:R->R) : R :=
    fun f f' => forall x, Rel (t x) f f'.


Module Req.
  Definition t := R.
  Definition eq := @eq R.
  Definition eq_equiv : Equivalence eq := eq_equivalence.
  Existing Instance eq_equiv.
End Req.
Module RM := VarMap.Make(Req).

Definition sty := RM.map -> R.

Definition tvar n : sty := fun i => i n.
Definition tarr (t1 t2: sty) : sty :=
  fun i => Rarr (t1 i) (t2 i).
Definition tall (t:sty) : sty :=
  fun i => Rall (fun x => t (RM.cons x i)).
Definition tlift n (t:sty) : sty :=
  fun i => t (RM.shift n i).
Definition tsub (arg body: sty) : sty :=
  fun i => body (RM.cons (arg i) i).

Definition val_ok (e:list sty) i j j' :=
  forall n ty, nth_error e n = value ty ->
  Rel (ty i) (j n) (j' n).

Lemma val_ok_cons : forall e i j j' x x' (ty:sty),
  val_ok e i j j' ->
  Rel (ty i) x x' ->
  val_ok (ty::e) i (DM.cons x j) (DM.cons x' j').
red; intros.
destruct n as [|n]; simpl in *.
 injection H1; clear H1; intros; subst ty0.
 trivial.

 apply H; trivial.
Qed.

Lemma val_ok_thin : forall e i j j' x,
  val_ok e i j j' ->
  val_ok (map (tlift 1) e) (RM.cons x i) j j'.
unfold val_ok; intros.
assert (exists2 t, nth_error e n = value t & ty0 = tlift 1 t).
 clear i j x H.
 revert e H0; induction n; destruct e; simpl; intros; try discriminate.
  injection H0; exists s; auto.

  specialize IHn with (1:=H0).
  destruct IHn.
  exists x; trivial.
destruct H1.
rewrite H2.
unfold tlift.
replace (RM.shift 1 (RM.cons x i)) with i; auto.
apply ext; intro.
reflexivity.
Qed.


Definition sjudge (e:list sty) (M:trm) (T:sty) :=
  forall i j j', val_ok e i j j' -> Rel (T i) (M j) (M j').

Lemma ty_ref : forall (e:list sty) n ty,
  nth_error e n = value ty ->
  sjudge e (ref n) ty.
red; intros.
apply H0; trivial.
Qed.

Lemma ty_app : forall e u v t1 t2,
  sjudge e u (tarr t1 t2) ->
  sjudge e v t1 ->
  sjudge e (app u v) t2.
unfold sjudge; intros.
unfold Rel, tarr, Rarr in H.
unfold app.
apply H; auto.
Qed.

Lemma ty_abs : forall e m ty1 ty2,
  sjudge (ty1::e) m ty2 -> 
  sjudge e (abs m) (tarr ty1 ty2).
unfold sjudge; intros.
unfold Rel, tarr, Rarr; intros.
unfold abs.
do 2 rewrite Dbeta.
apply H.
apply val_ok_cons; trivial.
Qed.

Lemma ty_gen : forall e m t,
  sjudge (List.map (tlift 1) e) m t ->
  sjudge e m (tall t).
unfold sjudge; intros.
unfold Rel, tall, Rall; intros.
apply H.
apply val_ok_thin; trivial.
Qed.

Lemma ty_spec : forall e m u ty,
  sjudge e m (tall u) ->
  sjudge e m (tsub ty u).
unfold sjudge; intros.
specialize H with (1:=H0).
unfold Rel, tall, Rall in H.
unfold tsub; trivial.
Qed.

End RelSemantics.


Module Beq.
Definition t := bool.
Definition eq := @eq bool.
Definition eq_equiv : Equivalence eq := eq_equivalence.
Existing Instance eq_equiv.
End Beq.
Module B := VarMap.Make(Beq).

Record fenv := {
  tenv : list trm;
  impl : B.map
}.

Definition tinj e :=
  Build_fenv e (B.nil false).

Definition push_var e T :=
  Build_fenv (T::tenv e) (B.cons false (impl e)).

Definition push_ivar e T :=
  Build_fenv (T::tenv e) (B.cons true (impl e)).

Module ICocSemantics.

  Parameter Uprop : Prop -> D.
  Parameter Uprop_inj : forall P Q, Uprop P = Uprop Q -> P = Q.

  Definition Uprop_inv x := exists2 P, P & x = Uprop P.
  Lemma Uprop_has_inv : forall P, Uprop_inv (Uprop P) = P.
intros.
unfold Uprop_inv.
apply prop_ext.
split; intros. (* introduce variable capture... *)
 destruct H.
 apply Uprop_inj in H0; rewrite H0; trivial.

 exists P; trivial.
Qed.

  Definition mkSet (P:D->Prop) : D :=
    Dlam (fun x => Uprop (P x)).

  Definition El (t x:D) := Uprop_inv (Dapp t x).

  Lemma Set_beta : forall (R:D->Prop) x,
    El (mkSet R) x = R x.
unfold El, mkSet; intros.
rewrite Dbeta.
apply Uprop_has_inv.
Qed.


  Definition Dprop := mkSet
    (fun x => exists P:Prop, x = mkSet(fun y => y = Uprop False /\ P)).

  Definition Dprod A F :=
    mkSet (fun f => forall x, El A x -> El (F x) (Dapp f x)).


  Definition prop : trm := fun _ => Dprop.

  Definition prod (A B:trm) : trm :=
    fun i => Dprod (A i) (fun x => B (DM.cons x i)).

(* OK  model is inconsistent (models Type:Type)
  Definition Dkind := mkSet (fun _ => True).

Lemma sysU : El Dkind Dkind.
unfold Dkind at 1.
rewrite Set_beta.
trivial.
Qed.

Lemma has_fix : forall F:D->D, exists x, F x = x.
intros.
pose (fx :=
  let dlt := Dlam (fun x => F (Dapp x x)) in
  Dapp dlt dlt).
exists fx.
unfold fx at 2; simpl.
rewrite Dbeta.
reflexivity.
Qed.

Definition Dnot x := Uprop (forall P:Prop, x = Uprop P -> ~P).
(* Rk: Dnot non monotonic, maps bottom to a valid prop but maps
   a valid prop to an invalid prop *)

Lemma paradox : False.
destruct (has_fix Dnot).
assert (Dnot x = Uprop False).
 unfold Dnot; apply f_equal; apply prop_ext.
 split; intros; try contradiction.
 generalize H0.
 apply H0.
 symmetry; assumption.
assert (Dnot x = Uprop True).
 rewrite <- H.
 unfold Dnot at 1; apply f_equal; apply prop_ext.
 split; intros; trivial.
 red; intros.
 rewrite H0 in H2; apply Uprop_inj in H2; rewrite H2; trivial.
rewrite H0 in H1; apply Uprop_inj in H1.
rewrite H1; trivial.
Qed.
*)

(* Additional judgments for fix body *)
Definition val_ok (e:fenv) i :=
    forall n ty,
    nth_error (tenv e) n = value ty ->
    El (ty (DM.shift (S n) i)) (i n).

Definition val_mono (e:fenv) (i i':DM.map) :=
  forall n,
  if impl e n then True
  else i n = i' n.

Lemma val_ok_cons : forall e i x (ty:trm),
  val_ok e i ->
  El (ty i) x ->
  val_ok (push_var e ty) (DM.cons x i).
red; intros.
destruct n as [|n]; simpl in *.
 injection H1; clear H1; intros; subst ty0.
 replace (DM.shift 1 (DM.cons x i)) with i; auto.
 apply ext; reflexivity.

 change (DM.shift (S (S n)) (DM.cons x i)) with (DM.shift (S n) i).
 apply H; trivial.
Qed.

Lemma val_mono_cons : forall e i i' x (ty:trm),
  val_mono e i i' ->
  val_mono (push_var e ty) (DM.cons x i) (DM.cons x i').
red; intros.
destruct n as [|n]; simpl in *; auto.
apply H.
Qed.
(*
Lemma val_ok_thin : forall e i i' x x',
  val_ok e i i' ->
  val_ok (map (lift 1) e) (DM.cons x i) (DM.cons x' i').
unfold val_ok; intros.
assert (exists2 t, nth_error e n = value t & ty0 = lift 1 t).
 clear i i' x x' H.
 revert e H0; induction n; destruct e; simpl; intros; try discriminate.
  injection H0; exists t; auto.

  specialize IHn with (1:=H0).
  destruct IHn.
  exists x; trivial.
destruct H1.
rewrite H2.
unfold lift.
replace (DM.shift 1 (DM.shift (S n) (DM.cons x i)))
 with (DM.shift (S n) i); auto.
replace (RM.shift 1 (RM.cons x i)) with i; auto.
apply ext; intro.
reflexivity.
Qed.
*)

Definition sjudge (e:fenv) (M T:trm) :=
  (forall i i', val_ok e i -> val_mono e i i' -> El (T i) (M i')) /\
  (forall i i', val_mono e i i' -> M i = M i').

Lemma ty_ref : forall e n ty,
  nth_error (tenv e) n = value ty ->
  impl e n = false ->
  sjudge e (ref n) (lift (S n) ty).
split; intros.
 red in H1,H2.
 specialize H2 with n.
 rewrite H0 in H2.
 apply H1 in H.
 rewrite H2 in H.
 trivial.

 unfold ref.
 red in H1.
 specialize H1 with n.
 rewrite H0 in H1; trivial.
Qed.


Lemma ty_app : forall e u v A B,
  sjudge e u (prod A B) ->
  sjudge e v A ->
  sjudge e (app u v) (sub v B).
split; intros.
 destruct H; destruct H0.
 specialize H with (1:=H1) (2:=H2).
 specialize H0 with (1:=H1) (2:=H2).
 unfold prod, Dprod in H.
 rewrite Set_beta in H.
 unfold sub, app.
 rewrite H4 with (1:=H2).
 auto.

 destruct H; destruct H0.
 unfold app.
 rewrite H2 with (1:=H1); rewrite H3 with (1:=H1); trivial.
Qed.

Lemma ty_abs : forall e m T U,
  sjudge (push_var e T) m U ->
  sjudge e (abs m) (prod T U).
split; intros.
 destruct H.
 unfold prod, Dprod; rewrite Set_beta.
 intros.
 assert (val_mono (push_var e T) (DM.cons x i) (DM.cons x i')).
  apply val_mono_cons; trivial.
 unfold abs.
 rewrite Dbeta.
 apply H; auto.
 apply val_ok_cons; auto.

 unfold abs.
 apply f_equal.
 apply ext; intros.
 destruct H.
 apply H1.
 apply val_mono_cons; auto.
Qed.

Definition is_kind e (T T':trm) :=
  forall i i', val_mono e i i' -> T i = T' i'.

Lemma ty_conv : forall ivars e m m' T T',
  sjudge ivars e m m' T ->
  is_kind (B.nil false) e T T' ->
  sjudge ivars e m m' T'.
unfold is_kind, sjudge; intros.
assert (val_ok (B.nil false) e i i).
 red; intros.
 admit.
specialize H0 with (1:=H2).
rewrite <- H0; auto.
Qed.

Lemma conv_beta : forall m v, app (abs m) v = sub v m.
intros.
apply ext; intro i.
unfold app, abs, sub.
rewrite Dbeta.
trivial.
Qed.

End CocSemantics.



Module CocRelSemantics.

  Parameter Uprop : Prop -> D.
  Parameter Uprop_inj : forall P Q, Uprop P = Uprop Q -> P = Q.

  Definition Uprop_inv x := exists2 P, P & x = Uprop P.
  Lemma Uprop_has_inv : forall P, Uprop_inv (Uprop P) = P.
intros.
unfold Uprop_inv.
apply prop_ext.
split; intros. (* introduce variable capture... *)
 destruct H.
 apply Uprop_inj in H0; rewrite H0; trivial.

 exists P; trivial.
Qed.

  Definition mkRel (R:D->D->Prop) : D :=
    Dlam (fun x => Dlam (fun y => Uprop (R x y))).

  Definition Rel (r x y:D) := Uprop_inv (Dapp (Dapp r x) y).

  Lemma Rel_beta : forall (R:D->D->Prop) x y,
    Rel (mkRel R) x y = R x y.
unfold Rel, mkRel; intros.
do 2 rewrite Dbeta.
apply Uprop_has_inv.
Qed.


  Definition Dprop := mkRel (fun x y => x=y /\ exists P:Prop, x = Uprop P).

  Definition Dprod A F :=
    mkRel (fun f f' => forall x x', Rel A x x' -> Rel (F x) (Dapp f x) (Dapp f' x')).


  Definition prop : trm := fun _ => Dprop.

  Definition prod (A B:trm) : trm :=
    fun i => Dprod (A i) (fun x => B (DM.cons x i)).

(* OK  model is inconsistent (models Type:Type)
  Definition Dkind := mkRel (fun x y => x=y).

Lemma sysU : Rel Dkind Dkind Dkind.
unfold Dkind at 1.
rewrite Rel_beta.
trivial.
Qed.

Lemma has_fix : forall F:D->D, exists x, F x = x.
intros.
pose (fx :=
  let dlt := Dlam (fun x => F (Dapp x x)) in
  Dapp dlt dlt).
exists fx.
unfold fx at 2; simpl.
rewrite Dbeta.
reflexivity.
Qed.

Definition Dnot x := Uprop (forall P:Prop, x = Uprop P -> ~P).
(* Rk: Dnot non monotonic, maps bottom to a valid prop but maps
   a valid prop to an invalid prop *)

Lemma paradox : False.
destruct (has_fix Dnot).
assert (Dnot x = Uprop False).
 unfold Dnot; apply f_equal; apply prop_ext.
 split; intros; try contradiction.
 generalize H0.
 apply H0.
 symmetry; assumption.
assert (Dnot x = Uprop True).
 rewrite <- H.
 unfold Dnot at 1; apply f_equal; apply prop_ext.
 split; intros; trivial.
 red; intros.
 rewrite H0 in H2; apply Uprop_inj in H2; rewrite H2; trivial.
rewrite H0 in H1; apply Uprop_inj in H1.
rewrite H1; trivial.
Qed.
*)

Module Beq.
Definition t := bool.
Definition eq := @eq bool.
Definition eq_equiv : Equivalence eq := eq_equivalence.
Existing Instance eq_equiv.
End Beq.
Module B := VarMap.Make(Beq).

 
Definition val_ok (ivars:B.map) (e:list trm) i i' :=
  forall n ty, nth_error e n = value ty ->
  ivars n = false ->
  Rel (ty (DM.shift (S n) i)) (i n) (i' n).

Lemma val_ok_cons : forall ivars e i i' x x' (ty:trm),
  val_ok ivars e i i' ->
  Rel (ty i) x x' ->
  val_ok (B.cons false ivars) (ty::e) (DM.cons x i) (DM.cons x' i').
red; intros.
destruct n as [|n]; simpl in *.
 injection H1; clear H1; intros; subst ty0.
 replace (DM.shift 1 (DM.cons x i)) with i; auto.
 apply ext; reflexivity.

 change (DM.shift (S (S n)) (DM.cons x i)) with (DM.shift (S n) i).
 apply H; trivial.
Qed.


Lemma val_ok_cons_impl : forall ivars e i i' x x' (ty:trm),
  val_ok ivars e i i' ->
  val_ok (B.cons true ivars) (ty::e) (DM.cons x i) (DM.cons x' i').
red; intros.
destruct n as [|n]; simpl in *.
 discriminate H1.

 change (DM.shift (S (S n)) (DM.cons x i)) with (DM.shift (S n) i).
 apply H; trivial.
Qed.


(*
Lemma val_ok_thin : forall e i i' x x',
  val_ok e i i' ->
  val_ok (map (lift 1) e) (DM.cons x i) (DM.cons x' i').
unfold val_ok; intros.
assert (exists2 t, nth_error e n = value t & ty0 = lift 1 t).
 clear i i' x x' H.
 revert e H0; induction n; destruct e; simpl; intros; try discriminate.
  injection H0; exists t; auto.

  specialize IHn with (1:=H0).
  destruct IHn.
  exists x; trivial.
destruct H1.
rewrite H2.
unfold lift.
replace (DM.shift 1 (DM.shift (S n) (DM.cons x i)))
 with (DM.shift (S n) i); auto.
replace (RM.shift 1 (RM.cons x i)) with i; auto.
apply ext; intro.
reflexivity.
Qed.
*)

Definition sjudge ivars (e:list trm) (M M' T:trm) :=
  forall i i', val_ok ivars e i i' -> Rel (T i) (M i) (M' i').

Lemma ty_ref : forall ivars (e:list trm) n ty,
  ivars n = false ->
  nth_error e n = value ty ->
  sjudge ivars e (ref n) (ref n) (lift (S n) ty).
red; intros.
apply H1; trivial.
Qed.

Lemma ty_app : forall ivars e u u' v v' A B,
  sjudge ivars e u u' (prod A B) ->
  sjudge ivars e v v' A ->
  sjudge ivars e (app u v) (app u' v') (sub v B).
unfold sjudge; intros.
specialize H with (1:=H1).
specialize H0 with (1:=H1).
unfold prod, Dprod in H.
rewrite Rel_beta in H.
unfold sub, app.
auto.
Qed.

Definition PER (r:D) := Symmetric (Rel r) /\ Transitive (Rel r).

Definition is_kind ivars (e:list trm) (T T':trm) :=
  forall i i', val_ok ivars e i i' -> T i = T' i'.

Lemma ty_abs : forall ivars b e m m' T U,
  sjudge (B.cons b ivars) (T::e) m m' U ->
  sjudge ivars e (abs m) (abs m') (prod T U).
unfold sjudge; intros.
unfold prod, Dprod; rewrite Rel_beta.
intros.
assert (val_ok (B.cons b ivars) (T::e) (DM.cons x i) (DM.cons x' i')).
 destruct b.
  apply val_ok_cons_impl; trivial.
  apply val_ok_cons; trivial.
specialize H with (1:=H2).
unfold abs.
do 2 rewrite Dbeta.
trivial.
Qed.

Lemma ty_beta : forall ivars e T U m m' v v',
  sjudge (B.cons false ivars) (T::e) m m' U ->
  sjudge ivars e v v' T ->
  sjudge ivars e (app (abs m) v) (sub v' m') (sub v U).
unfold sjudge, app, abs, sub; intros.
rewrite Dbeta.
apply H.
apply val_ok_cons; auto.
Qed.

Lemma ty_conv : forall ivars e m m' T T',
  sjudge ivars e m m' T ->
  is_kind (B.nil false) e T T' ->
  sjudge ivars e m m' T'.
unfold is_kind, sjudge; intros.
assert (val_ok (B.nil false) e i i).
 red; intros.
 admit.
specialize H0 with (1:=H2).
rewrite <- H0; auto.
Qed.
