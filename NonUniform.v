(** This file shows how big non-uniform parameters can be encoded
    as an index without changing the universe of the definition.
 *)

Lemma trans_refl_l A (x y:A) (e:x=y) : eq_trans eq_refl e = e.
destruct e; reflexivity.
Qed.

(** Big universe of the parameter *)
Definition T2 := Type.
(** Universe of the inductive definition *)
Definition T1:T2:=Type.

Module NoPayload.

(** The parameter type *)
Parameter P : T2.
(** The arity of the W-type. To simplify, we did not
    consider the payload *)
Parameter B : P -> T1.
(** The parameter update *)
Parameter f : forall p:P, B p -> P.

(** Encoding as an index. W is not in T1 *)
Inductive W : P -> T2 :=
| C : forall p, (forall i: B p, W (f p i)) -> W p.

(** We need functional extensionality *)
Axiom fext : forall (A:Type)(B:A->Type)(f g:forall x:A, B x),
  (forall x, f x = g x) -> f = g.

(** * Encoding parameters as paths *)

(** Type of paths from the initial value of the parameter to 
    subterms *)
Fixpoint path (p:P) (n:nat) : T1 :=
  match n with
  | 0 => unit
  | S k => {i:B p & path (f p i) k }
  end.

Fixpoint decn p n : path p n -> P :=
  match n return path p n -> P with
  | 0 => fun _ => p
  | S k => fun q => let (i,l') := q in decn (f p i) k l'
  end.

Fixpoint extpath p n : forall l:path p n, B(decn p n l) -> path p (S n) :=
  match n return forall l:path p n, B(decn p n l) -> path p (S n) with
  | 0 => fun _ i => existT _ i tt
  | S k => fun l =>
      match l return B (decn p (S k) l) -> path p (S (S k)) with
      | existT i' l' => fun i => existT _ i' (extpath _ k l' i)
      end
  end.

(** The encoded type. [p] is the initial value of the parameter. [(m,l)]
    is the path to the current value of the parameter.
 *)
Inductive W2 (p:P) : forall n, path p n -> T1 :=
  C2 : forall m l, (forall i:B (decn p m l), W2 p (S m) (extpath _ _ l i)) -> W2 p m l.

Record P' :T2:= mkP' {
  _p : P;
  _m : nat;
  _l : path _p _m
}.

Definition i0 (p:P) : P' := mkP' p 0 tt.
(*Definition i1 (p:P) (i:B p) : P' := mkP' p 1 (extpath p 0 tt i).*)

Definition d (p:P') : P := decn (_p p) (_m p) (_l p).
Definition f3 (p:P') (i:B(d p)) : P' := mkP' (_p p) (S (_m p)) (extpath _ _ (_l p) i).
Definition W3 (p:P') : T1 := W2 (_p p) (_m p) (_l p).
Definition C3 (p:P') (g:forall i:B(d p), W3 (f3 p i)) : W3 p :=
  C2 (_p p) (_m p) (_l p) g.
Definition unC3 (p:P') (w:W3 p) : forall i:B(d p), W3 (f3 p i) :=
  match w in W2 _ n l return forall i, W3 (mkP' _ _ (extpath _ _ l i))  with
  | C2 m l' g => g
  end.

Definition W3_case (p:P') (Q : W3 p -> Type)
  (h:forall (g : forall i : B(d p), W3 (f3 p i)), Q (C3 p g)) (w:W3 p) : Q w.
revert Q h; unfold d,f3,C3,W3; simpl.
unfold W3 in w.
pattern (_m p), (_l p), w.
case w.
intros n' l' g Q h.
apply (h g).
Defined.


Definition W3_elim (Q : forall p : P', W3 p -> Type)
  (h:forall p (g : forall i : B(d p), W3 (f3 p i)),
     (forall i:B(d p), Q (f3 p i) (g i)) -> Q p (C3 p g)) : forall (p:P') (w:W3 p), Q p w.
fix W3e 2.
intros p w; revert p w.
destruct p as (p,n,l); unfold W3; simpl.
intros w; case w.
intros n' l' g.
apply h.
intros i.
apply W3e.
Defined.

(*
Fixpoint Weq p (w1:W3 p) (w2:W3 p) {struct w1} :=
  forall (i:B(d p)),
  Weq _ (unC3 _ w1 i) (unC3 _ w2 i).

Lemma Weq_ext p w w': Weq p w w' -> w=w'.
revert w'; pattern p, w; apply W3_elim; simpl; intros.
revert X; pattern w'; apply W3_case; simpl; intros.
apply f_equal.
apply fext; auto.
Qed.

Lemma Weq_refl p w : Weq p w w.
pattern p, w; apply W3_elim; clear p w; simpl; intros; auto.
Qed.
*)

Lemma eq_ext p p' (i:B(d p')) (e:d p=d p') :
  d(f3 p (eq_rect_r B i e)) = d(f3 p' i).
revert i e; destruct p' as (p',n',l').
revert p' l'; induction n'; simpl.
 unfold f3 at 2; simpl.
 unfold d at 1 3; simpl.
 intros p' ? i e.
 unfold d; simpl.
 revert i; destruct e.
 unfold eq_rect_r; simpl.
 destruct p as (p,n,l); revert p l; induction n; simpl; intros.
  reflexivity.

  destruct l.
  apply IHn.

 destruct l'.
 apply IHn'.
Defined.

Lemma eq_ext_refl p (i:B(d p)) :
  eq_ext p p i eq_refl = eq_refl.
revert i; destruct p as (p,n,l); revert p l; induction n; simpl; intros; auto.
destruct l; intros.
apply IHn.
Qed.

(*
Lemma eq_ext_sym p (i:B(d p)) :
  eq_sym (eq_ext p (i0 (d p)) i eq_refl) =
  eq_ext (i0 (d p)) p i eq_refl.
destruct p as (p,n,l).
revert p l i; induction n; intros.
 simpl; reflexivity.

 destruct l; apply IHn.
Qed.
*)

Lemma extpath_trans_prf p p' p'' i (e:d p=d p') (e':d p'=d p'') :
  f3 p (eq_rect_r B i (eq_trans e e')) =
  f3 p (eq_rect_r B (eq_rect_r B i e') e).
revert i; destruct e'; reflexivity.
Defined.

Lemma tr_ext_trans p p' p'' i (e:d p=d p') (e':d p'=d p'') :
  eq_ext p p'' i (eq_trans e e') =
  eq_trans (f_equal d (extpath_trans_prf p p' p'' i e e'))
    (eq_trans (eq_ext p p' (eq_rect_r B i e') e) (eq_ext p' p'' i e')).
destruct p'' as (p'',n'',l''); revert p'' l'' e' i.
induction n'';[|destruct l'']; intros.
 unfold d at 2 in e'; unfold d in i; simpl in e',i.
 destruct e'.
 unfold eq_rect_r; simpl eq_rect; simpl extpath_trans_prf.
 rewrite trans_refl_l.
 destruct p' as (p',n',l'); simpl in l''.
 revert p' l' e i; induction n'; [|destruct l']; intros.
  unfold d at 2 in e; unfold d in i; simpl in e,i.
  destruct e.
  destruct p as (p,n,l); simpl in l'.
  revert p l i; induction n; [|destruct l]; intros.
   simpl; reflexivity.

   apply IHn.

  apply IHn'.

 apply IHn''.
Qed.
Opaque eq_ext.


Fixpoint tr p (w:W3 p) p' (e:d p=d p'): W3 p' :=
  C3 p' (fun i : B (d p') =>
     tr _ (unC3 p w (eq_rect_r B i e)) (f3 p' i) (eq_ext p p' i e)).


Lemma tr_id : forall p w, tr p w p eq_refl = w.
apply W3_elim; simpl; intros; trivial.
apply f_equal; apply fext; intros i.
unfold eq_rect_r; simpl.
rewrite eq_ext_refl; auto.
Qed.
(*
Lemma tr_id : forall p w, Weq _ (tr p w p eq_refl) w.
apply W3_elim; simpl; intros; trivial.
unfold eq_rect_r; simpl.
rewrite eq_ext_refl; auto.
Qed.
*)
Lemma tr_comm p p0 p' (e:d p = d p') (e':d p0 = d p')
  (w:W3 p) (w':W3 p0) (h:p0=p):
  w' = eq_rect_r W3 w h ->
  e' = eq_trans (f_equal d h) e ->
  tr _ w _ e = tr _ w' _ e'.
intros.
destruct p as (p,n,l); simpl _p in *; simpl _m in *; simpl _l in *.
subst.
apply f_equal.
symmetry; apply trans_refl_l.
Qed.

(** Applying two equality proofs is equivalent to applying the
    composition of these proofs *)
Lemma tr_comp p w p' e p'' e' :
  tr p' (tr p w p' e) p'' e' = tr p w p'' (eq_trans e e').
revert p' e p'' e'; pattern p, w; apply W3_elim; simpl; intros.
apply f_equal.
apply fext; intro i.
rewrite H.
clear H.
apply tr_comm with (h:=extpath_trans_prf _ _ _ i e e').
 unfold extpath_trans_prf.
 destruct e'; reflexivity.

 apply tr_ext_trans. 
Qed.

(*
Lemma tr_comp1 p p' (w:W3 p) (w':W3 p') (e:d p=d p'):
   Weq _ (tr p w p' e) w' ->
   Weq _ w (tr p' w' p (eq_sym e)).
revert p' w' e; pattern p, w; apply W3_elim; clear p w; simpl.
intros p g Hrec p' w' e .
pattern w'; apply W3_case; intros g' H i.
simpl.
specialize H with (eq_rect_r B i (eq_sym e)).

pose (e'' := eq_ext p p' (eq_rect_r B i (eq_sym e)) e).

generalize (Hrec
            (eq_rect_r B (eq_rect_r B i (eq_sym e)) e)
            (f3 p' (eq_rect_r B i (eq_sym e)))
            (g' (eq_rect_r B i (eq_sym e)))
            e'' H); intro H'.
clear Hrec H.
subst e''.
destruct p' as (p',n',l').
revert p' l' w' e g' H'; induction n'; intros.
 destruct l'.
 change (mkP' p' 0 tt) with (i0 p') in *.
 unfold d at 2 in e; simpl in e.
 destruct e.
 simpl.
 change  (eq_rect_r B i (eq_sym eq_refl)) with i in H'.
 change  (eq_rect_r B i eq_refl) with i in H'|-*.
 rewrite <- eq_ext_sym; trivial.

 simpl in l'.
 destruct l'.
admit.
Qed.
*)

Definition W' p : T1 := W3 (i0 p).

(** The constructor *)
Definition C' (p:P) (g:forall i, W' (f p i)) : W' p := 
  C3 (i0 p) (fun i : B p => tr (i0(f p i)) (g i) (f3 (i0 p) i) eq_refl).

(** The projection *)
Definition unC' p (w : W' p) (i:B p) : W' (f p i) :=
  tr (f3 (i0 p) i) (unC3 (i0 p) w i) (i0 (f p i)) eq_refl.

Lemma W'_surj p (w:W' p) : w = C' _ (unC' p w).
pattern w; apply W3_case; simpl; intros.
unfold C', unC'; simpl.
apply f_equal; apply fext; intros i.
rewrite tr_comp.
simpl eq_trans.
symmetry; apply tr_id.
Defined.

Definition W'_case p (w:W' p) (Q:W' p -> Type)
  (h:forall g:forall i:B p,W' (f p i), Q (C' p g)) : Q w.
rewrite (W'_surj _ w).
apply h.
Defined.


Definition W'_elim0 p (w:W' p) (Q:forall p, W' p -> Type)
  (h : forall p (g:forall i,W' (f p i)), (forall i, Q (f p i) (g i)) -> Q p (C' p g)) :
  forall p' (e:d(i0 p)=p'), Q p' (tr _ w (i0 p') e).
unfold W' in w.
pattern (i0 p), w.
apply W3_elim; clear p w; intros.
rewrite W'_surj.
apply h.
intros.
unfold unC';simpl.
rewrite tr_comp; simpl.
apply X.
Defined.

Definition W'_elim p (w:W' p) (Q:forall p, W' p -> Type)
  (h : forall p (g:forall i,W' (f p i)),
       (forall i, Q _ (g i)) -> Q _ (C' p g)) : Q p w.
rewrite <- (tr_id _ w).
apply W'_elim0; trivial.
Defined.

Lemma w_eta p g : unC' p (C' p g) = g.
unfold unC', C'; simpl.
apply fext; intros i.
rewrite tr_comp.
simpl eq_trans.
rewrite (tr_id _ (g i)); trivial.
Qed.

(** Proving the reduction is correct (non-dep!) *)
Lemma W'_case_nodep_eqn p Q g h : W'_case p (C' p g) (fun _=>Q) h = h g.
unfold W'_case.
simpl in h.
unfold eq_rect_r, eq_rect.
generalize (eq_sym (W'_surj p (C' p g))).
rewrite (w_eta p g).
intro e.
change ((fun w (e':C' p g=w) =>
     match e' in (@eq _ _ y) return Q with
     | eq_refl => h g
     end = h g) (C' p g) e).
case e; reflexivity.
Qed.

Lemma eqp_f p p' (e:p=p') (i:B p):
  f p i = f p' (eq_rect_r B i (eq_sym e)).
destruct e; reflexivity.
Defined.

Lemma W'_elim0_nodep_eqn p Q g h p' e :
  W'_elim0 p (C' p g) (fun p _=>Q p) h p' e =
  eq_rect_r Q (h p g (fun i:B p => W'_elim0 (f p i) (g i) (fun p _=>Q p) h (f p i) eq_refl)) (eq_sym e).
unfold W'_elim0.
Opaque W'_surj.
simpl W3_elim.
unfold unC'.
simpl unC3.
change (mkP' p 0 tt) with (i0 p).
unfold d in e; simpl in e.
destruct e; simpl.
unfold eq_rect_r; simpl.
match goal with |- eq_rect _ _ _ _ ?h =_ => set (e':=h) end.
destruct e'.
simpl.
f_equal.
 apply fext; intros i.
 rewrite tr_comp.
 rewrite tr_comp.
 rewrite eq_ext_refl.
 simpl.
 rewrite tr_id.
 trivial.

 apply fext; intros i.
 match goal with |- eq_rect _ _ _ _ ?h =_ => destruct h end.
 simpl.
Admitted.


Lemma W'_elim_nodep_eqn p Q g h :
  W'_elim p (C' p g) (fun _ _=>Q) h =
  h p g (fun i => W'_elim _ (g i) (fun _ _=>Q) h).
unfold W'_elim at 1.
simpl in h.
unfold eq_rect_r, eq_rect.
generalize (eq_sym (W'_surj p (C' p g))).
rewrite (w_eta p g).
intro e.
Admitted.
(*change ((fun w (e':C' p g=w) =>
     match e' in (@eq _ _ y) return Q with
     | eq_refl => h g
     end = h g) (C' p g) e).
case e; reflexivity.
Qed.
*)

Lemma W'_case_eqn p Q g h : W'_case p (C' p g) Q h = h g.
unfold W'_case.
unfold eq_rect_r, eq_rect.
generalize (eq_sym (W'_surj p (C' p g))).
rewrite (w_eta p g).
intro e.
generalize (h g).
Admitted.

End NoPayload.

(*********************************************************************************)

Module WithPayload.

(** The parameter type *)
Parameter P : T2.

(** The "payload" of the W-type. *)
Parameter A : P -> T1.
(** The arity of the W-type. *)
Parameter B : forall p:P, A p -> T1.
(** The parameter update *)
Parameter f : forall (p:P) (x:A p), B p x -> P.

(** Encoding as an index. W is not in T1 *)
Inductive W : P -> T2 :=
| C : forall (p:P) (x:A p), (forall i: B p x, W (f p x i)) -> W p.

(** We need functional extensionality *)
Axiom fext : forall (A:Type)(B:A->Type)(f g:forall x:A, B x),
  (forall x, f x = g x) -> f = g.

(** * Encoding parameters as paths *)

(** Type of paths from the initial value of the parameter to 
    subterms *)
Fixpoint path (p:P) (n:nat) : T1 :=
  match n with
  | 0 => unit
  | S k => {x:A p &{i:B p x & path (f p x i) k }}
  end.

Fixpoint decn p n : path p n -> P :=
  match n return path p n -> P with
  | 0 => fun _ => p
  | S k => fun q =>
     match q with
     | existT x (existT i l') => decn (f p x i) k l'
     end
  end.

Fixpoint extpath p n : forall (l:path p n) (x:A(decn p n l)), B _ x -> path p (S n) :=
  match n return forall (l:path p n) (x:A(decn p n l)), B _ x -> path p (S n) with
  | 0 => fun _ x i => existT _ x (existT _ i tt)
  | S k => fun l =>
      match l return forall (x:A(decn p (S k)l)), B _ x -> path p (S (S k)) with
      | existT x' (existT i' l') => fun x i => existT _ x' (existT _ i' (extpath _ k l' x i))
      end
  end.

(** The encoded type. [p] is the initial value of the parameter. [(m,l)]
    is the path to the current value of the parameter.
 *)
Inductive W2 (p:P) : forall n, path p n -> T1 :=
  C2 : forall m l (x:A(decn p m l)), (forall i:B _ x, W2 p (S m) (extpath _ _ l x i)) -> W2 p m l.

Definition unC2 (p : P) n (l:path p n) (w:W2 p n l) : {x:A(decn _ _ l)&forall(i:B _ x), W2 _ _ (extpath _ _ l x i)}:=
  match w in W2 _ n l return {x:_ & forall i, W2 _ _ (extpath _ _ l x i)}  with
  | C2 m l' x g => existT _ x g
  end.

Record P' :T2:= mkP' {
  _p : P;
  _m : nat;
  _l : path _p _m
}.


Definition d (p:P') : P := decn (_p p) (_m p) (_l p).
Definition W3 (p:P') : T1 := W2 (_p p) (_m p) (_l p).
Definition f3 (p:P') (x:A(d p)) (i:B _ x) : P' := mkP' (_p p) (S (_m p)) (extpath _ _ (_l p) x i).
Definition C3 (p:P') (xg:{x:A(d p) & forall i:B _ x, W3 (f3 p x i)}) : W3 p :=
  C2 (_p p) (_m p) (_l p) (projT1 xg) (projT2 xg).

Definition unC3 (p:P') (w:W3 p) : {x:A(d p) & forall i:B _ x, W3 (f3 p x i)} :=
  unC2 _ _ _ w.

Definition W3_case (p:P') (Q : W3 p -> Type)
  (h:forall (x:A(d p)) (g : forall i : B _ x, W3 (f3 p x i)), Q (C3 p (existT _ x g))) (w:W3 p) : Q w.
revert Q h; unfold d,f3,C3,W3; simpl.
unfold W3 in w.
pattern (_m p), (_l p), w.
case w.
(*apply W2_case.*)
intros n' l' x g Q h.
apply (h x g).
Defined.


Definition W3_elim (Q : forall p : P', W3 p -> Type)
  (h:forall p (x:A(d p)) (g : forall i : B _ x, W3 (f3 p x i)),
     (forall i:B _ x, Q (f3 p x i) (g i)) -> Q p (C3 p (existT _ x g))) : forall (p:P') (w:W3 p), Q p w.
fix W3e 2.
intros p w; revert p w.
destruct p as (p,n,l); unfold W3; simpl.
intros w; case w.
intros n' l' x g.
apply h.
intros i.
apply W3e.
Defined.

Definition i0 (p:P) : P' := mkP' p 0 tt.
Definition i1 (p:P) (x:A p) (i:B p x) : P' := mkP' p 1 (extpath p 0 tt x i).

Lemma eq_ext p p' (e:d p=d p') (x':A(d p')) (i':B(d p') x')  :
  let x := eq_rect_r A x' e in
  let i := match e as e in _=y return B y (eq_rect_r A x' e)->B(d p)x with eq_refl=> (fun x => x) end i' in
  d(f3 p x i) = d(f3 p' x' i').
revert i e; destruct p' as (p',n',l').
revert p' l'; induction n'; simpl.
 unfold f3 at 2; simpl.
 unfold d at 1 3; simpl.
 intros p' ? i e.
 unfold d; simpl.
 revert i; destruct e.
 unfold eq_rect_r; simpl.
 destruct p as (p,n,l); revert p l; induction n; simpl; intros.
  reflexivity.

  destruct l.
  apply IHn.

 destruct l'.
 apply IHn'.
Defined.

Lemma eq_extefl p (i:B(d p)) :
  eq_ext p p i eq_refl = eq_refl.
revert i; destruct p as (p,n,l); revert p l; induction n; simpl; intros; auto.
destruct l; intros.
apply IHn.
Qed.

Lemma eq_ext_sym p (i:B(d p)) :
  eq_sym (eq_ext p (i0 (d p)) i eq_refl) =
  eq_ext (i0 (d p)) p i eq_refl.
destruct p as (p,n,l).
revert p l i; induction n; intros.
 simpl; reflexivity.

 destruct l; apply IHn.
Qed.

Lemma extpath_trans_prf p p' p'' i (e:d p=d p') (e':d p'=d p'') :
  f3 p (eq_rect_r B i (eq_trans e e')) =
  f3 p (eq_rect_r B (eq_rect_r B i e') e).
revert i; destruct e'; reflexivity.
Defined.

Lemma tr_ext_trans p p' p'' i (e:d p=d p') (e':d p'=d p'') :
  eq_ext p p'' i (eq_trans e e') =
  eq_trans (f_equal d (extpath_trans_prf p p' p'' i e e'))
    (eq_trans (eq_ext p p' (eq_rect_r B i e') e) (eq_ext p' p'' i e')).
destruct p'' as (p'',n'',l''); revert p'' l'' e' i.
induction n'';[|destruct l'']; intros.
 unfold d at 2 in e'; unfold d in i; simpl in e',i.
 destruct e'.
 unfold eq_rect_r; simpl eq_rect; simpl extpath_trans_prf.
 rewrite trans_refl_l.
 destruct p' as (p',n',l'); simpl in l''.
 revert p' l' e i; induction n'; [|destruct l']; intros.
  unfold d at 2 in e; unfold d in i; simpl in e,i.
  destruct e.
  destruct p as (p,n,l); simpl in l'.
  revert p l i; induction n; [|destruct l]; intros.
   simpl; reflexivity.

   apply IHn.

  apply IHn'.

 apply IHn''.
Qed.

*)
Fixpoint tr p (w:W3 p) p' (e:d p=d p'): W3 p' :=
  let (x,g) := unC3 p w in
  let x' := eq_rect_r A x (eq_sym e) in
  C3 p' (existT _ x' (fun i : B _ x' =>
     let i' := match e as e in _=y return B y (eq_rect_r A x (eq_sym e))->B(d p)x with eq_refl=> (fun x => x) end i in
     tr _ (g i') (f3 p' x' i) e)).

 (eq_ext p p' i e))).


Lemma tr_id : forall p w, tr p w p eq_refl = w.
apply W3_elim; simpl; intros; trivial.
apply f_equal; apply fext; intros i.
unfold eq_rect_r; simpl.
rewrite eq_ext_refl; auto.
Qed.
(*
Lemma tr_id : forall p w, Weq _ (tr p w p eq_refl) w.
apply W3_elim; simpl; intros; trivial.
unfold eq_rect_r; simpl.
rewrite eq_ext_refl; auto.
Qed.
*)
Lemma tr_comm p p0 p' (e:d p = d p') (e':d p0 = d p')
  (w:W3 p) (w':W3 p0) (h:p0=p):
  w' = eq_rect_r W3 w h ->
  e' = eq_trans (f_equal d h) e ->
  tr _ w _ e = tr _ w' _ e'.
intros.
destruct p as (p,n,l); simpl _p in *; simpl _m in *; simpl _l in *.
subst.
apply f_equal.
symmetry; apply trans_refl_l.
Qed.

(** Applying two equality proofs is equivalent to applying the
    composition of these proofs *)
Lemma tr_comp p w p' e p'' e' :
  tr p' (tr p w p' e) p'' e' = tr p w p'' (eq_trans e e').
revert p' e p'' e'; pattern p, w; apply W3_elim; simpl; intros.
apply f_equal.
apply fext; intro i.
rewrite H.
clear H.
apply tr_comm with (h:=extpath_trans_prf _ _ _ i e e').
 unfold extpath_trans_prf.
 destruct e'; reflexivity.

 apply tr_ext_trans. 
Qed.

(*
Lemma tr_comp1 p p' (w:W3 p) (w':W3 p') (e:d p=d p'):
   Weq _ (tr p w p' e) w' ->
   Weq _ w (tr p' w' p (eq_sym e)).
revert p' w' e; pattern p, w; apply W3_elim; clear p w; simpl.
intros p g Hrec p' w' e .
pattern w'; apply W3_case; intros g' H i.
simpl.
specialize H with (eq_rect_r B i (eq_sym e)).

pose (e'' := eq_ext p p' (eq_rect_r B i (eq_sym e)) e).

generalize (Hrec
            (eq_rect_r B (eq_rect_r B i (eq_sym e)) e)
            (f3 p' (eq_rect_r B i (eq_sym e)))
            (g' (eq_rect_r B i (eq_sym e)))
            e'' H); intro H'.
clear Hrec H.
subst e''.
destruct p' as (p',n',l').
revert p' l' w' e g' H'; induction n'; intros.
 destruct l'.
 change (mkP' p' 0 tt) with (i0 p') in *.
 unfold d at 2 in e; simpl in e.
 destruct e.
 simpl.
 change  (eq_rect_r B i (eq_sym eq_refl)) with i in H'.
 change  (eq_rect_r B i eq_refl) with i in H'|-*.
 rewrite <- eq_ext_sym; trivial.

 simpl in l'.
 destruct l'.
admit.
Qed.
*)

Definition W' p : T1 := W3 (i0 p).

(** The constructor *)
Definition C' (p:P) (g:forall i, W' (f p i)) : W' p := 
  C3 (i0 p) (fun i : B p => tr (i0(f p i)) (g i) (f3 (i0 p) i) eq_refl).

(** The projection *)
Definition unC' p (w : W' p) (i:B p) : W' (f p i) :=
  tr (f3 (i0 p) i) (unC3 (i0 p) w i) (i0 (f p i)) eq_refl.

Lemma W'_surj p (w:W' p) : w = C' _ (unC' p w).
pattern w; apply W3_case; simpl; intros.
unfold C', unC'; simpl.
apply f_equal; apply fext; intros i.
rewrite tr_comp.
simpl eq_trans.
symmetry; apply Weq_ext.
apply tr_id.
Defined.

Definition W'_case p (w:W' p) (Q:W' p -> Type)
  (h:forall g:forall i:B p,W' (f p i), Q (C' p g)) : Q w.
rewrite (W'_surj _ w).
apply h.
Defined.


Definition W'_elim p (w:W' p) (Q:forall p, W' p -> Type)
  (h : forall p (g:forall i,W' (f p i)),
       (forall i, Q _ (g i)) -> Q _ (C' p g)) : Q p w.
cut (forall p' (e:d(i0 p) = d(i0 p')), Q p' (tr _ w (i0 p') e)).
 intro.
 rewrite <- (Weq_ext _ _ _ (tr_id _ w)).
 apply X.

unfold W' in w.
pattern (i0 p), w.
apply W3_elim; clear p w; intros.
rewrite W'_surj.
apply h.
intros.
unfold unC'.
simpl.
rewrite tr_comp; simpl.
apply X.
Defined.

Lemma w_eta p g : unC' p (C' p g) = g.
unfold unC', C'; simpl.
apply fext; intros i.
rewrite tr_comp.
simpl eq_trans.
rewrite (Weq_ext _ _ _ (tr_id _ (g i))); trivial.
Qed.

(** Proving the reduction is correct (non-dep!) *)
Lemma W'_case_nodep_eqn p Q g h : W'_case p (C' p g) (fun _=>Q) h = h g.
unfold W'_case.
simpl in h.
unfold eq_rect_r, eq_rect.
generalize (eq_sym (W'_surj p (C' p g))).
rewrite (w_eta p g).
intro e.
change ((fun w (e':C' p g=w) =>
     match e' in (@eq _ _ y) return Q with
     | eq_refl => h g
     end = h g) (C' p g) e).
case e; reflexivity.
Qed.

Lemma W'_elim_nodep_eqn p Q g h :
  W'_elim p (C' p g) (fun _ _=>Q) h =
  h p g (fun i => W'_elim _ (g i) (fun _ _=>Q) h).
unfold W'_elim.
simpl in h.
unfold eq_rect_r, eq_rect.
generalize (eq_sym (W'_surj p (C' p g))).
rewrite (w_eta p g).
intro e.
change ((fun w (e':C' p g=w) =>
     match e' in (@eq _ _ y) return Q with
     | eq_refl => h g
     end = h g) (C' p g) e).
case e; reflexivity.
Qed.

Lemma W'_case_eqn p Q g h : W'_case p (C' p g) Q h = h g.
unfold W'_case.
unfold eq_rect_r, eq_rect.
generalize (eq_sym (W'_surj p (C' p g))).
rewrite (w_eta p g).
intro e.
generalize (h g).
change ((fun w (e':C' p g=w) =>
    forall q:Q w,
     match e' in (@eq _ _ y) return Q y with
     | eq_refl => q
     end = q) (C' p g) e).
case e; reflexivity.

elim e.
apply eq_elim.
destruct e.
case e.

End WithPayload.

(*********************************************************************************)


(*Definition ejf p p' (f:B(d p')->B(d p)) (i:B(d p')) (i':(d(f3 p' i))) : B (d(f3 p (f i))).*)
Parameter hh : forall p p' f i, B(d(f3 p' i)) -> B(d(f3 p (f i))).
Inductive J0 : forall p p', (B (d p') -> B (d p)) -> Type :=
| Jr0 p : J0 p p (fun x => x)
| Jr1 p : J0 p (i0 (d p)) (fun x => x)
| Jr2 p : J0 (i0 (d p)) p (fun x => x)
| Jre0 p p' (f:B(d p')->B(d p)) (i:B(d p')) :
    J0 p p' f -> J0 (f3 p (f i)) (f3 p' i) (hh p p' f i).

Record J p p' := mkJ { Je : B(d p')->B(d p); _ : J0 p p' Je }.
Implicit Arguments Je [p p'].

Definition Jr p : J p p :=
  mkJ p p (fun x => x) (Jr0 p).
Definition Ji p i : J (i0 (f p i)) (f3 (i0 p) i) :=
  mkJ (i0 (f p i)) (f3 (i0 p) i) (fun x => x) (Jr2 (f3 (i0 p) i)).
Definition Ji1 p i : J (f3 (i0 p) i) (i0 (f p i)) :=
  mkJ (f3 (i0 p) i) (i0 (f p i)) (fun x => x) (Jr1 (f3 (i0 p) i)).

Definition eq1 : forall p p' (i:B(d p')) (e:J p p'),
  J (f3 p (Je e i)) (f3 p' i).
destruct e as (f,H); simpl.
revert i.
elim H; clear p p' f H; intros.
 apply Jr.

 econstructor.
 eapply (Jre0 p (i0(d p)) (fun x=>x) i (Jr1 p)).

 econstructor.
 eapply (Jre0 (i0(d p)) p (fun x=>x) i (Jr2 p)).

 destruct (X i).
 econstructor.
 apply Jre0.
 

 unfold d at 1 in i; simpl in i.

 appl


Admitted.

Fixpoint tr p (w:W3 p) p' (e:J p p'): W3 p' :=
  C3 p' (fun i : B (d p') =>
     tr _ (unC3 p w (Je e i)) (f3 p' i) (eq1 p p' i e)).
   

Fixpoint jm_Weq p (w1:W3 p) p' (w2:W3 p') (e:J p p') {struct w1} :=
  forall (i:B(d p')),
  jm_Weq (f3 p (Je e i)) (unC3 p w1 (Je e i)) (f3 p' i) (unC3 p' w2 i) (eq1 p p' i e).

Definition W' p : T1 := W3 (i0 p).

(** The constructor *)
Definition C' (p:P) (g:forall i, W' (f p i)) : W' p := 
  C3 (i0 p) (fun i : B p => tr (i0(f p i)) (g i) (f3 (i0 p) i) (Ji p i)).

(** The projection *)
Definition unC' p (w : W' p) (i:B p) : W' (f p i) :=
  tr (f3 (i0 p) i) (unC3 (i0 p) w i) (i0 (f p i)) (Ji1 p i).

Lemma W'_surj p (w:W' p) : w = C' _ (unC' p w).
unfold W' in w.
pattern w; apply W3_case.
pattern(i0 p), w; apply W3_case.
pattern w at 1; rewrite (W3_eq _ w).
unfold C'.
apply f_equal with (f:=C3 (i0 p)).
apply fext; simpl; intro i.
unfold unC'.
rewrite tr_comp.
rewrite tr_id.
reflexivity.
Defined.

(*
Inductive J : P'->P'->Prop :=
| Jr : forall p, J p p
| Jeq1 : forall p p' (i:B(d p')) (e:J p p'),
  J (f3 p (Je e i)) (f3 p' i).
*)


Parameter J : P' -> P' -> Prop.
Parameter Je : forall p p', J p p' -> B (d p') -> B (d p).
Parameter Ji' : forall p p', d p = d p' -> J p p'.
Parameter Ji : forall p i, J (i0 (f p i)) (f3 (i0 p) i).
Parameter Ji1 : forall p i, J (f3 (i0 p) i) (i0 (f p i)).
Parameter Jr : forall p, J p p.
Parameter Jt : forall p p' p'', J p p' -> J p' p'' -> J p p''.
Implicit Arguments Je [p p'].
Implicit Arguments Jt [p p' p''].
Implicit Arguments Ji' [p p'].


Parameter eq1 : forall p p' (i:B(d p')) (e:J p p'),
  J (f3 p (Je e i)) (f3 p' i).

(*
Parameter eq1_clos : forall p i,
  eq1 p p i (Jr p) = Jr (f3 p i).
*)

Fixpoint tr p (w:W3 p) p' (e:J p p'): W3 p' :=
  C3 p' (fun i : B (d p') =>
     tr _ (unC3 p w (Je e i)) (f3 p' i) (eq1 p p' i e)).
(*
Fixpoint Weq p (w1:W3 p) p' (w2:W3 p') (e:J p p') {struct w1} :=
  forall (i:B(d p')),
  Weq _ (unC3 _ w1 (Je e i)) _ (unC3 _ w2 i) (eq1 p p' i e).

Lemma W3_refl p p' w e : Weq p w p' (tr p w p' e) e.
revert p' e; pattern p, w; apply W3_elim; clear p w; simpl; intros.
apply X.
Defined.


Definition W4 (p:P') := forall p', J p p' -> W3 p'.

Parameter J1 : forall p p' (e:J p p') (i:B(d p')), J (f3 p (Je e i)) (f3 p' i).

Definition C4 (p:P') (g:forall i:B (d p), W4 (f3 p i)) : W4 p :=
  fun p' e => C3 p' (fun i:B(d p') => g (Je e i) (f3 p' i) (J1 p p' e i)).




Definition W4_case p (w:W4 p) (Q:W4 p -> Type)
  (h:forall g:forall i:B p,W' (f p i), Q (C' p g)) : Q w.
*)

Definition W' p : T1 := W3 (i0 p).

(** The constructor *)
Definition C' (p:P) (g:forall i, W' (f p i)) : W' p := 
  C3 (i0 p) (fun i : B p => tr (i0(f p i)) (g i) (f3 (i0 p) i) (Ji p i)).

(** The projection *)
Definition unC' p (w : W' p) (i:B p) : W' (f p i) :=
  tr (f3 (i0 p) i) (unC3 (i0 p) w i) (i0 (f p i)) (Ji1 p i).

(*
Lemma W3_eq p (w:W3 p) : Weq _ w _  (C3 _ (unC3 _ w)) (Jr p).
pattern w; apply W3_case.
; reflexivity.
Defined.
*)
(*
Lemma tr_comp p w p' e p'' e' :
  tr p' (tr p w p' e) p'' e' = tr p w p'' (Jt e e').

(** Applying reflexivity does not change w *)
Lemma tr_id : forall p w, tr p w p (Jr p) = w.
apply W3_elim; simpl; intros.
apply f_equal with (f:=C3 p).
apply fext; intro i.
unfold eq_rect_r; simpl.
replace (eq1 p p i eq_refl) with (@eq_refl _ (d (f3 p i))).
 apply H.

 admit. (* eq1 p p i eq_refl --> eq_refl *)
Qed.
*)

(** Eta-equality for dependent elimination *)
(*Lemma W'_surj p (w:W' p) : Weq _ w _ (C' _ (unC' p w)) (Jr (i0 p)).
unfold C'.
unfold W' in w; pattern (i0 p), w.
; apply W3_elim.
pattern w at 1; rewrite (W3_eq _ w).
unfold C'.
apply f_equal with (f:=C3 (i0 p)).
apply fext; simpl; intro i.
unfold unC'.
rewrite tr_comp.
rewrite tr_id.
reflexivity.
Defined.
*)

Definition W'_case p (w:W' p) (Q:W' p -> Type)
  (h:forall g:forall i:B p,W' (f p i), Q (C' p g)) : Q w.
pose (g' := fun i:B p=> tr (f3 (i0 p) i) (unC3 (i0 p) w i) (i0 (f p i)) (Ji1 p i)).
pose (hg' := h g').
unfold C' in hg'.
assert (Qm : 
  forall p' (e:J p' p) (w:
Q w
h (fun i:B p => tr (f3 (i0 p) i) (unC3 (i0 p) w i) (i0 (f p i)) (Ji1 p i)).



unfold C' in h.
unfold C3 in h; simpl in h.
revert
rewrite (W'_surj _ w).
intros.
apply h.
Defined.



(* Without W *)

(** Equivalence of two paths leading to the same parameter value *)
Lemma tr_ext p n l p' n' l' i (e: decn p n l = decn p' n' l') :
  decn p (S n) (extpath p n l (eq_rect_r B i e)) =
  decn p' (S n') (extpath p' n' l' i).
revert p' l'  i e.
induction n'; simpl; intros.
 revert i; destruct e.
 unfold eq_rect_r; simpl.
 revert p l; induction n; simpl; intros.
  reflexivity.

  destruct l.
  apply IHn.

 destruct l'.
 apply IHn'.
Defined.


Lemma tr_ext_refl p n (l:path p n) (i:B(decn p n l)) :
  tr_ext p n l p n l i eq_refl = eq_refl.
revert p l i; induction n; simpl; auto.
destruct l; intros.
apply IHn.
Qed.

Lemma extpath_trans_prf p n l p' n' l' p'' n'' l'' i
  (e:decn p n l = decn p' n' l') (e':decn p' n' l' = decn p'' n'' l'') :
  extpath _ _ l (eq_rect_r B i (eq_trans e e')) =
  extpath _ _ l (eq_rect_r B (eq_rect_r B i e') e).
revert i; destruct e'; reflexivity.
Defined.

Lemma tr_ext_trans p n l p' n' l' p'' n'' l'' i
  (e:decn p n l = decn p' n' l') (e':decn p' n' l' = decn p'' n'' l'') :
  tr_ext _ _ _ _ _ _ i (eq_trans e e') =
  eq_trans (f_equal (decn _ _) (extpath_trans_prf _ _ _ _ _ _ _ _ _ i e e'))
   (eq_trans (tr_ext _ _ _ _ _ _ (eq_rect_r B i e') e) (tr_ext _ _ _ _ _ _ i e')).
revert p'' l'' e' i.
induction n''; simpl decn; simpl path; [|destruct l''].
  destruct e'.
  unfold eq_rect_r; simpl eq_rect; simpl extpath_trans_prf; simpl f_equal.
  revert p' l' e; induction n'; simpl decn; simpl path; [|destruct l'].
   destruct e; intros.
   symmetry; apply trans_refl_l.

   apply IHn'.

  apply IHn''.
Qed.

(** Re-basing paths *)
Fixpoint tr p n l (w:W2 p n l) p' n' l' (e:decn p n l = decn p' n' l'): W2 p' n' l' :=
  C2 p' n' l' (fun i : B (decn p' n' l') =>
     tr _ _ _ (unC2 _ _ _ w (eq_rect_r B i e)) _ _ _ (tr_ext _ _ _ _ _ _ i e)).

(** Applying reflexivity does not change w *)
Lemma tr_id : forall p n l w,
  tr p n l w p n l eq_refl = w.
induction w; simpl; intros.
apply f_equal with (f:=C2 p m l).
apply fext; intro i.
rewrite tr_ext_refl.
apply H.
Qed.

Lemma tr_comm p n (l l0:path p n) p' n' (l':path p' n')
  (e:decn p n l = decn p' n' l') (e':decn p n l0 = decn p' n' l')
  (w:W2 p n l) (w':W2 p n l0) (h:l0=l):
  w' = eq_rect_r (W2 p n) w h ->
  e' = eq_trans (f_equal (decn _ _) h) e ->
  tr _ _ _ w _ _ _ e = tr _ _ _ w' _ _ _ e'.
intros.
subst.
apply f_equal.
symmetry; apply trans_refl_l.
Qed.

(** Applying two equality proofs is equivalent to applying the
    composition of these proofs *)
Lemma tr_comp p n l w p' n' l' e p'' n'' l'' e' :
  tr p' n' l' (tr p n l w p' n' l' e) p'' n'' l'' e' =
  tr p n l w p'' n'' l'' (eq_trans e e').
revert p' n' l' e p'' n'' l'' e'; induction w; simpl; intros.
apply f_equal with (f:=C2 p'' n'' l'').
apply fext; intro i.
rewrite H.
clear H.
apply tr_comm with (h:=extpath_trans_prf _ _ _ _ _ _ _ _ _ i e e').
 unfold extpath_trans_prf.
 destruct e'; reflexivity.

 apply tr_ext_trans. 
Qed.


(** * Equivalence with W *)

(** The W-type equivalent to W *)

Definition W' p : T1 := W2 p 0 tt.

(** The constructor *)
Definition C' (p:P) (g:forall i, W' (f p i)) : W' p := 
  C2 p 0 tt (fun i : B p => tr _ _ _ (g i) p 1 (extpath p 0 tt i) eq_refl).

(** The projection *)
Definition unC' p (w : W' p) (i:B p) : W' (f p i) :=
  tr _ _ _ (unC2 _ _ _ w i) (f p i) 0 tt eq_refl.

(** Eta-equality for dependent elimination *)
Lemma W'_surj p w : w = C' _ (unC' p w).
rewrite (W2_eq _ _ _ w).
unfold C'.
apply f_equal with (f:=C2 p 0 tt).
apply fext; simpl; intro i.
unfold unC'.
simpl.
rewrite tr_comp.
rewrite tr_id.
reflexivity.
Defined.


Definition W'_case p (w:W' p) (Q:W' p -> Type)
  (h:forall g:forall i:B p,W' (f p i), Q (C' p g)) : Q w.
rewrite (W'_surj _ w).
intros.
apply h.
Defined.

Definition W'_elim p (w:W' p) (Q:forall p, W' p -> Type)
  (h : forall p (g:forall i,W' (f p i)),
       (forall i, Q _ (g i)) -> Q _ (C' p g)) : Q p w.
cut (forall p' (e:decn p 0 tt  = decn p' 0 tt),
  Q p' (tr _ _ _ w p' 0 tt e)).
 intro.
 rewrite <- (tr_id _ _ _ w).
 apply X.

change ((fun n u w' =>
  forall p' (e:decn p n u = decn p' 0 tt),
  Q p' (tr p n u w' p' 0 tt e)) 0 tt w).
elim w; clear w.
intros.
(*change (Q p'
  (C2 _ _ _ (fun i : B (decn p' 0 tt) =>
     tr _ _ _ (unC2 _ _ _ (C2 p m l w) (eq_rect_r B i e)) _ _ _ (tr_ext _ _ _ _ _ _ i e)))).*)
simpl decn at 3 in X.
rewrite W'_surj.
apply h; intro i.
unfold unC'.
change (Q (f p' i)
  (tr p' 1 (extpath p' 0 tt i)
    (tr _ _ _ (w (eq_rect_r B i e)) _ _ _ (tr_ext _ _ _ _ _ _ (i:B(decn p' 0 tt)) e))
    (f p' i) 0 tt eq_refl)).
rewrite tr_comp.
apply X.
Defined.

(** Proving the reduction is correct *)
Lemma W'_case_eqn p Q g h : W'_case p (C' p g) Q h = h g.
unfold W'_case.
Check (W'_surj p (C' p g)).

change (unC' p (C' p g)) with g.
Check  eq_rect_r (fun w : W' p => Q w) (h (unC' p (C' p g))) (W'_surj p (C' p g)).
Check  eq_rect_r (fun w : W' p => Q w) (h (unC' p (C' p g))) (W'_surj p (C' p g)).

unfold W'_surj.
simpl.
simpl W'_surj.

Lemma feqd A (B:A->Type) (f:forall x, B x) (x y:A) (e:y=x) :
  eq_rect_r B (f x) e = f y.
destruct e; reflexivity.
Qed.
unfold W'_surj.
match goal with
 |- context [eq_ind_r _ ?prf _] => set (ef := prf)
end.
set (ew := W2_eq _ _ _ (C' p g)).

Check (fext _ _ g _ (fun i => W'_surj _ (g i))).

Lemma W2_eta p n l g : g = unC2 p n l (C2 _ _ _ g).
apply fext; intro; reflexivity.
Defined.

assert (g = unC' _ (C' p g)).
 admit.
rewrite <- (feqd _ _ h _ _ H).
set (ewf := eq_ind_r (fun w:W2 p 0 tt => w = C' p (unC' p w)) ef ew).

rewrite H.
rewrite (feqd _ _ h (W2_eta _ 0 tt g)).

unfold W'_surj.
assert (forall (ABS:forall T,T) A x y z (P:A->Type) (h:P x) (u:A) e1 e2,
   eq_rect_r P h (eq_ind_r (A:=A) (x:=y) (fun a => u = x) (y:=z) e1 e2) =
   ABS _).

rewrite <- 

rewrite (feqd _ _ (fun w => h (unC' p w))).

transitivity (h (unC2 _ _ _ (C2 _ _ _ g))).

set (z:=g) in |-* at 6.

apply feqd with (B:=fun w => Q w) (f:=fun i => h).

unfold W'_surj.
match goal with
 |- context [fext _ _ _ _ ?prf] => set (eh := prf)
end. 


(*assert (g = unC' _ (C' _ g)).
 apply fext; intro i.
 unfold unC'.
 simpl.
 rewrite tr_comp.
 rewrite tr_id.
 reflexivity.
*)
simpl tr_comp.
match goal with
 |- context [f_equal _ ?prf] => set (eg := prf)
end. 
unfold unC'.
generpattern (unC2 p 0 tt (C' p g)).
rewrite eg.
destruct eg.

assert (W'_surj p (C' p g) = eq_refl).


simpl.
 (fun i => W'_elim (f p i) (g i) Q h).
unfold W'_elim at 1.
simpl W'_elim.
simpl.

Lemma W'_elim_eqn Q p g h :
  W'_elim p (C' p g) Q h = h p g (fun i => W'_elim (f p i) (g i) Q h).
unfold W'_elim at 1.
simpl W'_elim.
simpl.


(* OK: with W *)

Lemma ext_reloc : forall n p l p' i
 (e :p' = decn p n l), f p' i = decn p (S n) (extpath _ _ l (eq_rect _ B i _ e)).
induction n; simpl; intros.
 destruct e; reflexivity.

 destruct l.
 apply IHn.
Defined.

Lemma ext_reloc2 : forall n p' l p i
 (e :p = decn p' n l), f p (eq_rect_r B i e) = decn p' (S n) (extpath _ _ l i).
induction n; simpl; intros.
 destruct e; reflexivity.

 destruct l.
 apply IHn.
Defined.

Fixpoint norm p n l (w:W2 p n l) p' (e:p'=decn p n l) : W p' :=
  C p' (fun i => norm p _ _ (unC2 _ _ _ w (eq_rect _ B i _ e)) (f p' i) (ext_reloc _ _ _ _ _ e)).

Lemma norm_eq p n l w p' e :
 norm p n l w p' e =
 C p' (fun i => norm p _ _ (unC2 _ _ _ w (eq_rect _ B i _ e)) (f p' i) (ext_reloc _ _ _ _ _ e)).
destruct w; reflexivity.
Defined.

Definition unC (p : P) (w:W p) : forall i:B p, W (f p i) :=
  match w in W p return forall i, W (f p i) with
  | C _ g => g
  end.

Fixpoint unnorm p (w:W p) p' n l (e:p=decn p' n l) : W2 p' n l :=
  C2 p' n l (fun i => unnorm _ (unC _ w (eq_rect_r B i e)) p' (S n) (extpath _ _ l i) (ext_reloc2 _ _ _ _ _ e)).

Lemma norm_unnorm0 : forall p n l (w:W2 p n l),
  w = unnorm _ (norm _ _ _ w _ eq_refl) _ _ _ eq_refl.
induction w; simpl; intros.
apply f_equal with (f:=C2 p m l).
apply fext; intro i.
rewrite (H i).
simpl decn.
unfold eq_rect_r; simpl.
set (i0 := projT1 (extpath p m l i)).
set (l0 := projT2 (extpath p m l i)).
pose (E:=existT2 (fun q => q = decn _ _ (extpath p m l i))
                 (fun q => q = decn _ _ (extpath p m l i))).
pose (x:= E (decn (f p i0) m l0) eq_refl eq_refl).
pose (y:= E(f (decn p m l) i) (ext_reloc _ _ _ _ _ eq_refl) (ext_reloc2 _ _ _ _ _ eq_refl)).
apply (@f_equal _ _ (fun a:{q:_ & q=decn _ _ (extpath p m l i) & q=decn _ _ (extpath p m l i)} =>
  match a with existT2 q e1 e2 => unnorm q (norm _ _ _ (w i) q e1) _ _ _ e2 end) x y).
subst x y.
clear w H.
revert p l i i0 l0 E; induction m; intros; simpl in *; intros.
 reflexivity.

 destruct l as (k,l'); simpl in *.
 exact (IHm (f p k) l' i).
Qed.

(*
Lemma norm_unnorm : forall p n l (w:W2 p n l) p' (e:p'=decn p n l),
  w = unnorm _ (norm _ _ _ w _ e) _ _ _ e.
induction w; simpl; intros.
apply f_equal with (f:=C2 p m l).
apply fext; intro i.
specialize (H i _ (ext_reloc2 _ _ _ _ _ e)).
rewrite H.
apply f_equal with (f:=fun w => unnorm _ w _ _ _ _).
set (j:=eq_rect_r B i e) in *.
set (i':=eq_rect p' B j _ e) in *.
pose (x := existT (fun w => f p' j = decn p (S m) (extpath p m l w)) 
           i (ext_reloc2 m p l p' i e)).
pose (y := existT (fun w => f p' j = decn p (S m) (extpath p m l w)) 
           i' (ext_reloc m p l p' j e)).
apply (@f_equal _ _ (fun a =>   norm p (S m) (extpath p m l (projT1 a)) (w (projT1 a)) (f p' j) (projT2 a)) x y).
clear w H.
subst x y.
revert p l p' e i j i'; induction m; intros; simpl in *; intros.
 revert i j i'; case e; reflexivity.

 destruct l as (k,l'); simpl in *.
 exact (IHm (f p k) l' _ e i).
Qed.
*)

Lemma unnorm_norm1 : forall p (w:W p) p' n l (e:p=decn p' n l),
  w = norm _ _ _ (unnorm _ w _ _ _ e) _ e.
induction w; simpl; intros.
apply f_equal with (f:=C p).
apply fext; intro i.
specialize (H i _ _ _ (ext_reloc _ _ _ _ _ e)).
rewrite H.
apply f_equal with (f:=fun w => norm _ _ _ w _ _).
set (j:=eq_rect _ B i _ e) in *.
set (i':=eq_rect_r B j e) in *.
pose (x := existT (fun w:B p => f p w = decn p' (S n) (extpath p' n l j)) 
           i (ext_reloc _ _ _ _ _ e)).
pose (y := existT (fun w:B p => f p w = decn p' (S n) (extpath p' n l j)) 
           i' (ext_reloc2 _ _ _ _  _ e)).
apply (@f_equal _ _ (fun a =>  unnorm (f p (projT1 a)) (w (projT1 a)) p' (S n) (extpath p' n l j) (projT2 a)) x y).
clear w H.
subst x y.
revert p' l e i j i'; induction n; intros; simpl in *; intros.
 revert i j i'; case e; reflexivity.

 destruct l as (k,l'); simpl in *.
 exact (IHn (f p' k) l' e i).
Qed.

Lemma unnorm_norm0 : forall p n l (w:W (decn p n l)),
  w = norm _ _ _ (unnorm _ w _ _ _ eq_refl) _ eq_refl.
intros.
apply  unnorm_norm1.
Qed.


Definition W' p : T1 := W2 p 0 tt.

Definition C' (p:P) (g:forall i, W' (f p i)) : W' p := 
  unnorm _ (C p (fun i => norm (f p i) 0 tt (g i) _ eq_refl)) p 0 tt eq_refl.

Definition unC' p (w : W' p) (i:B p) : W' (f p i) :=
  unnorm _ (unC _ (norm _ _ _ w _ eq_refl) i) (f p i) 0 tt eq_refl.

Lemma W'_surj p w :
  w = C' _ (unC' p w).
apply eq_trans with (1:=norm_unnorm0 _ _ _ w).
unfold C', unC'.
apply f_equal with (f:=fun w => unnorm p w p 0 tt eq_refl).
(*replace w with (C2 _ _ _ (match w with C2 _ _ g => g end)).
destruct w; simpl.*)
rewrite norm_eq.
simpl.
apply f_equal with (f:=C p).
apply fext; intro i.
apply unnorm_norm0 with (p:=f p i) (n:=0) (l:=tt).
Qed.

Definition W'_case p (w:W' p) (Q:W' p -> Type)
  (h:forall g:forall i:B p,W' (f p i), Q (C' p g)) : Q w.
rewrite (W'_surj _ w).
apply h.
Defined.

Definition W'_elim p (w:W' p) (Q:forall p, W' p -> Type)
  (h : forall p (g:forall i,W' (f p i)),
       (forall i, Q _ (g i)) ->
       Q _ (C' p g)) : Q p w.
rewrite (norm_unnorm0 _ _ _ w); simpl.
generalize (norm p 0 tt w p eq_refl); clear w; intro.
induction w; simpl; intros.
rewrite W'_surj.
apply h; intro i.
unfold unC'.
unfold eq_rect_r; simpl.
generalize (unnorm_norm0 p 1 (extpath p 0 tt i) (w i)).
simpl; intro.
rewrite <- H.
apply X.
Defined.

Print Assumptions W'_elim.

(*
Fixpoint mapW2 p p' (F:forall n (l:path p n), {m:nat & path p' m})
   (h:forall n l, B (decn p' (projT1 (F n l)) (projT2 (F n l))) -> B (decn p n l))
   (h':
   n l (w:W2 p n l) : W2 p' (projT1 (F n l)) (projT2 (F n l)) :=
  match w in W2 _ n l return W2 p' (projT1 (F n l)) (projT2 (F n l)) with
  | C2 n l g =>
    C2 p' (projT1 (F n l)) (projT2 (F n l)) (fun i => mapW2 p p' F h _ _ (g (h _ _ i)))
  end.
*)


Definition conspath (p:P) (i:B p) (n:nat) (l:path (f p i) n) : path p (S n) :=
  existT _ i l.

Fixpoint liftW2 p i n l (w:W2 (f p i) n l) : W2 p _ (conspath p i n l) :=
  C2 _ _ (conspath p i n l) (fun i1 => liftW2 _ _ _ _ (unC2 _ _ _ w i1)).

Fixpoint unliftW2 p i n l (w:W2 p _ (conspath p i n l)) : W2 (f p i) n l :=
  C2 (f p i) n l (fun i1 => unliftW2 _ _ _ (extpath _ _ l i1) (unC2 _ _ _ w i1)).


Lemma lift_unlift : forall p i n l w,
  w = unliftW2 p i n l (liftW2 p i n l w).
induction w; simpl; intros.
apply f_equal with (f:=C2 (f p i) m l).
apply fext; intro.
apply H.
Qed.

Lemma unlift_lift0 : forall p n l (w:W2 p n l),
  match n return forall l, W2 p n l -> Prop with
  | 0 => fun _ _ => True
  | S k => fun l =>
    match l with
      existT i l => fun w => 
      w = liftW2 p i k l (unliftW2 p i k l w)
    end
  end l w.
induction w.
destruct m as [|k]; simpl in *; trivial.
destruct l as (i,l); simpl in *.
apply f_equal with (f:=C2 p (S k) (conspath p i k l)).
apply fext; intro.
apply H.
Qed.

Lemma unlift_lift : forall p i n l w,
  w = liftW2 p i n l (unliftW2 p i n l w).
intros.
apply (unlift_lift0 _ _ _ w).
Qed.

Definition W2' p := W2 p 0 tt.

Definition C2' p (g:forall i:B p, W2' (f p i)) : W2' p :=
  C2 p 0 tt (fun i => liftW2 p i _ _ (g i)).

Lemma W2_eta : forall p n l (w:W2 p n l), w = C2 p n l (unC2 p n l w).
destruct w; simpl; trivial.
Qed.

Lemma C2'_surj : forall p (w:W2' p),
  w = C2' p (fun i => unliftW2 p i 0 tt (unC2 _ _ _ w i)).
intros.
transitivity (C2 _ _ _ (unC2 _ _ _ w)).
 apply W2_eta.
unfold C2'; simpl.
apply f_equal with (f:=C2 p 0 tt).
apply fext; intro.
apply (unlift_lift p x 0 tt).
Qed.

Lemma W2'_case : forall p (Q:W2' p -> Type),
  (forall (g:forall i:B p, W2' (f p i)), Q (C2' p g)) ->
  forall (w:W2' p), Q w.
intros.
rewrite C2'_surj.
apply X.
Qed.

Fixpoint apppath p n m : forall l:path p n, path (decn p n l) m -> path p (n+m) :=
  match n return forall l:path p n, path (decn p n l) m -> path p (n+m) with
  | 0 => fun _ l2 => l2 
  | S k => fun l l2 =>
      let i' := projT1 l in let l' := projT2 l in existT _ i' (apppath _ k  m l' l2)
  end.

Fixpoint liftW2n p n l m (l':path (decn p n l) m) (w:W2 (decn p n l) m l') : W2 p (n+m) (apppath _ _ _ l l') :=
  match n return forall l m l', W2 (decn p n l) m l' -> W2 p (n+m) (apppath _ _ _ l l') with
  | 0 => (fun l m l' w => w)
  | S k => (fun l m l' w =>
     liftW2 _ _ _ _ (liftW2n (f p (projT1 l)) k (projT2 l) m l' w))
  end l m l' w.

Lemma W2'_elim :
  forall Q:forall p, W2' p -> Type,
  (forall (p:P) (g:forall i:B p, W2' (f p i)),
   (forall i:B p, Q (f p i) (g i)) ->
   Q p (C2' p g)) ->
  forall p n l (w:W2 p n l) (h:W2 p n l -> W2' (decn p n l)), Q _ (h w).
fix W2'_elim 4.
intros.
rewrite C2'_surj.
apply X.
intro.
assert ({ h'|
 unC2 (decn p n l) 0 tt (h w) i =
 h' (unC2 _ _ _ w i)}).
 admit.
destruct X0 as (h',?).
rewrite e.
assert (chg : W2' (f (decn p n l) i) -> W2' (decn p (S n) (extpath _ _ l i))).
 admit.
assert (unchg : W2' (decn p (S n) (extpath _ _ l i)) -> W2' (f (decn p n l) i)).
 admit.

refine (W2'_elim (fun p => Q _ _ _ _ (unC2 p n l w i) (fun w => chg (unliftW2 _ i 0 tt (h' w)))).




 simpl.
set (w' := unC2 (decn p n l) 0 tt (

(* f (decn p n l) i = decn p (S n) (extpath _ _ l i) *)



Lemma W2'_elim :
  forall Q:forall p, W2' p -> Type,
  (forall (p:P) (g:forall i:B p, W2' (f p i)),
   (forall i:B p, Q (f p i) (g i)) ->
   Q p (C2' p g)) ->
  forall p (w:W2' p), Q p w.
fix W2'_elim 4.
intros.
rewrite C2'_surj.
apply X.
intro.


Lemma W2'_elim0 :
  forall Q: forall p , W2 p -> Type,
  (forall p g, (forall i, Q _ (normW _ _ _ (g i))) ->
   Q _ (C2' p (fun i => normW _ _ _ (g i)))) ->
  forall p n l (w:W2 p n l) p' n' l' w', decn p n l = decn p' n' l' -> Q (decn p' n' l') w'.


_ _ w).




Fixpoint normW p n l (w:W2 p n l) : W2' (decn p n l) :=
  match n return forall l (w:W2 p n l), W2' (decn p n l) with
  | 0 => fun l => match l with tt => fun w => w end
  | S k => fun l => match l with existT i l' =>
           fun w => normW _ k l' (unliftW2 p _ _ _ w) end
  end l w.

(*
Lemma W2n_elim :
  forall Q: forall p, W2' p -> Type,
  (forall p g, (forall i, Q _ (normW _ _ _ (g i))) ->
   Q _ (C2' p (fun i => normW _ _ _ (g i)))) ->
  forall p n l (w:W2 p n l), Q _ (normW _ _ _ w).
induction w; simpl; intros.
*)

Lemma W2'_elim :
  forall Q: forall p, W2' p -> Type,
  (forall (p:P) (g:forall i:B p, W2' (f p i)),
   (forall i:B p, Q (f p i) (g i)) ->
   Q p (C2' p g)) ->
  forall p n l (w:W2 p n l), Q (decn p n l) (normW _ _ _ w).
induction w; simpl.
replace (normW _ _ _ (C2 _ _ _ w)) with
 (C2 (decn p m l) 0 tt (fun i => normW _ _ _ (w i))).

rewrite C2'_surj.
apply X.
intro.
specialize X0 with i.
simpl normW in X0.
simpl decn in X0.

Lemma W2'_elim :
  forall Q:forall p, W2' p -> Type,
  (forall (p:P) (g:forall i:B p, W2' (f p i)),
   (forall i:B p, Q (f p i) (g i)) ->
   Q p (C2' p g)) ->
  forall p (w:W2' p), Q p w.
fix W2'_elim 4.
intros.
rewrite C2'_surj.
apply X.
intro.

*)



(*
Fixpoint apppath p n m : forall l:path n p, path m (decn p n l) -> path (m+n) p :=
  match n return forall l:path n p, path m (decn p n l) -> path (m+n) p with
  | 0 => fun _ l2 => l2
  | S k => fun l l2 =>
      let i' := projT1 l in let l' := projT2 l in existT _ i' (apppath _ k l' l2)
  end.
*)
Definition P' (p:P) : T1 := {n:nat & path p n}.
Definition nilP' p : P' p := existT (fun n => path p n) 0 tt.
Definition consP' p i (q:P' (f p i)) : P' p :=
  let n := projT1 q in let l := projT2 q in existT _ (S n) (existT _ i l).

Definition P'case p (Q:P' p->Type) (q:P' p)
  (h1:Q (nilP' _)) (h2: forall i (q':P' (f p i)), Q (consP' p i q')) : Q q :=
match q return Q q with
| existT 0 tt => h1
| existT (S k) (existT i l) => h2 i (existT _ k l)
end.

(*
Definition P'elim (Q:forall p, P' p -> Type)
 (h1: forall p, Q p (nilP' _))
 (h2: forall p,      Q (consP'
*)

Definition Dec (p:P) (q:P' p) : P :=
  let  n := projT1 q in let l := projT2 q in decn p n l.

Definition extP' p (q:P' p) (i:B(Dec p q)) : P' p :=
  let n := projT1 q in let l := projT2 q in existT _ (S n) (extpath _ _ l i).


Inductive W2 (p:P) : P' p -> T1 :=
  C2 : forall p':P' p, (forall i:B (Dec p p'), W2 p (extP' _ p' i)) -> W2 p p'.

Lemma unC2 :
 forall (p : P) (p' : P' p), W2 p p' ->
       (forall i : B (Dec p p'), W2 p (extP' p p' i)).
destruct 1; assumption.
Defined.

Lemma W2_eta : forall p q (w:W2 p q), w = C2 p q (unC2 p q w).
destruct w; simpl; trivial.
Qed.

Fixpoint liftW2 p i p' (w:W2 (f p i) p') : W2 p (consP' p i p') :=
  C2 _ (consP' p i p') (fun i1 => liftW2 p i _ (unC2 _ _ w i1)).

Fixpoint unliftW2 p i p' (w:W2 p (consP' p i p')) : W2 (f p i) p' :=
  C2 (f p i) p' (fun i1 => unliftW2 p i (extP' _ p' i1) (unC2 _ _ w i1)).


Lemma unlift_lift0 : forall p q (w:W2 p q),
  match q return W2 p q -> Prop with
  | existT 0 _ => fun _ => True
  | existT (S k) (existT i l) => fun w => 
    let q' := existT _ k l : P' (f p i) in
    w = liftW2 p i q' (unliftW2 p i q' w)
  end w.
induction w.
destruct p' as ([|k],l); simpl in *; trivial.
destruct l as (i,l); simpl in *.
set (q := existT (fun n : nat => path n p) (S k)
                     (existT (fun i : B p => path k (f p i)) i l)) in *.
apply f_equal with (f:=C2 p q).
apply fext; intro.
apply H.
Qed.

Lemma unlift_lift : forall p i p' w,
  w = liftW2 p i p' (unliftW2 p i p' w).
intros.
generalize (unlift_lift0 _ _ w).
destruct p'; trivial.
Qed.

Lemma lift_unlift : forall p i p' w,
  w = unliftW2 p i p' (liftW2 p i p' w).
induction w; simpl; intros.
apply f_equal with (f:=C2 (f p i) p').
apply fext; intro.
apply H.
Qed.

(*
Lemma W2q_case :
  forall Q:forall p q, W2 p q -> Type,
  (forall p q, (g:forall i:B (Dec p q), W2 (f _ i) q), Q p (C2' p g)) ->
  forall p q (w:W2 p q), Q p q w.
intros.
pose (g i := unliftW2 p i (nilP' (f p i)) (unC2 _ _ w i)).
pose (q := X _ g).
assert (w = C2' p (fun i => unliftW2 p i (nilP' _) (unC2 _ _ w i))).
 transitivity (C2 _ _ (unC2 _ _ w)).
  apply W2_eta.
 unfold C2'.
 unfold Dec; simpl.
 apply f_equal with (f:=C2 p (nilP' p)).
 apply fext; intro.
 apply (unlift_lift p x (nilP' _)).
rewrite H; exact q.
Qed.
*)


Definition W2' p := W2 p (nilP' p).

Lemma CC p q: W2 p q.
constructor.
intros.

Definition C2' p (g:forall i:B p, W2' (f p i)) : W2' p :=
  C2 p (nilP' p) (fun i => liftW2 p i _ (g i)).

Lemma C2'_surj : forall p (w:W2' p),
  w = C2' p (fun i => unliftW2 p i (nilP' _) (unC2 _ _ w i)).
intros.
transitivity (C2 _ _ (unC2 _ _ w)).
 apply W2_eta.
unfold C2'.
unfold Dec; simpl.
apply f_equal with (f:=C2 p (nilP' p)).
apply fext; intro.
apply (unlift_lift p x (nilP' _)).
Qed.

Lemma W2'_case : forall p (Q:W2' p -> Type),
  (forall (g:forall i:B p, W2' (f p i)), Q (C2' p g)) ->
  forall (w:W2' p), Q w.
intros.
rewrite C2'_surj.
apply X.
Qed.


(**)

Lemma W2'_elim :
  forall Q:forall p, W2' p -> Type,
  (forall (p:P) (g:forall i:B p, W2' (f p i)),
   (forall i:B p, Q (f p i) (g i)) ->
   Q p (C2' p g)) ->
  forall p (w:W2' p), Q p w.
fix W2'_elim 4.
intros.
rewrite C2'_surj.
apply X.
intro.
Show Proof.

apply W2'_elim with (Q:=fun p' w' => Q p' (unliftW2 p i (nilP' _) w')).


(************************************)

Record emb (X:T2) (Y:T1) : T2 := {
  f_ : X -> Y;
  g_ : Y -> X;
  injf : forall x, g_ (f_ x) = x
}.

Record iso (X:T2) (Y:T1) : T2 := {
  f__ : X -> Y;
  g__ : Y -> X;
  injf_ : forall x, g__ (f__ x) = x;
  injg_ : forall y, f__ (g__ y) = y
}.


Definition small (X:T2) := exists Y:T1, exists i:emb X Y, True.

Lemma PI: forall (P:Prop) (p1 p2:P), p1=p2.

Lemma Bs : forall p:P, iso {q:{p:P&B p}|projT1 q = p} (B p).
intros.
exists (fun x:{q:{p:P&B p}|projT1 q=p} =>
     eq_rect _ (fun p' => B p') (projT2 (proj1_sig x)) _ (proj2_sig x))
  (fun i : B p => exist (fun q => projT1 q = p) (existT (fun p' => B p') p i) (eq_refl _));
  simpl; auto.
destruct x as ((p',i),e); simpl.
unfold eq_rect; simpl.
destruct e; simpl.
trivial.
Qed.

Inductive dl (p0:P) : P -> T2 :=
  Ol : dl p0 p0
| Cl : forall (q:{p:P&B p}) (_:dl p0 (f (projT1 q) (projT2 q))), dl p0 (projT1 q).


Lemma smCl :
  forall p0 F,
  (forall (p:P) (i:B p), emb (dl p0 (f p i)) (F p i)) ->
  small {q:{p:P&B p} & dl p0 (f (projT1 q) (projT2 q))}.
intros.
exists {i: F p i


Fixpoint lg p0 p (l:dl p0 p) :=
  match l with
  | Ol => 0
  | Cl _ l' => S (lg _ _ l')
  end.

Lemma smdl : forall p p', small (dl p p').

|

(* non-unif param *)
Inductive W (p:P) : T1 :=
  C : (forall i:B p, W (f p i)) -> W p.

(* In the big univ: *)
Inductive W2 : P->T2 :=
  C2 : forall p, (forall i:B p, W2 (f p i)) -> W2 p.

Lemma Ws : forall p:P, small (W2 p).
Admitted.

Lemma smT1 : forall X:T2, small X -> T1.
Admitted.

Lemma smT1_iso : forall X (s:small X), iso X (smT1 X s).
Admitted.




Definition W' (p:P) : T1 := smT1 _ (Ws p).


Lemma IW : forall p, iso (W2 p) (W' p).
intro.
apply smT1_iso.
Qed.




P : Type_i+1
A : P -> Type_i
B : forall (p:P), A p -> Type_i.
f : forall (p:P) (x:A p) (i:B p x), P


(* non-unif param: *)
Inductive W (p:P) : Type_i :=
 C : forall x:A p, (forall i:B p x, W (f p x i).

(* unif param: *)
Inductive W' (D:P~->P): Type_i :=
 C' : forall (c:P~) (x:A (D c)), (B (D c) x -> W' D). 

(* enforcing deps *)
Inductive OK (w : W' D) (c:P~)


Inductive A' (p:P) : Type_i :=
  TopA (_:A p)
| Below


(Enc,Dec) : forall p:P, {c:P~ & D:P~->P | D c = p}

W p =d { w : W' (Dec p) | OK w (Enc p)



Inductive P~ (p:P) : A p -> Type_i :=
 C~ : forall x:A, (forall i:B x, P~ p) P~ 

Fixpoint D~ (t:P~) (p:P) (x:A p) (i:B :=
  match t with
   C~ x  


p : P
Inductive W : Type
 C :


(***********************************)
(* sans A: *)

P : Type_i+1
B : P -> Type_i


Definition small (X:Type_i+1) := exists Y:Type_i, X=Y.
Definition small' (X:Type_i+1) :=
  exists Y:Type_i, iso X Y.

Definition p2small (

forall p0:P, small {p:{p:P & B p}|projT1 p ==p0} (with iso!)


Definition L0 (p:P) := B p.
Definition L1 (p:P) (i:B p) := B (f p i).
Definition L2 (p:P) (i1:B p) (i2:B (f p i1)) := B (f (f p i1) i2).


Fixpoint Dec (l:list {p:P & B p}) (p:P) : Type_i :=
  match l with
    nil => B p
  | cons (existT p' b) l' => { c:B p' -> B p & Dec l' (f p (c b))}
  end.

Fixpoint Reach (p:P) (X:Type_i) : Prop :=
  exists l, Dec l p = X


Inductive W (p:P) : Type_i :=
  C : (forall i: B p ->p W (f p i)) -> W p.

small 


Inductive W (p:P) : p -> Type_i :=
  C : 


 
Inductive R (p:P) : P -> Prop :=
  R0 : R p p
| RS : forall (p':P), (i:B p'), R p p' -> R p (f p' i).

Inductive Bp (p0:P) : P -> Type_i :=
| B0 : B p0 -> Bp p0 p0
| BS : forall p, Bp p0 p -> B 

Inductive R (p:P) : P -> tree -> Prop :=
 Rtop : R p p 


(* Powerful instance *)
Definition Type_i := Type.

Parameter f : forall X:Type_i, X -> Type_i.

Inductive W (X:Type_i) : Type_i :=
| C : (forall x:X, W (f X x)) -> W X.
