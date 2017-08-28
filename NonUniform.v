Require Export CoqCompat.
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
(* begin hide *)

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

Definition C2hd (p : P) n (l:path p n) (w:W2 p n l) : A(decn _ _ l) :=
  match w in W2 _ n l with
  | C2 m l' x g => x
  end.

Definition C2tl (p : P) n (l:path p n) (w:W2 p n l) : forall(i:B _ (C2hd _ _ _ w)), W2 _ _ (extpath _ _ l _ i) :=
  match w in W2 _ n l return forall i:B _ (C2hd _ _ _ w), W2 _ _ (extpath _ _ l _ i)  with
  | C2 m l' x g => g
  end.

Record P' :T2:= mkP' {
  _p : P;
  _m : nat;
  _l : path _p _m
}.


Definition d (p:P') : P := decn (_p p) (_m p) (_l p).
Definition W3 (p:P') : T1 := W2 (_p p) (_m p) (_l p).
Definition f3 (p:P') (x:A(d p)) (i:B _ x) : P' := mkP' (_p p) (S (_m p)) (extpath _ _ (_l p) x i).
Definition C3 (p:P') (x:A(d p)) (g:forall i:B _ x, W3 (f3 p x i)) : W3 p :=
  C2 (_p p) (_m p) (_l p) x g.

Definition C3hd (p:P') (w:W3 p) : A(d p) := C2hd _ _ _ w.

Definition C3tl (p:P') (w:W3 p) (i:B _ (C3hd _ w)) : W3 (f3 p (C3hd _ w) i) :=
  C2tl _ _ _ w i.

Definition W3_case (p:P') (Q : W3 p -> Type)
  (h:forall (x:A(d p)) (g : forall i : B _ x, W3 (f3 p x i)), Q (C3 p x g)) (w:W3 p) : Q w.
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
     (forall i:B _ x, Q (f3 p x i) (g i)) -> Q p (C3 p x g)) : forall (p:P') (w:W3 p), Q p w.
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


Definition eqi p p' (e:d p = d p') (x:A(d p)) (x':=eq_rect_r A x (eq_sym e)) (i':B(d p') x') : B(d p) x :=
  match e in (_ = y) return (B y (eq_rect_r A x (eq_sym e)) -> B (d p) x) with
  | eq_refl => fun x => x
  end i'.

Lemma eq_ext p p' (e:d p=d p') (x:A(d p)) (x':=eq_rect_r A x (eq_sym e))
    (i':B(d p') x') (i := eqi _ _ e x i') :
  d(f3 p x i) = d(f3 p' x' i').
Admitted.
(*revert x' i' e x i; destruct p' as (p',n',l').
revert p' l'; induction n'; simpl.
 unfold f3 at 2; simpl.
 unfold eqi.
 intros p' l'; change (d(mkP' p' 0 l')) with p'; clear l'.
 intros x' i' e.
 unfold d; simpl.
 revert x' i'; destruct e.
 unfold eq_rect_r; simpl.
 destruct p as (p,n,l); revert p l; induction n; intros.
  simpl; reflexivity.

  simpl in l.
  destruct l as (y,(j,l')).
  apply IHn.

 destruct l' as (x,(i,l')).
 apply IHn'.
Defined.
*)

Lemma eq_ext_refl p x (i:B(d p) x) :
  eq_ext p p eq_refl x i = eq_refl.
Admitted.
(*revert i; destruct p as (p,n,l); revert p l; induction n; simpl; intros; auto.
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
*)
(*
Lemma extpath_trans_prf p p' p'' x x' i (e:d p=d p') (e':d p'=d p'') :
  f3 p x (eq_rect_r B i (eq_trans e e')) =
  f3 p x' (eq_rect_r B (eq_rect_r B i e') e).
revert i; destruct e'; reflexivity.
Defined.

Lemma tr_ext_trans p p' p'' x i (e:d p=d p') (e':d p'=d p'') :
  let x' := x in
  eq_ext p p'' (eq_trans e e') x i =
  eq_trans (f_equal d (extpath_trans_prf p p' p'' i e e'))
    (eq_trans (eq_ext p p' (eq_rect_r B i e') e) (eq_ext p' p'' e' x i)).
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
Fixpoint tr p (w:W3 p) p' (e:d p=d p') {struct w}: W3 p' :=
  let x := C3hd _ w in
  let g := C3tl _ w in
  let x' := eq_rect_r A x (eq_sym e) in
  C3 p' x' (fun i' : B _ x' =>
     let i := eqi _ _ e x i' in
     tr _ (g i) (f3 p' x' i') (eq_ext _ _ e x i')).

Lemma tr_id : forall p w, tr p w p eq_refl = w.
apply W3_elim; simpl; intros; trivial.
unfold eq_rect_r; simpl.
apply f_equal.
apply fext; intros i.
rewrite eq_ext_refl; auto.
Qed.

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
Admitted.
(*revert p' e p'' e'; pattern p, w; apply W3_elim; simpl; intros.
apply f_equal.
apply fext; intro i.
rewrite H.
clear H.
apply tr_comm with (h:=extpath_trans_prf _ _ _ i e e').
 unfold extpath_trans_prf.
 destruct e'; reflexivity.

 apply tr_ext_trans. 
Qed.
*)

Definition W' p : T1 := W3 (i0 p).

(** The constructor *)
Definition C' (p:P) (x:A p) (g:forall i, W' (f p x i)) : W' p := 
  C3 (i0 p) x (fun i : B p x => tr (i0(f p x i)) (g i) (f3 (i0 p) x i) eq_refl).

(** The projection *)
Definition C'hd p (w : W' p) : A p :=
  C3hd _ w.

Definition C'tl p (w : W' p) (i:B p (C'hd _ w)) : W' (f p (C'hd _ w) i) :=
  tr (f3 (i0 p) (C'hd _ w) i) (C3tl (i0 p) w i) (i0 (f p (C'hd _ w) i)) eq_refl.

Lemma W'_surj p (w:W' p) : w = C' _ (C'hd p w) (C'tl p w).
pattern w; apply W3_case; simpl; intros.
unfold C', C'hd, C'tl; simpl.
apply f_equal; apply fext; intros i.
rewrite tr_comp.
simpl eq_trans.
symmetry; apply tr_id.
Defined.

Definition W'_case p (w:W' p) (Q:W' p -> Type)
  (h:forall x (g:forall i:B p x,W' (f p x i)), Q (C' p x g)) : Q w.
rewrite (W'_surj _ w).
apply h.
Defined.

Definition W'_elim0 p (w:W' p) (Q:forall p, W' p -> Type)
  (h : forall p x (g:forall i,W' (f p x i)), (forall i, Q (f p x i) (g i)) -> Q p (C' p x g)) :
  forall p' (e:d(i0 p)=p'), Q p' (tr _ w (i0 p') e).
unfold W' in w.
pattern (i0 p), w.
apply W3_elim; clear p w; intros.
rewrite W'_surj.
apply h.
intros.
unfold C'hd, C'tl;simpl.
rewrite tr_comp; simpl.
apply X.
Defined.

Definition W'_elim p (w:W' p) (Q:forall p, W' p -> Type)
  (h : forall p x (g:forall i,W' (f p x i)),
       (forall i, Q _ (g i)) -> Q _ (C' p x g)) : Q p w.
rewrite <- (tr_id _ w).
apply W'_elim0; trivial.
Defined.

Lemma C'tl_eq p x g : C'tl p (C' p x g) = g.
unfold C'tl, C'; simpl.
apply fext; intros i.
rewrite tr_comp.
simpl eq_trans.
apply tr_id.
Qed.

(** Proving the reduction is correct (non-dep!) *)
Lemma W'_case_nodep_eqn p Q x g h : W'_case p (C' p x g) (fun _=>Q) h = h x g.
unfold W'_case.
simpl in h.
unfold eq_rect_r, eq_rect.
generalize (eq_sym (W'_surj p (C' p x g))).
unfold C'hd; simpl.
rewrite (C'tl_eq p x g).
intro e.
change ((fun w (e':C' p x g=w) =>
     match e' in (@eq _ _ y) return Q with
     | eq_refl => h x g
     end = h x g) (C' p x g) e).
case e; reflexivity.
Qed.

Lemma W'_elim_nodep_eqn p Q x g h :
  W'_elim p (C' p x g) (fun _ _=>Q) h =
  h p x g (fun i => W'_elim _ (g i) (fun _ _=>Q) h).
unfold W'_elim.
simpl in h.
unfold eq_rect_r, eq_rect.
Admitted.

End WithPayload.

(* end hide *)