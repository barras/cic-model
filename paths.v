Require Import Sublogic.

Infix "*" := eq_trans.

(** Groupoid laws *)

Lemma eq_sym_sym {A} {x y:A} (e:x=y) : eq_sym (eq_sym e) = e.
destruct e; reflexivity.
Defined.

Lemma eq_trans_idl {A} {x y:A} (e:x=y) : eq_refl * e = e.
destruct e; reflexivity.
Defined.

Lemma eq_trans_assoc {A} {x y z t:A} (e1:x=y)(e2:y=z)(e3:z=t) :
  (e1 * e2) * e3 = e1 * (e2 * e3).
destruct e3; destruct e2; reflexivity.
Defined.  

Lemma eq_sym_invl {A} {x y:A} (e:x=y) : eq_sym e * e = eq_refl.
destruct e; reflexivity.
Qed.

Lemma eq_sym_invr {A} {x y:A} (e:x=y) : e * eq_sym e = eq_refl.
destruct e; reflexivity.
Qed.

Lemma eq_sym_trans {A} {x y z:A} (e1:x=y)(e2:y=z) :
  eq_sym (e1*e2) = eq_sym e2 * eq_sym e1.
destruct e2; simpl.
symmetry; apply eq_trans_idl.
Defined.

Lemma eq_trans_rr2l {A} {x y z:A} (e:x=z) (e1:x=y) (e2:y=z) :
  e = e1 * e2 ->
  e * eq_sym e2 = e1.
intros; subst e.
rewrite eq_trans_assoc, eq_sym_invr; trivial.
Qed.

(** f_equal *)

Lemma f_equal_trans {A B} (f:A->B) {x y z:A} (e1:x=y) (e2:y=z) :
  f_equal f (e1 * e2) = f_equal f e1 * f_equal f e2.
destruct e2; reflexivity.
Qed.  

Lemma f_equal_sym {A B} (f:A->B) {x y:A} (e:x=y) :
  f_equal f (eq_sym e) = eq_sym (f_equal f e).
destruct e; reflexivity.
Qed.

Lemma f_equal_compose {A B C} (f:B->C) (g:A->B) {x y:A} (e:x=y) :
  f_equal f (f_equal g e) = f_equal (fun x=>f (g x)) e.
destruct e; reflexivity.
Qed.

Lemma f_equal_id {A} {x y:A} (e:x=y) :
  f_equal (fun x => x) e = e.
destruct e; reflexivity.
Qed.

Lemma f_equal_cst {A B} (b:B) {x y:A} (e:x=y) :
  f_equal (fun _ => b) e = eq_refl.
destruct e; reflexivity.
Qed.

Lemma f_equal_eq {A B} (f g:A->B) (h:forall x, f x = g x) {x y:A} (e:x=y) :
   f_equal f e = h x * (f_equal g e * eq_sym (h y)).
destruct e; simpl.
rewrite eq_trans_idl.
symmetry; apply eq_sym_invr.
Qed.

Lemma f_eq {A} {x y:A} {B} (f g:A->B) (h:forall x:A, f x = g x) (e:x=y) :
  h x = f_equal f e * (h y * eq_sym (f_equal g e)).
destruct e; simpl.
symmetry; apply eq_trans_idl.
Qed.

Lemma f_equal_qid {A} (f:A->A) (h:forall x, f x = x) {x y:A} (e:x=y) :
  f_equal f e =  h x * (e * eq_sym (h y)).
rewrite f_eq with (h0:=h) (e0:=e).
rewrite f_equal_id.
rewrite !eq_trans_assoc.
rewrite <-eq_trans_assoc with (e1:=eq_sym e), eq_sym_invl, eq_trans_idl.
rewrite eq_sym_invr; trivial.
Qed.

Lemma f_equal_qid' {A} (f:A->A) (h:forall x, f x = x) x :
   f_equal f (h x) = h (f x).
rewrite f_equal_qid with (h0:=h).
rewrite eq_sym_invr; trivial.
Qed.

(** Transport *)
  
Definition transport {A} (P:A->Type) {x y} (e:x=y) (h:P x) : P y :=
  eq_rect _ P h _ e.
Definition coe : forall {A B}, A=B -> A -> B := @transport _ (fun X=>X).

Definition eqD {A} (P:A->Type) {x y} (e:x=y) (h1:P x) (h2:P y) : Prop :=
  transport P e h1 = h2.

Lemma transport_trans {A} P {x y z:A} (e1:x=y)(e2:y=z) :
  transport P (e1*e2) = fun h => transport P e2 (transport P e1 h).
destruct e2; reflexivity.
Qed.

Lemma transport_cst {A P}{x y:A}(e:x=y)(h:P) :
   transport (fun _ => P) e h = h.
destruct e; reflexivity.
Qed.

Lemma transport_r2l {A x y} P (e:x=y:>A) (h:P y) (h':P x) :
  h = transport P e h' ->
  transport P (eq_sym e) h = h'.
revert h; destruct e; trivial.
Qed.  

Lemma transport_f_equal A B (P:B->Type) (f:A->B) x y (e:x=y) h :
  transport P (f_equal f e) h = transport (fun x => P (f x)) e h.
destruct e; reflexivity.
Defined.  

Lemma transport_eq {A} {x y:A} {B} (f g:A->B) (e:x=y) (h:f x = g x):
  transport (fun x => f x = g x) e h =
  eq_sym (f_equal f e) * (h * f_equal g e).
destruct e; simpl.
symmetry; apply eq_trans_idl.
Defined.


(** Set equivalences (isomorphisms) *)

Record retr (A B:Type) := mkR { rf : A->B; rg : B->A; rgf:forall a,rg(rf a)=a }.

Record eqv (A B:Type) :=
  mkE { ef : A->B;eg:B->A;egf:forall a,eg(ef a)=a;efg:forall b,ef(eg b)=b}.
Arguments mkE {A} {B} ef eg _ _.
Arguments ef {A} {B} e _.
Arguments eg {A} {B} e _.
Arguments egf {A} {B} e a.
Arguments efg {A} {B} e b.

Definition eqv2retr {A B} (E:eqv A B) : retr A B :=
  mkR _ _ (ef E) (eg E) (egf E).

Definition eqv_refl A : eqv A A :=
  mkE (fun x=>x) (fun x=>x) (fun _ => eq_refl) (fun _ => eq_refl).

Definition eqv_sym {A B} (E:eqv A B) : eqv B A :=
  mkE _ _ (efg E) (egf E).

Definition eqv_trans {A B C} (E1:eqv A B) (E2:eqv B C) : eqv A C :=
  mkE (fun a => ef E2 (ef E1 a)) (fun b => eg E1 (eg E2 b))
      (fun a => f_equal (eg E1) (egf E2 (ef E1 a)) * egf E1 a)
      (fun c => f_equal (ef E2) (efg E1 (eg E2 c)) * efg E2 c).

Definition eqv_loop {A B} (E:eqv A B) (b:B) : ef E (eg E b) = ef E (eg E b) :=
  eq_sym (efg E (ef E (eg E b))) * f_equal (ef E) (egf E (eg E b)).

Definition efg' {A B} (E:eqv A B) (b:B) : ef E (eg E b) = b :=
  eqv_loop E b * efg E b.  

Definition weqv A B :=
  {E:eqv A B & forall a, f_equal (ef E) (egf E a) = efg E (ef E a)}.

Definition eqv_cano {A B} (E:eqv A B) : eqv A B :=
  mkE (ef E) (eg E) (egf E) (efg' E).

Lemma weqv_from_eqv {A B} (E:eqv A B) : weqv A B.
exists (eqv_cano E).  
intros a.
destruct E as (f,g,gf,fg).
simpl.
unfold efg', eqv_loop; simpl.
specialize f_eq with (h:=fun a=>fg(f a)) (e:=gf a); intros e.
rewrite <- f_equal_compose with (f0:=f) (g0:=fun a=>g(f a)) in e.
rewrite f_equal_qid' with (h:=gf) (x:=a) in e.
rewrite <- eq_trans_assoc in e.
apply eq_trans_rr2l in e.
rewrite eq_sym_sym in e.
rewrite eq_trans_assoc, <- e.
rewrite <- eq_trans_assoc, eq_sym_invl, eq_trans_idl; trivial.
Defined.

Lemma eqv_singl_pred {A} {P:A->Type} (x:A) :
  eqv (P x) {xp:sigT P & projT1 xp = x}.
exists (fun p => existT (fun xp => projT1 xp =x) (existT P x p) eq_refl)
       (fun t:{xp:sigT P & projT1 xp=x} =>
           transport P (projT2 t) (projT2 (projT1 t))).
 simpl; intros; trivial.

 intros ((x',p),e); simpl.
 destruct e; reflexivity.
Defined.

Lemma weqv_singl_pred {A} {P:A->Type} (x:A) :
  weqv (P x) {xp:sigT P & projT1 xp = x}.
exists (eqv_singl_pred x); simpl; reflexivity.
Qed.

(****)

Definition f_app {A} {B:A->Type} {f g:forall x, B x} (e:f=g) x : f x = g x :=
  f_equal (fun f => f x) e.
Definition f_eqD {A} {B:A->Type} (f:forall x, B x) {x y} (e:x=y) :
    eqD B e (f x) (f y) :=
  match e with eq_refl => eq_refl end.

Lemma transport_dom A a b (e:a=b:>A) Y (f:A->Type) (g:f a->Y):
  transport (fun X => f X -> Y) e g =
  fun x => g (transport f (eq_sym e) x).
destruct e.
reflexivity.
Qed.
Lemma transport_rng A B (C:A->B->Type) (x1 x2:A) (e:x1=x2) (f:forall y:B, C x1 y) :
  transport (fun x => forall y:B, C x y) e f =
  fun y:B => transport (fun x => C x y) e (f y).
destruct e.
reflexivity.
Defined.
Lemma transport_app A B C (f g:A->B) (e:f=g) (a:A) h :
  transport (fun f:A->B => C (f a)) e h =
  transport C (f_app e a) h.
destruct e; reflexivity.
Defined.  

(****)

Lemma sigT_eq_intro {A B} (p q:@sigT A B) (e:projT1 p = projT1 q) :
   eqD B e (projT2 p) (projT2 q) ->
   p = q.
destruct p as (p1,p2); destruct q as (q1,q2); simpl in *.
destruct e; simpl; intros.
red in H; simpl in H.
rewrite H; reflexivity.
Defined.
Definition sigT_proj1 {A B} {p q:@sigT A B} (e:p=q) : projT1 p = projT1 q :=
  f_equal _ e.
Definition sigT_proj2 {A B} {p q:@sigT A B} (e:p=q) :
    eqD B (sigT_proj1 e) (projT2 p) (projT2 q) :=
  match e with eq_refl => eq_refl end.
Lemma sigT_eq {A B} (p q:@sigT A B) (e:projT1 p = projT1 q) :
   eqD B e (projT2 p) (projT2 q) ->
   p = q.
destruct p as (p1,p2); destruct q as (q1,q2); simpl in *.
destruct e; simpl; intros.
red in H; simpl in H.
rewrite H; reflexivity.
Qed.
Lemma sigT_intro_proj1 {A P} (p q:@sigT A P) e1 e2 :
 sigT_proj1 (sigT_eq_intro p q e1 e2) = e1.
unfold sigT_eq_intro; simpl.
destruct p; destruct q; simpl in *.
revert e2; destruct e1; simpl; intros.
destruct e2.
reflexivity.
Qed.
Lemma sigT_proj1_intro {A P}
      {p q:@sigT A P} (e:p=q) :
  e = sigT_eq_intro p q (sigT_proj1 e) (sigT_proj2 e).
destruct e.
simpl.
unfold sigT_eq_intro.
destruct p as (p,t); simpl.
reflexivity.
Qed.

Definition sig_proj1 {A B} {p q:@sig A B} (e:p=q) : proj1_sig p = proj1_sig q :=
  f_equal _ e.
Definition sig_proj2 {A B} {p q:@sig A B} (e:p=q) :
    eqD B (sig_proj1 e) (proj2_sig p) (proj2_sig q) :=
  match e with eq_refl => eq_refl end.
Lemma sig_eq {A B} (p q:@sig A B) (e:proj1_sig p = proj1_sig q) :
   eqD B e (proj2_sig p) (proj2_sig q) ->
   p = q.
destruct p as (p1,p2); destruct q as (q1,q2); simpl in *.
destruct e; simpl; intros.
red in H; simpl in H.
rewrite H; reflexivity.
Qed.


  
Lemma eqv_projT2 {A} {P Q:A->Type} (E:weqv (sigT P) (sigT Q)) :
  (forall xp, projT1 (ef (projT1 E) xp) = projT1 xp) ->
  forall x, eqv (P x) (Q x).
intros eq1 x.
pose (eq2 := fun xq => eq_sym (eq1 _) * f_equal (projT1(P:=Q)) (efg (projT1 E) xq)).
apply @eqv_trans with (B:={xp:sigT P & projT1 xp=x}).
 apply eqv_singl_pred.
apply @eqv_trans with (B:={xp:sigT Q & projT1 xp=x}).
 2:apply eqv_sym; apply eqv_singl_pred.
pose (f := ef (projT1 E)).
pose (g := eg (projT1 E)).
pose (gf := egf (projT1 E)).
pose (fg := efg (projT1 E)).
assert (coh := projT2 E); simpl in coh.
exists (fun t:{xp:sigT P & projT1 xp=x} =>
          existT (fun xq => projT1 xq=x) (f (projT1 t))
            (eq1 _ * projT2 t))
       (fun t:{xq:sigT Q & projT1 xq=x} =>
          existT (fun xp => projT1 xp=x) (g (projT1 t)) 
            (eq2 _ * projT2 t)).
 simpl.
 intros (xp,e); simpl.
 destruct e; simpl.
 eapply sigT_eq_intro with (e:=gf xp); simpl.
 red; unfold eq2.
 rewrite <- coh, f_equal_compose; simpl.
 rewrite transport_eq, f_equal_cst; simpl.
 rewrite f_equal_eq with (h:=eq1).
 rewrite !eq_trans_assoc.
 rewrite eq_sym_invl; simpl.
 rewrite <- eq_trans_assoc.
 rewrite <- eq_sym_trans.
 apply eq_sym_invl.

 simpl.
 intros (xq,e); simpl.
 destruct e; simpl.
 eapply sigT_eq_intro with (e:=fg xq); simpl.
 red; unfold eq2.
 rewrite transport_eq, f_equal_cst; simpl.
 rewrite <- eq_trans_assoc with (e1:=eq1(g xq)).
 rewrite eq_sym_invr, eq_trans_idl.
 apply eq_sym_invl.
Defined.

(*
  
  Lemma eqv_proj2' {A} {P Q:A->Type} (f:forall x:A,P x -> Q x) (g:sigT Q->sigT P)
  (f' := fun xp => existT Q (projT1 xp) (f (projT1 xp) (projT2 xp)))
  (gf : forall xp, g (f' xp) = xp)
  (fg : forall xq, f' (g xq) = xq) :
  (forall xp, f_equal f' (gf xp) = fg (f' xp)) ->
  forall x, eqv (P x) (Q x).
intros coh x.
exists (f x)
       (fun q => let x' := g (existT Q x q) in
                 let e : projT1 x' = x :=
                   f_equal (@projT1 _ _) (fg (existT Q x q)) in
                 transport P e (projT2 x')).
 simpl; intros p.  
 set (xq := existT Q x (f x p)).
 change xq with (f' (existT P x p)).
 rewrite <- coh.
 rewrite f_equal_compose; simpl.
 apply (sigT_proj2 (gf (existT P x p))).

 simpl; intros q.
 assert (aux := sigT_proj2 (fg (existT Q x q))).
 red in aux.
 simpl in aux.
 change (f_equal (projT1(P:=Q)) (fg (existT Q x q))) with
     (sigT_proj1 (fg (existT Q x q))).
 apply eq_trans with (2:=aux).
 generalize (sigT_proj1 (fg (existT Q x q))).
 simpl.
 set (xp := g (existT Q x q)).
 clearbody xp.
 intros.
 destruct e; reflexivity.
Defined.
*)
