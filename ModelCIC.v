(** Model of CIC in the type-based termination presentation.
*)
(* Work in progress. *)

Require Import List Bool Models.
Require Import ZF ZFsum ZFnats ZFrelations ZFord ZFfix ZFgrothendieck.
Require Import ZFfunext ZFind_wnup ZFspos_nup.
Require Import ModelZF ModelECC.

Import BuildModel.
Import T J R.

Require Import Model_variance.

(** Ordinals *)

Definition Ordt (o:set) : term := cst o.

Definition typ_ord_kind : forall e o, typ e (Ordt o) kind.
red; simpl; trivial.
Qed.

Lemma tyord_inv : forall e i o o',
  isOrd o' ->
  typ e o (Ordt o') ->
  val_ok e i ->
  isOrd (int o i) /\ int o i < o'.
unfold typ; simpl; intros.
unfold ZFnats.lt.
red in H0.
split; auto.
apply isOrd_inv with o'; trivial.
apply H0; trivial.
Qed.

Definition OSucc : term -> term.
(*begin show*)
intros o; left; exists (fun i => osucc (int o i)).
(*end show*)
do 2 red; intros.
rewrite H; reflexivity.
Defined.

  Lemma var_mono_OSucc : forall e O,
    var_mono e O ->
    var_mono e (OSucc O).
unfold var_mono; red; simpl; intros.
unfold osucc in H1|-*.
rewrite subset_ax in H1 |-*.
destruct H1; split; auto.
revert H1; apply power_mono.
red; intros; eauto.
revert H1; apply H; trivial.
Qed.

  Lemma typ_mono_OSucc : forall e O o,
    isOrd o ->
    typ_mono e O (Ordt o)->
    typ_mono e (OSucc O) (Ordt (osucc o)).
destruct 2.
split.
 apply var_mono_OSucc; trivial.

 red; simpl; intros.
 red.
 destruct tyord_inv with (2:=H1)(3:=H2) as (_,?); trivial.
 apply lt_osucc_compat; trivial.
Qed.

(** General substitutions *)
(*
Definition Sub (t:term) (s:val->val) {sm : Proper (eq_val==>eq_val) s} : term.
(* begin show *)
destruct t as [(t,tm)|];
 [left; exists (fun i => t (s i))|right].
(* end show *)
do 2 red; intros; auto.
Defined.

Definition typ_sub (e:env) (s:val->val) (f:env) :=
  forall i, val_ok e i -> val_ok f (s i).

Lemma typ_Sub e f s m u (sm: Proper (eq_val==>eq_val) s) :
  typ f m u ->
  typ_sub e s f ->
  typ e (Sub m s) (Sub u s).
unfold typ, typ_sub; intros.
destruct u as [(u,um)|]; simpl in *; trivial.
 simpl.
 destruct m as [(m,mm)|]; simpl in *; auto.
Qed.
*)

(** *)
Definition Op1 (f:set->set) {fm:morph1 f} (t:term) : term.
(* begin show *)
left; exists (fun i => f (int t i)).
(*end show*)
do 2 red; intros.
apply fm; apply int_morph; auto with *.
Defined.

Definition Op2 (f:set->set->set) {fm:morph2 f} (t1 t2:term) : term.
(* begin show *)
left; exists (fun i => f (int t1 i) (int t2 i)).
(*end show*)
do 2 red; intros.
apply fm; apply int_morph; auto with *.
Defined.

(** Syntax for telescopes *)

Require Import ZFpairs.


Definition Sigma (A B:term) : term.
(*begin show*)
left; exists (fun i => sigma (int A i) (fun x => int B (V.cons x i))).
(*end show*)
do 2 red; simpl; intros.
apply sigma_ext.
 rewrite H; reflexivity.
(**)
 red; intros.
 rewrite H; rewrite H1; reflexivity.
Defined.

Global Instance Sigma_morph : Proper (eq_term ==> eq_term ==> eq_term) Sigma.
unfold Sigma; do 5 red; simpl; intros.
apply sigma_ext.
 apply int_morph; auto.

 red; intros.
 rewrite H0; rewrite H1; rewrite H3; reflexivity.
Qed.

Definition val_couple : sub.
exists (fun i => V.cons (couple (i 1) (i 0)) (V.shift 2 i)).
(*
Instance val_couple_morph : Proper (eq_val==>eq_val) val_couple.*)
do 2 red; intros.
(*unfold val_couple.*)
apply V.cons_morph.
 apply couple_morph; apply H.
 rewrite H; reflexivity.
Defined.

Lemma typs_val_couple e A B :
  A <> kind ->
  B <> kind ->
  typ_sub (B::A::e) val_couple (Sigma A B::e).
intros Ank Bnk.
red; intros.
red; intros.
destruct n as [|n]; simpl in *.
 unfold val_couple.
 injection H0; clear H0; intros; subst T.
 simpl.
 apply couple_intro_sigma.
  do 2 red; intros.
  rewrite H1; reflexivity.

  assert (ty1 := H 1 _ eq_refl).
  apply in_int_not_kind in ty1; trivial.
  revert ty1; apply eq_elim.
  unfold lift; rewrite int_lift_rec_eq.
  reflexivity.
  destruct A as [(?,?)|];[discriminate|elim Ank; reflexivity].

  assert (ty0 := H 0 _ eq_refl).
  apply in_int_not_kind in ty0; trivial.
  revert ty0; apply eq_elim.
  unfold lift; rewrite int_lift_rec_eq.
  apply int_morph.
   reflexivity.

   do 2 rewrite V.lams0.
   intros [|n]; simpl; reflexivity.
  destruct B as [(?,?)|];[discriminate|elim Bnk; reflexivity].

 assert (ty := H (S (S n)) _ H0).
 destruct T as [(T,Tm)|]; simpl in *; auto.
Qed.

Definition SCouple t := Sub t val_couple.

(*Parameter cons_vect : nat -> set -> val -> val.*)
Fixpoint cons_vect n v i :=
  match n with
  | O => i
  | S n' => cons_vect n' (snd v) (V.cons (fst v) i)
  end.

Instance cons_vect_morph : Proper (eq==>eq_set==>eq_val==>eq_val) cons_vect.
do 4 red; intros.
subst y.
unfold cons_vect.
revert x0 y0 H0 x1 y1 H1; induction x; simpl; intros; auto.
apply IHx.
 apply snd_morph; trivial.
rewrite H1,H0; reflexivity.
Qed.

Definition ctxt := list term.

Fixpoint push_ctxt (e:env) (ctx:ctxt) : env :=
  match ctx with
  | nil => e
  | ty :: ctx' => push_ctxt (ty::e) ctx'
  end.

Fixpoint push_rev_ctxt (e:env) (ctx:list term) : env :=
  match ctx with
  | nil => e
  | ty :: ctx' => ty ::push_rev_ctxt e ctx'
  end.

Definition ctxt_of (l:list term) : ctxt := l.  (* newest bindings at bottom of list *)
(*Definition ctxt_of (l:list term) : ctxt := List.rev l*)  (* newest bindings at top of list *)

Fixpoint subst_ctxt k v e :=
  match e with
  | nil => nil
  | ty::e' => subst_rec v k ty :: subst_ctxt (S k) v e'
  end.

Fixpoint lift_ctxt k v e :=
  match e with
  | nil => nil
  | ty::e' => lift_rec v k ty :: lift_ctxt (S k) v e'
  end.

(*Parameter vect_of_ctxt : nat -> ctxt -> list term.*)
Fixpoint vect_of_ctxt n (e:ctxt) : list term :=
  match e with
  | nil => nil
  | ty::e' => Ref (n+List.length e') :: vect_of_ctxt n e'
  end.
Fixpoint vect_of_ctxt' n (e:nat) : list term :=
  match e with
  | 0 => nil
  | S e' => Ref (n+e') :: vect_of_ctxt' n e'
  end.
(*Fixpoint vect_of_ctxt n (e:ctxt) : list term :=
  match e with
  | nil => nil
  | ty::e' => List.app (vect_of_ctxt (S n) e') (Ref n :: nil)
  end.
Fixpoint vect_of_ctxt' n (e:nat) : list term :=
  match e with
  | 0 => nil
  | S e' => List.app (vect_of_ctxt' (S n) e') (Ref n :: nil)
  end.
*)

Lemma typ_sub_shift e ctx :
  typ_sub (push_ctxt e ctx) (sub_shift (List.length ctx)) e.
revert e.
induction ctx; simpl; intros.
 red; intros; auto.

 red; intros.
 apply IHctx in H.
 intros n T h.
 generalize (H (S n) T h).
 destruct T as [(T,Tm)|]; simpl; auto.
 do 2 rewrite V.lams0.
 unfold V.shift; simpl.
 rewrite plus_n_Sm.
 apply eq_elim.
 apply Tm.
 intro k.
 rewrite <- plus_n_Sm; reflexivity.
Qed.

(*Parameter mksig : ctxt -> term.*)
Fixpoint mksig (e:ctxt) : term :=
  match e with
   nil => cst(singl empty)
  | ty :: e' => Sigma ty (mksig e')
  end.
Notation mksigi e i := (int (mksig e) i).
(*Fixpoint mksigi (e:ctxt) (t:val->set) i : set :=
  match e with
   nil => t i
  | ty :: e' => mksigi e' (fun i => sigma (int ty i) (fun x => t (V.cons x i))) i
  end.*)

Eval simpl in fun A B C i (*f*) => mksigi (A::B::C::nil) (*f*) i.

Lemma subst_ctxt_eq k v e i :
  mksigi (subst_ctxt k v e) i == mksigi e (V.lams k (V.cons (int v (V.shift k i))) i).
revert k i; induction e; simpl; intros; auto with *.
apply sigma_morph.
 apply int_subst_rec_eq.

 red; intros.
 rewrite IHe.
 apply int_morph.
  reflexivity.
 rewrite V.cons_lams.
  apply V.lams_morph; trivial.
   apply V.cons_morph.
   reflexivity.
  rewrite H; reflexivity.

  apply V.cons_morph.
  reflexivity.
Qed.
Lemma lift_ctxt_eq k v e i :
  mksigi (lift_ctxt k v e) i == mksigi e (V.lams k (V.shift v) i).
revert k i; induction e; simpl; intros; auto with *.
apply sigma_morph.
 apply int_lift_rec_eq.

 red; intros.
 rewrite IHe.
 apply int_morph.
  reflexivity.
 rewrite V.cons_lams.
  apply V.lams_morph; trivial.
   apply V.shift_morph; trivial.
  rewrite H; reflexivity.

  apply V.shift_morph.
  reflexivity.
Qed.


Lemma cons_vect_typ e i a ctxt :
  val_ok e i ->
  a ∈ mksigi ctxt i ->
  val_ok (push_ctxt e ctxt) (cons_vect (List.length ctxt) a i).
revert e i a.
induction ctxt; simpl; intros; auto.
apply sigma_elim in H0.
destruct H0 as (_&ty1&ty2).
apply IHctxt; auto.
apply vcons_add_var; auto.
do 2 red; intros.
apply int_morph; auto with *.
rewrite H2; reflexivity.
Qed.

 

(*Parameter mkprod : ctxt -> term -> term.*)
Fixpoint mkprod (e:ctxt) (ty:term) : term :=
  match e with
  | a::e' => Prod a (mkprod e' ty)
  | nil => ty
  end.


(*Parameter mkvect : list term -> val -> set.*)
Fixpoint mkvect (v:list set) : set :=
  match v with
  | nil => empty
  | a::v' => couple a (mkvect v')
  end.
(* If |- arg : ctxt, then |- mkvect arg : mksig ctxt *)

Instance mkvect_morph : Proper (list_eq eq_set ==> eq_set) mkvect.
do 2 red; induction 1; simpl; auto with *.
apply couple_morph; trivial.
Qed.

Definition mkvecti (v:list term) (i:val) : set :=
  mkvect (List.map (fun t => int t i) v).

Instance mkvecti_morph : Proper (list_eq eq_term ==> eq_val ==> eq_set) mkvecti.
unfold mkvecti.
do 3 red; induction 1; simpl; intros; auto with *.
apply couple_morph; auto.
apply int_morph; trivial.
Qed.

Definition typ_ctxt (e:env) (v:list term) (ctx:ctxt) :=
  forall i, val_ok e i -> mkvecti v i ∈ mksigi ctx i.

Lemma typc_nil e : typ_ctxt e nil nil.
red; simpl; intros.
apply singl_intro.
Qed.
(*
Lemma mksigi_morph1 : forall e, Proper (eq_val ==> eq_set) (mksigi e).
induction e; simpl.
do 2 red; intros.
Admitted.
*)

Lemma typc_cons e a v ty ctx :
   ty <> kind ->
   typ e a ty ->
   typ_ctxt e v (subst_ctxt 0 a ctx) ->
   typ_ctxt e (a::v) (ty::ctx).
unfold typ_ctxt; simpl; intros.
unfold mkvecti; simpl.
apply couple_intro_sigma; auto.
 do 2 red; intros.
 apply int_morph.
  reflexivity.
 rewrite H4; reflexivity.

 apply in_int_not_kind; auto.

 generalize (H1 _ H2); apply eq_elim.
 rewrite subst_ctxt_eq.
 apply int_morph.
  reflexivity.
 rewrite V.lams0.
 reflexivity.
Qed.

Lemma typc_elim e a v ty ctx :
   typ_ctxt e (a::v) (ty::ctx) ->
   typ e a ty /\
   typ_ctxt e v (subst_ctxt 0 a ctx).
split; red; intros.
 apply H in H0.
 simpl in H0.
 apply in_int_el.
 apply fst_typ_sigma in H0.
 unfold mkvecti in H0; simpl in H0.
 rewrite fst_def in H0.
 trivial.

 apply H in H0.
 unfold mkvecti in H0; simpl in H0.
 apply sigma_elim in H0.
  destruct H0 as (_ & _ & ?).
  rewrite snd_def in H0.
  revert H0; apply eq_elim.
  rewrite subst_ctxt_eq.
  apply int_morph.
   reflexivity.
  rewrite V.lams0.
  apply V.cons_morph.
  2:reflexivity.
  rewrite fst_def.
  reflexivity.

 do 2 red; intros.
 apply int_morph.
  reflexivity.
 rewrite H2; reflexivity.
Qed.


(** Packs [n] last args of val into a vector *)
Fixpoint val_mkblock n i : val :=
  match n with
  | 0 => V.cons empty i
  | S n' => val_couple (val_mkblock n' i)
  end.

Instance val_mkblock_morph n : Proper (eq_val==>eq_val) (val_mkblock n).
induction n; simpl; intros.
 apply V.cons_morph; reflexivity.

 do 2 red; intros.
 apply (sub_m val_couple); auto.
Qed.

Definition sub_mkblock (n:nat) : sub := mkSub (val_mkblock n) (val_mkblock_morph n).

Lemma val_ok_mkblock e ctx :
  List.Forall (fun ty => ty <> kind) ctx ->
  typ_sub (push_ctxt e ctx) (sub_mkblock (List.length ctx)) (mksig ctx :: e).
revert e; induction  ctx; simpl.
 red; intros.
 apply vcons_add_var; auto.
 apply singl_intro.

 red; intros.
 inversion_clear H.
 apply typs_val_couple; trivial.
  destruct ctx; discriminate.
 apply IHctx; trivial.
Qed.



Fixpoint Absn (c:ctxt) (t:term) : term :=
  match c with
  | nil => t
  | ty :: c' => Abs ty (Absn c' t)
  end.

Lemma typ_Absn e c m u :
  u <> kind ->
  typ (push_ctxt e c) m u ->
  typ e (Absn c m) (mkprod c u).
intros u_nk; revert e.
induction c; simpl; intros; trivial.
apply typ_abs; auto.
destruct c.
 trivial.
 discriminate.
Qed.



(*Parameter mkapp : term -> list term -> term.*)
Fixpoint mkapp t args :=
  match args with
  | nil => t
  | a::args' => mkapp (App t a) args'
  end.



(*Parameter mktag : nat -> set -> set.*)
Fixpoint mktag n b :=
  match n with
  | 0 => inl b
  | S n' => inr (mktag n' b)
  end.

(*
Definition lam_ctxt (e:ctxt) (t:val->set) : val -> set

Definition lam_ctxt_obj (e:ctxt) (t:set->set) : val -> set :=
  List.fold_left
    (fun k ty v i => cc_lam (int ty i) (fun x => k (x::v) (V.cons x i)))
    e
    (fun v i => t (mkvect (List.rev v)))
    nil.






Definition lam_ctxt_obj (e:ctxt) (t:set->set) : val -> set :=
  List.fold_left
    (fun k ty v i => cc_lam (int ty i) (fun x => k (x::v) (V.cons x i)))
    e
    (fun v i => t (mkvect (List.rev v)))
    nil.
 
(* If Γ |- t : A, then |- lam_ctxt(Γ,t) : Π Γ. A
     with app(lam_ctxt(Γ,t),v) == t(mkvect v) *)
*)


Require Import ZFcoc.

Hint Resolve ZFecc.ecc_grot.
Lemma grot_ecc_S n :
  grot_univ (grot_succ (ZFecc.ecc n)).
Proof (ZFecc.ecc_grot (S n)).
Hint Resolve grot_ecc_S.
Lemma grot_ecc_omega n :
  omega ∈ grot_succ (ZFecc.ecc n).
change (omega ∈ ZFecc.ecc (S n)).
apply G_incl with (ZFecc.ecc n); auto.
 apply ZFecc.ecc_in2.

 apply ZFecc.omega_incl_ecc.
Qed.
Hint Resolve grot_ecc_omega.
Lemma grot_ecc_mt n :
  empty ∈ grot_succ (ZFecc.ecc n).
apply G_trans with omega; auto.
apply zero_omega.
Qed.
Hint Resolve grot_ecc_mt.

(** Syntax of inductive definitions *)

Inductive constr_arg :=
| CA_Const (ty:term)
| CA_Rec (idx:ctxt) (inst:list term).

Inductive eq_ca : relation constr_arg :=
| Eqca_const ty1 ty2 : eq_term ty1 ty2 -> eq_ca (CA_Const ty1) (CA_Const ty2)
| Eqca_rec idx1 idx2 inst1 inst2 :
    list_eq eq_term idx1 idx2 ->
    list_eq eq_term inst1 inst2 ->
    eq_ca (CA_Rec idx1 inst1) (CA_Rec idx2 inst2).

Instance eq_ca_equiv : Equivalence eq_ca.
split; red; intros.
 destruct x; constructor; auto with *.

 destruct H; constructor; auto with *.

 destruct H; inversion_clear H0; constructor.
  transitivity ty2; trivial.
  transitivity idx2; trivial.
  transitivity inst2; trivial.
Qed.

Record constructor := mkCstr {
  cstr_args : list constr_arg;
  cstr_inst : list term
}.

Definition eq_c (c1 c2:constructor) :=
  list_eq eq_ca c1.(cstr_args) c2.(cstr_args) /\
  list_eq eq_term c1.(cstr_inst) c2.(cstr_inst).

Instance eq_c_equiv : Equivalence eq_c.
split; red; intros.
 destruct x; simpl; split; reflexivity.

 destruct H; split; symmetry; trivial.

 destruct H; destruct H0; split; eapply transitivity; eauto.
Qed.

Record inductive := mkInd {
  ind_idx : ctxt;
  ind_kind : nat;
  ind_cstrs : list constructor
}.

Definition eq_ind i1 i2 :=
  list_eq eq_term i1.(ind_idx) i2.(ind_idx) /\
  i1.(ind_kind) = i2.(ind_kind) /\
  list_eq eq_c i1.(ind_cstrs) i2.(ind_cstrs).

Instance eq_ind_equiv : Equivalence eq_ind.
split; red; intros.
 destruct x; simpl; repeat split; reflexivity.

 destruct H as (?&?&?); split; [|split]; symmetry; trivial.

 destruct H as (?&?&?); destruct H0 as (?&?&?); split; [|split];
   eapply transitivity; eauto.
Qed.


Parameter A_ B_ N_ O_ D_ : term.
Parameter S_ : term -> term.
Definition myvect :=
  mkInd (ctxt_of(A_::lift 1 N_::nil)) 42
     (mkCstr nil (Ref 1::lift 2 O_::nil) ::
      mkCstr (CA_Const (lift 2 N_) :: CA_Const(lift 3 A_) :: CA_Rec nil (Ref 3::Ref 1::nil)::nil)
       (Ref 3 :: S_ (Ref 1) :: nil) ::
      nil).


(** Type-checking conditions of an inductive declaration *)

Fixpoint check_constructor_data (e:env) (idx:ctxt) (knd:nat) n args inst :=
  match args with
  | CA_Const ty :: args' =>
      typ e ty (type knd) /\ check_constructor_data (ty::e) idx knd (S n) args' inst
  | CA_Rec par rinst :: args' =>
        List.fold_right (fun p chk_cont f => typ f p (type knd) /\ chk_cont (p::f))
          (fun f => typ_ctxt f rinst (lift_ctxt 0 (plus_rev (List.length par) n) idx)) par e /\
      check_constructor_data e idx knd n args' inst
  | nil => typ_ctxt e inst idx
  end.

Definition check_constructor (e:env) (idx:ctxt) (knd:nat) (c:constructor) :=
  check_constructor_data (push_ctxt e idx) idx knd (List.length idx) c.(cstr_args) c.(cstr_inst).

Record check_inductive (e:env) (ind:inductive) := mkChkInd {
  idx_nk : Forall (fun ty => ty <> kind) (ind_idx ind);
  cstrs_ok : Forall (check_constructor e ind.(ind_idx) ind.(ind_kind)) ind.(ind_cstrs)
  }.

(** The type of an inductive type *)
Definition inductive_type (i:inductive) : term :=
  mkprod i.(ind_idx) (type i.(ind_kind)).
(*
Instance comp_sh s : Proper (eq_val==>eq_val) s ->
  Proper (eq_val==>eq_val) (fun i => V.shift 1 (s i)).
do 2 red; intros.
apply V.shift_morph; auto.
Qed.
Instance id_s : Proper (eq_val ==> eq_val) (fun x => x).
do 2 red; auto.
Qed.
*)
Fixpoint cstr_arg_ctxt X args dpth s :=
  match args with
  | CA_Const ty :: args' => Sub ty s :: cstr_arg_ctxt X args' (S dpth) (sub_lift 1 s)
  | CA_Rec par rinst :: args' =>
      mkprod par (mkapp (lift (length par + dpth) X)
                    (List.map (fun t => Sub t s) rinst)) ::
      cstr_arg_ctxt X args' (S dpth) (sub_comp s (sub_shift 1))
  | nil => nil
  end.

Fixpoint cstr_arg_concl_sub args s :=
  match args with
  | CA_Const _ :: args' => cstr_arg_concl_sub args' (sub_lift 1 s)
  | CA_Rec _ _ :: args' => cstr_arg_concl_sub args' (sub_comp s (sub_shift 1))
  | nil => s
  end.
(*
Instance cstr_arg_concl_sub_morph args s :
  Proper (eq_val==>eq_val) (cstr_arg_concl_sub args s).
revert s sm; induction args; simpl; intros; auto.
destruct a; auto.
Qed.
*)
(*
Fixpoint cstr_arg_concl Y args inst dpth s {sm:Proper(eq_val==>eq_val)s} :=
  match args with
  | CA_Const ty :: args' => cstr_arg_concl Y args' inst (S dpth) (V.lams 1 s)
  | CA_Rec par rinst :: args' =>
      cstr_arg_concl Y args' inst (S dpth) (fun i => V.shift 1 (s i))
  | nil =>
      mkapp (lift dpth Y) (List.map (fun t => Sub t s) inst) 
  end.
*)
Definition cstr_arg_concl Y args inst dpth s :=
  mkapp (lift (List.length args + dpth) Y)
        (List.map (fun t => Sub t (cstr_arg_concl_sub args s)) inst) .
  
Definition cstr_argument_ctxt X ind n dpth :=
  match nth_error ind.(ind_cstrs) n with
  | Some c => cstr_arg_ctxt X c.(cstr_args) dpth sub_id
  | None => nil
  end.

Definition constructor_type idx X Y c : term :=
  let dpth := List.length idx in
  mkprod idx
 (mkprod (cstr_arg_ctxt X c.(cstr_args) dpth sub_id)
    (cstr_arg_concl Y c.(cstr_args) c.(cstr_inst) dpth sub_id)).

(*
Definition constr_arg_type I c k n :=
  match c with
  | CA_Const ty => Prod ty (k (S n))
  | CA_Rec idx inst => Prod (mkprod idx (mkapp (lift (length idx+n) I) inst)) (lift 1 (k n))
  end.

Definition constructor_type idx I J c : term :=
  let arity := List.length idx in
  let cstrty :=
     List.fold_right (constr_arg_type I)
      (fun n => mkapp (lift n J) c.(cstr_inst))
      c.(cstr_args)
      arity in
  mkprod idx cstrty.
*)
(* n is the number of preceding args;     -> to relocate ref to inductive
   n' is the number of preceding rec args -> to relocate constant terms
*)
(*Definition constr_ctxt I c k :=
  List.fold_right (fun c k e n =>
  match c with
  | CA_Const ty => k (lift n ty :: e) n
  | CA_Rec idx inst =>
      k (mkprod (List.map (lift n') idx)
                   (mkapp (lift (length idx+n) I) (List.map (lift n) inst))
         ::e) (S n)
  end)
    c.(cstr_args)
    (fun e n => e)
    0.

        (k (S n) (S n'))
  end.
*)
(*Definition constr_arg_type I c k n n' :=
  match c with
  | CA_Const ty => Prod (lift n' ty) (k (S n) n')
  | CA_Rec idx inst =>
      Prod (mkprod (List.map (lift n') idx)
                   (mkapp (lift (length idx+n) I) (List.map (lift n') inst)))
        (k (S n) (S n'))
  end.
Definition constructor_type idx I J c : term :=
  let arity := List.length idx in
  let cstrty :=
     List.fold_right (constr_arg_type I)
      (fun n n' => mkapp (lift n J) (List.map (lift n') c.(cstr_inst)))
      c.(cstr_args)
      arity
      0 in
  mkprod idx cstrty.

Definition predicate_type ind knd : term :=
  mkprod ind.(ind_idx) (Prod (mkapp (inductive_type ind) (vect_of_ctxt 0 ind.(ind_idx))) knd).
*)
(** Translate an inductive declaration into a positive operator *)

Definition int_constr_arg (c:constr_arg) (cont : val->dpositive) (i:val) : dpositive :=
  match c with
  | CA_Const ty =>
      dpos_norec (int ty i)
        (fun x => cont (V.cons x i))
  | CA_Rec idx inst =>
      dpos_consrec
        (List.fold_right
           (fun ty cont i =>
              dpos_param (int ty i) (fun x => cont (V.cons x i)))
           (fun i => dpos_rec (mkvecti inst i))
           idx
           i)
        (cont i)
  end.

Definition int_constructor a (c:constructor) (i:val) : dpositive :=
  List.fold_right int_constr_arg
     (fun j => dpos_inst (mkvecti c.(cstr_inst) j) a)
     c.(cstr_args)
     i.


Lemma pm_ok :
  Proper (list_eq eq_term ==> list_eq eq_term ==> eq_val ==> eqdpos)
     (fun idx inst j =>
      fold_right
        (fun ty cont i => dpos_param (int ty i) (fun x => cont (V.cons x i)))
        (fun i => dpos_rec (mkvecti inst i)) idx 
        j).
do 4 red.
induction 1; simpl; intros.
 apply dpos_rec_morph.
 apply mkvecti_morph; trivial.

 apply dpos_param_morph.
  apply int_morph; trivial. 
 red; intros.
 apply IHForall2; trivial.
 apply V.cons_morph; trivial.
Qed.

Lemma int_constructor_morph :
  Proper (eq_set ==> eq_c ==> eq_val ==> eqdpos) int_constructor.
do 4 red.
unfold int_constructor.
intros ? ? ? ? ? (?&?).
elim H0; simpl; intros.
 apply dpos_inst_morph; trivial.
 apply mkvecti_morph; trivial.

 destruct H2; simpl.
  apply dpos_norec_morph; auto.
   apply int_morph; trivial.
  red; intros.
  apply H4.
  apply V.cons_morph; trivial.

  apply dpos_consrec_morph.
   apply pm_ok; auto with *.

   apply H4; trivial.
Qed.

Lemma pm_ok' :
  Proper (eq_set ==> list_eq eq_term ==> eq ==> eq_val ==> eqdpos)
     (fun a inst args j =>
      fold_right int_constr_arg
        (fun i => dpos_inst (mkvecti inst i) a) args 
        j).
do 4 red.
(*apply int_constructor_morph.*)
induction x1; intros; subst y1; simpl.
 red; intros.
 apply dpos_inst_morph; trivial.
 apply mkvecti_morph; trivial.

 red; intros.
 destruct a; simpl. 
  apply dpos_norec_morph; auto.
   rewrite H1; reflexivity.
  red; intros.
  apply IHx1; trivial.
  apply V.cons_morph; trivial.

  apply dpos_consrec_morph.
   apply pm_ok; auto with *.
  apply IHx1; trivial.
Qed.

Definition int_constructors (lc:list constructor) (i:val) a : dpositive :=
  List.fold_right (fun c p => dpos_sum (int_constructor a c i) p)
     (dpos_cst empty)
     lc.

Lemma int_constructors_morph :
  Proper (list_eq eq_c ==> eq_val ==> eq_set ==> eqdpos) int_constructors.
do 4 red.
unfold int_constructors.
induction 1; intros; simpl.
 apply dpos_cst_morph; reflexivity.

 apply dpos_sum_morph; auto.
 apply int_constructor_morph; trivial.
Qed.

(** Soundness of int_constructors *)

Lemma shift_split' m n i :
  eq_val (V.shift (m+n) i) (V.shift n (V.shift m i)).
intros k.
unfold V.shift; simpl.
rewrite Plus.plus_assoc; reflexivity.
Qed.

Lemma shift_cons_vect n x i :
  eq_val (V.shift n (cons_vect n x i)) i.
revert x i.
induction n; simpl; intros.
 reflexivity.

 replace (S n) with (n+1) by auto with *; rewrite shift_split'.
 rewrite IHn.
 reflexivity.
Qed.

Lemma check_inductive_pos_cstr e idx knd c i a :
  check_constructor e idx knd c ->
  val_ok e i ->
  a ∈ mksigi idx i ->
  isPositive (mksigi idx i) (int_constructor a c (cons_vect (length idx) a i)).
intros.
unfold check_constructor in H.
cut (forall j g,
   eq_val (V.shift (List.length g + List.length idx) j) i ->
   check_constructor_data (push_rev_ctxt (push_ctxt e idx) g) idx
     knd (List.length g + List.length idx) c.(cstr_args) c.(cstr_inst) -> 
  (val_ok (push_rev_ctxt (push_ctxt e idx) g) j) ->
   isPositive (mksigi idx i) (int_constructor a c j)).
  intros h.
  apply h with nil.
   simpl.
   apply shift_cons_vect.

   simpl.
   exact H.

   simpl.
   apply cons_vect_typ; trivial.

 unfold int_constructor.
 elim c.(cstr_args); simpl; intros.
  apply isDPos_inst.

  destruct a0; simpl.
   destruct H4.
   apply isDPos_norec; intros.
    do 2 red; intros.
    apply pm_ok'; auto with *.
    rewrite H7; reflexivity.
   eapply H2 with (ty::g); trivial.
    simpl.
    apply vcons_add_var; auto.

   destruct H4.
   apply isDPos_consrec; auto.
   2:apply H2 with g; trivial.
   clear H6.
   revert j g H3 H4 H5; induction idx0; simpl; intros.
    apply isDPos_rec.
    red in H4.
    specialize H4 with (1:=H5).
    rewrite lift_ctxt_eq in H4.
    rewrite V.lams0 in H4.
    rewrite H3 in H4.
    trivial.

    destruct H4.
    apply isDPos_param.
     do 2 red; intros.
     apply pm_ok; auto with *.
     rewrite H7; reflexivity.
    intros.
    apply IHidx0 with (a0::g); simpl; auto.
    apply vcons_add_var; trivial.
Qed.

Lemma check_inductive_pos e ind i a :
  check_inductive e ind ->
  val_ok e i ->
  a ∈ mksigi ind.(ind_idx) i ->
  isPositive (mksigi (ind_idx ind) i)
     (int_constructors (ind_cstrs ind) (cons_vect (length (ind_idx ind)) a i) a).
intros.
destruct H as (_ & cstrs_ok).
revert cstrs_ok.
induction ind.(ind_cstrs); simpl; intros.
 apply isPos_cst.

 inversion_clear cstrs_ok0.
 apply isDPos_sum; auto.
 apply check_inductive_pos_cstr with (1:=H); trivial.
Qed.


Lemma check_inductive_univ e ind i a :
  check_inductive e ind ->
  val_ok e i ->
  a ∈ mksigi ind.(ind_idx) i ->
  pos_universe (mksigi ind.(ind_idx) i)
               (ZFecc.ecc (S ind.(ind_kind)))
     (int_constructors (ind_cstrs ind) (cons_vect (length (ind_idx ind)) a i) a).
intros.
generalize (cstrs_ok _ _ H).
induction 1; simpl; intros.
 apply isUPos_cst; auto.

 apply isUPos_sum; auto.
  apply check_inductive_pos_cstr with (1:=H2); trivial.

  elim H3; simpl; intros.
  apply isPos_cst; auto.
  apply isDPos_sum; auto.
  apply check_inductive_pos_cstr with (1:=H4); trivial.

(* destruct x as (args,inst).*)
(* unfold int_constructor; simpl.*)
 clear H IHForall l H3.
 red in H2; simpl in H2.
 cut (forall j g,
  (val_ok (push_rev_ctxt (push_ctxt e ind.(ind_idx)) g) j) ->
   eq_val (V.shift (List.length g + List.length ind.(ind_idx)) j) i ->
   check_constructor_data (push_rev_ctxt (push_ctxt e (ind_idx ind)) g) 
         (ind_idx ind) (ind_kind ind) (length g + length (ind_idx ind)) x.(cstr_args) x.(cstr_inst) ->
   pos_universe (mksigi ind.(ind_idx) i) (ZFecc.ecc (S ind.(ind_kind)))
     (int_constructor a x j)).
  intros h.
  apply h with nil; simpl.
   apply cons_vect_typ; trivial.

   apply shift_cons_vect.

   exact H2.

 clear H2.
 unfold int_constructor.
 destruct x as (args,inst); simpl.
 induction args; simpl; intros.
  apply isUPos_inst; auto.

  destruct a0; simpl.
   destruct H3.
   apply isUPos_norec; intros; auto.
    do 2 red; intros.
    apply pm_ok'; auto with *.
    rewrite H5; reflexivity.

    apply H3; trivial.

    apply IHargs with (ty::g); simpl; auto.
    apply vcons_add_var; auto.

   destruct H3.
   apply isUPos_consrec; auto.
   2:apply IHargs with g; trivial.
   clear H4.
   revert j g H H2 H3; induction idx; simpl; intros.
    apply isUPos_rec; auto.
    red in H3.
    specialize H3 with (1:=H).
    rewrite lift_ctxt_eq in H3.
    rewrite V.lams0 in H3.
    rewrite H2 in H3.
    trivial.

    destruct H3.
    apply isUPos_param; trivial.
     do 2 red; intros.
     apply pm_ok; auto with *.
     rewrite H5; reflexivity.

     apply H3; auto.

    intros.
    apply IHidx with (a0::g); simpl; auto.
    apply vcons_add_var; auto.
Qed.



Definition SInd (ind:inductive) : term.
(* begin show *)
left; exists (fun i =>
  let pos a := int_constructors ind.(ind_cstrs)
                 (cons_vect (List.length ind.(ind_idx)) a (V.shift 1 i)) a in
  dIND (int (mksig ind.(ind_idx)) (V.shift 1 i)) pos (i 0)).
(* end show *)
do 2 red; intros.
apply dIND_morph_gen.
 apply int_morph; auto with *.
 rewrite H; reflexivity.

 red; intros.
 apply int_constructors_morph; auto with *.
 rewrite H,H0; reflexivity.

 apply H.
Defined.

Definition Ind (ind:inductive) : term :=
  Absn ind.(ind_idx)
    (Sub
      (SInd ind)
      (sub_mkblock (List.length ind.(ind_idx)))).

Lemma typ_SInd e ind :
  check_inductive e ind ->
  typ (mksig (ind_idx ind) :: e) (SInd ind) (type (ind_kind ind)).
red; intros.
apply in_int_el.
red.
simpl.
assert (val_ok e (V.shift 1 i)).
 red; intros.
 assert (tmp := H0 (S n) _ H1).
 destruct T as [(T,Tm)|]; simpl in *; trivial.
assert (i 0 ∈ int (mksig ind.(ind_idx)) (V.shift 1 i)).
 assert (tmp := H0 0 _ eq_refl).
 destruct ind.(ind_idx); simpl in *; trivial.
 revert tmp; apply eq_elim.
 apply sigma_morph.
  rewrite V.lams0; reflexivity.
 red; intros.
 rewrite V.lams0, H2.
 reflexivity.

apply G_dIND; auto.
 apply isDP_intro.
  do 2 red; intros.
  apply int_constructors_morph; auto.
  reflexivity.
  rewrite H3; reflexivity.

  intros.
  apply check_inductive_pos with (e:=e); trivial.

 red; intros.
 apply check_inductive_univ with (e:=e); trivial.
Qed.

Lemma typ_Ind e ind :
  check_inductive e ind ->
  typ e (Ind ind) (inductive_type ind).
intros ind_ok.
unfold Ind, inductive_type.
apply typ_Absn.
 discriminate.
pose (k := Sub (type ind.(ind_kind)) (sub_mkblock (List.length ind.(ind_idx)))).
assert (type ind.(ind_kind) = k).
 reflexivity.
rewrite H.
apply typ_Sub with (mksig ind.(ind_idx) :: e).
 apply typ_SInd; trivial.

 apply val_ok_mkblock.
 apply ind_ok.
Qed.



Instance mktag_morph n : morph1 (mktag n).
do 2 red.
induction n; simpl; intros.
 rewrite H; reflexivity.

 apply inr_morph; auto.
Qed.

(** Constructor [n] of arity [ar] *)
Definition SCstr (n ar:nat) : term :=
  Sub (Op1 (mktag n) (Ref 0)) (sub_mkblock ar).

Instance val_ok_morph : Proper (list_eq eq_term ==> eq_val ==> iff) val_ok.
apply morph_impl_iff2; auto with *.
do 4 red.
induction 1; simpl; intros.
 red; intros.
 destruct n; discriminate.

 red; intros.
 destruct n; simpl in *.
  generalize (H2 0 _ eq_refl).
  injection H3; intros; subst T.
  revert H5; apply el_morph; symmetry; auto.
  apply lift_morph; trivial.

  red in IHForall2.
  apply (V.shift_morph 1 _ eq_refl) in H1.
  apply typ_sub_shift with (ctx := x::nil) in H2; simpl in H2.
  specialize IHForall2 with (1:=H1)(2:=H2)(3:=H3).
  destruct T as [(T,Tm)|]; simpl in *; auto.
Qed.

Lemma cstr_ctxt_same_length X args d s :
  length (cstr_arg_ctxt X args d s) = length args.
revert d s.
induction args; simpl; intros; auto.
destruct a; simpl; rewrite IHargs; reflexivity.
Qed.

Lemma shift_mkblock n i :
  eq_val (V.shift 1 (val_mkblock n i)) (V.shift n i).
revert i.
induction n; simpl; intros.
 reflexivity.

 rewrite V.shift_cons.
 rewrite V.shiftS_split.
 rewrite IHn.
 rewrite <- V.shift_split.
 rewrite Plus.plus_comm; reflexivity.
Qed.

Lemma eq_Ind_app e ind n v i :
  typ_ctxt e v (lift_ctxt 0 n ind.(ind_idx)) ->
  val_ok e i ->
  int (mkapp (lift n (Ind ind)) v) i ==
  int (SInd ind) (V.cons (mkvecti v i) (V.shift n i)).
unfold typ_ctxt.
intros.
specialize H with (1:=H0).
rewrite lift_ctxt_eq in H.
rewrite V.lams0 in H.
change (fun k => i k) with i in H.
Admitted.

Lemma mksig_nk ctx : mksig ctx <> kind.
induction ctx; simpl; discriminate.
Qed.
Lemma lift_rec_nk n t k :
  t <> kind <->
  lift_rec n k t <> kind.
destruct t as [(t,tm)|]; simpl; auto with *.
split; intros; discriminate.
Qed.
Lemma subst_rec_nk a t k :
  t <> kind <->
  subst_rec a k t <> kind.
destruct t as [(t,tm)|]; simpl; auto with *.
split; intros; discriminate.
Qed.


Lemma typ_SCstr e ind n c :
  check_inductive e ind ->
  nth_error ind.(ind_cstrs) n = Some c ->
  typ (push_ctxt (push_ctxt e ind.(ind_idx))
        (cstr_arg_ctxt (Ind ind) (cstr_args c)
          (length (ind_idx ind)) sub_id))
    (SCstr n (length c.(cstr_args)))
    (cstr_arg_concl (Ind ind) (cstr_args c) c.(cstr_inst)
          (length (ind_idx ind)) sub_id).
intros chk_ind get_cstr.
unfold SCstr.
red; intros.
simpl.
apply in_int_el.
red.
assert (cstr_ok : check_constructor e ind.(ind_idx) ind.(ind_kind) c).
 revert n get_cstr.
 elim (cstrs_ok _ _ chk_ind); simpl; intros.
  destruct n; discriminate.
 destruct n.
  injection get_cstr; intros; subst x; trivial.
  apply H2 with n; exact get_cstr.
red in cstr_ok.
assert (val_ok1 :
  val_ok (push_ctxt e ind.(ind_idx)) (V.shift (length c.(cstr_args)) i)).
 apply typ_sub_shift in H.
 rewrite cstr_ctxt_same_length in H.
 trivial.
pose (i0 := V.shift (length c.(cstr_args) + length ind.(ind_idx)) i).
assert (val_ok0 : val_ok e i0).
 apply typ_sub_shift in val_ok1.
 unfold i0.
 revert val_ok1; apply val_ok_morph; auto with *.
 rewrite shift_split'; reflexivity.
pose (Arg := mksigi ind.(ind_idx) i0).
pose (a := val_mkblock (length ind.(ind_idx)) (V.shift (length c.(cstr_args)) i) 0).
(* argument well-typed *)
assert (tya : a ∈ Arg).
 apply val_ok_mkblock in val_ok1.
 2:apply chk_ind.
 red in val_ok1.
 assert (tmp := val_ok1 0 _ eq_refl).
 apply in_int_not_kind in tmp.
 2:apply lift_rec_nk.
 2:apply mksig_nk.
 red in tmp.
 fold a in tmp.
 revert tmp; apply eq_elim.
 unfold lift; rewrite int_lift_rec_eq.
 rewrite V.lams0.
 subst Arg.
 apply int_morph; auto with *.
 simpl.
 rewrite shift_mkblock.
 rewrite <- shift_split'.
 reflexivity.
(* positivity *)
pose (pos a := int_constructors ind.(ind_cstrs)
                  (cons_vect (length ind.(ind_idx)) a i0) a).
assert (posp : isDPositive Arg pos).
 unfold pos.
 unfold Arg.
 apply isDP_intro.
  do 2 red; intros.
  apply int_constructors_morph; auto with *.
  rewrite H0; reflexivity.
 intros.
 apply check_inductive_pos with (1:=chk_ind); trivial.

assert (int (cstr_arg_concl (Ind ind) (cstr_args c) (cstr_inst c)
          (length (ind_idx ind)) sub_id) i ==
        dIND Arg pos a).
 unfold cstr_arg_concl.
 rewrite eq_Ind_app with (e:= push_ctxt (push_ctxt e (ind_idx ind))
           (cstr_arg_ctxt (Ind ind) (cstr_args c) (length (ind_idx ind)) sub_id)); trivial.
  simpl.
  apply dIND_morph_gen. 
   unfold Arg.
   apply int_morph; auto with *.
   rewrite V.shift_cons.
   reflexivity.

   red; intros.
   unfold pos.
   apply int_constructors_morph; auto with *.
   apply cons_vect_morph; auto.
   rewrite V.shift_cons.
   reflexivity.

   admit. (* family index constraints !!! *)

 red; intros.

 admit. (* constr instance ok *)

rewrite H0.
rewrite dIND_eq; trivial.
(* type arg block *)
assert (tyblk : val_mkblock (length c.(cstr_args)) i 0 ∈
        dp_oper (int_constructor a c (cons_vect (length ind.(ind_idx)) a i0)) (dIND Arg pos)).

(*
  val_ok (push_ctxt e (cstr_arg_ctxt X args dp s)) i ->
  val_mkblock cargs i 0 ∈
    dp_oper (int_constructor a (mkCstr cargs inst) (V.shift (length cargs) i)) X
*)
 admit.
(* type tag *)
revert tyblk.
change (fun k => i k) with i.
generalize (val_mkblock (length c.(cstr_args)) i 0).
unfold pos at 2.
revert get_cstr.
generalize n.
elim ind.(ind_cstrs); simpl; intros.
 destruct n0; discriminate get_cstr.
destruct n0; simpl.
 injection get_cstr; clear get_cstr; intro.
 subst a0.
 apply inl_typ; trivial.

 apply inr_typ; auto.
Qed.


Definition Cstr (ind:inductive) (n:nat) : term :=
  let cargs := cstr_argument_ctxt (Ind ind) ind n (List.length ind.(ind_idx)) in
  Absn ind.(ind_idx) (Absn cargs (SCstr n (List.length cargs))).

Lemma mkprod_nk ctx t : t<>kind -> mkprod ctx t <> kind.
intros.
induction ctx; simpl; trivial.
discriminate.
Qed.

Lemma mkapp_nk t args : t <> kind -> mkapp t args <> kind.
revert t.
induction args; simpl; intros; trivial.
apply IHargs.
discriminate.
Qed.

Lemma Absn_nk ctx t : t <> kind -> Absn ctx t <> kind.
intros.
induction ctx; simpl; trivial.
discriminate.
Qed.


Lemma typ_Cstr e ind n c :
  check_inductive e ind ->
  nth_error ind.(ind_cstrs) n = Some c ->
  typ e (Cstr ind n) (constructor_type ind.(ind_idx) (Ind ind) (Ind ind) c).
intros chk_ind get_cstr.
unfold Cstr.
unfold constructor_type.
unfold cstr_argument_ctxt.
rewrite get_cstr.
apply typ_Absn.
 apply mkprod_nk.
 apply mkapp_nk.
 apply lift_rec_nk.
 apply Absn_nk.
 discriminate.
apply typ_Absn.
 apply mkapp_nk.
 apply lift_rec_nk.
 apply Absn_nk.
 discriminate.
rewrite cstr_ctxt_same_length.
apply typ_SCstr; trivial.
Qed.

(*Definition branch_type arity I J i c ar : term :=
  let cstrty :=
     List.fold_right (constr_arg_type I)
      (fun n n' => App (mkapp (lift n J) (List.map (lift n') c.(cstr_inst)))
                     (Cstr i (List.app (List.map (lift n) ar) (vect_of_ctxt' 0 (List.length c.(cstr_args))))))
      c.(cstr_args)
      arity
      0 in
  substn ar cstrty.
*)
(*Definition branch_type idx I J c : term :=
  let arity := List.length idx in
  let cstrty :=
     List.fold_right (constr_arg_type I)
      (fun n => App (mkapp (lift n J) c.(cstr_inst)) (cobj))
      c.(cstr_args)
      arity in
  mkprod idx cstrty.

Definition branch_type ind
*)


Section Test.
  Variable N A O : term.
  Variable S : term -> term.
  Variable i :val.
  Definition vect :=
    mkInd (ctxt_of(A::N::nil)) 42
     (mkCstr nil (O::nil) ::
      mkCstr (CA_Const N :: CA_Const(lift 3 A) :: CA_Rec nil (Ref 1::nil)::nil) (S (Ref 1) :: nil) ::
      nil).

(*  Definition t := inductive_type vect.*)
(*  Definition t := inductive_obj vect i.*)
 Definition t := List.map (constructor_type (ctxt_of(A::N::nil)) (Ind vect) (Ind vect)) myvect.(ind_cstrs).
  Goal t=t.
unfold t at 2.
unfold constructor_type.
Opaque Sub Ind.
simpl.
unfold cstr_arg_concl; simpl.

unfold inductive_type; simpl.
unfold inductive_obj, lam_ctxt_obj.
simpl.
unfold int_constructor; simpl.
unfold mkvecti; simpl.

(* List.fold_right () idx (dpos_rec (fun p => int (mkvect inst)))*)

(******************************************************************************************)
(* Not yet updated...... *)


(** W *)

Section Wtypes_typing.

Variable o : set.
Hypothesis oo : isOrd o.

Variable e:env.

Variable A B:term.
Hypothesis Ank : A <> kind.
Hypothesis Bnk : B <> kind.

Let Aw i := int A i.
Let Bw i x := int B (V.cons x i).
Let Ww i := W (Aw i) (Bw i).

Definition WF' i := W_F (Aw i) (Bw i).

Instance Aw_morph : Proper (eq_val==>eq_set) Aw.
do 2 red; intros.
apply int_morph; auto with *.
Qed.

Instance Bw_morph : Proper (eq_val==>eq_set==>eq_set) Bw.
do 3 red; intros.
unfold Bw.
rewrite H; rewrite H0; reflexivity.
Qed.

Instance WF'_morph : Proper (eq_val ==> eq_set ==> eq_set) WF'.
do 3 red; intros.
unfold WF'.
apply W_F_ext; trivial.
 apply Aw_morph; trivial.

 red; intros.
 apply Bw_morph; trivial.
Qed.

Definition WI (O:term) : term.
(*begin show*)
left; exists (fun i => TI (WF' i) (int O i)).
(*end show*)
do 3 red; intros.
apply TI_morph_gen.
 apply WF'_morph; trivial.

 rewrite H; reflexivity.
Defined.

Lemma typ_WI : forall eps O,
  isOrd eps ->
  typ e O (Ordt eps) ->
  typ e (WI O) kind.
red; simpl; trivial.
Qed.

(** Constructor *)

Require Import ZFpairs.

Definition Wc (x:term) (f:term) : term.
(* begin show *)
left; exists (fun i => couple (int x i) (int f i)).
(* end show *)
do 2 red; intros; apply couple_morph; apply int_morph; auto with *.
Defined.

Lemma typ_Wc : forall O X F,
  typ e O (Ordt o) ->
  typ e X A ->
  typ e F (Prod (subst X B) (lift 1 (WI O))) ->
  typ e (Wc X F) (WI (OSucc O)).
red; intros.
red in H0; specialize H0 with (1:=H2).
apply in_int_not_kind in H0; trivial.
red in H1; specialize H1 with (1:=H2).
apply in_int_not_kind in H1.
2:discriminate.
destruct tyord_inv with (2:=H)(3:=H2) as (?,?); trivial.
apply in_int_el.
assert (couple (int X i) (int F i) ∈ TI (WF' i) (osucc (int O i))).
 apply TI_intro with (int O i); auto.
  apply WF'_morph; reflexivity.

  unfold WF'.
  apply couple_intro_sigma.
   do 2 red; intros.
   rewrite H6; reflexivity.

   apply H0.

   rewrite El_int_arr in H1.
   rewrite int_subst_eq in H1.
   trivial.
assumption.
Qed.


(* Case analysis *)

Definition W_CASE b w :=
  sigma_case (fun x f => cc_app (cc_app b x) f) w.

Definition Wcase (b n : term) : term.
(*begin show*)
left; exists (fun i => W_CASE (int b i) (int n i)).
(*end show*)
do 3 red; intros.
apply sigma_case_morph.
 do 2 red; intros.
 rewrite H; rewrite H0; rewrite H1; reflexivity.

 rewrite H; reflexivity.
Defined.

Instance Wcase_morph :
  Proper (eq_term ==> eq_term ==> eq_term) Wcase.
do 3 red; simpl; intros.
red; intros.
 unfold sigma_case.
 apply cond_set_morph.
  rewrite H0; rewrite H1; reflexivity.
  rewrite H; rewrite H0; rewrite H1; reflexivity.
Qed.

Existing Instance Wcase_morph.

Lemma Wcase_iota : forall X F G,
  eq_typ e (Wcase G (Wc X F)) (App (App G X) F).
red; intros.
simpl.
unfold W_CASE.
rewrite sigma_case_couple with (a:=int X i) (b:=int F i).
 reflexivity.

 do 3 red; intros.
 rewrite H0; rewrite H1; reflexivity.

 reflexivity.
Qed.


Lemma typ_Wcase : forall P O G n,
  typ e O (Ordt o) ->
  typ e G (Prod A (Prod (Prod B (lift 2 (WI O))) (App (lift 2 P) (Wc (Ref 1) (Ref 0))))) ->
  typ e n (WI (OSucc O)) ->
  typ e (Wcase G n) (App P n).
red; intros.
destruct tyord_inv with (2:=H)(3:=H2) as (?,?); trivial.
red in H0; specialize H0 with (1:=H2).
apply in_int_not_kind in H0;[|discriminate].
red in H1; specialize H1 with (1:=H2).
apply in_int_not_kind in H1;[|discriminate].
apply in_int_el.
simpl int in H0.
simpl in H1.
red; simpl.
rewrite TI_mono_succ in H1; auto with *.
2:apply W_F_mono; trivial.
2:apply Bw_morph; reflexivity.
assert (fst (int n i) ∈ Aw i).
 apply fst_typ_sigma in H1; trivial.
 assert (snd (int n i) ∈ cc_arr (Bw i (fst (int n i))) (TI (WF' i) (int O i))).
  apply snd_typ_sigma with (y:=fst(int n i)) in H1; auto with *.
  do 2 red; intros.
  rewrite H7; reflexivity.
 assert (int n i == couple (fst (int n i)) (snd (int n i))).
  apply (surj_pair _ _ _ (subset_elim1 _ _ _ H1)).
 unfold W_CASE, sigma_case.
 rewrite cond_set_ok; trivial.
 specialize cc_prod_elim with (1:=H0) (2:=H5); clear H0; intro H0.
 apply eq_elim with
    (cc_app (int (lift 2 P) (V.cons (snd (int n i)) (V.cons (fst (int n i)) i)))
       (couple (fst (int n i)) (snd (int n i)))).
  apply cc_app_morph; auto with *.
  do 2 rewrite simpl_int_lift.
  rewrite lift0_term; reflexivity.

  apply cc_prod_elim with (1:=H0).
  revert H6; apply eq_elim.
  apply cc_prod_ext.
   reflexivity.

   red; intros.
   rewrite V.lams0.
   reflexivity.
Qed.
(*Print Assumptions typ_Wcase.*)

Lemma typ_Wcase' : forall P O G n T,
  T <> kind ->
  typ e O (Ordt o) ->
  sub_typ e (App P n) T -> 
  typ e G (Prod A (Prod (Prod B (lift 2 (WI O))) (App (lift 2 P) (Wc (Ref 1) (Ref 0))))) ->
  typ e n (WI (OSucc O)) ->
  typ e (Wcase G n) T.
intros.
apply typ_subsumption with (App P n); auto.
2:discriminate.
apply typ_Wcase with O; trivial.
Qed.

End Wtypes_typing.

  Lemma var_mono_Wi : forall e o A B O,
    isOrd o ->
    A <> kind ->
    typ (tenv e) O (Ordt o) ->
    var_equals e A ->
    var_equals (push_var e A) B ->
    var_mono e O ->
    var_mono e (WI A B O).
unfold var_mono.
intros e o A B O oo Ank tyO eqA eqB subO i i' val_m x xty.
destruct tyord_inv with (2:=tyO) (3:=proj1 val_m); trivial.
destruct tyord_inv with (2:=tyO) (3:=proj1 (proj2 val_m)); trivial.
red in eqA; specialize eqA with (1:=val_m).
specialize subO with (1:=val_m).
assert (x ∈ TI (WF' A B i') (int O i)).
 revert xty; simpl; apply eq_elim.
 apply TI_morph_gen; auto with *.
  red; intros.
  apply W_F_ext; auto with *.
  red; intros.
  apply eqB.
  apply val_push_var; auto with *.
  rewrite H5 in H4.
  rewrite eqA in H4; trivial.

  reflexivity.

 revert H3; apply TI_mono; trivial.
 apply W_F_mono.
 apply Bw_morph; reflexivity.
Qed.

  Lemma var_mono_Wi' : forall e o A B O,
    isOrd o ->
    A <> kind ->
    typ_equals e A kind ->
    typ_equals (push_var e A) B kind ->
    typ_mono e O (Ordt o) ->
    var_mono e (WI A B O).
intros e o A B O oo Ank (eqA,_) (eqB,_) (subO,tyO).
apply var_mono_Wi with (o:=o); trivial.
Qed.

(*****************************************************************************)
(** Recursor (without case analysis) *)

(* WFix O M is a fixpoint of domain WI O with body M *)
Definition WFix (O M:term) : term.
(*begin show*)
left.
exists (fun i =>
         WREC (fun o' f => int M (V.cons f (V.cons o' i))) (int O i)).
(*end show*)
do 2 red; intros.
unfold WREC.
unfold ZFfixrec.REC.
apply TR_morph.
2:rewrite H; reflexivity.
do 2 red; intros.
apply sup_morph; trivial.
red; intros.
apply int_morph; auto with *.
apply V.cons_morph.
 apply H0; trivial.
apply V.cons_morph; trivial.
Defined.


(** Typing rules of WFix *)

Section WFixRules.

  Variable infty : set.
  Hypothesis infty_ord : isOrd infty.
  Variable E : fenv.
  Let e := tenv E.
  Variable A B O U M : term.
  Hypothesis A_nk : A <> kind.
  Hypothesis Aeq : var_equals E A.
  Hypothesis Beq : var_equals (push_var E A) B.

  Definition WIL n := WI (lift n A) (lift_rec n 1 B).

  Hypothesis ty_O : typ e O (Ordt infty).
  Hypothesis ty_M : typ (Prod (WIL 1 (Ref 0)) U::OSucc O::e)
    M (Prod (WIL 2 (OSucc (Ref 1)))
         (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U)))).

  Hypothesis stab : var_ext
    (push_fun (push_ord E (OSucc O)) (WIL 1 (Ref 0)) U)
    (WIL 2 (OSucc (Ref 1)))
    M.

  Lemma WF'mono i : Proper (incl_set==>incl_set) (WF' A B i).
do 2 red; intros.
unfold WF'.
apply W_F_mono; trivial.
do 2 red; intros; apply Bw_morph; auto with *.
Qed.
  Hint Resolve WF'mono.

  Let Wi i o := TI (WF' A B i) o.
  Let F i := fun o' f => int M (V.cons f (V.cons o' i)).
  Let U' i := fun o' x => int U (V.cons x (V.cons o' i)).

  Local Instance U'morph : forall i, morph2 (U' i).
do 3 red; intros; unfold U'.
rewrite H; rewrite H0; reflexivity.
Qed.
  Instance morph_fix_body : forall i, morph2 (F i).
unfold F; do 3 red; intros.
rewrite H; rewrite H0; reflexivity.
Qed.
  Lemma ext_fun_ty : forall o i,
    ext_fun (Wi i o) (U' i o).
do 2 red; intros.
rewrite H0;reflexivity.
Qed.
  Hint Resolve U'morph morph_fix_body ext_fun_ty.


  Hypothesis var_mono_U :
    var_mono (push_var (push_ord E (OSucc O)) (WIL 1 (OSucc (Ref 0)))) U.


Lemma El_int_W_lift O' n i :
  int (WIL n O') i == TI (WF' A B (V.shift n i)) (int O' i).
unfold WIL; simpl.
apply TI_morph_gen; auto with *.
2:reflexivity.
red; intros.
unfold WF'; apply W_F_ext; auto with *.
 unfold lift; rewrite int_lift_rec_eq; rewrite V.lams0; reflexivity.

 red; intros.
 rewrite int_lift_rec_eq.
 rewrite <- V.cons_lams.
 2:apply V.shift_morph; trivial.
 rewrite V.lams0.
 rewrite H1; reflexivity.
Qed.

  Lemma val_mono_1 i i' y y' f g:
    val_mono E i i' ->
    isOrd (int O i) ->
    isOrd (int O i') ->
    int O i ⊆ int O i' ->
    isOrd y ->
    isOrd y' ->
    y ⊆ int O i ->
    y' ⊆ int O i' ->
    y ⊆ y' ->
    f ∈ cc_prod (Wi i y) (U' i y) ->
    g ∈ cc_prod (Wi i' y') (U' i' y') ->
    fcompat (Wi i y) f g ->
    val_mono (push_fun (push_ord E (OSucc O)) (WIL 1 (Ref 0)) U)
      (V.cons f (V.cons y i)) (V.cons g (V.cons y' i')).
intros is_val Oo Oo' oo' yo y'o yO y'O yy' fty gty eqfg.
apply val_push_fun.
 apply val_push_ord; auto.
  apply ole_lts; trivial.

  apply ole_lts; trivial.

 revert fty; apply eq_elim; apply cc_prod_ext; intros.
  rewrite El_int_W_lift; reflexivity.

  apply ext_fun_ty.

 revert gty; apply eq_elim; apply cc_prod_ext; intros.
  rewrite El_int_W_lift; reflexivity.

  apply ext_fun_ty.

 rewrite El_int_W_lift.
 trivial.
Qed.

  Lemma val_mono_2 i y y' n n':
    val_ok e i ->
    isOrd (int O i) ->
    isOrd y ->
    isOrd y' ->
    y ⊆ y' ->
    y' ⊆ int O i ->
    n ∈ Wi i y ->
    n == n' ->
    val_mono (push_var (push_ord E (OSucc O)) (WIL 1 (OSucc (Ref 0))))
      (V.cons n (V.cons y i)) (V.cons n' (V.cons y' i)).
Proof.
intros.
apply val_push_var; auto with *.
 apply val_push_ord; auto with *.
  apply val_mono_refl; trivial.

  apply ole_lts; auto.
  transitivity y'; trivial.

  apply ole_lts; auto.

 red; rewrite El_int_W_lift.
 revert H5; apply TI_incl; simpl; auto.

 red; rewrite El_int_W_lift.
 rewrite <- H6.
 revert H5; apply TI_incl; simpl; auto.
 apply ole_lts; trivial.
Qed.


  Lemma fix_codom_mono : forall o o' x x' i,
   val_ok e i ->
   isOrd o' ->
   o' ⊆ int O i ->
   isOrd o ->
   o ⊆ o' ->
   x ∈ Wi i o ->
   x == x' ->
   U' i o x ⊆ U' i o' x'.
Proof.
intros.
red in var_mono_U.
assert (val_mono (push_var (push_ord E (OSucc O)) (WIL 1(OSucc(Ref 0))))
  (V.cons x (V.cons o i)) (V.cons x' (V.cons o' i))).
 apply val_mono_2; trivial.
 apply ty_O in H.
 apply in_int_not_kind in H;[|discriminate].
 apply isOrd_inv with infty; auto.
apply var_mono_U in H6; trivial.
Qed.

  Lemma ty_fix_body : forall i o f,
   val_ok e i ->
   o < osucc (int O i) ->
   f ∈ cc_prod (Wi i o) (U' i o) ->
   F i o f ∈ cc_prod (Wi i (osucc o)) (U' i (osucc o)).
unfold F; intros.
destruct tyord_inv with (2:=ty_O) (3:=H); trivial.
assert (val_ok (Prod (WIL 1 (Ref 0)) U::OSucc O::e) (V.cons f (V.cons o i))).
 apply vcons_add_var; auto.
  apply vcons_add_var; auto.

  red; revert H1; apply eq_elim.
  apply cc_prod_ext.
   rewrite El_int_W_lift.
   reflexivity.

   apply ext_fun_ty.
red in ty_M.
specialize ty_M with (1:=H4).
apply in_int_not_kind in ty_M.
2:discriminate.
revert ty_M; apply eq_elim.
symmetry; apply cc_prod_ext.
 rewrite El_int_W_lift.
 reflexivity.

 red; intros.
 rewrite int_lift_rec_eq.
 rewrite int_subst_rec_eq.
 rewrite int_lift_rec_eq.
 apply int_morph; auto with *.
 do 3 red.
 intros [|[|k]].
  compute; trivial.

  unfold V.lams, V.shift; simpl.
  reflexivity.

  unfold V.lams, V.shift; simpl.
  replace (k-0) with k; auto with *.
Qed.

  Lemma fix_body_irrel : forall i,
    val_ok e i ->
    Wi_ord_irrel (int A i)
      (fun x => int B (V.cons x i)) (int O i)
      (F i) (U' i).
red; intros.
assert (isOrd (int O i)).
 apply ty_O in H.
 apply isOrd_inv with infty; auto.
red in stab.
assert (Hstab := stab (V.cons f (V.cons o i)) (V.cons g (V.cons o' i))).
red in Hstab.
red; intros.
eapply Hstab; clear Hstab; trivial.
 apply val_mono_1; auto with *.
  apply val_mono_refl; exact H.

  transitivity o'; trivial.

 rewrite El_int_W_lift; auto.
Qed.

  Hint Resolve morph_fix_body ext_fun_ty ty_fix_body fix_codom_mono fix_body_irrel.


Let fix_typ o i:
  val_ok e i ->
  isOrd o ->
  isOrd (int O i) ->
  o ⊆ int O i ->
  WREC (F i) o ∈ cc_prod (Wi i o) (U' i o).
intros.
eapply WREC_wt with (U:=U' i); trivial.
 do 2 red; intros.
 apply Bw_morph; auto with *.

 intros.
 apply fix_codom_mono with (1:=H); trivial.
 transitivity o; auto.

 intros.
 apply ty_fix_body with (1:=H); trivial.
 apply ole_lts; trivial.
 transitivity o; trivial.

 red; intros; apply fix_body_irrel with (1:=H); trivial.
 transitivity o; trivial.
Qed.


  Lemma fix_irr i o o' x :
    val_ok e i ->
    isOrd o ->
    isOrd o' ->
    isOrd (int O i) ->
    o ⊆ o' ->
    o' ⊆ int O i ->
    x ∈ Wi i o ->
    cc_app (WREC (F i) o) x == cc_app (WREC (F i) o') x.
intros.
assert (WRECi := WREC_irrel).
red in WRECi.
apply WRECi with 
  (A:=int A i) (B:=fun x=>int B (V.cons x i))
  (ord:=int O i) (U:=U' i); auto with *.
 do 2 red; intros; apply Bw_morph; auto with *.

 intros.
 apply ty_fix_body with (1:=H); trivial.
 apply ole_lts; trivial.
Qed.

Lemma fix_eqn0 : forall i o,
  val_ok e i ->
  isOrd o ->
  isOrd (int O i) ->
  o ⊆ int O i ->
  WREC (F i) (osucc o) == F i o (WREC (F i) o).
intros.
unfold WREC at 1.
rewrite ZFfixrec.REC_eq; auto with *.
rewrite eq_set_ax; intros z.
rewrite sup_ax; auto with *.
split; intros.
 destruct H3 as (o',o'lt,zty).
 assert (o'o : isOrd o') by eauto using isOrd_inv.
 assert (o'le : o' ⊆ o) by (apply olts_le; auto).
 assert (o'le' : o' ⊆ int O i) by (transitivity o; trivial).
 assert (F i o' (WREC (F i) o') ∈ cc_prod (TI (WF' A B i) (osucc o')) (U' i (osucc o'))).
  apply ty_fix_body with (1:=H); trivial.
   apply ole_lts; auto.

   apply fix_typ with (1:=H); trivial.
 assert (F i o (WREC (F i) o) ∈ cc_prod (TI (WF' A B i) (osucc o)) (U' i (osucc o))).
  apply ty_fix_body with (1:=H); trivial.
   apply ole_lts; auto.

   apply fix_typ with (1:=H); trivial.
 rewrite cc_eta_eq with (1:=H3) in zty.
 rewrite cc_eta_eq with (1:=H4).
 rewrite cc_lam_def in zty|-*.
 2:intros ? ? _ eqn; rewrite eqn; reflexivity.
 2:intros ? ? _ eqn; rewrite eqn; reflexivity.
 destruct zty as (n', n'ty, (y, yty, eqz)).
 exists n'.
  revert n'ty; apply TI_mono; auto with *.
  apply osucc_mono; auto.
 exists y; trivial.
 revert yty; apply eq_elim.
 assert (firrel := fix_body_irrel).
 do 2 red in firrel.
 apply firrel with (1:=H); auto.
  apply fix_typ with (1:=H); auto.
  apply fix_typ with (1:=H); auto.

  clear firrel.
  red; intros.
  apply fix_irr with (1:=H); trivial.

 exists o;[apply lt_osucc;trivial|trivial].
Qed.

Lemma fix_eqn : forall i o n,
  val_ok e i ->
  isOrd o ->
  isOrd (int O i) ->
  o ⊆ int O i ->
  n ∈ TI (WF' A B i) (osucc o) ->
  cc_app (WREC (F i) (osucc o)) n ==
  cc_app (F i o (WREC (F i) o)) n.
intros.
rewrite fix_eqn0 with (1:=H); trivial.
unfold F.
reflexivity.
Qed.

Lemma typ_wfix :
  typ e (WFix O M) (Prod (WI A B O) (subst_rec O 1 U)).
red; intros.
destruct tyord_inv with (2:=ty_O)(3:=H); trivial.
apply in_int_el.
eapply eq_elim.
2:simpl.
2:apply fix_typ with (1:=H); auto with *.
2:reflexivity.
apply cc_prod_ext.
 reflexivity.

 red; intros.
 rewrite int_subst_rec_eq.
 rewrite <- V.cons_lams.
 2:apply V.cons_morph; reflexivity.
 rewrite V.lams0.
 rewrite H3; reflexivity.
Qed.

(** Fixpoint equation. *)
Lemma wfix_eq : forall N,
  typ e N (WI A B O) ->
  eq_typ e (App (WFix O M) N)
           (App (subst O (subst (lift 1 (WFix O M)) M)) N).
intros N tyN.
red; intros.
red.
change
 (cc_app (WREC (F i) (int O i)) (int N i) ==
  cc_app (int (subst O (subst (lift 1 (WFix O M)) M)) i) (int N i)).
do 2 rewrite int_subst_eq.
rewrite simpl_int_lift.
rewrite lift0_term.
red in tyN; specialize tyN with (1:=H).
apply in_int_not_kind in tyN.
2:discriminate.
destruct tyord_inv with (2:=ty_O)(3:=H); trivial.
simpl in tyN.
apply TI_elim in tyN; auto.
destruct tyN as (o,oly,nty).
assert (oo: isOrd o) by eauto using isOrd_inv.
rewrite <- TI_mono_succ in nty; auto with *.
rewrite <- fix_irr with (1:=H)(o:=osucc o); auto with *.
2:apply olts_le.
2:apply lt_osucc_compat; auto.
rewrite fix_eqn with (1:=H); auto with *.
eapply fix_body_irrel with (1:=H); auto with *.
 apply fix_typ with (1:=H); trivial.
 red; intros; apply isOrd_trans with o; trivial.

 simpl.
 apply fix_typ with (1:=H); auto with *.

 red; simpl; intros.
 apply fix_irr with (1:=H); auto with *.
 reflexivity.
Qed.


Lemma wfix_extend :
  var_mono E O ->
  var_ext E (WI A B O) (WFix O M).
intro subO.
do 2 red; intros.
assert (isval := proj1 H).
assert (isval' := proj1 (proj2 H)).
assert (oo: isOrd (int O i)).
 destruct tyord_inv with (2:=ty_O) (3:=isval); trivial.
assert (oo': isOrd (int O i')).
 destruct tyord_inv with (2:=ty_O) (3:=isval'); trivial.
assert (inclo: int O i ⊆ int O i').
 apply subO in H; trivial.
clear subO.
change (cc_app (WREC (F i) (int O i)) x == cc_app (WREC (F i') (int O i')) x).
revert x H0.
change (int (WI A B O) i) with (Wi i (int O i)).
elim oo using isOrd_ind; intros.
simpl in H3; apply TI_elim in H3; auto.
destruct H3 as (o',?,?).
assert (o_o' : isOrd o') by eauto using isOrd_inv.
assert (o'_y : osucc o' ⊆ y).
 red; intros; apply le_lt_trans with o'; auto.
rewrite <- TI_mono_succ in H4; auto.
rewrite <- fix_irr with (1:=isval) (o:=osucc o'); auto.
rewrite fix_eqn with (1:=isval); auto.
 assert (TIeq: forall o', isOrd o' -> TI (WF' A B i) o' == TI (WF' A B i') o').
  intros; apply TI_morph_gen; auto with *.
  red; intros.
  apply W_F_ext; trivial.
   apply (Aeq _ _ H).

   red; intros.
   eapply Beq.
   apply val_push_var with (1:=H); trivial.
    rewrite (Aeq _ _ H) in H7.
    rewrite H8 in H7; trivial.

assert (x ∈ TI (WF' A B i') (osucc o')).
 rewrite <- TIeq; auto.
rewrite <- fix_irr with (1:=isval') (o:=osucc o'); auto with *.
2:red; intros; apply le_lt_trans with o' ;auto.
2:apply inclo; apply H1; trivial.
rewrite fix_eqn with (1:=isval'); auto.
assert (irr := stab).
do 2 red in irr.
eapply irr.
2:rewrite El_int_W_lift; trivial.
apply val_mono_1 with (1:=H); auto with *.
do 2 red; intros.
rewrite H2; trivial.
symmetry; apply fix_irr with (1:=proj1(proj2 H)); auto with *.
revert H6; apply eq_elim.
apply TIeq; trivial.
Qed.


Lemma wfix_equals :
  var_equals E O ->
  var_equals E (WFix O M).
red; intros.
assert (fxs: var_mono E O).
 apply var_eq_sub; trivial.
apply wfix_extend in fxs.
red in fxs.
specialize fxs with (1:=H0).
apply fcompat_typ_eq with (3:=fxs).
 eapply cc_prod_is_cc_fun.
 assert (h := typ_wfix _ (proj1 H0)).
 apply in_int_not_kind in h.
 2:discriminate.
 exact h.

 setoid_replace (int (WI A B O) i) with (int (WI A B O) i').
  eapply cc_prod_is_cc_fun.
  assert (h := typ_wfix _ (proj1 (proj2 H0))).
  apply in_int_not_kind in h.
  2:discriminate.
  exact h.
 do 2 red.
 assert (h:= H _ _ H0).
 apply TI_morph_gen; auto with *.
 red; intros.
 apply W_F_ext; trivial.
  apply (Aeq _ _ H0).

  red; intros.
  apply Beq.
  apply val_push_var with (1:=H0); trivial.
   rewrite H3 in H2.
   rewrite <- (Aeq _ _ H0); trivial.
Qed.

End WFixRules.

Print Assumptions typ_wfix.


Lemma typ_wfix' : forall infty e A B O U M T,
       T <> kind ->
       isOrd infty ->
       A <> kind ->
       typ e O (Ordt infty) ->
       typ (Prod (WIL A B 1 (Ref 0)) U :: OSucc O :: e) M
         (Prod (WIL A B 2 (OSucc (Ref 1)))
         (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U)))) ->
       var_ext (push_fun (push_ord (tinj e) (OSucc O)) (WIL A B 1 (Ref 0)) U)
         (WIL A B 2 (OSucc (Ref 1))) M ->
       var_mono (push_var (push_ord (tinj e) (OSucc O)) (WIL A B 1 (OSucc (Ref 0)))) U ->
       sub_typ e (Prod (WI A B O) (subst_rec O 1 U)) T ->
       typ e (WFix O M) T.
intros.
apply typ_subsumption with (Prod (WI A B O) (subst_rec O 1 U)); auto.
2:discriminate.
change e with (tenv (tinj e)).
apply typ_wfix with (infty:=infty); trivial.
Qed.

Lemma typ_wfix'' : forall infty e A B O U M T,
       isOrd infty ->
       T <> kind ->
       sub_typ (tenv e) (Prod (WI A B O) (subst_rec O 1 U)) T ->
       typ (tenv e) O (Ordt infty) ->
       typ_mono (push_var (push_ord e (OSucc O)) (WI (lift 1 A) (lift_rec 1 1 B) (OSucc (Ref 0)))) U kind ->
       typ_ext (push_fun (push_ord e (OSucc O)) (WI (lift 1 A) (lift_rec 1 1 B) (Ref 0)) U)
         M (WI (lift 2 A) (lift_rec 2 1 B) (OSucc (Ref 1)))
           (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
       typ (tenv e) (WFix O M) T.
intros.
destruct H3; destruct H4.
apply typ_subsumption with (2:=H1); trivial.
2:discriminate.
apply typ_wfix with infty; trivial.
Qed.

  Lemma typ_ext_fix : forall eps e A B O U M,
    isOrd eps ->
    A <> kind ->
    typ_equals e A kind ->
    typ_equals (push_var e A) B kind ->
    typ_mono e O (Ordt eps) ->
    typ_ext (push_fun (push_ord e (OSucc O)) (WI (lift 1 A) (lift_rec 1 1 B) (Ref 0)) U) M
      (WI (lift 2 A) (lift_rec 2 1 B) (OSucc (Ref 1)))
      (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    var_mono (push_var (push_ord e (OSucc O)) (WI (lift 1 A) (lift_rec 1 1 B) (OSucc (Ref 0)))) U ->
    typ_ext e (WFix O M) (WI A B O) (subst_rec O 1 U).
intros eps e A B O U M eps_ord Ank tyA tyB tyO tyM tyU.
destruct tyO as (inclO,tyO).
destruct tyM as (extM,tyM).
assert (tyF: typ (tenv e) (WFix O M) (Prod (WI A B O) (subst_rec O 1 U))).
 apply typ_wfix with eps; trivial.
split; trivial.
destruct tyB as (eqB,_).
destruct tyA as (eqA,tyA).
apply wfix_extend with eps U; trivial.
Qed.

  Lemma typ_equals_fix : forall eps e A B O U M,
    isOrd eps ->
    A <> kind ->
    typ_equals e A kind ->
    typ_equals (push_var e A) B kind ->
    typ_equals e O (Ordt eps) ->
    typ_ext (push_fun (push_ord e (OSucc O)) (WI (lift 1 A) (lift_rec 1 1 B) (Ref 0)) U) M
      (WI (lift 2 A) (lift_rec 2 1 B) (OSucc (Ref 1)))
      (lift_rec 1 1 (subst_rec (OSucc (Ref 0)) 1 (lift_rec 1 2 U))) ->
    var_mono (push_var (push_ord e (OSucc O)) (WI (lift 1 A) (lift_rec 1 1 B) (OSucc (Ref 0)))) U ->
    typ_equals e (WFix O M) (Prod (WI A B O) (subst_rec O 1 U)).
intros eps e A B O U M eps_ord Ank (eqA,tyA) (eqB,_) (inclO,tyO) (extM,tyM) tyU.
assert (tyF: typ (tenv e) (WFix O M) (Prod (WI A B O) (subst_rec O 1 U))).
 apply typ_wfix with eps; trivial.
split; trivial.
apply wfix_equals with eps A B U; trivial.
Qed.

(** * W-types and universes. *)

Lemma typ_WI_type n eps e A B O :
  isOrd eps ->
  A <> kind ->
  typ e O (Ordt eps) ->
  typ e A (type n) ->
  typ (A::e) B (type n) ->
  typ e (WI A B O) (type n).
red; intros epso Ank tyO tyA tyB i is_val.
red.
destruct tyord_inv with (2:=tyO)(3:=is_val) as (oo,_); trivial.
clear tyO.
red in tyA; specialize tyA with (1:=is_val).
apply in_int_not_kind in tyA.
2:discriminate.
assert (G_B : forall a, a ∈ int A i -> int B (V.cons a i) ∈ ZFecc.ecc (S n)).
 intros.
 assert (val_ok (A::e) (V.cons a i)).
  apply vcons_add_var; trivial.
 apply tyB in H0.
 apply in_int_not_kind in H0.
 2:discriminate.
 trivial.
apply G_incl with (TI (WF' A B i) (W_ord (int A i) (fun x => int B (V.cons x i)))); trivial.
 apply (ZFecc.ecc_grot (S n)).

 apply G_TI; trivial.
  apply (ZFecc.ecc_grot (S n)).

  apply WF'_morph; auto with *.

  unfold W_ord.
  apply Ffix_o_o; auto with *.
   apply Wf_mono.
   apply Bw_morph; reflexivity.

   red; intros.
   revert H0; apply Wf_typ; trivial.
   apply Bw_morph; reflexivity.

  apply G_W_ord; auto.
   apply Bw_morph; reflexivity.

   apply (ZFecc.ecc_grot (S n)).

   change (omega ∈ ZFecc.ecc (S n)); auto.

  intros.
  apply G_W_F; auto.
   apply Bw_morph; reflexivity.

   apply (ZFecc.ecc_grot (S n)).

 apply W_post; trivial.
 apply Bw_morph; reflexivity.
Qed.
