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

(* misc *)

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

Definition Couple := Op2 couple.

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

Lemma shift_cons_vect n x i :
  eq_val (V.shift n (cons_vect n x i)) i.
revert x i.
induction n; simpl; intros.
 reflexivity.

 replace (S n) with (n+1) by auto with *; rewrite V.shift_split.
 rewrite IHn.
 reflexivity.
Qed.

Lemma eq_lams_cons_vect n (s:sub) v i :
  eq_val (V.lams n s (cons_vect n v i)) (cons_vect n v (s i)).
revert s v i; induction n; simpl; intros.
 rewrite V.lams0; reflexivity.

 replace (S n) with (n+1); auto with *.
 rewrite V.lams_split.
 rewrite IHn with (s:=sub_lift 1 s).
 simpl.
 rewrite <- V.cons_lams.
 rewrite V.lams0.
 reflexivity.

 apply sub_m.
 apply sub_m.
Qed.

Lemma cons_vect_dom n v i j k :
  (forall a, a <> k -> i a == j a) ->
  forall a, a <> n+k -> cons_vect n v i a == cons_vect n v j a.
revert v i j k; elim n; simpl; intros; auto.
apply H with (S k); auto.
 intros [|a'] ?;[reflexivity|apply H0; auto with arith].

 rewrite <- plus_n_Sm; trivial.
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

Instance push_rev_ctxt_morph :
  Proper (list_eq eq_term ==> list_eq eq_term ==> list_eq eq_term) push_rev_ctxt.
do 3 red; intros.
revert x y H; induction H0; simpl; intros; trivial.
constructor; auto.
Qed.

Lemma push_ctxt_item e g n :
  nth_error (push_ctxt e g) (n + length g) = nth_error e n.
revert e n; induction g; simpl; intros.
 rewrite <- plus_n_O; trivial.

 rewrite <- plus_n_Sm.
 exact (IHg (a::e) (S n)).
Qed.

Lemma typ_sub_shift e ctx :
  typ_sub (push_ctxt e ctx) (sub_shift (List.length ctx)) e.
revert e.
induction ctx; simpl; intros.
 red; intros; auto.

 red; intros.
 apply IHctx in H.
 apply val_ok_shift1 in H.
 revert H; apply val_ok_morph; auto with *.
 simpl.
 rewrite <- V.shift_split.
 apply V.shift_morph; auto with *.
Qed.

Lemma typ_sub_shift' e ctx :
  typ_sub (push_rev_ctxt e ctx) (sub_shift (List.length ctx)) e.
revert e.
induction ctx; simpl; intros.
 red; intros; auto.

 red; intros.
 apply typ_sub_shift with (ctx:=a::nil) in H; simpl in H.
 apply IHctx in H.
 simpl in *.
 rewrite V.shiftS_split; trivial.
Qed.

Fixpoint sub_ctxt s rctx :=
  match rctx with
  | nil => nil
  | ty::l => Sub ty s :: sub_ctxt (sub_lift 1 s) l
  end.

Instance sub_ctxt_morph :
  Proper (eq_sub ==> list_eq eq_term ==> list_eq eq_term) sub_ctxt.
do 3 red; intros.
revert x y H.
induction H0; simpl; intros; auto with *.
constructor.
 apply Sub_morph; trivial.
 apply IHForall2.
 apply sub_lift_morph; trivial.
Qed.

Lemma sub_ctxt_length s ctx : length (sub_ctxt s ctx) = length ctx.
revert s; induction ctx; simpl; auto with arith.
Qed.

Fixpoint sub_rev_ctxt s rctx :=
  match rctx with
  | nil => nil
  | ty::l => Sub ty (sub_lift (length l) s) :: sub_rev_ctxt s l
  end.

Lemma typs_lams_rev e s f l :
  typ_sub e s f ->
  typ_sub (push_rev_ctxt e (sub_rev_ctxt s l)) (sub_lift (length l) s)
          (push_rev_ctxt f l).
revert e s f; induction l; simpl; intros.
 red; simpl; intros.
 rewrite V.lams0; auto.

 simpl.
 rewrite sub_lift_split with (m:=1).
 apply typ_sub_lams1.
 auto.
Qed.


Definition ctxt_of (l:list term) : ctxt := l.  (* newest bindings at bottom of list *)
(*Definition ctxt_of (l:list term) : ctxt := List.rev l*)  (* newest bindings at top of list *)

Fixpoint subst_ctxt k v e :=
  match e with
  | nil => nil
  | ty::e' => subst_rec v k ty :: subst_ctxt (S k) v e'
  end.

Lemma subst_ctxt_length k a ctx : length (subst_ctxt k a ctx) = length ctx.
revert k; induction ctx; simpl; auto with arith.
Qed.

Fixpoint lift_ctxt k v e :=
  match e with
  | nil => nil
  | ty::e' => lift_rec v k ty :: lift_ctxt (S k) v e'
  end.

Lemma lift_ctxt_length k a ctx : length (lift_ctxt k a ctx) = length ctx.
revert k; induction ctx; simpl; auto with arith.
Qed.

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

Lemma vect_of_ctxt'_length k n :
  length (vect_of_ctxt' k n) = n.
induction n; simpl; auto.
Qed.

(*Parameter mksig : ctxt -> term.*)
Fixpoint mksig (e:ctxt) : term :=
  match e with
   nil => cst(singl empty)
  | ty :: e' => Sigma ty (mksig e')
  end.
Notation mksigi e i := (int (mksig e) i).

Instance mksig_morph : Proper (list_eq eq_term ==> eq_term) mksig.
do 2 red; intros.
induction H; simpl.
 red; reflexivity.
red; intros.
apply sigma_ext.
 apply int_morph; trivial.
intros.
apply int_morph; trivial.
apply V.cons_morph; trivial.
Qed.

(*Eval simpl in fun A B C i (*f*) => mksigi (A::B::C::nil) (*f*) i.*)

Lemma sub_ctxt_eq s e i :
  mksigi (sub_ctxt s e) i == mksigi e (s i).
revert s i; induction e; simpl; intros; auto with *.
apply sigma_morph.
 rewrite int_Sub_eq.
 reflexivity.

 red; intros.
 rewrite IHe.
 apply int_morph.
  reflexivity.
 simpl.
 rewrite <- V.cons_lams.
 rewrite V.lams0.
 rewrite H.
 reflexivity.

 apply sub_m.
Qed.

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

Instance mkprod_morph : Proper (list_eq eq_term ==> eq_term ==> eq_term) mkprod.
do 3 red; intros.
induction H;  simpl (mkprod _ _); trivial.
apply Prod_morph; trivial.
Qed.

Lemma eq_sub_mkprod ctx t s :
  eq_term (Sub (mkprod ctx t) s) (mkprod (sub_ctxt s ctx) (Sub t (sub_lift (length ctx) s))).
revert s t; induction ctx; simpl.
 intros.
 apply Sub_morph; auto with *.
 red; simpl.
 red; intros.
 rewrite V.lams0; apply sub_m; trivial.

 red; intros.
 apply cc_prod_morph.
  rewrite int_Sub_eq.
  apply int_morph; auto with *.
  apply sub_m; trivial.

  red; intros.
  transitivity (int (mkprod ctx t) ((sub_lift 1 s) (V.cons x0 x))).
   simpl.
   rewrite <- V.cons_lams.
   rewrite V.lams0.
   reflexivity.
   apply sub_m.
  rewrite <- int_Sub_eq.
  rewrite IHctx.
  apply int_morph.
  2:apply V.cons_morph; trivial.
  apply mkprod_morph.
   reflexivity.
  apply Sub_morph.
   reflexivity.
  rewrite <- sub_lift_split.
  replace (S (length ctx)) with (length ctx + 1); auto with *.
Qed.


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

Lemma typ_ctxt_length_inv i j v ctx :
  mkvecti v i ∈ mksigi ctx j -> length v = length ctx.
revert i j ctx; induction v; destruct ctx; simpl; intros; trivial.
 apply subset_elim1 in H.
 specialize surj_pair with (1:=H); intro.
 symmetry in H0.
 apply couple_mt_discr in H0; contradiction.

 apply singl_elim in H.
 unfold mkvecti in H.
 simpl in H.
 apply couple_mt_discr in H; contradiction.

 apply snd_typ_sigma with (3:=reflexivity _) in H.
  unfold mkvecti in H; simpl in H.
  rewrite snd_def in H.
  apply IHv in H; auto.

  do 2 red; intros.
  apply int_morph; auto with *.
  rewrite H1; reflexivity.
Qed.

Lemma vect_of_ctxt'_reloc n dp dp' i :
  mkvecti (vect_of_ctxt' dp n) (V.shift dp' i) ==
  mkvecti (vect_of_ctxt' dp' n) (V.shift dp i).
induction n; simpl; intros.
 reflexivity.
unfold mkvecti; simpl.
apply couple_morph.
 unfold V.shift.
 replace (dp'+(dp+n)) with (dp+(dp'+n)) by omega.
 reflexivity.

 apply IHn.
Qed.

Lemma vect_of_ctxt'_typ e ctx i :
  val_ok (push_ctxt e ctx) i ->
  Forall (fun t => t <> kind) ctx ->
  mkvecti (vect_of_ctxt' 0 (length ctx)) i ∈ mksigi ctx (V.shift (length ctx) i).
revert e i; induction ctx; simpl; intros.
 apply singl_intro.
unfold mkvecti; simpl.
inversion_clear H0.
apply couple_intro_sigma.
 do 2 red; intros.
 rewrite H3; reflexivity.

 generalize (H _ _ (push_ctxt_item (a::e) ctx 0)); intro itm.
 simpl in itm.
 apply in_int_not_kind in itm.
 2:apply lift_rec_nk; trivial.
 unfold lift in itm.
 rewrite int_lift_rec_eq in itm.
 rewrite V.lams0 in itm.
 trivial.

 generalize (IHctx (a::e) i H H2).
 apply eq_elim.
 apply int_morph; auto with *.
 intro k; unfold V.cons,V.shift; simpl.
 destruct k; simpl.
  rewrite <- plus_n_O; reflexivity.
  rewrite plus_n_Sm; reflexivity.
Qed.

Lemma cons_vect_of_ctxt' n i :
  eq_val (cons_vect n (mkvecti (vect_of_ctxt' 0 n) i) (V.shift n i)) i.
revert i; induction n; simpl; intros.
 reflexivity.
 unfold mkvecti; simpl.
 rewrite fst_def.
 rewrite snd_def.
 replace (S n) with (n+1) by omega.
 rewrite V.shift_split.
 replace (i n) with (V.shift n i 0).
 2:unfold V.shift; rewrite <- plus_n_O; trivial.
 rewrite <- V.surj_pair.
 apply IHn.
Qed.

Fixpoint mkv v :=
  match v with
  | nil => cst empty
  | x::v' => Couple x (mkv v')
  end.

Lemma mkvecti_def v i : mkvecti v i == int (mkv v) i.
unfold mkvecti.
induction v; simpl; intros.
 reflexivity.

 apply couple_morph; auto with *.
 reflexivity.
Qed.

Definition typ_ctxt (e:env) (v:list term) (ctx:ctxt) :=
  forall i, val_ok e i -> mkvecti v i ∈ mksigi ctx i.

Lemma typc_nil e : typ_ctxt e nil nil.
red; simpl; intros.
apply singl_intro.
Qed.

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

Lemma mkblock_after n i k : val_mkblock n i (S k) = i (k+n).
revert k; induction n; simpl; intros.
 rewrite <- plus_n_O; trivial.

 unfold V.shift; simpl.
 rewrite IHn.
 rewrite <- plus_n_Sm; trivial.
Qed.

Lemma cons_mkblock n i :
  eq_val i (cons_vect n (val_mkblock n i 0) (V.shift n i)).
revert i; induction n; simpl; intros.
 reflexivity.

rewrite snd_def.
rewrite fst_def.
apply transitivity with (1:=IHn i).
apply cons_vect_morph; trivial.
 reflexivity.
intros a; unfold V.shift,V.cons.
red.
destruct a.
2:rewrite <- plus_n_Sm; reflexivity.
rewrite <- plus_n_O.
rewrite mkblock_after.
reflexivity.
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

Lemma val_mkblock_lams n m f i :
  (n <= m)%nat ->
  val_mkblock n (V.lams m f i) 0 == val_mkblock n i 0.
revert m; induction n; simpl; intros.
 reflexivity.
apply couple_morph.
 rewrite mkblock_after.
 simpl.
 unfold V.lams.
 destruct (le_gt_dec m n).
  exfalso; omega.
 rewrite mkblock_after.
 simpl; reflexivity.

 apply IHn. 
 auto with arith.
Qed.
Lemma val_mkblock_lams2 m n f i :
  Proper (eq_val ==> eq_val) f ->
  (n <= m)%nat ->
  eq_val (val_mkblock n (V.lams m f i)) (V.lams (S (m-n)) f (val_mkblock n i)).
intros fm.
induction n; simpl; intros.
 rewrite <- Minus.minus_n_O.
 rewrite V.cons_lams; trivial.
 reflexivity.

 rewrite <- V.cons_lams; trivial.
 apply V.cons_morph.
  apply couple_morph.
   rewrite mkblock_after; simpl.
   rewrite mkblock_after; simpl.
   unfold V.lams.
   destruct (le_gt_dec m n).
    exfalso; omega.
    reflexivity.

   rewrite val_mkblock_lams; auto with *.

 rewrite IHn; auto with *.
 intros a; red.
 unfold V.shift, V.lams; simpl.
 destruct (le_gt_dec (m-n) (S a)); simpl.
  destruct (le_gt_dec (m-S n) a).
   replace (m-n) with (S(m-S n)) by omega.
   reflexivity.

   exfalso; omega.

  destruct (le_gt_dec (m-S n) a).
   exfalso; omega.
  reflexivity.
Qed.

Lemma lift_rec_mkblock n k k' t :
  (k' <= k) %nat ->
  eq_term (lift_rec n k (Sub t (sub_mkblock k')))
          (Sub (lift_rec n (S (k-k')) t) (sub_mkblock k')).
destruct t as [(t,tm)|]; [simpl|reflexivity].
red; intros.
red.
apply tm.
rewrite val_mkblock_lams2; trivial.
2:apply V.shift_morph; trivial.
rewrite H0; reflexivity.
Qed.
Definition sub_unblock (n:nat) : sub.
exists (fun i => cons_vect n (i 0) (V.shift 1 i)).
do 2 red; intros.
apply cons_vect_morph; trivial.
 apply H.
rewrite H; reflexivity.
Defined.
Lemma sub_unblock_block n i :
  eq_val (sub_unblock n (sub_mkblock n i)) i.
induction n; simpl; intros.
 rewrite V.shift_cons; reflexivity.

 rewrite V.shift_cons.
 rewrite fst_def.
 rewrite snd_def.
 apply transitivity with (2:=IHn).
 simpl.
 apply cons_vect_morph; auto with *.
 rewrite mkblock_after; simpl.
 rewrite shift_mkblock.
 rewrite V.shiftS_split.
 rewrite shift_mkblock.

 intros [|a]; unfold V.shift; simpl; auto with *.
 replace (n+0) with n; auto with *.  
Qed.
Lemma sub_comp_block_unblock n :
  eq_sub (sub_comp (sub_unblock n) (sub_mkblock n)) sub_id.
red; simpl; red; intros.
rewrite <- H.
apply sub_unblock_block.
Qed.

Lemma vect_of_ctxt'_eq_mkblock n i :
  mkvecti (vect_of_ctxt' 0 n) i == val_mkblock n i 0.
revert i; induction n; simpl; intros.
 reflexivity.
unfold mkvecti; simpl.
apply couple_morph.
 rewrite mkblock_after; reflexivity.
apply IHn.
Qed.



Fixpoint Absn (c:ctxt) (t:term) : term :=
  match c with
  | nil => t
  | ty :: c' => Abs ty (Absn c' t)
  end.

Instance Absn_morph : Proper (list_eq eq_term ==> eq_term ==> eq_term) Absn.
do 3 red; intros.
induction H; simpl; auto.
red; intros.
apply cc_lam_morph.
 apply int_morph; trivial.
red; intros.
apply int_morph; trivial.
apply V.cons_morph; trivial.
Qed.
Lemma eq_subst_absn a k ctx t :
  eq_term (subst_rec a k (Absn ctx t))
          (Absn (subst_ctxt k a ctx) (Sub t (sub_lift (length ctx + k) (sub_cons a sub_id)))).
revert k; induction ctx; simpl; intros.   
 apply subst_rec_equiv.

 red; intros.
 red.
 apply cc_lam_ext.
  rewrite int_subst_rec_eq.
  rewrite H.
  reflexivity.
 red; intros.
 rewrite V.cons_lams.
 rewrite plus_n_Sm.
 rewrite <- IHctx.
 rewrite int_subst_rec_eq.
 apply int_morph; auto with *.
 apply V.lams_morph; trivial.
  red; intros.
  rewrite H2.
  rewrite H.
  reflexivity.

  rewrite H,H1; reflexivity.

 do 2 red; intros.
 rewrite H2; reflexivity.
Qed.

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


Lemma lift_rec_absn n k ctx t :
  eq_term (lift_rec n k (Absn ctx t)) (Absn (lift_ctxt k n ctx) (lift_rec n (length ctx + k) t)).
revert k; induction ctx; simpl; intros; auto with *.
red; intros.
red.
apply cc_lam_morph.
 symmetry; rewrite H; apply int_lift_rec_eq.
red; intros.
rewrite plus_n_Sm.
rewrite <- IHctx.
rewrite int_lift_rec_eq.
apply int_morph; auto with *.
rewrite V.cons_lams.
 apply V.lams_morph; auto with *.
  apply V.shift_morph; trivial.
 apply V.cons_morph; trivial.

 apply V.shift_morph; trivial.
Qed.


(*Parameter mkapp : term -> list term -> term.*)
Fixpoint mkapp t args :=
  match args with
  | nil => t
  | a::args' => mkapp (App t a) args'
  end.

Instance mkapp_morph : Proper (eq_term ==> list_eq eq_term ==> eq_term) mkapp.
do 3 red; intros.
revert x y H; induction H0; simpl; intros; auto.
apply IHForall2.
rewrite H,H1; reflexivity.
Qed.

Lemma eq_sub_mkapp t l s :
  eq_term (Sub (mkapp t l) s) (mkapp (Sub t s) (List.map (fun t => Sub t s) l)).
revert t; induction l; simpl; intros; auto with *.
rewrite IHl.
apply mkapp_morph.
apply eq_Sub_app.
reflexivity.
Qed.

Lemma eq_int_mkapp t t' v v' i i' :
  eq_val i i' ->
  int t i == int t' i' ->
  list_eq (fun a a' => int a i == int a' i') v v' ->
  int (mkapp t v) i == int (mkapp t' v') i'.
intros.
revert t t' H0; induction H1; simpl; intros; trivial.
apply IHForall2.
simpl.
apply cc_app_morph; trivial.
Qed.


Fixpoint sub_consn l s :=
  match l with
  | nil => s
  | a::l' => sub_consn l' (sub_cons a s)
  end.

Lemma sub_consn_vecti v s i :
  eq_val (sub_consn v s i) (cons_vect (length v) (mkvecti v i) (s i)).
revert s i; induction v; simpl; intros; auto with *.
rewrite IHv.
apply cons_vect_morph; trivial.
 unfold mkvecti; simpl; rewrite snd_def; reflexivity.

 simpl.
 apply V.cons_morph; auto with *.
 unfold mkvecti; simpl; rewrite fst_def; reflexivity.
Qed.

Lemma sub_consn_lams n v1 (s1 s2:sub) i :
  n = length v1 ->
  eq_val
     (V.lams n s1 (sub_consn v1 s2 i))
     (sub_consn v1 (sub_comp s1 s2) i).
intros; subst n.
revert s1 s2 i; induction v1; simpl; intros.
 rewrite V.lams0; reflexivity.

 replace (S (length v1)) with (length v1 + 1) by auto with *.
 rewrite V.lams_split.
 rewrite IHv1 with (s1:=sub_lift 1 s1) (s2:=sub_cons a s2).
rewrite sub_consn_vecti.
rewrite sub_consn_vecti.
apply cons_vect_morph; auto with *.
simpl.
rewrite <- V.cons_lams.
rewrite V.lams0; reflexivity.
apply sub_m.
apply sub_m.
Qed.

Lemma val_mkblock_consn n v s i :
  n = length v ->
  eq_val (val_mkblock n (sub_consn v s i)) (V.cons (mkvecti v i) (s i)).
intros; subst n.
revert i s; induction v; simpl; intros.
 reflexivity.

 apply V.cons_morph.
  unfold mkvecti; simpl.
  apply couple_morph.
   generalize (IHv i (sub_cons a s) 1).
   simpl; trivial.

   apply IHv.

  simpl.
  rewrite IHv; simpl.
  rewrite V.shiftS_cons.
  rewrite V.shiftS_cons.
  reflexivity.
Qed.

Lemma eq_betan e ctx s t v :
  typ_ctxt e v (sub_ctxt s ctx) ->
  eq_typ e (mkapp (Sub (Absn ctx t) s) v) (Sub t (sub_consn v s)).
red; intros.
apply H in H0.
clear e H.
revert i s t ctx H0; induction v; destruct ctx; intros.
 reflexivity.

 simpl in H0.
 apply subset_elim1 in H0.
 specialize surj_pair with (1:=H0); intro.
 symmetry in H.
 apply couple_mt_discr in H; contradiction.

 unfold mkvecti in H0; simpl in H0.
 apply singl_elim in H0.
 apply couple_mt_discr in H0; contradiction.

 red.
 simpl (Absn _ _).
 rewrite eq_sub_Abs.
 simpl.
 rewrite <- IHv with (ctx := (*subst_ctxt 0 a*) ctx).
  apply eq_int_mkapp; auto with *.
   simpl.
   rewrite cc_beta_eq.
    rewrite int_Sub_eq.
    rewrite int_Sub_eq.
    apply int_morph; auto with *.
    simpl.
    rewrite <- V.cons_lams.
    rewrite V.lams0; reflexivity.
    apply sub_m.

    do 2 red; intros.
    rewrite H1; reflexivity.

    simpl in H0.
    apply fst_typ_sigma in H0.
    unfold mkvecti in H0; simpl in H0.
    rewrite fst_def in H0.
    trivial.

   assert (Reflexive (fun a a' => int a i == int a' i)).
    red; intros; apply int_morph; auto with *.
   reflexivity.

unfold mkvecti in H0; simpl in H0.
apply snd_typ_sigma with (3:=reflexivity _) in H0.
 rewrite snd_def in H0.
 revert H0; apply eq_elim.
 rewrite sub_ctxt_eq.
 simpl.
 rewrite sub_ctxt_eq.
 apply int_morph; auto with *.
 simpl.
 rewrite <- V.cons_lams.
 2:apply sub_m.
 rewrite V.lams0.
 apply V.cons_morph.
 2:reflexivity.
 red; rewrite fst_def.
 reflexivity.

 do 2 red; intros.
 rewrite H1; reflexivity.
Qed.

Lemma eq_betan0 e ctx t v :
  typ_ctxt e v ctx ->
  eq_typ e (mkapp (Absn ctx t) v) (Sub t (sub_consn v sub_id)).
intros.
rewrite <- eq_sub_id with (t:=Absn ctx t).
apply eq_betan.
red; intros.
rewrite sub_ctxt_eq.
apply H; trivial.
Qed.

(*Parameter mktag : nat -> set -> set.*)
Fixpoint mktag n b :=
  match n with
  | 0 => inl b
  | S n' => inr (mktag n' b)
  end.

Instance mktag_morph n : morph1 (mktag n).
do 2 red.
induction n; simpl; intros.
 rewrite H; reflexivity.

 apply inr_morph; auto.
Qed.


Definition Sum_case (C:term) (B1 B2:term) : term.
left; exists (fun i => sum_case (fun b1 => int B1 (V.cons b1 i)) (fun b2 => int B2 (V.cons b2 i))
                         (int C i)).
do 2 red; intros.
apply sum_case_morph.
 red; intros.
 rewrite H,H0; reflexivity.

 red; intros.
 rewrite H,H0; reflexivity.

 rewrite H; reflexivity.
Defined.

Definition Dest_sum := Op1 dest_sum.

Fixpoint Switch (C:term) (L:list term) :=
  match L with
  | nil => cst empty (* dead code *)
  | br1::brs =>  Sum_case C br1 (lift 1 (Switch (Dest_sum C) brs))
  end.
(*
Fixpoint Switch (C:term) (L:list term) :=
  match L with
  | nil => cst empty (* dead code *)
  | br1::brs =>  Sum_case C br1 (Switch (Ref 0) (map (lift 1) brs))
  end.
*)
 
(* If Γ |- t : A, then |- lam_ctxt(Γ,t) : Π Γ. A
     with app(lam_ctxt(Γ,t),v) == t(mkvect v) *)


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


(* Term properties : not kind and free vars *)

Lemma mksig_nk ctx : mksig ctx <> kind.
induction ctx; simpl; discriminate.
Qed.

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


Definition dum := cst (singl empty).

Lemma typ_dum_ e : typ e (cst (singl empty)) kind.
red; simpl; intros; trivial.
Qed.
Hint Resolve typ_dum_.

(*
Definition nfv ty k :=
  forall u, eq_term ty (lift_rec 1 k (subst_rec u k ty)).
*)
Definition nfv ty k :=
  forall u, eq_term ty (Sub ty (sub_lift k (sub_cons u (sub_shift 1)))).

Definition nfv_list v k :=
  Forall (fun t => nfv t k) v.

Definition nfv_ctxt :=
  List.fold_right (fun p kont k => nfv p k /\ kont (S k)) (fun _ => True).

Fixpoint nfv_rev_ctxt l :=
  match l with
  | nil => True
  | ty::l' => nfv ty (length l') /\ nfv_rev_ctxt l'
  end.

Instance eq_term_morph : Proper (eq_term==>eq_term==>iff) eq_term.
do 3 red; intros.
split; intros.
 rewrite <- H,<- H0; trivial.
 rewrite H,H0; trivial.
Qed.

Instance nfv_morph : Proper (eq_term ==> eq ==> iff) nfv.
do 3 red; intros.
subst y0.
unfold nfv.
apply fa_morph; intros u.
apply eq_term_morph; trivial.
apply Sub_morph; trivial.
reflexivity.
Qed.

Lemma nfv_int t k i u :
  nfv t k -> int t i == int t (V.lams k (fun j => V.cons (int u j) (V.shift 1 j)) i).
unfold nfv; intros.
rewrite H with (u:=u) at 1.
destruct t as [(t,tm)|]; simpl; auto with *.
reflexivity.
Qed.

Lemma nfv_intro t k :
  (forall i j, (forall a, a <> k -> i a == j a) -> int t i == int t j) ->
  nfv t k.
red; intros.
destruct t as [(t,tm)|]; simpl; trivial.
do 2 red; intros.
simpl in H.
apply H.
intros.
unfold V.lams, V.shift, V.cons.
destruct (le_gt_dec k a).
2:apply H0.
case_eq (a-k); intros.
exfalso; omega.
replace (k+(1+n)) with a by omega.
apply H0.
Qed.

Lemma nfv_elim t k i j :
  nfv t k ->
  (forall a, a <> k -> i a == j a) ->
  int t i == int t j.
intros.
transitivity (int t (V.lams k (fun i' => V.cons (j k) (V.shift 1 i')) i)).
 apply nfv_int with (u:=cst (j k)); trivial.

 apply int_morph; auto with *.
 intros a; red.
 unfold V.lams, V.cons, V.shift.
 destruct (le_gt_dec k a).
  case_eq (a-k); intros.
   replace k with a by omega; reflexivity.

   replace (k+(1+n)) with a by omega.
   apply H0; omega.

  apply H0; omega.
Qed.

Lemma nfv_app a b k :
  nfv a k ->
  nfv b k ->
  nfv (App a b) k.
unfold nfv; intros.
red; simpl.
red; intros.
red.
apply cc_app_morph.
 rewrite H1.
 apply nfv_int; trivial.

 rewrite H1.
 apply nfv_int; trivial.
Qed.

Lemma nfv_mkapp a l k :
  nfv a k ->
  nfv_list l k ->
  nfv (mkapp a l) k.
intros.
revert a H H0; induction l; simpl; intros; auto.
inversion_clear H0.
apply IHl; trivial.
apply nfv_app; trivial.
Qed.

Lemma nfv_prod a b k :
  nfv a k ->
  nfv b (S k) ->
  nfv (Prod a b) k.
red; intros.
simpl.
do 2 red; intros.
apply cc_prod_morph.
 rewrite H1; apply nfv_int; trivial.

 red; intros.
 rewrite H1,H2.
 rewrite V.cons_lams.
  apply nfv_int; trivial.

  do 2 red; intros.
  rewrite H3; reflexivity.
Qed.

Lemma nfv_sigma a b k :
  nfv a k ->
  nfv b (S k) ->
  nfv (Sigma a b) k.
intros.
apply nfv_intro; intros.
simpl.
apply sigma_morph.
 apply nfv_elim with (1:=H); trivial.

 red; intros.
 apply nfv_elim with (1:=H0).
 intros.
 destruct a0; simpl; trivial.
 apply H1; omega.
Qed.

Lemma nfv_Couple a b k :
  nfv a k -> nfv b k -> nfv (Couple a b) k.
intros.
apply nfv_intro; intros.
simpl.
apply couple_morph.
 apply nfv_elim with (1:=H); trivial.
 apply nfv_elim with (1:=H0); trivial.
Qed.

Lemma nfv_mksig ctx k :
  nfv_ctxt ctx k ->
  nfv (mksig ctx) k.
revert k; induction ctx; simpl; intros.
 red; intros.
 reflexivity.

 destruct H.
 apply nfv_sigma; auto.
Qed.

Lemma nfv_lift_rec1 n k t m :
  k <= m < n+k ->
  nfv (lift_rec n k t) m.
red.
destruct t as [(t,tm)|]; simpl; intros; trivial.
do 2 red; intros.
apply tm.
intros a.
red.
unfold V.lams, V.shift.
destruct (le_gt_dec k a).
 destruct (le_gt_dec m (k+(n+(a-k)))).
 simpl.
 unfold V.cons.
 case_eq (k+(n+(a-k))-m); intros.
  exfalso; omega.
 replace (k+(n+(a-k))) with (m+S n0).
  apply H0.
 omega.

 apply H0.

 destruct (le_gt_dec m a).
 2:apply H0.
 exfalso; omega.
Qed.


Lemma nfv_lift_rec2 n k t m :
  (n+k <= m)%nat ->
  nfv t (m-n) ->
  nfv (lift_rec n k t) m.
intros.
apply nfv_intro; intros.
rewrite int_lift_rec_eq.
rewrite int_lift_rec_eq.
apply nfv_elim with (1:=H0).
intros.
unfold V.lams,V.shift.
destruct (le_gt_dec k a); apply H1; omega.
Qed.


Lemma nfv_rev_ctxt_eq u l :
  nfv_rev_ctxt l ->
  list_eq eq_term (sub_rev_ctxt (sub_cons u (sub_shift 1)) l) l.
induction l; simpl; auto with *.
destruct 1.
constructor; auto.
symmetry.
apply H.
Qed.

Lemma nfv_liftS n t k :
  nfv (lift n t) k ->
  nfv (lift (S n) t) (S k).
intros.
destruct (le_gt_dec n k).
 rewrite eq_term_liftS.
 apply nfv_lift_rec2; auto with *.
 simpl; rewrite <- Minus.minus_n_O.
 trivial.

 apply nfv_lift_rec1.
 omega.
Qed.

Lemma nfv_ctxt_lift_rec1 n k ctx m :
  k <= m < n+k ->
  nfv_ctxt (lift_ctxt k n ctx) m.
revert k m; induction ctx; simpl; intros; trivial.
split.
 apply nfv_lift_rec1; trivial.
 apply IHctx; omega.
Qed.


(** Syntax of inductive definitions *)

Inductive constr_arg :=
| CA_Const (ty:term)
| CA_Rec (idx:ctxt) (par inst:list term).

Inductive eq_ca : relation constr_arg :=
| Eqca_const ty1 ty2 : eq_term ty1 ty2 -> eq_ca (CA_Const ty1) (CA_Const ty2)
| Eqca_rec idx1 idx2 par1 par2 inst1 inst2 :
    list_eq eq_term idx1 idx2 ->
    list_eq eq_term par1 par2 ->
    list_eq eq_term inst1 inst2 ->
    eq_ca (CA_Rec idx1 par1 inst1) (CA_Rec idx2 par2 inst2).

Instance eq_ca_equiv : Equivalence eq_ca.
split; red; intros.
 destruct x; constructor; auto with *.

 destruct H; constructor; auto with *.

 destruct H; inversion_clear H0; constructor.
  transitivity ty2; trivial.
  transitivity idx2; trivial.
  transitivity par2; trivial.
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
  ind_par : ctxt;
  ind_idx : ctxt;
  ind_kind : nat;
  ind_cstrs : list constructor
}.

Definition eq_ind i1 i2 :=
  list_eq eq_term i1.(ind_par) i2.(ind_par) /\
  list_eq eq_term i1.(ind_idx) i2.(ind_idx) /\
  i1.(ind_kind) = i2.(ind_kind) /\
  list_eq eq_c i1.(ind_cstrs) i2.(ind_cstrs).

Instance eq_ind_equiv : Equivalence eq_ind.
split; red; intros.
 destruct x; simpl; repeat split; reflexivity.

 destruct H as (?&?&?&?); split; [|split;[|split]]; symmetry; trivial.

 destruct H as (?&?&?&?); destruct H0 as (?&?&?&?); split; [|split;[|split]];
   eapply transitivity; eauto.
Qed.


Parameter A_ B_ N_ O_ D_ : term.
Parameter S_ : term -> term.
Definition myvect :=
  mkInd nil (ctxt_of(A_::lift 1 N_::nil)) 42
     (mkCstr nil (Ref 1::lift 2 O_::nil) ::
      mkCstr (CA_Const (lift 2 N_) ::
              CA_Const (lift 3 A_) ::
              CA_Rec nil nil (Ref 3::Ref 1::nil)::nil)
                (Ref 4 :: S_ (Ref 2) :: nil) ::
      nil).


(** Type-checking conditions of an inductive declaration *)

Fixpoint nfv_cstr args inst k :=
  match args with
  | CA_Const ty :: args' => nfv ty k /\ nfv_cstr args' inst (S k)
  | CA_Rec par rpar rinst :: args' =>
      List.fold_right (fun p kont k => nfv p k /\ kont (S k))
         (fun k => nfv_list rpar k /\ nfv_list rinst k) par k /\
      nfv_cstr args' inst (S k)
  | nil => nfv_list inst k
  end. 

Fixpoint check_constructor_data (e:env) (ipar idx:ctxt) (knd:nat) n args inst :=
  match args with
  | CA_Const ty :: args' =>
      ty <> kind /\
      typ e ty (type knd) /\
      check_constructor_data (ty::e) ipar idx knd (S n) args' inst
  | CA_Rec par rpar rinst :: args' =>
      List.fold_right (fun p chk_cont f => typ f p (type knd) /\ chk_cont (p::f))
        (fun f => let ipar' := lift_ctxt 0 (plus_rev (List.length par) (n + length ipar)) ipar in
                  let idx' := lift_ctxt (length ipar) (plus_rev (List.length par) (n + length ipar)) idx in
                  typ_ctxt f rpar ipar' /\
                  typ_ctxt f rinst (sub_ctxt (sub_consn rpar sub_id) idx')
) par e /\
      nfv_cstr args' inst 0 /\
      check_constructor_data (dum::e) ipar idx knd (S n) args' inst
  | nil => typ_ctxt e inst (lift_ctxt 0 n idx)
  end.

Definition check_constructor (e:env) (par idx:ctxt) (knd:nat) (c:constructor) :=
  check_constructor_data (push_ctxt e par) par idx knd 0 c.(cstr_args) c.(cstr_inst).

Record check_inductive (e:env) (ind:inductive) := mkChkInd {
  par_nk : Forall (fun ty => ty <> kind) (ind_par ind);
  idx_nk : Forall (fun ty => ty <> kind) (ind_idx ind);
  cstrs_ok : Forall (check_constructor e ind.(ind_par) ind.(ind_idx) ind.(ind_kind)) ind.(ind_cstrs)
  }.

(** The type of an inductive type *)
Definition inductive_type (i:inductive) : term :=
  mkprod i.(ind_par) (mkprod i.(ind_idx) (type i.(ind_kind))).

Fixpoint cstr_arg_ctxt X args dpth :=
  match args with
  | CA_Const ty :: args' => ty :: cstr_arg_ctxt X args' (S dpth)
  | CA_Rec par rpar rinst :: args' =>
      mkprod par (mkapp (mkapp (lift (length par + dpth) X) rpar) rinst) ::
      cstr_arg_ctxt X args' (S dpth)
  | nil => nil
  end.

Definition cstr_arg_concl Y (args:list constr_arg) npar inst :=
  mkapp (mkapp (lift (List.length args + npar) Y) (vect_of_ctxt' (List.length args) npar)) inst.
  
Definition cstr_argument_ctxt X ind n dpth :=
  match nth_error ind.(ind_cstrs) n with
  | Some c => cstr_arg_ctxt X c.(cstr_args) dpth
  | None => nil
  end.

Definition constructor_type par X Y c : term :=
  let dpth := List.length par in
  mkprod par
 (mkprod (cstr_arg_ctxt X c.(cstr_args) dpth)
    (cstr_arg_concl Y c.(cstr_args) dpth c.(cstr_inst))).


Lemma cstr_ctxt_same_length X args d :
  length (cstr_arg_ctxt X args d) = length args.
revert d.
induction args; simpl; intros; auto.
destruct a; simpl; rewrite IHargs; reflexivity.
Qed.

Lemma nfv_cstr_arg_ctxt k X dp cargs v :
  nfv_cstr cargs v k ->
  nfv (lift dp X) k ->
  nfv_ctxt (cstr_arg_ctxt X cargs dp) k.
revert dp k; induction cargs; simpl; intros; trivial.
destruct a; simpl.
 destruct H.
 split; trivial.
 apply IHcargs; trivial.
 apply nfv_liftS; trivial.

 destruct H.
 split.
  clear H1; revert dp k H H0.
  induction idx; simpl; intros.
   destruct H.
   apply nfv_mkapp; trivial.
   apply nfv_mkapp; trivial.

   destruct H.
   apply nfv_prod; trivial.
   rewrite plus_n_Sm.
   apply IHidx; trivial.
   apply nfv_liftS; trivial.

  apply IHcargs; trivial.
  apply nfv_liftS; trivial.
Qed.
(*
Lemma nfv_cstr_args cargs cinst X dp k :
  nfv (lift dp X) k ->
  nfv_cstr cargs cinst k ->
  nfv_ctxt (cstr_arg_ctxt X cargs dp) k.
revert dp k; induction cargs; simpl; intros; trivial.
destruct a; simpl.
 destruct H0.
 split; trivial.
 apply IHcargs; trivial.
 apply nfv_liftS; trivial.

 destruct H0.
 split.
  clear H1; revert dp k H H0.
  elim idx; simpl; intros.
   destruct H0.
   apply nfv_mkapp; trivial.
   apply nfv_mkapp; trivial.

   destruct H1.
   apply nfv_prod; trivial.
   rewrite plus_n_Sm.
   apply H; trivial.
   apply nfv_liftS; trivial.

  apply IHcargs; trivial.
  apply nfv_liftS; trivial.
Qed.
*)
Lemma nfv_cstr_inst cargs cinst k :
  nfv_cstr cargs cinst k ->
  nfv_list cinst (length cargs + k).
revert k; induction cargs; simpl; intros; trivial.
destruct a; simpl.
 destruct H.
 rewrite plus_n_Sm.
 auto.

 destruct H.
 rewrite plus_n_Sm.
 auto.
Qed.

Lemma nfv_change_typ_ctxt e g X dp cargs v ctx ty' :
  let k := plus_rev (length g) (length cargs) in
  nfv_ctxt ctx k ->
  nfv_cstr cargs v (length g) ->
  nfv_rev_ctxt g ->
  nfv (lift dp X) (length g) ->
  typ_ctxt (push_ctxt (push_rev_ctxt (dum::e) g) (cstr_arg_ctxt X cargs dp)) v ctx ->
  typ_ctxt (push_ctxt (push_rev_ctxt (ty'::e) g) (cstr_arg_ctxt X cargs dp)) v ctx.
revert dp g.
induction cargs; simpl; intros.
 red; intros.
 red in H3.
 pose (i' := V.lams (length g) (fun j => V.cons empty (V.shift 1 j)) i).
 assert (mkvecti v i == mkvecti v i').
  unfold  mkvecti.
  elim H0; simpl; intros; auto with *.
  apply couple_morph; trivial.
  apply nfv_int with (u:=cst empty); trivial.
 assert (mksigi ctx i == mksigi ctx i').
  apply nfv_int with (u:=cst empty).
  apply nfv_mksig; trivial.
  rewrite plus_rev_def in H.
  rewrite <- plus_n_O in H.
  trivial.
 rewrite H5,H6.
 clear H5 H6.
 apply H3.
 assert (tmp := typs_lams_rev); red in tmp.
 apply tmp with (e:=ty'::e)(s := sub_cons (cst empty) (sub_shift 1)).
  red;simpl;intros.
  apply vcons_add_var; auto.
   eapply typ_sub_shift with (ctx:=ty'::nil); trivial.
   apply singl_intro.

   revert H4.
   apply val_ok_morph; auto with *.
   apply push_rev_ctxt_morph; auto with *.
   apply nfv_rev_ctxt_eq; trivial.

 destruct a.
  destruct H0.
  simpl.
  eapply IHcargs with (g:=ty::g); simpl; auto.
  apply nfv_liftS; trivial.

  destruct H0.
  simpl.
  eapply IHcargs with (g:=_::g); simpl; auto.
   split; trivial.
   revert H0 H2.
   generalize dp (length g).
   elim idx; simpl; intros.
    destruct H0.
    apply nfv_mkapp; trivial.
    apply nfv_mkapp; trivial.

    destruct H2.
    apply nfv_prod; trivial.
    rewrite plus_n_Sm.
    apply H0; trivial.
    apply nfv_liftS; trivial.

   apply nfv_liftS; trivial.
Qed.

Lemma cstr_ctxt_nk e par idx knd X dp dp' cargs cinst :
  check_constructor_data e par idx knd dp cargs cinst ->
  X <> kind ->
  Forall (fun ty : term => ty <> kind) (cstr_arg_ctxt X cargs dp').
revert e dp dp'; induction cargs; simpl; intros; auto.
destruct a.
 destruct H as (?&_&?).
 constructor; eauto.

 destruct H as (?&_&?).
 constructor; eauto.
 apply mkprod_nk.
 apply mkapp_nk.
 apply mkapp_nk.
 apply lift_rec_nk; trivial.
Qed.

Lemma check_cstr_inst X e par idx knd dp dp' cargs cinst :
  check_constructor_data e par idx knd dp cargs cinst ->
  typ_ctxt (push_ctxt e (cstr_arg_ctxt X cargs dp'))
    cinst (lift_ctxt 0 (length cargs + dp) idx).
revert e dp dp'; induction cargs; simpl; intros; trivial.
destruct a; simpl. 
 destruct H as (_&?&?).
 specialize IHcargs with (1:=H0) (dp':=S dp').
 rewrite plus_n_Sm; trivial.

 destruct H as (?&?&?).
 specialize IHcargs with (1:= H1) (dp':=S dp').
 rewrite plus_n_Sm.
 apply nfv_change_typ_ctxt with (g:=nil); simpl; auto with *.
  apply nfv_ctxt_lift_rec1.
  omega.

  apply nfv_lift_rec1; simpl; auto with arith.
Qed.
(*
Fixpoint rec_branch_ctxt X P args dpth s :=
  match args with
  | CA_Const ty :: args' => Sub ty s :: rec_branch_ctxt X P args' (S dpth) (sub_lift 1 s)
  | CA_Rec par rinst :: args' =>
      mkprod (sub_ctxt s par) (mkapp (lift (length par + dpth) X) (List.map (fun t => Sub t (sub_lift (length par) s)) rinst)) ::
      mkprod (sub_ctxt (sub_comp s (sub_shift 1)) par) 
        (App (mkapp (lift (length par + S dpth) P)
                 (List.map (fun t => Sub t (sub_lift (length par) (sub_comp s (sub_shift 1)))) rinst))
           (mkapp (Ref (length par)) (vect_of_ctxt 0 par))) ::
      rec_branch_ctxt X P args' (S (S dpth)) (sub_comp (sub_lift 1 s) (sub_shift 1))
  | nil => nil
  end.

Fixpoint rec_branch_sub args s :=
  match args with
  | CA_Const ty :: args' => rec_branch_sub args' (sub_lift 1 s)
  | CA_Rec par rinst :: args' =>
      rec_branch_sub args' (sub_comp (sub_lift 1 s) (sub_shift 1))
  | nil => s
  end.

Lemma val_ok_branch_sub X P e f args dpth dpth' (s:sub) i :
  typ_sub e s f ->
  (forall j, eq_val (V.shift dpth j) (V.shift dpth' (s j))) ->
  val_ok (push_ctxt e (rec_branch_ctxt X P args dpth s)) i ->
  val_ok (push_ctxt f (cstr_arg_ctxt X args dpth')) (rec_branch_sub args s i).
revert e f dpth dpth' s i; induction args; simpl; intros; auto.
destruct a.
 simpl.
 simpl in H1.
 apply IHargs with (3:=H1); intros.
  apply typs_lams_rev with (l:=ty::nil) in H.
  simpl in H.
  red; intros.
  apply H.
  revert H2; apply val_ok_morph; auto with *.
  constructor.
  2:reflexivity.
  rewrite sub_lift0.
  reflexivity.

  rewrite V.shiftS_split with (n:=dpth).
  rewrite V.shiftS_split with (n:=dpth').
  simpl.
  rewrite V.lams_shift.
  apply H0.

 simpl.
 simpl in H1.
 apply IHargs with (3:=H1).
  red; intros.
  simpl.
  assert (tmp := typs_lams_rev).
  red in tmp.
  apply val_ok_shift1 in H2.
  eapply tmp with (1:=H) (l:=_::nil).
  simpl.
 revert H2; apply val_ok_morph; auto with *.
  constructor.
  2:reflexivity.
  rewrite sub_lift0.
  rewrite eq_sub_mkprod.
  apply mkprod_morph.
   reflexivity.
  rewrite eq_sub_mkapp.
  apply mkapp_morph.
   destruct X as [(X,Xm)|]; simpl; trivial.
   red; intros; apply Xm.
   do 2 rewrite V.lams0.
   rewrite <- H2.
   rewrite V.shift_split.
   rewrite V.lams_shift.
   rewrite V.shift_split.
   symmetry; apply H0.

   reflexivity.

  intros.
  simpl.
  rewrite V.shiftS_split with (n:=dpth').
  rewrite V.lams_shift.
  rewrite <- H0.
  rewrite V.shiftS_split with (n:=S dpth).
  rewrite V.shiftS_split with (n:=dpth).
  reflexivity.
Qed.
*)

(** Translate an inductive declaration into a positive operator *)

Definition ind_par' ind i :=
  Σ p ∈ mksigi ind.(ind_par) i, mksigi ind.(ind_idx) (cons_vect (length ind.(ind_par)) p i).

Definition int_constr_arg (c:constr_arg) (cont : val->dpositive) (i:val) : dpositive :=
  match c with
  | CA_Const ty =>
      dpos_norec (int ty i)
        (fun x => cont (V.cons x i))
  | CA_Rec idx par inst =>
      dpos_consrec
        (List.fold_right
           (fun ty cont i =>
              dpos_param (int ty i) (fun x => cont (V.cons x i)))
           (fun i => dpos_rec (couple (mkvecti par i) (mkvecti inst i)))
           idx
           i)
        (cont (V.cons empty i))
  end.

Definition int_constructor a (c:constructor) (i:val) : dpositive :=
  List.fold_right int_constr_arg
     (fun j => dpos_cst (P2p (a == mkvecti c.(cstr_inst) j)))
     c.(cstr_args)
     i.

Instance ind_par'_morph : Proper (eq_ind ==> eq_val ==> eq_set) ind_par'.
do 3 red; intros; unfold ind_par'.
apply sigma_ext; intros.
 apply int_morph; auto with *.
 apply mksig_morph.
 apply H.

 apply int_morph.
  apply mksig_morph.
  apply H.

  apply cons_vect_morph; trivial.
  destruct H as (?,_).
  elim H; simpl; auto with *.
Qed.

Lemma pm_ok :
  Proper (list_eq eq_term ==> list_eq eq_term ==> list_eq eq_term ==> eq_val ==> eqdpos)
     (fun idx par inst j =>
      fold_right
        (fun ty cont i => dpos_param (int ty i) (fun x => cont (V.cons x i)))
        (fun i => dpos_rec (couple (mkvecti par i) (mkvecti inst i))) idx 
        j).
do 5 red.
induction 1; simpl; intros.
 apply dpos_rec_morph.
 apply couple_morph; apply mkvecti_morph; trivial.

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
 apply dpos_cst_morph.
 apply P2p_morph.
 apply eq_set_morph; trivial.
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
   apply V.cons_morph; auto with *.
Qed.

Lemma pm_ok' :
  Proper (eq_set ==> list_eq eq_term ==> eq ==> eq_val ==> eqdpos)
     (fun a inst args j =>
      fold_right int_constr_arg
        (fun i => dpos_cst (P2p (a == mkvecti inst i))) args 
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
  apply V.cons_morph; auto with *.
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


Lemma check_inductive_pos_cstr e par idx knd c i a :
  check_constructor e par idx knd c ->
  val_ok e i ->
  let par' := Σ p ∈ mksigi par i, mksigi idx (cons_vect (length par) p i) in
  a ∈ par' ->
  isPositive par' (int_constructor (snd a) c (cons_vect (length par) (fst a) i)).
intros.
unfold check_constructor in H.
cut (forall j g,
   eq_val (V.shift (List.length g + List.length par) j) i ->
   check_constructor_data (push_rev_ctxt (push_ctxt e par) g) par idx
     knd (List.length g) c.(cstr_args) c.(cstr_inst) -> 
  (val_ok (push_rev_ctxt (push_ctxt e par) g) j) ->
   isPositive par' (int_constructor (snd a) c j)).
  intros h.
  apply h with nil.
   simpl.
   apply shift_cons_vect.

   simpl.
   exact H.

   simpl.
   apply cons_vect_typ; trivial.
   apply fst_typ_sigma in H1; trivial.

 unfold int_constructor.
 elim c.(cstr_args); simpl; intros.
  apply isPos_cst.

  destruct a0; simpl.
   destruct H4 as (_&?&?).
   apply isDPos_norec; intros.
    do 2 red; intros.
    apply pm_ok'; auto with *.
    rewrite H7; reflexivity.
   eapply H2 with (ty::g); trivial.
    simpl.
    apply vcons_add_var; auto.

   destruct H4 as (?&?&?).
   apply isDPos_consrec; auto.
   2:apply H2 with (cst(singl empty) :: g); simpl; auto.
   2:apply vcons_add_var; simpl; trivial.
   2:apply singl_intro.
   clear H6 H7.
   revert j g H3 H4 H5; induction idx0; simpl; intros.
    destruct H4.
    apply isDPos_rec.
    apply couple_intro_sigma.
     do 2 red; intros.
     apply int_morph; auto with *.
     apply cons_vect_morph; auto with *.

     red in H4.
     specialize H4 with (1:=H5).
     rewrite lift_ctxt_eq in H4.
     rewrite V.lams0 in H4.
     rewrite H3 in H4.
     trivial.

     red in H6.
     specialize H6 with (1:=H5).
     rewrite sub_ctxt_eq in H6.
     rewrite lift_ctxt_eq in H6.
     revert H6; apply eq_elim.
     apply int_morph; auto with *.
     assert (length par = length par0).
      apply H4 in H5.
      apply typ_ctxt_length_inv in H5; trivial.
      rewrite lift_ctxt_length in H5; auto.
     rewrite sub_consn_vecti; simpl.
     rewrite <- H6.
     rewrite eq_lams_cons_vect with (s:=sub_shift (length g + length par)).
     simpl.
     rewrite H3; reflexivity.

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
  a ∈ ind_par' ind i ->
  isPositive (ind_par' ind i)
     (int_constructors ind.(ind_cstrs) (cons_vect (length ind.(ind_par)) (fst a) i) (snd a)).
intros.
destruct H as (_,_,cstrs_ok).
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
  a ∈ ind_par' ind i ->
  pos_universe (ind_par' ind i) (ZFecc.ecc (S ind.(ind_kind)))
     (int_constructors (ind_cstrs ind) (cons_vect (length ind.(ind_par)) (fst a) i) (snd a)).
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
  (val_ok (push_rev_ctxt (push_ctxt e ind.(ind_par)) g) j) ->
   eq_val (V.shift (List.length g + List.length ind.(ind_par)) j) i ->
   check_constructor_data (push_rev_ctxt (push_ctxt e (ind_par ind)) g) 
     ind.(ind_par) ind.(ind_idx) ind.(ind_kind) (length g) x.(cstr_args) x.(cstr_inst) ->
   pos_universe (ind_par' ind i) (ZFecc.ecc (S ind.(ind_kind))) (int_constructor (snd a) x j)).
  intros h.
  apply h with nil; simpl.
   apply cons_vect_typ; trivial.
   apply fst_typ_sigma in H1; trivial.

   apply shift_cons_vect.

   exact H2.

 clear H2.
 unfold int_constructor.
 destruct x as (args,inst); simpl.
 induction args; simpl; intros.
  apply isUPos_inst; auto.

  destruct a0; simpl.
   destruct H3 as (_&?&?).
   apply isUPos_norec; intros; auto.
    do 2 red; intros.
    apply pm_ok'; auto with *.
    rewrite H5; reflexivity.

    apply H3; trivial.

    apply IHargs with (ty::g); simpl; auto.
    apply vcons_add_var; auto.

   destruct H3 as (?&?&?).
   apply isUPos_consrec; auto.
   2:apply IHargs with (cst(singl empty) :: g); simpl; auto.
   2:apply vcons_add_var; trivial.
   2:apply singl_intro.
   clear H4 H5.
   revert j g H H2 H3; induction idx; simpl; intros.
    destruct H3.
    apply isUPos_rec; auto.
    apply couple_intro_sigma.
     do 2 red; intros.
     rewrite H6; reflexivity.

     red in H3.
     specialize H3 with (1:=H).
     rewrite lift_ctxt_eq in H3.
     rewrite V.lams0 in H3.
     rewrite H2 in H3.
     trivial.

     red in H4.
     specialize H4 with (1:=H).
     rewrite sub_ctxt_eq in H4.
     rewrite lift_ctxt_eq in H4.
     revert H4; apply eq_elim.
     apply int_morph; auto with *.
     assert (length par = length ind.(ind_par)).
      apply H3 in H.
      apply typ_ctxt_length_inv in H; trivial.
      rewrite lift_ctxt_length in H; auto.
     rewrite sub_consn_vecti; simpl.
     rewrite H4.
     rewrite eq_lams_cons_vect with (s:=sub_shift (length g + length ind.(ind_par))).
     simpl.
     rewrite H2; reflexivity.

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
                 (cons_vect (List.length ind.(ind_par)) (fst a) (V.shift 2 i)) (snd a) in
  dIND (ind_par' ind (V.shift 2 i)) pos (couple (i 1) (i 0))).
(* end show *)
do 2 red; intros.
apply dIND_morph_gen.
 apply sigma_morph.
  apply int_morph; auto with *.
  rewrite H; reflexivity.

  red; intros.
  apply int_morph; auto with *.
  rewrite H,H0; reflexivity.

 red; intros.
 apply int_constructors_morph; auto with *.
  rewrite H,H0; reflexivity.
  apply snd_morph; trivial.

 apply couple_morph; apply H.
Defined.

Definition Ind (ind:inductive) : term :=
  Absn ind.(ind_par)
    (Absn ind.(ind_idx)
      (Sub
        (SInd ind)
           (sub_comp
               (sub_lift 1 (sub_mkblock (List.length ind.(ind_par))))
               (sub_mkblock (List.length ind.(ind_idx)))))).


Lemma typ_SInd e ind :
  check_inductive e ind ->
  typ (Sub (mksig ind.(ind_idx)) (sub_unblock (length ind.(ind_par))) :: mksig ind.(ind_par) :: e)
    (SInd ind) (type (ind_kind ind)).
red; intros.
apply in_int_el.
red.
simpl.
assert (val_ok e (V.shift 2 i)).
 apply typ_sub_shift with
   (ctx:= mksig (ind_par ind) :: Sub(mksig (ind_idx ind))(sub_unblock (length ind.(ind_par))) :: nil); trivial.
assert (couple (i 1) (i 0) ∈ ind_par' ind (V.shift 2 i)).
 apply couple_intro_sigma.
  do 2 red; intros.
  apply int_morph; auto with *.
  rewrite H3; reflexivity.

  assert (tmp := H0 1 _ eq_refl).
  destruct ind.(ind_par); simpl in *; trivial.
  revert tmp; apply eq_elim.
  apply sigma_morph.
   rewrite V.lams0; reflexivity.
  red; intros.
  rewrite V.lams0, H2.
  reflexivity.

  assert (tmp := H0 0 _ eq_refl).
  destruct ind.(ind_idx); simpl in *; trivial.
apply G_dIND; auto.
 apply isDP_intro.
  do 2 red; intros.
  apply int_constructors_morph; auto.
  reflexivity.
  rewrite H3; reflexivity.
  apply snd_morph; trivial.

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
set (sb := sub_comp _ _).
apply typ_Absn.
 apply mkprod_nk.
 discriminate.
apply typ_Absn.
 discriminate.
pose (k := Sub (type ind.(ind_kind)) sb).
change (type ind.(ind_kind)) with k.
apply typ_Sub with (Sub (mksig ind.(ind_idx)) (sub_unblock (length ind.(ind_par))) :: mksig ind.(ind_par) :: e).
 apply typ_SInd; trivial.

 apply typ_sub_comp with (mksig ind.(ind_idx) :: push_ctxt e ind.(ind_par)).
  apply val_ok_mkblock.
  apply ind_ok.

  red; intros.
  assert (tmp := typ_sub_lams1).
  red in tmp.
  eapply tmp.
   apply val_ok_mkblock.
   apply ind_ok.

   rewrite eq_sub_comp.
   revert H; apply val_ok_morph; auto with *.
   constructor; auto with *.
   rewrite sub_comp_block_unblock.
   rewrite eq_sub_id.
   reflexivity.
Qed.

Lemma eq_Ind_app e ind n v1 v2 i :
  typ_ctxt e v1 (lift_ctxt 0 n ind.(ind_par)) ->
  typ_ctxt e v2 (sub_ctxt (sub_consn v1 sub_id) (lift_ctxt (length ind.(ind_par)) n ind.(ind_idx))) ->
  val_ok e i ->
  int (mkapp (mkapp (lift n (Ind ind)) v1) v2) i ==
  int (SInd ind) (V.cons (mkvecti v2 i) (V.cons (mkvecti v1 i) (V.shift n i))).
intros.
unfold Ind.
rewrite <- eq_sub_comp.
unfold lift; rewrite lift_rec_equiv.
assert (lg1 : length v1 = length ind.(ind_par)).
 apply H in H1.
 apply typ_ctxt_length_inv in H1.
 rewrite lift_ctxt_length in H1.
 trivial.
assert (lg2 : length v2 = length ind.(ind_idx)).
 apply H0 in H1.
 apply typ_ctxt_length_inv in H1.
 rewrite sub_ctxt_length in H1.
 rewrite lift_ctxt_length in H1.
 trivial.
assert (r : Reflexive (fun a a' => int a i == int a' i)).
 red; intros; reflexivity.
assert (tmp := eq_betan).
red in tmp.
eapply transitivity.
 apply eq_int_mkapp.
 reflexivity.
 2:reflexivity.
 eapply tmp with (e:=e); trivial.
 red in H|-*.
 intros; rewrite sub_ctxt_eq.
 apply H in H2.
 rewrite lift_ctxt_eq in H2.
 trivial.

 rewrite tmp with (2:=H1). 
  rewrite int_Sub_eq.
  rewrite int_Sub_eq.
  rewrite int_Sub_eq.
  apply int_morph; auto with *.
  simpl.
  rewrite val_mkblock_consn; auto.
  rewrite <- V.cons_lams.
  apply V.cons_morph; auto with *.
  rewrite V.lams0.
  rewrite val_mkblock_consn; auto.
  simpl.
  rewrite V.lams0.
  reflexivity.

  apply val_mkblock_morph.

 red; intros.
 apply H0 in H2.
 revert H2; apply eq_elim.
 rewrite sub_ctxt_eq.
 rewrite lift_ctxt_eq.
 rewrite sub_ctxt_eq.
 apply int_morph; auto with *.
 rewrite sub_consn_lams with (s1:= sub_shift n); auto.
 rewrite sub_consn_vecti.
 rewrite sub_consn_vecti.
 apply cons_vect_morph; auto with *.
 simpl.
 rewrite V.lams0; reflexivity.
Qed.


(** Constructor [n] of arity [ar] *)
Definition SCstr (n ar:nat) : term :=
  Sub (Op1 (mktag n) (Ref 0)) (sub_mkblock ar).


Lemma eq_oper_sigma e i' i par idx knd X X' c dp z :
  morph1 X' ->
  check_constructor_data e par idx knd dp c.(cstr_args) c.(cstr_inst) ->
  let dp' := dp + length par in
  (forall g j v1 v2,
   typ_ctxt (push_ctxt e g) v1 (lift_ctxt 0 (length g + dp') par) ->
   typ_ctxt (push_ctxt e g) v2 (sub_ctxt (sub_consn v1 sub_id) (lift_ctxt (length par) (length g + dp') idx)) ->
   val_ok (push_ctxt e g) j ->
   eq_val (V.shift (length g + dp') j) (V.shift dp' i) ->
   int (mkapp (mkapp (lift (length g + dp') X) v1) v2) j == X' (couple (mkvecti v1 j) (mkvecti v2 j))) ->
  val_ok e i ->
  mkvecti c.(cstr_inst) (cons_vect (length c.(cstr_args)) z i') ==
  mkvecti c.(cstr_inst) (cons_vect (length c.(cstr_args)) z i) ->
  z ∈ mksigi (cstr_arg_ctxt X c.(cstr_args) dp') i ->
  z ∈ dp_oper (int_constructor (mkvecti c.(cstr_inst) (cons_vect (length c.(cstr_args)) z i')) c i) X'.
intros X'm.
unfold int_constructor.
destruct c as (cargs,cinst); simpl.
revert z e i i' dp.
induction cargs; simpl; intros.
 unfold P2p; rewrite cond_set_ax; auto.

 destruct a; simpl.
  destruct H as (_&?&?).
  simpl in H3.
  apply sigma_elim in H3.
   destruct H3 as (zet&?&?).
   rewrite zet; clear zet.
   apply couple_intro_sigma; trivial.
    do 2 red; intros.
    apply @eq_dop; trivial.
    apply pm_ok'; auto with *.
    rewrite H7; reflexivity.
   apply IHcargs with (1:=H4); trivial.
    intros.
    simpl in H6, H7|-*; rewrite <- plus_n_Sm in H6, H7|-*.
    apply H0 with (g:=ty::g); trivial.
    simpl.
    simpl in H9; rewrite V.shiftS_split in H9.
    rewrite V.shift_cons in H9.
    rewrite <- plus_n_Sm in H9.
    trivial.
   apply vcons_add_var; trivial.

   do 2 red; intros.
   rewrite H6; reflexivity.

 simpl in H3.
 destruct H as (?&?&?).
 apply sigma_elim in H3.
 2:do 2 red; intros ? ? ? h; rewrite h; reflexivity.
 destruct H3 as (zet&?&?).
 rewrite zet; clear zet.
 apply couple_intro.
  revert H3; apply eq_elim.
  clear H4 H5 H6.
  revert dp e i i' H H0 H1 H2.
  elim idx0; simpl; intros.
   destruct H.
   apply H0 with (g:=nil); trivial.
   reflexivity.

   destruct H0.
   apply cc_prod_ext.
    reflexivity.
   red; intros.
   rewrite H6 in H5|-*.
   clear x H6; rename x' into x.  
   rewrite plus_n_Sm.

   apply H with (dp:=S dp)(e:=a::e)(i':=V.cons x i); trivial.
    intros.
    simpl in H6,H7|-*.
    rewrite <- plus_n_Sm in H6,H7|-*.
    apply H1 with (g:=a::g); trivial.
    simpl in H9.
    rewrite V.shiftS_cons in H9.
    rewrite <- plus_n_Sm in H9.
    trivial.

    apply vcons_add_var; trivial.

    reflexivity.
    
  apply IHcargs with (1:=H5); trivial.
   intros.
   simpl in H7,H8|-*.
   rewrite <- plus_n_Sm in H7,H8|-*.
   apply H0 with (g:=dum::g); trivial.
   simpl in H10.
   rewrite V.shiftS_cons in H10.
   rewrite <- plus_n_Sm in H10.
   trivial.

   apply vcons_add_var; auto.
   apply singl_intro.

   rewrite H2.
   rewrite mkvecti_def.
   rewrite mkvecti_def.
   eapply nfv_elim with (length cargs).
    apply nfv_cstr_inst in H4.
    rewrite <- plus_n_O in H4.
    elim H4; simpl; intros.
     red; reflexivity.
     apply nfv_Couple; trivial.

    intros.
    apply cons_vect_dom with (k:=0).
    2:omega.
    intros [|a'] h; [elim h;reflexivity|simpl;reflexivity].

   revert H6; apply eq_elim.
   simpl.
   apply nfv_elim with (k:=0).
    apply nfv_mksig.
  apply nfv_cstr_arg_ctxt with (1:=H4).
  apply nfv_lift_rec1; auto with arith.

  intros [|a] h;[elim h; trivial|simpl].
  reflexivity.
Qed.


Lemma typ_SCstr e ind n c :
  check_inductive e ind ->
  nth_error ind.(ind_cstrs) n = Some c ->
  typ (push_ctxt (push_ctxt e ind.(ind_par))
        (cstr_arg_ctxt (Ind ind) (cstr_args c) (length (ind_par ind))))
    (SCstr n (length c.(cstr_args)))
    (cstr_arg_concl (Ind ind) c.(cstr_args) (length ind.(ind_par)) c.(cstr_inst)).
intros chk_ind get_cstr.
unfold SCstr.
red; intros.
simpl.
apply in_int_el.
red.
assert (cstr_ok : check_constructor e ind.(ind_par) ind.(ind_idx) ind.(ind_kind) c).
 revert n get_cstr.
 elim (cstrs_ok _ _ chk_ind); simpl; intros.
  destruct n; discriminate.
 destruct n.
  injection get_cstr; intros; subst x; trivial.
  apply H2 with n; exact get_cstr.
red in cstr_ok.
assert (val_ok1 :
  val_ok (push_ctxt e ind.(ind_par)) (V.shift (length c.(cstr_args)) i)).
 apply typ_sub_shift in H.
 rewrite cstr_ctxt_same_length in H.
 trivial.
pose (i0 := V.shift (length c.(cstr_args) + length ind.(ind_par)) i).
assert (val_ok0 : val_ok e i0).
 apply typ_sub_shift in val_ok1.
 unfold i0.
 revert val_ok1; apply val_ok_morph; auto with *.
 rewrite V.shift_split; reflexivity.
pose (p := val_mkblock (length ind.(ind_par)) (V.shift (length c.(cstr_args)) i) 0).
pose (cinst := mkvecti c.(cstr_inst) i).
pose (a := couple p cinst).
assert (eq_i1 : eq_val (V.shift (length c.(cstr_args)) i)
           (cons_vect (length (ind_par ind)) p i0)).
 unfold i0.
 rewrite V.shift_split.
 unfold p.
 apply cons_mkblock.

(* parameter well-typed *)
assert (pty : p ∈ mksigi ind.(ind_par) i0).
  apply val_ok_mkblock in val_ok1.
  2:apply chk_ind.
  red in val_ok1.
  assert (tmp := val_ok1 0 _ eq_refl).
  apply in_int_not_kind in tmp.
  2:apply lift_rec_nk.
  2:apply mksig_nk.
  red in tmp.
  simpl in tmp; fold p in tmp.
  revert tmp; apply eq_elim.
  unfold lift; rewrite int_lift_rec_eq.
  rewrite V.lams0.
  apply int_morph; auto with *.
  rewrite shift_mkblock.
  rewrite <- V.shift_split.
  reflexivity.

(* argument well-typed *)
specialize check_cstr_inst with (X:=Ind ind) (dp':=length ind.(ind_par)) (1:=cstr_ok);
  intros tyinst.

assert (tya : a ∈ ind_par' ind i0).
 apply couple_intro_sigma; trivial.
  do 2 red; intros.
  rewrite H1; reflexivity.

  red in tyinst.
  specialize tyinst with (1:=H).
  revert tyinst; apply eq_elim.
  rewrite lift_ctxt_eq.
  apply int_morph; auto with *.
  rewrite V.lams0.
  rewrite <- plus_n_O; trivial.

(* positivity *)
pose (pos a := int_constructors ind.(ind_cstrs)
                  (cons_vect (length ind.(ind_par)) (fst a) i0) (snd a)).
assert (posp : isDPositive (ind_par' ind i0) pos).
 unfold pos.
 unfold ind_par'.
 apply isDP_intro.
  do 2 red; intros.
  apply int_constructors_morph; auto with *.
   rewrite H0; reflexivity.
   apply snd_morph; trivial.
 intros.
 apply check_inductive_pos with (1:=chk_ind); trivial.

assert (eq_ind_app :
        int (cstr_arg_concl (Ind ind) (cstr_args c) (length ind.(ind_par)) (cstr_inst c)) i ==
        dIND (ind_par' ind i0) pos a).
 unfold cstr_arg_concl.
 rewrite eq_Ind_app with (3:=H).
   simpl.
   apply dIND_morph_gen; auto with *.
    apply ind_par'_morph; auto with *.
    rewrite V.shift_split with (m:=1).
    rewrite V.shift_cons.
    rewrite V.shift_cons.
    reflexivity.

    red; intros.
    unfold pos.
    apply int_constructors_morph; auto with *.
     apply cons_vect_morph; auto with *.
      rewrite H0; reflexivity.
     rewrite V.shift_split with (m:=1).
     rewrite V.shift_cons.
     rewrite V.shift_cons.
     reflexivity.

     rewrite H0; reflexivity.

    apply couple_morph.
    2:reflexivity.
    unfold p.
    rewrite (vect_of_ctxt'_reloc _  _ 0 i).
    apply vect_of_ctxt'_eq_mkblock.

  red; intros.
  rewrite (vect_of_ctxt'_reloc _  _ 0 i1).
  rewrite lift_ctxt_eq.
  rewrite V.lams0.
  rewrite V.shift_split.
  apply typ_sub_shift in H0.
  simpl in H0; rewrite cstr_ctxt_same_length in H0.
  apply vect_of_ctxt'_typ with (1:=H0).
  apply chk_ind.

  red; intros.
  apply tyinst in H0.
  revert H0; apply eq_elim.
  rewrite lift_ctxt_eq.
  rewrite sub_ctxt_eq.
  rewrite lift_ctxt_eq.
  rewrite V.lams0.
  apply int_morph; auto with *.
  rewrite <- plus_n_O.
  rewrite sub_consn_vecti.
  rewrite vect_of_ctxt'_length.
  rewrite eq_lams_cons_vect with (s:=sub_shift (length c.(cstr_args) + length ind.(ind_par))).
  simpl.
  rewrite (vect_of_ctxt'_reloc _  _ 0 i1).
  rewrite V.shift_split.
  rewrite cons_vect_of_ctxt'.
  reflexivity.

rewrite eq_ind_app.
rewrite dIND_eq; trivial.

(* type arg block *)
pose (cinst' := mkvecti c.(cstr_inst)
        (cons_vect (length c.(cstr_args)) (val_mkblock (length c.(cstr_args)) i 0)
            (V.shift (length c.(cstr_args)) i))).
assert (eqi : cinst == cinst').
 unfold cinst, cinst'.
 rewrite <- cons_mkblock.
 reflexivity.
pose (cinst'' := mkvecti c.(cstr_inst)
        (cons_vect (length c.(cstr_args)) (val_mkblock (length c.(cstr_args)) i 0)
            (cons_vect (length ind.(ind_par)) p i0))).
assert (eqi' : cinst == cinst'').
 unfold cinst, cinst''.
 rewrite <- eq_i1.
 rewrite <- cons_mkblock.
 reflexivity.
assert (tyblk : val_mkblock (length c.(cstr_args)) i 0 ∈
        dp_oper (int_constructor cinst'' c (cons_vect (length ind.(ind_par)) p i0)) (dIND (ind_par' ind i0) pos)).
 eapply eq_oper_sigma with (2:=cstr_ok) (X:=Ind ind); auto with *.
  apply dIND_morph; auto with *.

  intros.
  simpl.
  rewrite eq_Ind_app with (1:=H0); trivial.
   simpl.
   apply dIND_morph_gen; auto with *.
    apply ind_par'_morph; auto with *.
    rewrite V.shift_split with (m:=1).
    rewrite V.shift_cons.
    rewrite V.shift_cons.
    simpl in H3.
    rewrite shift_cons_vect in H3; trivial.

    red; intros.
    unfold pos.
    apply int_constructors_morph; auto with *.
    apply cons_vect_morph; auto with *.
     rewrite H4; reflexivity.
    rewrite V.shift_split with (m:=1).
    rewrite V.shift_cons.
    rewrite V.shift_cons.
    simpl in H3.
    rewrite shift_cons_vect in H3; trivial.

    rewrite H4; reflexivity.

   rewrite <- eq_i1.
   trivial.

  apply val_ok_mkblock in H.
  generalize (H 0 _ eq_refl).
  intro.
  apply in_int_not_kind in H0.
  2:apply lift_rec_nk.
  2:apply mksig_nk.
  red in H0.
  simpl in H0.
  rewrite cstr_ctxt_same_length in H0.
  unfold lift in H0; rewrite int_lift_rec_eq in H0.
   rewrite V.lams0 in H0.
   rewrite shift_mkblock in H0.
   rewrite eq_i1 in H0.
   trivial.

   eapply cstr_ctxt_nk with (1:=cstr_ok).
   apply Absn_nk.
   apply Absn_nk.
   discriminate.


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
  revert tyblk; apply eq_elim.
  apply @eq_dop.
   apply int_constructor_morph; auto with *.
   unfold a.
   rewrite snd_def.
   auto with *.

   unfold a.
   rewrite fst_def.
   reflexivity.

  apply dIND_morph; trivial.

  apply inr_typ; auto.
Qed.


Definition Cstr (ind:inductive) (n:nat) : term :=
  let cargs := cstr_argument_ctxt (Ind ind) ind n (List.length ind.(ind_par)) in
  Absn ind.(ind_par) (Absn cargs (SCstr n (List.length cargs))).


Lemma typ_Cstr e ind n c :
  check_inductive e ind ->
  nth_error ind.(ind_cstrs) n = Some c ->
  typ e (Cstr ind n) (constructor_type ind.(ind_par) (Ind ind) (Ind ind) c).
intros chk_ind get_cstr.
unfold Cstr.
unfold constructor_type.
unfold cstr_argument_ctxt.
rewrite get_cstr.
apply typ_Absn.
 apply mkprod_nk.
 apply mkapp_nk.
 apply mkapp_nk.
 apply lift_rec_nk.
 apply Absn_nk.
 apply Absn_nk.
 discriminate.
apply typ_Absn.
 apply mkapp_nk.
 apply mkapp_nk.
 apply lift_rec_nk.
 apply Absn_nk.
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
    mkInd (ctxt_of(A::nil)) (ctxt_of (N::nil)) 42
     (mkCstr nil (O::nil) ::
      mkCstr (CA_Const N ::
              CA_Const(lift 2 A) ::
              CA_Rec nil (Ref 2::nil) (Ref 1::nil)::nil) (S (Ref 2) :: nil) ::
      nil).

(*  Definition t := inductive_type vect.*)
(*  Definition t := inductive_obj vect i.*)
 Definition t := List.map (constructor_type vect.(ind_par) (Ind vect) (Ind vect)) vect.(ind_cstrs).
  Goal t=t.
unfold t at 2.
unfold constructor_type.
Opaque Sub Ind.
simpl.
unfold cstr_arg_concl; simpl.
Abort.

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
