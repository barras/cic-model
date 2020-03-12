Require Import ZFfunext ZFfixrec ZFrelations ZFcoc ZFord.

Lemma cont_is_mono X :
  morph1 X -> continuous X -> increasing X.
intros Xm Xcont o o' oo oo' leo.
rewrite (Xcont o'); trivial.
apply sup_lub; intros.
 do 2 red; intros.
 rewrite H0; reflexivity.
rewrite (Xcont o); trivial.
apply sup_incl with (F:=fun o'=>X(osucc o')); auto.
do 2 red; intros.
rewrite H1; reflexivity.
Qed.

Section Recursor.

  (** The domain, indexed by ordinals *)
  Variable X : set -> set.
  (** The co-domain *)
  Variable U : set -> set -> set.

Section RecursorSpecification.

  (** The recursive definition *)
  Variable F : set -> set -> set.
  (** A function (indexed by ordinals) we expect to satisfy the recursive equation *)
  Variable f : set -> set.
  (** The ordinal up to which [f] satisfies the recursive equation *)
  Variable o : set.
  Hypothesis oo : isOrd o.
  
  (** The condition expressing that [f] satisfies the recursive equation [F] up to [o]. *)
  Record rec0 := mkrec0 {
    RXm : morph1 X;
    (* Domain is continuous *)
    RXcont : continuous X;
    (* typing *)
    Rtyp : forall o', isOrd o' -> o' ⊆ o -> f o' ∈ Π x ∈ X o', U o' x;
    (* equation *)
    Reqn : forall o1 o2 n,
        isOrd o1 -> isOrd o2 -> o1 ⊆ o -> o2 ⊆ o ->
        n ∈ X o1 ->
        n ∈ X (osucc o2) ->
        cc_app (f o1) n == cc_app (F o2 (f o2)) n
  }.

  Hypothesis isrec : rec0.

  Let Xm := RXm isrec.
  Let Xcont := RXcont isrec.
  Let Req := Reqn isrec.

  Let Xmono := cont_is_mono _ Xm Xcont.
  
  Lemma rec0_typ o' :
    isOrd o' ->
    o' ⊆ o ->
    f o' ∈ (Π x ∈ X o', U o' x).
apply (Rtyp isrec).
Qed.

  Lemma rec0_eqn_succ o' x :
    o' ∈ o ->
    x ∈ X (osucc o') ->
    cc_app (f (osucc o')) x == cc_app (F o' (f o')) x.
intros.
assert (oo' : isOrd o') by eauto using isOrd_inv.
apply Req; auto.
red; intros; apply isOrd_plump with o'; auto.
 apply isOrd_inv with (osucc o'); auto.
 apply olts_le; auto.
Qed.

  Lemma rec0_irr o1 o2 x :
    isOrd o1 -> isOrd o2 -> o1 ⊆ o2 -> o2 ⊆ o ->
    x ∈ X o1 ->
    cc_app (f o1) x == cc_app (f o2) x.
intros.
rewrite Req with (o1:=o2) (o2:=o2); auto.
 rewrite Req with (o1:=o1) (o2:=o2); auto with *.
  transitivity o2; trivial.

  revert H3; apply Xmono; auto.
  apply ord_lt_le; auto; apply ole_lts; auto.

 revert H3; apply Xmono; auto.

 revert H3; apply Xmono; auto.
 apply ord_lt_le; auto; apply ole_lts; auto.
Qed.

  Lemma rec0_eqn o' x :
    isOrd o' -> o' ⊆ o ->
    x ∈ X o' ->
    cc_app (f o') x == cc_app (F o' (f o')) x.
intros.
apply Req; auto.
revert H1; apply Xmono; auto with *.
apply ord_lt_le; auto; apply lt_osucc; auto.
Qed.

End RecursorSpecification.

Section RecursorDef.

  (** The recursive definition *)
  Variable F : set -> set -> set.

  Variable O : set.

Record rec0_hyps : Prop := rec0_intro {
    RHXm : morph1 X;
    (* Domain is continuous *)
    RHXcont : continuous X;
    Oo : isOrd O;
    RHUm : morph2 U;
    (* Co-domain is monotonic *)
    RHUmono : forall o o' x,
        isOrd o ->
        o ⊆ o' ->
        o' ∈ osucc O ->
        x ∈ X o ->
        U o x ⊆ U o' x;
    RHm : morph2 F;
    (* Recursive equation is well-typed *)
    RHtyp : forall o,
        o ∈ O ->
        forall f,
        f ∈ (Π x ∈ X o, U o x) ->
        F o f
          ∈ (Π x ∈ X (osucc o), U (osucc o) x);
    (* Recursive equation is stage irrelevant *)
    RHirr : forall o o' f g,
        isOrd o ->
        o ⊆ o' ->
        o' ∈ osucc O ->
        f ∈ (Π x ∈ X o, U o x) ->
        g ∈ (Π x ∈ X o', U o' x) ->
        fcompat (X o) f g ->
        fcompat (X (osucc o)) (F o f) (F o' g)
  }.

Hypothesis hyps : rec0_hyps.

Let Xm := RHXm hyps.
Let Xcont := RHXcont hyps.
Let Xmono := cont_is_mono _ Xm Xcont.
Let Oo : isOrd O := Oo hyps.
Let Um := RHUm hyps.
Let Fm := RHm hyps.

  Let Q' o f := forall x, x ∈ X o -> cc_app f x ∈ U o x.

Let Qty o f :
    isOrd o ->
    (is_cc_fun (X o) f /\ Q' o f <-> f ∈ cc_prod (X o) (U o)).
split; intros.
 destruct H0.
 rewrite cc_eta_eq' with (1:=H0).
 apply cc_prod_intro; auto.
  do 2 red; intros; apply cc_app_morph; auto with *.

  do 2 red; intros; apply Um; auto with *.

 split.
  rewrite cc_eta_eq with (1:=H0).
  apply is_cc_fun_lam.
  do 2 red; intros; apply cc_app_morph; auto with *.

  red; intros.
  apply cc_prod_elim with (1:=H0); trivial.
Qed.


Let Q'm :
   forall o o',
   isOrd o ->
   o ⊆ O ->
   o == o' -> forall f f', fcompat (X o) f f' -> Q' o f -> Q' o' f'.
intros.
unfold Q' in H3|-*; intros.
generalize Xm; intros. (* ? *)
rewrite <- H1 in H4.
specialize H3 with (1:=H4).
red in H2; rewrite <- H2; trivial.
revert H3; apply (RHUmono hyps); auto with *.
 rewrite <- H1; reflexivity.
 rewrite <- H1; apply ole_lts; trivial.
Qed.


Let Q'cont : forall o f : set,
 isOrd o ->
 o ⊆ O ->
 is_cc_fun (X o) f ->
 (forall o' : set, o' ∈ o -> Q' (osucc o') f) -> Q' o f.
intros.
red; intros.
red in Xcont; rewrite Xcont in H3; trivial.
apply sup_ax in H3.
 destruct H3 as (o',?,?).
generalize (H2 _ H3 _ H4).
apply (RHUmono hyps); eauto using isOrd_inv with *.
 red; intros.
 apply isOrd_plump with o'; eauto using isOrd_inv.
 apply olts_le in H5; trivial.

 apply ole_lts; auto.
do 2 red; intros; apply Xm; apply osucc_morph; trivial.
Qed.

Let Q'typ : forall o f,
 o ∈ O ->
 is_cc_fun (X o) f ->
 Q' o f -> is_cc_fun (X (osucc o)) (F o f) /\ Q' (osucc o) (F o f).
intros.
assert (isOrd o) by eauto using isOrd_inv.
apply Qty; auto.
apply (RHtyp hyps); trivial.
apply Qty; auto.
Qed.

Lemma REC0_recursor0 : recursor O X Q' F.
split; intros; auto.
 apply Q'm with o f; auto.

 red; intros.
 destruct H1 as (?,?).
 destruct H2 as (?,?).
 apply (RHirr hyps); auto.
  apply ole_lts; auto.

  apply Qty; auto.
  apply Qty; auto.
Qed.

Lemma REC0_is_rec : is_rec X Q' F (REC F) O.
apply REC_stage with (2:=REC0_recursor0); trivial.
Qed.

Lemma REC0_rec :
  rec0 F (REC F) O.
split; intros; trivial.
 apply Qty; auto.
 apply REC0_is_rec with (o' := o'); trivial.

 destruct REC0_is_rec with (o1⊔o2) as (typ,irr,exp).
  apply isOrd_osup2; auto.
  apply osup2_lub; auto.
 red in irr.
 rewrite irr with (o':=o1); auto.
 2:apply osup2_incl1; auto.
 red in exp.
 rewrite exp.
 2:revert H3; apply Xmono; auto.
 2:apply isOrd_osup2; auto.
 2:apply osup2_incl1; auto.
 symmetry.
 apply (RHirr hyps); auto.
  apply osup2_incl2; auto. 
  apply ole_lts; auto.
   apply isOrd_osup2; auto.
  apply osup2_lub; auto.  

  apply Qty; auto.
  apply REC0_is_rec with (o' := o2); trivial.

  apply Qty; auto.
  apply isOrd_osup2; auto.

  red; intros.
  apply irr; auto.
  apply osup2_incl2; auto.
Qed.

(*  
Lemma REC0_rec :
  rec0 (REC F) O.
elim Oo using isOrd_ind.
intros o oo leO Hrec.  
assert (Hrec_ty : forall o'', o'' ∈ o -> REC F o'' ∈ (Π x ∈ X o'', U o'' x)).
 intros.
 apply Hrec with (z:=o''); auto with *.
 eauto using isOrd_inv.
assert (Hrec_eqn :
        forall o1 o2 n : set,
        o1 ∈ o ->
        o2 ∈ o -> n ∈ X o1 -> n ∈ X (osucc o2) ->
        cc_app (REC F o1) n == cc_app (F o2 (REC F o2)) n).
 intros.
 apply Hrec with (z:=o1⊔o2); auto.
  apply osup2_lt; auto.
  eauto using isOrd_inv.
  eauto using isOrd_inv.
  apply osup2_incl1; auto.
  eauto using isOrd_inv.
  apply osup2_incl2; auto.
  eauto using isOrd_inv.
clear Hrec.
assert (Hirr : forall x y n,
           isOrd x -> x ⊆ y -> y ∈ o -> n ∈ X x ->
           cc_app (REC F x) n == cc_app (REC F y) n).
 intros.
 transitivity (cc_app (F x (REC F x)) n);[|symmetry].
 {apply Hrec_eqn; auto.
   apply isOrd_plump with y; auto.
   apply isOrd_plump with y; auto.
   revert H2; apply Xmono; auto.
    apply ord_lt_le; auto.
    apply lt_osucc; auto. }
 {apply Hrec_eqn; auto.
   apply isOrd_plump with y; auto.
   revert H2; apply Xmono; auto.
   eauto using isOrd_inv.
   revert H2; apply Xmono; auto.
    apply ord_lt_le; auto.
    apply lt_osucc; auto. }
assert (HeqF : forall x y n,
  x ∈ o -> y ∈ o ->
  n ∈ X (osucc x) ->
  n ∈ X (osucc y) ->
  cc_app (F x (REC F x)) n == cc_app (F y (REC F y)) n).
{intros.
 assert (isOrd x) by eauto using isOrd_inv.
 assert (isOrd y) by eauto using isOrd_inv.
 transitivity (cc_app (F (x⊔y) (REC F (x⊔y))) n);[|symmetry].
 {apply (Firr hyps); auto.
   apply osup2_incl1; auto.
   apply ole_lts; auto.
    apply isOrd_osup2; auto.
     apply ord_lt_le; auto.
     apply osup2_lt; auto.
    apply Hrec_ty.
     apply osup2_lt; auto.
     red; intros.
     apply Hirr; auto.
      apply osup2_incl1; auto.
      apply osup2_lt; auto. }
 {apply (Firr hyps); auto.
   apply osup2_incl2; auto.
   apply ole_lts; auto.
    apply isOrd_osup2; auto.
     apply ord_lt_le; auto.
     apply osup2_lt; auto.
    apply Hrec_ty.
     apply osup2_lt; auto.
     red; intros.
     apply Hirr; auto.
      apply osup2_incl2; auto.
      apply osup2_lt; auto. } }
assert (Heq : forall o' o'', isOrd o' -> o' ⊆ o -> o'' ∈ o' ->
              fcompat (X (osucc o'')) (F o'' (REC F o'')) (sup o' (fun w => F w (REC F w)))).
{intros.
 apply prd_sup with (A:=fun o => X (osucc o)) (F:=fun o => F o (REC F o)); trivial.
  admit.
 {intros.    
  assert (isOrd x) by eauto using isOrd_inv.
  apply Qty; auto.
  apply Ftyp; auto.
  apply ole_lts; auto. }
 {red; red; intros.
  apply inter2_def in H4; destruct H4.
  apply HeqF; auto. } }
split; intros.
{rewrite REC_eq; auto.
 apply Qty; trivial.
 split.
 {rewrite Xcont; auto.
  apply prd_union. admit. admit.
  intros.
  apply Qty; eauto using isOrd_inv.
  apply (Ftyp hyps); auto.
   apply ole_lts; auto.
   eauto using isOrd_inv. }
 {apply Q'cont; auto.
   transitivity o; auto.
  rewrite Xcont; auto.
  apply prd_union. admit. admit.
  intros.
  apply Qty; eauto using isOrd_inv.
  apply (Ftyp hyps); auto.
   apply ole_lts; auto.
   eauto using isOrd_inv.
  intros o'' lto' x tyx.
  red in Heq.
  rewrite <- Heq with (o'' := o''); auto.
  apply cc_prod_elim with (dom:=X(osucc o''))(F:=U (osucc o'')); trivial.
  apply Ftyp; auto.
  apply ole_lts; auto.
  eauto using isOrd_inv. } }
rewrite Hirr with (y:=o1⊔o2); auto.
2:apply osup2_incl1; auto.
2:apply ord_lt_le; auto; apply osup2_lub; auto.


rewrite REC_eq; auto.
rewrite Xcont in H3; trivial.
apply sup_ax in H3.
2:admit.
destruct H3 as (o1',?,?).
*)

End RecursorDef.

(** With bottom *)

Section BotRecursorSpecification.

  (** The recursive definition *)
  Variable F : set -> set -> set.
  (** A function (indexed by ordinals) we expect to satisfy the recursive equation *)
  Variable f : set -> set.
  (** The ordinal up to which [f] satisfies the recursive equation *)
  Variable o : set.
  Hypothesis oo : isOrd o.
  
  (** The condition expressing that [f] satisfies the recursive equation [F] up to [o]. *)
  Record rec := mkrec {
    RbXm : morph1 X;
    (* Domain is continuous and does not contain the bottom value *)
    RbXcont : continuous X;
    RbXmt : forall o, isOrd o -> ~ empty ∈ X o;
    (* typing *)
    Rbtyp : forall o',
        isOrd o' -> o' ⊆ o -> f o' ∈ Π x ∈ cc_bot (X o'), U o' x;
    (* strict *)
    Rbstr : forall o',
        isOrd o' -> o' ⊆ o -> cc_app (f o') empty == empty;
    (* equation *)
    Rbeqn: forall o1 o2 n,
        isOrd o1 -> isOrd o2 -> o1 ⊆ o -> o2 ⊆ o ->
        n ∈ X o1 ->
        n ∈ X (osucc o2) ->
        cc_app (f o1) n == cc_app (F o2 (f o2)) n
                  }.

  Hypothesis isrec : rec.

  Let Xm := RbXm isrec.
  Let Xcont := RbXcont isrec.
  Let Req := Rbeqn isrec.

  Let Xmono := cont_is_mono _ Xm Xcont.
  
  Lemma rec_typ o' :
    isOrd o' ->
    o' ⊆ o ->
    f o' ∈ (Π x ∈ cc_bot (X o'), U o' x).
apply (Rbtyp isrec).
Qed.

  Lemma rec_strict o' n :
    isOrd o' ->
    o' ⊆ o ->
    n == empty ->
    cc_app (f o') n == empty.
intros.
rewrite H1.
apply (Rbstr isrec); trivial.
Qed.

  Lemma rec_eqn_succ o' x :
    o' ∈ o ->
    x ∈ X (osucc o') ->
    cc_app (f (osucc o')) x == cc_app (F o' (f o')) x.
intros.
assert (oo' : isOrd o') by eauto using isOrd_inv.
apply Req; auto.
red; intros; apply isOrd_plump with o'; auto.
 apply isOrd_inv with (osucc o'); auto.
 apply olts_le; auto.
Qed.

  Lemma rec_irr o1 o2 x :
    isOrd o1 -> isOrd o2 -> o1 ⊆ o2 -> o2 ⊆ o ->
    x ∈ cc_bot (X o1) ->
    cc_app (f o1) x == cc_app (f o2) x.
intros.
apply cc_bot_ax in H3; destruct H3.
 rewrite rec_strict with (o':=o2); auto.
 rewrite rec_strict with (o':=o1); auto with *.
 transitivity o2; auto.

 rewrite Req with (o1:=o2) (o2:=o2); auto.
  rewrite Req with (o1:=o1) (o2:=o2); auto with *.
   transitivity o2; trivial.

   revert H3; apply Xmono; auto.
   apply ord_lt_le; auto; apply ole_lts; auto.

  revert H3; apply Xmono; auto.

  revert H3; apply Xmono; auto.
  apply ord_lt_le; auto; apply ole_lts; auto.
Qed.

  Lemma rec_eqn o' x :
    isOrd o' -> o' ⊆ o ->
    x ∈ X o' ->
    cc_app (f o') x == cc_app (F o' (f o')) x.
intros.
apply Req; auto.
revert H1; apply Xmono; auto with *.
apply ord_lt_le; auto; apply lt_osucc; auto.
Qed.
  
End BotRecursorSpecification.

Section BotRecursorDef.

  (** The recursive definition *)
  Variable F : set -> set -> set.

  Variable O : set.

Record rec_hyps : Prop := rec_intro {
    RHbXm : morph1 X;
    (* Domain is continuous and does not contain the bottom value *)
    RHbXcont : continuous X;
    RHbXmt : forall o, isOrd o -> ~ empty ∈ X o;
    RHbord : isOrd O;
    RHbUm : morph2 U;
    RHbUmono : forall o o' x,
        isOrd o ->
        o ⊆ o' ->
        o' ∈ osucc O ->
        x ∈ cc_bot (X o) ->
        U o x ⊆ U o' x;
    RHbUmt : forall o x, empty ∈ U o x;
    RHbm : morph2 F;
    RHbtyp : forall o,
        o ∈ O ->
        forall f,
        f ∈ (Π x ∈ cc_bot (X o), U o x) ->
        F o f
        ∈ (Π x ∈ cc_bot (X (osucc o)), U (osucc o) x);
    RHbirr : forall o o' f g,
        isOrd o ->
        o ⊆ o' ->
        o' ∈ osucc O ->
        f ∈ (Π x ∈ cc_bot (X o), U o x) ->
        g ∈ (Π x ∈ cc_bot (X o'), U o' x) ->
        fcompat (cc_bot (X o)) f g ->
        fcompat (cc_bot (X (osucc o))) (F o f) (F o' g)
  }.

Hypothesis hyps : rec_hyps.

Let Xm := RHbXm hyps.
Let Xcont := RHbXcont hyps.
Let Xmono := cont_is_mono _ Xm Xcont.
Let Oo : isOrd O := RHbord hyps.
Let Um := RHbUm hyps.
Let Fm := RHbm hyps.
Let Xmt := RHbXmt hyps.

Let F' o' f := squash (F o' f).

Definition REC' := REC F'.

Let F'm : morph2 F'.
do 3 red; intros.
apply squash_morph; apply Fm; trivial.
Qed.

  Let ext_fun_ty : forall o,
    ext_fun (cc_bot (X o)) (U o).
do 2 red; intros.
apply Um; auto with *.
Qed.

Lemma prod_ext_mt o f :
  isOrd o ->
  f ∈ cc_prod (X o) (U o) ->
  f ∈ cc_prod (cc_bot (X o)) (U o).
intros oo fty.
apply cc_prod_ext_mt in fty; trivial.
 apply (RHbUmt hyps).

 apply RHbXmt; trivial.
Qed.

Let F'typ : forall o,
   o ∈ O ->
   forall f, f ∈ (Π x ∈ X o, U o x) -> F' o f ∈ (Π x ∈ X (osucc o), U (osucc o) x).
intros.  
assert (oo : isOrd o) by eauto using isOrd_inv.
unfold F'.
apply squash_typ; auto.
apply (RHbtyp hyps); trivial.
apply prod_ext_mt; auto.
Qed.

Let F'irr : forall o o' f g,
   isOrd o ->
   o ⊆ o' ->
   o' ∈ osucc O ->
   f ∈ (Π x ∈ X o, U o x) ->
   g ∈ (Π x ∈ X o', U o' x) ->
   fcompat (X o) f g -> fcompat (X (osucc o)) (F' o f) (F' o' g).
red; intros.
assert (oo' : isOrd o') by eauto using isOrd_inv.
unfold F'.
assert (xnmt : ~ x == empty).
 intros h; revert H5; rewrite h; apply Xmt; auto.
rewrite squash_nmt; trivial.
rewrite squash_nmt; trivial.
apply (RHbirr hyps); auto.
 apply prod_ext_mt; auto.
 apply prod_ext_mt; auto.
red; intros.
apply cc_bot_ax in H6; destruct H6; auto.
rewrite H6.
apply cc_prod_is_cc_fun in H2.
apply cc_prod_is_cc_fun in H3.
rewrite cc_app_outside_domain with (1:=H2); auto.
rewrite cc_app_outside_domain with (1:=H3); auto with *.
Qed.

Lemma REC_rec0 :
    rec0 F' (REC') O.
apply REC0_rec.
split; auto.
intros; apply (RHbUmono hyps); auto.
Qed.

Lemma REC_rec : rec F REC' O.
split;intros; auto.
 apply prod_ext_mt; auto.
 apply rec0_typ  with (1:=REC_rec0); auto.

 specialize rec0_typ with (1:=REC_rec0) (2:=H) (3:=H0).
 intros ty.
 apply cc_prod_is_cc_fun in ty.
 rewrite cc_app_outside_domain with (1:=ty); auto with *.

 rewrite (Reqn _ _ _ REC_rec0) with (o1:=o1)(o2:=o2); auto.
 unfold F'.
 specialize rec0_typ with (1:=REC_rec0) (2:=H0) (3:=H2); intros ty2.
 eapply squash_nmt.
 intros h; revert H3; rewrite h; apply Xmt; auto.
Qed.

End BotRecursorDef.

End Recursor.

Lemma REC'_morph : Proper ((eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) REC'.
do 3 red; intros.
unfold REC'.
apply REC_morph_gen; trivial.
do 2 red; intros.
apply squash_morph.
apply H; trivial.
Qed.

(** Unicity of recursor *)
Lemma rec_ext0 X X' F F' U U' g g' o :
  isOrd o ->
  (forall o', isOrd o' -> o' ⊆ o -> X o' ⊆ X' o') ->
  rec X U F g o ->
  rec X' U' F' g' o ->
  (forall z, isOrd z -> z ⊆ o ->
   forall f f',
   f ∈ (Π x ∈ cc_bot (X z), U z x) ->
   f' ∈ (Π x ∈ cc_bot (X' z), U' z x) ->
   fcompat (cc_bot (X z)) f f' ->
   fcompat (X (osucc z)) (F z f) (F' z f')) -> 
  fcompat (cc_bot (X o)) (g o) (g' o).
intros oo Xincl oko oko' eqF.
elim oo using isOrd_ind; intros.
red; intros.
apply cc_bot_ax in H2; destruct H2.
 rewrite rec_strict with (1:=oko); auto with *.
 rewrite rec_strict with (1:=oko'); auto with *.

 destruct oko as (Xm,Xcont,_,tyo,_,eqno).
 destruct oko' as (_,_,_,tyo',_,eqno').
 red in Xcont; rewrite Xcont in H2; trivial.
 apply sup_ax in H2.
 2:do 2red; intros; apply Xm; apply osucc_morph; trivial.
 destruct H2 as (o'',?,?).
 assert (o_o'' : isOrd o'') by eauto using isOrd_inv.
 assert (o''_y : osucc o'' ⊆ y).
  red; intros; apply le_lt_trans with o''; auto.
 rewrite eqno with (o2:=o''); auto with *.
 2:revert H3; apply cont_is_mono; auto with *.
 rewrite eqno' with (o2:=o''); auto with *.
  apply eqF; auto.

  apply Xincl; auto.
  revert H3; apply cont_is_mono; auto with *.

  apply Xincl; auto.
  rewrite <- H0; trivial.
Qed.

Lemma rec_ext X X' F F' U U' g g' o o' :
  isOrd o ->
  isOrd o' ->
  o ⊆ o' ->
  (forall w, isOrd w -> w ⊆ o -> X w ⊆ X' w) ->
  rec X U F g o ->
  rec X' U' F' g' o' ->
  (forall z, isOrd z -> z ⊆ o ->
   forall f f',
   f ∈ (Π x ∈ cc_bot (X z), U z x) ->
   f' ∈ (Π x ∈ cc_bot (X' z), U' z x) ->
   fcompat (cc_bot (X z)) f f' ->
   fcompat (X (osucc z)) (F z f) (F' z f')) -> 
  fcompat (cc_bot (X o)) (g o) (g' o').
intros oo oo' ole Xincl oko oko' eqF n tyn.
assert (oko'o: rec X' U' F' g' o).
destruct oko' as (?,?,?,?,?,?).
 assert (forall o1, o1 ⊆ o -> o1 ⊆ o').
  intros; transitivity o; trivial.
 split; intros; auto.
transitivity (cc_app (g' o) n).  
{apply rec_ext0 with (3:=oko) (4:=oko'o); auto. }
{apply rec_irr with (1:=oko'); auto with *.
 revert tyn; apply cc_bot_mono.
 apply Xincl; auto with *. }
Qed. 

