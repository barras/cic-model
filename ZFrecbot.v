Require Import ZFfunext ZFfixrec ZFrelations ZFcoc ZFord.

Section Recursor.

(** With bottom *)

  (** The domain, indexed by ordinals *)
  Variable X : set -> set.
  (** The co-domain *)
  Variable U : set -> set -> set.

Section BotRecursorSpecification.

  (** The recursive definition *)
  Variable F : set -> set -> set.
  (** A function (indexed by ordinals) we expect to satisfy the recursive equation *)
  Variable f : set -> set.
  (** The ordinal up to which [f] satisfies the recursive equation *)
  Variable o : set.
  Hypothesis oo : isOrd o.
  
  (** The condition expressing that [f] satisfies the recursive equation [F] up to [o]. *)
  Record typed_bot_recursor_spec := mkrec {
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

  Hypothesis isrec : typed_bot_recursor_spec.

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

Record typed_bot_recursor_hyps : Prop := rec_intro {
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

Hypothesis hyps : typed_bot_recursor_hyps.

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

Lemma REC'_typed_recursor_spec :
    typed_recursor_spec X U F' REC' O.
apply typed_recursor; trivial.
apply mkTypedRec; auto.
intros; apply (RHbUmono hyps); auto.
Qed.

Lemma REC'_typed_bot_recursor_spec : typed_bot_recursor_spec F REC' O.
assert (isrec := REC'_typed_recursor_spec).
split;intros; auto.
 apply prod_ext_mt; auto.
 apply typed_rec_typ with (1:=isrec); auto.

 specialize typed_rec_typ with (1:=isrec) (2:=Um) (3:=H) (4:=H0).
 intros ty.
 apply cc_prod_is_cc_fun in ty.
 rewrite cc_app_outside_domain with (1:=ty); auto with *.

 rewrite (Reqn _ _ _ _ _ isrec) with (o1:=o1)(o2:=o2); auto.
 unfold F'.
 specialize typed_rec_typ with (1:=isrec) (2:=Um) (3:=H0) (4:=H2); intros ty2.
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
Lemma typed_bot_rec_ext0 X X' F F' U U' g g' o :
  isOrd o ->
  (forall o', isOrd o' -> o' ⊆ o -> X o' ⊆ X' o') ->
  typed_bot_recursor_spec X U F g o ->
  typed_bot_recursor_spec X' U' F' g' o ->
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

Lemma typed_bot_rec_ext X X' F F' U U' g g' o o' :
  isOrd o ->
  isOrd o' ->
  o ⊆ o' ->
  (forall w, isOrd w -> w ⊆ o -> X w ⊆ X' w) ->
  typed_bot_recursor_spec X U F g o ->
  typed_bot_recursor_spec X' U' F' g' o' ->
  (forall z, isOrd z -> z ⊆ o ->
   forall f f',
   f ∈ (Π x ∈ cc_bot (X z), U z x) ->
   f' ∈ (Π x ∈ cc_bot (X' z), U' z x) ->
   fcompat (cc_bot (X z)) f f' ->
   fcompat (X (osucc z)) (F z f) (F' z f')) -> 
  fcompat (cc_bot (X o)) (g o) (g' o').
intros oo oo' ole Xincl oko oko' eqF n tyn.
assert (oko'o: typed_bot_recursor_spec X' U' F' g' o).
destruct oko' as (?,?,?,?,?,?).
 assert (forall o1, o1 ⊆ o -> o1 ⊆ o').
  intros; transitivity o; trivial.
 split; intros; auto.
transitivity (cc_app (g' o) n).  
{apply typed_bot_rec_ext0 with (3:=oko) (4:=oko'o); auto. }
{apply rec_irr with (1:=oko'); auto with *.
 revert tyn; apply cc_bot_mono.
 apply Xincl; auto with *. }
Qed. 

