Require Import ZFrelations ZFbot ZFfunext ZFord ZFfixrec.

Section Recursor.

(** With bottom *)

  (** A set of "bottom values" *)
  Variable bot : set.

  (** The domain, indexed by ordinals *)
  Variable X : set -> set.
  Let Xbot o := bot ∪ X o.

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
    RbXnmt : forall o' x, isOrd o' -> x ∈ bot -> x ∈ X o' -> False;
(*    RbXmt : forall o, isOrd o -> ~ empty ∈ X o;*)
    (* typing *)
    Rbtyp : forall o',
        isOrd o' -> o' ⊆ o -> f o' ∈ Π x ∈ Xbot o', U o' x;
    (* strict *)
    Rbstr : forall o' x,
        isOrd o' -> o' ⊆ o -> x ∈ bot -> cc_app (f o') x == empty;
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
  
  Lemma typed_bot_rec_typ o' :
    isOrd o' ->
    o' ⊆ o ->
    f o' ∈ (Π x ∈ Xbot o', U o' x).
apply (Rbtyp isrec).
Qed.

  Lemma typed_bot_rec_strict o' n :
    isOrd o' ->
    o' ⊆ o ->
    n ∈ bot ->
    cc_app (f o') n == empty.
intros.
apply (Rbstr isrec); trivial.
Qed.

  Lemma typed_bot_rec_eqn_succ o' x :
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

  Lemma typed_bot_rec_irr o1 o2 x :
    isOrd o1 -> isOrd o2 -> o1 ⊆ o2 -> o2 ⊆ o ->
    x ∈ Xbot o1 ->
    cc_app (f o1) x == cc_app (f o2) x.
intros.
apply union2_ax in H3; destruct H3.
 rewrite typed_bot_rec_strict with (o':=o2); auto.
 rewrite typed_bot_rec_strict with (o':=o1); auto with *.
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

  Lemma typed_bot_rec_eqn o' x :
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
    RHbXnmt : forall o' x, isOrd o' -> x ∈ bot -> x ∈ X o' -> False;
    RHbord : isOrd O;
(*    RHbUm : morph2 U;*)
    RHbUmono : forall o o' x x',
        isOrd o ->
        o ⊆ o' ->
        o' ∈ osucc O ->
        x ∈ Xbot o ->
        x == x' ->
        U o x ⊆ U o' x';
    RHbUmt : forall o x, empty ∈ U o x;
    RHbm : morph2 F;
    RHbtyp : forall o,
        o ∈ O ->
        forall f,
        f ∈ (Π x ∈ Xbot o, U o x) ->
        F o f
        ∈ (Π x ∈ Xbot (osucc o), U (osucc o) x);
    RHbirr : forall o o' f g,
        isOrd o ->
        o ⊆ o' ->
        o' ∈ osucc O ->
        f ∈ (Π x ∈ Xbot o, U o x) ->
        g ∈ (Π x ∈ Xbot o', U o' x) ->
        fcompat (Xbot o) f g ->
        fcompat (Xbot (osucc o)) (F o f) (F o' g)
  }.

Hypothesis hyps : typed_bot_recursor_hyps.

Let Xm := RHbXm hyps.
Let Xcont := RHbXcont hyps.
Let Xmono := cont_is_mono _ Xm Xcont.
Let Oo : isOrd O := RHbord hyps.
Let Fm := RHbm hyps.
Let Xnmt := RHbXnmt hyps.


Let F' o' f := squ bot (F o' f).

Definition REC' := REC F'.

Let F'm : morph2 F'.
do 3 red; intros.
apply squ_morph; auto with *.
apply Fm; trivial.
Qed.

  Let ext_fun_ty : forall o,
    isOrd o ->
    o ⊆ O ->
    ext_fun (Xbot o) (U o).
do 2 red; intros.
apply incl_eq; apply (RHbUmono hyps); auto with *.
 apply ole_lts; trivial.
 apply ole_lts; trivial.
 rewrite <- H2; trivial.
Qed.


Lemma prod_ext_mt o f :
  isOrd o ->
  o ⊆ O ->
  f ∈ cc_prod (X o) (U o) ->
  f ∈ cc_prod (Xbot o) (U o).
intros oo leO fty.
apply cc_prod_ext_bot with (bot:=bot) in fty; trivial.
 apply ext_fun_ty; auto.

 intros; apply (RHbUmt hyps).

 red; intros x.
 apply (RHbXnmt hyps); trivial.
Qed.

Let F'typ : forall o,
   o ∈ O ->
   forall f, f ∈ (Π x ∈ X o, U o x) -> F' o f ∈ (Π x ∈ X (osucc o), U (osucc o) x).
intros.  
assert (oo : isOrd o) by eauto using isOrd_inv.
unfold F'.
apply squ_typ; auto.
 apply ext_fun_ty; auto.
 red; intros; apply isOrd_plump with o; auto.
  eauto using isOrd_inv.
  apply olts_le; auto.

 intros x xb xty; apply (RHbXnmt hyps) in xty; auto.

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
assert (xnmt : ~ x ∈ bot).
 intro; apply (RHbXnmt hyps) in H5; auto.
rewrite squ_nmt; trivial.
rewrite squ_nmt; trivial.
apply (RHbirr hyps); auto.
 apply prod_ext_mt; auto.
 transitivity o'; auto.
 apply olts_le; auto.
 apply prod_ext_mt; auto.
 apply olts_le; auto.
2:apply union2_intro2; trivial.
red; intros.
apply union2_ax in H6; destruct H6; auto.
apply cc_prod_is_cc_fun in H2.
apply cc_prod_is_cc_fun in H3.
rewrite cc_app_outside_domain with (1:=H2); auto.
 rewrite cc_app_outside_domain with (1:=H3); auto with *.

 intro h; apply (RHbXnmt hyps) in h; auto.
 intro h; apply (RHbXnmt hyps) in h; auto.
Qed.

Lemma REC'_typed_recursor_spec :
    typed_recursor_spec X U F' REC' O.
apply typed_recursor; trivial.
apply mkTypedRec; auto.
intros; apply (RHbUmono hyps); auto.
apply union2_intro2; trivial.
Qed.

Lemma REC'_typed_bot_recursor_spec : typed_bot_recursor_spec F REC' O.
assert (isrec := REC'_typed_recursor_spec).
split;intros; auto.
 apply (RHbXnmt hyps) in H1; auto.

 apply prod_ext_mt; auto.
 apply typed_rec_typ with (1:=isrec); auto.
 red; red; intros; apply ext_fun_ty; auto.
 apply union2_intro2; trivial.
 
 assert (Um : ext_fun (X o') (U o')).
  red; red; intros; apply ext_fun_ty; auto.
  apply union2_intro2; auto.
 specialize typed_rec_typ with (1:=isrec) (2:=Um) (3:=H) (4:=H0).
 intros ty.
 apply cc_prod_is_cc_fun in ty.
 rewrite cc_app_outside_domain with (1:=ty); auto with *.
 intros h; apply (RHbXnmt hyps) in h; auto.
 
 rewrite (Reqn _ _ _ _ _ isrec) with (o1:=o1)(o2:=o2); auto.
 unfold F'.
 assert (Um : ext_fun (X o2) (U o2)).
  red; red; intros; apply ext_fun_ty; auto.
  apply union2_intro2; auto.
 specialize typed_rec_typ with (1:=isrec) (2:=Um) (3:=H0) (4:=H2); intros ty2.
 eapply squ_nmt.
 intros h; apply (RHbXnmt hyps) in H4; auto.
Qed.

End BotRecursorDef.

End Recursor.

Lemma REC'_morph : Proper (eq_set ==> (eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) REC'.
do 4 red; intros.
unfold REC'.
apply REC_morph_gen; trivial.
do 2 red; intros.
apply squ_morph; auto.
apply H0; trivial.
Qed.

(** Unicity of recursor *)
Lemma typed_bot_rec_ext0 bot bot' X X' F F' U U' g g' o :
  isOrd o ->
  bot ⊆ bot' ->
  (forall o', isOrd o' -> o' ⊆ o -> X o' ⊆ X' o') ->
  typed_bot_recursor_spec bot X U F g o ->
  typed_bot_recursor_spec bot' X' U' F' g' o ->
  (forall z, isOrd z -> z ⊆ o ->
   forall f f',
   f ∈ (Π x ∈ bot ∪ X z, U z x) ->
   f' ∈ (Π x ∈ bot' ∪ X' z, U' z x) ->
   fcompat (bot ∪ X z) f f' ->
   fcompat (X (osucc z)) (F z f) (F' z f')) -> 
  fcompat (bot ∪ X o) (g o) (g' o).
intros oo botincl Xincl oko oko' eqF.
elim oo using isOrd_ind; intros.
red; intros.
apply union2_ax in H2; destruct H2.
 rewrite typed_bot_rec_strict with (1:=oko); auto with *.
 rewrite typed_bot_rec_strict with (1:=oko'); auto with *.

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

Lemma typed_bot_rec_ext bot bot' X X' F F' U U' g g' o o' :
  isOrd o ->
  isOrd o' ->
  o ⊆ o' ->
  bot ⊆ bot' ->
  (forall w, isOrd w -> w ⊆ o -> X w ⊆ X' w) ->
  typed_bot_recursor_spec bot X U F g o ->
  typed_bot_recursor_spec bot' X' U' F' g' o' ->
  (forall z, isOrd z -> z ⊆ o ->
   forall f f',
   f ∈ (Π x ∈ bot ∪ X z, U z x) ->
   f' ∈ (Π x ∈ bot' ∪ X' z, U' z x) ->
   fcompat (bot ∪ X z) f f' ->
   fcompat (X (osucc z)) (F z f) (F' z f')) -> 
  fcompat (bot ∪ X o) (g o) (g' o').
intros oo oo' ole botincl Xincl oko oko' eqF n tyn.
red; intros.
assert (oko'o: typed_bot_recursor_spec bot' X' U' F' g' o).
 destruct oko' as (?,?,?,?,?,?).
 assert (forall o1, o1 ⊆ o -> o1 ⊆ o').
  intros; transitivity o; trivial.
 split; intros; auto.
 eapply RbXnmt0; eauto.
 transitivity (cc_app (g' o) n).  
{apply typed_bot_rec_ext0 with (4:=oko) (5:=oko'o); auto. }
{apply typed_bot_rec_irr with (1:=oko'); auto with *.
 revert tyn; apply union2_mono; auto.
 apply Xincl; auto with *. }
Qed. 

