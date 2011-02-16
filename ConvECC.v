
Require Export TermECC.

Section Church_Rosser.

  Definition str_confluent R := commut _ R (transp term R).

  Lemma str_confluence_par_red1 : str_confluent par_red1.
red in |- *; red in |- *.
simple induction 1; intros.
inversion_clear H4.
elim H1 with M'0; auto with coc; intros.
elim H3 with N'0; auto with coc; intros.
exists (subst x1 x0); unfold subst in |- *; auto with coc.

inversion_clear H5.
elim H1 with M'1; auto with coc; intros.
elim H3 with N'0; auto with coc; intros.
exists (subst x1 x0); auto with coc; unfold subst in |- *; auto with coc.

inversion_clear H0.
exists (Srt s); auto with coc.

inversion_clear H0.
exists (Ref n); auto with coc.

inversion_clear H4.
elim H1 with M'0; auto with coc; intros.
elim H3 with T'0; auto with coc; intros.
exists (Abs x1 x0); auto with coc.

generalize H0 H1.
clear H0 H1.
inversion_clear H4.
intro.
inversion_clear H4.
intros.
elim H4 with (Abs T M'0); auto with coc; intros.
elim H3 with N'0; auto with coc; intros.
apply inv_par_red_abs with T' M'1 x0; intros; auto with coc.
generalize H7 H8.
rewrite H11.
clear H7 H8; intros.
inversion_clear H7.
inversion_clear H8.
exists (subst x1 U'); auto with coc.
unfold subst in |- *; auto with coc.

intros.
elim H5 with M'0; auto with coc; intros.
elim H3 with N'0; auto with coc; intros.
exists (App x0 x1); auto with coc.

intros.
inversion_clear H4.
elim H1 with M'0; auto with coc; intros.
elim H3 with N'0; auto with coc; intros.
exists (Prod x0 x1); auto with coc.
Qed.


  Lemma strip_lemma : commut _ par_red (transp _ par_red1).
unfold commut, par_red in |- *; simple induction 1; intros.
elim str_confluence_par_red1 with z x0 y0; auto with coc; intros.
exists x1; auto with coc.

elim H1 with z0; auto with coc; intros.
elim H3 with x1; intros; auto with coc.
exists x2; auto with coc.
apply t_trans with x1; auto with coc.
Qed.


  Lemma confluence_par_red : str_confluent par_red.
red in |- *; red in |- *.
simple induction 1; intros.
elim strip_lemma with z x0 y0; intros; auto with coc.
exists x1; auto with coc.

elim H1 with z0; intros; auto with coc.
elim H3 with x1; intros; auto with coc.
exists x2; auto with coc.
red in |- *.
apply t_trans with x1; auto with coc.
Qed.


  Lemma confluence_red : str_confluent red.
red in |- *; red in |- *.
intros.
elim confluence_par_red with x y z; auto with coc; intros.
exists x0; auto with coc.
Qed.


  Theorem church_rosser :
   forall u v, conv u v -> exists2 t : _, red u t & red v t.
simple induction 1; intros.
exists u; auto with coc.

elim H1; intros.
elim confluence_red with x P N; auto with coc; intros.
exists x0; auto with coc.
apply trans_red_red with x; auto with coc.

elim H1; intros.
exists x; auto with coc.
apply trans_red_red with P; auto with coc.
Qed.



  Lemma inv_conv_prod_l :
   forall a b c d, conv (Prod a c) (Prod b d) -> conv a b.
intros.
elim church_rosser with (Prod a c) (Prod b d); intros; auto with coc.
apply red_prod_prod with a c x; intros; auto with coc.
apply red_prod_prod with b d x; intros; auto with coc.
apply trans_conv_conv with a0; auto with coc.
apply sym_conv.
generalize H2.
rewrite H5; intro.
injection H8.
simple induction 2; auto with coc.
Qed.

  Lemma inv_conv_prod_r :
   forall a b c d, conv (Prod a c) (Prod b d) -> conv c d.
intros.
elim church_rosser with (Prod a c) (Prod b d); intros; auto with coc.
apply red_prod_prod with a c x; intros; auto with coc.
apply red_prod_prod with b d x; intros; auto with coc.
apply trans_conv_conv with b0; auto with coc.
apply sym_conv.
generalize H2.
rewrite H5; intro.
injection H8.
simple induction 1; auto with coc.
Qed.


  Lemma nf_uniqueness : forall u v, conv u v -> normal u -> normal v -> u = v. 
intros.
elim church_rosser with u v; intros; auto with coc.
rewrite (red_normal u x); auto with coc.
elim red_normal with v x; auto with coc.
Qed.


  Lemma conv_sort : forall s1 s2, conv (Srt s1) (Srt s2) -> s1 = s2.
intros.
cut (Srt s1 = Srt s2); intros.
injection H0; auto with coc.

apply nf_uniqueness; auto with coc.
red in |- *; red in |- *; intros.
inversion_clear H0.

red in |- *; red in |- *; intros.
inversion_clear H0.
Qed.


  Lemma conv_kind_prop : forall n, ~ conv (Srt (kind n)) (Srt prop).
red in |- *; intros.
absurd (kind n = prop).
discriminate.

apply conv_sort; auto with coc.
Qed.


  Lemma conv_sort_prod : forall s t u, ~ conv (Srt s) (Prod t u).
red in |- *; intros.
elim church_rosser with (Srt s) (Prod t u); auto with coc.
do 2 intro.
elim red_normal with (Srt s) x; auto with coc.
intro.
apply red_prod_prod with t u (Srt s); auto with coc; intros.
discriminate H2.

red in |- *; red in |- *; intros.
inversion_clear H1.
Qed.


End Church_Rosser.
