Require Import Arith.
Require Import List.

Inductive foterm :=
  | Val : nat -> foterm
  | Cst_0 : foterm
  | Cst_S : foterm -> foterm
  | Df_Add : foterm -> foterm -> foterm.

Fixpoint lift_trm_rec t n k:=
  match t with
  | Val i => 
    match le_gt_dec k i with
    | left _ => Val (i+n)
    | right _ => Val i
    end
  | Cst_0 => Cst_0
  | Cst_S u => Cst_S (lift_trm_rec u n k)
  | Df_Add u v => Df_Add (lift_trm_rec u n k) (lift_trm_rec v n k)
  end.

Definition lift_trm t n := lift_trm_rec t n 0.

Inductive foformula :=
  | atom : (list foterm -> Prop) -> list foterm -> foformula
  | TF   : foformula
  | BF   : foformula
  | neg : foformula -> foformula
  | conj : foformula -> foformula -> foformula
  | disj : foformula -> foformula -> foformula
  | implf : foformula -> foformula -> foformula
  | fall : foformula -> foformula
  | exst : foformula -> foformula.

Fixpoint lift_fml_rec f n k:=
  match f with
  | atom P l => atom P (map (fun x => lift_trm_rec x n k) l)
  | TF => TF
  | BF => BF
  | neg f' => neg (lift_fml_rec f' n k)
  | conj A B => conj (lift_fml_rec A n k) (lift_fml_rec B n k)
  | disj A B => disj (lift_fml_rec A n k) (lift_fml_rec B n k)
  | implf A B => implf (lift_fml_rec A n k) (lift_fml_rec B n k)
  | fall A => fall (lift_fml_rec A n (S k))
  | exst A => exst (lift_fml_rec A n (S k))
  end.

Definition lift_fml t n := lift_fml_rec t n 0.

Fixpoint subst_trm M N n:= 
  match M with
  | Val i =>
    match lt_eq_lt_dec n i with
    | inleft (left _) => Val (pred i)
    | inleft (right _) => lift_trm N n
    | inright _ => Val i
    end
  | Cst_0 => Cst_0
  | Cst_S M' => Cst_S (subst_trm M' N n)
  | Df_Add M1 M2 => Df_Add (subst_trm M1 N n) (subst_trm M2 N n)
  end.

Fixpoint subst_fml f N n :=
  match f with
  | atom P l => atom P (map (fun M => subst_trm M N n) l)
  | TF => TF
  | BF => BF
  | neg f => neg (subst_fml f N n)
  | conj f1 f2 => conj (subst_fml f1 N n) (subst_fml f2 N n)
  | disj f1 f2 => disj (subst_fml f1 N n) (subst_fml f2 N n)
  | implf f1 f2 => implf (subst_fml f1 N n) (subst_fml f2 N n)
  | fall f => fall (subst_fml f N (S n))
  | exst f => exst (subst_fml f N (S n))
  end.

Definition subst_fml0 f N := subst_fml f N 0.

Fixpoint free_var_fotrm t : list nat:=
 match t with
 | Val n => n::nil
 | Cst_0 => nil
 | Cst_S N => free_var_fotrm N
 | Df_Add M N => (free_var_fotrm M) ++ (free_var_fotrm N)
 end.

Definition hyp_ok (hyp:list (option foformula)) t := 
 forall n, In n (free_var_fotrm t) -> nth_error hyp n = Some None.

Definition predicate_stable P := forall l n k N, 
  (P l <-> P (map (fun x => lift_trm_rec x n k) l)) /\
  (P l <-> P (map (fun M : foterm => subst_trm M N k) l)).
 
Inductive deriv : list (option foformula) -> foformula -> Prop :=
  | weak : forall f hyp, deriv ((Some f)::hyp) (lift_fml f 1)
  | atom_intro : forall (P : list foterm -> Prop) l hyp, 
      predicate_stable P -> P l -> deriv hyp (atom P l)
  | neg_intro : forall hyp f, deriv hyp (implf f BF) -> deriv hyp (neg f)
  | conj_intro : forall hyp f1 f2 , 
      deriv hyp f1 -> deriv hyp f2 -> deriv hyp (conj f1 f2)
  | disj_intro1 : forall hyp f1 f2, 
      deriv hyp f1 -> deriv hyp (disj f1 f2)
  | disj_intro2 : forall hyp f1 f2, 
      deriv hyp f2 -> deriv hyp (disj f1 f2)
  | impl_intro : forall hyp f1 f2,
      deriv ((Some f1)::hyp) (lift_fml f2 1) -> deriv hyp (implf f1 f2)
  | fall_intro : forall hyp f,
      deriv (None::hyp) f -> deriv hyp (fall f)
  | exst_intro : forall hyp f N, hyp_ok hyp N -> 
      deriv hyp (subst_fml0 f N) -> deriv hyp (exst f). 






