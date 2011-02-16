
Definition TRUE := Prod (Srt prop) (Prod (Ref 0) (Ref 1)).

Definition FALSE := Prod (Srt prop) (Ref 0).

Definition INAT :=
  Prod (Srt prop)
 (Prod (Ref 0)
 (Prod (Prod (Ref 1) (Ref 2))
  (Ref 2))).

Definition EM :=
  Prod (Srt prop) (Prod (Prod (Prod (Ref 0) FALSE) FALSE) (Ref 1)).

Definition EQ A x y :=
  Prod (Prod A (Srt prop))
    (Prod (App (Ref 0) (lift 1 x)) (App (Ref 1) (lift 2 y))).

Definition PI :=
  Prod (Srt prop) (Prod (Ref 0) (Prod (Ref 1)
     (EQ (Ref 2) (Ref 1) (Ref 0)))).


Definition EXT s1 s2 :=
  Prod (Srt s1) (Prod (Prod (Ref 0) (Srt s2))
    (Prod (Prod (Ref 1) (App (Ref 1) (Ref 0)))
    (Prod (Prod (Ref 2) (App (Ref 2) (Ref 0)))
    (Prod (Prod (Ref 3)
             (EQ (App (Ref 3) (Ref 0))
               (App (Ref 2) (Ref 0)) (App (Ref 1) (Ref 0))))
    (EQ (Prod (Ref 4) (App (Ref 4) (Ref 0))) (Ref 2) (Ref 1)))))).
