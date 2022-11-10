(*zad 1.a*)

Goal forall X Y : Prop, 
    ~(X /\ Y) \/ (~X /\ Y) \/ (~X /\ ~Y) <-> ~(X /\ Y).
Proof.
  intros X Y. split. 
  - intros [H | [x | y]]. 
    -- exact H.
    -- intro. apply x, H. 
    -- intro. apply y, H.
  - intro. left. exact H.
Qed.

(* zad 1.b*)
Goal forall X Y Z : Prop, 
    ~(~X/\Y/\~Z) /\ ~(X/\Y/\Z) /\ (X/\~Y/\~Z) <-> X/\~(Y\/Z).
Proof.
  intros X Y Z. split.
  - intros [H1 [H2 [x [ny nz]]]]. split.
    -- exact x.
    -- intros [y | z].
      --- apply ny. exact y.
      --- apply nz. exact z.
  - intros [x H]. split.
    -- intros [nx [y nz]]. apply nx. exact x.
    -- split.
      --- intros [_ [y z]]. apply H. left. exact y.
      --- split. exact x. split. 
        ---- intro y. apply H. left. exact y.
        ----intro z. apply H. right. exact z.
Qed.