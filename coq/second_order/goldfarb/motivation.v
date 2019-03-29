Set Implicit Arguments.
Require Import List Lia std axioms.
Import ListNotations.

(** ** Multiplication Motivation  *)
Section Motivation.

  Variable (a b m n p: nat).

  Definition succ '(a, b) := (n + a, 1 + b).
  Definition ith i := (i * n + a, i + b).


  Section Streams.

    Implicit Type (X Y: nat -> (nat * nat)).

    Definition charac {A: Type} (X: nat -> A) (a: A) (Y: nat -> A) :=
      X 0 = a /\ forall n, X (S n) = Y n.

    Notation "X ≈ Y ⟶ Z" := (charac X Y Z) (at level 60).


    Definition Succ X  := X >> succ.

    Let X := ith. 

    Lemma X_satisfies:
      X ≈ (a, b) ⟶ Succ X.
    Proof.
      split; unfold X, ith; cbn; intros; f_equal; lia. 
    Qed.

    Lemma X_unique Y:
      (Y ≈ (a, b) ⟶ Succ Y) -> forall i, Y i = X i.
    Proof.
      intros H; induction i.
      - destruct H as [H _]. rewrite H. unfold X, ith. now simplify.
      - destruct H as [_ H]. unfold Succ, funcomp in *.
        rewrite H, IHi. unfold X, ith; cbn; f_equal; lia.
    Qed.

  End Streams.


  Section FiniteSequences.
    Implicit Type (X Y: list (nat * nat)).
    
    Notation succ' X := (map succ X).
    
    Lemma forward: p = m * n -> exists X, (a,b) :: succ' X = X ++ [(p + a, m + b)].
    Proof.
      intros ->. exists (tab ith m). 
      rewrite tab_map. change (tab _ _ ++ _) with (tab ith (S m)).
      rewrite tab_S. unfold ith, succ. cbn. rewrite !tab_map_nats.
      f_equal. eapply map_ext. intros i. f_equal; lia.
    Qed.


    Lemma backward' X x:
      (a, b) :: succ' X = X ++ [x] -> x = ith (length X).
    Proof.
      unfold ith. induction X as [|[l r] X IH] in a, b, x |-*; eauto.
      - cbn; simplify. intuition congruence. 
      - simplify. intros [= -> -> H]. eapply IH in H; subst.
        cbn; simplify; f_equal; lia.
    Qed.


  
    Lemma backward X:
      (a,b) :: succ' X = X ++ [(p + a, m + b)] -> m * n = p.
    Proof.
      intros H % backward'. injection H.
      intros; assert (m = |X|) as -> by lia. lia. 
    Qed.
  End FiniteSequences.

  
End Motivation.

