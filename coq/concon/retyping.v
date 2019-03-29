Set Implicit Arguments.
Require Import Morphisms Omega List std calculus unification 
    conservativity.
Import ListNotations.


(** ** Retyping *)
Section Retyping.

  Variable (X: Const).
  Arguments s₀ {_} {_} _.
  Arguments t₀ {_} {_} _.
  Arguments Gamma₀ {_} {_} _.
  Arguments A₀ {_} {_} _.

  Definition retype_ctx (n: nat) (Gamma : ctx) :=
    map (fun A => if dec2 le (ord A) n then A else alpha) Gamma.

  Lemma retype_ctx_ord n Gamma: 1 <= n -> ord' (retype_ctx n Gamma) <= n.
  Proof.
    intros H; induction Gamma; cbn; eauto; unfold retype_ctx in *.
    rewrite IHGamma; destruct dec2; eauto.
  Qed.
  
  Fixpoint retype_type (n: nat) (A : type) :=
    match A with
    | typevar beta => typevar beta
    | A → B => (if dec2 le (ord A) n then A else alpha) → retype_type n B
    end.


  Lemma retype_type_ord n A: 1 <= n -> ord (retype_type n A) <= S n.
  Proof.
    intros H; induction A; cbn [retype_type].
    - cbn; omega.
    - destruct dec2; simplify; intuition. 
  Qed.

  Lemma retype_type_id n A: ord A <= S n -> retype_type n A = A.
  Proof.
    induction A; cbn [retype_type]; simplify; intuition.
    destruct dec2; [congruence | omega].
  Qed.


  Lemma retype_Arr n L A:
    retype_type n (Arr L A) = Arr (retype_ctx n L) (retype_type n A).
  Proof.
    induction L; cbn; eauto; now rewrite IHL.
  Qed.

  Lemma normal_retyping n Gamma (s: exp X) A:
    normal s -> Gamma ⊢(n) s : A -> retype_ctx n Gamma ⊢(n) s : retype_type n A.
  Proof.
    intros H % normal_nf; induction H in Gamma, A |-*; subst.
    intros (L & B & ? & -> & ?) % Lambda_ordertyping_inv.
    rewrite retype_Arr. eapply Lambda_ordertyping; [unfold retype_ctx; now simplify|].
    unfold retype_ctx; rewrite <-map_rev, <-map_app; fold (retype_ctx n (rev L ++ Gamma)).
    eapply AppR_ordertyping_inv in H0 as (L' & ? &  ?).
    assert (ord' L' <= n).
    - destruct s; destruct i; inv H2; simplify in H4; intuition.
      rewrite H4 in H5; simplify in H5; intuition.
    - eapply AppR_ordertyping with (L0 := retype_ctx n L').
      + clear H2.
        induction H0; eauto.
        econstructor. all: cbn in H3; simplify in H3; intuition.
        destruct dec2; intuition.
        erewrite <-retype_type_id; [| transitivity n; eauto].
        eapply H; cbn; intuition.
      + unfold retype_ctx at 2;
          rewrite <-map_rev; fold (retype_ctx n (rev L')).
        rewrite <-retype_Arr. destruct s; destruct i.
        all: inv H2; rewrite retype_type_id; eauto.
        econstructor; eauto.
        unfold retype_ctx; erewrite map_nth_error; eauto.
        destruct dec2; intuition.
  Qed.


  Program Instance retype n (I: orduni n X) : orduni n X :=
    { Gamma₀ := retype_ctx n (Gamma₀ I);
      s₀ := eta₀ (s₀ I) H1₀;
      t₀ := eta₀ (t₀ I) H2₀;
      A₀ := retype_type n (A₀ I) }.
  Next Obligation.
    eapply normal_retyping. all: eauto using eta₀_normal, eta₀_typing.
  Qed.
  Next Obligation.
    eapply normal_retyping. all: eauto using eta₀_normal, eta₀_typing.
  Qed.



  Lemma retype_iff n (I: orduni n X):
    1 <= n -> OU n X I <-> OU n X (retype n I).
  Proof.
    intros Leq. rewrite orduni_normalise_correct. 
    destruct I as [Gamma s t A ? ?]; unfold orduni_normalise, retype, OU; cbn.
    split; intros (Delta & sigma & ? & ?); eapply ordertyping_weak_ordertyping; eauto.
    all: intros ??; simplify; intros ? [H'|H']; eapply H.
    all: rewrite nth_error_map_option in *.
    all: destruct (nth Gamma x) eqn: N; try discriminate; cbn in *.
    all: destruct dec2 as [|L]; eauto.
    all: exfalso; eapply L.
    all: eauto using vars_ordertyping_nth, eta₀_typing. 
  Qed.

End Retyping.
