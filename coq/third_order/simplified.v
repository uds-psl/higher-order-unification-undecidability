Set Implicit Arguments.
Require Import RelationClasses Morphisms List
        Omega Init.Nat Setoid std calculus unification.
Require Import third_order.pcp third_order.encoding.
Import ListNotations.

Definition MPCP' '(c, C) :=
  exists I, I ⊆ nats (length C) /\
       hd c ++ @concat symbol (select I (heads C)) = tl c ++ concat (select I (tails C)).

Lemma MPCP_MPCP' c C: MPCP (c, C) <-> MPCP' (c, c::C).
Proof. firstorder. Qed.

(** * Simplified Reduction *)
Section MPCP_U3.

  Variable (X: Const).

  Definition redtm (w: word) (W: list word): exp X :=
    lambda lambda (enc 0 1 w) (AppR (var 2) (Enc 0 1 W)).
  Definition redctx (n: nat)  := [Arr (repeat (alpha → alpha) n) alpha].

  Lemma redtm_typing w W:
    redctx (length W) ⊢(3) redtm w W : (alpha → alpha) → (alpha → alpha) →  alpha.
  Proof.
    unfold redctx; do 3 econstructor.
    - eapply enc_typing; eauto.
    - eapply AppR_ordertyping;[ eapply Enc_typing|]; simplify;
        econstructor; cbn; simplify; eauto.
  Qed.

  (** ** Reduction Function *)
  Program Instance MPCP'_to_U P : orduni 3 X :=
    { 
      Gamma₀ :=  redctx (length (snd P));
      s₀ :=  redtm (hd (fst P)) (heads (snd P));
      t₀ :=  redtm (tl (fst P)) (tails (snd P));
      A₀ := (alpha → alpha) → (alpha → alpha) →  alpha;
      H1₀ := redtm_typing (hd (fst P)) (heads (snd P));
      H2₀ := redtm_typing (tl (fst P)) (tails (snd P));
    }.
  Next Obligation. now simplify. Qed.
  Next Obligation. now simplify. Qed.


    (** ** Forward Direction *)
    Lemma MPCP'_U3 P: MPCP' P -> OU 3 X (MPCP'_to_U P).
    Proof.
      destruct P as [c C]; intros (I & Sub & EQ).
      exists [alpha]. exists (finst I (length C) .: var); split.
        - intros x A. destruct x as [| [|]]; try discriminate; cbn.
          injection 1 as ?; subst. 
          eapply finst_typing; eauto.
        - cbn -[enc]. rewrite !enc_subst_id; eauto. 
          rewrite !AppR_subst; rewrite ?Enc_subst_id; eauto; cbn.
          all: cbn; rewrite !ren_plus_base, !ren_plus_combine;
            change (1 + 1) with 2.
          replace (|C|) with (|map hd C|) at 1 by now simplify.
          replace (|C|) with (|map tl C|) at 1 by now simplify.
          rewrite !finst_equivalence, <-!enc_app, EQ.
          all: now simplify. 
    Qed.


    (** ** Backward Direction *)
    Lemma U3_MPCP' P:
      NOU 3 (MPCP'_to_U P) -> MPCP' P.
    Proof. destruct P as [c C].
      intros (Delta & sigma & T1 & EQ & N); cbn -[enc] in EQ.
      rewrite !enc_subst_id in EQ; eauto. 
      rewrite !AppR_subst in EQ; rewrite !Enc_subst_id in EQ; eauto; cbn in EQ; unfold funcomp in EQ.
      repeat eapply equiv_lam_elim in EQ.
      rewrite !ren_plus_base, !ren_plus_combine in *; change (1 + 1) with 2 in *.
      specialize (T1 0 (Arr (repeat (alpha → alpha) (length C)) alpha)); mp T1; eauto.
      specialize (N 0) as N1. eapply normal_nf in N1 as N2. destruct N2 as [k a ? T _ isA ->].
      eapply Lambda_ordertyping_inv in T1 as (L & B & H0 & H1 & <-).
      eapply id in H0 as T2.
      assert (|L | <= |C|) as L1 by
            (eapply (f_equal arity) in H1; simplify in H1; rewrite H1; eauto).
      symmetry in H1; eapply Arr_inversion in H1 as (L2 & H1 & H2); simplify; try omega.
      edestruct (@list_decompose_alt  (|L|) _ C) as (C1 & C2 & H4 & H5); try omega; subst C.
      eapply repeated_app_inv in H1 as (H1 & H3 & H4); eauto.
      rewrite H4 in H2; subst B. rewrite H3 in *; simplify in *. assert (|L2| = |C1|) by omega.
      clear H1 H3 H4 L1. revert H0 H H5 EQ T2 N1.
      generalize (length L); generalize (length L2); clear L L2. intros l k H0 H H5 EQ T2 N2. subst.
      rewrite !Lambda_ren in EQ; simplify in EQ. rewrite !AppR_app in EQ. 
      rewrite !AppR_Lambda' in EQ; simplify; eauto.
      rewrite !it_up_var_sapp in EQ; simplify; intros; unfold shift; try omega.
      destruct C1.
      - destruct (@AppL_largest _ (fun s => match s with var x => x < |C2| | _ => False end) (AppR a T))
        as (S & t & H1 & H2 & H3). intros []; intuition; now right.
        assert (exists I, I ⊆ nats (|C2|) /\ S = map var I) as [I []]. {
          clear H2. induction S. exists nil; cbn; intuition.
          edestruct IHS as [I]; [firstorder|]. intuition; subst.
          specialize (H1 a0); mp H1; [firstorder|].
          destruct a0 as [i| | |]; intuition. exists (i :: I); cbn.
          eapply lt_nats in H1. intuition. }
        clear H1. rewrite H2 in *. subst S. cbn -[add] in EQ.
        rewrite !AppL_subst in EQ.
        rewrite !select_variables_subst in EQ. 
        all: unfold dom; simplify; eauto using nats_lt. 
        cbn in T2; eapply AppL_ordertyping_inv in T2 as (L' & B & H8 & H9).
        assert (normal t) by now eapply normal_AppL_right, normal_Lambda, N2.
        rewrite <-!select_map, !enc_concat, <-!enc_app, !select_map in EQ.  
        eapply enc_eq in EQ; eauto. exists I; intuition.
        1 - 4: intros ? EQ3;
            eapply end_is_var_typed in EQ3 as (? & ? & ? & ?); cbn; simplify.
        (* close False goals *)
        1, 6, 11, 16: eapply H3; cbn; eauto; cbn; now simplify in *.
        (* close normal term goals *)
        2, 6, 10, 14: eauto.
        (* close Enc goals *)
        2, 5, 8, 11: reflexivity.
        (* close typing goals *)
        2, 4, 6, 8: eauto.
        (* close var goals *)
        1 - 4: intros; cbn; unfold funcomp; intuition discriminate.
      - rewrite AppR_subst in EQ.
        destruct a as [y| d | |]; cbn in isA; intuition; [destruct (le_lt_dec (length C2) y)|].
        + asimpl in EQ. rewrite !sapp_ge_in in EQ; simplify; eauto.
          eapply enc_eq in EQ; eauto.
           2 - 5: cbn; intros ? EQ' % equiv_head_equal; cbn; simplify; cbn; auto 1.
           2 - 5: revert EQ'; cbn; simplify; cbn; discriminate.
            exists nil; intuition; cbn; now simplify.
        + eapply AppR_ordertyping_inv in T2 as [? [_ T2]]; intuition. inv T2.
          eapply id in H2 as HH; rewrite nth_error_app1, nth_error_repeated in HH; simplify; eauto.
          injection HH as HH. eapply (f_equal ord) in HH. simplify in HH.
          symmetry in HH; eapply Nat.eq_le_incl in HH; simplify in HH.
          intuition. cbn in H6. omega. 
        + asimpl in EQ. eapply enc_eq in EQ; eauto.
          2 - 5: cbn; intros ? EQ' % equiv_head_equal; cbn; simplify; cbn; auto 1.
          2 - 5: revert EQ'; cbn; simplify; discriminate.
          exists nil; intuition; cbn; now simplify.
    Qed.


End MPCP_U3.


Lemma MPCP_U3 X: MPCP ⪯ OU 3 X.
Proof.
  exists (fun '(c, C) => MPCP'_to_U X (c, c::C)). intros [c C]; rewrite MPCP_MPCP'; split.
  2: rewrite OU_NOU; eauto.
  all: eauto using MPCP'_U3, U3_MPCP'.
Qed.  
