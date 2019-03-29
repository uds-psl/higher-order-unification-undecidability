Set Implicit Arguments.
Require Import RelationClasses Morphisms Wf List Omega Lia Init.Nat Setoid calculus unification.
Require Export second_order.diophantine_equations goldfarb.encoding.
Import ListNotations.




(** ** Equivalences *)
Section EquationEquivalences.

  Variable (sigma: fin -> exp abg).
  Hypothesis (N: forall x, normal (sigma x)).


  Section Variables.
    Lemma forward_vars x n: encodes (sigma (F x)) n -> sigma • fst (varEQ x) ≡ sigma • snd (varEQ x).
    Proof.
      cbn; asimpl. intros H. rewrite !H. now simplify.
    Qed.

    Lemma backward_vars x: sigma • fst (varEQ x) ≡ sigma • snd (varEQ x) -> exists n, encodes (sigma (F x)) n.
    Proof.
      cbn; asimpl; simplify; intros H; eapply normal_forms_encodes in H; eauto.
    Qed.

  End Variables.

  Section Constants.
      Variable (n: nat) (x: nat) (c: nat).
      Hypothesis (Ex: encodes (sigma (F x)) n).

      Lemma forward_consts: n = c -> sigma • fst (constEQ x c) ≡ sigma • snd (constEQ x c).
      Proof.
        intros <-. cbn. asimpl. eapply Ex.
      Qed.

      Lemma backward_consts:  sigma • fst (constEQ x c) ≡ sigma • snd (constEQ x c) -> n = c.
      Proof.
        cbn. asimpl. rewrite Ex. eapply enc_injective; eauto.
      Qed.

  End Constants.


  Section Addition.
    Variable (m n p: nat) (x y z: nat).
    Hypothesis (Ex: encodes (sigma (F x)) m) (Ey: encodes (sigma (F y)) n) (Ez: encodes (sigma (F z)) p).


    Lemma forward_add: m + n = p -> sigma • fst (addEQ x y z) ≡ sigma • snd (addEQ x y z).
    Proof.
      intros <-; cbn; erewrite Ex, Ey, Ez; now simplify.
    Qed.

    Lemma backward_add:
      sigma • fst (addEQ x y z) ≡ sigma • snd (addEQ x y z) -> m + n = p.
    Proof.
      cbn; rewrite Ex, Ey, Ez; simplify; eapply enc_injective; eauto.
    Qed.

  End Addition.


  (** *** Multiplication *)
  Section Multiplication.

    Variable (m n p: nat).
    Notation w3 := (var 0).
    Notation w2 := (var 1).
    Notation w1 := (var 2).

    Let σ1  := (g (g (enc p a) (enc m b)) a .: b .: a .: var).
    Let σ2 := (g (g (enc p b) (enc m a)) a .: a .: b .: var).
    Let τ1  := (a .: g a b .: enc n a .: var).
    Let τ2 := (a .: g a a .: enc n b .: var).

    

    Definition T (k: nat) := g (enc (k * n) w1) (enc k w2).

    Lemma T_step_tau1_sigma1 k:
      τ1 • T k = σ1 • T (1 + k).
    Proof.
      unfold τ1, τ2, σ1, σ2, T. asimpl; cbn [subst_exp add mult]; asimpl. simplify.
      cbn; replace (k * n + n) with (n + k * n) by omega.
      change (g a b) with (enc 1 b); now simplify.
    Qed.

    Lemma T_step_tau2_sigma2 k:
      τ2 • T k = σ2 • T (1 + k).
    Proof.
      unfold τ1, τ2, σ1, σ2, T. asimpl; cbn [subst_exp add mult]; asimpl. simplify.
      cbn; replace (k * n + n) with (n + k * n) by omega.
      change (g a a) with (enc 1 a); now simplify.
    Qed.

    Lemma subst_var σ σ' (s: exp abg):
      σ • s = a -> σ' • s = b -> exists x, s = var x.
    Proof.
      intros.
      destruct s as [? | | | s1 s2]; cbn in *; try congruence.
      eauto. 
    Qed.

    Lemma subst_var_a s':
      σ1 • s' = a -> σ2 • s' = b -> s' = w1.
    Proof.
      intros H4 H5; eapply subst_var in H4 as []; eauto.
      subst; cbn in *.
      destruct x as [| [| []]]; cbn in *; try discriminate; eauto.
    Qed.

    Lemma subst_var_b s':
      σ1 • s' = b -> σ2 • s' = a -> s' = w2.
    Proof.
      intros H4 H5; eapply subst_var in H4 as []; eauto.
      subst; cbn in *.
      destruct x as [| [| []]]; cbn in *; try discriminate; eauto.
    Qed.




    Lemma subst_enc_step k e u1 u2:
    σ1 • e = enc k u1 ->
    σ2 • e = enc k u2 ->
    exists e', e = enc k e' /\ σ1 • e' = u1 /\ σ2 • e' = u2.
    Proof.
      induction k in e |-*; cbn.
      - intros; eexists; intuition; eauto.
      - intros. simplify in *. 
        destruct e as [ [| [| []]] | | | e1 e3 ]; try discriminate.
        destruct e1 as [ [| [| []]] | | | e1 e2 ]; try discriminate.
        destruct e1 as [ [| [| []]] | [] | | ]; try discriminate.
        destruct e2 as [ [| [| []]] | [[]|] | | ]; try discriminate.
        simplify in H H0. 
        injection H as H; injection H0 as H0.
        destruct (IHk _ H H0) as [e']; intuition; subst.
        exists e'. simplify. intuition.  
    Qed.



    Lemma subst_T e k:
      σ1 • e = σ1 • T k ->
      σ2 • e = σ2 • T k ->
      e = T k.
    Proof.
      unfold T; intros.
      destruct e as [ [| [| []]] | | | e1 e3 ] ; try discriminate.
      { cbn in *. asimpl in H. asimpl in H0.  cbn in *.
        injection H0 as ?. destruct k; discriminate. }
      destruct e1 as [ [| [| []]] | | | e1 e2 ]; try discriminate.
      destruct e1 as [ [| [| []]] | [] | | ]; try discriminate.
      cbn in *.  f_equal; [f_equal |]; injection H0 as H0 H4; injection H as ?.
      - asimpl in H. asimpl in H0. clear H1 H4.
        eapply subst_enc_step in H as []; eauto. intuition.
        eapply subst_var_a in H; eauto. now subst. 
      - asimpl in H1. asimpl in H4. clear H H0.
        eapply subst_enc_step in H1 as []; eauto. intuition.
        eapply subst_var_b in H; eauto. now subst.
    Qed.

    Lemma step_u u k:
      σ1 • u = g (σ1 • T k) (τ1 • u) ->
      σ2 • u = g (σ2 • T k) (τ2 • u) ->
      u = w3 \/ (exists u', u = g (T k) u').
    Proof.
      intros EQ1 EQ2.
      destruct u as [| | | t1 t3]; try discriminate; eauto.
      - cbn in *. asimpl in EQ1. asimpl in EQ2. cbn in *.
        destruct f as [|[|[]]]; try discriminate. now left.
      - destruct t1 as [[|[|[]]]| | | t1 t2]; cbn in *; try discriminate; eauto.
        destruct t1 as [[|[|[]]]| [] | |]; cbn in *; try discriminate; eauto.
        injection EQ1. injection EQ2. clear EQ1 EQ2. intros.
        eapply subst_T in H0; subst; eauto.
    Qed.


    Fixpoint size_exp {X} (s: exp X) :=
      match s with
      | var _ => 0
      | const c => 0
      | app s t => S (size_exp s + size_exp t)
      | lambda s => S (size_exp s)
      end.

   

    Lemma steps_u u k:
      σ1 • u = g (σ1 • T k) (τ1 • u) ->
      σ2 • u = g (σ2 • T k) (τ2 • u) ->
      exists l, u = lin (tab (fun i => T (i + k)) l) w3.
    Proof.
      specialize (well_founded_ind (measure_wf lt_wf (@size_exp abg))) as ind.
      revert k. induction u as [u IH] using ind; intros k EQ1 EQ2. destruct (step_u _ EQ1 EQ2) as [H1|H1].
      - subst. exists 0. reflexivity.
      - destruct H1 as [u' H1]. subst.
        specialize (IH u'). mp IH; unfold MR; cbn. lia.
        cbn -[T] in EQ1, EQ2. injection EQ1; injection EQ2. clear EQ1 EQ2.
        change (g _ _) at 2 with (τ2 • (T k)). change (g _ _) at 3 with (τ1 • (T k)). 
        rewrite T_step_tau1_sigma1. rewrite T_step_tau2_sigma2.
        intros H1 H2. eapply IH in H1; eauto.
        destruct H1 as [l]. exists (S l). rewrite tab_S, H.
        simplify. f_equal. f_equal. rewrite !tab_map_nats. eapply map_ext.
        intros. f_equal; lia.
    Qed.


    Corollary steps_u_mult u:
      σ1 • u = g (σ1 • T 0) (τ1 • u) ->
      σ2 • u = g (σ2 • T 0) (τ2 • u) ->
      m * n = p.
    Proof.
      intros EQ1 EQ2. eapply steps_u with (k := 0) in EQ1 as H; eauto.
      destruct H as [l H]. replace (tab _ l) with (tab T l) in H.
      2: rewrite !tab_map_nats; eapply map_ext; intros ?; f_equal; lia.
      subst. asimpl in EQ1. cbn in EQ1. asimpl in EQ1. cbn in EQ1.
      simplify in EQ1. 
      change (g _ a) with (lin [g (enc p a) (enc m b)] a) in EQ1.
      change (g _ (lin _ _)) with (lin ((σ1 • T 0) :: (τ1 •₊ tab T l)) a) in EQ1.
      rewrite <-lin_app in EQ1. eapply lin_injective in EQ1 as [EQ1 _]; simplify; cbn; simplify; eauto.
      destruct l. 
      - (* p = m = 0 *)
        cbn in EQ1. injection EQ1 as EQ3 EQ4.
        eapply eq_equiv, enc_injective with (m := 0) in EQ3 as [EQ3 _]; eauto.
        eapply eq_equiv, enc_injective with (m := 0) in EQ4 as [EQ4 _]; eauto.
        subst; lia.
      - cbn in EQ1. simplify in EQ1. 
        rewrite app_comm_cons in EQ1. 
        eapply app_injective in EQ1 as [_ H]; cbn; simplify; cbn; simplify; eauto.
        injection H; asimpl; cbn. change (g a b) with (enc 1 b).
        rewrite !enc_app. intros EQ3 EQ4.
        eapply eq_equiv, enc_injective with (m := l + 1) in EQ3 as [EQ3 _]; eauto.
        eapply eq_equiv, enc_injective with (m := l * n + n) in EQ4 as [EQ4 _]; eauto.
        subst. lia. 
    Qed.

    Variables (x y z: nat).
    Hypothesis
      (Ex: encodes (sigma (F x)) m) (Ey: encodes (sigma (F y)) n) (Ez: encodes (sigma (F z)) p).
    
    Section MultiplicationBackward.
      
     
      Hypothesis (EQ1: sigma • fst (mulEQ₁ x y z) ≡ sigma • snd (mulEQ₁ x y z)).
      Hypothesis (EQ2: sigma • fst (mulEQ₂ x y z) ≡ sigma • snd (mulEQ₂ x y z)).



      Lemma multiplication_lambdas:
        sigma (G x y z) = lambda lambda g (g (var 1) (var 0)) \/ (exists u', sigma (G x y z) = lambda lambda lambda u').
      Proof.
        cbn in EQ1. cbn in EQ2. remember (sigma (G x y z)) as u.
        assert (normal u) as N' by (subst; eauto). rewrite !Ex, !Ey, !Ez in EQ1.
        asimpl in EQ1. asimpl in EQ2. rewrite !Ex, !Ey, !Ez in EQ2. clear Ex Ey Ez Hequ.
        destruct u as [| | u' | ].
        4: eapply head_atom in N'; eauto.
        1, 2, 4: Injection EQ1; Injection H; Discriminate.
        rewrite stepBeta in EQ1, EQ2; eauto.  asimpl in EQ1. asimpl in EQ2.
        destruct u' as  [[]| | u' | ]; cbn in EQ1, EQ2.
        1 - 3: Injection EQ1; Injection H; Discriminate.
        - rewrite stepBeta in EQ1, EQ2; eauto.
          asimpl in EQ1. asimpl in EQ2. 
          destruct u' as [[|[]] | | u' | u1 u2 ]; cbn in EQ1, EQ2.
          1 - 4: Injection EQ1; Discriminate.
          + right; eexists; eauto. 
          + left. repeat eapply normal_lam_elim in N'.
            eapply head_atom in N' as H'; eauto.
            eapply atom_lifting with (sigma := b .: a .: var) in H' as H4.
            eapply atom_lifting with (sigma := a .: b .: var) in H' as H5.
            2 - 3: intros [|[]]; cbn; eauto.
            rewrite head_subst in H4, H5.
            2 - 3: intros [|[]]; cbn; eauto.
            cbn in H4, H5; eauto.
            Injection EQ1. Injection EQ2.
            Injection H. Injection H1.
            eapply normal_subst with (sigma0 := a .: b .: var) in N' as N1.
            2: intros [|[]]; cbn; eauto. 2: intros [|[]]; cbn; eauto.
            eapply normal_subst with (sigma0 := b .: a .: var) in N' as N2.
            2: intros [|[]]; cbn; eauto. 2: intros [|[]]; cbn; eauto. cbn in N1, N2.
            eapply equiv_unique_normal_forms in H3. eapply equiv_unique_normal_forms in H6.
            eapply equiv_unique_normal_forms in H.  eapply equiv_unique_normal_forms in H7.
            1 - 12: eauto 2. 2, 4, 5, 7: eauto using normal_app_l, normal_app_r.
            all: repeat eapply normal_app_intro; eauto.
            destruct u1 as [[|[]]|[]| |]; try discriminate. 
            destruct u2 as [[|[]]| | |[[|[]]| | |] [[|[]] | | |]]; cbn in *; try congruence.
            destruct e as [[|[]]|[] | |]; cbn in *; try congruence.
            destruct e0 as [[|[]]|[] | |]; cbn in *; try congruence.
        - eapply normal_lam_elim in N'.
          eapply head_atom in N'; eauto.
          eapply atom_lifting with (sigma := a .: var) in N'.
          2: intros []; cbn; eauto.
          rewrite head_subst in N'.
          2: intros []; cbn; eauto.
          cbn in N. Injection EQ1. Injection H. Discriminate.
      Qed.




                                                                          
    Lemma backward_mult:
      m * n = p.
    Proof.
      destruct multiplication_lambdas as [H | [u']]; subst.
      - cbn in EQ2. rewrite H in *. rewrite Ex, Ey, Ez in *.
        do 2 (rewrite stepBeta in EQ2; cbn; asimpl; eauto).
        Injection EQ2. do 2 (rewrite stepBeta in H1; cbn; asimpl; eauto).
        Injection H1. Injection H0. Injection H2. Injection H0.
        eapply enc_injective in H1. eapply enc_injective in H3.
        all: eauto; intuition; subst. omega.
      - cbn in EQ1, EQ2; rewrite H in *.
        assert (normal u') as N' by (do 3 eapply normal_lam_elim; rewrite <-H; eauto).
        clear H. rewrite Ex, Ey, Ez in *. clear x y z Ex Ey Ez.
        do 6 (rewrite stepBeta in EQ1; cbn; asimpl; eauto).
        do 6 (rewrite stepBeta in EQ2; cbn; asimpl; eauto).
         simplify in EQ1 EQ2. 
        fold σ1 in EQ1. fold σ2 in EQ2. fold τ1 in EQ1. fold τ2 in EQ2.
        
        eapply equiv_unique_normal_forms in EQ1; [eauto | eauto |idtac..].
        eapply equiv_unique_normal_forms in EQ2; [eauto | eauto |idtac..].
        3, 5: eapply normal_app_intro; cbn; intuition.
        2 - 5: eapply normal_subst; try eassumption.
        2 - 9: intros [|[|[]]]; cbn; eauto 2.
        2, 4, 6, 7: (repeat eapply normal_app_intro); eauto 2.
        2 - 3: destruct n; simplify; eauto.
        eapply steps_u_mult; eauto. 
    Qed.

    
    End MultiplicationBackward.


    Section MultiplicationForward.

      Definition GT k := lambda lambda lambda lin (tab T k) (var 0).

      Lemma GT_equiv s t u k:
        GT k s t u ≡  lin (u .: t .: s .: var •₊ tab T k) u.
      Proof.
        unfold GT. 
        eapply equiv_expand. do 3 (dostep; cbn). asimpl.
        1 - 2: eauto. eapply eq_equiv. f_equal.
        rewrite !map_map. eapply map_ext.
        intros ?; asimpl. reflexivity.
      Qed.


      Lemma forward_mul1:
        m * n = p -> sigma (G x y z) = GT m -> sigma • fst (mulEQ₁ x y z) ≡ sigma • snd (mulEQ₁ x y z).
      Proof.
        intros <-. cbn. intros ->. rewrite Ex, Ey, Ez. clear Ex Ey Ez x y z. asimpl.
        rewrite !GT_equiv. simplify; fold σ1 τ1. 
        replace (g (enc _ _) (enc _ _)) with (σ1 • T m).
        2: cbn; asimpl; cbn; now rewrite mult_comm.
        rewrite <-lin_cons. change (g _ a) with (lin (σ1 •₊ [T m]) a).
        rewrite <-lin_app, <-map_app. change (tab _ m ++ _) with (tab T (S m)).
        eapply eq_equiv. f_equal.
        rewrite (map_ext_in) with (g := subst_exp (var 0 .: b .: a .: var)).
        2: intros ?; rewrite tab_map_nats; intros ?; mapinj; unfold T; cbn; now asimpl.
        rewrite !tab_subst. clear σ1 σ2. 
        induction m; simplify; cbn.
        - reflexivity.
        - simplify; cbn in *. rewrite app_comm_cons. f_equal.
          eauto.  asimpl; cbn; simplify.
          now rewrite plus_comm; change (g a b) with (enc 1 b); simplify.
      Qed.

      Lemma forward_mul2:
        m * n = p -> sigma (G x y z) = GT m -> sigma • fst (mulEQ₂ x y z) ≡ sigma • snd (mulEQ₂ x y z).
      Proof.
        intros <-. cbn. intros ->. rewrite Ex, Ey, Ez. clear Ex Ey Ez x y z. asimpl.
        rewrite !GT_equiv. simplify; fold σ2 τ2. 
        replace (g (enc _ _) (enc _ _)) with (σ2 • T m).
        2: cbn; asimpl; cbn; now rewrite mult_comm.
        rewrite <-lin_cons. change (g _ a) at 1 with (lin (σ2 •₊ [T m]) a).
        rewrite <-lin_app, <-map_app. change (tab _ m ++ _) with (tab T (S m)).
        eapply eq_equiv. f_equal.
        rewrite (map_ext_in) with (g := subst_exp (var 0 .: a .: b .: var)).
        2: intros ?; rewrite tab_map_nats; intros ?; mapinj; unfold T; cbn; now asimpl.
        rewrite !tab_subst. clear σ1 σ2. 
        induction m; simplify; cbn.
        - reflexivity.
        - simplify; cbn in *. rewrite app_comm_cons. f_equal.
          eauto.  asimpl; cbn; simplify.
          now rewrite plus_comm; change (g a a) with (enc 1 a); simplify.
      Qed.
      
    End MultiplicationForward.

  End Multiplication.
        
   
End EquationEquivalences.


(** ** Forward Direction **)
Section Forward.


  Variables (E: list deq).

  Definition func n := lambda enc n (var 0).
  

  Lemma tab_typing {X} n (f: nat -> exp X) g k Gamma:
    (forall i, Gamma ⊢(n) f i : g i) -> Gamma ⊢₊(n) tab f k : tab g k.
  Proof.
    intros; induction k; cbn; eauto.
    eapply orderlisttyping_app; eauto.
  Qed.

  Lemma func_typing Gamma n: Gamma ⊢(2) func n : alpha → alpha.
  Proof.
    econstructor. eapply enc_typing. eauto.
  Qed.

  Lemma GT_typing Gamma m n: Gamma ⊢(2) GT m n : alpha → alpha → alpha → alpha.
  Proof.
    do 3 econstructor. eapply lin_typing; [|eauto].
    rewrite repeated_tab. simplify.
    eapply tab_typing.
    intros; econstructor; cbn. econstructor.
    all: eauto using enc_typing. 
  Qed.

  Definition enc_sol (sigma: nat -> nat) (x: fin) :=
    match partition_F_G x with
    | inl (exist _ x _) => func (sigma x)
    | inr (exist _ (x,y,z) _) => GT (sigma y) (sigma x)
    end.

  Lemma enc_sol_encodes theta h: encodes (enc_sol theta (F h)) (theta h).
  Proof.
    unfold enc_sol.
    destruct partition_F_G as [[x ?]|[((x,y),z) ?]]. 
    - eapply F_injective in e as ->.
      intros t. unfold func. rewrite stepBeta; asimpl; eauto.
    - exfalso; eapply disjoint_F_G; eauto.
  Qed.
  
  Lemma enc_sol_GT theta x y z: (enc_sol theta (G x y z)) = GT (theta y) (theta x).
  Proof.
    unfold enc_sol.
    destruct partition_F_G as [[x' ?]|[((x',y'),z') ?]].
    - exfalso; eapply disjoint_F_G; eauto.
    - now eapply G_injective in y0 as (-> & -> & ->).   
  Qed.


  Lemma typing_forward sigma:
    (sigma ⊢⁺ₑ E) -> [] ⊩(2) enc_sol sigma : Gamma__deq E.
  Proof.
    eauto; intros ????; unfold enc_sol.
    destruct partition_F_G as [[]|[((x & y) & z) ?]]; subst.
    + eapply nth_Gamma__deq_F in H0 as ->. eapply func_typing.
    + eapply nth_Gamma__deq_G in H0 as ->. eapply GT_typing. 
  Qed.

  Lemma H10_SU: H10 E -> SOU abg 2 (H10_to_SOU  E).
  Proof.
    intros [sigma H].
    exists []. exists (enc_sol sigma).
    split. now eapply typing_forward.
    eapply equiv_pointwise_eqs.
    intros s t; change s with (fst (s,t)) at 2; change t with (snd (s,t)) at 3.
    remember (s,t) as e. clear Heqe s t.
    intros H'; cbn in *. eapply in_Equations in H' as (d & ? & ?).
      destruct d; cbn in *; intuition; subst.
      all: try eapply forward_add. all: try eapply forward_consts.
      all: try eapply forward_mul1. all: try eapply forward_mul2.
      all: try eapply forward_vars. 
      all: try eapply enc_sol_encodes.
      all: eapply H in H0; inv H0; eauto.
      all: eapply enc_sol_GT.
    Qed.

End Forward.    

(** ** Backward Direction **)
Section Backward.


  Definition decode_subst (sigma: fin -> exp abg) (N: forall x, normal (sigma x)) (x: fin) :=
    match dec_enc (N (F x)) with
    | inl  (exist _ n _) => n
    | inr _ => 0
    end.

  Lemma decode_subst_encodes (sigma: fin -> exp abg) N x n:
    encodes (sigma (F x)) n -> decode_subst sigma N x = n.
  Proof.
    intros H; unfold decode_subst.
    destruct dec_enc as [[m H1]|H1].
    - rewrite H in H1. eapply enc_injective in H1 as []; eauto.
    - exfalso. eapply H1. exists n. now rewrite H.
  Qed.



  Lemma SU_H10 E: SOU abg 2 (H10_to_SOU E) -> H10 E.
  Proof.
    rewrite SOU_NSOU; eauto. intros (Delta & sigma & T & EQ & N).
    exists (decode_subst sigma N). intros e H; pose (Q := eqs e).
    assert (forall p, p ∈ Q -> sigma • fst p ≡ sigma • snd p) as EQs; [|clear EQ].
    - intros [s t] G. cbn; eapply equiv_eqs_pointwise. eapply EQ.
      eapply in_Equations. eauto.
    - destruct e; econstructor; cbn in Q, EQs.
      all: specialize (EQs (varEQ x)) as EQx; mp EQx; intuition; eapply backward_vars in EQx as [n EQx]; eauto.
      2 - 3: specialize (EQs (varEQ y)) as EQy; mp EQy; intuition; eapply backward_vars in EQy as [m EQy]; eauto.
      2 - 3: specialize (EQs (varEQ z)) as EQz; mp EQz; intuition; eapply backward_vars in EQz as [p EQz]; eauto.
      all: repeat (erewrite decode_subst_encodes;[|eauto]).
      + eapply backward_consts; eauto.
      + eapply backward_add; eauto; eapply EQs; eauto.
      + eapply backward_mult; eauto; eapply EQs; intuition.
  Qed.   
End Backward.



Lemma Goldfarb': H10 ⪯ SOU abg 2.
Proof.
  exists H10_to_SOU; intros x; split.
  - eapply H10_SU.
  - eapply SU_H10.
Qed.


Lemma Goldfarb : H10 ⪯ OU 2 abg.
Proof.
  unshelve eexists.
  intros E. eapply (@ordsysuni_orduni _ _ (H10_to_SOU E)).
  eapply le_n_S. cbn; simplify; constructor.
  intros E. cbn. rewrite <-SOU_OU.
  split; eauto using H10_SU, SU_H10.
Qed.
