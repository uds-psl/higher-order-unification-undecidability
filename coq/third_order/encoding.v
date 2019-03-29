Set Implicit Arguments.
Require Import RelationClasses Morphisms List
        Omega Init.Nat Setoid std calculus pcp.
Import ListNotations.


(** * Third-Order Encoding *)
Section Encoding.

  Context {X: Const}.
  Variable  (u v: nat).
  Hypothesis (u_neq_v: u <> v).
  
  
  (** Encoding of symbols *)
  Definition encb (b: symbol) : exp X :=
    var (if b then u else v).

  (** Encoding of words *)
  Definition enc (w: word) : exp X :=
    lambda (AppL (renL shift (map encb w)) (var 0)).

  (** Encoding of words *)
  Notation Enc := (map enc).


  (** ** Encoding Typing *)
  Section Typing.
    
    Lemma encb_typing (Gamma: ctx) b:
      (Gamma ⊢(3) @var X u : alpha → alpha) ->
      (Gamma ⊢(3) @var X v : alpha → alpha) ->
      Gamma ⊢(3) encb b : (alpha → alpha).
    Proof.
      intros H1 H2. destruct b; eauto.
    Qed.
    

    Lemma enc_typing (Gamma: ctx) w:
      (Gamma ⊢(3) @var X u : alpha → alpha) ->
      (Gamma ⊢(3) @var X v : alpha → alpha) ->
      Gamma ⊢(3) enc w : alpha → alpha.
    Proof.      
      intros.
      econstructor; eauto. inv H; inv H0.
      eapply AppL_ordertyping_repeated;eauto.
      eapply orderlisttyping_preservation_under_renaming.
      eapply repeated_ordertyping; simplify.
      intros; mapinj. eapply encb_typing. all: eauto. 
      intros ??; cbn; eauto.
    Qed.
    
    Lemma Enc_typing (Gamma: ctx) W:
      (Gamma ⊢(3) @var X u : alpha → alpha) ->
      (Gamma ⊢(3) @var X v : alpha → alpha) ->
      Gamma ⊢₊(3) Enc W : repeat (alpha → alpha) (length W).
    Proof.
      intros. eapply repeated_ordertyping; simplify; eauto.
      intros; mapinj. eapply enc_typing; eauto.
    Qed.
  End Typing.



  (** ** Encoding Properities *)
  

  (** *** Reduction *)
  Section Reduction.
    
    Lemma enc_nil s: enc [] s ≡ s.
    Proof.
      unfold enc; cbn.
      rewrite stepBeta; asimpl; cbn; eauto.
    Qed.

    Lemma enc_cons b w s: enc (b :: w) s ≡ encb b (enc w s).
    Proof.
      unfold enc. eapply equiv_join; rewrite stepBeta; asimpl;  eauto.
      rewrite map_map, map_id_list. rewrite map_map, map_id_list. eauto.
      all: intros; now asimpl.
    Qed.

    Hint Rewrite enc_nil enc_cons : simplify.

    Lemma enc_app w1 w2 s:
      enc (w1 ++ w2) s ≡ enc w1 (enc w2 s).
    Proof.
      induction w1; cbn; simplify; eauto.
      now rewrite IHw1. 
    Qed.

    Hint Rewrite enc_app : simplify.
    
    Lemma enc_concat W s:
      AppL (Enc W) s ≡ enc (concat W) s.
    Proof.
      induction W; cbn; simplify; eauto.
      now rewrite IHW. 
    Qed.
  End Reduction.

  
  Hint Rewrite enc_nil enc_cons enc_app : simplify.
  


  (** *** Substitution *)
  Section Substitution.

    Lemma encb_subst_id a (sigma: fin -> exp X):
      sigma u = var u -> sigma v = var v -> sigma • encb a = encb a.
    Proof.
      intros; unfold encb; cbn; destruct a; eauto.
    Qed.

    Lemma enc_subst_id (sigma: fin -> exp X) w:
      sigma u = var u -> sigma v = var v ->  sigma • (enc w) = enc w.
    Proof.
      unfold enc.
      intros H1 H2. cbn. f_equal.
      asimpl. f_equal. rewrite map_id_list; eauto.
      intros x ?; mapinj; mapinj. asimpl.
      rewrite <-compComp_exp, encb_subst_id; eauto.
    Qed.
    
    Lemma Enc_subst_id (sigma: fin -> exp X) W:
      sigma u = var u -> sigma v = var v ->  sigma •₊ Enc W = Enc W.
    Proof.
      intros. eapply map_id_list.
      intros; mapinj;eapply enc_subst_id; eauto.
    Qed.
    
  End Substitution.

  (** *** Injectivity *)
  Section Injectivity.
    Lemma encb_eq a b:
      encb a ≡ encb b -> a = b.
    Proof.
      intros H % equiv_head_equal; cbn in *; eauto.
      injection H; destruct a, b; intros; eauto; exfalso; eapply u_neq_v; eauto.
    Qed.

    
    Lemma enc_eq w1 w2 s t:
      enc w1 s ≡ enc w2 t ->
      (forall s', ~ s ≡ var u s') -> (forall s', ~ s ≡ var v s') ->
      (forall t', ~ t ≡ var u t') -> (forall t', ~ t ≡ var v t') ->
      w1 = w2.
    Proof.
      simplify. intros. induction w1 in w2, H |-*; destruct w2; cbn in *; eauto.
      - simplify in H. destruct b; firstorder. 
      - simplify in H; symmetry in H; destruct a; firstorder. 
      - simplify in H; Injection H.
        now rewrite IHw1 with (w2 := w2), encb_eq with (a := a) (b := b).
    Qed.
  End Injectivity.
End Encoding.

Hint Rewrite @enc_app @enc_nil: simplify. 
Notation Enc u v := (map (enc u v)).




Section ReductionEncodings.

  Context {X: Const}.
  
  Definition finst I n := Lambda n (AppL (map var I) (@var X n)).

  Lemma finst_typing I n :
    I ⊆ nats n ->
    [alpha] ⊢(3) finst I n : Arr (repeat (alpha → alpha) n) alpha.
  Proof.
    intros H; eapply Lambda_ordertyping; simplify; eauto.
    eapply AppL_ordertyping_repeated.
    eapply repeated_ordertyping; simplify; eauto.
    intros; mapinj.  
    econstructor; simplify; cbn; eauto.
    rewrite nth_error_app1; simplify; eauto.
    eapply nth_error_repeated; eauto.
    1 - 2: eapply nats_lt, H, H2.
    econstructor; simplify; eauto.  
    rewrite nth_error_app2; simplify; eauto.
  Qed.
  
  
  Lemma finst_equivalence u v I W delta:
    I ⊆ nats (length W) ->
    AppR (ren delta (finst I (length W))) (Enc u v W) ≡ enc u v (concat (select I W)) (var (delta 0)).
  Proof.
    intros. unfold finst. rewrite !Lambda_ren, !AppL_ren.
    rewrite !map_id_list.
    2: intros ? ?; mapinj; cbn; eapply H, nats_lt in H2; now rewrite it_up_ren_lt. 
    cbn; rewrite it_up_ren_ge; eauto; simplify.
    rewrite !AppR_Lambda'; simplify; eauto. asimpl.
    rewrite !sapp_ge_in; simplify; eauto.
    rewrite !select_variables_subst; [|simplify; eauto..].
    now rewrite <-!select_map, enc_concat.  
  Qed.

End ReductionEncodings.


Section EquivalenceInversion.

  Variables  (X: Const) (s t: exp X) (x: nat) (sigma: fin -> exp X) (S: list (exp X)).
  Hypothesis (H1: forall y, isVar (sigma y) /\ sigma y <> var x).
  Hypothesis (N: normal s).
  Hypothesis (EQ: S .+ sigma • s ≡ (var x) t).


  Lemma end_head_var:
    exists (h: nat) T s', s = AppR (var h) T /\ nth S h = Some s'.
  Proof.
    eapply normal_nf in N as N'. inv N'. destruct k; cbn in *; eauto; [|Discriminate].
    destruct (s0); cbn in H; intuition; clear H.
    - assert(f < |S| \/ f >= |S|) as [] by omega; eauto.
      eapply nth_error_lt_Some in H as H2; destruct H2; eauto.
      asimpl in EQ; rewrite sapp_ge_in in EQ; eauto.
      specialize (H1 (f - |S|)). intuition.
      eapply equiv_head_equal in EQ; cbn; simplify; eauto. simplify in EQ; cbn in EQ; eauto.
      destruct (sigma (f - (|S|))); cbn in *; intuition.
    - eauto. asimpl in EQ.
      eapply equiv_head_equal in EQ; cbn; simplify in *; eauto.
      cbn in EQ; discriminate.
  Qed.


  Lemma end_is_var_typed Gamma A u v C:
    S = Enc u v C -> 
    (repeat (alpha → alpha) (|S|)  ++ Gamma ⊢(3) s : A) ->
    exists i e, i < |S| /\ s = var i e.
  Proof.
    intros H2 H4; destruct end_head_var as (h' & T & s' & H5); intuition; subst.   
    destruct T as [| t1 [| t2 T]].
    + cbn in EQ. erewrite nth_error_sapp in EQ; eauto.
      rewrite nth_error_map_option in H0; destruct nth; try discriminate.
      cbn in H0; injection H0 as <-.
      unfold enc in EQ; Discriminate. 
    + exists h'. exists t1. intuition. now eapply nth_error_Some_lt in H0.
    + eapply AppR_ordertyping_inv in H4.
      destruct H4 as [L]; intuition.
      inv H3. rewrite nth_error_app1, nth_error_repeated in H5; simplify in *; eauto.
      inv H2. inv H8. cbn in H5; injection H5 as ?.
      rewrite !Arr_app in H; cbn in H. eapply (f_equal arity) in H.
      rewrite arity_Arr in H; cbn in H. omega.
      all: eapply nth_error_Some_lt in H0; simplify in H0; eauto.
  Qed.

         
End EquivalenceInversion.
