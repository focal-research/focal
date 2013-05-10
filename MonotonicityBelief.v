Section MonotonicityBelief.

Require Import Syntax.
Require Import ProofSystem.
Require Import Belief.
Require Import TechnicalLemmasBelief.
Require Import Setoid.

Theorem B_lt_monotonic : forall (phi : formula)(B : belief_model) (w : B_W B) 
                              (v : var -> D (B_s B w)) ,
  B_models B w v phi -> forall (w' : B_W B) (l : B_lt B w w'), 
                          B_models B w' (B_extend_v B w w' l v) phi.
Proof.
  induction phi.
  (* Case FocaleTrue *)
    simpl. trivial.
  (* Case FocaleFalse *)
    intros. simpl in H. inversion H.
  (* Case Rel_f *)
    intros; destruct r; simpl. 
    assert (equiv_listD (B_s B w') (map (B_extend_d_lt B w w' l0) 
             (map (fun x : term => B_mu B w v x) l)) 
             (map (fun x : term => B_mu B w' (B_extend_v B w w' l0 v) x) l)).
      apply B_equiv_list_ext.
    simpl in H.
    rewrite <- ind_R with (ds := map (B_extend_d_lt B w w' l0) 
                                     (map (fun x : term => B_mu B w v x) l)).
    apply B_r_subset_lt. exact H. exact H0.
  (* Case Eq *)
    intros; simpl. 
    assert (d_Eq (B_s B w') (B_mu B w' (B_extend_v B w w' l v) t)
                          (B_extend_d_lt B w w' l (B_mu B w v t))).
      symmetry; apply B_mu_same.
    assert (d_Eq (B_s B w') (B_mu B w' (B_extend_v B w w' l v) t0)
                          (B_extend_d_lt B w w' l (B_mu B w v t0))).
      symmetry; apply B_mu_same.
    transitivity (B_extend_d_lt B w w' l (B_mu B w v t)). exact H0.
    symmetry;
    transitivity (B_extend_d_lt B w w' l (B_mu B w v t0)). exact H1.
    simpl in H. apply B_eq_subset_lt. symmetry in H; exact H.
  (* Case And *)
    intros; simpl; simpl in H; split. 
    apply IHphi1; apply H. apply IHphi2; apply H.
  (*Case Or *)
    intros. simpl; simpl in H. destruct H.
    left; apply IHphi1; exact H.
    right; apply IHphi2; exact H.
  (* Case Implies *)
    intros; simpl; simpl in H; intros.
    assert (B_lt B w w'0). apply B_lt_trans with (w' := w'); assumption.
    apply B_models_v_same with (v := B_extend_v B w w'0 H1 v).
    intro; rewrite B_extend_v_idempotent with (l'' := H1). reflexivity.
    apply H. apply B_models_v_same with (v := B_extend_v B w' w'0 l0 
                                               (B_extend_v B w w' l v)).
    intro; rewrite B_extend_v_idempotent with (l'' := H1). reflexivity.
    exact H0.
  (* Case Not *)
    intros. simpl in H. simpl.
    intros w'' l'.
    assert (B_lt B w w'').
      apply B_lt_trans with (w' := w'); [auto | auto].
    assert (forall v1 : var, (B_extend_v B w' w'' l' (B_extend_v B w w' l v)) v1 = (B_extend_v B w w'' H0 v) v1).
      apply B_extend_v_idempotent.
    rewrite B_model_v_same with (v' := B_extend_v B w w'' H0 v). apply H.
    assumption; assumption.
  (* Case Forall*)
    intros.  simpl.
    intros w'' d l'.
    assert (B_lt B w w'').
      apply B_lt_trans with (w' := w'); assumption.
    assert (forall d : D (B_s B w''), B_subst_map B w'' (B_extend_v B w' w'' l' (B_extend_v B w w' l v0)) v d = B_subst_map B w'' (B_extend_v B w w'' H0 v0) v d). 
      assert (forall v1 : var, B_extend_v B w' w'' l' (B_extend_v B w w' l v0) v1 = B_extend_v B w w'' H0 v0 v1). apply  B_extend_v_idempotent.
      assert (B_extend_v B w' w'' l' (B_extend_v B w w' l v0) = B_extend_v B w w'' H0 v0).
        apply function_same. assumption.
      rewrite H2. trivial. 
    rewrite H1.
    apply H.
  (* Case Exists *)
    intros. simpl.
    simpl in H. induction H.
    exists (B_extend_d_lt B w w' l x).
    assert (forall v1 : var, B_extend_v B w w' l (B_subst_map B w v0 v x) v1 = B_subst_map B w' (B_extend_v B w w' l v0) v (B_extend_d_lt B w w' l x) v1).
      unfold B_extend_v. unfold B_subst_map. intros.
      induction (var_dec v1 v).
      trivial. trivial.   
    assert (B_extend_v B w w' l (B_subst_map B w v0 v x) = B_subst_map B w' (B_extend_v B w w' l v0) v (B_extend_d_lt B w w' l x)). apply function_same. assumption.
    rewrite <- H1.
    apply IHphi with (v := B_subst_map B w v0 v x). assumption.
  (* Case Says *)
    intros. simpl; simpl in H.
    apply B_worldview_respects with (p := B_coerce_d_to_p B w (B_mu B w v t)).
    apply B_mu_pi_same. 
    apply B_worldview_monotonic with (w := w). exact H.
  (* Case Speaksfor *)
    simpl; intros.
    apply B_worldview_respects with (p := B_coerce_d_to_p B w (B_mu B w v t0)).
      apply B_mu_pi_same.
    assert (B_lt B w w'0). 
      apply B_lt_trans with (w' := w'); [exact l | exact l0].
    assert ((B_extend_v B w' w'0 l0 (B_extend_v B w w' l v))
           = B_extend_v B w w'0 H1 v).
      assert (forall v1 : var, 
            B_extend_v B w' w'0 l0 (B_extend_v B w w' l v) v1
           = B_extend_v B w w'0 H1 v v1).
      apply B_extend_v_idempotent. apply function_same. exact H2.
    rewrite H2.
    apply H. rewrite <- H2.
    apply B_worldview_respects with (p := B_coerce_d_to_p B w' 
                                           (B_mu B w' 
                                             (B_extend_v B w w' l v)
                                           t)).
    apply B_p_eq_symm. apply B_mu_pi_same.
    exact H0.
Qed. 


Theorem B_lt_monotonic_all : forall (B : belief_model) (w : B_W B) 
                              (v : var -> D (B_s B w)) (Gamma : list formula),
  B_modelsAll B w v Gamma -> forall (w' : B_W B) (l : B_lt B w w'), 
                               B_modelsAll B w' (B_extend_v B w w' l v) Gamma.
Proof.
  intros. induction Gamma as [| phi' Gamma'].
  simpl; trivial.
  simpl; split. simpl in H; apply B_lt_monotonic; apply H.
  simpl in H; apply IHGamma'. apply H.
Qed.

End MonotonicityBelief.