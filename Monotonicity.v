Section Monotonicity.

Require Import Syntax.
Require Import ProofSystem.
Require Import Model.
Require Import TechnicalLemmas.
Require Import Setoid.

Theorem lt_monotonic : forall (phi : formula)(M : focal_model) (w : W M) (v : var -> D (s M w)) , 
  models M w v phi -> forall (w' : W M) (l : lt M w w'),
    models M w' (extend_v M w w' l v) phi.
  induction phi.
  (* Case FocalTrue *)
    intros. simpl. trivial.
  (* Case FocalFalse *)
    intros. inversion H.
  (* Case Rel_f r l0 *)
    induction r. simpl. 
    intros. assert (equiv_listD (s M w') (map (extend_d_lt M w w' l0) (map (fun x : term => mu M w v x) l)) (map (fun x : term => mu M w' (extend_v M w w' l0 v) x) l)).
      apply equiv_list_ext with (M := M) (w := w) (w' := w') (l := l) (v := v) (ltww := l0).
    rewrite <- ind_R with (M := (s M w')) (i := n) (ds := (map (extend_d_lt M w w' l0) (map (fun x : term => mu M w v x) l))) (ds' := (map (fun x : term => mu M w' (extend_v M w w' l0 v) x) l)). 
    apply r_subset_lt with (M := M) (w := w) (w' := w') (i := n) (ds := map (fun x : term => mu M w v x) l) (l := l0); assumption. assumption.
  (* Case Eq t t0 *)
    intros.
    simpl; simpl in H.
    assert (d_Eq (s M w') (extend_d_lt M w w' l (mu M w v t)) (extend_d_lt M w w' l (mu M w v t0))).
      apply eq_subset_lt. assumption. 
    assert (d_Eq (s M w') (extend_d_lt M w w' l (mu M w v t)) (mu M w' (extend_v M w w' l v) t)).
      apply mu_same. 
    apply equiv_symm in H1.
    assert (d_Eq (s M w') (mu M w' (extend_v M w w' l v) t) (extend_d_lt M w w' l (mu M w v t0))).
      eauto with ModelTheory.
    assert (d_Eq (s M w') (extend_d_lt M w w' l (mu M w v t0)) (mu M w' (extend_v M w w' l v) t0)).
      apply mu_same. 
    eauto with ModelTheory.
  (* Case And phi1 phi2 *)
    intros.
    simpl. simpl in H.
    split.
    (* Part M w' v ||- phi1 *)
      apply IHphi1. apply H.
    (* Part M w' v ||- phi2 *)
      apply IHphi2; apply H.
  (* Case Or phi1 phi2 *)
    intros.
    simpl; simpl in H.
    induction H.
    left; apply IHphi1; auto.
    right; apply IHphi2; auto.
  (* Case Implies phi1 phi2 *)
    intros.
    simpl in H; simpl.
    intros w'' l'.
    assert (lt M w w'').
      apply lt_trans with (w' := w'); [auto | auto].
    assert (forall v1 : var, (extend_v M w' w'' l' (extend_v M w w' l v)) v1 = (extend_v M w w'' H0 v) v1).
      apply extend_v_idempotent.
    rewrite model_v_same with (v' := extend_v M w w'' H0 v). intro; rewrite model_v_same with (v' := extend_v M w w'' H0 v). 
    apply H. assumption. apply H1. apply H1.
  (* Case Not phi *)
    intros. simpl in H. simpl.
    intros w'' l'.
    assert (lt M w w'').
      apply lt_trans with (w' := w'); [auto | auto].
    assert (forall v1 : var, (extend_v M w' w'' l' (extend_v M w w' l v)) v1 = (extend_v M w w'' H0 v) v1).
      apply extend_v_idempotent.
    rewrite model_v_same with (v' := extend_v M w w'' H0 v). apply H.
    assumption; assumption.
  (* Case forall v phi *)
    intros.  simpl.
    intros w'' d l'.
    assert (lt M w w''). (* Anything reachable from w' is reachable from w. *)
      eauto with ModelTheory.
    assert (forall d : D (s M w''), subst_map M w'' (extend_v M w' w'' l' (extend_v M w w' l v0)) v d = subst_map M w'' (extend_v M w w'' H0 v0) v d). (* we only need to extend once. *) 
      assert (forall v : var, extend_v M w' w'' l' (extend_v M w w' l v0) v = extend_v M w w'' H0 v0 v). apply extend_v_idempotent.
      assert (extend_v M w' w'' l' (extend_v M w w' l v0) = extend_v M w w'' H0 v0).
        apply function_same. assumption.
      rewrite H2. trivial. 
    rewrite H1.
    apply H.
  (* Case Exists v phi *)
    intros. simpl.
    simpl in H. induction H.
    exists (extend_d_lt M w w' l x).
    assert (forall v1 : var, extend_v M w w' l (subst_map M w v0 v x) v1 = subst_map M w' (extend_v M w w' l v0) v (extend_d_lt M w w' l x) v1).
      unfold extend_v. unfold subst_map. intros.
      induction (var_dec v1 v).
      trivial. trivial.   
    assert (extend_v M w w' l (subst_map M w v0 v x) = subst_map M w' (extend_v M w w' l v0) v (extend_d_lt M w w' l x)). apply function_same. assumption.
    rewrite <- H1.
    apply IHphi with (v := subst_map M w v0 v x). assumption.
  (* Case Says t phi *)
    intros. simpl. intros u l' w'' a.
    assert (lt M w u).
      eauto with ModelTheory.
    simpl in H. 
    assert (forall (x : var), extend_v M w' u l' (extend_v M w w' l v) x = extend_v M w u H0 v x).
      apply extend_v_idempotent with (w'' := u) (l'' := H0).
    generalize dependent a.
    rewrite mu_v_same with (v := extend_v M w' u l' (extend_v M w w' l v)) (v' := extend_v M w u H0 v).
    intros.
    rewrite function_same with (f := extend_v M w' u l' (extend_v M w w' l v)) (g := extend_v M w u H0 v).
    apply H with (w' := u) (l := H0) (w'' := w''); assumption;
    eauto with ModelTheory.  eauto with ModelTheory. assumption.
  (* Case Speaksfor t t0 *)
    
    simpl. intros.
    assert (connected M (coerce_d_to_p M w (mu M w v t)) w w').
      assert (w' = w'). trivial.
      exists (lte M (coerce_d_to_p M w (mu M w v t)) w w' w' l (eqw M (coerce_d_to_p M w (mu M w v t)) w' w' H1)). trivial.
    apply connected_restricted with (w := w). apply connected_P_Eq with (p := (coerce_d_to_p M w (mu M w v t))). apply mu_pi_same. 
    assumption.
    apply restricted_A_P_Eq with (p := (coerce_d_to_p M w (mu M w v t))).
    apply mu_pi_same.
    assert (restricted_A M (coerce_d_to_p M w (mu M w v t0)) w w'0 w'').
      assert (restricted_A M (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) t0)) w w'0 w'').
        apply connected_restricted with (w := w').
        assert (connected M (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) t0)) w w'). 
          assert (w' = w'). trivial. 
          exists (lte M (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) t0)) w w' w' l (eqw M (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) t0)) w' w' H2)). trivial.
          destruct H2. clear H2.
          exists (con_symm M (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) t0)) w' w x). trivial.
        assumption.
      apply restricted_A_P_Eq with (p := coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) t0)). apply p_Eq_symm; apply mu_pi_same. assumption.
      apply H. assumption.
Qed.


Lemma lt_monotonic_all : forall (M : focal_model) (w w' : W M) (v : var -> D (s M w)) (l : lt M w w') (Gamma : list formula),
  modelsAll M w v Gamma -> modelsAll M w' (extend_v M w w' l v) Gamma.
  intros.
  induction Gamma as [| phi Gamma'].
  (* Case Gamma = nil *)
    simpl. trivial.
  (* Case Gamma = phi :: Gamma' *)
    unfold modelsAll; simpl; fold modelsAll.
    unfold modelsAll in H; simpl in H; fold modelsAll in H.
    split.
    (* Part M w' v ||- phi *)
      apply lt_monotonic. apply H.
    (* part modelsAll M w' v Gamma' *)
      apply IHGamma'. apply H.
  Qed.

End Monotonicity.
