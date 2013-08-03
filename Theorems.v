Section Theorems.

Require Import Syntax.
Require Import ProofSystem.
Require Import Monotonicity.
Require Import TechnicalLemmas.
Require Import Model.
Require Import Classical.
Require Import Belief.
Require Import TechnicalLemmasBelief.
Require Import MonotonicityBelief.

Theorem B_proofsystem_sound : forall (phi : formula) (Gamma : list formula) 
                                (B : belief_model) (w : B_W B) 
                                (v : var -> D (B_s B w)),
  proves Gamma phi -> B_modelsAll B w v Gamma -> B_models B w v phi.
Proof.
  intros phi Gamma B w v H.
  generalize dependent w.
  generalize dependent H.
  apply (proves_ind (fun Gamma phi => (forall (w : B_W B) (v : var -> D (B_s B w)), B_modelsAll B w v Gamma -> B_models B w v phi))).
  (* Case phi \in Gamma *)
    intros.
    apply B_modelsAll_all_modeled with (Gamma := Gamma0); assumption.
  (* Case trueI *)
    intros. simpl. trivial.
  (* Case falseE *)
    intros. apply B_false_models_all. apply H0; exact H1. (* Nothing ever models false, so false elimination is true vacuously. *)
  (* Case andI *)
    intros. simpl. split.
    apply H0; exact H3.
    apply H2; exact H3.
  (* Case andE1 *)
    intros. assert (B_models B w v (And phi0 psi)). apply H0; exact H1.
    simpl in H2. apply H2.
  (* Case andE2 *)
    intros. assert (B_models B w v (And phi0 psi)). apply H0; apply H1.
    simpl in H2. apply H2.
  (* Case orI1 *)
    intros. assert (B_models B w v phi0). apply H0; apply H1. 
    simpl. left; assumption.
  (* Case orI2 *)
    intros. assert (B_models B w v psi). apply H0; apply H1.
    simpl. right; assumption.
  (* Case orE *)
    intros. assert (B_models B w v (Or phi1 phi2)). apply H0; exact H5.
    simpl in H6; destruct H6.
    assert (B_modelsAll B w v (phi1 :: Gamma0)). apply B_pushback; assumption.
    apply H2; assumption.
    assert (B_modelsAll B w v (phi2 :: Gamma0)). apply B_pushback; assumption.
    apply H4; assumption.
  (* Case impI *)
    intros. simpl; intros.
    assert (B_modelsAll B w' (B_extend_v B w w' l v) Gamma0).
      apply B_lt_monotonic_all; assumption.
    apply H0. apply B_pushback; assumption.
  (* Case impE *)
    intros. assert (B_models B w v phi0).
      apply H0; assumption.
    simpl in H2. 
    assert (B_lt B w w). apply B_lt_refl.
    assert (forall variable : var, ((B_extend_v B w w H5 v) variable = v variable)).
      intros. unfold B_extend_v. apply B_extend_d_once.
    assert (B_models B w v psi <-> B_models B w (B_extend_v B w w H5 v) psi). (* This should be taken care of with functiofocale equality. *)
      apply B_model_v_same. symmetry. apply H6.
    rewrite H7. apply H2. assumption. apply H0.
    rewrite B_modelsAll_v_same with (v' := v); assumption.
  (* Case forallI *)
    intros. simpl. intros. apply H0. apply B_replace_all.
    exact H1. apply B_lt_monotonic_all. exact H2.
  (* Case forallE *)
    simpl; intros.
    rewrite <- B_pushback_subst.
    assert (forall (d : D (B_s B w)), B_models B w (B_subst_map B w v x d) phi0).
      intros. 
      assert (B_lt B w w). apply B_lt_refl.
      assert (B_extend_v B w w H2 v = v). apply function_same. unfold B_extend_v. intros. apply B_extend_d_once.
      rewrite <- H3. apply H0. assumption.
    apply H2.
  (* Case existsI *)
    simpl; intros.
    exists (B_mu B w v tau). rewrite B_pushback_subst. apply H0. assumption.
  (* Case existsE *)
    simpl; intros.
    assert (exists d : D (B_s B w), B_models B w (B_subst_map B w v x d) phi0).
      apply H0. assumption.
    assert (exists d : D (B_s B w), B_models B w (B_subst_map B w v x d) psi).
      destruct H5. exists x0. apply H2. split.
      assumption.
      rewrite <- B_replace_all. assumption. 
      unfold is_true in H3. unfold andb in H3. destruct (notfree_in_formula x psi). rewrite H3. unfold is_true. trivial. inversion H3.
    destruct H6. rewrite B_replacement with (d := x0) (x := x). assumption.
    unfold is_true in H3. unfold andb in H3. destruct (notfree_in_formula x psi). unfold is_true. trivial. inversion H3.
  (* Case saysIRL *)
    intros. simpl.
    apply B_worldview_closed with (Gamma := Gamma0).
    apply B_relativize_as_box. exact H1.
    exact H0.
  (* Case says IR *)
    intros. simpl.
    apply B_worldview_closed with (Gamma := relativize p Gamma0).
    apply B_relativize_as_box. rewrite <- worldview_transparant_relativize.
    exact H1. exact H0.
  (* Case saysIL *)
    intros. simpl.
    assert (B_worldview B (B_coerce_d_to_p B w (B_mu B w v p)) w v (Says p phi0)).
      apply B_worldview_closed with (Gamma := Gamma0).
      apply B_relativize_as_box. exact H1. exact H0.
    apply B_worldview_transparent. exact H2.
   (* Case eqRefl *)
     intros. simpl. apply equiv_refl.
   (* Case eqSymm *)
     intros; simpl. apply equiv_symm.
     assert (B_models B w v (Eq tau1 tau2)). apply H0. exact H1.
     simpl in H2; exact H2.
   (* Case eqTrans *)
     intros; simpl.
     assert (B_models B w v (Eq tau1 tau2)). apply H0; exact H3.
     assert (B_models B w v (Eq tau2 tau3)). apply H2; exact H3.
     simpl in H4; simpl in H5; apply equiv_trans with (d' := B_mu B w v tau2).
     exact H4. exact H5.
   (* Case indF *)
     intros; simpl. destruct f; apply ind_F.
     rewrite H. apply equiv_listD_refl.
   (* Case indR *)
     intros; simpl. destruct r. rewrite <- H.
     assert (B_models B w v (Rel_f (Rel n) taus)).
       apply H1; exact H2.
     simpl in H3. exact H3.
   (* Case handOff *)
     simpl; intros.
     assert (forall phi : formula,
       B_worldview B (B_coerce_d_to_p B w' (B_mu B w' (B_extend_v B w w' l v) tau1)) w'
                       (B_extend_v B w w' l v) phi ->
       B_worldview B (B_coerce_d_to_p B w' (B_mu B w' (B_extend_v B w w' l v) tau2)) w'
                       (B_extend_v B w w' l v) phi).
       apply B_handoff.
       apply B_worldview_respects with (p := B_coerce_d_to_p B w (B_mu B w v tau2)).
       apply B_mu_pi_same.
       apply B_worldview_monotonic. apply H0. exact H1.
     apply B_worldview_respects with (p := B_coerce_d_to_p B w' (B_mu B w' (B_extend_v B w w' l v) tau2)).
     apply B_p_eq_symm. apply B_mu_pi_same. apply H3.
     apply B_worldview_respects with (p := B_coerce_d_to_p B w (B_mu B w v tau1)).
     apply B_mu_pi_same. apply H2.
  (* Case speaksSays *)
     intros. simpl. assert (B_models B w v (Speaksfor tau1 tau2)).
     apply H0. exact H3.
     assert (B_models B w v (Says tau1 phi0)). apply H2; exact H3.
     simpl in H4; simpl in H5.
     assert (B_lt B w w). apply B_lt_refl.
     assert (v = B_extend_v B w w H6 v).
       assert (forall v1 : var, v v1 = B_extend_v B w w H6 v v1).
         apply B_extend_v_self.
       apply function_same. exact H7.
     rewrite H7.
     apply B_worldview_respects with (p := (B_coerce_d_to_p B w (B_mu B w v tau2))).
     rewrite <- H7. apply B_p_eq_refl.
     apply H4. rewrite <- H7. exact H5.
   (* Case speaksforRefl *)
     intros. simpl; intros. exact H0.
   (* Case speaksforTrans *)
     intros. simpl; intros.
     assert (B_models B w v (Speaksfor tau1 tau2)). apply H0; exact H3.
     assert (B_models B w v (Speaksfor tau2 tau3)). apply H2; exact H3.
     simpl in H5; simpl in H6. apply H6; apply H5. exact H4.
Qed.

Theorem proofsystem_sound : forall (phi : formula) (Gamma : list formula) (M : focal_model) (w : W M) (v : var -> D (s M w)),
  proves Gamma phi ->  modelsAll M w v Gamma -> models M w v phi.
Proof.
  intros phi Gamma M w v H.
  generalize dependent w.
  generalize dependent H.
  apply (proves_ind (fun Gamma phi => (forall (w : W M) (v : var -> D (s M w)), modelsAll M w v Gamma -> models M w v phi))).
  (* Case phi \in Gamma *)
    intros.
    apply modelsAll_all_modeled with (Gamma := Gamma0); assumption.
  (* Case trueI *)
    intros. simpl. trivial.
  (* Case falseE *)
    intros. apply false_models_all. apply H0; exact H1. (* Nothing ever models false, so false elimination is true vacuously. *)
  (* Case andI *)
    intros. simpl. split.
    apply H0; exact H3.
    apply H2; exact H3.
  (* Case andE1 *)
    intros. assert (models M w v (And phi0 psi)). apply H0; exact H1.
    simpl in H2. apply H2.
  (* Case andE2 *)
    intros. assert (models M w v (And phi0 psi)). apply H0; apply H1.
    simpl in H2. apply H2.
  (* Case orI1 *)
    intros. assert (models M w v phi0). apply H0; apply H1. 
    simpl. left; assumption.
  (* Case orI2 *)
    intros. assert (models M w v psi). apply H0; apply H1.
    simpl. right; assumption.
  (* Case orE *)
    intros. assert (models M w v (Or phi1 phi2)). apply H0; exact H5.
    simpl in H6; destruct H6.
    assert (modelsAll M w v (phi1 :: Gamma0)). apply pushback; assumption.
    apply H2; assumption.
    assert (modelsAll M w v (phi2 :: Gamma0)). apply pushback; assumption.
    apply H4; assumption.
  (* Case impI *)
    intros. simpl; intros.
    assert (modelsAll M w' (extend_v M w w' l v) Gamma0).
      apply lt_monotonic_all; assumption.
    apply H0. apply pushback; assumption.
  (* Case impE *)
    intros. assert (models M w v phi0).
      apply H0; assumption.
    simpl in H2. 
    assert (lt M w w). apply lt_refl.
    assert (forall variable : var, ((extend_v M w w H5 v) variable = v variable)).
      intros. unfold extend_v. apply extend_d_once.
    assert (models M w v psi <-> models M w (extend_v M w w H5 v) psi). (* This should be taken care of with functiofocale equality. *)
      apply model_v_same. symmetry. apply H6.
    rewrite H7. apply H2. assumption. apply H0.
    rewrite modelsAll_v_same with (v' := v); assumption.
  (* Case forallI *)
    simpl; intros.
    apply H0. rewrite <- replace_all.
    apply lt_monotonic_all with (w' := w') (l := l); assumption. assumption.
  (* Case forallE *)
    simpl; intros.
    rewrite <- pushback_subst.
    assert (forall (d : D (s M w)), models M w (subst_map M w v x d) phi0).
      intros. 
      assert (lt M w w). apply lt_refl.
      assert (extend_v M w w H2 v = v). apply function_same. unfold extend_v. intros. apply extend_d_once.
      rewrite <- H3. apply H0. assumption.
    apply H2.
  (* Case existsI *)
    simpl; intros.
    exists (mu M w v tau). rewrite pushback_subst. apply H0. assumption.
  (* Case existsE *)
    simpl; intros.
    assert (exists d : D (s M w), models M w (subst_map M w v x d) phi0).
      apply H0. assumption.
    assert (exists d : D (s M w), models M w (subst_map M w v x d) psi).
      destruct H5. exists x0. apply H2. split.
      assumption.
      rewrite <- replace_all. assumption. 
      unfold is_true in H3. unfold andb in H3. destruct (notfree_in_formula x psi). rewrite H3. unfold is_true. trivial. inversion H3.
    destruct H6. rewrite replacement with (d := x0) (x := x). assumption.
    unfold is_true in H3. unfold andb in H3. destruct (notfree_in_formula x psi). unfold is_true. trivial. inversion H3.
  (* Case saysLRI *)
    intros.
    assert (forall (w' w'' : W M) (l : lt M w w')
      (a : A M
        (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p))
      w' w''),
    modelsAll M w''
    (extend_v_A M w' w''
    (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p)) a
    (extend_v M w w' l v)) Gamma0).
      apply relativize_as_box. assumption.
    simpl. intros.
    apply H0. apply H2.

  (* Case SaysRI *) 
    simpl; intros Gamma0 p phi0 H H0 w v H1 w' l u; intros.
    assert (modelsAll M u (extend_v_A M w' u (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p)) a (extend_v M w w' l v)) (relativize p Gamma0)).
      apply relativize_as_box. intros u' v'' l0 a0.
      assert (exists w'' : W M, lt M w' w'' /\ A M (coerce_d_to_p M w (mu M w v p)) w'' u').
        apply F2 with (u := u). split.
        assert (p_Eq M (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p)) (coerce_d_to_p M w (mu M w v p))).
          apply p_Eq_symm; apply mu_pi_same.
        apply A_P_Eq with (p' := (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p))). apply mu_pi_same; assumption. assumption. assumption.
      destruct H2 as [w''].
      assert (exists w''' : W M, lt M w'' w'''/\ A M (coerce_d_to_p M w (mu M w v p)) w''' v'').
        apply A_Intuitive_Trans with (u := u'). split.
        apply H2. apply A_P_Eq with (p := (coerce_d_to_p M u' (mu M u' (extend_v M u u' l0 (extend_v_A M w' u (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p)) a (extend_v M w w' l v))) p))). 
        apply p_Eq_symm; apply p_Eq_trans with (p2 := coerce_d_to_p M u (mu M u 
                                                                            (extend_v_A M w' u 
                                                                                        (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p)) 
                                                                                        a (extend_v M w w' l v)) p)).
        apply p_Eq_trans with (p2 := coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p)).
        apply mu_pi_same. apply mu_pi_same_A. apply mu_pi_same. apply a0.
      destruct H3 as [w'''].
      assert (lt M w w''').
        apply lt_trans with (w' := w'). assumption. apply lt_trans with (w' := w''). apply H2. apply H3.
      rewrite relativize_as_box in H1.
      assert (A M (coerce_d_to_p M w (mu M w v p)) w''' v''). apply H3.
      assert (lt M w'' w'''). apply H3.
      assert (lt M w' w''). apply H2.
      assert (p_Eq M (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p)) (coerce_d_to_p M w (mu M w v p))).
        apply p_Eq_symm; apply mu_pi_same.
      assert (A M (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p)) w''' v'').
        apply A_P_Eq with (p := coerce_d_to_p M w (mu M w v p)) (p' := coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p)). apply mu_pi_same.
        assumption.
      assert ((extend_v_A M u' v'' (coerce_d_to_p M u'
           (mu M u'
              (extend_v M u u' l0
                 (extend_v_A M w' u
                    (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p)) a
                    (extend_v M w w' l v))) p)) a0
        (extend_v M u u' l0
           (extend_v_A M w' u
              (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p)) a
              (extend_v M w w' l v)))) = (extend_v_A M w''' v'' (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p))) H9
                                            (extend_v M w'' w''' H6
                                               (extend_v M w' w'' H7
                                                  (extend_v M w w' l v)))).
      apply saysRI_v_same. apply p_Eq_symm; apply p_Eq_trans with (p2 := coerce_d_to_p M u (mu M u 
                                                                            (extend_v_A M w' u 
                                                                                        (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p)) 
                                                                                        a (extend_v M w w' l v)) p)). 
      apply mu_pi_same_A. apply mu_pi_same. apply p_Eq_refl. 
      rewrite H10. 
    assert ((extend_v M w'' w''' H6 (extend_v M w' w'' H7 (extend_v M w w' l v))) = (extend_v M w w''' H4 v)).
      assert (lt M w w'').
        apply lt_trans with (w' := w'); assumption.
      assert ((extend_v M w' w'' H7 (extend_v M w w' l v)) = (extend_v M w w'' H11 v)). 
        apply function_same.
        apply extend_v_idempotent.
      rewrite H12. apply function_same. apply extend_v_idempotent.
    rewrite H11.
    assert (p_Eq M (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p)) (coerce_d_to_p M w''' (mu M w''' (extend_v M w w''' H4 v) p))).
      apply p_Eq_trans with (p2 := coerce_d_to_p M w (mu M w v p)); [apply p_Eq_symm | idtac]; apply mu_pi_same.
    assert (A M (coerce_d_to_p M w''' (mu M w''' (extend_v M w w''' H4 v) p)) w''' v'').
      apply A_P_Eq with (p' := (coerce_d_to_p M w''' (mu M w''' (extend_v M w w''' H4 v) p))) (p := (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p))).
        apply p_Eq_trans with (p2 := coerce_d_to_p M w (mu M w v p));
        [apply p_Eq_symm | idtac]; apply mu_pi_same. assumption.
    assert (forall (y : var), d_Eq (s M v'') (extend_v_A M w''' v'' (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p)) H9 (extend_v M w w''' H4 v) y) (extend_v_A M w''' v'' (coerce_d_to_p M w''' (mu M w''' (extend_v M w w''' H4 v) p)) H13 (extend_v M w w''' H4 v) y)).
      intros. apply extend_v_A_same. 
    apply modelsAll_d_Eq with (v' :=(extend_v_A M w''' v''
             (coerce_d_to_p M w''' (mu M w''' (extend_v M w w''' H4 v) p))
             H13 (extend_v M w w''' H4 v))). assumption.
    apply H1 with (w'' := v'') (w' := w''').
    apply H0. assumption.
  (* Case SaysLI *)
    intros; simpl. intros w' l u a.
    assert (exists w'' : W M, exists w''' : W M, lt M w' w'' /\ A M (coerce_d_to_p M w (mu M w v p)) w'' w''' /\ A M (coerce_d_to_p M w (mu M w v p)) w''' u).
      apply A_Intuitive_Dense.
      assert (p_Eq M (coerce_d_to_p M w (mu M w v p)) (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p))).
        apply mu_pi_same.
      apply A_P_Eq with (p := (coerce_d_to_p M w (mu M w v p))) (p' := (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p))); assumption.
    destruct H2 as [w'']. destruct H2 as [w''']. decompose [and] H2.
    assert (modelsAll M w''' (extend_v_A M w'' w''' (coerce_d_to_p M w (mu M w v p)) H5 (extend_v M w' w'' H3 (extend_v M w w' l v))) Gamma0).
      rewrite relativize_as_box in H1.
      assert (lt M w w''). apply lt_trans with (w' := w'); assumption.
      assert (p_Eq M (coerce_d_to_p M w (mu M w v p)) (coerce_d_to_p M w'' (mu M w'' (extend_v M w w'' H4 v) p))).
        apply mu_pi_same.
      assert (A M (coerce_d_to_p M w'' (mu M w'' (extend_v M w w'' H4 v) p)) w'' w''').
        apply A_P_Eq with (p := (coerce_d_to_p M w (mu M w v p))) (p' := (coerce_d_to_p M w'' (mu M w'' (extend_v M w w'' H4 v) p))).
        apply mu_pi_same. assumption.
      assert ((extend_v M w w'' H4 v) = (extend_v M w' w'' H3 (extend_v M w w' l v))).
        symmetry. apply function_same. apply extend_v_idempotent. 
      assert (forall (y : var), d_Eq (s M w''') (extend_v_A M w'' w''' (coerce_d_to_p M w (mu M w v p)) H5 (extend_v M w' w'' H3 (extend_v M w w' l v))y)(extend_v_A M w'' w''' (coerce_d_to_p M w'' (mu M w'' (extend_v M w w'' H4 v) p)) H8 (extend_v M w w'' H4 v)y)).
        intro; rewrite H9 at 2.
        apply extend_v_A_same; assumption.
      apply modelsAll_d_Eq with (v := (extend_v_A M w'' w'''
             (coerce_d_to_p M w'' (mu M w'' (extend_v M w w'' H4 v) p)) H8
             (extend_v M w w'' H4 v))). symmetry. generalize y. assumption.
      apply H1 with (w' := w'') (w'' := w''').
    assert (models M w''' (extend_v_A M w'' w''' (coerce_d_to_p M w (mu M w v p)) H5 (extend_v M w' w'' H3 (extend_v M w w' l v))) (Says p phi0)).
      apply H0. assumption.
    simpl in H7. assert (lt M w''' w'''). apply lt_refl.
    rewrite saysLI_v_same with (w'' := w'') (w''' := w''') (l := H8) (l' := H3) (a' := H5) (a'' := H6).
    assert (A M (coerce_d_to_p M w'''
       (mu M w'''
          (extend_v M w''' w''' H8
             (extend_v_A M w'' w''' (coerce_d_to_p M w (mu M w v p)) H5
                (extend_v M w' w'' H3 (extend_v M w w' l v)))) p)) w''' u).
      apply A_P_Eq with (p := (coerce_d_to_p M w (mu M w v p))) (p' := (coerce_d_to_p M w'''
       (mu M w'''
          (extend_v M w''' w''' H8
             (extend_v_A M w'' w''' (coerce_d_to_p M w (mu M w v p)) H5
                (extend_v M w' w'' H3 (extend_v M w w' l v)))) p))).
      apply p_Eq_trans with (p2 := coerce_d_to_p M  w''' (mu M w''' (extend_v_A M w'' w''' (coerce_d_to_p M w (mu M w v p)) H5
                                                                                (extend_v M w' w'' H3 (extend_v M w w' l v))) p)).
      apply p_Eq_trans with (p2 := coerce_d_to_p M w'' (mu M w'' (extend_v M w' w'' H3 (extend_v M w w' l v)) p)).
      apply p_Eq_trans with (p2 := coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p)).
      apply mu_pi_same. apply mu_pi_same. apply mu_pi_same_A. 
      assert ((extend_v M w''' w''' H8 (extend_v_A M w'' w''' (coerce_d_to_p M w (mu M w v p)) H5
                                                   (extend_v M w' w'' H3 (extend_v M w w' l v))))
              = (extend_v_A M w'' w''' (coerce_d_to_p M w (mu M w v p)) H5
                            (extend_v M w' w'' H3 (extend_v M w w' l v)))).
      apply function_same. symmetry; apply extend_v_self. rewrite H9. apply p_Eq_refl.
      assumption. 
    apply models_v_d_Eq with (v := extend_v_A M w''' u (coerce_d_to_p M w'''
       (mu M w'''
          (extend_v M w''' w''' H8
             (extend_v_A M w'' w''' (coerce_d_to_p M w (mu M w v p)) H5
                (extend_v M w' w'' H3 (extend_v M w w' l v)))) p)) H9 (extend_v M w''' w''' H8
             (extend_v_A M w'' w''' (coerce_d_to_p M w (mu M w v p)) H5
                (extend_v M w' w'' H3 (extend_v M w w' l v))))). intro. apply extend_v_A_same. 
    apply H7 with (w''0 := u) (w'0 := w''').
  (* Case Eq tau tau *)
    intros. simpl. apply equiv_refl.
  (* Case Eq tau1 tau2 -> Eq tau2 tau1 *)
    intros. simpl. apply equiv_symm. 
    simpl in H0. apply H0. assumption.
  (* Case Eq tau1 tau2 -> Eq tau2 tau3 -> Eq tau1 tau3 *)
    intros. simpl. apply equiv_trans with (d' := mu M w v tau2).
    simpl in H0. apply H0. assumption.
    simpl in H2. apply H2. assumption.
  (* Case Eq Fun_t f taus Fun_t f taus' *)
    intros. simpl.
    destruct f.
    apply ind_F. rewrite H. apply equiv_listD_refl.
  (* Case taus = taus' -> M w v |= Relf r taus -> M w v |= Relf r taus' *)
    intros. rewrite <- H. apply H1. apply H2.
  (* Case says tau2 speaksfor tau1 tau2 -> speaksfor tau1 tau2 *)
    intros. apply <- handoff_iff.
    apply H0. exact H1.
  (* Speaksfor tau1 tau2 -> tau1 says phi -> tau2 says phi *)
    intros; simpl; intros.
    assert (models M w v (Speaksfor tau1 tau2)).
      apply H0. assumption.
    simpl in H4.
    assert (restricted_A M (coerce_d_to_p M w (mu M w v tau1)) w w' w'').
      assert (restricted_A M (coerce_d_to_p M w (mu M w v tau2)) w w' w''). split.
        assert (w' = w'). trivial. exists (lte M _ w w' w' l (eqw M _ w' w' H5)). trivial. split.
        assert (w'' = w''). trivial. assert (A M (coerce_d_to_p M w (mu M w v tau2)) w' w''). apply A_P_Eq with (p := coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) tau2)). apply p_Eq_symm; apply mu_pi_same. assumption.
        exists (lte M _ w w'' w' l (ltp M _ w' w'' w'' H6 (eqw M _ w'' w'' H5))). trivial.
        apply A_P_Eq with (p := coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) tau2)). apply p_Eq_symm; apply mu_pi_same; assumption. assumption.
      apply H4. assumption.
    assert (models M w v (Says tau1 phi0)). apply H2; assumption.
    simpl in H6.
    assert (A M (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) tau1)) w' w'').
      unfold restricted_A in H5. decompose [and] H5. apply A_P_Eq with (p := coerce_d_to_p M w (mu M w v tau1)). apply mu_pi_same. assumption.
    apply models_v_d_Eq with (v := (extend_v_A M w' w''
                                    (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) tau1)) H7
                                    (extend_v M w w' l v))). 
    apply extend_v_A_same.
    apply H6.
   
  (* Case Speaksfor tau tau *)
    simpl; intros. assumption.
  (* Case Speaksfor tau1 tau2 -> Speaksfor tau2 tau3 -> Speaksfor tau1 tau3 *)
    simpl; intros. apply H0. assumption. apply H2; assumption.
Qed.

End Theorems.
