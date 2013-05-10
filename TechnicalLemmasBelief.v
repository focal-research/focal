Section TechnicalLemmasBelief.

Require Import Syntax.
Require Import ProofSystem.
Require Import Belief.

Axiom function_same : forall (A B : Set) (f g : A -> B),
  (forall (a : A), f a = g a) -> f = g. 

Axiom B_replacement : forall (B : belief_model) (w : B_W B) 
                             (v : var -> D (B_s B w)) (x : var) 
                             (d : D (B_s B w)) (phi : formula),
  is_true(notfree_in_formula x phi) 
  -> (B_models B w v phi <-> B_models B w (B_subst_map B w v x d) phi).

Axiom B_replacement_term : forall (B : belief_model) (w : B_W B) 
                                  (v : var -> D (B_s B w)) (x : var) 
                                  (d : D (B_s B w)) (tau : term),
  is_true(notfree_in_term x tau) -> 
  ((B_mu B w v tau) = (B_mu B w (B_subst_map B w v x d) tau)).


Axiom B_pushback_subst : forall (B : belief_model) (w : B_W B) 
                                (v : var -> D (B_s B w)) (x : var) 
                                (tau : term) (phi : formula),
  (B_models B w (B_subst_map B w v x (B_mu B w v tau)) phi) 
  <-> (B_models B w v (subst x tau phi)).

Axiom B_models_v_same : forall (B : belief_model) (w : B_W B) 
                               (v v' : var -> D (B_s B w)) (phi : formula), 
  (forall (y : var), d_Eq (B_s B w) (v y) (v' y)) 
  -> (B_models B w v phi <-> B_models B w v' phi).

Axiom B_mu_same : forall (B : belief_model) (w w' : B_W B) (l : B_lt B w w')
                       (v : var -> D (B_s B w)) (tau : term), 
  d_Eq (B_s B w') (B_extend_d_lt B w w' l (B_mu B w v tau)) 
                (B_mu B w' (B_extend_v B w w' l v) tau).

(* This can't be proven right now because of how we handle subsets. 
   However, it is provable in pencil-and-paper. *)
Axiom B_mu_pi_same : forall (B : belief_model) (w w' : B_W B) (l : B_lt B w w')
                          (v : var -> D (B_s B w)) (tau : term),
  B_p_Eq B (B_coerce_d_to_p B w (B_mu B w v tau))
           (B_coerce_d_to_p B w' (B_mu B w' (B_extend_v B w w' l v) tau)).

Theorem B_modelsAll_all_modeled : forall (B : belief_model) (w : B_W B) 
                                     (v : var -> D (B_s B w)) 
                                     (Gamma : list formula)(phi : formula),
  B_modelsAll B w v Gamma -> In phi Gamma -> B_models B w v phi.

Proof.
  intros; induction Gamma as [| phi' Gamma'].
  inversion H0.
  simpl in H0; destruct H0.
  simpl in H. 
  rewrite <- H0; apply H.
  assert (B_modelsAll B w v Gamma').
    simpl in H; apply H.
  apply IHGamma'.
  apply H1. apply H0.
Qed.

Theorem B_false_models_all : forall (B : belief_model) (w : B_W B)
                                    (v : var -> D (B_s B w)),
  B_models B w v FocalFalse -> forall (phi : formula), B_models B w v phi.
Proof.
  intros.
  simpl in H; inversion H.
Qed.

Lemma B_pushback : forall (B : belief_model) (w : B_W B)
                          (v : var -> D (B_s B w))
                          (Gamma : list formula) (phi : formula),
  B_modelsAll B w v Gamma -> B_models B w v phi 
  -> B_modelsAll B w v (phi :: Gamma).
Proof.
  intros. simpl; split. exact H0. exact H.
Qed.

Lemma B_model_v_same : forall (B : belief_model) (w : B_W B) 
                              (v v' : var -> D (B_s B w)), 
  (forall v1 : var, v v1 = v' v1)
  -> forall phi: formula, 
       B_models B w v phi <-> B_models B w v' phi.
Proof.
  intros. assert (v = v'). apply function_same. exact H.
  split; intros. rewrite <- H0. exact H1.
  rewrite H0. exact H1.
Qed.

Lemma B_modelsAll_v_same : forall (B : belief_model) (w : B_W B) 
                              (v v' : var -> D (B_s B w)), 
  (forall v1 : var, v v1 = v' v1)
  -> forall Gamma: list formula, 
       B_modelsAll B w v Gamma <-> B_modelsAll B w v' Gamma.
Proof.
  intros. assert (v = v'). apply function_same. exact H.
  split; intros. rewrite <- H0. exact H1.
  rewrite H0. exact H1.
Qed.

Theorem B_replace_all : forall (B : belief_model) (w : B_W B) 
                               (v : var -> D (B_s B w)) (x : var) 
                               (d : D (B_s B w)) (Gamma : list formula),
  is_true(notfree x Gamma) -> 
   (B_modelsAll B w v Gamma <-> B_modelsAll B w (B_subst_map B w v x d) Gamma).
Proof.
  intros.
  split.
  intro.
  induction Gamma as [| phi Gamma'].
  (* Case Gamma = nil *)
  simpl; trivial.
  (* Case Gamma = phi :: Gamma' *)
  simpl; simpl in H0. split.
  apply B_replacement. 
  simpl in H. unfold andb in H. destruct (notfree_in_formula x phi).
  unfold is_true. trivial. 
  inversion H. (* We assume something is true, it can't be false. *)
  apply H0.
  apply IHGamma'. (* Apply the inductive hypothesis. *)
  simpl in H. destruct (notfree x Gamma').
  unfold is_true. trivial.
  unfold andb in H. destruct (notfree_in_formula x phi); inversion H. apply H0.
  intro; induction Gamma as [| phi Gamma'].
  (* Case Gamma = nil *)
  simpl; trivial.
  (* Case Gamma = phi :: Gamma' *)
  simpl; simpl in H0. split.
  apply B_replacement with (d := d) (x := x).
  simpl in H. unfold andb in H. destruct (notfree_in_formula x phi).
  unfold is_true; trivial.
  inversion H.
  apply H0.
  apply IHGamma'.
  simpl in H. unfold andb in H. destruct (notfree_in_formula x phi).
  exact H.
  inversion H.
  apply H0.
Qed.

Theorem B_extend_v_idempotent : forall (B : belief_model) (w w' w'' : B_W B) 
                                       (v : var -> D (B_s B w)) (l : B_lt B w w')
                                       (l' : B_lt B w' w'') (l'' : B_lt B w w'')
                                       (v1 : var), 
  (B_extend_v B w' w'' l' (B_extend_v B w w' l v) v1) 
  = (B_extend_v B w w'' l'' v) v1.
Proof.
  intro; repeat unfold B_extend_v. intros.
  rewrite B_extend_d_lt_idempotent with (l'' := l''). trivial.
Qed.

Theorem B_extend_v_self : forall (B : belief_model) (w : B_W B)
                                 (v : var -> D (B_s B w)) (l : B_lt B w w)
                                 (v1 : var),
  v v1 = B_extend_v B w w l v v1.
Proof.
  intros.
  unfold B_extend_v. symmetry; apply B_extend_d_once.
Qed.

Theorem B_relativize_as_box : forall (B : belief_model) (w : B_W B)
                                   (v : var -> D (B_s B w))
                                   (Gamma : list formula) (tau : term),
  B_modelsAll B w v (relativize tau Gamma) 
  -> forall (phi : formula), In phi Gamma ->
       B_worldview B (B_coerce_d_to_p B w (B_mu B w v tau)) w v phi.
Proof.
  intros. induction Gamma as [|phi' Gamma'].
  inversion H0.
  simpl in H0; destruct H0.
  simpl in H. rewrite <- H0. apply H.
  apply IHGamma'. simpl in H; apply H. exact H0.
Qed.

Theorem worldview_transparant_relativize : forall (B: belief_model) (w : B_W B)
                                                  (v : var -> D (B_s B w))
                                                  (Gamma : list formula) 
                                                  (tau : term),
  B_modelsAll B w v (relativize tau Gamma) 
  <-> B_modelsAll B w v (relativize tau (relativize tau Gamma)).
Proof.
  intros. induction Gamma as [| phi' Gamma'].
  simpl. split; intro; trivial.
  simpl. split; split. rewrite <- B_worldview_transparent. apply H.
  rewrite <- IHGamma'. apply H.
  rewrite B_worldview_transparent. apply H.
  rewrite IHGamma'. apply H.
Qed.

Theorem B_p_eq_refl : forall (B : belief_model) (p : B_P B),
  B_p_Eq B p p.
Proof.
  intros; unfold B_p_Eq. intros.
  apply equiv_refl.
Qed.

Theorem B_p_eq_symm : forall (B : belief_model) (p p' : B_P B),
  B_p_Eq B p p' -> B_p_Eq B p' p.
Proof.
  intros; unfold B_p_Eq; intros.
  apply equiv_symm. unfold B_p_Eq in H. apply H.
Qed.

Theorem B_p_eq_trans : forall (B : belief_model) (p p' p'' : B_P B),
  B_p_Eq B p p' -> B_p_Eq B p' p'' -> B_p_Eq B p p''.
Proof.
  intros; unfold B_p_Eq; intros.
  unfold B_p_Eq in H; unfold B_p_Eq in H0.
  apply equiv_trans with (d' := B_coerce_p_to_d B w p'). apply H. apply H0.
Qed.

Theorem B_p_eq_equivalent : forall (B: belief_model) (p p' : B_P B),
                            B_p_Eq B p p' <-> 
                            exists w : B_W B, 
                              d_Eq (B_s B w) 
                               (B_coerce_p_to_d B w p) 
                               (B_coerce_p_to_d B w p').
Proof.
  intros. split; intro.
  unfold B_p_Eq in H. assert (exists w : B_W B, True). apply B_non_empty.
  destruct H0 as [w]; clear H0.
  exists w. apply H.
  destruct H as [w].
  assert (B_p_Eq B (B_coerce_d_to_p B w (B_coerce_p_to_d B w p)) 
                   (B_coerce_d_to_p B w (B_coerce_p_to_d B w p'))). 
    apply B_coerce_d_respects. exact H.
  apply B_p_eq_trans with (p' := B_coerce_d_to_p B w (B_coerce_p_to_d B w p)).
  apply B_p_eq_symm. apply B_coerce_d_inverse.
  apply B_p_eq_trans with (p' := B_coerce_d_to_p B w (B_coerce_p_to_d B w p')).
  exact H0. apply B_coerce_d_inverse.
Qed.


Lemma B_equiv_list_ext : forall (B : belief_model) (w w' : B_W B) 
                                (l : list term) (v : var -> D (B_s B w)) 
                                (ltww : B_lt B w w'),
  equiv_listD (B_s B w') (map (B_extend_d_lt B w w' ltww) (map (B_mu B w v) l)) 
                       (map (B_mu B w' (B_extend_v B w w' ltww v)) l).
Proof.
  intros; induction l.
  simpl; trivial.
  simpl; split.
  apply B_mu_same.
  exact IHl.
Qed.

Lemma notfree_for_all : forall (x : var) (Gamma : list formula),
  is_true (notfree x Gamma) <-> forall psi : formula, In psi Gamma -> is_true (notfree_in_formula x psi).
Proof.
  split; intros. unfold is_true.
  unfold is_true in H; unfold notfree in H.
  induction Gamma.
  simpl in H0. inversion H0.
  simpl in H. simpl in H0. destruct H0.
  rewrite <- H0. unfold andb in H. destruct (notfree_in_formula x a).
  trivial. inversion H.
  apply IHGamma. unfold andb in H. destruct (notfree_in_formula x a). 
  exact H. inversion H. exact H0.
  unfold notfree. induction Gamma. simpl. unfold is_true; trivial.
  simpl. unfold is_true; unfold andb.
  assert (is_true (notfree_in_formula x a)). apply H. simpl; left; trivial.
  destruct (notfree_in_formula x a).
  apply IHGamma. intros. apply H. simpl. right; exact H1. exact H0.
Qed.

End TechnicalLemmasBelief.

  