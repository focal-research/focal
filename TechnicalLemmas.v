Section TechnicalLemmas.

Require Import Syntax.
Require Import Model.
Require Import ProofSystem.
Require Import Setoid.
Require Import Classical.

(**********************************************************************************************************************)
(* Some techinical lemmas that should be true. These have not been proven in Coq yet, but some do have a paper and    *)
(*                                              pencil proof.                                                         *)    
(* Some are actually not provable in Coq because we cannnot define mu and models as inductive. This is because they   *)
(*                are mutually recursive, yet one is of sort Set while the other is of sort Prop.                     *)
(**********************************************************************************************************************)

(*
This allows us to treat functions as set-theoretic, as far as equality is concerned. This makes sense, given that we are trying to model a set-theoretic model.
*)
Axiom function_same : forall (A B : Set) (f g : A -> B), (forall a : A, f a = g a) -> f = g.

(*
This says that it shouldn't matter whether we extend v, and then interpret a term, or if we interpret the term, and then extend that.
Should be provable by induction over mu, which is sadly impossible in the current code.
*)
Axiom mu_same : forall (M : focal_model) (w w' : W M) (l : lt M w w') (v : var -> D (s M w)) (tau : term), 
  d_Eq (s M w') (extend_d_lt M w w' l (mu M w v tau)) (mu M w' (extend_v M w w' l v) tau).

(* 
This tells us that if we have a formula without x free in it, then we can make x map to anything in our valuation function.
Should be provable by induction over derivations of models.
*)
Axiom replacement : forall (M : focal_model) (w : W M) (v : var -> D (s M w)) (x : var) (d : D (s M w)) (phi : formula),
  is_true(notfree_in_formula x phi) -> (models M w v phi <-> models M w (subst_map M w v x d) phi).

(*
This tells us that we can substitute for any non-free variable in the valuation function, and it won't affect mu.
Should be provable by induction over mu.
*)
Axiom replacement_term : forall (M : focal_model) (w : W M) (v : var -> D (s M w)) (x : var) (d : D (s M w)) (tau : term),
                           is_true(notfree_in_term x tau) -> ((mu M w v tau) = (mu M w (subst_map M w v x d) tau)).

(* 
Substituting in the valuation function and in the formula does the same thing. 
Again, provable by induction over derivations of models.
*)
Axiom pushback_subst : forall (M : focal_model) (w : W M) (v : var -> D (s M w)) (x : var) (tau : term) (phi : formula),
  (models M w (subst_map M w v x (mu M w v tau)) phi) <-> (models M w v (subst x tau phi)). 


(*
This tells us that we can either extend v by p, then interpret a term; or we can interpret the term, then extend by p', as long as p' and p are equivalent.
*)
Axiom interpret_extend_A : forall (M : focal_model) (w w' : W M) (p p' : P M) (a : A M p w w') (a' : A M p' w w') (tau : term) (v : var -> D (s M w)),
                             p_Eq M p p' -> d_Eq (s M w') (mu M w' (extend_v_A M w w' p a v) tau) (extend_d_A M w w' p' a' (mu M w v tau)).

(*
This says that we can use two D-equivalent valuation functions and we should get the same results from models.
*)
Axiom models_v_d_Eq : forall (M : focal_model) (w : W M) (v v' : var -> D (s M w)) (phi : formula), (forall (y : var), d_Eq (s M w) (v y) (v' y)) -> (models M w v phi <-> models M w v' phi).

(*
This says that it doesn't matter if we extend a valuation function that has a substitution or if we extend the element that is getting substituted in and the valuation function that it is gettting substituted in.
*)
Axiom extend_v_subst : forall (M : focal_model) (w w' : W M) (l : lt M w w') (v : var -> D (s M w)) (x : var) (d : D (s M w)) (variable : var), 
(extend_v M w w' l (subst_map M w v x d) variable) = (subst_map M w' (extend_v M w w' l v) x (extend_d_lt M w w' l d) variable).


(* 
The following two axioms are provable on pencil-and-paper by induction over
tau and by using monotonicity. 
They allow us to move up in worlds without changing our principal.
*)
Axiom mu_pi_same : forall (M : focal_model) (w w' : W M) (v : var -> D (s M w)) 
                          (l : lt M w w') (tau : term),
                     p_Eq M 
                          (coerce_d_to_p M w (mu M w v tau)) 
                          (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) tau)).

Axiom mu_pi_same_A : forall (M : focal_model) (w w' : W M) (v : var -> D (s M w))
                            (p : P M) (a : A M p w w') (tau : term),
                       p_Eq M
                            (coerce_d_to_p M w (mu M w v tau))
                            (coerce_d_to_p M w' (mu M w' (extend_v_A M w w' p a v) tau)).


(**********************************************************************************************************************)
(* Some Lemmas, defitions, and Ltac related to connected proofs. These are used extensively below, but nowhere else   *)
(*                                                     in the code.                                                   *)
(**********************************************************************************************************************)

(*
Ltac to deal with the common cases in connections.
*)
Ltac connected :=
  repeat match goal with
           | [|- ?W = ?W ] => trivial
           | [|- True] => trivial
           | [H : True |- _] => clear H
           | [H : connected _ _ _ _ |- _ ] => destruct H
           | [H : connection ?M ?P ?W ?U |- connected ?M ?P ?W ?U] => exists H; trivial
           | [H : ?W = ?U |- connected ?M ?P ?W ?U ] => exists (eqw M P W U H); trivial
           | [|- (connected ?M ?P ?W ?W)] => assert (W = W)
           | [H : lt ?M ?W ?U, H0 : connection ?M ?P ?U ?V |- connected ?M ?P ?W ?V ] => exists (lte M P W V U H H0); trivial
           | [H : A ?M ?P ?W ?U, H0 : connection ?M ?P ?U ?V |- connected ?M ?P ?W ?V ] => exists (ltp M P W V U H H0); trivial
           | [H : lt ?M ?U ?W, H0 : connection ?M ?P ?U ?V |- connected ?M ?P ?W ?V ] => exists (gte M P W V U H H0); trivial
           | [H : A ?M ?P ?U ?W, H0 : connection ?M ?P ?U ?V |- connected ?M ?P ?W ?V ] => exists (gtp M P W V U H H0); trivial
           | [H : connection ?M ?P ?W ?U |- connected ?M ?P ?U ?W ] => exists (con_symm M P U W H); trivial
           | [H : connection ?M ?P ?W ?U, H0 : connection ?M ?P ?U ?V |- connected ?M ?P ?W ?V ] => exists (con_trans M P W V U H H0); trivial
           | [H : ?W = ?U |- connected ?M ?P ?V ?U ] => assert (connected M P U U); connected
           | [H : ?W = ?U |- connected ?M ?P ?V ?W ] => assert (connected M P W W); connected
   end.

(*
Connections without the explicit symmetry and transitivity. Used in some proofs where the simplar structure is necessary.
Later, we prove that the this is equivalent to the origifocal connection.
*)
Inductive connection' (M : focal_model) (p : P M) (w w' : W M) : Set :=
  | eqw' : w = w' -> connection' M p w w'
  | lte' : forall w'' : W M, lt M w w'' -> connection' M p w'' w' -> connection' M p w w'
  | ltp' : forall w'' : W M, A M p w w'' -> connection' M p w'' w' -> connection' M p w w'
  | gte' : forall w'' : W M, lt M w'' w -> connection' M p w'' w' -> connection' M p w w'
  | gtp' : forall w'' : W M, A M p w'' w -> connection' M p w'' w' -> connection' M p w w'.

(*
A definiton of connected, with connection's instead of connections.
*)
Definition connected' (M : focal_model) (p : P M) (w w' : W M) : Prop := exists c : connection' M p w w', True.

(*
Ltac for dealing with connected'. Based on the connected Ltac above.
*)
Ltac connected' :=
  repeat match goal with
           | [|- ?W = ?W ] => trivial
           | [|- True] => trivial
           | [H : True |- _] => clear H
           | [H : connected' _ _ _ _ |- _ ] => destruct H
           | [H : connection' ?M ?P ?W ?U |- connected' ?M ?P ?W ?U] => exists H; trivial
           | [H : ?W = ?U |- connected' ?M ?P ?W ?U ] => exists (eqw' M P W U H); trivial
           | [|- (connected' ?M ?P ?W ?W)] => assert (W = W)
           | [H : lt ?M ?W ?U, H0 : connection' ?M ?P ?U ?V |- connected' ?M ?P ?W ?V ] => exists (lte' M P W V U H H0); trivial
           | [H : A ?M ?P ?W ?U, H0 : connection' ?M ?P ?U ?V |- connected' ?M ?P ?W ?V ] => exists (ltp' M P W V U H H0); trivial
           | [H : lt ?M ?U ?W, H0 : connection' ?M ?P ?U ?V |- connected' ?M ?P ?W ?V ] => exists (gte' M P W V U H H0); trivial
           | [H : A ?M ?P ?U ?W, H0 : connection' ?M ?P ?U ?V |- connected' ?M ?P ?W ?V ] => exists (gtp' M P W V U H H0); trivial
           | [H : ?W = ?U |- connected' ?M ?P ?V ?U ] => assert (connected' M P U U); connected'
           | [H : ?W = ?U |- connected' ?M ?P ?V ?W ] => assert (connected' M P W W); connected'
   end.

(* 
Reflexivity of connected'. 
*)
Lemma connected'_refl : forall (M : focal_model) (p : P M) (w : W M), connected' M p w w.
Proof.
  intros. assert (w = w). trivial. exists (eqw' M p w w H). trivial.
Qed.

(*
Transitivity of connected'. This is used in the proof of symmetry, interestingly enough.
*)
Lemma connected'_trans : forall (M : focal_model) (p : P M) (w w' w'': W M), 
                           connected' M p w w' -> connected' M p w' w'' -> connected' M p w w''.
Proof.
  intros.
  connected'.
  induction x0; connected'.
  rewrite e. connected'.
  assert (connected' M p w''0 w''). apply IHx0. exact x. connected'. 
  assert (connected' M p w''0 w''). apply IHx0. exact x. connected'. 
  assert (connected' M p w''0 w''). apply IHx0. exact x. connected'. 
  assert (connected' M p w''0 w''). apply IHx0. exact x. connected'. 
Qed.

(*
Symmetry of connected'. Note the use of transitivity.
*)
Lemma connected'_symm : forall (M : focal_model) (p : P M) (w w' : W M),
                          connected' M p w w' -> connected' M p w' w.
Proof.
  intros.
  connected'; induction x.
  assert (w' = w). symmetry; exact e. exists (eqw' M p w' w H). trivial.
  assert (connected' M p w'' w). assert (w = w). trivial. exists (gte' M p w'' w w l (eqw' M p w w H)). trivial.
    apply connected'_trans with (w' := w''). exact IHx. exact H.
  assert (connected' M p w'' w). assert (w = w). trivial. exists (gtp' M p w'' w w a (eqw' M p w w H)). trivial.
    apply connected'_trans with (w' := w''). exact IHx. exact H.
  apply connected'_trans with (w' := w''). exact IHx. assert (w = w). trivial. exists (lte' M p w'' w w l (eqw' M p w w H)). trivial.
  apply connected'_trans with (w' := w''). exact IHx. assert (w =w ). trivial. exists (ltp' M p w'' w w a (eqw' M p w w H)). trivial.
Qed.

(*
Equivalence of connected and connected'.
*)
Theorem connected_connected' : forall (M : focal_model) (p : P M) (w w' : W M),
                                 connected M p w w' <-> connected' M p w w'.
Proof.
  split; intros.
  destruct H; clear H. induction x; connected'.
    apply connected'_symm. exists x0. trivial.
    apply connected'_trans with (w' := w''). exists x0. trivial. exists x. trivial.
  destruct H; clear H. induction x; connected.
Qed.


(**********************************************************************************************************************)
(*               The next three lemmas prove that the connected relation is an equivalence relation.                  *)
(**********************************************************************************************************************)

(*
Reflexivity
*)
Lemma connected_refl : forall (M : focal_model) (p : P M), reflexive _ (connected M p).
Proof.
  unfold reflexive; intros. assert (x = x). trivial. connected.
Qed.

(*
Symmetry
*)
Lemma connected_symm : forall (M : focal_model) (p : P M), symmetric _ (connected M p).
Proof.
  unfold symmetric; intros. connected. 
Qed.

(*
Transitivity
*)
Lemma connected_trans : forall (M : focal_model) (p : P M), transitive _ (connected M p).
Proof. 
  unfold transitive; intros. connected.
Qed.
(**********************************************************************************************************************)
(*              The next three lemmas prove that the equiv_listD relation is an equivalence relation.                 *)
(**********************************************************************************************************************)

(*
Reflexivity
*)
Theorem equiv_listD_refl : forall (M : fo_model), reflexive _ (equiv_listD M).
Proof.
  unfold reflexive; intros.
  induction x as [| d x'].
  (* x = nil *)
  simpl. trivial.
  (* x = d :: x' *)
  simpl. split.
  (* Part d_Eq M d d *)
  reflexivity.
  (* Part equiv_listD M x' x' *)
  apply IHx'.
Qed.

(*
Symmetry
*)
Theorem equiv_listD_symm : forall (M : fo_model), symmetric _ (equiv_listD M).
Proof.
  unfold symmetric; intros.
  generalize dependent x.
  induction y.
  induction x.
  intros. simpl. trivial.
  intros. simpl. contradiction.
  intros. induction x.
  simpl. contradiction.
  simpl. simpl in H. split.
  apply equiv_symm. apply H. apply IHy. apply H.
Qed.

(*
This allows us to do induction on three lists simultaneously. It is only used in the below proof of transitivity.
*)
Lemma list_triple_ind : forall (A : Set) (P : list A -> list A -> list A -> Prop),
                          P nil nil nil ->
                          (forall (l : list A), P nil nil l) -> 
                          (forall (l : list A), P nil l nil) ->
                          (forall (l : list A), P l nil nil) ->
                          (forall (a b : A) (l1 l2 : list A), P nil l1 l2 -> P nil (a :: l1) (b :: l2)) ->
                          (forall (a b : A) (l1 l2 : list A), P l1 nil l2 -> P (a :: l1) nil (b :: l2)) ->
                          (forall (a b : A) (l1 l2 : list A), P l1 l2 nil -> P (a :: l1) (b :: l2) nil) ->
                          (forall (a b c : A) (l1 l2 l3 : list A), P l1 l2 l3 -> P (a :: l1) (b :: l2) (c :: l3)) ->
                          forall (l1 l2 l3: list A), P l1 l2 l3.
Proof.
  induction l1.
  induction l2.
  auto.
  induction l3; auto.
  induction l2; induction l3; auto.
Qed.


(*
Transitivity
*)
Theorem equiv_listD_trans : forall (M : fo_model), transitive _ (equiv_listD M).
Proof.
  unfold transitive; intros.
  apply (list_triple_ind (D M) (fun x y z => equiv_listD M x y -> equiv_listD M y z -> equiv_listD M x z)) with (l1 := x) (l2 := y) (l3 := z); auto.
  intros; simpl; tauto.
  intros. simpl in H3. inversion H3.
  intros. simpl in H1; simpl in H2; simpl in H3; simpl.
  split.
  transitivity b. apply H2. apply H3.
  apply H1. apply H2. apply H3.
Qed.

(**********************************************************************************************************************)
(*                  The next three lemmas prove that the p_Eq relation is an equivalence relation.                    *)
(**********************************************************************************************************************)

(*
Reflexivity 
*)
Theorem p_Eq_refl : forall (M : focal_model) (p1 : P M),
                      p_Eq M p1 p1.
Proof.
  intros.
  unfold p_Eq.
  intros. reflexivity.
Qed.

(*
Symmetry
*)
Theorem p_Eq_symm : forall (M : focal_model) (p1 p2 : P M),
                      p_Eq M p1 p2 -> p_Eq M p2 p1.
Proof.
  intros. unfold p_Eq. intros.
  unfold p_Eq in H. apply equiv_symm. apply H.
Qed.

(*
Transitivity
*)
Theorem p_Eq_trans : forall (M : focal_model) (p1 p2 p3 : P M),
                       p_Eq M p1 p2 -> p_Eq M p2 p3 -> p_Eq M p1 p3.
Proof.
  intros; unfold p_Eq; intros.
  transitivity (coerce_p_to_d M w p2).
  unfold p_Eq in H; apply H.
  unfold p_Eq in H0; apply H0.
Qed.

(**********************************************************************************************************************)
(*                   Some technical lemmas that we have proven to be true, at least modulo the above.                 *)
(**********************************************************************************************************************)

Lemma extend_v_self : forall (M : focal_model) (w : W M) (l : lt M w w)
                             (v : var -> D (s M w)) (x : var),
                        v x = extend_v M w w l v x.
Proof.
  intros; unfold extend_v.
  rewrite extend_d_once. trivial.
Qed.

(* 
This tells us that, since var_dec x x is always true, if var_dec x x then a else b will always evaluate to a. 
Proof due to Adam Chilpala on the Coq-club mailing list.
*)
Lemma var_dec_if : forall (x : var) (A : Set) (a b : A), (if var_dec x x then a else b) = a.
Proof.
  intros.
  destruct (var_dec x x); tauto.
Qed.  

(*
This allows us to rebuild a $\Sigma$ type from it's projections.
Proof due to Adam Chilpala on the Coq-club mailing list.
*)
Lemma proj1_proj2_exist : forall (A : Set) (Q : A -> Prop) (b : {a : A | Q a}), b = exist Q (proj1_sig b) (proj2_sig b).
Proof.
  destruct b. reflexivity.
Qed.

(*
This says that two maps are equivalent if they start from the same base, and then substitute equivalent things for the same variable.
*)
Lemma subst_map_d_Eq : forall (M : focal_model) (w : W M) (v : var -> D (s M w)) (d d' : D (s M w)) (x : var),
                           d_Eq (s M w) d d' -> forall (y : var), d_Eq (s M w) (subst_map M w v x d y) (subst_map M w v x d' y).
Proof.
  intros. 
  assert ({x = y} + {x <> y}). apply var_dec. destruct H0.
  unfold subst_map. rewrite e. rewrite var_dec_if. rewrite var_dec_if. exact H.
  unfold subst_map. destruct (var_dec y x). exact H.
  reflexivity.
Qed.

(*
This says that two maps are equivalent if they start from equivalent bases, then substitute the same thing for the same variable.
*)
Lemma subst_map_v_Eq : forall (M : focal_model) (w : W M) (v v' : var -> D (s M w)) (d : D (s M w)) (x : var),
                         (forall y : var, d_Eq (s M w) (v y) (v' y)) ->
                         forall (y : var), d_Eq (s M w) (subst_map M w v x d y) (subst_map M w v' x d y).
Proof.
  intros.
  unfold subst_map. destruct (var_dec y x). reflexivity.
  apply H.
Qed.

(*
This says that, if we have two equal evaluation functions, then it doesn't matter which one we use in models.
*)
Lemma model_v_same : forall (M : focal_model) (w : W M) (v v' : var -> D (s M w)), 
                       (forall v1 : var, v v1 = v' v1) -> forall phi: formula, (models M w v phi) <-> models M w v' phi.
Proof.
  intros. assert (v = v'). apply function_same; assumption. 
  split; intros.  rewrite <- H0. assumption.
  rewrite H0. assumption.
Qed.

(*
This says that, if we have two equal evaluation function, it doesn't matter which one we use in mu.
*)
Lemma mu_v_same : forall (M : focal_model) (w : W M) (v v' : var -> D (s M w)), 
                    (forall v1 : var, v v1 = v' v1) -> forall tau : term, mu M w v tau = mu M w v' tau.
Proof.
  intros. assert (v = v'). apply function_same; assumption.
  rewrite H0. trivial.
Qed.

(*
This generalizes replacement to a list of formulas.
*)
Theorem replacement_all :forall (M : focal_model) (w : W M) (v : var -> D (s M w)) (x : var) (d : D (s M w)) (Gamma : list formula),
                           (forall (phi : formula), In phi Gamma -> is_true(notfree_in_formula x phi)) -> (modelsAll M w v Gamma <-> modelsAll M w (subst_map M w v x d) Gamma).
Proof.
  intros. induction Gamma. simpl. split; intros; trivial.
  split; intros. simpl. simpl in H0. decompose [and] H0. split.
  apply replacement. apply H. simpl. left; trivial. exact H1.
  apply IHGamma. intros. apply H. simpl. right; exact H3. exact H2.
  simpl. simpl in H0. decompose [and] H0. split.
  apply <- replacement. exact H1.
  apply H. simpl. left; trivial.
  apply <- IHGamma. exact H2.
  intros; apply H. simpl. right. exact H3.
Qed.

(*
If p and p' are equivalent, it doesn't matter which we use for the connected relation.
*)
Theorem connected_P_Eq : forall (M : focal_model) (p p' : P M) (w w' : W M),
                           p_Eq M p p' -> connected M p w w' -> connected M p' w w'.
Proof.
  intros.
  destruct H0. clear H0.
  induction x; connected. 
  assert (A M p' w w''). apply A_P_Eq with (p := p) (p' := p'); assumption.
  connected.
  assert (A M p' w'' w). apply A_P_Eq with (p := p) (p' := p'); assumption. 
  connected.
Qed.

(*
If two worlds are connected, then if two worlds are on restricted_A p w, then they are on restricted_A p w'.
*)
Theorem connected_restricted' : forall (M : focal_model) (p : P M) (w w' u u' : W M), 
                                  connected M p w w' -> restricted_A M p w u u' -> restricted_A M p w' u u'.
Proof.
  intros. unfold restricted_A. unfold restricted_A in H0. decompose[and] H0.
  split.
  (* connected M p w' u *)
  connected.
  assert (connected M p w' w). connected.
  connected.
  split.
  assert (connected M p w' w). connected.
  connected.
  (* A M p u u' *)
  assumption.
Qed.

(*
Generalizes the above to be <-> instead of ->.
*)
Theorem connected_restricted : forall (M : focal_model) (p : P M) (w w' u u' : W M), 
                                 connected M p w w' -> (restricted_A M p w u u' <-> restricted_A M p w' u u').
Proof.
  intros. split.
  intros. apply connected_restricted' with (w := w); assumption.
  apply connected_restricted' with (w := w'). connected.
Qed.

(*
If p and p' are equivalent, then two worlds are on restricted_A of one if they are on the restricted_A of the other.
*)
Theorem restricted_A_P_Eq : forall (M : focal_model) (p p' : P M) (w w' w'' : W M),
                              p_Eq M p p' -> restricted_A M p w w' w'' ->
                              restricted_A M p' w w' w''.
Proof.
  intros.
  unfold restricted_A in H0. decompose [and] H0.
  unfold restricted_A. split.
  apply connected_P_Eq with (p := p); assumption.
  split. apply connected_P_Eq with (p := p); assumption. 
  apply A_P_Eq with (p := p); assumption.
Qed.



(* 
This generalizes the previous lemma about replacement to sets (lists) of formulas. 
*)
Theorem replace_all : forall (M : focal_model) (w : W M) (v : var -> D (s M w)) (x : var) (d : D (s M w)) (Gamma : list formula),
                        is_true(notfree x Gamma) -> (modelsAll M w v Gamma <-> modelsAll M w (subst_map M w v x d) Gamma).
Proof.
  intros.
  split.
  intro.
  induction Gamma as [| phi Gamma'].
  (* Case Gamma = nil *)
  simpl; trivial.
  (* Case Gamma = phi :: Gamma' *)
  simpl; simpl in H0. split.
  apply replacement. 
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
  apply replacement with (d := d) (x := x).
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

(* 
We can use relativize p Gamma as if it were p says Gamma 
*)
Theorem relativize_as_box : forall (M : focal_model) (w : W M) (v : var -> D (s M w)) (Gamma : list formula) (p : term), 
                              modelsAll M w v (relativize p Gamma) <-> 
                              forall (w' w'' : W M) (l : lt M w w') (a : A M (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p)) w' w''),
                                modelsAll M w'' (extend_v_A M w' w'' (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) p)) a (extend_v M w w' l v)) Gamma.
Proof.
  split.
  intros.
  induction Gamma as [| phi Gamma'].
  simpl; trivial.
  simpl. split. simpl in H. apply H.
  apply IHGamma'. simpl in H. apply H.
  intros. induction Gamma as [| phi Gamma'].
  simpl; trivial.
  simpl. split. 
  simpl in H. intros; apply H.
  apply IHGamma'. simpl in H. intros; apply H.
Qed.

(* 
If a list of formulas are all modeled, then each formula is modeled individually.
*)
Lemma modelsAll_all_modeled : forall (M : focal_model) (w : W M) (v : var -> D (s M w)) (Gamma : list formula),
                                modelsAll M w v Gamma -> forall (phi : formula), In phi Gamma -> models M w v phi.
Proof.
  intros M w v Gamma.
  induction Gamma as [| phi' Gamma'].
  (* Case Gamma = nil *)
  intros. inversion H0.
  (* Case Gamma = phi' :: Gamma' *)
  unfold modelsAll.
  unfold In. intros.
  induction H0.
  (* Case phi = phi' *)
  rewrite <- H0. apply H.
  (* Case phi \in Gamma' *)
  apply IHGamma'. apply H. apply H0.
Qed.

(* 
If a world models false, the world models anything. 
*)
Lemma false_models_all : forall (M : focal_model) (w : W M) (v : var -> D (s M w)),
                           models M w v FocalFalse -> forall phi : formula, models M w v phi.
Proof.
  intros.
  inversion H.
Qed.

(* 
If a world models all of a list Gamma, and the world models phi, then the world models phi::Gamma.
*)
Lemma pushback : forall (M : focal_model) (w : W M) (v : var -> D(s M w)) 
                        (Gamma : list formula) (phi : formula),
                   modelsAll M w v Gamma -> models M w v phi 
                   -> modelsAll M w v (phi :: Gamma).
Proof.
  intros. induction Gamma as [| psi Gamma'].
  (* Case Gamma = nil *)
  simpl. auto.
  (* Case Gamma = psi :: Gamma' *)
  unfold modelsAll. fold modelsAll. split.
  apply H0. 
  split.
  unfold modelsAll in H. fold modelsAll in H. apply H.
  unfold modelsAll in H. fold modelsAll in H. apply H.
Qed.

(* 
The same list interpreted in a world and extended, or interpreted in the extended world, and it is equivalent.
*)
Lemma equiv_list_ext : forall (M : focal_model) (w w' : W M) (l : list term) (v : var -> D (s M w)) (ltww : lt M w w'),
                         equiv_listD (s M w') (map (extend_d_lt M w w' ltww) (map (mu M w v) l)) (map (mu M w' (extend_v M w w' ltww v)) l).
Proof.
  intros.
  induction l as [| tau l'].
  (* Case nil *)
  simpl. trivial.
  (* Case tau :: l' *)
  simpl. split.
  (* part mu M w v tau  = mu M w' v tau *)
  apply mu_same.
  (* part equiv_list map mu w l map mu w' l *)
  apply IHl'.
Qed.

(*
We can extend v twice, or we can extend once.
*)
Lemma extend_v_idempotent : forall (M : focal_model) (w w' w'' : W M) (v : var -> D (s M w)) (l : lt M w w') (l' : lt M w' w'') (l'' : lt M w w'') (v1 : var), (extend_v M w' w'' l' (extend_v M w w' l v) v1) = (extend_v M w w'' l'' v) v1.
Proof.
  intro; repeat unfold extend_v. intros.
  rewrite extend_d_lt_idempotent with  (l'' := l''). trivial.
Qed.

(*
It doesn't matter which principal we use to get from one world to another, extending a valuation function always gives the same result.
*)
Lemma extend_v_A_same : forall (M : focal_model) (w w' : W M) (v : var -> D (s M w)) (p p' : P M) (a : A M p w w') (a' : A M p' w w') (v1 : var),
                          d_Eq (s M w') (extend_v_A M w w' p a v v1) (extend_v_A M w w' p' a' v v1).
Proof.
  intros. unfold extend_v_A. apply extend_d_A_same.
Qed.

(*
Extends model_v_same to lists of formulas.
*)
Lemma modelsAll_v_same : forall (M : focal_model) (w : W M) (v v' : var -> D (s M w)), (forall v1 : var, v v1 = v' v1) -> forall Gamma : list formula, modelsAll M w v Gamma <-> modelsAll M w v' Gamma.
Proof.
  intros.
  unfold modelsAll.
  split.
  (* -> *)
  induction Gamma.
  (* Gamma = nil *)
  trivial.
  (* Gamma = a :: Gamma *)
  fold modelsAll in IHGamma.
  intros.
  split.
  (* M w v' ||- a *)
  rewrite model_v_same with (v' := v). apply H0. symmetry. apply H.
  (* M w v' ||- Gamma *)
  fold modelsAll; fold modelsAll in H0. apply IHGamma. apply H0.
  (* <- *)
  induction Gamma; fold modelsAll; intros.
  (* Gamma = nil *)
  trivial.
  (* Gamma = a :: Gamma *)
  split. 
  (* M w v ||- a *)
  rewrite model_v_same with (v' := v'). apply H0. apply H.
  (* M w v ||- Gamma *)
  fold modelsAll in IHGamma. apply IHGamma. apply H0.
Qed.

(*
Extends models_v_d_Eq to lists of formulas.
*)
Lemma modelsAll_d_Eq : forall (M : focal_model) (w : W M) (v v' : var -> D (s M w)) (Gamma : list formula),
                         (forall (y : var), d_Eq (s M w) (v y) (v' y)) -> (modelsAll M w v Gamma <-> modelsAll M w v' Gamma).
Proof.
  intros; split; intro.
  induction Gamma as [| psi Gamma'].
  simpl. trivial.
  simpl in H0. simpl. decompose [and] H0. split.
  apply models_v_d_Eq with (v := v); assumption. 
  apply IHGamma'. assumption.
  induction Gamma as [| psi Gamma'].
  simpl; trivial.
  simpl; simpl in H0; decompose [and] H0. split.
  apply models_v_d_Eq with (v := v'). intro. symmetry. generalize y. exact H. exact H1.
  apply IHGamma'. exact H2.
Qed.

(*
If a principal q has an accessiblity relation that is a subset of the accessiblity relation p, then their connected relations have the same relationship.
*)
Lemma A_subset_connected_subset : forall (M : focal_model) (p q : P M),
                                    (forall w u : W M, A M p w u -> A M q w u) ->
                                    forall w u : W M, connected M p w u -> connected M q w u.
Proof.
  intros; connected.
  induction x; connected.
  assert (A M q w w''). apply H. exact a. connected.
  assert (A M q w'' w). apply H. exact a. connected.
Qed.

(*
If two worlds are connected according to a principal, then they have the same restricted relation.
*)
Lemma connected_connected : forall (M : focal_model) (p : P M) (w w' : W M),
                              connected M p w w' -> forall u u' : W M, restricted_A M p w u u' <-> restricted_A M p w' u u'.
Proof.
  split; intros.
  unfold restricted_A in H0. decompose [and] H0. unfold restricted_A. split.
  assert (connected M p w' w). connected. connected. split.
  assert (connected M p w' w). connected. connected.
  exact H4.
  unfold restricted_A in H0. decompose [and] H0. unfold restricted_A. split; [connected | split; [connected | exact H4]].
Qed.

(*
If one principal has a restricted connection (on a world w) that is a superset of the other, then it judges a superset of worlds to be connected to w.
*)
Lemma restricted_restricts_connected : forall (M : focal_model) (p q : P M) (w : W M),
                                         (forall u u' : W M, restricted_A M p w u u' -> restricted_A M q w u u') ->
                                         forall u : W M, connected M p w u -> connected M q w u.
Proof.
  intros. 
  apply <- connected_connected'.
  assert (connected' M p w u). apply connected_connected'. exact H0.
  connected'. induction x; connected'.
  assert (connected' M q w'' w'). apply IHx. intros.
  apply connected_connected with (w := w). assert (w'' = w''). trivial. connected.
  apply H. apply connected_connected with (w := w'').  assert (w = w). trivial. connected. exact H1.
  apply <- connected_connected'. connected'.
  connected'.
  assert (connected' M q w'' w'). apply IHx. intros.
  apply connected_connected with (w := w). assert (A M q w w''). assert (restricted_A M q w w w''). apply H.
  unfold restricted_A. split. connected. split; [connected | exact a]. assert (w'' = w''). trivial. exists (ltp M p w w'' w'' a (eqw M p w'' w'' H0)). trivial.
  unfold restricted_A in H2. apply H2. assert (w'' = w''). trivial. connected.
  apply H. apply connected_connected with (w := w''). assert (w = w). trivial. connected. exact H1.
  connected. assert (A M q w w''). assert (restricted_A M q w w w''). apply H. unfold restricted_A. split; [connected | split]. assert (w'' = w''). trivial. connected. exact a.
  unfold restricted_A in H2. apply H2.
  connected'.
  assert (connected' M q w'' w'). apply IHx. intros.
  apply connected_connected with (w := w). assert (w'' = w''). trivial. connected.
  apply H. apply connected_connected with (w := w''). assert (w = w). trivial. connected. exact H1.
  apply connected_connected'. connected'.
  connected'.
  assert (A M q w'' w). assert (restricted_A M q w w'' w). apply H. unfold restricted_A. 
  split; [connected | split]. assert (w'' = w''). trivial. connected. connected. exact a.
  unfold restricted_A in H1. apply H1.
  assert (connected' M q w'' w'). apply IHx. intros.
  apply connected_connected with (w := w). assert (w'' = w''). trivial. connected. apply H.
  apply connected_connected with (w := w''). assert (w = w). trivial. connected. exact H2.
  apply connected_connected'. connected'.
  connected'.
Qed.

Theorem p_Eq_equivalent : forall (M : focal_model) (p p' : P M),
                            p_Eq M p p' <-> exists w : W M, d_Eq (s M w) (coerce_p_to_d M w p) (coerce_p_to_d M w p').
Proof.
  intros. split; intro.
  unfold p_Eq in H. assert (exists w : W M, True). apply non_empty.
  destruct H0 as [w]; clear H0.
  exists w. apply H.
  destruct H as [w].
  assert (p_Eq M (coerce_d_to_p M w (coerce_p_to_d M w p)) (coerce_d_to_p M w (coerce_p_to_d M w p'))). apply coerce_d_respects. exact H.
  apply p_Eq_trans with (p2 := coerce_d_to_p M w (coerce_p_to_d M w p)).
  apply p_Eq_symm. apply coerce_d_inverse.
  apply p_Eq_trans with (p2 := coerce_d_to_p M w (coerce_p_to_d M w p')).
  exact H0. apply coerce_d_inverse.
Qed.

Theorem handoff_iff : forall (M : focal_model) (w : W M) (v : var -> D (s M w))
                             (tau tau' : term),
  models M w v (Speaksfor tau tau') <-> models M w v (Says tau' (Speaksfor tau tau')).
Proof.
intros; split. intro.
simpl. intros. simpl in H.
assert (p_Eq M (coerce_d_to_p M w'' 
                 (mu M w'' (extend_v_A M w' w'' 
                             (coerce_d_to_p M w' 
                               (mu M w' (extend_v M w w' l v) tau')) 
                             a (extend_v M w w' l v)) 
                 tau))
               (coerce_d_to_p M w
                 (mu M w v tau))).
  apply p_Eq_trans with (p2 := (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) tau))).
  apply p_Eq_symm. apply mu_pi_same_A.
  apply p_Eq_symm. apply mu_pi_same.
assert (restricted_A M (coerce_d_to_p M w'' (mu M w''
        (extend_v_A M w' w''
           (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) tau')) a
           (extend_v M w w' l v)) tau)) w w'0 w''0).
apply restricted_A_P_Eq with (p := coerce_d_to_p M w (mu M w v tau)).
apply p_Eq_symm. exact H1.
assert (restricted_A M (coerce_d_to_p M w (mu M w v tau')) w w'0 w''0).
apply restricted_A_P_Eq with (p := (coerce_d_to_p M w''
          (mu M w''
             (extend_v_A M w' w''
                (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) tau')) a
                (extend_v M w w' l v)) tau'))).
  apply p_Eq_trans with (p2 := (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) tau'))).
  apply p_Eq_symm. apply mu_pi_same_A.
  apply p_Eq_symm. apply mu_pi_same.
apply connected_connected with (w' := w'').
assert (A M (coerce_d_to_p M w (mu M w v tau')) w' w'').
  apply A_P_Eq with (p' := coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) tau')).
  apply mu_pi_same. exact a.
assert (w = w). trivial.
assert (connected M (coerce_d_to_p M w (mu M w v tau')) w w'').
unfold connected.
exists (con_symm M _ w w''
         (gtp M (coerce_d_to_p M w (mu M w v tau')) w'' w w' H2
           (gte M (coerce_d_to_p M w (mu M w v tau')) w' w w l
             (eqw M _ w w H3)))). trivial.
apply connected_P_Eq with (p := coerce_d_to_p M w (mu M w v tau')).
  apply p_Eq_trans with (p2 := (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) tau'))).
  apply mu_pi_same. apply mu_pi_same_A.
  exact H4.
exact H0.
apply H. exact H2.
apply connected_connected with (w' := w).
apply connected_P_Eq with (p := coerce_d_to_p M w (mu M w v tau)).
  apply p_Eq_trans with (p2 := (coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) tau))).
  apply mu_pi_same. apply mu_pi_same_A.
assert (restricted_A M (coerce_d_to_p M w (mu M w v tau)) w w' w'').
apply H. unfold restricted_A. split; [connected | split].
assert (A M (coerce_d_to_p M w (mu M w v tau')) w' w'').
  apply A_P_Eq with (p' := coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) tau')).
  apply mu_pi_same. exact a.
unfold connected.
assert (w' = w'). trivial.
exists (lte M _ w w' w' l (eqw M _ w' w' H4)). trivial.
unfold connected.
assert (w = w). trivial.
assert (A M (coerce_d_to_p M w (mu M w v tau')) w' w'').
  apply A_P_Eq with (p' := coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) tau')).
  apply mu_pi_same. exact a.
exists (con_symm M _ w w''
         (gtp M _ w'' w w' H4
           (gte M _ w' w w l
             (eqw M _ w w H3)))). trivial.
apply A_P_Eq with (p' := coerce_d_to_p M w' (mu M w' (extend_v M w w' l v) tau')).
  apply mu_pi_same. exact a.
unfold connected.
unfold restricted_A in H3.
decompose [and] H3.
induction H6.
exists (con_symm M _ w'' w x). trivial.
exact H2.

(* <- *)

   simpl; intros.
    assert ((exists w' : W M, exists w'' : W M, lt M w w' /\ A M (coerce_d_to_p M w (mu M w v tau')) w' w'') \/ ~(exists w' : W M, exists w'' : W M, lt M w w' /\ A M (coerce_d_to_p M w (mu M w v tau')) w' w'')). apply classic.
    destruct H1. destruct H1 as [u]. destruct H1 as [u'].  decompose [and] H1.
    assert (restricted_A M (coerce_d_to_p M w (mu M w v tau)) u' w' w'').
      assert (A M (coerce_d_to_p M u (mu M u (extend_v M w u H2 v) tau')) u u').
        apply A_P_Eq with (p := (coerce_d_to_p M w (mu M w v tau'))). apply mu_pi_same. assumption.
      apply restricted_A_P_Eq with (p := (coerce_d_to_p M u'
            (mu M u'
               (extend_v_A M u u'
                  (coerce_d_to_p M u (mu M u (extend_v M w u H2 v) tau')) H4
                  (extend_v M w u H2 v)) tau))).
        apply p_Eq_trans with (p2 := (coerce_d_to_p M u (mu M u (extend_v M w u H2 v) tau))); apply p_Eq_symm.
        apply mu_pi_same_A. apply mu_pi_same.
        apply H.
        apply connected_restricted with (w := w). 
        assert (A M (coerce_d_to_p M u'
        (mu M u'
           (extend_v_A M u u'
              (coerce_d_to_p M u (mu M u (extend_v M w u H2 v) tau')) H4
              (extend_v M w u H2 v)) tau')) u u'). apply A_P_Eq with (p := (coerce_d_to_p M w (mu M w v tau'))). 
        apply p_Eq_trans with (p2 := coerce_d_to_p M u (mu M u (extend_v M w u H2 v) tau')).
        apply mu_pi_same. apply mu_pi_same_A.
        assumption.
        assert (u' = u'). trivial.
        exists (lte M (coerce_d_to_p M u' (mu M u' (extend_v_A M u u' (coerce_d_to_p M u (mu M u (extend_v M w u H2 v) tau')) H4 (extend_v M w u H2 v)) tau')) w u' u H2 (ltp M _ u u' u' H5 (eqw M _ u' u' H6))). trivial.
        apply restricted_A_P_Eq with (p := (coerce_d_to_p M w (mu M w v tau'))). 
        apply p_Eq_trans with (p2 := coerce_d_to_p M u (mu M u (extend_v M w u H2 v) tau')).
        apply mu_pi_same. apply mu_pi_same_A. assumption.
    apply connected_restricted with (w := u').
      assert (A M (coerce_d_to_p M w (mu M w v tau)) u u').
        assert (A M (coerce_d_to_p M u (mu M u (extend_v M w u H2 v) tau')) u u'). apply A_P_Eq with (p := (coerce_d_to_p M w (mu M w v tau'))). apply mu_pi_same. assumption.
        assert (restricted_A M (coerce_d_to_p M u' (mu M u' (extend_v_A M u u' (coerce_d_to_p M u (mu M u (extend_v M w u H2 v) tau')) H5 (extend_v M w u H2 v)) tau')) u' u u').
          apply restricted_A_P_Eq with (p := (coerce_d_to_p M u (mu M u (extend_v M w u H2 v) tau'))). 
          apply mu_pi_same_A. unfold restricted_A. split.
          assert (u = u). trivial.
          exists (gtp M _ u' u u H5 (eqw M _ u u H6)). trivial.
          split. assert (u' = u'). trivial. exists (eqw M _ u' u' H6). trivial.
          assumption.
        assert (restricted_A M (coerce_d_to_p M u' (mu M u' (extend_v_A M u u' (coerce_d_to_p M u (mu M u (extend_v M w u H2 v) tau')) H5 (extend_v M w u H2 v)) tau)) u' u u').
          apply H. assumption.
        unfold restricted_A in H7. decompose [and] H7. apply A_P_Eq with (p := (coerce_d_to_p M u'
             (mu M u'
                (extend_v_A M u u'
                   (coerce_d_to_p M u (mu M u (extend_v M w u H2 v) tau')) H5
                   (extend_v M w u H2 v)) tau))). 
        apply p_Eq_symm; apply p_Eq_trans with (p2 := coerce_d_to_p M u (mu M u (extend_v M w u H2 v) tau)).
        apply mu_pi_same. apply mu_pi_same_A. assumption.
        assert (u' = u'). trivial.
        exists (con_symm M _  u' w (lte M _ w u' u H2 (ltp M _ u u' u' H5 (eqw M _ u' u' H6)))). trivial. assumption.
        apply handoff_necc with (p := (coerce_d_to_p M w (mu M w v tau'))); assumption.
Qed.

End TechnicalLemmas.

Hint Resolve modelsAll_all_modeled false_models_all pushback equiv_list_ext extend_v_idempotent : Lemmas.

Hint Rewrite extend_v_idempotent : Lemmas.

Add Parametric Relation (M : fo_model) : (list (D M)) (@equiv_listD M)
    reflexivity proved by (equiv_listD_refl M)    
    symmetry proved by (equiv_listD_symm M)    
    transitivity proved by (equiv_listD_trans M)
      as LDE_rel.

Add Parametric Relation (M : focal_model) : (P M) (@p_Eq M)
    reflexivity proved by (p_Eq_refl M)
    symmetry proved by (p_Eq_symm M)
    transitivity proved by (p_Eq_trans M)
      as PE_rel.

Add Parametric Relation (M : focal_model) (p : P M) : (W M) (@connected M p)
    reflexivity proved by (connected_refl M p)
    symmetry proved by (connected_symm M p)
    transitivity proved by (connected_trans M p)
      as conn_rel.

Add Parametric Morphism (M : focal_model) (w : W M) : (@coerce_d_to_p M w) 
    with signature (@d_Eq (s M w)) ==> (@p_Eq M)
      as coerce_d_morph.
  intros. apply coerce_d_respects with (d := x) (d' := y) (M := M) (w := w). assumption.
Qed.

Add Parametric Morphism (M : focal_model) (w : W M) : (@coerce_p_to_d M w)
    with signature (@p_Eq M) ==> (@d_Eq (s M w))
      as coerce_p_morph.
  intros. apply coerce_p_respects. assumption.
Qed.

Add Parametric Morphism (M : focal_model) (w w' : W M) (l : lt M w w') : (@extend_d_lt M w w' l)
    with signature (@d_Eq (s M w)) ==> (@d_Eq (s M w'))
      as extend_d_lt_morph.
  intros. apply extend_d_lt_respects. assumption.
Qed.

Add Parametric Morphism (M : focal_model) (w w' : W M) (p : P M) (a : A M p w w') : (@extend_d_A M w w' p a)
    with signature (@d_Eq (s M w)) ==> (@d_Eq (s M w'))
      as extend_d_A_morph.
  intros. apply extend_d_A_respects. assumption.
Qed.
