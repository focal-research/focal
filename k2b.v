Section k2b.
  
  Require Import Belief.
  Require Import Model.
  Require Import Syntax.

  Definition k2b (M : focale_model) : belief_model :=
   let wv p w v phi := forall tau : term, p_Eq M (coerce_d_to_p M w (mu M w v tau)) p ->
                                          models M w v (Says tau phi) in 
   Build_belief_model (W M) (lt M) (s M) (P M) wv (coerce_p_to_d M) (coerce_d_to_p M).


  (* This isn't going to be possible to prove: it requires induction on
   * the models relation, which we can't provide because of the sort problems
   * with models and mu. 
   *)
(*
  Theorem k2b_sound : forall (M : focale_model) (w : W M) 
                             (v : var -> D (s M w)) (phi : formula),
    models M w v phi -> B_models (k2b M) w v phi.
  Proof.
    intros. unfold k2b.
*)

End k2b.