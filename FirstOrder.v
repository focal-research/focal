
Section FirstOrder.
  Require Import Coq.Lists.List.
  Require Import Coq.Bool.Bool.
  Require Import Setoid.
  Require Import Coq.Arith.Peano_dec.


  (************************************************************************************)
  (*                           The first-order model.                                 *)
  (************************************************************************************)

Record fo_model : Type := {
                           D : Set;
                           d_Eq:  relation D; (* Equivalence of domain elements *)
                           R: nat -> (list D -> Prop); (* An ordered set of relations *)
                           F: nat -> (list D -> D); (* An ordered set of funnctions *)
                           m : nat -> nat; (* arity function for R; a list of (m n) length is given to (R n) *)
                           n : nat -> nat (* arity function for F *)
                         }.
  (************************************************************************************)
  (*                        Equiv is an equivalence relation.                         *)
 (************************************************************************************)

  (* Reflexivity of equiv *)
  Axiom equiv_refl : forall (M : fo_model) (d: D M), 
                       d_Eq M d d. 

  (* Symmetry of equiv *)
  Axiom equiv_symm : forall (M : fo_model) (d d' : D M), 
                       d_Eq M d d' -> d_Eq M d' d. 

  (* Transitivity of equiv *)
  Axiom equiv_trans : forall (M : fo_model) (d d' d'' : D M), 
                        d_Eq M d d' -> d_Eq M d' d'' -> d_Eq M d d''.





  (************************************************************************************)
  (*                   Equivalence of a list of domain elements.                      *)
  (************************************************************************************)

  Definition equiv_listD : forall (M : fo_model), relation (list (D M)).
    exact (fix el M ds ds' :  Prop := match ds with
      | nil => match ds' with
                 | x :: ds'' => False (* Length differs. *)
                 | nil => True (* Base case. *)
               end
      | x :: ds'' => match ds' with
                       | y :: ds''' => (d_Eq M x y) /\ el M ds'' ds'''
                       | _ => False (* Length differs. *)
                     end
    end).
  Defined.



  (************************************************************************************)
  (*                        Indistiguishability under Equiv                           *)
  (************************************************************************************)

  (* Indistinguishability for relations *)
  Axiom ind_R : forall (M : fo_model) (ds : list (D M)) (ds' : list (D M)) (i : nat),
                  equiv_listD M ds ds' (* if two lists are equivalent *)
                  -> (R M i ds) = (R M i ds'). (* then they are either both related by R i or not *)

  (* Indisitinguishability for functions *)
  Axiom ind_F : forall (M : fo_model) (ds :list (D M)) (ds' : list (D M)) (i : nat),
                  equiv_listD M ds ds' (* if two lists are equivalent *)
                  -> d_Eq M (F M i ds) (F M i ds'). (* then they both produce the same result from a function F *)

End FirstOrder.

  Add Parametric Relation (M : fo_model) : (D M) (@d_Eq M)
    reflexivity proved by (equiv_refl M)    
    symmetry proved by (equiv_symm M)    
    transitivity proved by (equiv_trans M)
  as DE_rel.
