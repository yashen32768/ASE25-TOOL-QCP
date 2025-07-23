Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import bst_lib.
Import get_right_most.
Import naive_C_Rules.
Local Open Scope sac.
Require Import bst_strategy_goal.
Require Import bst_strategy_proof.
Require Import common_strategy_goal.
Require Import common_strategy_proof.

(*----- Function insert -----*)

Definition insert_safety_wit_1 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) ,
  [| ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr))) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition insert_safety_wit_2 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) ,
  [| ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr))) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "p" ) )) # Ptr  |-> b_v)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition insert_safety_wit_3 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (b_v = 0) |] 
  &&  [| ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr))) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |->_)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition insert_safety_wit_4 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (b_v = 0) |] 
  &&  [| ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr))) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |->_)
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition insert_entail_wit_1 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) ,
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v tr )
|--
  EX (b_v: Z)  (pt0: partial_tree)  (tr0: tree) ,
  [| ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr))) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_ptb b_pre b_pre pt0 )
  **  ((b_pre) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
.

Definition insert_entail_wit_2_1 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (b_v_2: Z) (b: Z) (pt0_2: partial_tree) (tr0_2: tree) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (x_pre < p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr0_2 = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_v_2 <> 0) |] 
  &&  [| ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr))) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  (store_ptb b b_pre pt0_2 )
  **  ((b) # Ptr  |-> b_v_2)
|--
  EX (b_v: Z)  (pt0: partial_tree)  (tr0: tree) ,
  [| ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr))) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "left") b_pre pt0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
.

Definition insert_entail_wit_2_2 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (b_v_2: Z) (b: Z) (pt0_2: partial_tree) (tr0_2: tree) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (p_key < x_pre) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr0_2 = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_v_2 <> 0) |] 
  &&  [| ((combine_tree (pt0_2) ((tree_insert (x_pre) (value_pre) (tr0_2)))) = (tree_insert (x_pre) (value_pre) (tr))) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_v_2)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_v_2)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_v_2)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  (store_ptb b b_pre pt0_2 )
  **  ((b) # Ptr  |-> b_v_2)
|--
  EX (b_v: Z)  (pt0: partial_tree)  (tr0: tree) ,
  [| ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr))) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_ptb &((b_v_2)  # "tree" ->ₛ "right") b_pre pt0 )
  **  ((&((b_v_2)  # "tree" ->ₛ "right")) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
.

Definition insert_return_wit_1 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (b_v = 0) |] 
  &&  [| ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr))) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> x_pre)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> 0)
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> retval)
  **  (store_tree b_v tr0 )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_insert (x_pre) (value_pre) (tr)) )
.

Definition insert_return_wit_2 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (p_key >= x_pre) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr0 = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr))) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_v)  # "tree" ->ₛ "value")) # Int  |-> value_pre)
  **  ((&((b_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_insert (x_pre) (value_pre) (tr)) )
.

Definition insert_partial_solve_wit_1 := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) ,
  [| (b_v = 0) |] 
  &&  [| ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr))) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
|--
  [| (b_v = 0) |] 
  &&  [| ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr))) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
.

Definition insert_partial_solve_wit_2_pure := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) ,
  [| (b_v <> 0) |] 
  &&  [| ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr))) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "p" ) )) # Ptr  |-> b_v)
  **  ((( &( "b" ) )) # Ptr  |-> b)
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (b_v <> 0) |]
.

Definition insert_partial_solve_wit_2_aux := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (tr: tree) (b_v: Z) (b: Z) (pt0: partial_tree) (tr0: tree) ,
  [| (b_v <> 0) |] 
  &&  [| ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr))) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
  **  (store_tree b_v tr0 )
|--
  [| (b_v <> 0) |] 
  &&  [| (b_v <> 0) |] 
  &&  [| ((combine_tree (pt0) ((tree_insert (x_pre) (value_pre) (tr0)))) = (tree_insert (x_pre) (value_pre) (tr))) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_tree b_v tr0 )
  **  (store_ptb b b_pre pt0 )
  **  ((b) # Ptr  |-> b_v)
.

Definition insert_partial_solve_wit_2 := insert_partial_solve_wit_2_pure -> insert_partial_solve_wit_2_aux.

Definition insert_which_implies_wit_1 := 
forall (tr0: tree) (p: Z) ,
  [| (p <> 0) |]
  &&  (store_tree p tr0 )
|--
  EX (p_right: Z)  (p_left: Z)  (l0: tree)  (p_value: Z)  (r0: tree)  (p_key: Z) ,
  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr0 = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
.

Definition insert_derive_high_level_spec_by_low_level_spec := 
forall (value_pre: Z) (x_pre: Z) (b_pre: Z) (m: mapping) ,
  EX b_pre_v,
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_map b_pre_v m )
|--
EX (tr: tree) ,
  (EX b_pre_v_3,
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((b_pre) # Ptr  |-> b_pre_v_3)
  **  (store_tree b_pre_v_3 tr ))
  **
  ((EX b_pre_v_4,
  ((b_pre) # Ptr  |-> b_pre_v_4)
  **  (store_tree b_pre_v_4 (tree_insert (x_pre) (value_pre) (tr)) ))
  -*
  (EX b_pre_v_2,
  ((b_pre) # Ptr  |-> b_pre_v_2)
  **  (store_map b_pre_v_2 (map_insert (x_pre) (value_pre) (m)) )))
.

Module Type VC_Correct.

Include bst_Strategy_Correct.
Include common_Strategy_Correct.

Axiom proof_of_insert_safety_wit_1 : insert_safety_wit_1.
Axiom proof_of_insert_safety_wit_2 : insert_safety_wit_2.
Axiom proof_of_insert_safety_wit_3 : insert_safety_wit_3.
Axiom proof_of_insert_safety_wit_4 : insert_safety_wit_4.
Axiom proof_of_insert_entail_wit_1 : insert_entail_wit_1.
Axiom proof_of_insert_entail_wit_2_1 : insert_entail_wit_2_1.
Axiom proof_of_insert_entail_wit_2_2 : insert_entail_wit_2_2.
Axiom proof_of_insert_return_wit_1 : insert_return_wit_1.
Axiom proof_of_insert_return_wit_2 : insert_return_wit_2.
Axiom proof_of_insert_partial_solve_wit_1 : insert_partial_solve_wit_1.
Axiom proof_of_insert_partial_solve_wit_2_pure : insert_partial_solve_wit_2_pure.
Axiom proof_of_insert_partial_solve_wit_2 : insert_partial_solve_wit_2.
Axiom proof_of_insert_which_implies_wit_1 : insert_which_implies_wit_1.
Axiom proof_of_insert_derive_high_level_spec_by_low_level_spec : insert_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
