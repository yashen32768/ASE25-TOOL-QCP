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

(*----- Function get_pre -----*)

Definition get_pre_safety_wit_1 := 
forall (t_pre: Z) (tr: tree) (t_right: Z) (t_left: Z) (l0: tree) (t_value: Z) (r0: tree) (t_key: Z) ,
  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (t_key) (t_value) (r0))) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t_pre)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
  **  (store_tree t_right r0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition get_pre_return_wit_1 := 
forall (t_pre: Z) (tr: tree) (tr_ret_right: tree) (t_right: Z) (t_left: Z) (l0: tree) (t_value: Z) (r0: tree) (t_key: Z) ,
  [| (t_right = 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (t_key) (t_value) (r0))) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t_pre)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
  **  (store_tree t_right r0 )
|--
  EX (retval_left: Z)  (retval_right: Z)  (pt: partial_tree)  (tr_ret_left: tree)  (retval_key: Z)  (retval_value: Z) ,
  [| (t_pre <> 0) |] 
  &&  [| forall (tr_ret_right: tree) , ((tree_pre_merge (tr) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right))))) |] 
  &&  [| (retval_right = 0) |] 
  &&  [| (INT_MIN <= retval_key) |] 
  &&  [| (retval_key <= INT_MAX) |]
  &&  ((&((t_pre)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((t_pre)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((t_pre)  # "tree" ->ₛ "right")) # Ptr  |-> retval_right)
  **  ((&((t_pre)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt t_pre t_pre pt )
.

Definition get_pre_return_wit_2 := 
forall (t_pre: Z) (tr: tree) (tr_ret_right: tree) (t_right: Z) (t_left: Z) (l0: tree) (t_value: Z) (r0: tree) (t_key: Z) (retval_left_2: Z) (retval_right_2: Z) (pt_2: partial_tree) (tr_ret_left_2: tree) (retval_key_2: Z) (retval_value_2: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| forall (tr_ret_right: tree) , ((tree_pre_merge (r0) (tr_ret_right)) = (combine_tree (pt_2) ((make_tree (tr_ret_left_2) (retval_key_2) (retval_value_2) (tr_ret_right))))) |] 
  &&  [| (retval_right_2 = 0) |] 
  &&  [| (INT_MIN <= retval_key_2) |] 
  &&  [| (retval_key_2 <= INT_MAX) |] 
  &&  [| (t_right <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (t_key) (t_value) (r0))) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value_2)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key_2)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> retval_right_2)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left_2)
  **  (store_tree retval_left_2 tr_ret_left_2 )
  **  (store_pt retval t_right pt_2 )
  **  ((&((t_pre)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t_pre)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
|--
  EX (retval_left: Z)  (retval_right: Z)  (pt: partial_tree)  (tr_ret_left: tree)  (retval_key: Z)  (retval_value: Z) ,
  [| (retval <> 0) |] 
  &&  [| forall (tr_ret_right: tree) , ((tree_pre_merge (tr) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right))))) |] 
  &&  [| (retval_right = 0) |] 
  &&  [| (INT_MIN <= retval_key) |] 
  &&  [| (retval_key <= INT_MAX) |]
  &&  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> retval_right)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt retval t_pre pt )
.

Definition get_pre_partial_solve_wit_1_pure := 
forall (t_pre: Z) (tr: tree) ,
  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  (store_tree t_pre tr )
|--
  [| (t_pre <> 0) |]
.

Definition get_pre_partial_solve_wit_1_aux := 
forall (t_pre: Z) (tr: tree) ,
  [| (t_pre <> 0) |]
  &&  (store_tree t_pre tr )
|--
  [| (t_pre <> 0) |] 
  &&  [| (t_pre <> 0) |]
  &&  (store_tree t_pre tr )
.

Definition get_pre_partial_solve_wit_1 := get_pre_partial_solve_wit_1_pure -> get_pre_partial_solve_wit_1_aux.

Definition get_pre_partial_solve_wit_2_pure := 
forall (t_pre: Z) (tr: tree) (t_right: Z) (t_left: Z) (l0: tree) (t_value: Z) (r0: tree) (t_key: Z) ,
  [| (t_right <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (t_key) (t_value) (r0))) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((&((t_pre)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t_pre)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
  **  (store_tree t_right r0 )
|--
  [| (t_right <> 0) |]
.

Definition get_pre_partial_solve_wit_2_aux := 
forall (t_pre: Z) (tr: tree) (t_right: Z) (t_left: Z) (l0: tree) (t_value: Z) (r0: tree) (t_key: Z) ,
  [| (t_right <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (t_key) (t_value) (r0))) |] 
  &&  [| (t_pre <> 0) |]
  &&  ((&((t_pre)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t_pre)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
  **  (store_tree t_right r0 )
|--
  [| (t_right <> 0) |] 
  &&  [| (t_right <> 0) |] 
  &&  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (t_key) (t_value) (r0))) |] 
  &&  [| (t_pre <> 0) |]
  &&  (store_tree t_right r0 )
  **  ((&((t_pre)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t_pre)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t_pre)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t_pre)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
.

Definition get_pre_partial_solve_wit_2 := get_pre_partial_solve_wit_2_pure -> get_pre_partial_solve_wit_2_aux.

Definition get_pre_which_implies_wit_1 := 
forall (tr: tree) (t: Z) ,
  [| (t <> 0) |]
  &&  (store_tree t tr )
|--
  EX (t_right: Z)  (t_left: Z)  (l0: tree)  (t_value: Z)  (r0: tree)  (t_key: Z) ,
  [| (INT_MIN <= t_key) |] 
  &&  [| (t_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (t_key) (t_value) (r0))) |]
  &&  ((&((t)  # "tree" ->ₛ "key")) # Int  |-> t_key)
  **  ((&((t)  # "tree" ->ₛ "value")) # Int  |-> t_value)
  **  ((&((t)  # "tree" ->ₛ "left")) # Ptr  |-> t_left)
  **  (store_tree t_left l0 )
  **  ((&((t)  # "tree" ->ₛ "right")) # Ptr  |-> t_right)
  **  (store_tree t_right r0 )
.

(*----- Function delete -----*)

Definition delete_safety_wit_1 := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) ,
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "p" ) )) # Ptr  |-> b_pre_v)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v tr )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition delete_safety_wit_2 := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> p_key)
  **  ((( &( "p" ) )) # Ptr  |-> b_pre_v)
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((b_pre) # Ptr  |-> b_pre_v)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition delete_safety_wit_3 := 
forall (tr_ret_right: tree) (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) (retval_left: Z) (retval_right: Z) (pt: partial_tree) (tr_ret_left: tree) (retval_key: Z) (retval_value: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| forall (tr_ret_right: tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right))))) |] 
  &&  [| (retval_right = 0) |] 
  &&  [| (INT_MIN <= retval_key) |] 
  &&  [| (retval_key <= INT_MAX) |] 
  &&  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt retval p_left pt )
  **  ((( &( "pre" ) )) # Ptr  |-> retval)
  **  ((( &( "y" ) )) # Int  |-> p_key)
  **  ((( &( "p" ) )) # Ptr  |-> b_pre_v)
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((b_pre) # Ptr  |-> b_pre_v)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition delete_return_wit_1 := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v_2: Z) ,
  [| (b_pre_v_2 = 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((b_pre) # Ptr  |-> b_pre_v_2)
  **  (store_tree b_pre_v_2 tr )
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete (x_pre) (tr)) )
.

Definition delete_return_wit_2_1 := 
forall (tr_ret_right: tree) (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v_2: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) (retval_left: Z) (retval_right: Z) (pt: partial_tree) (tr_ret_left: tree) (retval_key: Z) (retval_value: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| forall (tr_ret_right: tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right))))) |] 
  &&  [| (retval_right = 0) |] 
  &&  [| (INT_MIN <= retval_key) |] 
  &&  [| (retval_key <= INT_MAX) |] 
  &&  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v_2 <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt retval p_left pt )
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> p_left)
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete (x_pre) (tr)) )
.

Definition delete_return_wit_2_2 := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v_2: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (p_left = 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v_2 <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_tree p_left l0 )
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> p_right)
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete (x_pre) (tr)) )
.

Definition delete_return_wit_2_3 := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v_3: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) (b_pre_v_2: Z) ,
  [| (x_pre > p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v_3 <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v_3)  # "tree" ->ₛ "right")) # Ptr  |-> b_pre_v_2)
  **  (store_tree b_pre_v_2 (tree_delete (x_pre) (r0)) )
  **  ((&((b_pre_v_3)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v_3)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v_3)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((b_pre) # Ptr  |-> b_pre_v_3)
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete (x_pre) (tr)) )
.

Definition delete_return_wit_2_4 := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v_3: Z) (p_right: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) (b_pre_v_2: Z) ,
  [| (x_pre < p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v_3 <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v_3)  # "tree" ->ₛ "left")) # Ptr  |-> b_pre_v_2)
  **  (store_tree b_pre_v_2 (tree_delete (x_pre) (l0)) )
  **  ((&((b_pre_v_3)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v_3)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v_3)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> b_pre_v_3)
|--
  EX (b_pre_v: Z) ,
  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v (tree_delete (x_pre) (tr)) )
.

Definition delete_partial_solve_wit_1_pure := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) ,
  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "p" ) )) # Ptr  |-> b_pre_v)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v tr )
|--
  [| (b_pre_v <> 0) |]
.

Definition delete_partial_solve_wit_1_aux := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) ,
  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((b_pre) # Ptr  |-> b_pre_v)
  **  (store_tree b_pre_v tr )
|--
  [| (b_pre_v <> 0) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_tree b_pre_v tr )
  **  ((b_pre) # Ptr  |-> b_pre_v)
.

Definition delete_partial_solve_wit_1 := delete_partial_solve_wit_1_pure -> delete_partial_solve_wit_1_aux.

Definition delete_partial_solve_wit_2_pure := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (x_pre < p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> p_key)
  **  ((( &( "p" ) )) # Ptr  |-> b_pre_v)
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((b_pre) # Ptr  |-> b_pre_v)
|--
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
.

Definition delete_partial_solve_wit_2_aux := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (x_pre < p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> b_pre_v)
|--
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (x_pre < p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> b_pre_v)
.

Definition delete_partial_solve_wit_2 := delete_partial_solve_wit_2_pure -> delete_partial_solve_wit_2_aux.

Definition delete_partial_solve_wit_3_pure := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (x_pre > p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> p_key)
  **  ((( &( "p" ) )) # Ptr  |-> b_pre_v)
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((b_pre) # Ptr  |-> b_pre_v)
|--
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
.

Definition delete_partial_solve_wit_3_aux := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (x_pre > p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> b_pre_v)
|--
  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (x_pre > p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((b_pre) # Ptr  |-> b_pre_v)
.

Definition delete_partial_solve_wit_3 := delete_partial_solve_wit_3_pure -> delete_partial_solve_wit_3_aux.

Definition delete_partial_solve_wit_4 := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (p_left = 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> p_right)
|--
  [| (p_left = 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_left l0 )
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> p_right)
.

Definition delete_partial_solve_wit_5_pure := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "pre" ) )) # Ptr  |->_)
  **  ((( &( "y" ) )) # Int  |-> p_key)
  **  ((( &( "p" ) )) # Ptr  |-> b_pre_v)
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((b_pre) # Ptr  |-> b_pre_v)
|--
  [| (p_left <> 0) |]
.

Definition delete_partial_solve_wit_5_aux := 
forall (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) ,
  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> b_pre_v)
|--
  [| (p_left <> 0) |] 
  &&  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  (store_tree p_left l0 )
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> b_pre_v)
.

Definition delete_partial_solve_wit_5 := delete_partial_solve_wit_5_pure -> delete_partial_solve_wit_5_aux.

Definition delete_partial_solve_wit_6 := 
forall (tr_ret_right: tree) (x_pre: Z) (b_pre: Z) (tr: tree) (b_pre_v: Z) (p_right: Z) (p_left: Z) (l0: tree) (p_value: Z) (r0: tree) (p_key: Z) (retval_left: Z) (retval_right: Z) (pt: partial_tree) (tr_ret_left: tree) (retval_key: Z) (retval_value: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| forall (tr_ret_right: tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right))))) |] 
  &&  [| (retval_right = 0) |] 
  &&  [| (INT_MIN <= retval_key) |] 
  &&  [| (retval_key <= INT_MAX) |] 
  &&  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt retval p_left pt )
  **  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> 0)
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> p_left)
|--
  [| (retval <> 0) |] 
  &&  [| forall (tr_ret_right: tree) , ((tree_pre_merge (l0) (tr_ret_right)) = (combine_tree (pt) ((make_tree (tr_ret_left) (retval_key) (retval_value) (tr_ret_right))))) |] 
  &&  [| (retval_right = 0) |] 
  &&  [| (INT_MIN <= retval_key) |] 
  &&  [| (retval_key <= INT_MAX) |] 
  &&  [| (p_left <> 0) |] 
  &&  [| (x_pre <= p_key) |] 
  &&  [| (x_pre >= p_key) |] 
  &&  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |] 
  &&  [| (b_pre_v <> 0) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((&((b_pre_v)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((b_pre_v)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((b_pre_v)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  ((&((b_pre_v)  # "tree" ->ₛ "right")) # Ptr  |-> 0)
  **  ((&((retval)  # "tree" ->ₛ "value")) # Int  |-> retval_value)
  **  ((&((retval)  # "tree" ->ₛ "key")) # Int  |-> retval_key)
  **  ((&((retval)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  ((&((retval)  # "tree" ->ₛ "left")) # Ptr  |-> retval_left)
  **  (store_tree retval_left tr_ret_left )
  **  (store_pt retval p_left pt )
  **  (store_tree p_right r0 )
  **  ((b_pre) # Ptr  |-> p_left)
.

Definition delete_which_implies_wit_1 := 
forall (tr: tree) (p: Z) ,
  [| (p <> 0) |]
  &&  (store_tree p tr )
|--
  EX (p_right: Z)  (p_left: Z)  (l0: tree)  (p_value: Z)  (r0: tree)  (p_key: Z) ,
  [| (INT_MIN <= p_key) |] 
  &&  [| (p_key <= INT_MAX) |] 
  &&  [| (tr = (make_tree (l0) (p_key) (p_value) (r0))) |]
  &&  ((&((p)  # "tree" ->ₛ "key")) # Int  |-> p_key)
  **  ((&((p)  # "tree" ->ₛ "value")) # Int  |-> p_value)
  **  ((&((p)  # "tree" ->ₛ "left")) # Ptr  |-> p_left)
  **  (store_tree p_left l0 )
  **  ((&((p)  # "tree" ->ₛ "right")) # Ptr  |-> p_right)
  **  (store_tree p_right r0 )
.

Definition delete_derive_high_level_spec_by_low_level_spec := 
forall (x_pre: Z) (b_pre: Z) (m: mapping) ,
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
  **  (store_tree b_pre_v_4 (tree_delete (x_pre) (tr)) ))
  -*
  (EX b_pre_v_2,
  ((b_pre) # Ptr  |-> b_pre_v_2)
  **  (store_map b_pre_v_2 (map_delete (x_pre) (m)) )))
.

Module Type VC_Correct.

Include bst_Strategy_Correct.
Include common_Strategy_Correct.

Axiom proof_of_get_pre_safety_wit_1 : get_pre_safety_wit_1.
Axiom proof_of_get_pre_return_wit_1 : get_pre_return_wit_1.
Axiom proof_of_get_pre_return_wit_2 : get_pre_return_wit_2.
Axiom proof_of_get_pre_partial_solve_wit_1_pure : get_pre_partial_solve_wit_1_pure.
Axiom proof_of_get_pre_partial_solve_wit_1 : get_pre_partial_solve_wit_1.
Axiom proof_of_get_pre_partial_solve_wit_2_pure : get_pre_partial_solve_wit_2_pure.
Axiom proof_of_get_pre_partial_solve_wit_2 : get_pre_partial_solve_wit_2.
Axiom proof_of_get_pre_which_implies_wit_1 : get_pre_which_implies_wit_1.
Axiom proof_of_delete_safety_wit_1 : delete_safety_wit_1.
Axiom proof_of_delete_safety_wit_2 : delete_safety_wit_2.
Axiom proof_of_delete_safety_wit_3 : delete_safety_wit_3.
Axiom proof_of_delete_return_wit_1 : delete_return_wit_1.
Axiom proof_of_delete_return_wit_2_1 : delete_return_wit_2_1.
Axiom proof_of_delete_return_wit_2_2 : delete_return_wit_2_2.
Axiom proof_of_delete_return_wit_2_3 : delete_return_wit_2_3.
Axiom proof_of_delete_return_wit_2_4 : delete_return_wit_2_4.
Axiom proof_of_delete_partial_solve_wit_1_pure : delete_partial_solve_wit_1_pure.
Axiom proof_of_delete_partial_solve_wit_1 : delete_partial_solve_wit_1.
Axiom proof_of_delete_partial_solve_wit_2_pure : delete_partial_solve_wit_2_pure.
Axiom proof_of_delete_partial_solve_wit_2 : delete_partial_solve_wit_2.
Axiom proof_of_delete_partial_solve_wit_3_pure : delete_partial_solve_wit_3_pure.
Axiom proof_of_delete_partial_solve_wit_3 : delete_partial_solve_wit_3.
Axiom proof_of_delete_partial_solve_wit_4 : delete_partial_solve_wit_4.
Axiom proof_of_delete_partial_solve_wit_5_pure : delete_partial_solve_wit_5_pure.
Axiom proof_of_delete_partial_solve_wit_5 : delete_partial_solve_wit_5.
Axiom proof_of_delete_partial_solve_wit_6 : delete_partial_solve_wit_6.
Axiom proof_of_delete_which_implies_wit_1 : delete_which_implies_wit_1.
Axiom proof_of_delete_derive_high_level_spec_by_low_level_spec : delete_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
