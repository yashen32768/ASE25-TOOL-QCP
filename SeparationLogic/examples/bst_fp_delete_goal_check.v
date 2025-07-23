From SimpleC.EE Require Import bst_fp_delete_goal bst_fp_delete_proof_auto bst_fp_delete_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include bst_fp_strategy_proof.
  Include bst_fp_delete_proof_auto.
  Include bst_fp_delete_proof_manual.
End VC_Correctness.
