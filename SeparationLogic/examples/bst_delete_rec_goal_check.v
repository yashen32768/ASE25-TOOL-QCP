From SimpleC.EE Require Import bst_delete_rec_goal bst_delete_rec_proof_auto bst_delete_rec_proof_manual.

Module VC_Correctness : VC_Correct.
  Include bst_strategy_proof.
  Include common_strategy_proof.
  Include bst_delete_rec_proof_auto.
  Include bst_delete_rec_proof_manual.
End VC_Correctness.
