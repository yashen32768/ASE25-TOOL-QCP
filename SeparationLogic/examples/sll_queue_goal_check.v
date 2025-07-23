From SimpleC.EE Require Import sll_queue_goal sll_queue_proof_auto sll_queue_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include sll_strategy_proof.
  Include sll_queue_strategy_proof.
  Include sll_queue_proof_auto.
  Include sll_queue_proof_manual.
End VC_Correctness.
