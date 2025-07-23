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
From SimpleC.EE Require Import dll_queue_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import dll_queue_lib.
Local Open Scope sac.

Lemma proof_of_enqueue_safety_wit_1 : enqueue_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_enqueue_safety_wit_2 : enqueue_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_enqueue_safety_wit_3 : enqueue_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_enqueue_safety_wit_4 : enqueue_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_enqueue_partial_solve_wit_1 : enqueue_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_enqueue_partial_solve_wit_2 : enqueue_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_enqueue_partial_solve_wit_3_pure : enqueue_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_enqueue_partial_solve_wit_3 : enqueue_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_dequeue_safety_wit_1 : dequeue_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_dequeue_safety_wit_2 : dequeue_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_dequeue_safety_wit_3 : dequeue_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_dequeue_partial_solve_wit_1 : dequeue_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_dequeue_partial_solve_wit_2 : dequeue_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_dequeue_partial_solve_wit_3_pure : dequeue_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_dequeue_partial_solve_wit_3 : dequeue_partial_solve_wit_3.
Proof. Admitted. 

