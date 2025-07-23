struct list {
   void* data;
   struct list *next;
};

/*@ Extern Coq (sll : {A} -> (Z -> A -> Assertion) -> Z-> list A -> Assertion)
               (sllseg: {A} -> (Z -> A -> Assertion) -> Z -> Z -> list A -> Assertion)
               (sll_para: {A} -> (Z -> A -> Assertion) -> Prop)
 */

/*@ Import Coq Require Import poly_sll_lib */

/*@ include strategies "poly_sll.strategies" */