struct list {
  int data;
  struct list *next;
  struct list *prev;
};

struct queue {
  struct list * head;
  struct list * tail;
};

/*@ Import Coq Require Import dll_queue_lib */

/*@ Extern Coq (store_queue : Z -> list Z -> Assertion)
               (dllseg: Z -> Z -> Z -> Z -> list Z -> Assertion)
 */


/*@ include strategies "dll_queue.strategies" */