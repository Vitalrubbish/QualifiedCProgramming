

#include "dll_queue_def.h"

struct list * malloc_list_cell()
  /*@ Require emp
      Ensure __return != 0 &&
             store(&(__return -> next), 0) *
             store(&(__return -> prev), 0) *
             store(&(__return -> data), 0)
   */
  ;

void free_list_cell(struct list * p)
  /*@ Require exists x y z, 
             store(&(p -> next), x) *
             store(&(p -> prev), y) *
             store(&(p -> data), z)
      Ensure emp
   */
  ;

void enqueue(struct queue * q, int x)
  /*@ With l
      Require store_queue(q, l)
      Ensure store_queue(q, app(l, cons(x, nil)))
   */
{
  /*@ Assert 
      exists qhead qtail,
      q == q@pre && x == x@pre && 
      dllseg(qhead, 0, 0, qtail, l) *
      store(&(q -> head), qhead) *
      store(&(q -> tail), qtail)
  */
  struct list * p = malloc_list_cell();
  p -> data = x;
  if (q -> head == (void *)0) {
    q -> head = p;
    q -> tail = p;
    p -> next = (void *)0;
    p -> prev = (void *)0;
  }
  else {
    /*@ Assert exists l0 qtailv qtail qhead qtailnext qtailprev, 
          x == x@pre && q == q@pre &&
          p != 0 &&
          qtail != 0 && qhead != 0 &&
          l == app(l0, cons(qtailv, nil)) &&
          qtailnext == 0 &&
          dllseg(qhead, qtail, 0, qtailprev, l0) * 
          store(&(q -> tail), qtail) *
          store(&(q -> head), qhead) *
          store(&(qtail -> next), qtailnext) *
          store(&(qtail -> prev), qtailprev) *
          store(&(qtail -> data), qtailv) *
          store(&(p -> next), 0) *
          store(&(p -> prev), 0) *
          store(&(p -> data), x)
    */
    q -> tail -> next = p;
    p -> prev = q -> tail;
    q -> tail = p;
    p -> next = (void *)0;
  }
}

int dequeue(struct queue * q)
  /*@ With x l
      Require store_queue(q, cons(x, l))
      Ensure __return == x && store_queue(q, l)
   */
{
    /*@ Assert
      exists qhead qtail qheadnext,
        q == q@pre &&
      qhead != 0 &&
      store(&(qhead -> prev), 0) *
      store(&(qhead -> data), x) *
      store(&(qhead -> next), qheadnext) *
      dllseg(qheadnext, 0, qhead, qtail, l) *
      store(&(q -> head), qhead) *
      store(&(q -> tail), qtail)
  */
  struct list * p = q -> head;
  int x0 = p -> data;
  q -> head = p -> next;
  free_list_cell(p);
  if (q -> head == (void *)0) {
    q -> tail = (void *)0;
  }
  else {
        /*@ Assert exists qhead qtail headv qheadnext l0,
          q == q@pre &&
          x0 == x &&
          qhead != 0 &&
          l == cons(headv, l0) &&
          store(&(qhead -> prev), p) * 
          store(&(qhead -> data), headv) *
          store(&(qhead -> next), qheadnext) *
          dllseg(qheadnext, 0, qhead, qtail, l0) *
          store(&(q -> head), qhead) *
          store(&(q -> tail), qtail)
    */
    q -> head -> prev = (void *)0;
  }
  return x0;
}
