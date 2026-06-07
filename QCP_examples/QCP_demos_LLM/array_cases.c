


#include "sll_def.h"

/*@ Extern Coq (sum : list Z -> Z) */

unsigned int arr_sum(int n, unsigned int *a)
/*@ With l
    Require 0 <= n && n < 100 && UIntArray::full(a, n, l) &&
            (forall (i: Z), (0 <= i && i < n) => 0 <= l[i] && l[i] < 100)
    Ensure __return == sum(l) && UIntArray::full(a, n, l) */
{
  int i;
  unsigned int ret = 0;
  /*@ Inv Assert
      0 <= n@pre && n@pre < 100 &&
      0 <= i && i <= n@pre &&
      a == a@pre && n == n@pre &&
      (forall (i: Z), (0 <= i && i < n@pre) => 0 <= l[i] && l[i] < 100) &&
      ret == sum(sublist(0, i, l)) &&
      UIntArray::full(a, n, l)
  */
  for (i = 0; i < n; ++i) {
    ret += a[i];
  }
  return ret;
}

void array_copy1(int *dest, int *src, int n)
/*@ With l
    Require 0 <= n && n < INT_MAX && IntArray::undef_full(dest, n) * IntArray::full(src, n, l)
    Ensure IntArray::full(dest, n, l) * IntArray::full(src, n, l)
*/
{
  int i;
  /*@ Inv Assert
      0 <= i && i <= n@pre && n == n@pre && dest == dest@pre && src == src@pre &&
      0 <= n@pre && n@pre < INT_MAX &&
      IntArray::seg(dest@pre, 0, i, sublist(0, i, l)) *
      IntArray::undef_seg(dest@pre, i, n@pre) *
      IntArray::full(src@pre, n@pre, l)
  */
  for (i = 0; i < n; ++i) {
    dest[i] = src[i];
  }
}

void array_concat(int * ret, int *a, int n, int *b, int m)
/*@ With l1 l2
    Require 0 <= n && 0 <= m && n + m < INT_MAX && IntArray::full(a, n, l1) * IntArray::full(b, m, l2) * IntArray::undef_full(ret, n + m)
    Ensure IntArray::full(a, n, l1) * IntArray::full(b, m, l2) * IntArray::full(ret, n + m, app(l1, l2))
*/
{
  int i; 
  /*@ Inv Assert
      0 <= i && i <= n@pre && ret == ret@pre && a == a@pre && b == b@pre && n == n@pre && m == m@pre &&
      0 <= n@pre && 0 <= m@pre && n@pre + m@pre < INT_MAX &&
      IntArray::seg(ret@pre, 0, i, sublist(0, i, l1)) * IntArray::undef_seg(ret@pre, i, n@pre + m@pre) * IntArray::full(a, n, l1) * IntArray::full(b, m, l2)
  */
  for (i = 0; i < n; ++i) {
    ret[i] = a[i];
  }
  /*@ Inv Assert
      0 <= i && i <= m@pre && ret == ret@pre && a == a@pre && b == b@pre && n == n@pre && m == m@pre &&
      0 <= n@pre && 0 <= m@pre && n@pre + m@pre < INT_MAX &&
      IntArray::seg(ret@pre, 0, n@pre + i, app(l1, sublist(0, i, l2))) * IntArray::undef_seg(ret@pre, n@pre + i, n@pre + m@pre) * IntArray::full(a, n, l1) * IntArray::full(b, m, l2)
  */
  for (i = 0; i < m; ++i) {
    ret[n + i] = b[i];
  }
}

void array_swap(int *a, int *b, int n)
/*@ With l1 l2
  Require 0 <= n && n < INT_MAX && Zlength(l1) == n && Zlength(l2) == n && IntArray::full(a, n, l1) * IntArray::full(b, n, l2)
    Ensure IntArray::full(a, n, l2) * IntArray::full(b, n, l1)
*/
{
  int i;
  /*@ Inv Assert
      0 <= i && i <= n@pre && a == a@pre && b == b@pre && n == n@pre &&
    0 <= n@pre && n@pre < INT_MAX && Zlength(l1) == n@pre && Zlength(l2) == n@pre &&
      IntArray::full(a, n@pre, app(sublist(0, i, l2), sublist(i, n@pre, l1))) *
      IntArray::full(b, n@pre, app(sublist(0, i, l1), sublist(i, n@pre, l2)))
  */
  for (i = 0; i < n; ++i) {
    int tmp = a[i];
    a[i] = b[i];
    b[i] = tmp;
  }
}

void array_vector_sum(unsigned int *ret, unsigned int *a, unsigned int *b, int n)
/*@ With l1 l2
    Require 0 <= n && n < 100 && UIntArray::full(a, n, l1) * UIntArray::full(b, n, l2) * UIntArray::undef_full(ret, n) &&
            (forall (i: Z), (0 <= i && i < n) => 0 <= l1[i] && l1[i] < 100) &&
            (forall (i: Z), (0 <= i && i < n) => 0 <= l2[i] && l2[i] < 100)
    Ensure exists l3,
             Zlength(l3) == n &&
             (forall (i: Z), (0 <= i && i < n) => l3[i] == l1[i] + l2[i]) &&
             UIntArray::full(a, n, l1) * UIntArray::full(b, n, l2) * UIntArray::full(ret, n, l3)
*/
{
  int i;
  /*@ Inv Assert
      exists l3,
      0 <= i && i <= n@pre && ret == ret@pre && a == a@pre && b == b@pre && n == n@pre &&
      0 <= n@pre && n@pre < 100 &&
      Zlength(l3) == i &&
      (forall (k: Z), (0 <= k && k < n@pre) => 0 <= l1[k] && l1[k] < 100) &&
      (forall (k: Z), (0 <= k && k < n@pre) => 0 <= l2[k] && l2[k] < 100) &&
      (forall (k: Z), (0 <= k && k < i) => l3[k] == l1[k] + l2[k]) &&
      UIntArray::seg(ret@pre, 0, i, l3) * UIntArray::undef_seg(ret@pre, i, n@pre) * UIntArray::full(a, n, l1) * UIntArray::full(b, n, l2)
  */
  for (i = 0; i < n; ++i) {
    ret[i] = a[i] + b[i];
  }
}

void pointwise_mul(unsigned int *a, unsigned int *b, unsigned int *c, int n)
/*@ With l1 l2
    Require 0 <= n && n < 100 && UIntArray::full(a, n, l1) * UIntArray::full(b, n, l2) * UIntArray::undef_full(c, n) &&
            (forall (i: Z), (0 <= i && i < n) => 0 <= l1[i] && l1[i] < 100) &&
            (forall (i: Z), (0 <= i && i < n) => 0 <= l2[i] && l2[i] < 100)
    Ensure exists l3,
             Zlength(l3) == n &&
             (forall (i: Z), (0 <= i && i < n) => l3[i] == l1[i] * l2[i]) &&
             UIntArray::full(a, n, l1) * UIntArray::full(b, n, l2) * UIntArray::full(c, n, l3)
*/
{
  int i;
  /*@ Inv Assert
      exists l3,
      0 <= i && i <= n@pre && a == a@pre && b == b@pre && c == c@pre && n == n@pre &&
      0 <= n@pre && n@pre < 100 &&
      Zlength(l3) == i &&
      (forall (k: Z), (0 <= k && k < n@pre) => 0 <= l1[k] && l1[k] < 100) &&
      (forall (k: Z), (0 <= k && k < n@pre) => 0 <= l2[k] && l2[k] < 100) &&
      (forall (k: Z), (0 <= k && k < i) => l3[k] == l1[k] * l2[k]) &&
      UIntArray::seg(c@pre, 0, i, l3) * UIntArray::undef_seg(c@pre, i, n@pre) * UIntArray::full(a, n, l1) * UIntArray::full(b, n, l2)
  */
  for (i = 0; i < n; ++i) {
    c[i] = a[i] * b[i];
  }
}

int array_max(int *a, int n)
/*@ With l
    Require 0 <= n && n < INT_MAX && IntArray::full(a, n, l) &&
            (forall (i: Z), (0 <= i && i < n) => 0 <= l[i])
    Ensure IntArray::full(a, n, l) &&
           (n == 0 => __return == -1) &&
           (0 < n =>
             (exists i, 0 <= i && i < n && __return == l[i]) &&
             (forall (i: Z), (0 <= i && i < n) => l[i] <= __return))
*/
{
  int i;
  int max = -1;
  /*@ Inv Assert
      exists v, max == v && 0 <= i && i <= n@pre && a == a@pre && n == n@pre &&
      0 <= n@pre && n@pre < INT_MAX &&
      (forall (k: Z), (0 <= k && k < n@pre) => 0 <= l[k]) &&
      IntArray::full(a, n, l) &&
      (i == 0 => v == -1) &&
      (0 < i =>
        (exists k, 0 <= k && k < i && v == l[k]) &&
        (forall (k: Z), (0 <= k && k < i) => l[k] <= v))
  */
  for (i = 0; i < n; ++i) {
    if (a[i] > max) {
      max = a[i];
    }
  }
  return max;
}

void memset(int *a, int n, int value)
/*@ Require 0 <= n && n < INT_MAX && IntArray::undef_full(a, n)
    Ensure exists l,
             Zlength(l) == n &&
             (forall (i: Z), (0 <= i && i < n) => l[i] == value@pre) &&
             IntArray::full(a, n, l)
*/
{
  int i;
  /*@ Inv Assert
      exists l,
      0 <= i && i <= n@pre && a == a@pre && n == n@pre && value == value@pre &&
      0 <= n@pre && n@pre < INT_MAX &&
      Zlength(l) == i &&
      (forall (k: Z), (0 <= k && k < i) => l[k] == value@pre) &&
      IntArray::seg(a@pre, 0, i, l) * IntArray::undef_seg(a@pre, i, n@pre)
  */
  for (i = 0; i < n; ++i) {
    a[i] = value;
  }
}

struct list* malloc_list(int data)
/*@ With data0 
    Require data == data0 && emp
    Ensure __return != 0 && __return -> data == data0 && __return -> next == 0
*/;

struct list *array_to_list(int *a, int n)
/*@ With l
    Require 0 <= n && n < INT_MAX && IntArray::full(a, n, l)
    Ensure sll(__return, l) * IntArray::full(a, n, l)
*/
{
  struct list *head;
  struct list *tail;
  int i;
  if (n == 0) {
    return 0;
  }
  head = malloc_list(a[0]);
  tail = head;
  /*@ Inv Assert
      exists v, 
      1 <= i && i <= n@pre && head != 0 && tail != 0 && 
      a == a@pre && n == n@pre && 0 < n@pre && n@pre < INT_MAX &&
      v == Znth(i - 1, l, 0) &&
      store(&(tail -> data), v) *
      store(&(tail -> next), 0) *
      sllseg(head, tail, sublist(0, i - 1, l)) *
      IntArray::full(a, n, l)
  */
  for (i = 1; i < n; ++i) {
    struct list *node = malloc_list(a[i]);
    tail->next = node;
    tail = node;
  }
  return head;
}