#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq
      (HeapParent : Z -> Z)
      (Permutation : list Z -> list Z -> Prop)
      (PrefixMaxValue : list Z -> Z -> Z -> Prop)
      (MaxHeapPrefix : list Z -> Z -> Prop)
      (PriorityQueuePrefix : list Z -> Z -> Prop)
      (SameElementsPrefix : list Z -> list Z -> Z -> Prop)
      (PushLoopState : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (PushResult : list Z -> list Z -> Z -> Z -> Prop)
      (BuildPrefixState : list Z -> list Z -> Z -> Prop)
      (PopLoopState : list Z -> list Z -> Z -> Z -> Prop)
      (PopSelectedChild : list Z -> Z -> Z -> Z -> Prop)
      (PopReadyState : list Z -> list Z -> Z -> Z -> Prop)
      (PopResult : list Z -> list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Data_structures.priority_queue.priority_queue_lib */

void push(int *heap, int n, int x)
/*@ With (l : list Z)
    Require
      0 <= n && n < 100000 &&
      Zlength(l) == n + 1 &&
      l[n] == x &&
      INT_MIN <= x && x <= INT_MAX &&
      MaxHeapPrefix(l, n) &&
      IntArray::seg(heap, 0, n + 1, l) &&
      (forall (idx : Z), (0 <= idx && idx < n + 1) => (INT_MIN <= l[idx] && l[idx] <= INT_MAX))
    Ensure
      exists l_out,
      PushResult(l, l_out, n, x) &&
      PriorityQueuePrefix(l_out, n + 1) &&
      IntArray::seg(heap, 0, n + 1, l_out) &&
      (forall (idx : Z), (0 <= idx && idx < n + 1) => (INT_MIN <= l_out[idx] && l_out[idx] <= INT_MAX))
 */
{
  heap[n] = x;
  /*@ Assert
      exists l_cur,
      heap == heap@pre && n == n@pre && x == x@pre &&
      0 <= n@pre && n@pre < 100000 &&
      Zlength(l) == n@pre + 1 &&
      l[n@pre] == x@pre &&
      PushLoopState(l, l_cur, n@pre, n@pre, x@pre) &&
      IntArray::seg(heap, 0, n@pre + 1, l_cur) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre + 1) => (INT_MIN <= l_cur[idx] && l_cur[idx] <= INT_MAX))
   */
  int child = n;
  /*@ Inv Assert
      exists l_cur,
      heap == heap@pre && n == n@pre && x == x@pre &&
      0 <= n@pre && n@pre < 100000 &&
      0 <= child && child <= n@pre &&
      Zlength(l) == n@pre + 1 &&
      l[n@pre] == x@pre &&
      PushLoopState(l, l_cur, n@pre, child, x@pre) &&
      IntArray::seg(heap, 0, n@pre + 1, l_cur) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre + 1) => (INT_MIN <= l_cur[idx] && l_cur[idx] <= INT_MAX))
   */
  while (child > 0) {
    int parent = (child - 1) / 2;
    /*@ Assert
        exists l_cur,
        heap == heap@pre && n == n@pre && x == x@pre &&
        0 <= n@pre && n@pre < 100000 &&
        0 < child && child <= n@pre &&
        0 <= parent && parent < child && parent <= n@pre &&
        parent == HeapParent(child) &&
        Zlength(l) == n@pre + 1 &&
        l[n@pre] == x@pre &&
        PushLoopState(l, l_cur, n@pre, child, x@pre) &&
        IntArray::seg(heap, 0, n@pre + 1, l_cur) &&
        (forall (idx : Z), (0 <= idx && idx < n@pre + 1) => (INT_MIN <= l_cur[idx] && l_cur[idx] <= INT_MAX))
     */
    if (heap[parent] >= heap[child]) {
      /*@ Assert
          exists l_cur,
          heap == heap@pre && n == n@pre && x == x@pre &&
          0 <= n@pre && n@pre < 100000 &&
          0 < child && child <= n@pre &&
          0 <= parent && parent < child && parent <= n@pre &&
          parent == HeapParent(child) &&
          l_cur[parent] >= l_cur[child] &&
          PushResult(l, l_cur, n@pre, x@pre) &&
          PriorityQueuePrefix(l_cur, n@pre + 1) &&
          IntArray::seg(heap, 0, n@pre + 1, l_cur) &&
          (forall (idx : Z), (0 <= idx && idx < n@pre + 1) => (INT_MIN <= l_cur[idx] && l_cur[idx] <= INT_MAX))
       */
      break;
    }
    int tmp = heap[parent];
    heap[parent] = heap[child];
    heap[child] = tmp;
    /*@ Assert
        exists l_cur,
        heap == heap@pre && n == n@pre && x == x@pre &&
        0 <= n@pre && n@pre < 100000 &&
        0 < child && child <= n@pre &&
        0 <= parent && parent < child && parent <= n@pre &&
        parent == HeapParent(child) &&
        tmp == l_cur[child] &&
        PushLoopState(l, l_cur, n@pre, parent, x@pre) &&
        IntArray::seg(heap, 0, n@pre + 1, l_cur) &&
        (forall (idx : Z), (0 <= idx && idx < n@pre + 1) => (INT_MIN <= l_cur[idx] && l_cur[idx] <= INT_MAX))
     */
    child = parent;
  }
  /*@ Assert
      exists l_out,
      heap == heap@pre && n == n@pre && x == x@pre &&
      0 <= n@pre && n@pre < 100000 &&
      0 <= child && child <= n@pre &&
      PushResult(l, l_out, n@pre, x@pre) &&
      PriorityQueuePrefix(l_out, n@pre + 1) &&
      IntArray::seg(heap, 0, n@pre + 1, l_out) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre + 1) => (INT_MIN <= l_out[idx] && l_out[idx] <= INT_MAX))
   */
}

void build(int *heap, int n)
/*@ With (l : list Z)
    Require
      1 <= n && n <= 100000 &&
      Zlength(l) == n &&
      IntArray::full(heap, n, l) &&
      (forall (idx : Z), (0 <= idx && idx < n) => (INT_MIN <= l[idx] && l[idx] <= INT_MAX))
    Ensure
      exists l_out,
      BuildPrefixState(l, l_out, n) &&
      PriorityQueuePrefix(l_out, n) &&
      IntArray::full(heap, n, l_out) &&
      (forall (idx : Z), (0 <= idx && idx < n) => (INT_MIN <= l_out[idx] && l_out[idx] <= INT_MAX))
 */
{
  /*@ Inv Assert
      exists heap_l,
      heap == heap@pre && n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      1 <= i && i <= n@pre &&
      BuildPrefixState(l, heap_l, i) &&
      PriorityQueuePrefix(heap_l, i) &&
      IntArray::full(heap, n@pre, heap_l) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (INT_MIN <= heap_l[idx] && heap_l[idx] <= INT_MAX))
   */
  for (int i = 1; i < n; ++i) {
    int x = heap[i];
    /*@ Assert
        exists heap_l,
        heap == heap@pre && n == n@pre &&
        1 <= n@pre && n@pre <= 100000 &&
        Zlength(l) == n@pre &&
        1 <= i && i < n@pre &&
        x == heap_l[i] &&
        BuildPrefixState(l, heap_l, i) &&
        PriorityQueuePrefix(heap_l, i) &&
        MaxHeapPrefix(heap_l, i) &&
        IntArray::seg(heap, 0, i + 1, sublist(0, i + 1, heap_l)) *
        IntArray::seg(heap, i + 1, n@pre, sublist(i + 1, n@pre, heap_l)) &&
        (forall (idx : Z), (0 <= idx && idx < n@pre) => (INT_MIN <= heap_l[idx] && heap_l[idx] <= INT_MAX))
     */
    push(heap, i, x);
    /*@ Assert
        exists heap_l,
        heap == heap@pre && n == n@pre &&
        1 <= n@pre && n@pre <= 100000 &&
        Zlength(l) == n@pre &&
        1 <= i && i < n@pre &&
        INT_MIN <= x && x <= INT_MAX &&
        BuildPrefixState(l, heap_l, i + 1) &&
        PriorityQueuePrefix(heap_l, i + 1) &&
        IntArray::full(heap, n@pre, heap_l) &&
        (forall (idx : Z), (0 <= idx && idx < n@pre) => (INT_MIN <= heap_l[idx] && heap_l[idx] <= INT_MAX))
     */
  }
}

int pop(int *heap, int n)
/*@ With (l : list Z)
    Require
      1 <= n && n <= 100000 &&
      Zlength(l) == n &&
      PriorityQueuePrefix(l, n) &&
      IntArray::full(heap, n, l) &&
      (forall (idx : Z), (0 <= idx && idx < n) => (INT_MIN <= l[idx] && l[idx] <= INT_MAX))
    Ensure
      exists l_out,
      __return == l[0] &&
      PrefixMaxValue(l, n, __return) &&
      PopResult(l, l_out, n, __return) &&
      IntArray::full(heap, n, l_out) &&
      (forall (idx : Z), (0 <= idx && idx < n) => (INT_MIN <= l_out[idx] && l_out[idx] <= INT_MAX))
 */
{
  int ret = heap[0];
  /*@ Assert
      heap == heap@pre && n == n@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      ret == l[0] &&
      INT_MIN <= ret && ret <= INT_MAX &&
      PriorityQueuePrefix(l, n@pre) &&
      PrefixMaxValue(l, n@pre, ret) &&
      IntArray::full(heap, n@pre, l) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (INT_MIN <= l[idx] && l[idx] <= INT_MAX))
   */
  if (n == 1) {
    /*@ Assert
        heap == heap@pre && n == n@pre &&
        ret == l[0] &&
        INT_MIN <= ret && ret <= INT_MAX &&
        PrefixMaxValue(l, n@pre, ret) &&
        PopResult(l, l, n@pre, ret) &&
        IntArray::full(heap, n@pre, l) &&
        (forall (idx : Z), (0 <= idx && idx < n@pre) => (INT_MIN <= l[idx] && l[idx] <= INT_MAX))
     */
    return ret;
  }

  heap[0] = heap[n - 1];
  /*@ Assert
      exists heap_l,
      heap == heap@pre && n == n@pre &&
      1 < n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      ret == l[0] &&
      INT_MIN <= ret && ret <= INT_MAX &&
      PrefixMaxValue(l, n@pre, ret) &&
      PopLoopState(l, heap_l, n@pre, 0) &&
      IntArray::full(heap, n@pre, heap_l) &&
      (forall (idx : Z), (0 <= idx && idx < n@pre) => (INT_MIN <= heap_l[idx] && heap_l[idx] <= INT_MAX))
   */
  int idx = 0;
  /*@ Inv Assert
      exists heap_l,
      heap == heap@pre && n == n@pre &&
      1 < n@pre && n@pre <= 100000 &&
      Zlength(l) == n@pre &&
      ret == l[0] &&
      INT_MIN <= ret && ret <= INT_MAX &&
      PrefixMaxValue(l, n@pre, ret) &&
      0 <= idx && idx < n@pre - 1 &&
      0 <= idx * 2 + 1 && idx * 2 + 1 <= INT_MAX &&
      PopLoopState(l, heap_l, n@pre, idx) &&
      IntArray::full(heap, n@pre, heap_l) &&
      (forall (pos : Z), (0 <= pos && pos < n@pre) => (INT_MIN <= heap_l[pos] && heap_l[pos] <= INT_MAX))
   */
  while (idx * 2 + 1 < n - 1) {
    int left = idx * 2 + 1;
    int right = left + 1;
    int largest = left;
    /*@ Assert
        exists heap_l,
        heap == heap@pre && n == n@pre &&
        1 < n@pre && n@pre <= 100000 &&
        ret == l[0] &&
        INT_MIN <= ret && ret <= INT_MAX &&
        PrefixMaxValue(l, n@pre, ret) &&
        0 <= idx && idx < n@pre - 1 &&
        left == idx * 2 + 1 &&
        right == left + 1 &&
        largest == left &&
        0 <= left && left < n@pre - 1 &&
        0 <= right && right <= n@pre - 1 &&
        PopLoopState(l, heap_l, n@pre, idx) &&
        IntArray::full(heap, n@pre, heap_l) &&
        (forall (pos : Z), (0 <= pos && pos < n@pre) => (INT_MIN <= heap_l[pos] && heap_l[pos] <= INT_MAX))
     */
    if (right < n - 1 && heap[left] < heap[right]) {
      largest = right;
    }
    /*@ Assert
        exists heap_l,
        heap == heap@pre && n == n@pre &&
        1 < n@pre && n@pre <= 100000 &&
        ret == l[0] &&
        INT_MIN <= ret && ret <= INT_MAX &&
        PrefixMaxValue(l, n@pre, ret) &&
        0 <= idx && idx < n@pre - 1 &&
        left == idx * 2 + 1 &&
        right == left + 1 &&
        0 <= largest && largest < n@pre - 1 &&
        PopSelectedChild(heap_l, n@pre - 1, idx, largest) &&
        PopLoopState(l, heap_l, n@pre, idx) &&
        IntArray::full(heap, n@pre, heap_l) &&
        (forall (pos : Z), (0 <= pos && pos < n@pre) => (INT_MIN <= heap_l[pos] && heap_l[pos] <= INT_MAX))
     */
    if (heap[idx] >= heap[largest]) {
      /*@ Assert
          exists heap_l,
          heap == heap@pre && n == n@pre &&
          1 < n@pre && n@pre <= 100000 &&
          ret == l[0] &&
          INT_MIN <= ret && ret <= INT_MAX &&
          PrefixMaxValue(l, n@pre, ret) &&
          0 <= idx && idx < n@pre - 1 &&
          left == idx * 2 + 1 &&
          right == left + 1 &&
          0 <= left && left < n@pre - 1 &&
          0 <= right && right <= n@pre - 1 &&
          0 <= largest && largest < n@pre - 1 &&
          heap_l[idx] >= heap_l[largest] &&
          PopSelectedChild(heap_l, n@pre - 1, idx, largest) &&
          PopReadyState(l, heap_l, n@pre, ret) &&
          IntArray::full(heap, n@pre, heap_l) &&
          (forall (pos : Z), (0 <= pos && pos < n@pre) => (INT_MIN <= heap_l[pos] && heap_l[pos] <= INT_MAX))
       */
      break;
    }
    int tmp = heap[idx];
    heap[idx] = heap[largest];
    heap[largest] = tmp;
    /*@ Assert
        exists heap_l,
        heap == heap@pre && n == n@pre &&
        1 < n@pre && n@pre <= 100000 &&
        ret == l[0] &&
        INT_MIN <= ret && ret <= INT_MAX &&
        PrefixMaxValue(l, n@pre, ret) &&
        0 <= idx && idx < n@pre - 1 &&
        left == idx * 2 + 1 &&
        right == left + 1 &&
        0 <= left && left < n@pre - 1 &&
        0 <= right && right <= n@pre - 1 &&
        0 <= largest && largest < n@pre - 1 &&
        idx < largest &&
        tmp == heap_l[largest] &&
        PopLoopState(l, heap_l, n@pre, largest) &&
        IntArray::full(heap, n@pre, heap_l) &&
        (forall (pos : Z), (0 <= pos && pos < n@pre) => (INT_MIN <= heap_l[pos] && heap_l[pos] <= INT_MAX))
     */
    idx = largest;
  }
  /*@ Assert
      exists heap_l,
      heap == heap@pre && n == n@pre &&
      1 < n@pre && n@pre <= 100000 &&
      ret == l[0] &&
      INT_MIN <= ret && ret <= INT_MAX &&
      PrefixMaxValue(l, n@pre, ret) &&
      0 <= idx && idx < n@pre - 1 &&
      PopReadyState(l, heap_l, n@pre, ret) &&
      IntArray::full(heap, n@pre, heap_l) &&
      (forall (pos : Z), (0 <= pos && pos < n@pre) => (INT_MIN <= heap_l[pos] && heap_l[pos] <= INT_MAX))
   */
  heap[n - 1] = ret;
  /*@ Assert
      exists l_out,
      heap == heap@pre && n == n@pre &&
      1 < n@pre && n@pre <= 100000 &&
      ret == l[0] &&
      INT_MIN <= ret && ret <= INT_MAX &&
      0 <= idx && idx < n@pre - 1 &&
      PrefixMaxValue(l, n@pre, ret) &&
      PopResult(l, l_out, n@pre, ret) &&
      IntArray::full(heap, n@pre, l_out) &&
      (forall (pos : Z), (0 <= pos && pos < n@pre) => (INT_MIN <= l_out[pos] && l_out[pos] <= INT_MAX))
   */
  return ret;
}
