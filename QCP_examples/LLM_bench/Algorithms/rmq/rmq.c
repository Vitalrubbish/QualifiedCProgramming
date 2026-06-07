#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq
      (Power2 : Z -> Z)
      (RangeMaxValue : list Z -> Z -> Z -> Z -> Prop)
      (STCellRangeMax : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (STZeroPrefix : list Z -> Z -> Prop)
      (STBasePrefix : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (STBuiltBeforeLevel : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (STLevelPrefix : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
      (STBuilt : list Z -> list Z -> Z -> Z -> Prop)
      (QueryLogLoopState : Z -> Z -> Z -> Z -> Z -> Prop)
      (QueryLogFinalState : Z -> Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_lib */

void build(int *arr, int n, int K, int *st)
/*@ With (l : list Z) (st0 : list Z)
    Require
      1 <= n && n <= 100000 &&
      1 <= K && K <= 30 &&
      n * K <= 1000000 &&
      n < Power2(K) &&
      Zlength(l) == n &&
      Zlength(st0) == n * K &&
      IntArray::full(arr, n, l) *
      IntArray::full(st, n * K, st0) &&
      (forall (idx : Z), (0 <= idx && idx < n) => (INT_MIN <= l[idx] && l[idx] <= INT_MAX))
    Ensure
      exists st_l,
      STBuilt(l, st_l, K, n) &&
      Zlength(st_l) == n * K &&
      IntArray::full(arr, n, l) *
      IntArray::full(st, n * K, st_l)
 */
{
  /*@ Inv Assert
      exists st_l,
      arr == arr@pre && n == n@pre && K == K@pre && st == st@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= K@pre && K@pre <= 30 &&
      n@pre * K@pre <= 1000000 &&
      n@pre < Power2(K@pre) &&
      Zlength(l) == n@pre &&
      Zlength(st_l) == n@pre * K@pre &&
      0 <= idx && idx <= n@pre * K@pre &&
      STZeroPrefix(st_l, idx) &&
      IntArray::full(arr@pre, n@pre, l) *
      IntArray::full(st@pre, n@pre * K@pre, st_l) &&
      (forall (p : Z), (0 <= p && p < n@pre) => (INT_MIN <= l[p] && l[p] <= INT_MAX))
   */
  for (int idx = 0; idx < n * K; ++idx) {
    st[idx] = 0;
  }

  /*@ Assert
      exists st_l,
      arr == arr@pre && n == n@pre && K == K@pre && st == st@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= K@pre && K@pre <= 30 &&
      n@pre * K@pre <= 1000000 &&
      n@pre < Power2(K@pre) &&
      Zlength(l) == n@pre &&
      Zlength(st_l) == n@pre * K@pre &&
      STZeroPrefix(st_l, n@pre * K@pre) &&
      IntArray::full(arr@pre, n@pre, l) *
      IntArray::full(st@pre, n@pre * K@pre, st_l) &&
      (forall (p : Z), (0 <= p && p < n@pre) => (INT_MIN <= l[p] && l[p] <= INT_MAX))
   */

  /*@ Inv Assert
      exists st_l,
      arr == arr@pre && n == n@pre && K == K@pre && st == st@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= K@pre && K@pre <= 30 &&
      n@pre * K@pre <= 1000000 &&
      n@pre < Power2(K@pre) &&
      Zlength(l) == n@pre &&
      Zlength(st_l) == n@pre * K@pre &&
      0 <= i && i <= n@pre &&
      STBasePrefix(l, st_l, K@pre, n@pre, i) &&
      IntArray::full(arr@pre, n@pre, l) *
      IntArray::full(st@pre, n@pre * K@pre, st_l) &&
      (forall (p : Z), (0 <= p && p < n@pre) => (INT_MIN <= l[p] && l[p] <= INT_MAX))
   */
  for (int i = 0; i < n; ++i) {
    /*@ Assert
        exists st_l,
        arr == arr@pre && n == n@pre && K == K@pre && st == st@pre &&
        1 <= n@pre && n@pre <= 100000 &&
        1 <= K@pre && K@pre <= 30 &&
        n@pre * K@pre <= 1000000 &&
        n@pre < Power2(K@pre) &&
        Zlength(l) == n@pre &&
        Zlength(st_l) == n@pre * K@pre &&
        0 <= i && i < n@pre &&
        0 <= i * K@pre && i * K@pre < n@pre * K@pre &&
        STBasePrefix(l, st_l, K@pre, n@pre, i) &&
        IntArray::full(arr@pre, n@pre, l) *
        IntArray::full(st@pre, n@pre * K@pre, st_l) &&
        (forall (p : Z), (0 <= p && p < n@pre) => (INT_MIN <= l[p] && l[p] <= INT_MAX))
     */
    st[i * K] = arr[i];
    /*@ Assert
        exists st_l,
        arr == arr@pre && n == n@pre && K == K@pre && st == st@pre &&
        1 <= n@pre && n@pre <= 100000 &&
        1 <= K@pre && K@pre <= 30 &&
        n@pre * K@pre <= 1000000 &&
        n@pre < Power2(K@pre) &&
        Zlength(l) == n@pre &&
        Zlength(st_l) == n@pre * K@pre &&
        0 <= i && i < n@pre &&
        STBasePrefix(l, st_l, K@pre, n@pre, i + 1) &&
        IntArray::full(arr@pre, n@pre, l) *
        IntArray::full(st@pre, n@pre * K@pre, st_l) &&
        (forall (p : Z), (0 <= p && p < n@pre) => (INT_MIN <= l[p] && l[p] <= INT_MAX))
     */
  }

  /*@ Assert
      exists st_l,
      arr == arr@pre && n == n@pre && K == K@pre && st == st@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= K@pre && K@pre <= 30 &&
      n@pre * K@pre <= 1000000 &&
      n@pre < Power2(K@pre) &&
      Zlength(l) == n@pre &&
      Zlength(st_l) == n@pre * K@pre &&
      STBuiltBeforeLevel(l, st_l, K@pre, n@pre, 1) &&
      IntArray::full(arr@pre, n@pre, l) *
      IntArray::full(st@pre, n@pre * K@pre, st_l) &&
      (forall (p : Z), (0 <= p && p < n@pre) => (INT_MIN <= l[p] && l[p] <= INT_MAX))
   */

  int half = 1;
  int len = 2;
  /*@ Inv Assert
      exists st_l,
      arr == arr@pre && n == n@pre && K == K@pre && st == st@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= K@pre && K@pre <= 30 &&
      n@pre * K@pre <= 1000000 &&
      n@pre < Power2(K@pre) &&
      Zlength(l) == n@pre &&
      Zlength(st_l) == n@pre * K@pre &&
      1 <= j && j <= K@pre &&
      half == Power2(j - 1) &&
      len == Power2(j) &&
      STBuiltBeforeLevel(l, st_l, K@pre, n@pre, j) &&
      IntArray::full(arr@pre, n@pre, l) *
      IntArray::full(st@pre, n@pre * K@pre, st_l) &&
      (forall (p : Z), (0 <= p && p < n@pre) => (INT_MIN <= l[p] && l[p] <= INT_MAX))
   */
  for (int j = 1; j < K; ++j) {
    /*@ Inv Assert
        exists st_l,
        arr == arr@pre && n == n@pre && K == K@pre && st == st@pre &&
        1 <= n@pre && n@pre <= 100000 &&
        1 <= K@pre && K@pre <= 30 &&
        n@pre * K@pre <= 1000000 &&
        n@pre < Power2(K@pre) &&
        Zlength(l) == n@pre &&
        Zlength(st_l) == n@pre * K@pre &&
        1 <= j && j < K@pre &&
        half == Power2(j - 1) &&
        len == Power2(j) &&
        0 <= i && i <= n@pre &&
        STBuiltBeforeLevel(l, st_l, K@pre, n@pre, j) &&
        STLevelPrefix(l, st_l, K@pre, n@pre, j, i) &&
        IntArray::full(arr@pre, n@pre, l) *
        IntArray::full(st@pre, n@pre * K@pre, st_l) &&
        (forall (p : Z), (0 <= p && p < n@pre) => (INT_MIN <= l[p] && l[p] <= INT_MAX))
     */
    for (int i = 0; i + len <= n; ++i) {
      /*@ Assert
          exists st_l,
          arr == arr@pre && n == n@pre && K == K@pre && st == st@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          1 <= K@pre && K@pre <= 30 &&
          n@pre * K@pre <= 1000000 &&
          n@pre < Power2(K@pre) &&
          Zlength(l) == n@pre &&
          Zlength(st_l) == n@pre * K@pre &&
          1 <= j && j < K@pre &&
          half == Power2(j - 1) &&
          len == Power2(j) &&
          0 <= i && i + len <= n@pre &&
          0 <= i * K@pre + j - 1 && i * K@pre + j - 1 < n@pre * K@pre &&
          0 <= (i + half) * K@pre + j - 1 && (i + half) * K@pre + j - 1 < n@pre * K@pre &&
          0 <= i * K@pre + j && i * K@pre + j < n@pre * K@pre &&
          STBuiltBeforeLevel(l, st_l, K@pre, n@pre, j) &&
          STLevelPrefix(l, st_l, K@pre, n@pre, j, i) &&
          STCellRangeMax(l, st_l, K@pre, i, j - 1) &&
          STCellRangeMax(l, st_l, K@pre, i + half, j - 1) &&
          IntArray::full(arr@pre, n@pre, l) *
          IntArray::full(st@pre, n@pre * K@pre, st_l) &&
          (forall (p : Z), (0 <= p && p < n@pre) => (INT_MIN <= l[p] && l[p] <= INT_MAX))
       */
      int a = st[i * K + j - 1];
      int b = st[(i + half) * K + j - 1];
      /*@ Assert
          exists st_l,
          arr == arr@pre && n == n@pre && K == K@pre && st == st@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          1 <= K@pre && K@pre <= 30 &&
          n@pre * K@pre <= 1000000 &&
          n@pre < Power2(K@pre) &&
          Zlength(l) == n@pre &&
          Zlength(st_l) == n@pre * K@pre &&
          1 <= j && j < K@pre &&
          half == Power2(j - 1) &&
          len == Power2(j) &&
          0 <= i && i + len <= n@pre &&
          0 <= i * K@pre + j - 1 && i * K@pre + j - 1 < n@pre * K@pre &&
          0 <= (i + half) * K@pre + j - 1 && (i + half) * K@pre + j - 1 < n@pre * K@pre &&
          0 <= i * K@pre + j && i * K@pre + j < n@pre * K@pre &&
          a == st_l[i * K@pre + j - 1] &&
          b == st_l[(i + half) * K@pre + j - 1] &&
          STBuiltBeforeLevel(l, st_l, K@pre, n@pre, j) &&
          STLevelPrefix(l, st_l, K@pre, n@pre, j, i) &&
          STCellRangeMax(l, st_l, K@pre, i, j - 1) &&
          STCellRangeMax(l, st_l, K@pre, i + half, j - 1) &&
          IntArray::full(arr@pre, n@pre, l) *
          IntArray::full(st@pre, n@pre * K@pre, st_l) &&
          (forall (p : Z), (0 <= p && p < n@pre) => (INT_MIN <= l[p] && l[p] <= INT_MAX))
       */
      if (a >= b) {
        st[i * K + j] = a;
      } else {
        st[i * K + j] = b;
      }
      /*@ Assert
          exists st_l,
          arr == arr@pre && n == n@pre && K == K@pre && st == st@pre &&
          1 <= n@pre && n@pre <= 100000 &&
          1 <= K@pre && K@pre <= 30 &&
          n@pre * K@pre <= 1000000 &&
          n@pre < Power2(K@pre) &&
          Zlength(l) == n@pre &&
          Zlength(st_l) == n@pre * K@pre &&
          1 <= j && j < K@pre &&
          half == Power2(j - 1) &&
          len == Power2(j) &&
          0 <= i && i + len <= n@pre &&
          a == st_l[i * K@pre + j - 1] &&
          b == st_l[(i + half) * K@pre + j - 1] &&
          STBuiltBeforeLevel(l, st_l, K@pre, n@pre, j) &&
          STLevelPrefix(l, st_l, K@pre, n@pre, j, i + 1) &&
          IntArray::full(arr@pre, n@pre, l) *
          IntArray::full(st@pre, n@pre * K@pre, st_l) &&
          (forall (p : Z), (0 <= p && p < n@pre) => (INT_MIN <= l[p] && l[p] <= INT_MAX))
       */
    }
    /*@ Assert
        exists st_l,
        arr == arr@pre && n == n@pre && K == K@pre && st == st@pre &&
        1 <= n@pre && n@pre <= 100000 &&
        1 <= K@pre && K@pre <= 30 &&
        n@pre * K@pre <= 1000000 &&
        n@pre < Power2(K@pre) &&
        Zlength(l) == n@pre &&
        Zlength(st_l) == n@pre * K@pre &&
        1 <= j && j < K@pre &&
        half == Power2(j - 1) &&
        len == Power2(j) &&
        STBuiltBeforeLevel(l, st_l, K@pre, n@pre, j + 1) &&
        IntArray::full(arr@pre, n@pre, l) *
        IntArray::full(st@pre, n@pre * K@pre, st_l) &&
        (forall (p : Z), (0 <= p && p < n@pre) => (INT_MIN <= l[p] && l[p] <= INT_MAX))
     */
    half = len;
    len = len * 2;
  }
}

int query(int *st, int n, int K, int left, int right)
/*@ With (l : list Z) (st_l : list Z)
    Require
      1 <= n && n <= 100000 &&
      1 <= K && K <= 30 &&
      n * K <= 1000000 &&
      n < Power2(K) &&
      0 <= left && left <= right && right < n &&
      Zlength(l) == n &&
      Zlength(st_l) == n * K &&
      STBuilt(l, st_l, K, n) &&
      IntArray::full(st, n * K, st_l)
    Ensure
      RangeMaxValue(l, left, right + 1, __return) &&
      IntArray::full(st, n * K, st_l)
 */
{
  int len = right - left + 1;
  int k = 0;
  int pow = 1;

  /*@ Inv Assert
      st == st@pre && n == n@pre && K == K@pre &&
      left == left@pre && right == right@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= K@pre && K@pre <= 30 &&
      n@pre * K@pre <= 1000000 &&
      n@pre < Power2(K@pre) &&
      0 <= left@pre && left@pre <= right@pre && right@pre < n@pre &&
      len == right@pre - left@pre + 1 &&
      Zlength(l) == n@pre &&
      Zlength(st_l) == n@pre * K@pre &&
      STBuilt(l, st_l, K@pre, n@pre) &&
      QueryLogLoopState(K@pre, n@pre, len, k, pow) &&
      IntArray::full(st@pre, n@pre * K@pre, st_l)
   */
  while (pow * 2 <= len) {
    pow = pow * 2;
    k++;
  }

  /*@ Assert
      st == st@pre && n == n@pre && K == K@pre &&
      left == left@pre && right == right@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= K@pre && K@pre <= 30 &&
      n@pre * K@pre <= 1000000 &&
      n@pre < Power2(K@pre) &&
      0 <= left@pre && left@pre <= right@pre && right@pre < n@pre &&
      len == right@pre - left@pre + 1 &&
      Zlength(l) == n@pre &&
      Zlength(st_l) == n@pre * K@pre &&
      STBuilt(l, st_l, K@pre, n@pre) &&
      QueryLogFinalState(K@pre, n@pre, len, k, pow) &&
      0 <= left@pre * K@pre + k && left@pre * K@pre + k < n@pre * K@pre &&
      0 <= (right@pre - pow + 1) * K@pre + k &&
      (right@pre - pow + 1) * K@pre + k < n@pre * K@pre &&
      STCellRangeMax(l, st_l, K@pre, left@pre, k) &&
      STCellRangeMax(l, st_l, K@pre, right@pre - pow + 1, k) &&
      IntArray::full(st@pre, n@pre * K@pre, st_l)
   */

  int a = st[left * K + k];
  int b = st[(right - pow + 1) * K + k];
  /*@ Assert
      st == st@pre && n == n@pre && K == K@pre &&
      left == left@pre && right == right@pre &&
      1 <= n@pre && n@pre <= 100000 &&
      1 <= K@pre && K@pre <= 30 &&
      n@pre * K@pre <= 1000000 &&
      n@pre < Power2(K@pre) &&
      0 <= left@pre && left@pre <= right@pre && right@pre < n@pre &&
      len == right@pre - left@pre + 1 &&
      Zlength(l) == n@pre &&
      Zlength(st_l) == n@pre * K@pre &&
      a == st_l[left@pre * K@pre + k] &&
      b == st_l[(right@pre - pow + 1) * K@pre + k] &&
      STBuilt(l, st_l, K@pre, n@pre) &&
      QueryLogFinalState(K@pre, n@pre, len, k, pow) &&
      STCellRangeMax(l, st_l, K@pre, left@pre, k) &&
      STCellRangeMax(l, st_l, K@pre, right@pre - pow + 1, k) &&
      IntArray::full(st@pre, n@pre * K@pre, st_l)
   */
  if (a >= b) {
    /*@ Assert
        st == st@pre && n == n@pre && K == K@pre &&
        left == left@pre && right == right@pre &&
        1 <= n@pre && n@pre <= 100000 &&
        1 <= K@pre && K@pre <= 30 &&
        0 <= left@pre && left@pre <= right@pre && right@pre < n@pre &&
        len == right@pre - left@pre + 1 &&
        Zlength(l) == n@pre &&
        Zlength(st_l) == n@pre * K@pre &&
        a == st_l[left@pre * K@pre + k] &&
        b == st_l[(right@pre - pow + 1) * K@pre + k] &&
        QueryLogFinalState(K@pre, n@pre, len, k, pow) &&
        RangeMaxValue(l, left@pre, right@pre + 1, a) &&
        IntArray::full(st@pre, n@pre * K@pre, st_l)
     */
    return a;
  } else {
    /*@ Assert
        st == st@pre && n == n@pre && K == K@pre &&
        left == left@pre && right == right@pre &&
        1 <= n@pre && n@pre <= 100000 &&
        1 <= K@pre && K@pre <= 30 &&
        0 <= left@pre && left@pre <= right@pre && right@pre < n@pre &&
        len == right@pre - left@pre + 1 &&
        Zlength(l) == n@pre &&
        Zlength(st_l) == n@pre * K@pre &&
        a == st_l[left@pre * K@pre + k] &&
        b == st_l[(right@pre - pow + 1) * K@pre + k] &&
        QueryLogFinalState(K@pre, n@pre, len, k, pow) &&
        RangeMaxValue(l, left@pre, right@pre + 1, b) &&
        IntArray::full(st@pre, n@pre * K@pre, st_l)
     */
    return b;
  }
}
