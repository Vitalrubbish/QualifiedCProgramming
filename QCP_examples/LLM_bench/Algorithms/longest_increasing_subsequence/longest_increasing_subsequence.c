#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq
      (LISLength : list Z -> Z -> Prop)
      (LISDPState : list Z -> list Z -> Z -> Prop)
      (LISOuterState : list Z -> list Z -> Z -> Z -> Prop)
      (LISInnerBest : list Z -> list Z -> Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.longest_increasing_subsequence.longest_increasing_subsequence_lib */

int lengthOfLIS(int *nums, int numsSize, int *dp)
/*@ With (l : list Z)
    Require
      1 <= numsSize && numsSize <= 100000 &&
      Zlength(l) == numsSize &&
      IntArray::full(nums, numsSize, l) *
      IntArray::undef_full(dp, numsSize)
    Ensure
      exists d,
      LISLength(l, __return) &&
      LISDPState(l, d, numsSize) &&
      1 <= __return && __return <= numsSize &&
      IntArray::full(nums, numsSize, l) *
      IntArray::full(dp, numsSize, d)
 */
{
  int ans = 1;

  /*@ Inv Assert
      exists d,
      nums == nums@pre && dp == dp@pre && numsSize == numsSize@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100000 &&
      Zlength(l) == numsSize@pre &&
      0 <= i && i <= numsSize@pre &&
      Zlength(d) == i &&
      (forall (k : Z), (0 <= k && k < i) => (1 <= d[k] && d[k] <= i)) &&
      LISOuterState(l, d, i, ans) &&
      IntArray::full(nums@pre, numsSize@pre, l) *
      IntArray::seg(dp@pre, 0, i, d) *
      IntArray::undef_seg(dp@pre, i, numsSize@pre)
   */
  for (int i = 0; i < numsSize; ++i) {
    dp[i] = 1;

    /*@ Assert
      exists d,
      nums == nums@pre && dp == dp@pre && numsSize == numsSize@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100000 &&
      Zlength(l) == numsSize@pre &&
      0 <= i && i < numsSize@pre &&
      Zlength(d) == i &&
      (forall (k : Z), (0 <= k && k < i) => (1 <= d[k] && d[k] <= i)) &&
      LISOuterState(l, d, i, ans) &&
      LISInnerBest(l, d, i, 0, 1) &&
      IntArray::full(nums@pre, numsSize@pre, l) *
      IntArray::seg(dp@pre, 0, i + 1, app(d, cons(1, nil))) *
      IntArray::undef_seg(dp@pre, i + 1, numsSize@pre)
     */

    /*@ Inv Assert
      exists d best,
      nums == nums@pre && dp == dp@pre && numsSize == numsSize@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100000 &&
      Zlength(l) == numsSize@pre &&
      0 <= i && i < numsSize@pre &&
      0 <= j && j <= i &&
      Zlength(d) == i &&
      (forall (k : Z), (0 <= k && k < i) => (1 <= d[k] && d[k] <= i)) &&
      1 <= best && best <= i + 1 &&
      LISOuterState(l, d, i, ans) &&
      LISInnerBest(l, d, i, j, best) &&
      IntArray::full(nums@pre, numsSize@pre, l) *
      IntArray::seg(dp@pre, 0, i + 1, app(d, cons(best, nil))) *
      IntArray::undef_seg(dp@pre, i + 1, numsSize@pre)
     */
    for (int j = 0; j < i; ++j) {
      if (nums[j] < nums[i]) {
        int candidate = dp[j] + 1;
        /*@ Assert
          exists d best,
          nums == nums@pre && dp == dp@pre && numsSize == numsSize@pre &&
          1 <= numsSize@pre && numsSize@pre <= 100000 &&
          Zlength(l) == numsSize@pre &&
          0 <= i && i < numsSize@pre &&
          0 <= j && j < i &&
          Zlength(d) == i &&
          (forall (k : Z), (0 <= k && k < i) => (1 <= d[k] && d[k] <= i)) &&
          1 <= best && best <= i + 1 &&
          candidate == d[j] + 1 &&
          2 <= candidate && candidate <= i + 1 &&
          l[j] < l[i] &&
          LISOuterState(l, d, i, ans) &&
          LISInnerBest(l, d, i, j, best) &&
          IntArray::full(nums@pre, numsSize@pre, l) *
          IntArray::seg(dp@pre, 0, i + 1, app(d, cons(best, nil))) *
          IntArray::undef_seg(dp@pre, i + 1, numsSize@pre)
         */
        if (candidate > dp[i]) {
          dp[i] = candidate;
        }
      }
      /*@ Assert
        exists d best,
        nums == nums@pre && dp == dp@pre && numsSize == numsSize@pre &&
        1 <= numsSize@pre && numsSize@pre <= 100000 &&
        Zlength(l) == numsSize@pre &&
        0 <= i && i < numsSize@pre &&
        0 <= j && j < i &&
        Zlength(d) == i &&
        (forall (k : Z), (0 <= k && k < i) => (1 <= d[k] && d[k] <= i)) &&
        1 <= best && best <= i + 1 &&
        LISOuterState(l, d, i, ans) &&
        LISInnerBest(l, d, i, j + 1, best) &&
        IntArray::full(nums@pre, numsSize@pre, l) *
        IntArray::seg(dp@pre, 0, i + 1, app(d, cons(best, nil))) *
        IntArray::undef_seg(dp@pre, i + 1, numsSize@pre)
       */
    }

    /*@ Assert
      exists d best,
      nums == nums@pre && dp == dp@pre && numsSize == numsSize@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100000 &&
      Zlength(l) == numsSize@pre &&
      0 <= i && i < numsSize@pre &&
      Zlength(d) == i &&
      (forall (k : Z), (0 <= k && k < i) => (1 <= d[k] && d[k] <= i)) &&
      1 <= best && best <= i + 1 &&
      LISOuterState(l, d, i, ans) &&
      LISInnerBest(l, d, i, i, best) &&
      IntArray::full(nums@pre, numsSize@pre, l) *
      IntArray::seg(dp@pre, 0, i + 1, app(d, cons(best, nil))) *
      IntArray::undef_seg(dp@pre, i + 1, numsSize@pre)
     */
    if (dp[i] > ans) {
      ans = dp[i];
    }
    /*@ Assert
      exists d best,
      nums == nums@pre && dp == dp@pre && numsSize == numsSize@pre &&
      1 <= numsSize@pre && numsSize@pre <= 100000 &&
      Zlength(l) == numsSize@pre &&
      0 <= i && i < numsSize@pre &&
      Zlength(d) == i &&
      (forall (k : Z), (0 <= k && k < i) => (1 <= d[k] && d[k] <= i)) &&
      1 <= best && best <= i + 1 &&
      LISOuterState(l, app(d, cons(best, nil)), i + 1, ans) &&
      IntArray::full(nums@pre, numsSize@pre, l) *
      IntArray::seg(dp@pre, 0, i + 1, app(d, cons(best, nil))) *
      IntArray::undef_seg(dp@pre, i + 1, numsSize@pre)
     */
  }

  return ans;
}
