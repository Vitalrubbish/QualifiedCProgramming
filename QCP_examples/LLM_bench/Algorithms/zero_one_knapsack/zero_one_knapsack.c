#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq
      (KnapsackPlanValue : list Z -> list Z -> list Z -> Z -> Prop)
      (KnapsackPlan : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (KnapsackMaxValue : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (KnapsackCellCorrect : list Z -> list Z -> Z -> Z -> Z -> Prop)
      (KnapsackTablePrefix : list Z -> list Z -> Z -> list Z -> Z -> Prop)
      (KnapsackRowsDone : list Z -> list Z -> Z -> list Z -> Z -> Prop)
      (KnapsackRowProgress : list Z -> list Z -> Z -> list Z -> Z -> Z -> Prop)
 */
/*@ Import Coq Require Import SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack.zero_one_knapsack_lib */

int zeroOneKnapsack(int *weights, int *values, int n, int capacity, int *dp)
/*@ With (weights_l values_l : list Z)
    Require
      0 <= n && n <= 300 &&
      0 <= capacity && capacity <= 300 &&
      Zlength(weights_l) == n &&
      Zlength(values_l) == n &&
      IntArray::full(weights, n, weights_l) *
      IntArray::full(values, n, values_l) *
      IntArray::undef_full(dp, (n + 1) * (capacity + 1)) &&
      (forall (k : Z), (0 <= k && k < n) =>
        (1 <= weights_l[k] && weights_l[k] <= capacity + 1)) &&
      (forall (k : Z), (0 <= k && k < n) =>
        (0 <= values_l[k] && values_l[k] <= 10000))
    Ensure
      exists dp_l,
      KnapsackMaxValue(weights_l, values_l, n, capacity, __return) &&
      0 <= __return && __return <= 4000000 &&
      KnapsackRowsDone(weights_l, values_l, capacity, dp_l, n + 1) &&
      IntArray::full(weights, n, weights_l) *
      IntArray::full(values, n, values_l) *
      IntArray::full(dp, (n + 1) * (capacity + 1), dp_l)
 */
{
  int width = capacity + 1;

  /*@ Assert
      weights == weights@pre && values == values@pre && dp == dp@pre &&
      n == n@pre && capacity == capacity@pre &&
      width == capacity@pre + 1 &&
      0 <= n@pre && n@pre <= 300 &&
      0 <= capacity@pre && capacity@pre <= 300 &&
      1 <= width && width <= 301 &&
      Zlength(weights_l) == n@pre &&
      Zlength(values_l) == n@pre &&
      IntArray::full(weights, n@pre, weights_l) *
      IntArray::full(values, n@pre, values_l) *
      IntArray::undef_full(dp, (n@pre + 1) * (capacity@pre + 1)) &&
      (forall (k : Z), (0 <= k && k < n@pre) =>
        (1 <= weights_l[k] && weights_l[k] <= capacity@pre + 1)) &&
      (forall (k : Z), (0 <= k && k < n@pre) =>
        (0 <= values_l[k] && values_l[k] <= 10000))
   */
  /*@ Inv Assert
      exists dp_l,
      weights == weights@pre && values == values@pre && dp == dp@pre &&
      n == n@pre && capacity == capacity@pre &&
      width == capacity@pre + 1 &&
      0 <= n@pre && n@pre <= 300 &&
      0 <= capacity@pre && capacity@pre <= 300 &&
      1 <= width && width <= 301 &&
      Zlength(weights_l) == n@pre &&
      Zlength(values_l) == n@pre &&
      0 <= i && i <= n@pre + 1 &&
      0 <= i * width && i * width <= (n@pre + 1) * (capacity@pre + 1) &&
      KnapsackRowsDone(weights_l, values_l, capacity@pre, dp_l, i) &&
      (forall (k : Z), (0 <= k && k < Zlength(dp_l)) =>
        (0 <= dp_l[k] && dp_l[k] <= 4000000)) &&
      IntArray::full(weights, n@pre, weights_l) *
      IntArray::full(values, n@pre, values_l) *
      IntArray::seg(dp, 0, i * width, dp_l) *
      IntArray::undef_seg(dp, i * width, (n@pre + 1) * (capacity@pre + 1)) &&
      (forall (k : Z), (0 <= k && k < n@pre) =>
        (1 <= weights_l[k] && weights_l[k] <= capacity@pre + 1)) &&
      (forall (k : Z), (0 <= k && k < n@pre) =>
        (0 <= values_l[k] && values_l[k] <= 10000))
   */
  for (int i = 0; i <= n; ++i) {
    /*@ Inv Assert
        exists dp_l,
        weights == weights@pre && values == values@pre && dp == dp@pre &&
        n == n@pre && capacity == capacity@pre &&
        width == capacity@pre + 1 &&
        0 <= n@pre && n@pre <= 300 &&
        0 <= capacity@pre && capacity@pre <= 300 &&
        1 <= width && width <= 301 &&
        Zlength(weights_l) == n@pre &&
        Zlength(values_l) == n@pre &&
        0 <= i && i <= n@pre &&
        0 <= j && j <= capacity@pre + 1 &&
        0 <= i * width + j &&
        i * width + j <= (n@pre + 1) * (capacity@pre + 1) &&
        KnapsackRowProgress(weights_l, values_l, capacity@pre, dp_l, i, j) &&
        (forall (k : Z), (0 <= k && k < Zlength(dp_l)) =>
          (0 <= dp_l[k] && dp_l[k] <= 4000000)) &&
        IntArray::full(weights, n@pre, weights_l) *
        IntArray::full(values, n@pre, values_l) *
        IntArray::seg(dp, 0, i * width + j, dp_l) *
        IntArray::undef_seg(dp, i * width + j, (n@pre + 1) * (capacity@pre + 1)) &&
        (forall (k : Z), (0 <= k && k < n@pre) =>
          (1 <= weights_l[k] && weights_l[k] <= capacity@pre + 1)) &&
        (forall (k : Z), (0 <= k && k < n@pre) =>
          (0 <= values_l[k] && values_l[k] <= 10000))
     */
    for (int j = 0; j <= capacity; ++j) {
      int idx = i * width + j;
      /*@ Assert
          exists dp_l,
          weights == weights@pre && values == values@pre && dp == dp@pre &&
          n == n@pre && capacity == capacity@pre &&
          width == capacity@pre + 1 &&
          0 <= n@pre && n@pre <= 300 &&
          0 <= capacity@pre && capacity@pre <= 300 &&
          1 <= width && width <= 301 &&
          Zlength(weights_l) == n@pre &&
          Zlength(values_l) == n@pre &&
          0 <= i && i <= n@pre &&
          0 <= j && j <= capacity@pre &&
          idx == i * width + j &&
          0 <= idx && idx < (n@pre + 1) * (capacity@pre + 1) &&
          idx + 1 <= (n@pre + 1) * (capacity@pre + 1) &&
          0 <= idx && idx < (n@pre + 1) * (capacity@pre + 1) &&
          KnapsackRowProgress(weights_l, values_l, capacity@pre, dp_l, i, j) &&
          (forall (k : Z), (0 <= k && k < Zlength(dp_l)) =>
            (0 <= dp_l[k] && dp_l[k] <= 4000000)) &&
          IntArray::full(weights, n@pre, weights_l) *
          IntArray::full(values, n@pre, values_l) *
          IntArray::seg(dp, 0, idx, dp_l) *
          IntArray::undef_seg(dp, idx, (n@pre + 1) * (capacity@pre + 1)) &&
          (forall (k : Z), (0 <= k && k < n@pre) =>
            (1 <= weights_l[k] && weights_l[k] <= capacity@pre + 1)) &&
          (forall (k : Z), (0 <= k && k < n@pre) =>
            (0 <= values_l[k] && values_l[k] <= 10000))
       */

      if (i == 0) {
        dp[idx] = 0;
        /*@ Assert
            exists dp_l,
            weights == weights@pre && values == values@pre && dp == dp@pre &&
            n == n@pre && capacity == capacity@pre &&
            width == capacity@pre + 1 &&
            0 <= n@pre && n@pre <= 300 &&
            0 <= capacity@pre && capacity@pre <= 300 &&
            1 <= width && width <= 301 &&
            Zlength(weights_l) == n@pre &&
            Zlength(values_l) == n@pre &&
            0 <= i && i <= n@pre &&
            0 <= j && j <= capacity@pre &&
            idx == i * width + j &&
            0 <= idx && idx < (n@pre + 1) * (capacity@pre + 1) &&
            idx + 1 <= (n@pre + 1) * (capacity@pre + 1) &&
            KnapsackCellCorrect(weights_l, values_l, i, j, 0) &&
            KnapsackRowProgress(weights_l, values_l, capacity@pre, dp_l, i, j + 1) &&
            (forall (k : Z), (0 <= k && k < Zlength(dp_l)) =>
              (0 <= dp_l[k] && dp_l[k] <= 4000000)) &&
            IntArray::full(weights, n@pre, weights_l) *
            IntArray::full(values, n@pre, values_l) *
            IntArray::seg(dp, 0, idx + 1, dp_l) *
            IntArray::undef_seg(dp, idx + 1, (n@pre + 1) * (capacity@pre + 1)) &&
            (forall (k : Z), (0 <= k && k < n@pre) =>
              (1 <= weights_l[k] && weights_l[k] <= capacity@pre + 1)) &&
            (forall (k : Z), (0 <= k && k < n@pre) =>
              (0 <= values_l[k] && values_l[k] <= 10000))
         */
      } else if (j == 0) {
        dp[idx] = 0;
        /*@ Assert
            exists dp_l,
            weights == weights@pre && values == values@pre && dp == dp@pre &&
            n == n@pre && capacity == capacity@pre &&
            width == capacity@pre + 1 &&
            0 <= n@pre && n@pre <= 300 &&
            0 <= capacity@pre && capacity@pre <= 300 &&
            1 <= width && width <= 301 &&
            Zlength(weights_l) == n@pre &&
            Zlength(values_l) == n@pre &&
            1 <= i && i <= n@pre &&
            j == 0 &&
            idx == i * width + j &&
            0 <= idx && idx < (n@pre + 1) * (capacity@pre + 1) &&
            idx + 1 <= (n@pre + 1) * (capacity@pre + 1) &&
            KnapsackCellCorrect(weights_l, values_l, i, j, 0) &&
            KnapsackRowProgress(weights_l, values_l, capacity@pre, dp_l, i, j + 1) &&
            (forall (k : Z), (0 <= k && k < Zlength(dp_l)) =>
              (0 <= dp_l[k] && dp_l[k] <= 4000000)) &&
            IntArray::full(weights, n@pre, weights_l) *
            IntArray::full(values, n@pre, values_l) *
            IntArray::seg(dp, 0, idx + 1, dp_l) *
            IntArray::undef_seg(dp, idx + 1, (n@pre + 1) * (capacity@pre + 1)) &&
            (forall (k : Z), (0 <= k && k < n@pre) =>
              (1 <= weights_l[k] && weights_l[k] <= capacity@pre + 1)) &&
            (forall (k : Z), (0 <= k && k < n@pre) =>
              (0 <= values_l[k] && values_l[k] <= 10000))
         */
      } else {
        int item = i - 1;
        int w = weights[item];
        int v = values[item];
        /*@ Assert
            exists dp_l,
            weights == weights@pre && values == values@pre && dp == dp@pre &&
            n == n@pre && capacity == capacity@pre &&
            width == capacity@pre + 1 &&
            0 <= n@pre && n@pre <= 300 &&
            0 <= capacity@pre && capacity@pre <= 300 &&
            1 <= width && width <= 301 &&
            Zlength(weights_l) == n@pre &&
            Zlength(values_l) == n@pre &&
            1 <= i && i <= n@pre &&
            1 <= j && j <= capacity@pre &&
            item == i - 1 &&
            0 <= item && item < n@pre &&
            w == weights_l[item] &&
            v == values_l[item] &&
            1 <= w && w <= capacity@pre + 1 &&
            0 <= v && v <= 10000 &&
            idx == i * width + j &&
            0 <= idx && idx < (n@pre + 1) * (capacity@pre + 1) &&
            idx + 1 <= (n@pre + 1) * (capacity@pre + 1) &&
            0 <= (i - 1) * width + j &&
            (i - 1) * width + j < idx &&
            (i - 1) * width + j < (n@pre + 1) * (capacity@pre + 1) &&
            KnapsackRowProgress(weights_l, values_l, capacity@pre, dp_l, i, j) &&
            (forall (k : Z), (0 <= k && k < Zlength(dp_l)) =>
              (0 <= dp_l[k] && dp_l[k] <= 4000000)) &&
            IntArray::full(weights, n@pre, weights_l) *
            IntArray::full(values, n@pre, values_l) *
            IntArray::seg(dp, 0, idx, dp_l) *
            IntArray::undef_seg(dp, idx, (n@pre + 1) * (capacity@pre + 1)) &&
            (forall (k : Z), (0 <= k && k < n@pre) =>
              (1 <= weights_l[k] && weights_l[k] <= capacity@pre + 1)) &&
            (forall (k : Z), (0 <= k && k < n@pre) =>
              (0 <= values_l[k] && values_l[k] <= 10000))
         */
        int without = dp[(i - 1) * width + j];
        /*@ Assert
            exists dp_l,
            weights == weights@pre && values == values@pre && dp == dp@pre &&
            n == n@pre && capacity == capacity@pre &&
            width == capacity@pre + 1 &&
            0 <= n@pre && n@pre <= 300 &&
            0 <= capacity@pre && capacity@pre <= 300 &&
            1 <= width && width <= 301 &&
            Zlength(weights_l) == n@pre &&
            Zlength(values_l) == n@pre &&
            1 <= i && i <= n@pre &&
            1 <= j && j <= capacity@pre &&
            item == i - 1 &&
            0 <= item && item < n@pre &&
            w == weights_l[item] &&
            v == values_l[item] &&
            1 <= w && w <= capacity@pre + 1 &&
            0 <= v && v <= 10000 &&
            idx == i * width + j &&
            0 <= idx && idx < (n@pre + 1) * (capacity@pre + 1) &&
            idx + 1 <= (n@pre + 1) * (capacity@pre + 1) &&
            without == dp_l[(i - 1) * width + j] &&
            0 <= without && without <= 4000000 &&
            KnapsackCellCorrect(weights_l, values_l, i - 1, j, without) &&
            KnapsackRowProgress(weights_l, values_l, capacity@pre, dp_l, i, j) &&
            (forall (k : Z), (0 <= k && k < Zlength(dp_l)) =>
              (0 <= dp_l[k] && dp_l[k] <= 4000000)) &&
            IntArray::full(weights, n@pre, weights_l) *
            IntArray::full(values, n@pre, values_l) *
            IntArray::seg(dp, 0, idx, dp_l) *
            IntArray::undef_seg(dp, idx, (n@pre + 1) * (capacity@pre + 1)) &&
            (forall (k : Z), (0 <= k && k < n@pre) =>
              (1 <= weights_l[k] && weights_l[k] <= capacity@pre + 1)) &&
            (forall (k : Z), (0 <= k && k < n@pre) =>
              (0 <= values_l[k] && values_l[k] <= 10000))
         */

        if (w <= j) {
          /*@ Assert
              exists dp_l,
              weights == weights@pre && values == values@pre && dp == dp@pre &&
              n == n@pre && capacity == capacity@pre &&
              width == capacity@pre + 1 &&
              0 <= n@pre && n@pre <= 300 &&
              0 <= capacity@pre && capacity@pre <= 300 &&
              1 <= width && width <= 301 &&
              Zlength(weights_l) == n@pre &&
              Zlength(values_l) == n@pre &&
              1 <= i && i <= n@pre &&
              1 <= j && j <= capacity@pre &&
              item == i - 1 &&
              0 <= item && item < n@pre &&
              w == weights_l[item] &&
              v == values_l[item] &&
              1 <= w && w <= j &&
              0 <= v && v <= 10000 &&
              idx == i * width + j &&
              0 <= idx && idx < (n@pre + 1) * (capacity@pre + 1) &&
              idx + 1 <= (n@pre + 1) * (capacity@pre + 1) &&
              without == dp_l[(i - 1) * width + j] &&
              0 <= without && without <= 4000000 &&
              0 <= j - w &&
              j - w <= capacity@pre &&
              0 <= (i - 1) * width + (j - w) &&
              (i - 1) * width + (j - w) < idx &&
              (i - 1) * width + (j - w) < (n@pre + 1) * (capacity@pre + 1) &&
              KnapsackCellCorrect(weights_l, values_l, i - 1, j, without) &&
              KnapsackRowProgress(weights_l, values_l, capacity@pre, dp_l, i, j) &&
              (forall (k : Z), (0 <= k && k < Zlength(dp_l)) =>
                (0 <= dp_l[k] && dp_l[k] <= 4000000)) &&
              IntArray::full(weights, n@pre, weights_l) *
              IntArray::full(values, n@pre, values_l) *
              IntArray::seg(dp, 0, idx, dp_l) *
              IntArray::undef_seg(dp, idx, (n@pre + 1) * (capacity@pre + 1)) &&
              (forall (k : Z), (0 <= k && k < n@pre) =>
                (1 <= weights_l[k] && weights_l[k] <= capacity@pre + 1)) &&
              (forall (k : Z), (0 <= k && k < n@pre) =>
                (0 <= values_l[k] && values_l[k] <= 10000))
           */
          int prev = dp[(i - 1) * width + (j - w)];
          /*@ Assert
              exists dp_l,
              weights == weights@pre && values == values@pre && dp == dp@pre &&
              n == n@pre && capacity == capacity@pre &&
              width == capacity@pre + 1 &&
              0 <= n@pre && n@pre <= 300 &&
              0 <= capacity@pre && capacity@pre <= 300 &&
              1 <= width && width <= 301 &&
              Zlength(weights_l) == n@pre &&
              Zlength(values_l) == n@pre &&
              1 <= i && i <= n@pre &&
              1 <= j && j <= capacity@pre &&
              item == i - 1 &&
              0 <= item && item < n@pre &&
              w == weights_l[item] &&
              v == values_l[item] &&
              1 <= w && w <= j &&
              0 <= v && v <= 10000 &&
              idx == i * width + j &&
              0 <= idx && idx < (n@pre + 1) * (capacity@pre + 1) &&
              idx + 1 <= (n@pre + 1) * (capacity@pre + 1) &&
              without == dp_l[(i - 1) * width + j] &&
              prev == dp_l[(i - 1) * width + (j - w)] &&
              0 <= without && without <= 4000000 &&
              0 <= prev && prev <= 4000000 &&
              INT_MIN <= prev + v && prev + v <= INT_MAX &&
              KnapsackCellCorrect(weights_l, values_l, i - 1, j, without) &&
              KnapsackCellCorrect(weights_l, values_l, i - 1, j - w, prev) &&
              KnapsackRowProgress(weights_l, values_l, capacity@pre, dp_l, i, j) &&
              (forall (k : Z), (0 <= k && k < Zlength(dp_l)) =>
                (0 <= dp_l[k] && dp_l[k] <= 4000000)) &&
              IntArray::full(weights, n@pre, weights_l) *
              IntArray::full(values, n@pre, values_l) *
              IntArray::seg(dp, 0, idx, dp_l) *
              IntArray::undef_seg(dp, idx, (n@pre + 1) * (capacity@pre + 1)) &&
              (forall (k : Z), (0 <= k && k < n@pre) =>
                (1 <= weights_l[k] && weights_l[k] <= capacity@pre + 1)) &&
              (forall (k : Z), (0 <= k && k < n@pre) =>
                (0 <= values_l[k] && values_l[k] <= 10000))
           */
          int with_val = prev + v;
          if (with_val > without) {
            dp[idx] = with_val;
            /*@ Assert
                exists dp_l,
                weights == weights@pre && values == values@pre && dp == dp@pre &&
                n == n@pre && capacity == capacity@pre &&
                width == capacity@pre + 1 &&
                0 <= n@pre && n@pre <= 300 &&
                0 <= capacity@pre && capacity@pre <= 300 &&
                1 <= width && width <= 301 &&
                Zlength(weights_l) == n@pre &&
                Zlength(values_l) == n@pre &&
                1 <= i && i <= n@pre &&
                1 <= j && j <= capacity@pre &&
                item == i - 1 &&
                w == weights_l[item] &&
                v == values_l[item] &&
                1 <= w && w <= j &&
                0 <= v && v <= 10000 &&
                idx == i * width + j &&
                0 <= idx && idx < (n@pre + 1) * (capacity@pre + 1) &&
                idx + 1 <= (n@pre + 1) * (capacity@pre + 1) &&
                without == dp_l[(i - 1) * width + j] &&
                prev == dp_l[(i - 1) * width + (j - w)] &&
                with_val == prev + v &&
                with_val > without &&
                0 <= with_val && with_val <= 4000000 &&
                KnapsackCellCorrect(weights_l, values_l, i, j, with_val) &&
                KnapsackRowProgress(weights_l, values_l, capacity@pre, dp_l, i, j + 1) &&
                (forall (k : Z), (0 <= k && k < Zlength(dp_l)) =>
                  (0 <= dp_l[k] && dp_l[k] <= 4000000)) &&
                IntArray::full(weights, n@pre, weights_l) *
                IntArray::full(values, n@pre, values_l) *
                IntArray::seg(dp, 0, idx + 1, dp_l) *
                IntArray::undef_seg(dp, idx + 1, (n@pre + 1) * (capacity@pre + 1)) &&
                (forall (k : Z), (0 <= k && k < n@pre) =>
                  (1 <= weights_l[k] && weights_l[k] <= capacity@pre + 1)) &&
                (forall (k : Z), (0 <= k && k < n@pre) =>
                  (0 <= values_l[k] && values_l[k] <= 10000))
             */
          } else {
            dp[idx] = without;
            /*@ Assert
                exists dp_l,
                weights == weights@pre && values == values@pre && dp == dp@pre &&
                n == n@pre && capacity == capacity@pre &&
                width == capacity@pre + 1 &&
                0 <= n@pre && n@pre <= 300 &&
                0 <= capacity@pre && capacity@pre <= 300 &&
                1 <= width && width <= 301 &&
                Zlength(weights_l) == n@pre &&
                Zlength(values_l) == n@pre &&
                1 <= i && i <= n@pre &&
                1 <= j && j <= capacity@pre &&
                item == i - 1 &&
                w == weights_l[item] &&
                v == values_l[item] &&
                1 <= w && w <= j &&
                0 <= v && v <= 10000 &&
                idx == i * width + j &&
                0 <= idx && idx < (n@pre + 1) * (capacity@pre + 1) &&
                idx + 1 <= (n@pre + 1) * (capacity@pre + 1) &&
                without == dp_l[(i - 1) * width + j] &&
                prev == dp_l[(i - 1) * width + (j - w)] &&
                with_val == prev + v &&
                with_val <= without &&
                0 <= without && without <= 4000000 &&
                KnapsackCellCorrect(weights_l, values_l, i, j, without) &&
                KnapsackRowProgress(weights_l, values_l, capacity@pre, dp_l, i, j + 1) &&
                (forall (k : Z), (0 <= k && k < Zlength(dp_l)) =>
                  (0 <= dp_l[k] && dp_l[k] <= 4000000)) &&
                IntArray::full(weights, n@pre, weights_l) *
                IntArray::full(values, n@pre, values_l) *
                IntArray::seg(dp, 0, idx + 1, dp_l) *
                IntArray::undef_seg(dp, idx + 1, (n@pre + 1) * (capacity@pre + 1)) &&
                (forall (k : Z), (0 <= k && k < n@pre) =>
                  (1 <= weights_l[k] && weights_l[k] <= capacity@pre + 1)) &&
                (forall (k : Z), (0 <= k && k < n@pre) =>
                  (0 <= values_l[k] && values_l[k] <= 10000))
             */
          }
        } else {
          dp[idx] = without;
          /*@ Assert
              exists dp_l,
              weights == weights@pre && values == values@pre && dp == dp@pre &&
              n == n@pre && capacity == capacity@pre &&
              width == capacity@pre + 1 &&
              0 <= n@pre && n@pre <= 300 &&
              0 <= capacity@pre && capacity@pre <= 300 &&
              1 <= width && width <= 301 &&
              Zlength(weights_l) == n@pre &&
              Zlength(values_l) == n@pre &&
              1 <= i && i <= n@pre &&
              1 <= j && j <= capacity@pre &&
              item == i - 1 &&
              w == weights_l[item] &&
              v == values_l[item] &&
              j < w &&
              idx == i * width + j &&
              0 <= idx && idx < (n@pre + 1) * (capacity@pre + 1) &&
              idx + 1 <= (n@pre + 1) * (capacity@pre + 1) &&
              without == dp_l[(i - 1) * width + j] &&
              0 <= without && without <= 4000000 &&
              KnapsackCellCorrect(weights_l, values_l, i, j, without) &&
              KnapsackRowProgress(weights_l, values_l, capacity@pre, dp_l, i, j + 1) &&
              (forall (k : Z), (0 <= k && k < Zlength(dp_l)) =>
                (0 <= dp_l[k] && dp_l[k] <= 4000000)) &&
              IntArray::full(weights, n@pre, weights_l) *
              IntArray::full(values, n@pre, values_l) *
              IntArray::seg(dp, 0, idx + 1, dp_l) *
              IntArray::undef_seg(dp, idx + 1, (n@pre + 1) * (capacity@pre + 1)) &&
              (forall (k : Z), (0 <= k && k < n@pre) =>
                (1 <= weights_l[k] && weights_l[k] <= capacity@pre + 1)) &&
              (forall (k : Z), (0 <= k && k < n@pre) =>
                (0 <= values_l[k] && values_l[k] <= 10000))
           */
        }
      }
      /*@ Assert
          exists dp_l,
          weights == weights@pre && values == values@pre && dp == dp@pre &&
          n == n@pre && capacity == capacity@pre &&
          width == capacity@pre + 1 &&
          0 <= n@pre && n@pre <= 300 &&
          0 <= capacity@pre && capacity@pre <= 300 &&
          1 <= width && width <= 301 &&
          Zlength(weights_l) == n@pre &&
          Zlength(values_l) == n@pre &&
          0 <= i && i <= n@pre &&
          0 <= j && j <= capacity@pre &&
          idx == i * width + j &&
          0 <= idx && idx < (n@pre + 1) * (capacity@pre + 1) &&
          idx + 1 <= (n@pre + 1) * (capacity@pre + 1) &&
          KnapsackRowProgress(weights_l, values_l, capacity@pre, dp_l, i, j + 1) &&
          (forall (k : Z), (0 <= k && k < Zlength(dp_l)) =>
            (0 <= dp_l[k] && dp_l[k] <= 4000000)) &&
          IntArray::full(weights, n@pre, weights_l) *
          IntArray::full(values, n@pre, values_l) *
          IntArray::seg(dp, 0, idx + 1, dp_l) *
          IntArray::undef_seg(dp, idx + 1, (n@pre + 1) * (capacity@pre + 1)) &&
          (forall (k : Z), (0 <= k && k < n@pre) =>
            (1 <= weights_l[k] && weights_l[k] <= capacity@pre + 1)) &&
          (forall (k : Z), (0 <= k && k < n@pre) =>
            (0 <= values_l[k] && values_l[k] <= 10000))
       */
    }
    /*@ Assert
        exists dp_l,
        weights == weights@pre && values == values@pre && dp == dp@pre &&
        n == n@pre && capacity == capacity@pre &&
        width == capacity@pre + 1 &&
        0 <= n@pre && n@pre <= 300 &&
        0 <= capacity@pre && capacity@pre <= 300 &&
        1 <= width && width <= 301 &&
        Zlength(weights_l) == n@pre &&
        Zlength(values_l) == n@pre &&
        0 <= i && i <= n@pre &&
        KnapsackRowsDone(weights_l, values_l, capacity@pre, dp_l, i + 1) &&
        (forall (k : Z), (0 <= k && k < Zlength(dp_l)) =>
          (0 <= dp_l[k] && dp_l[k] <= 4000000)) &&
        IntArray::full(weights, n@pre, weights_l) *
        IntArray::full(values, n@pre, values_l) *
        IntArray::seg(dp, 0, (i + 1) * width, dp_l) *
        IntArray::undef_seg(dp, (i + 1) * width, (n@pre + 1) * (capacity@pre + 1)) &&
        (forall (k : Z), (0 <= k && k < n@pre) =>
          (1 <= weights_l[k] && weights_l[k] <= capacity@pre + 1)) &&
        (forall (k : Z), (0 <= k && k < n@pre) =>
          (0 <= values_l[k] && values_l[k] <= 10000))
     */
  }

  /*@ Assert
      exists dp_l,
      weights == weights@pre && values == values@pre && dp == dp@pre &&
      n == n@pre && capacity == capacity@pre &&
      width == capacity@pre + 1 &&
      0 <= n@pre && n@pre <= 300 &&
      0 <= capacity@pre && capacity@pre <= 300 &&
      1 <= width && width <= 301 &&
      Zlength(weights_l) == n@pre &&
      Zlength(values_l) == n@pre &&
      n * width + capacity == n@pre * width + capacity@pre &&
      0 <= n * width + capacity &&
      n * width + capacity < (n@pre + 1) * (capacity@pre + 1) &&
      KnapsackRowsDone(weights_l, values_l, capacity@pre, dp_l, n@pre + 1) &&
      KnapsackMaxValue(weights_l, values_l, n@pre, capacity@pre,
        dp_l[n@pre * width + capacity@pre]) &&
      0 <= dp_l[n@pre * width + capacity@pre] &&
      dp_l[n@pre * width + capacity@pre] <= 4000000 &&
      IntArray::full(weights, n@pre, weights_l) *
      IntArray::full(values, n@pre, values_l) *
      IntArray::full(dp, (n@pre + 1) * (capacity@pre + 1), dp_l)
   */
  return dp[n * width + capacity];
}
