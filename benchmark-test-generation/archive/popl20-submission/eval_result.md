Here is some result for current (commit 5d31160) implementation.

Some conclusions are:

1. Loop count in fig4's `main` and fig'6 `g` which around `if i = m then f m n` doesn't affect the result steps in working cases. It means we can set them to `1000`.
2. In dse_backotter3_fig4, `i_f` (max i in f) is 3 and `m` is 2.
3. In dse_backotter3_fig6, max `work` in main is 1. One of `i_f` and `m` can be 2.
4. In dse_backotter3_fig6, if we increase the three m in the same delta, like `42 <= m` with `g_loop 42` and `m = 43`, it's the same as `0 <= m` with `g_loop 0` andd `m = 1`.
5. In dse_distance_fig2_ignored_array_update (which I ignore the array update), the max working n is `n < 1`.
6. In input_nested_loops_sum

Some results:

The command is
` time ./test_generator -e relstack-rep -r 1 -t target <test>`

## for dse_backotter3_fig4

i_f = 1, m = 1, i_main = 2
    => [1, 2], 20091
[local]         1.77s user 0.09s system 99% cpu 1.870 total

i_f = 1, m = 1, i_main = 3
    => [1, 2], 20091
[local]         1.70s user 0.08s system 99% cpu 1.790 total

i_f = 1, m = 1, i_main = 10
    => [1, 2], 20091
[local]         1.73s user 0.05s system 99% cpu 1.797 total

i_f = 1, m = 2, i_main = 3
    => [2, 2], 154988
[local]         26.52s user 0.17s system 99% cpu 26.742 total

i_f = 1, m = 2, i_main = 4
    => [2, 2], 154988
[local]         25.66s user 0.20s system 99% cpu 25.903 total

i_f = 1, m = 2, i_main = 10
    => [2, 2], 154988
[local]         25.80s user 0.14s system 99% cpu 26.069 total

i_f = 1, m = 2, i_main = 1000
    => [2, 2], 154988
[local]         26.28s user 0.12s system 99% cpu 26.477 total

> the `i_main` doesn't affect the result when specifying just to find the first test with `-r 1`. Therefore, we can fix it to `1000`

i_f = 1, m = 3 => +inf (>9.2min)    

i_f = 2, m = 2 => [2, 4], 202125  # the same as Scott's post
[local]       38.97s user 0.28s system 99% cpu 39.378 total

i_f = 2, m = 3 => +inf (>57.6min)

i_f = 3, m = 1 => [1, 8], 495526
[local]       176.56s user 0.44s system 99% cpu 2:57.80 total

i_f = 3, m = 2 => [2, 8], 539518
[local]       203.64s user 0.44s system 99% cpu 3:24.91 total

i_f = 4, m = 1 => +inf (>17.6min)


## for dse_backotter3_fig6

i_f = 1, m = 1, i_g = 2, work = 0, 0 <= m
=> [1, 2], 65129
[local]       16.88s user 0.16s system 99% cpu 17.100 total

i_f = 1, m = 1, i_g = 2, work = 1, 0 <= m
=> [1, 2], 65097
[local]       14.25s user 0.16s system 99% cpu 14.459 total

i_f = 1, m = 1, i_g = 2, work = 2, 0 <= m
=> +inf (>6.7min)

i_f = 1, m = 1, i_g = 3, work = 1, 0 <= m
=> [1, 2], 65097
[local]       16.70s user 0.09s system 99% cpu 16.858 total

i_f = 1, m = 1, i_g = 1000, work = 1, 0 <= m
=> [1, 2], 65097
[local]       17.16s user 0.08s system 99% cpu 17.320 total

> Here we can have the same conclusion as `fig4` that the iteration times in `g` doesn't affect the running time. Therefore, we can set it to 1000.

i_f = 1, m = 2, work = 1, 0 <= m
=> [2, 2], 1210704
[local]       650.09s user 0.53s system 99% cpu 10:54.13 total

i_f = 2, m = 1, work = 1, 0 <= m
> [1, 4], 373980
[local]       167.30s user 0.27s system 99% cpu 2:47.99 total

i_f = 3, m = 1, work = 1, 0 <= m
=> +inf (>7.67min)

if `m` start from 30 at `g_loop 30` and check for `m == 31` with `30 <= m`, then we get (the same as `i=1, m=1`):
=> [31, 2], 65097
[local]       15.69s user 0.09s system 99% cpu 15.817 total

if `m` start from 41 at `g_loop 41` and check for `m == 43` with `30 <= m`, then we get
=> [43, 2], 1210704
[local]       787.33s user 0.78s system 99% cpu 13:08.80 total

if `m` start from 42 at `g_loop 42` and check for `m == 43` with `42 <= m`, then we get
=> [43, 2], 65097
[local]       16.38s user 0.11s system 99% cpu 16.517 total

## for dse_distance_fig2_ignored_array_update

n < 4
=> +inf (>34.9min)

n < 1
=> [2, 98, 98, 0, 0, 0, 0, 0, 0], 1338348
[local]       121.17s user 0.33s system 99% cpu 2:01.59 total

n < 2
=> +inf (>30.2min)

## input_nested_loops_sum

j = 2, i = 2, [1, 0], 65722
[local+flambda]   12.38s

j = 2, i = 3, [1, 0], 65722
[local+flambda]   12.38s

j = 2, i = 5, [1, 0], 65722
[local+flambda]   12.38s

j = 2, i = 100, [1, 0], 65722
[local+flambda]   12.38s

j = 3, i = 1, +inf
[local+flambda]   > 600s

j = 3, i = 2, +inf
[local+flambda]   > 600s
