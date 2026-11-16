#!/bin/zsh
# B=1e7: original lpf.c vs exact-filter copy, 2 threads each, sequential (nice 10)
cd "$(dirname "$0")"
for v in orig exact; do rm -f runs/rows_1e7_$v.txt
  /usr/bin/time -p nice -n 10 ./lpf_$v 10000000 2 odd 2 runs/rows_1e7_$v.txt runs/log_1e7_$v.log > runs/out_1e7_$v.txt 2> runs/err_1e7_$v.txt
done
{ cmp runs/rows_1e7_orig.txt runs/rows_1e7_exact.txt && echo ROWS_SAME
  cmp runs/log_1e7_orig.log runs/log_1e7_exact.log && echo LOG_SAME
  cmp runs/log_1e7_exact.log ../runs/c_10000000.log && echo LOG_SAME_AS_AUTHOR
  cmp runs/rows_1e7_exact.txt ../runs/rows_10000000.txt && echo ROWS_SAME_AS_AUTHOR
  grep -h -E "real|user|RESULT" runs/err_1e7_orig.txt runs/out_1e7_orig.txt runs/err_1e7_exact.txt runs/out_1e7_exact.txt; } > runs/compare_1e7.txt 2>&1
