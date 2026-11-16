#!/bin/zsh
# FULL independent verification of all rows of the B=1e9 run. NOT started automatically.
# Run only AFTER the lpf 1e9 run has finished (its rows file is then final). Resumable: a batch whose output
# already ends with a RESULT line is skipped.   usage: ./run_rowverify_1e9.sh [threads] [batch_size]
cd "$(dirname "$0")"
TH=${1:-2}; BS=${2:-400}
ROWS=../runs/rows_1000000000.txt
if pgrep -f "lpf 1000000000" >/dev/null; then echo "lpf 1e9 still running; refusing to start"; exit 1; fi
N=$(grep -c '' $ROWS)
for ((s=0; s<N; s+=BS)); do
  e=$((s+BS-1)); [ $e -ge $N ] && e=$((N-1))
  out=runs/rv_1e9_$s.out
  if [ -f $out ] && grep -q '^RESULT' $out; then continue; fi
  nice -n 10 ./rowverify 1000000000 $ROWS $TH $s $e > $out 2> runs/rv_1e9_$s.err
done
cat runs/rv_1e9_*.out | grep '^RESULT'
cat runs/rv_1e9_*.out | grep -c 'ok=1'; echo "rows in file: $N"
grep -h MISMATCH runs/rv_1e9_*.out | head
