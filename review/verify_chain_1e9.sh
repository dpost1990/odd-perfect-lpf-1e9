#!/bin/zsh
# After the B=1e9 run (run_1e9.sh) and its finish script are done, run the full independent
# verification: all rows (rowverify) + independent tree check + checksums. Patterns use [x] tricks so this
# script's own command line never matches the pgrep patterns of the other scripts.
cd "$(dirname "$0")"
LPF=../runs
while pgrep -f "replay[.]py 1000000000" >/dev/null || pgrep -f "finish_1e9[.]sh" >/dev/null; do sleep 60; done
{
  echo "== chain start $(date)"
  tail -3 $LPF/c_1e9.out
  tail -2 $LPF/c_1000000000.log
  shasum -a 256 $LPF/rows_1000000000.txt $LPF/c_1000000000.log
  echo "== rowverify start $(date)"
  ./run_rowverify_1e9.sh 6 400
  echo "== tree_check start $(date)"
  nice -n 10 python3 tree_check.py 1000000000 $LPF/rows_1000000000.txt $LPF/c_1000000000.log runs/mup_1000000000.txt 2>&1 | tail -5
  echo "== chain end $(date)"
} > runs/verify_chain_1e9.out 2>&1
