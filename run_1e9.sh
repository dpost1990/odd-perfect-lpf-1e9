#!/bin/zsh
# Resumable B=1e9 run: rows are appended to runs/rows_1000000000.txt (the checkpoint); rerunning this script
# reloads them and replays the (deterministic) DFS up to the frontier.  After completion the independent
# replay checker is run on the log.
cd "$(dirname "$0")"
THREADS=${1:-4}
/usr/bin/time -l ./lpf 1000000000 2 odd $THREADS runs/rows_1000000000.txt runs/c_1000000000.log > runs/c_1e9.out 2>> runs/c_1e9.err
python3 replay.py 1000000000 runs/rows_1000000000.txt runs/c_1000000000.log > runs/replay_1e9.out 2>&1
