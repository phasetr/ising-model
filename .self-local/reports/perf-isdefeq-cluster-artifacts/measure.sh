#!/bin/zsh
# SUPERSEDED 2026-07-31. Do not use this for new timings.
#
# Kept only as the provenance of the *_trace.out samples beside it (2026-07-26,
# isDefEq cluster A/B). It times `lake env lean`, which section 7 of
# ../perf-4724-fixed-cost-reconciliation.md retires as a per-module cost metric:
# the wrapper adds a constant ~1.07s that a real `lake build` never pays, and
# this script keeps no artifact, does no warm-up pass, and reports no spread.
#
# Replacement: python3 scripts/measure_module_cost.py (bare lean, one LEAN_PATH
# lookup, serial, discarded warm-up pass, >= 3 replicates, every sample kept in
# a JSON artifact).
#
# usage: measure.sh <file> <n>
f=$1; n=${2:-3}
for i in $(seq 1 $n); do
  out=$( { /usr/bin/time -p lake env lean -Dprofiler=true -Dprofiler.threshold=250 "$f"; } 2>&1 )
  real=$(echo "$out" | grep -E '^real' | awk '{print $2}')
  imp=$(echo "$out" | grep -m1 'import took' | sed -E 's/.*took ([0-9.]+)s.*/\1/')
  echo "real=$real import=$imp own=$(echo "$real - $imp" | bc)"
done
