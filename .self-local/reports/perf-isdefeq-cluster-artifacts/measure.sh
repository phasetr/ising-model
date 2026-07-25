#!/bin/zsh
# usage: measure.sh <file> <n>
f=$1; n=${2:-3}
for i in $(seq 1 $n); do
  out=$( { /usr/bin/time -p lake env lean -Dprofiler=true -Dprofiler.threshold=250 "$f"; } 2>&1 )
  real=$(echo "$out" | grep -E '^real' | awk '{print $2}')
  imp=$(echo "$out" | grep -m1 'import took' | sed -E 's/.*took ([0-9.]+)s.*/\1/')
  echo "real=$real import=$imp own=$(echo "$real - $imp" | bc)"
done
