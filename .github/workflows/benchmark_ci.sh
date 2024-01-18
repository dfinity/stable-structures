#!/usr/bin/env bash
set -Eexuo pipefail

# Install cargobench
cargo install --path ./profiler --features bin

BENCH_OUTPUT=$(canbench)

set +e
REGRESSIONS=$( echo "$BENCH_OUTPUT" |  grep -c "regressed by" )
set -e

if [[ $REGRESSIONS != 0 ]]; then
  echo "FAIL! Performance regressions are detected. 
        Please run \"cargo bench -- --persist\" to update \"results.yml\""
  exit 1
fi

echo "SUCCESS! Performance regressions are not detected."
