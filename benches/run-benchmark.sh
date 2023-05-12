#!/usr/bin/env bash
#
# Runs a benchmark using drun. The script assumes drun is available on the caller's path.
set -euo pipefail

BENCH_NAME=$1
FILE=mktemp

if ! type "drun" > /dev/null; then
  echo "drun is not installed. Please add drun to your path from commit d35535c96184be039aaa31f68b48bbe45909494e."
  exit 1
fi

cat > $FILE << EOF
create
install rwlgt-iiaaa-aaaaa-aaaaa-cai ../target/wasm32-unknown-unknown/release/benchmarks.wasm ""
query rwlgt-iiaaa-aaaaa-aaaaa-cai ${BENCH_NAME} "DIDL\x00\x00"
EOF

# Run the benchmarks, decode the output.
drun $FILE --instruction-limit 99999999999999 \
    | awk '{ print $3 }' \
    | grep "44.*" -o \
    | xargs didc decode
