#!/usr/bin/env bash
set -euo pipefail

DIR="$(dirname "$0")"
TARGET="wasm32-unknown-unknown"

cargo build --target $TARGET --release

cargo install ic-cdk-optimizer --version 0.3.2 --root "$DIR"/../target
STATUS=$?

echo "$DIR"

if [ "$STATUS" -eq "0" ]; then
      "$DIR"/../target/bin/ic-cdk-optimizer \
      "$DIR/../target/$TARGET/release/stable-demo.wasm" \
      -o "$DIR/../target/$TARGET/release/stable-demo.wasm"
  true
else
  echo Could not install ic-cdk-optimizer.
  false
fi
