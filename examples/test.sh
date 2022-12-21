#!/usr/bin/env bash
set -Eexuo pipefail

# Move to the script directory.
SCRIPT_DIR=$(cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd)
pushd "$SCRIPT_DIR"

# Run dfx stop if we run into errors.
trap "dfx stop" ERR EXIT

rm -rf .dfx
dfx start --background

# Deploys the examples.
dfx deploy

# Insert some data into the quick_start canister.
dfx canister call quick_start stable_insert '(1:nat, 2:nat)'
dfx canister call quick_start stable_insert '(3:nat, 4:nat)'
dfx canister call quick_start set_heap_data '(vec {1:nat8; 2:nat8; 3:nat8})'

# Upgrade the canister, which clears all the data in the heap.
dfx deploy --upgrade-unchanged quick_start

# Even though the canister has been upgraded and its heap is cleared,
# querying the canister should still return the data stored prior to
# the upgrade.
DATA=$(dfx canister call quick_start stable_get '(1:nat)')
if ! [[ $DATA = "(opt (2 : nat))" ]]; then
  echo "FAIL"
  exit 1
fi

DATA=$(dfx canister call quick_start stable_get '(3:nat)')
if ! [[ $DATA = "(opt (4 : nat))" ]]; then
  echo "FAIL"
  exit 1
fi

DATA=$(dfx canister call quick_start get_heap_data)
if ! [[ $DATA = '(blob "\01\02\03")' ]]; then
  echo "FAIL"
  exit 1
fi

echo "SUCCESS"
