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

# Insert some data into the basic_example canister.
dfx canister call basic_example insert '("alice", blob "12341234")'
dfx canister call basic_example insert '("bob", blob "789789789")'

# Upgrade the canister, which clears all the data in the heap.
dfx deploy --upgrade-unchanged basic_example

# Even though the canister has been upgraded and its heap is cleared,
# querying the canister should still return the data stored prior to
# the upgrade.
DATA=$(dfx canister call basic_example get '("alice")')
if ! [[ $DATA = "(opt blob \"12341234\")" ]]; then
  echo "FAIL"
  exit 1
fi

DATA=$(dfx canister call basic_example get '("bob")')
if ! [[ $DATA = "(opt blob \"789789789\")" ]]; then
  echo "FAIL"
  exit 1
fi

# Insert some data into the basic_example canister.
dfx canister call custom_types_example insert '(1, record { age = 32; name = "Some Name"})'
dfx canister call custom_types_example insert '(2, record { age = 48; name = "Other Name"})'

# Upgrade the canister, which clears all the data in the heap.
dfx deploy --upgrade-unchanged custom_types_example

# Even though the canister has been upgraded and its heap is cleared,
# querying the canister should still return the data stored prior to
# the upgrade.
DATA=$(dfx canister call custom_types_example get '(1)')
if ! [[ $DATA = "(opt record { age = 32 : nat8; name = \"Some Name\" })" ]]; then
  echo "FAIL"
  exit 1
fi

DATA=$(dfx canister call custom_types_example get '(2)')
if ! [[ $DATA = "(opt record { age = 48 : nat8; name = \"Other Name\" })" ]]; then
  echo "FAIL"
  exit 1
fi

echo "SUCCESS"
