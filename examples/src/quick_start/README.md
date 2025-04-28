# Quickstart Example

An example that showcases how you can incorporate stable structures, and specifically `StableBTreeMap`, into existing canisters that already store some data on the heap.

Example usage:

```bash
dfx start --background --clean

# Insert some data into the quick_start canister.
dfx canister call quick_start stable_insert '(1:nat, 2:nat)'
dfx canister call quick_start stable_insert '(3:nat, 4:nat)'
dfx canister call quick_start set_heap_data '(vec {1:nat8; 2:nat8; 3:nat8})'

# Upgrade the canister, which clears all the data in the heap.
dfx deploy --upgrade-unchanged quick_start

# Even though the canister has been upgraded and its heap is cleared,
# querying the canister should still return the data stored prior to
# the upgrade.
dfx canister call quick_start stable_get '(1:nat)'
> (opt (2 : nat))

dfx canister call quick_start stable_get '(3:nat)'
> (opt (4 : nat))

dfx canister call quick_start get_heap_data
> (blob "\01\02\03")
```
