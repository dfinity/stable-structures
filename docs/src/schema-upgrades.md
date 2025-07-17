# Schema Upgrades

Stable structures store data directly in stable memory and do not require upgrade hooks.
Since these structures are designed to persist throughout the lifetime of the canister, it's nearly inevitable that developers would want to make modifications to the data's schema as the canister evolves.

Let's say you are storing assets in your canister. The declaration of it can look something like this:

```rust
#[derive(Serialize, Deserialize, CandidType)]
struct Asset {
    // The contents of the asset.
    contents: Vec<u8>,
}

impl Storable for Asset {
    fn to_bytes(&self) -> std::borrow::Cow<'_, [u8]> {
        let mut bytes = vec![];
        ciborium::ser::into_writer(&self, &mut bytes).unwrap();
        Cow::Owned(bytes)
    }

    fn into_bytes(self) -> Vec<u8> {
        let mut bytes = vec![];
        ciborium::ser::into_writer(&self, &mut bytes).unwrap()
    }

    fn from_bytes(bytes: std::borrow::Cow<[u8]>) -> Self {
        ciborium::de::from_reader(&*bytes).expect("deserialization must succeed.")
    }

    const BOUND: Bound = Bound::Unbounded;
}
```

> **Note:** Stable structures do not enforce a specific data format.
It's up to the developer to use the data format that fits their use-case.
In this example, CBOR is used for encoding `Asset`.


## Adding an attribute

Adding a new field can be as simple as adding the field, like this:

```rust
#[derive(Serialize, Deserialize)]
struct Asset {
    // The contents of the asset.
    contents: Vec<u8>,

    // The timestamp the asset was created at.
    #[serde(default)]
    created_at: u64,
}
```

If the new attribute being added doesn't have a sensible default value, consider wrapping it in an `Option`:

```rust
#[derive(Serialize, Deserialize, CandidType)]
struct Asset {
    // The contents of the asset.
    contents: Vec<u8>,

    // The timestamp the asset was created at.
    #[serde(default)]
    created_at: u64,

    // The username of the uploader.
    uploaded_by: Option<String>,
}
```
