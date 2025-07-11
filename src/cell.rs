//! A serializable value stored in the stable memory.
use crate::storable::Storable;
use crate::{read_to_vec, Memory, WASM_PAGE_SIZE};
use std::borrow::{Borrow, Cow};
use std::fmt;

#[cfg(test)]
mod tests;

const MAGIC: &[u8; 3] = b"SCL"; // short for "stable cell"
const HEADER_V1_SIZE: u64 = 8;
const LAYOUT_VERSION: u8 = 1;

// NOTE: the size of this structure should be equal to [HEADER_V1_SIZE].
// NOTE: if you have to add more fields, you need to increase the version and handle decoding of
// previous versions in `Cell::read_header`.
//
// # V1 layout
//
// -------------------------------
// Magic "SCL"         ↕ 3 bytes
// -------------------------------
// Layout version      ↕ 1 byte
// -------------------------------
// Value length = N    ↕ 4 bytes
// -------------------------------
// <encoded value>     ↕ N bytes
// -------------------------------
#[derive(Debug)]
struct HeaderV1 {
    magic: [u8; 3],
    version: u8,
    value_length: u32,
}

/// Indicates a failure to initialize a Cell.
#[derive(Debug, PartialEq, Eq)]
pub enum InitError {
    /// The version of the library does not support version of the cell layout encoded in the
    /// memory.
    IncompatibleVersion {
        last_supported_version: u8,
        decoded_version: u8,
    },
    /// The initial value was to large to fit into the memory.
    ValueTooLarge { value_size: u64 },
}

impl fmt::Display for InitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InitError::IncompatibleVersion {
                last_supported_version,
                decoded_version,
            } => write!(
                f,
                "Incompatible version: last supported version is {}, but the memory contains version {}",
                last_supported_version, decoded_version
            ),
            InitError::ValueTooLarge { value_size } => write!(
                f,
                "The initial value is too large to fit into the memory: {} bytes",
                value_size
            ),
        }
    }
}

/// Indicates a failure to set cell's value.
#[derive(Debug, PartialEq, Eq)]
pub enum ValueError {
    /// The value is too large to fit into the cell memory.
    ValueTooLarge { value_size: u64 },
}

impl From<ValueError> for InitError {
    fn from(e: ValueError) -> InitError {
        match e {
            ValueError::ValueTooLarge { value_size } => InitError::ValueTooLarge { value_size },
        }
    }
}

/// Represents a value stored in stable memory.
///
/// A `Cell` stores a single value directly in stable memory and provides immediate persistence
/// on every write operation. This makes it ideal for configuration values, metadata, or any
/// small state that needs to survive canister upgrades.
///
/// You should use cells only for small (up to a few MiB) values to keep upgrades safe. For larger
/// values, consider using other data structures like `Vec` or `BTreeMap` instead.
///
/// # Example
///
/// ```rust
/// use ic_stable_structures::{Cell, DefaultMemoryImpl, Storable, storable::Bound};
/// use std::borrow::Cow;
/// use std::cell::RefCell;
///
/// #[derive(Clone)]
/// struct Config {
///     name: String,
///     version: u32,
/// }
///
/// // Implement Storable for serialization/deserialization when saving to stable memory.
/// impl Storable for Config {
///     fn to_bytes(&self) -> Cow<'_, [u8]> {
///         # let mut bytes = Vec::new();
///         // Convert config into bytes...
///         # Cow::Owned(bytes)
///     }
///
///     fn into_bytes(self) -> Vec<u8> {
///         # let mut bytes = Vec::new();
///         // Convert config into bytes...
///         # bytes
///     }
///
///     fn from_bytes(bytes: Cow<[u8]>) -> Self {
///         // Convert bytes back to Config
///         # let (name, version) = ("".to_string(), 0);
///         # Config { name, version }
///     }
///
///     // Types can be bounded or unbounded:
///     // - Use Bound::Unbounded if the size can vary or isn't known in advance (recommended for most cases)
///     // - Use Bound::Bounded if you know the maximum size and want memory optimization
///     const BOUND: Bound = Bound::Unbounded;
/// }
///
/// // Create a global cell variable
/// thread_local! {
///     static CONFIG: RefCell<Cell<Config, DefaultMemoryImpl>> = RefCell::new(
///         Cell::init(
///             DefaultMemoryImpl::default(),
///             Config {
///                 name: "MyConfig".to_string(),
///                 version: 1,
///             }
///         )
///     );
/// }
///
/// // Read the current configuration
/// fn get_version() -> u32 {
///     CONFIG.with(|c| c.borrow().get().version)
/// }
///
/// // Update the configuration
/// fn update_version(new_version: u32) {
///     CONFIG.with(|c| {
///         let mut cell = c.borrow_mut();
///         let mut config = cell.get().clone();
///         config.version = new_version;
///         cell.set(config);
///     });
/// }
///
/// # // Test to ensure example works as expected.
/// # fn main() {
/// #    assert_eq!(get_version(), 1);
/// #    update_version(2);
/// #    assert_eq!(get_version(), 2);
/// # }
/// ```
pub struct Cell<T: Storable, M: Memory> {
    memory: M,
    value: T,
}

impl<T: Storable, M: Memory> Cell<T, M> {
    /// Creates a new cell in the specified memory, overwriting the previous contents of the memory.
    pub fn new(memory: M, value: T) -> Self {
        Self::flush_value(&memory, &value).expect("Failed to write initial value to the memory");
        Self { memory, value }
    }

    /// Initializes the value of the cell based on the contents of the `memory`.
    /// If the memory already contains a cell, initializes the cell with the decoded value.
    /// Otherwise, sets the cell value to `default_value` and writes it to the memory.
    pub fn init(memory: M, default_value: T) -> Self {
        if memory.size() == 0 {
            return Self::new(memory, default_value);
        }

        let header = Self::read_header(&memory);

        if &header.magic != MAGIC {
            return Self::new(memory, default_value);
        }

        if header.version != LAYOUT_VERSION {
            panic!(
                "Failed to initialize cell: {}",
                InitError::IncompatibleVersion {
                    last_supported_version: LAYOUT_VERSION,
                    decoded_version: header.version,
                }
            );
        }

        Self {
            value: Self::read_value(&memory, header.value_length),
            memory,
        }
    }

    /// Reads and decodes the value of specified length.
    ///
    /// PRECONDITION: memory is large enough to contain the value.
    fn read_value(memory: &M, len: u32) -> T {
        let mut buf = vec![];
        read_to_vec(memory, HEADER_V1_SIZE.into(), &mut buf, len as usize);
        T::from_bytes(Cow::Owned(buf))
    }

    /// Reads the header from the specified memory.
    ///
    /// PRECONDITION: memory.size() > 0
    fn read_header(memory: &M) -> HeaderV1 {
        let mut magic: [u8; 3] = [0; 3];
        let mut version: [u8; 1] = [0; 1];
        let mut len: [u8; 4] = [0; 4];

        memory.read(0, &mut magic);
        memory.read(3, &mut version);
        memory.read(4, &mut len);

        HeaderV1 {
            magic,
            version: version[0],
            value_length: u32::from_le_bytes(len),
        }
    }

    /// Returns the current value in the cell.
    pub fn get(&self) -> &T {
        &self.value
    }

    /// Returns the underlying memory.
    pub fn into_memory(self) -> M {
        self.memory
    }

    /// Updates the current value in the cell.
    /// If the new value is too large to fit into the memory, the value in the cell does not
    /// change.
    pub fn set(&mut self, value: T) -> T {
        Self::flush_value(&self.memory, &value).expect("Failed to write value to the memory");
        std::mem::replace(&mut self.value, value)
    }

    /// Writes the value to the memory, growing the memory size if needed.
    fn flush_value(memory: &M, value: &T) -> Result<(), ValueError> {
        let encoded = value.to_bytes();
        let bytes: &[u8] = encoded.borrow();
        let len = bytes.len();
        if len > u32::MAX as usize {
            return Err(ValueError::ValueTooLarge {
                value_size: len as u64,
            });
        }
        let size = memory.size();
        let available_space = size * WASM_PAGE_SIZE;
        if len as u64 > available_space.saturating_sub(HEADER_V1_SIZE) || size == 0 {
            let grow_by =
                (len as u64 + HEADER_V1_SIZE + WASM_PAGE_SIZE - size * WASM_PAGE_SIZE - 1)
                    / WASM_PAGE_SIZE;
            if memory.grow(grow_by) < 0 {
                return Err(ValueError::ValueTooLarge {
                    value_size: len as u64,
                });
            }
        }

        debug_assert!(memory.size() * WASM_PAGE_SIZE >= len as u64 + HEADER_V1_SIZE);

        let version = [LAYOUT_VERSION; 1];
        memory.write(0, MAGIC);
        memory.write(3, &version);
        memory.write(4, &(len as u32).to_le_bytes());
        memory.write(HEADER_V1_SIZE, bytes);
        Ok(())
    }
}
