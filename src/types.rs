use core::ops::{Add, AddAssign, Div, Mul, Rem, Sub, SubAssign};

pub const NULL: Address = Address(0);

#[repr(C, packed)]
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq)]
pub struct Address(u64);

impl From<u64> for Address {
    fn from(addr: u64) -> Self {
        Self(addr)
    }
}

impl Address {
    pub fn get(&self) -> u64 {
        self.0
    }

    pub fn size() -> Bytes {
        assert_eq!(core::mem::size_of::<Address>(), 8);
        Bytes::from(8u64)
    }
}

impl Add<Bytes> for Address {
    type Output = Self;

    fn add(self, offset: Bytes) -> Self {
        Self(self.0 + offset.0)
    }
}

impl Sub<Address> for Address {
    type Output = Bytes;

    fn sub(self, address: Address) -> Self::Output {
        Bytes(self.0 - address.0)
    }
}

impl Sub<Bytes> for Address {
    type Output = Self;

    fn sub(self, offset: Bytes) -> Self {
        Self(self.0 - offset.0)
    }
}

impl AddAssign<Bytes> for Address {
    fn add_assign(&mut self, other: Bytes) {
        *self = Self(self.0 + other.0);
    }
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Ord, Eq)]
pub struct Bytes(u64);

impl From<u64> for Bytes {
    fn from(bytes: u64) -> Self {
        Self(bytes)
    }
}

impl From<usize> for Bytes {
    fn from(bytes: usize) -> Self {
        Self(bytes as u64)
    }
}

impl From<u32> for Bytes {
    fn from(bytes: u32) -> Self {
        Self(bytes as u64)
    }
}

impl From<u16> for Bytes {
    fn from(bytes: u16) -> Self {
        Self(bytes as u64)
    }
}

impl Add<Bytes> for Bytes {
    type Output = Self;

    fn add(self, bytes: Bytes) -> Self {
        Self(self.0 + bytes.0)
    }
}

impl Sub<Bytes> for Bytes {
    type Output = Self;

    fn sub(self, bytes: Bytes) -> Self {
        Self(self.0 - bytes.0)
    }
}

impl Mul<Bytes> for Bytes {
    type Output = Self;

    fn mul(self, bytes: Bytes) -> Self {
        Self(self.0 * bytes.0)
    }
}

impl Div<Bytes> for Bytes {
    type Output = Self;

    fn div(self, bytes: Bytes) -> Self {
        Self(self.0 / bytes.0)
    }
}

impl Rem<Bytes> for Bytes {
    type Output = Self;

    fn rem(self, bytes: Bytes) -> Self {
        Self(self.0 % bytes.0)
    }
}

impl Mul<u64> for Bytes {
    type Output = Self;

    fn mul(self, num: u64) -> Self {
        Self(self.0 * num)
    }
}

impl AddAssign<Bytes> for Bytes {
    fn add_assign(&mut self, other: Bytes) {
        *self = Self(self.0 + other.0);
    }
}

impl SubAssign<Bytes> for Bytes {
    fn sub_assign(&mut self, other: Bytes) {
        *self = Self(self.0 - other.0);
    }
}

impl Bytes {
    pub const fn new(val: u64) -> Self {
        Self(val)
    }

    pub fn get(&self) -> u64 {
        self.0
    }
}
