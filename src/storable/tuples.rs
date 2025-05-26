use crate::storable::{
    bounds, bytes_to_store_size, bytes_to_store_size_bounded, Bound, Bounds, Storable,
};
use std::borrow::{Borrow, Cow};

impl<A, B> Storable for (A, B)
where
    A: Storable,
    B: Storable,
{
    fn to_bytes(&self) -> Cow<[u8]> {
        match Self::BOUND {
            Bound::Bounded { max_size, .. } => {
                let a_bytes = self.0.to_bytes();
                let b_bytes = self.1.to_bytes();
                let a_bounds = bounds::<A>();
                let b_bounds = bounds::<B>();
                let a_max = a_bounds.max_size as usize;
                let b_max = b_bounds.max_size as usize;
                let a_size_len = bytes_to_store_size_bounded(&a_bounds) as usize;
                let b_size_len = bytes_to_store_size_bounded(&b_bounds) as usize;
                let sizes_offset = a_max + b_max;

                let mut bytes = vec![0; max_size as usize];
                bytes[..a_bytes.len()].copy_from_slice(a_bytes.borrow());
                bytes[a_max..a_max + b_bytes.len()].copy_from_slice(b_bytes.borrow());

                encode_size_of_bound(
                    &mut bytes[sizes_offset..sizes_offset + a_size_len],
                    a_bytes.len(),
                    &a_bounds,
                );
                encode_size_of_bound(
                    &mut bytes[sizes_offset + a_size_len..sizes_offset + a_size_len + b_size_len],
                    b_bytes.len(),
                    &b_bounds,
                );

                Cow::Owned(bytes)
            }
            _ => todo!("Serializing tuples with unbounded types is not yet supported."),
        }
    }

    #[inline]
    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        match Self::BOUND {
            Bound::Bounded { max_size, .. } => {
                assert_eq!(bytes.len(), max_size as usize);
                let a_bounds = bounds::<A>();
                let b_bounds = bounds::<B>();
                let a_max = a_bounds.max_size as usize;
                let b_max = b_bounds.max_size as usize;
                let sizes_offset = a_max + b_max;
                let a_size_len = bytes_to_store_size_bounded(&a_bounds) as usize;
                let b_size_len = bytes_to_store_size_bounded(&b_bounds) as usize;

                let a_len = decode_size_of_bound(
                    &bytes[sizes_offset..sizes_offset + a_size_len],
                    &a_bounds,
                );
                let b_len = decode_size_of_bound(
                    &bytes[sizes_offset + a_size_len..sizes_offset + a_size_len + b_size_len],
                    &b_bounds,
                );

                let a = A::from_bytes(Cow::Borrowed(&bytes[..a_len]));
                let b = B::from_bytes(Cow::Borrowed(&bytes[a_max..a_max + b_len]));
                (a, b)
            }
            _ => todo!("Deserializing tuples with unbounded types is not yet supported."),
        }
    }

    const BOUND: Bound = match (A::BOUND, B::BOUND) {
        (Bound::Bounded { .. }, Bound::Bounded { .. }) => {
            let a_bounds = bounds::<A>();
            let b_bounds = bounds::<B>();
            Bound::Bounded {
                max_size: a_bounds.max_size
                    + b_bounds.max_size
                    + bytes_to_store_size_bounded(&a_bounds)
                    + bytes_to_store_size_bounded(&b_bounds),
                is_fixed_size: a_bounds.is_fixed_size && b_bounds.is_fixed_size,
            }
        }
        _ => Bound::Unbounded,
    };
}

fn decode_size_of_bound(src: &[u8], bounds: &Bounds) -> usize {
    if bounds.is_fixed_size {
        bounds.max_size as usize
    } else {
        decode_size(src, bytes_to_store_size(bounds.max_size as usize))
    }
}

fn encode_size_of_bound(dst: &mut [u8], n: usize, bounds: &Bounds) {
    if !bounds.is_fixed_size {
        encode_size(dst, n, bytes_to_store_size(bounds.max_size as usize));
    }
}

/// Decodes size from the beginning of `src` of length `size_len` and returns it.
fn decode_size(src: &[u8], size_len: usize) -> usize {
    match size_len {
        1 => src[0] as usize,
        2 => u16::from_be_bytes([src[0], src[1]]) as usize,
        _ => u32::from_be_bytes([src[0], src[1], src[2], src[3]]) as usize,
    }
}

/// Encodes `size` at the beginning of `dst` of length `bytes_to_store_size` bytes.
fn encode_size(dst: &mut [u8], size: usize, bytes: usize) {
    match bytes {
        1 => dst[0] = size as u8,
        2 => dst[..2].copy_from_slice(&(size as u16).to_be_bytes()),
        _ => dst[..4].copy_from_slice(&(size as u32).to_be_bytes()),
    }
}

impl<A, B, C> Storable for (A, B, C)
where
    A: Storable,
    B: Storable,
    C: Storable,
{
    // Tuple (A, B, C) serialization:
    // If A and B have fixed size: <a_bytes> <b_bytes> <c_bytes>
    // Otherwise: <size_lengths (1B)> <size_a (0-4B)> <a_bytes> <size_b(0-4B)> <b_bytes> <c_bytes>
    fn to_bytes(&self) -> Cow<[u8]> {
        let a_bytes = self.0.to_bytes();
        let b_bytes = self.1.to_bytes();
        let c_bytes = self.2.to_bytes();
        let a_size = a_bytes.len();
        let b_size = b_bytes.len();
        let c_size = c_bytes.len();

        let sizes_overhead = sizes_overhead::<A, B>(a_size, b_size);
        let output_size = a_size + b_size + c_size + sizes_overhead;
        let mut bytes = vec![0; output_size];
        let mut offset = 0;

        if sizes_overhead != 0 {
            bytes[0] = encode_size_lengths(vec![a_size, b_size]);
            offset += 1;
        }

        offset += encode_tuple_element::<A>(&mut bytes[offset..], a_bytes.borrow(), false);
        offset += encode_tuple_element::<B>(&mut bytes[offset..], b_bytes.borrow(), false);
        offset += encode_tuple_element::<C>(&mut bytes[offset..], c_bytes.borrow(), true);

        debug_assert_eq!(offset, output_size);
        Cow::Owned(bytes)
    }

    #[inline]
    fn from_bytes(bytes: Cow<[u8]>) -> Self {
        let mut offset = 0;
        let mut size_lengths = [None, None];

        if !(A::BOUND.is_fixed_size() && B::BOUND.is_fixed_size()) {
            let lengths = decode_size_lengths(bytes[0], 2);
            offset += 1;
            if !A::BOUND.is_fixed_size() {
                size_lengths[0] = Some(lengths[0]);
            }
            if !B::BOUND.is_fixed_size() {
                size_lengths[1] = Some(lengths[1]);
            }
        }

        let (a, read) = decode_tuple_element::<A>(&bytes[offset..], size_lengths[0], false);
        offset += read;
        let (b, read) = decode_tuple_element::<B>(&bytes[offset..], size_lengths[1], false);
        offset += read;
        let (c, read) = decode_tuple_element::<C>(&bytes[offset..], None, true);
        offset += read;

        debug_assert_eq!(offset, bytes.len());
        (a, b, c)
    }

    const BOUND: Bound = match (A::BOUND, B::BOUND, C::BOUND) {
        (Bound::Bounded { .. }, Bound::Bounded { .. }, Bound::Bounded { .. }) => {
            let a_bounds = bounds::<A>();
            let b_bounds = bounds::<B>();
            let c_bounds = bounds::<C>();
            let sizes_overhead =
                sizes_overhead::<A, B>(a_bounds.max_size as usize, b_bounds.max_size as usize)
                    as u32;
            Bound::Bounded {
                max_size: a_bounds.max_size
                    + b_bounds.max_size
                    + c_bounds.max_size
                    + sizes_overhead,
                is_fixed_size: a_bounds.is_fixed_size
                    && b_bounds.is_fixed_size
                    && c_bounds.is_fixed_size,
            }
        }
        _ => Bound::Unbounded,
    };
}

const fn sizes_overhead<A: Storable, B: Storable>(a_size: usize, b_size: usize) -> usize {
    if A::BOUND.is_fixed_size() && B::BOUND.is_fixed_size() {
        0
    } else {
        1 + if !A::BOUND.is_fixed_size() {
            bytes_to_store_size(a_size)
        } else {
            0
        } + if !B::BOUND.is_fixed_size() {
            bytes_to_store_size(b_size)
        } else {
            0
        }
    }
}

fn encode_size_lengths(sizes: Vec<usize>) -> u8 {
    sizes.iter().fold(0, |acc, &size| {
        (acc << 2) + (bytes_to_store_size(size) - 1) as u8
    })
}

fn decode_size_lengths(mut encoded: u8, count: u8) -> Vec<u8> {
    let mut sizes = vec![];
    for _ in 0..count {
        sizes.push((encoded & 3) + 1);
        encoded >>= 2;
    }
    sizes.reverse();
    sizes
}

fn encode_tuple_element<T: Storable>(dst: &mut [u8], bytes: &[u8], last: bool) -> usize {
    let mut written = 0;
    if !last && !T::BOUND.is_fixed_size() {
        let size_len = bytes_to_store_size(bytes.len());
        encode_size(&mut dst[written..], bytes.len(), size_len);
        written += size_len;
    }
    dst[written..written + bytes.len()].copy_from_slice(bytes);
    written + bytes.len()
}

fn decode_tuple_element<T: Storable>(src: &[u8], size_len: Option<u8>, last: bool) -> (T, usize) {
    let mut read = 0;
    let size = if let Some(len) = size_len {
        let s = decode_size(&src[read..], len as usize);
        read += len as usize;
        s
    } else if let Bound::Bounded {
        max_size,
        is_fixed_size: true,
    } = T::BOUND
    {
        max_size as usize
    } else {
        assert!(last);
        src.len()
    };
    (
        T::from_bytes(Cow::Borrowed(&src[read..read + size])),
        read + size,
    )
}
