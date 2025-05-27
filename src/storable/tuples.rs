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
                let a_max_size = a_bounds.max_size as usize;
                let b_max_size = b_bounds.max_size as usize;
                let a_size_len = bytes_to_store_size_bounded(&a_bounds) as usize;
                let b_size_len = bytes_to_store_size_bounded(&b_bounds) as usize;
                let sizes_offset = a_max_size + b_max_size;

                debug_assert!(a_bytes.len() <= a_max_size);
                debug_assert!(b_bytes.len() <= b_max_size);

                let mut bytes = vec![0; max_size as usize];
                bytes[..a_bytes.len()].copy_from_slice(a_bytes.as_ref());
                bytes[a_max_size..a_max_size + b_bytes.len()].copy_from_slice(b_bytes.as_ref());

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
                let a_max_size = a_bounds.max_size as usize;
                let b_max_size = b_bounds.max_size as usize;
                let sizes_offset = a_max_size + b_max_size;
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
                let b = B::from_bytes(Cow::Borrowed(&bytes[a_max_size..a_max_size + b_len]));
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
fn encode_size(dst: &mut [u8], size_len: usize, bytes: usize) {
    match bytes {
        1 => dst[0] = size_len as u8,
        2 => dst[..2].copy_from_slice(&(size_len as u16).to_be_bytes()),
        _ => dst[..4].copy_from_slice(&(size_len as u32).to_be_bytes()),
    }
}

fn encode_size_lengths(sizes: &[usize]) -> u8 {
    assert!(sizes.len() <= 4);

    let mut size_lengths_byte: u8 = 0;

    for size in sizes.iter() {
        let size_length = bytes_to_store_size(*size);
        // Number of bytes required to store the size of every
        // element is represented with 2 bits.
        size_lengths_byte <<= 2;
        // `size_length` can take value in {1, 2, 4}, but to
        // compress it into 2 bit we will decrement its value.
        size_lengths_byte += (size_length - 1) as u8;
    }

    size_lengths_byte
}

fn decode_size_lengths(mut encoded_bytes_to_store: u8, number_of_encoded_lengths: u8) -> Vec<u8> {
    assert!(number_of_encoded_lengths <= 4);

    let mut bytes_to_store_sizes = vec![];

    for _ in 0..number_of_encoded_lengths {
        // The number of bytes required to store the size of every
        // element is represented with 2 bits. Hence we use
        // mask `11`, equivalent to 3 in the decimal system.
        let mask: u8 = 3;
        // The number of bytes required to store size can take value
        // in {1, 2, 4}, but to compress it to 2-bit,
        // when encoding we decreased the value, hence now we need
        // to do inverse.
        let bytes_to_store: u8 = (encoded_bytes_to_store & mask) + 1;
        bytes_to_store_sizes.push(bytes_to_store);
        encoded_bytes_to_store >>= 2;
    }

    // Because encoding and decoding are started on the same
    // end of the byte, we need to reverse `bytes_to_store_sizes`
    // to get sizes in order.
    bytes_to_store_sizes.reverse();

    bytes_to_store_sizes
}

// Encodes a serialized element `T` in a tuple.
// The element is assumed to be at the beginning of `dst`.
// Returns the number of bytes written to `dst`.
fn encode_tuple_element<T: Storable>(dst: &mut [u8], bytes: &[u8], last: bool) -> usize {
    let mut offset = 0;
    if !last && !T::BOUND.is_fixed_size() {
        let size_len = bytes_to_store_size(bytes.len());
        encode_size(&mut dst[offset..], bytes.len(), size_len);
        offset += size_len;
    }
    dst[offset..offset + bytes.len()].copy_from_slice(bytes);
    offset + bytes.len()
}

// Decodes an element `T` from a tuple.
//
// The element is assumed to be at the beginning of `src`.
// The length of the size of the element should be provided if the element is *not* fixed in size.
//
// Returns the element `T` and the number of bytes read from `src`.
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
        // This case should only happen for the last element.
        assert!(last);
        src.len()
    };
    (
        T::from_bytes(Cow::Borrowed(&src[read..read + size])),
        read + size,
    )
}

// Returns number of bytes required to store encoding of sizes for elements of type A and B.
const fn sizes_overhead<A: Storable, B: Storable>(a_size: usize, b_size: usize) -> usize {
    let mut sizes_overhead = 0;

    if !(A::BOUND.is_fixed_size() && B::BOUND.is_fixed_size()) {
        // 1B for size lengths encoding
        sizes_overhead += 1;

        if !A::BOUND.is_fixed_size() {
            sizes_overhead += bytes_to_store_size(a_size);
        }

        if !B::BOUND.is_fixed_size() {
            sizes_overhead += bytes_to_store_size(b_size);
        }
    }

    sizes_overhead
}

impl<A, B, C> Storable for (A, B, C)
where
    A: Storable,
    B: Storable,
    C: Storable,
{
    // Tuple (A, B, C) serialization:
    //   If A and B have fixed size:
    //     <a_bytes> <b_bytes> <c_bytes>
    //   Otherwise:
    //     <size_lengths (1B)> <size_a (0-4B)> <a_bytes> <size_b(0-4B)> <b_bytes> <c_bytes>
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
            bytes[0] = encode_size_lengths(&[a_size, b_size]);
            offset += 1;
        }

        offset += encode_tuple_element::<A>(&mut bytes[offset..], a_bytes.as_ref(), false);
        offset += encode_tuple_element::<B>(&mut bytes[offset..], b_bytes.as_ref(), false);
        offset += encode_tuple_element::<C>(&mut bytes[offset..], c_bytes.as_ref(), true);

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
