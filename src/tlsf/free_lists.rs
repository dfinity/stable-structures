use super::FIRST_LEVEL_INDEX_SIZE;
use super::MEMORY_POOL_SIZE;
use super::SECOND_LEVEL_INDEX_LOG_SIZE;
use super::SECOND_LEVEL_INDEX_SIZE;
use crate::Address;

#[derive(Debug, PartialEq)]
pub struct FreeLists {
    pub first_level_index: u64,
    pub second_level_index: [u32; FIRST_LEVEL_INDEX_SIZE],
    // TODO: remove the unneeded bits from this list.
    pub lists: [[Address; SECOND_LEVEL_INDEX_SIZE]; FIRST_LEVEL_INDEX_SIZE],
}

impl FreeLists {
    pub fn set(&mut self, f: usize, s: usize, address: Address) {
        if address == Address::NULL {
            // Unset the bit in the map.
            self.first_level_index &= !(1 << f as u64);
            self.second_level_index[f] &= !(1 << s as u32);
        } else {
            // Set the bit in the map.
            self.first_level_index |= 1 << f as u64;
            self.second_level_index[f] |= 1 << s as u64;
        }

        self.lists[f][s] = address;
    }

    pub fn get(&self, f: usize, s: usize) -> Address {
        self.lists[f][s]
    }

    // Returns the smallest block that accommodates the size.
    // TODO: size should be u64 (and add test)
    pub fn search(&self, size: u32) -> (usize, usize) {
        fn get_least_significant_bit_after(num: u32, position: usize) -> usize {
            (num & (u32::MAX - position as u32)).trailing_zeros() as usize
        }

        fn get_least_significant_bit_after_u64(num: u64, position: usize) -> usize {
            (num & (u64::MAX - position as u64)).trailing_zeros() as usize
        }

        // Identify the free list to take blocks from.
        let (f_idx, s_idx) = mapping(size as u64);

        // The identified free list maybe not have any free blocks.
        let s = get_least_significant_bit_after(self.second_level_index[f_idx], s_idx);

        if s < u32::BITS as usize {
            (f_idx, s)
        } else {
            // Continue searching elsewhere.
            let f = get_least_significant_bit_after_u64(self.first_level_index, f_idx + 1);

            let s = get_least_significant_bit_after(
                self.second_level_index[f],
                0, // s_idx + 1, // TODO: add test case to detect this
            );
            (f, s)
        }
    }
}

// Returns the indexes that point to the corresponding segregated list.
pub fn mapping(size: u64) -> (usize, usize) {
    assert!(size <= MEMORY_POOL_SIZE);

    let f = u64::BITS - size.leading_zeros() - 1;
    let s = (size ^ (1 << f)) >> (f - SECOND_LEVEL_INDEX_LOG_SIZE as u32);
    (f as usize, s as usize)
}

#[cfg(test)]
mod test {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn mapping_test() {
        proptest!(|(
            size in 0..u32::MAX,
        )| {
            let (f, s) = mapping(size as u64);
            assert!((1 << f) + (((1 << f) / SECOND_LEVEL_INDEX_SIZE) * (s + 1) - 1) >= size as usize);
            if s > 0 {
                assert!((1 << f) + ((1 << f) / SECOND_LEVEL_INDEX_SIZE) * s < size as usize);
            }
        });
    }

    #[test]
    fn free_lists_test() {
        let mut fl = FreeLists {
            first_level_index: 0,
            second_level_index: [0; FIRST_LEVEL_INDEX_SIZE],
            lists: [[Address::NULL; SECOND_LEVEL_INDEX_SIZE]; FIRST_LEVEL_INDEX_SIZE],
        };

        fl.set(0, 0, Address::new(1));
        assert_eq!(fl.first_level_index, 1);
        assert_eq!(fl.second_level_index[0], 1);
        assert_eq!(fl.lists[0][0], Address::new(1));

        fl.set(0, 0, Address::NULL);
        assert_eq!(fl.first_level_index, 0);
        assert_eq!(fl.second_level_index[0], 0);
        assert_eq!(fl.lists[0][0], Address::NULL);

        let mut fl = FreeLists {
            first_level_index: 0,
            second_level_index: [0; FIRST_LEVEL_INDEX_SIZE],
            lists: [[Address::NULL; SECOND_LEVEL_INDEX_SIZE]; FIRST_LEVEL_INDEX_SIZE],
        };

        fl.set(1, 1, Address::new(1));
        assert_eq!(fl.first_level_index, 2);
        assert_eq!(fl.second_level_index[1], 2);
        assert_eq!(fl.lists[1][1], Address::new(1));

        let mut fl = FreeLists {
            first_level_index: 0,
            second_level_index: [0; FIRST_LEVEL_INDEX_SIZE],
            lists: [[Address::NULL; SECOND_LEVEL_INDEX_SIZE]; FIRST_LEVEL_INDEX_SIZE],
        };

        fl.set(16, 16, Address::new(1));
        assert_eq!(fl.first_level_index, 1 << 16);
        assert_eq!(fl.second_level_index[16], 1 << 16);
        assert_eq!(fl.lists[16][16], Address::new(1));

        fl.set(16, 31, Address::new(1));
        assert_eq!(fl.first_level_index, 1 << 16);
        assert_eq!(fl.second_level_index[16], (1 << 31) | (1 << 16));
        assert_eq!(fl.lists[16][31], Address::new(1));
    }
}
