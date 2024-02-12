use crate::writer::{BufferedWriter, Writer};
use crate::{Memory, RestrictedMemory, VectorMemory, WASM_PAGE_SIZE};
use proptest::proptest;
use std::io::Write;

proptest! {
    #[test]
    fn should_write_single_slice(
        buffer_size in proptest::option::of(0..2 * WASM_PAGE_SIZE as usize),
        bytes in proptest::collection::vec(0..u8::MAX, 1..2 * WASM_PAGE_SIZE as usize),
        offset in 0..2 * WASM_PAGE_SIZE
    ) {
        let mut memory = VectorMemory::default();
        {
            let mut writer = build_writer(&mut memory, buffer_size, offset);

            writer.write_all(&bytes).unwrap();
            writer.flush().unwrap();
        }
        let mut buf = vec![0; bytes.len()];
        memory.read(offset, &mut buf);
        assert_eq!(bytes, buf);
    }

    #[test]
    fn should_write_many_slices(
        buffer_size in proptest::option::of(0..2 * WASM_PAGE_SIZE as usize),
        bytes in proptest::collection::vec(0..u8::MAX, 1..2000),
        repetitions in 1..15usize,
        offset in 0..2 * WASM_PAGE_SIZE
    ) {
        let mut memory = VectorMemory::default();
        {
            let mut writer = build_writer(&mut memory, buffer_size, offset);
            for _ in 0..repetitions {
                writer.write_all(&bytes).unwrap();
            }
            writer.flush().unwrap();
        }

        let mut read_offset = offset;
        for _ in 0..repetitions {
            let mut buf = vec![0; bytes.len()];
            memory.read(read_offset, &mut buf);
            assert_eq!(bytes, buf);
            read_offset += bytes.len() as u64;
        }
    }

    #[test]
    fn should_only_request_min_number_of_pages_required(
        buffer_size in proptest::option::of(0..2 * WASM_PAGE_SIZE as usize),
        bytes in proptest::collection::vec(0..u8::MAX, 0..3 * WASM_PAGE_SIZE as usize),
        offset in 0..2 * WASM_PAGE_SIZE
    ) {
        let mut memory = VectorMemory::default();
        {
            let mut writer = build_writer(&mut memory, buffer_size, offset);
            writer.write_all(&bytes).unwrap();
            writer.flush().unwrap();
        }

        let capacity_pages = memory.size();
        let min_pages_required = if bytes.is_empty() {
            0
        } else {
            u64::div_ceil(offset + bytes.len() as u64, WASM_PAGE_SIZE)
        };

        assert_eq!(capacity_pages, min_pages_required);
    }

    #[test]
    fn should_return_err_on_memory_bounds(
        buffer_size in proptest::option::of(0..2 * WASM_PAGE_SIZE as usize),
        offset in 0..2 * WASM_PAGE_SIZE
    ) {
        let bytes = vec![0; (2 * WASM_PAGE_SIZE + 1) as usize];
        let mut memory = RestrictedMemory::new(VectorMemory::default(), 0..2);
        let mut writer = build_writer(&mut memory, buffer_size, offset);
        let result = writer.write_all(&bytes);
        assert!(result.is_err());
    }
}

fn build_writer<'a, M: Memory>(
    memory: &'a mut M,
    buffer_size: Option<usize>,
    offset: u64,
) -> Box<dyn Write + 'a> {
    let writer = Writer::new(memory, offset);
    if let Some(buffer_size) = buffer_size {
        Box::new(BufferedWriter::new(buffer_size, writer))
    } else {
        Box::new(writer)
    }
}
