use crate::reader::{BufferedReader, Reader};
use crate::{safe_write, Memory, VectorMemory, WASM_PAGE_SIZE};
use proptest::proptest;
use std::io::Read;

proptest! {
    #[test]
    fn should_read_single_slice(
        buffer_size in proptest::option::of(0..2 * WASM_PAGE_SIZE as usize),
        bytes in proptest::collection::vec(0..u8::MAX, WASM_PAGE_SIZE as usize + 1024..2 * WASM_PAGE_SIZE as usize),
        offset in 0..WASM_PAGE_SIZE,
        len in 0..1024usize
    ) {
        let memory = VectorMemory::default();
        safe_write(&memory, 0, &bytes).unwrap();
        let mut reader = build_reader(&memory, buffer_size, offset);

        let mut output = vec![0u8; len];
        let num_read = reader.read(&mut output).unwrap();

        assert_eq!(num_read, len);
        assert_eq!(output.as_slice(), &bytes[offset as usize..offset as usize + len]);
    }

    #[test]
    fn should_read_multiple_slices(
        bytes in proptest::collection::vec(0..u8::MAX, WASM_PAGE_SIZE as usize + 4096..2 * WASM_PAGE_SIZE as usize),
        offset in 0..WASM_PAGE_SIZE,
        len in 0..512usize,
        repetitions in 2..8
    ) {
        let memory = VectorMemory::default();
        safe_write(&memory, 0, &bytes).unwrap();

        // use unbuffered reader, because buffered read might return fewer bytes depending on buffer state
        let mut reader = Reader::new(&memory, offset);

        let mut read_offset = offset;
        for _ in 0..repetitions {
            let mut output = vec![0u8; len];
            let num_read = reader.read(&mut output).unwrap();

            assert_eq!(num_read, len);
            assert_eq!(output.as_slice(), &bytes[read_offset as usize..read_offset as usize + len]);
            read_offset += num_read as u64;
        }
    }

    #[test]
    fn should_read_to_end(
        buffer_size in proptest::option::of(0..2 * WASM_PAGE_SIZE as usize),
        bytes in proptest::collection::vec(0..u8::MAX, 512..WASM_PAGE_SIZE as usize),
        offset in 0..512u64,
    ) {
        let memory = VectorMemory::default();
        safe_write(&memory, 0, &bytes).unwrap();
        let mut reader = build_reader(&memory, buffer_size, offset);

        let mut output = vec![];
        reader.read_to_end(&mut output).unwrap();

        assert_eq!(output.len(), (WASM_PAGE_SIZE - offset) as usize);
        // overlapping part with modified bytes
        assert_eq!(output[..(bytes.len() - offset as usize)], bytes[offset as usize..]);
        // check rest is all zeroes until end of wasm page
        assert!(output[(bytes.len() - offset as usize)..].iter().all(|&x| x == 0));
    }
}

fn build_reader<'a, M: Memory>(
    memory: &'a M,
    buffer_size: Option<usize>,
    offset: u64,
) -> Box<dyn Read + 'a> {
    let reader = Reader::new(memory, offset);
    if let Some(buffer_size) = buffer_size {
        Box::new(BufferedReader::new(buffer_size, reader))
    } else {
        Box::new(reader)
    }
}
