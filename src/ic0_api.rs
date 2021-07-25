#[link(wasm_import_module = "ic0")]
extern "C" {
    pub fn stable_size() -> u32;
    pub fn stable_grow(additional_pages: u32) -> i32;
    pub fn stable_read(dst: u32, offset: u32, size: u32);
    pub fn stable_write(offset: u32, src: u32, size: u32);
}
