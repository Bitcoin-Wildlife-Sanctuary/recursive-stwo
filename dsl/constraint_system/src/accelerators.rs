pub const ID_POSEIDON2: usize = 0x1;

pub struct Accelerator {
    pub id: usize,
    pub copy_len: usize,
}

#[derive(Debug, Clone)]
pub struct AcceleratorEntry {
    pub id: usize,
    pub start_idx: usize,
}
