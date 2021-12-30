use std::cmp::Ordering;

use quick_proc::RealQuickSer;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default, Hash, RealQuickSer)]
pub struct ID(pub u64);

impl ID {
    pub fn new(data: &str) -> Self {
        Self(data.sdbm_hash())
    }

    #[inline]
    pub fn add(self, id: Self) -> Self {
        ID(id
            .0
            .wrapping_mul((self.0 << 32) | (self.0 >> 32))
            .wrapping_add(self.0))
    }
}

impl PartialOrd for ID {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl Ord for ID {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

pub trait SdbmHash {
    fn bytes(&self) -> &[u8];

    #[inline]
    fn sdbm_hash(&self) -> u64 {
        self.bytes().iter().fold(0, |hash, &i| {
            (i as u64)
                .wrapping_add(hash << 6)
                .wrapping_add(hash << 16)
                .wrapping_sub(hash)
        })
    }
}

impl SdbmHash for &str {
    #[inline]
    fn bytes(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl SdbmHash for &String {
    #[inline]
    fn bytes(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl SdbmHash for () {
    #[inline]
    fn bytes(&self) -> &[u8] {
        &[]
    }
}

impl SdbmHash for &Vec<u8> {
    #[inline]
    fn bytes(&self) -> &[u8] {
        self.as_slice()
    }
}
