use std::cmp::Ordering;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default, Hash)]
pub struct ID(pub u64);

impl ID {
    #[inline]
    pub fn combine(self, id: Self) -> Self {
        ID((id.0) ^ (self.0 << 32) ^ (self.0 >> 32))	
    }
}

pub trait SdbmHashState {
    fn add<T: SdbmHash>(self, data: T) -> Self;
}

impl SdbmHashState for ID {
    #[inline]
    fn add<T: SdbmHash>(self, data: T) -> Self {
        ID(data.sdbm_hash(self.0))
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
    fn sdbm_hash(&self, init: u64) -> u64 {
        self.bytes().iter().fold(init, |hash, &i| {
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
