#[derive(Clone, Copy, Debug, PartialEq, Default)]
pub struct ID(u64);

impl ID {
    #[inline]
    pub fn new() -> ID {
        ID(0)
    }

    #[inline]
    pub fn combine(self, id: Self) -> Self {
        ID(self.0.wrapping_add(id.0))
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
