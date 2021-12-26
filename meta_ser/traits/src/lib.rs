
pub trait MetaSer {
    fn meta_ser(&self, buffer: &mut Vec<u8>);
}

pub trait MetaDeSer {
    fn meta_de_ser(progress: &mut usize, buffer: &[u8]) -> Self;
}

impl MetaSer for String {
    fn meta_ser(&self, buffer: &mut Vec<u8>) {
        self.len().meta_ser(buffer);
        buffer.extend_from_slice(self.as_bytes());
    }
}

impl<T: MetaSer> MetaSer for Option<T> {
    fn meta_ser(&self, buffer: &mut Vec<u8>) {
        match self {
            Some(t) => {
                buffer.push(1);
                t.meta_ser(buffer);
            },
            None => {
                buffer.push(0);
            },
        }
    }
}

impl<T: MetaDeSer> MetaDeSer for Option<T> {
    fn meta_de_ser(progress: &mut usize, buffer: &[u8]) -> Self {
        match buffer[*progress] {
            0 => {
                *progress += 1;
                None
            },
            1 => {
                *progress += 1;
                Some(T::meta_de_ser(progress, buffer))
            },
            _ => panic!("invalid enum tag"),
        }
    }
}

impl MetaDeSer for String {
    fn meta_de_ser(progress: &mut usize, buffer: &[u8]) -> Self {
        let len = usize::meta_de_ser(progress, buffer);
        let mut result = String::with_capacity(len);
        result.push_str(unsafe { 
            std::str::from_utf8_unchecked(&buffer[*progress..*progress + len]) 
        });
        *progress += len;
        result
    }
}

impl<T: MetaSer> MetaSer for Vec<T> {
    fn meta_ser(&self, buffer: &mut Vec<u8>) {
        self.len().meta_ser(buffer);
        for item in self {
            item.meta_ser(buffer);
        }
    }
}

impl<T: MetaDeSer> MetaDeSer for Vec<T> {
    fn meta_de_ser(progress: &mut usize, buffer: &[u8]) -> Self {
        let mut result = Vec::with_capacity(usize::meta_de_ser(progress, buffer));
        for _ in 0..result.capacity() {
            result.push(T::meta_de_ser(progress, buffer));
        }
        result
    }
}

macro_rules! impl_traits_for_numbers {
    ($($integer:ty),*) => {
        $(
            impl MetaSer for $integer {
                fn meta_ser(&self, buffer: &mut Vec<u8>) {
                    buffer.extend(self.to_le_bytes());
                }
            }
            
            impl MetaDeSer for $integer {
                fn meta_de_ser(progress: &mut usize, buffer: &[u8]) -> Self {
                    const SIZE: usize = std::mem::size_of::<$integer>();
                    let slice = buffer[*progress..*progress + SIZE].try_into().unwrap();
                    *progress += SIZE;
                    Self::from_le_bytes(slice)
                }
            }
        )*
    };
}

impl_traits_for_numbers!(
    u8, u16, u32, u64, u128, usize, 
    i8, i16, i32, i64, i128, isize,
    f32, f64
);
