
pub trait MetaSer where Self: Sized {
    fn ser(&self, buffer: &mut Vec<u8>);

    fn quick_ser(&self, _buffer: &mut Vec<u8>) {
        unimplemented!();
    }

    fn de_ser(progress: &mut usize, buffer: &[u8]) -> Self;

    fn quick_de_ser(_progress: &mut usize, _buffer: &[u8]) -> Self {
        unimplemented!();
    }
}

pub trait MetaQuickSer: Copy {}

impl MetaSer for String {
    fn ser(&self, buffer: &mut Vec<u8>) {
        self.len().ser(buffer);
        buffer.extend_from_slice(self.as_bytes());
    }

    fn de_ser(progress: &mut usize, buffer: &[u8]) -> Self {
        let len = usize::de_ser(progress, buffer);
        let mut result = String::with_capacity(len);
        result.push_str(unsafe { 
            std::str::from_utf8_unchecked(&buffer[*progress..*progress + len]) 
        });
        *progress += len;
        result
    }
}

impl<T: MetaSer> MetaSer for Option<T> {
    fn ser(&self, buffer: &mut Vec<u8>) {
        match self {
            Some(t) => {
                buffer.push(1);
                t.ser(buffer);
            },
            None => {
                buffer.push(0);
            },
        }
    }

    fn de_ser(progress: &mut usize, buffer: &[u8]) -> Self {
        match buffer[*progress] {
            0 => {
                *progress += 1;
                None
            },
            1 => {
                *progress += 1;
                Some(T::de_ser(progress, buffer))
            },
            _ => panic!("invalid enum tag"),
        }
    }
}

impl<T: MetaSer> MetaSer for Vec<T> {
    fn ser(&self, buffer: &mut Vec<u8>) {
        self.len().ser(buffer);
        for item in self {
            item.ser(buffer);
        }
    }

    fn quick_ser(&self, buffer: &mut Vec<u8>) {
        self.len().ser(buffer);
        let len = self.len() * std::mem::size_of::<T>();
        let new_len = len + buffer.len();
        buffer.reserve(new_len);
        unsafe {
            buffer.set_len(new_len);
            std::ptr::copy_nonoverlapping(
                self.as_ptr() as *const u8, 
                buffer.as_mut_ptr().offset((buffer.len() - len) as isize), 
                len
            );
        }
    }

    fn de_ser(progress: &mut usize, buffer: &[u8]) -> Self {
        let mut result = Vec::with_capacity(usize::de_ser(progress, buffer));
        for _ in 0..result.capacity() {
            result.push(T::de_ser(progress, buffer));
        }
        result
    }

    fn quick_de_ser(progress: &mut usize, buffer: &[u8]) -> Self {
        let len = usize::de_ser(progress, buffer);
        let mut result = Vec::with_capacity(len);
        let true_len = len * std::mem::size_of::<T>();
        unsafe {
            result.set_len(len);
            std::ptr::copy_nonoverlapping(
                buffer.as_ptr().offset(*progress as isize),
                result.as_mut_ptr() as *mut u8,
                true_len
            );
        }
        *progress += true_len;
        result
    }
}

impl<T: MetaQuickSer> MetaSer for T {
    fn ser(&self, buffer: &mut Vec<u8>) {
        let size = std::mem::size_of::<T>();
        let new_len = buffer.len() + size;
        buffer.reserve(new_len);
        unsafe {
            buffer.set_len(new_len);
            std::ptr::write(
                buffer.as_mut_ptr().offset((buffer.len() - size) as isize) as *mut T,
                *self
            );
        }
    }

    fn de_ser(progress: &mut usize, buffer: &[u8]) -> Self {
        let size = std::mem::size_of::<T>();
        let result = unsafe {
            std::ptr::read(
                buffer.as_ptr().offset(*progress as isize) as *const T
            )
        };
        *progress += size;
        result
    }
}

macro_rules! impl_traits_for_numbers {
    ($($integer:ty),*) => {
        $(
            impl MetaQuickSer for $integer {}
        )*
    };
}

impl_traits_for_numbers!(
    u8, u16, u32, u64, u128, usize, 
    i8, i16, i32, i64, i128, isize,
    f32, f64
);
