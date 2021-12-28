use meta_ser::{MetaSer, EnumGetters, CustomDefault};
use traits::*;

#[derive(MetaSer, PartialEq, Eq, CustomDefault)]
pub struct Something {
    pub a: u32,
    #[default(10)]
    pub b: u32,
}

#[derive(MetaSer, PartialEq, Eq)]
pub struct SomeTuple(pub u32, pub u32);

#[derive(MetaSer, PartialEq, Eq)]
pub struct SomeGenerics<T> {
    pub a: T,
    pub b: T,
}

#[derive(MetaSer, PartialEq, Eq, Debug, EnumGetters)]
pub enum SomeEnum {
    A(u32),
    B(u32, u32),
}

#[derive(MetaSer, PartialEq, Eq)]
pub struct SomeStruct {
    pub a: Vec<u8>,
}

#[test]
fn test_something() {
    let s = Something {
        a: 1,
        b: 2,
    };

    let mut buffer = vec![];
    s.ser(&mut buffer);
    let mut progress = 0;
    let o_s = Something::de_ser(&mut progress, &buffer);

    assert!(progress == buffer.len());
    assert!(s == o_s);

    let s = SomeEnum::A(1);
    let mut buffer = vec![];
    s.ser(&mut buffer);
    let mut progress = 0;
    let o_s = SomeEnum::de_ser(&mut progress, &buffer);

    assert!(progress == buffer.len());
    assert!(s == o_s);

    let s = SomeStruct {
        a: vec![1, 2, 3],
    };

    let mut buffer = vec![];
    s.ser(&mut buffer);
    let mut progress = 0;
    let o_s = SomeStruct::de_ser(&mut progress, &buffer);

    assert!(progress == buffer.len());
    assert!(s == o_s);
}