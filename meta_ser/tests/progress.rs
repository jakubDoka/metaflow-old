use meta_ser::{MetaSer, MetaDeSer, EnumGetters};
use traits::{MetaSer, MetaDeSer};

#[derive(MetaDeSer, MetaSer, PartialEq, Eq)]
pub struct Something {
    pub a: u32,
    pub b: u32,
}

#[derive(MetaDeSer, MetaSer, PartialEq, Eq)]
pub struct SomeTuple(pub u32, pub u32);

#[derive(MetaDeSer, MetaSer, PartialEq, Eq)]
pub struct SomeGenerics<T> {
    pub a: T,
    pub b: T,
}

#[derive(MetaDeSer, MetaSer, PartialEq, Eq, Debug, EnumGetters)]
pub enum SomeEnum {
    A(u32),
    B(u32, u32),
}

#[test]
fn test_something() {
    let s = Something {
        a: 1,
        b: 2,
    };

    let mut buffer = vec![];
    s.meta_ser(&mut buffer);
    let mut progress = 0;
    let o_s = Something::meta_de_ser(&mut progress, &buffer);

    assert!(progress == buffer.len());
    assert!(s == o_s);

    let s = SomeEnum::A(1);
    let mut buffer = vec![];
    s.meta_ser(&mut buffer);
    let mut progress = 0;
    let o_s = SomeEnum::meta_de_ser(&mut progress, &buffer);

    assert!(progress == buffer.len());
    assert!(s == o_s);
}