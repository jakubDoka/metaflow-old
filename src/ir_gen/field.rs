use super::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    embedded: bool,
    offset: u32,
    name: Spam,
    datatype: Cell<Datatype>,
}

impl Field {
    pub fn new(embedded: bool, offset: u32, name: Spam, datatype: Cell<Datatype>) -> Self {
        Self {
            embedded,
            offset,
            name,
            datatype,
        }
    }

    pub fn name(&self) -> &Spam {
        &self.name
    }

    pub fn datatype(&self) -> &Cell<Datatype> {
        &self.datatype
    }

    pub fn offset(&self) -> u32 {
        self.offset
    }

    pub fn set_offset(&mut self, offset: u32) {
        self.offset = offset;
    }

    pub fn embedded(&self) -> bool {
        self.embedded
    }

    pub fn datatype_mut(&mut self) -> &mut Datatype {
        &mut self.datatype
    }
}
