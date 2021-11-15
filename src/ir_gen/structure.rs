use super::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Structure {
    union: bool,
    fields: Vec<Field>,
}

impl Structure {
    pub fn new(union: bool, fields: Vec<Field>) -> Self {
        Structure {
            union,
            fields,
        }
    }

    pub fn union(&self) -> bool {
        self.union
    }

    pub fn fields(&self) -> &Vec<Field> {
        &self.fields
    }

    pub fn fields_mut(&mut self) -> &mut Vec<Field> {
        &mut self.fields
    }

    pub fn load_field(&self, name: &Token) -> Option<Field> {
        self.fields
            .iter()
            .find(|f| f.name().deref() == name.value().deref())
            .map(Clone::clone)
            .or_else(|| {
                self.fields
                    .iter()
                    .filter(|f| f.embedded() && f.datatype().is_on_stack())
                    .map(|f| {
                        (
                            f,
                            match &f.datatype().kind() {
                                DKind::Structure(s) => s.load_field(name),
                                _ => unreachable!(),
                            },
                        )
                    })
                    .find(|(_, f)| f.is_some())
                    .map(|(f, ef)| {
                        let ef = ef.unwrap();
                        Field::new(
                            false,
                            f.offset() + ef.offset(),
                            StrRef::empty(),
                            ef.datatype().clone(),
                        )
                    })
            })
    }
}