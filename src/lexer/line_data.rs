use super::*;

#[derive(Debug, Clone, Default)]
pub struct LineData {
    line: usize,
    column: usize,
    file_name: StrRef,
}

impl LineData {
    pub fn new(line: usize, column: usize, file_name: StrRef) -> Self {
        Self {
            line,
            column,
            file_name,
        }
    }

    pub fn file_name(&self) -> &StrRef {
        &self.file_name
    }
}
