use super::*;

#[derive(Debug, Clone, Default)]
pub struct LineData {
    line: usize,
    column: usize,
    file_name: Spam,
}

impl LineData {
    pub fn new(line: usize, column: usize, file_name: Spam) -> Self {
        Self {
            line,
            column,
            file_name,
        }
    }

    pub fn file_name(&self) -> &Spam {
        &self.file_name
    }
}
