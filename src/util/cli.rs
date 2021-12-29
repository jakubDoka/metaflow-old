use std::ops::Deref;

use super::sdbm::ID;

#[derive(Debug)]
pub struct Arguments {
    _filename: String,
    hash: ID,
    flags: Vec<String>,
    field_flags: Vec<(String, String)>,
    args: Vec<String>,
}

impl Arguments {
    pub fn new<T: Iterator<Item = String>>(args: T) -> Result<Arguments, ArgumentError> {
        let mut args = args.collect::<Vec<_>>();
        let mut result = Arguments {
            _filename: args
                .first()
                .cloned()
                .ok_or(ArgumentError::MissingFilename)?,
            flags: vec![],
            field_flags: vec![],
            args: vec![],
            hash: args
                .iter()
                .skip(1)
                .fold(ID(0), |acc, i| acc.add(ID::new(i.as_str()))),
        };

        let mut args = args.drain(1..);

        while let Some(mut arg) = args.next() {
            if arg.starts_with("--") {
                arg.replace_range(0..2, "");
                let mut value = args
                    .next()
                    .ok_or_else(|| ArgumentError::MissingValue(arg.clone()))?;
                Self::collect_arg(&mut value, &mut args);
                result.field_flags.push((arg, value));
                continue;
            }

            if arg.starts_with("-") {
                arg.replace_range(0..1, "");
                result.flags.push(arg);
                continue;
            }

            Self::collect_arg(&mut arg, &mut args);

            result.args.push(arg);
        }

        Ok(result)
    }

    pub fn hash(&self) -> ID {
        self.hash
    }

    fn collect_arg<T: Iterator<Item = String>>(arg: &mut String, args: &mut T) {
        if arg.starts_with('"') {
            arg.remove(0);
            while let Some(rest) = args.next() {
                arg.push(' ');
                arg.push_str(&rest);

                if rest.ends_with('"') {
                    arg.pop();
                    break;
                }
            }
        }
    }

    pub fn from_str(s: &str) -> Result<Arguments, ArgumentError> {
        Arguments::new(s.split_whitespace().map(|s| s.to_string()))
    }

    pub fn enabled(&self, flag: &str) -> bool {
        self.flags.iter().any(|f| f == flag)
    }

    pub fn get_flag(&self, flag: &str) -> Option<&str> {
        self.field_flags
            .iter()
            .find(|(f, _)| f == flag)
            .map(|(_, v)| v.as_str())
    }
}

impl Deref for Arguments {
    type Target = Vec<String>;

    fn deref(&self) -> &Self::Target {
        &self.args
    }
}

#[derive(Debug)]
pub enum ArgumentError {
    MissingValue(String),
    MissingFilename,
}

pub fn test() {
    println!(
        "{:?}",
        Arguments::new(
            "file arg -flag --flag value arg -flag"
                .split(" ")
                .map(|s| s.to_string())
        )
    );

    println!(
        "{:?}",
        Arguments::new("file \"string value\"".split(" ").map(|s| s.to_string()))
    );
}
