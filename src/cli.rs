#[derive(Debug)]
pub struct Arguments {
    pub filename: String,
    pub flags: Vec<String>,
    pub field_flags: Vec<(String, String)>,
    pub args: Vec<String>,
}

impl Arguments {
    pub fn new<T: Iterator<Item = String>>(mut args: T) -> Result<Arguments, ArgumentError> {
        let mut result = Arguments {
            filename: args.next().ok_or(ArgumentError::MissingFilename)?,
            flags: Vec::new(),
            field_flags: Vec::new(),
            args: Vec::new(),
        };

        loop {
            let mut arg = match args.next() {
                Some(arg) => arg,
                None => break,
            };

            if arg.starts_with("--") || arg.starts_with("-") {
                let i = if arg.starts_with("--") { 2 } else { 1 };

                arg.replace_range(..i, "");

                if arg.ends_with(":") {
                    arg.pop();
                    let value = args
                        .next()
                        .ok_or_else(|| ArgumentError::MissingValue(arg.clone()))?;
                    result.field_flags.push((arg, value));
                } else {
                    result.flags.push(arg);
                }
                continue;
            }

            if arg.starts_with('"') {
                loop {
                    let rest = match args.next() {
                        Some(rest) => rest,
                        None => break,
                    };

                    arg.push(' ');
                    arg.push_str(&rest);

                    if rest.ends_with('"') {
                        arg.remove(0);
                        arg.pop();
                        break;
                    }
                }
            }

            result.args.push(arg);
        }

        Ok(result)
    }

    pub fn from_str(s: &str) -> Result<Arguments, ArgumentError> {
        Arguments::new(s.split_whitespace().map(|s| s.to_string()))
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
            "file arg -flag --flag: value arg --flag"
                .split(" ")
                .map(|s| s.to_string())
        )
    );

    println!(
        "{:?}",
        Arguments::new("file \"string value\"".split(" ").map(|s| s.to_string()))
    );
}
