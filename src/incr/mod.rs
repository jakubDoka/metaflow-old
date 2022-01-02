use std::path::PathBuf;

use quick_proc::QuickSer;

use crate::util::sdbm::ID;

pub fn load_data<T: QuickSer>(root_path: &str, arg_hash: ID) -> Option<(T, usize)> {
    let mut path = PathBuf::new();
    path.push(root_path);
    path.push("meta");
    path.push(format!("{:x}.bin", arg_hash.0));
    if !path.exists() {
        return None;
    }

    let mut file = std::fs::read(path).ok()?;

    let mut progress = 0;
    let version = String::de_ser(&mut progress, &mut file);
    if version != crate::VERSION {
        return None;
    }

    let data = T::de_ser(&mut progress, &mut file);

    Some((data, progress))
}

pub fn save_data<T: QuickSer>(
    root_path: &str,
    data: &T,
    arg_hash: ID,
    size_hint: Option<usize>,
) -> std::io::Result<()> {
    let mut buffer = Vec::with_capacity(size_hint.unwrap_or(1024 * 1024));

    crate::VERSION.to_string().ser(&mut buffer);

    data.ser(&mut buffer);

    let mut path = PathBuf::new();
    path.push(root_path);
    path.push("meta");
    std::fs::create_dir_all(&path)?;
    path.push(format!("{:x}.bin", arg_hash.0));

    std::fs::write(path, buffer)?;

    Ok(())
}
