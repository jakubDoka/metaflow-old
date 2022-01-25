//! Module handles loading and saving of incremental data.
use std::path::PathBuf;

use quick_proc::QuickSer;

use crate::util::sdbm::ID;

/// Incremental data adds loading and saving methods to the type. Data is also 
/// compressed before saving on disc and decompressed before loading.
pub trait IncrementalData: QuickSer {
    /// Prepare the data for serialization. Usually just clear
    /// unwanted data to save time and memory.
    fn prepare(&mut self) {}

    /// Loads data based of  `root_path` that is the path to the root of the project.
    /// `hash` is to pick different save file based of for example command line arguments.
    /// If anything went wrong with loading, None is returned. This does not mean that loading
    /// cannot crash as change of data structure makes loading strategy useless. Thats why version
    /// of compiler is looked up each time data is loaded.
    fn load_data(root_path: &str, hash: ID) -> Option<(Self, usize)> {
        let mut path = PathBuf::new();
        path.push(root_path);
        path.push("meta");
        path.push(format!("{:x}.bin", hash.0));
        if !path.exists() {
            return None;
        }

        let file = std::fs::read(path).ok()?;

        let mut reader = snap::read::FrameDecoder::new(file.as_slice());

        let mut writer = Vec::with_capacity(snap::raw::decompress_len(&file).ok()?);

        std::io::copy(&mut reader, &mut writer).ok()?;

        let mut progress = 0;
        let version = String::de_ser(&mut progress, &writer);
        if version != crate::VERSION {
            return None;
        }

        let data = Self::de_ser(&mut progress, &writer);

        Some((data, progress))
    }

    /// Saves incremental data to disc. Location is determined as 
    /// `root_path` / meta / `hash` .bin. Data is compressed.
    fn save_data(
        &mut self,
        root_path: &str,
        arg_hash: ID,
        size_hint: Option<usize>,
    ) -> std::io::Result<()> {
        self.prepare();


        let mut buffer = Vec::with_capacity(size_hint.unwrap_or(1024 * 1024));

        crate::VERSION.to_string().ser(&mut buffer);

        self.ser(&mut buffer);


        let mut path = PathBuf::new();
        path.push(root_path);
        path.push("meta");
        std::fs::create_dir_all(&path)?;
        path.push(format!("{:x}.bin", arg_hash.0));

        let mut file = std::fs::File::create(path)?;

        let mut data = snap::write::FrameEncoder::new(&mut file);

        std::io::copy(&mut buffer.as_slice(), &mut data)?;

        Ok(())
    }
}
