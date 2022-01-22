use std::path::PathBuf;

use quick_proc::QuickSer;

use crate::util::sdbm::ID;

pub trait IncrementalData: QuickSer {
    /// Prepare the data for serialization. Usually just clear
    /// unwanted data to save time and memory.
    fn prepare(&mut self) {}

    fn load_data(root_path: &str, arg_hash: ID) -> Option<(Self, usize)> {
        let mut path = PathBuf::new();
        path.push(root_path);
        path.push("meta");
        path.push(format!("{:x}.bin", arg_hash.0));
        if !path.exists() {
            return None;
        }

        let file = std::fs::read(path).ok()?;

        let mut reader = snap::read::FrameDecoder::new(file.as_slice());

        let mut writer = Vec::with_capacity(snap::raw::decompress_len(&file).ok()?);

        std::io::copy(&mut reader, &mut writer).ok()?;

        let mut progress = 0;
        let version = String::de_ser(&mut progress, &writer);
        if version != crate::COMMIT_HASH {
            return None;
        }

        let data = Self::de_ser(&mut progress, &writer);

        Some((data, progress))
    }

    fn save_data(
        &mut self,
        root_path: &str,
        arg_hash: ID,
        size_hint: Option<usize>,
    ) -> std::io::Result<()> {
        self.prepare();


        let mut buffer = Vec::with_capacity(size_hint.unwrap_or(1024 * 1024));

        crate::COMMIT_HASH.to_string().ser(&mut buffer);

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
