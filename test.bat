set METAFLOW_CACHE=src/module_tree/test_project/cache
cargo run --features "testing" --release -- --nocapture -q > testout.txt
git diff testout.txt