if %1 == release (
    set FLAGS="--release"
) else (
    set FLAGS=""
)
set METAFLOW_CACHE=src/module_tree/test_project/cache
cargo run --features "testing" %FLAGS% -- --nocapture -q > testout.txt
git diff testout.txt