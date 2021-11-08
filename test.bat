cargo run --features "testing" -- --nocapture -q > testout.txt
git diff testout.txt