pub mod cell;
pub mod sdbm;
pub mod storage;

// taken from standard lib and modified to return result
pub fn try_retain<T, F, E>(vec: &mut Vec<T>, mut f: F) -> Result<(), E>
where
    F: FnMut(&T) -> Result<bool, E>,
{
    let original_len = vec.len();
    // Avoid double drop if the drop guard is not executed,
    // since we may make some holes during the process.
    unsafe { vec.set_len(0) };

    // Vec: [Kept, Kept, Hole, Hole, Hole, Hole, Unchecked, Unchecked]
    //      |<-              processed len   ->| ^- next to check
    //                  |<-  deleted cnt     ->|
    //      |<-              original_len                          ->|
    // Kept: Elements which predicate returns true on.
    // Hole: Moved or dropped element slot.
    // Unchecked: Unchecked valid elements.
    //
    // This drop guard will be invoked when predicate or `drop` of element panicked.
    // It shifts unchecked elements to cover holes and `set_len` to the correct length.
    // In cases when predicate and `drop` never panick, it will be optimized out.
    struct BackshiftOnDrop<'a, T> {
        v: &'a mut Vec<T>,
        processed_len: usize,
        deleted_cnt: usize,
        original_len: usize,
    }

    impl<T> Drop for BackshiftOnDrop<'_, T> {
        fn drop(&mut self) {
            if self.deleted_cnt > 0 {
                // SAFETY: Trailing unchecked items must be valid since we never touch them.
                unsafe {
                    std::ptr::copy(
                        self.v.as_ptr().add(self.processed_len),
                        self.v
                            .as_mut_ptr()
                            .add(self.processed_len - self.deleted_cnt),
                        self.original_len - self.processed_len,
                    );
                }
            }
            // SAFETY: After filling holes, all items are in contiguous memory.
            unsafe {
                self.v.set_len(self.original_len - self.deleted_cnt);
            }
        }
    }

    let mut g = BackshiftOnDrop {
        v: vec,
        processed_len: 0,
        deleted_cnt: 0,
        original_len,
    };

    while g.processed_len < original_len {
        // SAFETY: Unchecked element must be valid.
        let cur = unsafe { &mut *g.v.as_mut_ptr().add(g.processed_len) };
        if !f(cur)? {
            // Advance early to avoid double drop if `drop_in_place` panicked.
            g.processed_len += 1;
            g.deleted_cnt += 1;
            // SAFETY: We never touch this element again after dropped.
            unsafe { std::ptr::drop_in_place(cur) };
            // We already advanced the counter.
            continue;
        }
        if g.deleted_cnt > 0 {
            // SAFETY: `deleted_cnt` > 0, so the hole slot must not overlap with current element.
            // We use copy for move, and never touch this element again.
            unsafe {
                let hole_slot = g.v.as_mut_ptr().add(g.processed_len - g.deleted_cnt);
                std::ptr::copy_nonoverlapping(cur, hole_slot, 1);
            }
        }
        g.processed_len += 1;
    }

    // All item are processed. This can be optimized to `set_len` by LLVM.
    drop(g);

    Ok(())
}

pub fn test() {
    storage::test();
}
