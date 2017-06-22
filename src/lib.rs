use std::sync::atomic::Ordering;

mod segment;
mod state;


// TODO: try to relax the ordering, on a per call basis.
const DEFAULT_ORDERING: Ordering = Ordering::SeqCst;

#[cfg(test)]
mod assertions {
    use std::{fmt, mem};

    use super::state::AtomicState;
    use super::segment::{Segment, SegmentData, SEGMENT_SIZE};
    use super::queue::Queue;

    fn assert_send<T: Send>() {}
    fn assert_sync<T: Sync>() {}
    fn assert_debug<T: fmt::Debug>() {}
    fn assert_size<T>(want: usize) {
        assert_eq!(mem::size_of::<T>(), want);
    }

    #[test]
    fn atomic_state() {
        assert_send::<AtomicState>();
        assert_sync::<AtomicState>();
        assert_debug::<AtomicState>();

        #[cfg(target_pointer_width = "64")]
        let want = 8;
        #[cfg(target_pointer_width = "32")]
        let want = 4;
        assert_size::<AtomicState>(want);
    }

    #[test]
    fn segment_data() {
        assert_send::<SegmentData<u64>>();
        assert_sync::<SegmentData<u64>>();
        assert_debug::<SegmentData<u64>>();

        // 8 or 4 for the state, 8 bytes for the Option, 8 for u64 (the data).
        #[cfg(target_pointer_width = "64")]
        let want = 8 + 8 + 8;
        #[cfg(target_pointer_width = "32")]
        let want = 4 + 8 + 8;
        assert_size::<SegmentData<u64>>(want);
    }

    #[test]
    fn segment() {
        assert_send::<Segment<u64>>();
        assert_sync::<Segment<u64>>();
        assert_debug::<Segment<u64>>();

        // TODO: make the assertions below more static, so they complain when
        // something changes.

        // 8 bytes for the id, `SEGMENT_SIZE` * `SegmentData`, 2x pointers.
        #[cfg(target_pointer_width = "64")]
        let want = 8 + (SEGMENT_SIZE * (8 + 8 + 8)) + 8 + 8;
        #[cfg(target_pointer_width = "32")]
        let want = 8 + (SEGMENT_SIZE * (8 + 8 + 8)) + 4 + 4;
        assert_size::<Segment<u64>>(want);
    }

    #[test]
    fn queue() {
        assert_send::<Queue<u64>>();
        assert_sync::<Queue<u64>>();
        assert_debug::<Queue<u64>>();

        // 2x pointer for atomic pointers, 2x atomic isize.
        #[cfg(target_pointer_width = "64")]
        let want = 8 + 8 + 8 + 8;
        #[cfg(target_pointer_width = "32")]
        let want = 4 + 4 + 4 + 4;
        assert_size::<Queue<u64>>(want);
    }
}
