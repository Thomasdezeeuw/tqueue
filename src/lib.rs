use std::sync::atomic::Ordering;

mod pos;
mod segment;
mod state;


// TODO: try to relax the ordering, on a per call basis.
const DEFAULT_ORDERING: Ordering = Ordering::SeqCst;

#[cfg(test)]
mod assertions {
    use std::{fmt, mem};

    use super::pos::AtomicPos;
    use super::state::AtomicState;
    use super::segment::SegmentData;

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
    fn atomic_pos() {
        assert_send::<AtomicPos>();
        assert_sync::<AtomicPos>();
        assert_debug::<AtomicPos>();

        #[cfg(target_pointer_width = "64")]
        let want = 8;
        #[cfg(target_pointer_width = "32")]
        let want = 4;
        assert_size::<AtomicPos>(want);
    }

    #[test]
    fn segment_data() {
        assert_send::<SegmentData<u64>>();
        assert_sync::<SegmentData<u64>>();
        assert_debug::<SegmentData<u64>>();

        // Size of `AtomicState` + the size of an option of `u64`.
        let want = mem::size_of::<AtomicState>() + mem::size_of::<Option<u64>>();
        assert_size::<SegmentData<u64>>(want);
    }
}
