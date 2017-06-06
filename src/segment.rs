use std::cell::UnsafeCell;
use std::{fmt, mem, ptr};

use super::state::AtomicState;

/// `SegmentData` is a piece of data that can be written to once and read once,
/// and can then be reused.
pub struct SegmentData<T> {
    /// The state of the data.
    state: AtomicState,

    /// The actual data, protected by the state.
    data: UnsafeCell<T>,
}

impl<T> SegmentData<T> {
    /// Create new empty segment data.
    pub fn empty() -> SegmentData<T> {
        SegmentData {
            state: AtomicState::empty(),
            data: unsafe { mem::uninitialized() },
        }
    }

    /// Check if the data is empty.
    pub fn is_empty(&self) -> bool {
        self.state.is_empty()
    }

    /// Check if the data is ready for reading.
    pub fn is_ready(&self) -> bool {
        self.state.is_ready()
    }

    /// Write a value to the segment. This will return an error including the
    /// value if the data can't be written, this can happen if segment is
    /// currently not empty (this includes when the data is being read from or
    /// written to).
    pub fn write(&self, value: T) -> Result<(), T> {
        // Set the state to writing, if this returns false it means we can't
        // write the value currently and we'll return an error.
        if self.state.set_writing() {
            // Write the actual data.
            unsafe { ptr::write(self.data.get(), value); }
            // Update the state to indicate the data is ready.
            // TODO: what to do with this check.
            assert!(self.state.set_ready());
            Ok(())
        } else {
            Err(value)
        }
    }

    /// Read the data from the current segment and remove it. After which the
    /// segment will be empty. If the segment is already empty it will return
    /// `None`.
    pub fn pop(&self) -> Option<T> {
        // Set the state to reading, if this returns false it means we can't
        // read the value currently and we'll return `None`.
        if self.state.set_reading() {
            // Read the data located on the heap, this will allocate a
            let data = unsafe { ptr::read(self.data.get()) };
            // Update the state to indicate the data is empty.
            // TODO: what to do with this check.
            assert!(self.state.set_empty());
            Some(data)
        } else {
            None
        }
    }
}

impl<T> fmt::Debug for SegmentData<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.pad("SegmentData{{ ... }}")
    }
}

unsafe impl<T> Sync for SegmentData<T> {}

#[cfg(test)]
mod tests {
    use super::*;

    struct NotCopyable {
        value: usize,
        /// This is here to make sure the memory gets allocted.
        #[allow(dead_code)]
        bytes: [u8; 100]
    }

    impl NotCopyable {
        pub fn new(value: usize) -> NotCopyable {
            NotCopyable {
                value: value,
                bytes: [0; 100],
            }
        }
    }

    impl PartialEq for NotCopyable {
        fn eq(&self, other: &NotCopyable) -> bool {
            self.value == other.value
        }
    }

    impl fmt::Debug for NotCopyable {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "NotCopyable{{ value: {} }}", self.value)
        }
    }

    impl Clone for NotCopyable {
        fn clone(&self) -> NotCopyable {
            NotCopyable::new(self.value)
        }
    }

    #[test]
    fn segment_data_simple() {
        test_segment_data(1, 2, 0);
    }

    #[test]
    fn segment_data_str() {
        test_segment_data("value 1", "value 2", "err value");
    }

    #[test]
    fn segment_data_not_copyable() {
        test_segment_data(NotCopyable::new(100), NotCopyable::new(200), NotCopyable::new(0));
    }

    #[test]
    fn segment_data_string() {
        test_segment_data("value 1".to_owned(), "value 2".to_owned(), "err value".to_owned());
    }

    #[test]
    fn segment_data_vector() {
        test_segment_data(vec![1, 2, 3], vec![4, 5, 6], vec![]);
    }

    fn test_segment_data<T>(value1: T, value2: T, err_value: T)
        where T: Clone + PartialEq + fmt::Debug
    {
        let data = SegmentData::empty();
        assert!(data.is_empty());
        assert!(!data.is_ready());
        assert!(data.pop().is_none());

        // Write some data.
        assert!(data.write(value1.clone()).is_ok());
        assert!(!data.is_empty());
        assert!(data.is_ready());

        // Shouldn't be able to write again.
        assert!(data.write(err_value.clone()).is_err());

        // Read (pop) the data.
        let got1 = data.pop();
        assert_eq!(got1, Some(value1.clone()));
        assert!(data.is_empty());
        assert!(!data.is_ready());
        assert!(data.pop().is_none());

        // Test reuseage:

        // Write and read some data again.
        assert!(data.write(value2.clone()).is_ok());
        assert!(!data.is_empty());
        assert!(data.is_ready());
        let got2 = data.pop();
        assert_eq!(got2, Some(value2));
        assert!(data.is_empty());
        assert!(!data.is_ready());
        assert!(data.pop().is_none());

        // Test the orignal value again, make sure it's not overwritten.
        assert_eq!(got1, Some(value1));
        assert!(got1 != got2);
    }
}
