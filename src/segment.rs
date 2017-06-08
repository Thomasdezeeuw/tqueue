use std::cell::UnsafeCell;
use std::{fmt, mem};

use super::state::AtomicState;

/// `SegmentData` is a piece of data that can be written to once and then read
/// once, and can then be reused. It is not possible to overwrite the data or
/// read the data twice.
///
/// It is made for, and therefore safe for, concurrent use if `T` is [`Send`]
/// and [`Sync`].
///
/// [`Send`]: https://doc.rust-lang.org/nightly/core/marker/trait.Send.html
/// [`Sync`]: https://doc.rust-lang.org/nightly/core/marker/trait.Sync.html
pub struct SegmentData<T> {
    /// The state of the data.
    state: AtomicState,

    /// The actual data, protected by the state.
    ///
    /// If the `state` is `Empty` this must be `None`. However if the `state` is
    /// `Ready` this must be `Some`.
    data: UnsafeCell<Option<T>>,
}

impl<T> SegmentData<T> {
    /// Create new empty `SegmentData`.
    pub fn empty() -> SegmentData<T> {
        SegmentData {
            state: AtomicState::empty(),
            data: UnsafeCell::new(None),
        }
    }

    /// Check if the `SegmentData` is empty.
    pub fn is_empty(&self) -> bool {
        self.state.is_empty()
    }

    /// Check if the `SegmentData` is ready for reading.
    pub fn is_ready(&self) -> bool {
        self.state.is_ready()
    }

    /// Try to write a value to this `SegmentData`. If the state of this
    /// `SegmentData` is not [`Empty`], this includes when the data is being
    /// read from or written to, the value can't be written. If this is the case
    /// this function will return an error, which includes the value so it can be
    /// used in trying the write operation again.
    ///
    /// [`Empty`]: ../state/enum.State.html#variant.Empty
    pub fn try_write(&self, value: T) -> Result<(), T> {
        // Set the state to writing, if this returns false it means we can't
        // currently write the value and we'll return an error.
        if self.state.set_writing() {
            // This is safe because of the contract described in the `data`
            // field.
            mem::replace(unsafe { &mut *self.data.get() } , Some(value));

            // Update the `state` to indicate the data is `Ready`.
            // TODO: what to do with this check.
            assert!(self.state.set_ready());
            Ok(())
        } else {
            Err(value)
        }
    }

    /// This function does the same thing as [`try_write`], however if
    /// [`try_write`] returns an error this function will try it again until it
    /// succeeds or until it tried `tries` many times.
    ///
    /// [`try_write`]: struct.SegmentData.html#method.try_write
    pub fn write(&self, value: T, tries: usize) -> Result<(), T> {
        if tries == 0 {
            Err(value)
        } else {
            self.try_write(value)
                .or_else(|value| self.write(value, tries - 1))
        }
    }

    /// Try to read the data from this `SegmentData` and remove it, after which
    /// it will be empty. If the state is not [`Ready`], this includes when the
    /// data is being read from or written to, the value can't be read. If
    /// this is the case this function will return `None`.
    ///
    /// [`Ready`]: ../state/enum.State.html#variant.Ready
    pub fn try_pop(&self) -> Option<T> {
        // Set the state to reading, if this returns false it means we currently
        // can't read the value and we'll return `None`.
        if self.state.set_reading() {
            unsafe { self.take_data() }
        } else {
            None
        }
    }

    /// Take the value without checking if the state is [`Ready`] and setting it
    /// to [`Reading`], **this is the callers responsibility**. This is also the
    /// reason why this function is unsafe.
    ///
    /// The state will be updated to [`Empty`] after taking the data.
    ///
    /// # Safety
    ///
    /// The state must be set to [`Reading`] before calling this function, this is
    /// the reason this function is unsafe.
    ///
    /// [`Ready`]: ../state/enum.State.html#variant.Ready
    /// [`Reading`]: ../state/enum.State.html#variant.Reading
    /// [`Empty`]: ../state/enum.State.html#variant.Empty
    unsafe fn take_data(&self) -> Option<T> {
        // Take the data and leave `None` in its place. This is safe because of
        // the contract described in the `data` field as well as the contract
        // describe in the function documentation about the state.
        let data = (&mut *self.data.get()).take();

        // Update the state to indicate the data is empty.
        // TODO: what to do with this check.
        assert!(self.state.set_empty());
        data
    }

    /// This function does the same thing as [`try_pop`], however if [`try_pop`]
    /// returns `None` this function will try it again until it returns
    /// something or until it tried `tries` many times.
    ///
    /// [`try_pop`]: struct.SegmentData.html#method.try_pop
    pub fn pop(&self, tries: usize) -> Option<T> {
        if tries == 0 {
            None
        } else {
            self.try_pop().or_else(|| self.pop(tries - 1))
        }
    }

    /// This is the same as [`try_pop`], however makes sure the returned data
    /// fulfills the provided `predicate`. See [`try_pop`] for more.
    ///
    /// # Note
    ///
    /// The `predicate` function is called while blocking all other operations
    /// on this `SegmentData`, thus is it advised to make sure the `predicate`
    /// function doesn't take too long.
    ///
    /// [`try_pop`]: struct.SegmentData.html#method.try_pop
    pub fn conditional_try_pop<F>(&self, predicate: F) -> Option<T>
        where F: Fn(&T) -> bool
    {
        // Set the state to reading, if this returns false it means we currently
        // can't read the value and we'll return `None`.
        if self.state.set_reading() {
            // Get a reference to the data for calling the predicate.
            let data = unsafe {
                // This is safe because of the contract described in the `data`
                // field.
                &*self.data.get()
            }.as_ref().unwrap();

            if predicate(data) {
                // This is safe because we made sure the state is in `Reading`.
                unsafe { self.take_data() }
            } else {
                // Revert the state to indicate the data is still present.
                // TODO: what to do with this check.
                assert!(self.state.return_ready());
                None
            }
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

impl<T> Default for SegmentData<T> {
    /// Create an empty `SegmentData`, this does the same thing as
    /// `SegmentData::empty`.
    ///
    /// # Note
    ///
    /// It does not use `T`'s default value as starting value.
    fn default() -> SegmentData<T> {
        SegmentData::empty()
    }
}

unsafe impl<T: Send + Sync> Send for SegmentData<T> {}

unsafe impl<T: Send + Sync> Sync for SegmentData<T> {}

#[cfg(test)]
mod tests {
    use std::sync::{Arc, RwLock};

    use super::*;

    #[derive(Eq, PartialEq, Ord, PartialOrd, Debug, Clone)]
    struct NoCopy(usize);

    struct DropTest(Arc<RwLock<NoCopy>>);

    impl Drop for DropTest {
        fn drop(&mut self) {
            let mut value = self.0.write().unwrap();
            value.0 += 1;
        }
    }

    #[test]
    fn segment_data_drop_test() {
        let value = Arc::new(RwLock::new(NoCopy(0)));

        test_drop_empty_segment_data();
        test_drop_filled_segment_data(value.clone());
        test_drop_after_poping_segment_data(value.clone());
        assert_eq!(*value.read().unwrap(), NoCopy(2));
    }

    fn test_drop_filled_segment_data(value: Arc<RwLock<NoCopy>>) {
        {
            let data = SegmentData::empty();
            {
                assert!(data.try_write(DropTest(value.clone())).is_ok());
            }
            // Should not be dropped yet.
            assert_eq!(*value.read().unwrap(), NoCopy(0));
        }
        // The data should be dropped now.
        assert_eq!(*value.read().unwrap(), NoCopy(1));
    }

    fn test_drop_empty_segment_data() {
        // Shouldn't try to drop anything.
        let data: SegmentData<DropTest> = SegmentData::empty();
        // Shouldn't panic.
        mem::drop(data);
    }

    fn test_drop_after_poping_segment_data(value: Arc<RwLock<NoCopy>>) {
        {
            let data = SegmentData::empty();
            {
                assert!(data.try_write(DropTest(value.clone())).is_ok());
            }
            {
                let got_value = data.try_pop();
                // Should not be dropped yet.
                assert_eq!(*value.read().unwrap(), NoCopy(1));
                let got = &got_value.unwrap().0;
                let got = got.read().unwrap();
                let want = value.read().unwrap().clone();
                assert_eq!(*got, want);
                // Shouldn't be dropped yet.
                assert_eq!(*value.read().unwrap(), NoCopy(1));
            }
            // The data should be dropped now.
            assert_eq!(*value.read().unwrap(), NoCopy(2));
        }
        // The data shouldn't be dropped again.
        assert_eq!(*value.read().unwrap(), NoCopy(2));
    }

    #[test]
    fn segment_data_integers() {
        test_segment_data(1u8, 2, 0);
        test_segment_data(3u16, 4, 0);
        test_segment_data(5u32, 6, 0);
        test_segment_data(7u64, 8, 0);
        test_segment_data(-1i8, 2, 0);
        test_segment_data(-3i16, 4, 0);
        test_segment_data(-5i32, 6, 0);
        test_segment_data(-7i64, 8, 0);
    }

    #[test]
    fn segment_data_strings() {
        test_segment_data("value 1", "value 2", "err value");
        test_segment_data("value 1".to_owned(), "value 2".to_owned(), "err value".to_owned());
        test_segment_data("value 1".as_bytes(), "value 2".as_bytes(), "err value".as_bytes());
    }

    #[test]
    fn segment_data_vectors() {
        test_segment_data(vec![1u8, 2, 3], vec![4, 5, 6], vec![7, 8, 9]);
        test_segment_data(vec![10u16, 12, 13], vec![14, 15, 16], vec![17, 18, 19]);
        test_segment_data(vec![20u32, 22, 23], vec![24, 25, 26], vec![27, 28, 29]);
        test_segment_data(vec![30u64, 32, 33], vec![34, 35, 36], vec![37, 38, 39]);
        test_segment_data(vec![-1i8, 2, 3], vec![4, 5, 6], vec![7, 8, 9]);
        test_segment_data(vec![-10i16, 12, 13], vec![14, 15, 16], vec![17, 18, 19]);
        test_segment_data(vec![-20i32, 22, 23], vec![24, 25, 26], vec![27, 28, 29]);
        test_segment_data(vec![-30i64, 32, 33], vec![34, 35, 36], vec![37, 38, 39]);

        test_segment_data(vec!["1", "2", "3"],
            vec!["4", "5", "6"],
            vec!["7", "8", "9"]);
        test_segment_data(vec!["1".to_owned(), "2".to_owned(), "3".to_owned()],
            vec!["4".to_owned(), "5".to_owned(), "6".to_owned()],
            vec!["7".to_owned(), "8".to_owned(), "9".to_owned()]);
        test_segment_data(vec!["1".as_bytes(), "2".as_bytes(), "3".as_bytes()],
            vec!["4".as_bytes(), "5".as_bytes(), "6".as_bytes()],
            vec!["7".as_bytes(), "8".as_bytes(), "9".as_bytes()]);

        test_segment_data(vec![NoCopy(1), NoCopy(2), NoCopy(2)],
            vec![NoCopy(4), NoCopy(5), NoCopy(6)],
            vec![NoCopy(7), NoCopy(8), NoCopy(9)]);
    }

    #[test]
    fn segment_data_not_copyable() {
        test_segment_data(NoCopy(100), NoCopy(200), NoCopy(0));
    }

    /// Required: `value1` > `value2` and `value2` > `value1`.
    fn test_segment_data<T>(value1: T, value2: T, err_value: T)
        where T: Send + Sync + Clone + PartialEq + PartialOrd + fmt::Debug
    {
        const MAX_TRIES: usize = 5;

        let data = SegmentData::empty();
        assert!(data.is_empty());
        assert!(!data.is_ready());
        assert!(data.try_pop().is_none());

        // Write some data.
        assert!(data.try_write(value1.clone()).is_ok());
        assert!(!data.is_empty());
        assert!(data.is_ready());

        // Shouldn't be able to write again.
        assert!(data.write(err_value.clone(), MAX_TRIES).is_err());

        // Read (pop) the data.
        let got1 = data.try_pop();
        assert_eq!(got1, Some(value1.clone()));
        assert!(data.is_empty());
        assert!(!data.is_ready());
        assert!(data.pop(MAX_TRIES).is_none());
        assert!(data.is_empty());
        assert!(!data.is_ready());

        // Test reuseage:

        // Write and read some data again.
        assert!(data.write(value2.clone(), MAX_TRIES).is_ok());
        assert!(!data.is_empty());
        assert!(data.is_ready());

        // Predicate is not true.
        assert!(data.conditional_try_pop(|value2| *value2 < value1).is_none());
        // Predicate is true.
        let got2 = data.conditional_try_pop(|value2| *value2 > value1);
        assert_eq!(got2, Some(value2.clone()));
        assert!(data.is_empty());
        assert!(!data.is_ready());
        assert!(data.pop(MAX_TRIES).is_none());
        assert!(data.is_empty());
        assert!(!data.is_ready());

        // Test the orignal value again, make sure it's not overwritten.
        assert_eq!(got1, Some(value1.clone()));
        assert_eq!(got2, Some(value2));
        assert_ne!(got1, got2);
    }
}
