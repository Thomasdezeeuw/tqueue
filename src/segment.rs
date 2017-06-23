use std::cell::UnsafeCell;
use std::default::Default;
use std::sync::atomic::{AtomicPtr, AtomicIsize, Ordering};
use std::{fmt, mem, ptr};

use super::state::AtomicState;

// TODO: try to relax the ordering, on a per call basis.
const DEFAULT_ORDERING: Ordering = Ordering::SeqCst;

/// The size of a single [`Segment`]. 32 is chosen somewhat arbitrarily.
///
/// [`Segment`]: struct.Segment.html
//
// TODO: benchmark smaller and bigger sizes.
const SEGMENT_SIZE: usize = 32;

/// The id of a [`Segment`].
///
/// [`Segment`]: struct.Segment.html
type SegmentId = isize;

/// The position of a `Item` in the data array in `Segment`.
///
/// [`Item`]: struct.Item.html
type Pos = isize;

// Does not drop it the pointers to next and previous segments.
//
// TODO: make pub(crate), unstable feature.
pub struct Segment<T> {
    /// The `SegmentId` of the `Segment` used in determining to which `Segment`
    /// data must be written or read from.
    id: SegmentId,

    /// The data this segment is responible for. Due to the nature of the global
    /// position (see `push_front` and `push_back`) it is very possible that
    /// this will contain holes.
    ///
    // TODO: doc data fragmentation more.
    data: [Item<T>; SEGMENT_SIZE],

    /// The pointers to the next and previous `Segment`s.
    ///
    /// For the initial Segment these pointers wil be null, but after it set
    /// once it must always point to a correct `Segment` and **must never be
    /// null again**!
    prev: AtomicPtr<Segment<T>>,
    next: AtomicPtr<Segment<T>>,
}

impl<T> Segment<T> {
    /// Create new empty `Segment`, it is already boxed because this is required
    /// for the `expand` functions.
    pub fn empty() -> Box<Segment<T>> {
        Box::new(Segment {
            id: 0,
            // Creates an array of empty `Item`.
            data: Default::default(),
            prev: AtomicPtr::new(ptr::null_mut()),
            next: AtomicPtr::new(ptr::null_mut()),
        })
    }

    /// Push `data` to the front of the `Segment`.
    pub fn try_push_front(&self, head_pos: &AtomicIsize, data: T) -> Result<(), T> {
        // Grab a new position for ourself and try to write to it.
        //
        // Note we don't have exclusive access to it so we're still racing for
        // it, hence the fact that `Item` has it's own access control.
        let pos = head_pos.fetch_sub(1, DEFAULT_ORDERING);
        self.try_write_position(pos, data)
            .map_err(|data| {
                // Failed to write, release the position.
                head_pos.fetch_add(1, DEFAULT_ORDERING);
                // FIXME: it could also be that a `Item` is (currently)
                // in a invalid state, what then?
                data
            })
    }

    /// Push `data` to the back of the `Segment`.
    pub fn try_push_back(&self, tail_pos: &AtomicIsize, data: T) -> Result<(), T> {
        // See `push_front` for documentation, this does the same thing but with
        // a different position and returned error.
        let pos = tail_pos.fetch_add(1, DEFAULT_ORDERING);
        self.try_write_position(pos, data)
            .map_err(|data| {
                tail_pos.fetch_sub(1, DEFAULT_ORDERING);
                data
            })
    }

    /// Write the provided `data` to the provided position.
    ///
    /// # Note
    ///
    /// It possible that the position is not present on the current segment, if
    /// that is the case this function will deligate the writing to the correct
    /// segment, if present.
    ///
    /// If the segment to which the position belongs doesn't exitsts this will
    /// return an error.
    fn try_write_position(&self, pos: Pos, data: T) -> Result<(), T> {
        // Get the `SegmentId` based on the `Pos`ition in which this data must
        // be written.
        //
        // TODO: call get_segment_id only once per write.
        let segment_id = get_segment_id(pos);
        if segment_id == self.id {
            // If its this segment we can get the index and write to it.
            let index = pos_to_index(pos);
            self.data[index].try_write(data)
        } else if segment_id < self.id {
            // Otherwise we need to pass the write on to the `prev`ious or
            // `next` segment.
            try_write_position(&self.prev, pos, data)
        } else {
            try_write_position(&self.next, pos, data)
        }
    }

    /// Try to remove data from the front of the `Segment`.
    ///
    /// # Note
    ///
    /// This function will deligate to peer `Segement`s if the position is not
    /// in this `Segment`.
    pub fn try_pop_front(&self, head_pos: &AtomicIsize) -> Option<T> {
        // Grab a new position for ourself and try to read from it.
        //
        // Note we don't have exclusive access to it so we're still racing for
        // it, hence the fact that `Item` has it's own access control.
        let pos = head_pos.fetch_add(1, DEFAULT_ORDERING);
        self.try_pop_position(pos)
            .or_else(|| {
                // Failed to read, release the position.
                head_pos.fetch_sub(1, DEFAULT_ORDERING);
                // FIXME: it could also be that a `Item` is (currently)
                // in a invalid state, what then?
                None
            })
    }

    /// Try to remove data from the back of the `Segment`.
    ///
    /// # Note
    ///
    /// This function will deligate to peer `Segement`s if the position is not
    /// in this `Segment`.
    pub fn try_pop_back(&self, tail_pos: &AtomicIsize) -> Option<T> {
        // See `pop_front` for documentation, this does the same thing but with
        // a different position.
        let pos = tail_pos.fetch_sub(1, DEFAULT_ORDERING);
        self.try_pop_position(pos)
            .or_else(|| {
                tail_pos.fetch_add(1, DEFAULT_ORDERING);
                None
            })
    }

    /// Pop the `data` in the provided position.
    ///
    /// # Note
    ///
    /// It possible that the position is not present on the current segment, if
    /// that is the case this function will deligate the writing to the correct
    /// segment, if present.
    ///
    /// If the segment to which the position belongs doesn't exitsts this will
    /// return `None`.
    fn try_pop_position(&self, pos: Pos) -> Option<T> {
        // Get the `SegmentId` based on the `Pos`ition in which this data must
        // be written.
        //
        // TODO: call get_segment_id only once per read.
        let segment_id = get_segment_id(pos);
        if segment_id == self.id {
            // If its this segment we can get the index and write to it.
            let index = pos_to_index(pos);
            self.data[index].try_pop()
        } else if segment_id < self.id {
            // Otherwise we need to pass the read on to the `prev`ious or
            // `next` segment.
            try_pop_position(&self.prev, pos)
        } else {
            try_pop_position(&self.next, pos)
        }
    }

    pub fn conditional_try_pop_front<P>(&self, head_pos: &AtomicIsize, predicate: P) -> Option<T>
        where P: FnOnce(&T) -> bool
    {
        // Grab a new position for ourself and try to read from it.
        //
        // Note we don't have exclusive access to it so we're still racing for
        // it, hence the fact that `Item` has it's own access control.
        let pos = head_pos.fetch_add(1, DEFAULT_ORDERING);
        self.conditional_try_pop_position(pos, predicate)
            .or_else(|| {
                // Failed to read, release the position.
                head_pos.fetch_sub(1, DEFAULT_ORDERING);
                // FIXME: it could also be that a `Item` is (currently)
                // in a invalid state, what then?
                None
            })
    }

    pub fn conditional_try_pop_back<P>(&self, tail_pos: &AtomicIsize, predicate: P) -> Option<T>
        where P: FnOnce(&T) -> bool
    {
        // See `conditional_pop_front` for documentation, this does the same thing but with
        // a different position.
        let pos = tail_pos.fetch_sub(1, DEFAULT_ORDERING);
        self.conditional_try_pop_position(pos, predicate)
            .or_else(|| {
                tail_pos.fetch_add(1, DEFAULT_ORDERING);
                None
            })
    }

    /// Pop the `data` in the provided position, if the `predicate` is met.
    ///
    /// # Note
    ///
    /// It possible that the position is not present on the current segment, if
    /// that is the case this function will deligate the writing to the correct
    /// segment, if present.
    ///
    /// If the segment to which the position belongs doesn't exitsts this will
    /// return `None`.
    fn conditional_try_pop_position<P>(&self, pos: Pos, predicate: P) -> Option<T>
        where P: FnOnce(&T) -> bool
    {
        // Get the `SegmentId` based on the `Pos`ition in which this data must
        // be written.
        //
        // TODO: call get_segment_id only once per read.
        let segment_id = get_segment_id(pos);
        if segment_id == self.id {
            // If its this segment we can get the index and write to it.
            let index = pos_to_index(pos);
            self.data[index].conditional_try_pop(predicate)
        } else if segment_id < self.id {
            // Otherwise we need to pass the read on to the `prev`ious or
            // `next` segment.
            conditional_try_pop_position(&self.prev, pos, predicate)
        } else {
            conditional_try_pop_position(&self.next, pos, predicate)
        }
    }

    // Returns the pointer to the new tail segment.
    // Needs to be called on a box.
    //
    // Returns Some if a new segment was added, else None if it already had an
    // segment.
    //
    // return pointer will always be from Box::into_raw()
    //
    // MUST BE CALLED FROM BOX!!
    //
    // TODO: doc.
    pub unsafe fn expand_front(&self) -> Option<*mut Segment<T>> {
        if self.prev.load(DEFAULT_ORDERING).is_null() {
            let ptr = Segment::expand_front_with_segment(&self, Segment::empty());
            Some(ptr)
        } else {
            None
        }
    }

    /// Expand the current segment with the provided segment.
    ///
    /// # Note
    ///
    /// When this function returns it will always have a segment in `self.prev`,
    /// however it may be a different segment then the one provided.
    ///
    /// **This function must be called on a box**.
    unsafe fn expand_front_with_segment(&self, mut new_segment: Box<Segment<T>>) -> *mut Segment<T> {
        // For an `AtomicPtr` we need `*mut Segment<T>`, or a mutable raw
        // pointer to a `Segment`. But since we don't even use a mutable
        // reference (`&mut`) for any method, we can make do with a raw pointer
        // (`*const`). So we cast a raw pointer into a raw mutable pointer and
        // pass that to `AtomicPtr`.
        //
        // With the raw mutable pointer we set the correct `next` pointer on the
        // `new_segment` and set the correct id.
        let self_ptr: *const Segment<T> = &*self;
        new_segment.next = AtomicPtr::new(self_ptr as *mut Segment<T>);
        new_segment.id = self.id - 1;

        // Make sure the current `prev` ptr is null and we don't overwrite any
        // segments.
        let result = self.prev.compare_exchange(ptr::null_mut(), &mut *new_segment,
            DEFAULT_ORDERING, Ordering::Relaxed);
        if let Err(prev_ptr) = result {
            // So unfortunately a new segment was already allocated and added to
            // the current one.
            //
            // Now we have two choices:
            // 1) do nothing, the current segment has a segment after all, or
            // 2) add the new segment to the next segment, so we don't waste the
            //    allocation.
            //
            // We'll go with option two.

            // We already made sure the pointer is valid, so this is safe to
            // convert in to a `&Segment`.
            // It is to call `expand_front_with_segment` with the `prev_ptr`
            // because it is already on the heap.
            Segment::expand_front_with_segment(&*prev_ptr, new_segment)
        } else {
            // All is ok and we added the segment to the current segment.
            //
            // Now we need to forget about `new_segment` and return a raw
            // pointer to it.
            Box::into_raw(new_segment)
        }
    }

    /// See `expand_front` for docs. This does the same thing but adding a new
    /// `Segment` to the back.
    pub unsafe fn expand_back(&self) -> Option<*mut Segment<T>> {
        if self.next.load(DEFAULT_ORDERING).is_null() {
            let ptr = Segment::expand_back_with_segment(&self, Segment::empty());
            Some(ptr)
        } else {
            None
        }
    }

    /// See `expand_front_with_segment`.
    unsafe fn expand_back_with_segment(&self, mut new_segment: Box<Segment<T>>) -> *mut Segment<T> {
        // See `expand_front_with_segment` for docs.
        let self_ptr: *const Segment<T> = &*self;
        new_segment.prev = AtomicPtr::new(self_ptr as *mut Segment<T>);
        new_segment.id = self.id + 1;

        let result = self.next.compare_exchange(ptr::null_mut(), &mut *new_segment,
            DEFAULT_ORDERING, Ordering::Relaxed);
        if let Err(next_ptr) = result {
            Segment::expand_back_with_segment(&*next_ptr, new_segment)
        } else {
            Box::into_raw(new_segment)
        }
    }

    /// Get the peer `Segment`s from this `Segment`. If these are not null they
    /// will always point to other valid `Segment`s.
    ///
    /// # Note
    ///
    /// Once this method is called **all** peers of the `Segment` will become
    /// invalid and any method called on them, with the expection of this one,
    /// can result in a segfault.
    ///
    /// This method may only be called when dropping it, hence the fact that it
    /// moves and drops itself.
    pub fn get_peers(self) -> (*mut Segment<T>, *mut Segment<T>) {
        let prev = self.prev.load(Ordering::Relaxed);
        let next = self.next.load(Ordering::Relaxed);
        (prev, next)
    }
}

// TODO: benchmark inlining (using the attribute) of these functions:

/// Determine the `SegmentId` based on the `Pos`ition.
fn get_segment_id(pos: Pos) -> SegmentId {
    if pos == 0 {
        0
    } else if pos.is_negative() {
        // Slot 0 starts at 0, so Slot -1 starts at -SEGMENT_SIZE.
        -((pos / SEGMENT_SIZE as isize) - 1)
    } else {
        pos / SEGMENT_SIZE as isize
    }
}

/// Converts a `Pos`ition into an index for the data array.
fn pos_to_index(pos: Pos) -> usize {
    let index = pos % SEGMENT_SIZE as isize;
    if index.is_negative() {
        -index as usize
    } else {
        index as usize
    }
}

/// Call `segment.write_position` if the pointer points to a valid `Segment`,
/// else returns an error.
///
/// # Note
///
/// The provided pointer must follow the contract defined in the `Segment.{next,
/// prev}` fields.
fn try_write_position<T>(ptr: &AtomicPtr<Segment<T>>, pos: Pos, data: T) -> Result<(), T> {
    let segment = unsafe {
        // This is safe because the `previous` and `next` pointers must always
        // point to a valid segment, if not null.
        ptr.load(DEFAULT_ORDERING).as_ref()
            .map(|segment_ptr| &*segment_ptr)
    };

    if let Some(segment) = segment {
        // the next or previous segment exists and we'll let it deal with the
        // write.
        segment.try_write_position(pos, data)
    } else {
        // A next or previous segment doesn't exists, so we return an error.
        Err(data)
    }
}

/// Call `segment.pop_position` if the pointer points to a valid `Segment`, else
/// returns `None`.
///
/// # Note
///
/// The provided pointer must follow the contract defined in the `Segment.{next,
/// prev}` fields.
fn try_pop_position<T>(ptr: &AtomicPtr<Segment<T>>, pos: Pos) -> Option<T> {
    let segment = unsafe {
        // This is safe because the `previous` and `next` pointers must always
        // point to a valid segment, if not null.
        ptr.load(DEFAULT_ORDERING).as_ref()
            .map(|segment_ptr| &*segment_ptr)
    };

    if let Some(segment) = segment {
        // the next or previous segment exists and we'll let it deal with the
        // write.
        segment.try_pop_position(pos)
    } else {
        // A next or previous segment doesn't exists.
        None
    }
}

/// Call `segment.conditional_pop_position` if the pointer points to a valid
/// `Segment`, else returns `None`.
///
/// # Note
///
/// The provided pointer must follow the contract defined in the `Segment.{next,
/// prev}` fields.
fn conditional_try_pop_position<P, T>(ptr: &AtomicPtr<Segment<T>>, pos: Pos, predicate: P) -> Option<T>
    where P: FnOnce(&T) -> bool
{
    let segment = unsafe {
        // This is safe because the `previous` and `next` pointers must always
        // point to a valid segment, if not null.
        ptr.load(DEFAULT_ORDERING).as_ref()
            .map(|segment_ptr| &*segment_ptr)
    };

    if let Some(segment) = segment {
        // the next or previous segment exists and we'll let it deal with the
        // write.
        segment.conditional_try_pop_position(pos, predicate)
    } else {
        // A next or previous segment doesn't exists.
        None
    }
}

impl<T> fmt::Debug for Segment<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.pad("Segment{{ ... }}")
    }
}

/// `Item` is a piece of data that can be written to once and then read
/// once, and can then be reused. It is not possible to overwrite the data or
/// read the data twice.
///
/// It is made for, and therefore safe for, concurrent use if `T` is [`Send`]
/// and [`Sync`].
///
/// [`Send`]: https://doc.rust-lang.org/nightly/core/marker/trait.Send.html
/// [`Sync`]: https://doc.rust-lang.org/nightly/core/marker/trait.Sync.html
struct Item<T> {
    /// The state of the data.
    state: AtomicState,

    /// The actual data, protected by the state.
    ///
    /// If the `state` is `Empty` this must be `None`. However if the `state` is
    /// `Ready` this must be `Some`.
    data: UnsafeCell<Option<T>>,
}

impl<T> Item<T> {
    /// Create a new empty `Item`.
    pub fn empty() -> Item<T> {
        Item {
            state: AtomicState::empty(),
            data: UnsafeCell::new(None),
        }
    }

    /// Check if the `Item` is empty.
    #[cfg(test)]
    fn is_empty(&self) -> bool {
        self.state.is_empty()
    }

    /// Check if the `Item` is ready for reading.
    #[cfg(test)]
    fn is_ready(&self) -> bool {
        self.state.is_ready()
    }

    /// Try to write data to this `Item`. If the state of this
    /// `Item` is not [`Empty`], this includes when the data is being
    /// read from or written to, the data can't be written. If this is the case
    /// this function will return an error, which includes the data so it can be
    /// used in trying the write operation again.
    ///
    /// [`Empty`]: ../state/enum.State.html#variant.Empty
    pub fn try_write(&self, data: T) -> Result<(), T> {
        // Set the state to writing, if this returns false it means we can't
        // currently write the data and we'll return an error.
        if self.state.set_writing() {
            // This is safe because of the contract described in the `data`
            // field.
            mem::swap(unsafe { &mut *self.data.get() } , &mut Some(data));

            // Update the `state` to indicate the data is `Ready`.
            // TODO: what to do with this check.
            assert!(self.state.set_ready());
            Ok(())
        } else {
            Err(data)
        }
    }

    /// Try to read the data from this `Item` and remove it, after which
    /// it will be empty. If the state is not [`Ready`], this includes when the
    /// data is being read from or written to, the data can't be read. If
    /// this is the case this function will return `None`.
    ///
    /// [`Ready`]: ../state/enum.State.html#variant.Ready
    pub fn try_pop(&self) -> Option<T> {
        // Set the state to reading, if this returns false it means we currently
        // can't read the data and we'll return `None`.
        if self.state.set_reading() {
            unsafe { self.take_data() }
        } else {
            None
        }
    }

    /// Take the data without checking if the state is [`Ready`] and setting it
    /// to [`Reading`], **this is the callers responsibility**. This is also the
    /// reason why this function is unsafe.
    ///
    /// The state will be updated to [`Empty`] after taking the data.
    ///
    /// # Safety
    ///
    /// The state must be set to [`Reading`] before calling this function, this
    /// is the reason this function is unsafe.
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

    /// This is the same as [`try_pop`], however makes sure the returned data
    /// fulfills the provided `predicate`. See [`try_pop`] for more.
    ///
    /// # Note
    ///
    /// The `predicate` function is called while blocking all other operations
    /// on this `Item`, thus is it advised to make sure the `predicate` function
    /// doesn't take too long.
    ///
    /// [`try_pop`]: struct.Item.html#method.try_pop
    pub fn conditional_try_pop<P>(&self, predicate: P) -> Option<T>
        where P: FnOnce(&T) -> bool
    {
        // Set the state to reading, if this returns false it means we currently
        // can't read the data and we'll return `None`.
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

impl<T> fmt::Debug for Item<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.pad("Item{{ ... }}")
    }
}

impl<T> Default for Item<T> {
    /// Create an empty `Item`, this does the same thing as
    /// `Item::empty`.
    ///
    /// # Note
    ///
    /// It does not use `T`'s default value as starting value.
    fn default() -> Item<T> {
        Item::empty()
    }
}

unsafe impl<T: Send + Sync> Send for Item<T> {}

unsafe impl<T: Send + Sync> Sync for Item<T> {}

#[cfg(test)]
mod tests {
    use std::sync::{Arc, RwLock};

    use super::*;

    fn assert_send<T: Send>() {}
    fn assert_sync<T: Sync>() {}
    fn assert_debug<T: fmt::Debug>() {}
    fn assert_size<T>(want: usize) {
        assert_eq!(mem::size_of::<T>(), want);
    }

    #[test]
    fn item_assertions() {
        assert_send::<Item<u64>>();
        assert_sync::<Item<u64>>();
        assert_debug::<Item<u64>>();

        // 8 or 4 for the state, 8 bytes for the Option, 8 for u64 (the data).
        #[cfg(target_pointer_width = "64")]
        let want = 8 + 8 + 8;
        #[cfg(target_pointer_width = "32")]
        let want = 4 + 8 + 8;
        assert_size::<Item<u64>>(want);
    }

    #[test]
    fn segment_assertions() {
        assert_send::<Segment<u64>>();
        assert_sync::<Segment<u64>>();
        assert_debug::<Segment<u64>>();

        // 8 or 4 bytes for the id, `SEGMENT_SIZE` * `Item`, 2x pointers.
        #[cfg(target_pointer_width = "64")]
        let want = 8 + (SEGMENT_SIZE * (8 + 8 + 8)) + 8 + 8;
        #[cfg(target_pointer_width = "32")]
        let want = 4 + (SEGMENT_SIZE * (4 + 8 + 8)) + 4 + 4;
        assert_size::<Segment<u64>>(want);
    }

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
    fn item_drop_test() {
        let value = Arc::new(RwLock::new(NoCopy(0)));

        test_drop_empty_item();
        test_drop_filled_item(value.clone());
        test_drop_after_poping_item(value.clone());
        assert_eq!(*value.read().unwrap(), NoCopy(2));
    }

    fn test_drop_filled_item(value: Arc<RwLock<NoCopy>>) {
        {
            let data = Item::empty();
            {
                assert!(data.try_write(DropTest(value.clone())).is_ok());
            }
            // Should not be dropped yet.
            assert_eq!(*value.read().unwrap(), NoCopy(0));
        }
        // The data should be dropped now.
        assert_eq!(*value.read().unwrap(), NoCopy(1));
    }

    fn test_drop_empty_item() {
        // Shouldn't try to drop anything.
        let data: Item<DropTest> = Item::empty();
        // Shouldn't panic.
        mem::drop(data);
    }

    fn test_drop_after_poping_item(value: Arc<RwLock<NoCopy>>) {
        {
            let data = Item::empty();
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
    fn item_integers() {
        test_item(1u8, 2, 0);
        test_item(3u16, 4, 0);
        test_item(5u32, 6, 0);
        test_item(7u64, 8, 0);
        test_item(-1i8, 2, 0);
        test_item(-3i16, 4, 0);
        test_item(-5i32, 6, 0);
        test_item(-7i64, 8, 0);
    }

    #[test]
    fn item_strings() {
        test_item("value 1", "value 2", "err value");
        test_item("value 1".to_owned(), "value 2".to_owned(), "err value".to_owned());
        test_item("value 1".as_bytes(), "value 2".as_bytes(), "err value".as_bytes());
    }

    #[test]
    fn item_vectors() {
        test_item(vec![1u8, 2, 3], vec![4, 5, 6], vec![7, 8, 9]);
        test_item(vec![10u16, 12, 13], vec![14, 15, 16], vec![17, 18, 19]);
        test_item(vec![20u32, 22, 23], vec![24, 25, 26], vec![27, 28, 29]);
        test_item(vec![30u64, 32, 33], vec![34, 35, 36], vec![37, 38, 39]);
        test_item(vec![-1i8, 2, 3], vec![4, 5, 6], vec![7, 8, 9]);
        test_item(vec![-10i16, 12, 13], vec![14, 15, 16], vec![17, 18, 19]);
        test_item(vec![-20i32, 22, 23], vec![24, 25, 26], vec![27, 28, 29]);
        test_item(vec![-30i64, 32, 33], vec![34, 35, 36], vec![37, 38, 39]);

        test_item(vec!["1", "2", "3"],
            vec!["4", "5", "6"],
            vec!["7", "8", "9"]);
        test_item(vec!["1".to_owned(), "2".to_owned(), "3".to_owned()],
            vec!["4".to_owned(), "5".to_owned(), "6".to_owned()],
            vec!["7".to_owned(), "8".to_owned(), "9".to_owned()]);
        test_item(vec!["1".as_bytes(), "2".as_bytes(), "3".as_bytes()],
            vec!["4".as_bytes(), "5".as_bytes(), "6".as_bytes()],
            vec!["7".as_bytes(), "8".as_bytes(), "9".as_bytes()]);

        test_item(vec![NoCopy(1), NoCopy(2), NoCopy(2)],
            vec![NoCopy(4), NoCopy(5), NoCopy(6)],
            vec![NoCopy(7), NoCopy(8), NoCopy(9)]);
    }

    #[test]
    fn item_not_copyable() {
        test_item(NoCopy(100), NoCopy(200), NoCopy(0));
    }

    /// Required: `value1` > `value2` and `value2` > `value1`.
    fn test_item<T>(value1: T, value2: T, err_value: T)
        where T: Send + Sync + Clone + PartialEq + PartialOrd + fmt::Debug
    {
        let data = Item::empty();
        assert!(data.is_empty());
        assert!(!data.is_ready());
        assert!(data.try_pop().is_none());

        // Write some data.
        assert!(data.try_write(value1.clone()).is_ok());
        assert!(!data.is_empty());
        assert!(data.is_ready());

        // Shouldn't be able to write again.
        assert!(data.try_write(err_value.clone()).is_err());

        // Read (pop) the data.
        let got1 = data.try_pop();
        assert_eq!(got1, Some(value1.clone()));
        assert!(data.is_empty());
        assert!(!data.is_ready());
        assert!(data.try_pop().is_none());
        assert!(data.is_empty());
        assert!(!data.is_ready());

        // Test reuseage:

        // Write and read some data again.
        assert!(data.try_write(value2.clone()).is_ok());
        assert!(!data.is_empty());
        assert!(data.is_ready());

        // Predicate is not true.
        assert!(data.conditional_try_pop(|value2| *value2 < value1).is_none());
        // Predicate is true.
        let got2 = data.conditional_try_pop(|value2| *value2 > value1);
        assert_eq!(got2, Some(value2.clone()));
        assert!(data.is_empty());
        assert!(!data.is_ready());
        assert!(data.try_pop().is_none());
        assert!(data.is_empty());
        assert!(!data.is_ready());

        // Test the orignal value again, make sure it's not overwritten.
        assert_eq!(got1, Some(value1.clone()));
        assert_eq!(got2, Some(value2));
        assert_ne!(got1, got2);
    }
}
