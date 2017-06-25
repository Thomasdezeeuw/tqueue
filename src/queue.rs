use std::default::Default;
use std::fmt;
use std::sync::atomic::{AtomicPtr, AtomicIsize, Ordering};

use super::segment::Segment;

/// A queue to which you can push data, either in the
/// [`front`](#method.push_front) or at the [`back`](#method.push_back). And of
/// which you can pop data, again either in the [`front`](#method.try_pop_front)
/// or at the [`back`](#method.try_pop_back).
///
/// The queue is safe for concurrent use as all methods only require a
/// reference.
pub struct Queue<T> {
    /// Atomic pointers that point to the `head` and `tail` `Segment`s. Neither
    /// of them may be null or point to invalid memory. However they may point
    /// to an "incorrect" head or tail, e.g. it can point to a head which has
    /// another peer which is the actual head, `Segment` deals with this.
    ///
    /// `Queue` is responible for dropping all `Segment`s, inlcuding all peers.
    /// See the `Drop` implementation for more.
    head: AtomicPtr<Segment<T>>,
    tail: AtomicPtr<Segment<T>>,

    /// The head and tail positions that are used by `Segment`, neither may be
    /// modified outside of `Segment` calls. These are not in sync with each
    /// other in any way.
    head_pos: AtomicIsize,
    tail_pos: AtomicIsize,
}

impl<T> Queue<T> {
    /// Create a new, empty queue.
    pub fn new() -> Queue<T> {
        let segment = Segment::empty();
        let head_ptr = unsafe { Segment::expand_front(&segment).unwrap() };

        Queue {
            head: AtomicPtr::new(head_ptr),
            tail: AtomicPtr::new(Box::into_raw(segment)),
            head_pos: AtomicIsize::new(0),
            tail_pos: AtomicIsize::new(0),
        }
    }

    /// Push `data` to the front of the queue.
    pub fn push_front(&self, data: T) {
        self.head().try_push_front(&self.head_pos, data)
            .unwrap_or_else(|data| {
                // FIXME: expanding is not always needed.
                self.expand_front();
                self.push_front(data)
            });
    }

    /// Push `data` to the end of the queue.
    pub fn push_back(&self, data: T) {
        self.tail().try_push_back(&self.tail_pos, data)
            .unwrap_or_else(|data| {
                // FIXME: expanding is not always needed.
                self.expand_back();
                self.push_back(data)
            });
    }

    /// Try poping data from the front of the queue, if the queue is (currently)
    /// empty it will return `None`.
    pub fn try_pop_front(&self) -> Option<T> {
        self.head().try_pop_front(&self.head_pos)
    }

    /// Try poping data from the back of the queue, if the queue is (currently)
    /// empty it will return `None`.
    pub fn try_pop_back(&self) -> Option<T> {
        self.tail().try_pop_back(&self.tail_pos)
    }

    /// Try poping data from the front of the queue, but only return it if the
    /// `predicate` returns true. If the queue is (currently) empty, or if the
    /// `predicate` returns false, it will return `None`.
    pub fn conditional_try_pop_front<P>(&self, predicate: P) -> Option<T>
        where P: FnOnce(&T) -> bool
    {
        self.head().conditional_try_pop_front(&self.head_pos, predicate)
    }

    /// Try poping data from the back of the queue, but only return it if the
    /// `predicate` returns true. If the queue is (currently) empty, or if the
    /// `predicate` returns false, it will return `None`.
    pub fn conditional_try_pop_back<P>(&self, predicate: P) -> Option<T>
        where P: FnOnce(&T) -> bool
    {
        self.tail().conditional_try_pop_back(&self.tail_pos, predicate)
    }

    /// Expand the queue with a new `Segment` at the front.
    fn expand_front(&self) {
        // Expand the segment to the front and then store the new pointer as the
        // new head. We can use releaxed ordering here since `Segment` will take
        // into account that `self.head` might not point to the correct head.
        //
        // FIXME: Segment::expand_front must be called with a reference to the
        // heap, make sure that this is always the case.
        //
        // FIXME: if self.head points to an old head (head - 1), but the actual
        // head is full and we try to extend it wth Segment::expand_front, it
        // will return None, and we won't be able to expand the segment ever
        // again.
        if let Some(new_head_ptr) = unsafe { Segment::expand_front(self.head()) } {
            self.head.store(new_head_ptr, Ordering::Relaxed);
        }
    }

    /// See `expand_front` for docs.
    fn expand_back(&self) {
        if let Some(new_tail_ptr) = unsafe { Segment::expand_back(self.tail()) } {
            self.tail.store(new_tail_ptr, Ordering::Relaxed);
        }
    }

    /// Get a reference to the current `head`, note that it may not be the
    /// actual head, but `Segment` will deal with that.
    #[inline(always)]
    fn head(&self) -> &Segment<T> {
        // Safe because the head must always point to a valid segment.
        unsafe { &*self.head.load(Ordering::Relaxed) }
    }

    /// See `head` for docs.
    #[inline(always)]
    fn tail(&self) -> &Segment<T> {
        unsafe { &*self.tail.load(Ordering::Relaxed) }
    }
}

impl<T> Drop for Queue<T> {
    fn drop(&mut self) {
        // Load the head `Segment`, turning it into a `Box`. Next get it's peers,
        // dropping the `Segment` in the process.
        let segment_head = unsafe { Box::from_raw(self.head.load(Ordering::Relaxed)) };
        let (mut head_prev, mut head_next) = segment_head.get_peers();

        // To make sure we don't have an outdated header pointer, we first
        // deallocate any previous `Segment`s, before the `segment_head`.
        loop {
            if head_prev.is_null() {
                break;
            }

            // Turn the raw pointer into a boxed segment, get it's peers and
            // then drop the contents at the end of the loop.
            let segment_prev = unsafe { Box::from_raw(head_prev) };
            let (next_head_prev, _) = segment_prev.get_peers();
            head_prev = next_head_prev;
        }

        // Next follow the `next` pointers on the `Segment`s.
        loop {
            if head_next.is_null() {
                break;
            }

            // Turn the raw pointer into a boxed segment, get it's peers and
            // then drop the contents at the end of the loop.
            let segment_next = unsafe { Box::from_raw(head_next) };
            let (_, next_head_next) = segment_next.get_peers();
            head_next = next_head_next;
        }
    }
}

impl<T> fmt::Debug for Queue<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.pad("Queue{{ ... }}")
    }
}

impl<T> Default for Queue<T> {
    /// Create an empty `Queue`, this does the same thing as [`Queue::new`].
    ///
    /// [`Queue::new`]: struct.Queue.html#method.new
    fn default() -> Queue<T> {
        Queue::new()
    }
}

#[cfg(test)]
mod tests {
    use std::mem;

    use super::*;

    fn assert_send<T: Send>() {}
    fn assert_sync<T: Sync>() {}
    fn assert_debug<T: fmt::Debug>() {}
    fn assert_size<T>(want: usize) {
        assert_eq!(mem::size_of::<T>(), want);
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
