use std::fmt;
use std::sync::atomic::{AtomicPtr, AtomicIsize, Ordering};

use super::segment::Segment;

pub struct Queue<T> {
    // TODO: doc that both `head` and `tail` must always point to a valid
    // segment.
    //
    // Doc that the may not point to the correct head/tail and that `Segment`
    // will take that into account.
    //
    // Both must be from Box::into_raw
    head: AtomicPtr<Segment<T>>,
    tail: AtomicPtr<Segment<T>>,

    // The head and tail pos are not in sync in any way.
    head_pos: AtomicIsize,
    tail_pos: AtomicIsize,
}

impl<T> Queue<T> {
    pub fn new() -> Queue<T> {
        let segment = Segment::empty();
        let head_ptr = unsafe { Segment::expand_front(&segment).unwrap() };

        let queue = Queue {
            head: AtomicPtr::new(head_ptr),
            tail: AtomicPtr::new(Box::into_raw(segment)),
            head_pos: AtomicIsize::new(0),
            tail_pos: AtomicIsize::new(0),
        };
        queue
    }

    pub fn push_front(&self, data: T) {
        self.head().push_front(&self.head_pos, data)
            .unwrap_or_else(|data| {
                self.expand_front();
                self.push_front(data)
            });
    }

    pub fn push_back(&self, data: T) {
        self.tail().push_back(&self.tail_pos, data)
            .unwrap_or_else(|data| {
                self.expand_back();
                self.push_back(data)
            });
    }

    pub fn pop_front(&self) -> Option<T> {
        self.head().pop_front(&self.head_pos)
    }

    pub fn pop_back(&self) -> Option<T> {
        self.tail().pop_back(&self.tail_pos)
    }

    pub fn conditional_pop_front<P>(&self, predicate: P) -> Option<T>
        where P: Fn(&T) -> bool
    {
        self.head().conditional_pop_front(&self.head_pos, predicate)
    }

    pub fn conditional_pop_back<P>(&self, predicate: P) -> Option<T>
        where P: Fn(&T) -> bool
    {
        self.tail().conditional_pop_back(&self.tail_pos, predicate)
    }

    fn expand_front(&self) {
        // Expand the segment to the front and then store the new pointer as the
        // new head. We can use releaxed ordering here since `Segment` will take
        // into account that `self.head` might not point to the correct head. If
        // the function returns `None` .
        //
        // FIXME: this function must be called with a reference to the heap,
        // make sure that this is always the case.
        //
        // FIXME: if self.head points to an old head (head - 1), but the actual
        // head is full and we try to extend it expand_front will return None,
        // and we won't be able to expand the segment ever again.
        if let Some(new_head_ptr) = unsafe { Segment::expand_front(self.head()) } {
            self.head.store(new_head_ptr, Ordering::Relaxed);
        }
    }

    fn expand_back(&self) {
        // See `expand_front` for docs.
        if let Some(new_tail_ptr) = unsafe { Segment::expand_back(self.tail()) } {
            self.tail.store(new_tail_ptr, Ordering::Relaxed);
        }
    }

    #[inline(always)]
    fn head(&self) -> &Segment<T> {
        // Safe because the head must always point to a valid segment, but it
        // doesn't always have to point to the actual head; it may point to head
        // - 1.
        unsafe { &*self.head.load(Ordering::Relaxed) }
    }

    #[inline(always)]
    fn tail(&self) -> &Segment<T> {
        // For docs see `head`.
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
