use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr;
use std::mem;

#[cfg(test)]
mod tests;

struct Node<T> {
    /// May be null, but may not point to invalid data.
    next: AtomicPtr<Node<T>>,
    value: T,
}

impl<T> Node<T> {
    /// Create a new node with the provided value.
    pub fn new(value: T) -> Node<T> {
        Node {
            next: AtomicPtr::new(ptr::null_mut()),
            value: value,
        }
    }
}

pub struct AtomicVecDeque<T> {
    /// May be null, but may not point to invalid data.
    head: AtomicPtr<Node<T>>,
}

/// The maximum number of tries before an operation gives up.
const MAX_TRIES: usize = 20;

// TODO: try to relax the ordering, on a per call basis.
const DEFAULT_ORDERING: Ordering = Ordering::SeqCst;

impl<T> AtomicVecDeque<T> {
    /// Create a new waiting queue.
    pub fn new() -> AtomicVecDeque<T> {
        AtomicVecDeque {
            head: AtomicPtr::new(ptr::null_mut()),
        }
    }

    /// Add an item to the front.
    pub fn push_front(&self, value: T) {
        // We create a new node a give it a place on the heap.
        let mut new_head = Box::new(Node::new(value));
        // Next we swap the `new_head` with the current head.
        let old_head_ptr = self.head.swap(&mut *new_head, DEFAULT_ORDERING);
        // Now we add the old head as next to the `new_head`.
        new_head.next.swap(old_head_ptr, DEFAULT_ORDERING);

        // Now we need to forget about the boxed `new_head`. This is required
        // because otherwise Rust would deallocate the `new_head` right here,
        // and when we later want to retrieve it (by using a pop operation) the
        // memory point will be invalid. Next bad things will happend.
        //
        // So we forget about the `new_head` node here but leave it in memory.
        // Next a pop operation will read memory again and return it's value.
        // And after the user is done with the memory is done with it the
        // destructor will run, as normal.
        mem::forget(new_head);
    }

    /// Remove an item from the front.
    pub fn pop_front(&self) -> Option<T> {
        for _ in 0..MAX_TRIES {
            // First load the current head.
            let head_ptr = self.head.load(DEFAULT_ORDERING);
            let head = unsafe {
                // This is safe because the contract is that the pointer always
                // points to valid memory.
                head_ptr.as_ref()
            };
            if let Some(head) = head {
                // Then get the pointer for the new head (head.next).
                let new_head = head.next.load(DEFAULT_ORDERING);
                // Try to exchange the new head pointer for the "old head", making
                // sure the current head pointer is still the same as we expected.
                let result = self.head.compare_exchange(head_ptr, new_head,
                    DEFAULT_ORDERING, DEFAULT_ORDERING);
                if let Ok(old_head_ptr) = result {
                    let node = unsafe { ptr::read(old_head_ptr) };
                    return Some(node.value);
                } else {
                    // The old head was changed, we need to try again.
                    continue
                }
            } else {
                // If the current head is a null pointer we're done.
                return None;
            }
        }

        // Tried too many times, so we're giving up.
        None
    }
}

impl<T> Drop for AtomicVecDeque<T> {
    fn drop(&mut self) {
        // TODO: implement an iteration and use that instead.
        loop {
            // Retrieve every value from the deque to running it's Drop method.
            // See the `push_front` code.
            if self.pop_front().is_none() {
                break
            }
        }
    }
}
