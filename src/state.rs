use std::cell::UnsafeCell;
use std::{mem, ptr};
use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

use super::DEFAULT_ORDERING;

/// A state for a segment of data, for an concurrent version see
/// [`AtomicState`].
///
/// [`AtomicState`]: ./struct.AtomicState.html
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum State {
    /// No data has been written.
    Empty,

    /// Data is currently being written.
    Writing,

    /// Data is ready for reading.
    Ready,

    /// Data is currently being read.
    Reading,
}

/// An atomic state for a segment of data. See [`State`] for the possible
/// states.
///
/// A typical lifecycle of the state will be: [`Empty`][] (initial) ->
/// [`Writing`] -> [`Ready`] -> [`Reading`] -> [`Ready`] -> [`Writing`] ->
/// [`Empty`], and can be reused at that point.
///
/// [`State`]: ./enum.State.html
/// [`Empty`]: ./enum.State.html#variant.Empty
/// [`Writing`]: ./enum.State.html#variant.Writing
/// [`Ready`]: ./enum.State.html#variant.Ready
/// [`Reading`]: ./enum.State.html#variant.Reading
pub struct AtomicState {
    state: AtomicUsize,
}

impl AtomicState {
    /// Create a new atomic state, starting in the [`Empty`] state.
    ///
    /// [`Empty`]: ./enum.State.html#variant.Empty
    pub fn empty() -> AtomicState {
        AtomicState {
            state: AtomicUsize::new(State::Empty as usize),
        }
    }

    /// Check if the current state is [`Empty`].
    ///
    /// [`Empty`]: ./enum.State.html#variant.Empty
    pub fn is_empty(&self) -> bool {
        self.is_in_state(State::Empty)
    }

    /// Check if the current state is [`Ready`].
    ///
    /// [`Ready`]: ./enum.State.html#variant.Ready
    pub fn is_ready(&self) -> bool {
        self.is_in_state(State::Ready)
    }

    fn is_in_state(&self, state: State) -> bool {
        self.state.load(DEFAULT_ORDERING) == state as usize
    }

    /// Set the state to [`Writing`], returns true if all is ok. However it
    /// returns false if the state is not set to [`Writing`], which is the case
    /// if the current state is not [`Empty`].
    ///
    /// [`Writing`]: ./enum.State.html#variant.Writing
    /// [`Empty`]: ./enum.State.html#variant.Empty
    pub fn set_writing(&self) -> bool {
        self.swap_state(State::Empty, State::Writing)
    }

    /// Set the state to [`Ready`], returns true if all is ok. However it
    /// returns false if the state is not set to [`Ready`], which is the case
    /// if the current state is not [`Writing`].
    ///
    /// [`Ready`]: ./enum.State.html#variant.Ready
    /// [`Writing`]: ./enum.State.html#variant.Writing
    pub fn set_ready(&self) -> bool {
        self.swap_state(State::Writing, State::Ready)
    }

    /// Set the state to [`Reading`], returns true if all is ok. However it
    /// returns false if the state is not set to [`Reading`], which is the case
    /// if the current state is not [`Ready`].
    ///
    /// [`Reading`]: ./enum.State.html#variant.Reading
    /// [`Ready`]: ./enum.State.html#variant.Ready
    pub fn set_reading(&self) -> bool {
        self.swap_state(State::Ready, State::Reading)
    }

    /// Set the state to [`Empty`], returns true if all is ok. However it
    /// returns false if the state is not set to [`Empty`], which is the case
    /// if the current state is not [`Reading`].
    ///
    /// [`Empty`]: ./enum.State.html#variant.Empty
    /// [`Reading`]: ./enum.State.html#variant.Reading
    pub fn set_empty(&self) -> bool {
        self.swap_state(State::Reading, State::Empty)
    }

    fn swap_state(&self, current: State, next: State) -> bool {
        self.state.compare_exchange(current as usize, next as usize,
            DEFAULT_ORDERING, DEFAULT_ORDERING).is_ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn atomic_state() {
        let state = AtomicState::empty();
        assert!(state.is_empty());
        assert!(!state.is_ready());

        // Write to the data.
        assert!(state.set_writing());
        assert!(state.set_ready());
        assert!(!state.is_empty());
        assert!(state.is_ready());

        // Can't write again.
        assert!(!state.set_writing());
        assert!(!state.set_ready());

        // Read (pop) the data.
        assert!(state.set_reading());
        assert!(state.set_empty());
        assert!(state.is_empty());
        assert!(!state.is_ready());

        // Can't read now.
        assert!(!state.set_reading());
        assert!(!state.set_empty());
    }
}
