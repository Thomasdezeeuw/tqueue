use std::sync::atomic::AtomicIsize;

use super::DEFAULT_ORDERING;

/// A single position, first value is the `head`, the second the `tail` position.
pub type Pos = (i16, i16);

/// An `AtomicPos` is a single atomic that holds both a `head` and `tail`
/// position. Each operation (method) on this struct is a single atomic operation.
pub struct AtomicPos {
    // TODO: See what the performance difference is with different sizes, e.g.
    // i32 vs i64. Requires specific atomic sizes, see
    // https://github.com/rust-lang/rust/issues/32976.
    pos: AtomicIsize,
}

impl AtomicPos {
    /// Create a new `AtomicPos`, with a starting `head` and `tail` position.
    pub fn new(head: i16, tail: i16) -> AtomicPos {
        // If the head is negative we don't want all the high bits to be set to
        // 1 and then overwrite them with the tail, this will cause the tail to
        // always be incorrect. To fix this we'll make the head positive and
        // then make it negative again, but only in it's 16 bit space (by setting
        // all the bits to 1).
        let head: i32 = if head.is_negative() {
            let h = -head as i32;
            (h ^ 0b1111111111111111) + 1
        } else {
            head as i32
        };
        let pos = head | ((tail as i32) << 16);
        AtomicPos {
            pos: AtomicIsize::new(pos as isize),
        }
    }

    /// Load both the `head` and `tail` positions.
    pub fn load(&self) -> Pos {
        split(self.pos.load(DEFAULT_ORDERING))
    }

    /// Load `head` position.
    pub fn load_head(&self) -> i16 {
        high(self.pos.load(DEFAULT_ORDERING))
    }

    /// Load `tail` position.
    pub fn load_tail(&self) -> i16 {
        low(self.pos.load(DEFAULT_ORDERING))
    }

    /// Increase both the `head` and `tail` positions, returning the old values.
    pub fn increase_both(&self) -> Pos {
        split(self.pos.fetch_add(1 + (1 << 16), DEFAULT_ORDERING))
    }

    /// Increase `head` position, returning the old value.
    pub fn increase_head(&self) -> i16 {
        high(self.pos.fetch_add(1, DEFAULT_ORDERING))
    }

    /// Increase `tail` position, returning the old value.
    pub fn increase_tail(&self) -> i16 {
        low(self.pos.fetch_add(1 << 16, DEFAULT_ORDERING))
    }

    /// Decrease both the `head` and `tail` positions, returning the old values.
    pub fn decrease_both(&self) -> Pos {
        split(self.pos.fetch_sub(1 + (1 << 16), DEFAULT_ORDERING))
    }

    /// Decrease `head` position, returning the old value.
    pub fn decrease_head(&self) -> i16 {
        high(self.pos.fetch_sub(1, DEFAULT_ORDERING))
    }

    /// Decrease `tail` position, returning the old value.
    pub fn decrease_tail(&self) -> i16 {
        low(self.pos.fetch_sub(1 << 16, DEFAULT_ORDERING))
    }
}

/// Returns both the `head` and `tail` positions.
#[inline(always)]
fn split(value: isize) -> Pos {
    (high(value), low(value))
}

/// Return the `head` position.
#[inline(always)]
fn high(value: isize) -> i16 {
    value as i16
}

/// Return the `tail` position.
#[inline(always)]
fn low(value: isize) -> i16 {
    (value >> 16) as i16
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn atomic_position() {
        const MIN: i16 = ::std::i16::MIN + 1; // Don't underflow.
        const MAX: i16 = ::std::i16::MAX - 8; // Don't overflow.
        let tests = vec![
            (0, 0),
            (-100, 100),
            (100, -100),
            (MIN, 0),
            (MAX, 0),
            (0, MIN),
            (0, MAX),
            (MIN, MIN),
            (MAX, MAX),
            (MIN, MAX),
            (MAX, MIN),
        ];

        for test in tests {
            let pos = AtomicPos::new(test.0, test.1);
            assert_eq!(pos.load(), (test.0, test.1));
            assert_eq!(pos.load_head(), test.0);
            assert_eq!(pos.load_tail(), test.1);

            assert_eq!(pos.increase_head(), test.0);
            assert_eq!(pos.increase_head(), test.0 + 1);
            assert_eq!(pos.increase_head(), test.0 + 2);
            assert_eq!(pos.increase_head(), test.0 + 3);
            assert_eq!(pos.load_head(), test.0 + 4);
            assert_eq!(pos.load(), (test.0 + 4, test.1));

            assert_eq!(pos.increase_tail(), test.1);
            assert_eq!(pos.increase_tail(), test.1 + 1);
            assert_eq!(pos.increase_tail(), test.1 + 2);
            assert_eq!(pos.increase_tail(), test.1 + 3);
            assert_eq!(pos.load_tail(), test.1 + 4);
            assert_eq!(pos.load(), (test.0 + 4, test.1 + 4));

            assert_eq!(pos.increase_both(), (test.0 + 4, test.1 + 4));
            assert_eq!(pos.increase_both(), (test.0 + 5, test.1 + 5));
            assert_eq!(pos.increase_both(), (test.0 + 6, test.1 + 6));
            assert_eq!(pos.increase_both(), (test.0 + 7, test.1 + 7));
            assert_eq!(pos.load(), (test.0 + 8, test.1 + 8));

            assert_eq!(pos.decrease_both(), (test.0 + 8, test.1 + 8));
            assert_eq!(pos.decrease_both(), (test.0 + 7, test.1 + 7));
            assert_eq!(pos.decrease_both(), (test.0 + 6, test.1 + 6));
            assert_eq!(pos.decrease_both(), (test.0 + 5, test.1 + 5));
            assert_eq!(pos.load(), (test.0 + 4, test.1 + 4));

            assert_eq!(pos.decrease_head(), test.0 + 4);
            assert_eq!(pos.decrease_head(), test.0 + 3);
            assert_eq!(pos.decrease_head(), test.0 + 2);
            assert_eq!(pos.decrease_head(), test.0 + 1);
            assert_eq!(pos.load_head(), test.0);
            assert_eq!(pos.load(), (test.0, test.1 + 4));

            assert_eq!(pos.decrease_tail(), test.1 + 4);
            assert_eq!(pos.decrease_tail(), test.1 + 3);
            assert_eq!(pos.decrease_tail(), test.1 + 2);
            assert_eq!(pos.decrease_tail(), test.1 + 1);
            assert_eq!(pos.load_tail(), test.1);
            assert_eq!(pos.load(), (test.0, test.1));
        }
    }
}
