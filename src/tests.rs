use ::std::fmt;

use super::*;

fn assert_send<T: Send>() {}
fn assert_sync<T: Sync>() {}

#[test]
fn is_sync_and_send() {
    assert_send::<Queue<usize>>();
    assert_sync::<Queue<usize>>();
}

#[test]
fn simple_pushing_and_popping() {
    let queue = Queue::new();


    queue.push_front("My value1".to_owned());
    assert_eq!(queue.pop_front(), Some("My value1".to_owned()));
    assert_eq!(queue.pop_front(), None);

    queue.push_front("My value2".to_owned());
    queue.push_front("My value3".to_owned());
    assert_eq!(queue.pop_front(), Some("My value3".to_owned()));
    assert_eq!(queue.pop_front(), Some("My value2".to_owned()));

    assert_eq!(queue.pop_front(), None);
}

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

#[test]
fn stress_pushing_and_popping() {
    let queue = Queue::new();

    const MAX: usize = 1_000_000;

    for n in 0..MAX {
        println!("addding value: {}", n);
        queue.push_front(NotCopyable::new(n));
    }

    for n in (0..).take(MAX) {
        // Getting them back in reverse order.
        let want = Some(NotCopyable::new(MAX - 1 - n));
        let got = queue.pop_front();
        println!("got: {:?}", got);
        assert_eq!(got, want);
    }

    assert_eq!(queue.pop_front(), None);
}
