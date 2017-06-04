use std::sync::atomic::Ordering;

mod pos;
mod segment;


// TODO: try to relax the ordering, on a per call basis.
const DEFAULT_ORDERING: Ordering = Ordering::SeqCst;
