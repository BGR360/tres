use core::panic;

use crate::error::{NotTraced, Traced};

/// A trait for types that store an error trace.
pub trait Trace {
    /// Appends a code location to the error trace.
    fn trace(&mut self, location: &'static panic::Location);
}

/// An extension trait applied to all untraced error types that allows
/// conversion to [`Traced`].
pub trait ErrorExt: Sized + NotTraced {
    /// Wraps self in a `Traced` and starts an error trace with the
    /// caller's location.
    #[track_caller]
    fn traced<T: Trace + Default>(self) -> Traced<Self, T> {
        Traced::new(self)
    }
}

impl<E: NotTraced> ErrorExt for E {}
