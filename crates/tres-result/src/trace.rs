use std::panic;

/// A trait that enables return tracing for [`Err`] variants of [`Result`].
///
/// [`Err`]: crate::Result::Err
/// [`Result`]: crate::Result
pub trait Trace {
    /// Called during `?` with the code location of the `?` invocation.
    fn trace(&mut self, location: &'static panic::Location<'static>);
}
