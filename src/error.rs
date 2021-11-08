use crate::result::Traced;
use crate::trace::ErrorTrace;

use core::{fmt, panic};

/// Wraps a generic error value and keeps track of an error trace.
#[derive(Clone)]
pub struct TracedError<
    // Type of the contained error value.
    E,
    // Type of the error trace.
    // NOTE: this trait bound has to be in the struct definition, otherwise we
    // won't be allowed to use the trait bound when implementing `Traced`.
    // This is because of the restrictions of `feature(min_specialization)`
    // imparted by `#[rustc_specialization_trait]`.
    T: ErrorTrace,
> {
    inner: E,
    trace: T,
}

impl<E, T> TracedError<E, T>
where
    T: ErrorTrace + Default,
{
    /// Wraps the given error and starts a new trace with the caller's location.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use tres::TracedError;
    ///
    /// let x: TracedError<&str> = TracedError::new("Oops!");
    /// ```
    ///
    /// Showing that the trace includes the caller of `new()`:
    ///
    /// ```
    /// use std::panic::Location;
    /// use tres::{Locations, TracedError};
    ///
    /// let here: &Location = Location::caller();
    /// let x: TracedError<&str> = TracedError::new("Oops!");
    ///
    /// let locs: &Locations = x.trace();
    /// let there: &Location = locs.0.first().unwrap();
    /// assert_eq!(there.line(), here.line() + 1);
    /// ```
    ///
    /// Using a custom trace type:
    ///
    /// ```
    /// use std::panic::Location;
    /// use tres::ErrorTrace;
    /// use tres::error::TracedError;  // not tres::TracedError
    ///
    /// #[derive(Default)]
    /// struct BangTrace(pub String);
    ///
    /// impl ErrorTrace for BangTrace {
    ///     fn append_location(&mut self, _location: &'static Location) {
    ///         self.0.push('!');
    ///     }
    /// }
    ///
    /// let x: TracedError<&str, BangTrace> = TracedError::new("Oops!");
    /// assert_eq!(&x.trace().0, "!");
    /// ```
    #[track_caller]
    pub fn new(inner: E) -> Self {
        let mut trace: T = Default::default();
        trace.append_location(panic::Location::caller());
        Self { inner, trace }
    }

    /// Wraps the given error and starts a new, empty trace.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use tres::TracedError;
    ///
    /// let x: TracedError<&str> = TracedError::empty("Oops!");
    /// assert!(x.trace().0.is_empty());
    /// ```
    pub fn empty(inner: E) -> Self {
        Self {
            inner,
            trace: Default::default(),
        }
    }
}

impl<E, T> TracedError<E, T>
where
    T: ErrorTrace,
{
    /// Returns a reference to the contained error value.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use tres::TracedError;
    ///
    /// let x: TracedError<String> = TracedError::new("Oops!".to_string());
    ///
    /// let inner: &String = x.inner();
    /// assert_eq!(inner.as_str(), "Oops!");
    /// ```
    pub fn inner(&self) -> &E {
        &self.inner
    }

    /// Returns a reference to the error trace.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use tres::{Locations, TracedError};
    ///
    /// let x: TracedError<String> = TracedError::new("Oops!".to_string());
    ///
    /// let trace: &Locations = x.trace();
    /// assert_eq!(trace.0.len(), 1);
    /// ```
    pub fn trace(&self) -> &T {
        &self.trace
    }

    /// Constructs a new `TracedError` from an error value and a trace.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use tres::{Locations, TracedError};
    ///
    /// let error: String = "Oops!".into();
    /// let trace: Locations = Default::default();
    ///
    /// let x = TracedError::from_parts(error, trace);
    /// assert_eq!(x.inner(), &"Oops!");
    /// assert_eq!(x.trace(), &Locations(vec![]));
    /// ```
    pub fn from_parts(inner: E, trace: T) -> Self {
        Self { inner, trace }
    }

    /// Returns the contained error value and error trace, consuming self.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use tres::{Locations, TracedError};
    ///
    /// let x: TracedError<String> = TracedError::new("Oops!".to_string());
    ///
    /// let (error, trace): (String, Locations) = x.into_parts();
    /// assert_eq!(error, "Oops!".to_string());
    /// assert_eq!(trace.0.len(), 1);
    /// ```
    pub fn into_parts(self) -> (E, T) {
        let Self { inner, trace } = self;
        (inner, trace)
    }

    /// Returns the contained error value, consuming self and discarding the trace.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use tres::TracedError;
    ///
    /// let x: TracedError<String> = TracedError::new("Oops!".to_string());
    ///
    /// let error: String = x.into_inner();
    /// assert_eq!(error, "Oops!".to_string());
    /// ```
    pub fn into_inner(self) -> E {
        let (inner, _trace) = self.into_parts();
        inner
    }

    /// Maps a `TracedError<E, T>` to `TracedError<F, T>` by applying a function
    /// to the contained error value, leaving the error trace untouched.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use tres::TracedError;
    ///
    /// let x: TracedError<u32> = TracedError::new(42);
    /// assert_eq!(x.trace().0.len(), 1);
    ///
    /// let x: TracedError<String> = x.map(|i| i.to_string());
    /// assert_eq!(x.trace().0.len(), 1);
    /// ```
    pub fn map<F, O: FnOnce(E) -> F>(self, op: O) -> TracedError<F, T> {
        TracedError {
            inner: op(self.inner),
            trace: self.trace,
        }
    }
}

/// The whole point. Enables tracing via `?` when used as an [`Err`] variant.
///
/// [`Err`]: crate::result::Result::Err
impl<E, T> Traced for TracedError<E, T>
where
    T: ErrorTrace,
{
    #[inline]
    fn trace(&mut self, location: &'static panic::Location) {
        self.trace.append_location(location);
    }
}

impl<E, T> fmt::Display for TracedError<E, T>
where
    E: fmt::Display,
    T: ErrorTrace + fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", &self.inner, &self.trace)
    }
}

impl<E, T> fmt::Debug for TracedError<E, T>
where
    E: fmt::Debug,
    T: ErrorTrace + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}: {:?}", &self.inner, &self.trace)
    }
}
