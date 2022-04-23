use core::{fmt, panic};

use crate::{Locations, Trace};

/// Wraps a generic error value and keeps track of an error trace.
#[derive(Clone)]
pub struct Traced<E, T = Locations>
where
    // NOTE: this trait bound has to be in the struct definition, otherwise we
    // won't be allowed to use the trait bound when implementing `Traced`.
    // This is because of the restrictions of `feature(min_specialization)`
    // imparted by `#[rustc_specialization_trait]`.
    T: Trace,
{
    inner: E,
    trace: T,
}

impl<E, T> Traced<E, T>
where
    T: Trace + Default,
{
    /// Wraps the given error and starts a new trace with the caller's location.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use tres::Traced;
    ///
    /// let x: Traced<&str> = Traced::new("Oops!");
    /// ```
    ///
    /// Showing that the trace includes the caller of `new()`:
    ///
    /// ```
    /// use std::panic::Location;
    /// use tres::{Locations, Traced};
    ///
    /// let here: &Location = Location::caller();
    /// let x: Traced<&str> = Traced::new("Oops!");
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
    /// use tres::{Trace, Traced};
    ///
    /// #[derive(Default)]
    /// struct BangTrace(pub String);
    ///
    /// impl Trace for BangTrace {
    ///     fn trace(&mut self, _location: &'static Location) {
    ///         self.0.push('!');
    ///     }
    /// }
    ///
    /// let x: Traced<&str, BangTrace> = Traced::new("Oops!");
    /// assert_eq!(&x.trace().0, "!");
    /// ```
    #[track_caller]
    pub fn new(inner: E) -> Self {
        let mut trace: T = Default::default();
        trace.trace(panic::Location::caller());
        Self { inner, trace }
    }

    /// Wraps the given error and starts a new, empty trace.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use tres::Traced;
    ///
    /// let x: Traced<&str> = Traced::empty("Oops!");
    /// assert!(x.trace().0.is_empty());
    /// ```
    pub fn empty(inner: E) -> Self {
        Self {
            inner,
            trace: Default::default(),
        }
    }
}

impl<E, T> Traced<E, T>
where
    T: Trace,
{
    /// Returns a reference to the contained error value.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use tres::Traced;
    ///
    /// let x: Traced<String> = Traced::new("Oops!".to_string());
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
    /// use tres::{Locations, Traced};
    ///
    /// let x: Traced<String> = Traced::new("Oops!".to_string());
    ///
    /// let trace: &Locations = x.trace();
    /// assert_eq!(trace.0.len(), 1);
    /// ```
    pub fn trace(&self) -> &T {
        &self.trace
    }

    /// Constructs a new `Traced` from an error value and a trace.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use tres::{Locations, Traced};
    ///
    /// let error: String = "Oops!".into();
    /// let trace: Locations = Default::default();
    ///
    /// let x = Traced::from_parts(error, trace);
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
    /// use tres::{Locations, Traced};
    ///
    /// let x: Traced<String> = Traced::new("Oops!".to_string());
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
    /// use tres::Traced;
    ///
    /// let x: Traced<String> = Traced::new("Oops!".to_string());
    ///
    /// let error: String = x.into_inner();
    /// assert_eq!(error, "Oops!".to_string());
    /// ```
    pub fn into_inner(self) -> E {
        let (inner, _trace) = self.into_parts();
        inner
    }

    /// Maps a `Traced<E, T>` to `Traced<F, T>` by applying a function
    /// to the contained error value, leaving the error trace untouched.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use tres::Traced;
    ///
    /// let x: Traced<u32> = Traced::new(42);
    /// assert_eq!(x.trace().0.len(), 1);
    ///
    /// let x: Traced<String> = x.map(|i| i.to_string());
    /// assert_eq!(x.trace().0.len(), 1);
    /// ```
    pub fn map<F, O: FnOnce(E) -> F>(self, op: O) -> Traced<F, T> {
        Traced {
            inner: op(self.inner),
            trace: self.trace,
        }
    }
}

/// The whole point. Enables tracing via `?` when used as an [`Err`] variant.
///
/// [`Err`]: crate::result::Result::Err
impl<E, T> crate::result::Trace for Traced<E, T>
where
    T: Trace,
{
    #[inline]
    fn trace(&mut self, location: &'static panic::Location) {
        self.trace.trace(location);
    }
}

impl<E, T> fmt::Display for Traced<E, T>
where
    E: fmt::Display,
    T: Trace + fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", &self.inner, &self.trace)
    }
}

impl<E, T> fmt::Debug for Traced<E, T>
where
    E: fmt::Debug,
    T: Trace + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}: {:?}", &self.inner, &self.trace)
    }
}

/////////////////////////////////////////////////////////////////////////////
// Blanket From impls
/////////////////////////////////////////////////////////////////////////////

/// An auto trait used to determine if two types are the same.
pub auto trait NotSame {}
impl<T> !NotSame for (T, T) {}

/// An auto trait used to determine if a type is a `Traced`.
pub auto trait NotTraced {}
impl<E, T: Trace> !NotTraced for Traced<E, T> {}

// Auto traits do not apply to non-sized types (e.g., `dyn Trait`), so we have
// to manually write positive implementations of the above two traits for things
// that might contain those types.
impl<T: ?Sized> NotSame for Box<T> {}
impl<T: ?Sized> NotTraced for Box<T> {}

/// Enables `?` conversion from `Traced<E, T>` to `Traced<F, T>`, as
/// long as `F: From<E>`.
///
/// # Examples
///
/// ```
/// use tres::{Result, Result::Err, Result::Ok, Traced};
///
/// fn foo() -> Result<(), Traced<String>> {
///     Ok(bar()?)
/// }
///
/// fn bar() -> Result<(), Traced<&'static str>> {
///     Err(Traced::new("Oops!"))
/// }
///
/// let x: Traced<String> = foo().unwrap_err();
/// assert_eq!(x.inner(), "Oops!");
/// assert_eq!(x.trace().0.len(), 2);
/// ```
impl<E, F, T> From<Traced<E, T>> for Traced<F, T>
where
    F: From<E>,
    (E, F): NotSame,
    T: Trace,
{
    #[inline]
    fn from(source: Traced<E, T>) -> Self {
        Self {
            inner: From::from(source.inner),
            trace: source.trace,
        }
    }
}

/// Enables `?` conversion from `E` to `Traced<F, T>`, as long as `F: From<E>`.
///
/// # Examples
///
/// ```
/// use tres::Traced;
///
/// fn foo() -> Result<(), Traced<String>> {
///     Ok(bar()?)
/// }
///
/// fn bar() -> Result<(), &'static str> {
///     Err("Oops!")
/// }
///
/// let x: Traced<String> = foo().unwrap_err();
/// assert_eq!(x.inner(), "Oops!");
/// ```
impl<E, F, T> From<E> for Traced<F, T>
where
    E: NotTraced,
    F: From<E>,
    T: Trace + Default,
{
    fn from(source: E) -> Self {
        Self {
            inner: From::from(source),
            // Use default() here, as we should already be inside a `?`
            // invocation, and that will append the location for us.
            trace: Default::default(),
        }
    }
}
