//! Error handling with the `Result` type.
//!
//! See the [standard library documentation][core::result] for more information.

use crate::Traced;

use core::iter::{FromIterator, FusedIterator, TrustedLen};
use core::ops::{self, ControlFlow, Deref, DerefMut};
use core::{convert, fmt, hint, panic};

use self::Result::Err;
use self::Result::Ok;

/// A drop-in replacement for [`core::result::Result`] that supports return
/// tracing using the `?` operator.
///
/// If the [`Err`] variant implements [`Traced`], then each invocation of the
/// `?` operator on an [`Err`] variant will call [`Traced::trace()`] with the
/// code location where `?` was invoked.
#[derive(Copy, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
#[must_use = "this `Result` may be an `Err` variant, which should be handled"]
pub enum Result<T, E> {
    /// Contains the success value
    Ok(T),

    /// Contains the error value
    Err(E),
}

/////////////////////////////////////////////////////////////////////////////
// Conversion to/from core result
/////////////////////////////////////////////////////////////////////////////

impl<T, E> From<core::result::Result<T, E>> for Result<T, E> {
    #[inline]
    fn from(x: core::result::Result<T, E>) -> Self {
        match x {
            core::result::Result::Ok(x) => Ok(x),
            core::result::Result::Err(err) => Err(err),
        }
    }
}

impl<T, E> From<Result<T, E>> for core::result::Result<T, E> {
    #[inline]
    fn from(x: Result<T, E>) -> Self {
        match x {
            Ok(x) => core::result::Result::Ok(x),
            Err(err) => core::result::Result::Err(err),
        }
    }
}

/////////////////////////////////////////////////////////////////////////////
// Try trait
/////////////////////////////////////////////////////////////////////////////

impl<T, E> ops::Try for Result<T, E> {
    type Output = T;
    type Residual = Result<convert::Infallible, E>;

    #[inline]
    fn from_output(output: Self::Output) -> Self {
        Ok(output)
    }

    #[inline]
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        match self {
            Ok(v) => ControlFlow::Continue(v),
            Err(e) => ControlFlow::Break(Err(e)),
        }
    }
}

/////////////////////////////////////////////////////////////////////////////
// FromResidual: tres_result::Result -> tres_result::Result
/////////////////////////////////////////////////////////////////////////////

impl<T, E, F> ops::FromResidual<Result<convert::Infallible, E>> for Result<T, F>
where
    F: From<E>,
{
    #[inline]
    default fn from_residual(residual: Result<convert::Infallible, E>) -> Self {
        match residual {
            Ok(_) => unreachable!(),
            Err(e) => Err(From::from(e)),
        }
    }
}

impl<T, E, F> ops::FromResidual<Result<convert::Infallible, E>> for Result<T, F>
where
    F: From<E> + Traced,
{
    #[track_caller]
    #[inline]
    fn from_residual(residual: Result<convert::Infallible, E>) -> Self {
        match residual {
            Ok(_) => unreachable!(),
            Err(e) => {
                let mut f = F::from(e);
                f.trace(panic::Location::caller());
                Err(f)
            }
        }
    }
}

/////////////////////////////////////////////////////////////////////////////
// FromResidual: core::result::Result -> tres_result::Result
/////////////////////////////////////////////////////////////////////////////

impl<T, E, F> ops::FromResidual<core::result::Result<convert::Infallible, E>> for Result<T, F>
where
    F: From<E>,
{
    #[inline]
    default fn from_residual(residual: core::result::Result<convert::Infallible, E>) -> Self {
        match residual {
            core::result::Result::Ok(_) => unreachable!(),
            core::result::Result::Err(e) => Err(From::from(e)),
        }
    }
}

impl<T, E, F> ops::FromResidual<core::result::Result<convert::Infallible, E>> for Result<T, F>
where
    F: From<E> + Traced,
{
    #[track_caller]
    #[inline]
    fn from_residual(residual: core::result::Result<convert::Infallible, E>) -> Self {
        match residual {
            core::result::Result::Ok(_) => unreachable!(),
            core::result::Result::Err(e) => {
                let mut f = F::from(e);
                f.trace(panic::Location::caller());
                Err(f)
            }
        }
    }
}

/////////////////////////////////////////////////////////////////////////////
// FromResidual: tres_result::Result -> core::result::Result
/////////////////////////////////////////////////////////////////////////////

impl<T, E, F> ops::FromResidual<Result<convert::Infallible, E>> for core::result::Result<T, F>
where
    F: From<E>,
{
    #[inline]
    default fn from_residual(residual: Result<convert::Infallible, E>) -> Self {
        match residual {
            Ok(_) => unreachable!(),
            Err(e) => core::result::Result::Err(From::from(e)),
        }
    }
}

impl<T, E, F> ops::FromResidual<Result<convert::Infallible, E>> for core::result::Result<T, F>
where
    E: Traced,
    F: From<E>,
{
    #[track_caller]
    #[inline]
    fn from_residual(residual: Result<convert::Infallible, E>) -> Self {
        match residual {
            Ok(_) => unreachable!(),
            Err(mut e) => {
                e.trace(panic::Location::caller());
                core::result::Result::Err(From::from(e))
            }
        }
    }
}

/////////////////////////////////////////////////////////////////////////////
// Type implementation
/////////////////////////////////////////////////////////////////////////////

impl<T, E> Result<T, E> {
    /////////////////////////////////////////////////////////////////////////
    // Querying the contained values
    /////////////////////////////////////////////////////////////////////////

    /// Returns `true` if the result is [`Ok`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let x: Result<i32, &str> = Ok(-3);
    /// assert_eq!(x.is_ok(), true);
    ///
    /// let x: Result<i32, &str> = Err("Some error message");
    /// assert_eq!(x.is_ok(), false);
    /// ```
    #[must_use = "if you intended to assert that this is ok, consider `.unwrap()` instead"]
    #[inline]
    pub const fn is_ok(&self) -> bool {
        matches!(*self, Ok(_))
    }

    /// Returns `true` if the result is [`Err`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let x: Result<i32, &str> = Ok(-3);
    /// assert_eq!(x.is_err(), false);
    ///
    /// let x: Result<i32, &str> = Err("Some error message");
    /// assert_eq!(x.is_err(), true);
    /// ```
    #[must_use = "if you intended to assert that this is err, consider `.unwrap_err()` instead"]
    #[inline]
    pub const fn is_err(&self) -> bool {
        !self.is_ok()
    }

    /// Returns `true` if the result is an [`Ok`] value containing the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(option_result_contains)]
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    ///
    /// let x: Result<u32, &str> = Ok(2);
    /// assert_eq!(x.contains(&2), true);
    ///
    /// let x: Result<u32, &str> = Ok(3);
    /// assert_eq!(x.contains(&2), false);
    ///
    /// let x: Result<u32, &str> = Err("Some error message");
    /// assert_eq!(x.contains(&2), false);
    /// ```
    #[must_use]
    #[inline]
    //#[unstable(feature = "option_result_contains", issue = "62358")]
    pub fn contains<U>(&self, x: &U) -> bool
    where
        U: PartialEq<T>,
    {
        match self {
            Ok(y) => x == y,
            Err(_) => false,
        }
    }

    /// Returns `true` if the result is an [`Err`] value containing the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(result_contains_err)]
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    ///
    /// let x: Result<u32, &str> = Ok(2);
    /// assert_eq!(x.contains_err(&"Some error message"), false);
    ///
    /// let x: Result<u32, &str> = Err("Some error message");
    /// assert_eq!(x.contains_err(&"Some error message"), true);
    ///
    /// let x: Result<u32, &str> = Err("Some other error message");
    /// assert_eq!(x.contains_err(&"Some error message"), false);
    /// ```
    #[must_use]
    #[inline]
    //#[unstable(feature = "result_contains_err", issue = "62358")]
    pub fn contains_err<F>(&self, f: &F) -> bool
    where
        F: PartialEq<E>,
    {
        match self {
            Ok(_) => false,
            Err(e) => f == e,
        }
    }

    /////////////////////////////////////////////////////////////////////////
    // Adapter for each variant
    /////////////////////////////////////////////////////////////////////////

    /// Converts from `Result<T, E>` to [`Option<T>`].
    ///
    /// Converts `self` into an [`Option<T>`], consuming `self`,
    /// and discarding the error, if any.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let x: Result<u32, &str> = Ok(2);
    /// assert_eq!(x.ok(), Some(2));
    ///
    /// let x: Result<u32, &str> = Err("Nothing here");
    /// assert_eq!(x.ok(), None);
    /// ```
    #[inline]
    pub fn ok(self) -> Option<T> {
        match self {
            Ok(x) => Some(x),
            Err(_) => None,
        }
    }

    /// Converts from `Result<T, E>` to [`Option<E>`].
    ///
    /// Converts `self` into an [`Option<E>`], consuming `self`,
    /// and discarding the success value, if any.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let x: Result<u32, &str> = Ok(2);
    /// assert_eq!(x.err(), None);
    ///
    /// let x: Result<u32, &str> = Err("Nothing here");
    /// assert_eq!(x.err(), Some("Nothing here"));
    /// ```
    #[inline]
    pub fn err(self) -> Option<E> {
        match self {
            Ok(_) => None,
            Err(x) => Some(x),
        }
    }

    /////////////////////////////////////////////////////////////////////////
    // Adapter for working with references
    /////////////////////////////////////////////////////////////////////////

    /// Converts from `&Result<T, E>` to `Result<&T, &E>`.
    ///
    /// Produces a new `Result`, containing a reference
    /// into the original, leaving the original in place.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let x: Result<u32, &str> = Ok(2);
    /// assert_eq!(x.as_ref(), Ok(&2));
    ///
    /// let x: Result<u32, &str> = Err("Error");
    /// assert_eq!(x.as_ref(), Err(&"Error"));
    /// ```
    #[inline]
    pub const fn as_ref(&self) -> Result<&T, &E> {
        match *self {
            Ok(ref x) => Ok(x),
            Err(ref x) => Err(x),
        }
    }

    /// Converts from `&mut Result<T, E>` to `Result<&mut T, &mut E>`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// fn mutate(r: &mut Result<i32, i32>) {
    ///     match r.as_mut() {
    ///         Ok(v) => *v = 42,
    ///         Err(e) => *e = 0,
    ///     }
    /// }
    ///
    /// let mut x: Result<i32, i32> = Ok(2);
    /// mutate(&mut x);
    /// assert_eq!(x.unwrap(), 42);
    ///
    /// let mut x: Result<i32, i32> = Err(13);
    /// mutate(&mut x);
    /// assert_eq!(x.unwrap_err(), 0);
    /// ```
    #[inline]
    pub fn as_mut(&mut self) -> Result<&mut T, &mut E> {
        match *self {
            Ok(ref mut x) => Ok(x),
            Err(ref mut x) => Err(x),
        }
    }

    /////////////////////////////////////////////////////////////////////////
    // Transforming contained values
    /////////////////////////////////////////////////////////////////////////

    /// Maps a `Result<T, E>` to `Result<U, E>` by applying a function to a
    /// contained [`Ok`] value, leaving an [`Err`] value untouched.
    ///
    /// This function can be used to compose the results of two functions.
    ///
    /// # Examples
    ///
    /// Print the numbers on each line of a string multiplied by two.
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let x: Result<u32, &str> = Ok(2);
    /// assert_eq!(x.map(|i| i * 2), Ok(4));
    ///
    /// let x: Result<u32, &str> = Err("Nothing here");
    /// assert_eq!(x.map(|i| i * 2), Err("Nothing here"));
    /// ```
    #[inline]
    pub fn map<U, F: FnOnce(T) -> U>(self, op: F) -> Result<U, E> {
        match self {
            Ok(t) => Ok(op(t)),
            Err(e) => Err(e),
        }
    }

    /// Returns the provided default (if [`Err`]), or
    /// applies a function to the contained value (if [`Ok`]),
    ///
    /// Arguments passed to `map_or` are eagerly evaluated; if you are passing
    /// the result of a function call, it is recommended to use [`map_or_else`],
    /// which is lazily evaluated.
    ///
    /// [`map_or_else`]: Result::map_or_else
    ///
    /// # Examples
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let x: Result<_, &str> = Ok("foo");
    /// assert_eq!(x.map_or(42, |v| v.len()), 3);
    ///
    /// let x: Result<&str, _> = Err("bar");
    /// assert_eq!(x.map_or(42, |v| v.len()), 42);
    /// ```
    #[inline]
    pub fn map_or<U, F: FnOnce(T) -> U>(self, default: U, f: F) -> U {
        match self {
            Ok(t) => f(t),
            Err(_) => default,
        }
    }

    /// Maps a `Result<T, E>` to `U` by applying a fallback function to a
    /// contained [`Err`] value, or a default function to a
    /// contained [`Ok`] value.
    ///
    /// This function can be used to unpack a successful result
    /// while handling an error.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let k = 21;
    ///
    /// let x : Result<_, &str> = Ok("foo");
    /// assert_eq!(x.map_or_else(|e| k * 2, |v| v.len()), 3);
    ///
    /// let x : Result<&str, _> = Err("bar");
    /// assert_eq!(x.map_or_else(|e| k * 2, |v| v.len()), 42);
    /// ```
    #[inline]
    pub fn map_or_else<U, D: FnOnce(E) -> U, F: FnOnce(T) -> U>(self, default: D, f: F) -> U {
        match self {
            Ok(t) => f(t),
            Err(e) => default(e),
        }
    }

    /// Maps a `Result<T, E>` to `Result<T, F>` by applying a function to a
    /// contained [`Err`] value, leaving an [`Ok`] value untouched.
    ///
    /// This function can be used to pass through a successful result while handling
    /// an error.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// fn stringify(x: u32) -> String { format!("error code: {}", x) }
    ///
    /// let x: Result<u32, u32> = Ok(2);
    /// assert_eq!(x.map_err(stringify), Ok(2));
    ///
    /// let x: Result<u32, u32> = Err(13);
    /// assert_eq!(x.map_err(stringify), Err("error code: 13".to_string()));
    /// ```
    #[inline]
    pub fn map_err<F, O: FnOnce(E) -> F>(self, op: O) -> Result<T, F> {
        match self {
            Ok(t) => Ok(t),
            Err(e) => Err(op(e)),
        }
    }

    /////////////////////////////////////////////////////////////////////////
    // Iterator constructors
    /////////////////////////////////////////////////////////////////////////

    /// Returns an iterator over the possibly contained value.
    ///
    /// The iterator yields one value if the result is [`Result::Ok`], otherwise none.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let x: Result<u32, &str> = Ok(7);
    /// assert_eq!(x.iter().next(), Some(&7));
    ///
    /// let x: Result<u32, &str> = Err("nothing!");
    /// assert_eq!(x.iter().next(), None);
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            inner: self.as_ref().ok(),
        }
    }

    /// Returns a mutable iterator over the possibly contained value.
    ///
    /// The iterator yields one value if the result is [`Result::Ok`], otherwise none.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let mut x: Result<u32, &str> = Ok(7);
    /// match x.iter_mut().next() {
    ///     Some(v) => *v = 40,
    ///     None => {},
    /// }
    /// assert_eq!(x, Ok(40));
    ///
    /// let mut x: Result<u32, &str> = Err("nothing!");
    /// assert_eq!(x.iter_mut().next(), None);
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            inner: self.as_mut().ok(),
        }
    }

    ////////////////////////////////////////////////////////////////////////
    // Boolean operations on the values, eager and lazy
    /////////////////////////////////////////////////////////////////////////

    /// Returns `res` if the result is [`Ok`], otherwise returns the [`Err`] value of `self`.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let x: Result<u32, &str> = Ok(2);
    /// let y: Result<&str, &str> = Err("late error");
    /// assert_eq!(x.and(y), Err("late error"));
    ///
    /// let x: Result<u32, &str> = Err("early error");
    /// let y: Result<&str, &str> = Ok("foo");
    /// assert_eq!(x.and(y), Err("early error"));
    ///
    /// let x: Result<u32, &str> = Err("not a 2");
    /// let y: Result<&str, &str> = Err("late error");
    /// assert_eq!(x.and(y), Err("not a 2"));
    ///
    /// let x: Result<u32, &str> = Ok(2);
    /// let y: Result<&str, &str> = Ok("different result type");
    /// assert_eq!(x.and(y), Ok("different result type"));
    /// ```
    #[inline]
    pub fn and<U>(self, res: Result<U, E>) -> Result<U, E> {
        match self {
            Ok(_) => res,
            Err(e) => Err(e),
        }
    }

    /// Calls `op` if the result is [`Ok`], otherwise returns the [`Err`] value of `self`.
    ///
    ///
    /// This function can be used for control flow based on `Result` values.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// fn sq(x: u32) -> Result<u32, u32> { Ok(x * x) }
    /// fn err(x: u32) -> Result<u32, u32> { Err(x) }
    ///
    /// assert_eq!(Ok(2).and_then(sq).and_then(sq), Ok(16));
    /// assert_eq!(Ok(2).and_then(sq).and_then(err), Err(4));
    /// assert_eq!(Ok(2).and_then(err).and_then(sq), Err(2));
    /// assert_eq!(Err(3).and_then(sq).and_then(sq), Err(3));
    /// ```
    #[inline]
    pub fn and_then<U, F: FnOnce(T) -> Result<U, E>>(self, op: F) -> Result<U, E> {
        match self {
            Ok(t) => op(t),
            Err(e) => Err(e),
        }
    }

    /// Returns `res` if the result is [`Err`], otherwise returns the [`Ok`] value of `self`.
    ///
    /// Arguments passed to `or` are eagerly evaluated; if you are passing the
    /// result of a function call, it is recommended to use [`or_else`], which is
    /// lazily evaluated.
    ///
    /// [`or_else`]: Result::or_else
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let x: Result<u32, &str> = Ok(2);
    /// let y: Result<u32, &str> = Err("late error");
    /// assert_eq!(x.or(y), Ok(2));
    ///
    /// let x: Result<u32, &str> = Err("early error");
    /// let y: Result<u32, &str> = Ok(2);
    /// assert_eq!(x.or(y), Ok(2));
    ///
    /// let x: Result<u32, &str> = Err("not a 2");
    /// let y: Result<u32, &str> = Err("late error");
    /// assert_eq!(x.or(y), Err("late error"));
    ///
    /// let x: Result<u32, &str> = Ok(2);
    /// let y: Result<u32, &str> = Ok(100);
    /// assert_eq!(x.or(y), Ok(2));
    /// ```
    #[inline]
    pub fn or<F>(self, res: Result<T, F>) -> Result<T, F> {
        match self {
            Ok(v) => Ok(v),
            Err(_) => res,
        }
    }

    /// Calls `op` if the result is [`Err`], otherwise returns the [`Ok`] value of `self`.
    ///
    /// This function can be used for control flow based on result values.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// fn sq(x: u32) -> Result<u32, u32> { Ok(x * x) }
    /// fn err(x: u32) -> Result<u32, u32> { Err(x) }
    ///
    /// assert_eq!(Ok(2).or_else(sq).or_else(sq), Ok(2));
    /// assert_eq!(Ok(2).or_else(err).or_else(sq), Ok(2));
    /// assert_eq!(Err(3).or_else(sq).or_else(err), Ok(9));
    /// assert_eq!(Err(3).or_else(err).or_else(err), Err(3));
    /// ```
    #[inline]
    pub fn or_else<F, O: FnOnce(E) -> Result<T, F>>(self, op: O) -> Result<T, F> {
        match self {
            Ok(t) => Ok(t),
            Err(e) => op(e),
        }
    }

    /// Returns the contained [`Ok`] value or a provided default.
    ///
    /// Arguments passed to `unwrap_or` are eagerly evaluated; if you are passing
    /// the result of a function call, it is recommended to use [`unwrap_or_else`],
    /// which is lazily evaluated.
    ///
    /// [`unwrap_or_else`]: Result::unwrap_or_else
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let default = 2;
    /// let x: Result<u32, &str> = Ok(9);
    /// assert_eq!(x.unwrap_or(default), 9);
    ///
    /// let x: Result<u32, &str> = Err("error");
    /// assert_eq!(x.unwrap_or(default), default);
    /// ```
    #[inline]
    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Ok(t) => t,
            Err(_) => default,
        }
    }

    /// Returns the contained [`Ok`] value or computes it from a closure.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// fn count(x: &str) -> usize { x.len() }
    ///
    /// assert_eq!(Ok(2).unwrap_or_else(count), 2);
    /// assert_eq!(Err("foo").unwrap_or_else(count), 3);
    /// ```
    #[inline]
    pub fn unwrap_or_else<F: FnOnce(E) -> T>(self, op: F) -> T {
        match self {
            Ok(t) => t,
            Err(e) => op(e),
        }
    }

    /// Returns the contained [`Ok`] value, consuming the `self` value,
    /// without checking that the value is not an [`Err`].
    ///
    /// # Safety
    ///
    /// Calling this method on an [`Err`] is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(option_result_unwrap_unchecked)]
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let x: Result<u32, &str> = Ok(2);
    /// assert_eq!(unsafe { x.unwrap_unchecked() }, 2);
    /// ```
    ///
    /// ```no_run
    /// #![feature(option_result_unwrap_unchecked)]
    /// let x: Result<u32, &str> = Err("emergency failure");
    /// unsafe { x.unwrap_unchecked(); } // Undefined behavior!
    /// ```
    #[inline]
    #[track_caller]
    //#[unstable(feature = "option_result_unwrap_unchecked", reason = "newly added", issue = "81383")]
    pub unsafe fn unwrap_unchecked(self) -> T {
        debug_assert!(self.is_ok());
        match self {
            Ok(t) => t,
            // SAFETY: the safety contract must be upheld by the caller.
            Err(_) => unsafe { hint::unreachable_unchecked() },
        }
    }

    /// Returns the contained [`Err`] value, consuming the `self` value,
    /// without checking that the value is not an [`Ok`].
    ///
    /// # Safety
    ///
    /// Calling this method on an [`Ok`] is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// # Examples
    ///
    /// ```no_run
    /// #![feature(option_result_unwrap_unchecked)]
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let x: Result<u32, &str> = Ok(2);
    /// unsafe { x.unwrap_err_unchecked() }; // Undefined behavior!
    /// ```
    ///
    /// ```
    /// #![feature(option_result_unwrap_unchecked)]
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let x: Result<u32, &str> = Err("emergency failure");
    /// assert_eq!(unsafe { x.unwrap_err_unchecked() }, "emergency failure");
    /// ```
    #[inline]
    #[track_caller]
    //#[unstable(feature = "option_result_unwrap_unchecked", reason = "newly added", issue = "81383")]
    pub unsafe fn unwrap_err_unchecked(self) -> E {
        debug_assert!(self.is_err());
        match self {
            // SAFETY: the safety contract must be upheld by the caller.
            Ok(_) => unsafe { hint::unreachable_unchecked() },
            Err(e) => e,
        }
    }
}

impl<T: Copy, E> Result<&T, E> {
    /// Maps a `Result<&T, E>` to a `Result<T, E>` by copying the contents of the
    /// `Ok` part.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(result_copied)]
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let val = 12;
    /// let x: Result<&i32, i32> = Ok(&val);
    /// assert_eq!(x, Ok(&12));
    /// let copied = x.copied();
    /// assert_eq!(copied, Ok(12));
    /// ```
    //#[unstable(feature = "result_copied", reason = "newly added", issue = "63168")]
    pub fn copied(self) -> Result<T, E> {
        self.map(|&t| t)
    }
}

impl<T: Copy, E> Result<&mut T, E> {
    /// Maps a `Result<&mut T, E>` to a `Result<T, E>` by copying the contents of the
    /// `Ok` part.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(result_copied)]
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let mut val = 12;
    /// let x: Result<&mut i32, i32> = Ok(&mut val);
    /// assert_eq!(x, Ok(&mut 12));
    /// let copied = x.copied();
    /// assert_eq!(copied, Ok(12));
    /// ```
    //#[unstable(feature = "result_copied", reason = "newly added", issue = "63168")]
    pub fn copied(self) -> Result<T, E> {
        self.map(|&mut t| t)
    }
}

impl<T: Clone, E> Result<&T, E> {
    /// Maps a `Result<&T, E>` to a `Result<T, E>` by cloning the contents of the
    /// `Ok` part.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(result_cloned)]
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let val = 12;
    /// let x: Result<&i32, i32> = Ok(&val);
    /// assert_eq!(x, Ok(&12));
    /// let cloned = x.cloned();
    /// assert_eq!(cloned, Ok(12));
    /// ```
    //#[unstable(feature = "result_cloned", reason = "newly added", issue = "63168")]
    pub fn cloned(self) -> Result<T, E> {
        self.map(|t| t.clone())
    }
}

impl<T: Clone, E> Result<&mut T, E> {
    /// Maps a `Result<&mut T, E>` to a `Result<T, E>` by cloning the contents of the
    /// `Ok` part.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(result_cloned)]
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let mut val = 12;
    /// let x: Result<&mut i32, i32> = Ok(&mut val);
    /// assert_eq!(x, Ok(&mut 12));
    /// let cloned = x.cloned();
    /// assert_eq!(cloned, Ok(12));
    /// ```
    //#[unstable(feature = "result_cloned", reason = "newly added", issue = "63168")]
    pub fn cloned(self) -> Result<T, E> {
        self.map(|t| t.clone())
    }
}

impl<T, E: fmt::Debug> Result<T, E> {
    /// Returns the contained [`Ok`] value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is an [`Err`], with a panic message including the
    /// passed message, and the content of the [`Err`].
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```should_panic
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let x: Result<u32, &str> = Err("emergency failure");
    /// x.expect("Testing expect"); // panics with `Testing expect: emergency failure`
    /// ```
    #[inline]
    #[track_caller]
    pub fn expect(self, msg: &str) -> T {
        match self {
            Ok(t) => t,
            Err(e) => unwrap_failed(msg, &e),
        }
    }

    /// Returns the contained [`Ok`] value, consuming the `self` value.
    ///
    /// Because this function may panic, its use is generally discouraged.
    /// Instead, prefer to use pattern matching and handle the [`Err`]
    /// case explicitly, or call [`unwrap_or`], [`unwrap_or_else`], or
    /// [`unwrap_or_default`].
    ///
    /// [`unwrap_or`]: Result::unwrap_or
    /// [`unwrap_or_else`]: Result::unwrap_or_else
    /// [`unwrap_or_default`]: Result::unwrap_or_default
    ///
    /// # Panics
    ///
    /// Panics if the value is an [`Err`], with a panic message provided by the
    /// [`Err`]'s value.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Ok};
    /// let x: Result<u32, &str> = Ok(2);
    /// assert_eq!(x.unwrap(), 2);
    /// ```
    ///
    /// ```should_panic
    /// # use tres_result::{Result, Result::Err};
    /// let x: Result<u32, &str> = Err("emergency failure");
    /// x.unwrap(); // panics with `emergency failure`
    /// ```
    #[inline]
    #[track_caller]
    pub fn unwrap(self) -> T {
        match self {
            Ok(t) => t,
            Err(e) => unwrap_failed("called `Result::unwrap()` on an `Err` value", &e),
        }
    }
}

impl<T: fmt::Debug, E> Result<T, E> {
    /// Returns the contained [`Err`] value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is an [`Ok`], with a panic message including the
    /// passed message, and the content of the [`Ok`].
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```should_panic
    /// # use tres_result::{Result, Result::Ok};
    /// let x: Result<u32, &str> = Ok(10);
    /// x.expect_err("Testing expect_err"); // panics with `Testing expect_err: 10`
    /// ```
    #[inline]
    #[track_caller]
    pub fn expect_err(self, msg: &str) -> E {
        match self {
            Ok(t) => unwrap_failed(msg, &t),
            Err(e) => e,
        }
    }

    /// Returns the contained [`Err`] value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is an [`Ok`], with a custom panic message provided
    /// by the [`Ok`]'s value.
    ///
    /// # Examples
    ///
    /// ```should_panic
    /// # use tres_result::{Result, Result::Ok};
    /// let x: Result<u32, &str> = Ok(2);
    /// x.unwrap_err(); // panics with `2`
    /// ```
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err};
    /// let x: Result<u32, &str> = Err("emergency failure");
    /// assert_eq!(x.unwrap_err(), "emergency failure");
    /// ```
    #[inline]
    #[track_caller]
    pub fn unwrap_err(self) -> E {
        match self {
            Ok(t) => unwrap_failed("called `Result::unwrap_err()` on an `Ok` value", &t),
            Err(e) => e,
        }
    }
}

impl<T: Default, E> Result<T, E> {
    /// Returns the contained [`Ok`] value or a default
    ///
    /// Consumes the `self` argument then, if [`Ok`], returns the contained
    /// value, otherwise if [`Err`], returns the default value for that
    /// type.
    ///
    /// # Examples
    ///
    /// Converts a string to an integer, turning poorly-formed strings
    /// into 0 (the default value for integers). [`parse`] converts
    /// a string to any other type that implements [`FromStr`], returning an
    /// [`Err`] on error.
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// use core::str::FromStr;
    ///
    /// fn parse<T: FromStr>(s: &str) -> Result<T, <T as FromStr>::Err> {
    ///     s.parse().into()
    /// }
    ///
    /// let good_year_from_input = "1909";
    /// let bad_year_from_input = "190blarg";
    /// let good_year = parse(good_year_from_input).unwrap_or_default();
    /// let bad_year = parse(bad_year_from_input).unwrap_or_default();
    ///
    /// assert_eq!(1909, good_year);
    /// assert_eq!(0, bad_year);
    /// ```
    ///
    /// [`parse`]: str::parse
    /// [`FromStr`]: core::str::FromStr
    #[inline]
    pub fn unwrap_or_default(self) -> T {
        match self {
            Ok(x) => x,
            Err(_) => Default::default(),
        }
    }
}

//#[unstable(feature = "unwrap_infallible", reason = "newly added", issue = "61695")]
impl<T, E: Into<!>> Result<T, E> {
    /// Returns the contained [`Ok`] value, but never panics.
    ///
    /// Unlike [`unwrap`], this method is known to never panic on the
    /// result types it is implemented for. Therefore, it can be used
    /// instead of `unwrap` as a maintainability safeguard that will fail
    /// to compile if the error type of the `Result` is later changed
    /// to an error that can actually occur.
    ///
    /// [`unwrap`]: Result::unwrap
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # #![feature(never_type)]
    /// # #![feature(unwrap_infallible)]
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    ///
    /// fn only_good_news() -> Result<String, !> {
    ///     Ok("this is fine".into())
    /// }
    ///
    /// let s: String = only_good_news().into_ok();
    /// println!("{}", s);
    /// ```
    #[inline]
    pub fn into_ok(self) -> T {
        match self {
            Ok(x) => x,
            Err(e) => e.into(),
        }
    }
}

//#[unstable(feature = "unwrap_infallible", reason = "newly added", issue = "61695")]
impl<T: Into<!>, E> Result<T, E> {
    /// Returns the contained [`Err`] value, but never panics.
    ///
    /// Unlike [`unwrap_err`], this method is known to never panic on the
    /// result types it is implemented for. Therefore, it can be used
    /// instead of `unwrap_err` as a maintainability safeguard that will fail
    /// to compile if the ok type of the `Result` is later changed
    /// to a type that can actually occur.
    ///
    /// [`unwrap_err`]: Result::unwrap_err
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # #![feature(never_type)]
    /// # #![feature(unwrap_infallible)]
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    ///
    /// fn only_bad_news() -> Result<!, String> {
    ///     Err("Oops, it failed".into())
    /// }
    ///
    /// let error: String = only_bad_news().into_err();
    /// println!("{}", error);
    /// ```
    #[inline]
    pub fn into_err(self) -> E {
        match self {
            Ok(x) => x.into(),
            Err(e) => e,
        }
    }
}

impl<T: Deref, E> Result<T, E> {
    /// Converts from `Result<T, E>` (or `&Result<T, E>`) to `Result<&<T as Deref>::Target, &E>`.
    ///
    /// Coerces the [`Ok`] variant of the original [`Result`] via [`Deref`](core::ops::Deref)
    /// and returns the new [`Result`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let x: Result<String, u32> = Ok("hello".to_string());
    /// let y: Result<&str, &u32> = Ok("hello");
    /// assert_eq!(x.as_deref(), y);
    ///
    /// let x: Result<String, u32> = Err(42);
    /// let y: Result<&str, &u32> = Err(&42);
    /// assert_eq!(x.as_deref(), y);
    /// ```
    pub fn as_deref(&self) -> Result<&T::Target, &E> {
        self.as_ref().map(|t| t.deref())
    }
}

impl<T: DerefMut, E> Result<T, E> {
    /// Converts from `Result<T, E>` (or `&mut Result<T, E>`) to `Result<&mut <T as DerefMut>::Target, &mut E>`.
    ///
    /// Coerces the [`Ok`] variant of the original [`Result`] via [`DerefMut`](core::ops::DerefMut)
    /// and returns the new [`Result`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let mut s = "HELLO".to_string();
    /// let mut x: Result<String, u32> = Ok("hello".to_string());
    /// let y: Result<&mut str, &mut u32> = Ok(&mut s);
    /// assert_eq!(x.as_deref_mut().map(|x| { x.make_ascii_uppercase(); x }), y);
    ///
    /// let mut i = 42;
    /// let mut x: Result<String, u32> = Err(42);
    /// let y: Result<&mut str, &mut u32> = Err(&mut i);
    /// assert_eq!(x.as_deref_mut().map(|x| { x.make_ascii_uppercase(); x }), y);
    /// ```
    pub fn as_deref_mut(&mut self) -> Result<&mut T::Target, &mut E> {
        self.as_mut().map(|t| t.deref_mut())
    }
}

impl<T, E> Result<Option<T>, E> {
    /// Transposes a `Result` of an `Option` into an `Option` of a `Result`.
    ///
    /// `Ok(None)` will be mapped to `None`.
    /// `Ok(Some(_))` and `Err(_)` will be mapped to `Some(Ok(_))` and `Some(Err(_))`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// #[derive(Debug, Eq, PartialEq)]
    /// struct SomeErr;
    ///
    /// let x: Result<Option<i32>, SomeErr> = Ok(Some(5));
    /// let y: Option<Result<i32, SomeErr>> = Some(Ok(5));
    /// assert_eq!(x.transpose(), y);
    /// ```
    #[inline]
    pub fn transpose(self) -> Option<Result<T, E>> {
        match self {
            Ok(Some(x)) => Some(Ok(x)),
            Ok(None) => None,
            Err(e) => Some(Err(e)),
        }
    }
}

impl<T, E> Result<Result<T, E>, E> {
    /// Converts from `Result<Result<T, E>, E>` to `Result<T, E>`
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(result_flattening)]
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let x: Result<Result<&'static str, u32>, u32> = Ok(Ok("hello"));
    /// assert_eq!(Ok("hello"), x.flatten());
    ///
    /// let x: Result<Result<&'static str, u32>, u32> = Ok(Err(6));
    /// assert_eq!(Err(6), x.flatten());
    ///
    /// let x: Result<Result<&'static str, u32>, u32> = Err(6);
    /// assert_eq!(Err(6), x.flatten());
    /// ```
    ///
    /// Flattening only removes one level of nesting at a time:
    ///
    /// ```
    /// #![feature(result_flattening)]
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let x: Result<Result<Result<&'static str, u32>, u32>, u32> = Ok(Ok(Ok("hello")));
    /// assert_eq!(Ok(Ok("hello")), x.flatten());
    /// assert_eq!(Ok("hello"), x.flatten().flatten());
    /// ```
    #[inline]
    //#[unstable(feature = "result_flattening", issue = "70142")]
    pub fn flatten(self) -> Result<T, E> {
        self.and_then(convert::identity)
    }
}

impl<T> Result<T, T> {
    /// Returns the [`Ok`] value if `self` is `Ok`, and the [`Err`] value if
    /// `self` is `Err`.
    ///
    /// In other words, this function returns the value (the `T`) of a
    /// `Result<T, T>`, regardless of whether or not that result is `Ok` or
    /// `Err`.
    ///
    /// This can be useful in conjunction with APIs such as
    /// [`Atomic*::compare_exchange`], or [`slice::binary_search`], but only in
    /// cases where you don't care if the result was `Ok` or not.
    ///
    /// [`Atomic*::compare_exchange`]: core::sync::atomic::AtomicBool::compare_exchange
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(result_into_ok_or_err)]
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let ok: Result<u32, u32> = Ok(3);
    /// let err: Result<u32, u32> = Err(4);
    ///
    /// assert_eq!(ok.into_ok_or_err(), 3);
    /// assert_eq!(err.into_ok_or_err(), 4);
    /// ```
    #[inline]
    //#[unstable(feature = "result_into_ok_or_err", reason = "newly added", issue = "82223")]
    pub fn into_ok_or_err(self) -> T {
        match self {
            Ok(v) => v,
            Err(v) => v,
        }
    }
}

// This is a separate function to reduce the code size of the methods
#[inline(never)]
#[cold]
#[track_caller]
fn unwrap_failed(msg: &str, error: &dyn fmt::Debug) -> ! {
    panic!("{}: {:?}", msg, error)
}

/////////////////////////////////////////////////////////////////////////////
// Trait implementations
/////////////////////////////////////////////////////////////////////////////

impl<T: Clone, E: Clone> Clone for Result<T, E> {
    #[inline]
    fn clone(&self) -> Self {
        match self {
            Ok(x) => Ok(x.clone()),
            Err(x) => Err(x.clone()),
        }
    }

    #[inline]
    fn clone_from(&mut self, source: &Self) {
        match (self, source) {
            (Ok(to), Ok(from)) => to.clone_from(from),
            (Err(to), Err(from)) => to.clone_from(from),
            (to, from) => *to = from.clone(),
        }
    }
}

impl<T, E> IntoIterator for Result<T, E> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    /// Returns a consuming iterator over the possibly contained value.
    ///
    /// The iterator yields one value if the result is [`Result::Ok`], otherwise none.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let x: Result<u32, &str> = Ok(5);
    /// let v: Vec<u32> = x.into_iter().collect();
    /// assert_eq!(v, [5]);
    ///
    /// let x: Result<u32, &str> = Err("nothing!");
    /// let v: Vec<u32> = x.into_iter().collect();
    /// assert_eq!(v, []);
    /// ```
    #[inline]
    fn into_iter(self) -> IntoIter<T> {
        IntoIter { inner: self.ok() }
    }
}

impl<'a, T, E> IntoIterator for &'a Result<T, E> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<'a, T, E> IntoIterator for &'a mut Result<T, E> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> IterMut<'a, T> {
        self.iter_mut()
    }
}

/////////////////////////////////////////////////////////////////////////////
// The Result Iterators
/////////////////////////////////////////////////////////////////////////////

/// An iterator over a reference to the [`Ok`] variant of a [`Result`].
///
/// The iterator yields one value if the result is [`Ok`], otherwise none.
///
/// Created by [`Result::iter`].
#[derive(Debug)]
pub struct Iter<'a, T: 'a> {
    inner: Option<&'a T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        self.inner.take()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = if self.inner.is_some() { 1 } else { 0 };
        (n, Some(n))
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a T> {
        self.inner.take()
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {}

impl<T> FusedIterator for Iter<'_, T> {}

//#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<A> TrustedLen for Iter<'_, A> {}

impl<T> Clone for Iter<'_, T> {
    #[inline]
    fn clone(&self) -> Self {
        Iter { inner: self.inner }
    }
}

/// An iterator over a mutable reference to the [`Ok`] variant of a [`Result`].
///
/// Created by [`Result::iter_mut`].
#[derive(Debug)]
pub struct IterMut<'a, T: 'a> {
    inner: Option<&'a mut T>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<&'a mut T> {
        self.inner.take()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = if self.inner.is_some() { 1 } else { 0 };
        (n, Some(n))
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut T> {
        self.inner.take()
    }
}

impl<T> ExactSizeIterator for IterMut<'_, T> {}

impl<T> FusedIterator for IterMut<'_, T> {}

//#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<A> TrustedLen for IterMut<'_, A> {}

/// An iterator over the value in a [`Ok`] variant of a [`Result`].
///
/// The iterator yields one value if the result is [`Ok`], otherwise none.
///
/// This struct is created by the [`into_iter`] method on
/// [`Result`] (provided by the [`IntoIterator`] trait).
///
/// [`into_iter`]: IntoIterator::into_iter
#[derive(Clone, Debug)]
pub struct IntoIter<T> {
    inner: Option<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.inner.take()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = if self.inner.is_some() { 1 } else { 0 };
        (n, Some(n))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        self.inner.take()
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {}

impl<T> FusedIterator for IntoIter<T> {}

//#[unstable(feature = "trusted_len", issue = "37572")]
unsafe impl<A> TrustedLen for IntoIter<A> {}

/////////////////////////////////////////////////////////////////////////////
// FromIterator
/////////////////////////////////////////////////////////////////////////////

impl<A, E, V: FromIterator<A>> FromIterator<Result<A, E>> for Result<V, E> {
    /// Takes each element in the `Iterator`: if it is an `Err`, no further
    /// elements are taken, and the `Err` is returned. Should no `Err` occur, a
    /// container with the values of each `Result` is returned.
    ///
    /// Here is an example which increments every integer in a vector,
    /// checking for overflow:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let v = vec![1, 2];
    /// let res: Result<Vec<u32>, &'static str> = v.iter().map(|x: &u32|
    ///     x.checked_add(1).ok_or("Overflow!").into()
    /// ).collect();
    /// assert_eq!(res, Ok(vec![2, 3]));
    /// ```
    ///
    /// Here is another example that tries to subtract one from another list
    /// of integers, this time checking for underflow:
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let v = vec![1, 2, 0];
    /// let res: Result<Vec<u32>, &'static str> = v.iter().map(|x: &u32|
    ///     x.checked_sub(1).ok_or("Underflow!").into()
    /// ).collect();
    /// assert_eq!(res, Err("Underflow!"));
    /// ```
    ///
    /// Here is a variation on the previous example, showing that no
    /// further elements are taken from `iter` after the first `Err`.
    ///
    /// ```
    /// # use tres_result::{Result, Result::Err, Result::Ok};
    /// let v = vec![3, 2, 1, 10];
    /// let mut shared = 0;
    /// let res: Result<Vec<u32>, &'static str> = v.iter().map(|x: &u32| {
    ///     shared += x;
    ///     x.checked_sub(2).ok_or("Underflow!").into()
    /// }).collect();
    /// assert_eq!(res, Err("Underflow!"));
    /// assert_eq!(shared, 6);
    /// ```
    ///
    /// Since the third element caused an underflow, no further elements were taken,
    /// so the final value of `shared` is 6 (= `3 + 2 + 1`), not 16.
    #[inline]
    fn from_iter<I: IntoIterator<Item = Result<A, E>>>(iter: I) -> Result<V, E> {
        let mut error = None;

        let iter = iter.into_iter().scan((), |_, x| match x {
            Ok(x) => Some(x),
            Err(err) => {
                error = Some(err);
                None
            }
        });

        let v = V::from_iter(iter);

        match error {
            Some(err) => Err(err),
            None => Ok(v),
        }
    }
}
