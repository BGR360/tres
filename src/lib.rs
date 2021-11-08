//! Effortless, low overhead error tracing in Rust.

#![feature(min_specialization)]

pub use tres_result as result;

pub mod error;
mod trace;

pub use result::{Result, Result::Err, Result::Ok};
pub use trace::{ErrorTrace, Locations};

/// Alias to [`TracedError<E, T>`] that uses a vector of locations for its trace.
///
/// If you want to use your own trace type, use [`TracedError<E, T>`].
///
/// [`TracedError<E, T>`]: error::TracedError
pub type TracedError<E> = error::TracedError<E, Locations>;
