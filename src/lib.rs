//! Effortless, low overhead error tracing in Rust.
//!
//! Tres provides error traces with **no stack unwinding** and **no symbol
//! lookups**. All you need to do is wrap your error type(s) with
//! [`Traced<E>`] and make sure you use a `Result` type that
//! [supports return tracing](#how-it-works).
//!
//! # Usage
//!
//! Consider the following two "crates" with their respective error types:
//!
//! ```
//! mod crate_one {
//! #   use super::crate_two;
//!     #[derive(Debug)]
//!     pub enum Error {
//!         FileTooLarge {
//!             size: u64
//!         },
//!         CrateTwo(crate_two::Error),
//!     }
//!
//!     impl From<crate_two::Error> for Error {
//!         fn from(error: crate_two::Error) -> Self {
//!             Self::CrateTwo(error)
//!         }
//!     }
//!
//!     pub fn foo() -> Result<(), Error> {
//!         let size = crate_two::file_size("foo.txt")?;
//!         if size > 1024 {
//!             return Err(Error::FileTooLarge { size });
//!         }
//!         Ok(())
//!     }
//! }
//!
//! mod crate_two {
//!     #[derive(Debug)]
//!     pub struct Error(pub std::io::Error);
//!
//!     impl From<std::io::Error> for Error {
//!         fn from(error: std::io::Error) -> Self {
//!             Self(error)
//!         }
//!     }
//!
//!     pub fn file_size(filename: &str) -> Result<u64, Error> {
//!         let size = std::fs::File::open(filename)?
//!             .metadata()?
//!             .len();
//!         Ok(size)
//!     }
//! }
//! # fn main() {}
//! ```
//!
//! Converting the code to provide error traces can be done in a few simple
//! steps:
//!
//! * Replace all `Result<_, E>` with `Result<_, Traced<E>>`
//! * Use [`ErrorExt::traced()`] in all places where a new error is returned.
//!
//! And that's it! Any existing type conversions that were happening as a result
//! of the `?` operator will continue to work after switching over to `tres`.
//!
//! Here's what the final result looks like:
//!
//! ```
//! # use tres::{Err, Ok, Result};
//! mod crate_one {
//! #   use super::crate_two;
//! #   use tres::{Err, Ok, Result};
//!     use tres::{ErrorExt, Traced};
//!
//!     /* ... */
//! #   #[derive(Debug)]
//! #   pub enum Error {
//! #       FileTooLarge {
//! #           size: u64
//! #       },
//! #       CrateTwo(crate_two::Error),
//! #   }
//! #   impl From<crate_two::Error> for Error {
//! #       fn from(error: crate_two::Error) -> Self {
//! #           Self::CrateTwo(error)
//! #       }
//! #   }
//!
//!     // Result uses `Traced`.
//!     pub fn foo() -> Result<(), Traced<Error>> {
//!         // `?` operator converts `Traced<crate_two::Error>` to `Traced<Error>`!
//!         let size = crate_two::file_size("foo.txt")?;
//!         if size > 1024 {
//!             // `ErrorExt::traced()` converts `Error` to `Traced<Error>`.
//!             return Err(Error::FileTooLarge { size }.traced());
//!         }
//!         Ok(())
//!     }
//! }
//!
//! mod crate_two {
//! #   use tres::{Err, Ok, Result};
//!     use tres::Traced;
//!
//!     /* ... */
//! #   #[derive(Debug)]
//! #   pub struct Error(pub std::io::Error);
//! #   impl From<std::io::Error> for Error {
//! #       fn from(error: std::io::Error) -> Self {
//! #           Self(error)
//! #       }
//! #   }
//!
//!     // Result uses `Traced`.
//!     pub fn file_size(filename: &str) -> Result<u64, Traced<Error>> {
//!         // `?` operator converts `std::io::Error` to `Traced<Error>`!
//!         let size = std::fs::File::open(filename)?
//!             .metadata()?
//!             .len();
//!         Ok(size)
//!     }
//! }
//! # fn main() {}
//! ```
//!
//! And if we run that code...
//!
//! ```no_run
//! # #[allow(clippy::needless_doctest_main)]
//! # mod crate_one {
//! #   use tres::Traced;
//! #   pub fn foo() -> Result<(), Traced<()>> { Ok(()) }
//! # }
//! fn main() {
//!     let error = crate_one::foo().unwrap_err();
//!     println!("{:?}", error);
//! }
//! ```
//!
//! We get the output below, complete with an error trace!
//!
//! ```text
//! CrateTwo(Error(Os { code: 2, kind: NotFound, message: "No such file or directory" })):
//! [src/lib.rs:51:20, src/lib.rs:26:20]
//! ```
//!
//! # Caveat: Remember to propagate!
//!
//! The error trace inside a [`Traced`] is appended to **only** when
//! propagated using the try (`?`) operator. Because of this, it is important to
//! ensure that all results in your code are propagated using the try operator,
//! otherwise your error traces may end up missing certain locations.
//!
//! This can be avoided by ensuring that all return values are surrounded by
//! `Ok(..?)`:
//!
//! ```
//! # use tres::Traced;
//! fn gives_error() -> Result<(), Traced<&'static str>> {
//!     Err(Traced::new("Oops!"))
//! }
//!
//! fn foo() -> Result<(), Traced<&'static str>> {
//!     // !! NO !!
//!     gives_error()
//! }
//!
//! fn bar() -> Result<(), Traced<&'static str>> {
//!     // !! YES !!
//!     Ok(gives_error()?)
//! }
//! ```
//!
//! TODO: implement a lint to detect missing `Ok(..?)`.
//!
//! Another option is to make use of [try blocks]. This makes it impossible to
//! accidentally return a bare result without propagating it.
//!
//! [try blocks]:
//! https://doc.rust-lang.org/beta/unstable-book/language-features/try-blocks.html
//!
//! ```
//! #![feature(try_blocks)]
//! # use tres::Traced;
//! # fn gives_error() -> Result<(), Traced<&'static str>> {
//! #     Err(Traced::new("Oops!"))
//! # }
//! fn foo() -> Result<(), Traced<&'static str>> {
//!     try {
//!         gives_error()?
//!     }
//! }
//! ```
//!
//! ```compile_fail
//! #![feature(try_blocks)]
//! # use tres::Traced;
//! # fn gives_error() -> Result<(), Traced<&'static str>> {
//! #     Err(Traced::new("Oops!"))
//! # }
//! fn bar() -> Result<(), Traced<&'static str>> {
//!     try {
//!         // Does not compile without `?` operator!
//!         gives_error()
//!     }
//! }
//! ```
//!
//! # How it works
//!
//! The error tracing behavior of `tres` is made possible by specializing the
//! `Result` type's behavior during try-propagation (`?` operator). When the
//! `Err` variant of the result supports tracing (as indicated by the presence
//! of the [`Trace`][tres_result::Trace] trait), each invocation of the `?`
//! operator calls [`Trace::trace()`][tres_result::Trace::trace] on the error
//! with the location of the `?` invocation.
//!
//! For now, this behavior must be provided by a third party `Result` type. The
//! [`tres-result`][tres_result] crate provides one; it is included in `tres` as
//! [`Result`].
//!
//! Eventually, this crate is meant to be used with the standard library
//! `Result` type. There will likely be an RFC to add a `Traced` trait to the
//! standard library and specialize the behavior or [`core::result::Result`] in
//! the same way that [`tres_result::Result`] is specialized.

#![feature(auto_traits)]
#![feature(min_specialization)]
#![feature(negative_impls)]

pub use tres_result as result;

pub mod error;
mod trace;

#[doc(inline)]
pub use error::ErrorExt;
pub use result::Result;
pub use result::Result::{Err, Ok};
pub use trace::{Locations, Trace};

/// Alias to [`Traced<E, T>`] that uses a vector of locations for its trace.
///
/// If you want to use your own trace type, use [`Traced<E, T>`].
///
/// [`Traced<E, T>`]: error::Traced
pub type Traced<E> = error::Traced<E, Locations>;
