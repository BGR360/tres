//! This crate provides two things:
//!
//! [`tres_result::Traced`], a trait that enables an error value to be traced as
//! it propagates through different parts of the source code.
//!
//! [`tres_result::Result`], a drop-in substitute for [`Result`] that allows
//! tracking the propagation of [`Traced`] errors using the `?` operator.
//!
//! [`tres_result::Traced`]: crate::Traced
//! [`tres_result::Result`]: crate::Result
//! [`Result`]: core::result::Result

#![feature(min_specialization)]
#![feature(rustc_attrs)]
#![feature(try_trait_v2)]
// Needed in order to implement certain unstable apis on [`Result`].
#![feature(never_type, trusted_len)]
#![warn(unsafe_op_in_unsafe_fn)]

// TODO:
// * Add crate features to correspond to the core Result features.

mod result;
mod traced;

#[doc(inline)]
pub use result::Result;
#[doc(inline)]
pub use traced::Traced;
