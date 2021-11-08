# tres-result

This crate provides two things:

`tres_result::Traced`, a trait that enables an error value to be traced
as it propagates through different parts of the source code.

`tres_result::Result`, a drop-in substitute for
[`Result`](https://doc.rust-lang.org/core/result/enum.Result.html) that
allows tracking the propagation of `Traced` errors using the `?` operator.
