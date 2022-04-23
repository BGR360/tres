# tres-result

This crate provides two things:

`tres_result::Traced`, a trait that enables an error value to be traced
as it propagates through different parts of the source code.

`tres_result::Result`, a drop-in substitute for
[`Result`](https://doc.rust-lang.org/core/result/enum.Result.html) that
allows tracking the propagation of `Traced` errors using the `?` operator.

#### License

<sup>
Licensed under either of <a href="LICENSE-APACHE">Apache License, Version
2.0</a> or <a href="LICENSE-MIT">MIT license</a> at your option.
</sup>

<br>

<sub>
Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this crate by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
</sub>
