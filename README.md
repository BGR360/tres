# tres

Effortless, low overhead error tracing in Rust.

Tres provides error traces with **no stack unwinding** and **no symbol
lookups**. All you need to do is wrap your error type(s) with `Traced<E>`
and make sure you use a `Result` type that supports return tracing.

See the documentation for more details.

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
