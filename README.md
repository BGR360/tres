# tres

Effortless, low overhead error tracing in Rust.

Tres provides error traces with **no stack unwinding** and **no symbol
lookups**. All you need to do is wrap your error type(s) with `TracedError<E>`
and make sure you use a `Result` type that supports return tracing.

See the documentation for more details.
