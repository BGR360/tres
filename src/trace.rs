use core::{fmt, panic};

/// A trait for types that store an error trace.
pub trait ErrorTrace {
    /// Appends a code location to the error trace.
    fn append_location(&mut self, location: &'static panic::Location);
}

/// A simple vector of Rust code locations.
#[derive(Clone, Default, PartialEq, Eq)]
pub struct Locations(pub Vec<&'static panic::Location<'static>>);

impl ErrorTrace for Locations {
    fn append_location(&mut self, location: &'static panic::Location) {
        self.0.push(location);
    }
}

impl fmt::Display for Locations {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Self as fmt::Debug>::fmt(self, f)
    }
}

impl fmt::Debug for Locations {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list()
            .entries(self.0.iter().map(|loc| LocationPrinter(loc)))
            .finish()
    }
}

struct LocationPrinter(&'static panic::Location<'static>);

impl fmt::Debug for LocationPrinter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}:{}", self.0.file(), self.0.line(), self.0.column())
    }
}
