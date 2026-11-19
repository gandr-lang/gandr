//! The names and the numbers that each signature of the crate is stated in.
//!
//! A symbol, a path, an LLVM type and a commit are all text, and a size, an
//! offset and an alignment are all integers. Each has its own type, so the
//! compiler refuses a swap of two of them.

use alloc::string::String;
use core::fmt;

/// Declares a transparent wrapper over one owned text, with its conversions
/// and its rendering.
macro_rules! text {
    (
        $(#[$attribute:meta])*
        $visibility:vis struct $name:ident;
    ) => {
        $(#[$attribute])*
        #[repr(transparent)]
        #[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        $visibility struct $name(String);

        impl From<String> for $name
        {
            /// Reads the text as this name.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: String) -> Self
            {
                Self(value)
            }
        }

        impl From<&str> for $name
        {
            /// Copies the text as this name.
            ///
            /// # Specification
            /// trivial.
            ///
            /// # Cost
            /// - allocation: the copy of the text, durable by the name
            #[inline]
            fn from(value: &str) -> Self
            {
                Self(String::from(value))
            }
        }

        impl AsRef<str> for $name
        {
            /// The text of the name.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn as_ref(&self) -> &str
            {
                &self.0
            }
        }

        impl fmt::Display for $name
        {
            /// Writes the text of the name.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn fmt(
                &self,
                f: &mut fmt::Formatter<'_>,
            ) -> fmt::Result
            {
                f.write_str(&self.0)
            }
        }
    };
}

/// Declares a transparent wrapper over one primitive integer, with its
/// conversions in both directions and its rendering.
macro_rules! number {
    (
        $(#[$attribute:meta])*
        $visibility:vis struct $name:ident($primitive:ty);
    ) => {
        $(#[$attribute])*
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        $visibility struct $name($primitive);

        impl From<$primitive> for $name
        {
            /// Reads the primitive as this quantity.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $primitive) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for $primitive
        {
            /// Reads the quantity back out as its primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $name) -> Self
            {
                value.0
            }
        }

        impl fmt::Display for $name
        {
            /// Writes the quantity through its primitive's rendering.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn fmt(
                &self,
                f: &mut fmt::Formatter<'_>,
            ) -> fmt::Result
            {
                fmt::Display::fmt(&self.0, f)
            }
        }
    };
}

text! {
    /// A function's path inside its crate, as `module::function`, with no
    /// crate name before it.
    pub struct FunctionPath;
}

text! {
    /// The name that rustc mints for a function under the v0 mangling.
    pub struct Symbol;
}

text! {
    /// An LLVM type as LLVM spells it: `i64`, `ptr`, `[2 x i64]` or
    /// `{ i64, i32 }`.
    pub struct LlvmType;
}

text! {
    /// A Rust type as rustc prints it.
    pub struct TypeName;
}

text! {
    /// A field's name: the declared name, or the index of a tuple's field.
    pub struct FieldName;
}

text! {
    /// An enum variant's declared name.
    pub struct VariantName;
}

text! {
    /// The commit of the Rust toolchain, as `rustc -vV` prints it.
    pub struct Commit;
}

text! {
    /// A target tuple, as `x86_64-unknown-linux-gnu`.
    pub struct Target;
}

number! {
    /// A count of bytes: a size, an offset, a stride or an alignment.
    pub struct Bytes(u64);
}

number! {
    /// How many values a niche leaves outside its valid range.
    pub struct Available(u128);
}

number! {
    /// A position in a record's canonical bytes.
    pub struct Offset(u64);
}

number! {
    /// The status that a process exited with.
    pub struct Status(i32);
}

text! {
    /// The path of a source file that the reader read, as UTF-8.
    pub struct SourcePath;
}
