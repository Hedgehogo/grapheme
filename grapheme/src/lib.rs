#![doc = include_str!("../README.md")]

pub mod grapheme;
pub mod grapheme_owned;
pub mod graphemes;
pub(crate) mod modification;

pub use grapheme::Grapheme;
pub use grapheme_macro::{g, gs};
pub use grapheme_owned::{GraphemeOwned, MaybeGraphemeOwned};
pub use graphemes::Graphemes;

pub(crate) use modification::{Modification, to_modified};

/// Commonly used functions, traits and types.
pub mod prelude {
    pub use super::{Grapheme, GraphemeOwned, Graphemes, MaybeGraphemeOwned, g, gs};
}
