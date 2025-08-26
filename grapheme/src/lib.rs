#![doc = include_str!("../README.md")]

pub mod grapheme;
pub mod graphemes;

pub use grapheme::Grapheme;
pub use grapheme_macro::{g, gs};
pub use graphemes::Graphemes;

/// Commonly used functions, traits and types.
pub mod prelude {
    pub use super::{Grapheme, Graphemes, g, gs};
}
