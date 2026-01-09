#![doc = include_str!("../README.md")]

pub mod grapheme;
pub mod grapheme_owned;
pub mod graphemes;
#[allow(dead_code)]
pub(crate) mod modification;
pub mod normalization;

pub use grapheme::Grapheme;
pub use grapheme_macro::{g, gs};
pub use grapheme_owned::{GraphemeOwned, MaybeGraphemeOwned};
pub use graphemes::Graphemes;
pub use normalization::{Nfc, Nfd, Nfkc, Nfkd, Unnormalized};

/// Commonly used functions, traits and types.
pub mod prelude {
    pub use super::{
        Grapheme, GraphemeOwned, Graphemes, MaybeGraphemeOwned, Nfc, Nfd, Nfkc, Nfkd, Unnormalized,
        g, gs,
    };
}
