//! Utilities for the `Grapheme` type.
//!
//! *[See also the `Grapheme` type.](Grapheme)*

use crate::{GraphemeOwned, Modification, to_modified};
use std::{
    cmp::PartialEq,
    fmt,
    hash::Hash,
    str::{Bytes, Chars},
};
use ucd::Codepoint;
use unicode_normalization::UnicodeNormalization;
use unicode_segmentation::UnicodeSegmentation;

/// The `Grapheme` type represents a single character. More specifically, since
/// ‘character’ isn’t a well-defined concept in Unicode, `Grapheme` is a
/// ‘extended Unicode grapheme cluster’. It's something between `str` and
/// `char`.  Like `char`, it is a type representing a single unit of text and
/// therefore has methods such as [`is_whitespace`].  But just like `str`, it
/// is a type of dynamic size and is more often found in the borrowed form of
/// `&Grapheme`. It contains a slice of a string, and it can also contain
/// smaller graphemes inside itself.
///
/// [`is_whitespace`]: #method.is_whitespace
///
/// # Basic Usage
///
/// Grapheme literals are string slices:
/// ```
/// # use grapheme::prelude::*;
/// let h = g!("h");
/// ```
///
/// Here we have declared a grapheme initialized with a grapheme literal.
/// Grapheme literals have a static lifetime, which means the grapheme `h` is
/// guaranteed to be valid for the duration of the entire program. We can
/// explicitly specify `h`’s lifetime as well:
/// ```
/// # use grapheme::prelude::*;
/// let h: &'static Grapheme = g!("h");
/// ```
///
/// # Validity and Layout
///
/// A `Grapheme` is a ‘extended Unicode grapheme cluster’. Its size in memory
/// is unlimited.
///
/// No `Grapheme` may be constructed, whether as a literal or at runtime, that
/// is not a single extended Unicode grapheme cluster. Violating this rule
/// leads to undefined behavior.
///
/// ```compile_fail
/// # use grapheme::prelude::*;
/// [g!(100), g!("ab")];
/// ```
///
/// ```should_panic
/// # use grapheme::prelude::*;
/// Grapheme::from_code_points("ab").unwrap();
/// ```
///
/// ```no_run
/// # use grapheme::prelude::*;
/// // Undefined behavior
/// let _ = unsafe { Grapheme::from_code_points_unchecked("ab") };
/// ```
///
/// # Representation
/// A `&Grapheme` is made up of two components: a pointer to some bytes, and a
/// length. You can look at these with the `as_str` and `len` methods:
///
/// ```
/// # use grapheme::prelude::*;
/// use std::slice;
/// use std::str;
///
/// let strange = g!("y̆");
///
/// let ptr = strange.as_str().as_ptr();
/// let len = strange.len();
///
/// // strange has nineteen bytes
/// assert_eq!(3, len);
///
/// // We can re-build a grapheme out of ptr and len. This is all unsafe because
/// // we are responsible for making sure the two components are valid:
/// let g = unsafe {
///     // First, we build a &[u8]...
///     let slice = slice::from_raw_parts(ptr, len);
///
///     // ... and then convert that slice into a string slice
///     str::from_utf8(slice).ok().and_then(Grapheme::from_code_points)
/// };
///
/// assert_eq!(g, Some(strange));
/// ```
#[derive(Eq)]
#[repr(transparent)]
pub struct Grapheme(str);

impl Grapheme {
    /// Converts a `&str` to a `&Grapheme`.
    ///
    /// Note that all `Grapheme`s are valid [`str`]s, and can be cast to one with [`as_str`]:
    /// ```
    /// # use grapheme::prelude::*;
    /// let g = g!('💯');
    /// let s = g.as_str();
    ///
    /// assert_eq!("💯", s);
    /// ```
    ///
    /// However, the reverse is not true: not all valid [`str`]s are valid
    /// `Grapheme`s. `from_str_unchecked()` will return `None` if the input is not a valid value
    /// for a `Grapheme`.
    ///
    /// For an unsafe version of this function which ignores these checks, see
    /// [`from_u32_unchecked`].
    ///
    /// [`as_str`]: #method.as_str
    /// [`from_u32_unchecked`]: #method.from_u32_unchecked
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let c = Grapheme::from_code_points("❤");
    ///
    /// assert_eq!(Some(g!('❤')), c);
    /// ```
    ///
    /// Returning `None` when the input is not a valid `Grapheme`:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let c = Grapheme::from_code_points("ab");
    ///
    /// assert_eq!(None, c);
    /// ```
    #[must_use]
    #[inline]
    #[doc(alias = "from_chars", alias = "from_usvs", alias = "from_str")]
    pub fn from_code_points(value: &str) -> Option<&Self> {
        let mut iter = value.graphemes(true);
        matches!((iter.next(), iter.next()), (Some(_), None))
            .then(|| unsafe { Self::from_code_points_unchecked(value) })
    }

    /// Converts a `&str` to a `&Grapheme`, ignoring validity.
    ///
    /// Note that all `Grapheme`s are valid [`str`]s, and can be cast to one with [`as_str`]:
    /// ```
    /// # use grapheme::prelude::*;
    /// let g = g!('💯');
    /// let s = g.as_str();
    ///
    /// assert_eq!("💯", s);
    /// ```
    ///
    /// However, the reverse is not true: not all valid [`str`]s are valid
    /// `Grapheme`s. `from_str_unchecked()` will ignore this, and blindly cast to
    /// `Grapheme`, possibly creating an invalid one.
    ///
    /// [`as_str`]: #method.as_str
    ///
    /// # Safety
    ///
    /// This function is unsafe, as it may construct invalid `Grapheme` values.
    ///
    /// For a safe version of this function, see the [`from_str`] function.
    ///
    /// [`from_str`]: #method.from_str
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let c = unsafe { Grapheme::from_code_points_unchecked("❤") };
    ///
    /// assert_eq!(g!('❤'), c);
    /// ```
    #[must_use]
    #[inline]
    #[doc(
        alias = "from_chars_unchecked",
        alias = "from_str_unchecked",
        alias = "from_usvs_unchecked"
    )]
    pub const unsafe fn from_code_points_unchecked(value: &str) -> &Self {
        // SAFETY: This is ok because Grapheme is #[repr(transparent)]
        unsafe { &*(value as *const str as *const Self) }
    }

    /// Returns the number of bytes this `Grapheme` would need if encoded in UTF-8.
    ///
    /// That number of bytes is always greater than 0.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let len = g!('A').len();
    /// assert_eq!(len, 1);
    ///
    /// let len = g!('ß').len();
    /// assert_eq!(len, 2);
    ///
    /// let len = g!('ℝ').len();
    /// assert_eq!(len, 3);
    ///
    /// let len = g!('💣').len();
    /// assert_eq!(len, 4);
    /// ```
    ///
    /// The `&Graphemes` type guarantees that its contents are UTF-8, and so we can compare the length it
    /// would take if each code point was represented as a `&Grapheme` vs in the `&Graphemes` itself:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// // as graphemes
    /// let eastern = g!('東');
    /// let capital = g!('京');
    ///
    /// // both can be represented as three bytes
    /// assert_eq!(3, eastern.len());
    /// assert_eq!(3, capital.len());
    ///
    /// // as a &str, these two are encoded in UTF-8
    /// let tokyo = gs!("東京");
    ///
    /// let len = eastern.len() + capital.len();
    ///
    /// // we can see that they take six bytes total...
    /// assert_eq!(6, tokyo.len());
    ///
    /// // ... just like the &str
    /// assert_eq!(len, tokyo.len());
    /// ```
    #[expect(clippy::len_without_is_empty)]
    #[must_use]
    #[inline]
    #[doc(alias = "len_utf8")]
    pub const fn len(&self) -> usize {
        self.as_str().len()
    }

    /// Checks if a `Grapheme` is a digit in the given radix.
    ///
    /// A 'radix' here is sometimes also called a 'base'. A radix of two
    /// indicates a binary number, a radix of ten, decimal, and a radix of
    /// sixteen, hexadecimal, to give some common values. Arbitrary
    /// radices are supported.
    ///
    /// Compared to [`is_numeric()`], this function only recognizes the characters
    /// `0-9`, `a-z` and `A-Z`.
    ///
    /// 'Digit' is defined to be only the following characters:
    ///
    /// * `0-9`
    /// * `a-z`
    /// * `A-Z`
    ///
    /// For a more comprehensive understanding of 'digit', see [`is_numeric()`].
    ///
    /// [`is_numeric()`]: #method.is_numeric
    ///
    /// # Panics
    ///
    /// Panics if given a radix smaller than 2 or larger than 36.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// assert!(g!('1').is_digit(10));
    /// assert!(g!('f').is_digit(16));
    /// assert!(!g!('f').is_digit(10));
    /// ```
    ///
    /// Passing a large radix, causing a panic:
    ///
    /// ```should_panic
    /// # use grapheme::prelude::*;
    /// // this panics
    /// g!('1').is_digit(37);
    /// ```
    ///
    /// Passing a small radix, causing a panic:
    ///
    /// ```should_panic
    /// # use grapheme::prelude::*;
    /// // this panics
    /// g!('1').is_digit(1);
    /// ```
    #[inline]
    pub fn is_digit(&self, radix: u32) -> bool {
        self.to_code_point().is_some_and(|c| c.is_digit(radix))
    }

    /// Converts a `Grapheme` to a digit in the given radix.
    ///
    /// A 'radix' here is sometimes also called a 'base'. A radix of two
    /// indicates a binary number, a radix of ten, decimal, and a radix of
    /// sixteen, hexadecimal, to give some common values. Arbitrary
    /// radices are supported.
    ///
    /// 'Digit' is defined to be only the following characters:
    ///
    /// * `0-9`
    /// * `a-z`
    /// * `A-Z`
    ///
    /// # Errors
    ///
    /// Returns `None` if the `Grapheme` does not refer to a digit in the given radix.
    ///
    /// # Panics
    ///
    /// Panics if given a radix smaller than 2 or larger than 36.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// assert_eq!(g!('1').to_digit(10), Some(1));
    /// assert_eq!(g!('f').to_digit(16), Some(15));
    /// ```
    ///
    /// Passing a non-digit results in failure:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// assert_eq!(g!('f').to_digit(10), None);
    /// assert_eq!(g!('z').to_digit(16), None);
    /// ```
    ///
    /// Passing a large radix, causing a panic:
    ///
    /// ```should_panic
    /// # use grapheme::prelude::*;
    /// // this panics
    /// let _ = g!('1').to_digit(37);
    /// ```
    /// Passing a small radix, causing a panic:
    ///
    /// ```should_panic
    /// # use grapheme::prelude::*;
    /// // this panics
    /// let _ = g!('1').to_digit(1);
    /// ```
    #[inline]
    pub fn to_digit(&self, radix: u32) -> Option<u32> {
        self.to_code_point().and_then(|c| c.to_digit(radix))
    }

    /// Returns `true` if all code points inside are `Alphabetic`, or diacritics.
    ///
    /// `Alphabetic` is described in Chapter 4 (Character Properties) of the [Unicode Standard] and
    /// specified in the [Unicode Character Database][ucd] [`DerivedCoreProperties.txt`].
    ///
    /// [Unicode Standard]: https://www.unicode.org/versions/latest/
    /// [ucd]: https://www.unicode.org/reports/tr44/
    /// [`DerivedCoreProperties.txt`]: https://www.unicode.org/Public/UCD/latest/ucd/DerivedCoreProperties.txt
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// assert!(g!('a').is_alphabetic());
    /// assert!(g!('京').is_alphabetic());
    /// assert!(g!("y̆").is_alphabetic());
    /// assert!(g!("yͧ").is_alphabetic());
    ///
    /// let c = g!('💝');
    /// // love is many things, but it is not alphabetic
    /// assert!(!c.is_alphabetic());
    /// ```
    #[inline]
    pub fn is_alphabetic(&self) -> bool {
        match to_modified(self) {
            Some((grapheme, modification)) => {
                (match modification {
                    Modification::Extend(c) => c.is_diacritic() || c.is_alphabetic(),
                    Modification::SpacingMark(c) => c.is_diacritic() || c.is_alphabetic(),
                    Modification::Prepend(c) => c.is_diacritic() || c.is_alphabetic(),
                    _ => false,
                }) && grapheme.is_alphabetic()
            }

            _ => self.code_points().all(char::is_alphabetic),
        }
    }

    /// Returns `true` if this `Grapheme` satisfies either [`is_alphabetic()`] or [`is_numeric()`].
    ///
    /// [`is_alphabetic()`]: #method.is_alphabetic
    /// [`is_numeric()`]: #method.is_numeric
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// assert!(g!('٣').is_alphanumeric());
    /// assert!(g!('7').is_alphanumeric());
    /// assert!(g!('৬').is_alphanumeric());
    /// assert!(g!('¾').is_alphanumeric());
    /// assert!(g!('①').is_alphanumeric());
    /// assert!(g!('K').is_alphanumeric());
    /// assert!(g!('و').is_alphanumeric());
    /// assert!(g!('藏').is_alphanumeric());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_alphanumeric(&self) -> bool {
        self.is_numeric() || self.is_alphabetic()
    }

    /// Returns `true` if all code points has one of the general categories for numbers.
    ///
    /// The general categories for numbers (`Nd` for decimal digits, `Nl` for letter-like numeric
    /// characters, and `No` for other numeric characters) are specified in the [Unicode Character
    /// Database][ucd] [`UnicodeData.txt`].
    ///
    /// This method doesn't cover everything that could be considered a number, e.g. ideographic numbers like '三'.
    /// If you want everything including characters with overlapping purposes then you might want to use
    /// a unicode or language-processing library that exposes the appropriate character properties instead
    /// of looking at the unicode categories.
    ///
    /// If you want to parse ASCII decimal digits (0-9) or ASCII base-N, use
    /// `is_ascii_digit` or `is_digit` instead.
    ///
    /// [Unicode Standard]: https://www.unicode.org/versions/latest/
    /// [ucd]: https://www.unicode.org/reports/tr44/
    /// [`UnicodeData.txt`]: https://www.unicode.org/Public/UCD/latest/ucd/UnicodeData.txt
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// assert!(g!('٣').is_numeric());
    /// assert!(g!('7').is_numeric());
    /// assert!(g!('৬').is_numeric());
    /// assert!(g!('¾').is_numeric());
    /// assert!(g!('①').is_numeric());
    /// assert!(!g!('K').is_numeric());
    /// assert!(!g!('و').is_numeric());
    /// assert!(!g!('藏').is_numeric());
    /// assert!(!g!('三').is_numeric());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_numeric(&self) -> bool {
        self.code_points().all(char::is_numeric)
    }

    /// Returns `true` if all code points have the `White_Space` property.
    ///
    /// `White_Space` is specified in the [Unicode Character Database][ucd] [`PropList.txt`].
    ///
    /// [ucd]: https://www.unicode.org/reports/tr44/
    /// [`PropList.txt`]: https://www.unicode.org/Public/UCD/latest/ucd/PropList.txt
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// assert!(g!(' ').is_whitespace());
    ///
    /// // line break
    /// assert!(g!('\n').is_whitespace());
    ///
    /// // a non-breaking space
    /// assert!(g!('\u{A0}').is_whitespace());
    ///
    /// assert!(!g!('越').is_whitespace());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_whitespace(&self) -> bool {
        self.code_points().all(char::is_whitespace)
    }

    /// Returns `true` if the only code point in this `Grapheme` has the general category for
    /// control codes.
    ///
    /// Control codes (code points with the general category of `Cc`) are described in Chapter 4
    /// (Character Properties) of the [Unicode Standard] and specified in the [Unicode Character
    /// Database][ucd] [`UnicodeData.txt`].
    ///
    /// [Unicode Standard]: https://www.unicode.org/versions/latest/
    /// [ucd]: https://www.unicode.org/reports/tr44/
    /// [`UnicodeData.txt`]: https://www.unicode.org/Public/UCD/latest/ucd/UnicodeData.txt
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// // U+009C, STRING TERMINATOR
    /// assert!(g!('').is_control());
    /// assert!(!g!('q').is_control());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_control(&self) -> bool {
        self.as_str() == "\r\n" || self.to_code_point().is_some_and(char::is_control)
    }

    /// Checks if the value is within the ASCII range.
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let ascii = g!('a');
    /// let non_ascii = g!('❤');
    ///
    /// assert!(ascii.is_ascii());
    /// assert!(!non_ascii.is_ascii());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_ascii(&self) -> bool {
        self.to_code_point().is_some_and(|c| c.is_ascii())
    }

    /// Checks if the value is an ASCII alphabetic character:
    ///
    /// - U+0041 'A' ..= U+005A 'Z', or
    /// - U+0061 'a' ..= U+007A 'z'.
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let uppercase_a = g!('A');
    /// let uppercase_g = g!('G');
    /// let a = g!('a');
    /// let g = g!('g');
    /// let zero = g!('0');
    /// let percent = g!('%');
    /// let space = g!(' ');
    /// let lf = g!('\n');
    /// let esc = g!('\x1b');
    ///
    /// assert!(uppercase_a.is_ascii_alphabetic());
    /// assert!(uppercase_g.is_ascii_alphabetic());
    /// assert!(a.is_ascii_alphabetic());
    /// assert!(g.is_ascii_alphabetic());
    /// assert!(!zero.is_ascii_alphabetic());
    /// assert!(!percent.is_ascii_alphabetic());
    /// assert!(!space.is_ascii_alphabetic());
    /// assert!(!lf.is_ascii_alphabetic());
    /// assert!(!esc.is_ascii_alphabetic());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_ascii_alphabetic(&self) -> bool {
        self.to_code_point()
            .is_some_and(|c| c.is_ascii_alphabetic())
    }

    /// Checks if the value is an ASCII alphanumeric character:
    ///
    /// - U+0041 'A' ..= U+005A 'Z', or
    /// - U+0061 'a' ..= U+007A 'z', or
    /// - U+0030 '0' ..= U+0039 '9'.
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let uppercase_a = g!('A');
    /// let uppercase_g = g!('G');
    /// let a = g!('a');
    /// let g = g!('g');
    /// let zero = g!('0');
    /// let percent = g!('%');
    /// let space = g!(' ');
    /// let lf = g!('\n');
    /// let esc = g!('\x1b');
    ///
    /// assert!(uppercase_a.is_ascii_alphanumeric());
    /// assert!(uppercase_g.is_ascii_alphanumeric());
    /// assert!(a.is_ascii_alphanumeric());
    /// assert!(g.is_ascii_alphanumeric());
    /// assert!(zero.is_ascii_alphanumeric());
    /// assert!(!percent.is_ascii_alphanumeric());
    /// assert!(!space.is_ascii_alphanumeric());
    /// assert!(!lf.is_ascii_alphanumeric());
    /// assert!(!esc.is_ascii_alphanumeric());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_ascii_alphanumeric(&self) -> bool {
        self.to_code_point()
            .is_some_and(|c| c.is_ascii_alphanumeric())
    }

    /// Checks if the value is an ASCII decimal digit:
    /// U+0030 '0' ..= U+0039 '9'.
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let uppercase_a = g!('A');
    /// let uppercase_g = g!('G');
    /// let a = g!('a');
    /// let g = g!('g');
    /// let zero = g!('0');
    /// let percent = g!('%');
    /// let space = g!(' ');
    /// let lf = g!('\n');
    /// let esc = g!('\x1b');
    ///
    /// assert!(!uppercase_a.is_ascii_digit());
    /// assert!(!uppercase_g.is_ascii_digit());
    /// assert!(!a.is_ascii_digit());
    /// assert!(!g.is_ascii_digit());
    /// assert!(zero.is_ascii_digit());
    /// assert!(!percent.is_ascii_digit());
    /// assert!(!space.is_ascii_digit());
    /// assert!(!lf.is_ascii_digit());
    /// assert!(!esc.is_ascii_digit());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_ascii_digit(&self) -> bool {
        self.to_code_point().is_some_and(|c| c.is_ascii_digit())
    }

    /// Checks if the value is an ASCII punctuation character:
    ///
    /// - U+0021 ..= U+002F `! " # $ % & ' ( ) * + , - . /`, or
    /// - U+003A ..= U+0040 `: ; < = > ? @`, or
    /// - U+005B ..= U+0060 ``[ \ ] ^ _ ` ``, or
    /// - U+007B ..= U+007E `{ | } ~`
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let uppercase_a = g!('A');
    /// let uppercase_g = g!('G');
    /// let a = g!('a');
    /// let g = g!('g');
    /// let zero = g!('0');
    /// let percent = g!('%');
    /// let space = g!(' ');
    /// let lf = g!('\n');
    /// let esc = g!('\x1b');
    ///
    /// assert!(!uppercase_a.is_ascii_punctuation());
    /// assert!(!uppercase_g.is_ascii_punctuation());
    /// assert!(!a.is_ascii_punctuation());
    /// assert!(!g.is_ascii_punctuation());
    /// assert!(!zero.is_ascii_punctuation());
    /// assert!(percent.is_ascii_punctuation());
    /// assert!(!space.is_ascii_punctuation());
    /// assert!(!lf.is_ascii_punctuation());
    /// assert!(!esc.is_ascii_punctuation());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_ascii_punctuation(&self) -> bool {
        self.to_code_point()
            .is_some_and(|c| c.is_ascii_punctuation())
    }

    /// Checks if the value is an ASCII graphic character:
    /// U+0021 '!' ..= U+007E '~'.
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let uppercase_a = g!('A');
    /// let uppercase_g = g!('G');
    /// let a = g!('a');
    /// let g = g!('g');
    /// let zero = g!('0');
    /// let percent = g!('%');
    /// let space = g!(' ');
    /// let lf = g!('\n');
    /// let esc = g!('\x1b');
    ///
    /// assert!(uppercase_a.is_ascii_graphic());
    /// assert!(uppercase_g.is_ascii_graphic());
    /// assert!(a.is_ascii_graphic());
    /// assert!(g.is_ascii_graphic());
    /// assert!(zero.is_ascii_graphic());
    /// assert!(percent.is_ascii_graphic());
    /// assert!(!space.is_ascii_graphic());
    /// assert!(!lf.is_ascii_graphic());
    /// assert!(!esc.is_ascii_graphic());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_ascii_graphic(&self) -> bool {
        self.code_points().any(|c| c.is_ascii_graphic())
    }

    /// Checks if the value is an ASCII whitespace character:
    /// U+0020 SPACE, U+0009 HORIZONTAL TAB, U+000A LINE FEED,
    /// U+000C FORM FEED, or U+000D CARRIAGE RETURN.
    ///
    /// Rust uses the WhatWG Infra Standard's [definition of ASCII
    /// whitespace][infra-aw]. There are several other definitions in
    /// wide use. For instance, [the POSIX locale][pct] includes
    /// U+000B VERTICAL TAB as well as all the above characters,
    /// but—from the very same specification—[the default rule for
    /// "field splitting" in the Bourne shell][bfs] considers *only*
    /// SPACE, HORIZONTAL TAB, and LINE FEED as whitespace.
    ///
    /// If you are writing a program that will process an existing
    /// file format, check what that format's definition of whitespace is
    /// before using this function.
    ///
    /// [infra-aw]: https://infra.spec.whatwg.org/#ascii-whitespace
    /// [pct]: https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap07.html#tag_07_03_01
    /// [bfs]: https://pubs.opengroup.org/onlinepubs/9699919799/utilities/V3_chap02.html#tag_18_06_05
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let uppercase_a = g!('A');
    /// let uppercase_g = g!('G');
    /// let a = g!('a');
    /// let g = g!('g');
    /// let zero = g!('0');
    /// let percent = g!('%');
    /// let space = g!(' ');
    /// let lf = g!('\n');
    /// let esc = g!('\x1b');
    ///
    /// assert!(!uppercase_a.is_ascii_whitespace());
    /// assert!(!uppercase_g.is_ascii_whitespace());
    /// assert!(!a.is_ascii_whitespace());
    /// assert!(!g.is_ascii_whitespace());
    /// assert!(!zero.is_ascii_whitespace());
    /// assert!(!percent.is_ascii_whitespace());
    /// assert!(space.is_ascii_whitespace());
    /// assert!(lf.is_ascii_whitespace());
    /// assert!(!esc.is_ascii_whitespace());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_ascii_whitespace(&self) -> bool {
        self.to_code_point()
            .is_some_and(|c| c.is_ascii_whitespace())
    }

    /// Checks if the value is an ASCII control character:
    /// U+0000 NUL ..= U+001F UNIT SEPARATOR, or U+007F DELETE.
    /// Note that most ASCII whitespace characters are control
    /// characters, but SPACE is not.
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let uppercase_a = g!('A');
    /// let uppercase_g = g!('G');
    /// let a = g!('a');
    /// let g = g!('g');
    /// let zero = g!('0');
    /// let percent = g!('%');
    /// let space = g!(' ');
    /// let lf = g!('\n');
    /// let esc = g!('\x1b');
    ///
    /// assert!(!uppercase_a.is_ascii_control());
    /// assert!(!uppercase_g.is_ascii_control());
    /// assert!(!a.is_ascii_control());
    /// assert!(!g.is_ascii_control());
    /// assert!(!zero.is_ascii_control());
    /// assert!(!percent.is_ascii_control());
    /// assert!(!space.is_ascii_control());
    /// assert!(lf.is_ascii_control());
    /// assert!(esc.is_ascii_control());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_ascii_control(&self) -> bool {
        self.to_code_point().is_some_and(|c| c.is_ascii_control())
    }

    /// Checks if the `Grapheme` contains exactly one code point.
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let code_point = g!('東');
    /// let non_code_point = g!("\r\n");
    ///
    /// assert!(code_point.is_code_point());
    /// assert!(!non_code_point.is_code_point());
    /// ```
    #[inline]
    #[doc(alias = "is_char", alias = "is_usv")]
    pub fn is_code_point(&self) -> bool {
        let mut iter = self.0.chars();
        matches!((iter.next(), iter.next()), (Some(_), None))
    }

    /// Returns `Some` if the `Grapheme` contains exactly one code point,
    /// or `None` if it's not.
    ///
    /// This is preferred to [`Self::is_code_point`] when you're passing the value
    /// along to something else that can take [`char`] rather than
    /// needing to check again for itself whether the value is one code point.
    #[must_use]
    #[inline]
    #[doc(alias = "to_char", alias = "to_usv")]
    pub fn to_code_point(&self) -> Option<char> {
        let mut iter = self.0.chars();
        if let (Some(c), None) = (iter.next(), iter.next()) {
            Some(c)
        } else {
            None
        }
    }

    /// Returns an iterator over the [`char`]s of a `&Grapheme`.
    ///
    /// As a `&Grapheme` consists of valid UTF-8, we can iterate through a
    /// `&Grapheme` by [`char`]. This method returns such an iterator.
    ///
    /// It's important to remember that [`char`] represents a Unicode Scalar
    /// Value, and might not match your idea of what a 'character' is.
    ///
    /// [`char`]: prim@char
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let y = g!("y̆");
    ///
    /// let mut code_points = y.code_points();
    ///
    /// assert_eq!(Some('y'), code_points.next()); // not 'y̆'
    /// assert_eq!(Some('\u{0306}'), code_points.next());
    ///
    /// assert_eq!(None, code_points.next());
    /// ```
    #[inline]
    #[doc(alias = "chars", alias = "usvs")]
    pub fn code_points(&self) -> Chars<'_> {
        self.0.chars()
    }

    /// Returns an iterator over the bytes of a `&Grapheme`.
    ///
    /// As a `&Grapheme` consists of a sequence of bytes, we can iterate
    /// through a `&Grapheme` by byte. This method returns such an iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let mut bytes = g!("y̆").bytes();
    ///
    /// assert_eq!(Some(b'y'), bytes.next());
    /// assert_eq!(Some(0xCC), bytes.next());
    /// assert_eq!(Some(0x86), bytes.next());
    ///
    /// assert_eq!(None, bytes.next());
    /// ```
    #[inline]
    pub fn bytes(&self) -> Bytes<'_> {
        self.0.bytes()
    }

    /// Returns a string slice of this `Grapheme`'s contents.
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let g = g!('f');
    ///
    /// assert_eq!("f", g.as_str());
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_str(&self) -> &str {
        &self.0
    }

    /// Returns a byte slice of this `Grapheme`'s contents.
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let g = g!('h');
    ///
    /// assert_eq!(&[b'h'], g.as_bytes());
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }

    /// Converts from `&Grapheme` to `GraphemeOwned`.
    pub fn to_owned(&self) -> GraphemeOwned {
        GraphemeOwned::from_ref(self)
    }

    /// Splits the grapheme into the first code point and the remaining code points.
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let (code_point, rest) = g!("y̆").split();
    ///
    /// assert_eq!('y', code_point);
    /// assert_eq!("\u{0306}", rest);
    /// ```
    #[inline]
    pub fn split(&self) -> (char, &str) {
        let mut iter = self.0.chars();
        // The operation never falls because the grapheme always contains at least one code point.
        let first = iter.next().unwrap();
        (first, iter.as_str())
    }

    /// Splits the grapheme into the remaining code points and the last code point.
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let (rest, code_point) = g!("y̆").split_rev();
    ///
    /// assert_eq!("y", rest);
    /// assert_eq!('\u{0306}', code_point);
    /// ```
    #[inline]
    pub fn split_rev(&self) -> (&str, char) {
        let mut iter = self.0.char_indices().rev();
        // Never falls because the grapheme always contains at least one code point.
        let (i, last) = iter.next().unwrap();
        let (rest, _) = self.0.split_at(i);
        (rest, last)
    }
}

impl fmt::Debug for Grapheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("g'")?;
        for i in self.as_str().chars() {
            fmt::Display::fmt(&i.escape_default(), f)?;
        }
        f.write_str("'")?;
        Ok(())
    }
}

impl fmt::Display for Grapheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl PartialEq for Grapheme {
    fn eq(&self, other: &Self) -> bool {
        self.0.nfd().eq(other.0.nfd())
    }
}

impl Hash for Grapheme {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl AsRef<str> for Grapheme {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<[u8]> for Grapheme {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<Grapheme> for Grapheme {
    fn as_ref(&self) -> &Grapheme {
        self
    }
}

impl<'src> From<&'src Grapheme> for Box<Grapheme> {
    fn from(value: &'src Grapheme) -> Self {
        let value: Box<str> = Box::from(value.as_str());
        // SAFETY: This is ok because Grapheme is #[repr(transparent)]
        unsafe { Box::from_raw(Box::into_raw(value) as *mut Grapheme) }
    }
}

impl From<Box<Grapheme>> for Box<str> {
    fn from(value: Box<Grapheme>) -> Self {
        // SAFETY: This is ok because Grapheme is #[repr(transparent)]
        unsafe { Box::from_raw(Box::into_raw(value) as *mut str) }
    }
}

impl From<Box<Grapheme>> for Box<[u8]> {
    fn from(value: Box<Grapheme>) -> Self {
        Box::<str>::from(value).into()
    }
}

impl Clone for Box<Grapheme> {
    fn clone(&self) -> Self {
        self.as_ref().into()
    }
}
