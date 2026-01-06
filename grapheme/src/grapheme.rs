//! Utilities for the `Grapheme` type.
//!
//! *[See also the `Grapheme` type.](Grapheme)*

use crate::GraphemeOwned;
use icu_properties::{
    CodePointMapData,
    props::{CanonicalCombiningClass, GeneralCategory, GraphemeClusterBreak},
};
use std::{
    cmp::PartialEq,
    fmt,
    hash::Hash,
    str::{Bytes, Chars},
};
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
/// Grapheme literals are grapheme slices:
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
/// Grapheme::from_usvs("ab").unwrap();
/// ```
///
/// ```no_run
/// # use grapheme::prelude::*;
/// // Undefined behavior
/// let _ = unsafe { Grapheme::from_usvs_unchecked("ab") };
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
///     // ... and then convert that slice into a grapheme slice
///     str::from_utf8(slice).ok().and_then(Grapheme::from_usvs)
/// };
///
/// assert_eq!(g, Some(strange));
/// ```
///
/// # Normalization
///
/// `Grapheme` stores an unnormalized slice of a string. For some
/// operations, it is normalized on the fly. In most cases, these
/// performance losses are minimal and less significant than losses
/// when allocating a normalized string.
///
/// Implementations of traits such as [`Hash`], [`PartialEq`], and
/// [`PartialOrd`] rely on a [NFD] normalized version of a string
/// representing a grapheme cluster:
///
/// ```
/// # use grapheme::prelude::*;
/// use std::hash::{DefaultHasher, Hash, Hasher};
/// use std::cmp::Ordering;
///
/// # fn main() {
/// // Within NFC
/// let canonical = g!("\u{00c7}\u{0304}");
/// let non_canonical = g!("C\u{0327}\u{0304}");
///
/// assert_eq!(g!("Ç̄"), canonical);
/// assert_eq!(canonical, non_canonical);
/// assert_eq!(canonical.cmp(non_canonical), Ordering::Equal);
/// assert_eq!(calculate_hash(&canonical), calculate_hash(&non_canonical));
/// # }
///
/// fn calculate_hash<T: Hash>(t: &T) -> u64 {
///     let mut s = DefaultHasher::new();
///     t.hash(&mut s);
///     s.finish()
/// }
/// ```
///
/// The [`Ord`] and [`PartialOrd`] implementations compare [USV]
/// sequences [lexicographically](Ord#lexicographical-comparison):
///
/// ```
/// # use grapheme::prelude::*;
/// use std::cmp::Ordering;
///
/// assert_eq!(g!("Ç̄").cmp(g!("Ç̄")), Ordering::Equal);
/// assert_eq!(g!("Ç̄").cmp(g!("Ç")), Ordering::Greater);
/// assert_eq!(g!("Ç").cmp(g!("Ç̄")), Ordering::Less);
/// ```
///
/// [NFD]: https://www.unicode.org/reports/tr15/#Norm_Forms
/// [USV]: #method.to_usv
#[derive(Eq)]
#[repr(transparent)]
pub struct Grapheme(str);

impl Grapheme {
    /// Alias for [`from_usvs`](#method.from_usvs).
    #[inline]
    #[deprecated(since = "1.2.0", note = "use `from_usvs` instead")]
    pub fn from_code_points(value: &str) -> Option<&Self> {
        Self::from_usvs(value)
    }

    /// Converts a `&str` to a `&Grapheme`.
    ///
    /// Note that all `Grapheme`s are valid [`str`]s, and can be cast to one
    /// with [`as_str`]:
    /// ```
    /// # use grapheme::prelude::*;
    /// let g = g!("👁‍🗨");
    /// let s = g.as_str();
    ///
    /// assert_eq!("👁‍🗨", s);
    /// ```
    ///
    /// However, the reverse is not true: not all valid [`str`]s are valid
    /// `Grapheme`s. `from_usvs()` will return `None` if the input is
    /// not a valid value for a `Grapheme`.
    ///
    /// For an unsafe version of this function which ignores these checks, see
    /// [`from_usvs_unchecked`].
    ///
    /// [`as_str`]: #method.as_str
    /// [`from_usvs_unchecked`]: #method.from_usvs_unchecked
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let c = Grapheme::from_usvs("❤️");
    ///
    /// assert_eq!(Some(g!("❤️")), c);
    /// ```
    ///
    /// Returning `None` when the input is not a valid `Grapheme`:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let c = Grapheme::from_usvs("ab");
    ///
    /// assert_eq!(None, c);
    /// ```
    #[must_use]
    #[inline]
    #[doc(alias = "from_chars", alias = "from_code_points", alias = "from_str")]
    pub fn from_usvs(value: &str) -> Option<&Self> {
        let mut iter = value.graphemes(true);
        matches!((iter.next(), iter.next()), (Some(_), None))
            .then(|| unsafe { Self::from_usvs_unchecked(value) })
    }

    /// Alias for [`from_usvs_unchecked`](#method.from_usvs_unchecked).
    #[inline]
    #[expect(clippy::missing_safety_doc)]
    #[deprecated(since = "1.2.0", note = "use `from_usvs_unchecked` instead")]
    pub const unsafe fn from_code_points_unchecked(value: &str) -> &Self {
        unsafe { Self::from_usvs_unchecked(value) }
    }

    /// Converts a `&str` to a `&Grapheme`, ignoring validity.
    ///
    /// Note that all `Grapheme`s are valid [`str`]s, and can be cast to one with [`as_str`]:
    /// ```
    /// # use grapheme::prelude::*;
    /// let g = g!("👁‍🗨");
    /// let s = g.as_str();
    ///
    /// assert_eq!("👁‍🗨", s);
    /// ```
    ///
    /// However, the reverse is not true: not all valid [`str`]s are valid
    /// `Grapheme`s. `from_usvs_unchecked()` will ignore this, and
    /// blindly cast to `Grapheme`, possibly creating an invalid one.
    ///
    /// [`as_str`]: #method.as_str
    ///
    /// # Safety
    ///
    /// This function is unsafe, as it may construct invalid `Grapheme` values.
    ///
    /// For a safe version of this function, see the [`from_usvs`] function.
    ///
    /// [`from_usvs`]: #method.from_usvs
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let c = unsafe { Grapheme::from_usvs_unchecked("❤️") };
    ///
    /// assert_eq!(g!("❤️"), c);
    /// ```
    #[must_use]
    #[inline]
    #[doc(
        alias = "from_chars_unchecked",
        alias = "from_str_unchecked",
        alias = "from_code_points_unchecked"
    )]
    pub const unsafe fn from_usvs_unchecked(value: &str) -> &Self {
        // SAFETY: This is ok because Grapheme is #[repr(transparent)]
        unsafe { &*(value as *const str as *const Self) }
    }

    /// Returns the number of bytes this `Grapheme` would need if encoded in UTF-8.
    ///
    /// That number of bytes is always greater than 0.
    ///
    /// Note that equal graphemes do not always have the same byte
    /// representation:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// // Within NFC
    /// let canonical = g!("\u{00c7}\u{0304}");
    /// let non_canonical = g!("C\u{0327}\u{0304}");
    ///
    /// assert_eq!(g!("Ç̄"), canonical);
    /// assert_eq!(canonical, non_canonical);
    /// assert!(canonical.len() != non_canonical.len());
    /// ```
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
    ///
    /// let len = g!("🤦‍♂️").len();
    /// assert_eq!(len, 13);
    /// ```
    ///
    /// The `&Graphemes` type guarantees that its contents are UTF-8, and so we can compare the length it
    /// would take if each [USV] was represented as a `&Grapheme` vs in the `&Graphemes` itself:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// // as graphemes
    /// let ka = g!('क');
    /// let rm = g!("र्म");
    ///
    /// // can be represented as three and nine bytes, respectively
    /// assert_eq!(3, ka.len());
    /// assert_eq!(9, rm.len());
    ///
    /// // as a &Graphemes, these two are encoded in UTF-8
    /// let karma = gs!("कर्म");
    ///
    /// let len = ka.len() + rm.len();
    ///
    /// // we can see that they take twelve bytes in total...
    /// assert_eq!(12, karma.len());
    ///
    /// // ... just like the &Graphemes
    /// assert_eq!(len, karma.len());
    /// ```
    ///
    /// [USV]: #method.to_usv
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
        self.to_usv().is_some_and(|c| c.is_digit(radix))
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
        self.to_usv().and_then(|c| c.to_digit(radix))
    }

    /// Returns `true` if decomposing a grapheme into components yields a
    /// result where:
    /// - All independent [USV]s are alphabetic.
    /// - All non-independent [USV]s are diacritics or alphabetic.
    ///
    /// `Alphabetic` is described in Chapter 4 (Character Properties) of the [Unicode Standard] and
    /// specified in the [Unicode Character Database][ucd] [`DerivedCoreProperties.txt`].
    ///
    /// [USV]: #method.to_usv
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
    /// assert!(g!("र्क").is_alphabetic());
    ///
    /// let c = g!("❤️");
    /// // love is many things, but it is not alphabetic
    /// assert!(!c.is_alphabetic());
    /// ```
    #[inline]
    pub fn is_alphabetic(&self) -> bool {
        let is_diacritic = |c| {
            let ccc = CodePointMapData::<CanonicalCombiningClass>::new().get(c);
            ccc != CanonicalCombiningClass::NotReordered
        };

        let (first, rest) = self.split();
        let first = first.is_alphabetic();
        let rest = rest.chars().all(|c| is_diacritic(c) || c.is_alphabetic());
        first && rest
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
    /// assert!(g!("र्क").is_alphanumeric());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_alphanumeric(&self) -> bool {
        self.is_numeric() || self.is_alphabetic()
    }

    /// Returns `true` if the only [USV] has one of the general categories
    /// for numbers.
    ///
    /// The general categories for numbers (`Nd` for decimal digits, `Nl` for
    /// letter-like numeric characters, and `No` for other numeric characters)
    /// are specified in the [Unicode Character Database][ucd]
    /// [`UnicodeData.txt`].
    ///
    /// This method doesn't cover everything that could be considered a number,
    /// e.g. ideographic numbers like '三'.
    /// If you want everything including characters with overlapping purposes
    /// then you might want to use a unicode or language-processing library
    /// that exposes the appropriate character properties instead of looking at
    /// the unicode categories.
    ///
    /// If you want to parse ASCII decimal digits (0-9) or ASCII base-N, use
    /// `is_ascii_digit` or `is_digit` instead.
    ///
    /// [USV]: #method.to_usv
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
    /// assert!(!g!("र्क").is_numeric());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_numeric(&self) -> bool {
        self.to_usv().is_some_and(char::is_numeric)
    }

    /// Returns if the grapheme starts with a [USV] having the
    /// `White_Space` property, and the remaining [USV]s have the general
    /// category `Cf`, have the `GCB=Extend` property, and are not included in
    /// the following list to mitigate against [CVE-2021-42574]:
    /// - `'\u{202A}'`
    /// - `'\u{202B}'`
    /// - `'\u{202C}'`
    /// - `'\u{202D}'`
    /// - `'\u{202E}'`
    /// - `'\u{2066}'`
    /// - `'\u{2067}'`
    /// - `'\u{2068}'`
    /// - `'\u{2069}'`
    ///
    /// And also returns `true` if the grapheme is `g'\r\n'`.
    ///
    /// `White_Space` is specified in the [Unicode Character Database][ucd] [`PropList.txt`].
    ///
    /// [USV]: #method.to_usv
    /// [ucd]: https://www.unicode.org/reports/tr44/
    /// [`PropList.txt`]: https://www.unicode.org/Public/UCD/latest/ucd/PropList.txt
    /// [CVE-2021-42574]: https://nvd.nist.gov/vuln/detail/CVE-2021-42574
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
    /// // with zero width non-joiner
    /// assert!(g!(" \u{200C}").is_whitespace());
    ///
    /// assert!(!g!('越').is_whitespace());
    /// assert!(!g!("र्क").is_whitespace());
    /// assert!(!g!("\u{200C}").is_whitespace());
    /// assert!(!g!("越\u{200C}").is_whitespace());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_whitespace(&self) -> bool {
        let is_extend_format = |c| {
            let category = CodePointMapData::<GeneralCategory>::new().get(c);
            let gcb = CodePointMapData::<GraphemeClusterBreak>::new().get(c);
            category == GeneralCategory::Format && gcb == GraphemeClusterBreak::Extend
        };

        let is_not_embeding = |c| {
            ![
                '\u{202A}', '\u{202B}', '\u{202C}', '\u{202D}', '\u{202E}', '\u{2066}', '\u{2067}',
                '\u{2068}', '\u{2069}',
            ]
            .contains(&c)
        };

        if self.as_str() == "\r\n" {
            return true;
        }

        let (first, rest) = self.split();
        let first = first.is_whitespace();
        let rest = rest
            .chars()
            .all(|c| is_not_embeding(c) && is_extend_format(c));

        first && rest
    }

    /// Returns `true` if the `Grapheme` is `g'\r\n'` or its only [USV]
    /// has the general category `Cc`.
    ///
    /// Control codes ([USV]s with the general category of `Cc`) are
    /// described in Chapter 4 (Character Properties) of the [Unicode Standard]
    /// and specified in the [Unicode Character Database][ucd]
    /// [`UnicodeData.txt`].
    ///
    /// [USV]: #method.to_usv
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
    /// assert!(g!("\r\n").is_control());
    ///
    /// assert!(!g!('q').is_control());
    /// assert!(!g!("र्क").is_control());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_control(&self) -> bool {
        self.as_str() == "\r\n" || self.to_usv().is_some_and(char::is_control)
    }

    /// Checks that all [USV]s are within the ASCII range.
    ///
    /// Note that the only `Grapheme` containing more than one [USV] suitable
    /// for this condition is `g'\r\n'`.
    ///
    /// [USV]: #method.to_usv
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// assert!(g!('a').is_ascii());
    /// assert!(g!("\r\n").is_ascii());
    /// assert!(!g!('❤').is_ascii());
    /// assert!(!g!("❤️").is_ascii());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii(&self) -> bool {
        self.as_bytes().is_ascii()
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
    /// let crlf = g!("\r\n");
    /// let esc = g!('\x1b');
    /// let rk = g!("र्क");
    ///
    /// assert!(uppercase_a.is_ascii_alphabetic());
    /// assert!(uppercase_g.is_ascii_alphabetic());
    /// assert!(a.is_ascii_alphabetic());
    /// assert!(g.is_ascii_alphabetic());
    /// assert!(!zero.is_ascii_alphabetic());
    /// assert!(!percent.is_ascii_alphabetic());
    /// assert!(!space.is_ascii_alphabetic());
    /// assert!(!lf.is_ascii_alphabetic());
    /// assert!(!crlf.is_ascii_alphabetic());
    /// assert!(!esc.is_ascii_alphabetic());
    /// assert!(!rk.is_ascii_alphabetic());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii_alphabetic(&self) -> bool {
        if let [only] = self.as_bytes() {
            only.is_ascii_alphabetic()
        } else {
            false
        }
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
    /// let crlf = g!("\r\n");
    /// let esc = g!('\x1b');
    /// let rk = g!("र्क");
    ///
    /// assert!(uppercase_a.is_ascii_alphanumeric());
    /// assert!(uppercase_g.is_ascii_alphanumeric());
    /// assert!(a.is_ascii_alphanumeric());
    /// assert!(g.is_ascii_alphanumeric());
    /// assert!(zero.is_ascii_alphanumeric());
    /// assert!(!percent.is_ascii_alphanumeric());
    /// assert!(!space.is_ascii_alphanumeric());
    /// assert!(!lf.is_ascii_alphanumeric());
    /// assert!(!crlf.is_ascii_alphanumeric());
    /// assert!(!esc.is_ascii_alphanumeric());
    /// assert!(!rk.is_ascii_alphanumeric());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii_alphanumeric(&self) -> bool {
        if let [only] = self.as_bytes() {
            only.is_ascii_alphanumeric()
        } else {
            false
        }
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
    /// let crlf = g!("\r\n");
    /// let esc = g!('\x1b');
    /// let rk = g!("र्क");
    ///
    /// assert!(!uppercase_a.is_ascii_digit());
    /// assert!(!uppercase_g.is_ascii_digit());
    /// assert!(!a.is_ascii_digit());
    /// assert!(!g.is_ascii_digit());
    /// assert!(zero.is_ascii_digit());
    /// assert!(!percent.is_ascii_digit());
    /// assert!(!space.is_ascii_digit());
    /// assert!(!lf.is_ascii_digit());
    /// assert!(!crlf.is_ascii_digit());
    /// assert!(!esc.is_ascii_digit());
    /// assert!(!rk.is_ascii_digit());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii_digit(&self) -> bool {
        if let [only] = self.as_bytes() {
            only.is_ascii_digit()
        } else {
            false
        }
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
    /// let crlf = g!("\r\n");
    /// let esc = g!('\x1b');
    /// let rk = g!("र्क");
    ///
    /// assert!(!uppercase_a.is_ascii_punctuation());
    /// assert!(!uppercase_g.is_ascii_punctuation());
    /// assert!(!a.is_ascii_punctuation());
    /// assert!(!g.is_ascii_punctuation());
    /// assert!(!zero.is_ascii_punctuation());
    /// assert!(percent.is_ascii_punctuation());
    /// assert!(!space.is_ascii_punctuation());
    /// assert!(!lf.is_ascii_punctuation());
    /// assert!(!crlf.is_ascii_punctuation());
    /// assert!(!esc.is_ascii_punctuation());
    /// assert!(!rk.is_ascii_punctuation());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii_punctuation(&self) -> bool {
        if let [only] = self.as_bytes() {
            only.is_ascii_punctuation()
        } else {
            false
        }
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
    /// let crlf = g!("\r\n");
    /// let esc = g!('\x1b');
    /// let rk = g!("र्क");
    ///
    /// assert!(uppercase_a.is_ascii_graphic());
    /// assert!(uppercase_g.is_ascii_graphic());
    /// assert!(a.is_ascii_graphic());
    /// assert!(g.is_ascii_graphic());
    /// assert!(zero.is_ascii_graphic());
    /// assert!(percent.is_ascii_graphic());
    /// assert!(!space.is_ascii_graphic());
    /// assert!(!lf.is_ascii_graphic());
    /// assert!(!crlf.is_ascii_graphic());
    /// assert!(!esc.is_ascii_graphic());
    /// assert!(!rk.is_ascii_graphic());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii_graphic(&self) -> bool {
        if let [only] = self.as_bytes() {
            only.is_ascii_graphic()
        } else {
            false
        }
    }

    /// Checks if the value is an ASCII whitespace:
    /// U+0020 SPACE, U+0009 HORIZONTAL TAB, U+000A LINE FEED,
    /// U+000C FORM FEED, U+000D CARRIAGE RETURN or U+000D + U+000A.
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
    /// [USV]: #method.to_usv
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
    /// let crlf = g!("\r\n");
    /// let esc = g!('\x1b');
    /// let rk = g!("र्क");
    ///
    /// assert!(!uppercase_a.is_ascii_whitespace());
    /// assert!(!uppercase_g.is_ascii_whitespace());
    /// assert!(!a.is_ascii_whitespace());
    /// assert!(!g.is_ascii_whitespace());
    /// assert!(!zero.is_ascii_whitespace());
    /// assert!(!percent.is_ascii_whitespace());
    /// assert!(space.is_ascii_whitespace());
    /// assert!(lf.is_ascii_whitespace());
    /// assert!(crlf.is_ascii_whitespace());
    /// assert!(!esc.is_ascii_whitespace());
    /// assert!(!rk.is_ascii_whitespace());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii_whitespace(&self) -> bool {
        match self.as_bytes() {
            b"\r\n" => true,
            [only] => only.is_ascii_whitespace(),
            _ => false,
        }
    }

    /// Checks if the value is an ASCII control:
    /// U+0000 NUL ..= U+001F UNIT SEPARATOR, or U+007F DELETE.
    /// Note that most ASCII whitespace characters are control
    /// characters, but SPACE is not.
    ///
    /// Note that the only `Grapheme` containing more than one [USV] suitable
    /// for this condition is `g'\r\n'`.
    ///
    /// [USV]: #method.to_usv
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
    /// let crlf = g!("\r\n");
    /// let esc = g!('\x1b');
    /// let rk = g!("र्क");
    ///
    /// assert!(!uppercase_a.is_ascii_control());
    /// assert!(!uppercase_g.is_ascii_control());
    /// assert!(!a.is_ascii_control());
    /// assert!(!g.is_ascii_control());
    /// assert!(!zero.is_ascii_control());
    /// assert!(!percent.is_ascii_control());
    /// assert!(!space.is_ascii_control());
    /// assert!(lf.is_ascii_control());
    /// assert!(crlf.is_ascii_control());
    /// assert!(esc.is_ascii_control());
    /// assert!(!rk.is_ascii_control());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii_control(&self) -> bool {
        match self.as_bytes() {
            b"\r\n" => true,
            [only] => only.is_ascii_control(),
            _ => false,
        }
    }

    /// Alias for [`is_usv`](#method.is_usv).
    #[inline]
    #[deprecated(since = "1.2.0", note = "use `is_usv` instead")]
    pub fn is_code_point(&self) -> bool {
        self.is_usv()
    }

    /// Checks if the `Grapheme` contains exactly one [USV].
    ///
    /// [USV]: #method.to_usv
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let usv = g!('東');
    /// let non_usv = g!("र्क");
    ///
    /// assert!(usv.is_usv());
    /// assert!(!non_usv.is_usv());
    /// ```
    #[inline]
    #[doc(alias = "is_char", alias = "is_code_point")]
    pub fn is_usv(&self) -> bool {
        let mut iter = self.0.chars();
        matches!((iter.next(), iter.next()), (Some(_), None))
    }

    /// Alias for [`to_usv`](#method.to_usv).
    #[inline]
    #[deprecated(since = "1.2.0", note = "use `to_usv` instead")]
    pub fn to_code_point(&self) -> Option<char> {
        self.to_usv()
    }

    /// Returns `Some` if the `Grapheme` contains exactly one Unicode scalar
    /// value (USV), or `None` if it's not.
    ///
    /// This is preferred to [`Self::is_usv`] when you're passing the value
    /// along to something else that can take [`char`] rather than
    /// needing to check again for itself whether the value is one USV.
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let usv = g!('東');
    /// let non_usv = g!("र्क");
    ///
    /// assert_eq!(Some('東'), usv.to_usv());
    /// assert_eq!(None, non_usv.to_usv());
    /// ```
    #[must_use]
    #[inline]
    #[doc(alias = "to_char", alias = "to_code_point")]
    pub fn to_usv(&self) -> Option<char> {
        let mut iter = self.0.chars();
        if let (Some(c), None) = (iter.next(), iter.next()) {
            Some(c)
        } else {
            None
        }
    }

    /// Returns an iterator over the [USV]s of a `&Grapheme`.
    ///
    /// As a `&Grapheme` consists of valid UTF-8, we can iterate through a
    /// `&Grapheme` by [USV]. This method returns such an iterator.
    ///
    /// It's important to remember that [USV] might not match your idea of what a
    /// 'character' is.
    ///
    /// [USV]: #method.to_usv
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let y = g!("y̆");
    ///
    /// # #[expect(deprecated)]
    /// let mut usvs = y.code_points();
    ///
    /// assert_eq!(Some('y'), usvs.next()); // not 'y̆'
    /// assert_eq!(Some('\u{0306}'), usvs.next());
    ///
    /// assert_eq!(None, usvs.next());
    /// ```
    #[inline]
    #[doc(alias = "chars")]
    #[deprecated(since = "1.2.0", note = "use `.as_str().chars()` instead")]
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
    /// # #[expect(deprecated)]
    /// let mut bytes = g!("y̆").bytes();
    ///
    /// assert_eq!(Some(b'y'), bytes.next());
    /// assert_eq!(Some(0xCC), bytes.next());
    /// assert_eq!(Some(0x86), bytes.next());
    ///
    /// assert_eq!(None, bytes.next());
    /// ```
    #[inline]
    #[deprecated(since = "1.2.0", note = "use `.as_bytes().iter()` instead")]
    pub fn bytes(&self) -> Bytes<'_> {
        self.0.bytes()
    }

    /// Returns a string slice of this `Grapheme`'s contents.
    ///
    /// Note that equal graphemes do not always have the same string
    /// representation:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// // Within NFD
    /// let canonical = g!("C\u{0327}\u{0304}");
    /// let non_canonical = g!("C\u{0304}\u{0327}");
    ///
    /// assert_eq!(g!("Ç̄"), canonical);
    /// assert_eq!(canonical, non_canonical);
    /// assert!(canonical.as_str() != non_canonical.as_str());
    /// ```
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
    /// Note that equal graphemes do not always have the same byte
    /// representation:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// // Within NFD
    /// let canonical = g!("C\u{0327}\u{0304}");
    /// let non_canonical = g!("C\u{0304}\u{0327}");
    ///
    /// assert_eq!(g!("Ç̄"), canonical);
    /// assert_eq!(canonical, non_canonical);
    /// assert!(canonical.as_bytes() != non_canonical.as_bytes());
    /// ```
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

    /// Splits the grapheme into the first [USV] and the remaining [USV]s.
    ///
    /// Note that equal graphemes do not always have the same string
    /// representation:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// // Within NFD
    /// let canonical = g!("C\u{0327}\u{0304}");
    /// let non_canonical = g!("C\u{0304}\u{0327}");
    ///
    /// assert_eq!(g!("Ç̄"), canonical);
    /// assert_eq!(canonical, non_canonical);
    /// assert!(canonical.split() != non_canonical.split());
    /// ```
    ///
    /// [USV]: #method.to_usv
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let (usv, rest) = g!("y̆").split();
    ///
    /// assert_eq!('y', usv);
    /// assert_eq!("\u{0306}", rest);
    /// ```
    #[inline]
    pub fn split(&self) -> (char, &str) {
        let mut iter = self.0.chars();
        // The operation never falls because the grapheme always contains at
        // least one [USV].
        let first = iter.next().unwrap();
        (first, iter.as_str())
    }

    /// Splits the grapheme into the remaining [USV]s and the last [USV].
    ///
    /// Note that equal graphemes do not always have the same string
    /// representation:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// // Within NFD
    /// let canonical = g!("C\u{0327}\u{0304}");
    /// let non_canonical = g!("C\u{0304}\u{0327}");
    ///
    /// assert_eq!(g!("Ç̄"), canonical);
    /// assert_eq!(canonical, non_canonical);
    /// assert!(canonical.split_rev() != non_canonical.split_rev());
    /// ```
    ///
    /// [USV]: #method.to_usv
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let (rest, usv) = g!("y̆").split_rev();
    ///
    /// assert_eq!("y", rest);
    /// assert_eq!('\u{0306}', usv);
    /// ```
    #[inline]
    pub fn split_rev(&self) -> (&str, char) {
        let mut iter = self.0.char_indices().rev();
        // Never falls because the grapheme always contains at least one code
        // point.
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

#[inline]
fn map_pair<A, AG, GA, G, O>(
    ascii: A,
    a_g: AG,
    g_a: GA,
    grapheme: G,
) -> impl FnOnce(&Grapheme, &Grapheme) -> O
where
    A: FnOnce(&u8, &u8) -> O,
    AG: FnOnce(u8, &Grapheme) -> O,
    GA: FnOnce(&Grapheme, u8) -> O,
    G: FnOnce(&Grapheme, &Grapheme) -> O,
{
    |first, second| match (first.len(), second.len()) {
        (1, 1) => ascii(&first.0.as_bytes()[0], &second.0.as_bytes()[0]),
        (1, _) => a_g(first.0.as_bytes()[0], second),
        (_, 1) => g_a(first, second.0.as_bytes()[0]),
        _ => grapheme(first, second),
    }
}

#[inline]
fn map_usvs<U, O>(usv: U, grapheme: O) -> impl FnOnce(&Grapheme) -> O
where
    U: FnOnce(char) -> O,
{
    |g| {
        let mut iter = g.0.nfd();
        let c = unsafe { iter.next().unwrap_unchecked() };
        if iter.next().is_some() {
            grapheme
        } else {
            usv(c)
        }
    }
}

impl PartialOrd for Grapheme {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Grapheme {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        map_pair(
            Ord::cmp,
            |a, b| map_usvs(|b| (a as u32).cmp(&(b as u32)), std::cmp::Ordering::Greater)(b),
            |a, b| map_usvs(|a| (a as u32).cmp(&(b as u32)), std::cmp::Ordering::Less)(a),
            |a, b| a.0.nfd().cmp(b.0.nfd()),
        )(self, other)
    }
}

impl PartialEq for Grapheme {
    fn eq(&self, other: &Self) -> bool {
        map_pair(
            PartialEq::eq,
            |a, b| map_usvs(|b| a as u32 == b as u32, false)(b),
            |a, b| map_usvs(|a| a as u32 == b as u32, false)(a),
            |a, b| a.0.nfd().eq(b.0.nfd()),
        )(self, other)
    }
}

impl Hash for Grapheme {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        for usv in self.0.nfd() {
            state.write_u32(usv as u32);
        }
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
