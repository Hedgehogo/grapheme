//! Utilities for the `Graphemes` type.
//!
//! *[See also the `Graphemes` type.](Graphemes)*

use super::Grapheme;
use std::ops::Deref;
use std::{fmt, hash::Hash, str::Chars};
use unicode_normalization::UnicodeNormalization;
use unicode_segmentation::UnicodeSegmentation;

/// The `Graphemes` type, also called a ‘grapheme slice’. It is usually seen
/// in its borrowed form, `&Graphemes`. It is also the type of graphemes
/// literals, `&'static str`.
///
/// # Basic Usage
///
/// Graphemes literals are graphemes slices:
/// ```
/// # use grapheme::prelude::*;
/// let hello_world  = gs!("Hello, World!");
/// ```
///
/// Here we have declared a grapheme slice initialized with a graphemes literal.
/// Grapheme literals have a static lifetime, which means the graphemes
/// `hello_world` is guaranteed to be valid for the duration of the entire
/// program. We can explicitly specify `h`’s lifetime as well:
/// ```
/// # use grapheme::prelude::*;
/// let hello_world: &'static Graphemes = gs!("Hello, world!");
/// ```
///
/// # Representation
/// A `&Graphemes` is made up of two components: a pointer to some bytes, and a
/// length. You can look at these with the `as_str` and `len` methods:
///
/// ```
/// # use grapheme::prelude::*;
/// use std::slice;
/// use std::str;
///
/// let story = gs!("Once upon a time...");
///
/// let ptr = story.as_str().as_ptr();
/// let len = story.len();
///
/// // story has nineteen bytes
/// assert_eq!(19, len);
///
/// // We can re-build graphemes out of ptr and len. This is all unsafe because
/// // we are responsible for making sure the two components are valid:
/// let g = unsafe {
///     // First, we build a &[u8]...
///     let slice = slice::from_raw_parts(ptr, len);
///
///     // ... and then convert that slice into a grapheme slice
///     str::from_utf8(slice).ok().map(Graphemes::from_usvs)
/// };
///
/// assert_eq!(g, Some(story));
/// ```
#[derive(Eq)]
#[repr(transparent)]
pub struct Graphemes(str);

impl Graphemes {
    /// Alias for [`from_usvs`](#method.from_usvs).
    #[inline]
    #[deprecated(since = "1.2.0", note = "use `from_usvs` instead")]
    pub fn from_code_points(inner: &str) -> &Self {
        Self::from_usvs(inner)
    }

    /// Converts a `&str` into a `&Graphemes`.
    #[must_use]
    #[inline]
    #[doc(alias = "from_chars", alias = "from_code_points", alias = "from_str")]
    pub fn from_usvs(inner: &str) -> &Self {
        // SAFETY: This is ok because Graphemes is #[repr(transparent)]
        unsafe { &*(inner as *const str as *const Self) }
    }

    /// Converts a `Box<Graphemes>` into a `Box<str>` without copying or allocating.
    ///
    /// Note that equal graphemes do not always have the same string
    /// representation:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// // Within NFD
    /// let canonical = gs!("C\u{0327}\u{0304}");
    /// let non_canonical = gs!("C\u{0304}\u{0327}");
    ///
    /// assert_eq!(gs!("Ç̄"), canonical);
    /// assert_eq!(canonical, non_canonical);
    /// assert!(canonical.as_str() != non_canonical.as_str());
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let s = gs!("this is a grapheme string");
    /// let boxed_graphemes = Box::<Graphemes>::from(s);
    /// let boxed_str = boxed_graphemes.into_boxed_str();
    /// assert_eq!(*boxed_str, *s.as_str());
    /// ```
    #[must_use]
    #[inline]
    pub fn into_boxed_str(self: Box<Self>) -> Box<str> {
        self.into()
    }

    /// Converts a `Box<Graphemes>` into a `Box<[u8]>` without copying or allocating.
    ///
    /// Note that equal graphemes do not always have the same byte
    /// representation:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// // Within NFD
    /// let canonical = gs!("C\u{0327}\u{0304}");
    /// let non_canonical = gs!("C\u{0304}\u{0327}");
    ///
    /// assert_eq!(gs!("Ç̄"), canonical);
    /// assert_eq!(canonical, non_canonical);
    /// assert!(canonical.as_bytes() != non_canonical.as_bytes());
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let s = gs!("this is a grapheme string");
    /// let boxed_graphemes = Box::<Graphemes>::from(s);
    /// let boxed_str = boxed_graphemes.into_boxed_bytes();
    /// assert_eq!(*boxed_str, *s.as_bytes());
    /// ```
    #[must_use]
    #[inline]
    pub fn into_boxed_bytes(self: Box<Self>) -> Box<[u8]> {
        self.into()
    }

    /// Returns the length of `self`.
    ///
    /// This length is in bytes, not [USV]s or graphemes. In other words,
    /// it might not be what a human considers the length of the string.
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
    /// [USV]: prim@char
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let len = gs!("yes").len();
    /// assert_eq!(3, len);
    ///
    /// assert_eq!(gs!("y̆es").len(), 5); // unusual y!
    /// assert_eq!(gs!("y̆es").iter().count(), 3);
    /// ```
    #[must_use]
    #[inline]
    pub const fn len(&self) -> usize {
        self.as_str().len()
    }

    /// Returns `true` if `self` has a length of zero bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let s = gs!("");
    /// assert!(s.is_empty());
    ///
    /// let s = gs!("not empty");
    /// assert!(!s.is_empty());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Checks if all [`Grapheme`]s in this string are within the ASCII range.
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let ascii = gs!("hello!\r\n");
    /// let non_ascii = gs!("Grüße, Jürgen ❤");
    ///
    /// assert!(ascii.is_ascii());
    /// assert!(!non_ascii.is_ascii());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii(&self) -> bool {
        // We can treat each byte as USV here: all multibyte USVs start with a
        // byte that is not in the ASCII range, so we will stop there already.
        //
        // In a single ASCII grapheme consisting of several bytes (g'\r\n'),
        // each byte is ASCII.
        self.as_bytes().is_ascii()
    }

    /// Returns an iterator over the [`Grapheme`]s of a `Graphemes`.
    ///
    /// As a `&Grapheme` consists of valid Unicode, we can iterate through a
    /// [`Grapheme`] by `Graphemes`. This method returns such an iterator.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let yes = gs!("y̆es");
    ///
    /// let mut iter = yes.iter();
    ///
    /// assert_eq!(Some(g!("y̆")), iter.next()); // g'y̆', not like str!
    /// assert_eq!(Some(g!('e')), iter.next());
    /// assert_eq!(Some(g!('s')), iter.next());
    ///
    /// assert_eq!(None, iter.next());
    /// ```
    #[must_use]
    #[inline]
    pub fn iter(&self) -> Iter {
        Iter::new(self)
    }

    /// Returns an iterator over the [`Grapheme`]s and their byte indices of a
    /// `Graphemes`.
    ///
    /// As a graphemes slice consists of valid UTF-8, we can iterate through a
    /// graphemes slice by [`Grapheme`]. This method returns an iterator of
    /// both these [`Grapheme`]s, as well as their byte positions.
    ///
    /// The iterator yields tuples. The position is first, the [`Grapheme`] is
    /// second.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let word = gs!("y̆es");
    ///
    /// let count = word.iter_with_indices().count();
    /// assert_eq!(3, count);
    ///
    /// let mut iter = word.iter_with_indices();
    ///
    /// assert_eq!(Some((0, g!("y̆"))), iter.next());
    /// assert_eq!(Some((3, g!('e'))), iter.next());
    /// assert_eq!(Some((4, g!('s'))), iter.next());
    ///
    /// assert_eq!(None, iter.next());
    /// ```
    #[must_use]
    #[inline]
    pub fn iter_with_indices(&self) -> IterWithIndices {
        IterWithIndices::new(self)
    }

    /// Returns an iterator over the [`char`]s of a `&Graphemes`.
    ///
    /// As a `&Graphemes` consists of valid Unicode, we can iterate through a
    /// `&Graphemes` by [`char`]. This method returns such an iterator.
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
    /// let yes = gs!("y̆es");
    ///
    /// # #[expect(deprecated)]
    /// let mut usvs = yes.code_points();
    ///
    /// assert_eq!(Some('y'), usvs.next()); // not 'y̆'
    /// assert_eq!(Some('\u{0306}'), usvs.next());
    /// assert_eq!(Some('e'), usvs.next());
    /// assert_eq!(Some('s'), usvs.next());
    ///
    /// assert_eq!(None, usvs.next());
    /// ```
    #[inline]
    #[doc(alias = "chars", alias = "usvs")]
    #[deprecated(since = "1.2.0", note = "use `.as_str().chars()` instead")]
    pub fn code_points(&self) -> Chars<'_> {
        self.0.chars()
    }

    /// Returns a string slice of this `&Graphemes`’s contents.
    ///
    /// Note that equal graphemes do not always have the same string
    /// representation:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// // Within NFD
    /// let canonical = gs!("C\u{0327}\u{0304}");
    /// let non_canonical = gs!("C\u{0304}\u{0327}");
    ///
    /// assert_eq!(gs!("Ç̄"), canonical);
    /// assert_eq!(canonical, non_canonical);
    /// assert!(canonical.as_str() != non_canonical.as_str());
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let s = gs!("y̆es");
    ///
    /// assert_eq!("y̆es", s.as_str());
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_str(&self) -> &str {
        &self.0
    }

    /// Returns a byte slice of this `&Graphemes`'s contents.
    ///
    /// Note that equal graphemes do not always have the same byte
    /// representation:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// // Within NFD
    /// let canonical = gs!("C\u{0327}\u{0304}");
    /// let non_canonical = gs!("C\u{0304}\u{0327}");
    ///
    /// assert_eq!(gs!("Ç̄"), canonical);
    /// assert_eq!(canonical, non_canonical);
    /// assert!(canonical.as_bytes() != non_canonical.as_bytes());
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let s = gs!("y̆es");
    ///
    /// assert_eq!(&[b'y', 204, 134, b'e', b's'], s.as_bytes());
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }
}

impl Deref for Graphemes {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl fmt::Debug for Graphemes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("g")?;
        fmt::Debug::fmt(&self.0, f)
    }
}

impl fmt::Display for Graphemes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl PartialEq for Graphemes {
    fn eq(&self, other: &Self) -> bool {
        self.0.nfd().eq(other.0.nfd())
    }
}

impl Hash for Graphemes {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        for usv in self.0.nfd() {
            state.write_u32(usv as u32);
        }
        state.write_u8(0xFF);
    }
}

impl AsRef<str> for Graphemes {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<[u8]> for Graphemes {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsRef<Graphemes> for Graphemes {
    fn as_ref(&self) -> &Graphemes {
        self
    }
}

impl<'src> From<&'src str> for &'src Graphemes {
    fn from(value: &'src str) -> Self {
        Graphemes::from_usvs(value)
    }
}

impl<'src> From<&'src Graphemes> for &'src str {
    fn from(value: &'src Graphemes) -> Self {
        value.as_str()
    }
}

impl<'src> From<&'src Graphemes> for Box<Graphemes> {
    fn from(value: &'src Graphemes) -> Self {
        value.as_str().into()
    }
}

impl<'src> From<&'src str> for Box<Graphemes> {
    fn from(value: &'src str) -> Self {
        Box::<str>::from(value).into()
    }
}

impl From<Box<str>> for Box<Graphemes> {
    fn from(value: Box<str>) -> Self {
        // SAFETY: This is ok because Grapheme is #[repr(transparent)]
        unsafe { Box::from_raw(Box::into_raw(value) as *mut Graphemes) }
    }
}

impl From<Box<Graphemes>> for Box<str> {
    fn from(value: Box<Graphemes>) -> Self {
        // SAFETY: This is ok because Grapheme is #[repr(transparent)]
        unsafe { Box::from_raw(Box::into_raw(value) as *mut str) }
    }
}

impl From<Box<Graphemes>> for Box<[u8]> {
    fn from(value: Box<Graphemes>) -> Self {
        Box::<str>::from(value).into()
    }
}

impl Clone for Box<Graphemes> {
    fn clone(&self) -> Self {
        self.as_ref().into()
    }
}

impl<'src> IntoIterator for &'src Graphemes {
    type Item = &'src Grapheme;

    type IntoIter = Iter<'src>;

    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self)
    }
}

/// Alias for [`Iter`].
#[deprecated(since = "1.2.0", note = "use `Iter` instead")]
pub type GraphemesIter<'g> = Iter<'g>;

/// An iterator over the [`Grapheme`]s of a graphemes slice.
///
/// This struct is created by the [`iter`] method on
/// [`Graphemes`]. See its documentation for more.
///
/// [`iter`]: Graphemes::iter    
#[derive(Debug, Clone)]
pub struct Iter<'g> {
    iter: unicode_segmentation::Graphemes<'g>,
}

impl<'g> Iter<'g> {
    /// Creates new `Iter`.
    pub fn new(graphemes: &'g Graphemes) -> Self {
        Self {
            iter: graphemes.as_str().graphemes(true),
        }
    }

    /// Returns a string slice of this `&Graphemes`’s contents.
    pub fn as_str(self) -> &'g str {
        self.iter.as_str()
    }
}

impl<'g> Iterator for Iter<'g> {
    type Item = &'g Grapheme;

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|grapheme| unsafe { Grapheme::from_usvs_unchecked(grapheme) })
    }
}

impl DoubleEndedIterator for Iter<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter
            .next_back()
            .map(|grapheme| unsafe { Grapheme::from_usvs_unchecked(grapheme) })
    }
}

/// An iterator over the [`Grapheme`]s and their byte indices of a graphemes slice.
///
/// This struct is created by the [`iter_with_indices`] method on [`Graphemes`]. See its documentation for more.
///
/// [`iter_with_indices`]: Graphemes::iter_with_indices
#[derive(Debug, Clone)]
pub struct IterWithIndices<'g> {
    iter: unicode_segmentation::GraphemeIndices<'g>,
}

impl<'g> IterWithIndices<'g> {
    /// Creates new `IterWithIndices`.
    pub fn new(graphemes: &'g Graphemes) -> Self {
        Self {
            iter: graphemes.as_str().grapheme_indices(true),
        }
    }

    /// Returns a string slice of this `&Graphemes`’s contents.
    pub fn as_str(self) -> &'g str {
        self.iter.as_str()
    }
}

impl<'g> Iterator for IterWithIndices<'g> {
    type Item = (usize, &'g Grapheme);

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|(i, g)| (i, unsafe { Grapheme::from_usvs_unchecked(g) }))
    }
}

impl DoubleEndedIterator for IterWithIndices<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter
            .next_back()
            .map(|(i, g)| (i, unsafe { Grapheme::from_usvs_unchecked(g) }))
    }
}
