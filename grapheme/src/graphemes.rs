//! Utilities for the `Graphemes` type.
//!
//! *[See also the `Graphemes` type.](Graphemes)*

use super::{
    Grapheme,
    normalization::{Normalization, Unnormalized},
};
use std::{fmt, hash::Hash, marker::PhantomData};
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
///     str::from_utf8(slice).ok().and_then(Graphemes::from_usvs)
/// };
///
/// assert_eq!(g, Some(story));
/// ```
///
/// # Normalization
///
/// `Graphemes` stores an unnormalized string slice. For some
/// operations, it is normalized on the fly. In most cases, these
/// performance losses are minimal and less significant than losses
/// when allocating a normalized string.
///
/// Implementations of traits such as [`Hash`] and [`PartialEq`] rely
/// on a [NFD] normalized version of a string representing a grapheme
/// cluster:
///
/// ```
/// # use grapheme::prelude::*;
/// use std::hash::{DefaultHasher, Hash, Hasher};
/// use std::cmp::Ordering;
///
/// # fn main() {
/// // Within NFC
/// let canonical = gs!("caf\u{00E9}");
/// let non_canonical = gs!("cafe\u{0301}");
///
/// assert_eq!(gs!("café"), canonical);
/// assert_eq!(canonical, non_canonical);
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
/// [NFD]: https://www.unicode.org/reports/tr15/#Norm_Forms
#[repr(transparent)]
pub struct Graphemes<N: Normalization = Unnormalized> {
    phantom: PhantomData<N>,
    inner: str,
}

impl<N: Normalization> Graphemes<N> {
    /// Converts a `&str` to a `&Graphemes`.
    ///
    /// Note that all `Graphemes`s are valid [`str`]s, and can be cast to one
    /// with [`as_str`]:
    /// ```
    /// # use grapheme::prelude::*;
    /// let gs = gs!("y̆es");
    /// let s = gs.as_str();
    ///
    /// assert_eq!("y̆es", s);
    /// ```
    ///
    /// However, the reverse is not true: not all valid [`str`]s are valid
    /// `Graphemes`s. `from_usvs()` will return `None` if the input is
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
    /// let c = Graphemes::from_usvs("y̆es");
    ///
    /// assert_eq!(Some(gs!("y̆es")), c);
    /// ```
    ///
    /// Returning `None` when the input is not a valid `Graphemes`:
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let c = Graphemes::<Nfd>::from_usvs("\u{00c7}");
    ///
    /// assert_eq!(None, c);
    /// ```
    #[must_use]
    #[inline]
    #[doc(alias = "from_chars", alias = "from_code_points", alias = "from_str")]
    pub fn from_usvs(inner: &str) -> Option<&Self> {
        N::is_normalized(inner).then(|| unsafe { Self::from_usvs_unchecked(inner) })
    }

    /// Converts a `&str` to a `&Graphemes`, ignoring validity.
    ///
    /// Note that all `Graphemes`s are valid [`str`]s, and can be cast to one with [`as_str`]:
    /// ```
    /// # use grapheme::prelude::*;
    /// let g = gs!("y̆es");
    /// let s = g.as_str();
    ///
    /// assert_eq!("y̆es", s);
    /// ```
    ///
    /// However, the reverse is not true: not all valid [`str`]s are valid
    /// `Graphemes`s. `from_usvs_unchecked()` will ignore this, and
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
    /// let c = unsafe { Graphemes::from_usvs_unchecked("y̆es") };
    ///
    /// assert_eq!(gs!("y̆es"), c);
    /// ```
    #[must_use]
    #[inline]
    #[doc(alias = "from_chars", alias = "from_code_points", alias = "from_str")]
    pub unsafe fn from_usvs_unchecked(inner: &str) -> &Self {
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
        // SAFETY: This is ok because Grapheme is #[repr(transparent)]
        unsafe { Box::from_raw(Box::into_raw(self) as *mut str) }
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
        self.into_boxed_str().into_boxed_bytes()
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
    pub fn iter(&self) -> Iter<N> {
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
    pub fn iter_with_indices(&self) -> IterWithIndices<N> {
        IterWithIndices::new(self)
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
        &self.inner
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
        self.inner.as_bytes()
    }
}

impl<N: Normalization> fmt::Debug for Graphemes<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("g")?;
        fmt::Debug::fmt(&self.inner, f)
    }
}

impl<N: Normalization> fmt::Display for Graphemes<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.inner, f)
    }
}

impl<N: Normalization> PartialEq for Graphemes<N> {
    fn eq(&self, other: &Self) -> bool {
        N::eq_str(self.as_str(), other.as_str())
    }
}

impl<N: Normalization> Eq for Graphemes<N> {}

impl<N: Normalization> Hash for Graphemes<N> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        N::hash_str(self.as_str(), state);
    }
}

impl<N: Normalization> AsRef<str> for Graphemes<N> {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<N: Normalization> AsRef<[u8]> for Graphemes<N> {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<N: Normalization> AsRef<Graphemes<N>> for Graphemes<N> {
    fn as_ref(&self) -> &Graphemes<N> {
        self
    }
}

impl<'src, N: Normalization> From<&'src Graphemes<N>> for &'src str {
    fn from(value: &'src Graphemes<N>) -> Self {
        value.as_str()
    }
}

impl<'src, N: Normalization> From<&'src Graphemes<N>> for Box<Graphemes<N>> {
    fn from(value: &'src Graphemes<N>) -> Self {
        let boxed_str: Box<str> = value.as_str().into();
        // SAFETY: This is ok because Grapheme is #[repr(transparent)]
        unsafe { Box::from_raw(Box::into_raw(boxed_str) as *mut Graphemes<N>) }
    }
}

impl<N: Normalization> From<Box<Graphemes<N>>> for Box<str> {
    fn from(value: Box<Graphemes<N>>) -> Self {
        value.into_boxed_str()
    }
}

impl<N: Normalization> From<Box<Graphemes<N>>> for Box<[u8]> {
    fn from(value: Box<Graphemes<N>>) -> Self {
        value.into_boxed_bytes()
    }
}

impl<N: Normalization> Clone for Box<Graphemes<N>> {
    fn clone(&self) -> Self {
        self.as_ref().into()
    }
}

impl<'src, N: Normalization> IntoIterator for &'src Graphemes<N> {
    type Item = &'src Grapheme<N>;

    type IntoIter = Iter<'src, N>;

    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self)
    }
}

impl<'src> From<&'src str> for &'src Graphemes {
    fn from(value: &'src str) -> Self {
        // SAFETY: This is ok because unnormalized `Graphemes` are being created
        unsafe { Graphemes::from_usvs_unchecked(value) }
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
        unsafe { Box::from_raw(Box::into_raw(value) as *mut Graphemes<Unnormalized>) }
    }
}

/// An iterator over the [`Grapheme`]s of a graphemes slice.
///
/// This struct is created by the [`iter`] method on
/// [`Graphemes`]. See its documentation for more.
///
/// [`iter`]: Graphemes::iter    
#[derive(Debug, Clone)]
pub struct Iter<'g, N: Normalization> {
    iter: unicode_segmentation::Graphemes<'g>,
    phantom: PhantomData<N>,
}

impl<'g, N: Normalization> Iter<'g, N> {
    /// Creates new `Iter`.
    pub fn new(graphemes: &'g Graphemes<N>) -> Self {
        Self {
            iter: graphemes.as_str().graphemes(true),
            phantom: PhantomData,
        }
    }

    /// Returns a string slice of this `&Graphemes`’s contents.
    pub fn as_str(self) -> &'g str {
        self.iter.as_str()
    }
}

impl<'g, N: Normalization> Iterator for Iter<'g, N> {
    type Item = &'g Grapheme<N>;

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

impl<N: Normalization> DoubleEndedIterator for Iter<'_, N> {
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
pub struct IterWithIndices<'g, N: Normalization> {
    iter: unicode_segmentation::GraphemeIndices<'g>,
    phantom: PhantomData<N>,
}

impl<'g, N: Normalization> IterWithIndices<'g, N> {
    /// Creates new `IterWithIndices`.
    pub fn new(graphemes: &'g Graphemes<N>) -> Self {
        Self {
            iter: graphemes.as_str().grapheme_indices(true),
            phantom: PhantomData,
        }
    }

    /// Returns a string slice of this `&Graphemes`’s contents.
    pub fn as_str(self) -> &'g str {
        self.iter.as_str()
    }
}

impl<'g, N: Normalization> Iterator for IterWithIndices<'g, N> {
    type Item = (usize, &'g Grapheme<N>);

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

impl<N: Normalization> DoubleEndedIterator for IterWithIndices<'_, N> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter
            .next_back()
            .map(|(i, g)| (i, unsafe { Grapheme::from_usvs_unchecked(g) }))
    }
}
