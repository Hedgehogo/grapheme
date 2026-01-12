//! Utilities for the `GraphemeOwned` type.
//!
//! *[See also the `GraphemeOwned` type.](GraphemeOwned)*

use super::Grapheme;
use super::normalization::{Normalization, NormalizationLossless, Unnormalized};
use smallvec::SmallVec;
use std::{
    borrow::{Borrow, BorrowMut, Cow},
    fmt,
    hash::Hash,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    str,
};

const USIZE_BYTES: usize = size_of::<usize>();
type GraphemeOwnedInner = SmallVec<[u8; USIZE_BYTES]>;

/// The `GraphemeOwned` type represents a single character. More specifically,
/// since ‘character’ isn’t a well-defined concept in Unicode, `Grapheme` is a
/// ‘extended Unicode grapheme cluster’. It's something between `String` and
/// `char`.  Like `char`, it is a type representing a single unit of text. But
/// just like `String` it is the owning version of `&Grapheme`. It can allocate
/// memory on the heap, and it can also contain smaller graphemes inside
/// itself.
///
/// # Examples
///
/// You can create a `GraphemeOwned` from a grapheme literal with
/// `GraphemeOwned::from_ref` or [`Grapheme::to_owned`]:
///
/// ```
/// # use grapheme::prelude::*;
/// let h = g!('h').to_owned();
/// ```
///
/// # Deref
///
/// `GraphemeOwned` implements <code>[Deref]<Target = [Grapheme]></code>, and
/// so inherits all of [`Grapheme`]’s methods. In addition, this means that you
/// can pass a `GraphemeOwned` to a function which takes a
/// <code>&[Grapheme]</code> by using an ampersand (&):
///
/// ```
/// # use grapheme::prelude::*;
/// fn takes_grapheme(g: &Grapheme) { }
///
/// let g = GraphemeOwned::from(g!('h'));
///
/// takes_grapheme(&g);
/// ```
///
/// This will create a <code>&[Grapheme]</code> from the `GraphemeOwned` and
/// pass it in. This conversion is very inexpensive, and so generally,
/// functions will accept <code>&[Grapheme]</code>s as arguments unless they
/// need a `GraphemeOwned` for some specific reason.
///
/// # Representation
///
/// The `GraphemeOwned` contains a statically allocated buffer equal to usize
/// in size (usually eight u8). As long as the grapheme encoded in UTF-8 does
/// not exceed this size, it is stored in this buffer, otherwise it is located
/// in the heap, and the buffer contains capacity and a pointer to memory in
/// the heap.
#[derive(Clone, Eq)]
#[repr(transparent)]
pub struct GraphemeOwned<N: Normalization = Unnormalized> {
    phantom: PhantomData<N>,
    inner: GraphemeOwnedInner,
}

impl<N: Normalization> GraphemeOwned<N> {
    /// Converts from `&Grapheme` to `GraphemeOwned`.
    pub fn from_ref(grapheme: &Grapheme<N>) -> Self {
        let bytes = grapheme.as_bytes();
        Self {
            phantom: PhantomData,
            inner: SmallVec::from_slice(bytes),
        }
    }

    /// Converts from `Box<Grapheme>` to `GraphemeOwned`
    pub fn from_box(grapheme: Box<Grapheme<N>>) -> Self {
        let bytes: Box<[u8]> = grapheme.into();
        Self {
            phantom: PhantomData,
            inner: SmallVec::from_vec(bytes.into()),
        }
    }

    /// Converts from `GraphemeOwned` to `Box<Grapheme>`
    pub fn into_box(self) -> Box<Grapheme<N>> {
        let bytes = self.inner.into_boxed_slice();
        // SAFETY: This is ok because `[u8]` previously contained `Grapheme`.
        let string = unsafe { str::from_boxed_utf8_unchecked(bytes) };
        // SAFETY: This is ok because `Grapheme` is `#[repr[transparent]]`.
        unsafe { Box::from_raw(Box::<str>::into_raw(string) as *mut Grapheme<N>) }
    }

    /// Returns this `GraphemeOwned` capacity, in bytes.
    ///
    /// # Examples
    /// ```
    /// # use grapheme::prelude::*;
    /// let g = GraphemeOwned::from(g!("y̆"));
    ///
    /// assert!(g.capacity() >= 2);
    /// ```
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Converts from `&GraphemeOwned` to `&Grapheme`
    pub fn as_grapheme(&self) -> &Grapheme<N> {
        let bytes = self.inner.as_slice();
        // SAFETY: This is ok because `[u8]` previously contained `Grapheme`.
        let string = unsafe { <str>::from_utf8_unchecked(bytes) };
        // SAFETY: This is ok because `Grapheme` is `#[repr[transparent]]`.
        unsafe { &*(string as *const str as *const Grapheme<N>) }
    }

    /// Converts from `&mut GraphemeOwned` to `&mut Grapheme`
    pub fn as_grapheme_mut(&mut self) -> &mut Grapheme<N> {
        let bytes = self.inner.as_mut_slice();
        // SAFETY: This is ok because `[u8]` previously contained `Grapheme`.
        let string = unsafe { <str>::from_utf8_unchecked_mut(bytes) };
        // SAFETY: This is ok because `Grapheme` is `#[repr[transparent]]`.
        unsafe { &mut *(string as *mut str as *mut Grapheme<N>) }
    }
}

impl<N: Normalization> Deref for GraphemeOwned<N> {
    type Target = Grapheme<N>;

    fn deref(&self) -> &Self::Target {
        GraphemeOwned::as_grapheme(self)
    }
}

impl<N: Normalization> DerefMut for GraphemeOwned<N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        GraphemeOwned::as_grapheme_mut(self)
    }
}

impl<N: Normalization> Borrow<Grapheme<N>> for GraphemeOwned<N> {
    fn borrow(&self) -> &Grapheme<N> {
        GraphemeOwned::as_grapheme(self)
    }
}

impl<N: Normalization> BorrowMut<Grapheme<N>> for GraphemeOwned<N> {
    fn borrow_mut(&mut self) -> &mut Grapheme<N> {
        GraphemeOwned::as_grapheme_mut(self)
    }
}

impl<N: Normalization> fmt::Debug for GraphemeOwned<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_grapheme(), f)
    }
}

impl<N: Normalization> fmt::Display for GraphemeOwned<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_grapheme(), f)
    }
}

impl<N: Normalization> PartialEq for GraphemeOwned<N> {
    fn eq(&self, other: &Self) -> bool {
        self.deref() == other.deref()
    }
}

impl<N: Normalization> Hash for GraphemeOwned<N> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.deref().hash(state);
    }
}

impl<'src, N: Normalization> From<&'src Grapheme<N>> for GraphemeOwned<N> {
    fn from(value: &'src Grapheme<N>) -> Self {
        Self::from_ref(value)
    }
}

impl<N: Normalization> From<Box<Grapheme<N>>> for GraphemeOwned<N> {
    fn from(value: Box<Grapheme<N>>) -> Self {
        Self::from_box(value)
    }
}

impl<N: Normalization> From<GraphemeOwned<N>> for Box<Grapheme<N>> {
    fn from(value: GraphemeOwned<N>) -> Self {
        value.into_box()
    }
}

/// `MaybeGraphemeOwned` is an optimized version of `Option<GraphemeOwned>`.
///
/// # Examples
///
/// You can create `MaybeGraphemeOwned` from `Option<GraphemeOwned>` using
/// [`MaybeGraphemeOwned::from`]:
///
/// ```
/// # use grapheme::prelude::*;
/// let h = MaybeGraphemeOwned::from(Some(g!('h').to_owned()));
/// ```
///
/// # Representation
///
/// `MaybeGraphemeOwned` is arranged in the same way as [`GraphemeOwned`], but
/// has a buffer length of zero when it contains `None`.
#[derive(Default, Clone, Eq)]
#[repr(transparent)]
pub struct MaybeGraphemeOwned<N: Normalization = Unnormalized> {
    phantom: PhantomData<N>,
    inner: GraphemeOwnedInner,
}

impl<N: Normalization> MaybeGraphemeOwned<N> {
    /// Converts from `Option<GraphemeOwned>` to `MaybeGraphemeOwned`.
    pub fn from_option(value: Option<GraphemeOwned<N>>) -> Self {
        let inner = value.map(|grapheme| grapheme.inner).unwrap_or_default();
        Self {
            inner,
            phantom: PhantomData,
        }
    }

    /// Converts from `MaybeGraphemeOwned` to `Option<GraphemeOwned>`.
    pub fn into_option(self) -> Option<GraphemeOwned<N>> {
        self.is_some().then(|| GraphemeOwned {
            inner: self.inner,
            phantom: PhantomData,
        })
    }

    /// Returns `true` if the option is a [`Some`] value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let x: MaybeGraphemeOwned = Some(g!('h').to_owned()).into();
    /// assert_eq!(x.is_some(), true);
    ///
    /// let x: MaybeGraphemeOwned = None.into();
    /// assert_eq!(x.is_some(), false);
    /// ```
    #[must_use = "if you intended to assert that this has a value, consider `.unwrap()` instead"]
    #[inline]
    pub fn is_some(&self) -> bool {
        !self.is_none()
    }

    /// Returns `true` if the option is a [`None`] value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let x: MaybeGraphemeOwned = Some(g!('h').to_owned()).into();
    /// assert_eq!(x.is_none(), false);
    ///
    /// let x: MaybeGraphemeOwned = None.into();
    /// assert_eq!(x.is_none(), true);
    /// ```
    #[must_use]
    #[inline]
    pub fn is_none(&self) -> bool {
        self.inner.is_empty()
    }

    /// Converts from `&MaybeGraphemeOwned` to `Option<&GraphemeOwned>`
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let grapheme: MaybeGraphemeOwned = Some(g!('h').to_owned()).into();
    /// // First, cast `MaybeGraphemeOwned` to `Option<&GraphemeOwned>` with
    /// // `as_ref`, then consume *that* with `map`, leaving `text` on the
    /// // stack.
    /// let length: Option<_> = grapheme.as_ref().map(|g| g.len());
    /// println!("still can print grapheme: {grapheme:?}");
    /// ```
    pub fn as_ref(&self) -> Option<&GraphemeOwned<N>> {
        self.is_some().then(|| {
            let inner = &self.inner;
            // SAFETY: This is ok because `&GraphemeOwned` is `#[repr[transparent]]`.
            unsafe { &*(inner as *const GraphemeOwnedInner as *const GraphemeOwned<N>) }
        })
    }

    /// Converts from `&mut MaybeGraphemeOwned` to `Option<&mut GraphemeOwned>`
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let mut x: MaybeGraphemeOwned = Some(g!('h').to_owned()).into();
    /// match x.as_mut() {
    ///     Some(v) => *v = g!('e').into(),
    ///     None => {},
    /// }
    /// assert_eq!(x, Some(g!('e').to_owned()).into());
    /// ```
    pub fn as_mut(&mut self) -> Option<&mut GraphemeOwned<N>> {
        self.is_some().then(|| {
            let inner = &mut self.inner;
            // SAFETY: This is ok because `&GraphemeOwned` is `#[repr[transparent]]`.
            unsafe { &mut *(inner as *mut GraphemeOwnedInner as *mut GraphemeOwned<N>) }
        })
    }

    /// Converts from `MaybeGraphemeOwned` (or `&MaybeGraphemeOwned`) to
    /// `Option<&Grapheme>`.
    ///
    /// Leaves the original `MaybeGraphemeOwned` in-place, creating a new one
    /// with a reference to the original one, additionally coercing the
    /// contents via [`Deref`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use grapheme::prelude::*;
    /// let x: MaybeGraphemeOwned = Some(g!('h').to_owned()).into();
    /// assert_eq!(x.as_deref(), Some(g!('h')));
    ///
    /// let x: MaybeGraphemeOwned = None.into();
    /// assert_eq!(x.as_deref(), None);
    /// ```
    pub fn as_deref(&self) -> Option<&Grapheme<N>> {
        self.as_ref().map(|grapheme| grapheme.deref())
    }

    /// Converts from `MaybeGraphemeOwned` (or `&mut MaybeGraphemeOwned`) to
    /// `Option<&mut Grapheme>`
    ///
    /// Leaves the original `MaybeGraphemeOwned` in-place, creating a new one
    /// containing a mutable reference to the inner type's [`Deref::Target`]
    /// type.
    pub fn as_deref_mut(&mut self) -> Option<&mut Grapheme<N>> {
        self.as_mut().map(|grapheme| grapheme.deref_mut())
    }
}

impl<N: Normalization> fmt::Debug for MaybeGraphemeOwned<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.as_ref(), f)
    }
}

impl<N: Normalization> PartialEq for MaybeGraphemeOwned<N> {
    fn eq(&self, other: &Self) -> bool {
        self.as_deref() == other.as_deref()
    }
}

impl<N: Normalization> Hash for MaybeGraphemeOwned<N> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_deref().hash(state);
    }
}

impl<N: Normalization> From<Option<GraphemeOwned<N>>> for MaybeGraphemeOwned<N> {
    fn from(value: Option<GraphemeOwned<N>>) -> Self {
        Self::from_option(value)
    }
}

impl<N: Normalization> From<MaybeGraphemeOwned<N>> for Option<GraphemeOwned<N>> {
    fn from(value: MaybeGraphemeOwned<N>) -> Self {
        value.into_option()
    }
}

/// Converts from `&Grapheme` to `GraphemeOwned<N>`.
pub(crate) fn normalize<N: NormalizationLossless>(grapheme: &Grapheme) -> Cow<'_, Grapheme<N>> {
    let mut buf = GraphemeOwnedInner::new();
    let mut iter_u = grapheme.as_str().char_indices();

    for usv_n in N::iter(grapheme.as_str()) {
        if buf.is_empty() {
            let mut init_buf = |s: &str| {
                let start = s.as_bytes();
                buf = GraphemeOwnedInner::from_slice(start);
            };

            match iter_u.next() {
                Some((i, usv_u)) => {
                    if usv_n != usv_u {
                        init_buf(&grapheme.as_str()[0..i])
                    } else {
                        continue;
                    }
                }

                None => init_buf(grapheme.as_str()),
            };
        }

        let mut b = [0u8; 4];
        let res = usv_n.encode_utf8(&mut b);
        let res = res.as_bytes();
        buf.reserve(res.len());
        for byte in res {
            buf.push(*byte);
        }
    }

    if buf.is_empty() {
        let value = grapheme.as_str();
        // SAFETY: this is okay, because it has already been verified that the content
        // corresponds to the normalized form
        let g = unsafe { Grapheme::from_usvs_unchecked(value) };

        Cow::Borrowed(g)
    } else {
        let g = GraphemeOwned {
            inner: buf,
            phantom: PhantomData,
        };

        Cow::Owned(g)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{Grapheme, Nfc, Nfd};
    use unicode_normalization::UnicodeNormalization;

    #[test]
    fn normalize_test() {
        let saddle = Grapheme::<Unnormalized>::from_usvs("C\u{0304}\u{0327}").unwrap();

        assert_eq!(
            saddle.as_str().nfd().collect::<String>(),
            "C\u{0327}\u{0304}"
        );
        assert_eq!(saddle.as_str().nfc().collect::<String>(), "Ç\u{304}");

        let saddle_u = normalize::<Unnormalized>(saddle);
        assert!(matches!(saddle_u, Cow::Borrowed(_)));
        assert_eq!(saddle_u.as_str(), "C\u{0304}\u{0327}");

        let saddle_d = normalize::<Nfd>(saddle);
        assert!(matches!(saddle_d, Cow::Owned(_)));
        assert_eq!(saddle_d.as_str(), "C\u{0327}\u{0304}");

        let saddle_c = normalize::<Nfc>(saddle);
        assert!(matches!(saddle_c, Cow::Owned(_)));
        assert_eq!(saddle_c.as_str(), "Ç\u{304}");
    }
}
