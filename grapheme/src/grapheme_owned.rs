//! Utilities for the `GraphemeOwned` type.
//!
//! *[See also the `GraphemeOwned` type.](GraphemeOwned)*

use super::Grapheme;
use smallvec::SmallVec;
use std::{
    fmt,
    hash::Hash,
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
pub struct GraphemeOwned(GraphemeOwnedInner);

impl GraphemeOwned {
    /// Converts from `&Grapheme` to `GraphemeOwned`.
    pub fn from_ref(grapheme: &Grapheme) -> Self {
        let bytes = grapheme.as_bytes();
        Self(SmallVec::from_slice(bytes))
    }

    /// Converts from `Box<Grapheme>` to `GraphemeOwned`
    pub fn from_box(grapheme: Box<Grapheme>) -> GraphemeOwned {
        let bytes: Box<[u8]> = grapheme.into();
        Self(SmallVec::from_vec(bytes.into()))
    }

    /// Converts from `GraphemeOwned` to `Box<Grapheme>`
    pub fn into_box(self) -> Box<Grapheme> {
        let bytes = self.0.into_boxed_slice();
        // SAFETY: This is ok because `[u8]` previously contained `Grapheme`.
        let string = unsafe { str::from_boxed_utf8_unchecked(bytes) };
        // SAFETY: This is ok because `Grapheme` is `#[repr[transparent]]`.
        unsafe { Box::from_raw(Box::<str>::into_raw(string) as *mut Grapheme) }
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
        self.0.capacity()
    }

    /// Converts from `&GraphemeOwned` to `&Grapheme`
    pub fn as_grapheme(&self) -> &Grapheme {
        let bytes = self.0.as_slice();
        // SAFETY: This is ok because `[u8]` previously contained `Grapheme`.
        let string = unsafe { <str>::from_utf8_unchecked(bytes) };
        // SAFETY: This is ok because `Grapheme` is `#[repr[transparent]]`.
        unsafe { &*(string as *const str as *const Grapheme) }
    }

    /// Converts from `&mut GraphemeOwned` to `&mut Grapheme`
    pub fn as_grapheme_mut(&mut self) -> &mut Grapheme {
        let bytes = self.0.as_mut_slice();
        // SAFETY: This is ok because `[u8]` previously contained `Grapheme`.
        let string = unsafe { <str>::from_utf8_unchecked_mut(bytes) };
        // SAFETY: This is ok because `Grapheme` is `#[repr[transparent]]`.
        unsafe { &mut *(string as *mut str as *mut Grapheme) }
    }
}

impl Deref for GraphemeOwned {
    type Target = Grapheme;

    fn deref(&self) -> &Self::Target {
        GraphemeOwned::as_grapheme(self)
    }
}

impl DerefMut for GraphemeOwned {
    fn deref_mut(&mut self) -> &mut Self::Target {
        GraphemeOwned::as_grapheme_mut(self)
    }
}

impl fmt::Debug for GraphemeOwned {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_grapheme(), f)
    }
}

impl fmt::Display for GraphemeOwned {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_grapheme(), f)
    }
}

impl PartialEq for GraphemeOwned {
    fn eq(&self, other: &Self) -> bool {
        self.deref() == other.deref()
    }
}

impl Hash for GraphemeOwned {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.deref().hash(state);
    }
}

impl<'src> From<&'src Grapheme> for GraphemeOwned {
    fn from(value: &'src Grapheme) -> Self {
        Self::from_ref(value)
    }
}

impl From<Box<Grapheme>> for GraphemeOwned {
    fn from(value: Box<Grapheme>) -> Self {
        Self::from_box(value)
    }
}

impl From<GraphemeOwned> for Box<Grapheme> {
    fn from(value: GraphemeOwned) -> Self {
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
pub struct MaybeGraphemeOwned(GraphemeOwnedInner);

impl MaybeGraphemeOwned {
    /// Converts from `Option<GraphemeOwned>` to `MaybeGraphemeOwned`.
    pub fn from_option(value: Option<GraphemeOwned>) -> Self {
        Self(value.map(|grapheme| grapheme.0).unwrap_or_default())
    }

    /// Converts from `MaybeGraphemeOwned` to `Option<GraphemeOwned>`.
    pub fn into_option(self) -> Option<GraphemeOwned> {
        self.is_some().then(|| GraphemeOwned(self.0))
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
        self.0.is_empty()
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
    /// let length: Option<usize> = grapheme.as_ref().map(|g| g.len());
    /// println!("still can print grapheme: {grapheme:?}");
    /// ```
    pub fn as_ref(&self) -> Option<&GraphemeOwned> {
        self.is_some().then(|| {
            let inner = &self.0;
            // SAFETY: This is ok because `&GraphemeOwned` is `#[repr[transparent]]`.
            unsafe { &*(inner as *const GraphemeOwnedInner as *const GraphemeOwned) }
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
    pub fn as_mut(&mut self) -> Option<&mut GraphemeOwned> {
        self.is_some().then(|| {
            let inner = &mut self.0;
            // SAFETY: This is ok because `&GraphemeOwned` is `#[repr[transparent]]`.
            unsafe { &mut *(inner as *mut GraphemeOwnedInner as *mut GraphemeOwned) }
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
    pub fn as_deref(&self) -> Option<&Grapheme> {
        self.as_ref().map(|grapheme| grapheme.deref())
    }

    /// Converts from `MaybeGraphemeOwned` (or `&mut MaybeGraphemeOwned`) to
    /// `Option<&mut Grapheme>`
    ///
    /// Leaves the original `MaybeGraphemeOwned` in-place, creating a new one
    /// containing a mutable reference to the inner type's [`Deref::Target`]
    /// type.
    pub fn as_deref_mut(&mut self) -> Option<&mut Grapheme> {
        self.as_mut().map(|grapheme| grapheme.deref_mut())
    }
}

impl fmt::Debug for MaybeGraphemeOwned {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.as_ref(), f)
    }
}

impl PartialEq for MaybeGraphemeOwned {
    fn eq(&self, other: &Self) -> bool {
        self.as_deref() == other.as_deref()
    }
}

impl Hash for MaybeGraphemeOwned {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_deref().hash(state);
    }
}

impl From<Option<GraphemeOwned>> for MaybeGraphemeOwned {
    fn from(value: Option<GraphemeOwned>) -> Self {
        Self::from_option(value)
    }
}

impl From<MaybeGraphemeOwned> for Option<GraphemeOwned> {
    fn from(value: MaybeGraphemeOwned) -> Self {
        value.into_option()
    }
}
