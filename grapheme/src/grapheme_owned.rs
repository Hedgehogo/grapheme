//! Utilities for the `GraphemeOwned` type.
//!
//! *[See also the `GraphemeOwned` type.](GraphemeOwned)*

use super::Grapheme;
use smallvec::SmallVec;
use std::{
    fmt,
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
/// `GraphemeOwned::from`:
///
/// ```
/// # use grapheme::prelude::*;
/// let h = GraphemeOwned::from(g!('h'));
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
#[derive(Default, Clone, PartialEq, Eq, Hash)]
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
