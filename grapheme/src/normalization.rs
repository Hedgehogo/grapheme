//! Utilities for the `Normalization` trait.
//!
//! *[See also the `Normalization` trait.](Normalization)*

use crate::Grapheme;
use std::{cmp::Ordering, hash::Hash, str::Chars};
use unicode_normalization::{Decompositions, Recompositions, UnicodeNormalization};

#[inline]
fn map_pair<A, AG, GA, G, O, N: Normalization>(
    ascii: A,
    a_g: AG,
    g_a: GA,
    grapheme: G,
) -> impl FnOnce(&Grapheme<N>, &Grapheme<N>) -> O
where
    A: FnOnce(&u8, &u8) -> O,
    AG: FnOnce(u8, &Grapheme<N>) -> O,
    GA: FnOnce(&Grapheme<N>, u8) -> O,
    G: FnOnce(&Grapheme<N>, &Grapheme<N>) -> O,
{
    |first, second| match (first.as_str().len(), second.as_str().len()) {
        (1, 1) => ascii(&first.as_bytes()[0], &second.as_bytes()[0]),
        (1, _) => a_g(first.as_bytes()[0], second),
        (_, 1) => g_a(first, second.as_bytes()[0]),
        _ => grapheme(first, second),
    }
}

#[inline]
fn map_usvs<U, O, N: Normalization>(usv: U, grapheme: O) -> impl FnOnce(&Grapheme<N>) -> O
where
    U: FnOnce(char) -> O,
{
    |g| {
        let mut iter = g.as_str().nfd();
        let c = unsafe { iter.next().unwrap_unchecked() };
        if iter.next().is_some() {
            grapheme
        } else {
            usv(c)
        }
    }
}

pub(crate) trait NormalizationSealed {
    type Iter<'src>: Iterator<Item = char>;

    fn iter<'src>(slice: &'src str) -> Self::Iter<'src>;

    fn is_normalized(slice: &str) -> bool {
        Self::iter(slice).eq(slice.chars())
    }
}

/// The `Normalization` trait describes the form of string normalization.
#[expect(private_bounds)]
pub trait Normalization: NormalizationSealed + Sized {
    fn eq_grapheme(lhs: &Grapheme<Self>, rhs: &Grapheme<Self>) -> bool {
        lhs.as_str().eq(rhs.as_str())
    }

    fn cmp_grapheme(lhs: &Grapheme<Self>, rhs: &Grapheme<Self>) -> Ordering {
        lhs.as_str().cmp(rhs.as_str())
    }

    fn hash_grapheme<H: std::hash::Hasher>(grapheme: &Grapheme<Self>, state: &mut H) {
        grapheme.as_str().hash(state);
    }
}

/// The `Unnormalized` type implements the [`Normalization`] trait for cases where the
/// string has not been normalized.
pub struct Unnormalized();

impl NormalizationSealed for Unnormalized {
    type Iter<'src> = Chars<'src>;

    fn iter<'src>(slice: &'src str) -> Self::Iter<'src> {
        slice.chars()
    }

    fn is_normalized(_slice: &str) -> bool {
        true
    }
}

impl Normalization for Unnormalized {
    fn eq_grapheme(lhs: &Grapheme, rhs: &Grapheme) -> bool {
        map_pair(
            PartialEq::eq,
            |a, b| map_usvs(|b| a as u32 == b as u32, false)(b),
            |a, b| map_usvs(|a| a as u32 == b as u32, false)(a),
            |a, b| a.as_str().nfd().eq(b.as_str().nfd()),
        )(lhs, rhs)
    }

    fn cmp_grapheme(lhs: &Grapheme, rhs: &Grapheme) -> Ordering {
        map_pair(
            Ord::cmp,
            |a, b| map_usvs(|b| (a as u32).cmp(&(b as u32)), std::cmp::Ordering::Greater)(b),
            |a, b| map_usvs(|a| (a as u32).cmp(&(b as u32)), std::cmp::Ordering::Less)(a),
            |a, b| a.as_str().nfd().cmp(b.as_str().nfd()),
        )(lhs, rhs)
    }

    fn hash_grapheme<H: std::hash::Hasher>(grapheme: &Grapheme<Self>, state: &mut H) {
        for usv in grapheme.as_str().nfd() {
            state.write_u32(usv as u32);
        }
    }
}

/// The `Nfd` type describes the normalization from D (canonical decomposition).
pub struct Nfd();

impl NormalizationSealed for Nfd {
    type Iter<'src> = Decompositions<Chars<'src>>;

    fn iter<'src>(slice: &'src str) -> Self::Iter<'src> {
        slice.chars().nfd()
    }
}

impl Normalization for Nfd {}

/// The `Nfc` type describes the normalization from C (canonical composition).
pub struct Nfc();

impl NormalizationSealed for Nfc {
    type Iter<'src> = Recompositions<Chars<'src>>;

    fn iter<'src>(slice: &'src str) -> Self::Iter<'src> {
        slice.chars().nfc()
    }
}

impl Normalization for Nfc {}

/// The `Nfkd` type describes the normalization from KD (compatibility decomposition).
pub struct Nfkd();

impl NormalizationSealed for Nfkd {
    type Iter<'src> = Decompositions<Chars<'src>>;

    fn iter<'src>(slice: &'src str) -> Self::Iter<'src> {
        slice.chars().nfkd()
    }
}

impl Normalization for Nfkd {}

/// The `Nfkc` type describes the normalization from KC (compatibility composition).
pub struct Nfkc();

impl NormalizationSealed for Nfkc {
    type Iter<'src> = Recompositions<Chars<'src>>;

    fn iter<'src>(slice: &'src str) -> Self::Iter<'src> {
        slice.chars().nfkc()
    }
}

impl Normalization for Nfkc {}
