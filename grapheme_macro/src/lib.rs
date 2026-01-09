#![doc = include_str!("../README.md")]

use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::quote;
use syn::{Ident, Lit, LitStr, Path, punctuated::Punctuated, token::PathSep};
use unicode_normalization::UnicodeNormalization;
use unicode_segmentation::UnicodeSegmentation;

#[derive(Debug)]
enum Normalization {
    Unnormalized,
    Nfd,
    Nfc,
    Nfkd,
    Nfkc,
}

impl Normalization {
    fn from_suffix(suffix: &str, span: Span) -> syn::Result<Self> {
        match suffix {
            "" => Ok(Normalization::Unnormalized),
            "u" => Ok(Normalization::Unnormalized),
            "d" => Ok(Normalization::Nfd),
            "c" => Ok(Normalization::Nfc),
            "kd" => Ok(Normalization::Nfkd),
            "kc" => Ok(Normalization::Nfkc),
            _ => {
                let message = "suffix can only be 'u', 'd', 'c', 'kd' or 'kc'";
                Err(syn::Error::new(span, message))
            }
        }
    }

    fn to_path(&self) -> Path {
        let new_segment = |ident| syn::PathSegment {
            ident: Ident::new(ident, Span::call_site()),
            arguments: syn::PathArguments::None,
        };

        let name = format!("{:?}", self);
        let mut segments = Punctuated::new();
        segments.push(new_segment("grapheme"));
        segments.push(new_segment("prelude"));
        segments.push(new_segment(&name));

        let spans = [Span::call_site(); 2];
        Path {
            leading_colon: Some(PathSep { spans }),
            segments,
        }
    }

    fn normalize(&self, s: String) -> String {
        match self {
            Normalization::Unnormalized => s,
            Normalization::Nfd => s.chars().nfd().collect(),
            Normalization::Nfc => s.chars().nfc().collect(),
            Normalization::Nfkd => s.chars().nfkd().collect(),
            Normalization::Nfkc => s.chars().nfkc().collect(),
        }
    }
}

#[inline]
fn grapheme_macro(literal: Lit) -> syn::Result<TokenStream2> {
    let span = literal.span();
    let normalization = Normalization::from_suffix(literal.suffix(), span)?;
    let path = normalization.to_path();
    let inner = match literal {
        Lit::Str(lit_str) => {
            let string = lit_str.value();
            let mut iter = string.graphemes(true);

            match (iter.next(), iter.next()) {
                (Some(_), Some(_)) => {
                    let message = "string must not contain more than one grapheme cluster";
                    return Err(syn::Error::new_spanned(lit_str, message));
                }

                (Some(_), _) => string,

                _ => {
                    let message = "string must not be empty";
                    return Err(syn::Error::new_spanned(lit_str, message));
                }
            }
        }

        Lit::Char(lit_char) => std::iter::once(lit_char.value()).collect(),

        _ => {
            let message = "a utf8 string literal or a char literal was expected";
            return Err(syn::Error::new_spanned(literal, message));
        }
    };

    let inner = normalization.normalize(inner);
    let lit_str = LitStr::new(&inner, span);
    Ok(quote! {
        unsafe { ::grapheme::Grapheme::<#path>::from_usvs_unchecked(#lit_str) }
    })
}

/// Creates a `Grapheme` from a string literal or a char literal.
///
/// One of the following suffixes can be placed after the literal:
/// - `u` - creates a `Grapheme<Unnormalized>`
/// - `d` - creates a `Grapheme<Nfd>`
/// - `c` - creates a `Grapheme<Nfc>`
/// - `kd` - creates a `Grapheme<Nfkd>`
/// - `kc` - creates a `Grapheme<Nfkc>`
///
/// If the suffix is missing, `Grapheme<Unnormalized>` will be created by default.
///
/// If the string is not normalized according to the suffix, it will be normalized
/// forcibly:
/// ```no_compile
/// let c = g!("\u0043\u0327"c);
/// assert_eq!(c.as_str(), "\u00c7");
/// ```
#[proc_macro]
pub fn g(input: TokenStream) -> TokenStream {
    let result = syn::parse(input).and_then(grapheme_macro);

    match result {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

#[inline]
fn graphemes_macro(literal: LitStr) -> syn::Result<TokenStream2> {
    let span = literal.span();
    let normalization = Normalization::from_suffix(literal.suffix(), span)?;
    let _path = normalization.to_path();
    let inner = normalization.normalize(literal.value());
    let lit_str = LitStr::new(&inner, span);
    Ok(quote! {
        ::grapheme::Graphemes::from_usvs(#lit_str)
    })
}

/// Literal for `Graphemes`
#[proc_macro]
pub fn gs(input: TokenStream) -> TokenStream {
    let result = syn::parse(input).and_then(graphemes_macro);

    match result {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

#[cfg(test)]
mod tests {
    use crate::grapheme_macro;

    use super::*;

    #[test]
    fn grapheme_macro_test() {
        {
            let with_nf = syn::parse2(quote! { 'a' }).unwrap();
            let output = grapheme_macro(with_nf).unwrap();
            let expected = quote! { unsafe { ::grapheme::Grapheme::<::grapheme::prelude::Unnormalized>::from_usvs_unchecked("a") } };
            assert_eq!(output.to_string(), expected.to_string());
        }
        {
            let with_nf = syn::parse2(quote! { "a" }).unwrap();
            let output = grapheme_macro(with_nf).unwrap();
            let expected = quote! { unsafe { ::grapheme::Grapheme::<::grapheme::prelude::Unnormalized>::from_usvs_unchecked("a") } };
            assert_eq!(output.to_string(), expected.to_string());
        }
        {
            let with_nf = syn::parse2(quote! { "a"u }).unwrap();
            let output = grapheme_macro(with_nf).unwrap();
            let expected = quote! { unsafe { ::grapheme::Grapheme::<::grapheme::prelude::Unnormalized>::from_usvs_unchecked("a") } };
            assert_eq!(output.to_string(), expected.to_string());
        }
        {
            let with_nf = syn::parse2(quote! { "a"d }).unwrap();
            let output = grapheme_macro(with_nf).unwrap();
            let expected = quote! { unsafe { ::grapheme::Grapheme::<::grapheme::prelude::Nfd>::from_usvs_unchecked("a") } };
            assert_eq!(output.to_string(), expected.to_string());
        }
    }

    #[test]
    #[should_panic]
    fn grapheme_macro_test_not_eq() {
        let with_nf = syn::parse2(quote! { "a" }).unwrap();
        let output = grapheme_macro(with_nf).unwrap();
        let expected = quote! { unsafe { ::grapheme::Grapheme::<::grapheme::prelude::Unnormalized>::from_usvs_unchecked("b") } };
        assert_eq!(output.to_string(), expected.to_string());
    }

    #[test]
    #[should_panic]
    fn grapheme_macro_test_not_unique() {
        let with_nf = syn::parse2(quote! { "aa" }).unwrap();
        let _ = grapheme_macro(with_nf).unwrap();
    }

    #[test]
    #[should_panic]
    fn grapheme_macro_test_not_inner() {
        let with_nf = syn::parse2(quote! { 10 }).unwrap();
        let _ = grapheme_macro(with_nf).unwrap();
    }

    #[test]
    #[should_panic]
    fn grapheme_macro_test_not_nf() {
        let with_nf = syn::parse2(quote! { "a"m }).unwrap();
        let _ = grapheme_macro(with_nf).unwrap();
    }

    #[test]
    fn graphemes_macro_test() {
        {
            let with_nf = syn::parse2(quote! { "a" }).unwrap();
            let output = graphemes_macro(with_nf).unwrap();
            let expected = quote! { ::grapheme::Graphemes::from_usvs("a") };
            assert_eq!(output.to_string(), expected.to_string());
        }
        {
            let with_nf = syn::parse2(quote! { "aa"u }).unwrap();
            let output = graphemes_macro(with_nf).unwrap();
            let expected = quote! { ::grapheme::Graphemes::from_usvs("aa") };
            assert_eq!(output.to_string(), expected.to_string());
        }
    }

    #[test]
    #[should_panic]
    fn graphemes_macro_test_not_eq() {
        let with_nf = syn::parse2(quote! { "a" }).unwrap();
        let output = graphemes_macro(with_nf).unwrap();
        let expected = quote! { ::grapheme::Graphemes::from_usvs("b") };
        assert_eq!(output.to_string(), expected.to_string());
    }

    #[test]
    #[should_panic]
    fn graphemes_macro_test_not_inner() {
        let with_nf = syn::parse2(quote! { 10 }).unwrap();
        let _ = graphemes_macro(with_nf).unwrap();
    }
}
