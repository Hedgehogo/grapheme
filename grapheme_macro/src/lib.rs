#![doc = include_str!("../README.md")]

use proc_macro::TokenStream;
use quote::quote;
use syn::LitStr;
use unicode_segmentation::UnicodeSegmentation;

#[inline]
fn grapheme_macro(literal: syn::Lit) -> TokenStream {
    let span = literal.span();
    match literal {
        syn::Lit::Str(lit_str) => {
            let string = lit_str.value();
            let mut iter = string.graphemes(true);

            match (iter.next(), iter.next()) {
                (Some(_), Some(_)) => {
                    panic!("{span:?}: string must not contain more than one grapheme cluster.")
                }

                (Some(_), _) => {
                    let generated = quote! {
                        unsafe { ::grapheme::Grapheme::from_code_points_unchecked(#lit_str) }
                    };
                    generated.into()
                }

                _ => panic!("{span:?}: string must not be empty."),
            }
        }

        syn::Lit::Char(lit_char) => {
            let string: String = std::iter::once(lit_char.value()).collect();
            let lit_str = LitStr::new(&string, lit_char.span());
            let generated = quote! {
                unsafe { ::grapheme::Grapheme::from_code_points_unchecked(#lit_str) }
            };
            generated.into()
        }

        _ => panic!("{span:?}: a utf8 string literal or a char literal was expected"),
    }
}

/// Literal for `Grapheme`
#[proc_macro]
pub fn g(input: TokenStream) -> TokenStream {
    grapheme_macro(syn::parse(input).unwrap())
}

#[inline]
fn graphemes_macro(literal: syn::LitStr) -> TokenStream {
    let generated = quote! {
        unsafe { ::grapheme::Graphemes::from_code_points(#literal) }
    };
    generated.into()
}

/// Literal for `Graphemes`
#[proc_macro]
pub fn gs(input: TokenStream) -> TokenStream {
    graphemes_macro(syn::parse(input).unwrap())
}
