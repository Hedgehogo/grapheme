use crate::Grapheme;
use ucd::{Codepoint, GraphemeClusterBreak};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Conjunct<'g> {
    pub(crate) consonant: &'g Grapheme,
    pub(crate) linker: char,
    pub(crate) invalid_extend: &'g str,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Modification<'g> {
    Extend(char),           // GB9
    Zwj,                    // GB9
    SpacingMark(char),      // GB9a
    Prepend(char),          // GB9b
    Conjunct(Conjunct<'g>), // GB9c
}

impl<'g> Modification<'g> {
    #[cfg(test)]
    pub(crate) fn conjunct(consonant: &'g Grapheme, linker: char, invalid_extend: &'g str) -> Self {
        Self::Conjunct(Conjunct {
            consonant,
            linker,
            invalid_extend,
        })
    }
}

pub(crate) fn is_incb_linker(c: char) -> bool {
    matches!(c, |'\u{94D}'| '\u{9CD}'
        | '\u{ACD}'
        | '\u{B4D}'
        | '\u{C4D}'
        | '\u{D4D}')
}

fn to_conjunct(grapheme: &Grapheme) -> Option<(&Grapheme, Conjunct)> {
    // C = \p{InCB=Consonant}
    // E = \p{InCB=Extend}
    // L = \p{InCB=Linker}
    let mut iter = grapheme.as_str().char_indices();

    // Any grapheme has at least 1 code point.
    //
    // Separate `C` from `E* L [EL]* C Any*`
    let (_, _consonant) = iter.next().unwrap();

    // `C E* L [EL]* C Any*`
    //       ^ - Looking for this
    let maybe_conjunct = iter.find(|(_, c)| is_incb_linker(*c));

    if let Some((linker_i, linker)) = maybe_conjunct {
        // The grapheme has at least the first code point and the found one,
        // that is, two. The only options for how L could not be at the
        // beginning are GB9, GB9a and GB9c. But GB9 and GB9a would have
        // already been processed, so only GB9c remains. This means that there
        // is at least one C next.
        //
        // `C E* L [EL]* C Any*`
        //               ^ - Looking for this
        let (rest_i, _) = iter
            .find(|(_, c)| {
                !matches!(
                    c.grapheme_cluster_break(),
                    GraphemeClusterBreak::Extend | GraphemeClusterBreak::SpacingMark
                )
            })
            .unwrap();

        // Separate `C E* L [EL]*` from `C Any*`
        let (conjunct, rest) = grapheme.as_str().split_at(rest_i);

        // Separate `C E*` from `L [EL]*`
        let (consonant, invalid_extend) = conjunct.split_at(linker_i);

        // Separate `L` from `[EL]*`
        let mut iter = invalid_extend.chars();
        let _ = iter.next().unwrap();
        let invalid_extend = iter.as_str();

        let rest = Grapheme::from_code_points(rest).unwrap();
        let conjunct = Conjunct {
            consonant: Grapheme::from_code_points(consonant).unwrap(),
            linker,
            invalid_extend,
        };

        return Some((rest, conjunct));
    }

    None
}

pub(crate) fn to_modified(grapheme: &Grapheme) -> Option<(&Grapheme, Modification)> {
    if grapheme.is_code_point() {
        return None;
    }

    let (rest, last) = grapheme.split_rev();

    match last.grapheme_cluster_break() {
        GraphemeClusterBreak::Extend => {
            let grapheme = Grapheme::from_code_points(rest).unwrap();
            return Some((grapheme, Modification::Extend(last)));
        }

        GraphemeClusterBreak::ZWJ => {
            let grapheme = Grapheme::from_code_points(rest).unwrap();
            return Some((grapheme, Modification::Zwj));
        }

        GraphemeClusterBreak::SpacingMark => {
            let grapheme = Grapheme::from_code_points(rest).unwrap();
            return Some((grapheme, Modification::SpacingMark(last)));
        }

        _ => {}
    }

    let (first, rest) = grapheme.split();

    if let GraphemeClusterBreak::Prepend = first.grapheme_cluster_break() {
        let grapheme = Grapheme::from_code_points(rest).unwrap();
        return Some((grapheme, Modification::Prepend(first)));
    }

    to_conjunct(grapheme).map(|(rest, conjunct)| (rest, Modification::Conjunct(conjunct)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_categorize() {
        let g = |s| Grapheme::from_code_points(s).unwrap();
        assert_eq!(
            to_modified(g("y̆")),
            Some((g("y"), Modification::Extend('\u{0306}')))
        );
        assert_eq!(
            to_modified(g("y\u{200C}")),
            Some((g("y"), Modification::Extend('\u{200C}')))
        );
        assert_eq!(
            to_modified(g("y\u{200D}")),
            Some((g("y"), Modification::Zwj))
        );
        assert_eq!(
            to_modified(g("நி")),
            Some((g("ந"), Modification::SpacingMark('\u{0BBF}')))
        );
        assert_eq!(
            to_modified(g("؀ا")),
            Some((g("\u{0627}"), Modification::Prepend('؀')))
        );
        assert_eq!(
            to_modified(g("र्क")),
            Some((g("क"), Modification::conjunct(g("र"), '्', "")))
        );
        assert_eq!(to_modified(g("a")), None);
    }
}
