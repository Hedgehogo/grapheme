use crate::Grapheme;
use ucd::{Codepoint, GraphemeClusterBreak};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Modification {
    Extend(char),      // GB9
    Zwj(char),         // GB9
    SpacingMark(char), // GB9a
    Prepend(char),     // GB9b
}

pub(crate) fn to_modified(grapheme: &Grapheme) -> Option<(&Grapheme, Modification)> {
    let (first, rest) = grapheme.split();
    let first_category = first.grapheme_cluster_break();

    if let GraphemeClusterBreak::Prepend = first_category {
        let grapheme = Grapheme::from_code_points(rest).unwrap();
        return Some((grapheme, Modification::Prepend(first)));
    }

    let (rest, last) = grapheme.split_rev();

    match last.grapheme_cluster_break() {
        GraphemeClusterBreak::Extend => {
            let grapheme = Grapheme::from_code_points(rest).unwrap();
            Some((grapheme, Modification::Extend(last)))
        }

        GraphemeClusterBreak::ZWJ => {
            let grapheme = Grapheme::from_code_points(rest).unwrap();
            Some((grapheme, Modification::Zwj(last)))
        }

        GraphemeClusterBreak::SpacingMark => {
            let grapheme = Grapheme::from_code_points(rest).unwrap();
            Some((grapheme, Modification::SpacingMark(last)))
        }

        _ => None,
    }
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
            Some((g("y"), Modification::Zwj('\u{200D}')))
        );
        assert_eq!(
            to_modified(g("நி")),
            Some((g("ந"), Modification::SpacingMark('\u{0BBF}')))
        );
        assert_eq!(
            to_modified(g("؅y")),
            Some((g("y"), Modification::Prepend('\u{0605}')))
        );
        assert_eq!(to_modified(g("a")), None);
    }
}
