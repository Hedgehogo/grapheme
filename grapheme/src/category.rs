use crate::Grapheme;

#[expect(dead_code)]
pub(crate) enum Categorized<'g> {
    Control(&'g Grapheme),
    Hangul(&'g Grapheme, char),
    Extend(&'g Grapheme, char),
    SpacingMark(&'g Grapheme, char),
    Prepend(char, &'g Grapheme),
    Consonant(&'g Grapheme, char),
    ExtendedPictographic(&'g Grapheme, char),
    RegionalIndicator(char, char),
    Any(char),
}
