grapheme
=========

This crate offers types related to Unicode extended grapheme clusters, which
are replacements for the standard types `char` and `str`.

## Features

- Replacement for the standard library `char` and `str` types.
- Macros `g!` and `gs!`, used as literals to create crate types, performing
  all necessary checks at compile time.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
grapheme = "1"
```

Then:

```rust
use grapheme::prelude::*;

let yes = gs!("y̆es");

let mut iter = yes.iter();

assert_eq!(Some(g!("y̆")), iter.next()); // g'y̆', not like str!
assert_eq!(Some(g!('e')), iter.next());
assert_eq!(Some(g!('s')), iter.next());

assert_eq!(None, iter.next());
```
