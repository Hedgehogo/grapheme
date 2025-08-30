grapheme
=========
[![Crates.io](https://img.shields.io/crates/v/grapheme.svg)](https://crates.io/crates/grapheme)
[![Documentation](https://docs.rs/grapheme/badge.svg)](https://docs.rs/grapheme)

This crate offers types related to extended Unicode grapheme clusters, which
are replacements for the standard types `char` and `str`.

## Features

- Replacement for the standard library `char` and `str` types.
- Optimized owning grapheme type.
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

let yes = gs!("a 6 y̆ நி");

let mut iter = yes.iter().filter(|g| g.is_alphabetic());

assert_eq!(Some(g!("a")), iter.next());
assert_eq!(Some(g!("y̆")), iter.next()); // g'y̆', not like str!
assert_eq!(Some(g!("நி")), iter.next());

assert_eq!(None, iter.next());
```
