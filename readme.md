This crate aims to prevent the combinatorial explosion of `str` splitting APIs.

The explosions comes from the combinations of the following:

- reversed (`rsplit`, `rsplit_once`, `rsplit_terminator`, `rsplitn`)
- inclusive (`split_inclusive`)
- terminated (`split_terminator`, `rsplit_terminator`)
- limited (`splitn`, `rsplitn`)
- once (`split_once`, `rsplit_once`)

As you can see, various combinations are currently missing (not exhaustive):

- inclusive + reversed
- inclusive + limited
- inclusive + once
- inclusive + reversed + limited
- inclusive + reversed + once

Plus, it may be useful to have right- or left-inclusive versions.

This could quickly balloon the API surface of `str` which is not ideal.

Instead, this crate implements a kind of builder API. It does this two different ways:
- using const generic parameters to store the direction and inclusion
- using struct wrapper type states to store the direction and inclusion

Both have almost identical APIs. Usage looks like this:

```rust
use str_splitter::combinators::SplitExt;
// OR
// use str_splitter::const_generics::SplitExt;

// `split`
let v: Vec<&str> = "lionXXtigerXleopard".splitter('X').collect();
assert_eq!(v, ["lion", "", "tiger", "leopard"]);

// `splitn`
let v: Vec<&str> = "Mary had a little lambda".splitter(' ').with_limit(3).collect();
assert_eq!(v, ["Mary", "had", "a little lambda"]);

// `rsplitn`
let v: Vec<&str> = "lion::tiger::leopard".splitter("::").to_reversed().with_limit(2).collect();
assert_eq!(v, ["leopard", "lion::tiger"]);

// `rsplit_terminator`
let v: Vec<&str> = "A.B.".splitter('.').to_terminated().to_reversed().collect();
assert_eq!(v, ["B", "A"]);

// `rsplit_inclusive_once` if it existed
assert_eq!("cfg=foo=bar".splitter('=').to_inclusive().to_reversed().once(), Some(("cfg=foo", "=bar")));
```

The idea is that the struct returned by the existing `split` method would add the various 
modifier methods that `Splitter` has in this library.

This crate relies on the unstable `Pattern` trait, so requires nightly Rust.
