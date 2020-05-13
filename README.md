# liblet-rust

[![Crates.io](https://img.shields.io/crates/v/liblet)](https://crates.io/crates/liblet)
[![GitHub Workflow Status (branch)](https://img.shields.io/github/workflow/status/kristiannotari/liblet-rust/build/v0.1.1)](https://github.com/kristiannotari/liblet-rust/actions?query=workflow%3Abuild+branch%3Av0.1.1)
[![Codecov branch](https://img.shields.io/codecov/c/github/kristiannotari/liblet-rust/master)](https://codecov.io/gh/kristiannotari/liblet-rust/branch/master)
[![contributions welcome](https://img.shields.io/badge/contributions-welcome-brightgreen.svg?style=flat)](https://github.com/kristiannotari/liblet-rust/issues)

> coverage disclaimer: percentage of code coverage is not reliable as of now, due to some issues with the tool used (cargo tarpaulin). If you have any advices, feel free to contact me.

Porting project for the [liblet library](https://github.com/let-unimi/liblet) of the University of Milan course "Linguaggi e Traduttori" (Languages and Translators) in Rust.

A generic and _possibly_ updated roadmap/to-do list is available in this repo project.
If you want to contribute or correct any errors, please do so opening issues or creating pull requests.

This is also a learning project, used to better comprehend both the course topics and the rust programming language.

## Features

[![changelog](https://img.shields.io/badge/changelog-see-lightgrey)](https://github.com/kristiannotari/liblet-rust/blob/master/CHANGELOG.md)

More info available at the [docs](https://docs.rs/liblet/0.1.0).

> Following the official liblet [documentation](https://liblet.readthedocs.io).

- [x] symbol (new)
- [x] production
- [ ] item (not planned)
- [x] grammar
- [x] derivation
- [ ] transition
- [ ] automaton
- [ ] antlr support (not planned)
- [ ] rich display (not planned yet)
- [ ] utilities (not planned yet)

> Notice that this project doesn't make any difference between grammar types at the moment. In fact, you won't find parameters like "context_free" flags for switching behaviour depending on grammar type, because there's no such equivalent switch in implementation planned for this library at the moment. This library implementation ignores the grammar type concepts, at least at the moment, for those features which don't need a strict grammar type level (eg. grammar creation, grammar restrict_to function, etc.).

## Examples

- [basics](examples/basics.rs)
- [symbols](examples/symbols.rs)
- [productions](examples/productions.rs)
- [derivations](examples/derivations.rs)

## License

Licensed under either of

- Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
