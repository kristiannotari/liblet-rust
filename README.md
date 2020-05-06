# liblet-rust

`v0.1.0`

[![Build Status](https://travis-ci.org/kristiannotari/liblet-rust.png?branch=master)](https://travis-ci.org/kristiannotari/liblet-rust)
[![codecov](https://codecov.io/gh/kristiannotari/liblet-rust/branch/master/graph/badge.svg)](https://codecov.io/gh/kristiannotari/liblet-rust)
[![contributions welcome](https://img.shields.io/badge/contributions-welcome-brightgreen.svg?style=flat)](https://github.com/dwyl/esta/issues)

> coverage disclaimer: percentage of code coverage is not reliable as of now, due to some errors in the tools used.

Porting project for the [liblet library](https://github.com/let-unimi/liblet) of the University of Milan course "Linguaggi e Traduttori" (Languages and Translators) in Rust.

This is a learning project, used to better comprehend both the course topics and the rust programming language.

A generic and _possibly_ updated roadmap/to-do list is available in this repo project.

> Note that this project specifically aims to reproduce most of the features prioritizing CF grammars. So, for first versions of ported features, support for type 0 and 1 grammars could be missing.

> Moreover, you won't find parameters like "context_free" flags for switching behaviour depending on grammar type, because there's no such equivalent switch in implementation planned for this library at the moment. This library implementation ignores the grammar type concepts, at least at the moment, for those features which don't need a strict grammar type level (eg. grammar creation, grammar restrict_to function).

## Contributing

If you want to contribute or correct any errors, please do so opening a issues or creating pull requests.

## Ported features

More info available at the docs (*coming soon*).

> Following the official liblet [documentation](https://liblet.readthedocs.io/en/v1.1.0-alpha/api.html#liblet.grammar.Grammar.restrict_to).

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
