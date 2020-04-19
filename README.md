# liblet-rust

Porting project for the [liblet library](https://github.com/let-unimi/liblet) of the University of Milan course "Linguaggi e Traduttori" (Languages and Translators) in Rust.

This is a learning project, used to better comprehend both the course topics and the rust programming language.

A generic and _possibly_ updated roadmap/to-do list is available in this repo project.

> Note that this project specifically aims to reproduce most of the features prioritizing CF grammars. So, for first versions of ported features, support for type 0 and 1 grammars could be missing.

> Moreover, you won't find parameters like "context_free" flags for switching behaviour depending on grammar type, because there's no such equivalent switch in implementation planned for this library at the moment. This library implementation ignores the grammar type concepts, at least at the moment, for those features which don't need a strict grammar type level (eg. grammar creation, grammar restrict_to function).

## Contributing

If you want to contribute or correct any errors, please do so opening a issues or creating pull requests.

## Ported features

`v0.1.0`

Following the official liblet [documentation](https://liblet.readthedocs.io/en/v1.1.0-alpha/api.html#liblet.grammar.Grammar.restrict_to).

More info available at the docs (*coming soon*).

All implementations use a custom type called *Symbol* for representing symbols in a structured way. It also comes with some handy functions to help working on grammar symbols.

### Production

- basic Production implementation, with left and right hand sides
- `from_string` function on a production
- `such_that` function on a production for production filters (uses ProductionPredicate)

### Grammar

- basic Grammar implementation, with non terminal and terminal symbols, production rules of the type *Production* and the start symbol
- `alternatives` function on a grammar
- `restrict_to` function on a grammar
