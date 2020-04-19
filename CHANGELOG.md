# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.0] - 2020-04-19

### Added

- added parser for parsing strings into symbols, productions and grammars and generally handling strings input
- added symbol as standalone struct for dealing with symbol management
- added production as standalone struct for dealing with productions management
- added grammar as standalone struct for dealing with grammar management
- added derivation as placeholder struct for dealing with grammar derivation in future versions
- implemented a first version of production predicate to filter productions base on some common filtering cases
- for *Symbol* added `new` function
- for *Symbol* added `as_str` function
- for *Symbol* added `to_string` function
- for *Symbol* added `is_terminal` function
- for *Symbol* added `is_non_terminal` function
- for *Symbol* added `is_valid_char` function
- for *Symbol* added `symbols_from_string` function
- added a `symbol` function to the *symbol* module
- added a `symbols` function to the *symbol* module
- added *SymbolError* as enum for symbol errors
- for *Production* added a `new` function
- for *Production* added a `new_from_string` function
- for *Production* added a `lhs` function
- for *Production* added a `rhs` function
- for *Production* added a `symbols` function
- for *Production* added a `from_string` function
- for *Production* added a `from_iter` function
- for *Production* added a `such_that` function
- added a `production` function to the *production* module
- added a `productions` function to the *production* module
- added a `productions_iter` function to the *production* module
- for *ProductionPredicate* added a `LhsEquals` variant
- for *ProductionPredicate* added a `RhsEquals` variant
- for *ProductionPredicate* added a `RhsLengthEquals` variant
- for *ProductionPredicate* added a `RhsIsSuffixOf` variant
- for *Grammar* added a `new` function
- for *Grammar* added a `new_from_string` function
- for *Grammar* added a `from_string` function
- for *Grammar* added a `alternatives` function
- for *Grammar* added a `restrict_to` function
- added a `grammar` function to the *grammar* module
- added a `grammar_iter` function to the *grammar* module

## [0.0.0] - 2020-04-09

Initial commit
