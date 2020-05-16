# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unrealeased]

## Added

- Added `Transition` struct for automaton transitions in the `automaton` module
- Added method `new` on `Transition` struct for creating new transitions
- Added method `from` on `Transition` struct for accessing the from state of the transition
- Added method `label` on `Transition` struct for accessing the label of the transition
- Added method `to` on `Transition` struct for accessing the to state of the transition
- Added static method `from_string` on `Transition` struct for creating transitions from strings
- Added implementation of the `From` trait for `Transition`
- Added constructor functions `transition` and `transitions` in the `automaton` module
- Added `TransitionError` enum for errors occurring during transitions manipulations
  - Added variant `SymbolError`
  - Added variant `FormatError`
- Added function `transitions_from_string` for the `tokenizer` module to tokenize transitions from strings
- Added enum variants for `TokenizerError` in order to cover the new tokenizing of transitions from strings
  - Added variant `TransitionNoTo`
  - Added variant `TransitionNoLabel`
  - Added variant `TransitionMultipleOneLine`
  - Added variant `TransitionEmpty`

## [0.1.2] - 2020-05-16

### Fixed

- Replaced error variant returned for production `try_from` method in order to be more precise about the occurred error when no productions are parsed from the input string

## [0.1.1] - 2020-05-12

### Fixed

- Removed `itertools` dependency

## [0.1.0] - 2020-05-07

Initial public release

## [0.0.0] - 2020-04-09

Initial commit
