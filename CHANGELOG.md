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
- Added implementation of the `TryFrom` trait for `Transition`, from `&str`
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
- Added `Automaton` struct in the `automaton` module
- Added method `new` on `Automaton` struct for constructing automatons
- Added method `with_q0` on `Automaton` struct for constructing automatons with a specified initial state
- Added method `n` on `Automaton` struct for getting automaton states
- Added method `t` on `Automaton` struct for getting automaton transitions labels
- Added method `transitions` on `Automaton` struct for getting automaton transitions
- Added method `q0` on `Automaton` struct for getting automaton initial state
- Added method `f` on `Automaton` struct for getting automaton final states
- Added method `f` on `Automaton` struct for getting automaton final states
- Added method `next` on `Automaton` struct as transition function for the automaton
- Added method `from_string` on `Automaton` of symbols struct as constructor for automaton of symbols
- Added method `from_grammar` on `Automaton` of symbols struct as constructor for automaton of symbols
- Added implementation of the `TryFrom` trait for `Automaton`, from `&Grammar`
- Added `AutomatonError` enum for errors occurring during automatons manipulations
  - Added variant `NoStates`
  - Added variant `TransitionError`
  - Added variant `InvalidGrammar`
- Added module level function `transition` to `automaton` module to conveniently construct a transition
- Added module level function `transitions` to `automaton` module to conveniently construct transitions
- Added module level function `automaton` to `automaton` module to conveniently construct an automaton
- Added module level function `automaton_with_q0` to `automaton` module to conveniently construct an automaton with a specified initial state

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
