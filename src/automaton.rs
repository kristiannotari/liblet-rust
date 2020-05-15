//! A module for working with automaton and transitions.
//!
//! This module can help abstracting over regular grammars, seeing them as automaton.
//! It collaborates strictly with the other modules of the library in order to be as easy
//! as possible to work with.
use crate::symbol::{sentential_form, Symbol, SymbolError};
use crate::tokenizer;
use crate::tokenizer::TokenizerError;
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::error::Error;
use std::fmt;

/// Errors resulting from tokenizing strings.
///
/// When parsing custom strings, invalid or bad formatted strings can generate
/// tokenizer errors, according to which representation is expected.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum TransitionError {
    /// Error for failing to create transitions from something which is not a symbol
    SymbolError(SymbolError),
    /// Error trying to tokenize/parse transitions from strings
    FormatError(TokenizerError),
}

impl fmt::Display for TransitionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TransitionError::SymbolError(e) => {
                write!(f, "TransitionError: symbol error encountered = {}", e)
            }
            TransitionError::FormatError(e) => {
                write!(f, "TransitionError: format error encountered = {}", e)
            }
        }
    }
}

impl Error for TransitionError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            TransitionError::SymbolError(e) => Some(e),
            TransitionError::FormatError(e) => Some(e),
        }
    }
}

impl std::convert::From<TokenizerError> for TransitionError {
    fn from(e: TokenizerError) -> Self {
        TransitionError::FormatError(e)
    }
}

impl std::convert::From<SymbolError> for TransitionError {
    fn from(e: SymbolError) -> Self {
        TransitionError::SymbolError(e)
    }
}

/// A transition data structure to help abstracting automaton transitions
///
/// It is used in the automatons to define a transition between two states:
/// - from
/// - to
///
/// Transitions can be labeled.
///
/// States are defined as collections of [Symbol](../symbol/struct.Symbol.html)s.
/// To define a transition between two symbols, simply use singleton collections.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct Transition<T>
where
    T: Eq + std::hash::Hash + Clone,
{
    from: HashSet<T>,
    label: Option<String>,
    to: HashSet<T>,
}

impl fmt::Display for Transition<Symbol> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut from = self.from().into_iter().collect::<Vec<Symbol>>();
        let mut to = self.to().into_iter().collect::<Vec<Symbol>>();
        from.sort();
        to.sort();
        write!(
            f,
            "{{{}}} --\"{}\"--> {{{}}}",
            sentential_form(from).replace(" ", ","),
            self.label().unwrap_or(String::new()),
            sentential_form(to).replace(" ", ",")
        )
    }
}

impl<T> Transition<T>
where
    T: Eq + std::hash::Hash + Clone,
{
    /// Constructor for a new transition.
    ///
    /// It takes the 3 fundamental details of a transition:
    /// - the *from* collection
    /// - the label of the transition
    /// - the *to* collection
    ///
    /// # Examples
    /// ```rust
    /// use liblet::automaton::Transition;
    /// use liblet::symbol::symbol;
    ///
    /// // here we define a transition of the form {A} --> "label" --> {B}
    /// let t = Transition::new(vec![symbol("A")], Some("label"), vec![symbol("B")]);
    /// ```
    pub fn new<I>(from: I, label: Option<&str>, to: I) -> Transition<T>
    where
        I: IntoIterator<Item = T>,
    {
        Transition {
            from: from.into_iter().collect(),
            label: label.map(|s| s.to_string()),
            to: to.into_iter().collect(),
        }
    }

    /// Return the set of symbols which defines the from state of this transition.
    ///
    /// # Examples
    /// ```rust
    /// use liblet::automaton::Transition;
    /// use liblet::symbol::symbol;
    /// use std::collections::HashSet;
    /// use std::iter::FromIterator;
    ///
    /// let t = Transition::new(vec![symbol("A")], Some("label"), vec![symbol("B")]);
    ///
    /// assert_eq!(t.from(), HashSet::from_iter(vec![symbol("A")]));
    ///
    /// ```
    pub fn from(&self) -> HashSet<T> {
        self.from.clone()
    }

    /// Return the set of symbols which defines the to state of this transition.
    ///
    /// # Examples
    /// ```rust
    /// use liblet::automaton::Transition;
    /// use liblet::symbol::symbol;
    /// use std::collections::HashSet;
    /// use std::iter::FromIterator;
    ///
    /// let t = Transition::new(vec![symbol("A")], Some("label"), vec![symbol("B")]);
    ///
    /// assert_eq!(t.to(), HashSet::from_iter(vec![symbol("B")]));
    ///
    /// ```
    pub fn to(&self) -> HashSet<T> {
        self.to.clone()
    }

    /// Return the label of this transition, if present.
    ///
    /// # Examples
    /// ```rust
    /// use liblet::automaton::Transition;
    /// use liblet::symbol::symbol;
    ///
    /// let t = Transition::new(vec![symbol("A")], Some("label"), vec![symbol("B")]);
    ///
    /// assert!(t.label().is_some());
    /// assert_eq!(t.label().unwrap(), "label".to_string());
    /// ```
    pub fn label(&self) -> Option<String> {
        self.label.clone()
    }
}

impl Transition<Symbol> {
    /// Construct a new transition from a string.
    ///
    /// # Errors
    /// Can return a [TokenizerError]()
    ///
    /// # Examples
    /// ```rust
    /// use liblet::automaton::Transition;
    /// use liblet::symbol::symbol;
    ///
    /// // here we define a transition of the form {A1,A2} --> "label" --> {B1,B2}
    /// let t = Transition::from_string("A1 A2 -> label -> B1 B2");
    ///
    /// assert!(t.is_ok());
    /// ```
    pub fn from_string(string: &str) -> Result<Vec<Transition<Symbol>>, TransitionError> {
        let tokens = tokenizer::transitions_from_string(string)?;

        tokens
            .iter()
            .try_fold(Vec::new(), |mut acc, (from, label, to)| {
                let from = from.into_iter().try_fold(
                    Vec::new(),
                    |mut acc: Vec<Symbol>, s: &String| -> Result<Vec<Symbol>, TransitionError> {
                        let s = Symbol::new(s)?;
                        acc.push(s);
                        Ok(acc)
                    },
                )?;
                let to = to.iter().try_fold(
                    Vec::new(),
                    |mut acc: Vec<Symbol>, s: &String| -> Result<Vec<Symbol>, TransitionError> {
                        let s = Symbol::new(s)?;
                        acc.push(s);
                        Ok(acc)
                    },
                )?;
                let t: Transition<Symbol>;
                if label.is_empty() {
                    t = Transition::new(from, None, to);
                } else {
                    t = Transition::new(from, Some(label), to);
                }

                acc.push(t);
                Ok(acc)
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::symbol;
    use std::fmt::Write;
    use std::iter::FromIterator;

    // struct.Transition

    #[test]
    fn transition_new() {
        let from_check = vec![symbol("A")];
        let label = "label";
        let label_check = Some(label);
        let to_check = vec![symbol("B")];
        let t = Transition::new(from_check.clone(), label_check, to_check.clone());

        assert_eq!(
            t.from,
            HashSet::from_iter(from_check),
            "New transition creation, from don't match"
        );
        assert!(
            t.label.is_some(),
            "New transition creation, label not found"
        );
        assert_eq!(
            t.label.unwrap(),
            label.to_string(),
            "New transition creation, label not found"
        );
        assert_eq!(
            t.to,
            HashSet::from_iter(to_check),
            "New transition creation, to set don't match"
        );
    }

    #[test]
    fn transition_display_symbol() {
        let mut buf = String::new();
        let t = Transition::new(
            vec![symbol("A1"), symbol("A2")],
            Some("label"),
            vec![symbol("B1"), symbol("B2")],
        );

        let result = write!(buf, "{}", t);
        assert!(result.is_ok());
        assert_eq!(buf, "{A1,A2} --\"label\"--> {B1,B2}")
    }

    #[test]
    fn transition_from_string() {
        let result = Transition::from_string("A -> label -> B");

        assert!(
            result.is_ok(),
            "Transition from string should not return an Err"
        );
        let t = result.unwrap();

        assert_eq!(
            t.len(),
            1,
            "Transitions from string are not long as expected"
        );
        assert_eq!(
            t[0].from(),
            vec![symbol("A")].into_iter().collect::<HashSet<Symbol>>()
        );
        assert_eq!(t[0].label(), Some("label".to_string()));
        assert_eq!(
            t[0].to(),
            vec![symbol("B")].into_iter().collect::<HashSet<Symbol>>()
        );
    }

    #[test]
    fn transition_from_string_none_label() {
        let result = Transition::from_string("A -> -> B");

        assert!(
            result.is_ok(),
            "Transition from string should not return an Err"
        );
        let t = result.unwrap();

        assert_eq!(
            t.len(),
            1,
            "Transitions from string are not long as expected"
        );
        assert_eq!(
            t[0].from(),
            vec![symbol("A")].into_iter().collect::<HashSet<Symbol>>()
        );
        assert_eq!(t[0].label(), None);
        assert_eq!(
            t[0].to(),
            vec![symbol("B")].into_iter().collect::<HashSet<Symbol>>()
        );
    }

    #[test]
    fn transition_from_string_tokenizer_error() {
        let result = Transition::from_string("A -> label");

        assert!(
            result.is_err(),
            "Transition from string should return an Err"
        );
        let e = result.unwrap_err();

        assert_eq!(
            e,
            TransitionError::FormatError(TokenizerError::TransitionNoTo("A -> label".to_string()))
        );
    }

    #[test]
    fn transition_from_string_symbol_error_from() {
        let result = Transition::from_string("λ -> label -> B");

        assert!(
            result.is_err(),
            "Transition from string should return an Err"
        );
        let e = result.unwrap_err();

        assert_eq!(
            e,
            TransitionError::SymbolError(SymbolError::InvalidSymbol("λ".to_string()))
        );
    }

    #[test]
    fn transition_from_string_symbol_error_to() {
        let result = Transition::from_string("A -> label -> λ");

        assert!(
            result.is_err(),
            "Transition from string should return an Err"
        );
        let e = result.unwrap_err();

        assert_eq!(
            e,
            TransitionError::SymbolError(SymbolError::InvalidSymbol("λ".to_string()))
        );
    }

    /// enum.TransitionError

    #[test]
    fn transition_error_display_symbol_error() {
        let mut buf = String::new();
        let string = "\n";
        let error = SymbolError::InvalidSymbol(string.to_string());

        let result = write!(buf, "{}", TransitionError::SymbolError(error.clone()));
        assert!(result.is_ok());
        assert_eq!(
            buf,
            format!("TransitionError: symbol error encountered = {}", error)
        )
    }

    #[test]
    fn transition_error_display_format_error() {
        let mut buf = String::new();
        let string = "A";
        let error = TokenizerError::TransitionNoLabel(string.to_string());

        let result = write!(buf, "{}", TransitionError::FormatError(error.clone()));
        assert!(result.is_ok());
        assert_eq!(
            buf,
            format!("TransitionError: format error encountered = {}", error)
        )
    }
}
