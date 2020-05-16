//! A module for working with automaton and transitions.
//!
//! This module can help abstracting over regular grammars, seeing them as automaton.
//! It collaborates strictly with the other modules of the library in order to be as easy
//! as possible to work with.
use crate::symbol::{sentential_form, Symbol, SymbolError};
use crate::tokenizer;
use crate::tokenizer::TokenizerError;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::error::Error;
use std::fmt;

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
#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord, Serialize, Deserialize, Hash)]
pub struct Transition<T>
where
    T: Eq + Clone + Ord,
{
    from: BTreeSet<T>,
    label: Symbol,
    to: BTreeSet<T>,
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
            self.label(),
            sentential_form(to).replace(" ", ",")
        )
    }
}

impl std::convert::TryFrom<&str> for Transition<Symbol> {
    type Error = TransitionError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let t = Transition::from_string(value)?;
        let mut t_iter = t.iter();
        if let Some(t) = t_iter.next() {
            if t_iter.next().is_none() {
                Ok(t.clone())
            } else {
                Err(TransitionError::FormatError(
                    TokenizerError::TransitionMultiple(value.to_string()),
                ))
            }
        } else {
            Err(TransitionError::FormatError(
                TokenizerError::TransitionEmpty(value.to_string()),
            ))
        }
    }
}

impl<T> Transition<T>
where
    T: Eq + Clone + Ord,
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
    /// let t = Transition::new(vec![symbol("A")], symbol("label"), vec![symbol("B")]);
    /// ```
    pub fn new<I>(from: I, label: Symbol, to: I) -> Transition<T>
    where
        I: IntoIterator<Item = T>,
    {
        Transition {
            from: from.into_iter().collect(),
            label: label,
            to: to.into_iter().collect(),
        }
    }

    /// Return the set of symbols which defines the from state of this transition.
    ///
    /// # Examples
    /// ```rust
    /// use liblet::automaton::Transition;
    /// use liblet::symbol::symbol;
    /// use std::collections::BTreeSet;
    /// use std::iter::FromIterator;
    ///
    /// let t = Transition::new(vec![symbol("A")], symbol("label"), vec![symbol("B")]);
    ///
    /// assert_eq!(t.from(), BTreeSet::from_iter(vec![symbol("A")]));
    /// ```
    pub fn from(&self) -> BTreeSet<T> {
        self.from.clone().into_iter().collect()
    }

    /// Return the set of symbols which defines the to state of this transition.
    ///
    /// # Examples
    /// ```rust
    /// use liblet::automaton::Transition;
    /// use liblet::symbol::symbol;
    /// use std::collections::BTreeSet;
    /// use std::iter::FromIterator;
    ///
    /// let t = Transition::new(vec![symbol("A")], symbol("label"), vec![symbol("B")]);
    ///
    /// assert_eq!(t.to(), BTreeSet::from_iter(vec![symbol("B")]));
    /// ```
    pub fn to(&self) -> BTreeSet<T> {
        self.to.clone()
    }

    /// Return the label of this transition, if present.
    ///
    /// # Examples
    /// ```rust
    /// use liblet::automaton::Transition;
    /// use liblet::symbol::symbol;
    ///
    /// let t = Transition::new(vec![symbol("A")], symbol("label"), vec![symbol("B")]);
    ///
    /// assert_eq!(t.label(), symbol("label"));
    /// ```
    pub fn label(&self) -> Symbol {
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

                let label = Symbol::new(label)?;

                acc.push(Transition::new(from, label, to));
                Ok(acc)
            })
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum AutomatonError {
    /// Error for describing the attempt to create an automaton without any states.
    NoStates,
    /// A [TransitionError](enum.TransitionError.html) occurring during manipulation of automatons
    TransitionError(TransitionError),
}

impl std::convert::From<TransitionError> for AutomatonError {
    fn from(e: TransitionError) -> Self {
        AutomatonError::TransitionError(e)
    }
}

impl fmt::Display for AutomatonError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AutomatonError::NoStates => write!(
                f,
                "AutomatonError: impossible to create an automaton with no states",
            ),
            AutomatonError::TransitionError(e) => {
                write!(f, "AutomatonError: transition error encountered = {}", e)
            }
        }
    }
}

impl Error for AutomatonError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            AutomatonError::TransitionError(e) => Some(e),
            AutomatonError::NoStates => None,
        }
    }
}

/// The main type of this module.
///
/// This type represents a nondeterministic finite automaton defined as:
/// A = (N,T,transitions,q0,F) where N is the set of states, T is the set of transitions labels,
/// q0 is the starting state and F is the set of final states.
///
/// The transitions are the ones defined in this same module: [Transition](struct.Transition.html)s.
#[derive(Clone, Debug, Serialize, Deserialize, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Automaton<T>
where
    T: Eq + Clone + Ord,
{
    transitions: BTreeSet<Transition<T>>,
    q0: BTreeSet<T>,
    f: BTreeSet<BTreeSet<T>>,
}

// impl<T> fmt::Display for Automaton<T>
// where
//     T: Eq + Clone + Ord,
// {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         write!(
//             f,
//             "n: {}\nt: {}\ntransitions: {}\nq0: {}\nf: {}",
//             self.n(),
//             self.t(),
//             self.transitions,
//             self.q0,
//             self.f
//         )
//     }
// }

impl<T> Automaton<T>
where
    T: Eq + Clone + Ord,
{
    /// Creates a new automaton based on the transitions
    /// and final states given.
    ///
    /// The starting state will be the "from" part of the first transition
    /// given.
    ///
    /// # Errors
    /// Can return a [AutomatonError::NoStates](enum.AutomatonError.html#variant.NoStates)
    /// error if no transitions are given.
    ///
    /// # Examples
    /// Automaton of generic type
    /// ```rust
    /// use liblet::automaton::{Automaton,Transition};
    /// use liblet::symbol::symbol;
    /// use std::collections::BTreeSet;
    ///
    /// let t = Transition::new(vec!["0"], symbol("label"), vec!["1"]);
    /// let mut f: BTreeSet<BTreeSet<&str>> = BTreeSet::new();
    /// f.insert(vec!["1"].into_iter().collect());
    ///
    /// // automaton with starting state {"0"}
    /// // and final state {"1"}
    /// // and transiton "label" from {"0"} to {"1"}
    /// let a = Automaton::new(vec![t], f);
    /// ```
    ///
    /// Automaton of symbols
    /// ```rust
    /// use liblet::automaton::{Automaton,transitions};
    /// use liblet::symbol::{Symbol,symbol};
    /// use std::collections::BTreeSet;
    ///
    /// let t = transitions("A -> label -> B");
    /// let mut f: BTreeSet<BTreeSet<Symbol>> = BTreeSet::new();
    /// f.insert(vec![symbol("B")].into_iter().collect());
    ///
    /// // automaton with starting state {"A"}
    /// // and final state {"B"}
    /// // and transiton "label" from {"A"} to {"B"}
    /// let a = Automaton::new(t, f);
    /// ```
    pub fn new<I, Q, F>(transitions: I, f: F) -> Result<Automaton<T>, AutomatonError>
    where
        I: IntoIterator<Item = Transition<T>>,
        Q: IntoIterator<Item = T>,
        F: IntoIterator<Item = Q>,
    {
        let transitions: Vec<Transition<T>> = transitions.into_iter().collect();
        let q0 = match transitions.first() {
            Some(t) => t.from(),
            None => return Err(AutomatonError::NoStates),
        };

        Automaton::with_q0(
            transitions,
            f.into_iter()
                .map(|f| f.into_iter().collect())
                .collect::<BTreeSet<BTreeSet<T>>>(),
            q0,
        )
    }

    /// Creates a new automaton based on the transitions, starting state
    /// and final states given.
    ///
    /// # Errors
    /// Can return a [AutomatonError::NoStates](enum.AutomatonError.html#variant.NoStates)
    /// error if no transitions are given.
    ///
    /// # Examples
    /// Automaton of generic type
    /// ```rust
    /// use liblet::automaton::{Automaton,Transition};
    /// use liblet::symbol::symbol;
    /// use std::collections::BTreeSet;
    ///
    /// let t = Transition::new(vec!["0"], symbol("label"), vec!["1"]);
    /// let q0: BTreeSet<&str> = vec!["0"].into_iter().collect();
    /// let mut f: BTreeSet<BTreeSet<&str>> = BTreeSet::new();
    /// f.insert(vec!["1"].into_iter().collect());
    ///
    /// // automaton with starting state {"0"}
    /// // and final state {"1"}
    /// // and transiton "label" from {"0"} to {"1"}
    /// let a = Automaton::with_q0(vec![t], f, q0);
    /// ```
    ///
    /// Automaton of symbols
    /// ```rust
    /// use liblet::automaton::{Automaton,transitions};
    /// use liblet::symbol::{Symbol,symbol};
    /// use std::collections::BTreeSet;
    ///
    /// let t = transitions("A -> label -> B");
    /// let q0: BTreeSet<Symbol> = vec![symbol("A")].into_iter().collect();
    /// let mut f: BTreeSet<BTreeSet<Symbol>> = BTreeSet::new();
    /// f.insert(vec![symbol("B")].into_iter().collect());
    ///
    /// // automaton with starting state {"A"}
    /// // and final state {"B"}
    /// // and transiton "label" from {"A"} to {"B"}
    /// let a = Automaton::with_q0(t, f, q0);
    /// ```
    pub fn with_q0<I, Q, F>(transitions: I, f: F, q0: Q) -> Result<Automaton<T>, AutomatonError>
    where
        I: IntoIterator<Item = Transition<T>>,
        Q: IntoIterator<Item = T>,
        F: IntoIterator<Item = Q>,
    {
        let transitions: Vec<Transition<T>> = transitions.into_iter().collect();
        if transitions.is_empty() {
            Err(AutomatonError::NoStates)
        } else {
            Ok(Automaton {
                transitions: transitions.into_iter().collect(),
                q0: q0.into_iter().collect(),
                f: f.into_iter().map(|f| f.into_iter().collect()).collect(),
            })
        }
    }

    /// Return the states of the automaton.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::automaton::{Automaton,Transition};
    /// use liblet::symbol::symbol;
    /// use std::collections::BTreeSet;
    ///
    /// let t = Transition::new(vec!["0"], symbol("label"), vec!["1"]);
    /// let mut f: BTreeSet<BTreeSet<&str>> = BTreeSet::new();
    /// f.insert(vec!["1"].into_iter().collect());
    ///
    /// let a = Automaton::new(vec![t], f)?;
    ///
    /// // states will be {{"0"}, {"1"}}
    /// let states: BTreeSet<BTreeSet<&str>> =
    ///     vec![vec!["0"],vec!["1"]].into_iter()
    ///         .map(|s| s.into_iter().collect())
    ///         .collect();
    ///
    /// assert_eq!(a.n(), states);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn n(&self) -> BTreeSet<BTreeSet<T>> {
        self.transitions
            .clone()
            .into_iter()
            .fold(BTreeSet::new(), |mut acc, t| {
                acc.insert(t.from());
                acc.insert(t.to());
                acc
            })
    }

    /// Return the starting state of the automaton.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::automaton::{Automaton,Transition};
    /// use liblet::symbol::symbol;
    /// use std::collections::BTreeSet;
    ///
    /// let t = Transition::new(vec!["0"], symbol("label"), vec!["1"]);
    /// let mut f: BTreeSet<BTreeSet<&str>> = BTreeSet::new();
    /// f.insert(vec!["1"].into_iter().collect());
    ///
    /// let a = Automaton::new(vec![t], f)?;
    ///
    /// // starting state will be {"0"}
    /// let q0: BTreeSet<&str> =
    ///     vec!["0"].into_iter().collect();
    ///
    /// assert_eq!(a.q0(), q0);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn q0(&self) -> BTreeSet<T> {
        self.q0.clone()
    }

    /// Return the labels set of the automaton.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::automaton::{Automaton,Transition,transitions};
    /// use liblet::symbol::{symbol,Symbol};
    /// use std::collections::BTreeSet;
    ///
    /// let t = transitions("
    ///     A1 -> label1 -> B1
    ///     A2 -> label2 -> B2
    /// ");
    ///
    /// let a = Automaton::new::<
    ///        Vec<Transition<Symbol>>,
    ///        BTreeSet<Symbol>,
    ///        BTreeSet<BTreeSet<Symbol>>,
    ///    >(t, BTreeSet::new())?;
    ///
    /// // labels set will be {"label1","label2"}
    /// let labels: BTreeSet<Symbol> =
    ///     vec![
    ///         symbol("label1"),
    ///         symbol("label2")
    ///     ].into_iter().collect();
    ///
    /// assert_eq!(a.t(), labels);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn t(&self) -> BTreeSet<Symbol> {
        self.transitions.iter().fold(BTreeSet::new(), |mut acc, t| {
            acc.insert(t.label().clone());
            acc
        })
    }

    /// Return the final states set of the automaton.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::automaton::{Automaton,transitions};
    /// use liblet::symbol::{symbol,Symbol};
    /// use std::collections::BTreeSet;
    ///
    /// let t = transitions("
    ///     A1 -> label1 -> B1
    ///     A2 -> label2 -> B2
    /// ");
    /// let mut f: BTreeSet<BTreeSet<Symbol>> = BTreeSet::new();
    /// f.insert(vec![symbol("B1")].into_iter().collect());
    ///
    /// let a = Automaton::new(t, f)?;
    ///
    /// // labels set will be {"label1","label2"}
    /// let states: BTreeSet<BTreeSet<Symbol>> =
    ///     vec![vec![symbol("B1")]].into_iter()
    ///         .map(|s| s.into_iter().collect())
    ///         .collect();
    ///
    /// assert_eq!(a.f(), states);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn f(&self) -> BTreeSet<BTreeSet<T>> {
        self.f.clone()
    }
}

impl Automaton<Symbol> {
    /// Create a new automaton based on the transitions specified as string,
    /// other than an optional starting state and the final states.
    ///
    /// The starting state is inferred from the "from" part of the first parsed
    /// transition, if None is specified at input (if there's at least one transition).
    ///
    /// # Errors
    /// Can return a [AutomatonError](enum.AutomatonError.html) if an error occurs
    /// while parsing transitions from string or during automaton creation.
    ///
    /// # Example
    /// ```rust
    /// use liblet::automaton::Automaton;
    /// use liblet::symbol::symbol;
    ///
    /// // create an automaton with two transitions,
    /// // 3 states and the starting state {"A"},
    /// // but no final state
    /// let a = Automaton::from_string(
    ///     "A -> label -> B",
    ///     vec![],
    ///     Some(vec![symbol("A")])
    /// );
    /// ```
    pub fn from_string<Q, F>(
        transitions: &str,
        f: F,
        q0: Option<Q>,
    ) -> Result<Automaton<Symbol>, AutomatonError>
    where
        Q: IntoIterator<Item = Symbol>,
        F: IntoIterator<Item = Q>,
    {
        let t = Transition::from_string(transitions)?;

        match q0 {
            Some(q0) => Automaton::with_q0(t, f, q0),
            None => Automaton::new(t, f),
        }
    }
}

/// Convenience method for creating a transition of symbols from a string.
///
/// It returns the transition directly, as opposed to the `Result` returned from
/// the transition [from_string](struct.Transition.html#method.from_string) method.
///
/// # Panics
/// Panics if converting the string to transition is not possible as specified in the
/// transition [from_string](struct.Transition.html#method.from_string) method.
///
/// # Examples
/// ```rust
/// use liblet::automaton::transition;
///
/// let t = transition("A -> label -> B");
/// ```
pub fn transition(string: &str) -> Transition<Symbol> {
    use std::convert::TryFrom;
    Transition::<Symbol>::try_from(string).unwrap()
}

/// Convenience method for creating a collections of transitions from a string.
///
/// It returns the transition directly, as opposed to the `Result` returned from
/// the transition [from_string](struct.Transition.html#method.from_string) method.
///
/// # Panics
/// Panics if converting the string to transitions is not possible as specified in the
/// transition [from_string](struct.Transition.html#method.from_string) method.
///
/// # Examples
/// ```rust
/// use liblet::automaton::transitions;
///
/// let t = transitions("A1 -> label1 -> B1\nA2 -> label2 -> B2");
/// assert_eq!(t.len(), 2);
/// ```
pub fn transitions(string: &str) -> Vec<Transition<Symbol>> {
    Transition::from_string(string).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::symbol;
    use std::convert::TryFrom;
    use std::fmt::Write;
    use std::iter::FromIterator;

    // struct.Transition

    #[test]
    fn transition_new() {
        let from_check = vec![symbol("A")];
        let label = symbol("label");
        let to_check = vec![symbol("B")];
        let t = Transition::new(from_check.clone(), label.clone(), to_check.clone());

        assert_eq!(
            t.from,
            BTreeSet::from_iter(from_check),
            "New transition creation, from don't match"
        );
        assert_eq!(
            t.label, label,
            "New transition creation, label is no the one expected"
        );
        assert_eq!(
            t.to,
            BTreeSet::from_iter(to_check),
            "New transition creation, to set don't match"
        );
    }

    #[test]
    fn transition_display_symbol() {
        let mut buf = String::new();
        let t = Transition::new(
            vec![symbol("A1"), symbol("A2")],
            symbol("label"),
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
            "Transition from string are not long as expected"
        );
        assert_eq!(
            t[0].from(),
            vec![symbol("A")].into_iter().collect::<BTreeSet<Symbol>>(),
            "Transition from is not what expected"
        );
        assert_eq!(
            t[0].label(),
            symbol("label"),
            "Transition label is not what expected"
        );
        assert_eq!(
            t[0].to(),
            vec![symbol("B")].into_iter().collect::<BTreeSet<Symbol>>(),
            "Transition to is not what expected"
        );
    }

    #[test]
    fn transition_from_string_no_label() {
        let result = Transition::from_string("A -> -> B");

        assert!(
            result.is_err(),
            "Transition from string should return an Err"
        );
        let e = result.unwrap_err();

        assert_eq!(
            e,
            TransitionError::SymbolError(SymbolError::EmptySymbol),
            "Transitions from string returned error is not the one expected"
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

    #[test]
    fn transition_try_from() {
        let t = Transition::<Symbol>::try_from("A -> label -> B");
        assert!(t.is_ok(), "Transition try from should not return an error");
    }

    #[test]
    fn transition_try_from_multiple() {
        let string = "A -> label -> B\nA -> label -> B";
        let t = Transition::<Symbol>::try_from(string);
        assert!(t.is_err(), "Transition try from should return an error");
        let e = t.unwrap_err();
        assert_eq!(
            e,
            TransitionError::FormatError(TokenizerError::TransitionMultiple(string.to_string()),),
            "Transition try from returned error is not the one expected"
        )
    }

    #[test]
    fn transition_try_from_empty() {
        let string = "\t";
        let t = Transition::<Symbol>::try_from(string);
        assert!(t.is_err(), "Transition try from should return an error");
        let e = t.unwrap_err();
        assert_eq!(
            e,
            TransitionError::FormatError(TokenizerError::TransitionEmpty(string.to_string()),),
            "Transition try from returned error is not the one expected"
        )
    }

    #[test]
    fn transition_try_from_error() {
        let t = Transition::<Symbol>::try_from("A -> label");
        assert!(t.is_err(), "Transition try from should return an error");
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

    #[test]
    fn transition_error_source() {
        assert!(
            TransitionError::FormatError(TokenizerError::TransitionNoLabel(String::new()))
                .source()
                .is_some(),
            "Transition Error format error source should be some"
        );
        assert!(
            TransitionError::SymbolError(SymbolError::EmptySymbol)
                .source()
                .is_some(),
            "Transition Error symbol error source should be some"
        );
    }

    /// struct.Automaton   

    #[test]
    fn automaton_new() {
        let t = Transition::new(vec!["0"], symbol("label"), vec!["1"]);
        let mut f: BTreeSet<BTreeSet<&str>> = BTreeSet::new();
        f.insert(vec!["1"].into_iter().collect());

        let result = Automaton::new(vec![t], f);
        assert!(
            result.is_ok(),
            "Automaton creation should not return an error"
        );

        let expected_n: BTreeSet<BTreeSet<&str>> = vec![vec!["0"], vec!["1"]]
            .into_iter()
            .map(|s| s.into_iter().collect())
            .collect();

        assert_eq!(
            result.unwrap().n(),
            expected_n,
            "New automaton states are not those expected"
        );
    }

    #[test]
    fn automaton_with_q0() {
        let t = Transition::new(vec!["0"], symbol("label"), vec!["1"]);
        let q0: BTreeSet<&str> = vec!["A"].into_iter().collect();
        let mut f: BTreeSet<BTreeSet<&str>> = BTreeSet::new();
        f.insert(vec!["1"].into_iter().collect());

        let result = Automaton::with_q0(vec![t], f, q0.clone());
        assert!(
            result.is_ok(),
            "Automaton creation should not return an error"
        );
        let a = result.unwrap();

        assert_eq!(
            a.q0(),
            q0,
            "New automaton q0 starting state is not the one expected"
        );

        let expected_n: BTreeSet<BTreeSet<&str>> = vec![vec!["0"], vec!["1"]]
            .into_iter()
            .map(|s| s.into_iter().collect())
            .collect();

        assert_eq!(
            a.n(),
            expected_n,
            "New automaton states are not those expected"
        );
    }

    #[test]
    fn automaton_n() {
        let t = Transition::new(vec!["0"], symbol("label"), vec!["1"]);
        let mut f: BTreeSet<BTreeSet<&str>> = BTreeSet::new();
        f.insert(vec!["1"].into_iter().collect());

        let result = Automaton::new(vec![t], f);
        assert!(
            result.is_ok(),
            "Automaton creation should not return an error"
        );

        let expected_n: BTreeSet<BTreeSet<&str>> = vec![vec!["0"], vec!["1"]]
            .into_iter()
            .map(|s| s.into_iter().collect())
            .collect();

        assert_eq!(
            result.unwrap().n(),
            expected_n,
            "New automaton states are not those expected"
        );
    }

    #[test]
    fn automaton_q0() {
        let t = Transition::new(vec!["0"], symbol("label"), vec!["1"]);
        let mut f: BTreeSet<BTreeSet<&str>> = BTreeSet::new();
        f.insert(vec!["1"].into_iter().collect());

        let result = Automaton::new(vec![t], f);
        assert!(
            result.is_ok(),
            "Automaton creation should not return an error"
        );

        let expected_q0: BTreeSet<&str> = vec!["0"].into_iter().collect();

        assert_eq!(
            result.unwrap().q0(),
            expected_q0,
            "New automaton starting state is not the one expected"
        );
    }

    #[test]
    fn automaton_t() {
        let t = super::transitions(
            "
         A1 -> label1 -> B1
         A2 -> label2 -> B2
        ",
        );

        let result = Automaton::new::<
            Vec<Transition<Symbol>>,
            BTreeSet<Symbol>,
            BTreeSet<BTreeSet<Symbol>>,
        >(t, BTreeSet::new());
        assert!(
            result.is_ok(),
            "Automaton creation should not return an error"
        );

        let labels: BTreeSet<Symbol> = vec![symbol("label1"), symbol("label2")]
            .into_iter()
            .collect();

        assert_eq!(
            result.unwrap().t(),
            labels,
            "Automaton labels set is not the one expected"
        );
    }

    /// enum.AutomatonError

    #[test]
    fn automaton_error_display_no_states() {
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

    #[test]
    fn automaton_error_display_transition_error() {
        let mut buf = String::new();
        let string = "A";
        let error =
            TransitionError::FormatError(TokenizerError::TransitionNoLabel(string.to_string()));

        let result = write!(buf, "{}", AutomatonError::TransitionError(error.clone()));
        assert!(result.is_ok());
        assert_eq!(
            buf,
            format!("AutomatonError: transition error encountered = {}", error)
        )
    }

    #[test]
    fn automaton_error_source() {
        assert!(
            AutomatonError::NoStates.source().is_none(),
            "Automaton Error format error source should be none"
        );
        assert!(
            AutomatonError::TransitionError(TransitionError::FormatError(
                TokenizerError::ProductionEmpty(String::new())
            ))
            .source()
            .is_some(),
            "Transition Error symbol error source should be some"
        );
    }

    /// mod.automaton

    #[test]
    fn transition() {
        super::transition("A -> label -> B");
    }

    #[test]
    #[should_panic]
    fn transition_error() {
        super::transition("A -> label");
    }

    #[test]
    fn transitions() {
        let t = super::transitions("A1 -> label1 -> B1\nA2 -> label2 -> B2");
        assert_eq!(t.len(), 2);
    }

    #[test]
    #[should_panic]
    fn transitions_error() {
        super::transitions("A -> label");
    }
}
