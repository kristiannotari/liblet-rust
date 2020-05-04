//! Module for handling all grammar related operations.
//!
//! Its goal is to emulate a formal grammar.
//!
//! It defines a `Grammar` type which can be used to conveniently work with grammar and derivation manipulations
//! and provide abstraction over grammar quadruple of terminal and non terminal symbols, start symbol and productions.
//!
//! It can be easily constructed from `&str`s or collections of [Symbol](../symbol/struct.Symbol.html)s and [Production](../production/struct.Production.html)s.

use crate::production::{Production, ProductionError};
use crate::symbol::{Symbol, SymbolError};
use itertools::Itertools;
use std::collections::HashSet;
use std::error::Error;
use std::fmt;

#[derive(Debug, PartialEq)]
pub enum GrammarError {
    /// Error returned if any of the given non terminals is an invalid non terminal symbol.
    WrongNonTerminals,
    /// Error returned if any of the given terminals is an invalid terminal symbol.
    WrongTerminals,
    /// Error returned if the given start symbol is an invalid non terminal symbol.
    WrongStartSymbol(Symbol),
    /// Error returned if an error occurred during symbol creation.
    SymbolError(SymbolError),
    /// Error returned if an error occurred during productions creation.
    ProductionError(ProductionError),
    /// Error returned if trying to create a grammar without a start symbol.
    ///
    /// The optional passed argument is the reason which caused the grammar to not have a
    /// start symbol and can be useful for debugging purposes
    ///
    /// When trying to create a grammar from string, the start symbol will be taken from the left hand
    /// side of the first produciton rule, that is, it should be a 1 long collection of symbols.
    NoStartSymbol(Option<String>),
    /// Error returned if trying to create a grammar with too many start symbols.
    ///
    /// The passed production argument is the production from which a start symbol has been tried to extract.
    ///
    /// When trying to create a grammar from string, the start symbol will be taken from the left hand
    /// side of the first produciton rule, that is, it should be a 1 long collection of symbols.
    MultipleStartSymbols(Production),
}

impl fmt::Display for GrammarError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GrammarError::WrongNonTerminals => write!(
                f,
                "GrammarError: non non terminal symbols as non terminal symbols for grammar"
            ),
            GrammarError::WrongTerminals => write!(
                f,
                "GrammarError: non terminal symbols as terminal symbols in grammar"
            ),
            GrammarError::WrongStartSymbol(s) => write!(
                f,
                "GrammarError: start symbol should be a valid nont terminal symbol, received \"{}\" instead", s
            ),
            GrammarError::NoStartSymbol(cause) => {
                write!(f, "GrammarError: grammar has no start symbol, cause: {}", cause.clone().unwrap_or("unspecified".to_string()))
            },
            GrammarError::MultipleStartSymbols(p) => {
                write!(f, "GrammarError: grammar has multiple start symbols in production {}", p)
            },
            GrammarError::SymbolError(e) => {
                write!(f, "GrammarError: symbol error encountered = {}", e)
            },
            GrammarError::ProductionError(e) => {
                write!(f, "GrammarError: production error encountered = {}", e)
            }
        }
    }
}

impl Error for GrammarError {}

impl std::convert::From<ProductionError> for GrammarError {
    fn from(e: ProductionError) -> Self {
        GrammarError::ProductionError(e)
    }
}

/// A grammar is the main type of this module
///
/// It allows to work on grammar over an easy abstraction. A grammar is a quadruple of:
/// - n, a set of non terminal symbols
/// - t, a set of terminal symbols
/// - p, an ordered collection of productions
/// - s, a start symbol
///
/// You can easily create a grammar from a raw string by specifing the productions involved.
/// The remaining n, t and s elements of the quadruple will be automatically extracted from the productions.
/// The s (start symbol) element will be the left hand side of the first production encountered, which has to be a 1 symbol long length.
/// For further details about the formatting of the raw string, you can have a look at how
/// to specify productions from a raw string in the [Production](../production/struct.Production.html) documentation.
#[derive(Debug, PartialEq, Clone)]
pub struct Grammar {
    n: HashSet<Symbol>,
    t: HashSet<Symbol>,
    p: Vec<Production>,
    s: Symbol,
}

impl Grammar {
    /// Return a new grammar based on the quadruple elements passed as arguments.
    ///
    /// # Errors
    /// Returns an error if any of the strings from n, t collections or s are not valid symbols, specifically:
    /// - [WrongNonTerminals](enum.GrammarError.html#variant.WrongNonTerminals) if any of the n symbols aren't non terminals
    /// - [WrongTerminals](enum.GrammarError.html#variant.WrongTerminals) if any of the t symbols aren't terminals
    /// - [SymbolError](enum.GrammarError.html#variant.SymbolError) if the s symbol is not a non terminal
    ///
    /// # Examples
    /// ```rust
    /// use liblet::grammar::Grammar;
    /// use liblet::production::production;
    /// use liblet::symbol::symbol;
    ///
    /// // create a grammar
    /// let g = Grammar::new(
    ///     vec![symbol("A")], // one non terminal "A"
    ///     vec![symbol("a")], // one terminal, "a"
    ///     vec![production("A","a")], // only one production, A -> a
    ///     symbol("A") // the start symbol "A"
    /// );
    ///
    /// assert!(g.is_ok());
    /// ```
    pub fn new<S, P>(n: S, t: S, p: P, s: Symbol) -> Result<Grammar, GrammarError>
    where
        S: IntoIterator<Item = Symbol>,
        P: IntoIterator<Item = Production>,
    {
        let mut n: HashSet<Symbol> = n.into_iter().collect();
        let t: HashSet<Symbol> = t.into_iter().collect();
        let p: Vec<Production> = p.into_iter().collect();

        if !s.is_non_terminal() {
            return Err(GrammarError::WrongStartSymbol(s));
        }

        n.insert(s.clone());

        if !n.iter().all(|s: &Symbol| s.is_non_terminal()) {
            return Err(GrammarError::WrongNonTerminals);
        }

        if !t.iter().all(|s: &Symbol| s.is_terminal()) {
            return Err(GrammarError::WrongTerminals);
        }

        Ok(Grammar {
            n: n,
            t: t,
            p: p,
            s: s,
        })
    }

    /// Return a new grammar based on the quadruple elements passed as arguments.
    /// This differ from the [new](#method.new) constructor because it allows you to use plain string
    /// instead of already built [Symbol](../symbol/struct.Symbol.html)s.
    ///
    /// # Errors
    /// Returns an error if any of the strings from n, t collections or s can't be transformed into [Symbol](../symbol/struct.Symbol.html), specifically:
    /// - [WrongNonTerminals](enum.GrammarError.html#variant.WrongNonTerminals) if an error occurred in the n collection
    /// - [WrongTerminals](enum.GrammarError.html#variant.WrongTerminals) if an error occurred in the t collection
    /// - [SymbolError](enum.GrammarError.html#variant.SymbolError) if an error occurred in the s
    ///
    /// Returns a [ProductionError](enum.GrammarError.html#variant.ProductionError) if any of the strings from the productions collection can't be transformed into [Production](../production/struct.Production.html).
    ///
    /// # Examples
    /// ```rust
    /// use liblet::grammar::Grammar;
    ///
    /// // create a grammar (same as new constructor)
    /// let g = Grammar::new_from_string(
    ///     vec!["A"],
    ///     vec!["a"],
    ///     vec!["A -> a"],
    ///     "A"
    /// );
    ///
    /// assert!(g.is_ok());
    /// ```
    pub fn new_from_string<'a, I>(n: I, t: I, p: I, s: &str) -> Result<Grammar, GrammarError>
    where
        I: IntoIterator<Item = &'a str>,
    {
        let n = n
            .into_iter()
            .map(|s| Symbol::new(s))
            .fold_results(HashSet::new(), |mut acc, x| {
                acc.insert(x);
                acc
            });
        let t = t
            .into_iter()
            .map(|s| Symbol::new(s))
            .fold_results(HashSet::new(), |mut acc, x| {
                acc.insert(x);
                acc
            });

        let p = Production::from_iter(p);
        let s = Symbol::new(s);

        match (n, t, p, s) {
            (Ok(n), Ok(t), Ok(p), Ok(s)) => Grammar::new(n, t, p, s),
            (Err(_), _, _, _) => Err(GrammarError::WrongNonTerminals),
            (_, Err(_), _, _) => Err(GrammarError::WrongTerminals),
            (_, _, Err(e), _) => Err(GrammarError::ProductionError(e)),
            (_, _, _, Err(e)) => Err(GrammarError::SymbolError(e)),
        }
    }

    /// Return the set of non terminal symbols representing the n of the grammar quadruple.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::grammar::Grammar;
    /// use liblet::production::production;
    /// use liblet::symbol::{Symbol,symbol};
    /// use std::collections::HashSet;
    ///
    /// // create a grammar
    /// let g = Grammar::new_from_string(
    ///     vec!["A"],
    ///     vec!["a"],
    ///     vec!["A -> a"],
    ///     "A"
    /// )?;
    /// let n: HashSet<Symbol> = vec![symbol("A")].into_iter().collect();
    ///
    /// assert_eq!(g.n(), n);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn n(&self) -> HashSet<Symbol> {
        self.n.clone()
    }

    /// Return the set of terminal symbols representing the t of the grammar quadruple.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::grammar::Grammar;
    /// use liblet::production::production;
    /// use liblet::symbol::{Symbol,symbol};
    /// use std::collections::HashSet;
    ///
    /// // create a grammar
    /// let g = Grammar::new_from_string(
    ///     vec!["A"],
    ///     vec!["a"],
    ///     vec!["A -> a"],
    ///     "A"
    /// )?;
    /// let t: HashSet<Symbol> = vec![symbol("a")].into_iter().collect();
    ///
    /// assert_eq!(g.t(), t);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn t(&self) -> HashSet<Symbol> {
        self.t.clone()
    }

    /// Return the ordered collection of productions representing the p of the grammar quadruple.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::grammar::Grammar;
    /// use liblet::production::{Production,production};
    ///
    /// // create a grammar
    /// let g = Grammar::new_from_string(
    ///     vec!["A"],
    ///     vec!["a"],
    ///     vec!["A -> a"],
    ///     "A"
    /// )?;
    /// let p: Vec<Production> = vec![production("A","a")];
    ///
    /// assert_eq!(g.p(), p);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn p(&self) -> Vec<Production> {
        self.p.clone()
    }

    /// Return the start symbol, that is the s of the grammar quadruple.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::grammar::Grammar;
    /// use liblet::symbol::{Symbol,symbol};
    ///
    /// // create a grammar
    /// let g = Grammar::new_from_string(
    ///     vec!["A"],
    ///     vec!["a"],
    ///     vec!["A -> a"],
    ///     "A"
    /// )?;
    /// let s: Symbol = symbol("A");
    ///
    /// assert_eq!(g.s(), s);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn s(&self) -> Symbol {
        self.s.clone()
    }

    /// Return a new grammar constructed from the raw string passed as argument.
    ///
    /// The process of converting from a raw string to a grammar is defined at the grammar
    /// struct [documentation](struct.Grammar.html) level.
    ///
    /// # Errors
    /// - Returns a [NoStartSymbol](enum.GrammarError.html#variant.NoStartSymbol) error if there are no productions in the raw string
    /// (since it can not derive a valid start symbol automatically) or if the first production
    /// doesn't have a left hand side
    /// - Returns a [MultipleStartSymbols](enum.GrammarError.html#variant.MultipleStartSymbols) error if there are multiple symbols in the first production left hand side
    ///
    /// # Examples
    /// ```rust
    /// use liblet::grammar::Grammar;
    ///
    /// // create a grammar
    /// let g = Grammar::from_string("A -> a");
    /// // n = {A}
    /// // t = {a}
    /// // p = [A -> a]
    /// // s = {A}
    ///
    /// assert!(g.is_ok());
    /// ```
    pub fn from_string(string: &str) -> Result<Grammar, GrammarError> {
        let p = Production::from_string(string)?;

        let (n, t): (HashSet<Symbol>, HashSet<Symbol>) = p
            .iter()
            .map(|p| p.symbols())
            .fold(HashSet::new(), |mut acc, s| {
                acc.extend(s);
                acc
            })
            .into_iter()
            .partition(|s| s.is_non_terminal());

        let s: Symbol;

        if let Some(p) = p.iter().next() {
            let lhs = p.lhs();
            let mut lhs = lhs.iter();
            if let Some(lhs) = lhs.next() {
                s = lhs.clone()
            } else {
                return Err(GrammarError::NoStartSymbol(Some(
                    "first production rule does not have a lhs".to_string(),
                )));
            }

            if let Some(_) = lhs.next() {
                return Err(GrammarError::MultipleStartSymbols(p.clone()));
            }
        } else {
            return Err(GrammarError::NoStartSymbol(Some(
                "found no production rules".to_string(),
            )));
        }

        Grammar::new(n, t, p, s)
    }

    /// Return a collection of productions right hand side for each production which left hand side matches
    /// the given ordered collection of symbols.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::grammar::Grammar;
    /// use liblet::symbol::{Symbol,symbol};
    ///
    /// // create a grammar
    /// let g = Grammar::from_string("A -> a | b")?;
    /// // find alternatives for left hand side "A"
    /// let alternatives = g.alternatives(vec![symbol("A")]);
    ///
    /// assert_eq!(alternatives.len(), 2);
    /// assert_eq!(alternatives[0], vec![symbol("a")]);
    /// assert_eq!(alternatives[1], vec![symbol("b")]);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn alternatives<I>(&self, symbols: I) -> Vec<Vec<Symbol>>
    where
        I: IntoIterator<Item = Symbol>,
    {
        let symbols: Vec<Symbol> = symbols.into_iter().collect();
        let mut alternatives: Vec<Vec<Symbol>> = Vec::new();
        for p in &self.p {
            if &p.lhs() == &symbols {
                alternatives.push(p.rhs())
            }
        }

        alternatives
    }

    /// Return a new grammar restricted to have only the symbols in the collection passed as argument.
    ///
    /// So every element in the new grammar quadruple can only have the passed symbols inside, everything else is deleted.
    /// This does not affect the original grammar.
    ///
    /// # Errors
    /// Returns a [NoStartSymbol](enum.GrammarError.html#variant.NoStartSymbol) error if the restrict operation would
    /// delete the start symbol from the original grammar, since it can't automatically choose another start symbol.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::grammar::Grammar;
    /// use liblet::production::production;
    /// use liblet::symbol::{Symbol,symbol};
    /// use std::collections::HashSet;
    ///
    /// // create a grammar
    /// let g = Grammar::from_string("A -> a | b")?;
    /// // restrict the grammar to a new one with only the "A" and "a" symbols
    /// let g_restricted = g.restrict_to(vec![symbol("A"),symbol("a")])?;
    /// // we except a single non terminal symbol "A"
    /// let expected_n: HashSet<Symbol> = vec![symbol("A")].into_iter().collect();
    /// // we except the terminal symbols "A" and "a", but not "b"
    /// let expected_t: HashSet<Symbol> = vec![symbol("a")].into_iter().collect();
    /// // we except the only production "A -> a", but not "A -> b"
    /// let expected_p = vec![production("A","a")];
    ///
    /// assert_eq!(g_restricted.n(), expected_n);
    /// assert_eq!(g_restricted.t(), expected_t);
    /// assert_eq!(g_restricted.p(), expected_p);
    /// assert_eq!(g_restricted.s(), symbol("A")); // the start symbol is still the same
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn restrict_to<I>(&self, symbols: I) -> Result<Grammar, GrammarError>
    where
        I: IntoIterator<Item = Symbol>,
    {
        let symbols: HashSet<Symbol> = symbols.into_iter().collect();
        let n: HashSet<Symbol> = symbols.intersection(&self.n).cloned().collect();
        let t: HashSet<Symbol> = symbols.intersection(&self.t).cloned().collect();

        if !symbols.contains(&self.s) {
            return Err(GrammarError::NoStartSymbol(Some(
                "restricting the grammar lead to a grammar without start symbol".to_string(),
            )));
        }

        let p: Vec<Production> = self
            .p
            .iter()
            .filter(|p: &&Production| p.symbols().difference(&symbols).count() == 0)
            .cloned()
            .collect();

        Grammar::new(n, t, p, self.s.clone())
    }

    /// Return a set of symbols (from the grammar symbols) which are productives.
    ///
    /// That is, only the symbols that have some production rule (or production rule chains)
    /// that transform that symbol to a non terminal one. The set of productives symbols contains the terminal ones,
    /// since they are the products themself.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::grammar::Grammar;
    /// use liblet::symbol::{Symbol,symbol};
    /// use std::collections::HashSet;
    ///
    /// // create a grammar
    /// let g = Grammar::from_string("
    ///     A -> a | C
    ///     B -> b
    /// ")?;
    /// // let's define the expected productives, "C" should not be productive
    /// let expected: HashSet<Symbol> = vec![
    ///     symbol("A"),
    ///     symbol("B"),
    ///     symbol("a"),
    ///     symbol("b"),
    /// ].into_iter().collect();
    ///
    /// assert_eq!(g.productives(), expected);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn productives(&self) -> HashSet<Symbol> {
        self.productives_from(self.t.clone())
    }

    fn productives_from(&self, productives: HashSet<Symbol>) -> HashSet<Symbol> {
        let mut productives_next: HashSet<Symbol> = productives.clone();
        for p in &self.p {
            let rhs: HashSet<Symbol> = p.rhs().into_iter().collect();
            if rhs.is_subset(&productives_next) {
                let lhs: HashSet<Symbol> = p.lhs().into_iter().collect();
                productives_next = productives_next.union(&lhs).cloned().collect();
            }
        }

        if productives == productives_next {
            productives_next
        } else {
            self.productives_from(productives_next)
        }
    }

    /// Return a set of symbols (from the grammar symbols) which are reachable from
    /// the start symbol of the grammar.
    ///
    /// That is, only symbols that can be reached by some production rule (or production rule chains).
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::grammar::Grammar;
    /// use liblet::symbol::{Symbol,symbol};
    /// use std::collections::HashSet;
    ///
    /// // create a grammar
    /// let g = Grammar::from_string("
    ///     A -> a | b
    ///     B -> b
    /// ")?;
    /// // let's define the expected rachable, "B" should not be reachable
    /// let expected: HashSet<Symbol> = vec![
    ///     symbol("A"),
    ///     symbol("a"),
    ///     symbol("b"),
    /// ].into_iter().collect();
    ///
    /// assert_eq!(g.reachable(), expected);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn reachable(&self) -> HashSet<Symbol> {
        let from: HashSet<Symbol> = vec![self.s()].into_iter().collect();
        self.reachable_from(from)
    }

    /// Return a set of symbols (from the grammar symbols) which are reachable from
    /// the set of symbols passed as arguments.
    ///
    /// It has the same behaviour of the [reachable](#method.reachable) method but the symbols to search from
    /// are here passed as input.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::grammar::Grammar;
    /// use liblet::symbol::{Symbol,symbol};
    /// use std::collections::HashSet;
    ///
    /// // create a grammar
    /// let g = Grammar::from_string("
    ///     A -> a | b
    ///     B -> b
    /// ")?;
    /// // let's define the expected rachable, "A" and "a" should not be reachable
    /// // if we start from "B"
    /// let expected: HashSet<Symbol> = vec![
    ///     symbol("B"),
    ///     symbol("b"),
    /// ].into_iter().collect();
    ///
    /// assert_eq!(g.reachable_from(vec![symbol("B")]), expected);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn reachable_from<I>(&self, reached: I) -> HashSet<Symbol>
    where
        I: IntoIterator<Item = Symbol>,
    {
        let reached: HashSet<Symbol> = reached.into_iter().collect();
        let mut reached_next: HashSet<Symbol> = reached.clone();
        for p in &self.p {
            let lhs: HashSet<Symbol> = p.lhs().into_iter().collect();
            if lhs.is_subset(&reached_next) {
                let rhs: HashSet<Symbol> = p.rhs().into_iter().collect();
                reached_next = reached_next.union(&rhs).cloned().collect();
            }
        }

        if reached == reached_next {
            reached_next
        } else {
            self.reachable_from(reached_next)
        }
    }
}

/// Convenience function for creating a grammar from a raw string
/// (which defines the productions of the grammar, as described in the Grammar struct
/// [documentation](struct.Grammar.html))
///
/// It returns the grammar directly,
/// as opposed to the `Result` returned from the grammar [constructor](struct.Grammar.html#method.new).
///
/// # Panics
/// Panics if some error occurred during grammar creation (see grammar [consructor](struct.Grammar.html#method.new) for further details)
///
/// # Examples
/// ```rust
/// use liblet::grammar::grammar;
/// use liblet::production::production;
/// use liblet::symbol::symbol;
///
/// let g = grammar("A -> a");
///
/// assert_eq!(g.n(), vec![symbol("A")].into_iter().collect());
/// assert_eq!(g.t(), vec![symbol("a")].into_iter().collect());
/// assert_eq!(g.p(), vec![production("A","a")]);
/// assert_eq!(g.s(), symbol("A"));
/// ```
pub fn grammar(string: &str) -> Grammar {
    Grammar::from_string(string).unwrap()
}

/// Convenience function for creating a grammar from collections of string as in grammar
/// [new_from_string](struct.Grammar.html#method.new_from_string).
///
/// It returns the grammar directly,
/// as opposed to the `Result` returned from the grammar [new_from_string](struct.Grammar.html#method.new_from_string).
///
/// # Panics
/// Panics if some error occurred during grammar creation (see grammar [new_from_string](struct.Grammar.html#method.new_from_string) for further details)
///
/// # Examples
/// ```rust
/// use liblet::grammar::grammar_iter;
/// use liblet::production::production;
/// use liblet::symbol::symbol;
///
/// let g = grammar_iter(
///     vec!["A"],
///     vec!["a"],
///     vec!["A -> a"],
///     "A"
/// );
///
/// assert_eq!(g.n(), vec![symbol("A")].into_iter().collect());
/// assert_eq!(g.t(), vec![symbol("a")].into_iter().collect());
/// assert_eq!(g.p(), vec![production("A","a")]);
/// assert_eq!(g.s(), symbol("A"));
/// ```
pub fn grammar_iter<'a, I>(n: I, t: I, p: I, s: &str) -> Grammar
where
    I: IntoIterator<Item = &'a str>,
{
    Grammar::new_from_string(n, t, p, s).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::production::production;
    use crate::symbol::symbol;

    #[test]
    pub fn from_string() {
        let s_check: Symbol = symbol("S");
        let n_check: HashSet<Symbol> = vec![symbol("S"), symbol("A"), symbol("B")]
            .into_iter()
            .collect();
        let t_check: HashSet<Symbol> = vec![symbol("a"), symbol("b")].into_iter().collect();
        let p_check: Vec<Production> = vec![
            production("S", "A B"),
            production("A", "a"),
            production("A", "B"),
            production("B", "b"),
        ];

        let g = Grammar::from_string("S -> A B\nA -> a | B\nB -> b").unwrap();
        assert_eq!(g.s, s_check, "Parsed start symbol is not the one expected");
        assert_eq!(
            g.n, n_check,
            "Parsed non terminal symbols are not those expected"
        );
        assert_eq!(
            g.t, t_check,
            "Parsed terminal symbols are not those expected"
        );
        assert_eq!(
            g.p, p_check,
            "Parsed production rules are not those expected"
        );
    }

    #[test]
    pub fn from_string_error() {
        match Grammar::from_string("S ->\n -> a | B\nB -> b") {
            Ok(_) => panic!("grammar from string should return error"),
            Err(e) => match e {
                GrammarError::ProductionError(_) => (),
                e => panic!(
                    "Creation of grammar from test input should return a ProductionError but returned Err \"{}\" instead",
                    e
                ),
            }
        }
    }

    #[test]
    pub fn alternatives() {
        let g = Grammar::from_string("S -> A B\nA -> a | B\nB -> b").unwrap();
        let a_check = vec![vec![symbol("a")], vec![symbol("B")]];

        assert_eq!(
            g.alternatives(vec![symbol("A")]),
            a_check,
            "Alternatives are not the one expected"
        );
    }

    #[test]
    pub fn alternatives_empty() {
        let g = Grammar::from_string("S -> A B\nA -> a | B\nB -> b").unwrap();

        assert!(
            g.alternatives(vec![symbol("a")]).is_empty(),
            "Alternatives are not empty when they should"
        );
    }

    #[test]
    pub fn restrict_to() {
        let g_restricted = Grammar::from_string("S -> A\nA -> a | B\nB -> b")
            .unwrap()
            .restrict_to(vec![symbol("S"), symbol("A"), symbol("a")])
            .unwrap();

        let s_check: Symbol = symbol("S");
        let n_check: HashSet<Symbol> = vec![symbol("S"), symbol("A")].into_iter().collect();
        let t_check: HashSet<Symbol> = vec![symbol("a")].into_iter().collect();
        let p_check: Vec<Production> = vec![production("S", "A"), production("A", "a")];

        assert_eq!(
            g_restricted.s, s_check,
            "Restricted grammar start symbol is not the one expected"
        );
        assert_eq!(
            g_restricted.n, n_check,
            "Restricted grammar non terminal symbols are not those expected"
        );
        assert_eq!(
            g_restricted.t, t_check,
            "Restricted grammar terminal symbols are not those expected"
        );
        assert_eq!(
            g_restricted.p, p_check,
            "Restricted grammar production rules are not those expected"
        );
    }

    #[test]
    pub fn restrict_to_panic_start_symbol() {
        match Grammar::from_string("S -> A\nA -> a | B\nB -> b")
            .unwrap()
            .restrict_to(vec![symbol("A"), symbol("a")]) {
                Ok(_) => panic!("restricting grammar should return error"),
                Err(e) => match e {
                    GrammarError::NoStartSymbol(_) => (),
                    e => panic!(
                        "Creation of grammar from test input should return a NoStartSymbol error but returned Err \"{}\" instead",
                        e
                    ),
            }
            }
    }

    #[test]
    pub fn new() {
        let s_check: Symbol = symbol("S");
        let n_check: HashSet<Symbol> = vec![symbol("S"), symbol("A")].into_iter().collect();
        let t_check: HashSet<Symbol> = vec![symbol("a")].into_iter().collect();
        let p_check: Vec<Production> = vec![production("S", "A"), production("A", "a")];
        let g = Grammar::new(
            n_check.clone(),
            t_check.clone(),
            p_check.clone(),
            s_check.clone(),
        )
        .unwrap();

        assert_eq!(
            g.s, s_check,
            "new grammar start symbol is not the one expected"
        );
        assert_eq!(
            g.n, n_check,
            "New grammar non terminal symbols are not those expected"
        );
        assert_eq!(
            g.t, t_check,
            "New grammar terminal symbols are not those expected"
        );
        assert_eq!(
            g.p, p_check,
            "New grammar production rules are not those expected"
        );
    }

    #[test]
    pub fn new_from_string() {
        let s_check: Symbol = symbol("S");
        let n_check: HashSet<Symbol> = vec![symbol("S"), symbol("A")].into_iter().collect();
        let t_check: HashSet<Symbol> = vec![symbol("a")].into_iter().collect();
        let p_check: Vec<Production> = vec![production("S", "A"), production("A", "a")];
        let g = Grammar::new_from_string(vec!["S", "A"], vec!["a"], vec!["S -> A\nA -> a"], "S")
            .unwrap();

        assert_eq!(
            g.s, s_check,
            "new grammar start symbol is not the one expected"
        );
        assert_eq!(
            g.n, n_check,
            "New grammar non terminal symbols are not those expected"
        );
        assert_eq!(
            g.t, t_check,
            "New grammar terminal symbols are not those expected"
        );
        assert_eq!(
            g.p, p_check,
            "New grammar production rules are not those expected"
        );
    }

    #[test]
    pub fn grammar() {
        let s_check: Symbol = symbol("S");
        let n_check: HashSet<Symbol> = vec![symbol("S"), symbol("A"), symbol("B")]
            .into_iter()
            .collect();
        let t_check: HashSet<Symbol> = vec![symbol("a"), symbol("b")].into_iter().collect();
        let p_check: Vec<Production> = vec![
            production("S", "A B"),
            production("A", "a"),
            production("A", "B"),
            production("B", "b"),
        ];

        let g = super::grammar("S -> A B\nA -> a | B\nB -> b");
        assert_eq!(g.s, s_check, "Parsed start symbol is not the one expected");
        assert_eq!(
            g.n, n_check,
            "Parsed non terminal symbols are not those expected"
        );
        assert_eq!(
            g.t, t_check,
            "Parsed terminal symbols are not those expected"
        );
        assert_eq!(
            g.p, p_check,
            "Parsed production rules are not those expected"
        );
    }

    #[test]
    pub fn grammar_iter() {
        let s_check: Symbol = symbol("S");
        let n_check: HashSet<Symbol> = vec![symbol("S"), symbol("A")].into_iter().collect();
        let t_check: HashSet<Symbol> = vec![symbol("a")].into_iter().collect();
        let p_check: Vec<Production> = vec![production("S", "A"), production("A", "a")];
        let g = super::grammar_iter(vec!["S", "A"], vec!["a"], vec!["S -> A\nA -> a"], "S");

        assert_eq!(
            g.s, s_check,
            "new grammar start symbol is not the one expected"
        );
        assert_eq!(
            g.n, n_check,
            "New grammar non terminal symbols are not those expected"
        );
        assert_eq!(
            g.t, t_check,
            "New grammar terminal symbols are not those expected"
        );
        assert_eq!(
            g.p, p_check,
            "New grammar production rules are not those expected"
        );
    }

    #[test]
    pub fn reachable() {
        let g: Grammar = super::grammar(
            "
            S -> A | B
            A -> a
            B -> b
            C -> c
        ",
        );
        let symbols_check: HashSet<Symbol> = vec![
            symbol("S"),
            symbol("A"),
            symbol("B"),
            symbol("a"),
            symbol("B"),
            symbol("b"),
        ]
        .into_iter()
        .collect();
        assert_eq!(
            g.reachable(),
            symbols_check,
            "Reachable symbols from grammar are not those expected"
        );
    }

    #[test]
    pub fn reachable_from() {
        let g: Grammar = super::grammar(
            "
            S -> A | B
            A -> a
            B -> b
            C -> c
        ",
        );
        let symbols_check: HashSet<Symbol> = vec![symbol("A"), symbol("a")].into_iter().collect();
        let from: HashSet<Symbol> = vec![symbol("A")].into_iter().collect();
        assert_eq!(
            g.reachable_from(from),
            symbols_check,
            "Reachable symbols from grammar are not those expected"
        );
    }

    #[test]
    pub fn productives() {
        let g: Grammar = super::grammar(
            "
            S -> A | B
            B -> b
            C -> c
            D -> d
        ",
        );
        let symbols_check: HashSet<Symbol> = vec![
            symbol("S"),
            symbol("B"),
            symbol("b"),
            symbol("C"),
            symbol("c"),
            symbol("D"),
            symbol("d"),
        ]
        .into_iter()
        .collect();
        assert_eq!(
            g.productives(),
            symbols_check,
            "Productives symbols from grammar are not those expected"
        );
    }

    #[test]
    pub fn productives_from() {
        let g: Grammar = super::grammar(
            "
            S -> A | B
            B -> b
            C -> c
            D -> d
        ",
        );
        let symbols_check: HashSet<Symbol> = vec![symbol("S"), symbol("B"), symbol("b")]
            .into_iter()
            .collect();
        let from: HashSet<Symbol> = vec![symbol("b")].into_iter().collect();
        assert_eq!(
            g.productives_from(from),
            symbols_check,
            "Productives symbols from grammar are not those expected"
        );
    }
}
