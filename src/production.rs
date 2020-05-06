//! Module for handling all productions related operations.
//!
//! Its goal is to emulate a formal grammar production.
//!
//! It defines a `Production` type which can be used to conveniently work with productions in grammars,
//! and provide abstraction over normal collection of symbols, organized in a left and right hand side (form A -> B).
//!
//! It can be easily constructed from `&str`s or collections of [Symbol](../symbol/struct.Symbol.html)s.

use crate::symbol::{Symbol, SymbolError};
use crate::tokenizer;
use crate::tokenizer::TokenizerError;
use itertools::Itertools;
use std::collections::HashSet;
use std::error::Error;
use std::fmt;

#[derive(Debug, PartialEq, Clone)]
pub enum ProductionError {
    /// Error returned for trying to create a Production with an empty / missing left hand side.
    /// Left hand side of productions should be an ordered collection of n >= 1 symbols.
    NoLhs,
    /// Error returned for trying to create a Production with an empty / missing right hand side.
    /// Right hand side of productions should be an ordered collection of n >= 1 symbols.
    NoRhs,
    /// Error returned for trying to create a Production with invalid symbols.
    /// To be expected when creating productions from raw string inputs.
    SymbolError(SymbolError),
    /// Error returned for trying to create a Production with a bad formatted raw input string.
    /// Properly formatted productions as strings are described in the
    /// [Production](struct.Production.html) documentation.
    FormatError(TokenizerError),
}

impl fmt::Display for ProductionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProductionError::NoLhs => write!(f, "ProductionError: no lhs in production"),
            ProductionError::NoRhs => write!(f, "ProductionError: no rhs in production"),
            ProductionError::SymbolError(e) => {
                write!(f, "ProductionError: symbol error encountered = {}", e)
            }
            ProductionError::FormatError(e) => write!(
                f,
                "ProductionError: bad formatted string encountered, error = {}",
                e
            ),
        }
    }
}

impl Error for ProductionError {}

impl std::convert::From<TokenizerError> for ProductionError {
    fn from(e: TokenizerError) -> Self {
        ProductionError::FormatError(e)
    }
}

/// A predicate for checking if production match some expected characteristics.
///
/// You can test a predicate on a Production by using the [test]: #method.test method.
pub enum ProductionPredicate {
    /// It checks if the left hand side of the production equals the given ordered collection of symbols.
    LhsEquals(Vec<Symbol>),
    /// It checks if the right hand side of the production equals the given ordered collection of symbols.
    RhsEquals(Vec<Symbol>),
    /// It checks if the right hand side length (symbols count) of the production equals the given number.
    RhsLengthEquals(usize),
    /// It checks if the right hand side of the production ends with the given ordered collection of symbols.
    RhsIsSuffixOf(Vec<Symbol>),
}

impl ProductionPredicate {
    /// Test if a production match the predicate
    ///
    /// # Examples
    /// ```rust
    /// use liblet::production::{ProductionPredicate, production};
    /// use liblet::symbol::symbol;
    ///
    /// // create a new production "A -> B C"
    /// let p = production("A", "B C");
    /// let rhs = vec![symbol("B"), symbol("C")];
    ///
    /// assert!(ProductionPredicate::RhsEquals(rhs).test(&p));
    /// ```
    pub fn test(&self, p: &Production) -> bool {
        match self {
            ProductionPredicate::LhsEquals(symbols) => p.lhs() == *symbols,
            ProductionPredicate::RhsEquals(symbols) => p.rhs() == *symbols,
            ProductionPredicate::RhsLengthEquals(length) => p.rhs().len() == *length,
            ProductionPredicate::RhsIsSuffixOf(symbols) => p.rhs().ends_with(&symbols),
        }
    }
}

/// The main type of this module.
///
/// It allows to abstract over grammar productions, having a defined left and right and side,
/// which are ordered collections of symbols.
///
/// A production can be created easily from strings, following these rules:
/// - string can contain any number of whitespace
/// - multiple productions are divided by '\n' char
/// - string must have a sequence of symbol to the left of a "->"
/// - string must have a sequence of alternatives to the right of a "->"
/// - string can have only one "->" per production (per line)
/// - a sequence of symbol is a sequence of symbols divided by some whitespace
/// - a sequence of alternative is one ore more sequence of symbols divided by the "|" char
/// - string can't contain anything else
///
/// # Examples
/// `A -> B` leads to a production from the symbol `A` to the symbol `B`
///
/// `A -> B | C` leads to two productions, one for each alternative (`A` -> `B` and `A` -> `C`)
///
/// `A -> B\nA -> C` leads to the same result of the above one, defining the two productions separately
///
/// `A -> ` will results in an error, because there's no right hand side for the production
#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub struct Production {
    lhs: Vec<Symbol>,
    rhs: Vec<Symbol>,
}

impl fmt::Display for Production {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for lhs in self.lhs() {
            write!(f, "{} ", lhs)?;
        }
        write!(f, "->")?;
        for rhs in self.rhs() {
            write!(f, " {}", rhs)?;
        }

        Ok(())
    }
}

impl Production {
    /// Creates a new Production based on the left and right hand side given as collections of symbols.
    ///
    /// # Errors
    /// It can return an error if either the left or right hand side is empty.
    ///
    /// # Examples
    /// ```rust
    /// use liblet::production::Production;
    /// use liblet::symbol::symbol;
    ///
    /// // create left and right hand side for production "A -> B C"
    /// let lhs = vec![symbol("A")];
    /// let rhs = vec![symbol("B"), symbol("C")];
    ///
    /// // create a new production based on the previously defined left and right hand side
    /// let production = Production::new(lhs, rhs);
    ///
    /// assert!(production.is_ok());
    /// ```
    pub fn new<I>(lhs: I, rhs: I) -> Result<Production, ProductionError>
    where
        I: IntoIterator<Item = Symbol>,
    {
        let lhs: Vec<Symbol> = lhs.into_iter().collect();
        let rhs: Vec<Symbol> = rhs.into_iter().collect();

        if lhs.is_empty() {
            return Err(ProductionError::NoLhs);
        }
        if rhs.is_empty() {
            return Err(ProductionError::NoRhs);
        }

        Ok(Production { lhs: lhs, rhs: rhs })
    }

    /// Creates a new Production based on the left and right hand side given as collections of `&str`.
    ///
    /// # Errors
    /// It can return an error if the strings are not convertible to [Symbol](../symbol/struct.Symbol.html)s.
    /// Otherwise, it acts like [new](#method.new).
    ///
    /// # Examples
    /// ```rust
    /// use liblet::production::Production;
    /// use liblet::symbol::symbol;
    ///
    /// // create left and right hand side for production "A -> B C"
    /// let lhs = vec!["A"];
    /// let rhs = vec!["B", "C"];
    ///
    /// // create a new production based on the previously defined left and right hand side
    /// let production = Production::new_from_string(lhs, rhs);
    ///
    /// assert!(production.is_ok());
    /// ```
    pub fn new_from_string<'a, I>(lhs: I, rhs: I) -> Result<Production, ProductionError>
    where
        I: IntoIterator<Item = &'a str>,
    {
        let lhs =
            lhs.into_iter()
                .map(|s: &str| Symbol::new(s))
                .fold_results(Vec::new(), |mut acc, x| {
                    acc.push(x);
                    acc
                });
        let rhs =
            rhs.into_iter()
                .map(|s: &str| Symbol::new(s))
                .fold_results(Vec::new(), |mut acc, x| {
                    acc.push(x);
                    acc
                });

        match (lhs, rhs) {
            (Ok(lhs), Ok(rhs)) => Production::new(lhs, rhs),
            (Err(e), _) => Err(ProductionError::SymbolError(e)),
            (_, Err(e)) => Err(ProductionError::SymbolError(e)),
        }
    }

    /// Return the ordered collection of symbol representing the left hand side of the production.
    ///
    /// # Examples
    /// ```rust
    /// use liblet::production::{Production,production};
    /// use liblet::symbol::symbol;
    ///
    /// // create a production representing "A -> B C"
    /// let p = production("A", "B C");
    ///
    /// assert_eq!(p.lhs(), vec![symbol("A")]);
    /// ```
    pub fn lhs(&self) -> Vec<Symbol> {
        self.lhs.clone()
    }

    /// Return the ordered collection of symbol representing the right hand side of the production.
    ///
    /// # Examples
    /// ```rust
    /// use liblet::production::{Production,production};
    /// use liblet::symbol::symbol;
    ///
    /// // create a production representing "A -> B C"
    /// let p = production("A", "B C");
    ///
    /// assert_eq!(p.rhs(), vec![symbol("B"), symbol("C")]);
    /// ```
    pub fn rhs(&self) -> Vec<Symbol> {
        self.rhs.clone()
    }

    /// Return a set containing all the different symbols which appears on the left
    /// and right hand side of the production.
    ///
    /// # Examples
    /// ```rust
    /// use liblet::production::{Production,production};
    /// use liblet::symbol::{Symbol,symbol};
    /// use std::collections::HashSet;
    ///
    /// // create a production representing "A -> B C"
    /// let p = production("A", "B C");
    /// let symbols: HashSet<Symbol> = vec![symbol("A"), symbol("B"), symbol("C")].into_iter().collect();
    ///
    /// assert_eq!(p.symbols(), symbols);
    /// ```
    pub fn symbols(&self) -> HashSet<Symbol> {
        let mut symbols: Vec<Symbol> = self.lhs();
        symbols.append(&mut self.rhs());
        symbols.into_iter().collect()
    }

    /// Create a collection of productions from a raw input string.
    ///
    /// # Errors
    /// Can return an error if the raw string can't be parsed to obtain actual productions both due to wrong
    /// string formatting (LHS -> RHS | ...)(see [from_string](../symbol/struct.Symbol.html) method from symbols
    /// for more info about string formatting symbols) and due to production creation error (see production [constructor](#method.new) for more info).
    ///
    /// In the case an empty or whitespace only string is given, it just returns an empty collection of productions.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::production::Production;
    ///
    /// let result = Production::from_string("
    ///     A -> B C
    ///     B -> b
    /// ")?;
    ///
    /// assert_eq!(result.len(), 2);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn from_string(string: &str) -> Result<Vec<Production>, ProductionError> {
        tokenizer::productions_from_string(string)?
            .iter()
            .map(|p| {
                Production::new_from_string::<Vec<&str>>(
                    p.0.iter().map(String::as_str).collect(),
                    p.1.iter().map(String::as_str).collect(),
                )
            })
            .fold_results(Vec::new(), |mut acc, p| {
                acc.push(p);
                acc
            })
    }

    /// Create a collection of productions from a collection of raw input string.
    /// Same as [from_string](#method.from_string) but accepts an `IntoIterator`.
    ///
    /// # Errors
    /// Can return an error if any of the raw strings can't be parsed to obtain actual productions both due to wrong
    /// string formatting (LHS -> RHS | ...)(see [from_string](../symbol/struct.Symbol.html) method from symbols
    /// for more info about string formatting symbols) and due to production creation error (see production [constructor](#method.new) for more info).
    ///
    /// In the case empty or whitespace only strings are given, it just returns an empty collection of productions.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::production::Production;
    ///
    /// let result = Production::from_iter(vec![
    ///     "A -> B C",
    ///     "B -> b"
    /// ])?;
    ///
    /// assert_eq!(result.len(), 2);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn from_iter<'a, I>(strings: I) -> Result<Vec<Production>, ProductionError>
    where
        I: IntoIterator<Item = &'a str>,
    {
        let mut p: Vec<Production> = Vec::new();

        for string in strings {
            p.append(&mut Production::from_string(string)?)
        }

        Ok(p)
    }

    /// Return a boxed `FnMut` which accepts a production and test the given predicate on it, returning a `bool`ean value.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::production::{Production,ProductionPredicate};
    /// use liblet::symbol::symbol;
    ///
    /// let p = Production::from_string("
    ///     A -> B C
    ///     B -> b
    /// ")?;
    /// let closure = Production::such_that(ProductionPredicate::RhsEquals(vec![symbol("b")]));
    /// let expected = Production::new(vec![symbol("B")], vec![symbol("b")])?;
    /// let mut result = p.iter().filter(closure);
    ///
    /// assert_eq!(result.next(), Some(&expected));
    /// assert_eq!(result.next(), None);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn such_that(predicate: ProductionPredicate) -> Box<dyn FnMut(&&Production) -> bool> {
        Box::new(move |p| predicate.test(&p))
    }
}

/// Convenience function for creating a production from a pair of raw strings
/// (left hand side and right hand side).
///
/// It returns the production directly,
/// as opposed to the `Result` returned from the production [constructor](struct.Production.html#method.new).
///
/// # Panics
/// Panics if some error occurred during production creation (see production [consructor](struct.Production.html#method.new) for further details)
///
/// # Examples
/// ```rust
/// use liblet::production::production;
/// use liblet::symbol::symbol;
///
/// let p = production("A", "B C");
///
/// assert_eq!(p.lhs(), vec![symbol("A")]);
/// assert_eq!(p.rhs(), vec![symbol("B"),symbol("C")]);
/// ```
pub fn production(lhs: &str, rhs: &str) -> Production {
    Production::new(
        Symbol::from_string(lhs).unwrap(),
        Symbol::from_string(rhs).unwrap(),
    )
    .unwrap()
}

/// Convenience function for creating a collection of productions from a raw string.
///
/// It returns the productions directly,
/// as opposed to the `Result` returned from the production [from_string](struct.Production.html#method.from_string) method.
///
/// # Panics
/// Panics if some error occurred during productions creation (see production [from_string](struct.Production.html#method.from_string) method for further details)
///
/// # Examples
/// ```rust
/// use liblet::production::productions;
///
/// let p = productions("
///     A -> B C
///     B -> b
/// ");
///
/// assert_eq!(p.len(), 2);
/// ```
pub fn productions(string: &str) -> Vec<Production> {
    Production::from_string(string).unwrap()
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::symbol::symbol;
    use std::fmt::Write;

    #[test]
    pub fn from_string() {
        let p_check = vec![
            Production {
                lhs: vec![symbol("S")],
                rhs: vec![symbol("A"), symbol("B")],
            },
            Production {
                lhs: vec![symbol("A")],
                rhs: vec![symbol("a")],
            },
            Production {
                lhs: vec![symbol("A")],
                rhs: vec![symbol("B")],
            },
            Production {
                lhs: vec![symbol("B")],
                rhs: vec![symbol("b")],
            },
        ];

        assert_eq!(
            Production::from_string("S -> A B\nA -> a | B\nB -> b").unwrap(),
            p_check,
            "Parsed production rules are not those expected"
        );
    }

    #[test]
    pub fn from_string_error() {
        let error = TokenizerError::ProductionNoRhs("S".to_string());
        let result = Production::from_string("S ->\n -> a | B\nB -> b");

        assert!(
            result.is_err(),
            "Production from string on test input should return error"
        );
        let e = result.unwrap_err();
        assert_eq!(
            e,
            ProductionError::FormatError(error),
            "Creation of productions from test input returned the wrong error"
        );
    }

    #[test]
    pub fn from_iter() {
        let p_check = vec![
            Production {
                lhs: vec![symbol("S")],
                rhs: vec![symbol("A"), symbol("B")],
            },
            Production {
                lhs: vec![symbol("A")],
                rhs: vec![symbol("a")],
            },
            Production {
                lhs: vec![symbol("B")],
                rhs: vec![symbol("a")],
            },
            Production {
                lhs: vec![symbol("B")],
                rhs: vec![symbol("b")],
            },
        ];

        assert_eq!(
            super::productions("S -> A B\nA -> a\nB -> a | b"),
            p_check,
            "Created production rules are not those expected"
        );
    }

    #[test]
    pub fn predicate_lhs_equals() {
        let predicate = ProductionPredicate::LhsEquals(vec![symbol("T")]);

        assert!(
            predicate.test(&Production {
                lhs: vec![symbol("T")],
                rhs: vec![]
            }),
            "Predicate should return true"
        );
        assert!(
            !predicate.test(&Production {
                lhs: vec![symbol("F")],
                rhs: vec![]
            }),
            "Predicate should return false"
        );
    }

    #[test]
    pub fn predicate_rhs_equals() {
        let predicate = ProductionPredicate::RhsEquals(vec![symbol("T")]);

        assert!(
            predicate.test(&Production {
                lhs: vec![],
                rhs: vec![symbol("T")]
            }),
            "Predicate should return true"
        );
        assert!(
            !predicate.test(&Production {
                lhs: vec![],
                rhs: vec![symbol("F")]
            }),
            "Predicate should return false"
        );
    }

    #[test]
    pub fn predicate_rhs_length_equals() {
        let predicate = ProductionPredicate::RhsLengthEquals(2);

        assert!(
            predicate.test(&Production {
                lhs: vec![],
                rhs: vec![symbol("T1"), symbol("T2")]
            }),
            "Predicate should return true"
        );
        assert!(
            !predicate.test(&Production {
                lhs: vec![],
                rhs: vec![symbol("F")]
            }),
            "Predicate should return false"
        );
    }

    #[test]
    pub fn predicate_rhs_is_suffix_of() {
        let predicate = ProductionPredicate::RhsIsSuffixOf(vec![symbol("T2"), symbol("T3")]);

        assert!(
            predicate.test(&Production {
                lhs: vec![],
                rhs: vec![symbol("T1"), symbol("T2"), symbol("T3")]
            }),
            "Predicate should return true"
        );
        assert!(
            !predicate.test(&Production {
                lhs: vec![],
                rhs: vec![symbol("F")]
            }),
            "Predicate should return false"
        );
    }

    #[test]
    pub fn such_that() {
        let filter = Production::such_that(ProductionPredicate::LhsEquals(vec![symbol("T")]));
        let productions = Production::from_string("S -> A | B\nA -> a\nT -> t\nB -> B").unwrap();

        let productions_iter = productions.clone();
        let mut filtered = productions_iter.iter().filter(filter);

        assert_eq!(
            filtered.next(),
            productions.get(3),
            "Filtered productions on test input should return the T -> t production"
        );
        assert_eq!(
            filtered.next(),
            None,
            "Filtered productions on test input should return no more productions"
        );
    }

    #[test]
    pub fn new() {
        let p_check = Production {
            lhs: vec![symbol("S")],
            rhs: vec![symbol("A"), symbol("B")],
        };

        assert_eq!(
            Production::new(p_check.lhs(), p_check.rhs()).unwrap(),
            p_check,
            "Created production rule is not the one expected"
        );
    }

    #[test]
    pub fn new_empty_side_lhs() {
        let iter = vec![symbol("S")];

        let result = Production::new(vec![], iter);
        assert!(
            result.is_err(),
            "Creation of production rule should return an error"
        );
        let e = result.unwrap_err();
        assert_eq!(
            e,
            ProductionError::NoLhs,
            "Creation of production rule returned the wrong error"
        );
    }

    #[test]
    pub fn new_empty_side_rhs() {
        let iter = vec![symbol("S")];

        let result = Production::new(iter, vec![]);
        assert!(
            result.is_err(),
            "Creation of production rule should return an error"
        );
        let e = result.unwrap_err();
        assert_eq!(
            e,
            ProductionError::NoRhs,
            "Creation of production rule returned the wrong error"
        );
    }

    #[test]
    pub fn new_from_string() {
        let p_check = Production {
            lhs: vec![symbol("S")],
            rhs: vec![symbol("A"), symbol("B")],
        };

        assert_eq!(
            Production::new_from_string(vec!["S"], vec!["A", "B"]).unwrap(),
            p_check,
            "Created production rule is not the one expected"
        );
    }

    #[test]
    pub fn new_from_string_error_lhs() {
        let error = SymbolError::InvalidSymbol("\n".to_string());
        let result = Production::new_from_string(vec!["\n"], vec!["A", "B"]);

        assert!(
            result.is_err(),
            "Created production rule should return error"
        );
        let e = result.unwrap_err();
        assert_eq!(
            e,
            ProductionError::SymbolError(error),
            "Creation of production rule returned the wrong error"
        );
    }

    #[test]
    pub fn new_from_string_error_rhs() {
        let error = SymbolError::InvalidSymbol("\n".to_string());
        let result = Production::new_from_string(vec!["S"], vec!["\n"]);

        assert!(
            result.is_err(),
            "Created production rule should return error"
        );
        let e = result.unwrap_err();
        assert_eq!(
            e,
            ProductionError::SymbolError(error),
            "Creation of production rule returned the wrong error"
        );
    }

    #[test]
    pub fn production() {
        let p_check = Production {
            lhs: vec![symbol("S")],
            rhs: vec![symbol("A"), symbol("B")],
        };

        assert_eq!(
            super::production("S", "A B"),
            p_check,
            "Created production rule is not the one expected"
        );
    }

    #[test]
    pub fn productions() {
        let p_check = vec![
            Production {
                lhs: vec![symbol("S")],
                rhs: vec![symbol("A"), symbol("B")],
            },
            Production {
                lhs: vec![symbol("A")],
                rhs: vec![symbol("a")],
            },
        ];

        assert_eq!(
            super::productions("S -> A B\nA -> a"),
            p_check,
            "Created production rules are not those expected"
        );
    }

    #[test]
    fn production_error_display_no_lhs() {
        let mut buf = String::new();

        let result = write!(buf, "{}", ProductionError::NoLhs);
        assert!(result.is_ok());
        assert_eq!(buf, "ProductionError: no lhs in production")
    }

    #[test]
    fn production_error_display_no_rhs() {
        let mut buf = String::new();

        let result = write!(buf, "{}", ProductionError::NoRhs);
        assert!(result.is_ok());
        assert_eq!(buf, "ProductionError: no rhs in production")
    }

    #[test]
    fn production_error_display_symbol_error() {
        let mut buf = String::new();
        let error = SymbolError::EmptySymbol;

        let result = write!(buf, "{}", ProductionError::SymbolError(error.clone()));
        assert!(result.is_ok());
        assert_eq!(
            buf,
            format!("ProductionError: symbol error encountered = {}", error)
        )
    }

    #[test]
    fn production_error_display_format_error() {
        let mut buf = String::new();
        let error = TokenizerError::ProductionNoLhs;

        let result = write!(buf, "{}", ProductionError::FormatError(error.clone()));
        assert!(result.is_ok());
        assert_eq!(
            buf,
            format!(
                "ProductionError: bad formatted string encountered, error = {}",
                error
            )
        )
    }

    #[test]
    fn production_display() {
        let mut buf = String::new();
        let p = super::production("A", "B C");

        let result = write!(buf, "{}", p);
        assert!(result.is_ok());
        assert_eq!(buf, "A -> B C")
    }
}
