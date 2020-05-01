use crate::symbol::{Symbol, SymbolError};
use crate::tokenizer;
use crate::tokenizer::TokenizerError;
use itertools::Itertools;
use std::collections::HashSet;
use std::error::Error;
use std::fmt;

#[derive(Debug, PartialEq)]
pub enum ProductionError {
    NoLhs,
    NoRhs,
    SymbolError(SymbolError),
    TokenizerError(TokenizerError),
}

impl fmt::Display for ProductionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProductionError::NoLhs => write!(f, "ProductionError: no lhs in production"),
            ProductionError::NoRhs => write!(f, "ProductionError: no rhs in production"),
            ProductionError::SymbolError(e) => {
                write!(f, "ProductionError: symbol error encountered = {}", e)
            }
            ProductionError::TokenizerError(e) => {
                write!(f, "ProductionError: tokenizer error encountered = {}", e)
            }
        }
    }
}

impl Error for ProductionError {}

impl std::convert::From<TokenizerError> for ProductionError {
    fn from(e: TokenizerError) -> Self {
        ProductionError::TokenizerError(e)
    }
}

pub enum ProductionPredicate {
    LhsEquals(Vec<Symbol>),
    RhsEquals(Vec<Symbol>),
    RhsLengthEquals(usize),
    RhsIsSuffixOf(Vec<Symbol>),
}

impl ProductionPredicate {
    fn test(&self, p: &Production) -> bool {
        match self {
            ProductionPredicate::LhsEquals(symbols) => p.lhs() == *symbols,
            ProductionPredicate::RhsEquals(symbols) => p.rhs() == *symbols,
            ProductionPredicate::RhsLengthEquals(length) => p.rhs().len() == *length,
            ProductionPredicate::RhsIsSuffixOf(symbols) => p.rhs().ends_with(&symbols),
        }
    }
}

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

    pub fn lhs(&self) -> Vec<Symbol> {
        self.lhs.clone()
    }

    pub fn rhs(&self) -> Vec<Symbol> {
        self.rhs.clone()
    }

    pub fn symbols(&self) -> HashSet<Symbol> {
        let mut symbols: Vec<Symbol> = self.lhs();
        symbols.append(&mut self.rhs());
        symbols.into_iter().collect()
    }

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

    pub fn such_that(predicate: ProductionPredicate) -> Box<dyn FnMut(&&Production) -> bool> {
        Box::new(move |p| predicate.test(&p))
    }
}

pub fn production(lhs: &str, rhs: &str) -> Production {
    Production::new(
        Symbol::symbols_from_string(lhs).unwrap(),
        Symbol::symbols_from_string(rhs).unwrap(),
    )
    .unwrap()
}

pub fn productions(string: &str) -> Vec<Production> {
    Production::from_string(string).unwrap()
}

pub fn productions_iter<'a, I>(strings: I) -> Vec<Production>
where
    I: IntoIterator<Item = &'a str>,
{
    Production::from_iter(strings).unwrap()
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::symbol::symbol;

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
        match Production::from_string("S ->\n -> a | B\nB -> b") {
            Ok(_) => panic!("production from string should return error"),
            Err(e) => match e {
                ProductionError::TokenizerError(_) => (),
                e => panic!(
                    "Creation of productions from test input should return a TokenizerError but returned Err \"{}\" instead",
                    e
                ),
            }
        }
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
            super::productions_iter(vec!["S -> A B", "A -> a", "B -> a | b"]),
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
    pub fn productions_iter() {
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
            super::productions_iter(vec!["S -> A B", "A -> a", "B -> a | b"]),
            p_check,
            "Created production rules are not those expected"
        );
    }
}
