use crate::parser;
use crate::symbol::Symbol;
use std::collections::HashSet;

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

#[derive(Debug, PartialEq, Clone)]
pub struct Production {
    pub lhs: Vec<Symbol>,
    pub rhs: Vec<Symbol>,
}

impl Production {
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

    pub fn from_string(string: &str) -> Vec<Production> {
        parser::productions_from_string(string).unwrap()
    }

    pub fn such_that(predicate: ProductionPredicate) -> Box<dyn FnMut(&&Production) -> bool> {
        Box::new(move |p| predicate.test(&p))
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    pub fn from_string() {
        let p_check = vec![
            Production {
                lhs: vec![Symbol::new("S").unwrap()],
                rhs: vec![Symbol::new("A").unwrap(), Symbol::new("B").unwrap()],
            },
            Production {
                lhs: vec![Symbol::new("A").unwrap()],
                rhs: vec![Symbol::new("a").unwrap()],
            },
            Production {
                lhs: vec![Symbol::new("A").unwrap()],
                rhs: vec![Symbol::new("B").unwrap()],
            },
            Production {
                lhs: vec![Symbol::new("B").unwrap()],
                rhs: vec![Symbol::new("b").unwrap()],
            },
        ];

        assert_eq!(
            Production::from_string("S -> A B\nA -> a | B\nB -> b"),
            p_check,
            "Parsed production rules are not those expected"
        );
    }

    #[test]
    #[should_panic]
    pub fn from_string_panic() {
        Production::from_string("S ->\n -> a | B\nB -> b");
    }

    #[test]
    pub fn predicate_lhs_equals() {
        let predicate = ProductionPredicate::LhsEquals(vec![Symbol::new("T").unwrap()]);

        assert!(
            predicate.test(&Production {
                lhs: vec![Symbol::new("T").unwrap()],
                rhs: vec![]
            }),
            "Predicate should return true"
        );
        assert!(
            !predicate.test(&Production {
                lhs: vec![Symbol::new("F").unwrap()],
                rhs: vec![]
            }),
            "Predicate should return false"
        );
    }

    #[test]
    pub fn predicate_rhs_equals() {
        let predicate = ProductionPredicate::RhsEquals(vec![Symbol::new("T").unwrap()]);

        assert!(
            predicate.test(&Production {
                lhs: vec![],
                rhs: vec![Symbol::new("T").unwrap()]
            }),
            "Predicate should return true"
        );
        assert!(
            !predicate.test(&Production {
                lhs: vec![],
                rhs: vec![Symbol::new("F").unwrap()]
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
                rhs: vec![Symbol::new("T1").unwrap(), Symbol::new("T2").unwrap()]
            }),
            "Predicate should return true"
        );
        assert!(
            !predicate.test(&Production {
                lhs: vec![],
                rhs: vec![Symbol::new("F").unwrap()]
            }),
            "Predicate should return false"
        );
    }

    #[test]
    pub fn predicate_rhs_is_suffix_of() {
        let predicate = ProductionPredicate::RhsIsSuffixOf(vec![
            Symbol::new("T2").unwrap(),
            Symbol::new("T3").unwrap(),
        ]);

        assert!(
            predicate.test(&Production {
                lhs: vec![],
                rhs: vec![
                    Symbol::new("T1").unwrap(),
                    Symbol::new("T2").unwrap(),
                    Symbol::new("T3").unwrap()
                ]
            }),
            "Predicate should return true"
        );
        assert!(
            !predicate.test(&Production {
                lhs: vec![],
                rhs: vec![Symbol::new("F").unwrap()]
            }),
            "Predicate should return false"
        );
    }

    #[test]
    pub fn such_that() {
        let filter = Production::such_that(ProductionPredicate::LhsEquals(vec![
            Symbol::new("T").unwrap()
        ]));
        let productions = Production::from_string("S -> A | B\nA -> a\nT -> t\nB -> B");

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
}
