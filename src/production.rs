use crate::parser;
use crate::symbol::Symbol;
use std::collections::HashSet;

#[derive(Debug, PartialEq)]
pub struct Production {
    pub lhs: Vec<Symbol>,
    pub rhs: Vec<Symbol>,
}

impl Production {
    pub fn new<I>(lhs: I, rhs: I) -> Production
    where
        I: IntoIterator<Item = Symbol>,
    {
        Production {
            lhs: lhs.into_iter().collect(),
            rhs: rhs.into_iter().collect(),
        }
    }

    pub fn new_from_string<'a, I>(lhs: I, rhs: I) -> Production
    where
        I: IntoIterator<Item = &'a str>,
    {
        Production::new(
            lhs.into_iter()
                .map(|s| Symbol::new(s).unwrap())
                .collect::<Vec<Symbol>>(),
            rhs.into_iter()
                .map(|s| Symbol::new(s).unwrap())
                .collect::<Vec<Symbol>>(),
        )
    }

    pub fn lhs(&self) -> HashSet<Symbol> {
        self.lhs.clone().into_iter().collect()
    }

    pub fn rhs(&self) -> HashSet<Symbol> {
        self.rhs.clone().into_iter().collect()
    }

    pub fn symbols(&self) -> HashSet<Symbol> {
        self.lhs().union(&self.rhs()).map(|x| x.clone()).collect()
    }

    pub fn from_string(string: &str) -> Vec<Production> {
        parser::productions_from_string(string).unwrap()
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
}
