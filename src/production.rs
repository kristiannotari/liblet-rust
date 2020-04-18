use crate::parser;
use crate::symbol::Symbol;
use std::collections::HashSet;

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
