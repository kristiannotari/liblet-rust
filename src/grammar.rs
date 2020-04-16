use crate::parser;
use crate::production::Production;
use crate::symbol::Symbol;
use std::collections::HashSet;

#[derive(Debug, PartialEq)]
pub struct Grammar {
    pub s: Symbol,
    pub t: HashSet<Symbol>,
    pub n: HashSet<Symbol>,
    pub p: Vec<Production>,
}

impl Grammar {
    pub fn from_string(string: &str) -> Grammar {
        parser::grammar_from_string(string).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn from_string() {
        let s_check: Symbol = Symbol::new("S").unwrap();
        let n_check: HashSet<Symbol> = vec![
            Symbol::new("S").unwrap(),
            Symbol::new("A").unwrap(),
            Symbol::new("B").unwrap(),
        ]
        .into_iter()
        .collect();
        let t_check: HashSet<Symbol> = vec![Symbol::new("a").unwrap(), Symbol::new("b").unwrap()]
            .into_iter()
            .collect();
        let p_check: Vec<Production> = vec![
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

        let g = Grammar::from_string("S -> A B\nA -> a | B\nB -> b");
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
    #[should_panic]
    pub fn from_string_panic() {
        Grammar::from_string("S ->\n -> a | B\nB -> b");
    }
}
