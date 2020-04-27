use crate::parser;
use crate::production::{Production};
use crate::symbol::Symbol;
use std::collections::HashSet;

#[derive(Debug, PartialEq, Clone)]
pub struct Grammar {
    pub n: HashSet<Symbol>,
    pub t: HashSet<Symbol>,
    pub p: Vec<Production>,
    pub s: Symbol,
}

impl Grammar {
    pub fn new<S, P>(n: S, t: S, p: P, s: Symbol) -> Grammar
    where
        S: IntoIterator<Item = Symbol>,
        P: IntoIterator<Item = Production>,
    {
        let mut n: HashSet<Symbol> = n.into_iter().collect();
        let t: HashSet<Symbol> = t.into_iter().collect();
        let p: Vec<Production> = p.into_iter().collect();

        n.insert(s.clone());

        if !n.iter().all(|s: &Symbol| s.is_non_terminal()) {
            panic!("Non terminal symbols in grammar should all be valid non terminals")
        }

        if !t.iter().all(|s: &Symbol| s.is_terminal()) {
            panic!("Terminal symbols in grammar should all be valid terminals")
        }

        Grammar {
            n: n,
            t: t,
            p: p,
            s: s,
        }
    }

    pub fn new_from_string<'a, I>(n: I, t: I, p: I, s: &str) -> Grammar
    where
        I: IntoIterator<Item = &'a str>,
    {
        let n: HashSet<Symbol> = n.into_iter().map(|s| Symbol::new(s).unwrap()).collect();
        let t: HashSet<Symbol> = t.into_iter().map(|s| Symbol::new(s).unwrap()).collect();
        let p: Vec<Production> = Production::from_iter(p);
        let s: Symbol = Symbol::new(s).unwrap();

        Grammar::new(n, t, p, s)
    }

    pub fn from_string(string: &str) -> Grammar {
        parser::grammar_from_string(string).unwrap()
    }

    pub fn alternatives(&self, symbols: &Vec<Symbol>) -> Vec<Vec<Symbol>> {
        let mut alternatives: Vec<Vec<Symbol>> = Vec::new();
        for p in &self.p {
            if &p.lhs == symbols {
                alternatives.push(p.rhs.clone())
            }
        }

        alternatives
    }

    pub fn restrict_to<I>(&self, symbols: &I) -> Grammar
    where
        I: IntoIterator<Item = Symbol> + Clone,
    {
        let symbols: HashSet<Symbol> = symbols.clone().into_iter().collect();
        let n: HashSet<Symbol> = symbols.intersection(&self.n).cloned().collect();
        let t: HashSet<Symbol> = symbols.intersection(&self.t).cloned().collect();

        if !symbols.contains(&self.s) {
            panic!("Restricting the grammar lead to a grammar without start symbol");
        }

        let p: Vec<Production> = self
            .p
            .iter()
            .filter(|p: &&Production| p.symbols().difference(&symbols).count() == 0)
            .cloned()
            .collect();

        Grammar {
            n: n,
            t: t,
            p: p,
            s: self.s.clone(),
        }
    }

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

    pub fn reachable(&self) -> HashSet<Symbol> {
        let from: HashSet<Symbol> = vec![self.s.clone()].into_iter().collect();
        self.reachable_from(from)
    }

    pub fn reachable_from(&self, reached: HashSet<Symbol>) -> HashSet<Symbol> {
        let mut reached_next = reached.clone();
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

pub fn grammar(string: &str) -> Grammar {
    Grammar::from_string(string)
}

pub fn grammar_iter<'a, I>(n: I, t: I, p: I, s: &str) -> Grammar
where
    I: IntoIterator<Item = &'a str>,
{
    Grammar::new_from_string(n, t, p, s)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::symbol;

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

    #[test]
    pub fn alternatives() {
        let g = Grammar::from_string("S -> A B\nA -> a | B\nB -> b");
        let a_check = vec![
            vec![Symbol::new("a").unwrap()],
            vec![Symbol::new("B").unwrap()],
        ];

        assert_eq!(
            g.alternatives(&vec![Symbol::new("A").unwrap()]),
            a_check,
            "Alternatives are not the one expected"
        );
    }

    #[test]
    pub fn alternatives_empty() {
        let g = Grammar::from_string("S -> A B\nA -> a | B\nB -> b");

        assert!(
            g.alternatives(&vec![Symbol::new("a").unwrap()]).is_empty(),
            "Alternatives are not empty when they should"
        );
    }

    #[test]
    pub fn restrict_to() {
        let g_restricted = Grammar::from_string("S -> A\nA -> a | B\nB -> b").restrict_to(&vec![
            Symbol::new("S").unwrap(),
            Symbol::new("A").unwrap(),
            Symbol::new("a").unwrap(),
        ]);

        let s_check: Symbol = Symbol::new("S").unwrap();
        let n_check: HashSet<Symbol> = vec![Symbol::new("S").unwrap(), Symbol::new("A").unwrap()]
            .into_iter()
            .collect();
        let t_check: HashSet<Symbol> = vec![Symbol::new("a").unwrap()].into_iter().collect();
        let p_check: Vec<Production> = vec![
            Production {
                lhs: vec![Symbol::new("S").unwrap()],
                rhs: vec![Symbol::new("A").unwrap()],
            },
            Production {
                lhs: vec![Symbol::new("A").unwrap()],
                rhs: vec![Symbol::new("a").unwrap()],
            },
        ];

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
    #[should_panic]
    pub fn restrict_to_panic_start_symbol() {
        Grammar::from_string("S -> A\nA -> a | B\nB -> b")
            .restrict_to(&vec![Symbol::new("A").unwrap(), Symbol::new("a").unwrap()]);
    }

    #[test]
    pub fn new() {
        let s_check: Symbol = Symbol::new("S").unwrap();
        let n_check: HashSet<Symbol> = vec![Symbol::new("S").unwrap(), Symbol::new("A").unwrap()]
            .into_iter()
            .collect();
        let t_check: HashSet<Symbol> = vec![Symbol::new("a").unwrap()].into_iter().collect();
        let p_check: Vec<Production> = vec![
            Production {
                lhs: vec![Symbol::new("S").unwrap()],
                rhs: vec![Symbol::new("A").unwrap()],
            },
            Production {
                lhs: vec![Symbol::new("A").unwrap()],
                rhs: vec![Symbol::new("a").unwrap()],
            },
        ];
        let g = Grammar::new(
            n_check.clone(),
            t_check.clone(),
            p_check.clone(),
            s_check.clone(),
        );

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
        let s_check: Symbol = Symbol::new("S").unwrap();
        let n_check: HashSet<Symbol> = vec![Symbol::new("S").unwrap(), Symbol::new("A").unwrap()]
            .into_iter()
            .collect();
        let t_check: HashSet<Symbol> = vec![Symbol::new("a").unwrap()].into_iter().collect();
        let p_check: Vec<Production> = vec![
            Production {
                lhs: vec![Symbol::new("S").unwrap()],
                rhs: vec![Symbol::new("A").unwrap()],
            },
            Production {
                lhs: vec![Symbol::new("A").unwrap()],
                rhs: vec![Symbol::new("a").unwrap()],
            },
        ];
        let g = Grammar::new_from_string(vec!["S", "A"], vec!["a"], vec!["S -> A\nA -> a"], "S");

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
        let s_check: Symbol = Symbol::new("S").unwrap();
        let n_check: HashSet<Symbol> = vec![Symbol::new("S").unwrap(), Symbol::new("A").unwrap()]
            .into_iter()
            .collect();
        let t_check: HashSet<Symbol> = vec![Symbol::new("a").unwrap()].into_iter().collect();
        let p_check: Vec<Production> = vec![
            Production {
                lhs: vec![Symbol::new("S").unwrap()],
                rhs: vec![Symbol::new("A").unwrap()],
            },
            Production {
                lhs: vec![Symbol::new("A").unwrap()],
                rhs: vec![Symbol::new("a").unwrap()],
            },
        ];
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
