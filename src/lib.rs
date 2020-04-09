use std::collections::HashSet;

const PRODUCTION_SEP: &str = "->";
const PRODUCTION_OR: &str = "|";

#[cfg(test)]
mod tests {
    use crate::{Derivation, Grammar, Production};
    use std::collections::HashSet;

    #[test]
    fn grammar_from_string() {
        let g = Grammar::from_string("A -> a b\nB -> C | .");

        let mut t: HashSet<String> = HashSet::new();
        t.insert("a".to_string());
        t.insert("b".to_string());
        t.insert(".".to_string());
        let mut n: HashSet<String> = HashSet::new();
        n.insert("A".to_string());
        n.insert("B".to_string());
        n.insert("C".to_string());
        let p: Vec<Production> = vec![
            Production {
                lhs: "A".to_string(),
                rhs: "a b".to_string(),
            },
            Production {
                lhs: "B".to_string(),
                rhs: "C".to_string(),
            },
            Production {
                lhs: "B".to_string(),
                rhs: ".".to_string(),
            },
        ];

        assert_eq!(g.t, t);
        assert_eq!(g.n, n);
        assert_eq!(g.s, "A".to_string());
        assert!(g.p.len() == p.len());
        assert!(g.p.iter().zip(p).all(|(a, b)| *a == b));
    }

    #[test]
    fn production_from_string() {
        let p = Production::from_string("a -> a b\nB -> C | .");
        let p_check: Vec<Production> = vec![
            Production {
                lhs: "a".to_string(),
                rhs: "a b".to_string(),
            },
            Production {
                lhs: "B".to_string(),
                rhs: "C".to_string(),
            },
            Production {
                lhs: "B".to_string(),
                rhs: ".".to_string(),
            },
        ];

        assert!(
            p.len() == p_check.len(),
            "Created production rules length not as expected length"
        );
        assert!(
            p.iter().zip(p_check).all(|(a, b)| *a == b),
            "Created production rules not as expected rules"
        );
    }

    #[test]
    fn grammar_alternatives() {
        let mut a = Grammar::from_string("A -> a C\nB -> C | .\nA -> C").alternatives("A");
        a.sort();
        let a_check: Vec<String> = vec!["C".to_string(), "a".to_string()];

        println!("{:?}", a);

        assert!(
            a.len() == a_check.len(),
            "Grammar alternatives length not as expected length"
        );
        assert!(
            a.iter().zip(a_check).all(|(a, b)| *a == b),
            "Grammar alternatives not as expected alternatives"
        );
    }

    #[test]
    fn grammar_restrict_to() {
        let mut symbols = HashSet::new();
        symbols.insert("A".to_string());
        symbols.insert("a".to_string());
        symbols.insert("b".to_string());
        let g = Grammar::from_string("A -> a b\nB -> C | .").restrict_to(&symbols);

        let mut t: HashSet<String> = HashSet::new();
        t.insert("a".to_string());
        t.insert("b".to_string());
        let mut n: HashSet<String> = HashSet::new();
        n.insert("A".to_string());
        let p: Vec<Production> = vec![Production {
            lhs: "A".to_string(),
            rhs: "a b".to_string(),
        }];

        assert_eq!(g.t, t);
        assert_eq!(g.n, n);
        assert_eq!(g.s, "A".to_string());
        assert!(g.p.len() == p.len());
        assert!(g.p.iter().zip(p).all(|(a, b)| *a == b));
    }

    #[test]
    fn grammar_to_production_table() {
        Grammar::from_string("A -> a b\nB -> C | .").production_table();
    }

    #[test]
    fn derivation() {
        let g1 = Grammar::from_string("A -> a b\nB -> C | .");
        let g2 = Grammar::from_string("A -> a b\nB -> C | .");
        let d = Derivation::new(g1);

        assert_eq!(g2, d.g);
    }

    #[test]
    fn derivation_steps() {
        let g = Grammar::from_string("A -> a B\nB -> C | .");
        let d = Derivation::new(g).step(0, 0).step(1, 1);
        let steps: Vec<(usize, usize)> = vec![(0, 0), (1, 1)];

        assert!(d.steps.len() == steps.len());
        assert!(d.steps.iter().zip(steps).all(|(a, b)| *a == b));
    }
}

#[derive(Debug, PartialEq)]
pub struct Grammar {
    pub s: String,
    pub t: HashSet<String>,
    pub n: HashSet<String>,
    pub p: Vec<Production>,
}

impl Grammar {
    pub fn from_string(string: &str) -> Grammar {
        let string = string.trim();

        if string.is_empty() {
            panic!("Empty string passed as parameter for the grammar creation");
        }

        let mut s: String = String::new();

        // parse start symbol
        let mut start_symbol_iter = string.split_whitespace();
        if let (Some(symbol), Some(PRODUCTION_SEP)) =
            (start_symbol_iter.next(), start_symbol_iter.next())
        {
            if let Some(first_char) = symbol.chars().next() {
                if first_char.is_ascii_uppercase() {
                    s = symbol.to_string();
                }
            }
            if s.is_empty() {
                panic!("First symbol of first production rule should be capitalized since it's the start symbol");
            }
        } else {
            panic!(
                "Expected start symbol as the only and first symbol of the first production rule of the form A {} ...)",
                PRODUCTION_SEP
            );
        }

        let p: Vec<Production> = Production::from_string(string);

        let mut t: HashSet<String> = HashSet::new();
        let mut n: HashSet<String> = HashSet::new();

        for rule in &p {
            // parse symbols
            for symbol in rule.symbols() {
                if let Some(first_char) = symbol.chars().next() {
                    if first_char.is_ascii_uppercase() {
                        n.insert(symbol.to_string());
                    } else {
                        t.insert(symbol.to_string());
                    }
                }
            }
        }

        Grammar {
            s: s,
            t: t,
            n: n,
            p: p,
        }
    }

    pub fn alternatives(&self, string: &str) -> Vec<String> {
        let mut alternatives: HashSet<String> = HashSet::new();

        for rule in self.p.iter() {
            if rule.lhs == string {
                for rhs in rule.rhs.split_whitespace() {
                    alternatives.insert(rhs.to_string());
                }
            }
        }

        alternatives.into_iter().collect()
    }

    pub fn restrict_to(&self, symbols: &HashSet<String>) -> Grammar {
        // restrict start symbol if needed
        let s: String;
        if symbols.contains(&self.s) {
            s = String::from(&self.s)
        } else {
            panic!("Can't restrict a grammar to not have a start symbol")
        }

        // restrict terminals and non terminals if needed
        let mut t: HashSet<String> = HashSet::new();
        let mut n: HashSet<String> = HashSet::new();
        for symbol in self.t.intersection(symbols) {
            t.insert(symbol.clone());
        }
        for symbol in self.n.intersection(symbols) {
            n.insert(symbol.clone());
        }

        // restrict productions if needed
        let mut p: Vec<Production> = Vec::new();
        for rule in &self.p {
            if !rule.symbols().eq(symbols) {
                continue;
            }

            p.push(Production {
                lhs: rule.lhs.clone(),
                rhs: rule.rhs.clone(),
            });
        }

        Grammar {
            s: s,
            t: t,
            n: n,
            p: p,
        }
    }

    pub fn production_table(&self) -> () {
        let mut count = 0;
        for rule in &self.p {
            count += 1;
            println!("({}) {} -> {}", count, rule.lhs, rule.rhs);
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Production {
    pub lhs: String,
    pub rhs: String,
}

impl Production {
    pub fn from_string(string: &str) -> Vec<Production> {
        let mut p: Vec<Production> = Vec::new();

        for rule in string.trim().lines() {
            // parse rules
            let mut rule_sides = rule.trim().split_terminator(PRODUCTION_SEP);
            match (rule_sides.next(), rule_sides.next()) {
                (Some(lhs), Some(rhs)) => {
                    let lhs = lhs.trim();
                    for rhs in rhs.trim().split_terminator(PRODUCTION_OR) {
                        p.push(Production {
                            lhs: String::from(lhs),
                            rhs: String::from(rhs.trim()),
                        })
                    }
                }
                (Some(lhs), None) => panic!(
                    "Expected right hand side of production rule {} {} ...",
                    lhs, PRODUCTION_SEP
                ),
                (None, _) => panic!(
                    "Expected left hand side for production rules (form A {} B)",
                    PRODUCTION_SEP
                ),
            }
        }

        p
    }

    fn symbols(&self) -> HashSet<String> {
        let mut symbols: HashSet<String> = HashSet::new();

        for symbol in self.lhs.split_whitespace() {
            symbols.insert(symbol.to_string());
        }

        for symbol in self.rhs.split_whitespace() {
            symbols.insert(symbol.to_string());
        }

        symbols
    }
}

pub struct Derivation {
    g: Grammar,
    steps: Vec<(usize, usize)>,
}

impl Derivation {
    pub fn new(g: Grammar) -> Derivation {
        Derivation {
            g: g,
            steps: Vec::new(),
        }
    }

    pub fn step(mut self, p_index: usize, index: usize) -> Derivation {
        self.steps.push((p_index, index));

        self
    }
}
