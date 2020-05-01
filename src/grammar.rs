use crate::production::{Production, ProductionError};
use crate::symbol::{Symbol, SymbolError};
use itertools::Itertools;
use std::collections::HashSet;
use std::error::Error;
use std::fmt;

#[derive(Debug, PartialEq)]
pub enum GrammarError {
    WrongNonTerminals,
    WrongTerminals,
    WrongStartSymbol(Symbol),
    SymbolError(SymbolError),
    ProductionError(ProductionError),
    NoStartSymbol(Option<String>),
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

#[derive(Debug, PartialEq, Clone)]
pub struct Grammar {
    n: HashSet<Symbol>,
    t: HashSet<Symbol>,
    p: Vec<Production>,
    s: Symbol,
}

impl Grammar {
    pub fn n(&self) -> HashSet<Symbol> {
        self.n.clone()
    }

    pub fn t(&self) -> HashSet<Symbol> {
        self.t.clone()
    }

    pub fn p(&self) -> Vec<Production> {
        self.p.clone()
    }

    pub fn s(&self) -> Symbol {
        self.s.clone()
    }

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

    pub fn alternatives(&self, symbols: &Vec<Symbol>) -> Vec<Vec<Symbol>> {
        let mut alternatives: Vec<Vec<Symbol>> = Vec::new();
        for p in &self.p {
            if &p.lhs() == symbols {
                alternatives.push(p.rhs())
            }
        }

        alternatives
    }

    pub fn restrict_to<I>(&self, symbols: &I) -> Result<Grammar, GrammarError>
    where
        I: IntoIterator<Item = Symbol> + Clone,
    {
        let symbols: HashSet<Symbol> = symbols.clone().into_iter().collect();
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
    Grammar::from_string(string).unwrap()
}

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
            g.alternatives(&vec![symbol("A")]),
            a_check,
            "Alternatives are not the one expected"
        );
    }

    #[test]
    pub fn alternatives_empty() {
        let g = Grammar::from_string("S -> A B\nA -> a | B\nB -> b").unwrap();

        assert!(
            g.alternatives(&vec![symbol("a")]).is_empty(),
            "Alternatives are not empty when they should"
        );
    }

    #[test]
    pub fn restrict_to() {
        let g_restricted = Grammar::from_string("S -> A\nA -> a | B\nB -> b")
            .unwrap()
            .restrict_to(&vec![symbol("S"), symbol("A"), symbol("a")])
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
            .restrict_to(&vec![symbol("A"), symbol("a")]) {
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
