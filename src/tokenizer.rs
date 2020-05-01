use crate::grammar::Grammar;
use crate::production::Production;
use crate::symbol::Symbol;
use std::collections::HashSet;
use std::error::Error;
use std::fmt;

const PRODUCTION_SEP: &str = "->";
const PRODUCTION_OR: &str = "|";
const PRODUCTION_SPACE: &str = " ";

#[derive(Debug, PartialEq)]
pub enum TokenizerError {
    NoProductions,
    ProductionNoLhs,
    ProductionNoRhs(String),
    ProductionMultipleOneLine(usize),
    ProductionsNoStartSymbol,
    ProductionsTooManyStartSymbols(String),
    NoSymbols,
    InvalidSymbol(String),
}

impl fmt::Display for TokenizerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenizerError::NoProductions => write!(f, "TokenizerError: No productions found in input"),
            TokenizerError::ProductionNoLhs => write!(
                f,
                "TokenizerError: Expected left hand side for production rules (form A {} B)",
                PRODUCTION_SEP
            ),
            TokenizerError::ProductionNoRhs(lhs) => write!(
                f,
                "TokenizerError: Expected right hand side of production rule {} {} ...",
                lhs, PRODUCTION_SEP
            ),
            TokenizerError::ProductionMultipleOneLine(index) => write!(
                f,
                "TokenizerError: Too many production rule on the same line on line {}",
                index
            ),
            TokenizerError::ProductionsNoStartSymbol => write!(
                f,
                "TokenizerError: No start symbol found in production rules. It must start with a capital letter",
            ),
            TokenizerError::ProductionsTooManyStartSymbols(lhs) => write!(
                f,
                "TokenizerError: Too many start symbols found in left hand side \"{}\" of production rule",
                lhs
            ),
            TokenizerError::NoSymbols => write!(
                f,
                "TokenizerError: No symbols found in input",
            ),
            TokenizerError::InvalidSymbol(symbol) => write!(
                f,
                "TokenizerError: Invalid symbol \"{}\" encountered tokenizing productions",
                symbol
            ),
        }
    }
}

impl Error for TokenizerError {}

pub fn grammar_from_string(string: &str) -> Result<Grammar, TokenizerError> {
    let p: Vec<Production> = productions_from_string(string)?;
    let mut s: Option<Symbol> = None;

    if let Some(p_first) = p.first() {
        if p_first.lhs.len() > 1 {
            return Err(TokenizerError::ProductionsTooManyStartSymbols(
                p_first
                    .lhs
                    .clone()
                    .into_iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<String>>()
                    .join(PRODUCTION_SPACE),
            ));
        }

        if let Some(symbol) = p_first.lhs.first() {
            if symbol.is_non_terminal() {
                s = Some(symbol.clone());
            }
        }
    }

    let mut t: HashSet<Symbol> = HashSet::new();
    let mut n: HashSet<Symbol> = HashSet::new();

    for rule in &p {
        let (t_temp, n_temp): (HashSet<Symbol>, HashSet<Symbol>) = rule
            .symbols()
            .iter()
            .map(|s| s.clone())
            .partition(|s| s.is_terminal());

        t.extend(t_temp);
        n.extend(n_temp);
    }

    if let Some(s) = s {
        Ok(Grammar {
            n: n,
            t: t,
            p: p,
            s: s,
        })
    } else {
        Err(TokenizerError::ProductionsNoStartSymbol)
    }
}

pub fn productions_from_string(string: &str) -> Result<Vec<Production>, TokenizerError> {
    let mut p: Vec<Production> = Vec::new();
    for (i, rule) in string.trim().lines().enumerate() {
        let mut sides = rule.split_terminator(PRODUCTION_SEP);
        match (sides.next(), sides.next(), sides.next()) {
            (Some(lhs), Some(rhs), None) => {
                let lhs = lhs.trim();
                if lhs.is_empty() {
                    return Err(TokenizerError::ProductionNoLhs);
                }
                for rhs in rhs.split(PRODUCTION_OR) {
                    let rhs = rhs.trim();
                    if rhs.is_empty() {
                        return Err(TokenizerError::ProductionNoRhs(lhs.to_string()));
                    }
                    p.push(Production {
                        lhs: symbols_from_string(lhs)?,
                        rhs: symbols_from_string(rhs)?,
                    })
                }
            }
            (Some(_), Some(_), Some(_)) => {
                return Err(TokenizerError::ProductionMultipleOneLine(i))
            }
            (Some(lhs), None, _) => {
                return Err(TokenizerError::ProductionNoRhs(lhs.trim().to_string()))
            }
            (None, _, _) => return Err(TokenizerError::ProductionNoLhs),
        }
    }

    if p.is_empty() {
        return Err(TokenizerError::NoProductions);
    }

    Ok(p)
}

pub fn symbols_from_string(string: &str) -> Result<Vec<Symbol>, TokenizerError> {
    let mut symbols: Vec<Symbol> = Vec::new();
    for s in string.split_whitespace() {
        if let Ok(symbol) = Symbol::new(s) {
            symbols.push(symbol)
        } else {
            return Err(TokenizerError::InvalidSymbol(s.to_string()));
        }
    }

    if symbols.is_empty() {
        return Err(TokenizerError::NoSymbols);
    }

    Ok(symbols)
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn productions_from_string() {
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

        match super::productions_from_string("S -> A B\nA -> a | B\nB -> b") {
            Ok(p) => assert_eq!(
                p, p_check,
                "Tokenized production rules are not those expected"
            ),
            Err(e) => panic!("Error tokenizing productions from string: {}", e),
        }
    }

    #[test]
    fn productions_from_string_empty() {
        match super::productions_from_string("") {
            Ok(_) => panic!("Productions from test input should return an Err result"),
            Err(e) => match e {
                TokenizerError::NoProductions => (),
                e => panic!(
                    "Productions from test input should return Err \"{}\" but returned Err \"{}\" instead",
                    TokenizerError::NoProductions,
                    e
                ),
            },
        }
    }

    #[test]
    fn productions_from_string_no_lhs() {
        match super::productions_from_string("-> B") {
            Ok(a) => {println!("ret: {:?}", a); panic!("Productions from test input should return an Err result")},
            Err(e) => match e {
                TokenizerError::ProductionNoLhs => (),
                e => panic!(
                    "Productions from test input should return Err \"{}\" but returned Err \"{}\" instead",
                    TokenizerError::NoProductions,
                    e
                ),
            },
        }
    }

    #[test]
    fn productions_from_string_no_rhs() {
        let lhs = "A";
        match super::productions_from_string(format!("{} -> ", lhs).as_str()) {
            Ok(_) => panic!("Productions from test input should return an Err result"),
            Err(e) => match e {
                TokenizerError::ProductionNoRhs(_) => (),
                e => panic!(
                    "Productions from  should return Err \"{}\" but returned Err \"{}\" instead",
                    TokenizerError::ProductionNoRhs(lhs.to_string()),
                    e
                ),
            },
        }
    }

    #[test]
    fn productions_from_string_no_production_sep() {
        let lhs = "abc test d";
        match super::productions_from_string(lhs) {
            Ok(_) => panic!("Productions from test input should return an Err result"),
            Err(e) => match e {
                TokenizerError::ProductionNoRhs(_) => (),
                e => panic!(
                    "Productions from test input should return Err \"{}\" but returned Err \"{}\" instead",
                    TokenizerError::ProductionNoRhs(lhs.to_string()),
                    e
                ),
            },
        }
    }

    #[test]
    fn productions_from_string_no_rhs_or() {
        let lhs = "A";
        match super::productions_from_string(format!("{} -> B | ", lhs).as_str()) {
            Ok(g) => {
                println!("{:?}", g);
                panic!("Productions from test input should return an Err result")
            },
            Err(e) => match e {
                TokenizerError::ProductionNoRhs(_) => (),
                e => panic!(
                    "Productions from test input should return Err \"{}\" but returned Err \"{}\" instead",
                    TokenizerError::ProductionNoRhs(lhs.to_string()),
                    e
                ),
            },
        }
    }

    #[test]
    fn productions_from_string_multiple_one_line() {
        let expected_index = 0;
        match super::productions_from_string("A -> B -> C") {
            Ok(_) => panic!("Productions from test input should return an Err result"),
            Err(e) => match e {
                TokenizerError::ProductionMultipleOneLine(i) => assert_eq!(i, expected_index, "Production rule error should come from the {}° line not {}° line", expected_index, i),
                e => panic!(
                    "Productions from test input should return Err \"{}\" but returned Err \"{}\" instead",
                    TokenizerError::ProductionMultipleOneLine(expected_index),
                    e
                ),
            },
        }
    }

    #[test]
    fn grammar_from_string() {
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

        match super::grammar_from_string("S -> A B\nA -> a | B\nB -> b") {
            Ok(g) => {
                assert_eq!(
                    g.s, s_check,
                    "Tokenized start symbol is not the one expected"
                );
                assert_eq!(
                    g.n, n_check,
                    "Tokenized non terminal symbols are not those expected"
                );
                assert_eq!(
                    g.t, t_check,
                    "Tokenized terminal symbols are not those expected"
                );
                assert_eq!(
                    g.p, p_check,
                    "Tokenized production rules are not those expected"
                );
            }
            Err(e) => panic!("Error tokenizing grammar from string: {}", e),
        }
    }

    #[test]
    fn grammar_from_string_too_many_start_symbols() {
        let expected_lhs = "A B".to_string();
        match super::grammar_from_string(format!("{} -> A\nA -> a | B\nB -> b", expected_lhs).as_str()) {
            Ok(_) => panic!("Tokenizing grammar from test input should return an Err result"),
            Err(e) => match e {
                TokenizerError::ProductionsTooManyStartSymbols(lhs) => assert_eq!(expected_lhs, lhs, "Tokenizing grammar error lhs string should be {} not {}", expected_lhs, lhs),
                e => panic!(
                    "Tokenizing grammar from test input should return Err \"{}\" but returned Err \"{}\" instead",
                    TokenizerError::ProductionsTooManyStartSymbols(expected_lhs),
                    e
                ),
            },
        }
    }

    #[test]
    fn symbols_from_string() {
        let expected_symbols: Vec<Symbol> =
            vec![Symbol::new("A").unwrap(), Symbol::new("B").unwrap()];
        match super::symbols_from_string("A B") {
            Ok(symbols) => {
                assert_eq!(
                    symbols, expected_symbols,
                    "Tokenized symbols are not the ones expected"
                );
            }
            Err(e) => panic!("Error tokenizing symbols from string: {}", e),
        }
    }

    #[test]
    fn symbols_from_string_no_symbols() {
        match super::symbols_from_string("  ") {
            Ok(_) => panic!("Tokenizing symbols from test input should return an Err result"),
            Err(e) => match e {
                TokenizerError::NoSymbols => (),
                e => panic!(
                    "Tokenizing symbols from test input should return Err \"{}\" but returned Err \"{}\" instead",
                    TokenizerError::NoSymbols,
                    e
                ),
            },
        }
    }

    #[test]
    fn symbols_from_string_invalid_symbol() {
        let test_input = "®".to_string();
        match super::symbols_from_string(format!("A {}", test_input).as_str()) {
            Ok(_) => panic!("Tokenizing symbols from test input should return an Err result"),
            Err(e) => match e {
                TokenizerError::InvalidSymbol(s) => assert_eq!(s, test_input),
                e => panic!(
                    "Tokenizing symbols from test input should return Err \"{}\" but returned Err \"{}\" instead",
                    TokenizerError::InvalidSymbol(test_input),
                    e
                ),
            },
        }
    }
}
