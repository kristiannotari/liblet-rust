use std::error::Error;
use std::fmt;

const PRODUCTION_SEP: &str = "->";
const PRODUCTION_OR: &str = "|";

#[derive(Debug, PartialEq)]
pub enum TokenizerError {
    ProductionNoLhs,
    ProductionNoRhs(String),
    ProductionMultipleOneLine(usize),
}

impl fmt::Display for TokenizerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
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
        }
    }
}

impl Error for TokenizerError {}

pub fn productions_from_string(
    string: &str,
) -> Result<Vec<(Vec<String>, Vec<String>)>, TokenizerError> {
    let mut p: Vec<(Vec<String>, Vec<String>)> = Vec::new();

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
                    p.push((symbols_from_string(lhs), symbols_from_string(rhs)))
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

    Ok(p)
}

pub fn symbols_from_string(string: &str) -> Vec<String> {
    string
        .trim()
        .split_whitespace()
        .map(|s| s.to_string())
        .collect()
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn productions_from_string() {
        let p_check = vec![
            (vec!["S"], vec!["A", "B"]),
            (vec!["A"], vec!["a"]),
            (vec!["A"], vec!["B"]),
            (vec!["B"], vec!["b"]),
        ];

        match super::productions_from_string("S -> A B\nA -> a | B\nB -> b") {
            Ok(p) => {
                assert_eq!(p.len(), p_check.len());
                for (i, p) in p.iter().enumerate() {
                    assert_eq!(
                        p.0, p_check[i].0,
                        "Tokenized production left side is not the one expected"
                    );
                    assert_eq!(
                        p.1, p_check[i].1,
                        "Tokenized production right side is not the one expected"
                    );
                }
            }
            Err(e) => panic!("Error tokenizing productions from string: {}", e),
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
                    TokenizerError::ProductionNoLhs,
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
    fn symbols_from_string() {
        let expected_symbols = vec!["A", "B"];

        assert_eq!(
            super::symbols_from_string("A B"),
            expected_symbols,
            "Tokenized symbols are not the ones expected"
        );
    }

    #[test]
    fn symbols_from_string_no_symbols() {
        assert_eq!(super::symbols_from_string("  \t   \n   \r   ").len(), 0);
    }

    #[test]
    fn symbols_from_string_empty() {
        assert_eq!(super::symbols_from_string("").len(), 0);
    }
}
