use std::error::Error;
use std::fmt;

const PRODUCTION_SEP: &str = "->";
const PRODUCTION_OR: &str = "|";

#[derive(Debug, PartialEq)]
pub enum TokenizerError {
    ProductionNoLhs,
    ProductionNoRhs(String),
    ProductionNoSeparator(String),
    ProductionMultipleOneLine(usize),
}

impl fmt::Display for TokenizerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenizerError::ProductionNoLhs => write!(
                f,
                "TokenizerError: Expected left hand side for production rule (form A {} B)",
                PRODUCTION_SEP
            ),
            TokenizerError::ProductionNoRhs(lhs) => write!(
                f,
                "TokenizerError: Expected right hand side of production rule {} {} ...",
                lhs, PRODUCTION_SEP
            ),
            TokenizerError::ProductionNoSeparator(production) => write!(
                f,
                "TokenizerError: Expected separator in production rule \"{}\"",
                production
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

    for (i, rule) in string.trim().lines().map(|s| s.trim()).enumerate() {
        let index: usize = rule
            .find(PRODUCTION_SEP)
            .ok_or(TokenizerError::ProductionNoSeparator(rule.to_string()))?;
        let mut sides = rule
            .split(PRODUCTION_SEP)
            .map(|s| s.trim())
            .filter(|s| !s.is_empty());
        match (sides.next(), sides.next(), sides.next()) {
            (Some(lhs), Some(rhs), None) => {
                for rhs in rhs.split(PRODUCTION_OR).map(|s| s.trim()) {
                    if rhs.is_empty() {
                        return Err(TokenizerError::ProductionNoRhs(lhs.to_string()));
                    }
                    p.push((symbols_from_string(lhs), symbols_from_string(rhs)))
                }
            }
            (Some(_), Some(_), Some(_)) => {
                return Err(TokenizerError::ProductionMultipleOneLine(i))
            }
            (Some(s), _, _) => {
                if index == rule.len() - PRODUCTION_SEP.len() {
                    return Err(TokenizerError::ProductionNoRhs(s.to_string()));
                } else {
                    return Err(TokenizerError::ProductionNoLhs);
                }
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
    use std::fmt::Write;

    #[test]
    fn productions_from_string() {
        let p_check = vec![
            (vec!["S"], vec!["A", "B"]),
            (vec!["A"], vec!["a"]),
            (vec!["A"], vec!["B"]),
            (vec!["B"], vec!["b"]),
        ];

        let result = super::productions_from_string("S -> A B\nA -> a | B\nB -> b");

        assert!(result.is_ok(), "Error tokenizing productions from string");
        let p = result.unwrap();
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

    #[test]
    fn productions_from_string_no_lhs() {
        let result = super::productions_from_string("-> B");

        assert!(
            result.is_err(),
            "Productions from test input should return an Err result"
        );
        let e = result.unwrap_err();
        assert_eq!(
            e,
            TokenizerError::ProductionNoLhs,
            "Productions from test input should returned the wrong error"
        );
    }

    #[test]
    fn productions_from_string_no_lhs_sep() {
        let result = super::productions_from_string("->");

        assert!(
            result.is_err(),
            "Productions from test input should return an Err result"
        );
        let e = result.unwrap_err();
        assert_eq!(
            e,
            TokenizerError::ProductionNoLhs,
            "Productions from test input should returned the wrong error"
        );
    }

    #[test]
    fn productions_from_string_no_rhs() {
        let lhs = "A";
        let result = super::productions_from_string(format!("{} -> ", lhs).as_str());

        assert!(
            result.is_err(),
            "Productions from test input should return an Err result"
        );
        let e = result.unwrap_err();
        assert_eq!(
            e,
            TokenizerError::ProductionNoRhs(lhs.to_string()),
            "Productions from test input should returned the wrong error"
        );
    }

    #[test]
    fn productions_from_string_no_production_sep() {
        let lhs = "abc test d";
        let result = super::productions_from_string(lhs);

        assert!(
            result.is_err(),
            "Productions from test input should return an Err result"
        );
        let e = result.unwrap_err();
        assert_eq!(
            e,
            TokenizerError::ProductionNoSeparator(lhs.to_string()),
            "Productions from test input should returned the wrong error"
        );
    }

    #[test]
    fn productions_from_string_no_rhs_or() {
        let lhs = "A";
        let result = super::productions_from_string(format!("{} -> B | ", lhs).as_str());

        assert!(
            result.is_err(),
            "Productions from test input should return an Err result"
        );
        let e = result.unwrap_err();
        assert_eq!(
            e,
            TokenizerError::ProductionNoRhs(lhs.to_string()),
            "Productions from test input should returned the wrong error"
        );
    }

    #[test]
    fn productions_from_string_multiple_one_line() {
        let expected_index = 0;
        let result = super::productions_from_string("A -> B -> C");

        assert!(
            result.is_err(),
            "Productions from test input should return an Err result"
        );
        let e = result.unwrap_err();
        assert_eq!(
            e,
            TokenizerError::ProductionMultipleOneLine(expected_index),
            "Productions from test input should returned the wrong error"
        );
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

    #[test]
    fn tokenizer_error_display_production_no_lhs() {
        let mut buf = String::new();

        let result = write!(buf, "{}", TokenizerError::ProductionNoLhs);
        assert!(result.is_ok());
        assert_eq!(
            buf,
            format!(
                "TokenizerError: Expected left hand side for production rule (form A {} B)",
                PRODUCTION_SEP
            )
        )
    }

    #[test]
    fn tokenizer_error_display_production_no_rhs() {
        let mut buf = String::new();
        let string = String::from("test");

        let result = write!(buf, "{}", TokenizerError::ProductionNoRhs(string.clone()));
        assert!(result.is_ok());
        assert_eq!(
            buf,
            format!(
                "TokenizerError: Expected right hand side of production rule {} {} ...",
                string, PRODUCTION_SEP
            )
        )
    }

    #[test]
    fn tokenizer_error_display_production_no_separator() {
        let mut buf = String::new();
        let string = String::from("test");

        let result = write!(
            buf,
            "{}",
            TokenizerError::ProductionNoSeparator(string.clone())
        );
        assert!(result.is_ok());
        assert_eq!(
            buf,
            format!(
                "TokenizerError: Expected separator in production rule \"{}\"",
                string
            )
        )
    }

    #[test]
    fn tokenizer_error_display_production_multiple_one_line() {
        let mut buf = String::new();
        let index = 0;

        let result = write!(buf, "{}", TokenizerError::ProductionMultipleOneLine(index));
        assert!(result.is_ok());
        assert_eq!(
            buf,
            format!(
                "TokenizerError: Too many production rule on the same line on line {}",
                index
            )
        )
    }
}
