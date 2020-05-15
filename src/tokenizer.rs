use std::error::Error;
use std::fmt;

const PRODUCTION_SEP: &str = "->";
const PRODUCTION_OR: &str = "|";
const TRANSITION_SEP: &str = "->";

/// Errors resulting from tokenizing strings.
///
/// When parsing custom strings, invalid or bad formatted strings can generate
/// tokenizer errors, according to which representation is expected.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum TokenizerError {
    /// Error for productions which doesn't have a left hand side
    ProductionNoLhs,
    /// Error for productions which doesn't have a right hand side
    ProductionNoRhs(String),
    /// Error for productions which doesn't have the production separator
    /// (see [Production](production/index.html) module for further details)
    ProductionNoSeparator(String),
    /// Error for having multiple productions on the same row/line
    ProductionMultipleOneLine(usize),
    /// Error for having multiple productions when expecting only one in the
    /// whole given string
    ProductionMultiple(String),
    /// Error for having no "to" part in the transition
    TransitionNoTo(String),
    /// Error for having no "label" part in the transition
    TransitionNoLabel(String),
    /// Error for having no "from" part in the transition
    TransitionMultipleOneLine(usize),
    /// Error for having too many transitions but expected one in the whole
    /// given string
    TransitionMultiple(String),
    /// Error for having a given string not containing any transition but
    /// at least one was expected (see [Transition](automaton/struct.Transition.html)
    /// documentation for further details)
    TransitionEmpty(String),
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
            TokenizerError::ProductionMultiple(string) => write!(
                f,
                "TokenizerError: Too many production rules found in \"{}\", expected only 1",
                string
            ),
            TokenizerError::TransitionNoTo(string) => write!(
                f,
                "TokenizerError: no \"to\" part in transition \"{}\"",
                string
            ),
            TokenizerError::TransitionNoLabel(string) => write!(
                f,
                "TokenizerError: no \"label\" part in transition \"{}\"",
                string
            ),
            TokenizerError::TransitionMultipleOneLine(index) => write!(
                f,
                "TokenizerError: too many separator found for transition on the same line on line {}",
                index
            ),
            TokenizerError::TransitionMultiple(string) => write!(
                f,
                "TokenizerError: found too many transitions in the given input \"{}\" but 1 expected",
                string
            ),
            TokenizerError::TransitionEmpty(string) => write!(
                f,
                "TokenizerError: expected at least one transition but zero found in the given input \"{}\"",
                string
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

pub fn transitions_from_string(
    string: &str,
) -> Result<Vec<(Vec<String>, String, Vec<String>)>, TokenizerError> {
    let mut transitions = Vec::new();

    for (i, transition) in string.trim().lines().map(|s| s.trim()).enumerate() {
        let mut parts = transition.split(TRANSITION_SEP);
        println!("PRINTING: {}", transition);
        match (parts.next(), parts.next(), parts.next(), parts.next()) {
            (Some(from), Some(label), Some(to), None) => transitions.push((
                symbols_from_string(from),
                label.trim().to_string(),
                symbols_from_string(to),
            )),
            (Some(_), Some(_), None, _) => {
                return Err(TokenizerError::TransitionNoTo(transition.to_string()))
            }
            (Some(_), None, _, _) => {
                return Err(TokenizerError::TransitionNoLabel(transition.to_string()))
            }
            (_, _, _, _) => return Err(TokenizerError::TransitionMultipleOneLine(i)),
        }
    }

    Ok(transitions)
}

#[cfg(test)]
mod tests {

    use super::*;
    use std::fmt::Write;

    // mod.tokenizer

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
    fn transitions_from_string() {
        let expected_from = vec!["A1", "A2"];
        let expected_label = "label".to_string();
        let expected_to = vec!["B1", "B2"];
        let result = super::transitions_from_string("A1 A2 -> label -> B1 B2");

        assert!(
            result.is_ok(),
            "Tokenizing transitions should not return an error"
        );
        let transitions = result.unwrap();
        assert_eq!(
            transitions.len(),
            1,
            "Tokenized transitions are not the ones expected"
        );
        let (from, label, to) = transitions[0].clone();
        assert_eq!(
            from, expected_from,
            "Tokenized transition from is not the one expected"
        );
        assert_eq!(
            label, expected_label,
            "Tokenized transition label is not the one expected"
        );
        assert_eq!(
            to, expected_to,
            "Tokenized transition to is not the one expected"
        )
    }

    #[test]
    fn transitions_from_string_no_to() {
        let result = super::transitions_from_string("A -> B ");

        assert!(
            result.is_err(),
            "Transitions from test input should return an Err result"
        );
        let e = result.unwrap_err();
        assert_eq!(
            e,
            TokenizerError::TransitionNoTo("A -> B".to_string()),
            "Transitions from test input returned the wrong error"
        );
    }

    #[test]
    fn transitions_from_string_no_to_no_label() {
        let result = super::transitions_from_string("A -> ");

        assert!(
            result.is_err(),
            "Transitions from test input should return an Err result"
        );
        let e = result.unwrap_err();
        assert_eq!(
            e,
            TokenizerError::TransitionNoTo("A ->".to_string()),
            "Transitions from test input returned the wrong error"
        );
    }

    #[test]
    fn transitions_from_string_no_label() {
        let result = super::transitions_from_string("A ");

        assert!(
            result.is_err(),
            "Transitions from test input should return an Err result"
        );
        let e = result.unwrap_err();
        assert_eq!(
            e,
            TokenizerError::TransitionNoLabel("A".to_string()),
            "Transitions from test input returned the wrong error"
        );
    }

    #[test]
    fn transitions_from_string_multiple_one_line() {
        let result = super::transitions_from_string("A -> B -> C -> ");

        assert!(
            result.is_err(),
            "Transitions from test input should return an Err result"
        );
        let e = result.unwrap_err();
        assert_eq!(
            e,
            TokenizerError::TransitionMultipleOneLine(0),
            "Transitions from test input returned the wrong error"
        );
    }

    // enum.TokenizerError

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

    #[test]
    fn tokenizer_error_display_production_multiple() {
        let mut buf = String::new();
        let string = "A -> B -> C";

        let result = write!(
            buf,
            "{}",
            TokenizerError::ProductionMultiple(string.to_string())
        );
        assert!(result.is_ok());
        assert_eq!(
            buf,
            format!(
                "TokenizerError: Too many production rules found in \"{}\", expected only 1",
                string
            )
        )
    }

    #[test]
    fn tokenizer_error_display_transition_no_to() {
        let mut buf = String::new();
        let string = "A -> B";

        let result = write!(
            buf,
            "{}",
            TokenizerError::TransitionNoTo(string.to_string())
        );
        assert!(result.is_ok());
        assert_eq!(
            buf,
            format!(
                "TokenizerError: no \"to\" part in transition \"{}\"",
                string
            )
        )
    }

    #[test]
    fn tokenizer_error_display_transition_no_label() {
        let mut buf = String::new();
        let string = "A";

        let result = write!(
            buf,
            "{}",
            TokenizerError::TransitionNoLabel(string.to_string())
        );
        assert!(result.is_ok());
        assert_eq!(
            buf,
            format!(
                "TokenizerError: no \"label\" part in transition \"{}\"",
                string
            )
        )
    }

    #[test]
    fn tokenizer_error_display_transition_multiple_one_line() {
        let mut buf = String::new();
        let index = 0;

        let result = write!(buf, "{}", TokenizerError::TransitionMultipleOneLine(index));
        assert!(result.is_ok());
        assert_eq!(
            buf,
            format!(
                "TokenizerError: too many separator found for transition on the same line on line {}",
                index
            )
        )
    }

    #[test]
    fn tokenizer_error_display_transition_multiple() {
        let mut buf = String::new();
        let string = "A -> label -> B\nA -> label -> B";

        let result = write!(
            buf,
            "{}",
            TokenizerError::TransitionMultiple(string.to_string())
        );
        assert!(result.is_ok());
        assert_eq!(
            buf,
            format!(
                "TokenizerError: found too many transitions in the given input \"{}\" but 1 expected",
                string
            )
        )
    }

    #[test]
    fn tokenizer_error_display_transition_no_separator() {
        let mut buf = String::new();
        let string = "\t";

        let result = write!(
            buf,
            "{}",
            TokenizerError::TransitionEmpty(string.to_string())
        );
        assert!(result.is_ok());
        assert_eq!(
            buf,
            format!(
                "TokenizerError: expected at least one transition but zero found in the given input \"{}\"",
                string
            )
        )
    }
}
