use crate::parser;
use std::error::Error;
use std::fmt;

const EMPTY_WORD: char = 'ε';

#[derive(Debug,PartialEq)]
pub enum SymbolError {
    EmptySymbol,
    InvalidSymbol(String),
}

impl fmt::Display for SymbolError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SymbolError::EmptySymbol => write!(f, "SymbolError: Empty input given for symbol"),
            SymbolError::InvalidSymbol(symbol) => {
                write!(f, "SymbolError: Invalid symbol \"{}\"", symbol)
            }
        }
    }
}

impl Error for SymbolError {}

#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub struct Symbol {
    string: String,
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.string)
    }
}

impl Symbol {
    pub fn new(string: &str) -> Result<Symbol, SymbolError> {
        if string.is_empty() {
            return Err(SymbolError::EmptySymbol);
        }

        let s: String = string
            .to_string()
            .chars()
            .filter(|c| Symbol::is_valid_char(c))
            .collect();
        if s.len() != string.len() {
            return Err(SymbolError::InvalidSymbol(string.to_string()));
        }

        Ok(Symbol { string: s })
    }

    pub fn as_str(&self) -> &str {
        self.string.as_str()
    }

    pub fn to_string(&self) -> String {
        self.string.clone()
    }

    pub fn is_terminal(&self) -> bool {
        !self.is_non_terminal()
    }

    pub fn is_non_terminal(&self) -> bool {
        match self.string.chars().next() {
            Some(c) => c.is_ascii_uppercase(),
            None => false,
        }
    }

    pub fn is_valid_char(c: &char) -> bool {
        c.is_ascii_graphic() || c == &EMPTY_WORD
    }

    pub fn symbols_from_string(string: &str) -> Vec<Symbol> {
        parser::symbols_from_string(string).unwrap()
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn new() {
        let symbol = "A";
        match Symbol::new(symbol) {
            Ok(s) => assert_eq!(s.as_str(), symbol),
            Err(e) => panic!("Error {} creating new symbol from string: {}", e, symbol),
        }
    }

    #[test]
    fn new_empty_symbol() {
        let symbol = "";
        match Symbol::new(symbol) {
            Ok(_) => panic!("Creation of symbol from test input should return an Err result"),
            Err(e) => 
            match e {
                SymbolError::EmptySymbol => (),
                e => panic!(
                    "Creation of symbol from test input should return Err \"{}\" but returned Err \"{}\" instead",
                    SymbolError::EmptySymbol,
                    e
                ),
            }
        }
    }

    #[test]
    fn new_invalid_char() {
        let invalid_symbol = "Aλ";
        match Symbol::new(invalid_symbol) {
            Ok(_) => panic!("Creation of symbol from test input should return an Err result"),
            Err(e) => 
            match e {
                SymbolError::InvalidSymbol(symbol) => assert_eq!(symbol, invalid_symbol),
                e => panic!(
                    "Creation of symbol from test input should return Err \"{}\" but returned Err \"{}\" instead",
                    SymbolError::InvalidSymbol(invalid_symbol.to_string()),
                    e
                ),
            }
        }
    }

    #[test]
    fn as_str() {
        let s = "A";
        assert_eq!(Symbol::new(s).unwrap().as_str(), s)
    }

    #[test]
    fn to_string() {
        let s = "A";
        assert_eq!(Symbol::new(s).unwrap().to_string(), s)
    }

    #[test]
    fn is_terminal() {
        let s = "a";
        let symbol = Symbol::new(s).unwrap();
        assert!(symbol.is_terminal(), "Symbol {} should be flagged as terminal", symbol);
        assert!(!symbol.is_non_terminal(), "Symbol {} should not be flagged as non terminal", symbol)
    }

    #[test]
    fn is_non_terminal() {
        let s = "A";
        let symbol = Symbol::new(s).unwrap();
        assert!(!symbol.is_terminal(), "Symbol {} should not flagged as terminal", symbol);
        assert!(symbol.is_non_terminal(), "Symbol {} should be flagged as non terminal", symbol)
    }

    #[test]
    fn is_valid_char() {
        let valid_symbol = 'A';
        let invalid_symbol_1 = 'Σ';
        let invalid_symbol_2 = '\n';
        assert!(Symbol::is_valid_char(&valid_symbol), "Char {} should be flagged as valid", valid_symbol);
        assert!(!Symbol::is_valid_char(&invalid_symbol_1), "Char {} should not be flagged as valid", invalid_symbol_1);
        assert!(!Symbol::is_valid_char(&invalid_symbol_2), "Char {} should not be flagged as valid", invalid_symbol_2);
        assert!(Symbol::is_valid_char(&EMPTY_WORD), "Empty word {} should be flagged as valid", EMPTY_WORD);
    }

    #[test]
    fn symbols_from_string() {
        let symbols = vec![Symbol::new("A").unwrap(), Symbol::new("B").unwrap(), Symbol::new("a").unwrap()];
        assert_eq!(Symbol::symbols_from_string("A B a"), symbols, "Parsed symbols");
    }
}
