//! Module for handling all symbols related operations.
//! 
//! It defines a `Symbol` type which can be used to conveniently work with symbols in grammars and productions
//! and provide abstraction over normal collection of chars.
//! 
//! It can be easily constructed from `&str`s.

use crate::tokenizer;
use std::error::Error;
use std::fmt;
use itertools::Itertools;

const EMPTY_SYMBOL: char = 'ε';

#[derive(Debug,PartialEq)]
pub enum SymbolError {
    /// Error resulting from the attempt to create a Symbol from an empty collection of chars.
    EmptySymbol,
    /// Error resulting from the the attempt to create a Symbol from an invalid collection of chars.
    /// It also provides the `String` used to attempt the Symbol creation, which generated the error.
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

/// The main type of this module. It provides abstraction over symbols.
/// Great to work with correct dataset when dealing with grammars and productions, or similar.
/// 
/// A Symbol can be made of every ascii-graphic chars,
/// like the one described in [rust documentation](https://doc.rust-lang.org/std/primitive.char.html#method.is_ascii_graphic)
/// for chars `ascii_graphic` method, which accept chars going from U+0021 '!' ..= U+007E '~', including 'ε', the "empty word" symbol.
/// 
/// Symbols can be logically divided in 2 major categories, defined as follow:
/// - non terminals, which start with an uppercase letter (A-Z)
/// - terminals, which start with everything else
/// 
/// Checking if a symbol is terminal or non terminal can be done using the according boolean methods you can find below.
/// 
/// A symbol can be created easily from strings, following these rules:
/// - string can contain any number of whitespace
/// - string has to contain at least one valid char (see above)
/// - string can't contain anything else
/// 
/// It also implements the `IntoIterator` to iterate over the collection of chars which make up the Symbol.
#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub struct Symbol {
    string: String,
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.string)
    }
}

impl<'a> IntoIterator for &'a Symbol {
    type Item = char;
    type IntoIter = std::str::Chars<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.string.chars()
    }
}

impl Symbol {

    /// Creates a new Symbol based on the chars in the input.
    /// 
    /// # Errors
    /// It can return an error if the input is empty or contains invalid chars.
    /// 
    /// ## Examples
    /// ```rust
    /// use liblet::symbol::Symbol;
    /// 
    /// // create a new symbol based from the string "mysymbol"
    /// let symbol = Symbol::new("mysymbol");
    /// 
    /// assert!(symbol.is_ok());
    /// ```
    pub fn new(string: &str) -> Result<Symbol, SymbolError> {
        if string.is_empty() {
            return Err(SymbolError::EmptySymbol);
        }

        let s = string.to_string();

        if s
        .chars()
        .any(|c| !Symbol::is_valid_char(&c)) {
            return Err(SymbolError::InvalidSymbol(s));
        }

        Ok(Symbol { string: s })
    }

    /// Return the `&str` representing this symbol chars.
    /// 
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::symbol::Symbol;
    /// 
    /// // create a new symbol based from the string "mysymbol"
    /// let symbol = Symbol::new("mysymbol")?;
    /// 
    /// assert_eq!(symbol.as_str(), "mysymbol");
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn as_str(&self) -> &str {
        self.string.as_str()
    }

    /// Return the `String` representing this symbol chars.
    /// 
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::symbol::Symbol;
    /// 
    /// // create a new symbol based from the string "mysymbol"
    /// let symbol = Symbol::new("mysymbol")?;
    /// 
    /// assert_eq!(symbol.to_string(), String::from("mysymbol"));
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn to_string(&self) -> String {
        self.string.clone()
    }

    /// Check if symbol is terminal.
    /// You can expect the call to `is_non_terminal` to return an opposite result.
    /// 
    /// `true` if symbol is terminal, `false` otherwise
    /// 
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::symbol::Symbol;
    /// 
    /// // create a new symbol based from the string "mysymbol"
    /// let symbol = Symbol::new("mysymbol").unwrap();
    /// 
    /// assert!(symbol.is_terminal());
    /// assert!(!symbol.is_non_terminal());
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn is_terminal(&self) -> bool {
        !self.is_non_terminal()
    }

    /// Check if symbol is non terminal.
    /// You can expect the call to `is_terminal` to return an opposite result.
    /// 
    /// `true` if symbol is non terminal, `false` otherwise
    /// 
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::symbol::Symbol;
    /// 
    /// // create a new symbol based from the string "Mysymbol"
    /// let symbol = Symbol::new("Mysymbol")?;
    /// 
    /// assert!(symbol.is_non_terminal());
    /// assert!(!symbol.is_terminal());
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn is_non_terminal(&self) -> bool {
        match self.string.chars().next() {
            Some(c) => c.is_ascii_uppercase(),
            None => false,
        }
    }

    /// Check if char is a valid symbol char.
    /// `true` if char is a valid symbol char, `false` otherwise
    /// 
    /// # Examples
    /// ```rust
    /// use liblet::symbol::Symbol;
    /// 
    /// assert!(Symbol::is_valid_char(&'c'));
    /// assert!(!Symbol::is_valid_char(&'\n'));
    /// ```
    pub fn is_valid_char(c: &char) -> bool {
        c.is_ascii_graphic() || c == &EMPTY_SYMBOL
    }

    /// Create a collection of symbols from a raw input string.
    ///
    /// # Errors
    /// Can return an error if the raw string can't be parsed to obtain actual symbols both due to wrong
    /// string formatting (symbols should be contiguous chars separated between them by every kind of whitespace) and due to
    /// symbol creation error (invalid char, empty symbol, etc.).
    /// 
    /// In the case an empty or whitespace only string is given, it just returns an empty collection of symbols.
    /// 
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::symbol::Symbol;
    /// 
    /// let result = Symbol::symbols_from_string("A B C")?;
    /// 
    /// assert_eq!(result.len(), 3);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn symbols_from_string(string: &str) -> Result<Vec<Symbol>, SymbolError> {
        tokenizer::symbols_from_string(string).iter().map(|s| Symbol::new(s)).fold_results(Vec::new(), |mut acc, s| { acc.push(s); acc})
    }
}

/// Convenience function for creating a symbol from a raw string.
/// 
/// It returns the symbol directly,
/// as opposed to the `Result` returned from the Symbol constructor.
/// 
/// # Panics
/// Panics if some error occurred during symbol creation (see Symbol [consructor](struct.Symbol.html#method.new) for further details)
/// 
/// # Examples
/// ```rust
/// use liblet::symbol::symbol;
/// 
/// let symbol = symbol("A");
/// 
/// assert_eq!(symbol.as_str(), "A");
/// ```
pub fn symbol(string: &str) -> Symbol {
    Symbol::new(string).unwrap()
}

/// Convenience function for creating a collection of symbols from a raw string.
/// 
/// It returns the symbols directly,
/// as opposed to the `Result` returned from the Symbol `symbols_from_string` method.
///
/// # Panics
/// Panics if some error occurred during symbol creation or string parsing (see Symbol [symbols_from_string](struct.Symbol.html#method.symbols_from_string) method for further details)
/// 
/// # Examples
/// ```rust
/// use liblet::symbol::symbols;
/// 
/// let result = symbols("A B C");
/// 
/// assert_eq!(result.len(), 3);
/// ```
pub fn symbols(string: &str) -> Vec<Symbol> {
    Symbol::symbols_from_string(string).unwrap()
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
        assert!(Symbol::is_valid_char(&EMPTY_SYMBOL), "Empty word {} should be flagged as valid", EMPTY_SYMBOL);
    }

    #[test]
    fn symbols_from_string() {
        let symbols = vec![Symbol::new("A").unwrap(), Symbol::new("B").unwrap(), Symbol::new("a").unwrap()];
        assert_eq!(Symbol::symbols_from_string("A B a").unwrap(), symbols, "Parsed symbols");
    }

    #[test]
    fn symbol() {
        let s = "A";
        assert_eq!(super::symbol(s).as_str(), s)
    }

    #[test]
    fn symbols() {
        let s = "A B C D";
        assert_eq!(super::symbols(s), vec![
            super::symbol("A"),
            super::symbol("B"),
            super::symbol("C"),
            super::symbol("D"),
        ])
    }

    #[test]
    fn into_iter() {
        let symbol = super::symbol("Abcdef");
        let chars_check: &Vec<char> = &vec!['A','b','c','d','e','f']; 
        let chars: &Vec<char> = &symbol.into_iter().collect();

        assert_eq!(chars, chars_check, "Chars collected from iterating over the symbol are not those expected")
    }
}
