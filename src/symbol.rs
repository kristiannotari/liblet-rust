//! Module for handling all symbols related operations.
//!
//! It defines a `Symbol` type which can be used to conveniently work with symbols in grammars and productions
//! and provide abstraction over normal collection of chars.
//!
//! It can be easily constructed from `&str`s.

use crate::tokenizer;
use itertools::Itertools;
use std::error::Error;
use std::fmt;

const EPSILON: char = 'ε';

#[derive(Debug, PartialEq)]
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

        if !Symbol::is_valid_symbol(string) {
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
            None => unreachable!(),
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
        c.is_ascii_graphic()
    }

    /// Check if a string is a valid symbol.
    /// `true` if the string is a valid symbol, `false` otherwise
    ///
    /// # Examples
    /// ```rust
    /// use liblet::symbol::Symbol;
    ///
    /// assert!(Symbol::is_valid_symbol("A"));
    /// assert!(!Symbol::is_valid_symbol("\n"));
    /// ```
    pub fn is_valid_symbol(string: &str) -> bool {
        string == EPSILON.to_string() || string.chars().all(|c| Symbol::is_valid_char(&c))
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
    /// let result = Symbol::from_string("A B C")?;
    ///
    /// assert_eq!(result.len(), 3);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn from_string(string: &str) -> Result<Vec<Symbol>, SymbolError> {
        tokenizer::symbols_from_string(string)
            .iter()
            .map(|s| Symbol::new(s))
            .fold_results(Vec::new(), |mut acc, s| {
                acc.push(s);
                acc
            })
    }

    /// Return a new symbol which represent the empty symbol 'ε'.
    ///
    /// # Examples
    /// ```rust
    /// use liblet::symbol::Symbol;
    ///
    /// let symbol = Symbol::empty();
    ///
    /// assert_eq!(symbol.to_string(), "ε");
    /// ```
    pub fn empty() -> Symbol {
        Symbol {
            string: EPSILON.to_string(),
        }
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
/// as opposed to the `Result` returned from the Symbol `from_string` method.
///
/// # Panics
/// Panics if some error occurred during symbol creation or string parsing (see Symbol [from_string](struct.Symbol.html#method.from_string) method for further details)
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
    Symbol::from_string(string).unwrap()
}

#[cfg(test)]
mod tests {

    use super::*;
    use std::fmt::Write;

    #[test]
    fn new() {
        let symbol = "A";
        let result = Symbol::new(symbol);

        assert!(result.is_ok(), "Error creating new symbol from string");
    }

    #[test]
    fn new_empty_symbol() {
        let symbol = "";
        let result = Symbol::new(symbol);

        assert!(
            result.is_err(),
            "Creation of symbol from test input should return an Err result"
        );
        let e = result.unwrap_err();
        assert_eq!(
            e,
            SymbolError::EmptySymbol,
            "Creation of symbol from test input returned the wrong error"
        );
    }

    #[test]
    fn new_invalid_char() {
        let invalid_symbol = "Aλ";
        let result = Symbol::new(invalid_symbol);

        assert!(
            result.is_err(),
            "Creation of symbol from test input should return an Err result"
        );
        let e = result.unwrap_err();
        assert_eq!(
            e,
            SymbolError::InvalidSymbol(invalid_symbol.to_string()),
            "Creation of symbol from test input returned the wrong error"
        );
    }

    #[test]
    fn as_str() {
        let s = "A";
        assert_eq!(
            Symbol::new(s).unwrap().as_str(),
            s,
            "Symbol as_str doesn't correspond to expected one"
        )
    }

    #[test]
    fn to_string() {
        let s = "A";
        assert_eq!(
            Symbol::new(s).unwrap().to_string(),
            s,
            "Symbol to_string doesn't correspond to expected one"
        )
    }

    #[test]
    fn is_terminal() {
        let s = "a";
        let symbol = Symbol::new(s).unwrap();
        assert!(
            symbol.is_terminal(),
            "Symbol {} should be flagged as terminal",
            symbol
        );
        assert!(
            !symbol.is_non_terminal(),
            "Symbol {} should not be flagged as non terminal",
            symbol
        )
    }

    #[test]
    fn is_non_terminal() {
        let s = "A";
        let symbol = Symbol::new(s).unwrap();
        assert!(
            !symbol.is_terminal(),
            "Symbol {} should not flagged as terminal",
            symbol
        );
        assert!(
            symbol.is_non_terminal(),
            "Symbol {} should be flagged as non terminal",
            symbol
        )
    }

    #[test]
    fn is_valid_char() {
        let valid_symbol = 'A';
        let invalid_symbol_1 = 'Σ';
        let invalid_symbol_2 = '\n';
        assert!(
            Symbol::is_valid_char(&valid_symbol),
            "Char {} should be flagged as valid",
            valid_symbol
        );
        assert!(
            !Symbol::is_valid_char(&invalid_symbol_1),
            "Char {} should not be flagged as valid",
            invalid_symbol_1
        );
        assert!(
            !Symbol::is_valid_char(&invalid_symbol_2),
            "Char {} should not be flagged as valid",
            invalid_symbol_2
        );
        assert!(
            !Symbol::is_valid_char(&EPSILON),
            format!("Empty word {} should not be flagged as valid", EPSILON)
        );
    }

    #[test]
    fn is_valid_symbol() {
        let valid_symbol = "A";
        let invalid_symbol_1 = "Σ";
        let invalid_symbol_2 = "\n";
        assert!(
            Symbol::is_valid_symbol(&valid_symbol),
            "String {} should be flagged as valid",
            valid_symbol
        );
        assert!(
            !Symbol::is_valid_symbol(&invalid_symbol_1),
            "String {} should not be flagged as valid",
            invalid_symbol_1
        );
        assert!(
            !Symbol::is_valid_symbol(&invalid_symbol_2),
            "String {} should not be flagged as valid",
            invalid_symbol_2
        );
        assert!(
            Symbol::is_valid_symbol(&EPSILON.to_string()),
            format!("Empty word {} should be flagged as valid", EPSILON)
        );
    }

    #[test]
    fn from_string() {
        let symbols = vec![
            Symbol::new("A").unwrap(),
            Symbol::new("B").unwrap(),
            Symbol::new("a").unwrap(),
        ];
        assert_eq!(
            Symbol::from_string("A B a").unwrap(),
            symbols,
            "Parsed symbols"
        );
    }

    #[test]
    fn empty() {
        let symbol = Symbol::empty();
        assert_eq!(symbol.to_string(), EPSILON.to_string());
    }

    #[test]
    fn symbol() {
        let s = "A";
        assert_eq!(super::symbol(s).as_str(), s)
    }

    #[test]
    fn symbols() {
        let s = "A B C D";
        assert_eq!(
            super::symbols(s),
            vec![
                super::symbol("A"),
                super::symbol("B"),
                super::symbol("C"),
                super::symbol("D"),
            ]
        )
    }

    #[test]
    fn into_iter() {
        let symbol = super::symbol("Abcdef");
        let chars_check: &Vec<char> = &vec!['A', 'b', 'c', 'd', 'e', 'f'];
        let chars: &Vec<char> = &symbol.into_iter().collect();

        assert_eq!(
            chars, chars_check,
            "Chars collected from iterating over the symbol are not those expected"
        )
    }

    #[test]
    fn symbol_error_display_empty_symbol() {
        let mut buf = String::new();

        let result = write!(buf, "{}", SymbolError::EmptySymbol);
        assert!(result.is_ok());
        assert_eq!(buf, "SymbolError: Empty input given for symbol")
    }

    #[test]
    fn symbol_error_display_invalid_symbol() {
        let mut buf = String::new();
        let symbol = "\n";

        let result = write!(buf, "{}", SymbolError::InvalidSymbol(symbol.to_string()));
        assert!(result.is_ok());
        assert_eq!(buf, format!("SymbolError: Invalid symbol \"{}\"", symbol))
    }

    #[test]
    fn symbol_display() {
        let mut buf = String::new();
        let symbol = "A";

        let result = write!(buf, "{}", Symbol::new(symbol).unwrap());
        assert!(result.is_ok());
        assert_eq!(buf, symbol)
    }
}
