use std::fmt;

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
    pub fn new(string: &str) -> Symbol {
        let s: String = string
            .to_string()
            .chars()
            .filter(|c| Symbol::is_symbol_char(c))
            .collect();
        if s.is_empty() {
            panic!("Can't create symbol from empty input or non alphanumeric characters");
        }

        Symbol { string: s }
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
            Some(c) => c.is_uppercase(),
            None => false,
        }
    }

    fn is_symbol_char(c: &char) -> bool {
        c.is_alphanumeric() || c == &'ε'
    }
}
