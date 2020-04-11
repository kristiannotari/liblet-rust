use crate::parser;
use crate::symbol::Symbol;
use std::collections::HashSet;

#[derive(Debug, PartialEq)]
pub struct Production {
    pub lhs: Vec<Symbol>,
    pub rhs: Vec<Symbol>,
}

impl Production {
    pub fn symbols_lhs(&self) -> HashSet<Symbol> {
        self.lhs.clone().into_iter().collect()
    }

    pub fn symbols_rhs(&self) -> HashSet<Symbol> {
        self.rhs.clone().into_iter().collect()
    }

    pub fn symbols(&self) -> HashSet<Symbol> {
        self.symbols_lhs()
            .union(&self.symbols_rhs())
            .map(|x| x.clone())
            .collect()
    }
}

#[cfg(test)]
mod tests {}
