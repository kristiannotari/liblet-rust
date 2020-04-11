use crate::parser;
use crate::production::Production;
use crate::symbol::Symbol;
use std::collections::HashSet;

#[derive(Debug, PartialEq)]
pub struct Grammar {
    pub s: Symbol,
    pub t: HashSet<Symbol>,
    pub n: HashSet<Symbol>,
    pub p: Vec<Production>,
}

impl Grammar {}

#[cfg(test)]
mod tests {}
