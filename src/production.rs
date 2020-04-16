use crate::parser;
use crate::symbol::Symbol;
use std::collections::HashSet;

#[derive(Debug, PartialEq)]
pub struct Production {
    pub lhs: Vec<Symbol>,
    pub rhs: Vec<Symbol>,
}

impl Production {
    pub fn new<I>(lhs: I, rhs: I) -> Production
    where
        I: IntoIterator<Item = Symbol>,
    {
        Production {
            lhs: lhs.into_iter().collect(),
            rhs: rhs.into_iter().collect(),
        }
    }

    pub fn new_from_string<'a, I>(lhs: I, rhs: I) -> Production
    where
        I: IntoIterator<Item = &'a str>,
    {
        Production::new(
            lhs.into_iter()
                .map(|s| Symbol::new(s).unwrap())
                .collect::<Vec<Symbol>>(),
            rhs.into_iter()
                .map(|s| Symbol::new(s).unwrap())
                .collect::<Vec<Symbol>>(),
        )
    }

    pub fn lhs(&self) -> HashSet<Symbol> {
        self.lhs.clone().into_iter().collect()
    }

    pub fn rhs(&self) -> HashSet<Symbol> {
        self.rhs.clone().into_iter().collect()
    }

    pub fn symbols(&self) -> HashSet<Symbol> {
        self.lhs().union(&self.rhs()).map(|x| x.clone()).collect()
    }
}

#[cfg(test)]
mod tests {}
