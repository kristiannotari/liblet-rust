//! Module for handling all derivation related operations.
//!
//! Its goal is to emulate derivation on grammars.
//!
//! It defines a `Derivation` type which can be used to conveniently work with grammar and derive them in many ways.

use crate::grammar::Grammar;
use crate::production::Production;
use crate::symbol::Symbol;
use std::error::Error;
use std::fmt;

#[derive(Debug, PartialEq)]
pub enum DerivationError {
    /// Error for when the derivation tries to apply a production whose index is not in the valid ones for the grammar.
    ///
    /// # Examples
    /// If you have a grammar with 3 productions, then the indexes of those productions will be [0..2]. If you specify 3 or more as
    /// production index, you'll get this error.
    WrongProductionIndex(usize),
    /// Error for when the derivation tries to apply a production to the indexed symbol in the current sentential form
    /// but the latter doesn't have enough symbols to reach the indexed one.
    ///
    /// # Examples
    /// If you have a sentential form like this `A B C` (which has 3 symbols, so the indexes of those symbols in the sentential
    /// form are 0 for the `A`, 1 for the `B` and 2 for the `C`) and try to apply a production rule to an index >= 3,
    /// then you'll get this error.
    WrongIndex(Vec<Symbol>, usize),
    /// Error for when the derivation tries to apply a production on part of the sentential form, but the production can't be applied
    /// due to the left hand side not matching the part of the sentential form the production is being applied to.
    ///
    /// # Examples
    /// If you have a derivation step which target the production `A -> B` and the index 0 of the sentential form,
    /// which contains `C A B`, the left hand side of the production (`A`) doesn't match the sentential form starting from
    /// 0 (`C`), so the derivation step can't be applied and you'll get this error.
    ImpossibleStep(Production, Vec<Symbol>, DerivationStep),
    /// Error for when the derivation tries to apply a [leftmost_n](struct.Derivation.html#method.leftmost_n) or
    /// [rightmost_n](struct.Derivation.html#method.rightmost_n) derivation to a sentential form which doesn't have a non terminal symbol,
    /// so the derivation step can't be applied, because there's no sentential form index to derive from.
    ///
    /// # Examples
    /// If you have the derivation step which target the production `A -> B` and the current sentential form is `a` (it doesn't have any non
    /// terminal symbols), you'll get this error.
    NoNSymbol(Vec<Symbol>),
}

impl fmt::Display for DerivationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DerivationError::WrongProductionIndex(p_index) => write!(
                f,
                "Wrong production index: can't find production with index {}° in the grammar",
                p_index
            ),
            DerivationError::WrongIndex(sf, index) => write!(
                f,
                "Wrong step index: can't find index {}° of sentential form \"{:?}\"",
                index, sf
            ),
            DerivationError::ImpossibleStep(p, sf, step) => write!(
                f,
                "Impossible step: can't apply {}° production \"{}\" to {}° symbol of sentential form \"{:?}\"",
                step.p_index, p, step.index, sf
            ),
            DerivationError::NoNSymbol(sf) => write!(
                f,
                "Impossible leftmost_n step: can't find a non terminal symbol to start the derivation from, within the sentential form \"{:?}\"",
                sf
            ),
        }
    }
}

impl Error for DerivationError {}

/// A useful abstraction over derivation steps.
///
/// It contains two information:
/// - p_index, the production index, needed to retrieve the correct production from the grammar
/// - index, the index of the first symbol of the sentential form from which apply the derivation step
///
/// # Examples
/// If you have a grammar based on the productions:
/// - `A -> B C`
/// - `B -> b`
///
/// you can create a derivation on that grammar, based on the default sentential form which is `A`
/// (it matches the grammar start symbol initially), then apply a derivation step based on:
/// - p_index = 0, so the 0° (first) production rule of the grammar will be used (`A -> B C`)
/// - index = 0, so the 0° (first) symbol of the current sentential form (`A`) which is `A`
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct DerivationStep {
    pub p_index: usize,
    pub index: usize,
}

/// The main type of this module.
///
/// It allows derivations on a specified grammar. Every derivation step modify the current derivation state.
/// A derivation can be created from scratch with the initial sentential form based on the grammar start symbol or a
/// custom sentential form can be used to initialize the derivation from there (in the latter case, no previous steps are automatically
/// calculated, so the history can't be reproduced using the derivation).
///
/// At any time, you can query the sentential form and the applied steps of the derivation.
///
/// For more information about derivation steps, check out their [documentation](struct.DerivationStep.html).
///
/// # Notice
/// A derivation needs to borrow a grammar, in order for it to work even if the grammar is then left. So if the original grammar is then modified,
/// it doesn't affect the derivation of the original one.
#[derive(Debug, Clone)]
pub struct Derivation {
    g: Grammar,
    steps: Vec<DerivationStep>,
    sentential_forms: Vec<Vec<Symbol>>,
}

impl fmt::Display for Derivation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            self.sentential_forms
                .iter()
                .map(|x: &Vec<Symbol>| {
                    x.iter()
                        .fold(String::new(), |acc: String, s: &Symbol| acc + s.as_str())
                })
                .collect::<Vec<String>>()
                .join(" -> ")
        )
    }
}

impl Derivation {
    /// Return a new derivation based on the given grammar.
    /// The initial sentential form is supposed to be the start symbol of the grammar.
    ///
    /// # Examples
    /// ```rust
    /// use liblet::derivation::Derivation;
    /// use liblet::grammar::grammar;
    /// use liblet::symbol::symbol;
    ///
    /// let g = grammar("A -> a");
    /// let d = Derivation::new(g);
    ///
    /// assert_eq!(d.sentential_form(), vec![symbol("A")]);
    /// ```
    pub fn new(g: Grammar) -> Derivation {
        let from = vec![g.s()];
        Derivation::new_from(g, from)
    }

    /// Return a new derivation based on the given grammar.
    /// The initial sentential form is the collection of symbols passed as input, ordered as it's passed.
    ///
    /// # Notice
    /// It allows you to create derivation based on sentential forms with any symbols, even the ones not in the grammar.
    ///
    /// # Examples
    /// ```rust
    /// use liblet::derivation::Derivation;
    /// use liblet::grammar::grammar;
    /// use liblet::symbol::symbol;
    ///
    /// let g = grammar("A -> a");
    /// let d = Derivation::new_from(g, vec![symbol("Custom")]);
    ///
    /// assert_eq!(d.sentential_form(), vec![symbol("Custom")]);
    /// ```
    pub fn new_from<I>(g: Grammar, sentential_form: I) -> Derivation
    where
        I: IntoIterator<Item = Symbol>,
    {
        Derivation {
            g: g,
            steps: Vec::new(),
            sentential_forms: vec![sentential_form.into_iter().collect()],
        }
    }

    /// Return the steps done from the derivation until now.
    ///
    /// Return an empy collection if no steps have been done.
    ///
    /// # Examples
    /// ```rust
    /// use liblet::derivation::Derivation;
    /// use liblet::grammar::grammar;
    ///
    /// let g = grammar("A -> a");
    /// let d = Derivation::new(g);
    ///
    /// assert!(d.steps().is_empty());
    /// ```
    pub fn steps(&self) -> Vec<DerivationStep> {
        self.steps.clone()
    }

    /// Return the current sentential form of the derivation, that is, the sentential form obtained
    /// by applying the derivation steps on the initial sentential form of the derivation.
    ///
    /// Return the initial sentential form if no steps have been done.
    ///
    /// # Examples
    /// ```rust
    /// use liblet::derivation::Derivation;
    /// use liblet::grammar::grammar;
    /// use liblet::symbol::symbol;
    ///
    /// let g = grammar("A -> a");
    /// let d = Derivation::new(g);
    ///
    /// assert_eq!(d.sentential_form(), vec![symbol("A")]);
    /// ```
    pub fn sentential_form(&self) -> Vec<Symbol> {
        if let Some(last) = self.sentential_forms.last() {
            last.clone()
        } else {
            vec![self.g.s()]
        }
    }

    /// Apply the given step (production index and sentential form index) to the derivation.
    /// Return the modified derivation for writing things like `d.step(0,0).step(1,2)` etc.
    ///
    /// Return the initial sentential form if no steps have been done.
    ///
    /// # Errors
    /// For more info about the errors returned, check the [DerivationError](enum.DerivationError.html) documentation.
    /// - [WrongProductionIndex](enum.DerivationError.html#variant.WrongProductionIndex) error if the production index targets a nonexistent grammar production
    /// - [WrongIndex](enum.DerivationError.html#variant.WrongIndex) error if the index target an impossible index of the current derivation sentential form
    /// - [ImpossibleStep](enum.DerivationError.html#variant.ImpossibleStep) error if the step to be applied can't be applied to the current derivation sentential form
    /// (but the steps indexes were correct)
    ///
    /// # Examples
    /// ```rust
    /// use liblet::derivation::Derivation;
    /// use liblet::grammar::grammar;
    /// use liblet::symbol::symbol;
    ///
    /// let g = grammar("A -> a");
    /// let d = Derivation::new(g);
    ///
    /// assert_eq!(d.sentential_form(), vec![symbol("A")]);
    /// ```
    pub fn step(mut self, p_index: usize, index: usize) -> Result<Derivation, DerivationError> {
        let step = DerivationStep { p_index, index };
        let p: Production = self
            .g
            .p()
            .get(p_index)
            .ok_or(DerivationError::WrongProductionIndex(p_index))?
            .clone();
        let mut sf: Vec<Symbol> = self.sentential_form();
        if sf.len() <= step.index {
            return Err(DerivationError::WrongIndex(sf, step.index));
        }
        let mut lhs: Vec<Symbol> = sf.split_off(step.index);

        if lhs.starts_with(&p.lhs()) {
            let mut rhs = p.rhs().clone();
            let mut remaining = lhs.split_off(p.lhs().len());
            sf.append(&mut rhs);
            sf.append(&mut remaining);
            self.steps.push(step);
            self.sentential_forms.push(sf);
        } else {
            return Err(DerivationError::ImpossibleStep(
                p.clone(),
                self.sentential_form(),
                step,
            ));
        }

        Ok(self)
    }

    /// Apply the given ordered collection of steps.
    ///
    /// It works just like the [step](#method.step) method, but it receives a collection of steps instead of a single one.
    /// For clarity reason, a colleciton of formal [DerivationStep](struct.DerivationStep.html)s is required here.
    ///
    /// # Errors
    /// Return an error if any of the given steps return an error when applied.
    /// For more info about the errors returned, check the [DerivationError](enum.DerivationError.html) documentation.
    /// - [WrongProductionIndex](enum.DerivationError.html#variant.WrongProductionIndex) error if the production index target a nonexistent grammar production
    /// - [WrongIndex](enum.DerivationError.html#variant.WrongIndex) error if the index target an impossible index of the current derivation sentential form
    /// - [ImpossibleStep](enum.DerivationError.html#variant.ImpossibleStep) error if the step to be applied can't be applied to the current derivation sentential form
    /// (but the steps indexes were correct)
    ///
    /// # Examples
    /// ```rust
    /// use liblet::derivation::Derivation;
    /// use liblet::grammar::grammar;
    /// use liblet::symbol::symbol;
    ///
    /// let g = grammar("A -> a");
    /// let d = Derivation::new(g);
    ///
    /// assert_eq!(d.sentential_form(), vec![symbol("A")]);
    /// ```
    pub fn step_from_iter<I>(self, steps: I) -> Result<Derivation, DerivationError>
    where
        I: IntoIterator<Item = DerivationStep>,
    {
        let mut d = self;
        for step in steps {
            d = d.step(step.p_index, step.index)?;
        }

        Ok(d)
    }

    /// Apply a step on the leftmost symbol of the current sentential form, using the production
    /// specified as input with the production index.
    ///
    /// It works just like the [step](#method.step) method, using 0 as the index of the sentential
    /// form symbol to derive from.
    ///
    /// # Errors
    /// Return an error according to the [step](#method.step) method.
    ///
    /// # Examples
    /// ```rust
    /// use liblet::derivation::Derivation;
    /// use liblet::grammar::grammar;
    /// use liblet::symbol::symbol;
    ///
    /// let g = grammar("A -> a");
    /// let d = Derivation::new(g);
    ///
    /// assert!(d.leftmost(0).is_ok()); // applied "A -> a" on "A"
    /// ```
    pub fn leftmost(self, p_index: usize) -> Result<Derivation, DerivationError> {
        self.step(p_index, 0)
    }

    /// Apply a step on the leftmost symbol of the current sentential form, using the production
    /// specified as input with the production index.
    ///
    /// It works just like the [step](#method.step) method, using the index of
    /// the first non terminal symbol within the current sentential form as the sentential form symbol index.
    ///
    /// # Errors
    /// Return an error according to the [step](#method.step) method.
    ///
    /// Moreover, it can return a [NoNSymbol](enum.DerivationError.html#variant.NoNSymbol) error if there are no non terminal symbols in the current
    /// sentential form
    ///
    /// # Examples
    /// ```rust
    /// use liblet::derivation::Derivation;
    /// use liblet::grammar::grammar;
    /// use liblet::symbol::symbol;
    ///
    /// let g = grammar("A -> a");
    /// let d = Derivation::new(g);
    ///
    /// assert!(d.leftmost_n(0).is_ok()); // applied "A -> a" on "A"
    /// ```
    pub fn leftmost_n(self, p_index: usize) -> Result<Derivation, DerivationError> {
        let sf = self.sentential_form();
        for (index, symbol) in sf.iter().enumerate() {
            if symbol.is_non_terminal() {
                return self.step(p_index, index);
            }
        }

        Err(DerivationError::NoNSymbol(sf))
    }

    /// Repeated [leftmost](#method.leftmost) for each production index in an ordered collection of productions passed as input
    pub fn leftmost_from_iter<I>(self, p_indexes: I) -> Result<Derivation, DerivationError>
    where
        I: IntoIterator<Item = usize>,
    {
        let mut d = self;
        for p_index in p_indexes {
            d = d.leftmost(p_index)?;
        }

        Ok(d)
    }

    /// Repeated [leftmost_n](#method.leftmost_n) for each production index in an ordered collection of productions passed as input
    pub fn leftmost_n_from_iter<I>(self, p_indexes: I) -> Result<Derivation, DerivationError>
    where
        I: IntoIterator<Item = usize>,
    {
        let mut d = self;
        for p_index in p_indexes {
            d = d.leftmost_n(p_index)?;
        }

        Ok(d)
    }

    /// Apply a step on the rightmost symbol of the current sentential form, using the production
    /// specified as input with the production index.
    ///
    /// It works just like the [step](#method.step) method, using as the index of the sentential
    /// form symbol to derive from the index of the last symbol of the sentential form.
    ///
    /// # Errors
    /// Return an error according to the [step](#method.step) method.
    ///
    /// # Examples
    /// ```rust
    /// use liblet::derivation::Derivation;
    /// use liblet::grammar::grammar;
    /// use liblet::symbol::symbol;
    ///
    /// let g = grammar("A -> a");
    /// let d = Derivation::new(g);
    ///
    /// assert!(d.rightmost(0).is_ok()); // applied "A -> a" on "A"
    /// ```
    pub fn rightmost(self, p_index: usize) -> Result<Derivation, DerivationError> {
        let sf = self.sentential_form();
        self.step(p_index, std::cmp::max(0, sf.len() - 1))
    }

    /// Apply a step on the rightmost symbol of the current sentential form, using the production
    /// specified as input with the production index.
    ///
    /// It works just like the [step](#method.step) method, using as the index of the sentential
    /// form symbol to derive from the index of rightmost non terminal symbol within the sentential form
    ///
    /// # Errors
    /// Return an error according to the [step](#method.step) method.
    ///
    /// Moreover, it can return a [NoNSymbol](enum.DerivationError.html#variant.NoNSymbol) error if there are no non terminal symbols in the current
    /// sentential form.
    ///
    /// # Examples
    /// ```rust
    /// use liblet::derivation::Derivation;
    /// use liblet::grammar::grammar;
    /// use liblet::symbol::symbol;
    ///
    /// let g = grammar("A -> a");
    /// let d = Derivation::new(g);
    ///
    /// assert!(d.rightmost_n(0).is_ok()); // applied "A -> a" on "A"
    /// ```
    pub fn rightmost_n(self, p_index: usize) -> Result<Derivation, DerivationError> {
        let sf = self.sentential_form();
        let len = sf.len();
        for (index, symbol) in sf.iter().rev().enumerate() {
            if symbol.is_non_terminal() {
                return self.step(p_index, (len - 1) - index);
            }
        }

        let index = std::cmp::max(0, self.sentential_form().len() - 1);
        self.step(p_index, index)
    }

    /// Repeated [rightmost](#method.rightmost) for each production index in an ordered collection of productions passed as input
    pub fn rightmost_from_iter<I>(self, p_indexes: I) -> Result<Derivation, DerivationError>
    where
        I: IntoIterator<Item = usize>,
    {
        let mut d = self;
        for p_index in p_indexes {
            d = d.rightmost(p_index)?;
        }

        Ok(d)
    }

    /// Repeated [rightmost_n](#method.rightmost_n) for each production index in an ordered collection of productions passed as input
    pub fn rightmost_n_from_iter<I>(self, p_indexes: I) -> Result<Derivation, DerivationError>
    where
        I: IntoIterator<Item = usize>,
    {
        let mut d = self;
        for p_index in p_indexes {
            d = d.rightmost_n(p_index)?;
        }

        Ok(d)
    }

    /// Check if a given step is appliable to the current sentential form.
    ///
    /// Return `true` if the given step is appliable, `false` otherwise.
    ///
    /// # Examples
    /// ```rust
    /// use liblet::derivation::Derivation;
    /// use liblet::grammar::grammar;
    /// use liblet::symbol::symbol;
    ///
    /// let g = grammar("A -> a");
    /// let d = Derivation::new(g);
    ///
    /// // check if step "A -> a" on "A" is appliable
    /// assert!(d.is_possible_step(0,0));
    /// ```
    pub fn is_possible_step(self, p_index: usize, index: usize) -> bool {
        self.clone().step(p_index, index).is_ok()
    }

    /// Return a collection of steps, representing the possible steps from the current derivation state,
    /// based on trying to derive using the production whose production index is given as argument
    /// with each possible sentential form symbol index.
    ///
    /// Can return an empty collection if no steps are possible.
    ///
    /// # Errors
    /// Return a [WrongProductionIndex](enum.DerivationError.html#variant.WrongProductionIndex) error if the production
    /// index targets a nonexistent grammar production
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::derivation::Derivation;
    /// use liblet::grammar::grammar;
    /// use liblet::symbol::symbol;
    ///
    /// let g = grammar("A -> a");
    /// let d = Derivation::new(g);
    ///
    /// // get all possible steps for applying "A -> a"
    /// // on the current sentential form (which is only 1),
    /// // the step (0,0)
    /// let possible_steps = d.possible_steps_by_prod(0)?;
    /// assert_eq!(possible_steps.len(), 1);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn possible_steps_by_prod(
        self,
        p_index: usize,
    ) -> Result<Vec<DerivationStep>, DerivationError> {
        let sf = self.sentential_form();
        let sf_len = self.sentential_form().len();
        let lhs: Vec<Symbol> = self
            .g
            .p()
            .get(p_index)
            .ok_or(DerivationError::WrongProductionIndex(p_index))?
            .lhs();
        let mut steps: Vec<DerivationStep> = Vec::new();

        for i in 0..sf_len {
            if sf[i..sf_len] == lhs[0..lhs.len()] {
                steps.push(DerivationStep {
                    p_index: p_index,
                    index: i,
                });
            }
        }

        Ok(steps)
    }

    /// Return a collection of steps, representing the possible steps from the current derivation state,
    /// based on trying to derive using the sentential form symbol index given as argument
    /// with each possible production of the grammar.
    ///
    /// Can return an empty collection if no steps are possible.
    ///
    /// # Errors
    /// Return a [WrongIndex](enum.DerivationError.html#variant.WrongIndex) error if the sentential form symbol
    /// index is not in range of the sentential form symbol indexes.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// use liblet::derivation::Derivation;
    /// use liblet::grammar::grammar;
    /// use liblet::symbol::symbol;
    ///
    /// let g = grammar("A -> a");
    /// let d = Derivation::new(g);
    ///
    /// // get all possible steps starting from the 0°
    /// // symbol of the sentential form ("A"), which is
    /// // only 1, the step (0,0)
    /// let possible_steps = d.possible_steps_by_index(0)?;
    /// assert_eq!(possible_steps.len(), 1);
    /// #
    /// #     Ok(())
    /// # }
    /// ```
    pub fn possible_steps_by_index(
        self,
        index: usize,
    ) -> Result<Vec<DerivationStep>, DerivationError> {
        let sf = self.sentential_form();
        let sf_len = self.sentential_form().len();
        let mut steps: Vec<DerivationStep> = Vec::new();

        if sf_len <= index {
            return Err(DerivationError::WrongIndex(sf, index));
        }

        for (i, p) in self.g.p().iter().enumerate() {
            let lhs = p.lhs();
            if sf[index..sf_len] == lhs[0..lhs.len()] {
                steps.push(DerivationStep {
                    p_index: i,
                    index: index,
                });
            }
        }

        Ok(steps)
    }
}

/// Convenience function for creating a derivation from a grammar.
///
/// # Examples
/// ```rust
/// use liblet::derivation::derivation;
/// use liblet::grammar::grammar;
/// use liblet::symbol::symbol;
///
/// let g = grammar("A -> a");
/// let d = derivation(g);
///
/// assert_eq!(d.sentential_form(), vec![symbol("A")]);
/// ```
pub fn derivation(g: Grammar) -> Derivation {
    Derivation::new(g)
}

/// Convenience function for creating a step from a production index and a
/// sentential form symbol index.
///
/// # Examples
/// ```rust
/// use liblet::derivation::step;
/// use liblet::symbol::symbol;
///
/// let s = step(0,0);
///
/// assert_eq!(s.p_index, 0);
/// assert_eq!(s.index, 0);
/// ```
pub fn step(p_index: usize, index: usize) -> DerivationStep {
    DerivationStep {
        p_index: p_index,
        index: index,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grammar::grammar;
    use crate::production::production;
    use crate::symbol::symbol;

    #[test]
    pub fn new() {
        let g = grammar("S -> A | B");
        let d = Derivation::new(g.clone());

        assert_eq!(d.g, g);
        assert_eq!(d.steps(), Vec::new());
        assert_eq!(d.sentential_form(), vec![symbol("S")]);
    }

    #[test]
    pub fn new_from() {
        let g = grammar("S -> A | B\nA -> a");
        let d = Derivation::new_from(g.clone(), vec![symbol("A")]);

        assert_eq!(d.g, g);
        assert_eq!(d.steps(), Vec::new());
        assert_eq!(d.sentential_form(), vec![symbol("A")]);
    }

    #[test]
    pub fn derivation() {
        let g = grammar("S -> A | B");
        let d = super::derivation(g.clone());

        assert_eq!(d.g, g);
        assert_eq!(d.steps(), Vec::new());
        assert_eq!(d.sentential_form(), vec![symbol("S")]);
    }

    #[test]
    pub fn sentential_form_before_steps() {
        let g = grammar("S -> A | B");
        let d = super::derivation(g.clone());

        assert_eq!(d.sentential_form(), vec![symbol("S")]);
    }

    #[test]
    pub fn step() {
        let g = grammar("S -> A | B");
        let d = super::derivation(g.clone());
        let step = DerivationStep {
            p_index: 0,
            index: 0,
        };
        match d.step(step.p_index, step.index) {
            Ok(d) => {
                assert_eq!(d.steps(), vec![step]);
                assert_eq!(d.sentential_form(), vec![symbol("A")]);
                assert_eq!(d.sentential_forms.len(), 2);
                assert_eq!(d.sentential_forms[0], vec![symbol("S")]);
                assert_eq!(d.sentential_forms[1], vec![symbol("A")]);
            }
            Err(_) => panic!("Step on derivation should not return an error"),
        }
    }

    #[test]
    pub fn step_wrong_production_index() {
        let g = grammar("S -> A | B");
        let d = super::derivation(g.clone());
        let step = DerivationStep {
            p_index: 2,
            index: 0,
        };
        match d.step(step.p_index, step.index) {
            Ok(_) => panic!("Step on derivation should return an error"),
            Err(e) => match e {
                DerivationError::WrongProductionIndex(p_index) => {
                    assert_eq!(p_index, step.p_index);
                }
                _ => panic!(
                    "Step on derivation should return an {} error, but {} was returned instead",
                    DerivationError::WrongProductionIndex(step.p_index),
                    e
                ),
            },
        }
    }

    #[test]
    pub fn step_wrong_index() {
        let g = grammar("S -> A | B");
        let d = super::derivation(g.clone());
        let sentential_form = vec![symbol("S")];
        let step = DerivationStep {
            p_index: 0,
            index: 1,
        };
        match d.step(step.p_index, step.index) {
            Ok(_) => panic!("Step on derivation should return an error"),
            Err(e) => match e {
                DerivationError::WrongIndex(sf, index) => {
                    assert_eq!(sf, sentential_form);
                    assert_eq!(index, step.index);
                }
                _ => panic!(
                    "Step on derivation should return an {} error, but {} was returned instead",
                    DerivationError::WrongIndex(sentential_form, step.index),
                    e
                ),
            },
        }
    }

    #[test]
    pub fn step_impossible_step() {
        let g = grammar("S -> A | B\nA -> a");
        let d = super::derivation(g.clone());
        let sentential_form = vec![symbol("S")];
        let production = production("A", "a");
        let step = DerivationStep {
            p_index: 2,
            index: 0,
        };
        match d.step(step.p_index, step.index) {
            Ok(_) => panic!("Step on derivation should return an error"),
            Err(e) => match e {
                DerivationError::ImpossibleStep(p, sf, s) => {
                    assert_eq!(p, production);
                    assert_eq!(sf, sentential_form);
                    assert_eq!(s, step);
                }
                _ => panic!(
                    "Step on derivation should return an {} error, but {} was returned instead",
                    DerivationError::ImpossibleStep(production, sentential_form, step),
                    e
                ),
            },
        }
    }

    #[test]
    pub fn step_from_iter() {
        let g = grammar("S -> A | B\nA -> a");
        let d = super::derivation(g.clone());
        let steps: Vec<DerivationStep> = vec![
            DerivationStep {
                p_index: 0,
                index: 0,
            },
            DerivationStep {
                p_index: 2,
                index: 0,
            },
        ];
        match d.step_from_iter(steps.clone()) {
            Ok(d) => {
                assert_eq!(d.steps(), steps);
                assert_eq!(d.sentential_form(), vec![symbol("a")]);
                assert_eq!(d.sentential_forms.len(), 3);
                assert_eq!(d.sentential_forms[0], vec![symbol("S")]);
                assert_eq!(d.sentential_forms[1], vec![symbol("A")]);
                assert_eq!(d.sentential_forms[2], vec![symbol("a")]);
            }
            Err(_) => panic!("Step on derivation should not return an error"),
        }
    }

    #[test]
    pub fn leftmost() {
        let g = grammar("S -> A B | B C\nA -> a");
        let mut d = super::derivation(g.clone());
        let p_index = 2;
        let steps = vec![
            DerivationStep {
                p_index: 0,
                index: 0,
            },
            DerivationStep {
                p_index: p_index,
                index: 0,
            },
        ];
        d = d.step(0, 0).unwrap();
        match d.leftmost(p_index) {
            Ok(d) => {
                assert_eq!(d.steps(), steps);
                assert_eq!(d.sentential_form(), vec![symbol("a"), symbol("B")]);
                assert_eq!(d.sentential_forms.len(), 3);
                assert_eq!(d.sentential_forms[0], vec![symbol("S")]);
                assert_eq!(d.sentential_forms[1], vec![symbol("A"), symbol("B")]);
                assert_eq!(d.sentential_forms[2], vec![symbol("a"), symbol("B")]);
            }
            Err(_) => panic!("Leftmost step on derivation should not return an error"),
        }
    }

    #[test]
    pub fn leftmost_from_iter() {
        let g = grammar("S -> A B | B C\nA -> B\n B -> b");
        let d = super::derivation(g.clone());
        let steps = vec![
            DerivationStep {
                p_index: 0,
                index: 0,
            },
            DerivationStep {
                p_index: 2,
                index: 0,
            },
            DerivationStep {
                p_index: 3,
                index: 0,
            },
        ];
        match d.leftmost_from_iter(steps.clone().iter().map(|x: &DerivationStep| x.p_index)) {
            Ok(d) => {
                assert_eq!(d.steps(), steps);
                assert_eq!(d.sentential_form(), vec![symbol("b"), symbol("B")]);
                assert_eq!(d.sentential_forms.len(), 4);
                assert_eq!(d.sentential_forms[0], vec![symbol("S")]);
                assert_eq!(d.sentential_forms[1], vec![symbol("A"), symbol("B")]);
                assert_eq!(d.sentential_forms[2], vec![symbol("B"), symbol("B")]);
                assert_eq!(d.sentential_forms[3], vec![symbol("b"), symbol("B")]);
            }
            Err(_) => panic!("Leftmost steps on derivation should not return an error"),
        }
    }

    #[test]
    pub fn rightmost() {
        let g = grammar("S -> A B | B\nB -> b");
        let mut d = super::derivation(g.clone());
        let p_index = 2;
        let steps = vec![
            DerivationStep {
                p_index: 0,
                index: 0,
            },
            DerivationStep {
                p_index: p_index,
                index: 1,
            },
        ];
        d = d.step(0, 0).unwrap();
        match d.rightmost(p_index) {
            Ok(d) => {
                assert_eq!(d.steps(), steps);
                assert_eq!(d.sentential_form(), vec![symbol("A"), symbol("b")]);
                assert_eq!(d.sentential_forms.len(), 3);
                assert_eq!(d.sentential_forms[0], vec![symbol("S")]);
                assert_eq!(d.sentential_forms[1], vec![symbol("A"), symbol("B")]);
                assert_eq!(d.sentential_forms[2], vec![symbol("A"), symbol("b")]);
            }
            Err(_) => panic!("Rightmost step on derivation should not return an error"),
        }
    }

    #[test]
    pub fn rightmost_from_iter() {
        let g = grammar("S -> A B | B\nB -> A\nA -> a");
        let d = super::derivation(g.clone());
        let steps = vec![
            DerivationStep {
                p_index: 0,
                index: 0,
            },
            DerivationStep {
                p_index: 2,
                index: 1,
            },
            DerivationStep {
                p_index: 3,
                index: 1,
            },
        ];
        match d.rightmost_from_iter(steps.clone().iter().map(|x: &DerivationStep| x.p_index)) {
            Ok(d) => {
                assert_eq!(d.steps(), steps);
                assert_eq!(d.sentential_form(), vec![symbol("A"), symbol("a")]);
                assert_eq!(d.sentential_forms.len(), 4);
                assert_eq!(d.sentential_forms[0], vec![symbol("S")]);
                assert_eq!(d.sentential_forms[1], vec![symbol("A"), symbol("B")]);
                assert_eq!(d.sentential_forms[2], vec![symbol("A"), symbol("A")]);
                assert_eq!(d.sentential_forms[3], vec![symbol("A"), symbol("a")]);
            }
            Err(_) => panic!("Rightmost steps on derivation should not return an error"),
        }
    }

    #[test]
    pub fn is_possible_step_true() {
        let g = grammar("S -> A | B");
        let d = super::derivation(g.clone());
        assert!(
            d.is_possible_step(0, 0),
            "Step on derivation should be possible"
        );
    }

    #[test]
    pub fn is_possible_step_false() {
        let g = grammar("S -> A | B");
        let d = super::derivation(g.clone());
        assert!(
            !d.is_possible_step(0, 1),
            "Step on derivation should not be possible"
        );
    }

    #[test]
    pub fn possible_steps_by_prod() {
        let g = grammar("S -> A | B");
        let d = super::derivation(g.clone());
        assert_eq!(
            d.possible_steps_by_prod(1).unwrap(),
            vec![super::step(1, 0)]
        );
    }

    #[test]
    pub fn possible_steps_by_index() {
        let g = grammar("S -> A | B");
        let d = super::derivation(g.clone());
        assert_eq!(
            d.possible_steps_by_index(0).unwrap(),
            vec![super::step(0, 0), super::step(1, 0)]
        );
    }
}
