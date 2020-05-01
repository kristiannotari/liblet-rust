use crate::grammar::Grammar;
use crate::production::Production;
use crate::symbol::Symbol;
use std::error::Error;
use std::fmt;

#[derive(Debug, PartialEq)]
pub enum DerivationError {
    WrongProductionIndex(usize),
    WrongIndex(Vec<Symbol>, usize),
    ImpossibleStep(Production, Vec<Symbol>, DerivationStep),
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
        }
    }
}

impl Error for DerivationError {}

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct DerivationStep {
    pub p_index: usize,
    pub index: usize,
}

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
    pub fn new(g: Grammar) -> Derivation {
        let from = vec![g.s()];
        Derivation::new_from(g, from)
    }

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
    pub fn steps(&self) -> Vec<DerivationStep> {
        self.steps.clone()
    }

    pub fn sentential_form(&self) -> Vec<Symbol> {
        if let Some(last) = self.sentential_forms.last() {
            last.clone()
        } else {
            vec![self.g.s()]
        }
    }

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

    pub fn step_iter<I>(self, steps: I) -> Result<Derivation, DerivationError>
    where
        I: IntoIterator<Item = DerivationStep>,
    {
        let mut d = self;
        for step in steps {
            d = d.step(step.p_index, step.index)?;
        }

        Ok(d)
    }

    pub fn leftmost(self, p_index: usize) -> Result<Derivation, DerivationError> {
        for (index, symbol) in self.sentential_form().iter().enumerate() {
            if symbol.is_non_terminal() {
                return self.step(p_index, index);
            }
        }

        self.step(p_index, 0)
    }

    pub fn leftmost_iter<I>(self, p_indexes: I) -> Result<Derivation, DerivationError>
    where
        I: IntoIterator<Item = usize>,
    {
        let mut d = self;
        for p_index in p_indexes {
            d = d.leftmost(p_index)?;
        }

        Ok(d)
    }

    pub fn rightmost(self, p_index: usize) -> Result<Derivation, DerivationError> {
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

    pub fn rightmost_iter<I>(self, p_indexes: I) -> Result<Derivation, DerivationError>
    where
        I: IntoIterator<Item = usize>,
    {
        let mut d = self;
        for p_index in p_indexes {
            d = d.rightmost(p_index)?;
        }

        Ok(d)
    }

    pub fn is_possible_step(self, p_index: usize, index: usize) -> bool {
        self.clone().step(p_index, index).is_ok()
    }

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

pub fn derivation(g: Grammar) -> Derivation {
    Derivation::new(g)
}

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
    pub fn step_iter() {
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
        match d.step_iter(steps.clone()) {
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
    pub fn leftmost_iter() {
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
        match d.leftmost_iter(steps.clone().iter().map(|x: &DerivationStep| x.p_index)) {
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
    pub fn rightmost_iter() {
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
        match d.rightmost_iter(steps.clone().iter().map(|x: &DerivationStep| x.p_index)) {
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
