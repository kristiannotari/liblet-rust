use crate::grammar::Grammar;

pub struct Derivation {
    g: Grammar,
    steps: Vec<(usize, usize)>,
}

impl Derivation {
    pub fn new(g: Grammar) -> Derivation {
        Derivation {
            g: g,
            steps: Vec::new(),
        }
    }

    pub fn step(mut self, p_index: usize, index: usize) -> Derivation {
        self.steps.push((p_index, index));

        self
    }
}

#[cfg(test)]
mod tests {}
