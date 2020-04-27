use crate::production::Production;

pub fn prods2table<I>(productions: I)
where
    I: Iterator<Item = Production>,
{
    for (i, p) in productions.enumerate() {
        println!("{} {}", i, p)
    }
}
