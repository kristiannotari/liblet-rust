use liblet::production::{production, ProductionPredicate};
use liblet::symbol::symbol;

extern crate liblet;

// simple production usage
fn main() {
    // let's create a production
    // we can create producions directly from strings
    let p = production("A", "B C");

    // we can access production sides
    println!("Production lhs: {:?}", p.lhs());
    println!("Production rhs: {:?}", p.rhs());
    // and even get a set of all symbols involved in the production
    println!("Production symbols: {:?}", p.symbols());

    // we can test if productions have some properties
    // by using production predicates
    assert!(ProductionPredicate::LhsEquals(vec![symbol("A")]).test(&p));
    assert!(!ProductionPredicate::LhsEquals(vec![]).test(&p));
    assert!(ProductionPredicate::RhsEquals(vec![symbol("B"), symbol("C")]).test(&p));
    assert!(!ProductionPredicate::RhsEquals(vec![symbol("C")]).test(&p));
    // you can discover more predicates and usage checking out the documentation
}
