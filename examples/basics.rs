use liblet::grammar::grammar;
use liblet::production::production;
use liblet::symbol::symbol;

extern crate liblet;

fn main() {
    // simple grammar construction by string

    // you can specify a grammar by simply writing its productions
    // in the form LHS -> RHS | ...

    // the start symbol is the non terminal symbol in the first encountered production
    // which is, in this case, "Sentence"
    let g = grammar(
        "
        Sentence -> Name | List End
        List -> Name | Name , List
        Name -> tom | dick | harry
        , Name End -> and Name
    ",
    );

    // prints out the grammar
    // it will show the n, t and s symbols and the productions
    println!("{}", g);

    // you can also construct symbols from string directly
    // check out the documentation to know which kind of strings/chars
    // are accepted
    let symbol = symbol("MySymbol");
    println!("My symbol: {}", symbol);

    // you can also construct productions from string directly
    // specifying the left and right hand sides
    let production = production("A", "B");
    println!("My production: {}", production);
}
