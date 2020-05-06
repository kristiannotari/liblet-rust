use liblet::symbol::symbol;

extern crate liblet;

// simple symbols usage
fn main() {
    // let's create a couple of symbols

    // we can create symbols directly from strings
    // check out the documentation to know which kind of strings/chars
    // are accepted
    let s1 = symbol("A");
    let s2 = symbol("a");

    // we can check if a symbol is a terminal or non terminal one
    // non terminal one starts with an uppercase letter
    assert!(s1.is_non_terminal());
    assert!(s2.is_terminal());

    // we can create a collection of symbols directly
    // from string, separating them by any whitespace
    let symbols = liblet::symbol::Symbol::from_string("a b c d");
    // it returns a result, cause the parsing of symbols can fail
    assert!(symbols.is_ok());
    // [a, b, c, d]
    println!("Symbols: {:?}", symbols.unwrap());
}
