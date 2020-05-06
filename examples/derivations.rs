use liblet::derivation::derivation;
use liblet::grammar::grammar;

extern crate liblet;

// simple derivations usage starting from a grammar
fn main() {
    // let's create our grammar first
    let g = grammar(
        "
        Sentence -> Name | List End
        List -> Name | Name , List
        Name -> tom | dick | harry
        , Name End -> and Name
    ",
    );

    // then create a derivation on it
    let d = derivation(g);

    // it does nothing by itself but we can make derivation
    // steps on it, in order to get new sentential forms,
    // based on the grammar production rules and the initial
    // sentential form, which, by default, is the grammar start symbol

    // we specify the production rule index and the index of the symbol
    // in the sentential form from which to apply the derivation
    let result = d.step(1, 0);

    // notice that a derivation step could fail, so a Result is returned
    assert!(result.is_ok());
    let d = result.unwrap();

    // we can now print out our derivation, which prints all the
    // derivation steps done on the initial sentential form
    // [Sentence -> Name]
    println!("Derivation: {}", d);

    // we can now do multiple steps at once, thanks to step
    // returning a result containing the modified derivation as Ok
    let result = d
        .step(3, 0) // List End -> Name , List End
        .and_then(|d| d.step(4, 0)) // Name , List End -> tom , List End
        .and_then(|d| d.step(2, 2)) // tom , List End -> tom , Name End
        .and_then(|d| d.step(7, 1)) // tom , Name End -> tom and Name
        .and_then(|d| d.step(5, 2)); // tom and Name -> tom and dick
    assert!(result.is_ok());
    let d = result.unwrap();
    println!("Derivation final: {}", d);

    // at any time, you can query the derivation to get the
    // derivation steps applied and the current sentential form
    println!("Derivation steps: {:?}", d.steps());
    println!("Derivation sentential form: {:?}", d.sentential_form());
}
