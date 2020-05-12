#![doc(html_root_url = "https://docs.rs/liblet/0.1.1")]

//! Porting project for the liblet library of the Unimi course "Linguaggi e Traduttori" in Rust.
//!
//! The aim of this library is to provide a set of convenient data types representing the usual
//! objects of study of *formal languages* and *parsing* such as: grammars, productions, derivations...
//!
//! More info about the original library can be found [here](https://liblet.readthedocs.io/en/v1.1.0-alpha/index.html).
//!
//! At the moment the library follows a learning goal, which means it's useful to use in order to achieve
//! a better understanding of the formal languages world and objects. This porting also aims to deliver,
//! over the library already existing stuff, some other ready algorithms implementations in order to better comprehend
//! how objects can interact with others. However, this should not be a reference for algorithms implementations,
//! but a set of tools to create your own, instead. They will be there, too, just in case.
//!
//! # Notice
//! This project is also a learning project for writing libraries in Rust.
//! If you encounter any issue or have any advice, please report them. Thanks a lot.
//!
//!
//! # Examples
//! Simple grammar creation from string:
//! ```rust
//! # use std::error::Error;
//! #
//! # fn main() -> Result<(), Box<dyn Error>> {
//! use liblet::grammar::grammar;
//!
//! // grammar creation from string
//! let g = grammar("
//!     S -> A | B
//!     A -> a
//!     B -> b
//! ");
//! #
//! #     Ok(())
//! # }
//! ```
//!
//! Derivation steps over a grammar:
//! ```rust
//! # use std::error::Error;
//! #
//! # fn main() -> Result<(), Box<dyn Error>> {
//! use liblet::grammar::grammar;
//! use liblet::derivation::derivation;
//! use liblet::symbol::symbol;
//!
//! // grammar creation from string
//! let g = grammar("
//!     S -> A | B
//!     A -> a
//!     B -> b
//! ");
//!
//! // derivation created over the grammar g
//! // and two derivation steps applied, in order
//! // to obtain an "a" sentential form
//! let d = derivation(g).step(0,0)?.step(2,0)?;
//!
//! assert_eq!(d.sentential_form(), vec![symbol("a")]);
//! #
//! #     Ok(())
//! # }
//! ```
//!

mod tokenizer;

pub mod derivation;
pub mod grammar;
pub mod production;
pub mod symbol;

pub use self::derivation::Derivation;
pub use self::derivation::DerivationError;
pub use self::derivation::DerivationStep;

pub use self::grammar::Grammar;
pub use self::grammar::GrammarError;

pub use self::production::Production;
pub use self::production::ProductionError;
pub use self::production::ProductionPredicate;

pub use self::symbol::Symbol;
pub use self::symbol::SymbolError;
