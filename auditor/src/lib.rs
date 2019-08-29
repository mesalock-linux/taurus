#![feature(rustc_private)]

extern crate rustc;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_mir;
extern crate rustc_apfloat;
extern crate rustc_target;
extern crate syntax;
extern crate syntax_pos;

#[macro_use]
extern crate log;
#[macro_use]
extern crate serde_derive;
extern crate sled;

extern crate taurus_attributes;

pub mod extractor;
pub mod analyzer;
pub(crate) mod annotated;
pub(crate) mod summaries;
