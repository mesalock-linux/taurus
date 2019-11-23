#![crate_name = "taurus_annotation"]
#![crate_type = "dylib"]
#![feature(plugin_registrar)]
#![feature(rustc_private)]

extern crate rustc_plugin;
extern crate syntax;
extern crate taurus_attributes;

use rustc_plugin::Registry;
use taurus_attributes::Symbols;
use syntax::feature_gate::AttributeType::Whitelisted;

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    let symbols = Symbols::new();
    reg.register_attribute(symbols.require_audit, Whitelisted);
    reg.register_attribute(symbols.audited, Whitelisted);
    reg.register_attribute(symbols.entry_point, Whitelisted);
}
