#![feature(rustc_private)]

extern crate syntax;

use syntax::symbol::Symbol;

macro_rules! symbols {
    ($($s: ident),+ $(,)?) => {
        #[derive(Clone)]
        #[allow(non_snake_case)]
        pub struct Symbols {
            $(pub $s: Symbol,)+
        }

        impl Symbols {
            pub fn new() -> Self {
                Symbols {
                    $($s: Symbol::intern(stringify!($s)),)+
                }
            }
        }
    }
}

symbols! {
    require_audit,
    audited,
    entry_point,
}
