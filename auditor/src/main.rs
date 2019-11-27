#![feature(rustc_private)]

extern crate env_logger;
extern crate rustc_driver;

use std::env;
use std::path::Path;

use taurus::analyzer;
use taurus::extractor;

// Probe the sysroot for rust compiler. This should be fairly simple if user uses
// rustup to setup the environment.
pub fn find_sysroot() -> String {
    let home = option_env!("RUSTUP_HOME");
    let toolchain = option_env!("RUSTUP_TOOLCHAIN");
    match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .expect("Could not find sysroot. Use rustup to set up the compiler")
            .to_owned(),
    }
}

fn main() {
    // rustc has its own logs. Switch it on/off according to 'RUST_LOG'
    if env::var("RUST_LOG").is_ok() {
        rustc_driver::init_rustc_env_logger();
    }

    // Use "TAURUS_LOG" to control our own logging facility
    if env::var("TAURUS_LOG").is_ok() {
        let e = env_logger::Env::new()
            .filter("TAURUS_LOG")
            .write_style("TAURUS_LOG_STYLE");
        env_logger::init_from_env(e);
    }

    let mut cmd_args: Vec<_> = env::args().collect();

    // In data collection mode, we assume that RUSTC_WRAPPER is set to 'taurus' such
    // that Cargo passes 'rustc' as the first argument. Otherwise, taurus is invoked
    // in data analysis mode
    if cmd_args.len() > 1 && Path::new(&cmd_args[1]).file_stem() == Some("rustc".as_ref()) {
        cmd_args.remove(1);

        // Tell compiler where to find the std library.
        cmd_args.push(String::from("--sysroot"));
        cmd_args.push(find_sysroot());

        let result = rustc_driver::report_ices_to_stderr_if_any(move || {
            let extractor = &mut extractor::TaurusExtractor::default();
            rustc_driver::run_compiler(
                &cmd_args, extractor, None, // use default file loader
                None, // emit output to default destination
            )
        });

        std::process::exit(result.is_err() as i32);
    } else {
        // We are in analysis mode
        let db_path = Path::new("target/debug/deps/taurus.depstore");
        let analyzer = analyzer::TaurusAnalyzer::new(&db_path);
        // println!("{}", analyzer.get_depgraph_dot());
        let report = analyzer.audit();
        for to_warn in report.unaudited {
            println!("unaudited: {} at {}", to_warn.0, to_warn.1);
        }
        for to_inform in report.audited {
            println!(
                "audited: {} by {} at {}",
                to_inform.0, to_inform.1, to_inform.2
            );
        }
        println!("Audit completed");
    }

    return;
}
