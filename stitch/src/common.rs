// SPDX-License-Identifier: Apache-2.0

use std::path::Path;

use topstitch::{ModDef, ParserConfig};
use clap::Args;

#[derive(Args)]
pub struct CommonArgs {
    /// The SystemVerilog files needed to load the module to instantiate
    #[arg(long)]
    pub sv_files: Vec<String>,

    /// SystemVerilog headers needed to load the module to instantiate
    #[arg(long)]
    pub sv_headers: Vec<String>,
}

pub fn load_module(
    name: &str,
    files: &[String],
    headers: &[String],
) -> ModDef {
    // To speed up parsing, only include source files that
    // * are the top-level source file, indicated by the file stem, or
    // * are packages, indicated by the presence of "endpackage", or
    // * contain multiple module definitions (e.g., br_gate_mock.sv)
    let file_stem_variants = [name.to_string(), format!("{name}_mock")];
    let sources: Vec<&str> = files
        .iter()
        .map(|file| file.as_str())
        .filter(|file| {
            if Path::new(file)
                .file_stem()
                .and_then(|stem| stem.to_str())
                .map(|stem| file_stem_variants.contains(&stem.to_string()))
                .unwrap_or(false)
            {
                true
            } else if let Ok(contents) = std::fs::read_to_string(file) {
                contents.contains("endpackage") || contents.matches("endmodule").count() >= 2
            } else {
                false
            }
        })
        .collect();
    let mut incdirs: Vec<&str> = headers
        .iter()
        .map(|hdr| Path::new(hdr).parent().unwrap().to_str().unwrap())
        .collect();
    incdirs.sort();
    incdirs.dedup();

    let config = ParserConfig {
        sources: &sources,
        incdirs: &incdirs,
        tops: &[name],
        ignore_unknown_modules: true,
        skip_unsupported: true,
        timescale: None,
        extra_arguments: &[
            "--threads",
            "1",
        ],
        ..Default::default()
    };

    ModDef::from_verilog_with_config(name, &config)
}
