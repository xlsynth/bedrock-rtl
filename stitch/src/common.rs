use std::path::Path;

use slang_rs::SlangConfig;
use topstitch::ModDef;
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
    let sources: Vec<&str> = files.iter().map(|file| file.as_str()).collect();
    let mut incdirs: Vec<&str> = headers.iter().map(
        |hdr| Path::new(hdr).parent().unwrap().to_str().unwrap()
    ).collect();
    incdirs.sort();
    incdirs.dedup();

    let config = SlangConfig {
        sources: &sources,
        incdirs: &incdirs,
        tops: &[name],
        ignore_unknown_modules: true,
        timescale: None,
        ..Default::default()
    };

    ModDef::from_verilog_using_slang(name, &config, true)
}
