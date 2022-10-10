use anyhow::{Context, Result};
use crustabri::{AAFramework, AspartixReader};
use crusti_app_helper::{info, warn, Arg};
use std::{
    fs::{self, File},
    io::BufReader,
    path::PathBuf,
};

pub(crate) const ARG_INPUT: &str = "INPUT";

pub(crate) fn input_args() -> Arg<'static, 'static> {
    Arg::with_name(ARG_INPUT)
        .short("f")
        .empty_values(false)
        .multiple(false)
        .help("the input file in Aspartix format")
        .required(true)
}

pub(crate) fn read_aspartix_file_path(file_path: &str) -> Result<AAFramework<String>> {
    let canonicalized = canonicalize_file_path(file_path)?;
    info!("reading input file {:?}", canonicalized);
    let mut file_reader = BufReader::new(File::open(canonicalized)?);
    let mut parser = AspartixReader::default();
    parser.add_warning_handler(Box::new(|line, msg| warn!("at line {}: {}", line, msg)));
    let af = parser.read(&mut file_reader)?;
    info!(
        "The argumentation framework has {} arguments and {} attacks",
        af.n_arguments(),
        af.n_attacks(),
    );
    Ok(af)
}

/// Canonicalize a path given by the user.
pub(crate) fn canonicalize_file_path(file_path: &str) -> Result<PathBuf> {
    fs::canonicalize(&PathBuf::from(file_path))
        .with_context(|| format!(r#"while opening file "{}""#, file_path))
}
