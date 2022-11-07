use anyhow::{Context, Result};
use crustabri::{AAFramework, InstanceReader, LabelType};
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
        .help("the input file that contains the AF")
        .required(true)
}

pub(crate) const ARG_READER: &str = "READER";

pub(crate) fn reader_arg() -> Arg<'static, 'static> {
    Arg::with_name(ARG_READER)
        .short("r")
        .long("reader")
        .empty_values(false)
        .multiple(false)
        .possible_values(&["apx", "iccma23"])
        .default_value("iccma23")
        .help("the input file format")
        .required(false)
}

pub(crate) fn read_file_path<T>(
    file_path: &str,
    reader: &mut dyn InstanceReader<T>,
) -> Result<AAFramework<T>>
where
    T: LabelType,
{
    let canonicalized = canonicalize_file_path(file_path)?;
    info!("reading input file {:?}", canonicalized);
    let mut file_reader = BufReader::new(File::open(canonicalized)?);
    reader.add_warning_handler(Box::new(|line, msg| warn!("at line {}: {}", line, msg)));
    let af = reader.read(&mut file_reader)?;
    info!(
        "the argumentation framework has {} argument(s) and {} attack(s)",
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
