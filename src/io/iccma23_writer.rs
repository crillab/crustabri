use crate::{Argument, ResponseWriter};
use anyhow::{Context, Result};
use std::io::Write;

/// A writer for the output format used in the ICCMA 2023 competition.
#[derive(Default)]
pub struct Iccma23Writer;

impl ResponseWriter<usize> for Iccma23Writer {
    fn write_no_extension(&self, writer: &mut dyn Write) -> Result<()> {
        super::specs::write_no_extension(writer)
    }

    fn write_single_extension(
        &self,
        writer: &mut dyn Write,
        extension: &[&Argument<usize>],
    ) -> Result<()> {
        let context = "while writing an extension";
        write!(writer, "w").context(context)?;
        extension
            .iter()
            .try_for_each(|arg| write!(writer, " {}", arg).context(context))?;
        writeln!(writer).context(context)?;
        writer.flush().context(context)
    }

    fn write_acceptance_status(
        &self,
        writer: &mut dyn Write,
        acceptance_status: bool,
    ) -> Result<()> {
        super::specs::write_acceptance_status(writer, acceptance_status)
    }
}
