use crate::{AAFramework, Argument, LabelType};
use anyhow::{Context, Result};
use std::io::{Read, Write};

/// The type of callback functions to call when warnings are raised while parsing an AF.
pub type WarningHandler = Box<dyn Fn(usize, String)>;

/// A trait implemented by objects able to read Argumentation Frameworks.
pub trait InstanceReader<T>
where
    T: LabelType,
{
    /// Reads an [`AAFramework`].
    /// The [LabelType](crate::LabelType) of the returned AFs is depends on the reader.
    ///
    /// In case warnings are raised, the callback functions registered by [add_warning_handler](Self::add_warning_handler) are triggered.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::{AAFramework, AspartixReader, InstanceReader};
    /// fn read_af_from_str(s: &str) -> AAFramework<String> {
    ///     let reader = AspartixReader::default();
    ///     reader.read(&mut s.as_bytes()).expect("invalid Aspartix AF")
    /// }
    /// # read_af_from_str("arg(a).");
    /// ```
    fn read(&self, reader: &mut dyn Read) -> Result<AAFramework<T>>;

    /// Reads an argument from a string.
    fn read_arg_from_str<'a>(&self, af: &'a AAFramework<T>, arg: &str) -> Result<&'a Argument<T>>;

    /// Adds a callback function to call when warnings are raised while parsing an AF.
    fn add_warning_handler(&mut self, h: WarningHandler);
}

/// A trait implemented by objects that write responses to problems.
pub trait ResponseWriter<T>
where
    T: LabelType,
{
    /// Writes the text associated with the fact the problem has no extension.
    fn write_no_extension(&self, writer: &mut dyn Write) -> Result<()>;

    /// Writes a single extension.
    fn write_single_extension(
        &self,
        writer: &mut dyn Write,
        extension: &[&Argument<T>],
    ) -> Result<()>;

    /// Writes an acceptance status.
    fn write_acceptance_status(
        &self,
        writer: &mut dyn Write,
        acceptance_status: bool,
    ) -> Result<()>;
}

pub(crate) fn write_no_extension(writer: &mut dyn Write) -> Result<()> {
    let context = "while writing problem has no extension";
    writeln!(writer, "NO").context(context)?;
    writer.flush().context(context)
}

pub(crate) fn write_acceptance_status(
    writer: &mut dyn Write,
    acceptance_status: bool,
) -> Result<()> {
    let context = "while writing an acceptance_status";
    writeln!(writer, "{}", if acceptance_status { "YES" } else { "NO" }).context(context)?;
    writer.flush().context(context)
}
