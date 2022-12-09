use crate::{
    aa::{AAFramework, Argument},
    utils::LabelType,
};
use anyhow::{Context, Result};
use std::io::{Read, Write};

/// The type of callback functions to call when warnings are raised while parsing an AF.
///
/// Such callback functions take as input the line number and the warning message.
pub type WarningHandler = Box<dyn Fn(usize, String)>;

/// A trait implemented by objects able to read Argumentation Frameworks.
///
/// They must detect errors encountered while reading a framework and can also raise warnings using the ones registered through the [add_warning_handler](Self::add_warning_handler) function.
///
/// In addition to complete frameworks, such readers are also able to read single argument labels given as strings.
pub trait InstanceReader<T>
where
    T: LabelType,
{
    /// Reads an [`AAFramework`].
    ///
    /// The [LabelType](crate::aa::LabelType) of the returned AFs is depends on the reader.
    ///
    /// In case warnings are raised, the callback functions registered by [add_warning_handler](Self::add_warning_handler) are triggered.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::io::{AspartixReader, InstanceReader};
    /// # use crustabri::aa::AAFramework;
    /// fn read_af_from_str(s: &str) -> AAFramework<String> {
    ///     let reader = AspartixReader::default();
    ///     reader.read(&mut s.as_bytes()).expect("invalid Aspartix AF")
    /// }
    /// # read_af_from_str("arg(a).");
    /// ```
    fn read(&self, reader: &mut dyn Read) -> Result<AAFramework<T>>;

    /// Reads an argument from a string.
    ///
    /// The argument must belong to the provided framework.
    /// If it is not the case, an error is returned.
    ///
    /// # Example
    ///
    /// ```
    /// # use crustabri::aa::{AAFramework};
    /// # use crustabri::utils::LabelType;
    /// # use crustabri::io::{AspartixReader, InstanceReader};
    /// fn print_arg_status<T>(reader: &dyn InstanceReader<T>, af: &AAFramework<T>, arg: &str)
    /// where
    ///     T: LabelType,
    /// {
    ///     match reader.read_arg_from_str(af, arg) {
    ///         Ok(a) => println!("arg {} has id {}", a.label(), a.id()),
    ///         Err(_) => println!("no arg with label {} in AF", arg),
    ///     }
    /// }
    /// # print_arg_status(&AspartixReader::default(), &AAFramework::default(), "");
    /// ```
    fn read_arg_from_str<'a>(&self, af: &'a AAFramework<T>, arg: &str) -> Result<&'a Argument<T>>;

    /// Adds a callback function to call when warnings are raised while parsing an AF.
    ///
    /// Such callback functions take as input the line number and the warning message.
    fn add_warning_handler(&mut self, h: WarningHandler);
}

/// A trait implemented by objects that write responses to argumentation problems.
pub trait ResponseWriter<T>
where
    T: LabelType,
{
    /// Writes the text associated with the fact the problem has no extension.
    ///
    /// Such answer may be written by a solver seeking extensions.
    fn write_no_extension(&self, writer: &mut dyn Write) -> Result<()>;

    /// Writes a single extension.
    ///
    /// Such answer may be written by a solver seeking extensions.
    fn write_single_extension(
        &self,
        writer: &mut dyn Write,
        extension: &[&Argument<T>],
    ) -> Result<()>;

    /// Writes an acceptance status.
    ///
    /// Such answer may be written by a solver checking the credulous or the skeptical acceptance of an argument.
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
